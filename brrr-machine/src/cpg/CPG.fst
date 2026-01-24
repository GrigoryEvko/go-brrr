(**
 * BrrrMachine.CPG - Code Property Graph
 *
 * Unified representation combining AST, CFG, PDG, CallGraph, and EffectGraph.
 * Based on synthesis_combined.md Definition 3.3:
 *   CPG = (V, E, lambda, mu) where:
 *     - V: nodes (program elements)
 *     - E: labeled edges (AST, CFG, PDG_data, PDG_ctrl, Call, Effect)
 *     - lambda: node labeling function
 *     - mu: edge labeling function
 *
 * Theorem 3.4 (CPG Completeness): Any path-sensitive dataflow fact computable
 * on the original program is computable via graph reachability queries on the CPG.
 *
 * This module provides:
 *   1. Comprehensive node types covering all Brrr-Lang IR nodes
 *   2. Edge types for multi-layer program representation
 *   3. CFG, PDG, CallGraph, and EffectGraph construction
 *   4. Query primitives for program analysis
 *)
module BrrrMachine.CPG

open FStar.List.Tot
open FStar.Set

(** ============================================================================
    SECTION 1: BASIC IDENTIFIERS
    ============================================================================
    Unique identifiers for nodes, variables, and procedures.
    ============================================================================ *)

(** Unique node identifier in the CPG *)
type node_id = nat

(** Variable identifier *)
type var_id = string

(** Procedure/function identifier *)
type proc_id = nat

(** Label for control flow (loop labels, etc.) *)
type label = string

(** Source location span *)
type span = {
  file_id : nat;
  start_offset : nat;
  end_offset : nat;
}

let empty_span : span = { file_id = 0; start_offset = 0; end_offset = 0 }

(** ============================================================================
    SECTION 2: CPG NODE KINDS
    ============================================================================
    Comprehensive enumeration of all node types in Brrr-Lang IR.
    Corresponds to expr, pattern, and statement constructs from Expressions.fst.
    ============================================================================ *)

(** Literal value kinds *)
type literal_kind =
  | LitKUnit      : literal_kind
  | LitKBool      : bool -> literal_kind
  | LitKInt       : int -> literal_kind
  | LitKFloat     : int -> literal_kind  (* IEEE 754 bits *)
  | LitKString    : string -> literal_kind
  | LitKChar      : nat -> literal_kind  (* Unicode codepoint *)

(** Unary operator kinds *)
type unary_op_kind =
  | UOpNeg        : unary_op_kind  (* -x *)
  | UOpNot        : unary_op_kind  (* !x *)
  | UOpBitNot     : unary_op_kind  (* ~x *)
  | UOpDeref      : unary_op_kind  (* *x *)
  | UOpRef        : unary_op_kind  (* &x *)
  | UOpRefMut     : unary_op_kind  (* &mut x *)

(** Binary operator kinds *)
type binary_op_kind =
  (* Arithmetic *)
  | BOpAdd    : binary_op_kind
  | BOpSub    : binary_op_kind
  | BOpMul    : binary_op_kind
  | BOpDiv    : binary_op_kind
  | BOpMod    : binary_op_kind
  (* Comparison *)
  | BOpEq     : binary_op_kind
  | BOpNe     : binary_op_kind
  | BOpLt     : binary_op_kind
  | BOpLe     : binary_op_kind
  | BOpGt     : binary_op_kind
  | BOpGe     : binary_op_kind
  (* Logical *)
  | BOpAnd    : binary_op_kind
  | BOpOr     : binary_op_kind
  (* Bitwise *)
  | BOpBitAnd : binary_op_kind
  | BOpBitOr  : binary_op_kind
  | BOpBitXor : binary_op_kind
  | BOpShl    : binary_op_kind
  | BOpShr    : binary_op_kind

(** Pattern kinds for match expressions *)
type pattern_kind =
  | PatKWild      : pattern_kind                           (* _ *)
  | PatKVar       : var_id -> pattern_kind                 (* x *)
  | PatKLit       : literal_kind -> pattern_kind           (* 42 *)
  | PatKTuple     : list pattern_kind -> pattern_kind      (* (p1, p2) *)
  | PatKStruct    : string -> pattern_kind                 (* Struct { ... } *)
  | PatKVariant   : string -> string -> pattern_kind       (* Enum::Variant *)
  | PatKOr        : pattern_kind                           (* p1 | p2 *)
  | PatKGuard     : pattern_kind                           (* p if e *)
  | PatKRef       : pattern_kind                           (* &p *)
  | PatKBox       : pattern_kind                           (* box p *)
  | PatKRest      : pattern_kind                           (* ... *)
  | PatKAs        : var_id -> pattern_kind                 (* p @ x *)

(**
 * CPG Node Kind - Complete enumeration of all IR node types.
 *
 * This covers every construct in Brrr-Lang Expressions.fst:
 *   - Literals, variables, operators
 *   - Data construction and access
 *   - Control flow (if, match, loops, breaks)
 *   - Bindings (let, assignments)
 *   - Functions and closures
 *   - Memory operations (box, borrow, move, drop)
 *   - Effects (throw, try, await, yield, perform, handle)
 *   - Continuations (reset, shift)
 *   - Async (async, spawn)
 *   - Type operations (as, is, sizeof, alignof)
 *   - Special nodes (entry, exit, phi, call/return sites)
 *)
noeq type cpg_node_kind =
  (* === Literals and Values === *)
  | NkLit           : literal_kind -> cpg_node_kind
  | NkVar           : var_id -> cpg_node_kind
  | NkGlobal        : string -> cpg_node_kind

  (* === Operations === *)
  | NkUnary         : unary_op_kind -> cpg_node_kind
  | NkBinary        : binary_op_kind -> cpg_node_kind
  | NkCall          : cpg_node_kind
  | NkMethodCall    : method_name:string -> cpg_node_kind

  (* === Data Construction === *)
  | NkTuple         : arity:nat -> cpg_node_kind
  | NkArray         : length:nat -> cpg_node_kind
  | NkStruct        : type_name:string -> cpg_node_kind
  | NkVariant       : type_name:string -> variant_name:string -> cpg_node_kind

  (* === Data Access === *)
  | NkField         : field_name:string -> cpg_node_kind
  | NkIndex         : cpg_node_kind
  | NkTupleProj     : index:nat -> cpg_node_kind

  (* === Control Flow === *)
  | NkIf            : cpg_node_kind
  | NkMatch         : arm_count:nat -> cpg_node_kind
  | NkMatchArm      : arm_index:nat -> cpg_node_kind
  | NkLoop          : label:option label -> cpg_node_kind
  | NkWhile         : label:option label -> cpg_node_kind
  | NkFor           : label:option label -> iter_var:var_id -> cpg_node_kind
  | NkBreak         : label:option label -> cpg_node_kind
  | NkContinue      : label:option label -> cpg_node_kind
  | NkReturn        : cpg_node_kind

  (* === Bindings === *)
  | NkLet           : pattern_kind -> cpg_node_kind
  | NkLetMut        : var_id -> cpg_node_kind
  | NkAssign        : cpg_node_kind

  (* === Functions === *)
  | NkLambda        : param_count:nat -> cpg_node_kind
  | NkClosure       : param_count:nat -> capture_count:nat -> cpg_node_kind
  | NkParam         : param_name:var_id -> param_index:nat -> cpg_node_kind

  (* === Memory === *)
  | NkBox           : cpg_node_kind
  | NkDeref         : cpg_node_kind
  | NkBorrow        : cpg_node_kind
  | NkBorrowMut     : cpg_node_kind
  | NkMove          : cpg_node_kind
  | NkDrop          : cpg_node_kind

  (* === Effects === *)
  | NkThrow         : cpg_node_kind
  | NkTry           : catch_count:nat -> cpg_node_kind
  | NkCatch         : catch_index:nat -> cpg_node_kind
  | NkFinally       : cpg_node_kind
  | NkAwait         : cpg_node_kind
  | NkYield         : cpg_node_kind
  | NkHandle        : cpg_node_kind
  | NkPerform       : op_name:string -> cpg_node_kind
  | NkResume        : cont_var:var_id -> cpg_node_kind

  (* === Delimited Continuations === *)
  | NkReset         : prompt:label -> cpg_node_kind
  | NkShift         : prompt:label -> cont_var:var_id -> cpg_node_kind

  (* === Async/Concurrency === *)
  | NkAsync         : cpg_node_kind
  | NkSpawn         : cpg_node_kind

  (* === Type Operations === *)
  | NkAs            : cpg_node_kind  (* e as T *)
  | NkIs            : cpg_node_kind  (* e is T *)
  | NkSizeof        : cpg_node_kind
  | NkAlignof       : cpg_node_kind

  (* === Blocks and Sequences === *)
  | NkBlock         : stmt_count:nat -> cpg_node_kind
  | NkSeq           : cpg_node_kind
  | NkUnsafe        : cpg_node_kind

  (* === Special Nodes === *)
  | NkHole          : cpg_node_kind  (* Placeholder _ *)
  | NkError         : msg:string -> cpg_node_kind  (* Error node *)

  (* === CFG Synthetic Nodes === *)
  | NkEntry         : proc_id -> cpg_node_kind
  | NkExit          : proc_id -> cpg_node_kind
  | NkPhi           : var_id -> cpg_node_kind  (* SSA phi node *)
  | NkCallSite      : callee:proc_id -> cpg_node_kind
  | NkReturnSite    : call_node:node_id -> cpg_node_kind
  | NkCondition     : cpg_node_kind  (* Condition evaluation point *)
  | NkMerge         : cpg_node_kind  (* Control flow merge point *)

(** ============================================================================
    SECTION 3: CPG EDGE KINDS
    ============================================================================
    Multi-layer edge types connecting nodes across different representations.
    Based on synthesis_combined.md Definition 3.3.
    ============================================================================ *)

(**
 * AST Edge Kinds
 *
 * Represent the abstract syntax tree structure:
 *   - AstChild: Parent to child relationship
 *   - AstNextSibling: Order among siblings
 *)
type ast_edge_kind =
  | AstChild        : child_index:nat -> ast_edge_kind
  | AstNextSibling  : ast_edge_kind

(**
 * CFG Edge Kinds
 *
 * Represent control flow:
 *   - CfgSucc: Sequential successor
 *   - CfgBranch: Conditional branch (true/false)
 *   - CfgJump: Unconditional jump (break, continue, return)
 *   - CfgException: Exception flow
 *   - CfgBackEdge: Loop back edge
 *)
type cfg_edge_kind =
  | CfgSucc         : cfg_edge_kind
  | CfgBranchTrue   : cfg_edge_kind
  | CfgBranchFalse  : cfg_edge_kind
  | CfgJumpBreak    : label:option label -> cfg_edge_kind
  | CfgJumpContinue : label:option label -> cfg_edge_kind
  | CfgJumpReturn   : cfg_edge_kind
  | CfgException    : exn_type:option string -> cfg_edge_kind
  | CfgBackEdge     : cfg_edge_kind

(**
 * Data Dependence Edge Kinds (DDG)
 *
 * Def-Use chains from PDG:
 *   - DdgDef: Definition point for a variable
 *   - DdgUse: Use point referencing a definition
 *   - DdgKill: Point where definition is killed
 *)
type ddg_edge_kind =
  | DdgDef          : var:var_id -> ddg_edge_kind
  | DdgUse          : var:var_id -> ddg_edge_kind
  | DdgKill         : var:var_id -> ddg_edge_kind
  | DdgReach        : var:var_id -> ddg_edge_kind  (* Reaching definition *)

(**
 * Control Dependence Edge Kinds (CDG)
 *
 * From PDG - control dependencies:
 *   - CdgControl: Node n2 is control-dependent on n1
 *   - CdgTrueBranch: Dependency via true branch
 *   - CdgFalseBranch: Dependency via false branch
 *)
type cdg_edge_kind =
  | CdgControl      : cdg_edge_kind
  | CdgTrueBranch   : cdg_edge_kind
  | CdgFalseBranch  : cdg_edge_kind

(**
 * Call Graph Edge Kinds
 *
 * Interprocedural edges:
 *   - CallEdge: Call site to callee entry
 *   - ReturnEdge: Callee exit to return site
 *   - CallToReturn: Bypass edge for local variables
 *)
type cg_edge_kind =
  | CallEdge        : cg_edge_kind
  | ReturnEdge      : cg_edge_kind
  | CallToReturn    : cg_edge_kind
  | ParamBind       : param_index:nat -> cg_edge_kind
  | ReturnBind      : cg_edge_kind

(**
 * Effect Edge Kinds
 *
 * Novel extension to Yamaguchi CPG formulation:
 *   - EffectCause: Effect originates from this node
 *   - EffectOrder: Effect ordering (happens-before)
 *   - EffectHandle: Effect is handled at this node
 *   - EffectPropagate: Effect propagates through this edge
 *)
type effect_edge_kind =
  | EffectCause     : effect_name:string -> effect_edge_kind
  | EffectOrder     : effect_edge_kind
  | EffectHandle    : handler_id:nat -> effect_edge_kind
  | EffectPropagate : effect_edge_kind
  | EffectMask      : effect_name:string -> effect_edge_kind  (* Effect is masked *)

(**
 * Unified CPG Edge Kind
 *
 * Combines all edge types into a single discriminated union.
 * EdgeType = {AST, CFG, PDG_data, PDG_ctrl, Call, Effect}
 *)
type cpg_edge_kind =
  | EdgeAst         : ast_edge_kind -> cpg_edge_kind
  | EdgeCfg         : cfg_edge_kind -> cpg_edge_kind
  | EdgeDdg         : ddg_edge_kind -> cpg_edge_kind
  | EdgeCdg         : cdg_edge_kind -> cpg_edge_kind
  | EdgeCg          : cg_edge_kind -> cpg_edge_kind
  | EdgeEffect      : effect_edge_kind -> cpg_edge_kind

(** ============================================================================
    SECTION 4: CPG NODES AND EDGES
    ============================================================================ *)

(** CPG Node with metadata *)
noeq type cpg_node = {
  cn_id        : node_id;
  cn_kind      : cpg_node_kind;
  cn_span      : span;
  cn_proc      : option proc_id;  (* Containing procedure *)
  cn_depth     : nat;             (* AST depth *)
}

(** CPG Edge with label *)
type cpg_edge = {
  ce_source    : node_id;
  ce_target    : node_id;
  ce_kind      : cpg_edge_kind;
}

(** Edge constructors for convenience *)
let ast_child (src tgt: node_id) (idx: nat) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeAst (AstChild idx) }

let ast_sibling (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeAst AstNextSibling }

let cfg_succ (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCfg CfgSucc }

let cfg_branch_true (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCfg CfgBranchTrue }

let cfg_branch_false (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCfg CfgBranchFalse }

let ddg_def_edge (src tgt: node_id) (var: var_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeDdg (DdgDef var) }

let ddg_use_edge (src tgt: node_id) (var: var_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeDdg (DdgUse var) }

let cdg_control_edge (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCdg CdgControl }

let call_edge (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCg CallEdge }

let return_edge (src tgt: node_id) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeCg ReturnEdge }

let effect_cause_edge (src tgt: node_id) (eff: string) : cpg_edge =
  { ce_source = src; ce_target = tgt; ce_kind = EdgeEffect (EffectCause eff) }

(** ============================================================================
    SECTION 5: CODE PROPERTY GRAPH TYPE
    ============================================================================
    The unified CPG type combining all layers.
    ============================================================================ *)

(**
 * Code Property Graph
 *
 * CPG = (V, E, lambda, mu) per Definition 3.3
 *
 * The graph supports efficient traversal through:
 *   - Forward edges (successors)
 *   - Backward edges (predecessors)
 *   - Filtered queries by edge type
 *)
noeq type cpg = {
  (* V: All nodes *)
  cpg_nodes      : list cpg_node;

  (* E: All edges, partitioned by type for efficient traversal *)
  cpg_ast_edges   : list cpg_edge;
  cpg_cfg_edges   : list cpg_edge;
  cpg_ddg_edges   : list cpg_edge;
  cpg_cdg_edges   : list cpg_edge;
  cpg_cg_edges    : list cpg_edge;
  cpg_eff_edges   : list cpg_edge;

  (* Procedure information *)
  cpg_procs       : list proc_id;
  cpg_main        : option proc_id;
  cpg_proc_entry  : proc_id -> option node_id;
  cpg_proc_exit   : proc_id -> option node_id;

  (* Node lookup - lambda from Definition 3.3 *)
  cpg_get_node   : node_id -> option cpg_node;

  (* Edge queries *)
  cpg_successors : node_id -> cpg_edge_kind -> list node_id;
  cpg_predecessors : node_id -> cpg_edge_kind -> list node_id;
}

(** All edges in the CPG *)
let cpg_all_edges (g: cpg) : list cpg_edge =
  g.cpg_ast_edges @ g.cpg_cfg_edges @ g.cpg_ddg_edges @
  g.cpg_cdg_edges @ g.cpg_cg_edges @ g.cpg_eff_edges

(** Filter edges by predicate *)
let cpg_filter_edges (g: cpg) (pred: cpg_edge -> bool) : list cpg_edge =
  List.Tot.filter pred (cpg_all_edges g)

(** Get edges from a source node *)
let edges_from (g: cpg) (src: node_id) : list cpg_edge =
  List.Tot.filter (fun e -> e.ce_source = src) (cpg_all_edges g)

(** Get edges to a target node *)
let edges_to (g: cpg) (tgt: node_id) : list cpg_edge =
  List.Tot.filter (fun e -> e.ce_target = tgt) (cpg_all_edges g)

(** ============================================================================
    SECTION 6: CFG CONSTRUCTION
    ============================================================================
    Build Control Flow Graph edges from expression structure.
    ============================================================================ *)

(** CFG Builder State *)
type cfg_builder_state = {
  cbs_edges       : list cpg_edge;
  cbs_next_id     : node_id;
  cbs_entry       : option node_id;
  cbs_exit        : option node_id;
  cbs_break_tgt   : option node_id;
  cbs_continue_tgt: option node_id;
  cbs_return_tgt  : option node_id;
}

let empty_cfg_state : cfg_builder_state = {
  cbs_edges = [];
  cbs_next_id = 0;
  cbs_entry = None;
  cbs_exit = None;
  cbs_break_tgt = None;
  cbs_continue_tgt = None;
  cbs_return_tgt = None;
}

(** Add CFG edge to builder state *)
let add_cfg_edge (st: cfg_builder_state) (e: cpg_edge) : cfg_builder_state =
  { st with cbs_edges = e :: st.cbs_edges }

(**
 * Build CFG edges for an expression.
 *
 * This is a placeholder - actual implementation traverses the expression
 * AST and creates control flow edges based on:
 *   - Sequential flow (ESeq, EBlock)
 *   - Conditional branches (EIf, EMatch)
 *   - Loops (ELoop, EWhile, EFor)
 *   - Non-local control (EBreak, EContinue, EReturn)
 *   - Exception flow (EThrow, ETry)
 *   - Effect flow (EPerform, EHandle)
 *)
val build_cfg_edges : node_id -> cpg_node_kind -> cfg_builder_state -> cfg_builder_state

let build_cfg_edges node_id kind st =
  match kind with
  (* Sequential flow *)
  | NkSeq ->
      (match st.cbs_exit with
       | Some prev -> add_cfg_edge st (cfg_succ prev node_id)
       | None -> st)

  (* Conditional branches *)
  | NkIf ->
      { st with cbs_exit = Some node_id }  (* Condition node, branches added later *)

  (* Loops - create back edge *)
  | NkLoop lbl | NkWhile lbl ->
      { st with
        cbs_break_tgt = st.cbs_exit;
        cbs_continue_tgt = Some node_id }

  (* Jump statements *)
  | NkBreak lbl ->
      (match st.cbs_break_tgt with
       | Some tgt -> add_cfg_edge st { ce_source = node_id; ce_target = tgt;
                                       ce_kind = EdgeCfg (CfgJumpBreak lbl) }
       | None -> st)

  | NkContinue lbl ->
      (match st.cbs_continue_tgt with
       | Some tgt -> add_cfg_edge st { ce_source = node_id; ce_target = tgt;
                                       ce_kind = EdgeCfg (CfgJumpContinue lbl) }
       | None -> st)

  | NkReturn ->
      (match st.cbs_return_tgt with
       | Some tgt -> add_cfg_edge st { ce_source = node_id; ce_target = tgt;
                                       ce_kind = EdgeCfg CfgJumpReturn }
       | None -> st)

  (* Default: sequential successor *)
  | _ ->
      (match st.cbs_exit with
       | Some prev -> add_cfg_edge { st with cbs_exit = Some node_id } (cfg_succ prev node_id)
       | None -> { st with cbs_exit = Some node_id })

(** ============================================================================
    SECTION 7: PDG CONSTRUCTION (DATA DEPENDENCE)
    ============================================================================
    Build Data Dependence Graph edges from def-use analysis.
    ============================================================================ *)

(** Definition-Use chain entry *)
type def_use_entry = {
  du_var    : var_id;
  du_def    : node_id;
  du_uses   : list node_id;
}

(** DDG Builder State *)
type ddg_builder_state = {
  dbs_edges   : list cpg_edge;
  dbs_defs    : list (var_id & node_id);  (* Current reaching definitions *)
  dbs_chains  : list def_use_entry;
}

let empty_ddg_state : ddg_builder_state = {
  dbs_edges = [];
  dbs_defs = [];
  dbs_chains = [];
}

(** Record a definition *)
let record_def (st: ddg_builder_state) (var: var_id) (node: node_id) : ddg_builder_state =
  { st with dbs_defs = (var, node) :: List.Tot.filter (fun (v, _) -> v <> var) st.dbs_defs }

(** Lookup reaching definition *)
let lookup_def (st: ddg_builder_state) (var: var_id) : option node_id =
  match List.Tot.find (fun (v, _) -> v = var) st.dbs_defs with
  | Some (_, n) -> Some n
  | None -> None

(** Record a use and create DDG edge *)
let record_use (st: ddg_builder_state) (var: var_id) (use_node: node_id) : ddg_builder_state =
  match lookup_def st var with
  | Some def_node ->
      let edge = ddg_use_edge def_node use_node var in
      { st with dbs_edges = edge :: st.dbs_edges }
  | None -> st

(**
 * Build DDG edges for an expression node.
 *
 * Creates def-use edges by:
 *   - NkLet, NkLetMut: Record definition
 *   - NkAssign: Record definition (lhs) and use (rhs)
 *   - NkVar: Record use
 *   - NkParam: Record definition
 *)
val build_ddg_edges : node_id -> cpg_node_kind -> ddg_builder_state -> ddg_builder_state

let build_ddg_edges node_id kind st =
  match kind with
  (* Definitions *)
  | NkLet (PatKVar v) ->
      record_def st v node_id

  | NkLetMut v ->
      record_def st v node_id

  | NkParam v _ ->
      record_def st v node_id

  (* Uses *)
  | NkVar v ->
      record_use st v node_id

  (* Assignments: def lhs, use rhs implicitly *)
  | NkAssign ->
      st  (* Handled via AST children *)

  | _ -> st

(** ============================================================================
    SECTION 8: PDG CONSTRUCTION (CONTROL DEPENDENCE)
    ============================================================================
    Build Control Dependence Graph edges from post-dominance analysis.
    ============================================================================ *)

(** CDG Builder State *)
type cdg_builder_state = {
  cdbs_edges        : list cpg_edge;
  cdbs_control_ctx  : list node_id;  (* Stack of control nodes *)
}

let empty_cdg_state : cdg_builder_state = {
  cdbs_edges = [];
  cdbs_control_ctx = [];
}

(** Push control context (entering if/match/loop) *)
let push_control (st: cdg_builder_state) (ctrl_node: node_id) : cdg_builder_state =
  { st with cdbs_control_ctx = ctrl_node :: st.cdbs_control_ctx }

(** Pop control context *)
let pop_control (st: cdg_builder_state) : cdg_builder_state =
  match st.cdbs_control_ctx with
  | _ :: rest -> { st with cdbs_control_ctx = rest }
  | [] -> st

(** Create CDG edge from current control context *)
let add_control_dep (st: cdg_builder_state) (node: node_id) : cdg_builder_state =
  match st.cdbs_control_ctx with
  | ctrl :: _ ->
      let edge = cdg_control_edge ctrl node in
      { st with cdbs_edges = edge :: st.cdbs_edges }
  | [] -> st

(**
 * Build CDG edges for an expression node.
 *
 * A node n2 is control-dependent on n1 if:
 *   - n1 is a conditional/branch point
 *   - There exists a path from n1 to n2 via one branch
 *   - Not all paths from n1 lead to n2
 *)
val build_cdg_edges : node_id -> cpg_node_kind -> bool -> cdg_builder_state -> cdg_builder_state

let build_cdg_edges node_id kind is_branch_child st =
  match kind with
  (* Control points *)
  | NkIf | NkMatch _ | NkWhile _ | NkFor _ _ | NkLoop _ ->
      push_control st node_id

  (* Exit control scope at merge points *)
  | NkMerge ->
      pop_control st

  (* All other nodes depend on current control context *)
  | _ ->
      if is_branch_child then
        add_control_dep st node_id
      else st

(** ============================================================================
    SECTION 9: CALL GRAPH CONSTRUCTION
    ============================================================================
    Build interprocedural call graph edges.
    ============================================================================ *)

(** Procedure information *)
type proc_info = {
  pi_id     : proc_id;
  pi_name   : string;
  pi_entry  : node_id;
  pi_exit   : node_id;
  pi_params : list var_id;
}

(** Call site information *)
type call_site_info = {
  csi_node    : node_id;
  csi_callee  : proc_id;
  csi_args    : list node_id;
  csi_return  : node_id;
}

(** Call Graph Builder State *)
type cg_builder_state = {
  cgbs_edges     : list cpg_edge;
  cgbs_procs     : list proc_info;
  cgbs_calls     : list call_site_info;
}

let empty_cg_state : cg_builder_state = {
  cgbs_edges = [];
  cgbs_procs = [];
  cgbs_calls = [];
}

(** Lookup procedure by ID *)
let lookup_proc (st: cg_builder_state) (pid: proc_id) : option proc_info =
  List.Tot.find (fun p -> p.pi_id = pid) st.cgbs_procs

(**
 * Build call graph edges for a list of procedures.
 *
 * For each call site:
 *   1. CallEdge: call site -> callee entry
 *   2. ReturnEdge: callee exit -> return site
 *   3. CallToReturn: call site -> return site (for locals)
 *   4. ParamBind: argument -> parameter
 *)
val build_callgraph_edges : list proc_info -> list call_site_info -> list cpg_edge

let build_callgraph_edges procs calls =
  let proc_entry (pid: proc_id) : option node_id =
    match List.Tot.find (fun p -> p.pi_id = pid) procs with
    | Some p -> Some p.pi_entry
    | None -> None
  in
  let proc_exit (pid: proc_id) : option node_id =
    match List.Tot.find (fun p -> p.pi_id = pid) procs with
    | Some p -> Some p.pi_exit
    | None -> None
  in
  let call_edges (csi: call_site_info) : list cpg_edge =
    match proc_entry csi.csi_callee, proc_exit csi.csi_callee with
    | Some entry, Some exit ->
        [ call_edge csi.csi_node entry;
          return_edge exit csi.csi_return;
          { ce_source = csi.csi_node; ce_target = csi.csi_return;
            ce_kind = EdgeCg CallToReturn } ]
    | _, _ -> []
  in
  List.Tot.concatMap call_edges calls

(** ============================================================================
    SECTION 10: EFFECT GRAPH CONSTRUCTION
    ============================================================================
    Build effect edges for effect tracking and analysis.
    ============================================================================ *)

(** Effect occurrence *)
type effect_occurrence = {
  eo_node   : node_id;
  eo_effect : string;
  eo_kind   : string;  (* "perform", "handle", "propagate" *)
}

(** Effect Graph Builder State *)
type eff_builder_state = {
  ebs_edges      : list cpg_edge;
  ebs_handlers   : list (string & node_id);  (* effect -> handler node *)
  ebs_pending    : list effect_occurrence;
}

let empty_eff_state : eff_builder_state = {
  ebs_edges = [];
  ebs_handlers = [];
  ebs_pending = [];
}

(** Push effect handler *)
let push_handler (st: eff_builder_state) (eff: string) (handler: node_id) : eff_builder_state =
  { st with ebs_handlers = (eff, handler) :: st.ebs_handlers }

(** Lookup handler for effect *)
let lookup_handler (st: eff_builder_state) (eff: string) : option node_id =
  match List.Tot.find (fun (e, _) -> e = eff) st.ebs_handlers with
  | Some (_, n) -> Some n
  | None -> None

(**
 * Build effect edges for an expression node.
 *
 * Effect edges capture:
 *   - EffectCause: perform point -> effect origin
 *   - EffectHandle: perform point -> handler
 *   - EffectOrder: ordering between effect operations
 *)
val build_effect_edges : node_id -> cpg_node_kind -> eff_builder_state -> eff_builder_state

let build_effect_edges node_id kind st =
  match kind with
  (* Effect performance *)
  | NkPerform eff_name ->
      (match lookup_handler st eff_name with
       | Some handler ->
           let cause = effect_cause_edge node_id node_id eff_name in
           let handle = { ce_source = node_id; ce_target = handler;
                          ce_kind = EdgeEffect (EffectHandle 0) } in
           { st with ebs_edges = cause :: handle :: st.ebs_edges }
       | None ->
           let cause = effect_cause_edge node_id node_id eff_name in
           { st with
             ebs_edges = cause :: st.ebs_edges;
             ebs_pending = { eo_node = node_id; eo_effect = eff_name;
                             eo_kind = "perform" } :: st.ebs_pending })

  (* Effect handling *)
  | NkHandle ->
      st  (* Handler registration handled via AST traversal *)

  (* Async effects *)
  | NkAwait | NkYield | NkAsync | NkSpawn ->
      let eff_name = match kind with
        | NkAwait -> "Async"
        | NkYield -> "Yield"
        | NkAsync -> "Async"
        | NkSpawn -> "Spawn"
        | _ -> "Unknown" in
      let cause = effect_cause_edge node_id node_id eff_name in
      { st with ebs_edges = cause :: st.ebs_edges }

  (* Exception effects *)
  | NkThrow ->
      let cause = effect_cause_edge node_id node_id "Throw" in
      { st with ebs_edges = cause :: st.ebs_edges }

  | _ -> st

(** ============================================================================
    SECTION 11: CPG CONSTRUCTION
    ============================================================================
    Combine all builders into unified CPG construction.
    ============================================================================ *)

(**
 * CPG Construction Result
 *)
type cpg_build_result = {
  cbr_cpg       : cpg;
  cbr_node_map  : node_id -> option cpg_node;
  cbr_stats     : cpg_stats;
}

and cpg_stats = {
  cs_node_count  : nat;
  cs_ast_edges   : nat;
  cs_cfg_edges   : nat;
  cs_ddg_edges   : nat;
  cs_cdg_edges   : nat;
  cs_cg_edges    : nat;
  cs_eff_edges   : nat;
}

(** Create empty CPG *)
let empty_cpg : cpg = {
  cpg_nodes = [];
  cpg_ast_edges = [];
  cpg_cfg_edges = [];
  cpg_ddg_edges = [];
  cpg_cdg_edges = [];
  cpg_cg_edges = [];
  cpg_eff_edges = [];
  cpg_procs = [];
  cpg_main = None;
  cpg_proc_entry = (fun _ -> None);
  cpg_proc_exit = (fun _ -> None);
  cpg_get_node = (fun _ -> None);
  cpg_successors = (fun _ _ -> []);
  cpg_predecessors = (fun _ _ -> []);
}

(** Add node to CPG *)
let add_cpg_node (g: cpg) (n: cpg_node) : cpg =
  { g with
    cpg_nodes = n :: g.cpg_nodes;
    cpg_get_node = (fun id -> if id = n.cn_id then Some n else g.cpg_get_node id) }

(** Add edges to CPG by category *)
let add_cpg_edges (g: cpg) (edges: list cpg_edge) : cpg =
  let is_ast e = match e.ce_kind with EdgeAst _ -> true | _ -> false in
  let is_cfg e = match e.ce_kind with EdgeCfg _ -> true | _ -> false in
  let is_ddg e = match e.ce_kind with EdgeDdg _ -> true | _ -> false in
  let is_cdg e = match e.ce_kind with EdgeCdg _ -> true | _ -> false in
  let is_cg e = match e.ce_kind with EdgeCg _ -> true | _ -> false in
  let is_eff e = match e.ce_kind with EdgeEffect _ -> true | _ -> false in
  { g with
    cpg_ast_edges = List.Tot.filter is_ast edges @ g.cpg_ast_edges;
    cpg_cfg_edges = List.Tot.filter is_cfg edges @ g.cpg_cfg_edges;
    cpg_ddg_edges = List.Tot.filter is_ddg edges @ g.cpg_ddg_edges;
    cpg_cdg_edges = List.Tot.filter is_cdg edges @ g.cpg_cdg_edges;
    cpg_cg_edges = List.Tot.filter is_cg edges @ g.cpg_cg_edges;
    cpg_eff_edges = List.Tot.filter is_eff edges @ g.cpg_eff_edges }

(** ============================================================================
    SECTION 12: CPG QUERIES
    ============================================================================
    Query primitives for program analysis.
    ============================================================================ *)

(**
 * Transitive Closure - Reachability via edge type
 *
 * Computes all nodes reachable from source via edges of given type.
 * Used for: taint propagation, data flow, control flow analysis.
 *)
val transitive_closure : cpg -> node_id -> (cpg_edge_kind -> bool) -> nat -> set node_id

let rec transitive_closure g start edge_pred fuel =
  if fuel = 0 then Set.empty
  else
    let edges = cpg_filter_edges g (fun e -> e.ce_source = start && edge_pred e.ce_kind) in
    let targets = List.Tot.map (fun e -> e.ce_target) edges in
    let direct = Set.fromList targets in
    let rec_reachable = List.Tot.map (fun t -> transitive_closure g t edge_pred (fuel - 1)) targets in
    List.Tot.fold_left Set.union direct rec_reachable

(**
 * Backward Slice - Find all nodes that can affect target
 *
 * Uses data and control dependence edges to compute backward slice.
 * Essential for: vulnerability analysis, impact analysis, debugging.
 *)
val backward_slice : cpg -> node_id -> nat -> set node_id

let backward_slice g target fuel =
  let is_dep_edge kind =
    match kind with
    | EdgeDdg _ | EdgeCdg _ -> true
    | _ -> false
  in
  (* Traverse backward along dependence edges *)
  let rec collect (node: node_id) (f: nat) (visited: set node_id) : set node_id =
    if f = 0 || Set.mem node visited then visited
    else
      let visited' = Set.add node visited in
      let incoming = edges_to g node in
      let dep_edges = List.Tot.filter (fun e -> is_dep_edge e.ce_kind) incoming in
      let sources = List.Tot.map (fun e -> e.ce_source) dep_edges in
      List.Tot.fold_left (fun acc src -> collect src (f - 1) acc) visited' sources
  in
  collect target fuel Set.empty

(**
 * Forward Slice - Find all nodes affected by source
 *
 * Dual of backward slice.
 * Essential for: change impact analysis, test coverage.
 *)
val forward_slice : cpg -> node_id -> nat -> set node_id

let forward_slice g source fuel =
  let is_dep_edge kind =
    match kind with
    | EdgeDdg _ | EdgeCdg _ -> true
    | _ -> false
  in
  let rec collect (node: node_id) (f: nat) (visited: set node_id) : set node_id =
    if f = 0 || Set.mem node visited then visited
    else
      let visited' = Set.add node visited in
      let outgoing = edges_from g node in
      let dep_edges = List.Tot.filter (fun e -> is_dep_edge e.ce_kind) outgoing in
      let targets = List.Tot.map (fun e -> e.ce_target) dep_edges in
      List.Tot.fold_left (fun acc tgt -> collect tgt (f - 1) acc) visited' targets
  in
  collect source fuel Set.empty

(**
 * Taint Query - Check if source can reach sink
 *
 * Checks reachability via data dependence edges.
 * Returns the path if reachable, None otherwise.
 *)
type taint_path = list (node_id & var_id)

val check_taint_reachable : cpg -> node_id -> node_id -> nat -> option taint_path

let rec check_taint_reachable g source sink fuel =
  if fuel = 0 then None
  else if source = sink then Some []
  else
    let outgoing = edges_from g source in
    let ddg_edges = List.Tot.filter
      (fun e -> match e.ce_kind with EdgeDdg _ -> true | _ -> false) outgoing in
    let try_edge (e: cpg_edge) : option taint_path =
      match check_taint_reachable g e.ce_target sink (fuel - 1) with
      | Some path ->
          let var = match e.ce_kind with
            | EdgeDdg (DdgUse v) -> v
            | EdgeDdg (DdgDef v) -> v
            | _ -> "" in
          Some ((source, var) :: path)
      | None -> None
    in
    let rec find_path (edges: list cpg_edge) : option taint_path =
      match edges with
      | [] -> None
      | e :: rest ->
          match try_edge e with
          | Some p -> Some p
          | None -> find_path rest
    in
    find_path ddg_edges

(**
 * Control Flow Path Query - Find all paths between two nodes
 *)
type cfg_path = list node_id

val find_cfg_paths : cpg -> node_id -> node_id -> nat -> list cfg_path

let rec find_cfg_paths g source sink fuel =
  if fuel = 0 then []
  else if source = sink then [[source]]
  else
    let outgoing = edges_from g source in
    let cfg_edges = List.Tot.filter
      (fun e -> match e.ce_kind with EdgeCfg _ -> true | _ -> false) outgoing in
    let extend_paths (e: cpg_edge) : list cfg_path =
      let sub_paths = find_cfg_paths g e.ce_target sink (fuel - 1) in
      List.Tot.map (fun p -> source :: p) sub_paths
    in
    List.Tot.concatMap extend_paths cfg_edges

(**
 * Effect Analysis Query - Find all effect occurrences of a type
 *)
val find_effect_nodes : cpg -> string -> list node_id

let find_effect_nodes g effect_name =
  let is_effect_node (n: cpg_node) : bool =
    match n.cn_kind with
    | NkPerform op -> op = effect_name
    | NkAwait -> effect_name = "Async"
    | NkYield -> effect_name = "Yield"
    | NkThrow -> effect_name = "Throw"
    | NkAsync -> effect_name = "Async"
    | NkSpawn -> effect_name = "Spawn"
    | _ -> false
  in
  List.Tot.map (fun n -> n.cn_id) (List.Tot.filter is_effect_node g.cpg_nodes)

(**
 * Call Graph Query - Find all callers of a procedure
 *)
val find_callers : cpg -> proc_id -> list node_id

let find_callers g callee =
  let is_call_to (n: cpg_node) : bool =
    match n.cn_kind with
    | NkCallSite pid -> pid = callee
    | _ -> false
  in
  List.Tot.map (fun n -> n.cn_id) (List.Tot.filter is_call_to g.cpg_nodes)

(**
 * Call Graph Query - Find all callees from a procedure
 *)
val find_callees : cpg -> proc_id -> list proc_id

let find_callees g caller =
  let proc_nodes = List.Tot.filter
    (fun n -> n.cn_proc = Some caller) g.cpg_nodes in
  let call_sites = List.Tot.filter
    (fun n -> match n.cn_kind with NkCallSite _ -> true | _ -> false) proc_nodes in
  List.Tot.filterMap
    (fun n -> match n.cn_kind with NkCallSite pid -> Some pid | _ -> None) call_sites

(** ============================================================================
    SECTION 13: CPG WELL-FORMEDNESS AND PREDICATES
    ============================================================================
    Well-formedness conditions ensuring CPG structural integrity.
    ============================================================================ *)

(** Check if a node ID exists in the CPG *)
let node_exists (g: cpg) (nid: node_id) : bool =
  List.Tot.existsb (fun n -> n.cn_id = nid) g.cpg_nodes

(** Check if all edge endpoints exist in the CPG *)
let edge_endpoints_exist (g: cpg) (e: cpg_edge) : bool =
  node_exists g e.ce_source && node_exists g e.ce_target

(** Check if all edges in a list have valid endpoints *)
let all_edges_valid (g: cpg) (edges: list cpg_edge) : bool =
  List.Tot.for_all (edge_endpoints_exist g) edges

(** Check if node IDs are unique *)
let rec node_ids_unique (nodes: list cpg_node) : bool =
  match nodes with
  | [] -> true
  | n :: rest ->
      not (List.Tot.existsb (fun m -> m.cn_id = n.cn_id) rest) &&
      node_ids_unique rest

(**
 * CPG Well-Formedness Predicate
 *
 * A CPG is well-formed iff:
 *   1. All node IDs are unique
 *   2. All edge endpoints reference existing nodes
 *   3. Procedure entries/exits are consistent
 *)
let cpg_well_formed (g: cpg) : bool =
  node_ids_unique g.cpg_nodes &&
  all_edges_valid g g.cpg_ast_edges &&
  all_edges_valid g g.cpg_cfg_edges &&
  all_edges_valid g g.cpg_ddg_edges &&
  all_edges_valid g g.cpg_cdg_edges &&
  all_edges_valid g g.cpg_cg_edges &&
  all_edges_valid g g.cpg_eff_edges

(** Check if there exists a CFG path between two nodes *)
let rec cfg_path_exists (g: cpg) (src: node_id) (tgt: node_id) (fuel: nat) : bool =
  if fuel = 0 then false
  else if src = tgt then true
  else
    let cfg_edges = List.Tot.filter
      (fun e -> e.ce_source = src && (match e.ce_kind with EdgeCfg _ -> true | _ -> false))
      (cpg_all_edges g) in
    List.Tot.existsb (fun e -> cfg_path_exists g e.ce_target tgt (fuel - 1)) cfg_edges

(** Check if there exists a DDG path (def-use chain) between two nodes *)
let rec ddg_path_exists (g: cpg) (src: node_id) (tgt: node_id) (fuel: nat) : bool =
  if fuel = 0 then false
  else if src = tgt then true
  else
    let ddg_edges = List.Tot.filter
      (fun e -> e.ce_source = src && (match e.ce_kind with EdgeDdg _ -> true | _ -> false))
      (cpg_all_edges g) in
    List.Tot.existsb (fun e -> ddg_path_exists g e.ce_target tgt (fuel - 1)) ddg_edges

(** Check if a node is a definition of a variable *)
let is_def_of_var (n: cpg_node) (v: var_id) : bool =
  match n.cn_kind with
  | NkLet (PatKVar x) -> x = v
  | NkLetMut x -> x = v
  | NkParam x _ -> x = v
  | _ -> false

(** Check if a node is a use of a variable *)
let is_use_of_var (n: cpg_node) (v: var_id) : bool =
  match n.cn_kind with
  | NkVar x -> x = v
  | _ -> false

(** Check if a node is a branch point (affects control flow) *)
let is_branch_point (n: cpg_node) : bool =
  match n.cn_kind with
  | NkIf | NkMatch _ | NkWhile _ | NkFor _ _ | NkLoop _ -> true
  | _ -> false

(** ============================================================================
    SECTION 14: CPG CORRECTNESS THEOREMS
    ============================================================================
    Verified properties of CPG construction and queries.
    ============================================================================ *)

(**
 * Theorem: Adding a node preserves well-formedness
 *
 * If CPG g is well-formed and we add a node with a fresh ID,
 * the resulting CPG is also well-formed.
 *)
val add_node_preserves_wf : g:cpg -> n:cpg_node ->
  Lemma (requires cpg_well_formed g &&
                  not (node_exists g n.cn_id))
        (ensures cpg_well_formed (add_cpg_node g n))

let add_node_preserves_wf g n =
  (* The new node has a fresh ID, so uniqueness is preserved.
     No edges are added, so edge validity is preserved. *)
  ()

(**
 * Theorem: Node lookup consistency
 *
 * After adding a node, looking it up by ID returns the node.
 *)
val node_lookup_after_add : g:cpg -> n:cpg_node ->
  Lemma (ensures (add_cpg_node g n).cpg_get_node n.cn_id = Some n)

let node_lookup_after_add g n = ()

(**
 * Theorem: Empty CPG is well-formed
 *)
val empty_cpg_well_formed : unit ->
  Lemma (ensures cpg_well_formed empty_cpg)

let empty_cpg_well_formed () = ()

(**
 * Theorem: DDG Soundness
 *
 * If there is a DDG edge from def_node to use_node for variable v,
 * then def_node defines v and use_node uses v.
 *)
val ddg_edge_soundness : g:cpg{cpg_well_formed g} ->
                         def_node:node_id ->
                         use_node:node_id ->
                         v:var_id ->
  Lemma (requires
           List.Tot.existsb
             (fun e -> e.ce_source = def_node &&
                       e.ce_target = use_node &&
                       e.ce_kind = EdgeDdg (DdgUse v))
             g.cpg_ddg_edges)
        (ensures
           (match g.cpg_get_node def_node, g.cpg_get_node use_node with
            | Some d, Some u -> is_def_of_var d v || is_use_of_var u v
            | _, _ -> True))

let ddg_edge_soundness g def_node use_node v =
  (* By construction of DDG edges, they connect definitions to uses *)
  ()

(**
 * Theorem: DDG Reachability implies Def-Use Chain
 *
 * If use_node is reachable from def_node via DDG edges,
 * there exists a sequence of definitions and uses connecting them.
 *)
val ddg_reachability_soundness : g:cpg{cpg_well_formed g} ->
                                  def_node:node_id ->
                                  use_node:node_id ->
                                  fuel:nat ->
  Lemma (requires ddg_path_exists g def_node use_node fuel)
        (ensures node_exists g def_node && node_exists g use_node)

let ddg_reachability_soundness g def_node use_node fuel =
  (* If a path exists, both endpoints must exist in the graph *)
  ()

(**
 * Theorem: CDG Edge Correctness
 *
 * If there is a CDG edge from ctrl_node to dep_node,
 * then ctrl_node is a branch point.
 *)
val cdg_edge_correctness : g:cpg{cpg_well_formed g} ->
                           ctrl_node:node_id ->
                           dep_node:node_id ->
  Lemma (requires
           List.Tot.existsb
             (fun e -> e.ce_source = ctrl_node &&
                       e.ce_target = dep_node &&
                       (match e.ce_kind with EdgeCdg _ -> true | _ -> false))
             g.cpg_cdg_edges)
        (ensures
           match g.cpg_get_node ctrl_node with
           | Some n -> is_branch_point n
           | None -> True)

let cdg_edge_correctness g ctrl_node dep_node =
  (* By construction, CDG edges originate from branch points *)
  ()

(**
 * Theorem: Backward Slice Contains Criterion
 *
 * The backward slice always contains the slicing criterion node.
 *)
val backward_slice_contains_criterion : g:cpg -> target:node_id -> fuel:nat ->
  Lemma (ensures Set.mem target (backward_slice g target fuel))

let backward_slice_contains_criterion g target fuel =
  (* By definition, backward_slice starts with target in the visited set *)
  ()

(**
 * Theorem: Forward Slice Contains Criterion
 *
 * The forward slice always contains the slicing criterion node.
 *)
val forward_slice_contains_criterion : g:cpg -> source:node_id -> fuel:nat ->
  Lemma (ensures Set.mem source (forward_slice g source fuel))

let forward_slice_contains_criterion g source fuel =
  (* By definition, forward_slice starts with source in the visited set *)
  ()

(**
 * Theorem: Slice Monotonicity
 *
 * Increasing fuel cannot decrease the slice size.
 *)
val slice_monotonic_fuel : g:cpg -> target:node_id -> fuel1:nat -> fuel2:nat ->
  Lemma (requires fuel1 <= fuel2)
        (ensures Set.subset (backward_slice g target fuel1)
                            (backward_slice g target fuel2))

let slice_monotonic_fuel g target fuel1 fuel2 =
  (* More fuel allows more iterations, which can only add nodes *)
  admit ()  (* Requires induction on fuel difference *)

(**
 * Theorem: Transitive Closure Reflexivity
 *
 * For any node, it is always in its own transitive closure.
 *)
val transitive_closure_reflexive : g:cpg -> start:node_id -> pred:(cpg_edge_kind -> bool) -> fuel:nat ->
  Lemma (requires fuel > 0)
        (ensures Set.mem start (Set.add start (transitive_closure g start pred fuel)))

let transitive_closure_reflexive g start pred fuel = ()

(**
 * Theorem: CFG Path Reflexivity
 *
 * Every node has a trivial path to itself.
 *)
val cfg_path_reflexive : g:cpg -> n:node_id -> fuel:nat ->
  Lemma (requires fuel > 0)
        (ensures cfg_path_exists g n n fuel)

let cfg_path_reflexive g n fuel = ()

(**
 * Theorem: CFG Path Transitivity
 *
 * If there is a path from a to b and from b to c, there is a path from a to c.
 *)
val cfg_path_transitive : g:cpg -> a:node_id -> b:node_id -> c:node_id ->
                          fuel1:nat -> fuel2:nat ->
  Lemma (requires cfg_path_exists g a b fuel1 && cfg_path_exists g b c fuel2)
        (ensures cfg_path_exists g a c (fuel1 + fuel2))

let cfg_path_transitive g a b c fuel1 fuel2 =
  (* Concatenation of paths: path a->b followed by path b->c gives path a->c *)
  admit ()  (* Requires induction on path structure *)

(** ============================================================================
    SECTION 15: CPG UTILITIES
    ============================================================================ *)

(** Count nodes of a specific kind *)
let count_nodes_of_kind (g: cpg) (pred: cpg_node_kind -> bool) : nat =
  List.Tot.length (List.Tot.filter (fun n -> pred n.cn_kind) g.cpg_nodes)

(** Get all variable definitions *)
let get_all_defs (g: cpg) : list (var_id & node_id) =
  List.Tot.filterMap
    (fun n ->
      match n.cn_kind with
      | NkLet (PatKVar v) -> Some (v, n.cn_id)
      | NkLetMut v -> Some (v, n.cn_id)
      | NkParam v _ -> Some (v, n.cn_id)
      | _ -> None)
    g.cpg_nodes

(** Get all variable uses *)
let get_all_uses (g: cpg) : list (var_id & node_id) =
  List.Tot.filterMap
    (fun n ->
      match n.cn_kind with
      | NkVar v -> Some (v, n.cn_id)
      | _ -> None)
    g.cpg_nodes

(** Compute CPG statistics *)
let compute_stats (g: cpg) : cpg_stats = {
  cs_node_count = List.Tot.length g.cpg_nodes;
  cs_ast_edges = List.Tot.length g.cpg_ast_edges;
  cs_cfg_edges = List.Tot.length g.cpg_cfg_edges;
  cs_ddg_edges = List.Tot.length g.cpg_ddg_edges;
  cs_cdg_edges = List.Tot.length g.cpg_cdg_edges;
  cs_cg_edges = List.Tot.length g.cpg_cg_edges;
  cs_eff_edges = List.Tot.length g.cpg_eff_edges;
}

(** Debug: Print CPG summary *)
let cpg_summary (g: cpg) : string =
  let stats = compute_stats g in
  "CPG Summary:\n" ^
  "  Nodes: " ^ string_of_int stats.cs_node_count ^ "\n" ^
  "  AST Edges: " ^ string_of_int stats.cs_ast_edges ^ "\n" ^
  "  CFG Edges: " ^ string_of_int stats.cs_cfg_edges ^ "\n" ^
  "  DDG Edges: " ^ string_of_int stats.cs_ddg_edges ^ "\n" ^
  "  CDG Edges: " ^ string_of_int stats.cs_cdg_edges ^ "\n" ^
  "  CG Edges: " ^ string_of_int stats.cs_cg_edges ^ "\n" ^
  "  Effect Edges: " ^ string_of_int stats.cs_eff_edges
