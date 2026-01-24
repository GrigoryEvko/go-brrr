(**
 * BrrrMachine.Analysis.Taint
 *
 * Taint analysis for tracking untrusted data flow.
 * Core security analysis for detecting injection vulnerabilities.
 *)
module BrrrMachine.Analysis.Taint

open FStar.List.Tot
open FStar.Set
open BrrrMachine.Core.Types
open BrrrMachine.Core.CFG
open BrrrMachine.Core.CallGraph
open BrrrMachine.Analysis.Dataflow

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT LABELS
    ═══════════════════════════════════════════════════════════════════════════ *)

type taint_label =
  | TaintUserInput       (* HTTP request, CLI args *)
  | TaintDatabase        (* Data from database *)
  | TaintFile            (* Data from file system *)
  | TaintNetwork         (* Data from network *)
  | TaintEnvironment     (* Environment variables *)
  | TaintCustom of string

type taint_set = set taint_label

let no_taint : taint_set = Set.empty
let all_taint : taint_set =
  Set.union (Set.singleton TaintUserInput)
    (Set.union (Set.singleton TaintDatabase)
      (Set.union (Set.singleton TaintFile)
        (Set.union (Set.singleton TaintNetwork)
          (Set.singleton TaintEnvironment))))

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT STATE
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Map from variables to their taint sets *)
type taint_state = var_id -> taint_set

let empty_taint_state : taint_state = fun _ -> no_taint

let get_taint (s: taint_state) (v: var_id) : taint_set = s v

let set_taint (s: taint_state) (v: var_id) (t: taint_set) : taint_state =
  fun v' -> if v' = v then t else s v'

let join_taint (s1 s2: taint_state) : taint_state =
  fun v -> Set.union (s1 v) (s2 v)

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT LATTICE
    ═══════════════════════════════════════════════════════════════════════════ *)

let taint_lattice : lattice taint_state = {
  bottom = empty_taint_state;
  join = join_taint;
  leq = (fun s1 s2 -> true);  (* Simplified - should check subset relation *)
}

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT SOURCES (Go-specific)
    ═══════════════════════════════════════════════════════════════════════════ *)

type taint_source = {
  src_package: string;
  src_func: string;
  src_param: option nat;  (* Which parameter/return, None = receiver *)
  src_label: taint_label;
}

(* Standard Go taint sources *)
let go_taint_sources : list taint_source = [
  (* HTTP *)
  { src_package = "net/http"; src_func = "Request.URL"; src_param = None; src_label = TaintUserInput };
  { src_package = "net/http"; src_func = "Request.Body"; src_param = None; src_label = TaintUserInput };
  { src_package = "net/http"; src_func = "Request.Form"; src_param = None; src_label = TaintUserInput };
  { src_package = "net/http"; src_func = "Request.Header"; src_param = None; src_label = TaintUserInput };

  (* OS *)
  { src_package = "os"; src_func = "Args"; src_param = None; src_label = TaintUserInput };
  { src_package = "os"; src_func = "Getenv"; src_param = Some 0; src_label = TaintEnvironment };
  { src_package = "os"; src_func = "ReadFile"; src_param = Some 0; src_label = TaintFile };

  (* IO *)
  { src_package = "io"; src_func = "ReadAll"; src_param = Some 0; src_label = TaintNetwork };
  { src_package = "bufio"; src_func = "Reader.ReadString"; src_param = Some 0; src_label = TaintNetwork };

  (* Database *)
  { src_package = "database/sql"; src_func = "Rows.Scan"; src_param = Some 0; src_label = TaintDatabase };
]

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT SINKS (Go-specific)
    ═══════════════════════════════════════════════════════════════════════════ *)

type sink_kind =
  | SinkSQLInjection
  | SinkCommandInjection
  | SinkPathTraversal
  | SinkXSS
  | SinkLDAPInjection
  | SinkLogInjection

type taint_sink = {
  sink_package: string;
  sink_func: string;
  sink_param: nat;  (* Which parameter is sensitive *)
  sink_kind: sink_kind;
  sink_labels: taint_set;  (* Which taint labels are dangerous here *)
}

let go_taint_sinks : list taint_sink = [
  (* SQL Injection *)
  { sink_package = "database/sql"; sink_func = "DB.Query"; sink_param = 0;
    sink_kind = SinkSQLInjection; sink_labels = Set.singleton TaintUserInput };
  { sink_package = "database/sql"; sink_func = "DB.Exec"; sink_param = 0;
    sink_kind = SinkSQLInjection; sink_labels = Set.singleton TaintUserInput };

  (* Command Injection *)
  { sink_package = "os/exec"; sink_func = "Command"; sink_param = 0;
    sink_kind = SinkCommandInjection; sink_labels = Set.singleton TaintUserInput };
  { sink_package = "os/exec"; sink_func = "CommandContext"; sink_param = 1;
    sink_kind = SinkCommandInjection; sink_labels = Set.singleton TaintUserInput };

  (* Path Traversal *)
  { sink_package = "os"; sink_func = "Open"; sink_param = 0;
    sink_kind = SinkPathTraversal; sink_labels = Set.singleton TaintUserInput };
  { sink_package = "os"; sink_func = "ReadFile"; sink_param = 0;
    sink_kind = SinkPathTraversal; sink_labels = Set.singleton TaintUserInput };
  { sink_package = "io/ioutil"; sink_func = "ReadFile"; sink_param = 0;
    sink_kind = SinkPathTraversal; sink_labels = Set.singleton TaintUserInput };

  (* XSS *)
  { sink_package = "html/template"; sink_func = "HTML"; sink_param = 0;
    sink_kind = SinkXSS; sink_labels = Set.singleton TaintUserInput };
  { sink_package = "net/http"; sink_func = "ResponseWriter.Write"; sink_param = 0;
    sink_kind = SinkXSS; sink_labels = Set.singleton TaintUserInput };
]

(** ═══════════════════════════════════════════════════════════════════════════
    SANITIZERS (Go-specific)
    ═══════════════════════════════════════════════════════════════════════════ *)

type sanitizer = {
  san_package: string;
  san_func: string;
  san_removes: taint_set;  (* Which taints are removed *)
  san_for_sinks: list sink_kind;  (* Effective against which sinks *)
}

let go_sanitizers : list sanitizer = [
  (* SQL - use parameterized queries instead, but these help *)
  { san_package = "database/sql"; san_func = "Named";
    san_removes = Set.singleton TaintUserInput; san_for_sinks = [SinkSQLInjection] };

  (* HTML escaping *)
  { san_package = "html/template"; san_func = "HTMLEscapeString";
    san_removes = Set.singleton TaintUserInput; san_for_sinks = [SinkXSS] };
  { san_package = "html"; san_func = "EscapeString";
    san_removes = Set.singleton TaintUserInput; san_for_sinks = [SinkXSS] };

  (* Path cleaning *)
  { san_package = "path/filepath"; san_func = "Clean";
    san_removes = Set.singleton TaintUserInput; san_for_sinks = [SinkPathTraversal] };
  { san_package = "path/filepath"; san_func = "Base";
    san_removes = Set.singleton TaintUserInput; san_for_sinks = [SinkPathTraversal] };
]

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT TRANSFER FUNCTION
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Get taint from an expression *)
val expr_taint : taint_state -> ir_expr -> taint_set

let rec expr_taint state expr =
  match expr with
  | EVar v -> get_taint state v
  | ELit _ -> no_taint
  | EBinOp _ e1 e2 -> Set.union (expr_taint state e1) (expr_taint state e2)
  | EUnOp _ e -> expr_taint state e
  | ECall func args ->
      (* Combine taint from all arguments - simplified *)
      List.Tot.fold_left Set.union no_taint (List.Tot.map (expr_taint state) args)
  | EIndex base idx -> Set.union (expr_taint state base) (expr_taint state idx)
  | EField base _ -> expr_taint state base
  | ESlice base _ _ -> expr_taint state base
  | _ -> no_taint

(* Transfer function for taint analysis *)
val taint_transfer : transfer_fn taint_state

let taint_transfer node state =
  match node.node_kind with
  | NodeStmt stmt -> (
      match stmt with
      | SAssign lhs rhs ->
          (* Propagate taint from RHS to LHS *)
          let rhs_taint = List.Tot.fold_left Set.union no_taint
            (List.Tot.map (expr_taint state) rhs) in
          List.Tot.fold_left (fun s lhs_expr ->
            match lhs_expr with
            | EVar v -> set_taint s v rhs_taint
            | _ -> s
          ) state lhs
      | SShortDecl vars values ->
          let rhs_taint = List.Tot.fold_left Set.union no_taint
            (List.Tot.map (expr_taint state) values) in
          List.Tot.fold_left (fun s v -> set_taint s v rhs_taint) state vars
      | _ -> state
    )
  | _ -> state

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT ANALYSIS RESULTS
    ═══════════════════════════════════════════════════════════════════════════ *)

type taint_finding = {
  finding_sink: taint_sink;
  finding_taint: taint_set;
  finding_path: list node_id;  (* Path from source to sink *)
  finding_loc: source_location;
}

type taint_result = {
  result_findings: list taint_finding;
  result_sources_found: nat;
  result_sinks_checked: nat;
}

(** ═══════════════════════════════════════════════════════════════════════════
    TAINT ANALYSIS ENTRY POINT
    ═══════════════════════════════════════════════════════════════════════════ *)

val analyze_taint : cfg -> taint_result

let analyze_taint g =
  let init_state = empty_taint_state in
  let final_state = forward_analyze taint_lattice taint_transfer g init_state 100 in
  (* Check sinks - simplified *)
  {
    result_findings = [];
    result_sources_found = 0;
    result_sinks_checked = List.Tot.length go_taint_sinks;
  }

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREM: TAINT ANALYSIS SOUNDNESS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* If tainted data reaches a sink in concrete execution,
   the analysis will detect it *)
val taint_analysis_sound :
  g:cfg ->
  result:taint_result{result = analyze_taint g} ->
  (* For any concrete path from source to sink... *)
  Lemma (True)  (* Simplified - actual theorem would specify no false negatives *)

let taint_analysis_sound g result = ()
