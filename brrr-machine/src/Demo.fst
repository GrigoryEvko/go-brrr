(**
 * Demo.fst - Simple F* verification demo
 *)
module Demo

open FStar.List.Tot

(** ═══════════════════════════════════════════════════════════════════════════
    PART 1: REFINEMENT TYPES
    ═══════════════════════════════════════════════════════════════════════════ *)

(* A positive integer - F* verifies all uses satisfy x > 0 *)
type pos = x:int{x > 0}

(* Safe division - can ONLY be called with non-zero divisor *)
let safe_div (a: int) (b: int{b <> 0}) : int = a / b

(* This compiles - F* proves 5 <> 0 *)
let good = safe_div 10 5


(** ═══════════════════════════════════════════════════════════════════════════
    PART 2: SIMPLE LEMMAS (Auto-proven by Z3)
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Lemma: addition is commutative *)
val add_comm : x:int -> y:int -> Lemma (x + y == y + x)
let add_comm x y = ()  (* Empty proof - Z3 handles it *)

(* Lemma: adding positive numbers gives positive *)
val pos_plus_pos : x:pos -> y:pos -> Lemma (x + y > 0)
let pos_plus_pos x y = ()  (* Z3 proves: x > 0 ∧ y > 0 ⟹ x + y > 0 *)


(** ═══════════════════════════════════════════════════════════════════════════
    PART 3: LIST EXAMPLE WITH INDUCTION
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Length of a list *)
let rec my_length #a (l: list a) : nat =
  match l with
  | [] -> 0
  | _ :: tl -> 1 + my_length tl

(* Lemma: appending adds lengths *)
val append_length : #a:Type -> l1:list a -> l2:list a ->
  Lemma (my_length (l1 @ l2) == my_length l1 + my_length l2)
let rec append_length #a l1 l2 =
  match l1 with
  | [] -> ()  (* Base case *)
  | _ :: tl -> append_length tl l2  (* Inductive step *)


(** ═══════════════════════════════════════════════════════════════════════════
    PART 4: CFG-LIKE EXAMPLE (Relevant to brrr-machine)
    ═══════════════════════════════════════════════════════════════════════════ *)

type node_id = nat

type edge = {
  src: node_id;
  dst: node_id;
}

type graph = {
  nodes: list node_id;
  edges: list edge;
}

(* Get successors of a node *)
let successors (g: graph) (n: node_id) : list node_id =
  List.Tot.map (fun e -> e.dst)
    (List.Tot.filter (fun e -> e.src = n) g.edges)

(* Get predecessors of a node *)
let predecessors (g: graph) (n: node_id) : list node_id =
  List.Tot.map (fun e -> e.src)
    (List.Tot.filter (fun e -> e.dst = n) g.edges)

(* A simple graph for testing *)
let test_graph : graph = {
  nodes = [0; 1; 2];
  edges = [
    { src = 0; dst = 1 };
    { src = 1; dst = 2 };
  ];
}

(* Lemma: node 0 has successor 1 in test_graph *)
val test_successors : unit -> Lemma (successors test_graph 0 == [1])
let test_successors () = ()  (* F* computes and verifies! *)

(* Lemma: node 0 has no predecessors in test_graph *)
val test_no_preds : unit -> Lemma (predecessors test_graph 0 == [])
let test_no_preds () = ()


(** ═══════════════════════════════════════════════════════════════════════════
    PART 5: TAINT ANALYSIS
    ═══════════════════════════════════════════════════════════════════════════ *)

type taint = | Clean | Tainted

(* Taint propagates through operations *)
let combine_taint (t1 t2: taint) : taint =
  match t1, t2 with
  | Tainted, _ -> Tainted
  | _, Tainted -> Tainted
  | Clean, Clean -> Clean

(* Lemma: if either input is tainted, output is tainted *)
val taint_propagates : t1:taint -> t2:taint ->
  Lemma (requires t1 == Tainted \/ t2 == Tainted)
        (ensures combine_taint t1 t2 == Tainted)
let taint_propagates t1 t2 = ()

(* Lemma: clean inputs produce clean output *)
val clean_stays_clean : t1:taint -> t2:taint ->
  Lemma (requires t1 == Clean /\ t2 == Clean)
        (ensures combine_taint t1 t2 == Clean)
let clean_stays_clean t1 t2 = ()
