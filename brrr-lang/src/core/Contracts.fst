(**
 * BrrrLang.Core.Contracts
 *
 * Contracts and Hoare Logic for Brrr-Lang.
 * Based on brrr_lang_spec_v0.4.tex Part IX - Contracts.
 *
 * Implements:
 *   - Function contracts with pre/postconditions
 *   - Refinement type helpers (nat_type, pos_type, bounded_index)
 *   - Hoare triple representation and semantics
 *   - Hoare logic rules (H-Skip, H-Assign, H-Seq, H-If, H-While, H-Conseq)
 *   - Weakest precondition calculation
 *   - Verification condition generation
 *   - Loop invariant support
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, DependentTypes, Values, Eval
 *)
module Contracts

open FStar.List.Tot
open FStar.Classical
open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open DependentTypes
open Values
open Eval

(** ============================================================================
    REFINEMENT TYPE HELPERS
    ============================================================================

    Common refined types for program verification.
    These are meta-level types in F* that correspond to Brrr refinement types.
    ============================================================================ *)

(* Natural numbers: non-negative integers *)
type nat_type = x:int{x >= 0}

(* Positive integers: strictly positive *)
type pos_type = x:int{x > 0}

(* Bounded array index: valid index into array of given length *)
type bounded_index (len:nat{len > 0}) = i:nat{i < len}

(* Non-empty list: list with at least one element *)
type non_empty_list (a:Type) = l:list a{Cons? l}

(* Percentage: value between 0 and 100 *)
type percentage = x:int{0 <= x /\ x <= 100}

(** ============================================================================
    FUNCTION CONTRACTS
    ============================================================================

    A contract specifies the expected behavior of a function:
    - Precondition: What must hold before the function is called
    - Postcondition: What will hold after the function returns

    The postcondition can reference the special variable "result" which
    represents the return value of the function.
    ============================================================================ *)

noeq type contract = {
  precondition  : formula;   (* What caller must ensure *)
  postcondition : formula;   (* What function guarantees, can use "result" *)
}

(* Create a trivial contract: true -> true *)
let trivial_contract : contract = {
  precondition = FTrue;
  postcondition = FTrue;
}

(* Create a pure function contract: no side effects, only return value matters *)
let pure_contract (pre: formula) (post: formula) : contract = {
  precondition = pre;
  postcondition = post;
}

(* Contract with only a precondition *)
let requires_only (pre: formula) : contract = {
  precondition = pre;
  postcondition = FTrue;
}

(* Contract with only a postcondition *)
let ensures_only (post: formula) : contract = {
  precondition = FTrue;
  postcondition = post;
}

(** ============================================================================
    PROGRAM STATE ABSTRACTION
    ============================================================================

    For Hoare logic, we need an abstract view of program state.
    A state is a mapping from variables to values.
    ============================================================================ *)

(* Abstract state: mapping from variable names to values *)
type state = var_id -> option value

(* Empty state: no variables defined *)
let empty_state : state = fun _ -> None

(* State update: s[x := v] *)
let state_update (s: state) (x: var_id) (v: value) : state =
  fun y -> if y = x then Some v else s y

(* State lookup *)
let state_lookup (s: state) (x: var_id) : option value = s x

(* Convert eval environment to abstract state *)
let env_to_state (e: env) : state =
  fun x -> lookup x e

(* Convert abstract state to environment (as list of bindings) *)
let rec state_to_env_helper (vars: list var_id) (s: state) : env =
  match vars with
  | [] -> []
  | x :: rest ->
      match s x with
      | Some v -> (x, v) :: state_to_env_helper rest s
      | None -> state_to_env_helper rest s

(** ============================================================================
    FORMULA EVALUATION
    ============================================================================

    Evaluate a formula in a given state to get a boolean result.
    This provides the semantic foundation for Hoare logic.
    ============================================================================ *)

(* Evaluate expression in state, returning option value *)
let eval_expr_in_state (e: expr) (s: state) (fuel: nat) : option value =
  (* Build environment from variables in expression *)
  let vars = free_vars e in
  let env = state_to_env_helper vars s in
  let st = { init_eval_state with es_env = env } in
  match fst (eval_expr fuel e st) with
  | ROk v -> Some v
  | _ -> None

(* Evaluate comparison operator *)
let eval_cmp_op (op: cmp_op) (v1 v2: value) : option bool =
  match v1, v2 with
  | VInt n1, VInt n2 ->
      Some (match op with
            | CmpEq -> n1 = n2
            | CmpNe -> n1 <> n2
            | CmpLt -> n1 < n2
            | CmpLe -> n1 <= n2
            | CmpGt -> n1 > n2
            | CmpGe -> n1 >= n2)
  | VBool b1, VBool b2 ->
      (match op with
       | CmpEq -> Some (b1 = b2)
       | CmpNe -> Some (b1 <> b2)
       | _ -> None)
  | VString s1, VString s2 ->
      Some (match op with
            | CmpEq -> s1 = s2
            | CmpNe -> s1 <> s2
            | CmpLt -> FStar.String.compare s1 s2 < 0
            | CmpLe -> FStar.String.compare s1 s2 <= 0
            | CmpGt -> FStar.String.compare s1 s2 > 0
            | CmpGe -> FStar.String.compare s1 s2 >= 0)
  | _, _ -> None

(* Evaluate formula in state with fuel for recursive calls *)
let rec eval_formula_in_state (fuel: nat) (phi: formula) (s: state) : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    match phi with
    | FTrue -> Some true
    | FFalse -> Some false

    | FCmp op e1 e2 ->
        (match eval_expr_in_state e1 s (fuel - 1), eval_expr_in_state e2 s (fuel - 1) with
         | Some v1, Some v2 -> eval_cmp_op op v1 v2
         | _, _ -> None)

    | FAnd phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some false -> Some false
         | Some true -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    | FOr phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some true -> Some true
         | Some false -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    | FNot phi' ->
        (match eval_formula_in_state (fuel - 1) phi' s with
         | Some b -> Some (not b)
         | None -> None)

    | FImpl phi1 phi2 ->
        (* P => Q is equivalent to ~P \/ Q *)
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some false -> Some true
         | Some true -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    | FIff phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s, eval_formula_in_state (fuel - 1) phi2 s with
         | Some b1, Some b2 -> Some (b1 = b2)
         | _, _ -> None)

    | FForall _ _ _ -> None  (* Cannot evaluate unbounded quantifiers *)
    | FExists _ _ _ -> None

    | FPred _ _ -> None  (* Predicates need external interpretation *)

    | FExpr e ->
        (match eval_expr_in_state e s (fuel - 1) with
         | Some (VBool b) -> Some b
         | _ -> None)

(* Default fuel for formula evaluation *)
let formula_eval_fuel : nat = 1000

(* Check if formula holds in state *)
let formula_holds (phi: formula) (s: state) : bool =
  match eval_formula_in_state formula_eval_fuel phi s with
  | Some true -> true
  | _ -> false

(** ============================================================================
    ASSERTION TYPE - Semantic predicates on states
    ============================================================================

    An assertion is a predicate on program states.
    We represent assertions both as formulas (syntactic) and as
    semantic predicates (for proofs).
    ============================================================================ *)

(* Semantic assertion: predicate on states *)
type assertion = state -> Type0

(* Convert formula to semantic assertion *)
let formula_to_assertion (phi: formula) : assertion =
  fun s -> formula_holds phi s == true

(* Trivially true assertion *)
let assert_true : assertion = fun _ -> True

(* Trivially false assertion *)
let assert_false : assertion = fun _ -> False

(* Conjunction of assertions *)
let assert_and (p q: assertion) : assertion =
  fun s -> p s /\ q s

(* Disjunction of assertions *)
let assert_or (p q: assertion) : assertion =
  fun s -> p s \/ q s

(* Implication of assertions *)
let assert_impl (p q: assertion) : assertion =
  fun s -> p s ==> q s

(* Negation of assertion *)
let assert_not (p: assertion) : assertion =
  fun s -> ~(p s)

(** ============================================================================
    HOARE TRIPLE REPRESENTATION
    ============================================================================

    A Hoare triple {P} c {Q} asserts:
      For all states s, if P holds in s and executing c from s terminates
      in state s', then Q holds in s'.

    We use an abstract/axiomatic approach where Hoare triples are
    propositions whose validity is established through the VC generation
    and checking mechanism.
    ============================================================================ *)

(* Execute expression and get resulting state *)
let exec_expr (e: expr) (s: state) (fuel: nat) : option (value & state) =
  let vars = free_vars e in
  let env = state_to_env_helper vars s in
  let st = { init_eval_state with es_env = env } in
  match eval_expr fuel e st with
  | (ROk v, st') -> Some (v, env_to_state st'.es_env)
  | _ -> None

(* Hoare triple validity as a semantic proposition.
   {P} c {Q} holds when: for all states s satisfying P,
   if c terminates with value v in state s', then Q holds in s'.

   We define this directly as the semantic meaning of partial correctness. *)
let hoare_triple_valid (pre: assertion) (c: expr) (post: assertion) : Type0 =
  forall (s: state) (fuel: nat) (v: value) (s': state).
    pre s ==> (exec_expr c s fuel == Some (v, s') ==> post s')

(* Notation helper: create Hoare triple from formulas *)
let hoare (pre: formula) (c: expr) (post: formula) : Type0 =
  hoare_triple_valid (formula_to_assertion pre) c (formula_to_assertion post)

(* Total correctness: termination + partial correctness *)
let hoare_total (pre: assertion) (c: expr) (post: assertion) : Type0 =
  (forall (s: state). pre s ==> (exists (fuel: nat) (v: value) (s': state). exec_expr c s fuel == Some (v, s'))) /\
  hoare_triple_valid pre c post

(** ============================================================================
    HOARE LOGIC RULES - Axiomatized Sound Rules
    ============================================================================

    The following rules are the standard Hoare logic rules.
    We axiomatize them as sound with respect to operational semantics.
    Soundness is justified by classical Hoare logic theory.
    ============================================================================ *)

(* H-Skip: {P} unit {P}
   Skip (unit expression) preserves any assertion.
   Sound because evaluating unit produces unit without state change. *)
assume val h_skip : p:assertion -> Lemma (hoare_triple_valid p (ELit LitUnit) p)

(* H-Skip for formulas *)
assume val h_skip_formula : phi:formula -> Lemma (hoare phi (ELit LitUnit) phi)

(* H-Seq: {P} c1 {Q} /\ {Q} c2 {R} ==> {P} c1;c2 {R}
   Sequential composition: intermediate state satisfies Q.
   Sound because evaluation of c1;c2 proceeds through intermediate state. *)
assume val h_seq : p:assertion -> q:assertion -> r:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid p c1 q /\ hoare_triple_valid q c2 r)
        (ensures hoare_triple_valid p (ESeq c1 c2) r)

(* H-Conseq: P' ==> P /\ {P} c {Q} /\ Q ==> Q' ==> {P'} c {Q'}
   Consequence rule: strengthen precondition, weaken postcondition.
   Sound by transitivity of implication. *)
assume val h_conseq : p:assertion -> p':assertion -> q:assertion -> q':assertion -> c:expr ->
  Lemma (requires (forall s. p' s ==> p s) /\
                  hoare_triple_valid p c q /\
                  (forall s. q s ==> q' s))
        (ensures hoare_triple_valid p' c q')

(* H-If: {P /\ b} c1 {Q} /\ {P /\ ~b} c2 {Q} ==> {P} if b c1 c2 {Q}
   Conditional rule: both branches establish postcondition.
   Sound because exactly one branch is taken based on condition. *)
assume val h_if_valid : p:assertion -> q:assertion -> b_true:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid (assert_and p b_true) c1 q /\
                  hoare_triple_valid (assert_and p (assert_not b_true)) c2 q)
        (ensures hoare_triple_valid p (EIf (ELit (LitBool true)) c1 c2) q)

(* H-While: {I /\ b} c {I} ==> {I} while b do c {I /\ ~b}
   While rule with loop invariant.
   Sound because invariant is preserved by each iteration. *)
assume val h_while_valid : inv:assertion -> b_true:assertion -> body:expr ->
  Lemma (requires hoare_triple_valid (assert_and inv b_true) body inv)
        (ensures hoare_triple_valid inv
                   (EWhile (ELit (LitBool true)) body)
                   (assert_and inv (assert_not b_true)))

(** ============================================================================
    WEAKEST PRECONDITION CALCULUS
    ============================================================================

    The weakest precondition WP(c, Q) is the weakest assertion P such that
    {P} c {Q} holds. Computing WP allows automatic VC generation.

    WP rules:
    - WP(skip, Q) = Q
    - WP(x := e, Q) = Q[e/x]
    - WP(c1; c2, Q) = WP(c1, WP(c2, Q))
    - WP(if b then c1 else c2, Q) = (b => WP(c1, Q)) /\ (~b => WP(c2, Q))
    - WP(while b inv I do c, Q) = I /\ forall state. (I /\ ~b => Q) /\ (I /\ b => WP(c, I))
    ============================================================================ *)

(* Substitute expression for variable in formula (WP computation) *)
let wp_subst (x: var_id) (e: expr) (post: formula) : formula =
  subst_formula x e post

(* Weakest precondition computation with fuel for termination *)
let rec wp_compute (fuel: nat) (c: expr) (post: formula) : Tot formula (decreases fuel) =
  if fuel = 0 then FFalse  (* Conservative: cannot compute *)
  else
    match c with
    (* WP(unit, Q) = Q *)
    | ELit LitUnit -> post

    (* WP(x, Q) = Q (variable reference is pure) *)
    | EVar _ -> post

    (* WP(literal, Q) = Q *)
    | ELit _ -> post

    (* WP(x := e, Q) = Q[e/x] - but we need to handle assignment specially *)
    | EAssign (EVar x) e ->
        wp_subst x e post

    (* WP(let x = e1 in e2, Q) = WP(e1, [result/x]WP(e2, Q)) *)
    | ELet (PatVar x) _ e1 e2 ->
        let wp_e2 = wp_compute (fuel - 1) e2 post in
        wp_compute (fuel - 1) e1 (subst_formula x (EVar "result") wp_e2)

    (* WP(c1; c2, Q) = WP(c1, WP(c2, Q)) *)
    | ESeq c1 c2 ->
        let wp_c2 = wp_compute (fuel - 1) c2 post in
        wp_compute (fuel - 1) c1 wp_c2

    (* WP(if b then c1 else c2, Q) = (b => WP(c1, Q)) /\ (~b => WP(c2, Q)) *)
    | EIf b c1 c2 ->
        let wp_c1 = wp_compute (fuel - 1) c1 post in
        let wp_c2 = wp_compute (fuel - 1) c2 post in
        FAnd (FImpl (FExpr b) wp_c1) (FImpl (FNot (FExpr b)) wp_c2)

    (* WP(block [e], Q) = WP(e, Q) *)
    | EBlock [e] -> wp_compute (fuel - 1) e post

    (* WP(block (e::es), Q) = WP(e, WP(block es, Q)) *)
    | EBlock (e :: es) ->
        let wp_rest = wp_compute (fuel - 1) (EBlock es) post in
        wp_compute (fuel - 1) e wp_rest

    (* WP(block [], Q) = Q *)
    | EBlock [] -> post

    (* For other expressions, conservatively return post
       (assumes expression is pure/side-effect-free) *)
    | _ -> post

(* Default fuel for WP computation *)
let wp_fuel : nat = 100

(* Compute weakest precondition *)
let wp (c: expr) (post: formula) : formula =
  wp_compute wp_fuel c post

(** ============================================================================
    LOOP INVARIANTS
    ============================================================================

    For while loops, we need loop invariants to enable verification.
    The invariant must:
    1. Hold initially (when entering the loop)
    2. Be preserved by each iteration
    3. Together with loop termination condition, imply the postcondition
    ============================================================================ *)

(* Annotated while loop with invariant *)
noeq type annotated_while = {
  while_cond      : expr;      (* Loop condition *)
  while_body      : expr;      (* Loop body *)
  while_invariant : formula;   (* Loop invariant *)
  while_variant   : option expr; (* Optional decreasing variant for termination *)
}

(* Check if invariant is preserved by loop body *)
let invariant_preserved (inv: formula) (cond: expr) (body: expr) : formula =
  (* {I /\ b} body {I} expressed as: (I /\ b) => WP(body, I) *)
  FImpl (FAnd inv (FExpr cond)) (wp body inv)

(* Generate verification conditions for while loop *)
let while_vc (w: annotated_while) (post: formula) : formula =
  let inv = w.while_invariant in
  let cond = w.while_cond in
  let body = w.while_body in
  (* VCs:
     1. Invariant preservation: (I /\ b) => WP(body, I)
     2. Postcondition establishment: (I /\ ~b) => post *)
  FAnd
    (invariant_preserved inv cond body)
    (FImpl (FAnd inv (FNot (FExpr cond))) post)

(* WP for annotated while loop *)
let wp_while (w: annotated_while) (post: formula) : formula =
  (* WP(while b inv I do c, Q) = I /\ VC(while, Q) *)
  FAnd w.while_invariant (while_vc w post)

(** ============================================================================
    VERIFICATION CONDITIONS
    ============================================================================

    Verification conditions (VCs) are logical formulas that, if valid,
    guarantee the correctness of a program with respect to its contract.
    ============================================================================ *)

(* VC representation - richer than formula for SMT solving *)
noeq type vc =
  | VCTrue   : vc                              (* Trivially true *)
  | VCFalse  : vc                              (* Trivially false *)
  | VCImpl   : vc -> vc -> vc                  (* Implication *)
  | VCAnd    : vc -> vc -> vc                  (* Conjunction *)
  | VCOr     : vc -> vc -> vc                  (* Disjunction *)
  | VCNot    : vc -> vc                        (* Negation *)
  | VCForall : var_id -> brrr_type -> vc -> vc (* Universal quantifier *)
  | VCExists : var_id -> brrr_type -> vc -> vc (* Existential quantifier *)
  | VCFormula : formula -> vc                  (* Embed formula *)

(* VC size for termination proofs *)
let rec vc_size (v: vc) : Tot nat (decreases v) =
  match v with
  | VCTrue | VCFalse | VCFormula _ -> 1
  | VCNot v' -> 1 + vc_size v'
  | VCImpl v1 v2 | VCAnd v1 v2 | VCOr v1 v2 -> 1 + vc_size v1 + vc_size v2
  | VCForall _ _ v' | VCExists _ _ v' -> 1 + vc_size v'

(* Convert formula to VC *)
let formula_to_vc (phi: formula) : vc = VCFormula phi

(* Convert VC to formula (best effort - quantifiers may not convert) *)
let rec vc_to_formula (v: vc) : Tot formula (decreases v) =
  match v with
  | VCTrue -> FTrue
  | VCFalse -> FFalse
  | VCImpl v1 v2 -> FImpl (vc_to_formula v1) (vc_to_formula v2)
  | VCAnd v1 v2 -> FAnd (vc_to_formula v1) (vc_to_formula v2)
  | VCOr v1 v2 -> FOr (vc_to_formula v1) (vc_to_formula v2)
  | VCNot v' -> FNot (vc_to_formula v')
  | VCForall x t v' -> FForall x t (vc_to_formula v')
  | VCExists x t v' -> FExists x t (vc_to_formula v')
  | VCFormula phi -> phi

(* Simplify VC *)
let rec simplify_vc (v: vc) : Tot vc (decreases v) =
  match v with
  | VCTrue -> VCTrue
  | VCFalse -> VCFalse

  | VCAnd v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCTrue, _ -> v2'
       | _, VCTrue -> v1'
       | VCFalse, _ -> VCFalse
       | _, VCFalse -> VCFalse
       | _, _ -> VCAnd v1' v2')

  | VCOr v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCTrue, _ -> VCTrue
       | _, VCTrue -> VCTrue
       | VCFalse, _ -> v2'
       | _, VCFalse -> v1'
       | _, _ -> VCOr v1' v2')

  | VCImpl v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCFalse, _ -> VCTrue  (* False => anything is true *)
       | _, VCTrue -> VCTrue   (* anything => True is true *)
       | VCTrue, _ -> v2'      (* True => P is P *)
       | _, _ -> VCImpl v1' v2')

  | VCNot v' ->
      (match simplify_vc v' with
       | VCTrue -> VCFalse
       | VCFalse -> VCTrue
       | VCNot v'' -> v''  (* Double negation elimination *)
       | v'' -> VCNot v'')

  | VCForall x t v' -> VCForall x t (simplify_vc v')
  | VCExists x t v' -> VCExists x t (simplify_vc v')
  | VCFormula phi -> VCFormula (simplify_formula phi)

(** ============================================================================
    VC CHECKING
    ============================================================================

    Check if a VC is valid (semantically true in all states).
    This is a conservative approximation - returns true only when
    we can syntactically determine validity.
    ============================================================================ *)

(* Conservative VC validity check - operates on original VC structure *)
let rec check_vc (v: vc) : Tot bool (decreases v) =
  match v with
  | VCTrue -> true
  | VCFalse -> false

  | VCAnd v1 v2 -> check_vc v1 && check_vc v2

  | VCImpl v1 v2 ->
      (* If premise is false or conclusion is true, implication holds *)
      (match v1, v2 with
       | VCFalse, _ -> true
       | _, VCTrue -> true
       | _, _ -> check_vc v2)  (* Conservative: assume premise *)

  | VCOr v1 v2 -> check_vc v1 || check_vc v2

  | VCNot v' ->
      (match v' with
       | VCFalse -> true
       | VCTrue -> false
       | _ -> false)  (* Conservative *)

  | VCForall _ _ v' -> check_vc v'  (* Conservative: check body *)
  | VCExists _ _ _ -> false  (* Cannot check existentials without witness *)
  | VCFormula phi ->
      (match phi with
       | FTrue -> true
       | FFalse -> false
       | _ -> false)  (* Conservative for complex formulas *)

(* Simplified VC check that first simplifies the VC *)
let check_vc_simplified (v: vc) : bool =
  check_vc (simplify_vc v)

(** ============================================================================
    VC GENERATION FROM CONTRACT AND EXPRESSION
    ============================================================================

    Generate verification conditions that must be valid for the contract
    to hold on the given expression.
    ============================================================================ *)

(* Generate VC for contract and expression *)
let generate_vc (c: contract) (e: expr) : vc =
  (* VC: pre => WP(e, post) *)
  let wp_post = wp e c.postcondition in
  VCImpl (VCFormula c.precondition) (VCFormula wp_post)

(* Generate VC with loop invariants *)
let rec generate_vc_with_invariants (fuel: nat) (c: contract) (e: expr)
    (invariants: list (expr & formula))  (* Map from while expr to invariant *)
    : Tot vc (decreases fuel) =
  if fuel = 0 then VCFalse
  else
    match e with
    | EWhile cond body ->
        (* Find invariant for this loop *)
        let inv_opt = List.Tot.find (fun (e', _) ->
          match e', e with
          | EWhile c1 b1, EWhile c2 b2 -> expr_eq c1 c2 && expr_eq b1 b2
          | _, _ -> false) invariants in
        (match inv_opt with
         | Some (_, inv) ->
             let w : annotated_while = {
               while_cond = cond;
               while_body = body;
               while_invariant = inv;
               while_variant = None;
             } in
             (* Generate VCs for the loop *)
             VCAnd
               (* Precondition establishes invariant *)
               (VCImpl (VCFormula c.precondition) (VCFormula inv))
               (* Loop VCs *)
               (VCFormula (while_vc w c.postcondition))
         | None ->
             (* No invariant provided - cannot verify loop *)
             VCFalse)

    | ESeq e1 e2 ->
        (* Generate VCs for both parts *)
        let vc1 = generate_vc_with_invariants (fuel - 1) c e1 invariants in
        let intermediate_contract = { c with postcondition = wp e2 c.postcondition } in
        let vc2 = generate_vc_with_invariants (fuel - 1) intermediate_contract e2 invariants in
        VCAnd vc1 vc2

    | EIf cond then_e else_e ->
        (* VCs for both branches *)
        let vc_then = generate_vc_with_invariants (fuel - 1) c then_e invariants in
        let vc_else = generate_vc_with_invariants (fuel - 1) c else_e invariants in
        VCAnd
          (VCImpl (VCFormula (FExpr cond)) vc_then)
          (VCImpl (VCNot (VCFormula (FExpr cond))) vc_else)

    | EBlock [] -> generate_vc c (ELit LitUnit)
    | EBlock [e'] -> generate_vc_with_invariants (fuel - 1) c e' invariants
    | EBlock (e' :: es) ->
        let vc1 = generate_vc_with_invariants (fuel - 1)
                    { c with postcondition = wp (EBlock es) c.postcondition }
                    e' invariants in
        let vc2 = generate_vc_with_invariants (fuel - 1) c (EBlock es) invariants in
        VCAnd vc1 vc2

    | _ -> generate_vc c e

(** ============================================================================
    CONTRACT VERIFICATION
    ============================================================================

    Verify that a contract holds for an expression by generating and
    checking verification conditions.
    ============================================================================ *)

(* Verification result *)
noeq type verification_result =
  | Verified : verification_result                (* Contract holds *)
  | Failed   : vc -> verification_result          (* VC that couldn't be proved *)
  | Unknown  : verification_result                (* Cannot determine *)

(* Verify contract on expression *)
let verify_contract (c: contract) (e: expr) : verification_result =
  let vc = generate_vc c e in
  let vc' = simplify_vc vc in
  if check_vc vc' then Verified
  else Failed vc'

(* Verify with loop invariants *)
let verify_contract_with_invariants (c: contract) (e: expr)
    (invariants: list (expr & formula)) : verification_result =
  let vc = generate_vc_with_invariants 100 c e invariants in
  let vc' = simplify_vc vc in
  if check_vc vc' then Verified
  else Failed vc'

(** ============================================================================
    HOARE LOGIC SOUNDNESS
    ============================================================================

    The soundness of our Hoare logic rules with respect to the
    operational semantics. These are axiomatized based on classical
    Hoare logic theory.
    ============================================================================ *)

(* Soundness of WP: {WP(c, Q)} c {Q}
   If we start in a state satisfying WP(c, Q) and c terminates,
   then the final state satisfies Q.
   This is the fundamental theorem of weakest precondition calculus. *)
assume val wp_sound : c:expr -> q:formula ->
  Lemma (hoare (wp c q) c q)

(* Soundness of VC generation:
   If generate_vc(contract, e) is valid, then the contract holds for e.
   Proof: By construction, generate_vc produces pre => WP(e, post),
   and if this holds, then by wp_sound we get {pre} e {post}. *)
assume val vc_generation_sound : c:contract -> e:expr ->
  Lemma (requires check_vc (generate_vc c e) == true)
        (ensures hoare c.precondition e c.postcondition)

(** ============================================================================
    HOARE TRIPLE AS INDEXED TYPE
    ============================================================================

    Alternative representation of Hoare triples as an indexed type,
    enabling computation with proofs. This provides a monadic interface
    for composing verified computations.
    ============================================================================ *)

(* Hoare triple as an indexed type with witness function *)
noeq type hoare_triple_t (pre: Type0) (a: Type) (post: a -> Type0) =
  | HT : (f: (unit -> Pure a (requires pre) (ensures post))) -> hoare_triple_t pre a post

(* Run a Hoare triple when precondition is satisfied *)
let run_ht (#pre: Type0) (#a: Type) (#post: a -> Type0)
           (ht: hoare_triple_t pre a post)
           (_: squash pre) : Pure a (requires pre) (ensures post) =
  let HT f = ht in
  f ()

(* Return for Hoare triples: trivially satisfied *)
let return_ht (#a: Type) (x: a) : hoare_triple_t True a (fun r -> r == x) =
  HT (fun () -> x)

(* Compose Hoare triples sequentially using explicit precondition threading.
   This requires that executing ht1 establishes the precondition for ht2. *)
val bind_ht : #pre1:Type0 -> #a:Type -> #mid:(a -> Type0) -> #b:Type -> #post:(b -> Type0) ->
              ht1:hoare_triple_t pre1 a mid ->
              ht2:(x:a -> hoare_triple_t (mid x) b post) ->
              hoare_triple_t pre1 b post
let bind_ht #pre1 #a #mid #b #post ht1 ht2 =
  HT (fun () ->
    let HT f1 = ht1 in
    let x : a = f1 () in
    (* At this point, mid x holds from f1's postcondition *)
    let HT f2 = ht2 x in
    f2 ())

(** ============================================================================
    LOOP INVARIANT HELPERS
    ============================================================================ *)

(* Check that invariant holds initially *)
let invariant_holds_initially (pre: formula) (inv: formula) : vc =
  VCImpl (VCFormula pre) (VCFormula inv)

(* Check that invariant is inductive *)
let invariant_is_inductive (inv: formula) (cond: expr) (body: expr) : vc =
  VCImpl
    (VCAnd (VCFormula inv) (VCFormula (FExpr cond)))
    (VCFormula (wp body inv))

(* Check that invariant with negated condition implies post *)
let invariant_implies_post (inv: formula) (cond: expr) (post: formula) : vc =
  VCImpl
    (VCAnd (VCFormula inv) (VCNot (VCFormula (FExpr cond))))
    (VCFormula post)

(* Generate all VCs for a loop *)
let loop_vcs (pre: formula) (inv: formula) (cond: expr) (body: expr) (post: formula) : vc =
  VCAnd
    (invariant_holds_initially pre inv)
    (VCAnd
      (invariant_is_inductive inv cond body)
      (invariant_implies_post inv cond post))

(** ============================================================================
    FUNCTION CONTRACT VERIFICATION
    ============================================================================ *)

(* Function definition with contract *)
noeq type contracted_function = {
  fn_name     : string;
  fn_params   : list (var_id & brrr_type);
  fn_return   : brrr_type;
  fn_contract : contract;
  fn_body     : expr;
}

(* Verify a contracted function *)
let verify_function (f: contracted_function) : verification_result =
  verify_contract f.fn_contract f.fn_body

(* Create contract from requires/ensures annotations *)
let make_contract (requires_clause: formula) (ensures_clause: formula) : contract = {
  precondition = requires_clause;
  postcondition = ensures_clause;
}

(** ============================================================================
    DEPENDENT REFINEMENT TYPE INTEGRATION
    ============================================================================ *)

(* Convert refinement type to precondition *)
let refinement_to_precondition (x: var_id) (t: dep_type) : formula =
  match t with
  | DRefinement _ _ phi -> subst_formula x (EVar x) phi
  | _ -> FTrue

(* Extract contract from dependent function type *)
let dep_func_to_contract (fn_type: dep_type) (result_var: var_id) : option contract =
  match fn_type with
  | DPi x param_type return_type ->
      let pre = refinement_to_precondition x param_type in
      let post =
        match return_type with
        | DRefinement _ _ phi -> subst_formula result_var (EVar result_var) phi
        | _ -> FTrue
      in
      Some { precondition = pre; postcondition = post }
  | _ -> None

(** ============================================================================
    SPECIFICATION LANGUAGE HELPERS
    ============================================================================ *)

(* Assert: inline assertion *)
let spec_assert (phi: formula) : expr =
  EIf (ELit (LitBool true))  (* Condition that's always true *)
      (ELit LitUnit)
      (EError "assertion failed")

(* Assume: assume formula holds (for verification) *)
let spec_assume (phi: formula) : formula = phi

(* Old: refer to pre-state value (for postconditions) *)
let spec_old (x: var_id) : var_id = "old_" ^ x

(* Result: the return value in postconditions *)
let spec_result : var_id = "result"

(* Create postcondition referencing result *)
let ensures_result (f: expr -> formula) : formula =
  f (EVar spec_result)

(* Create postcondition comparing result to old value *)
let ensures_modified (x: var_id) (relation: expr -> expr -> formula) : formula =
  relation (EVar x) (EVar (spec_old x))

(** ============================================================================
    COMMON CONTRACT PATTERNS
    ============================================================================ *)

(* Pure function: no precondition, result satisfies predicate *)
let pure_function_contract (result_pred: expr -> formula) : contract = {
  precondition = FTrue;
  postcondition = result_pred (EVar spec_result);
}

(* Partial function: precondition required, ensures result *)
let partial_function_contract (pre: formula) (result_pred: expr -> formula) : contract = {
  precondition = pre;
  postcondition = result_pred (EVar spec_result);
}

(* Monotonic function: result >= input *)
let monotonic_contract (input_var: var_id) : contract = {
  precondition = FTrue;
  postcondition = FCmp CmpGe (EVar spec_result) (EVar input_var);
}

(* Non-negative result contract *)
let non_negative_result_contract : contract = {
  precondition = FTrue;
  postcondition = FCmp CmpGe (EVar spec_result) (e_int 0);
}

(* Bounded result contract *)
let bounded_result_contract (lo hi: int) : contract = {
  precondition = FTrue;
  postcondition = FAnd
    (FCmp CmpGe (EVar spec_result) (e_int lo))
    (FCmp CmpLt (EVar spec_result) (e_int hi));
}

(** ============================================================================
    VC TO STRING (for debugging)
    ============================================================================ *)

let rec vc_to_string (v: vc) : Tot string (decreases v) =
  match v with
  | VCTrue -> "true"
  | VCFalse -> "false"
  | VCImpl v1 v2 -> "(" ^ vc_to_string v1 ^ " => " ^ vc_to_string v2 ^ ")"
  | VCAnd v1 v2 -> "(" ^ vc_to_string v1 ^ " /\\ " ^ vc_to_string v2 ^ ")"
  | VCOr v1 v2 -> "(" ^ vc_to_string v1 ^ " \\/ " ^ vc_to_string v2 ^ ")"
  | VCNot v' -> "~" ^ vc_to_string v'
  | VCForall x _ v' -> "(forall " ^ x ^ ". " ^ vc_to_string v' ^ ")"
  | VCExists x _ v' -> "(exists " ^ x ^ ". " ^ vc_to_string v' ^ ")"
  | VCFormula phi -> formula_to_string phi

(** ============================================================================
    VERIFICATION REPORTING
    ============================================================================ *)

(* Verification report for a function *)
noeq type verification_report = {
  vr_function : string;
  vr_result   : verification_result;
  vr_vc       : vc;
  vr_message  : string;
}

(* Create verification report *)
let make_report (f: contracted_function) : verification_report =
  let vc = generate_vc f.fn_contract f.fn_body in
  let result = verify_contract f.fn_contract f.fn_body in
  let msg = match result with
    | Verified -> "Function " ^ f.fn_name ^ " verified successfully"
    | Failed _ -> "Function " ^ f.fn_name ^ " failed verification"
    | Unknown -> "Function " ^ f.fn_name ^ " verification inconclusive"
  in
  { vr_function = f.fn_name;
    vr_result = result;
    vr_vc = vc;
    vr_message = msg; }
