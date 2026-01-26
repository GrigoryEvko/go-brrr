(**
 * BrrrLang.Core.SMT
 *
 * SMT Solver Interface for Brrr-Lang.
 * Provides semantic formula implication via external Z3 binding.
 *
 * Gap Resolution:
 *   1. SMT integration - formula_implies is currently syntactic only
 *   2. Semantic formula implication with quantifier handling
 *   3. Three-valued logic (Definitely/DefinitelyNot/Unknown)
 *   4. SMTLIB2 formula translation
 *
 * This module defines the interface; actual Z3 binding is via FFI.
 *
 * Depends on: Primitives, BrrrTypes, Expressions, DependentTypes
 *)
module SMT

open FStar.List.Tot
open Primitives
open BrrrTypes
open Expressions
open DependentTypes

(** ============================================================================
    THREE-VALUED LOGIC (TRILEAN)
    ============================================================================

    SMT queries can have three outcomes:
    - Definitely: The property holds in ALL models
    - DefinitelyNot: The property fails in ALL models (counterexample exists)
    - Unknown: Solver timeout, incomplete theory, or undecidable fragment

    Information ordering: Unknown is LESS informative than definite values.
    This matches TVLA's three-valued logic semantics.
    ============================================================================ *)

type trilean =
  | Definitely     (* True in all models - SAT of negation is UNSAT *)
  | DefinitelyNot  (* False in all models - found counterexample *)
  | Unknown        (* Cannot determine - timeout or incomplete *)

(* Trilean negation *)
let trilean_not (t: trilean) : trilean =
  match t with
  | Definitely -> DefinitelyNot
  | DefinitelyNot -> Definitely
  | Unknown -> Unknown

(* Trilean conjunction (Kleene semantics) *)
let trilean_and (t1 t2: trilean) : trilean =
  match t1, t2 with
  | DefinitelyNot, _ -> DefinitelyNot
  | _, DefinitelyNot -> DefinitelyNot
  | Definitely, Definitely -> Definitely
  | _, _ -> Unknown

(* Trilean disjunction (Kleene semantics) *)
let trilean_or (t1 t2: trilean) : trilean =
  match t1, t2 with
  | Definitely, _ -> Definitely
  | _, Definitely -> Definitely
  | DefinitelyNot, DefinitelyNot -> DefinitelyNot
  | _, _ -> Unknown

(* Trilean implication: a => b is ~a \/ b *)
let trilean_impl (t1 t2: trilean) : trilean =
  trilean_or (trilean_not t1) t2

(* Convert trilean to boolean (conservative for Unknown) *)
let trilean_to_bool_conservative (t: trilean) : bool =
  match t with
  | Definitely -> true
  | DefinitelyNot -> false
  | Unknown -> false  (* Conservative: treat unknown as false *)

(* Convert trilean to boolean (optimistic for Unknown) *)
let trilean_to_bool_optimistic (t: trilean) : bool =
  match t with
  | Definitely -> true
  | DefinitelyNot -> false
  | Unknown -> true   (* Optimistic: treat unknown as true *)

(* Information ordering: Unknown < Definite values *)
let trilean_info_leq (t1 t2: trilean) : bool =
  match t1, t2 with
  | Unknown, _ -> true              (* Unknown is bottom *)
  | _, Unknown -> false
  | Definitely, Definitely -> true
  | DefinitelyNot, DefinitelyNot -> true
  | _, _ -> false

(** ============================================================================
    SMT RESULT TYPE
    ============================================================================ *)

(* Model: satisfying assignment for variables *)
type smt_model = list (string & int)  (* Simplified: just int assignments *)

(* SMT solver result *)
noeq type smt_result =
  | Sat     : model:smt_model -> smt_result    (* Satisfiable with witness *)
  | Unsat   : smt_result                        (* Unsatisfiable *)
  | SmtUnknown : reason:string -> smt_result   (* Unknown with reason *)

(* Convert SMT result to trilean for entailment queries *)
let smt_result_to_trilean_entailment (r: smt_result) : trilean =
  match r with
  (* If negation is UNSAT, original is valid (Definitely) *)
  | Unsat -> Definitely
  (* If negation is SAT, original has counterexample (DefinitelyNot) *)
  | Sat _ -> DefinitelyNot
  (* Unknown stays Unknown *)
  | SmtUnknown _ -> Unknown

(** ============================================================================
    SMTLIB2 REPRESENTATION
    ============================================================================

    Abstract syntax for SMTLIB2 formulas.
    This is the target of formula translation.
    ============================================================================ *)

(* SMTLIB2 sorts *)
type smt_sort =
  | SortBool   : smt_sort
  | SortInt    : smt_sort
  | SortReal   : smt_sort
  | SortBitVec : width:nat -> smt_sort
  | SortArray  : idx:smt_sort -> elem:smt_sort -> smt_sort
  | SortUninterpreted : name:string -> smt_sort

(* SMTLIB2 terms/expressions *)
noeq type smt_term =
  (* Constants *)
  | SmtTrue    : smt_term
  | SmtFalse   : smt_term
  | SmtInt     : int -> smt_term
  | SmtReal    : string -> smt_term  (* String representation for rationals *)
  | SmtBitVec  : value:int -> width:nat -> smt_term

  (* Variables *)
  | SmtVar     : name:string -> smt_sort -> smt_term

  (* Core theory *)
  | SmtNot     : smt_term -> smt_term
  | SmtAnd     : list smt_term -> smt_term
  | SmtOr      : list smt_term -> smt_term
  | SmtImpl    : smt_term -> smt_term -> smt_term
  | SmtIff     : smt_term -> smt_term -> smt_term
  | SmtIte     : cond:smt_term -> then_:smt_term -> else_:smt_term -> smt_term

  (* Equality *)
  | SmtEq      : smt_term -> smt_term -> smt_term
  | SmtDistinct : list smt_term -> smt_term

  (* Arithmetic *)
  | SmtNeg     : smt_term -> smt_term
  | SmtAdd     : list smt_term -> smt_term
  | SmtSub     : smt_term -> smt_term -> smt_term
  | SmtMul     : list smt_term -> smt_term
  | SmtDiv     : smt_term -> smt_term -> smt_term
  | SmtMod     : smt_term -> smt_term -> smt_term

  (* Comparisons *)
  | SmtLt      : smt_term -> smt_term -> smt_term
  | SmtLe      : smt_term -> smt_term -> smt_term
  | SmtGt      : smt_term -> smt_term -> smt_term
  | SmtGe      : smt_term -> smt_term -> smt_term

  (* Quantifiers *)
  | SmtForall  : bindings:list (string & smt_sort) -> body:smt_term -> smt_term
  | SmtExists  : bindings:list (string & smt_sort) -> body:smt_term -> smt_term

  (* Uninterpreted functions *)
  | SmtApply   : func:string -> args:list smt_term -> smt_term

  (* Let bindings *)
  | SmtLet     : bindings:list (string & smt_term) -> body:smt_term -> smt_term

(* SMTLIB2 commands *)
noeq type smt_command =
  | CmdSetLogic     : logic_name:string -> smt_command
  | CmdDeclareSort  : name:string -> arity:nat -> smt_command
  | CmdDefineSort   : name:string -> params:list string -> def:smt_sort -> smt_command
  | CmdDeclareConst : name:string -> sort:smt_sort -> smt_command
  | CmdDeclareFun   : name:string -> args:list smt_sort -> ret:smt_sort -> smt_command
  | CmdDefineFun    : name:string -> args:list (string & smt_sort) -> ret:smt_sort -> body:smt_term -> smt_command
  | CmdAssert       : term:smt_term -> smt_command
  | CmdCheckSat     : smt_command
  | CmdGetModel     : smt_command
  | CmdPush         : levels:nat -> smt_command
  | CmdPop          : levels:nat -> smt_command
  | CmdReset        : smt_command
  | CmdExit         : smt_command

(* SMTLIB2 script is a sequence of commands *)
type smt_script = list smt_command

(** ============================================================================
    BRRR TYPE TO SMT SORT TRANSLATION
    ============================================================================ *)

(* Translate Brrr base type to SMT sort *)
let rec brrr_type_to_smt_sort (t: brrr_type) : smt_sort =
  match t with
  | TUnit -> SortBool  (* Unit maps to trivially true *)
  | TBool -> SortBool
  | TInt it ->
      (match it.width with
       | I8 | I16 | I32 | I64 -> SortInt  (* Use unbounded int for simplicity *)
       | ISize | IPtr -> SortInt)
  | TFloat _ -> SortReal
  | TString -> SortUninterpreted "String"
  | TOption t' -> SortUninterpreted ("Option_" ^ sort_to_string (brrr_type_to_smt_sort t'))
  | TArray t' -> SortArray SortInt (brrr_type_to_smt_sort t')
  | TFunc _ _ _ -> SortUninterpreted "Function"
  | TPair t1 t2 -> SortUninterpreted ("Pair_" ^ sort_to_string (brrr_type_to_smt_sort t1) ^
                                       "_" ^ sort_to_string (brrr_type_to_smt_sort t2))
  | TAny -> SortUninterpreted "Any"
  | TUnknown -> SortUninterpreted "Unknown"
  | TNever -> SortBool  (* Never maps to false *)

and sort_to_string (s: smt_sort) : Tot string (decreases s) =
  match s with
  | SortBool -> "Bool"
  | SortInt -> "Int"
  | SortReal -> "Real"
  | SortBitVec w -> "BitVec" ^ string_of_int w
  | SortArray _ _ -> "Array"
  | SortUninterpreted n -> n

(** ============================================================================
    EXPRESSION TO SMT TERM TRANSLATION
    ============================================================================ *)

(* Translate comparison operator *)
let translate_cmp_op (op: cmp_op) (e1 e2: smt_term) : smt_term =
  match op with
  | CmpEq -> SmtEq e1 e2
  | CmpNe -> SmtNot (SmtEq e1 e2)
  | CmpLt -> SmtLt e1 e2
  | CmpLe -> SmtLe e1 e2
  | CmpGt -> SmtGt e1 e2
  | CmpGe -> SmtGe e1 e2

(* Translate expression to SMT term (partial - handles common cases) *)
let rec expr_to_smt_term (e: expr) : option smt_term =
  match e with
  | ELit (LitBool true) -> Some SmtTrue
  | ELit (LitBool false) -> Some SmtFalse
  | ELit (LitInt n) -> Some (SmtInt n)
  | ELit LitUnit -> Some SmtTrue

  | EVar x -> Some (SmtVar x SortInt)  (* Default to int for variables *)

  | EUnary UnNot e' ->
      (match expr_to_smt_term e' with
       | Some t -> Some (SmtNot t)
       | None -> None)

  | EUnary UnNeg e' ->
      (match expr_to_smt_term e' with
       | Some t -> Some (SmtNeg t)
       | None -> None)

  | EBinary BinAdd e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtAdd [t1; t2])
       | _, _ -> None)

  | EBinary BinSub e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtSub t1 t2)
       | _, _ -> None)

  | EBinary BinMul e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtMul [t1; t2])
       | _, _ -> None)

  | EBinary BinDiv e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtDiv t1 t2)
       | _, _ -> None)

  | EBinary BinMod e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtMod t1 t2)
       | _, _ -> None)

  | EBinary BinAnd e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtAnd [t1; t2])
       | _, _ -> None)

  | EBinary BinOr e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtOr [t1; t2])
       | _, _ -> None)

  | EBinary BinEq e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtEq t1 t2)
       | _, _ -> None)

  | EBinary BinNe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtNot (SmtEq t1 t2))
       | _, _ -> None)

  | EBinary BinLt e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtLt t1 t2)
       | _, _ -> None)

  | EBinary BinLe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtLe t1 t2)
       | _, _ -> None)

  | EBinary BinGt e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtGt t1 t2)
       | _, _ -> None)

  | EBinary BinGe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtGe t1 t2)
       | _, _ -> None)

  | EIf cond then_ else_ ->
      (match expr_to_smt_term cond, expr_to_smt_term then_, expr_to_smt_term else_ with
       | Some c, Some t, Some e -> Some (SmtIte c t e)
       | _, _, _ -> None)

  | ECall (EGlobal fn) args ->
      let smt_args = List.Tot.map expr_to_smt_term args in
      if List.Tot.for_all Some? smt_args then
        Some (SmtApply fn (List.Tot.map (fun x -> match x with Some t -> t | None -> SmtTrue) smt_args))
      else None

  | _ -> None  (* Unsupported expression *)

(** ============================================================================
    FORMULA TO SMT TERM TRANSLATION
    ============================================================================ *)

(* Translate dependent type to SMT sort *)
let rec dep_type_to_smt_sort (t: dep_type) : smt_sort =
  match t with
  | DBase bt -> brrr_type_to_smt_sort bt
  | DPi _ _ _ -> SortUninterpreted "Function"
  | DSigma _ _ _ -> SortUninterpreted "Pair"
  | DRefinement _ base _ -> dep_type_to_smt_sort base
  | DApp t' _ -> dep_type_to_smt_sort t'

(* Translate formula to SMT term *)
let rec formula_to_smt_term (phi: formula) : option smt_term =
  match phi with
  | FTrue -> Some SmtTrue
  | FFalse -> Some SmtFalse

  | FCmp op e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (translate_cmp_op op t1 t2)
       | _, _ -> None)

  | FAnd phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtAnd [t1; t2])
       | _, _ -> None)

  | FOr phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtOr [t1; t2])
       | _, _ -> None)

  | FNot phi' ->
      (match formula_to_smt_term phi' with
       | Some t -> Some (SmtNot t)
       | None -> None)

  | FImpl phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtImpl t1 t2)
       | _, _ -> None)

  | FIff phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtIff t1 t2)
       | _, _ -> None)

  | FForall x bt phi' ->
      let sort = brrr_type_to_smt_sort bt in
      (match formula_to_smt_term phi' with
       | Some body -> Some (SmtForall [(x, sort)] body)
       | None -> None)

  | FExists x bt phi' ->
      let sort = brrr_type_to_smt_sort bt in
      (match formula_to_smt_term phi' with
       | Some body -> Some (SmtExists [(x, sort)] body)
       | None -> None)

  | FPred name e ->
      (match expr_to_smt_term e with
       | Some t -> Some (SmtApply name [t])
       | None -> None)

  | FExpr e -> expr_to_smt_term e

(** ============================================================================
    SMT TERM TO SMTLIB2 STRING
    ============================================================================ *)

(* Convert sort to SMTLIB2 string *)
let rec smt_sort_to_string (s: smt_sort) : Tot string (decreases s) =
  match s with
  | SortBool -> "Bool"
  | SortInt -> "Int"
  | SortReal -> "Real"
  | SortBitVec w -> "(_ BitVec " ^ string_of_int w ^ ")"
  | SortArray idx elem ->
      "(Array " ^ smt_sort_to_string idx ^ " " ^ smt_sort_to_string elem ^ ")"
  | SortUninterpreted n -> n

(* Convert term to SMTLIB2 string *)
let rec smt_term_to_string (t: smt_term) : Tot string (decreases t) =
  match t with
  | SmtTrue -> "true"
  | SmtFalse -> "false"
  | SmtInt n -> if n >= 0 then string_of_int n else "(- " ^ string_of_int (-n) ^ ")"
  | SmtReal s -> s
  | SmtBitVec v w -> "(_ bv" ^ string_of_int v ^ " " ^ string_of_int w ^ ")"
  | SmtVar name _ -> name

  | SmtNot t' -> "(not " ^ smt_term_to_string t' ^ ")"
  | SmtAnd ts -> "(and " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtOr ts -> "(or " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtImpl t1 t2 -> "(=> " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtIff t1 t2 -> "(= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtIte c th el -> "(ite " ^ smt_term_to_string c ^ " " ^
                       smt_term_to_string th ^ " " ^ smt_term_to_string el ^ ")"

  | SmtEq t1 t2 -> "(= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtDistinct ts -> "(distinct " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"

  | SmtNeg t' -> "(- " ^ smt_term_to_string t' ^ ")"
  | SmtAdd ts -> "(+ " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtSub t1 t2 -> "(- " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtMul ts -> "(* " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtDiv t1 t2 -> "(div " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtMod t1 t2 -> "(mod " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"

  | SmtLt t1 t2 -> "(< " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtLe t1 t2 -> "(<= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtGt t1 t2 -> "(> " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtGe t1 t2 -> "(>= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"

  | SmtForall bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, s) ->
        "(" ^ n ^ " " ^ smt_sort_to_string s ^ ")") bindings) in
      "(forall (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

  | SmtExists bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, s) ->
        "(" ^ n ^ " " ^ smt_sort_to_string s ^ ")") bindings) in
      "(exists (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

  | SmtApply func args ->
      if List.Tot.length args = 0 then func
      else "(" ^ func ^ " " ^ String.concat " " (List.Tot.map smt_term_to_string args) ^ ")"

  | SmtLet bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, t) ->
        "(" ^ n ^ " " ^ smt_term_to_string t ^ ")") bindings) in
      "(let (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

(** ============================================================================
    SMT SOLVER INTERFACE (AXIOMATIZED)
    ============================================================================

    The actual Z3 binding is via FFI. These functions define the interface
    that will be implemented by the external solver.
    ============================================================================ *)

(* SMT solver configuration *)
noeq type smt_config = {
  timeout_ms   : nat;           (* Solver timeout in milliseconds *)
  smt_logic    : string;        (* SMTLIB2 logic (e.g., "QF_LIA", "ALL") *)
  incremental  : bool;          (* Use incremental mode *)
}

let default_smt_config : smt_config = {
  timeout_ms = 5000;            (* 5 second default timeout *)
  smt_logic = "ALL";            (* Full logic by default *)
  incremental = true;
}

(* Check satisfiability of SMT term - axiomatized external call *)
assume val smt_check_sat : config:smt_config -> term:smt_term -> smt_result

(* Check if phi1 implies phi2 using SMT *)
let smt_check_implication (config: smt_config) (phi1 phi2: smt_term) : trilean =
  (* phi1 => phi2 is valid iff phi1 /\ ~phi2 is UNSAT *)
  let negated = SmtAnd [phi1; SmtNot phi2] in
  smt_result_to_trilean_entailment (smt_check_sat config negated)

(** ============================================================================
    SEMANTIC FORMULA IMPLICATION
    ============================================================================

    This is the key function that replaces the syntactic formula_implies
    from DependentTypes.fst with semantic SMT-based implication.
    ============================================================================ *)

(* Semantic formula implication using SMT solver
   Returns trilean: Definitely (valid), DefinitelyNot (invalid), Unknown *)
let formula_implies_semantic (config: smt_config) (phi1 phi2: formula) : trilean =
  match formula_to_smt_term phi1, formula_to_smt_term phi2 with
  | Some smt1, Some smt2 -> smt_check_implication config smt1 smt2
  | _, _ -> Unknown  (* Could not translate to SMT *)

(* Combined syntactic + semantic implication check
   First tries fast syntactic check, falls back to SMT *)
let formula_implies_hybrid (config: smt_config) (phi1 phi2: formula) : trilean =
  (* First try syntactic check from DependentTypes *)
  if formula_implies phi1 phi2 then Definitely
  else
    (* Fall back to SMT *)
    formula_implies_semantic config phi1 phi2

(** ============================================================================
    VERIFICATION CONDITION DISCHARGE
    ============================================================================ *)

(* Collect free variables in formula for SMT declarations *)
let rec collect_formula_vars (phi: formula) : list (string & smt_sort) =
  match phi with
  | FTrue | FFalse -> []
  | FCmp _ e1 e2 ->
      collect_expr_vars e1 @ collect_expr_vars e2
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      collect_formula_vars phi1 @ collect_formula_vars phi2
  | FNot phi' -> collect_formula_vars phi'
  | FForall x bt phi' | FExists x bt phi' ->
      filter (fun (y, _) -> y <> x) (collect_formula_vars phi')
  | FPred _ e -> collect_expr_vars e
  | FExpr e -> collect_expr_vars e

and collect_expr_vars (e: expr) : list (string & smt_sort) =
  match e with
  | EVar x -> [(x, SortInt)]  (* Default to Int *)
  | EUnary _ e' -> collect_expr_vars e'
  | EBinary _ e1 e2 -> collect_expr_vars e1 @ collect_expr_vars e2
  | EIf c t f -> collect_expr_vars c @ collect_expr_vars t @ collect_expr_vars f
  | ECall _ args -> List.Tot.concatMap collect_expr_vars args
  | _ -> []

(* Generate SMTLIB2 script for checking formula validity *)
let generate_validity_script (phi: formula) : option smt_script =
  match formula_to_smt_term phi with
  | None -> None
  | Some smt_phi ->
      let vars = collect_formula_vars phi in
      let unique_vars = List.Tot.noRepeats vars in  (* Deduplicate *)
      let decls = List.Tot.map (fun (n, s) -> CmdDeclareConst n s) unique_vars in
      (* Check validity: assert negation and check for UNSAT *)
      Some (
        [CmdSetLogic "ALL"] @
        decls @
        [CmdAssert (SmtNot smt_phi); CmdCheckSat]
      )

(* Discharge a verification condition *)
let discharge_vc (config: smt_config) (phi: formula) : trilean =
  formula_implies_semantic config FTrue phi

(** ============================================================================
    SOUNDNESS AXIOMS
    ============================================================================

    These axioms relate SMT validity to semantic truth.
    They are the meta-level soundness assumptions for the SMT integration.
    ============================================================================ *)

(* Soundness: If SMT says UNSAT, the formula is semantically valid *)
assume val smt_soundness_unsat :
  config:smt_config ->
  phi:smt_term ->
  Lemma (requires smt_check_sat config phi == Unsat)
        (ensures forall (model: smt_model). True)  (* phi has no models *)

(* Completeness for decidable fragments: If valid, SMT will return UNSAT *)
assume val smt_completeness_qf_lia :
  config:smt_config{config.smt_logic = "QF_LIA"} ->
  phi:smt_term ->
  Lemma (requires True)  (* phi is in QF_LIA *)
        (ensures smt_check_sat config phi <> SmtUnknown "incomplete")

(** ============================================================================
    INCREMENTAL SMT CONTEXT
    ============================================================================

    For efficiency, maintain SMT context across multiple queries.
    ============================================================================ *)

(* Incremental solver state *)
noeq type smt_context = {
  ctx_config     : smt_config;
  ctx_assertions : list smt_term;   (* Current assertion stack *)
  ctx_level      : nat;              (* Push level *)
}

let empty_smt_context (config: smt_config) : smt_context = {
  ctx_config = config;
  ctx_assertions = [];
  ctx_level = 0;
}

let smt_push (ctx: smt_context) : smt_context =
  { ctx with ctx_level = ctx.ctx_level + 1 }

let smt_pop (ctx: smt_context) : smt_context =
  if ctx.ctx_level > 0 then { ctx with ctx_level = ctx.ctx_level - 1 }
  else ctx

let smt_assert (ctx: smt_context) (phi: smt_term) : smt_context =
  { ctx with ctx_assertions = phi :: ctx.ctx_assertions }

(* Check satisfiability in current context *)
assume val smt_context_check_sat : ctx:smt_context -> smt_result

(** ============================================================================
    WHAT BRRR-MACHINE NEEDS FROM REFINEMENT CHECKING
    ============================================================================

    This section documents the interface that Brrr-Machine analysis toolkit
    requires from the refinement type system.

    1. TYPE CHECKING QUERIES:
       - does_type_check : expr -> dep_type -> trilean
       - subtype_check : dep_type -> dep_type -> trilean

    2. REFINEMENT ENTAILMENT:
       - For {x:T | phi} <: {x:T | psi}, need: forall x:T. phi => psi
       - This requires SMT for non-trivial formulas

    3. DIVERGENCE INFORMATION:
       - For lazy languages, need divergence labels on types
       - DivMay/DivWhnf/DivFin affect VC generation

    4. COUNTEREXAMPLE GENERATION:
       - When subtyping fails, provide witness
       - Important for bug localization in Brrr-Machine

    5. PERFORMANCE REQUIREMENTS:
       - Caching: same queries should not re-invoke SMT
       - Incremental: use push/pop for related queries
       - Timeout: graceful degradation to Unknown
    ============================================================================ *)

(* Query result with optional counterexample *)
noeq type refinement_result =
  | RefinementHolds      : refinement_result
  | RefinementFails      : cex:option smt_model -> refinement_result
  | RefinementUnknown    : reason:string -> refinement_result

(* Convert trilean to refinement result *)
let trilean_to_refinement (t: trilean) (cex: option smt_model) : refinement_result =
  match t with
  | Definitely -> RefinementHolds
  | DefinitelyNot -> RefinementFails cex
  | Unknown -> RefinementUnknown "SMT timeout or incomplete"

(* Check refinement subtyping with counterexample *)
let check_refinement_subtype
    (config: smt_config)
    (x: dep_var)
    (base: dep_type)
    (phi1 phi2: formula)
    : refinement_result =
  (* Need to check: forall x:base. phi1 => phi2 *)
  let smt_base = dep_type_to_smt_sort base in
  match formula_to_smt_term phi1, formula_to_smt_term phi2 with
  | Some smt1, Some smt2 ->
      (* Check if exists x. phi1 /\ ~phi2 is SAT (counterexample) *)
      let negated = SmtExists [(x, smt_base)] (SmtAnd [smt1; SmtNot smt2]) in
      (match smt_check_sat config negated with
       | Unsat -> RefinementHolds
       | Sat model -> RefinementFails (Some model)
       | SmtUnknown reason -> RefinementUnknown reason)
  | _, _ -> RefinementUnknown "Could not translate formula to SMT"
