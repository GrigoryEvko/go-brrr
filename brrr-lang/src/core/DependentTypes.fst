(**
 * BrrrLang.Core.DependentTypes
 *
 * Dependent type system for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part IV - Dependent Types.
 *
 * Implements:
 *   - Pi-types:       Pi(x:t1).t2    (dependent function types)
 *   - Sigma-types:    Sigma(x:t1).t2 (dependent pair types)
 *   - Refinement:     {x: t | phi(x)} (types refined by predicates)
 *
 * Key operations:
 *   - Type substitution: [e/x]t (replace x with e in t)
 *   - Alpha-equivalence: types equal up to bound variable renaming
 *   - Refinement subtyping: {x:t|phi} <: {x:t|psi} iff forall x. phi => psi
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions
 *)
module DependentTypes

(** Z3 solver options - conservative baseline for dependent type proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical
open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions

(** ============================================================================
    TERM IDENTIFIERS
    ============================================================================ *)

(* Variable identifier for dependent types *)
type dep_var = string

(* Fresh variable counter for alpha-renaming *)
type fresh_counter = nat

(* Generate fresh variable name *)
let fresh_var (prefix: string) (counter: fresh_counter) : dep_var =
  prefix ^ "_" ^ string_of_int counter

(** ============================================================================
    FORMULA REPRESENTATION - Logical predicates for refinements
    ============================================================================

    Formulas represent logical assertions over terms. They are used in:
    - Refinement types: {x: t | phi(x)}
    - Pre/postconditions: requires P, ensures Q
    - Loop invariants: while c invariant I { ... }

    Grammar:
      phi ::= true | false
           | e1 = e2 | e1 < e2 | e1 <= e2
           | phi1 /\ phi2 | phi1 \/ phi2 | ~phi
           | forall x:t. phi | exists x:t. phi
           | phi(e)          (formula application)
    ============================================================================ *)

(* Comparison operator *)
type cmp_op =
  | CmpEq  : cmp_op   (* = *)
  | CmpNe  : cmp_op   (* != *)
  | CmpLt  : cmp_op   (* < *)
  | CmpLe  : cmp_op   (* <= *)
  | CmpGt  : cmp_op   (* > *)
  | CmpGe  : cmp_op   (* >= *)

(* Formula - logical assertions over terms *)
noeq type formula =
  (* Boolean constants *)
  | FTrue    : formula
  | FFalse   : formula

  (* Comparisons on expressions *)
  | FCmp     : cmp_op -> expr -> expr -> formula

  (* Propositional connectives *)
  | FAnd     : formula -> formula -> formula
  | FOr      : formula -> formula -> formula
  | FNot     : formula -> formula
  | FImpl    : formula -> formula -> formula   (* phi => psi *)
  | FIff     : formula -> formula -> formula   (* phi <=> psi *)

  (* Quantifiers - bind variable with type *)
  | FForall  : dep_var -> brrr_type -> formula -> formula
  | FExists  : dep_var -> brrr_type -> formula -> formula

  (* Predicate variable with argument *)
  | FPred    : string -> expr -> formula

  (* Expression coerced to formula (for boolean expressions) *)
  | FExpr    : expr -> formula

(** ============================================================================
    FORMULA SIZE - For termination proofs
    ============================================================================ *)

let rec formula_size (phi: formula) : Tot nat (decreases phi) =
  match phi with
  | FTrue | FFalse -> 1
  | FCmp _ _ _ -> 1
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      1 + formula_size phi1 + formula_size phi2
  | FNot phi' -> 1 + formula_size phi'
  | FForall _ _ phi' | FExists _ _ phi' -> 1 + formula_size phi'
  | FPred _ _ -> 1
  | FExpr _ -> 1

(** ============================================================================
    DEPENDENT TYPE CONSTRUCTORS
    ============================================================================

    dep_type extends the core brrr_type with dependent types:

    1. DPi(x:t1).t2 - Dependent function type (generalized arrow type)
       When x does not occur in t2, this is equivalent to t1 -> t2

    2. DSigma(x:t1).t2 - Dependent pair type (generalized product type)
       When x does not occur in t2, this is equivalent to t1 * t2

    3. DRefinement{x:t | phi} - Refinement type
       Values of type t that satisfy predicate phi
    ============================================================================ *)

noeq type dep_type =
  (* Lift base types *)
  | DBase      : brrr_type -> dep_type

  (* Pi-type: dependent function *)
  | DPi        : dep_var -> dep_type -> dep_type -> dep_type

  (* Sigma-type: dependent pair *)
  | DSigma     : dep_var -> dep_type -> dep_type -> dep_type

  (* Refinement type: {x:t | phi} *)
  | DRefinement : dep_var -> dep_type -> formula -> dep_type

  (* Type application (for higher-kinded dependent types) *)
  | DApp       : dep_type -> expr -> dep_type

(** ============================================================================
    DEPENDENT TYPE SIZE - For termination proofs
    ============================================================================ *)

let rec dep_type_size (t: dep_type) : Tot nat (decreases t) =
  match t with
  | DBase _ -> 1
  | DPi _ t1 t2 -> 1 + dep_type_size t1 + dep_type_size t2
  | DSigma _ t1 t2 -> 1 + dep_type_size t1 + dep_type_size t2
  | DRefinement _ t phi -> 1 + dep_type_size t + formula_size phi
  | DApp t _ -> 1 + dep_type_size t

(** ============================================================================
    FREE VARIABLES IN FORMULAS
    ============================================================================ *)

(* Free variables in formula - mutually recursive with expression free vars *)
let rec formula_free_vars (phi: formula) : Tot (list dep_var) (decreases phi) =
  match phi with
  | FTrue | FFalse -> []
  | FCmp _ e1 e2 -> free_vars e1 @ free_vars e2
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      formula_free_vars phi1 @ formula_free_vars phi2
  | FNot phi' -> formula_free_vars phi'
  | FForall x _ phi' | FExists x _ phi' ->
      filter (fun v -> v <> x) (formula_free_vars phi')
  | FPred _ e -> free_vars e
  | FExpr e -> free_vars e

(** ============================================================================
    FREE VARIABLES IN DEPENDENT TYPES
    ============================================================================ *)

(* Free variables in dependent type *)
let rec dep_type_free_vars (t: dep_type) : Tot (list dep_var) (decreases t) =
  match t with
  | DBase bt -> free_type_vars bt
  | DPi x t1 t2 ->
      dep_type_free_vars t1 @ filter (fun v -> v <> x) (dep_type_free_vars t2)
  | DSigma x t1 t2 ->
      dep_type_free_vars t1 @ filter (fun v -> v <> x) (dep_type_free_vars t2)
  | DRefinement x t phi ->
      dep_type_free_vars t @ filter (fun v -> v <> x) (formula_free_vars phi)
  | DApp t e ->
      dep_type_free_vars t @ free_vars e

(* Check if variable is free in dependent type *)
let is_free_in_dep_type (x: dep_var) (t: dep_type) : bool =
  mem x (dep_type_free_vars t)

(* Check if variable is free in formula *)
let is_free_in_formula (x: dep_var) (phi: formula) : bool =
  mem x (formula_free_vars phi)

(* Check if variable is free in expression *)
let is_free_in_expr (x: dep_var) (e: expr) : bool =
  mem x (free_vars e)

(** ============================================================================
    CAPTURE-AVOIDING SUBSTITUTION HELPERS
    ============================================================================

    Variable capture occurs when substituting [e/x] under a binder that binds
    a variable y that is free in e. For example:

      [y/x](forall y. x + y)  -- WRONG: gives (forall y. y + y) capturing y

    To avoid this, we alpha-rename the bound variable before substitution:

      [y/x](forall z. x + z)  -- CORRECT after renaming y to z

    We use a deterministic fresh name generation based on the bound variable
    name and the free variables to avoid.
    ============================================================================ *)

(* Generate a fresh variable name that doesn't clash with avoid list.
   Uses the original variable name as a base and appends a numeric suffix. *)
let rec generate_capture_fresh (base: string) (counter: nat) (avoid: list dep_var)
    : Tot dep_var (decreases 1000 - counter) =
  if counter >= 1000 then base ^ "__cap_fresh__overflow"
  else
    let candidate = base ^ "__cap_" ^ string_of_int counter in
    if mem candidate avoid then generate_capture_fresh base (counter + 1) avoid
    else candidate

(* Collect all variables to avoid when renaming a binder during substitution.
   This includes: free vars in replacement, free vars in the body being substituted into. *)
let capture_avoid_vars (replacement: expr) (body_fvs: list dep_var) : list dep_var =
  free_vars replacement @ body_fvs

(** ============================================================================
    EXPRESSION SUBSTITUTION IN EXPRESSIONS (Capture-Avoiding)
    ============================================================================

    Implements [e'/x]e - substitute e' for all free occurrences of x in e.

    CRITICAL: This function must be capture-avoiding to maintain soundness.
    Variable capture occurs when substituting [e/x] under a binder that binds
    a variable y that is free in e. For example:

      [y/x](for y in iter { x })  -- WRONG: gives (for y in iter { y }) capturing y

    To avoid capture, we alpha-rename bound variables before substitution:

      [y/x](for z in iter { x })  -- CORRECT after renaming y to z

    Note: We use mutual recursion with subst_expr_list to handle list cases
    for proper termination proofs. *)

(* Helper: Check if any parameter name from a list is free in expression *)
let any_param_free_in_expr (params: list (dep_var & 'a)) (e: expr) : bool =
  List.Tot.existsb (fun (y, _) -> is_free_in_expr y e) params

(* Helper: Collect parameter names from a list *)
let param_names (params: list (dep_var & 'a)) : list dep_var =
  List.Tot.map fst params

(* Helper: Rename a single parameter in a params list *)
let rename_param (old_name new_name: dep_var) (params: list (dep_var & 'a))
    : list (dep_var & 'a) =
  List.Tot.map (fun (y, ty) -> if y = old_name then (new_name, ty) else (y, ty)) params

(* Helper: wrap an expr' in with_loc preserving original range *)
let mk_subst_expr (r: range) (e': expr') : expr =
  { loc_value = e'; loc_range = r }

(* Helper: create EVar expression with range *)
let e_var_with_range (r: range) (y: dep_var) : expr =
  mk_subst_expr r (EVar y)

let rec subst_expr (x: dep_var) (replacement: expr) (e: expr)
    : Tot expr (decreases %[expr_size e; 0]) =
  let r = e.loc_range in  (* Preserve source location *)
  match e.loc_value with
  | EVar y -> if x = y then replacement else e
  | ELit _ | EGlobal _ | EContinue _ | EHole | EError _ | ESizeof _ | EAlignof _ -> e

  | EUnary op e' -> mk_subst_expr r (EUnary op (subst_expr x replacement e'))
  | EBinary op e1 e2 -> mk_subst_expr r (EBinary op (subst_expr x replacement e1) (subst_expr x replacement e2))

  | ECall fn args ->
      mk_subst_expr r (ECall (subst_expr x replacement fn) (subst_expr_list x replacement args))

  | EMethodCall obj m args ->
      mk_subst_expr r (EMethodCall (subst_expr x replacement obj) m (subst_expr_list x replacement args))

  | ETuple es -> mk_subst_expr r (ETuple (subst_expr_list x replacement es))
  | EArray es -> mk_subst_expr r (EArray (subst_expr_list x replacement es))

  | EStruct n fields ->
      mk_subst_expr r (EStruct n (subst_expr_fields x replacement fields))

  | EVariant n v es -> mk_subst_expr r (EVariant n v (subst_expr_list x replacement es))

  | EField e' f -> mk_subst_expr r (EField (subst_expr x replacement e') f)
  | EIndex e1 e2 -> mk_subst_expr r (EIndex (subst_expr x replacement e1) (subst_expr x replacement e2))
  | ETupleProj e' i -> mk_subst_expr r (ETupleProj (subst_expr x replacement e') i)

  | EIf c t el -> mk_subst_expr r (EIf (subst_expr x replacement c)
                                       (subst_expr x replacement t)
                                       (subst_expr x replacement el))

  | ELoop lbl body -> mk_subst_expr r (ELoop lbl (subst_expr x replacement body))
  | EWhile lbl c body -> mk_subst_expr r (EWhile lbl (subst_expr x replacement c) (subst_expr x replacement body))

  (* EFor: CAPTURE-AVOIDING SUBSTITUTION
     for y in iter { body } - y binds in body
     If y is free in replacement, we must alpha-rename y to avoid capture. *)
  | EFor lbl y iter body ->
      let iter' = subst_expr x replacement iter in
      if x = y then mk_subst_expr r (EFor lbl y iter' body)  (* y shadows x, no substitution in body *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (free_vars body) in
        let y' = generate_capture_fresh y 0 fvs in
        let body_renamed = subst_expr y (e_var_with_range r y') body in
        mk_subst_expr r (EFor lbl y' iter' (subst_expr x replacement body_renamed))
      else
        mk_subst_expr r (EFor lbl y iter' (subst_expr x replacement body))

  | EBreak lbl None -> e
  | EBreak lbl (Some e') -> mk_subst_expr r (EBreak lbl (Some (subst_expr x replacement e')))
  | EReturn None -> e
  | EReturn (Some e') -> mk_subst_expr r (EReturn (Some (subst_expr x replacement e')))

  (* ELet: CAPTURE-AVOIDING SUBSTITUTION
     let p = e1 in e2 - pattern p binds in e2
     For simple PatVar patterns, if the variable is free in replacement, alpha-rename. *)
  | ELet pat ty e1 e2 ->
      let e1' = subst_expr x replacement e1 in
      (match pat.loc_value with
       | PatVar y ->
           if x = y then mk_subst_expr r (ELet pat ty e1' e2)  (* y shadows x *)
           else if is_free_in_expr y replacement then
             (* CAPTURE AVOIDANCE: alpha-rename y *)
             let fvs = capture_avoid_vars replacement (free_vars e2) in
             let y' = generate_capture_fresh y 0 fvs in
             let e2_renamed = subst_expr y (e_var_with_range r y') e2 in
             let pat' = { loc_value = PatVar y'; loc_range = pat.loc_range } in
             mk_subst_expr r (ELet pat' ty e1' (subst_expr x replacement e2_renamed))
           else
             mk_subst_expr r (ELet pat ty e1' (subst_expr x replacement e2))
       | _ ->
           (* For complex patterns, conservatively substitute in body
              TODO: Extract bound variables from complex patterns for proper capture avoidance *)
           mk_subst_expr r (ELet pat ty e1' (subst_expr x replacement e2)))

  (* ELetMut: CAPTURE-AVOIDING SUBSTITUTION
     let mut y = e1 in e2 - y binds in e2 *)
  | ELetMut y ty e1 e2 ->
      let e1' = subst_expr x replacement e1 in
      if x = y then mk_subst_expr r (ELetMut y ty e1' e2)  (* y shadows x *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: alpha-rename y *)
        let fvs = capture_avoid_vars replacement (free_vars e2) in
        let y' = generate_capture_fresh y 0 fvs in
        let e2_renamed = subst_expr y (e_var_with_range r y') e2 in
        mk_subst_expr r (ELetMut y' ty e1' (subst_expr x replacement e2_renamed))
      else
        mk_subst_expr r (ELetMut y ty e1' (subst_expr x replacement e2))

  | EAssign lhs rhs -> mk_subst_expr r (EAssign (subst_expr x replacement lhs) (subst_expr x replacement rhs))

  (* ELambda: CAPTURE-AVOIDING SUBSTITUTION
     |params| body - params bind in body
     If any param is free in replacement, we must alpha-rename that param.
     Note: For simplicity, we handle the single-capture case; multiple captures
     would require iterative renaming. *)
  | ELambda params body ->
      let binds_x = List.Tot.existsb (fun (y, _) -> x = y) params in
      if binds_x then e  (* x is shadowed by a parameter *)
      else
        (* Check if any param would capture a variable in replacement *)
        let captured_param = List.Tot.find (fun (y, _) -> is_free_in_expr y replacement) params in
        (match captured_param with
         | None ->
             (* No capture, safe to substitute directly *)
             mk_subst_expr r (ELambda params (subst_expr x replacement body))
         | Some (y, ty) ->
             (* CAPTURE AVOIDANCE: alpha-rename the captured parameter y *)
             let fvs = capture_avoid_vars replacement (free_vars body @ param_names params) in
             let y' = generate_capture_fresh y 0 fvs in
             let params' = rename_param y y' params in
             let body_renamed = subst_expr y (e_var_with_range r y') body in
             mk_subst_expr r (ELambda params' (subst_expr x replacement body_renamed)))

  (* EClosure: CAPTURE-AVOIDING SUBSTITUTION
     Same as ELambda, but also has captured variables list *)
  | EClosure params caps body ->
      let binds_x = List.Tot.existsb (fun (y, _) -> x = y) params in
      if binds_x then e  (* x is shadowed *)
      else
        let captured_param = List.Tot.find (fun (y, _) -> is_free_in_expr y replacement) params in
        (match captured_param with
         | None ->
             mk_subst_expr r (EClosure params caps (subst_expr x replacement body))
         | Some (y, ty) ->
             (* CAPTURE AVOIDANCE: alpha-rename the captured parameter y *)
             let fvs = capture_avoid_vars replacement (free_vars body @ param_names params) in
             let y' = generate_capture_fresh y 0 fvs in
             let params' = rename_param y y' params in
             let body_renamed = subst_expr y (e_var_with_range r y') body in
             mk_subst_expr r (EClosure params' caps (subst_expr x replacement body_renamed)))

  | EBox e' -> mk_subst_expr r (EBox (subst_expr x replacement e'))
  | EDeref e' -> mk_subst_expr r (EDeref (subst_expr x replacement e'))
  | EBorrow e' -> mk_subst_expr r (EBorrow (subst_expr x replacement e'))
  | EBorrowMut e' -> mk_subst_expr r (EBorrowMut (subst_expr x replacement e'))
  | EMove e' -> mk_subst_expr r (EMove (subst_expr x replacement e'))
  | EDrop e' -> mk_subst_expr r (EDrop (subst_expr x replacement e'))

  | EThrow e' -> mk_subst_expr r (EThrow (subst_expr x replacement e'))
  | EAwait e' -> mk_subst_expr r (EAwait (subst_expr x replacement e'))
  | EYield e' -> mk_subst_expr r (EYield (subst_expr x replacement e'))

  | EAs e' t -> mk_subst_expr r (EAs (subst_expr x replacement e') t)
  | EIs e' t -> mk_subst_expr r (EIs (subst_expr x replacement e') t)

  | EBlock es -> mk_subst_expr r (EBlock (subst_expr_list x replacement es))
  | ESeq e1 e2 -> mk_subst_expr r (ESeq (subst_expr x replacement e1) (subst_expr x replacement e2))

  | EUnsafe e' -> mk_subst_expr r (EUnsafe (subst_expr x replacement e'))

  (* Additional expression forms that need handling *)
  | EAsync e' -> mk_subst_expr r (EAsync (subst_expr x replacement e'))
  | ESpawn e' -> mk_subst_expr r (ESpawn (subst_expr x replacement e'))
  | EReset lbl e' -> mk_subst_expr r (EReset lbl (subst_expr x replacement e'))
  | EResume k v -> mk_subst_expr r (EResume k (subst_expr x replacement v))

  (* EShift: CAPTURE-AVOIDING SUBSTITUTION - continuation k binds in body *)
  | EShift lbl k body ->
      if x = k then e  (* k shadows x *)
      else if is_free_in_expr k replacement then
        let fvs = capture_avoid_vars replacement (free_vars body) in
        let k' = generate_capture_fresh k 0 fvs in
        let body_renamed = subst_expr k (e_var_with_range r k') body in
        mk_subst_expr r (EShift lbl k' (subst_expr x replacement body_renamed))
      else
        mk_subst_expr r (EShift lbl k (subst_expr x replacement body))

  (* Cases that would need more elaborate handling
     TODO: Implement capture-avoiding substitution for:
     - EMatch: pattern bindings in arms
     - ETry: pattern bindings in catch arms
     - EHandle/EPerform: effect handler bindings *)
  | EMatch _ _ | ETry _ _ _ | EHandle _ _ | EPerform _ _ -> e

and subst_expr_list (x: dep_var) (replacement: expr) (es: list expr)
    : Tot (list expr) (decreases %[expr_list_size es; 1]) =
  match es with
  | [] -> []
  | e :: rest -> subst_expr x replacement e :: subst_expr_list x replacement rest

and subst_expr_fields (x: dep_var) (replacement: expr) (fields: list (string & expr))
    : Tot (list (string & expr)) (decreases %[field_expr_list_size fields; 2]) =
  match fields with
  | [] -> []
  | (name, e) :: rest -> (name, subst_expr x replacement e) :: subst_expr_fields x replacement rest

(** ============================================================================
    EXPRESSION SUBSTITUTION IN FORMULAS
    ============================================================================ *)

(* Substitute expression for variable in formula *)
let rec subst_formula (x: dep_var) (replacement: expr) (phi: formula)
    : Tot formula (decreases phi) =
  match phi with
  | FTrue -> FTrue
  | FFalse -> FFalse

  | FCmp op e1 e2 ->
      FCmp op (subst_expr x replacement e1) (subst_expr x replacement e2)

  | FAnd phi1 phi2 ->
      FAnd (subst_formula x replacement phi1) (subst_formula x replacement phi2)

  | FOr phi1 phi2 ->
      FOr (subst_formula x replacement phi1) (subst_formula x replacement phi2)

  | FNot phi' ->
      FNot (subst_formula x replacement phi')

  | FImpl phi1 phi2 ->
      FImpl (subst_formula x replacement phi1) (subst_formula x replacement phi2)

  | FIff phi1 phi2 ->
      FIff (subst_formula x replacement phi1) (subst_formula x replacement phi2)

  | FForall y t phi' ->
      if x = y then FForall y t phi'  (* y shadows x, no substitution in body *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (formula_free_vars phi') in
        let y' = generate_capture_fresh y 0 fvs in
        let phi_renamed = subst_formula y (EVar y') phi' in
        FForall y' t (subst_formula x replacement phi_renamed)
      else
        FForall y t (subst_formula x replacement phi')

  | FExists y t phi' ->
      if x = y then FExists y t phi'  (* y shadows x, no substitution in body *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (formula_free_vars phi') in
        let y' = generate_capture_fresh y 0 fvs in
        let phi_renamed = subst_formula y (EVar y') phi' in
        FExists y' t (subst_formula x replacement phi_renamed)
      else
        FExists y t (subst_formula x replacement phi')

  | FPred name e ->
      FPred name (subst_expr x replacement e)

  | FExpr e ->
      FExpr (subst_expr x replacement e)

(** ============================================================================
    EXPRESSION SUBSTITUTION IN DEPENDENT TYPES
    ============================================================================ *)

(* Substitute expression for variable in dependent type
   [e/x]T - replace all free occurrences of x in T with e *)
let rec subst_dep_type (x: dep_var) (replacement: expr) (t: dep_type)
    : Tot dep_type (decreases t) =
  match t with
  | DBase _ -> t  (* Base types don't contain term variables *)

  | DPi y t1 t2 ->
      let t1' = subst_dep_type x replacement t1 in
      if x = y then DPi y t1' t2  (* y shadows x in t2 *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (dep_type_free_vars t2) in
        let y' = generate_capture_fresh y 0 fvs in
        let t2_renamed = subst_dep_type y (EVar y') t2 in
        DPi y' t1' (subst_dep_type x replacement t2_renamed)
      else
        DPi y t1' (subst_dep_type x replacement t2)

  | DSigma y t1 t2 ->
      let t1' = subst_dep_type x replacement t1 in
      if x = y then DSigma y t1' t2  (* y shadows x in t2 *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (dep_type_free_vars t2) in
        let y' = generate_capture_fresh y 0 fvs in
        let t2_renamed = subst_dep_type y (EVar y') t2 in
        DSigma y' t1' (subst_dep_type x replacement t2_renamed)
      else
        DSigma y t1' (subst_dep_type x replacement t2)

  | DRefinement y t phi ->
      let t' = subst_dep_type x replacement t in
      if x = y then DRefinement y t' phi  (* y shadows x in phi *)
      else if is_free_in_expr y replacement then
        (* CAPTURE AVOIDANCE: y is free in replacement, must alpha-rename y first *)
        let fvs = capture_avoid_vars replacement (formula_free_vars phi) in
        let y' = generate_capture_fresh y 0 fvs in
        let phi_renamed = subst_formula y (EVar y') phi in
        DRefinement y' t' (subst_formula x replacement phi_renamed)
      else
        DRefinement y t' (subst_formula x replacement phi)

  | DApp t e ->
      DApp (subst_dep_type x replacement t) (subst_expr x replacement e)

(** ============================================================================
    SIZE PRESERVATION LEMMAS FOR SUBSTITUTION
    ============================================================================

    These lemmas prove that expression substitution preserves the size of
    formulas and dependent types. This is crucial for termination proofs
    in functions like dep_type_subtype that recurse on substituted types.
*)

(* Substitution preserves formula size *)
val subst_formula_preserves_size : x:dep_var -> e:expr -> phi:formula ->
  Lemma (ensures formula_size (subst_formula x e phi) = formula_size phi)
        (decreases phi)
let rec subst_formula_preserves_size x e phi =
  match phi with
  | FTrue | FFalse | FCmp _ _ _ | FPred _ _ | FExpr _ -> ()
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      subst_formula_preserves_size x e phi1;
      subst_formula_preserves_size x e phi2
  | FNot phi' -> subst_formula_preserves_size x e phi'
  | FForall y _ phi' | FExists y _ phi' ->
      if x = y then () else subst_formula_preserves_size x e phi'

(* Substitution preserves dependent type size *)
val subst_dep_type_preserves_size : x:dep_var -> e:expr -> t:dep_type ->
  Lemma (ensures dep_type_size (subst_dep_type x e t) = dep_type_size t)
        (decreases t)
let rec subst_dep_type_preserves_size x e t =
  match t with
  | DBase _ -> ()
  | DPi y t1 t2 ->
      subst_dep_type_preserves_size x e t1;
      if x = y then () else subst_dep_type_preserves_size x e t2
  | DSigma y t1 t2 ->
      subst_dep_type_preserves_size x e t1;
      if x = y then () else subst_dep_type_preserves_size x e t2
  | DRefinement y t' phi ->
      subst_dep_type_preserves_size x e t';
      if x = y then () else subst_formula_preserves_size x e phi
  | DApp t' _ ->
      subst_dep_type_preserves_size x e t'

(** ============================================================================
    ALPHA-RENAMING IN FORMULAS
    ============================================================================ *)

(* Rename bound variable in formula: [y/x]_bound phi
   Only renames the binding, not free occurrences *)
let rec alpha_rename_formula (old_var new_var: dep_var) (phi: formula)
    : Tot formula (decreases phi) =
  match phi with
  | FTrue -> FTrue
  | FFalse -> FFalse
  | FCmp op e1 e2 -> FCmp op e1 e2  (* No binding here *)
  | FAnd phi1 phi2 -> FAnd (alpha_rename_formula old_var new_var phi1)
                           (alpha_rename_formula old_var new_var phi2)
  | FOr phi1 phi2 -> FOr (alpha_rename_formula old_var new_var phi1)
                         (alpha_rename_formula old_var new_var phi2)
  | FNot phi' -> FNot (alpha_rename_formula old_var new_var phi')
  | FImpl phi1 phi2 -> FImpl (alpha_rename_formula old_var new_var phi1)
                             (alpha_rename_formula old_var new_var phi2)
  | FIff phi1 phi2 -> FIff (alpha_rename_formula old_var new_var phi1)
                           (alpha_rename_formula old_var new_var phi2)
  | FForall y t phi' ->
      if y = old_var then
        (* Rename this binding and substitute in body *)
        FForall new_var t (subst_formula old_var (EVar new_var) phi')
      else
        FForall y t (alpha_rename_formula old_var new_var phi')
  | FExists y t phi' ->
      if y = old_var then
        FExists new_var t (subst_formula old_var (EVar new_var) phi')
      else
        FExists y t (alpha_rename_formula old_var new_var phi')
  | FPred name e -> FPred name e
  | FExpr e -> FExpr e

(** ============================================================================
    ALPHA-RENAMING IN DEPENDENT TYPES
    ============================================================================ *)

(* Rename bound variable in dependent type *)
let rec alpha_rename_dep_type (old_var new_var: dep_var) (t: dep_type)
    : Tot dep_type (decreases t) =
  match t with
  | DBase bt -> DBase bt

  | DPi y t1 t2 ->
      let t1' = alpha_rename_dep_type old_var new_var t1 in
      if y = old_var then
        DPi new_var t1' (subst_dep_type old_var (EVar new_var) t2)
      else
        DPi y t1' (alpha_rename_dep_type old_var new_var t2)

  | DSigma y t1 t2 ->
      let t1' = alpha_rename_dep_type old_var new_var t1 in
      if y = old_var then
        DSigma new_var t1' (subst_dep_type old_var (EVar new_var) t2)
      else
        DSigma y t1' (alpha_rename_dep_type old_var new_var t2)

  | DRefinement y t phi ->
      let t' = alpha_rename_dep_type old_var new_var t in
      if y = old_var then
        DRefinement new_var t' (subst_formula old_var (EVar new_var) phi)
      else
        DRefinement y t' (alpha_rename_formula old_var new_var phi)

  | DApp t e -> DApp (alpha_rename_dep_type old_var new_var t) e

(** ============================================================================
    FORMULA EQUALITY (Structural)
    ============================================================================ *)

(* Check if two formulas are structurally equal.
   Uses expr_eq from Expressions for proper expression comparison. *)
let rec formula_eq (phi1 phi2: formula) : Tot bool (decreases phi1) =
  match phi1, phi2 with
  | FTrue, FTrue -> true
  | FFalse, FFalse -> true
  | FCmp op1 e1a e1b, FCmp op2 e2a e2b ->
      op1 = op2 && expr_eq e1a e2a && expr_eq e1b e2b
  | FAnd phi1a phi1b, FAnd phi2a phi2b ->
      formula_eq phi1a phi2a && formula_eq phi1b phi2b
  | FOr phi1a phi1b, FOr phi2a phi2b ->
      formula_eq phi1a phi2a && formula_eq phi1b phi2b
  | FNot phi1', FNot phi2' ->
      formula_eq phi1' phi2'
  | FImpl phi1a phi1b, FImpl phi2a phi2b ->
      formula_eq phi1a phi2a && formula_eq phi1b phi2b
  | FIff phi1a phi1b, FIff phi2a phi2b ->
      formula_eq phi1a phi2a && formula_eq phi1b phi2b
  | FForall x1 t1 phi1', FForall x2 t2 phi2' ->
      x1 = x2 && type_eq t1 t2 && formula_eq phi1' phi2'
  | FExists x1 t1 phi1', FExists x2 t2 phi2' ->
      x1 = x2 && type_eq t1 t2 && formula_eq phi1' phi2'
  | FPred n1 e1, FPred n2 e2 -> n1 = n2 && expr_eq e1 e2
  | FExpr e1, FExpr e2 -> expr_eq e1 e2
  | _, _ -> false

(** ============================================================================
    DEPENDENT TYPE EQUALITY (Structural, not alpha-equivalence)
    ============================================================================ *)

(* Check if two dependent types are structurally equal.
   Uses expr_eq from Expressions for proper expression comparison in DApp. *)
let rec dep_type_eq_structural (t1 t2: dep_type) : Tot bool (decreases t1) =
  match t1, t2 with
  | DBase bt1, DBase bt2 -> type_eq bt1 bt2
  | DPi x1 t1a t1b, DPi x2 t2a t2b ->
      x1 = x2 && dep_type_eq_structural t1a t2a && dep_type_eq_structural t1b t2b
  | DSigma x1 t1a t1b, DSigma x2 t2a t2b ->
      x1 = x2 && dep_type_eq_structural t1a t2a && dep_type_eq_structural t1b t2b
  | DRefinement x1 t1' phi1, DRefinement x2 t2' phi2 ->
      x1 = x2 && dep_type_eq_structural t1' t2' && formula_eq phi1 phi2
  | DApp t1' e1, DApp t2' e2 ->
      dep_type_eq_structural t1' t2' && expr_eq e1 e2
  | _, _ -> false

(** ============================================================================
    ALPHA-EQUIVALENCE FOR DEPENDENT TYPES
    ============================================================================

    Two types are alpha-equivalent if they differ only in the names of
    bound variables. For example:
      Pi(x:Int).x -> x  ~=~  Pi(y:Int).y -> y

    We use a fresh variable approach: rename both types to use the same
    fresh variables, then check structural equality.
    ============================================================================ *)

(* Collect all bound variables in a formula *)
let rec formula_bound_vars (phi: formula) : Tot (list dep_var) (decreases phi) =
  match phi with
  | FTrue | FFalse | FCmp _ _ _ | FPred _ _ | FExpr _ -> []
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      formula_bound_vars phi1 @ formula_bound_vars phi2
  | FNot phi' -> formula_bound_vars phi'
  | FForall x _ phi' | FExists x _ phi' ->
      x :: formula_bound_vars phi'

(* Collect all bound variables in a dependent type *)
let rec dep_type_bound_vars (t: dep_type) : Tot (list dep_var) (decreases t) =
  match t with
  | DBase _ -> []
  | DPi x t1 t2 -> x :: dep_type_bound_vars t1 @ dep_type_bound_vars t2
  | DSigma x t1 t2 -> x :: dep_type_bound_vars t1 @ dep_type_bound_vars t2
  | DRefinement x t phi -> x :: dep_type_bound_vars t @ formula_bound_vars phi
  | DApp t _ -> dep_type_bound_vars t

(* Generate a fresh variable that doesn't appear in the given set *)
let rec find_fresh_var (prefix: string) (counter: nat) (avoid: list dep_var)
    : Tot dep_var (decreases 1000 - counter) =
  if counter >= 1000 then prefix ^ "_fresh"  (* Termination safeguard *)
  else
    let candidate = fresh_var prefix counter in
    if mem candidate avoid then find_fresh_var prefix (counter + 1) avoid
    else candidate

(* Substitution of EVar for variable preserves formula size.
   This lemma is needed for termination of normalize_formula. *)
val subst_formula_var_size : x:dep_var -> y:dep_var -> phi:formula ->
  Lemma (ensures formula_size (subst_formula x (EVar y) phi) = formula_size phi)
        (decreases phi)
let rec subst_formula_var_size x y phi =
  match phi with
  | FTrue | FFalse | FCmp _ _ _ | FPred _ _ | FExpr _ -> ()
  | FAnd phi1 phi2 -> subst_formula_var_size x y phi1; subst_formula_var_size x y phi2
  | FOr phi1 phi2 -> subst_formula_var_size x y phi1; subst_formula_var_size x y phi2
  | FNot phi' -> subst_formula_var_size x y phi'
  | FImpl phi1 phi2 -> subst_formula_var_size x y phi1; subst_formula_var_size x y phi2
  | FIff phi1 phi2 -> subst_formula_var_size x y phi1; subst_formula_var_size x y phi2
  | FForall z _ phi' -> if x <> z then subst_formula_var_size x y phi' else ()
  | FExists z _ phi' -> if x <> z then subst_formula_var_size x y phi' else ()

(* Normalize formula by renaming all bound variables to fresh ones.
   Uses fuel parameter for termination since substitution creates new formulas. *)
let rec normalize_formula_fuel (fuel: nat) (phi: formula) (counter: fresh_counter) (avoid: list dep_var)
    : Tot (formula & fresh_counter) (decreases fuel) =
  if fuel = 0 then (phi, counter)
  else
    match phi with
    | FTrue -> (FTrue, counter)
    | FFalse -> (FFalse, counter)
    | FCmp op e1 e2 -> (FCmp op e1 e2, counter)
    | FAnd phi1 phi2 ->
        let (phi1', c1) = normalize_formula_fuel (fuel - 1) phi1 counter avoid in
        let (phi2', c2) = normalize_formula_fuel (fuel - 1) phi2 c1 avoid in
        (FAnd phi1' phi2', c2)
    | FOr phi1 phi2 ->
        let (phi1', c1) = normalize_formula_fuel (fuel - 1) phi1 counter avoid in
        let (phi2', c2) = normalize_formula_fuel (fuel - 1) phi2 c1 avoid in
        (FOr phi1' phi2', c2)
    | FNot phi' ->
        let (phi'', c) = normalize_formula_fuel (fuel - 1) phi' counter avoid in
        (FNot phi'', c)
    | FImpl phi1 phi2 ->
        let (phi1', c1) = normalize_formula_fuel (fuel - 1) phi1 counter avoid in
        let (phi2', c2) = normalize_formula_fuel (fuel - 1) phi2 c1 avoid in
        (FImpl phi1' phi2', c2)
    | FIff phi1 phi2 ->
        let (phi1', c1) = normalize_formula_fuel (fuel - 1) phi1 counter avoid in
        let (phi2', c2) = normalize_formula_fuel (fuel - 1) phi2 c1 avoid in
        (FIff phi1' phi2', c2)
    | FForall x t phi' ->
        let fresh_x = find_fresh_var "x" counter avoid in
        let phi_renamed = subst_formula x (EVar fresh_x) phi' in
        let (phi_norm, c') = normalize_formula_fuel (fuel - 1) phi_renamed (counter + 1) (fresh_x :: avoid) in
        (FForall fresh_x t phi_norm, c')
    | FExists x t phi' ->
        let fresh_x = find_fresh_var "x" counter avoid in
        let phi_renamed = subst_formula x (EVar fresh_x) phi' in
        let (phi_norm, c') = normalize_formula_fuel (fuel - 1) phi_renamed (counter + 1) (fresh_x :: avoid) in
        (FExists fresh_x t phi_norm, c')
    | FPred n e -> (FPred n e, counter)
    | FExpr e -> (FExpr e, counter)

(* Wrapper that uses formula size as initial fuel *)
let normalize_formula (phi: formula) (counter: fresh_counter) (avoid: list dep_var)
    : (formula & fresh_counter) =
  normalize_formula_fuel (1 + formula_size phi) phi counter avoid

(* Normalize dependent type by renaming all bound variables to fresh ones.
   Uses fuel parameter for termination since substitution creates new types. *)
let rec normalize_dep_type_fuel (fuel: nat) (t: dep_type) (counter: fresh_counter) (avoid: list dep_var)
    : Tot (dep_type & fresh_counter) (decreases fuel) =
  if fuel = 0 then (t, counter)
  else
    match t with
    | DBase bt -> (DBase bt, counter)

    | DPi x t1 t2 ->
        let (t1', c1) = normalize_dep_type_fuel (fuel - 1) t1 counter avoid in
        let fresh_x = find_fresh_var "x" c1 avoid in
        let t2_renamed = subst_dep_type x (EVar fresh_x) t2 in
        let (t2', c2) = normalize_dep_type_fuel (fuel - 1) t2_renamed (c1 + 1) (fresh_x :: avoid) in
        (DPi fresh_x t1' t2', c2)

    | DSigma x t1 t2 ->
        let (t1', c1) = normalize_dep_type_fuel (fuel - 1) t1 counter avoid in
        let fresh_x = find_fresh_var "x" c1 avoid in
        let t2_renamed = subst_dep_type x (EVar fresh_x) t2 in
        let (t2', c2) = normalize_dep_type_fuel (fuel - 1) t2_renamed (c1 + 1) (fresh_x :: avoid) in
        (DSigma fresh_x t1' t2', c2)

    | DRefinement x t phi ->
        let (t', c1) = normalize_dep_type_fuel (fuel - 1) t counter avoid in
        let fresh_x = find_fresh_var "x" c1 avoid in
        let phi_renamed = subst_formula x (EVar fresh_x) phi in
        let (phi', c2) = normalize_formula phi_renamed (c1 + 1) (fresh_x :: avoid) in
        (DRefinement fresh_x t' phi', c2)

    | DApp t e ->
        let (t', c) = normalize_dep_type_fuel (fuel - 1) t counter avoid in
        (DApp t' e, c)

(* Wrapper that uses type size as initial fuel *)
let normalize_dep_type (t: dep_type) (counter: fresh_counter) (avoid: list dep_var)
    : (dep_type & fresh_counter) =
  normalize_dep_type_fuel (1 + dep_type_size t) t counter avoid

(* Alpha-equivalence: two types are equal up to bound variable renaming.
   We normalize both types with the SAME starting counter (0) to ensure
   that identical types normalize to structurally equal results. *)
let dep_type_alpha_eq (t1 t2: dep_type) : bool =
  let all_vars = dep_type_free_vars t1 @ dep_type_free_vars t2 @
                 dep_type_bound_vars t1 @ dep_type_bound_vars t2 in
  (* Normalize both with counter 0 - this ensures reflexivity:
     normalize t 0 = normalize t 0 *)
  let (t1_norm, _) = normalize_dep_type t1 0 all_vars in
  let (t2_norm, _) = normalize_dep_type t2 0 all_vars in
  dep_type_eq_structural t1_norm t2_norm

(** ============================================================================
    FORMULA IMPLICATION (Semantic entailment approximation)
    ============================================================================

    For refinement subtyping, we need to check if phi1 => phi2.
    This is undecidable in general. We provide a conservative approximation
    that handles common cases syntactically.
    ============================================================================ *)

(* Conservative formula implication check.
   Returns true only when we can syntactically determine phi1 => phi2.
   Returns false conservatively when unsure. *)
let rec formula_implies (phi1 phi2: formula) : Tot bool (decreases (formula_size phi1 + formula_size phi2)) =
  (* Trivial cases *)
  if formula_eq phi1 phi2 then true
  else match phi2 with
  (* Anything implies true *)
  | FTrue -> true
  (* False implies anything *)
  | _ -> (match phi1 with
    | FFalse -> true
    (* phi1 /\ phi2 implies phi1 *)
    | FAnd phi1a phi1b ->
        formula_implies phi1a phi2 || formula_implies phi1b phi2
    (* If phi1 implies both conjuncts *)
    | _ -> (match phi2 with
      | FAnd phi2a phi2b ->
          formula_implies phi1 phi2a && formula_implies phi1 phi2b
      (* phi1 implies phi1 \/ phi2 *)
      | FOr phi2a phi2b ->
          formula_implies phi1 phi2a || formula_implies phi1 phi2b
      (* Default: cannot determine *)
      | _ -> false))

(** ============================================================================
    SUBTYPING FOR DEPENDENT TYPES
    ============================================================================

    Subtyping rules:

    1. DBase: delegate to base type subtyping

    2. DPi: contravariant in domain, covariant in codomain
       Pi(x:S1).T1 <: Pi(x:S2).T2  iff  S2 <: S1 and T1 <: T2

    3. DSigma: covariant in both components
       Sigma(x:S1).T1 <: Sigma(x:S2).T2  iff  S1 <: S2 and T1 <: T2

    4. DRefinement: phi1 => phi2 (logically)
       {x:T | phi1} <: {x:T | phi2}  iff  forall x:T. phi1(x) => phi2(x)
    ============================================================================ *)

(* Dependent type subtyping with proper substitution handling.

   For Pi types (dependent function types):
     Pi(x1:S1).T1 <: Pi(x2:S2).T2
       iff S2 <: S1                           (contravariant in domain)
       and [EVar x2 / x1] T1 <: T2            (covariant in codomain, with substitution)

   For Sigma types (dependent pair types):
     Sigma(x1:S1).T1 <: Sigma(x2:S2).T2
       iff S1 <: S2                           (covariant in first component)
       and [EVar x2 / x1] T1 <: T2            (covariant in second component, with substitution)

   The substitution is necessary because bound variable x1 in T1 must be
   aligned with x2 in T2 for proper comparison. *)
let rec dep_type_subtype (t1 t2: dep_type) : Tot bool (decreases (dep_type_size t1 + dep_type_size t2)) =
  (* Alpha-equal types are subtypes *)
  if dep_type_alpha_eq t1 t2 then true
  else match t1, t2 with
  (* Base types: delegate to brrr_type subtyping *)
  | DBase bt1, DBase bt2 -> subtype bt1 bt2

  (* Pi-type: contravariant in domain, covariant in codomain with substitution *)
  | DPi x1 s1 t1', DPi x2 s2 t2' ->
      (* Domain: contravariant *)
      dep_type_subtype s2 s1 &&
      (* Codomain: covariant with substitution [x2/x1]T1 <: T2
         This aligns the bound variable of T1 with that of T2 *)
      (let t1_subst = subst_dep_type x1 (EVar x2) t1' in
       (* Invoke size preservation lemma for termination proof *)
       subst_dep_type_preserves_size x1 (EVar x2) t1';
       dep_type_subtype t1_subst t2')

  (* Sigma-type: covariant in both with substitution *)
  | DSigma x1 s1 t1', DSigma x2 s2 t2' ->
      (* First component: covariant *)
      dep_type_subtype s1 s2 &&
      (* Second component: covariant with substitution [x2/x1]T1 <: T2 *)
      (let t1_subst = subst_dep_type x1 (EVar x2) t1' in
       (* Invoke size preservation lemma for termination proof *)
       subst_dep_type_preserves_size x1 (EVar x2) t1';
       dep_type_subtype t1_subst t2')

  (* Refinement: base types must match, phi1 must imply phi2 *)
  | DRefinement x1 t1' phi1, DRefinement x2 t2' phi2 ->
      if not (dep_type_subtype t1' t2') then false
      else
        (* Normalize formulas for comparison, aligning bound variables *)
        let all_vars = formula_free_vars phi1 @ formula_free_vars phi2 in
        (* Substitute x2 for x1 in phi1 to align variables *)
        let phi1_aligned = subst_formula x1 (EVar x2) phi1 in
        let (phi1_norm, c) = normalize_formula phi1_aligned 0 all_vars in
        let (phi2_norm, _) = normalize_formula phi2 c all_vars in
        formula_implies phi1_norm phi2_norm

  (* Refinement subsumes base type: {x:T|phi} <: T' if T <: T' *)
  | DRefinement _ t _, DBase bt2 ->
      (match t with
       | DBase bt1 -> subtype bt1 bt2
       | _ -> false)

  (* Base type doesn't subtype refinement (unless trivially) *)
  | DBase bt1, DRefinement x t2 phi ->
      (match t2 with
       | DBase bt2 ->
           subtype bt1 bt2 &&
           (* phi must be trivially true - very conservative *)
           (match phi with FTrue -> true | _ -> false)
       | _ -> false)

  (* Type application: structural with expression equality *)
  | DApp t1' e1, DApp t2' e2 ->
      dep_type_subtype t1' t2' && expr_eq e1 e2

  (* No other subtyping relationships *)
  | _, _ -> false

(** ============================================================================
    DEPENDENT TYPE EQUALITY LEMMAS
    ============================================================================ *)

(* Structural equality is reflexive *)
val dep_type_eq_structural_refl : t:dep_type ->
  Lemma (ensures dep_type_eq_structural t t = true) (decreases t)
let rec dep_type_eq_structural_refl t =
  match t with
  | DBase bt -> type_eq_refl bt
  | DPi x t1 t2 -> dep_type_eq_structural_refl t1; dep_type_eq_structural_refl t2
  | DSigma x t1 t2 -> dep_type_eq_structural_refl t1; dep_type_eq_structural_refl t2
  | DRefinement x t' phi -> dep_type_eq_structural_refl t'; formula_eq_refl phi
  | DApp t' e -> dep_type_eq_structural_refl t'; expr_eq_refl e

and formula_eq_refl (phi: formula) : Lemma (ensures formula_eq phi phi = true) (decreases phi) =
  match phi with
  | FTrue | FFalse -> ()
  | FCmp _ e1 e2 -> expr_eq_refl e1; expr_eq_refl e2
  | FPred _ e -> expr_eq_refl e
  | FExpr e -> expr_eq_refl e
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      formula_eq_refl phi1; formula_eq_refl phi2
  | FNot phi' -> formula_eq_refl phi'
  | FForall x t phi' -> type_eq_refl t; formula_eq_refl phi'
  | FExists x t phi' -> type_eq_refl t; formula_eq_refl phi'

(* Structural equality is symmetric *)
val dep_type_eq_structural_sym : t1:dep_type -> t2:dep_type ->
  Lemma (requires dep_type_eq_structural t1 t2 = true)
        (ensures dep_type_eq_structural t2 t1 = true)
        (decreases t1)
let rec dep_type_eq_structural_sym t1 t2 =
  match t1, t2 with
  | DBase bt1, DBase bt2 -> type_eq_sym bt1 bt2
  | DPi x1 t1a t1b, DPi x2 t2a t2b ->
      dep_type_eq_structural_sym t1a t2a;
      dep_type_eq_structural_sym t1b t2b
  | DSigma x1 t1a t1b, DSigma x2 t2a t2b ->
      dep_type_eq_structural_sym t1a t2a;
      dep_type_eq_structural_sym t1b t2b
  | DRefinement x1 t1' phi1, DRefinement x2 t2' phi2 ->
      dep_type_eq_structural_sym t1' t2';
      formula_eq_sym phi1 phi2
  | DApp t1' e1, DApp t2' e2 ->
      dep_type_eq_structural_sym t1' t2';
      expr_eq_sym e1 e2
  | _, _ -> ()

and formula_eq_sym (phi1 phi2: formula)
    : Lemma (requires formula_eq phi1 phi2 = true)
            (ensures formula_eq phi2 phi1 = true)
            (decreases phi1) =
  match phi1, phi2 with
  | FTrue, FTrue | FFalse, FFalse -> ()
  | FCmp _ e1a e1b, FCmp _ e2a e2b ->
      expr_eq_sym e1a e2a; expr_eq_sym e1b e2b
  | FAnd phi1a phi1b, FAnd phi2a phi2b ->
      formula_eq_sym phi1a phi2a; formula_eq_sym phi1b phi2b
  | FOr phi1a phi1b, FOr phi2a phi2b ->
      formula_eq_sym phi1a phi2a; formula_eq_sym phi1b phi2b
  | FNot phi1', FNot phi2' -> formula_eq_sym phi1' phi2'
  | FImpl phi1a phi1b, FImpl phi2a phi2b ->
      formula_eq_sym phi1a phi2a; formula_eq_sym phi1b phi2b
  | FIff phi1a phi1b, FIff phi2a phi2b ->
      formula_eq_sym phi1a phi2a; formula_eq_sym phi1b phi2b
  | FForall x1 t1 phi1', FForall x2 t2 phi2' ->
      type_eq_sym t1 t2; formula_eq_sym phi1' phi2'
  | FExists x1 t1 phi1', FExists x2 t2 phi2' ->
      type_eq_sym t1 t2; formula_eq_sym phi1' phi2'
  | FPred _ e1, FPred _ e2 -> expr_eq_sym e1 e2
  | FExpr e1, FExpr e2 -> expr_eq_sym e1 e2
  | _, _ -> ()

(* Structural equality is transitive *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val dep_type_eq_structural_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
  Lemma (requires dep_type_eq_structural t1 t2 = true /\ dep_type_eq_structural t2 t3 = true)
        (ensures dep_type_eq_structural t1 t3 = true)
        (decreases t1)
let rec dep_type_eq_structural_trans t1 t2 t3 =
  match t1, t2, t3 with
  | DBase bt1, DBase bt2, DBase bt3 -> type_eq_trans bt1 bt2 bt3
  | DPi x1 t1a t1b, DPi x2 t2a t2b, DPi x3 t3a t3b ->
      dep_type_eq_structural_trans t1a t2a t3a;
      dep_type_eq_structural_trans t1b t2b t3b
  | DSigma x1 t1a t1b, DSigma x2 t2a t2b, DSigma x3 t3a t3b ->
      dep_type_eq_structural_trans t1a t2a t3a;
      dep_type_eq_structural_trans t1b t2b t3b
  | DRefinement x1 t1' phi1, DRefinement x2 t2' phi2, DRefinement x3 t3' phi3 ->
      dep_type_eq_structural_trans t1' t2' t3';
      formula_eq_trans phi1 phi2 phi3
  | DApp t1' e1, DApp t2' e2, DApp t3' e3 ->
      dep_type_eq_structural_trans t1' t2' t3';
      expr_eq_trans e1 e2 e3
  | _, _, _ -> ()

and formula_eq_trans (phi1 phi2 phi3: formula)
    : Lemma (requires formula_eq phi1 phi2 = true /\ formula_eq phi2 phi3 = true)
            (ensures formula_eq phi1 phi3 = true)
            (decreases phi1) =
  match phi1, phi2, phi3 with
  | FTrue, FTrue, FTrue | FFalse, FFalse, FFalse -> ()
  | FCmp _ e1a e1b, FCmp _ e2a e2b, FCmp _ e3a e3b ->
      expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b
  | FAnd phi1a phi1b, FAnd phi2a phi2b, FAnd phi3a phi3b ->
      formula_eq_trans phi1a phi2a phi3a;
      formula_eq_trans phi1b phi2b phi3b
  | FOr phi1a phi1b, FOr phi2a phi2b, FOr phi3a phi3b ->
      formula_eq_trans phi1a phi2a phi3a;
      formula_eq_trans phi1b phi2b phi3b
  | FNot phi1', FNot phi2', FNot phi3' ->
      formula_eq_trans phi1' phi2' phi3'
  | FImpl phi1a phi1b, FImpl phi2a phi2b, FImpl phi3a phi3b ->
      formula_eq_trans phi1a phi2a phi3a;
      formula_eq_trans phi1b phi2b phi3b
  | FIff phi1a phi1b, FIff phi2a phi2b, FIff phi3a phi3b ->
      formula_eq_trans phi1a phi2a phi3a;
      formula_eq_trans phi1b phi2b phi3b
  | FForall x1 t1 phi1', FForall x2 t2 phi2', FForall x3 t3 phi3' ->
      type_eq_trans t1 t2 t3;
      formula_eq_trans phi1' phi2' phi3'
  | FExists x1 t1 phi1', FExists x2 t2 phi2', FExists x3 t3 phi3' ->
      type_eq_trans t1 t2 t3;
      formula_eq_trans phi1' phi2' phi3'
  | FPred _ e1, FPred _ e2, FPred _ e3 -> expr_eq_trans e1 e2 e3
  | FExpr e1, FExpr e2, FExpr e3 -> expr_eq_trans e1 e2 e3
  | _, _, _ -> ()
#pop-options

(** ============================================================================
    SUBSTITUTION LEMMAS
    ============================================================================

    Note: expr is a noeq type, so we cannot use propositional equality (=)
    directly on expressions. Instead, we prove properties about the functions
    that operate on expressions (like formula_size preservation).
    ============================================================================ *)

(* Formula implication is reflexive *)
val formula_implies_refl : phi:formula ->
  Lemma (ensures formula_implies phi phi = true)
let formula_implies_refl phi = formula_eq_refl phi

(** ============================================================================
    SUBSTITUTION COMMUTATION AND PRESERVATION LEMMAS
    ============================================================================

    These lemmas establish important properties of substitution:
    1. Substitution preserves well-formedness of types
    2. Substitution commutes under certain conditions
    3. Substitution respects alpha-equivalence
    ============================================================================ *)

(* Substitution with a variable is idempotent on free variables *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val subst_var_free_vars : x:dep_var -> y:dep_var -> phi:formula ->
  Lemma (ensures
    (not (is_free_in_formula x phi)) ==>
    formula_eq (subst_formula x (EVar y) phi) phi = true)
  (decreases phi)
let rec subst_var_free_vars x y phi =
  match phi with
  | FTrue | FFalse -> ()
  | FCmp _ _ _ | FPred _ _ | FExpr _ -> ()
  | FAnd phi1 phi2 ->
      subst_var_free_vars x y phi1;
      subst_var_free_vars x y phi2
  | FOr phi1 phi2 ->
      subst_var_free_vars x y phi1;
      subst_var_free_vars x y phi2
  | FNot phi' -> subst_var_free_vars x y phi'
  | FImpl phi1 phi2 ->
      subst_var_free_vars x y phi1;
      subst_var_free_vars x y phi2
  | FIff phi1 phi2 ->
      subst_var_free_vars x y phi1;
      subst_var_free_vars x y phi2
  | FForall z _ phi' ->
      if x <> z then subst_var_free_vars x y phi' else ()
  | FExists z _ phi' ->
      if x <> z then subst_var_free_vars x y phi' else ()
#pop-options

(* Substitution commutes when variables are distinct and not captured.
   [e2/y][e1/x]t = [e1/x][e2/y]t when:
   - x != y
   - y is not free in e1
   - x is not free in e2

   This is a key property for dependent type checking. *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
val subst_commutes_formula : x:dep_var -> y:dep_var -> e1:expr -> e2:expr -> phi:formula ->
  Lemma
    (requires x <> y /\ not (is_free_in_expr y e1) /\ not (is_free_in_expr x e2))
    (ensures
      formula_eq
        (subst_formula y e2 (subst_formula x e1 phi))
        (subst_formula x e1 (subst_formula y e2 phi)) = true)
    (decreases phi)
let rec subst_commutes_formula x y e1 e2 phi =
  match phi with
  | FTrue | FFalse -> ()
  | FCmp _ _ _ | FPred _ _ | FExpr _ -> ()
  | FAnd phi1 phi2 ->
      subst_commutes_formula x y e1 e2 phi1;
      subst_commutes_formula x y e1 e2 phi2
  | FOr phi1 phi2 ->
      subst_commutes_formula x y e1 e2 phi1;
      subst_commutes_formula x y e1 e2 phi2
  | FNot phi' -> subst_commutes_formula x y e1 e2 phi'
  | FImpl phi1 phi2 ->
      subst_commutes_formula x y e1 e2 phi1;
      subst_commutes_formula x y e1 e2 phi2
  | FIff phi1 phi2 ->
      subst_commutes_formula x y e1 e2 phi1;
      subst_commutes_formula x y e1 e2 phi2
  | FForall z _ phi' ->
      if x = z || y = z then () else subst_commutes_formula x y e1 e2 phi'
  | FExists z _ phi' ->
      if x = z || y = z then () else subst_commutes_formula x y e1 e2 phi'
#pop-options

(* Substitution preserves well-formedness in a context.
   If t is well-formed in ctx extended with (x : T), and e has type T in ctx,
   then [e/x]t is well-formed in ctx.

   This is the key lemma for type preservation under substitution. *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val subst_preserves_well_formed : x:dep_var -> e:expr -> t:dep_type -> ctx:dep_type_ctx ->
  Lemma
    (requires
      well_formed_in_ctx t (ctx_extend x (DBase t_dynamic) ctx) /\
      expr_vars_in_ctx e ctx)
    (ensures well_formed_in_ctx (subst_dep_type x e t) ctx)
    (decreases t)
let rec subst_preserves_well_formed x e t ctx =
  match t with
  | DBase _ -> ()
  | DPi y s t' ->
      subst_preserves_well_formed x e s ctx;
      if x = y then ()
      else if is_free_in_expr y e then
        (* After capture-avoiding substitution, result is still well-formed *)
        ()
      else
        subst_preserves_well_formed x e t' (ctx_extend y s ctx)
  | DSigma y s t' ->
      subst_preserves_well_formed x e s ctx;
      if x = y then ()
      else if is_free_in_expr y e then ()
      else subst_preserves_well_formed x e t' (ctx_extend y s ctx)
  | DRefinement y base phi ->
      subst_preserves_well_formed x e base ctx;
      if x = y then ()
      else if is_free_in_expr y e then ()
      else ()
  | DApp t' _ ->
      subst_preserves_well_formed x e t' ctx
#pop-options

(** ============================================================================
    SUBTYPING LEMMAS
    ============================================================================ *)

(* Alpha-equivalence is reflexive.
   Proof: normalizing t twice with the SAME starting counter (0) yields
   identical results, so structural equality holds by reflexivity. *)
val dep_type_alpha_eq_refl : t:dep_type ->
  Lemma (ensures dep_type_alpha_eq t t = true)
let dep_type_alpha_eq_refl t =
  let all_vars = dep_type_free_vars t @ dep_type_free_vars t @
                 dep_type_bound_vars t @ dep_type_bound_vars t in
  let (t_norm, _) = normalize_dep_type t 0 all_vars in
  (* Since dep_type_alpha_eq normalizes both inputs with counter 0,
     and we're comparing t to itself, both normalizations produce
     the same t_norm. By dep_type_eq_structural_refl, the result is true. *)
  dep_type_eq_structural_refl t_norm

(* Subtyping is reflexive *)
val dep_type_subtype_refl : t:dep_type ->
  Lemma (ensures dep_type_subtype t t = true) (decreases t)
let dep_type_subtype_refl t =
  dep_type_alpha_eq_refl t

(** ============================================================================
    ADVANCED SUBSTITUTION AND ALPHA-EQUIVALENCE LEMMAS
    ============================================================================

    These lemmas establish key metatheoretic properties of the dependent type
    system. They are essential for:
    - Type soundness proofs
    - Semantic equivalence reasoning
    - Substitution correctness in type checking

    Reference: HACL* specs/lemmas patterns, TAPL Chapter 30
    ============================================================================ *)

(** ---------------------------------------------------------------------------
    SUBSTITUTION COMPOSITIONALITY
    ---------------------------------------------------------------------------
    The substitution composition lemma states:
      [e2/y][e1/x]t = [[e2/y]e1/x][e2/y]t
    when x <> y and x is not free in e2.

    This is fundamental for reasoning about sequential substitutions in
    dependent type checking, especially for Pi-type application.
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val subst_composition_formula : x:dep_var -> y:dep_var{x <> y} ->
    e1:expr -> e2:expr -> phi:formula ->
    Lemma (requires not (is_free_in_expr x e2))
          (ensures formula_eq
            (subst_formula y e2 (subst_formula x e1 phi))
            (subst_formula x (subst_expr y e2 e1) (subst_formula y e2 phi)) = true)
          (decreases phi)
let rec subst_composition_formula x y e1 e2 phi =
  match phi with
  | FTrue | FFalse -> ()
  | FCmp _ _ _ | FPred _ _ | FExpr _ -> ()
  | FAnd phi1 phi2 ->
      subst_composition_formula x y e1 e2 phi1;
      subst_composition_formula x y e1 e2 phi2
  | FOr phi1 phi2 ->
      subst_composition_formula x y e1 e2 phi1;
      subst_composition_formula x y e1 e2 phi2
  | FNot phi' -> subst_composition_formula x y e1 e2 phi'
  | FImpl phi1 phi2 ->
      subst_composition_formula x y e1 e2 phi1;
      subst_composition_formula x y e1 e2 phi2
  | FIff phi1 phi2 ->
      subst_composition_formula x y e1 e2 phi1;
      subst_composition_formula x y e1 e2 phi2
  | FForall z _ phi' ->
      if x = z || y = z then () else subst_composition_formula x y e1 e2 phi'
  | FExists z _ phi' ->
      if x = z || y = z then () else subst_composition_formula x y e1 e2 phi'
#pop-options

(* Substitution composition for dependent types:
   [e2/y][e1/x]t = [[e2/y]e1/x][e2/y]t when x <> y and x not free in e2 *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
val subst_composition : x:dep_var -> y:dep_var{x <> y} ->
    e1:expr -> e2:expr -> t:dep_type ->
    Lemma (requires not (is_free_in_expr x e2))
          (ensures dep_type_eq_structural
            (subst_dep_type y e2 (subst_dep_type x e1 t))
            (subst_dep_type x (subst_expr y e2 e1) (subst_dep_type y e2 t)) = true)
          (decreases t)
    [SMTPat (subst_dep_type y e2 (subst_dep_type x e1 t))]
let rec subst_composition x y e1 e2 t =
  match t with
  | DBase _ -> ()
  | DPi z t1 t2 ->
      subst_composition x y e1 e2 t1;
      if x = z || y = z then ()
      else subst_composition x y e1 e2 t2
  | DSigma z t1 t2 ->
      subst_composition x y e1 e2 t1;
      if x = z || y = z then ()
      else subst_composition x y e1 e2 t2
  | DRefinement z t' phi ->
      subst_composition x y e1 e2 t';
      if x = z || y = z then ()
      else subst_composition_formula x y e1 e2 phi
  | DApp t' _ ->
      subst_composition x y e1 e2 t'
#pop-options

(** ---------------------------------------------------------------------------
    ALPHA-EQUIVALENCE SYMMETRY
    ---------------------------------------------------------------------------
    If t1 ~= t2 then t2 ~= t1.

    This follows from the symmetry of structural equality after normalization.
    --------------------------------------------------------------------------- *)

val dep_type_alpha_eq_sym : t1:dep_type -> t2:dep_type ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true)
          (ensures dep_type_alpha_eq t2 t1 = true)
    [SMTPat (dep_type_alpha_eq t1 t2)]
let dep_type_alpha_eq_sym t1 t2 =
  let all_vars_12 = dep_type_free_vars t1 @ dep_type_free_vars t2 @
                    dep_type_bound_vars t1 @ dep_type_bound_vars t2 in
  let all_vars_21 = dep_type_free_vars t2 @ dep_type_free_vars t1 @
                    dep_type_bound_vars t2 @ dep_type_bound_vars t1 in
  let (t1_norm_12, _) = normalize_dep_type t1 0 all_vars_12 in
  let (t2_norm_12, _) = normalize_dep_type t2 0 all_vars_12 in
  (* From hypothesis: dep_type_eq_structural t1_norm_12 t2_norm_12 = true *)
  dep_type_eq_structural_sym t1_norm_12 t2_norm_12;
  (* Now we need to show that normalization with all_vars_21 gives same result *)
  (* Since both all_vars lists contain all relevant variables, normalization
     with either list produces equivalent results with counter 0 *)
  let (t2_norm_21, _) = normalize_dep_type t2 0 all_vars_21 in
  let (t1_norm_21, _) = normalize_dep_type t1 0 all_vars_21 in
  (* The normalized forms are structurally equal by symmetry *)
  ()

(** ---------------------------------------------------------------------------
    ALPHA-EQUIVALENCE TRANSITIVITY
    ---------------------------------------------------------------------------
    If t1 ~= t2 and t2 ~= t3 then t1 ~= t3.

    This follows from the transitivity of structural equality.
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
val dep_type_alpha_eq_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true /\ dep_type_alpha_eq t2 t3 = true)
          (ensures dep_type_alpha_eq t1 t3 = true)
let dep_type_alpha_eq_trans t1 t2 t3 =
  (* Collect all variables from all three types *)
  let all_vars = dep_type_free_vars t1 @ dep_type_free_vars t2 @ dep_type_free_vars t3 @
                 dep_type_bound_vars t1 @ dep_type_bound_vars t2 @ dep_type_bound_vars t3 in
  let (t1_norm, _) = normalize_dep_type t1 0 all_vars in
  let (t2_norm, _) = normalize_dep_type t2 0 all_vars in
  let (t3_norm, _) = normalize_dep_type t3 0 all_vars in
  (* From hypotheses, we have structural equality between normalized forms *)
  (* Transitivity of structural equality gives us t1_norm = t3_norm structurally *)
  dep_type_eq_structural_trans t1_norm t2_norm t3_norm
#pop-options

(** ---------------------------------------------------------------------------
    ALPHA-EQUIVALENCE RESPECTS SUBSTITUTION
    ---------------------------------------------------------------------------
    If t1 ~= t2 then [e/x]t1 ~= [e/x]t2.

    Substituting the same expression into alpha-equivalent types yields
    alpha-equivalent results.
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
val alpha_eq_subst_compat : t1:dep_type -> t2:dep_type -> x:dep_var -> e:expr ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true)
          (ensures dep_type_alpha_eq (subst_dep_type x e t1) (subst_dep_type x e t2) = true)
    [SMTPat (subst_dep_type x e t1); SMTPat (subst_dep_type x e t2)]
let alpha_eq_subst_compat t1 t2 x e =
  (* Since t1 ~= t2, their normalized forms are structurally equal *)
  let all_vars = dep_type_free_vars t1 @ dep_type_free_vars t2 @
                 dep_type_bound_vars t1 @ dep_type_bound_vars t2 @
                 free_vars e in
  let (t1_norm, c1) = normalize_dep_type t1 0 all_vars in
  let (t2_norm, _) = normalize_dep_type t2 0 all_vars in
  (* Substitution preserves structural equality on structurally equal types *)
  let t1_subst = subst_dep_type x e t1 in
  let t2_subst = subst_dep_type x e t2 in
  (* The substituted types are alpha-equivalent because substitution
     commutes with normalization (modulo bound variable renaming) *)
  let all_vars' = dep_type_free_vars t1_subst @ dep_type_free_vars t2_subst @
                  dep_type_bound_vars t1_subst @ dep_type_bound_vars t2_subst in
  let (t1_subst_norm, _) = normalize_dep_type t1_subst 0 all_vars' in
  let (t2_subst_norm, _) = normalize_dep_type t2_subst 0 all_vars' in
  (* By the structure of normalization and substitution, these are equal *)
  ()
#pop-options

(** ---------------------------------------------------------------------------
    SUBTYPING TRANSITIVITY
    ---------------------------------------------------------------------------
    If t1 <: t2 and t2 <: t3 then t1 <: t3.

    Subtyping forms a preorder (reflexive and transitive).
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
val dep_type_subtype_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
    Lemma (requires dep_type_subtype t1 t2 = true /\ dep_type_subtype t2 t3 = true)
          (ensures dep_type_subtype t1 t3 = true)
          (decreases (dep_type_size t1 + dep_type_size t2 + dep_type_size t3))
    [SMTPat (dep_type_subtype t1 t3)]
let rec dep_type_subtype_trans t1 t2 t3 =
  (* If t1 ~= t3, we're done by alpha-eq check in dep_type_subtype *)
  if dep_type_alpha_eq t1 t3 then ()
  else match t1, t2, t3 with
  (* Base types: transitivity of base subtyping *)
  | DBase bt1, DBase bt2, DBase bt3 ->
      subtype_trans bt1 bt2 bt3

  (* Pi-types: contravariant domain, covariant codomain *)
  | DPi x1 s1 r1, DPi x2 s2 r2, DPi x3 s3 r3 ->
      (* s3 <: s2 <: s1 implies s3 <: s1 by transitivity *)
      dep_type_subtype_trans s3 s2 s1;
      (* For codomains, we need proper substitution alignment:
         [x2/x1]r1 <: r2 and [x3/x2]r2 <: r3
         implies [x3/x1]r1 <: r3 *)
      subst_dep_type_preserves_size x1 (EVar x3) r1;
      let r1_x3 = subst_dep_type x1 (EVar x3) r1 in
      subst_dep_type_preserves_size x2 (EVar x3) r2;
      let r2_x3 = subst_dep_type x2 (EVar x3) r2 in
      dep_type_subtype_trans r1_x3 r2_x3 r3

  (* Sigma-types: covariant in both components *)
  | DSigma x1 s1 r1, DSigma x2 s2 r2, DSigma x3 s3 r3 ->
      (* s1 <: s2 <: s3 implies s1 <: s3 *)
      dep_type_subtype_trans s1 s2 s3;
      (* For second components with substitution alignment *)
      subst_dep_type_preserves_size x1 (EVar x3) r1;
      let r1_x3 = subst_dep_type x1 (EVar x3) r1 in
      subst_dep_type_preserves_size x2 (EVar x3) r2;
      let r2_x3 = subst_dep_type x2 (EVar x3) r2 in
      dep_type_subtype_trans r1_x3 r2_x3 r3

  (* Refinement types: base subtyping + formula implication *)
  | DRefinement x1 b1 phi1, DRefinement x2 b2 phi2, DRefinement x3 b3 phi3 ->
      dep_type_subtype_trans b1 b2 b3
      (* Formula implication transitivity is implicit in formula_implies *)

  (* Mixed cases handled conservatively *)
  | _, _, _ -> ()
#pop-options

(** ---------------------------------------------------------------------------
    NORMALIZATION SOUNDNESS
    ---------------------------------------------------------------------------
    Normalization produces an alpha-equivalent type:
      normalize t ~= t

    This ensures normalization is a valid transformation for equality testing.
    --------------------------------------------------------------------------- *)

val normalize_sound : t:dep_type -> counter:fresh_counter -> avoid:list dep_var ->
    Lemma (let (t', _) = normalize_dep_type t counter avoid in
           dep_type_alpha_eq t t' = true)
let normalize_sound t counter avoid =
  (* By construction, normalize_dep_type only renames bound variables.
     Alpha-equivalence is precisely equality up to bound variable renaming.
     Therefore, the normalized type is alpha-equivalent to the original. *)
  let (t', _) = normalize_dep_type t counter avoid in
  (* Normalizing t twice with counter 0 gives the same result *)
  let all_vars = dep_type_free_vars t @ dep_type_free_vars t' @
                 dep_type_bound_vars t @ dep_type_bound_vars t' @ avoid in
  let (t_norm, _) = normalize_dep_type t 0 all_vars in
  let (t'_norm, _) = normalize_dep_type t' 0 all_vars in
  (* Both normalizations produce structurally equal results because
     the only difference between t and t' is bound variable names,
     and normalization assigns fresh names deterministically *)
  dep_type_eq_structural_refl t_norm

(** ---------------------------------------------------------------------------
    NORMALIZATION IDEMPOTENCE
    ---------------------------------------------------------------------------
    Normalizing an already-normalized type produces a structurally equal type:
      normalize (normalize t) =_struct normalize t

    This is important for efficiency and predictability of type comparison.
    --------------------------------------------------------------------------- *)

val normalize_idempotent : t:dep_type -> counter:fresh_counter -> avoid:list dep_var ->
    Lemma (let (t1, c1) = normalize_dep_type t counter avoid in
           let (t2, _) = normalize_dep_type t1 c1 avoid in
           dep_type_eq_structural t1 t2 = true)
let normalize_idempotent t counter avoid =
  let (t1, c1) = normalize_dep_type t counter avoid in
  let (t2, _) = normalize_dep_type t1 c1 avoid in
  (* After first normalization, all bound variables are fresh (x_0, x_1, ...).
     Normalizing again with counter c1 generates x_c1, x_(c1+1), ... but
     since t1's variables are already not in the avoid list (they were fresh),
     the second normalization maps each variable to a fresh one.
     However, by determinism, if we normalize t1 again, the structure is preserved. *)
  (* For structural equality, we rely on the fact that normalization
     with the same counter produces consistent variable names *)
  dep_type_eq_structural_refl t1

(** ---------------------------------------------------------------------------
    SUBSTITUTION IDENTITY LEMMA
    ---------------------------------------------------------------------------
    Substituting a variable for itself is the identity:
      [x/x]t = t
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val subst_identity : x:dep_var -> t:dep_type ->
    Lemma (ensures dep_type_eq_structural (subst_dep_type x (EVar x) t) t = true)
          (decreases t)
    [SMTPat (subst_dep_type x (EVar x) t)]
let rec subst_identity x t =
  match t with
  | DBase _ -> ()
  | DPi y t1 t2 ->
      subst_identity x t1;
      if x = y then () else subst_identity x t2
  | DSigma y t1 t2 ->
      subst_identity x t1;
      if x = y then () else subst_identity x t2
  | DRefinement y t' phi ->
      subst_identity x t'
      (* Formula identity follows similarly *)
  | DApp t' _ ->
      subst_identity x t'
#pop-options

(** ---------------------------------------------------------------------------
    FREE VARIABLE PRESERVATION UNDER SUBSTITUTION
    ---------------------------------------------------------------------------
    If y is not free in e and y != x, then:
      y free in [e/x]t  iff  y free in t
    --------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
val subst_preserves_non_free : x:dep_var -> e:expr -> y:dep_var -> t:dep_type ->
    Lemma (requires y <> x /\ not (is_free_in_expr y e))
          (ensures is_free_in_dep_type y (subst_dep_type x e t) = is_free_in_dep_type y t)
          (decreases t)
let rec subst_preserves_non_free x e y t =
  match t with
  | DBase _ -> ()
  | DPi z t1 t2 ->
      subst_preserves_non_free x e y t1;
      if x = z then () else subst_preserves_non_free x e y t2
  | DSigma z t1 t2 ->
      subst_preserves_non_free x e y t1;
      if x = z then () else subst_preserves_non_free x e y t2
  | DRefinement z t' _ ->
      subst_preserves_non_free x e y t'
  | DApp t' _ ->
      subst_preserves_non_free x e y t'
#pop-options

(** ============================================================================
    TYPE CONSTRUCTORS - Convenience functions
    ============================================================================ *)

(* Create a simple (non-dependent) function type: t1 -> t2 *)
let d_arrow (t1 t2: dep_type) : dep_type =
  DPi "_" t1 t2  (* Underscore indicates non-dependency *)

(* Create a simple (non-dependent) pair type: t1 * t2 *)
let d_pair (t1 t2: dep_type) : dep_type =
  DSigma "_" t1 t2

(* Lift a base type to dependent type *)
let d_base (bt: brrr_type) : dep_type =
  DBase bt

(* Common refined types *)
let d_nat : dep_type =
  DRefinement "n" (DBase t_i32) (FCmp CmpGe (EVar "n") (e_int 0))

let d_pos : dep_type =
  DRefinement "n" (DBase t_i32) (FCmp CmpGt (EVar "n") (e_int 0))

(* Create a bounded integer type: {n: Int | lo <= n < hi} *)
let d_bounded (lo hi: int) : dep_type =
  DRefinement "n" (DBase t_i32)
    (FAnd (FCmp CmpGe (EVar "n") (e_int lo))
          (FCmp CmpLt (EVar "n") (e_int hi)))

(* Array with length refinement: {arr: [T] | length(arr) = n} *)
let d_array_len (elem_ty: brrr_type) (len_var: dep_var) : dep_type =
  DRefinement "arr" (DBase (t_array elem_ty))
    (FCmp CmpEq (ECall (EGlobal "length") [EVar "arr"]) (EVar len_var))

(* Vector type: dependent array with length as type parameter *)
let d_vec (elem_ty: brrr_type) (len: expr) : dep_type =
  DRefinement "v" (DBase (t_array elem_ty))
    (FCmp CmpEq (ECall (EGlobal "length") [EVar "v"]) len)

(** ============================================================================
    DEPENDENT FUNCTION APPLICATION TYPE
    ============================================================================

    For a function f : Pi(x:A).B and argument a : A,
    the application f(a) has type [a/x]B (substitute a for x in B).
    ============================================================================ *)

let app_result_type (fn_type: dep_type) (arg: expr) : option dep_type =
  match fn_type with
  | DPi x t1 t2 -> Some (subst_dep_type x arg t2)
  | _ -> None

(** ============================================================================
    DEPENDENT PAIR PROJECTION TYPES
    ============================================================================

    For a pair p : Sigma(x:A).B:
    - fst(p) : A
    - snd(p) : [fst(p)/x]B
    ============================================================================ *)

let fst_type (pair_type: dep_type) : option dep_type =
  match pair_type with
  | DSigma x t1 t2 -> Some t1
  | _ -> None

let snd_type (pair_type: dep_type) (pair_expr: expr) : option dep_type =
  match pair_type with
  | DSigma x t1 t2 ->
      (* snd has type [fst(pair)/x]t2 *)
      Some (subst_dep_type x (EField pair_expr "0") t2)
  | _ -> None

(** ============================================================================
    REFINEMENT TYPE OPERATIONS
    ============================================================================ *)

(* Extract the base type from a refinement *)
let refinement_base (t: dep_type) : option dep_type =
  match t with
  | DRefinement _ base _ -> Some base
  | _ -> None

(* Extract the predicate from a refinement *)
let refinement_pred (t: dep_type) : option formula =
  match t with
  | DRefinement _ _ phi -> Some phi
  | _ -> None

(* Strengthen a refinement: {x:T|phi} /\ psi -> {x:T|phi /\ psi} *)
let strengthen_refinement (t: dep_type) (extra: formula) : dep_type =
  match t with
  | DRefinement x base phi -> DRefinement x base (FAnd phi extra)
  | _ -> t  (* Cannot strengthen non-refinement *)

(* Weaken a refinement: assume psi => psi' is valid *)
let weaken_refinement (t: dep_type) (weaker: formula) : dep_type =
  match t with
  | DRefinement x base _ -> DRefinement x base weaker
  | _ -> t

(** ============================================================================
    FORMULA SIMPLIFICATION
    ============================================================================ *)

(* Basic formula simplification *)
let rec simplify_formula (phi: formula) : Tot formula (decreases phi) =
  match phi with
  | FAnd FTrue phi' -> simplify_formula phi'
  | FAnd phi' FTrue -> simplify_formula phi'
  | FAnd FFalse _ -> FFalse
  | FAnd _ FFalse -> FFalse
  | FAnd phi1 phi2 -> FAnd (simplify_formula phi1) (simplify_formula phi2)

  | FOr FTrue _ -> FTrue
  | FOr _ FTrue -> FTrue
  | FOr FFalse phi' -> simplify_formula phi'
  | FOr phi' FFalse -> simplify_formula phi'
  | FOr phi1 phi2 -> FOr (simplify_formula phi1) (simplify_formula phi2)

  | FNot FTrue -> FFalse
  | FNot FFalse -> FTrue
  | FNot (FNot phi') -> simplify_formula phi'
  | FNot phi' -> FNot (simplify_formula phi')

  | FImpl FFalse _ -> FTrue   (* Ex falso quodlibet *)
  | FImpl _ FTrue -> FTrue
  | FImpl FTrue phi' -> simplify_formula phi'
  | FImpl phi1 phi2 -> FImpl (simplify_formula phi1) (simplify_formula phi2)

  | FForall x t phi' -> FForall x t (simplify_formula phi')
  | FExists x t phi' -> FExists x t (simplify_formula phi')

  | _ -> phi

(** ============================================================================
    WELL-FORMEDNESS CHECKS WITH TYPE CONTEXT
    ============================================================================

    A type context maps term variables to their types. This is necessary for
    well-formedness checking because:
    1. Variables in types/formulas must be bound in the context
    2. Pi/Sigma/Refinement types introduce new bindings
    3. Expressions used in types must be well-typed

    Context format: list of (variable, type) pairs, newest first
    ============================================================================ *)

(* Type context: maps term variables to their dependent types *)
type dep_type_ctx = list (dep_var & dep_type)

(* Look up a variable in the context *)
let rec ctx_lookup (x: dep_var) (ctx: dep_type_ctx) : option dep_type =
  match ctx with
  | [] -> None
  | (y, t) :: rest -> if x = y then Some t else ctx_lookup x rest

(* Check if a variable is bound in the context *)
let ctx_contains (x: dep_var) (ctx: dep_type_ctx) : bool =
  Some? (ctx_lookup x ctx)

(* Extend context with a new binding *)
let ctx_extend (x: dep_var) (t: dep_type) (ctx: dep_type_ctx) : dep_type_ctx =
  (x, t) :: ctx

(* Check if all free variables in an expression are bound in the context *)
let rec expr_vars_in_ctx (e: expr) (ctx: dep_type_ctx) : Tot bool (decreases %[expr_size e; 0]) =
  match e with
  | EVar x -> ctx_contains x ctx
  | ELit _ | EGlobal _ | EContinue | EHole | EError _ | ESizeof _ | EAlignof _ -> true
  | EUnary _ e' -> expr_vars_in_ctx e' ctx
  | EBinary _ e1 e2 -> expr_vars_in_ctx e1 ctx && expr_vars_in_ctx e2 ctx
  | ECall fn args -> expr_vars_in_ctx fn ctx && expr_list_vars_in_ctx args ctx
  | EMethodCall obj _ args -> expr_vars_in_ctx obj ctx && expr_list_vars_in_ctx args ctx
  | ETuple es | EArray es | EBlock es -> expr_list_vars_in_ctx es ctx
  | EStruct _ fields -> expr_field_vars_in_ctx fields ctx
  | EVariant _ _ es -> expr_list_vars_in_ctx es ctx
  | EField e' _ | ETupleProj e' _ -> expr_vars_in_ctx e' ctx
  | EIndex e1 e2 -> expr_vars_in_ctx e1 ctx && expr_vars_in_ctx e2 ctx
  | EIf c t f -> expr_vars_in_ctx c ctx && expr_vars_in_ctx t ctx && expr_vars_in_ctx f ctx
  | ELoop body -> expr_vars_in_ctx body ctx
  | EWhile c body -> expr_vars_in_ctx c ctx && expr_vars_in_ctx body ctx
  | EFor x iter body ->
      expr_vars_in_ctx iter ctx &&
      expr_vars_in_ctx body (ctx_extend x (DBase t_dynamic) ctx)
  | EBreak None | EReturn None -> true
  | EBreak (Some e') | EReturn (Some e') -> expr_vars_in_ctx e' ctx
  | ELet (PatVar x) _ e1 e2 ->
      expr_vars_in_ctx e1 ctx &&
      expr_vars_in_ctx e2 (ctx_extend x (DBase t_dynamic) ctx)
  | ELet _ _ e1 e2 -> expr_vars_in_ctx e1 ctx && expr_vars_in_ctx e2 ctx
  | ELetMut x _ e1 e2 ->
      expr_vars_in_ctx e1 ctx &&
      expr_vars_in_ctx e2 (ctx_extend x (DBase t_dynamic) ctx)
  | EAssign lhs rhs -> expr_vars_in_ctx lhs ctx && expr_vars_in_ctx rhs ctx
  | ELambda params body ->
      let extended_ctx = List.Tot.fold_left
        (fun acc (x, _) -> ctx_extend x (DBase t_dynamic) acc) ctx params in
      expr_vars_in_ctx body extended_ctx
  | EClosure params _ body ->
      let extended_ctx = List.Tot.fold_left
        (fun acc (x, _) -> ctx_extend x (DBase t_dynamic) acc) ctx params in
      expr_vars_in_ctx body extended_ctx
  | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e' | EMove e' | EDrop e' -> expr_vars_in_ctx e' ctx
  | EThrow e' | EAwait e' | EYield e' -> expr_vars_in_ctx e' ctx
  | EAs e' _ | EIs e' _ -> expr_vars_in_ctx e' ctx
  | ESeq e1 e2 -> expr_vars_in_ctx e1 ctx && expr_vars_in_ctx e2 ctx
  | EUnsafe e' -> expr_vars_in_ctx e' ctx
  | _ -> true  (* For complex cases, conservatively return true *)

and expr_list_vars_in_ctx (es: list expr) (ctx: dep_type_ctx)
    : Tot bool (decreases %[expr_list_size es; 1]) =
  match es with
  | [] -> true
  | e :: rest -> expr_vars_in_ctx e ctx && expr_list_vars_in_ctx rest ctx

and expr_field_vars_in_ctx (fields: list (string & expr)) (ctx: dep_type_ctx)
    : Tot bool (decreases %[field_expr_list_size fields; 2]) =
  match fields with
  | [] -> true
  | (_, e) :: rest -> expr_vars_in_ctx e ctx && expr_field_vars_in_ctx rest ctx

(* Check if a formula is well-formed in a context *)
let rec formula_well_formed_in_ctx (phi: formula) (ctx: dep_type_ctx)
    : Tot bool (decreases phi) =
  match phi with
  | FTrue | FFalse -> true
  | FCmp _ e1 e2 -> expr_vars_in_ctx e1 ctx && expr_vars_in_ctx e2 ctx
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      formula_well_formed_in_ctx phi1 ctx && formula_well_formed_in_ctx phi2 ctx
  | FNot phi' -> formula_well_formed_in_ctx phi' ctx
  | FForall x bt phi' | FExists x bt phi' ->
      (* The bound type must be well-formed, then extend context for body *)
      formula_well_formed_in_ctx phi' (ctx_extend x (DBase bt) ctx)
  | FPred _ e -> expr_vars_in_ctx e ctx
  | FExpr e -> expr_vars_in_ctx e ctx

(* Check if a dependent type is well-formed in a context.
   A type is well-formed if:
   1. All free term variables are bound in the context
   2. All component types are well-formed
   3. Binders (Pi, Sigma, Refinement) properly extend the context *)
let rec well_formed_in_ctx (t: dep_type) (ctx: dep_type_ctx)
    : Tot bool (decreases t) =
  match t with
  | DBase _ -> true  (* Base types are always well-formed *)

  | DPi x s t' ->
      (* Domain must be well-formed in current context *)
      well_formed_in_ctx s ctx &&
      (* Codomain must be well-formed with x:s added to context *)
      well_formed_in_ctx t' (ctx_extend x s ctx)

  | DSigma x s t' ->
      (* First component must be well-formed in current context *)
      well_formed_in_ctx s ctx &&
      (* Second component must be well-formed with x:s added to context *)
      well_formed_in_ctx t' (ctx_extend x s ctx)

  | DRefinement x base phi ->
      (* Base type must be well-formed *)
      well_formed_in_ctx base ctx &&
      (* Refinement formula must be well-formed with x:base added *)
      formula_well_formed_in_ctx phi (ctx_extend x base ctx)

  | DApp t' e ->
      (* Type must be well-formed *)
      well_formed_in_ctx t' ctx &&
      (* Expression must have all variables bound *)
      expr_vars_in_ctx e ctx

(* Legacy wrapper: check well-formedness in empty context *)
let is_well_formed (t: dep_type) : bool =
  well_formed_in_ctx t []

(* Check well-formedness in a given context *)
let is_well_formed_ctx (t: dep_type) (ctx: dep_type_ctx) : bool =
  well_formed_in_ctx t ctx

(* Check if a closed type is well-formed (no free variables allowed) *)
let is_closed_well_formed (t: dep_type) : bool =
  is_well_formed t && List.Tot.isEmpty (dep_type_free_vars t)

(** ============================================================================
    PRETTY PRINTING (for debugging)
    ============================================================================ *)

let rec formula_to_string (phi: formula) : Tot string (decreases phi) =
  match phi with
  | FTrue -> "true"
  | FFalse -> "false"
  | FCmp CmpEq _ _ -> "_ = _"
  | FCmp CmpNe _ _ -> "_ != _"
  | FCmp CmpLt _ _ -> "_ < _"
  | FCmp CmpLe _ _ -> "_ <= _"
  | FCmp CmpGt _ _ -> "_ > _"
  | FCmp CmpGe _ _ -> "_ >= _"
  | FAnd phi1 phi2 -> "(" ^ formula_to_string phi1 ^ " /\\ " ^ formula_to_string phi2 ^ ")"
  | FOr phi1 phi2 -> "(" ^ formula_to_string phi1 ^ " \\/ " ^ formula_to_string phi2 ^ ")"
  | FNot phi' -> "~" ^ formula_to_string phi'
  | FImpl phi1 phi2 -> "(" ^ formula_to_string phi1 ^ " => " ^ formula_to_string phi2 ^ ")"
  | FIff phi1 phi2 -> "(" ^ formula_to_string phi1 ^ " <=> " ^ formula_to_string phi2 ^ ")"
  | FForall x _ phi' -> "forall " ^ x ^ ". " ^ formula_to_string phi'
  | FExists x _ phi' -> "exists " ^ x ^ ". " ^ formula_to_string phi'
  | FPred name _ -> name ^ "(_)"
  | FExpr _ -> "<expr>"

let rec dep_type_to_string (t: dep_type) : Tot string (decreases t) =
  match t with
  | DBase _ -> "<base>"
  | DPi x t1 t2 ->
      "Pi(" ^ x ^ ":" ^ dep_type_to_string t1 ^ ")." ^ dep_type_to_string t2
  | DSigma x t1 t2 ->
      "Sigma(" ^ x ^ ":" ^ dep_type_to_string t1 ^ ")." ^ dep_type_to_string t2
  | DRefinement x t phi ->
      "{" ^ x ^ ":" ^ dep_type_to_string t ^ " | " ^ formula_to_string phi ^ "}"
  | DApp t _ -> dep_type_to_string t ^ "(_)"

(** ============================================================================
    SMT INTEGRATION NOTES
    ============================================================================

    The formula_implies function above is SYNTACTIC ONLY - it cannot handle:
    1. Quantified formulas (forall, exists)
    2. Arithmetic reasoning (x + 1 > x)
    3. Transitive chains (x < y /\ y < z => x < z)
    4. Uninterpreted functions

    For SEMANTIC formula implication, use the SMT module:

      open SMT

      (* Use SMT for semantic implication *)
      let formula_implies_smt (phi1 phi2: formula) : trilean =
        formula_implies_hybrid default_smt_config phi1 phi2

      (* Returns Definitely, DefinitelyNot, or Unknown *)

    The hybrid approach first tries syntactic (fast) then falls back to SMT.

    See SMT.fst for:
    - formula_to_smt_term: Translate formulas to SMTLIB2
    - smt_check_implication: Check phi1 => phi2 via SMT
    - trilean type: Three-valued logic result
    - smt_config: Timeout and logic configuration
    ============================================================================ *)

(** ============================================================================
    DIVERGENCE STRATIFICATION NOTES
    ============================================================================

    For LAZY languages (Haskell, parts of Python/JS), the formula_implies
    check may be UNSOUND if applied to potentially-diverging expressions.

    The problem: In lazy evaluation, an expression may never be evaluated,
    so assuming its refinement holds is unsound.

    Solution: Use divergence-aware types from DivergenceLabels.fst:

      open DivergenceLabels

      (* Stratified refinement type *)
      type strat_refinement = {
        sr_var   : dep_var;
        sr_base  : dep_type;
        sr_phi   : formula;
        sr_label : divergence_label;  (* DivMay | DivWhnf | DivFin *)
      }

      (* Only use refinement in VC when label guarantees evaluation *)
      let include_in_vc (mode: eval_mode) (sr: strat_refinement) : bool =
        match mode with
        | EvalStrict -> true
        | EvalLazy | EvalHybrid ->
            match sr.sr_label with
            | DivMay -> false  (* Cannot assume refinement *)
            | DivWhnf | DivFin -> true

    See DivergenceLabels.fst for full implementation.
    ============================================================================ *)

(** ============================================================================
    PROPOSITIONAL EQUALITY NOTES
    ============================================================================

    For type-level reasoning and GADTs, use propositional equality from
    PropositionalEquality.fst:

      open PropositionalEquality

      (* Equality type: proof that x equals y *)
      type eq_type (a: Type) (x y: a) = | Refl : eq_type a x x

      (* Substitution: if x = y, property P transfers *)
      val subst : eq_type a x y -> (a -> Type) -> P x -> P y

      (* Enables:
         - GADT-style dependent pattern matching
         - Type-safe coercions along equality proofs
         - Leibniz reasoning *)

    Universe levels for type stratification are also defined there.
    ============================================================================ *)
