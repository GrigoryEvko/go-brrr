(**
 * BrrrLang.Core.SecurityTypeChecker
 *
 * Security-aware type checker for Brrr-Lang IR.
 * Extends the base type checker with security label tracking.
 *
 * Implements:
 *   - Security context with label tracking
 *   - PC (program counter) label for implicit flow prevention
 *   - Security-typed inference and checking
 *   - Taint propagation through expressions
 *   - Effect-based taint tracking
 *   - Source/Sink/Sanitizer annotation checking
 *
 * Based on:
 *   - Denning 1977 (Information Flow)
 *   - Volpano 1996 (Security Type System)
 *   - brrr_lang_spec_v0.4.tex Part IX
 *
 * Depends on: TypeChecker, SecurityTypes, TaintEffects, Expressions
 *)
module SecurityTypeChecker

(** Z3 solver options for security type checking proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open SecurityTypes
open TaintEffects

(** ============================================================================
    SECURITY TYPE CONTEXT
    ============================================================================

    Extends the base type context with security labels.
    Each variable has: name, base type, mode, and security label.
    ============================================================================ *)

(** Security context entry *)
noeq type sec_ctx_binding = {
  scb_name  : var_id;
  scb_type  : sec_type;      (* Base type + security label *)
  scb_mode  : mode;
}

(** Security type context *)
type security_ctx = list sec_ctx_binding

(** Empty security context *)
let empty_security_ctx : security_ctx = []

(** Extend security context *)
let extend_security_ctx
    (x: var_id)
    (st: sec_type)
    (m: mode)
    (ctx: security_ctx)
    : security_ctx =
  { scb_name = x; scb_type = st; scb_mode = m } :: ctx

(** Lookup in security context *)
let rec lookup_security_ctx (x: var_id) (ctx: security_ctx)
    : option (sec_type & mode) =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.scb_name = x then Some (b.scb_type, b.scb_mode)
      else lookup_security_ctx x rest

(** Merge two security contexts after branch divergence.
    For each variable present in both contexts, join their security labels.
    This is critical for soundness: after an if-then-else, a variable may have
    been assigned different values in each branch, so its label must reflect
    the join of both possibilities.

    Invariant: Both contexts should have the same domain (same variables). *)
let rec merge_security_ctx (ctx1 ctx2: security_ctx) : security_ctx =
  match ctx1, ctx2 with
  | [], [] -> []
  | b1 :: rest1, b2 :: rest2 ->
      if b1.scb_name = b2.scb_name then
        (* Join the security labels from both branches *)
        let merged_label = sec_label_join b1.scb_type.label b2.scb_type.label in
        let merged_type = { b1.scb_type with label = merged_label } in
        (* Mode is the minimum of both (most restrictive) *)
        let merged_mode = match b1.scb_mode, b2.scb_mode with
          | MZero, _ | _, MZero -> MZero
          | MOne, _ | _, MOne -> MOne
          | MOmega, MOmega -> MOmega
        in
        { scb_name = b1.scb_name; scb_type = merged_type; scb_mode = merged_mode }
        :: merge_security_ctx rest1 rest2
      else
        (* Misaligned contexts - fallback to first context binding *)
        (* This should not happen for well-formed type checking *)
        b1 :: merge_security_ctx rest1 ctx2
  | ctx, [] -> ctx
  | [], ctx -> ctx

(** Consume a linear variable in security context *)
let rec consume_sec_var (x: var_id) (ctx: security_ctx)
    : option security_ctx =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.scb_name = x then
        match b.scb_mode with
        | MZero -> None
        | MOne -> Some ({ b with scb_mode = MZero } :: rest)
        | MOmega -> Some (b :: rest)
      else
        match consume_sec_var x rest with
        | Some rest' -> Some (b :: rest')
        | None -> None

(** ============================================================================
    SECURITY TYPING RESULT
    ============================================================================ *)

(** Result of security type checking *)
type sec_typing_result =
  | STyOk    : sec_type -> security_ctx -> effect_row -> sec_typing_result
  | STyError : string -> sec_typing_result

(** Combine effects from sequential expressions *)
let seq_effects (e1: effect_row) (e2: effect_row) : effect_row =
  row_join e1 e2

(** ============================================================================
    SECURITY TYPE INFERENCE FOR LITERALS
    ============================================================================

    Literals are always untainted and public - they are constant values
    that don't come from any external source.
    ============================================================================ *)

(** Infer base type of a literal *)
let literal_base_type (lit: literal) : brrr_type =
  match lit with
  | LitUnit -> t_unit
  | LitBool _ -> t_bool
  | LitInt _ it -> t_int it
  | LitFloat _ fp -> t_float fp
  | LitString _ -> t_string
  | LitChar _ -> t_char

(** Infer security type of a literal (always untainted) *)
let infer_literal_sec (lit: literal) : sec_type =
  untainted_type (literal_base_type lit)

(** ============================================================================
    SECURITY TYPE INFERENCE FOR OPERATORS
    ============================================================================

    For operations:
    - Unary: result has same security as operand
    - Binary: result has join of both operand securities
    ============================================================================ *)

(** Infer type of unary operation *)
let infer_unary_sec (op: unary_op) (st: sec_type) : option sec_type =
  match op, st.base with
  | OpNeg, TNumeric (NumInt it) ->
      Some { base = t_int it; label = st.label }
  | OpNeg, TNumeric (NumFloat fp) ->
      Some { base = t_float fp; label = st.label }
  | OpNot, TPrim PBool ->
      Some { base = t_bool; label = st.label }
  | OpBitNot, TNumeric (NumInt it) ->
      Some { base = t_int it; label = st.label }
  | OpDeref, TWrap WRef inner ->
      Some { base = inner; label = st.label }
  | OpDeref, TWrap WRefMut inner ->
      Some { base = inner; label = st.label }
  | OpRef, t ->
      Some { base = t_ref t; label = st.label }
  | OpRefMut, t ->
      Some { base = t_ref_mut t; label = st.label }
  | _, _ -> None

(** Infer type of binary operation *)
let infer_binary_sec (op: binary_op) (st1 st2: sec_type) : option sec_type =
  let result_label = sec_label_join st1.label st2.label in
  match op with
  (* Arithmetic *)
  | OpAdd | OpSub | OpMul | OpDiv | OpMod ->
      (match st1.base, st2.base with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
           if i1 = i2 then Some { base = t_int i1; label = result_label }
           else None
       | TNumeric (NumFloat f1), TNumeric (NumFloat f2) ->
           if f1 = f2 then Some { base = t_float f1; label = result_label }
           else None
       | _, _ -> None)
  (* Comparison *)
  | OpEq | OpNe | OpLt | OpLe | OpGt | OpGe ->
      if type_eq st1.base st2.base then
        Some { base = t_bool; label = result_label }
      else None
  (* Logical *)
  | OpAnd | OpOr ->
      (match st1.base, st2.base with
       | TPrim PBool, TPrim PBool ->
           Some { base = t_bool; label = result_label }
       | _, _ -> None)
  (* Bitwise *)
  | OpBitAnd | OpBitOr | OpBitXor ->
      (match st1.base, st2.base with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
           if i1 = i2 then Some { base = t_int i1; label = result_label }
           else None
       | _, _ -> None)
  | OpShl | OpShr ->
      (match st1.base, st2.base with
       | TNumeric (NumInt i1), TNumeric (NumInt _) ->
           Some { base = t_int i1; label = result_label }
       | _, _ -> None)

(** ============================================================================
    SECURITY TYPE CHECKING
    ============================================================================

    Main security type checking algorithm with PC tracking.
    ============================================================================ *)

(** Infer security type of expression *)
let rec sec_infer
    (ctx: security_ctx)
    (pc: pc_label)
    (e: expr)
    : Tot sec_typing_result (decreases e) =
  match e with
  (* Literal: always untainted *)
  | ELit lit ->
      STyOk (infer_literal_sec lit) ctx pure

  (* Variable: lookup in context *)
  | EVar x ->
      (match lookup_security_ctx x ctx with
       | Some (st, m) ->
           if m = MZero then
             STyError ("Variable already consumed: " ^ x)
           else
             (match consume_sec_var x ctx with
              | Some ctx' -> STyOk st ctx' pure
              | None -> STyError ("Cannot consume variable: " ^ x))
       | None ->
           STyError ("Variable not found: " ^ x))

  (* Global: assume untainted unless annotated *)
  | EGlobal name ->
      STyOk (untainted_type t_dynamic) ctx pure

  (* Unary operation: propagate security *)
  | EUnary op e1 ->
      (match sec_infer ctx pc e1 with
       | STyOk st1 ctx1 eff1 ->
           (match infer_unary_sec op st1 with
            | Some st -> STyOk st ctx1 eff1
            | None -> STyError "Type error in unary operation")
       | STyError msg -> STyError msg)

  (* Binary operation: join securities *)
  | EBinary op e1 e2 ->
      (match sec_infer ctx pc e1 with
       | STyOk st1 ctx1 eff1 ->
           (match sec_infer ctx1 pc e2 with
            | STyOk st2 ctx2 eff2 ->
                (match infer_binary_sec op st1 st2 with
                 | Some st -> STyOk st ctx2 (seq_effects eff1 eff2)
                 | None -> STyError "Type error in binary operation")
            | STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* Tuple: join all element securities WITH PC.
     A tuple constructed under high PC must have that PC reflected in its label.
     This prevents implicit flow: if (secret) { tuple = (a, b); } *)
  | ETuple es ->
      (match sec_infer_list ctx pc es with
       | STyOk' sts ctx' effs ->
           let labels = List.Tot.map (fun st -> st.label) sts in
           let bases = List.Tot.map (fun st -> st.base) sts in
           (* CRITICAL: Include PC in the joined label to capture implicit flows *)
           let elem_joined = List.Tot.fold_left sec_label_join sec_public_trusted labels in
           let joined = sec_label_join pc elem_joined in
           STyOk { base = TTuple bases; label = joined } ctx' effs
       | STyError' msg -> STyError msg)

  (* If-then-else: raise PC for branches.
     CRITICAL for non-interference:
     1. Result label MUST include PC' (raised PC) because the value was computed
        under that PC. Even if both branches return public data, the fact that
        we're in a branch guarded by a secret makes the result secret.
     2. Contexts from both branches MUST be merged, joining labels for any
        variable that might have been modified differently in each branch. *)
  | EIf cond then_e else_e ->
      (match sec_infer ctx pc cond with
       | STyOk cond_st ctx1 eff1 ->
           if not (type_eq cond_st.base t_bool) then
             STyError "Condition must be boolean"
           else
             (* Raise PC based on condition's security *)
             let pc' = raise_pc pc cond_st.label in
             (match sec_infer ctx1 pc' then_e, sec_infer ctx1 pc' else_e with
              | STyOk then_st ctx_then eff_then, STyOk else_st ctx_else eff_else ->
                  if type_eq then_st.base else_st.base then
                    (* CRITICAL FIX: Result MUST include PC' because value computed under raised PC.
                       Example: if (secret) { 1 } else { 2 } -- result is SECRET, not public!
                       The information about which branch was taken leaks through the value. *)
                    let branch_joined = sec_label_join then_st.label else_st.label in
                    let result_label = sec_label_join pc' branch_joined in
                    (* CRITICAL FIX: Merge contexts from both branches.
                       Variables modified in either branch must have their labels joined. *)
                    let merged_ctx = merge_security_ctx ctx_then ctx_else in
                    let result_st = { base = then_st.base; label = result_label } in
                    STyOk result_st merged_ctx (seq_effects eff1 (row_join eff_then eff_else))
                  else
                    STyError "Branches have incompatible types"
              | STyError msg, _ -> STyError msg
              | _, STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* Let binding: bound variable inherits PC label to prevent implicit flows.
     If we're in a branch guarded by secret condition, the binding inherits that secrecy.
     This is critical for soundness: x = e under high PC means x's label >= PC. *)
  | ELet (PatVar x) _ e1 e2 ->
      (match sec_infer ctx pc e1 with
       | STyOk st1 ctx1 eff1 ->
           (* Join the expression's label with PC to capture implicit flows *)
           let effective_label = sec_label_join pc st1.label in
           let st1_with_pc = { st1 with label = effective_label } in
           let ctx2 = extend_security_ctx x st1_with_pc MOmega ctx1 in
           (match sec_infer ctx2 pc e2 with
            | STyOk st2 ctx3 eff2 ->
                STyOk st2 ctx3 (seq_effects eff1 eff2)
            | STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* Assignment: check flow constraint *)
  | EAssign (EVar x) rhs ->
      (match lookup_security_ctx x ctx with
       | Some (lhs_st, _) ->
           (match sec_infer ctx pc rhs with
            | STyOk rhs_st ctx1 eff ->
                (* Flow check: pc join rhs_label <= lhs_label *)
                if check_flow pc rhs_st.label lhs_st.label then
                  STyOk (untainted_type t_unit) ctx1 eff
                else
                  STyError "Security flow violation in assignment"
            | STyError msg -> STyError msg)
       | None ->
           STyError ("Variable not found: " ^ x))

  (* Sequence *)
  | ESeq e1 e2 ->
      (match sec_infer ctx pc e1 with
       | STyOk _ ctx1 eff1 ->
           (match sec_infer ctx1 pc e2 with
            | STyOk st2 ctx2 eff2 ->
                STyOk st2 ctx2 (seq_effects eff1 eff2)
            | STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* Block *)
  | EBlock es ->
      sec_infer_block ctx pc es

  (* While loop: raise PC based on condition to track implicit flows through loop *)
  | EWhile _ cond body ->
      (match sec_infer ctx pc cond with
       | STyOk cond_st ctx1 eff1 ->
           if not (type_eq cond_st.base t_bool) then
             STyError "While condition must be boolean"
           else
             (* Raise PC for loop body - loop condition controls what executes *)
             let pc' = raise_pc pc cond_st.label in
             (match sec_infer ctx1 pc' body with
              | STyOk _ ctx2 eff2 ->
                  (* While loop returns unit *)
                  STyOk (untainted_type t_unit) ctx2 (seq_effects eff1 eff2)
              | STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* For loop: raise PC based on iterator expression *)
  | EFor _ x iter body ->
      (match sec_infer ctx pc iter with
       | STyOk iter_st ctx1 eff1 ->
           (* Raise PC based on iterator's security - controls loop iterations *)
           let pc' = raise_pc pc iter_st.label in
           (* Bind loop variable with iterator's label joined with PC *)
           let effective_label = sec_label_join pc' iter_st.label in
           let elem_type = untainted_type t_dynamic in  (* Simplified: would need actual element type *)
           let elem_st = { elem_type with label = effective_label } in
           let ctx2 = extend_security_ctx x elem_st MOmega ctx1 in
           (match sec_infer ctx2 pc' body with
            | STyOk _ ctx3 eff2 ->
                STyOk (untainted_type t_unit) ctx3 (seq_effects eff1 eff2)
            | STyError msg -> STyError msg)
       | STyError msg -> STyError msg)

  (* Infinite loop: PC stays the same, no condition *)
  | ELoop _ body ->
      (match sec_infer ctx pc body with
       | STyOk _ ctx1 eff ->
           (* Loop returns unit (or never, but simplified here) *)
           STyOk (untainted_type t_unit) ctx1 eff
       | STyError msg -> STyError msg)

  (* Match expression: raise PC based on scrutinee.
     CRITICAL: The scrutinee's security label affects all arm results because
     which arm executes reveals information about the scrutinee's value.
     Contexts from all arms must be merged since different arms may modify
     variables differently. *)
  | EMatch scrutinee arms ->
      (match sec_infer ctx pc scrutinee with
       | STyOk scrut_st ctx1 eff1 ->
           (* Raise PC based on scrutinee - controls which arm executes *)
           let pc' = raise_pc pc scrut_st.label in
           (match sec_infer_match_arms ctx1 pc' arms with
            | Some (result_st, merged_ctx, eff2) ->
                (* Use merged context from all arms *)
                STyOk result_st merged_ctx (seq_effects eff1 eff2)
            | None ->
                STyError "Match arms have incompatible types or patterns")
       | STyError msg -> STyError msg)

  (* Try-catch: PC stays same, but catch arms may have tainted exceptions *)
  | ETry body catch_arms finally_opt ->
      (match sec_infer ctx pc body with
       | STyOk body_st ctx1 eff1 ->
           (* For now, simplified handling of try-catch *)
           STyOk body_st ctx1 eff1
       | STyError msg -> STyError msg)

  (* Other expressions - simplified handling *)
  | _ -> STyError "Expression not yet supported in security checker"

(** Infer security types for a list of expressions *)
and sec_infer_list
    (ctx: security_ctx)
    (pc: pc_label)
    (es: list expr)
    : Tot sec_list_result (decreases es)
and sec_list_result =
  | STyOk'    : list sec_type -> security_ctx -> effect_row -> sec_list_result
  | STyError' : string -> sec_list_result

let rec sec_infer_list ctx pc es =
  match es with
  | [] -> STyOk' [] ctx pure
  | e :: rest ->
      match sec_infer ctx pc e with
      | STyOk st ctx' eff ->
          (match sec_infer_list ctx' pc rest with
           | STyOk' sts ctx'' effs ->
               STyOk' (st :: sts) ctx'' (seq_effects eff effs)
           | STyError' msg -> STyError' msg)
      | STyError msg -> STyError' msg

(** Infer security type of a block *)
and sec_infer_block
    (ctx: security_ctx)
    (pc: pc_label)
    (es: list expr)
    : Tot sec_typing_result (decreases es) =
  match es with
  | [] -> STyOk (untainted_type t_unit) ctx pure
  | [e] -> sec_infer ctx pc e
  | e :: rest ->
      match sec_infer ctx pc e with
      | STyOk _ ctx' eff ->
          (match sec_infer_block ctx' pc rest with
           | STyOk st ctx'' effs -> STyOk st ctx'' (seq_effects eff effs)
           | STyError msg -> STyError msg)
      | STyError msg -> STyError msg

(** Infer security type for match arms.
    Each arm's body is checked under the raised PC.
    CRITICAL: Result label MUST include PC because match arms execute under
    the PC raised by the scrutinee. The choice of which arm executes leaks
    information about the scrutinee's value.
    Returns the joined result type, merged context, and effects of all arms. *)
let rec sec_infer_match_arms
    (ctx: security_ctx)
    (pc: pc_label)
    (arms: list match_arm)
    : option (sec_type & security_ctx & effect_row) =
  match arms with
  | [] -> None  (* Empty match is an error *)
  | [arm] ->
      (* Single arm: check the body, result includes PC *)
      (match sec_infer ctx pc arm.arm_body with
       | STyOk st ctx' eff ->
           (* CRITICAL: Include PC in result label *)
           let result_label = sec_label_join pc st.label in
           let result_st = { st with label = result_label } in
           Some (result_st, ctx', eff)
       | STyError _ -> None)
  | arm :: rest ->
      (* Multiple arms: check first, then recurse and join *)
      (match sec_infer ctx pc arm.arm_body with
       | STyOk st1 ctx1 eff1 ->
           (match sec_infer_match_arms ctx pc rest with
            | Some (st2, ctx2, eff2) ->
                if type_eq st1.base st2.base then
                  (* CRITICAL FIX: Include PC in joined label.
                     Which arm executed depends on scrutinee value. *)
                  let branch_joined = sec_label_join st1.label st2.label in
                  let result_label = sec_label_join pc branch_joined in
                  let result_st = { base = st1.base; label = result_label } in
                  (* Merge contexts from all arms *)
                  let merged_ctx = merge_security_ctx ctx1 ctx2 in
                  Some (result_st, merged_ctx, row_join eff1 eff2)
                else None
            | None -> None)
       | STyError _ -> None)

(** ============================================================================
    FUNCTION SECURITY CHECKING
    ============================================================================ *)

(** Check function against security role *)
let check_function_role
    (func_st: sec_func_type)
    (effects: effect_row)
    : option string =
  match func_st.sf_role with
  | SrNone -> None  (* No security constraints *)

  | SrSource taints ->
      (* Source must return tainted data *)
      if has_any_taint taints func_st.sf_return.label then None
      else Some "Source function must return tainted data"

  | SrSink rejected ->
      (* Sink must not receive tainted data *)
      let param_taints = List.Tot.map (fun p -> p.sp_type.label) func_st.sf_params in
      if List.Tot.existsb (fun l -> has_any_taint rejected l) param_taints then
        Some "Sink function received tainted data"
      else None

  | SrSanitizer removes ->
      (* Sanitizer must remove specified taints *)
      None  (* Checked structurally *)

  | SrValidator _ ->
      None  (* Validators are partial sanitizers *)

(** ============================================================================
    EFFECT-BASED TAINT CHECKING
    ============================================================================ *)

(** Check expression effects for taint safety *)
let check_effect_taint_safety
    (input_taint: sec_label)
    (effects: effect_row)
    : option string =
  let violations = detect_violations input_taint effects in
  match violations with
  | [] -> None
  | v :: _ -> Some v.tv_message

(** ============================================================================
    SECURITY ANNOTATION CHECKING
    ============================================================================ *)

(** Check if function call respects sink annotations *)
let check_sink_annotation
    (snk: sink_annotation)
    (arg_types: list sec_type)
    : bool =
  let arg_labels = List.Tot.map (fun st -> st.label) arg_types in
  sink_check snk arg_labels

(** Check if result matches source annotation *)
let check_source_annotation
    (src: source_annotation)
    (result_type: sec_type)
    : bool =
  (* Source should return data tainted with declared taints *)
  let expected_taints = src.src_taints in
  List.Tot.for_all (fun k -> taint_in_set k result_type.label.taints) expected_taints

(** ============================================================================
    SECURITY TYPE CHECKING ENTRY POINT
    ============================================================================ *)

(** Full security check for an expression *)
let security_check
    (ctx: security_ctx)
    (e: expr)
    : option string =
  match sec_infer ctx initial_pc e with
  | STyOk st ctx' effects ->
      (* Check effect-based taint safety *)
      check_effect_taint_safety sec_public_trusted effects
  | STyError msg ->
      Some msg

(** Security check for a function body *)
let security_check_function
    (params: list sec_param)
    (body: expr)
    (role: sec_role)
    : option string =
  (* Build context from parameters *)
  let ctx = List.Tot.fold_right
    (fun p ctx ->
      match p.sp_name with
      | Some name -> extend_security_ctx name p.sp_type p.sp_mode ctx
      | None -> ctx)
    params
    empty_security_ctx
  in
  (* Infer body type *)
  match sec_infer ctx initial_pc body with
  | STyOk result_st ctx' effects ->
      (* Check role constraints *)
      let func_st = {
        sf_params = params;
        sf_return = result_st;
        sf_effects = effects;
        sf_role = role;
        sf_is_unsafe = false;
      } in
      check_function_role func_st effects
  | STyError msg ->
      Some msg

(** ============================================================================
    NON-INTERFERENCE THEOREM
    ============================================================================

    The fundamental security property: if two contexts agree on low (observable)
    data, then evaluation under those contexts produces results that also agree
    on low data. This ensures that high (secret) data cannot influence what an
    observer at level `obs` can see.

    Definition: Two contexts are low-equivalent at observation level `obs` if
    for every variable x with label l such that l <= obs, both contexts agree
    on x's value.
    ============================================================================ *)

(** Check if a security label is observable at a given observation level *)
let is_observable (l: sec_label) (obs: sec_label) : bool =
  sec_label_leq l obs

(** Check if two security context entries are low-equivalent at observation level *)
let ctx_entry_low_equiv (obs: sec_label) (b1 b2: sec_ctx_binding) : bool =
  if b1.scb_name = b2.scb_name then
    (* If the variable is observable, entries must have same type and label *)
    if is_observable b1.scb_type.label obs then
      type_eq b1.scb_type.base b2.scb_type.base &&
      sec_label_eq b1.scb_type.label b2.scb_type.label
    else
      (* High (non-observable) variables can differ *)
      true
  else
    false

(** Check if two security contexts are low-equivalent at observation level *)
let rec low_equiv (obs: sec_label) (ctx1 ctx2: security_ctx) : bool =
  match ctx1, ctx2 with
  | [], [] -> true
  | b1 :: rest1, b2 :: rest2 ->
      ctx_entry_low_equiv obs b1 b2 && low_equiv obs rest1 rest2
  | _, _ -> false  (* Different lengths means not equivalent *)

(** Check if two security types are low-equivalent at observation level *)
let sec_type_low_equiv (obs: sec_label) (st1 st2: sec_type) : bool =
  if is_observable st1.label obs && is_observable st2.label obs then
    type_eq st1.base st2.base && sec_label_eq st1.label st2.label
  else if not (is_observable st1.label obs) && not (is_observable st2.label obs) then
    (* Both high - they're equivalent from observer's perspective *)
    true
  else
    (* One observable, one not - not equivalent *)
    false

(** Non-interference theorem statement (axiomatized).

    If:
    1. Two contexts ctx1 and ctx2 are low-equivalent at observation level obs
    2. The PC label is NOT observable (pc > obs) - meaning we're in a secret branch
    3. Expression e type-checks in both contexts

    Then:
    The results r1 and r2 are low-equivalent at obs.

    Proof sketch (informal):
    - Literals: Always produce the same value, trivially equivalent.
    - Variables: If variable is low, both contexts agree by low_equiv assumption.
                 If variable is high, result is high, so equivalent by definition.
    - Binary ops: Result label = join(l1, l2). If both args are low-equiv,
                  result is low-equiv. If either is high, result is high.
    - If-then-else: PC is raised to join(pc, cond_label).
                    - If cond is low: both executions take same branch, results equiv.
                    - If cond is high: PC' is high, so result label includes PC',
                      making result high (not observable).
    - Assignment: Flow check ensures we can't write high data to low variable.
                  So low variables remain consistent across contexts.

    This is the key soundness property that makes the type system secure. *)
val noninterference :
  ctx1:security_ctx ->
  ctx2:security_ctx ->
  pc:pc_label ->
  e:expr ->
  obs:sec_label ->
  Lemma (requires
           low_equiv obs ctx1 ctx2 = true /\
           sec_label_leq pc obs = false)
        (ensures
           (match sec_infer ctx1 pc e, sec_infer ctx2 pc e with
            | STyOk st1 ctx1' _, STyOk st2 ctx2' _ ->
                sec_type_low_equiv obs st1 st2 = true /\
                low_equiv obs ctx1' ctx2' = true
            | STyError _, STyError _ -> true
            | _, _ -> true))

(** The proof is complex and requires induction on the expression structure.
    For now, we axiomatize it. A full mechanized proof would require:
    1. Operational semantics for expressions
    2. Denotational model relating types to values
    3. Logical relations argument for compositionality *)
let noninterference ctx1 ctx2 pc e obs = admit ()

(** Corollary: If PC is low (observable), and contexts are low-equiv,
    then observable results are identical.
    This handles the "normal" case where we're not in a secret branch. *)
val noninterference_low_pc :
  ctx1:security_ctx ->
  ctx2:security_ctx ->
  pc:pc_label ->
  e:expr ->
  obs:sec_label ->
  Lemma (requires
           low_equiv obs ctx1 ctx2 = true /\
           sec_label_leq pc obs = true)
        (ensures
           (match sec_infer ctx1 pc e, sec_infer ctx2 pc e with
            | STyOk st1 ctx1' _, STyOk st2 ctx2' _ ->
                (* With low PC, observable results must be equal *)
                (is_observable st1.label obs ==>
                   sec_type_low_equiv obs st1 st2 = true) /\
                low_equiv obs ctx1' ctx2' = true
            | STyError _, STyError _ -> true
            | _, _ -> true))

let noninterference_low_pc ctx1 ctx2 pc e obs = admit ()

(** ============================================================================
    PC LABEL PROPAGATION INVARIANTS
    ============================================================================

    The following invariants must hold for the type system to be sound:

    1. RULE-IF: For if e1 then e2 else e3:
       result_label >= pc' where pc' = join(pc, label(e1))

    2. RULE-MATCH: For match e with arms:
       result_label >= pc' where pc' = join(pc, label(e))

    3. RULE-LET: For let x = e1 in e2:
       label(x) >= join(pc, label(e1))

    4. RULE-TUPLE: For (e1, ..., en):
       result_label >= join(pc, label(e1), ..., label(en))

    5. RULE-ASSIGN: For x := e:
       Requires: join(pc, label(e)) <= label(x)

    These invariants ensure that:
    - Implicit flows through control flow are captured
    - No high data can flow to low variables
    - The security lattice is respected throughout execution
    ============================================================================ *)

(** Verify that a typing result respects PC propagation invariant *)
let pc_invariant_holds (pc: pc_label) (st: sec_type) : bool =
  sec_label_leq pc st.label

(** ============================================================================
    SUMMARY
    ============================================================================

    This module provides security type checking:

    1. Security Context (security_ctx):
       - Tracks variables with security labels and modes
       - Supports linear type consumption
       - Supports context merging after branches (merge_security_ctx)

    2. Security Type Inference (sec_infer):
       - Infers security types for expressions
       - Tracks PC label for implicit flow prevention
       - CRITICAL: Includes PC in result labels for if/match/tuple
       - Checks flow constraints on assignments

    3. Effect-Based Taint Checking:
       - Detects taint violations in effect sequences
       - Integrates with TaintEffects module

    4. Annotation Checking:
       - Verifies source/sink/sanitizer annotations
       - Checks function role constraints

    5. Non-Interference Theorem:
       - Formalizes the fundamental security property
       - low_equiv defines when contexts are indistinguishable
       - noninterference states that high data cannot affect low observations

    Integration with Brrr-Machine:
    - Use security_check for expression-level analysis
    - Use security_check_function for function-level analysis
    - Collect violations for SARIF output
    ============================================================================ *)
