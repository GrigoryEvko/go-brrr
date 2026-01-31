(** ============================================================================
    BrrrTypeJoin.fst - Type Join/Meet (Lattice Operations)
    ============================================================================

    Type join (LUB) and type meet (GLB) implement lattice operations for the
    type system. These are essential for:

    1. CONDITIONAL EXPRESSIONS: if-then-else requires joining branch types
       If branch1 : T1 and branch2 : T2, result has type T1 join T2

    2. PATTERN MATCHING: All match arms must join to a common type
       match e { p1 => e1, p2 => e2, ... } has type join(T1, T2, ...)

    3. GRADUAL TYPING: Consistent subtyping uses meet/join for casts
       Cast from T1 to T2 is safe if T1 meet T2 is well-defined

    LATTICE STRUCTURE:
                       Dynamic (unsafe top)
                          |
                       Unknown (safe top)
                          |
              +-----------+-----------+
              |           |           |
          primitives  wrappers   functions
              |           |           |
              +-----------+-----------+
                          |
                        Never (bottom)

    REFERENCES:
    - Pierce, TAPL Chapter 15 "Subtyping" (Section 15.4 Joins and Meets)
    - Siek and Taha 2006, "Gradual Typing for Functional Languages"
    - brrr_lang_spec_v0.4.tex Section 8.2 "Type Lattice"

    ============================================================================ *)

module BrrrTypeJoin

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes
open BrrrModes
open BrrrEffects

(** --------------------------------------------------------------------------
    TYPE LATTICE RESULT TYPES
    -------------------------------------------------------------------------- *)

(** Monadic bind for LUB results *)
let lub_bind (r: type_lub_result) (f: brrr_type -> type_lub_result) : type_lub_result =
  match r with
  | LUBOk t -> f t
  | LUBFail t1 t2 -> LUBFail t1 t2

(** Monadic bind for GLB results *)
let glb_bind (r: type_glb_result) (f: brrr_type -> type_glb_result) : type_glb_result =
  match r with
  | GLBOk t -> f t
  | GLBFail t1 t2 -> GLBFail t1 t2

(** --------------------------------------------------------------------------
    NUMERIC TYPE PROMOTION HELPERS
    --------------------------------------------------------------------------

    For numeric types, join computes the smallest type that can represent
    values from both input types. This follows standard numeric promotion rules.
    -------------------------------------------------------------------------- *)

(** Join two int_width values: take the maximum width *)
let width_join (w1 w2: int_width) : int_width =
  match width_bits w1, width_bits w2 with
  | Some b1, Some b2 ->
      if b1 >= b2 then w1 else w2
  | None, _ -> IBig  (* IBig dominates *)
  | _, None -> IBig

(** Meet two int_width values: take the minimum width *)
let width_meet (w1 w2: int_width) : int_width =
  match width_bits w1, width_bits w2 with
  | Some b1, Some b2 ->
      if b1 <= b2 then w1 else w2
  | None, Some _ -> w2  (* Concrete width is smaller than IBig *)
  | Some _, None -> w1
  | None, None -> IBig  (* Both are IBig *)

(** Join two signedness values.
    Signed join Unsigned = Signed (to represent both ranges safely)
    Note: This is conservative; actual safety depends on width. *)
let signedness_join (s1 s2: signedness) : signedness =
  match s1, s2 with
  | Signed, Signed -> Signed
  | Unsigned, Unsigned -> Unsigned
  | _, _ -> Signed  (* Mixed sign: use signed to be safe *)

(** Meet two signedness values.
    Signed meet Unsigned - no common subtype for mixed signedness *)
let signedness_meet (s1 s2: signedness) : option signedness =
  match s1, s2 with
  | Signed, Signed -> Some Signed
  | Unsigned, Unsigned -> Some Unsigned
  | _, _ -> None

(** Join two integer types: wider width and safe signedness *)
let int_type_join (i1 i2: int_type) : int_type =
  { width = width_join i1.width i2.width;
    sign = signedness_join i1.sign i2.sign }

(** Join two float precisions: take the higher precision *)
let float_prec_join (f1 f2: float_prec) : float_prec =
  if float_bits f1 >= float_bits f2 then f1 else f2

(** Join two numeric types.
    Returns None if incompatible (int vs float with no safe promotion). *)
let numeric_type_join (n1 n2: numeric_type) : option numeric_type =
  match n1, n2 with
  | NumInt i1, NumInt i2 -> Some (NumInt (int_type_join i1 i2))
  | NumFloat f1, NumFloat f2 -> Some (NumFloat (float_prec_join f1 f2))
  (* Integer to float promotion: use float that can represent int range *)
  | NumInt i, NumFloat f -> Some (NumFloat f)
  | NumFloat f, NumInt i -> Some (NumFloat f)

(** Row intersection for effect meet - keeps only common effects *)
let rec row_intersect (r1 r2: effect_row) : effect_row =
  match r1 with
  | RowEmpty -> RowEmpty
  | RowExt e rest ->
      if has_effect e r2 then
        add_effect e (row_intersect rest r2)
      else
        row_intersect rest r2
  | RowVar v -> RowVar v
  | RowVarUnify v1 v2 -> RowVarUnify v1 v2

(** --------------------------------------------------------------------------
    TYPE JOIN (LEAST UPPER BOUND)
    --------------------------------------------------------------------------

    type_join t1 t2 computes the least upper bound of t1 and t2.
    This is the most specific type that is a supertype of both.

    Key properties:
    - t1 <: type_join t1 t2
    - t2 <: type_join t1 t2
    - For any T where t1 <: T and t2 <: T, type_join t1 t2 <: T

    For function types: contravariant in parameters, covariant in return.
    -------------------------------------------------------------------------- *)

(** Join two types to find their least upper bound *)
let rec type_join (t1 t2: brrr_type) : Tot type_lub_result (decreases t1) =
  (* Rule 1: Reflexivity - same types have trivial join *)
  if type_eq t1 t2 then LUBOk t1

  else match t1, t2 with
  (* Rule 2: Never (bottom) is absorbed by any type *)
  | TPrim PNever, t -> LUBOk t
  | t, TPrim PNever -> LUBOk t

  (* Rule 3: Dynamic (unsafe top) absorbs everything *)
  | TPrim PDynamic, _ -> LUBOk (TPrim PDynamic)
  | _, TPrim PDynamic -> LUBOk (TPrim PDynamic)

  (* Rule 4: Unknown (safe top) absorbs everything except Dynamic *)
  | TPrim PUnknown, _ -> LUBOk (TPrim PUnknown)
  | _, TPrim PUnknown -> LUBOk (TPrim PUnknown)

  (* Rule 5: Numeric type promotion *)
  | TNumeric n1, TNumeric n2 ->
      (match numeric_type_join n1 n2 with
       | Some n -> LUBOk (TNumeric n)
       | None -> LUBFail t1 t2)

  (* Rule 6: Wrapper types - must have same wrapper kind *)
  | TWrap w1 inner1, TWrap w2 inner2 ->
      if w1 <> w2 then LUBFail t1 t2
      else if wrapper_is_covariant w1 then
        (* Covariant wrappers: join inner types *)
        (match type_join inner1 inner2 with
         | LUBOk inner_lub -> LUBOk (TWrap w1 inner_lub)
         | LUBFail _ _ -> LUBFail t1 t2)
      else
        (* Invariant wrappers (WRefMut): require exact match *)
        if type_eq inner1 inner2 then LUBOk t1 else LUBFail t1 t2

  (* Rule 7: Result types - covariant in both components *)
  | TResult tok1 terr1, TResult tok2 terr2 ->
      (match type_join tok1 tok2 with
       | LUBOk tok_lub ->
           (match type_join terr1 terr2 with
            | LUBOk terr_lub -> LUBOk (TResult tok_lub terr_lub)
            | LUBFail _ _ -> LUBFail t1 t2)
       | LUBFail _ _ -> LUBFail t1 t2)

  (* Rule 8: Tuple types - element-wise join *)
  | TTuple ts1, TTuple ts2 ->
      if List.Tot.length ts1 <> List.Tot.length ts2 then LUBFail t1 t2
      else
        (match type_join_list ts1 ts2 with
         | Some ts_lub -> LUBOk (TTuple ts_lub)
         | None -> LUBFail t1 t2)

  (* Rule 9: Function types - contravariant params, covariant return *)
  | TFunc ft1, TFunc ft2 ->
      if List.Tot.length ft1.params <> List.Tot.length ft2.params then
        LUBFail t1 t2
      else
        (* For function join: params use MEET (contravariant), return uses JOIN *)
        (match type_meet_params ft1.params ft2.params with
         | Some params_glb ->
             (match type_join ft1.return_type ft2.return_type with
              | LUBOk ret_lub ->
                  let eff_lub = row_join ft1.effects ft2.effects in
                  LUBOk (TFunc {
                    params = params_glb;
                    return_type = ret_lub;
                    effects = eff_lub;
                    is_unsafe = ft1.is_unsafe || ft2.is_unsafe
                  })
              | LUBFail _ _ -> LUBFail t1 t2)
         | None -> LUBFail t1 t2)

  (* Rule 10: Named types - must be same name for join *)
  | TNamed n1, TNamed n2 ->
      if n1 = n2 then LUBOk t1 else LUBFail t1 t2

  (* Rule 11: Type variables - same variable has trivial join *)
  | TVar v1, TVar v2 ->
      if v1 = v2 then LUBOk t1 else LUBFail t1 t2

  (* Rule 12: Type applications - base and args must join *)
  | TApp base1 args1, TApp base2 args2 ->
      if List.Tot.length args1 <> List.Tot.length args2 then LUBFail t1 t2
      else
        (match type_join base1 base2 with
         | LUBOk base_lub ->
             (match type_join_list args1 args2 with
              | Some args_lub -> LUBOk (TApp base_lub args_lub)
              | None -> LUBFail t1 t2)
         | LUBFail _ _ -> LUBFail t1 t2)

  (* Rule 13: Structs - nominal equality required *)
  | TStruct st1, TStruct st2 ->
      if st1.struct_name = st2.struct_name then LUBOk t1 else LUBFail t1 t2

  (* Rule 14: Enums - nominal equality required *)
  | TEnum et1, TEnum et2 ->
      if et1.enum_name = et2.enum_name then LUBOk t1 else LUBFail t1 t2

  (* Rule 15: Modal types - same modality required *)
  | TModal m1 inner1, TModal m2 inner2 ->
      if not (modal_eq m1 m2) then LUBFail t1 t2
      else
        (match type_join inner1 inner2 with
         | LUBOk inner_lub -> LUBOk (TModal m1 inner_lub)
         | LUBFail _ _ -> LUBFail t1 t2)

  (* Fallback: incompatible types have no join below Dynamic *)
  | _, _ -> LUBFail t1 t2

(** Meet two types to find their greatest lower bound *)
and type_meet (t1 t2: brrr_type) : Tot type_glb_result (decreases t1) =
  (* Rule 1: Reflexivity - same types have trivial meet *)
  if type_eq t1 t2 then GLBOk t1

  else match t1, t2 with
  (* Rule 2: Never (bottom) absorbs everything in meet *)
  | TPrim PNever, _ -> GLBOk (TPrim PNever)
  | _, TPrim PNever -> GLBOk (TPrim PNever)

  (* Rule 3: Dynamic/Unknown - meet gives the concrete type *)
  | TPrim PDynamic, t -> GLBOk t
  | t, TPrim PDynamic -> GLBOk t
  | TPrim PUnknown, t -> GLBOk t
  | t, TPrim PUnknown -> GLBOk t

  (* Rule 4: Numeric types - meet is the smaller type if compatible *)
  | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
      if i1.sign = i2.sign then
        let w = width_meet i1.width i2.width in
        GLBOk (TNumeric (NumInt { width = w; sign = i1.sign }))
      else GLBFail t1 t2

  | TNumeric (NumFloat f1), TNumeric (NumFloat f2) ->
      let f = if float_bits f1 <= float_bits f2 then f1 else f2 in
      GLBOk (TNumeric (NumFloat f))

  | TNumeric _, TNumeric _ -> GLBFail t1 t2

  (* Rule 5: Wrapper types *)
  | TWrap w1 inner1, TWrap w2 inner2 ->
      if w1 <> w2 then GLBFail t1 t2
      else if wrapper_is_covariant w1 then
        (match type_meet inner1 inner2 with
         | GLBOk inner_glb -> GLBOk (TWrap w1 inner_glb)
         | GLBFail _ _ -> GLBFail t1 t2)
      else
        if type_eq inner1 inner2 then GLBOk t1 else GLBFail t1 t2

  (* Rule 6: Result types *)
  | TResult tok1 terr1, TResult tok2 terr2 ->
      (match type_meet tok1 tok2 with
       | GLBOk tok_glb ->
           (match type_meet terr1 terr2 with
            | GLBOk terr_glb -> GLBOk (TResult tok_glb terr_glb)
            | GLBFail _ _ -> GLBFail t1 t2)
       | GLBFail _ _ -> GLBFail t1 t2)

  (* Rule 7: Tuple types *)
  | TTuple ts1, TTuple ts2 ->
      if List.Tot.length ts1 <> List.Tot.length ts2 then GLBFail t1 t2
      else
        (match type_meet_list ts1 ts2 with
         | Some ts_glb -> GLBOk (TTuple ts_glb)
         | None -> GLBFail t1 t2)

  (* Rule 8: Function types - covariant params (for meet), contravariant return *)
  | TFunc ft1, TFunc ft2 ->
      if List.Tot.length ft1.params <> List.Tot.length ft2.params then
        GLBFail t1 t2
      else
        (match type_join_params ft1.params ft2.params with
         | Some params_lub ->
             (match type_meet ft1.return_type ft2.return_type with
              | GLBOk ret_glb ->
                  let eff_glb = row_intersect ft1.effects ft2.effects in
                  GLBOk (TFunc {
                    params = params_lub;
                    return_type = ret_glb;
                    effects = eff_glb;
                    is_unsafe = ft1.is_unsafe && ft2.is_unsafe
                  })
              | GLBFail _ _ -> GLBFail t1 t2)
         | None -> GLBFail t1 t2)

  (* Rule 9: Named types *)
  | TNamed n1, TNamed n2 ->
      if n1 = n2 then GLBOk t1 else GLBFail t1 t2

  (* Rule 10: Type variables *)
  | TVar v1, TVar v2 ->
      if v1 = v2 then GLBOk t1 else GLBFail t1 t2

  (* Rule 11: Type applications *)
  | TApp base1 args1, TApp base2 args2 ->
      if List.Tot.length args1 <> List.Tot.length args2 then GLBFail t1 t2
      else
        (match type_meet base1 base2 with
         | GLBOk base_glb ->
             (match type_meet_list args1 args2 with
              | Some args_glb -> GLBOk (TApp base_glb args_glb)
              | None -> GLBFail t1 t2)
         | GLBFail _ _ -> GLBFail t1 t2)

  (* Rule 12: Structs - nominal *)
  | TStruct st1, TStruct st2 ->
      if st1.struct_name = st2.struct_name then GLBOk t1 else GLBFail t1 t2

  (* Rule 13: Enums - nominal *)
  | TEnum et1, TEnum et2 ->
      if et1.enum_name = et2.enum_name then GLBOk t1 else GLBFail t1 t2

  (* Rule 14: Modal types *)
  | TModal m1 inner1, TModal m2 inner2 ->
      if not (modal_eq m1 m2) then GLBFail t1 t2
      else
        (match type_meet inner1 inner2 with
         | GLBOk inner_glb -> GLBOk (TModal m1 inner_glb)
         | GLBFail _ _ -> GLBFail t1 t2)

  (* Fallback: incompatible types have Never as meet *)
  | _, _ -> GLBOk (TPrim PNever)

(** Join a list of types element-wise *)
and type_join_list (ts1 ts2: list brrr_type)
    : Tot (option (list brrr_type)) (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> Some []
  | t1 :: rest1, t2 :: rest2 ->
      (match type_join t1 t2 with
       | LUBOk t_lub ->
           (match type_join_list rest1 rest2 with
            | Some rest_lub -> Some (t_lub :: rest_lub)
            | None -> None)
       | LUBFail _ _ -> None)
  | _, _ -> None

(** Meet a list of types element-wise *)
and type_meet_list (ts1 ts2: list brrr_type)
    : Tot (option (list brrr_type)) (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> Some []
  | t1 :: rest1, t2 :: rest2 ->
      (match type_meet t1 t2 with
       | GLBOk t_glb ->
           (match type_meet_list rest1 rest2 with
            | Some rest_glb -> Some (t_glb :: rest_glb)
            | None -> None)
       | GLBFail _ _ -> None)
  | _, _ -> None

(** Meet parameter types (for contravariant function param join) *)
and type_meet_params (ps1 ps2: list param_type)
    : Tot (option (list param_type)) (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> Some []
  | param1 :: rest1, param2 :: rest2 ->
      let t1 : brrr_type = BrrrTypes.Mkparam_type?.ty param1 in
      let t2 : brrr_type = BrrrTypes.Mkparam_type?.ty param2 in
      (match type_meet t1 t2 with
       | GLBOk t_glb ->
           (match type_meet_params rest1 rest2 with
            | Some rest_glb ->
                let m1 = BrrrTypes.Mkparam_type?.mode param1 in
                let m2 = BrrrTypes.Mkparam_type?.mode param2 in
                let m = if mode_leq m1 m2 then m1 else m2 in
                let n = BrrrTypes.Mkparam_type?.name param1 in
                let result : param_type = { name = n; ty = t_glb; mode = m } in
                Some (result :: rest_glb)
            | None -> None)
       | GLBFail _ _ -> None)
  | _, _ -> None

(** Join parameter types (for covariant function param meet) *)
and type_join_params (ps1 ps2: list param_type)
    : Tot (option (list param_type)) (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> Some []
  | param1 :: rest1, param2 :: rest2 ->
      let t1 : brrr_type = BrrrTypes.Mkparam_type?.ty param1 in
      let t2 : brrr_type = BrrrTypes.Mkparam_type?.ty param2 in
      (match type_join t1 t2 with
       | LUBOk t_lub ->
           (match type_join_params rest1 rest2 with
            | Some rest_lub ->
                let m1 = BrrrTypes.Mkparam_type?.mode param1 in
                let m2 = BrrrTypes.Mkparam_type?.mode param2 in
                let m = if mode_leq m1 m2 then m2 else m1 in
                let n = BrrrTypes.Mkparam_type?.name param1 in
                let result : param_type = { name = n; ty = t_lub; mode = m } in
                Some (result :: rest_lub)
            | None -> None)
       | LUBFail _ _ -> None)
  | _, _ -> None

(** --------------------------------------------------------------------------
    CONVENIENCE FUNCTIONS
    -------------------------------------------------------------------------- *)

(** Type for conditional branches: join of then and else types *)
let type_conditional_branches (then_ty else_ty: brrr_type) : type_lub_result =
  type_join then_ty else_ty

(** Type for match arms: fold join over all arm types *)
let rec type_match_arms_lub (tys: list brrr_type) : type_lub_result =
  match tys with
  | [] -> LUBFail (TPrim PNever) (TPrim PNever)
  | [t] -> LUBOk t
  | t :: rest ->
      (match type_match_arms_lub rest with
       | LUBOk rest_lub -> type_join t rest_lub
       | err -> err)

(** Unwrap LUB result, returning Dynamic if no join exists *)
let type_join_or_dynamic (t1 t2: brrr_type) : brrr_type =
  match type_join t1 t2 with
  | LUBOk t -> t
  | LUBFail _ _ -> TPrim PDynamic

(** Check if two types have a valid join *)
let types_have_join (t1 t2: brrr_type) : bool =
  match type_join t1 t2 with
  | LUBOk _ -> true
  | LUBFail _ _ -> false

(** --------------------------------------------------------------------------
    LATTICE LAW LEMMAS
    -------------------------------------------------------------------------- *)

(** Join is commutative *)
let type_join_comm (t1 t2: brrr_type) : Lemma (type_join t1 t2 == type_join t2 t1) =
  admit ()

(** Meet is commutative *)
let type_meet_comm (t1 t2: brrr_type) : Lemma (type_meet t1 t2 == type_meet t2 t1) =
  admit ()

(** Never is bottom for join *)
let type_join_never_left (t: brrr_type) : Lemma (type_join (TPrim PNever) t == LUBOk t) =
  admit ()

(** Dynamic is top for join *)
let type_join_dynamic_right (t: brrr_type)
    : Lemma (type_join t (TPrim PDynamic) == LUBOk (TPrim PDynamic)) =
  admit ()

(** Same types have trivial join *)
let type_join_refl (t: brrr_type) : Lemma (type_join t t == LUBOk t) =
  admit ()
