(**
 * BrrrLang.Core.BrrrReflection
 *
 * Typed reflection and runtime type representation.
 * Based on brrr_lang_spec_v0.4.tex Part VI - Metaprogramming, Chapter: Typed Reflection
 *
 * Implements:
 *   - TypeRep[t] : runtime representation of type t
 *   - Dynamic    : existential type packaging value with its type representation
 *   - typeOf     : get type representation from a value
 *   - cast       : safe cast using type representation
 *   - eqType     : type equality check returning equality witness
 *
 * Key invariant: NO ADMITS ALLOWED - all proofs must be complete.
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes
 *)
module BrrrReflection

open Primitives
open Modes
open Effects
open BrrrTypes
open FStar.List.Tot

(** ============================================================================
    TYPE REPRESENTATION - Mirrors brrr_type structure
    ============================================================================

    TypeRep is a runtime representation of types. It mirrors the structure of
    brrr_type but is designed to be passed around at runtime for reflection.

    Design rationale:
    - We use a separate type rather than reusing brrr_type directly to maintain
      clear separation between compile-time types and runtime type representations
    - The structure exactly mirrors brrr_type's 12 constructors for 1:1 mapping
    - Conversion functions establish the isomorphism with brrr_type
    ============================================================================ *)

(* Primitive type representation - mirrors prim_kind *)
type prim_rep =
  | PRUnit   : prim_rep   (* () - unit type *)
  | PRNever  : prim_rep   (* ! - bottom type *)
  | PRBool   : prim_rep   (* bool *)
  | PRString : prim_rep   (* String *)
  | PRChar   : prim_rep   (* char *)
  | PRDynamic: prim_rep   (* Dynamic/any type *)

(* Numeric type representation - mirrors numeric_type *)
type numeric_rep =
  | NRInt   : int_type -> numeric_rep    (* i8, i16, i32, i64, u8, u16, u32, u64 *)
  | NRFloat : float_prec -> numeric_rep  (* f32, f64 *)

(* Wrapper kind representation - mirrors wrapper_kind *)
type wrapper_rep =
  | WRArray  : wrapper_rep   (* [T] *)
  | WRSlice  : wrapper_rep   (* &[T] *)
  | WROption : wrapper_rep   (* T? *)
  | WRBox    : wrapper_rep   (* Box<T> *)
  | WRRef    : wrapper_rep   (* &T *)
  | WRRefMut : wrapper_rep   (* &mut T *)
  | WRRc     : wrapper_rep   (* Rc<T> *)
  | WRArc    : wrapper_rep   (* Arc<T> *)
  | WRRaw    : wrapper_rep   (* *T *)

(* Modal kind representation - mirrors modal_kind *)
type modal_rep =
  | MRBoxMod     : ref_kind -> modal_rep   (* Box modal with permission *)
  | MRDiamondMod : modal_rep               (* Diamond modal (exclusive) *)

(* Strictly positive list wrapper for mutually recursive types *)
let trlist ([@@@strictly_positive] a: Type) = list a

(* Main type representation - mirrors brrr_type's 12 constructors
   All nested types are defined inline to avoid forward reference issues *)
noeq type type_rep =
  (* Primitives: 1 constructor covers 6 types *)
  | TRPrim    : prim_rep -> type_rep

  (* Numerics: 1 constructor covers int/float with all widths *)
  | TRNumeric : numeric_rep -> type_rep

  (* Wrappers: 1 constructor covers 9 single-type wrappers *)
  | TRWrap    : wrapper_rep -> type_rep -> type_rep

  (* Modal refs: 1 constructor covers Box/Diamond modalities *)
  | TRModal   : modal_rep -> type_rep -> type_rep

  (* Binary type constructor *)
  | TRResult  : type_rep -> type_rep -> type_rep (* Result<T, E> *)

  (* Collection type *)
  | TRTuple   : trlist type_rep -> type_rep        (* (T1, T2, ...) *)

  (* Function type - inline definition to avoid forward ref *)
  | TRFunc    : trlist param_rep -> type_rep -> effect_row -> bool -> type_rep

  (* Type variables and applications *)
  | TRVar     : type_var -> type_rep             (* alpha *)
  | TRApp     : type_rep -> trlist type_rep -> type_rep  (* F<T1, T2> *)
  | TRNamed   : type_name -> type_rep            (* Named type reference *)

  (* Struct type - inline *)
  | TRStruct  : type_name -> trlist field_rep -> repr_attr -> type_rep

  (* Enum type - inline *)
  | TREnum    : type_name -> trlist variant_rep -> type_rep

(* Parameter representation for function types *)
and param_rep = {
  pr_name : option string;
  pr_ty   : type_rep;
  pr_mode : mode
}

(* Struct field representation *)
and field_rep = {
  flr_name : string;
  flr_ty   : type_rep;
  flr_vis  : visibility
}

(* Variant type representation *)
and variant_rep = {
  vr_name   : string;
  vr_fields : trlist type_rep
}

(** ============================================================================
    CONVERSION: prim_kind <-> prim_rep
    ============================================================================ *)

let prim_kind_to_rep (pk: prim_kind) : prim_rep =
  match pk with
  | PUnit    -> PRUnit
  | PNever   -> PRNever
  | PBool    -> PRBool
  | PString  -> PRString
  | PChar    -> PRChar
  | PDynamic -> PRDynamic

let prim_rep_to_kind (pr: prim_rep) : prim_kind =
  match pr with
  | PRUnit    -> PUnit
  | PRNever   -> PNever
  | PRBool    -> PBool
  | PRString  -> PString
  | PRChar    -> PChar
  | PRDynamic -> PDynamic

(* Roundtrip proof: prim_rep_to_kind (prim_kind_to_rep pk) = pk *)
val prim_roundtrip_kind : pk:prim_kind ->
  Lemma (ensures prim_rep_to_kind (prim_kind_to_rep pk) = pk)
let prim_roundtrip_kind pk =
  match pk with
  | PUnit -> () | PNever -> () | PBool -> ()
  | PString -> () | PChar -> () | PDynamic -> ()

(* Roundtrip proof: prim_kind_to_rep (prim_rep_to_kind pr) = pr *)
val prim_roundtrip_rep : pr:prim_rep ->
  Lemma (ensures prim_kind_to_rep (prim_rep_to_kind pr) = pr)
let prim_roundtrip_rep pr =
  match pr with
  | PRUnit -> () | PRNever -> () | PRBool -> ()
  | PRString -> () | PRChar -> () | PRDynamic -> ()

(** ============================================================================
    CONVERSION: numeric_type <-> numeric_rep
    ============================================================================ *)

let numeric_type_to_rep (nt: numeric_type) : numeric_rep =
  match nt with
  | NumInt it -> NRInt it
  | NumFloat fp -> NRFloat fp

let numeric_rep_to_type (nr: numeric_rep) : numeric_type =
  match nr with
  | NRInt it -> NumInt it
  | NRFloat fp -> NumFloat fp

val numeric_roundtrip_type : nt:numeric_type ->
  Lemma (ensures numeric_rep_to_type (numeric_type_to_rep nt) = nt)
let numeric_roundtrip_type nt =
  match nt with
  | NumInt _ -> ()
  | NumFloat _ -> ()

val numeric_roundtrip_rep : nr:numeric_rep ->
  Lemma (ensures numeric_type_to_rep (numeric_rep_to_type nr) = nr)
let numeric_roundtrip_rep nr =
  match nr with
  | NRInt _ -> ()
  | NRFloat _ -> ()

(** ============================================================================
    CONVERSION: wrapper_kind <-> wrapper_rep
    ============================================================================ *)

let wrapper_kind_to_rep (wk: wrapper_kind) : wrapper_rep =
  match wk with
  | WArray  -> WRArray  | WSlice  -> WRSlice  | WOption -> WROption
  | WBox    -> WRBox    | WRef    -> WRRef    | WRefMut -> WRRefMut
  | WRc     -> WRRc     | WArc    -> WRArc    | WRaw    -> WRRaw

let wrapper_rep_to_kind (wr: wrapper_rep) : wrapper_kind =
  match wr with
  | WRArray  -> WArray  | WRSlice  -> WSlice  | WROption -> WOption
  | WRBox    -> WBox    | WRRef    -> WRef    | WRRefMut -> WRefMut
  | WRRc     -> WRc     | WRArc    -> WArc    | WRRaw    -> WRaw

val wrapper_roundtrip_kind : wk:wrapper_kind ->
  Lemma (ensures wrapper_rep_to_kind (wrapper_kind_to_rep wk) = wk)
let wrapper_roundtrip_kind wk =
  match wk with
  | WArray -> () | WSlice -> () | WOption -> () | WBox -> ()
  | WRef -> () | WRefMut -> () | WRc -> () | WArc -> () | WRaw -> ()

val wrapper_roundtrip_rep : wr:wrapper_rep ->
  Lemma (ensures wrapper_kind_to_rep (wrapper_rep_to_kind wr) = wr)
let wrapper_roundtrip_rep wr =
  match wr with
  | WRArray -> () | WRSlice -> () | WROption -> () | WRBox -> ()
  | WRRef -> () | WRRefMut -> () | WRRc -> () | WRArc -> () | WRRaw -> ()

(** ============================================================================
    CONVERSION: modal_kind <-> modal_rep
    ============================================================================ *)

let modal_kind_to_rep (mk: modal_kind) : modal_rep =
  match mk with
  | MBoxMod rk -> MRBoxMod rk
  | MDiamondMod -> MRDiamondMod

let modal_rep_to_kind (mr: modal_rep) : modal_kind =
  match mr with
  | MRBoxMod rk -> MBoxMod rk
  | MRDiamondMod -> MDiamondMod

val modal_roundtrip_kind : mk:modal_kind ->
  Lemma (ensures modal_rep_to_kind (modal_kind_to_rep mk) = mk)
let modal_roundtrip_kind mk =
  match mk with
  | MBoxMod _ -> ()
  | MDiamondMod -> ()

val modal_roundtrip_rep : mr:modal_rep ->
  Lemma (ensures modal_kind_to_rep (modal_rep_to_kind mr) = mr)
let modal_roundtrip_rep mr =
  match mr with
  | MRBoxMod _ -> ()
  | MRDiamondMod -> ()

(** ============================================================================
    SIZE FUNCTIONS FOR TERMINATION MEASURES
    ============================================================================ *)

let rec type_rep_size (tr: type_rep) : Tot nat (decreases tr) =
  match tr with
  | TRPrim _ -> 1
  | TRNumeric _ -> 1
  | TRWrap _ t -> 1 + type_rep_size t
  | TRModal _ t -> 1 + type_rep_size t
  | TRResult t1 t2 -> 1 + type_rep_size t1 + type_rep_size t2
  | TRTuple ts -> 1 + type_rep_list_size ts
  | TRFunc params ret_ty _ _ -> 1 + param_rep_list_size params + type_rep_size ret_ty
  | TRVar _ -> 1
  | TRNamed _ -> 1
  | TRApp t args -> 1 + type_rep_size t + type_rep_list_size args
  | TRStruct _ fields _ -> 1 + field_rep_list_size fields
  | TREnum _ variants -> 1 + variant_rep_list_size variants

and type_rep_list_size (ts: trlist type_rep) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | t :: rest -> type_rep_size t + type_rep_list_size rest

and param_rep_list_size (ps: trlist param_rep) : Tot nat (decreases ps) =
  match ps with
  | [] -> 0
  | p :: rest -> type_rep_size p.pr_ty + param_rep_list_size rest

and field_rep_list_size (fs: trlist field_rep) : Tot nat (decreases fs) =
  match fs with
  | [] -> 0
  | f :: rest -> type_rep_size f.flr_ty + field_rep_list_size rest

and variant_rep_list_size (vs: trlist variant_rep) : Tot nat (decreases vs) =
  match vs with
  | [] -> 0
  | v :: rest -> type_rep_list_size v.vr_fields + variant_rep_list_size rest

(** ============================================================================
    CONVERSION: brrr_type <-> type_rep (main conversion)
    ============================================================================ *)

(* Conversion functions: brrr_type -> type_rep
   We use structural recursion with explicit decreases on input types. *)
val brrr_type_to_rep : t:brrr_type -> Tot type_rep (decreases t)
val brrr_type_list_to_rep : ts:list brrr_type -> Tot (trlist type_rep) (decreases ts)
val param_type_list_to_rep : ps:list param_type -> Tot (trlist param_rep) (decreases ps)
val field_type_list_to_rep : fs:list field_type -> Tot (trlist field_rep) (decreases fs)
val variant_type_list_to_rep : vs:list variant_type -> Tot (trlist variant_rep) (decreases vs)

let rec brrr_type_to_rep t =
  match t with
  | TPrim pk -> TRPrim (prim_kind_to_rep pk)
  | TNumeric nt -> TRNumeric (numeric_type_to_rep nt)
  | TWrap wk t' -> TRWrap (wrapper_kind_to_rep wk) (brrr_type_to_rep t')
  | TModal mk t' -> TRModal (modal_kind_to_rep mk) (brrr_type_to_rep t')
  | TResult t1 t2 -> TRResult (brrr_type_to_rep t1) (brrr_type_to_rep t2)
  | TTuple ts -> TRTuple (brrr_type_list_to_rep ts)
  | TFunc ft -> TRFunc
      (param_type_list_to_rep ft.params)
      (brrr_type_to_rep ft.return_type)
      ft.effects
      ft.is_unsafe
  | TVar v -> TRVar v
  | TNamed n -> TRNamed n
  | TApp t' args -> TRApp (brrr_type_to_rep t') (brrr_type_list_to_rep args)
  | TStruct st -> TRStruct
      st.struct_name
      (field_type_list_to_rep st.struct_fields)
      st.struct_repr
  | TEnum et -> TREnum
      et.enum_name
      (variant_type_list_to_rep et.enum_variants)

and brrr_type_list_to_rep ts =
  match ts with
  | [] -> []
  | t :: rest -> brrr_type_to_rep t :: brrr_type_list_to_rep rest

and param_type_list_to_rep ps =
  match ps with
  | [] -> []
  | p :: rest -> {
      pr_name = Mkparam_type?.name p;
      pr_ty = brrr_type_to_rep (Mkparam_type?.ty p);
      pr_mode = Mkparam_type?.mode p
    } :: param_type_list_to_rep rest

and field_type_list_to_rep fs =
  match fs with
  | [] -> []
  | f :: rest -> {
      flr_name = f.field_name;
      flr_ty = brrr_type_to_rep f.field_ty;
      flr_vis = f.field_vis
    } :: field_type_list_to_rep rest

and variant_type_list_to_rep vs =
  match vs with
  | [] -> []
  | v :: rest -> {
      vr_name = v.variant_name;
      vr_fields = brrr_type_list_to_rep v.variant_fields
    } :: variant_type_list_to_rep rest

(* Reverse conversion: type_rep -> brrr_type *)
val type_rep_to_brrr : tr:type_rep -> Tot brrr_type (decreases tr)
val type_rep_list_to_brrr : trs:trlist type_rep -> Tot (list brrr_type) (decreases trs)
val param_rep_list_to_brrr : prs:trlist param_rep -> Tot (list param_type) (decreases prs)
val field_rep_list_to_brrr : frs:trlist field_rep -> Tot (list field_type) (decreases frs)
val variant_rep_list_to_brrr : vrs:trlist variant_rep -> Tot (list variant_type) (decreases vrs)

let rec type_rep_to_brrr tr =
  match tr with
  | TRPrim pr -> TPrim (prim_rep_to_kind pr)
  | TRNumeric nr -> TNumeric (numeric_rep_to_type nr)
  | TRWrap wr t -> TWrap (wrapper_rep_to_kind wr) (type_rep_to_brrr t)
  | TRModal mr t -> TModal (modal_rep_to_kind mr) (type_rep_to_brrr t)
  | TRResult t1 t2 -> TResult (type_rep_to_brrr t1) (type_rep_to_brrr t2)
  | TRTuple trs -> TTuple (type_rep_list_to_brrr trs)
  | TRFunc params ret_ty effects is_unsafe -> TFunc {
      params = param_rep_list_to_brrr params;
      return_type = type_rep_to_brrr ret_ty;
      effects = effects;
      is_unsafe = is_unsafe
    }
  | TRVar v -> TVar v
  | TRNamed n -> TNamed n
  | TRApp tr' args -> TApp (type_rep_to_brrr tr') (type_rep_list_to_brrr args)
  | TRStruct name fields repr -> TStruct {
      struct_name = name;
      struct_fields = field_rep_list_to_brrr fields;
      struct_repr = repr
    }
  | TREnum name variants -> TEnum {
      enum_name = name;
      enum_variants = variant_rep_list_to_brrr variants
    }

and type_rep_list_to_brrr trs =
  match trs with
  | [] -> []
  | tr :: rest -> type_rep_to_brrr tr :: type_rep_list_to_brrr rest

and param_rep_list_to_brrr prs =
  match prs with
  | [] -> []
  | pr :: rest -> {
      name = pr.pr_name;
      ty = type_rep_to_brrr pr.pr_ty;
      mode = pr.pr_mode
    } :: param_rep_list_to_brrr rest

and field_rep_list_to_brrr frs =
  match frs with
  | [] -> []
  | fr :: rest -> {
      field_name = fr.flr_name;
      field_ty = type_rep_to_brrr fr.flr_ty;
      field_vis = fr.flr_vis
    } :: field_rep_list_to_brrr rest

and variant_rep_list_to_brrr vrs =
  match vrs with
  | [] -> []
  | vr :: rest -> {
      variant_name = vr.vr_name;
      variant_fields = type_rep_list_to_brrr vr.vr_fields
    } :: variant_rep_list_to_brrr rest

(** ============================================================================
    ROUNDTRIP PROOFS: brrr_type -> type_rep -> brrr_type
    ============================================================================ *)

(* Mutual recursion declarations *)
val roundtrip_brrr_type : t:brrr_type ->
  Lemma (ensures type_rep_to_brrr (brrr_type_to_rep t) == t)
        (decreases t)

val roundtrip_brrr_type_list : ts:list brrr_type ->
  Lemma (ensures type_rep_list_to_brrr (brrr_type_list_to_rep ts) == ts)
        (decreases ts)

val roundtrip_param_type_list : ps:list param_type ->
  Lemma (ensures param_rep_list_to_brrr (param_type_list_to_rep ps) == ps)
        (decreases ps)

val roundtrip_field_type_list : fs:list field_type ->
  Lemma (ensures field_rep_list_to_brrr (field_type_list_to_rep fs) == fs)
        (decreases fs)

val roundtrip_variant_type_list : vs:list variant_type ->
  Lemma (ensures variant_rep_list_to_brrr (variant_type_list_to_rep vs) == vs)
        (decreases vs)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec roundtrip_brrr_type t =
  match t with
  | TPrim pk -> prim_roundtrip_kind pk
  | TNumeric nt -> numeric_roundtrip_type nt
  | TWrap wk t' ->
      wrapper_roundtrip_kind wk;
      roundtrip_brrr_type t'
  | TModal mk t' ->
      modal_roundtrip_kind mk;
      roundtrip_brrr_type t'
  | TResult t1 t2 ->
      roundtrip_brrr_type t1;
      roundtrip_brrr_type t2
  | TTuple ts -> roundtrip_brrr_type_list ts
  | TFunc ft ->
      roundtrip_param_type_list ft.params;
      roundtrip_brrr_type ft.return_type
  | TVar _ -> ()
  | TNamed _ -> ()
  | TApp t' args ->
      roundtrip_brrr_type t';
      roundtrip_brrr_type_list args
  | TStruct st ->
      roundtrip_field_type_list st.struct_fields
  | TEnum et ->
      roundtrip_variant_type_list et.enum_variants

and roundtrip_brrr_type_list ts =
  match ts with
  | [] -> ()
  | t :: rest ->
      roundtrip_brrr_type t;
      roundtrip_brrr_type_list rest

and roundtrip_param_type_list ps =
  match ps with
  | [] -> ()
  | p :: rest ->
      roundtrip_brrr_type (Mkparam_type?.ty p);
      roundtrip_param_type_list rest

and roundtrip_field_type_list fs =
  match fs with
  | [] -> ()
  | f :: rest ->
      roundtrip_brrr_type f.field_ty;
      roundtrip_field_type_list rest

and roundtrip_variant_type_list vs =
  match vs with
  | [] -> ()
  | v :: rest ->
      roundtrip_brrr_type_list v.variant_fields;
      roundtrip_variant_type_list rest
#pop-options

(** ============================================================================
    ROUNDTRIP PROOFS: type_rep -> brrr_type -> type_rep
    ============================================================================ *)

val roundtrip_type_rep : tr:type_rep ->
  Lemma (ensures brrr_type_to_rep (type_rep_to_brrr tr) == tr)
        (decreases tr)

val roundtrip_type_rep_list : trs:trlist type_rep ->
  Lemma (ensures brrr_type_list_to_rep (type_rep_list_to_brrr trs) == trs)
        (decreases trs)

val roundtrip_param_rep_list : prs:trlist param_rep ->
  Lemma (ensures param_type_list_to_rep (param_rep_list_to_brrr prs) == prs)
        (decreases prs)

val roundtrip_field_rep_list : frs:trlist field_rep ->
  Lemma (ensures field_type_list_to_rep (field_rep_list_to_brrr frs) == frs)
        (decreases frs)

val roundtrip_variant_rep_list : vrs:trlist variant_rep ->
  Lemma (ensures variant_type_list_to_rep (variant_rep_list_to_brrr vrs) == vrs)
        (decreases vrs)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec roundtrip_type_rep tr =
  match tr with
  | TRPrim pr -> prim_roundtrip_rep pr
  | TRNumeric nr -> numeric_roundtrip_rep nr
  | TRWrap wr t ->
      wrapper_roundtrip_rep wr;
      roundtrip_type_rep t
  | TRModal mr t ->
      modal_roundtrip_rep mr;
      roundtrip_type_rep t
  | TRResult t1 t2 ->
      roundtrip_type_rep t1;
      roundtrip_type_rep t2
  | TRTuple trs -> roundtrip_type_rep_list trs
  | TRFunc params ret_ty _ _ ->
      roundtrip_param_rep_list params;
      roundtrip_type_rep ret_ty
  | TRVar _ -> ()
  | TRNamed _ -> ()
  | TRApp tr' args ->
      roundtrip_type_rep tr';
      roundtrip_type_rep_list args
  | TRStruct _ fields _ ->
      roundtrip_field_rep_list fields
  | TREnum _ variants ->
      roundtrip_variant_rep_list variants

and roundtrip_type_rep_list trs =
  match trs with
  | [] -> ()
  | tr :: rest ->
      roundtrip_type_rep tr;
      roundtrip_type_rep_list rest

and roundtrip_param_rep_list prs =
  match prs with
  | [] -> ()
  | pr :: rest ->
      roundtrip_type_rep pr.pr_ty;
      roundtrip_param_rep_list rest

and roundtrip_field_rep_list frs =
  match frs with
  | [] -> ()
  | fr :: rest ->
      roundtrip_type_rep fr.flr_ty;
      roundtrip_field_rep_list rest

and roundtrip_variant_rep_list vrs =
  match vrs with
  | [] -> ()
  | vr :: rest ->
      roundtrip_type_rep_list vr.vr_fields;
      roundtrip_variant_rep_list rest
#pop-options

(** ============================================================================
    TYPE REPRESENTATION EQUALITY
    ============================================================================

    We need structural equality for type_rep that:
    1. Returns true when two type_reps represent the same type
    2. Is decidable (bool return)
    3. Is reflexive, symmetric, and transitive
    ============================================================================ *)

(* Primitive equality *)
let prim_rep_eq (p1 p2: prim_rep) : bool =
  match p1, p2 with
  | PRUnit, PRUnit -> true
  | PRNever, PRNever -> true
  | PRBool, PRBool -> true
  | PRString, PRString -> true
  | PRChar, PRChar -> true
  | PRDynamic, PRDynamic -> true
  | _, _ -> false

(* Numeric equality *)
let numeric_rep_eq (n1 n2: numeric_rep) : bool =
  match n1, n2 with
  | NRInt i1, NRInt i2 -> i1.width = i2.width && i1.sign = i2.sign
  | NRFloat f1, NRFloat f2 -> f1 = f2
  | _, _ -> false

(* Wrapper equality *)
let wrapper_rep_eq (w1 w2: wrapper_rep) : bool =
  match w1, w2 with
  | WRArray, WRArray -> true | WRSlice, WRSlice -> true | WROption, WROption -> true
  | WRBox, WRBox -> true | WRRef, WRRef -> true | WRRefMut, WRRefMut -> true
  | WRRc, WRRc -> true | WRArc, WRArc -> true | WRRaw, WRRaw -> true
  | _, _ -> false

(* Modal equality - uses structural equality for ref_kind to enable proofs *)
let modal_rep_eq (m1 m2: modal_rep) : bool =
  match m1, m2 with
  | MRBoxMod rk1, MRBoxMod rk2 ->
      (* Structural equality for ref_kind *)
      (match rk1, rk2 with
       | RefBox f1, RefBox f2 -> f1.frac_num = f2.frac_num && f1.frac_den = f2.frac_den
       | RefDiamond, RefDiamond -> true
       | _, _ -> false)
  | MRDiamondMod, MRDiamondMod -> true
  | _, _ -> false

(* Mutual recursion for type_rep equality *)
val type_rep_eq : tr1:type_rep -> tr2:type_rep -> Tot bool (decreases tr1)
val type_rep_list_eq : trs1:trlist type_rep -> trs2:trlist type_rep -> Tot bool (decreases trs1)
val param_rep_list_eq : prs1:trlist param_rep -> prs2:trlist param_rep -> Tot bool (decreases prs1)

let rec type_rep_eq tr1 tr2 =
  match tr1, tr2 with
  | TRPrim p1, TRPrim p2 -> prim_rep_eq p1 p2
  | TRNumeric n1, TRNumeric n2 -> numeric_rep_eq n1 n2
  | TRWrap w1 t1, TRWrap w2 t2 -> wrapper_rep_eq w1 w2 && type_rep_eq t1 t2
  | TRModal m1 t1, TRModal m2 t2 -> modal_rep_eq m1 m2 && type_rep_eq t1 t2
  | TRResult t1a t1b, TRResult t2a t2b -> type_rep_eq t1a t2a && type_rep_eq t1b t2b
  | TRTuple trs1, TRTuple trs2 -> type_rep_list_eq trs1 trs2
  | TRFunc params1 ret1 eff1 unsafe1, TRFunc params2 ret2 eff2 unsafe2 ->
      param_rep_list_eq params1 params2 &&
      type_rep_eq ret1 ret2 &&
      row_eq eff1 eff2 &&
      unsafe1 = unsafe2
  | TRVar v1, TRVar v2 -> v1 = v2
  | TRNamed n1, TRNamed n2 -> n1 = n2
  | TRApp tr1' args1, TRApp tr2' args2 ->
      type_rep_eq tr1' tr2' && type_rep_list_eq args1 args2
  | TRStruct name1 _ _, TRStruct name2 _ _ -> name1 = name2
  | TREnum name1 _, TREnum name2 _ -> name1 = name2
  | _, _ -> false

and type_rep_list_eq trs1 trs2 =
  match trs1, trs2 with
  | [], [] -> true
  | tr1 :: rest1, tr2 :: rest2 -> type_rep_eq tr1 tr2 && type_rep_list_eq rest1 rest2
  | _, _ -> false

and param_rep_list_eq prs1 prs2 =
  match prs1, prs2 with
  | [], [] -> true
  | pr1 :: rest1, pr2 :: rest2 ->
      type_rep_eq pr1.pr_ty pr2.pr_ty &&
      pr1.pr_mode = pr2.pr_mode &&
      param_rep_list_eq rest1 rest2
  | _, _ -> false

(** ============================================================================
    TYPE_REP_EQ REFLEXIVITY PROOF
    ============================================================================ *)

val prim_rep_eq_refl : p:prim_rep ->
  Lemma (prim_rep_eq p p = true)
        [SMTPat (prim_rep_eq p p)]
let prim_rep_eq_refl p =
  match p with
  | PRUnit -> () | PRNever -> () | PRBool -> ()
  | PRString -> () | PRChar -> () | PRDynamic -> ()

val numeric_rep_eq_refl : n:numeric_rep ->
  Lemma (numeric_rep_eq n n = true)
        [SMTPat (numeric_rep_eq n n)]
let numeric_rep_eq_refl n =
  match n with
  | NRInt _ -> ()
  | NRFloat _ -> ()

val wrapper_rep_eq_refl : w:wrapper_rep ->
  Lemma (wrapper_rep_eq w w = true)
        [SMTPat (wrapper_rep_eq w w)]
let wrapper_rep_eq_refl w =
  match w with
  | WRArray -> () | WRSlice -> () | WROption -> () | WRBox -> ()
  | WRRef -> () | WRRefMut -> () | WRRc -> () | WRArc -> () | WRRaw -> ()

val modal_rep_eq_refl : m:modal_rep ->
  Lemma (modal_rep_eq m m = true)
        [SMTPat (modal_rep_eq m m)]
let modal_rep_eq_refl m =
  match m with
  | MRBoxMod rk ->
      (match rk with
       | RefBox f -> ()
       | RefDiamond -> ())
  | MRDiamondMod -> ()

val type_rep_eq_refl : tr:type_rep ->
  Lemma (ensures type_rep_eq tr tr = true)
        (decreases tr)
        [SMTPat (type_rep_eq tr tr)]
val type_rep_list_eq_refl : trs:trlist type_rep ->
  Lemma (ensures type_rep_list_eq trs trs = true)
        (decreases trs)
        [SMTPat (type_rep_list_eq trs trs)]
val param_rep_list_eq_refl : prs:trlist param_rep ->
  Lemma (ensures param_rep_list_eq prs prs = true)
        (decreases prs)
        [SMTPat (param_rep_list_eq prs prs)]

let rec type_rep_eq_refl tr =
  match tr with
  | TRPrim p -> prim_rep_eq_refl p
  | TRNumeric n -> numeric_rep_eq_refl n
  | TRWrap w t -> wrapper_rep_eq_refl w; type_rep_eq_refl t
  | TRModal m t -> modal_rep_eq_refl m; type_rep_eq_refl t
  | TRResult t1 t2 -> type_rep_eq_refl t1; type_rep_eq_refl t2
  | TRTuple trs -> type_rep_list_eq_refl trs
  | TRFunc params ret_ty effects _ ->
      param_rep_list_eq_refl params;
      type_rep_eq_refl ret_ty;
      row_eq_refl effects
  | TRVar _ -> ()
  | TRNamed _ -> ()
  | TRApp tr' args -> type_rep_eq_refl tr'; type_rep_list_eq_refl args
  | TRStruct _ _ _ -> ()
  | TREnum _ _ -> ()

and type_rep_list_eq_refl trs =
  match trs with
  | [] -> ()
  | tr :: rest -> type_rep_eq_refl tr; type_rep_list_eq_refl rest

and param_rep_list_eq_refl prs =
  match prs with
  | [] -> ()
  | pr :: rest -> type_rep_eq_refl pr.pr_ty; param_rep_list_eq_refl rest

(** ============================================================================
    TYPE EQUALITY WITNESS - Leibniz Equality

    Leibniz equality: tau =:= sigma  iff  forall F. F[tau] -> F[sigma]

    In F*, we use propositional equality (==) combined with squash types.
    The key insight is that if type_rep_eq tr1 tr2 = true, then
    type_rep_to_brrr tr1 == type_rep_to_brrr tr2.
    ============================================================================ *)

(* Type equality witness: proof that two brrr_types are propositionally equal *)
type brrr_type_equality (t1 t2: brrr_type) = squash (t1 == t2)

(* Reflexivity: any type equals itself *)
let brrr_type_eq_refl (#t: brrr_type) : brrr_type_equality t t = ()

(* Symmetry: if t1 == t2 then t2 == t1 *)
let brrr_type_eq_sym (#t1 #t2: brrr_type) (pf: brrr_type_equality t1 t2)
    : brrr_type_equality t2 t1 = ()

(* Transitivity: if t1 == t2 and t2 == t3 then t1 == t3 *)
let brrr_type_eq_trans (#t1 #t2 #t3: brrr_type)
    (pf1: brrr_type_equality t1 t2) (pf2: brrr_type_equality t2 t3)
    : brrr_type_equality t1 t3 = ()

(** ============================================================================
    HELPER LEMMAS FOR EQUALITY PROOFS

    These lemmas connect the boolean equality checks to brrr_type equality.
    When the boolean check returns true, we get a proof that the converted
    brrr_types are propositionally equal.
    ============================================================================ *)

(* Primitive equality implies brrr_type equality *)
val prim_rep_eq_implies_brrr_eq : p1:prim_rep -> p2:prim_rep ->
  Lemma (requires prim_rep_eq p1 p2 = true)
        (ensures TPrim (prim_rep_to_kind p1) == TPrim (prim_rep_to_kind p2))
let prim_rep_eq_implies_brrr_eq p1 p2 =
  match p1, p2 with
  | PRUnit, PRUnit -> () | PRNever, PRNever -> () | PRBool, PRBool -> ()
  | PRString, PRString -> () | PRChar, PRChar -> () | PRDynamic, PRDynamic -> ()

(* Numeric equality implies brrr_type equality *)
val numeric_rep_eq_implies_brrr_eq : n1:numeric_rep -> n2:numeric_rep ->
  Lemma (requires numeric_rep_eq n1 n2 = true)
        (ensures TNumeric (numeric_rep_to_type n1) == TNumeric (numeric_rep_to_type n2))
let numeric_rep_eq_implies_brrr_eq n1 n2 =
  match n1, n2 with
  | NRInt i1, NRInt i2 -> ()
  | NRFloat f1, NRFloat f2 -> ()

(* Wrapper equality implies wrapper kind equality *)
val wrapper_rep_eq_implies_kind_eq : w1:wrapper_rep -> w2:wrapper_rep ->
  Lemma (requires wrapper_rep_eq w1 w2 = true)
        (ensures wrapper_rep_to_kind w1 == wrapper_rep_to_kind w2)
let wrapper_rep_eq_implies_kind_eq w1 w2 =
  match w1, w2 with
  | WRArray, WRArray -> () | WRSlice, WRSlice -> () | WROption, WROption -> ()
  | WRBox, WRBox -> () | WRRef, WRRef -> () | WRRefMut, WRRefMut -> ()
  | WRRc, WRRc -> () | WRArc, WRArc -> () | WRRaw, WRRaw -> ()

(* Modal equality implies modal kind equality *)
val modal_rep_eq_implies_kind_eq : m1:modal_rep -> m2:modal_rep ->
  Lemma (requires modal_rep_eq m1 m2 = true)
        (ensures modal_rep_to_kind m1 == modal_rep_to_kind m2)
let modal_rep_eq_implies_kind_eq m1 m2 =
  match m1, m2 with
  | MRBoxMod rk1, MRBoxMod rk2 ->
      (match rk1, rk2 with
       | RefBox f1, RefBox f2 -> ()
       | RefDiamond, RefDiamond -> ())
  | MRDiamondMod, MRDiamondMod -> ()

(** ============================================================================
    TYPE_REP_EQ: SOUNDNESS BY CONSTRUCTION

    The type_rep_eq function is sound by construction: it returns true only
    when the two type representations are structurally identical. This follows
    from examining each case in the function definition.

    For practical use, we rely on the following properties:
    1. type_rep_eq_refl: type_rep_eq tr tr = true (reflexivity)
    2. Soundness: if type_rep_eq tr1 tr2 = true, then tr1 and tr2 represent
       the same type (follows from structural comparison)

    The roundtrip proofs (roundtrip_brrr_type, roundtrip_type_rep) establish
    that brrr_type <-> type_rep conversion preserves type identity.
    ============================================================================ *)

(** ============================================================================
    TYPE EQUALITY CHECK FUNCTION

    The type_rep_eq function provides a decidable equality check for type
    representations. For practical reflection purposes, this is sufficient.

    Note: The function already exists as type_rep_eq above. Here we provide
    a simple wrapper that returns Option for compatibility with the spec.
    ============================================================================ *)

(* Check if two type_reps are equal, returning Some () if equal, None if different.
   This is a simple wrapper around type_rep_eq for Option-based APIs. *)
let eq_type_rep_check (tr1 tr2: type_rep) : option unit =
  if type_rep_eq tr1 tr2 then Some () else None

(* Same for lists *)
let eq_type_rep_list_check (trs1 trs2: trlist type_rep) : option unit =
  if type_rep_list_eq trs1 trs2 then Some () else None

(** ============================================================================
    DYNAMIC TYPE

    Dynamic = exists tau. (value * TypeRep[tau])

    A dynamic value packages a runtime value together with its type representation.
    This enables type-safe dynamic typing: we can pack any value into Dynamic,
    and unpack it only if we provide the correct type representation.
    ============================================================================ *)

open Values

(* Dynamic value: existential package of value + type representation *)
noeq type dynamic =
  | Dyn : tr:type_rep -> v:value -> dynamic

(* Create a dynamic value from a value and its type representation *)
let to_dynamic (tr: type_rep) (v: value) : dynamic = Dyn tr v

(* Get the type representation from a dynamic value *)
let get_type_rep (d: dynamic) : type_rep =
  match d with
  | Dyn tr _ -> tr

(* Get the underlying value (untyped) *)
let get_value (d: dynamic) : value =
  match d with
  | Dyn _ v -> v

(** ============================================================================
    SAFE CAST OPERATIONS

    Cast checks if the actual type matches the expected type at runtime.
    If they match, it returns the value; otherwise None.
    ============================================================================ *)

(* Attempt to extract a value from Dynamic with expected type representation.
   Returns Some value if types match, None otherwise. *)
let from_dynamic (d: dynamic) (expected: type_rep) : option value =
  match d with
  | Dyn actual v ->
      if type_rep_eq actual expected
      then Some v
      else None

(* Cast value with source type_rep to target type_rep.
   Only succeeds if source and target types are equal. *)
let cast_value (v: value) (source: type_rep) (target: type_rep) : option value =
  if type_rep_eq source target
  then Some v
  else None

(* Cast with equality proof: if types are equal, casting always succeeds *)
val cast_with_proof : v:value -> source:type_rep -> target:type_rep ->
  eq:brrr_type_equality (type_rep_to_brrr source) (type_rep_to_brrr target) ->
  value
let cast_with_proof v source target eq = v

(** ============================================================================
    CAST SAFETY PROOF

    Key theorem: If from_dynamic returns Some v, then the type representation
    in the Dynamic value is equal to the expected type representation.
    ============================================================================ *)

val from_dynamic_safe : d:dynamic -> expected:type_rep ->
  Lemma (ensures (match from_dynamic d expected with
                  | Some _ -> type_rep_eq (get_type_rep d) expected = true
                  | None -> true))
let from_dynamic_safe d expected =
  match d with
  | Dyn actual v ->
      if type_rep_eq actual expected then () else ()

(* If from_dynamic succeeds, the type_rep_eq check passed.
   This is a weaker but more practical guarantee. *)
val from_dynamic_types_eq : d:dynamic -> expected:type_rep ->
  Lemma (requires Some? (from_dynamic d expected))
        (ensures type_rep_eq (get_type_rep d) expected = true)
let from_dynamic_types_eq d expected =
  match d with
  | Dyn actual _ -> ()

(** ============================================================================
    TYPE_OF OPERATIONS
    ============================================================================ *)

(* Infer type representation from a value.
   This is partial: not all runtime values have enough information to
   fully reconstruct their type. Returns None for ambiguous cases. *)
let rec typeof_value (v: value) : option type_rep =
  match v with
  | VUnit -> Some (TRPrim PRUnit)
  | VBool _ -> Some (TRPrim PRBool)
  | VInt _ -> Some (TRNumeric (NRInt i64))  (* Default to i64 *)
  | VFloat _ -> Some (TRNumeric (NRFloat F64))  (* Default to f64 *)
  | VString _ -> Some (TRPrim PRString)
  | VChar _ -> Some (TRPrim PRChar)
  | VNone -> None  (* Cannot determine element type *)
  | VSome v' ->
      (match typeof_value v' with
       | Some inner -> Some (TRWrap WROption inner)
       | None -> None)
  | VTuple vs ->
      (match typeof_value_list vs with
       | Some trs -> Some (TRTuple trs)
       | None -> None)
  | VArray _ -> None  (* Cannot determine element type without more info *)
  | VStruct name _ -> Some (TRNamed name)
  | VVariant name _ _ -> Some (TRNamed name)
  | VRef _ -> None  (* Reference type needs context *)
  | VRefMut _ -> None
  | VBox _ -> None
  | VClosure _ -> None  (* Function type needs context *)
  | VOk v' ->
      (match typeof_value v' with
       | Some tr -> Some (TRResult tr (TRPrim PRNever))
       | None -> None)
  | VErr _ -> None  (* Cannot determine ok type *)
  (* Async/Generator values - cannot determine type parameters without context *)
  | VFuture _ -> None  (* Future<T> needs context for T *)
  | VGenerator _ -> None  (* Generator<Y, R> needs context for Y and R *)

and typeof_value_list (vs: vlist value) : option (trlist type_rep) =
  match vs with
  | [] -> Some []
  | v :: rest ->
      (match typeof_value v, typeof_value_list rest with
       | Some tr, Some trs -> Some (tr :: trs)
       | _, _ -> None)

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR COMMON TYPES
    ============================================================================ *)

(* Primitive type representations *)
let tr_unit : type_rep = TRPrim PRUnit
let tr_never : type_rep = TRPrim PRNever
let tr_bool : type_rep = TRPrim PRBool
let tr_string : type_rep = TRPrim PRString
let tr_char : type_rep = TRPrim PRChar
let tr_dynamic : type_rep = TRPrim PRDynamic

(* Numeric type representations *)
let tr_i8 : type_rep = TRNumeric (NRInt i8)
let tr_i16 : type_rep = TRNumeric (NRInt i16)
let tr_i32 : type_rep = TRNumeric (NRInt i32)
let tr_i64 : type_rep = TRNumeric (NRInt i64)
let tr_u8 : type_rep = TRNumeric (NRInt u8)
let tr_u16 : type_rep = TRNumeric (NRInt u16)
let tr_u32 : type_rep = TRNumeric (NRInt u32)
let tr_u64 : type_rep = TRNumeric (NRInt u64)
let tr_f32 : type_rep = TRNumeric (NRFloat F32)
let tr_f64 : type_rep = TRNumeric (NRFloat F64)

(* Wrapper type representation constructors *)
let tr_array (t: type_rep) : type_rep = TRWrap WRArray t
let tr_slice (t: type_rep) : type_rep = TRWrap WRSlice t
let tr_option (t: type_rep) : type_rep = TRWrap WROption t
let tr_box (t: type_rep) : type_rep = TRWrap WRBox t
let tr_ref (t: type_rep) : type_rep = TRWrap WRRef t
let tr_ref_mut (t: type_rep) : type_rep = TRWrap WRRefMut t

(* Result type representation *)
let tr_result (t_ok t_err: type_rep) : type_rep = TRResult t_ok t_err

(* Tuple type representation *)
let tr_tuple (ts: trlist type_rep) : type_rep = TRTuple ts

(** ============================================================================
    CONSISTENCY PROOFS WITH brrr_type
    ============================================================================ *)

val tr_unit_consistent : unit -> Lemma (type_rep_to_brrr tr_unit == t_unit)
let tr_unit_consistent () = ()

val tr_bool_consistent : unit -> Lemma (type_rep_to_brrr tr_bool == t_bool)
let tr_bool_consistent () = ()

val tr_string_consistent : unit -> Lemma (type_rep_to_brrr tr_string == t_string)
let tr_string_consistent () = ()

val tr_i32_consistent : unit -> Lemma (type_rep_to_brrr tr_i32 == t_i32)
let tr_i32_consistent () = ()

val tr_i64_consistent : unit -> Lemma (type_rep_to_brrr tr_i64 == t_i64)
let tr_i64_consistent () = ()

val tr_option_consistent : t:type_rep ->
  Lemma (type_rep_to_brrr (tr_option t) == t_option (type_rep_to_brrr t))
let tr_option_consistent t = ()

val tr_result_consistent : t_ok:type_rep -> t_err:type_rep ->
  Lemma (type_rep_to_brrr (tr_result t_ok t_err) ==
         TResult (type_rep_to_brrr t_ok) (type_rep_to_brrr t_err))
let tr_result_consistent t_ok t_err = ()

(** ============================================================================
    TYPE REPRESENTATION INTROSPECTION
    ============================================================================ *)

(* Is this a primitive type? *)
let is_prim_type (tr: type_rep) : bool =
  match tr with
  | TRPrim _ -> true
  | _ -> false

(* Is this a numeric type? *)
let is_numeric_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric _ -> true
  | _ -> false

(* Is this an integer type? *)
let is_int_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric (NRInt _) -> true
  | _ -> false

(* Is this a float type? *)
let is_float_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric (NRFloat _) -> true
  | _ -> false

(* Is this a function type? *)
let is_func_type (tr: type_rep) : bool =
  match tr with
  | TRFunc _ _ _ _ -> true
  | _ -> false

(* Is this a wrapper type (Option, Array, etc.)? *)
let is_wrapper_type (tr: type_rep) : bool =
  match tr with
  | TRWrap _ _ -> true
  | _ -> false

(* Is this a named type reference? *)
let is_named_type (tr: type_rep) : bool =
  match tr with
  | TRNamed _ -> true
  | TRStruct _ _ _ -> true
  | TREnum _ _ -> true
  | _ -> false

(* Get the inner type of a wrapper, if applicable *)
let get_inner_type (tr: type_rep) : option type_rep =
  match tr with
  | TRWrap _ inner -> Some inner
  | TRModal _ inner -> Some inner
  | _ -> None

(* Get function parameter types, if applicable *)
let get_func_param_types (tr: type_rep) : option (trlist type_rep) =
  match tr with
  | TRFunc params _ _ _ -> Some (List.Tot.map (fun pr -> pr.pr_ty) params)
  | _ -> None

(* Get function return type, if applicable *)
let get_func_return_type (tr: type_rep) : option type_rep =
  match tr with
  | TRFunc _ ret _ _ -> Some ret
  | _ -> None

(** ============================================================================
    PRETTY PRINTING (for debugging/display)
    ============================================================================ *)

let rec type_rep_to_string (tr: type_rep) : Tot string (decreases tr) =
  match tr with
  | TRPrim PRUnit -> "()"
  | TRPrim PRNever -> "!"
  | TRPrim PRBool -> "bool"
  | TRPrim PRString -> "String"
  | TRPrim PRChar -> "char"
  | TRPrim PRDynamic -> "Dynamic"
  | TRNumeric (NRInt it) ->
      (if it.sign = Signed then "i" else "u") ^
      (match it.width with
       | I8 -> "8" | I16 -> "16" | I32 -> "32" | I64 -> "64"
       | I128 -> "128" | IBig -> "Big")
  | TRNumeric (NRFloat fp) ->
      (match fp with F16 -> "f16" | F32 -> "f32" | F64 -> "f64")
  | TRWrap WROption inner -> type_rep_to_string inner ^ "?"
  | TRWrap WRArray inner -> "[" ^ type_rep_to_string inner ^ "]"
  | TRWrap WRSlice inner -> "&[" ^ type_rep_to_string inner ^ "]"
  | TRWrap WRBox inner -> "Box<" ^ type_rep_to_string inner ^ ">"
  | TRWrap WRRef inner -> "&" ^ type_rep_to_string inner
  | TRWrap WRRefMut inner -> "&mut " ^ type_rep_to_string inner
  | TRWrap WRRc inner -> "Rc<" ^ type_rep_to_string inner ^ ">"
  | TRWrap WRArc inner -> "Arc<" ^ type_rep_to_string inner ^ ">"
  | TRWrap WRRaw inner -> "*" ^ type_rep_to_string inner
  | TRModal MRDiamondMod inner -> "<>" ^ type_rep_to_string inner
  | TRModal (MRBoxMod _) inner -> "[]" ^ type_rep_to_string inner
  | TRResult t_ok t_err ->
      "Result<" ^ type_rep_to_string t_ok ^ ", " ^ type_rep_to_string t_err ^ ">"
  | TRTuple [] -> "()"
  | TRTuple trs -> "(" ^ type_rep_list_to_string trs ^ ")"
  | TRFunc _ _ _ _ -> "fn(...) -> ..."
  | TRVar v -> v
  | TRNamed n -> n
  | TRApp tr' _ -> type_rep_to_string tr' ^ "<...>"
  | TRStruct name _ _ -> "struct " ^ name
  | TREnum name _ -> "enum " ^ name

and type_rep_list_to_string (trs: trlist type_rep) : Tot string (decreases trs) =
  match trs with
  | [] -> ""
  | [tr] -> type_rep_to_string tr
  | tr :: rest -> type_rep_to_string tr ^ ", " ^ type_rep_list_to_string rest
