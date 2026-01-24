(**
 * BrrrLang.Core.Types
 *
 * Complete type system for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Parts II-III.
 *
 * Depends on: Primitives, Modes, Effects
 *)
module BrrrTypes

open Primitives
open Modes
open Effects
open Utils  (* Shared utilities - zip_lists, option combinators, etc. *)
open FStar.List.Tot
open FStar.Classical

(* Z3 solver options for SMT tractability - following HACL*/EverParse patterns *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    SOURCE LOCATION TRACKING (following EverParse with_meta_t pattern)
    ============================================================================

    Every AST node and type can carry source location information for:
    - Precise error messages with file:line:col
    - Type error diagnostics with source spans
    - IDE integration (go-to-definition, hover info)

    Pattern from EverParse/Ast.fst:
    - type_pos: A source position (file, line, column)
    - type_range: A span from start to end position
    - with_type_loc: A wrapper that attaches location to any type

    Note: Expressions.fst has its own pos/range for expression-level tracking.
    These type-level locations are for type definitions, type errors, etc.
    ============================================================================ *)

(** Source position for type-level diagnostics *)
type type_pos = {
  tpos_filename : string;  (* Source file path *)
  tpos_line     : nat;     (* 1-indexed line number *)
  tpos_col      : nat      (* 0-indexed column number *)
}

(** Dummy position for synthetic/generated types *)
let dummy_type_pos : type_pos = {
  tpos_filename = "<synthetic>";
  tpos_line = 0;
  tpos_col = 0
}

(** Format type position as "file:line:col" for error messages *)
let string_of_type_pos (p: type_pos) : string =
  p.tpos_filename ^ ":" ^
  string_of_int p.tpos_line ^ ":" ^
  string_of_int p.tpos_col

(** Type range: span from start to end position *)
type type_range = type_pos & type_pos

(** Dummy range for synthetic/generated types *)
let dummy_type_range : type_range = (dummy_type_pos, dummy_type_pos)

(** Format type range for error messages *)
let string_of_type_range (r: type_range) : string =
  let (start_p, end_p) = r in
  if start_p.tpos_filename = end_p.tpos_filename then
    start_p.tpos_filename ^ ":" ^
    string_of_int start_p.tpos_line ^ ":" ^
    string_of_int start_p.tpos_col ^ "-" ^
    string_of_int end_p.tpos_line ^ ":" ^
    string_of_int end_p.tpos_col
  else
    string_of_type_pos start_p ^ " to " ^ string_of_type_pos end_p

(** Merge two ranges into a range spanning both.
    Returns the smallest range containing both input ranges.
    If ranges are from different files, returns the first range. *)
let merge_type_ranges (r1 r2: type_range) : type_range =
  let (s1, e1) = r1 in
  let (s2, e2) = r2 in
  if s1.tpos_filename <> s2.tpos_filename then r1
  else
    let start_pos =
      if s1.tpos_line < s2.tpos_line then s1
      else if s1.tpos_line > s2.tpos_line then s2
      else if s1.tpos_col <= s2.tpos_col then s1
      else s2
    in
    let end_pos =
      if e1.tpos_line > e2.tpos_line then e1
      else if e1.tpos_line < e2.tpos_line then e2
      else if e1.tpos_col >= e2.tpos_col then e1
      else e2
    in
    (start_pos, end_pos)

(** Wrapper type that attaches source location to any value.
    Following the EverParse with_meta_t pattern for type-level locations. *)
noeq type with_type_loc 'a = {
  tloc_value : 'a;          (* The wrapped value *)
  tloc_range : type_range;  (* Source span *)
}

(** Create a located type value *)
let locate_type (#a: Type) (v: a) (r: type_range) : with_type_loc a =
  { tloc_value = v; tloc_range = r }

(** Create a located value at dummy location (for synthetic types) *)
let locate_type_dummy (#a: Type) (v: a) : with_type_loc a =
  { tloc_value = v; tloc_range = dummy_type_range }

(** Extract the value from a located wrapper *)
let unloc_type (#a: Type) (w: with_type_loc a) : a = w.tloc_value

(** Extract the range from a located wrapper *)
let loc_of_type (#a: Type) (w: with_type_loc a) : type_range = w.tloc_range

(** Map a function over a located value, preserving location *)
let map_type_loc (#a #b: Type) (f: a -> b) (w: with_type_loc a) : with_type_loc b =
  { tloc_value = f w.tloc_value; tloc_range = w.tloc_range }

(** Type error with source location *)
noeq type type_error = {
  terr_message : string;
  terr_range   : type_range;
}

(** Create a type error at a location *)
let type_error_at (msg: string) (r: type_range) : type_error =
  { terr_message = msg; terr_range = r }

(** Format a type error for display *)
let string_of_type_error (e: type_error) : string =
  string_of_type_range e.terr_range ^ ": type error: " ^ e.terr_message

(** ============================================================================
    TYPE IDENTIFIERS
    ============================================================================ *)

(* Type variable *)
type type_var = string

(* Named type reference *)
type type_name = string

(* Type ID for interning *)
type type_id = nat

(** ============================================================================
    TYPE DISCRIMINATORS - SMT Tractability Optimization
    ============================================================================

    These discriminator types group related type variants under fewer top-level
    constructors. This reduces Z3 proof complexity from 27^3 = 19,683 combinations
    to 12^3 = 1,728 combinations for transitivity proofs.
    ============================================================================ *)

(* Primitive type kinds - 7 variants combined into 1 constructor *)
type prim_kind =
  | PUnit   : prim_kind   (* () - unit type *)
  | PNever  : prim_kind   (* ! - bottom type, no values *)
  | PBool   : prim_kind   (* bool *)
  | PString : prim_kind   (* String *)
  | PChar   : prim_kind   (* char *)
  | PDynamic: prim_kind   (* Dynamic/any type - UNSAFE: allows any operation without checks *)
  | PUnknown: prim_kind   (* Unknown type - SAFE top type: requires runtime checks before use
                             For gradual typing: gamma(Unknown) = {all static types}
                             Unlike Dynamic, operations on Unknown require type guards/casts *)

(* Numeric type - integers and floats with their width/precision *)
type numeric_type =
  | NumInt   : int_type -> numeric_type    (* i8, i16, i32, i64, u8, u16, u32, u64 *)
  | NumFloat : float_prec -> numeric_type  (* f32, f64 *)

(* Numeric type equality *)
let numeric_eq (n1 n2: numeric_type) : bool =
  match n1, n2 with
  | NumInt i1, NumInt i2 -> i1.width = i2.width && i1.sign = i2.sign
  | NumFloat p1, NumFloat p2 -> p1 = p2
  | _, _ -> false

(* Wrapper kinds - 9 single-type wrappers combined into 1 constructor *)
type wrapper_kind =
  | WArray  : wrapper_kind   (* [T] - array *)
  | WSlice  : wrapper_kind   (* &[T] - slice *)
  | WOption : wrapper_kind   (* T? - optional *)
  | WBox    : wrapper_kind   (* Box<T> - owned heap *)
  | WRef    : wrapper_kind   (* &T - shared ref *)
  | WRefMut : wrapper_kind   (* &mut T - exclusive ref *)
  | WRc     : wrapper_kind   (* Rc<T> - reference counted *)
  | WArc    : wrapper_kind   (* Arc<T> - atomic RC *)
  | WRaw    : wrapper_kind   (* *T - raw pointer *)

(* Is this wrapper covariant (subtype inner -> subtype outer)?
   RefMut is invariant; all others are covariant *)
let wrapper_is_covariant (w: wrapper_kind) : bool =
  match w with
  | WRefMut -> false  (* Invariant: &mut T requires exact T match *)
  | _ -> true         (* Covariant: inner subtype implies outer subtype *)

(* Modal reference kinds - for fractional permissions *)
type modal_kind =
  | MBoxMod     : ref_kind -> modal_kind   (* □τ @ p - shared ref with permission p *)
  | MDiamondMod : modal_kind               (* ◇τ - exclusive ref (permission = 1) *)

(* Modal kind equality *)
let modal_eq (m1 m2: modal_kind) : bool =
  match m1, m2 with
  | MBoxMod rk1, MBoxMod rk2 -> frac_eq (ref_permission rk1) (ref_permission rk2)
  | MDiamondMod, MDiamondMod -> true
  | _, _ -> false

(** ============================================================================
    CORE TYPE CONSTRUCTORS - Restructured for SMT Tractability
    ============================================================================

    12 constructors instead of 27:
    1. TPrim    - covers 6 primitive types
    2. TNumeric - covers all integer and float types
    3. TWrap    - covers 9 single-type wrappers
    4. TModal   - covers Box/Diamond modal references
    5. TResult  - Result<T, E> binary type
    6. TTuple   - (T1, T2, ...) product type
    7. TFunc    - function types
    8. TVar     - type variables
    9. TApp     - type application F<T1, T2>
    10. TNamed  - named type references
    11. TStruct - struct types
    12. TEnum   - enum types
    ============================================================================ *)

(* The main type definition - mutually recursive with function types *)
noeq type brrr_type =
  (* Primitives: 1 constructor covers 6 types *)
  | TPrim    : prim_kind -> brrr_type

  (* Numerics: 1 constructor covers int/float with all widths *)
  | TNumeric : numeric_type -> brrr_type

  (* Wrappers: 1 constructor covers 9 single-type wrappers *)
  | TWrap    : wrapper_kind -> brrr_type -> brrr_type

  (* Modal refs: 1 constructor covers Box/Diamond modalities *)
  | TModal   : modal_kind -> brrr_type -> brrr_type

  (* Binary type constructor *)
  | TResult  : brrr_type -> brrr_type -> brrr_type (* Result<T, E> *)

  (* Collection type *)
  | TTuple   : list brrr_type -> brrr_type         (* (T1, T2, ...) *)

  (* Function type *)
  | TFunc    : func_type -> brrr_type

  (* Type variables and applications *)
  | TVar     : type_var -> brrr_type               (* α *)
  | TApp     : brrr_type -> list brrr_type -> brrr_type  (* F<T1, T2> *)
  | TNamed   : type_name -> brrr_type              (* Named type reference *)

  (* Algebraic types *)
  | TStruct  : struct_type -> brrr_type
  | TEnum    : enum_type -> brrr_type

(* Function type with effects and modes *)
and func_type = {
  params      : list param_type;    (* Parameter types *)
  return_type : brrr_type;          (* Return type *)
  effects     : effect_row;         (* Effect annotation *)
  is_unsafe   : bool                (* Requires unsafe context? *)
}

(* Parameter with mode annotation *)
and param_type = {
  name : option string;   (* Optional parameter name *)
  ty   : brrr_type;       (* Parameter type *)
  mode : mode             (* Usage mode *)
}

(* Struct type *)
and struct_type = {
  struct_name   : type_name;
  struct_fields : list field_type;
  struct_repr   : repr_attr         (* Memory representation *)
}

(* Enum type *)
and enum_type = {
  enum_name     : type_name;
  enum_variants : list variant_type
}

(* Struct field *)
and field_type = {
  field_name : string;
  field_ty   : brrr_type;
  field_vis  : visibility
}

(* Enum variant *)
and variant_type = {
  variant_name   : string;
  variant_fields : list brrr_type   (* Tuple-like or unit *)
}

(* Visibility *)
and visibility =
  | Public  : visibility
  | Private : visibility
  | Module  : visibility            (* Visible within module *)

(* Helper: check if n is a power of 2 (n = 2^k for some k >= 0)
   Valid alignments: 1, 2, 4, 8, 16, 32, 64, 128, 256, ... *)
let rec is_power_of_2 (n: pos) : Tot bool (decreases n) =
  if n = 1 then true
  else if n % 2 <> 0 then false
  else is_power_of_2 (n / 2)

(* Valid alignment: positive power of 2, at most 2^29 (reasonable max for memory alignment) *)
type valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}

(* Memory representation attribute *)
and repr_attr =
  | ReprRust        : repr_attr     (* Default Rust layout *)
  | ReprC           : repr_attr     (* C-compatible layout *)
  | ReprPacked      : repr_attr     (* No padding *)
  | ReprTransparent : repr_attr     (* Same as inner type *)
  | ReprAlign       : valid_alignment -> repr_attr  (* Aligned to n bytes, must be power of 2 *)

(** ============================================================================
    MODED TYPES (Type + Mode)
    ============================================================================ *)

(* A type annotated with its usage mode *)
noeq type moded_type = {
  ty   : brrr_type;
  mode : mode
}

(* Create moded type *)
let linear_type (t: brrr_type) : moded_type =
  { ty = t; mode = MOne }

let unrestricted_type (t: brrr_type) : moded_type =
  { ty = t; mode = MOmega }

(** ============================================================================
    TYPE SCHEMES (Polymorphism)
    ============================================================================ *)

(* Universally quantified type: ∀α₁...αₙ. τ *)
noeq type type_scheme = {
  type_vars   : list type_var;      (* Bound type variables *)
  effect_vars : list string;        (* Bound effect variables *)
  body        : brrr_type           (* The type body *)
}

(* Monomorphic type *)
let mono_type (t: brrr_type) : type_scheme =
  { type_vars = []; effect_vars = []; body = t }

(** ============================================================================
    TYPE CONSTRUCTORS - Convenience Aliases
    ============================================================================ *)

(* Primitive type aliases *)
let t_unit : brrr_type = TPrim PUnit
let t_never : brrr_type = TPrim PNever
let t_bool : brrr_type = TPrim PBool
let t_string : brrr_type = TPrim PString
let t_char : brrr_type = TPrim PChar
let t_dynamic : brrr_type = TPrim PDynamic
let t_unknown : brrr_type = TPrim PUnknown  (* Safe top type for gradual typing *)

(* Numeric type aliases *)
let t_i8 : brrr_type = TNumeric (NumInt i8)
let t_i16 : brrr_type = TNumeric (NumInt i16)
let t_i32 : brrr_type = TNumeric (NumInt i32)
let t_i64 : brrr_type = TNumeric (NumInt i64)
let t_u8 : brrr_type = TNumeric (NumInt u8)
let t_u16 : brrr_type = TNumeric (NumInt u16)
let t_u32 : brrr_type = TNumeric (NumInt u32)
let t_u64 : brrr_type = TNumeric (NumInt u64)
let t_f32 : brrr_type = TNumeric (NumFloat F32)
let t_f64 : brrr_type = TNumeric (NumFloat F64)

(* Wrapper type constructors *)
let t_array (t: brrr_type) : brrr_type = TWrap WArray t
let t_slice (t: brrr_type) : brrr_type = TWrap WSlice t
let t_option (t: brrr_type) : brrr_type = TWrap WOption t
let t_box (t: brrr_type) : brrr_type = TWrap WBox t
let t_ref (t: brrr_type) : brrr_type = TWrap WRef t
let t_ref_mut (t: brrr_type) : brrr_type = TWrap WRefMut t
let t_rc (t: brrr_type) : brrr_type = TWrap WRc t
let t_arc (t: brrr_type) : brrr_type = TWrap WArc t
let t_raw (t: brrr_type) : brrr_type = TWrap WRaw t

(* Modal type constructors *)
let t_box_mod (rk: ref_kind) (t: brrr_type) : brrr_type = TModal (MBoxMod rk) t
let t_diamond (t: brrr_type) : brrr_type = TModal MDiamondMod t

(* Legacy aliases for backward compatibility *)
let t_int (it: int_type) : brrr_type = TNumeric (NumInt it)
let t_float (fp: float_prec) : brrr_type = TNumeric (NumFloat fp)

(* Function type constructors *)
let t_func (params: list brrr_type) (ret: brrr_type) (eff: effect_row) : brrr_type =
  TFunc {
    params = List.Tot.map (fun t -> { name = None; ty = t; mode = MOmega }) params;
    return_type = ret;
    effects = eff;
    is_unsafe = false
  }

let t_pure_func (params: list brrr_type) (ret: brrr_type) : brrr_type =
  t_func params ret pure

(** ============================================================================
    TYPE EQUALITY - Simplified for 12 Constructors
    ============================================================================ *)

(* Helper: check if two lists of types are equal *)
let rec type_list_eq (ts1 ts2: list brrr_type) : Tot bool (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> true
  | t1 :: r1, t2 :: r2 -> type_eq t1 t2 && type_list_eq r1 r2
  | _, _ -> false

(* Helper: check if two param lists are equal *)
and param_list_eq (ps1: list param_type) (ps2: list param_type) : Tot bool (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> true
  | p1 :: r1, p2 :: r2 ->
      let p1_ty : brrr_type = Mkparam_type?.ty p1 in
      let p2_ty : brrr_type = Mkparam_type?.ty p2 in
      let p1_mode : mode = Mkparam_type?.mode p1 in
      let p2_mode : mode = Mkparam_type?.mode p2 in
      type_eq p1_ty p2_ty && p1_mode = p2_mode && param_list_eq r1 r2
  | _, _ -> false

(* Structural type equality - now much simpler with 12 constructors *)
and type_eq (t1 t2: brrr_type) : Tot bool (decreases t1) =
  match t1, t2 with
  (* Primitives: compare prim_kind *)
  | TPrim p1, TPrim p2 -> p1 = p2

  (* Numerics: use numeric_eq helper *)
  | TNumeric n1, TNumeric n2 -> numeric_eq n1 n2

  (* Wrappers: same wrapper_kind and equal inner types *)
  | TWrap w1 t1', TWrap w2 t2' -> w1 = w2 && type_eq t1' t2'

  (* Modal refs: use modal_eq helper and compare inner types *)
  | TModal m1 t1', TModal m2 t2' -> modal_eq m1 m2 && type_eq t1' t2'

  (* Result: compare both type parameters *)
  | TResult t1a t1b, TResult t2a t2b -> type_eq t1a t2a && type_eq t1b t2b

  (* Tuple: compare all elements *)
  | TTuple ts1, TTuple ts2 -> type_list_eq ts1 ts2

  (* Function: compare params, return, effects, unsafe flag *)
  | TFunc ft1, TFunc ft2 ->
      param_list_eq ft1.params ft2.params &&
      type_eq ft1.return_type ft2.return_type &&
      row_eq ft1.effects ft2.effects &&
      ft1.is_unsafe = ft2.is_unsafe

  (* Type variables: string equality *)
  | TVar v1, TVar v2 -> v1 = v2

  (* Type application: compare base and args *)
  | TApp t1' args1, TApp t2' args2 -> type_eq t1' t2' && type_list_eq args1 args2

  (* Named types: string equality *)
  | TNamed n1, TNamed n2 -> n1 = n2

  (* Struct and enum: nominal equality by name *)
  | TStruct st1, TStruct st2 -> st1.struct_name = st2.struct_name
  | TEnum et1, TEnum et2 -> et1.enum_name = et2.enum_name

  (* Different constructors are not equal *)
  | _, _ -> false

(** ============================================================================
    SUBTYPING - Simplified for 12 Constructors
    ============================================================================ *)

(* Subtyping relation: t1 <: t2 means t1 can be used where t2 is expected *)
let rec subtype (t1 t2: brrr_type) : bool =
  if type_eq t1 t2 then true
  else match t1, t2 with
  (* Never (via TPrim PNever) is subtype of everything - bottom type *)
  | TPrim PNever, _ -> true

  (* Everything is subtype of Dynamic (via TPrim PDynamic) - UNSAFE top type *)
  | _, TPrim PDynamic -> true

  (* Everything is subtype of Unknown (via TPrim PUnknown) - SAFE top type
     This is the key gradual typing rule: any concrete type can be "forgotten"
     to become Unknown, but using Unknown requires runtime type guards *)
  | _, TPrim PUnknown -> true

  (* Unknown is NOT a subtype of concrete types (requires explicit cast/guard)
     This is what makes Unknown "safe" unlike Dynamic which allows any operation *)
  | TPrim PUnknown, _ -> false

  (* Wrappers: covariance/invariance depends on wrapper_kind *)
  | TWrap w1 t1', TWrap w2 t2' ->
      w1 = w2 && (
        if wrapper_is_covariant w1 then subtype t1' t2'  (* Covariant *)
        else type_eq t1' t2'  (* Invariant (WRefMut) *)
      )

  (* Modal references - Chapter 9 *)
  | TModal m1 t1', TModal m2 t2' ->
      (match m1, m2 with
       (* □τ @ p ≤ □τ @ q iff p ≤ q and τ₁ ≤ τ₂ (covariant in type, permission can shrink) *)
       | MBoxMod rk1, MBoxMod rk2 ->
           frac_leq (ref_permission rk1) (ref_permission rk2) && subtype t1' t2'
       (* ◇τ is invariant in the type (exclusive/linear) *)
       | MDiamondMod, MDiamondMod -> type_eq t1' t2'
       (* ◇τ can become □τ @ p (freeze) where p = 1 (full permission) *)
       | MDiamondMod, MBoxMod rk ->
           is_full_perm (ref_permission rk) && subtype t1' t2'
       (* □τ cannot become ◇τ (would need to collect all shares) *)
       | MBoxMod _, MDiamondMod -> false)

  (* Result is covariant in both type parameters *)
  | TResult t1a t1b, TResult t2a t2b -> subtype t1a t2a && subtype t1b t2b

  (* Integer promotions: narrower can be promoted to wider of same sign *)
  | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
      (match width_bits i1.width, width_bits i2.width with
       | Some w1, Some w2 -> w1 <= w2 && i1.sign = i2.sign
       | _, _ -> false)

  (* No other subtyping relationships *)
  | _, _ -> false

(** ============================================================================
    TYPE EQUALITY LEMMAS - Simplified for 12 Constructors
    ============================================================================ *)

(* Mutually recursive lemmas for type_list_eq and type_eq reflexivity *)

(* Reflexivity lemmas with SMTPat triggers for automatic Z3 application *)
val type_list_eq_refl : ts:list brrr_type ->
  Lemma (ensures type_list_eq ts ts = true)
        (decreases ts)
        [SMTPat (type_list_eq ts ts)]

val param_list_eq_refl : ps:list param_type ->
  Lemma (ensures param_list_eq ps ps = true)
        (decreases ps)
        [SMTPat (param_list_eq ps ps)]

val type_eq_refl : t:brrr_type ->
  Lemma (ensures type_eq t t = true)
        (decreases t)
        [SMTPat (type_eq t t)]

let rec type_list_eq_refl ts =
  match ts with
  | [] -> ()
  | t :: rest -> type_eq_refl t; type_list_eq_refl rest

and param_list_eq_refl ps =
  match ps with
  | [] -> ()
  | p :: rest -> type_eq_refl (Mkparam_type?.ty p); param_list_eq_refl rest

(* With 12 constructors, type_eq_refl is now much simpler *)
and type_eq_refl t =
  match t with
  (* Primitives: decidable equality on prim_kind *)
  | TPrim _ -> ()
  (* Numerics: numeric_eq is reflexive *)
  | TNumeric _ -> ()
  (* Wrappers: recurse on inner type *)
  | TWrap _ t' -> type_eq_refl t'
  (* Modal: modal_eq is reflexive, recurse on inner *)
  | TModal _ t' -> type_eq_refl t'
  (* Result: recurse on both *)
  | TResult t1 t2 -> type_eq_refl t1; type_eq_refl t2
  (* Tuple: recurse on list *)
  | TTuple ts -> type_list_eq_refl ts
  (* Function: recurse *)
  | TFunc ft -> param_list_eq_refl ft.params; type_eq_refl ft.return_type; row_eq_refl ft.effects
  (* Type vars and named: decidable string equality *)
  | TVar _ -> ()
  | TNamed _ -> ()
  (* Type application: recurse *)
  | TApp t' args -> type_eq_refl t'; type_list_eq_refl args
  (* Struct/Enum: nominal by name *)
  | TStruct _ -> ()
  | TEnum _ -> ()

(* type_eq is symmetric - simplified for 12 constructors *)
val type_list_eq_sym : ts1:list brrr_type -> ts2:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true) (ensures type_list_eq ts2 ts1 = true) (decreases ts1)
val param_list_eq_sym : ps1:list param_type -> ps2:list param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true) (ensures param_list_eq ps2 ps1 = true) (decreases ps1)
val type_eq_sym : t1:brrr_type -> t2:brrr_type ->
  Lemma (requires type_eq t1 t2 = true) (ensures type_eq t2 t1 = true) (decreases t1)

let rec type_list_eq_sym ts1 ts2 =
  match ts1, ts2 with
  | [], [] -> ()
  | t1 :: r1, t2 :: r2 -> type_eq_sym t1 t2; type_list_eq_sym r1 r2
  | _, _ -> ()

and param_list_eq_sym ps1 ps2 =
  match ps1, ps2 with
  | [], [] -> ()
  | p1 :: r1, p2 :: r2 -> type_eq_sym (Mkparam_type?.ty p1) (Mkparam_type?.ty p2); param_list_eq_sym r1 r2
  | _, _ -> ()

(* With 12 constructors, symmetry proof is simpler *)
and type_eq_sym t1 t2 =
  match t1, t2 with
  (* Primitives: symmetric by definition *)
  | TPrim _, TPrim _ -> ()
  (* Numerics: symmetric by definition *)
  | TNumeric _, TNumeric _ -> ()
  (* Wrappers: recurse on inner *)
  | TWrap _ t1', TWrap _ t2' -> type_eq_sym t1' t2'
  (* Modal: recurse on inner *)
  | TModal _ t1', TModal _ t2' -> type_eq_sym t1' t2'
  (* Result: recurse on both *)
  | TResult t1a t1b, TResult t2a t2b -> type_eq_sym t1a t2a; type_eq_sym t1b t2b
  (* Tuple: recurse on list *)
  | TTuple ts1, TTuple ts2 -> type_list_eq_sym ts1 ts2
  (* Function: recurse *)
  | TFunc ft1, TFunc ft2 ->
      param_list_eq_sym ft1.params ft2.params;
      type_eq_sym ft1.return_type ft2.return_type;
      row_eq_sym ft1.effects ft2.effects
  (* Type vars: symmetric string equality *)
  | TVar _, TVar _ -> ()
  (* Named: symmetric string equality *)
  | TNamed _, TNamed _ -> ()
  (* Type app: recurse *)
  | TApp t1' args1, TApp t2' args2 -> type_eq_sym t1' t2'; type_list_eq_sym args1 args2
  (* Struct/Enum: symmetric by name *)
  | TStruct _, TStruct _ -> ()
  | TEnum _, TEnum _ -> ()
  (* Different constructors: vacuously true (precondition false) *)
  | _, _ -> ()

(* type_eq is transitive - MUCH SIMPLER with only 12 constructors!
   Z3 now only needs to consider 12^3 = 1,728 combinations instead of 27^3 = 19,683 *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val type_list_eq_trans : ts1:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true /\ type_list_eq ts2 ts3 = true)
        (ensures type_list_eq ts1 ts3 = true) (decreases ts1)
val param_list_eq_trans : ps1:list param_type -> ps2:list param_type -> ps3:list param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true /\ param_list_eq ps2 ps3 = true)
        (ensures param_list_eq ps1 ps3 = true) (decreases ps1)
val type_eq_trans : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t1 t2 = true /\ type_eq t2 t3 = true)
        (ensures type_eq t1 t3 = true) (decreases t1)

let rec type_list_eq_trans ts1 ts2 ts3 =
  match ts1, ts2, ts3 with
  | [], [], [] -> ()
  | t1 :: r1, t2 :: r2, t3 :: r3 -> type_eq_trans t1 t2 t3; type_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

and param_list_eq_trans ps1 ps2 ps3 =
  match ps1, ps2, ps3 with
  | [], [], [] -> ()
  | p1 :: r1, p2 :: r2, p3 :: r3 -> type_eq_trans (Mkparam_type?.ty p1) (Mkparam_type?.ty p2) (Mkparam_type?.ty p3); param_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

(* With only 12 constructors, transitivity proof is tractable *)
and type_eq_trans t1 t2 t3 =
  match t1, t2, t3 with
  (* Primitives: transitive by decidable equality *)
  | TPrim _, TPrim _, TPrim _ -> ()
  (* Numerics: transitive by decidable equality *)
  | TNumeric _, TNumeric _, TNumeric _ -> ()
  (* Wrappers: recurse on inner types *)
  | TWrap _ t1', TWrap _ t2', TWrap _ t3' -> type_eq_trans t1' t2' t3'
  (* Modal: frac_eq is transitive, recurse on inner *)
  | TModal (MBoxMod rk1) t1', TModal (MBoxMod rk2) t2', TModal (MBoxMod rk3) t3' ->
      frac_eq_trans (ref_permission rk1) (ref_permission rk2) (ref_permission rk3);
      type_eq_trans t1' t2' t3'
  | TModal MDiamondMod t1', TModal MDiamondMod t2', TModal MDiamondMod t3' ->
      type_eq_trans t1' t2' t3'
  (* Result: two type parameters *)
  | TResult t1a t1b, TResult t2a t2b, TResult t3a t3b ->
      type_eq_trans t1a t2a t3a;
      type_eq_trans t1b t2b t3b
  (* Tuple: delegate to list transitivity *)
  | TTuple ts1, TTuple ts2, TTuple ts3 -> type_list_eq_trans ts1 ts2 ts3
  (* Function: params, return, effects *)
  | TFunc ft1, TFunc ft2, TFunc ft3 ->
      param_list_eq_trans ft1.params ft2.params ft3.params;
      type_eq_trans ft1.return_type ft2.return_type ft3.return_type;
      row_eq_trans ft1.effects ft2.effects ft3.effects
  (* Type vars: transitive by string equality *)
  | TVar _, TVar _, TVar _ -> ()
  (* Named: transitive by string equality *)
  | TNamed _, TNamed _, TNamed _ -> ()
  (* Type app: recurse *)
  | TApp t1' args1, TApp t2' args2, TApp t3' args3 ->
      type_eq_trans t1' t2' t3';
      type_list_eq_trans args1 args2 args3
  (* Struct/Enum: transitive by name equality *)
  | TStruct _, TStruct _, TStruct _ -> ()
  | TEnum _, TEnum _, TEnum _ -> ()
  (* Different constructors: precondition is false, vacuously true *)
  | _, _, _ -> ()
#pop-options

(* Helper: type_eq t1 t = type_eq t2 t when type_eq t1 t2 = true
   Proof: If type_eq t1 t = true, then by symmetry type_eq t t1 = true,
   and by transitivity with type_eq t1 t2, we get type_eq t t2 = true,
   hence by symmetry type_eq t2 t = true.
   The converse holds by the same argument with symmetry of type_eq t1 t2. *)
val type_eq_left_eq : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq t1 t = type_eq t2 t)
let type_eq_left_eq t1 t2 t =
  if type_eq t1 t then begin
    type_eq_sym t1 t;
    type_eq_trans t t1 t2;
    type_eq_sym t t2
  end else if type_eq t2 t then begin
    type_eq_sym t2 t;
    type_eq_sym t1 t2;
    type_eq_trans t t2 t1;
    type_eq_sym t t1
  end else ()

(* If type_eq t1 t2 = true, then subtype t1 t = subtype t2 t for any t.
   Simplified for 12 constructors. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val type_eq_subtype_left : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures subtype t1 t = subtype t2 t) (decreases t1)
let rec type_eq_subtype_left t1 t2 t =
  type_eq_left_eq t1 t2 t;
  if type_eq t1 t then ()
  else match t1, t2 with
    (* Never: subtype PNever _ is always true *)
    | TPrim PNever, TPrim PNever -> ()
    (* Wrappers: covariant (except WRefMut which is invariant) *)
    | TWrap w1 t1', TWrap w2 t2' ->
        (match t with
         | TWrap w t' ->
             if w1 = w then
               if wrapper_is_covariant w1 then type_eq_subtype_left t1' t2' t'
               else type_eq_left_eq t1' t2' t'  (* Invariant case *)
             else ()
         | _ -> ())
    (* Modal: Diamond is invariant, BoxMod is covariant in type *)
    | TModal m1 t1', TModal m2 t2' ->
        (match t with
         | TModal m t' ->
             (match m1, m2, m with
              | MDiamondMod, MDiamondMod, MDiamondMod -> type_eq_left_eq t1' t2' t'
              | MDiamondMod, MDiamondMod, MBoxMod _ -> type_eq_subtype_left t1' t2' t'
              | MBoxMod _, MBoxMod _, MBoxMod _ -> type_eq_subtype_left t1' t2' t'
              | _, _, _ -> ())
         | _ -> ())
    (* Result: covariant in both type parameters *)
    | TResult t1a t1b, TResult t2a t2b ->
        (match t with
         | TResult ta tb ->
             type_eq_subtype_left t1a t2a ta;
             type_eq_subtype_left t1b t2b tb
         | _ -> ())
    (* Numerics: integer promotion *)
    | TNumeric _, TNumeric _ -> ()
    (* All others *)
    | _, _ -> ()
#pop-options

(* Helper: type_eq t t2 = type_eq t t3 when type_eq t2 t3 = true (right version) *)
val type_eq_right_eq : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures type_eq t t2 = type_eq t t3)
let type_eq_right_eq t t2 t3 =
  if type_eq t t2 then begin
    type_eq_trans t t2 t3
  end else if type_eq t t3 then begin
    type_eq_sym t2 t3;
    type_eq_trans t t3 t2
  end else ()

(* If type_eq t2 t3 = true, then subtype t t2 = subtype t t3 for any t.
   Simplified for 12 constructors. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val type_eq_subtype_right : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures subtype t t2 = subtype t t3) (decreases t)
let rec type_eq_subtype_right t t2 t3 =
  type_eq_right_eq t t2 t3;
  if type_eq t t2 then ()
  else match t with
    (* Never: subtype PNever _ = true *)
    | TPrim PNever -> ()
    (* Wrappers: covariant (except WRefMut) *)
    | TWrap w t' ->
        (match t2, t3 with
         | TWrap w2 t2', TWrap w3 t3' ->
             if w = w2 then
               if wrapper_is_covariant w then type_eq_subtype_right t' t2' t3'
               else type_eq_right_eq t' t2' t3'  (* Invariant *)
             else ()
         | _, _ -> ())
    (* Modal: Diamond invariant, BoxMod covariant in type *)
    | TModal m t' ->
        (match t2, t3 with
         | TModal m2 t2', TModal m3 t3' ->
             (match m, m2 with
              | MDiamondMod, MDiamondMod -> type_eq_right_eq t' t2' t3'
              | MDiamondMod, MBoxMod _ -> type_eq_subtype_right t' t2' t3'
              | MBoxMod _, MBoxMod _ -> type_eq_subtype_right t' t2' t3'
              | _, _ -> ())
         | _, _ -> ())
    (* Result: covariant in both type parameters *)
    | TResult ta tb ->
        (match t2, t3 with
         | TResult t2a t2b, TResult t3a t3b ->
             type_eq_subtype_right ta t2a t3a;
             type_eq_subtype_right tb t2b t3b
         | _, _ -> ())
    (* Numerics: integer promotion *)
    | TNumeric _ -> ()
    (* All others *)
    | _ -> ()
#pop-options

(* subtype is reflexive *)
(* Subtype reflexivity with SMTPat trigger *)
val subtype_refl : t:brrr_type ->
  Lemma (ensures subtype t t = true)
        (decreases t)
        [SMTPat (subtype t t)]
let subtype_refl t = type_eq_refl t

(** ============================================================================
    WRAPPER AND SUBSTITUTION LEMMAS
    ============================================================================ *)

(* Wrapper covariant subtype: for covariant wrappers, inner subtype implies outer subtype.
   This is a key lemma for type-safe coercions through wrapper types.

   Proof: By definition of subtype on TWrap:
   - If wrapper_is_covariant w = true, then subtype (TWrap w t1) (TWrap w t2)
     reduces to subtype t1 t2.
   - The lemma provides the forward direction for covariant wrappers. *)
#push-options "--fuel 1"
val wrapper_covariant_subtype : w:wrapper_kind -> t1:brrr_type -> t2:brrr_type ->
  Lemma (requires wrapper_is_covariant w = true /\ subtype t1 t2 = true)
        (ensures subtype (TWrap w t1) (TWrap w t2) = true)
        [SMTPat (subtype (TWrap w t1) (TWrap w t2))]
let wrapper_covariant_subtype w t1 t2 =
  (* Direct from subtype definition: TWrap w t1 <: TWrap w t2 when
     w = w (trivial) and wrapper_is_covariant w implies subtype t1 t2 *)
  ()
#pop-options

(* Substitution preserves type equality.
   If t1 and t2 are equal, then substituting the same variable with the same
   replacement in both yields equal types.

   Proof: By structural induction on t1. Since type_eq t1 t2 = true implies
   t1 and t2 have the same structure (including at each recursive position),
   substitution proceeds identically in both, yielding structurally equal results. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
val subst_type_var_preserves_eq : v:type_var -> repl:brrr_type -> t1:brrr_type -> t2:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq (subst_type_var v repl t1) (subst_type_var v repl t2) = true)
        (decreases %[type_size t1; 0])
let rec subst_type_var_preserves_eq v repl t1 t2 =
  match t1, t2 with
  | TVar v1, TVar v2 ->
      (* type_eq implies v1 = v2, so subst result is the same *)
      ()
  | TPrim _, TPrim _ -> ()
  | TNumeric _, TNumeric _ -> ()
  | TWrap w1 inner1, TWrap w2 inner2 ->
      (* type_eq implies w1 = w2 and type_eq inner1 inner2 *)
      subst_type_var_preserves_eq v repl inner1 inner2
  | TModal m1 inner1, TModal m2 inner2 ->
      subst_type_var_preserves_eq v repl inner1 inner2
  | TResult t1a t1b, TResult t2a t2b ->
      subst_type_var_preserves_eq v repl t1a t2a;
      subst_type_var_preserves_eq v repl t1b t2b
  | TTuple ts1, TTuple ts2 ->
      subst_type_list_preserves_eq v repl ts1 ts2
  | TFunc ft1, TFunc ft2 ->
      subst_param_list_preserves_eq v repl ft1.params ft2.params;
      subst_type_var_preserves_eq v repl ft1.return_type ft2.return_type
  | TNamed _, TNamed _ -> ()
  | TApp base1 args1, TApp base2 args2 ->
      subst_type_var_preserves_eq v repl base1 base2;
      subst_type_list_preserves_eq v repl args1 args2
  | TStruct _, TStruct _ -> ()
  | TEnum _, TEnum _ -> ()
  | _, _ -> ()  (* Mismatched constructors: precondition false *)

and subst_type_list_preserves_eq (v: type_var) (repl: brrr_type) (ts1 ts2: list brrr_type)
    : Lemma (requires type_list_eq ts1 ts2 = true)
            (ensures type_list_eq (subst_type_list v repl ts1) (subst_type_list v repl ts2) = true)
            (decreases %[type_list_size ts1; 1]) =
  match ts1, ts2 with
  | [], [] -> ()
  | t1 :: rest1, t2 :: rest2 ->
      subst_type_var_preserves_eq v repl t1 t2;
      subst_type_list_preserves_eq v repl rest1 rest2
  | _, _ -> ()

and subst_param_list_preserves_eq (v: type_var) (repl: brrr_type) (ps1 ps2: list param_type)
    : Lemma (requires param_list_eq ps1 ps2 = true)
            (ensures param_list_eq (subst_param_list v repl ps1) (subst_param_list v repl ps2) = true)
            (decreases %[param_list_size ps1; 1]) =
  match ps1, ps2 with
  | [], [] -> ()
  | p1 :: rest1, p2 :: rest2 ->
      subst_type_var_preserves_eq v repl p1.ty p2.ty;
      subst_param_list_preserves_eq v repl rest1 rest2
  | _, _ -> ()
#pop-options

(** ============================================================================
    TYPE SIZE FUNCTIONS - Simplified for 12 Constructors
    ============================================================================ *)

(* Size of a type - used for termination measures in recursive functions *)
let rec type_size (t: brrr_type) : Tot nat (decreases t) =
  match t with
  (* Primitives: size 1 *)
  | TPrim _ -> 1
  (* Numerics: size 1 *)
  | TNumeric _ -> 1
  (* Wrappers: 1 + inner size *)
  | TWrap _ t' -> 1 + type_size t'
  (* Modal: 1 + inner size *)
  | TModal _ t' -> 1 + type_size t'
  (* Result: 1 + both parameters *)
  | TResult t1 t2 -> 1 + type_size t1 + type_size t2
  (* Tuple: 1 + sum of elements *)
  | TTuple ts -> 1 + type_list_size ts
  (* Function: 1 + params + return *)
  | TFunc ft -> 1 + param_list_size ft.params + type_size ft.return_type
  (* Type var: size 1 *)
  | TVar _ -> 1
  (* Named: size 1 *)
  | TNamed _ -> 1
  (* Type app: 1 + base + args *)
  | TApp t' args -> 1 + type_size t' + type_list_size args
  (* Struct: 1 + fields *)
  | TStruct st -> 1 + field_list_size st.struct_fields
  (* Enum: 1 + variants *)
  | TEnum et -> 1 + variant_list_size et.enum_variants

and type_list_size (ts: list brrr_type) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | t :: rest -> type_size t + type_list_size rest

and param_list_size (ps: list param_type) : Tot nat (decreases ps) =
  match ps with
  | [] -> 0
  | p :: rest -> type_size (Mkparam_type?.ty p) + param_list_size rest

and field_list_size (fs: list field_type) : Tot nat (decreases fs) =
  match fs with
  | [] -> 0
  | f :: rest -> type_size f.field_ty + field_list_size rest

and variant_list_size (vs: list variant_type) : Tot nat (decreases vs) =
  match vs with
  | [] -> 0
  | v :: rest -> type_list_size v.variant_fields + variant_list_size rest

(** ============================================================================
    SUBTYPE TRANSITIVITY
    ============================================================================ *)

(* Helper: transitivity for integer width ordering *)
val int_width_trans : w1:int_width -> w2:int_width -> w3:int_width ->
  Lemma (requires (match width_bits w1, width_bits w2 with Some a, Some b -> a <= b | _ -> false) /\
                  (match width_bits w2, width_bits w3 with Some b, Some c -> b <= c | _ -> false))
        (ensures (match width_bits w1, width_bits w3 with Some a, Some c -> a <= c | _ -> false))
let int_width_trans w1 w2 w3 = ()

(* Main transitivity lemma for the basic subtype function *)
(* Helper: check if type is TNever (now TPrim PNever) - bottom type *)
let is_never (t: brrr_type) : bool =
  match t with TPrim PNever -> true | _ -> false

(* Helper: check if type is TDynamic (now TPrim PDynamic) - unsafe top type *)
let is_dynamic (t: brrr_type) : bool =
  match t with TPrim PDynamic -> true | _ -> false

(* Helper: check if type is TUnknown (now TPrim PUnknown) - safe top type
   For gradual typing: Unknown requires runtime checks before operations *)
let is_unknown (t: brrr_type) : bool =
  match t with TPrim PUnknown -> true | _ -> false

(* Helper: check if type is any top type (Dynamic or Unknown) *)
let is_top_type (t: brrr_type) : bool =
  is_dynamic t || is_unknown t

(* Helper: extract inner subtype fact from Diamond->Box *)
val subtype_diamond_box_inner : t1':brrr_type -> rk:ref_kind -> t2':brrr_type ->
  Lemma (requires subtype (TModal MDiamondMod t1') (TModal (MBoxMod rk) t2') = true)
        (ensures subtype t1' t2' = true)
let subtype_diamond_box_inner t1' rk t2' = ()

(* Helper: extract inner subtype fact from Box->Box when not type_eq *)
val subtype_box_box_inner : rk1:ref_kind -> t1':brrr_type -> rk2:ref_kind -> t2':brrr_type ->
  Lemma (requires subtype (TModal (MBoxMod rk1) t1') (TModal (MBoxMod rk2) t2') = true /\
                  type_eq (TModal (MBoxMod rk1) t1') (TModal (MBoxMod rk2) t2') = false)
        (ensures subtype t1' t2' = true)
let subtype_box_box_inner rk1 t1' rk2 t2' = ()

(* Helper: Full permission is preserved under frac_leq in the (0,1] permission range.
   The fraction type now enforces frac_num <= frac_den via valid_frac, making this
   formally provable.

   Proof:
   Given: is_full_perm f1 => f1.frac_num = f1.frac_den (call this d1)
          frac_leq f1 f2 => f1.frac_num * f2.frac_den <= f2.frac_num * f1.frac_den
   Substituting: d1 * f2.frac_den <= f2.frac_num * d1
   Since d1 > 0, divide: f2.frac_den <= f2.frac_num
   From valid_frac f2: f2.frac_num <= f2.frac_den
   Combining: f2.frac_num = f2.frac_den, hence is_full_perm f2 *)
#push-options "--z3rlimit 300 --z3cliopt smt.arith.nl=true"
val full_perm_leq_preserves_full : f1:fraction -> f2:fraction ->
  Lemma (requires is_full_perm f1 = true /\ frac_leq f1 f2 = true)
        (ensures is_full_perm f2 = true)
let full_perm_leq_preserves_full f1 f2 =
  (* Extract the invariant from the refined type: f2.frac_num <= f2.frac_den *)
  assert (valid_frac f2);
  (* The SMT solver can derive from:
     1. is_full_perm f1: f1.frac_num = f1.frac_den
     2. frac_leq f1 f2: f1.frac_num * f2.frac_den <= f2.frac_num * f1.frac_den
     3. valid_frac f2: f2.frac_num <= f2.frac_den
     That: f2.frac_num = f2.frac_den *)
  ()
#pop-options

(* Subtype transitivity - MUCH SIMPLER with 12 constructors!
   Z3 now only needs 12^3 = 1,728 combinations instead of 27^3 = 19,683 *)
#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"
val subtype_trans : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires subtype t1 t2 = true /\ subtype t2 t3 = true)
        (ensures subtype t1 t3 = true)
        (decreases t1)
let rec subtype_trans t1 t2 t3 =
  (* Handle type_eq cases first *)
  if type_eq t1 t2 then begin
    type_eq_subtype_left t1 t2 t3
  end
  else if type_eq t2 t3 then begin
    type_eq_subtype_right t1 t2 t3
  end
  else
    (* Both type_eq checks false - match structural cases *)
    match t1, t2, t3 with
    (* Bottom type: subtype PNever _ = true *)
    | TPrim PNever, _, _ -> ()
    (* Top type: subtype _ PDynamic = true *)
    | _, _, TPrim PDynamic -> ()
    | _, TPrim PDynamic, _ -> ()

    (* Wrappers: covariant (except WRefMut) *)
    | TWrap w1 t1', TWrap w2 t2', TWrap w3 t3' ->
        if wrapper_is_covariant w1 then subtype_trans t1' t2' t3'
        else type_eq_trans t1' t2' t3'  (* Invariant case *)

    (* Modal references *)
    | TModal (MBoxMod rk1) t1', TModal (MBoxMod rk2) t2', TModal (MBoxMod rk3) t3' ->
        frac_leq_trans (ref_permission rk1) (ref_permission rk2) (ref_permission rk3);
        subtype_trans t1' t2' t3'

    | TModal MDiamondMod t1', TModal MDiamondMod t2', TModal MDiamondMod t3' ->
        type_eq_trans t1' t2' t3'

    | TModal MDiamondMod t1', TModal MDiamondMod t2', TModal (MBoxMod _) t3' ->
        type_eq_subtype_left t1' t2' t3'

    | TModal MDiamondMod t1', TModal (MBoxMod rk2) t2', TModal (MBoxMod rk3) t3' ->
        subtype_diamond_box_inner t1' rk2 t2';
        subtype_box_box_inner rk2 t2' rk3 t3';
        full_perm_leq_preserves_full (ref_permission rk2) (ref_permission rk3);
        if type_eq t1' t2' then type_eq_subtype_left t1' t2' t3'
        else if type_eq t2' t3' then type_eq_subtype_right t1' t2' t3'
        else subtype_trans t1' t2' t3'

    (* Result: covariant in both *)
    | TResult t1a t1b, TResult t2a t2b, TResult t3a t3b ->
        subtype_trans t1a t2a t3a;
        subtype_trans t1b t2b t3b

    (* Integer promotion: transitive *)
    | TNumeric (NumInt i1), TNumeric (NumInt i2), TNumeric (NumInt i3) ->
        int_width_trans i1.width i2.width i3.width

    (* All other patterns: mismatched constructors, vacuously true *)
    | _, _, _ -> ()
#pop-options

(** ============================================================================
    TYPE SUBSTITUTION - Simplified for 12 Constructors
    ============================================================================ *)

(* Substitute type variable with a type - mutually recursive with list helpers *)
let rec subst_type_var (v: type_var) (replacement: brrr_type) (t: brrr_type)
    : Tot brrr_type (decreases %[type_size t; 0]) =
  match t with
  (* Type variable: substitute if matches *)
  | TVar v' -> if v = v' then replacement else t
  (* Primitives: no substitution *)
  | TPrim _ -> t
  (* Numerics: no substitution *)
  | TNumeric _ -> t
  (* Wrappers: substitute in inner type *)
  | TWrap w t' -> TWrap w (subst_type_var v replacement t')
  (* Modal: substitute in inner type *)
  | TModal m t' -> TModal m (subst_type_var v replacement t')
  (* Result: substitute in both *)
  | TResult t1 t2 -> TResult (subst_type_var v replacement t1)
                             (subst_type_var v replacement t2)
  (* Tuple: substitute in list *)
  | TTuple ts -> TTuple (subst_type_list v replacement ts)
  (* Function: substitute in params and return *)
  | TFunc ft -> TFunc { ft with
      params = subst_param_list v replacement ft.params;
      return_type = subst_type_var v replacement ft.return_type
    }
  (* Named: no substitution *)
  | TNamed _ -> t
  (* Type app: substitute in base and args *)
  | TApp t' args -> TApp (subst_type_var v replacement t')
                         (subst_type_list v replacement args)
  (* Struct/Enum: no substitution (nominal types) *)
  | TStruct _ -> t
  | TEnum _ -> t

and subst_type_list (v: type_var) (replacement: brrr_type) (ts: list brrr_type)
    : Tot (list brrr_type) (decreases %[type_list_size ts; 1]) =
  match ts with
  | [] -> []
  | t :: rest -> subst_type_var v replacement t :: subst_type_list v replacement rest

and subst_param_list (v: type_var) (replacement: brrr_type) (ps: list param_type)
    : Tot (list param_type) (decreases %[param_list_size ps; 1]) =
  match ps with
  | [] -> []
  | p :: rest ->
      { name = Mkparam_type?.name p; ty = subst_type_var v replacement (Mkparam_type?.ty p); mode = Mkparam_type?.mode p }
      :: subst_param_list v replacement rest

(* Instantiate type scheme with concrete types *)
let instantiate (scheme: type_scheme) (type_args: list brrr_type)
    : option brrr_type =
  if List.Tot.length scheme.type_vars <> List.Tot.length type_args then None
  else
    let bindings = zip_lists scheme.type_vars type_args in
    let folder t binding =
      match binding with
      | (v, r) -> subst_type_var v r t
    in
    Some (List.Tot.fold_left folder scheme.body bindings)

(** ============================================================================
    FREE VARIABLES - Simplified for 12 Constructors
    ============================================================================ *)

(* Collect free type variables - mutually recursive with list helpers *)
let rec free_type_vars (t: brrr_type) : Tot (list type_var) (decreases %[type_size t; 0]) =
  match t with
  (* Type variable: return it *)
  | TVar v -> [v]
  (* Primitives: no free vars *)
  | TPrim _ -> []
  (* Numerics: no free vars *)
  | TNumeric _ -> []
  (* Wrappers: recurse on inner *)
  | TWrap _ t' -> free_type_vars t'
  (* Modal: recurse on inner *)
  | TModal _ t' -> free_type_vars t'
  (* Result: recurse on both *)
  | TResult t1 t2 -> free_type_vars t1 @ free_type_vars t2
  (* Tuple: recurse on list *)
  | TTuple ts -> free_type_vars_list ts
  (* Function: params and return *)
  | TFunc ft -> free_type_vars_params ft.params @ free_type_vars ft.return_type
  (* Named: no free vars (nominal) *)
  | TNamed _ -> []
  (* Type app: base and args *)
  | TApp t' args -> free_type_vars t' @ free_type_vars_list args
  (* Struct/Enum: no free vars (nominal) *)
  | TStruct _ -> []
  | TEnum _ -> []

and free_type_vars_list (ts: list brrr_type) : Tot (list type_var) (decreases %[type_list_size ts; 1]) =
  match ts with
  | [] -> []
  | t :: rest -> free_type_vars t @ free_type_vars_list rest

and free_type_vars_params (ps: list param_type) : Tot (list type_var) (decreases %[param_list_size ps; 1]) =
  match ps with
  | [] -> []
  | p :: rest -> free_type_vars (Mkparam_type?.ty p) @ free_type_vars_params rest

(* Is type closed (no free variables)? *)
let is_closed (t: brrr_type) : bool =
  List.Tot.isEmpty (free_type_vars t)

(** ============================================================================
    REGION TYPES - Chapter 4 (Ownership & Memory)
    ============================================================================

    Region types annotate base types with lifetime/scope information:
      tau @ rho  =  type tau allocated in region rho

    Regions form a lattice with outlives ordering:
      rho1 <= rho2  means  rho1 outlives (includes) rho2
      'static <= all regions (static outlives everything)
    ============================================================================ *)

(* Region identifier - canonical definition used across all modules *)
type region =
  | RStatic : region                  (* 'static - lives forever *)
  | RNamed  : string -> region        (* Named region variable like 'a *)
  | RFresh  : nat -> region           (* Fresh region from letregion *)
  | RScope  : nat -> region           (* Tied to lexical scope depth *)

(* Region equality *)
let region_eq (r1 r2: region) : bool =
  match r1, r2 with
  | RStatic, RStatic -> true
  | RNamed n1, RNamed n2 -> n1 = n2
  | RFresh n1, RFresh n2 -> n1 = n2
  | RScope d1, RScope d2 -> d1 = d2
  | _, _ -> false

(* Region ordering: r1 outlives r2 (r1 <= r2)
   Meaning: r1's scope includes r2's scope *)
let region_outlives (r1 r2: region) : bool =
  match r1, r2 with
  | RStatic, _ -> true                   (* Static outlives everything *)
  | RNamed a, RNamed b -> a = b          (* Same region *)
  | RFresh n1, RFresh n2 -> n1 <= n2     (* Earlier fresh = longer lived *)
  | RScope d1, RScope d2 -> d1 <= d2     (* Lower depth = longer lived *)
  | RScope _, RFresh _ -> false          (* Scope doesn't outlive fresh *)
  | RFresh _, RScope _ -> false          (* Fresh doesn't outlive scope *)
  | _, RStatic -> false                  (* Nothing outlives static except static *)

(* Type with region annotation: tau @ rho
   Keeps the core brrr_type separate for SMT tractability *)
noeq type regioned_type = {
  base_type : brrr_type;
  region    : region
}

(* Create regioned type with static lifetime *)
let static_type (t: brrr_type) : regioned_type =
  { base_type = t; region = RStatic }

(* Create regioned type with named lifetime *)
let lifetime_type (t: brrr_type) (lifetime: string) : regioned_type =
  { base_type = t; region = RNamed lifetime }

(* Regioned type subtyping: tau1 @ rho1 <: tau2 @ rho2 iff
   tau1 <: tau2 AND rho1 outlives rho2 *)
let regioned_subtype (rt1 rt2: regioned_type) : bool =
  subtype rt1.base_type rt2.base_type && region_outlives rt1.region rt2.region

(* Check if region escapes a type (appears free in type's structure)
   Used for letregion scoping checks.

   TODO: IMPLEMENT - Currently returns false as regions are tracked externally.
   When region annotations are added to brrr_type (e.g., TRef with lifetime),
   this function should recursively check:
   1. TWrap WRef/WRefMut - check if the inner reference carries region r
   2. TModal - check modal references for region annotations
   3. TFunc - check if return type or captured closures escape region
   4. TStruct/TEnum - check fields/variants for escaped regions

   See: brrr_lang_spec_v0.4.tex Section 4.3 (Region Escape Analysis)

   Current workaround: Regions are tracked via regioned_type wrapper,
   not embedded in brrr_type itself. This simplifies SMT reasoning but
   requires external tracking of lifetime bounds.
*)
let rec region_escapes (r: region) (t: brrr_type) : Tot bool (decreases type_size t) =
  match t with
  (* Wrappers: recursively check inner type *)
  | TWrap _ inner -> region_escapes r inner
  | TModal _ inner -> region_escapes r inner
  | TResult t1 t2 -> region_escapes r t1 || region_escapes r t2
  | TTuple ts -> List.Tot.existsb (region_escapes r) ts
  | TFunc ft ->
      (* Check return type and all parameter types *)
      region_escapes r ft.return_type ||
      List.Tot.existsb (fun p -> region_escapes r p.ty) ft.params
  | TApp base args ->
      region_escapes r base || List.Tot.existsb (region_escapes r) args
  (* Base cases: no region information in current design *)
  | TPrim _ -> false
  | TNumeric _ -> false
  | TVar _ -> false
  | TNamed _ -> false
  | TStruct _ -> false  (* TODO: check struct fields when regions are embedded *)
  | TEnum _ -> false    (* TODO: check enum variants when regions are embedded *)

(** ============================================================================
    TYPE SCHEME INSTANTIATION WITH EFFECT VARIABLES
    ============================================================================ *)

(* Full instantiation: handles both type variables and effect variables

   A type scheme forall a1..an, e1..em. tau can be instantiated by:
   1. Providing concrete types for type variables a1..an
   2. Providing concrete effect rows for effect variables e1..em

   Effect substitution is applied to function types in the scheme body. *)
let instantiate_full (scheme: type_scheme)
                     (type_args: list brrr_type)
                     (effect_args: list effect_row)
    : option brrr_type =
  (* Check arity matches *)
  if List.Tot.length scheme.type_vars <> List.Tot.length type_args then None
  else if List.Tot.length scheme.effect_vars <> List.Tot.length effect_args then None
  else
    (* Step 1: Substitute type variables *)
    let type_bindings = zip_lists scheme.type_vars type_args in
    let subst_types t =
      List.Tot.fold_left (fun ty (v, r) -> subst_type_var v r ty) t type_bindings
    in
    let body_with_types = subst_types scheme.body in

    (* Step 2: Substitute effect variables in function types
       This requires a recursive traversal to find all TFunc types *)
    let effect_bindings = zip_lists scheme.effect_vars effect_args in
    let subst_effects_in_row row =
      List.Tot.fold_left (fun r (v, repl) -> subst_effect_var v repl r) row effect_bindings
    in

    (* Effect substitution in types - traverse and update TFunc effects *)
    let rec subst_effects_in_type (t: brrr_type) : Tot brrr_type (decreases type_size t) =
      match t with
      | TFunc ft ->
          (* Explicitly construct param_type to avoid ambiguity with moded_type *)
          let subst_param (p: param_type) : param_type =
            { name = p.name; ty = subst_effects_in_type p.ty; mode = p.mode }
          in
          TFunc { ft with
            effects = subst_effects_in_row ft.effects;
            return_type = subst_effects_in_type ft.return_type;
            params = List.Tot.map subst_param ft.params
          }
      | TWrap w t' -> TWrap w (subst_effects_in_type t')
      | TModal m t' -> TModal m (subst_effects_in_type t')
      | TResult t1 t2 -> TResult (subst_effects_in_type t1) (subst_effects_in_type t2)
      | TTuple ts -> TTuple (List.Tot.map subst_effects_in_type ts)
      | TApp t' args -> TApp (subst_effects_in_type t') (List.Tot.map subst_effects_in_type args)
      | _ -> t  (* Primitives, numerics, vars, named, struct, enum unchanged *)
    in

    Some (subst_effects_in_type body_with_types)

(** ============================================================================
    TYPE UTILITY FUNCTIONS FOR ANALYSIS
    ============================================================================ *)

(* is_nullable: Check if a type represents a nullable/optional value
   Used by Brrr-Machine for null pointer analysis (Section 2.1.7) *)
let is_nullable (t: brrr_type) : bool =
  match t with
  | TWrap WOption _ -> true           (* Option<T> is nullable *)
  | TResult _ _ -> true               (* Result<T,E> can be Err (similar to null) *)
  | TPrim PDynamic -> true            (* Dynamic can be null in some languages *)
  | TPrim PUnknown -> true            (* Unknown could be null *)
  | _ -> false

(* is_owned: Check if a type represents owned (non-borrowed) data
   Used for ownership analysis and move semantics *)
let is_owned (t: brrr_type) : bool =
  match t with
  (* References and borrows are not owned *)
  | TWrap WRef _ -> false             (* &T - shared borrow *)
  | TWrap WRefMut _ -> false          (* &mut T - exclusive borrow *)
  | TWrap WRaw _ -> false             (* *T - raw pointer, not owned semantically *)

  (* These represent owned data *)
  | TWrap WBox _ -> true              (* Box<T> - owned heap allocation *)
  | TWrap WArray _ -> true            (* [T] - owned array *)
  | TWrap WOption _ -> true           (* Option<T> - owned optional *)
  | TWrap WSlice _ -> false           (* &[T] - slice is a borrowed view *)
  | TWrap WRc _ -> true               (* Rc<T> - shared ownership *)
  | TWrap WArc _ -> true              (* Arc<T> - shared ownership *)

  (* Modal references follow the modality *)
  | TModal MDiamondMod _ -> true      (* Diamond: exclusive/owned *)
  | TModal (MBoxMod rk) _ ->          (* Box with fraction: owned if full perm *)
      is_full_perm (ref_permission rk)

  (* Base types are considered owned *)
  | TPrim _ -> true
  | TNumeric _ -> true
  | TTuple _ -> true
  | TStruct _ -> true
  | TEnum _ -> true
  | TResult _ _ -> true
  | TFunc _ -> true                   (* Function pointers are owned values *)
  | TVar _ -> true                    (* Assume type vars are owned by default *)
  | TNamed _ -> true                  (* Named types are owned by default *)
  | TApp _ _ -> true                  (* Applied types are owned by default *)

(* get_inner_type: Extract the inner type from wrapper types
   Returns None for non-wrapper types
   Used by Brrr-Machine for type analysis and unwrapping *)
let get_inner_type (t: brrr_type) : option brrr_type =
  match t with
  (* Single-type wrappers *)
  | TWrap _ inner -> Some inner
  | TModal _ inner -> Some inner

  (* For Result, return the success type (first type parameter) *)
  | TResult ok_type _ -> Some ok_type

  (* Type application: return the base type (the functor) *)
  | TApp base _ -> Some base

  (* Non-wrappers return None *)
  | _ -> None

(* get_error_type: For Result types, get the error type (second parameter)
   Returns None for non-Result types *)
let get_error_type (t: brrr_type) : option brrr_type =
  match t with
  | TResult _ err_type -> Some err_type
  | _ -> None

(* unwrap_all: Recursively unwrap all wrapper types to get the innermost type
   e.g., Option<Box<&T>> -> T *)
let rec unwrap_all (t: brrr_type) : Tot brrr_type (decreases type_size t) =
  match get_inner_type t with
  | Some inner -> unwrap_all inner
  | None -> t

(* is_reference_type: Check if type is any kind of reference/borrow *)
let is_reference_type (t: brrr_type) : bool =
  match t with
  | TWrap WRef _ -> true
  | TWrap WRefMut _ -> true
  | TWrap WRaw _ -> true
  | TWrap WSlice _ -> true            (* Slices are borrowed views *)
  | TModal (MBoxMod _) _ -> true      (* Box modality is shared ref *)
  | _ -> false

(* is_mutable_reference: Check if type allows mutation through it *)
let is_mutable_reference (t: brrr_type) : bool =
  match t with
  | TWrap WRefMut _ -> true           (* &mut T *)
  | TModal MDiamondMod _ -> true      (* Diamond allows exclusive access *)
  | TModal (MBoxMod rk) _ ->          (* Box with full permission allows write *)
      is_full_perm (ref_permission rk)
  | _ -> false

(* requires_runtime_check: Check if operations on this type need runtime checks
   Used by Brrr-Machine for gradual typing analysis *)
let requires_runtime_check (t: brrr_type) : bool =
  match t with
  | TPrim PUnknown -> true            (* Unknown requires runtime type guards *)
  | TPrim PDynamic -> true            (* Dynamic should have runtime checks (but often doesn't) *)
  | TWrap WOption _ -> true           (* Option requires Some/None check *)
  | TResult _ _ -> true               (* Result requires Ok/Err check *)
  | _ -> false

(* get_pointee_type: For pointer/reference types, get what they point to *)
let get_pointee_type (t: brrr_type) : option brrr_type =
  match t with
  | TWrap WRef inner -> Some inner
  | TWrap WRefMut inner -> Some inner
  | TWrap WRaw inner -> Some inner
  | TWrap WBox inner -> Some inner
  | TWrap WRc inner -> Some inner
  | TWrap WArc inner -> Some inner
  | TModal _ inner -> Some inner
  | _ -> None
