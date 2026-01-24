(**
 * BrrrLang.Core.Types - Interface
 *
 * Public interface for the Brrr-Lang type system.
 * Based on brrr_lang_spec_v0.4.tex Parts II-III.
 *
 * This interface follows HACL*/EverParse patterns:
 *   - unfold for simple type aliases (enables inlining for verification)
 *   - inline_for_extraction for extracted type constructors (C/Rust extraction)
 *   - [@(strict_on_arguments [n])] for strict argument evaluation
 *   - val declarations with refinement types and pre/post conditions
 *   - SMTPat triggers for automatic lemma application by Z3
 *
 * Key design decisions:
 *   - 12 type constructors (reduced from 27) for SMT tractability
 *   - noeq for recursive types (equality not decidable on function types)
 *   - Termination measures via type_size for recursive functions
 *
 * Depends on: Primitives, Modes, Effects
 *)
module BrrrTypes

open Primitives
open Modes
open Effects
open FStar.List.Tot

(* Z3 solver options for SMT tractability - following HACL*/EverParse patterns
   - z3rlimit 50: reasonable timeout for most proofs
   - fuel 0: disable recursive function unfolding by default
   - ifuel 0: disable inductive type unfolding by default *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    TYPE IDENTIFIERS - Simple unfold aliases for efficient verification
    ============================================================================ *)

(* Type variable identifier - used in polymorphic types (forall a. ...)
   Exposed as unfold to allow direct string operations in proofs *)
unfold
type type_var = string

(* Named type reference - for nominal types (struct Foo, enum Bar)
   Exposed as unfold for nominal equality checks *)
unfold
type type_name = string

(* Type interning ID - for efficient type comparison in large codebases
   Exposed as unfold for nat operations *)
unfold
type type_id = nat

(** ============================================================================
    TYPE DISCRIMINATORS - Grouped variants for SMT tractability

    These discriminators reduce Z3 proof complexity from 27^3 = 19,683
    combinations to 12^3 = 1,728 combinations for transitivity proofs.
    ============================================================================ *)

(* Primitive type kinds - 7 variants for unit, never, bool, string, char, dynamic, unknown
   Full definition exposed for pattern matching in client code *)
type prim_kind =
  | PUnit   : prim_kind   (* () - unit type, single inhabitant *)
  | PNever  : prim_kind   (* ! - bottom type, uninhabited *)
  | PBool   : prim_kind   (* bool - two inhabitants: true, false *)
  | PString : prim_kind   (* String - UTF-8 string *)
  | PChar   : prim_kind   (* char - Unicode scalar value *)
  | PDynamic: prim_kind   (* Dynamic/any - UNSAFE top type, allows any operation *)
  | PUnknown: prim_kind   (* Unknown - SAFE top type for gradual typing *)

(* Numeric types - integers and floats with width/precision
   Uses int_type and float_prec from Primitives module *)
type numeric_type =
  | NumInt   : int_type -> numeric_type    (* i8, i16, i32, i64, u8, u16, u32, u64 *)
  | NumFloat : float_prec -> numeric_type  (* f32, f64 *)

(* Numeric type equality - decidable, compares width and sign
   Exposed for type checking implementation *)
val numeric_eq : n1:numeric_type -> n2:numeric_type -> Tot bool

(* Wrapper type kinds - 9 single-type wrappers
   Full definition exposed for covariance/invariance analysis *)
type wrapper_kind =
  | WArray  : wrapper_kind   (* [T] - owned array *)
  | WSlice  : wrapper_kind   (* &[T] - borrowed slice view *)
  | WOption : wrapper_kind   (* T? - optional value *)
  | WBox    : wrapper_kind   (* Box<T> - owned heap allocation *)
  | WRef    : wrapper_kind   (* &T - shared borrow *)
  | WRefMut : wrapper_kind   (* &mut T - exclusive borrow *)
  | WRc     : wrapper_kind   (* Rc<T> - reference counted *)
  | WArc    : wrapper_kind   (* Arc<T> - atomic reference counted *)
  | WRaw    : wrapper_kind   (* *T - raw pointer *)

(* Covariance check for wrappers - critical for subtyping
   RefMut is invariant (requires exact type match), all others covariant
   Exposed as unfold+inline for efficient evaluation in proofs *)
[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let wrapper_is_covariant (w: wrapper_kind) : bool =
  match w with
  | WRefMut -> false  (* Invariant: &mut T requires exact T match *)
  | _ -> true         (* Covariant: inner subtype implies outer subtype *)

(* Modal reference kinds - for fractional permissions (Chapter 9)
   MBoxMod carries a ref_kind with permission fraction *)
type modal_kind =
  | MBoxMod     : ref_kind -> modal_kind   (* Box τ @ p - shared ref with permission *)
  | MDiamondMod : modal_kind               (* Diamond τ - exclusive ref (full permission) *)

(* Modal kind equality - decidable, compares permission fractions
   Exposed for modal type checking *)
val modal_eq : m1:modal_kind -> m2:modal_kind -> Tot bool

(** ============================================================================
    VISIBILITY - Access control for struct/enum fields
    ============================================================================ *)

type visibility =
  | Public  : visibility   (* Accessible from anywhere *)
  | Private : visibility   (* Accessible only within defining module *)
  | Module  : visibility   (* Accessible within module hierarchy *)

(** ============================================================================
    MEMORY REPRESENTATION ATTRIBUTES
    ============================================================================ *)

(* Power of 2 check for alignment values - total, terminating *)
val is_power_of_2 : n:pos -> Tot bool (decreases n)

(* Valid alignment: positive power of 2, at most 2^29
   Refinement ensures only valid alignments can be constructed *)
unfold
type valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}

(* Memory layout representation - affects ABI compatibility *)
type repr_attr =
  | ReprRust        : repr_attr   (* Default Rust layout - may reorder fields *)
  | ReprC           : repr_attr   (* C-compatible layout - stable ABI *)
  | ReprPacked      : repr_attr   (* No padding between fields *)
  | ReprTransparent : repr_attr   (* Same layout as inner type *)
  | ReprAlign       : valid_alignment -> repr_attr  (* Explicit alignment *)

(** ============================================================================
    CORE TYPE CONSTRUCTORS - 12 constructors for SMT tractability

    noeq required because func_type contains effect_row which may have
    function-typed elements, making equality undecidable.
    ============================================================================ *)

(* Main type definition - mutually recursive with auxiliary record types *)
noeq type brrr_type =
  (* Primitives: 1 constructor covers 7 types *)
  | TPrim    : prim_kind -> brrr_type

  (* Numerics: 1 constructor covers int/float with all widths *)
  | TNumeric : numeric_type -> brrr_type

  (* Wrappers: 1 constructor covers 9 single-type wrappers *)
  | TWrap    : wrapper_kind -> brrr_type -> brrr_type

  (* Modal refs: 1 constructor covers Box/Diamond modalities *)
  | TModal   : modal_kind -> brrr_type -> brrr_type

  (* Binary type constructors *)
  | TResult  : brrr_type -> brrr_type -> brrr_type  (* Result<T, E> *)

  (* Collection type *)
  | TTuple   : list brrr_type -> brrr_type          (* (T1, T2, ...) *)

  (* Function type with effects *)
  | TFunc    : func_type -> brrr_type

  (* Type variables and applications *)
  | TVar     : type_var -> brrr_type                (* alpha, beta, ... *)
  | TApp     : brrr_type -> list brrr_type -> brrr_type  (* F<T1, T2> *)
  | TNamed   : type_name -> brrr_type               (* Named type reference *)

  (* Algebraic types *)
  | TStruct  : struct_type -> brrr_type
  | TEnum    : enum_type -> brrr_type

(* Function type with effects and modes *)
and func_type = {
  params      : list param_type;    (* Parameter types with modes *)
  return_type : brrr_type;          (* Return type *)
  effects     : effect_row;         (* Effect annotation from Effects module *)
  is_unsafe   : bool                (* Requires unsafe context? *)
}

(* Parameter with mode annotation - tracks ownership/borrowing *)
and param_type = {
  name : option string;   (* Optional parameter name for documentation *)
  ty   : brrr_type;       (* Parameter type *)
  mode : mode             (* Usage mode from Modes module *)
}

(* Struct type - product type with named fields *)
and struct_type = {
  struct_name   : type_name;
  struct_fields : list field_type;
  struct_repr   : repr_attr         (* Memory representation *)
}

(* Enum type - sum type with named variants *)
and enum_type = {
  enum_name     : type_name;
  enum_variants : list variant_type
}

(* Struct field with visibility *)
and field_type = {
  field_name : string;
  field_ty   : brrr_type;
  field_vis  : visibility
}

(* Enum variant - optionally carries data *)
and variant_type = {
  variant_name   : string;
  variant_fields : list brrr_type   (* Empty for unit variants *)
}

(** ============================================================================
    MODED TYPES - Type with usage mode annotation
    ============================================================================ *)

(* Type paired with its usage mode for linear/affine/relevant typing *)
noeq type moded_type = {
  ty   : brrr_type;
  mode : mode
}

(* Create linear (use-exactly-once) type *)
inline_for_extraction
val linear_type : t:brrr_type -> r:moded_type{r.ty == t /\ r.mode == MOne}

(* Create unrestricted (copyable) type *)
inline_for_extraction
val unrestricted_type : t:brrr_type -> r:moded_type{r.ty == t /\ r.mode == MOmega}

(** ============================================================================
    TYPE SCHEMES - Polymorphism support (forall a b. T)
    ============================================================================ *)

(* Universally quantified type with both type and effect variables *)
noeq type type_scheme = {
  type_vars   : list type_var;      (* Bound type variables *)
  effect_vars : list string;        (* Bound effect variables *)
  body        : brrr_type           (* The type body *)
}

(* Create monomorphic type scheme (no quantified variables) *)
inline_for_extraction
val mono_type : t:brrr_type -> r:type_scheme{r.type_vars == [] /\ r.effect_vars == [] /\ r.body == t}

(** ============================================================================
    TYPE SIZE FUNCTIONS - Termination measures for recursive functions
    ============================================================================ *)

(* Type size - structural size for termination proofs *)
val type_size : t:brrr_type -> Tot nat (decreases t)

val type_list_size : ts:list brrr_type -> Tot nat (decreases ts)

val param_list_size : ps:list param_type -> Tot nat (decreases ps)

val field_list_size : fs:list field_type -> Tot nat (decreases fs)

val variant_list_size : vs:list variant_type -> Tot nat (decreases vs)

(** ============================================================================
    TYPE EQUALITY - Structural equality (decidable)
    ============================================================================ *)

(* Type list equality - element-wise comparison *)
val type_list_eq : ts1:list brrr_type -> ts2:list brrr_type -> Tot bool (decreases ts1)

(* Parameter list equality - compares types and modes *)
val param_list_eq : ps1:list param_type -> ps2:list param_type -> Tot bool (decreases ps1)

(* Structural type equality - the main equality function *)
val type_eq : t1:brrr_type -> t2:brrr_type -> Tot bool (decreases t1)

(** ============================================================================
    TYPE EQUALITY LEMMAS - Reflexivity, Symmetry, Transitivity

    These lemmas establish that type_eq is an equivalence relation.
    SMTPat triggers enable automatic application by Z3.
    ============================================================================ *)

(* Reflexivity with SMTPat - automatically applied by Z3 when seeing type_eq t t *)
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

(* Symmetry - if t1 = t2 then t2 = t1 *)
val type_list_eq_sym : ts1:list brrr_type -> ts2:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true)
        (ensures type_list_eq ts2 ts1 = true)
        (decreases ts1)

val param_list_eq_sym : ps1:list param_type -> ps2:list param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true)
        (ensures param_list_eq ps2 ps1 = true)
        (decreases ps1)

val type_eq_sym : t1:brrr_type -> t2:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq t2 t1 = true)
        (decreases t1)

(* Transitivity - key for chained equality reasoning *)
val type_list_eq_trans : ts1:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true /\ type_list_eq ts2 ts3 = true)
        (ensures type_list_eq ts1 ts3 = true)
        (decreases ts1)

val param_list_eq_trans : ps1:list param_type -> ps2:list param_type -> ps3:list param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true /\ param_list_eq ps2 ps3 = true)
        (ensures param_list_eq ps1 ps3 = true)
        (decreases ps1)

val type_eq_trans : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t1 t2 = true /\ type_eq t2 t3 = true)
        (ensures type_eq t1 t3 = true)
        (decreases t1)

(* Equality substitutivity - enables rewriting in proofs
   If t1 = t2, then type_eq t1 t = type_eq t2 t for any t *)
val type_eq_left_eq : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq t1 t = type_eq t2 t)

val type_eq_right_eq : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures type_eq t t2 = type_eq t t3)

(** ============================================================================
    SUBTYPING RELATION - t1 <: t2 means t1 can be used where t2 is expected
    ============================================================================ *)

(* Main subtyping relation - combines structural and nominal subtyping *)
val subtype : t1:brrr_type -> t2:brrr_type -> Tot bool

(* Type discriminators for bottom/top types - inline for efficient guards *)
[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let is_never (t: brrr_type) : bool =
  match t with TPrim PNever -> true | _ -> false

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let is_dynamic (t: brrr_type) : bool =
  match t with TPrim PDynamic -> true | _ -> false

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let is_unknown (t: brrr_type) : bool =
  match t with TPrim PUnknown -> true | _ -> false

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let is_top_type (t: brrr_type) : bool =
  is_dynamic t || is_unknown t

(** ============================================================================
    SUBTYPING LEMMAS - Reflexivity, Transitivity, Covariance
    ============================================================================ *)

(* Subtype reflexivity with SMTPat - automatically applied by Z3 *)
val subtype_refl : t:brrr_type ->
  Lemma (ensures subtype t t = true)
        (decreases t)
        [SMTPat (subtype t t)]

(* Subtype transitivity - critical for type checking chains *)
val subtype_trans : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires subtype t1 t2 = true /\ subtype t2 t3 = true)
        (ensures subtype t1 t3 = true)
        (decreases t1)

(* Type equality implies subtype equality on left *)
val type_eq_subtype_left : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures subtype t1 t = subtype t2 t)
        (decreases t1)

(* Type equality implies subtype equality on right *)
val type_eq_subtype_right : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures subtype t t2 = subtype t t3)
        (decreases t)

(* Covariant wrapper subtyping with SMTPat - automatically applied *)
val wrapper_covariant_subtype : w:wrapper_kind -> t1:brrr_type -> t2:brrr_type ->
  Lemma (requires wrapper_is_covariant w = true /\ subtype t1 t2 = true)
        (ensures subtype (TWrap w t1) (TWrap w t2) = true)
        [SMTPat (subtype (TWrap w t1) (TWrap w t2))]

(** ============================================================================
    TYPE SUBSTITUTION - For polymorphism instantiation
    ============================================================================ *)

(* Substitute type variable with replacement type *)
val subst_type_var : v:type_var -> replacement:brrr_type -> t:brrr_type ->
  Tot brrr_type (decreases %[type_size t; 0])

val subst_type_list : v:type_var -> replacement:brrr_type -> ts:list brrr_type ->
  Tot (list brrr_type) (decreases %[type_list_size ts; 1])

val subst_param_list : v:type_var -> replacement:brrr_type -> ps:list param_type ->
  Tot (list param_type) (decreases %[param_list_size ps; 1])

(* Substitution preserves type equality - key for polymorphism soundness *)
val subst_type_var_preserves_eq : v:type_var -> repl:brrr_type -> t1:brrr_type -> t2:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq (subst_type_var v repl t1) (subst_type_var v repl t2) = true)
        (decreases %[type_size t1; 0])

(** ============================================================================
    TYPE SCHEME INSTANTIATION
    ============================================================================ *)

(* Instantiate type scheme with concrete type arguments *)
val instantiate : scheme:type_scheme -> type_args:list brrr_type -> option brrr_type

(* Full instantiation with both type and effect variable arguments *)
val instantiate_full : scheme:type_scheme -> type_args:list brrr_type ->
                       effect_args:list effect_row -> option brrr_type

(** ============================================================================
    FREE TYPE VARIABLES
    ============================================================================ *)

(* Collect free type variables in a type *)
val free_type_vars : t:brrr_type -> Tot (list type_var) (decreases %[type_size t; 0])

val free_type_vars_list : ts:list brrr_type -> Tot (list type_var) (decreases %[type_list_size ts; 1])

val free_type_vars_params : ps:list param_type -> Tot (list type_var) (decreases %[param_list_size ps; 1])

(* Check if type is closed (no free variables) *)
val is_closed : t:brrr_type -> bool

(** ============================================================================
    REGION TYPES - Lifetime and scope annotations (Chapter 4)
    ============================================================================ *)

(* Region identifier for lifetime tracking *)
type region =
  | RStatic : region                  (* 'static - lives forever *)
  | RNamed  : string -> region        (* Named region variable like 'a *)
  | RFresh  : nat -> region           (* Fresh region from letregion *)
  | RScope  : nat -> region           (* Tied to lexical scope depth *)

(* Region equality - decidable *)
val region_eq : r1:region -> r2:region -> bool

(* Region outlives ordering: r1 outlives r2 (r1's scope includes r2's) *)
val region_outlives : r1:region -> r2:region -> bool

(* Check if region escapes in type structure *)
val region_escapes : r:region -> t:brrr_type -> Tot bool (decreases type_size t)

(* Type with region annotation: tau @ rho *)
noeq type regioned_type = {
  base_type : brrr_type;
  region    : region
}

(* Create regioned type with static lifetime *)
inline_for_extraction
val static_type : t:brrr_type -> r:regioned_type{r.base_type == t /\ r.region == RStatic}

(* Create regioned type with named lifetime *)
inline_for_extraction
val lifetime_type : t:brrr_type -> lifetime:string ->
                    r:regioned_type{r.base_type == t /\ r.region == RNamed lifetime}

(* Regioned type subtyping: combines type and region subtyping *)
val regioned_subtype : rt1:regioned_type -> rt2:regioned_type -> bool

(** ============================================================================
    TYPE UTILITY FUNCTIONS - For analysis in Brrr-Machine
    ============================================================================ *)

(* Check if type represents nullable/optional value *)
val is_nullable : t:brrr_type -> bool

(* Check if type represents owned (non-borrowed) data *)
val is_owned : t:brrr_type -> bool

(* Extract inner type from wrapper types *)
val get_inner_type : t:brrr_type -> option brrr_type

(* Get error type from Result types *)
val get_error_type : t:brrr_type -> option brrr_type

(* Recursively unwrap all wrapper types *)
val unwrap_all : t:brrr_type -> Tot brrr_type (decreases type_size t)

(* Check if type is any kind of reference/borrow *)
val is_reference_type : t:brrr_type -> bool

(* Check if type allows mutation through it *)
val is_mutable_reference : t:brrr_type -> bool

(* Check if operations on type need runtime checks (gradual typing) *)
val requires_runtime_check : t:brrr_type -> bool

(* Get pointee type for pointer/reference types *)
val get_pointee_type : t:brrr_type -> option brrr_type

(** ============================================================================
    TYPE CONSTRUCTORS - Convenience aliases following HACL* unfold pattern

    These provide short names for common types while maintaining
    full transparency through unfold.
    ============================================================================ *)

(* Primitive type aliases - directly usable constants *)
unfold let t_unit : brrr_type = TPrim PUnit
unfold let t_never : brrr_type = TPrim PNever
unfold let t_bool : brrr_type = TPrim PBool
unfold let t_string : brrr_type = TPrim PString
unfold let t_char : brrr_type = TPrim PChar
unfold let t_dynamic : brrr_type = TPrim PDynamic
unfold let t_unknown : brrr_type = TPrim PUnknown

(* Numeric type aliases *)
unfold let t_i8 : brrr_type = TNumeric (NumInt i8)
unfold let t_i16 : brrr_type = TNumeric (NumInt i16)
unfold let t_i32 : brrr_type = TNumeric (NumInt i32)
unfold let t_i64 : brrr_type = TNumeric (NumInt i64)
unfold let t_u8 : brrr_type = TNumeric (NumInt u8)
unfold let t_u16 : brrr_type = TNumeric (NumInt u16)
unfold let t_u32 : brrr_type = TNumeric (NumInt u32)
unfold let t_u64 : brrr_type = TNumeric (NumInt u64)
unfold let t_f32 : brrr_type = TNumeric (NumFloat F32)
unfold let t_f64 : brrr_type = TNumeric (NumFloat F64)

(* Wrapper type constructors with refinement postconditions *)
inline_for_extraction
val t_array : t:brrr_type -> r:brrr_type{r == TWrap WArray t}

inline_for_extraction
val t_slice : t:brrr_type -> r:brrr_type{r == TWrap WSlice t}

inline_for_extraction
val t_option : t:brrr_type -> r:brrr_type{r == TWrap WOption t}

inline_for_extraction
val t_box : t:brrr_type -> r:brrr_type{r == TWrap WBox t}

inline_for_extraction
val t_ref : t:brrr_type -> r:brrr_type{r == TWrap WRef t}

inline_for_extraction
val t_ref_mut : t:brrr_type -> r:brrr_type{r == TWrap WRefMut t}

inline_for_extraction
val t_rc : t:brrr_type -> r:brrr_type{r == TWrap WRc t}

inline_for_extraction
val t_arc : t:brrr_type -> r:brrr_type{r == TWrap WArc t}

inline_for_extraction
val t_raw : t:brrr_type -> r:brrr_type{r == TWrap WRaw t}

(* Modal type constructors *)
inline_for_extraction
val t_box_mod : rk:ref_kind -> t:brrr_type -> r:brrr_type{r == TModal (MBoxMod rk) t}

inline_for_extraction
val t_diamond : t:brrr_type -> r:brrr_type{r == TModal MDiamondMod t}

(* Legacy aliases for backward compatibility *)
inline_for_extraction
val t_int : it:int_type -> r:brrr_type{r == TNumeric (NumInt it)}

inline_for_extraction
val t_float : fp:float_prec -> r:brrr_type{r == TNumeric (NumFloat fp)}

(* Function type constructors *)
val t_func : params:list brrr_type -> ret:brrr_type -> eff:effect_row -> brrr_type

val t_pure_func : params:list brrr_type -> ret:brrr_type -> brrr_type
