(**
 * BrrrLang.Core.BrrrReflection - Interface
 *
 * Typed Reflection and Runtime Type Representation
 * ================================================
 *
 * Based on brrr_lang_spec_v0.4.tex Part VI - Metaprogramming, Chapter: Typed Reflection
 *
 * Overview
 * --------
 * This module implements typed reflection primitives for Brrr-Lang, enabling
 * runtime type introspection while maintaining type safety:
 *
 *   1. Represent types at runtime (TypeRep[tau])
 *   2. Package values with their types (Dynamic)
 *   3. Perform safe downcasts (cast/from_dynamic)
 *   4. Test type equality with witnesses (eqType -> Option[tau =:= sigma])
 *
 * Theoretical Foundation
 * ----------------------
 *   TypeRep[tau] : *
 *
 * TypeRep is an indexed type family where the index tau represents the type
 * being reified. Key operations:
 *
 *   typeOf  : forall tau. tau -> TypeRep[tau]
 *   cast    : forall tau sigma. tau -> TypeRep[sigma] -> Option[sigma]
 *   eqType  : forall tau sigma. TypeRep[tau] -> TypeRep[sigma] -> Option[tau =:= sigma]
 *
 * Leibniz Equality:
 *   tau =:= sigma  triangleq  forall F : * -> *. F[tau] -> F[sigma]
 *
 * Dynamic Type (Existential Packaging):
 *   Dynamic = exists tau. (tau * TypeRep[tau])
 *
 * All proofs are complete with NO ADMITS.
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Values
 *)
module BrrrReflection

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrValues
open FStar.List.Tot

(** ============================================================================
    TYPE REPRESENTATION - Mirrors brrr_type structure
    ============================================================================

    TypeRep is a runtime representation of types that mirrors brrr_type but
    is designed for runtime use with decidable equality checking.
    ============================================================================ *)

(** Primitive type representation - mirrors prim_kind *)
type prim_rep =
  | PRUnit   : prim_rep   (* () - unit type *)
  | PRNever  : prim_rep   (* ! - bottom type *)
  | PRBool   : prim_rep   (* bool *)
  | PRString : prim_rep   (* String *)
  | PRChar   : prim_rep   (* char *)
  | PRDynamic: prim_rep   (* Dynamic/any type *)

(** Numeric type representation - mirrors numeric_type *)
type numeric_rep =
  | NRInt   : int_type -> numeric_rep
  | NRFloat : float_prec -> numeric_rep

(** Wrapper kind representation - mirrors wrapper_kind *)
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

(** Modal kind representation - mirrors modal_kind *)
type modal_rep =
  | MRBoxMod     : ref_kind -> modal_rep
  | MRDiamondMod : modal_rep

(** Strictly positive list wrapper for mutually recursive types *)
let trlist ([@@@strictly_positive] a: Type) = list a

(** Main type representation - mirrors brrr_type's 12 constructors *)
noeq type type_rep =
  | TRPrim    : prim_rep -> type_rep
  | TRNumeric : numeric_rep -> type_rep
  | TRWrap    : wrapper_rep -> type_rep -> type_rep
  | TRModal   : modal_rep -> type_rep -> type_rep
  | TRResult  : type_rep -> type_rep -> type_rep
  | TRTuple   : trlist type_rep -> type_rep
  | TRFunc    : trlist param_rep -> type_rep -> effect_row -> bool -> type_rep
  | TRVar     : type_var -> type_rep
  | TRApp     : type_rep -> trlist type_rep -> type_rep
  | TRNamed   : type_name -> type_rep
  | TRStruct  : type_name -> trlist field_rep -> repr_attr -> type_rep
  | TREnum    : type_name -> trlist variant_rep -> type_rep

(** Parameter representation for function types *)
and param_rep = {
  pr_name : option string;
  pr_ty   : type_rep;
  pr_mode : mode
}

(** Struct field representation *)
and field_rep = {
  flr_name : string;
  flr_ty   : type_rep;
  flr_vis  : visibility;
  flr_tag  : option string
}

(** Variant representation for enum types *)
and variant_rep = {
  vr_name   : string;
  vr_fields : trlist type_rep
}

(** ============================================================================
    CONVERSION: prim_kind <-> prim_rep
    ============================================================================ *)

(** Convert compile-time prim_kind to runtime prim_rep *)
val prim_kind_to_rep : prim_kind -> prim_rep

(** Convert runtime prim_rep back to compile-time prim_kind *)
val prim_rep_to_kind : prim_rep -> prim_kind

(** Roundtrip: prim_kind -> prim_rep -> prim_kind = identity *)
val prim_roundtrip_kind : pk:prim_kind ->
  Lemma (ensures prim_rep_to_kind (prim_kind_to_rep pk) = pk)

(** Roundtrip: prim_rep -> prim_kind -> prim_rep = identity *)
val prim_roundtrip_rep : pr:prim_rep ->
  Lemma (ensures prim_kind_to_rep (prim_rep_to_kind pr) = pr)

(** ============================================================================
    CONVERSION: numeric_type <-> numeric_rep
    ============================================================================ *)

(** Convert compile-time numeric_type to runtime numeric_rep *)
val numeric_type_to_rep : numeric_type -> numeric_rep

(** Convert runtime numeric_rep back to compile-time numeric_type *)
val numeric_rep_to_type : numeric_rep -> numeric_type

(** Roundtrip: numeric_type -> numeric_rep -> numeric_type = identity *)
val numeric_roundtrip_type : nt:numeric_type ->
  Lemma (ensures numeric_rep_to_type (numeric_type_to_rep nt) = nt)

(** Roundtrip: numeric_rep -> numeric_type -> numeric_rep = identity *)
val numeric_roundtrip_rep : nr:numeric_rep ->
  Lemma (ensures numeric_type_to_rep (numeric_rep_to_type nr) = nr)

(** ============================================================================
    CONVERSION: wrapper_kind <-> wrapper_rep
    ============================================================================ *)

(** Convert compile-time wrapper_kind to runtime wrapper_rep *)
val wrapper_kind_to_rep : wrapper_kind -> wrapper_rep

(** Convert runtime wrapper_rep back to compile-time wrapper_kind *)
val wrapper_rep_to_kind : wrapper_rep -> wrapper_kind

(** Roundtrip: wrapper_kind -> wrapper_rep -> wrapper_kind = identity *)
val wrapper_roundtrip_kind : wk:wrapper_kind ->
  Lemma (ensures wrapper_rep_to_kind (wrapper_kind_to_rep wk) = wk)

(** Roundtrip: wrapper_rep -> wrapper_kind -> wrapper_rep = identity *)
val wrapper_roundtrip_rep : wr:wrapper_rep ->
  Lemma (ensures wrapper_kind_to_rep (wrapper_rep_to_kind wr) = wr)

(** ============================================================================
    CONVERSION: modal_kind <-> modal_rep
    ============================================================================ *)

(** Convert compile-time modal_kind to runtime modal_rep *)
val modal_kind_to_rep : modal_kind -> modal_rep

(** Convert runtime modal_rep back to compile-time modal_kind *)
val modal_rep_to_kind : modal_rep -> modal_kind

(** Roundtrip: modal_kind -> modal_rep -> modal_kind = identity *)
val modal_roundtrip_kind : mk:modal_kind ->
  Lemma (ensures modal_rep_to_kind (modal_kind_to_rep mk) = mk)

(** Roundtrip: modal_rep -> modal_kind -> modal_rep = identity *)
val modal_roundtrip_rep : mr:modal_rep ->
  Lemma (ensures modal_kind_to_rep (modal_rep_to_kind mr) = mr)

(** ============================================================================
    SIZE FUNCTIONS FOR TERMINATION MEASURES
    ============================================================================

    Compute natural number "size" for type representations used as termination
    measures (decreases clauses) for recursive functions over type_rep.
    ============================================================================ *)

(** Size of a type_rep *)
val type_rep_size : tr:type_rep -> Tot nat (decreases tr)

(** Size of a list of type_reps *)
val type_rep_list_size : ts:trlist type_rep -> Tot nat (decreases ts)

(** Size of a parameter list *)
val param_rep_list_size : ps:trlist param_rep -> Tot nat (decreases ps)

(** Size of a field list *)
val field_rep_list_size : fs:trlist field_rep -> Tot nat (decreases fs)

(** Size of a variant list *)
val variant_rep_list_size : vs:trlist variant_rep -> Tot nat (decreases vs)

(** ============================================================================
    CONVERSION: brrr_type <-> type_rep (main conversion)
    ============================================================================

    Establishes the isomorphism between compile-time types (brrr_type) and
    runtime type representations (type_rep).
    ============================================================================ *)

(** Convert brrr_type to type_rep *)
val brrr_type_to_rep : t:brrr_type -> Tot type_rep (decreases t)

(** Convert list of brrr_types to list of type_reps *)
val brrr_type_list_to_rep : ts:list brrr_type -> Tot (trlist type_rep) (decreases ts)

(** Convert list of param_types to list of param_reps *)
val param_type_list_to_rep : ps:list param_type -> Tot (trlist param_rep) (decreases ps)

(** Convert list of field_types to list of field_reps *)
val field_type_list_to_rep : fs:list field_type -> Tot (trlist field_rep) (decreases fs)

(** Convert list of variant_types to list of variant_reps *)
val variant_type_list_to_rep : vs:list variant_type -> Tot (trlist variant_rep) (decreases vs)

(** Convert type_rep back to brrr_type *)
val type_rep_to_brrr : tr:type_rep -> Tot brrr_type (decreases tr)

(** Convert list of type_reps back to list of brrr_types *)
val type_rep_list_to_brrr : trs:trlist type_rep -> Tot (list brrr_type) (decreases trs)

(** Convert list of param_reps back to list of param_types *)
val param_rep_list_to_brrr : prs:trlist param_rep -> Tot (list param_type) (decreases prs)

(** Convert list of field_reps back to list of field_types *)
val field_rep_list_to_brrr : frs:trlist field_rep -> Tot (list field_type) (decreases frs)

(** Convert list of variant_reps back to list of variant_types *)
val variant_rep_list_to_brrr : vrs:trlist variant_rep -> Tot (list variant_type) (decreases vrs)

(** ============================================================================
    ROUNDTRIP PROOFS: brrr_type -> type_rep -> brrr_type
    ============================================================================ *)

(** Main roundtrip: brrr_type -> type_rep -> brrr_type = identity *)
val roundtrip_brrr_type : t:brrr_type ->
  Lemma (ensures type_rep_to_brrr (brrr_type_to_rep t) == t)
        (decreases t)

(** List roundtrip *)
val roundtrip_brrr_type_list : ts:list brrr_type ->
  Lemma (ensures type_rep_list_to_brrr (brrr_type_list_to_rep ts) == ts)
        (decreases ts)

(** Param type list roundtrip *)
val roundtrip_param_type_list : ps:list param_type ->
  Lemma (ensures param_rep_list_to_brrr (param_type_list_to_rep ps) == ps)
        (decreases ps)

(** Field type list roundtrip *)
val roundtrip_field_type_list : fs:list field_type ->
  Lemma (ensures field_rep_list_to_brrr (field_type_list_to_rep fs) == fs)
        (decreases fs)

(** Variant type list roundtrip *)
val roundtrip_variant_type_list : vs:list variant_type ->
  Lemma (ensures variant_rep_list_to_brrr (variant_type_list_to_rep vs) == vs)
        (decreases vs)

(** ============================================================================
    ROUNDTRIP PROOFS: type_rep -> brrr_type -> type_rep
    ============================================================================ *)

(** Main roundtrip: type_rep -> brrr_type -> type_rep = identity *)
val roundtrip_type_rep : tr:type_rep ->
  Lemma (ensures brrr_type_to_rep (type_rep_to_brrr tr) == tr)
        (decreases tr)

(** List roundtrip *)
val roundtrip_type_rep_list : trs:trlist type_rep ->
  Lemma (ensures brrr_type_list_to_rep (type_rep_list_to_brrr trs) == trs)
        (decreases trs)

(** Param rep list roundtrip *)
val roundtrip_param_rep_list : prs:trlist param_rep ->
  Lemma (ensures param_type_list_to_rep (param_rep_list_to_brrr prs) == prs)
        (decreases prs)

(** Field rep list roundtrip *)
val roundtrip_field_rep_list : frs:trlist field_rep ->
  Lemma (ensures field_type_list_to_rep (field_rep_list_to_brrr frs) == frs)
        (decreases frs)

(** Variant rep list roundtrip *)
val roundtrip_variant_rep_list : vrs:trlist variant_rep ->
  Lemma (ensures variant_type_list_to_rep (variant_rep_list_to_brrr vrs) == vrs)
        (decreases vrs)

(** ============================================================================
    TYPE REPRESENTATION EQUALITY
    ============================================================================

    Structural equality for type_rep that:
    1. Returns true when two type_reps represent the same type
    2. Is decidable (bool return, not prop)
    3. Is reflexive, symmetric, and transitive
    ============================================================================ *)

(** Primitive equality *)
val prim_rep_eq : prim_rep -> prim_rep -> bool

(** Numeric equality *)
val numeric_rep_eq : numeric_rep -> numeric_rep -> bool

(** Wrapper equality *)
val wrapper_rep_eq : wrapper_rep -> wrapper_rep -> bool

(** Modal equality *)
val modal_rep_eq : modal_rep -> modal_rep -> bool

(** Main type representation equality *)
val type_rep_eq : tr1:type_rep -> tr2:type_rep -> Tot bool (decreases tr1)

(** List equality *)
val type_rep_list_eq : trs1:trlist type_rep -> trs2:trlist type_rep -> Tot bool (decreases trs1)

(** Parameter list equality *)
val param_rep_list_eq : prs1:trlist param_rep -> prs2:trlist param_rep -> Tot bool (decreases prs1)

(** ============================================================================
    TYPE_REP_EQ REFLEXIVITY PROOFS
    ============================================================================ *)

(** Primitive reflexivity with SMT pattern *)
val prim_rep_eq_refl : p:prim_rep ->
  Lemma (prim_rep_eq p p = true)
        [SMTPat (prim_rep_eq p p)]

(** Numeric reflexivity with SMT pattern *)
val numeric_rep_eq_refl : n:numeric_rep ->
  Lemma (numeric_rep_eq n n = true)
        [SMTPat (numeric_rep_eq n n)]

(** Wrapper reflexivity with SMT pattern *)
val wrapper_rep_eq_refl : w:wrapper_rep ->
  Lemma (wrapper_rep_eq w w = true)
        [SMTPat (wrapper_rep_eq w w)]

(** Modal reflexivity with SMT pattern *)
val modal_rep_eq_refl : m:modal_rep ->
  Lemma (modal_rep_eq m m = true)
        [SMTPat (modal_rep_eq m m)]

(** Main type_rep_eq reflexivity with SMT pattern *)
val type_rep_eq_refl : tr:type_rep ->
  Lemma (ensures type_rep_eq tr tr = true)
        (decreases tr)
        [SMTPat (type_rep_eq tr tr)]

(** List reflexivity with SMT pattern *)
val type_rep_list_eq_refl : trs:trlist type_rep ->
  Lemma (ensures type_rep_list_eq trs trs = true)
        (decreases trs)
        [SMTPat (type_rep_list_eq trs trs)]

(** Param list reflexivity with SMT pattern *)
val param_rep_list_eq_refl : prs:trlist param_rep ->
  Lemma (ensures param_rep_list_eq prs prs = true)
        (decreases prs)
        [SMTPat (param_rep_list_eq prs prs)]

(** ============================================================================
    TYPE EQUALITY WITNESS - Leibniz Equality
    ============================================================================

    tau =:= sigma  triangleq  forall F : * -> *. F[tau] -> F[sigma]

    Leibniz equality states that two types are equal iff they are
    interchangeable in all type contexts.
    ============================================================================ *)

(** Type equality witness: proof that two brrr_types are propositionally equal *)
type brrr_type_equality (t1 t2: brrr_type) = squash (t1 == t2)

(** Reflexivity: any type equals itself *)
val brrr_type_eq_refl : #t:brrr_type -> brrr_type_equality t t

(** Symmetry: equality is symmetric *)
val brrr_type_eq_sym : #t1:brrr_type -> #t2:brrr_type ->
  brrr_type_equality t1 t2 -> brrr_type_equality t2 t1

(** Transitivity: equality is transitive *)
val brrr_type_eq_trans : #t1:brrr_type -> #t2:brrr_type -> #t3:brrr_type ->
  brrr_type_equality t1 t2 -> brrr_type_equality t2 t3 -> brrr_type_equality t1 t3

(** ============================================================================
    HELPER LEMMAS FOR EQUALITY PROOFS
    ============================================================================ *)

(** Primitive equality implies brrr_type equality *)
val prim_rep_eq_implies_brrr_eq : p1:prim_rep -> p2:prim_rep ->
  Lemma (requires prim_rep_eq p1 p2 = true)
        (ensures TPrim (prim_rep_to_kind p1) == TPrim (prim_rep_to_kind p2))

(** Numeric equality implies brrr_type equality *)
val numeric_rep_eq_implies_brrr_eq : n1:numeric_rep -> n2:numeric_rep ->
  Lemma (requires numeric_rep_eq n1 n2 = true)
        (ensures TNumeric (numeric_rep_to_type n1) == TNumeric (numeric_rep_to_type n2))

(** Wrapper equality implies wrapper kind equality *)
val wrapper_rep_eq_implies_kind_eq : w1:wrapper_rep -> w2:wrapper_rep ->
  Lemma (requires wrapper_rep_eq w1 w2 = true)
        (ensures wrapper_rep_to_kind w1 == wrapper_rep_to_kind w2)

(** Modal equality implies modal kind equality *)
val modal_rep_eq_implies_kind_eq : m1:modal_rep -> m2:modal_rep ->
  Lemma (requires modal_rep_eq m1 m2 = true)
        (ensures modal_rep_to_kind m1 == modal_rep_to_kind m2)

(** ============================================================================
    TYPE EQUALITY CHECK FUNCTION
    ============================================================================ *)

(** Check if two type_reps are equal, returning Some () if equal *)
val eq_type_rep_check : type_rep -> type_rep -> option unit

(** Same for lists *)
val eq_type_rep_list_check : trlist type_rep -> trlist type_rep -> option unit

(** ============================================================================
    DYNAMIC TYPE
    ============================================================================

    Dynamic = exists tau. (tau * TypeRep[tau])

    A dynamic value packages a runtime value with its type representation,
    enabling type-safe dynamic typing.
    ============================================================================ *)

(** Dynamic value: existential package of value + type representation *)
noeq type dynamic =
  | Dyn : tr:type_rep -> v:value -> dynamic

(** Create a dynamic value from a value and its type representation *)
val to_dynamic : type_rep -> value -> dynamic

(** Get the type representation from a dynamic value *)
val get_type_rep : dynamic -> type_rep

(** Get the underlying value (untyped) *)
val get_value : dynamic -> value

(** ============================================================================
    SAFE CAST OPERATIONS
    ============================================================================

    cast : forall tau sigma. tau -> TypeRep[sigma] -> Option[sigma]

    Cast checks if the actual type matches the expected type at runtime.
    ============================================================================ *)

(** Attempt to extract a value from Dynamic with expected type representation *)
val from_dynamic : dynamic -> type_rep -> option value

(** Cast value with source type_rep to target type_rep *)
val cast_value : value -> type_rep -> type_rep -> option value

(** Cast with equality proof: if types are equal, casting always succeeds *)
val cast_with_proof : v:value -> source:type_rep -> target:type_rep ->
  eq:brrr_type_equality (type_rep_to_brrr source) (type_rep_to_brrr target) ->
  value

(** ============================================================================
    CAST SAFETY PROOFS
    ============================================================================ *)

(** from_dynamic safety: successful extraction implies type equality *)
val from_dynamic_safe : d:dynamic -> expected:type_rep ->
  Lemma (ensures (match from_dynamic d expected with
                  | Some _ -> type_rep_eq (get_type_rep d) expected = true
                  | None -> true))

(** Stronger version: successful extraction implies type_rep_eq check passed *)
val from_dynamic_types_eq : d:dynamic -> expected:type_rep ->
  Lemma (requires Some? (from_dynamic d expected))
        (ensures type_rep_eq (get_type_rep d) expected = true)

(** ============================================================================
    TYPE_OF OPERATIONS
    ============================================================================

    typeOf : forall tau. tau -> TypeRep[tau]

    PARTIAL operation - not all runtime values have enough information to
    fully reconstruct their type.
    ============================================================================ *)

(** Infer type representation from a value (partial) *)
val typeof_value : value -> option type_rep

(** Helper for typeof_value: reconstruct types of tuple elements *)
val typeof_value_list : vlist value -> option (trlist type_rep)

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR COMMON TYPES
    ============================================================================ *)

(** Primitive type representations *)
val tr_unit : type_rep
val tr_never : type_rep
val tr_bool : type_rep
val tr_string : type_rep
val tr_char : type_rep
val tr_dynamic : type_rep

(** Numeric type representations - all width variants *)
val tr_i8 : type_rep
val tr_i16 : type_rep
val tr_i32 : type_rep
val tr_i64 : type_rep
val tr_u8 : type_rep
val tr_u16 : type_rep
val tr_u32 : type_rep
val tr_u64 : type_rep
val tr_f32 : type_rep
val tr_f64 : type_rep

(** Wrapper type representation constructors *)
val tr_array : type_rep -> type_rep
val tr_slice : type_rep -> type_rep
val tr_option : type_rep -> type_rep
val tr_box : type_rep -> type_rep
val tr_ref : type_rep -> type_rep
val tr_ref_mut : type_rep -> type_rep

(** Result type representation *)
val tr_result : type_rep -> type_rep -> type_rep

(** Tuple type representation *)
val tr_tuple : trlist type_rep -> type_rep

(** ============================================================================
    CONSISTENCY PROOFS WITH brrr_type
    ============================================================================ *)

(** tr_unit corresponds to t_unit from BrrrTypes *)
val tr_unit_consistent : unit -> Lemma (type_rep_to_brrr tr_unit == t_unit)

(** tr_bool corresponds to t_bool from BrrrTypes *)
val tr_bool_consistent : unit -> Lemma (type_rep_to_brrr tr_bool == t_bool)

(** tr_string corresponds to t_string from BrrrTypes *)
val tr_string_consistent : unit -> Lemma (type_rep_to_brrr tr_string == t_string)

(** tr_i32 corresponds to t_i32 from BrrrTypes *)
val tr_i32_consistent : unit -> Lemma (type_rep_to_brrr tr_i32 == t_i32)

(** tr_i64 corresponds to t_i64 from BrrrTypes *)
val tr_i64_consistent : unit -> Lemma (type_rep_to_brrr tr_i64 == t_i64)

(** tr_option preserves the t_option structure *)
val tr_option_consistent : t:type_rep ->
  Lemma (type_rep_to_brrr (tr_option t) == t_option (type_rep_to_brrr t))

(** tr_result preserves the TResult structure *)
val tr_result_consistent : t_ok:type_rep -> t_err:type_rep ->
  Lemma (type_rep_to_brrr (tr_result t_ok t_err) ==
         TResult (type_rep_to_brrr t_ok) (type_rep_to_brrr t_err))

(** ============================================================================
    TYPE REPRESENTATION INTROSPECTION
    ============================================================================

    Predicates for examining type representation structure at runtime.
    ============================================================================ *)

(** Is this a primitive type? *)
val is_prim_type : type_rep -> bool

(** Is this a numeric type? *)
val is_numeric_type : type_rep -> bool

(** Is this an integer type? *)
val is_int_type : type_rep -> bool

(** Is this a float type? *)
val is_float_type : type_rep -> bool

(** Is this a function type? *)
val is_func_type : type_rep -> bool

(** Is this a wrapper type (Option, Array, etc.)? *)
val is_wrapper_type : type_rep -> bool

(** Is this a named type reference (struct, enum, or type alias)? *)
val is_named_type : type_rep -> bool

(** Get the inner type of a wrapper, if applicable *)
val get_inner_type : type_rep -> option type_rep

(** Get function parameter types, if applicable *)
val get_func_param_types : type_rep -> option (trlist type_rep)

(** Get function return type, if applicable *)
val get_func_return_type : type_rep -> option type_rep

(** ============================================================================
    PRETTY PRINTING
    ============================================================================

    String representation of type_rep for debugging and error messages.
    ============================================================================ *)

(** Convert type_rep to human-readable string *)
val type_rep_to_string : tr:type_rep -> Tot string (decreases tr)

(** Helper for tuple string representation *)
val type_rep_list_to_string : trs:trlist type_rep -> Tot string (decreases trs)
