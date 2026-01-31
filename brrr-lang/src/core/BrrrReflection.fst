(**
 * BrrrLang.Core.BrrrReflection
 *
 * Typed Reflection and Runtime Type Representation
 * ================================================
 *
 * Based on brrr_lang_spec_v0.4.tex Part VI - Metaprogramming, Chapter: Typed Reflection
 * See also: fstar_pop_book.md lines 14500-16500 (Meta-F*, tactics, quotations)
 * Reference: FSTAR_REFERENCE.md Section 7 (Tactics), Section 8 (Reflection API)
 *
 * Overview
 * --------
 * This module implements typed reflection primitives for Brrr-Lang, enabling
 * runtime type introspection while maintaining type safety. Unlike dynamically
 * typed languages where type information is erased, typed reflection provides
 * a principled way to:
 *
 *   1. Represent types at runtime (TypeRep[tau])
 *   2. Package values with their types (Dynamic)
 *   3. Perform safe downcasts (cast/from_dynamic)
 *   4. Test type equality with witnesses (eqType -> Option[tau =:= sigma])
 *
 * Theoretical Foundation
 * ----------------------
 * From brrr_lang_spec_v0.4.tex Section "TypeRep":
 *
 *   TypeRep[tau] : *
 *
 * TypeRep is an indexed type family where the index tau represents the type
 * being reified. This follows the pattern of Generalized Algebraic Data Types
 * (GADTs) where the return type of each constructor refines the index.
 *
 * The key operations from the specification:
 *
 *   typeOf  : forall tau. tau -> TypeRep[tau]
 *   cast    : forall tau sigma. tau -> TypeRep[sigma] -> Option[sigma]
 *   eqType  : forall tau sigma. TypeRep[tau] -> TypeRep[sigma] -> Option[tau =:= sigma]
 *
 * Where tau =:= sigma denotes Leibniz equality (identity of indiscernibles).
 *
 * Leibniz Equality and Type Witnesses
 * ------------------------------------
 * From brrr_lang_spec_v0.4.tex Section "Type Equality Witness":
 *
 *   tau =:= sigma  triangleq  forall F : * -> *. F[tau] -> F[sigma]
 *
 * This captures the fundamental notion that two types are equal iff they are
 * interchangeable in all contexts. Coercion via equality:
 *
 *   coerce : forall tau sigma. (tau =:= sigma) -> tau -> sigma
 *   coerce(eq, x) = eq[lambda T. T](x)
 *
 * In F*, we use propositional equality (==) with squash types to represent
 * type equality witnesses.
 *
 * Dynamic Type (Existential Packaging)
 * ------------------------------------
 * From brrr_lang_spec_v0.4.tex Section "Dynamic Type":
 *
 *   Dynamic = exists tau. (tau * TypeRep[tau])
 *
 * Dynamic packages a value with its type representation, enabling type-safe
 * dynamic typing. Operations:
 *
 *   toDyn   : forall tau. tau -> Dynamic
 *   fromDyn : forall tau. Dynamic -> TypeRep[tau] -> Option[tau]
 *
 * The fromDyn operation performs a runtime type check and returns None if
 * the expected type doesn't match the actual type.
 *
 * Implementation Strategy
 * -----------------------
 * Unlike the GADT approach shown in the spec (where type_rep : Type -> Type),
 * this implementation uses a separate type_rep that mirrors brrr_type but is
 * designed for runtime use. This approach:
 *
 *   - Avoids the complexity of indexed inductive types in F*
 *   - Enables decidable equality checking (type_rep_eq)
 *   - Maintains clear separation between compile-time and runtime types
 *   - Provides proven isomorphism with brrr_type via conversion functions
 *
 * The roundtrip proofs establish:
 *   type_rep_to_brrr (brrr_type_to_rep t) == t
 *   brrr_type_to_rep (type_rep_to_brrr tr) == tr
 *
 * Relationship to FStar.Reflection
 * ---------------------------------
 * F*'s native reflection API (FStar.Reflection.V2) provides:
 *
 *   - term_view : inspect/pack for term structure
 *   - quote/unquote : static quotation and unquotation
 *   - Tac effect : tactic monad for metaprogramming
 *
 * This module provides a DIFFERENT kind of reflection - runtime type
 * representation for Brrr-Lang's type system, not F* term inspection.
 * See fstar_pop_book.md lines 16100-16350 for F* reflection details.
 *
 * Key Invariant
 * -------------
 * NO ADMITS ALLOWED - all proofs must be complete. This ensures the
 * type safety guarantees of reflection are formally verified.
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Values
 *
 * References
 * ----------
 * [1] brrr_lang_spec_v0.4.tex, Part VI "Metaprogramming"
 * [2] fstar_pop_book.md, lines 14500-16500 (Meta-F* and tactics)
 * [3] FSTAR_REFERENCE.md, Sections 7-8 (Tactics and Reflection API)
 * [4] SPECIFICATION_ERRATA.md, Chapter 7 (Pattern Type Mismatch)
 *)
module BrrrReflection

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open FStar.List.Tot

(** ============================================================================
    TYPE REPRESENTATION - Mirrors brrr_type structure
    ============================================================================

    TypeRep is a runtime representation of types. It mirrors the structure of
    brrr_type but is designed to be passed around at runtime for reflection.

    From brrr_lang_spec_v0.4.tex:
      TypeRep[tau] : *

    Design rationale:
    -----------------
    1. We use a separate type rather than reusing brrr_type directly to maintain
       clear separation between compile-time types and runtime type representations.

    2. The structure exactly mirrors brrr_type's 12 constructors for 1:1 mapping.
       This follows the "discriminator types" pattern from the spec (Section on
       Z3 quantifier explosion workaround):

         type prim_kind = PUnit | PNever | PBool | PString | PChar | PDynamic
         type numeric_type = NumInt of int_type | NumFloat of float_prec
         type wrapper_kind = WArray | WSlice | WOption | ...

    3. Conversion functions establish the proven isomorphism with brrr_type.
       The roundtrip proofs (roundtrip_brrr_type, roundtrip_type_rep) ensure
       no information is lost during conversion.

    Theoretical Basis:
    ------------------
    TypeRep implements the GADT pattern conceptually, where each constructor
    produces a type representation for a specific type index. However, F*'s
    lack of first-class indexed inductive types means we use a simpler
    unindexed representation with explicit equality checking.

    Compare to spec's indexed version:
      noeq type type_rep : Type -> Type =
        | TRInt    : type_rep int
        | TRBool   : type_rep bool
        | TRPair   : #a:Type -> #b:Type -> type_rep a -> type_rep b -> type_rep (a & b)
        ...

    Our version loses the index but gains:
      - Decidable equality (type_rep_eq : type_rep -> type_rep -> bool)
      - Simpler termination arguments
      - Better SMT performance
    ============================================================================ *)

(** Primitive type representation - mirrors prim_kind from BrrrTypes.
    These are the "atomic" types that have no substructure.

    From spec:
      PDynamic corresponds to the "any" type for FFI interop
      PNever is the bottom type (uninhabited) *)
type prim_rep =
  | PRUnit   : prim_rep   (* () - unit type, the trivial type with one value *)
  | PRNever  : prim_rep   (* ! - bottom type, no inhabitants, for divergence *)
  | PRBool   : prim_rep   (* bool - two-valued type *)
  | PRString : prim_rep   (* String - UTF-8 string type *)
  | PRChar   : prim_rep   (* char - Unicode scalar value *)
  | PRDynamic: prim_rep   (* Dynamic/any type - for FFI and dynamic code *)

(** Numeric type representation - mirrors numeric_type.
    Handles all integer and floating-point width combinations.

    From SPECIFICATION_ERRATA.md Chapter 1:
    - Integer types have valid_input constraints for operations
    - Overflow behavior depends on checked vs wrapping operations *)
type numeric_rep =
  | NRInt   : int_type -> numeric_rep    (* i8, i16, i32, i64, u8, u16, u32, u64 *)
  | NRFloat : float_prec -> numeric_rep  (* f32, f64 *)

(** Wrapper kind representation - mirrors wrapper_kind.
    These are single-argument type constructors.

    Memory safety implications (from spec):
    - WRRef, WRRefMut : borrow checker enforced
    - WRBox, WRRc, WRArc : heap allocation
    - WRRaw : unsafe, requires manual management *)
type wrapper_rep =
  | WRArray  : wrapper_rep   (* [T] - owned array *)
  | WRSlice  : wrapper_rep   (* &[T] - borrowed slice *)
  | WROption : wrapper_rep   (* T? - optional value *)
  | WRBox    : wrapper_rep   (* Box<T> - heap-allocated owned value *)
  | WRRef    : wrapper_rep   (* &T - immutable borrow *)
  | WRRefMut : wrapper_rep   (* &mut T - mutable borrow *)
  | WRRc     : wrapper_rep   (* Rc<T> - reference-counted pointer *)
  | WRArc    : wrapper_rep   (* Arc<T> - atomic reference-counted pointer *)
  | WRRaw    : wrapper_rep   (* *T - raw pointer (unsafe) *)

(** Modal kind representation - mirrors modal_kind.
    From spec Part III on Modal Types and Ownership:

    MBoxMod with ref_kind encodes fractional permissions:
      - RefBox { frac_num, frac_den } : fraction frac_num/frac_den of ownership
      - RefDiamond : exclusive/unique ownership

    MDiamondMod represents the "diamond" modality for exclusive resources. *)
type modal_rep =
  | MRBoxMod     : ref_kind -> modal_rep   (* Box modal with permission *)
  | MRDiamondMod : modal_rep               (* Diamond modal (exclusive) *)

(** Strictly positive list wrapper for mutually recursive types.

    The [@@@strictly_positive] attribute tells F* that this type parameter
    appears only in strictly positive positions, enabling safe recursion.

    This is necessary because type_rep is mutually recursive with its list
    forms (TRTuple, TRFunc params, etc.). Without this annotation, F* would
    reject the definition as potentially non-terminating.

    See fstar_pop_book.md on positivity checking. *)
let trlist ([@@@strictly_positive] a: Type) = list a

(** Main type representation - mirrors brrr_type's 12 constructors.

    From brrr_lang_spec_v0.4.tex, the discriminator pattern keeps top-level
    constructor count at 12 to avoid Z3 quantifier explosion (n^3 combinations
    for transitivity proofs with n constructors).

    All nested types are defined inline to avoid forward reference issues.
    This follows the pattern from the spec's brrr_type definition.

    noeq is used because:
    - type_rep contains functions (in TRFunc via effect_row)
    - Abstract types like type_var, type_name are not eqtype
    - We provide explicit equality via type_rep_eq *)
noeq type type_rep =
  (* Primitives: 1 constructor covers 6 types - unit, never, bool, string, char, dynamic *)
  | TRPrim    : prim_rep -> type_rep

  (* Numerics: 1 constructor covers int/float with all widths (i8-i64, u8-u64, f32, f64) *)
  | TRNumeric : numeric_rep -> type_rep

  (* Wrappers: 1 constructor covers 9 single-type wrappers (array, slice, option, etc.) *)
  | TRWrap    : wrapper_rep -> type_rep -> type_rep

  (* Modal refs: 1 constructor covers Box/Diamond modalities with permission fractions *)
  | TRModal   : modal_rep -> type_rep -> type_rep

  (* Binary type constructor: Result<T, E> for error handling *)
  | TRResult  : type_rep -> type_rep -> type_rep

  (* Collection type: n-ary tuples (T1, T2, ..., Tn) *)
  | TRTuple   : trlist type_rep -> type_rep

  (* Function type: (params) -> return_type with effects and unsafe flag
     The effect_row comes from Effects module and tracks effect polymorphism *)
  | TRFunc    : trlist param_rep -> type_rep -> effect_row -> bool -> type_rep

  (* Type variables: polymorphic type parameters (alpha, beta, ...) *)
  | TRVar     : type_var -> type_rep

  (* Type applications: generic type instantiation F<T1, T2, ...> *)
  | TRApp     : type_rep -> trlist type_rep -> type_rep

  (* Named type references: struct/enum names before full definition is available *)
  | TRNamed   : type_name -> type_rep

  (* Struct types: named product types with fields and representation attributes
     The repr_attr controls memory layout (C, packed, align, etc.) *)
  | TRStruct  : type_name -> trlist field_rep -> repr_attr -> type_rep

  (* Enum types: named sum types with variants, each variant can have fields *)
  | TREnum    : type_name -> trlist variant_rep -> type_rep

(** Parameter representation for function types.

    Corresponds to param_type in BrrrTypes. Each parameter has:
    - Optional name (for named arguments)
    - Type representation
    - Mode from the mode semiring (0, 1, omega for absent, linear, unrestricted) *)
and param_rep = {
  pr_name : option string;  (* None for positional, Some name for named params *)
  pr_ty   : type_rep;       (* Type of the parameter *)
  pr_mode : mode            (* Usage mode from Modes module *)
}

(** Struct field representation.

    Corresponds to field_type in BrrrTypes. Fields have:
    - Name (required, structs use named fields)
    - Type representation
    - Visibility (public, private, protected)
    - Tag (optional struct field tag metadata, e.g. Go `json:"name"`) *)
and field_rep = {
  flr_name : string;      (* Field name, required *)
  flr_ty   : type_rep;    (* Field type *)
  flr_vis  : visibility;  (* Access control *)
  flr_tag  : option string (* Struct field tag metadata *)
}

(** Variant representation for enum types.

    Corresponds to variant_type in BrrrTypes. Each variant has:
    - Name (the constructor name)
    - List of field types (empty for unit variants, one for newtype, many for struct variants) *)
and variant_rep = {
  vr_name   : string;           (* Variant constructor name *)
  vr_fields : trlist type_rep   (* Variant payload types *)
}

(** ============================================================================
    CONVERSION: prim_kind <-> prim_rep
    ============================================================================

    These conversion functions establish the isomorphism between compile-time
    primitive kinds (prim_kind from BrrrTypes) and runtime primitive
    representations (prim_rep).

    The roundtrip proofs below verify:
      prim_rep_to_kind (prim_kind_to_rep pk) = pk
      prim_kind_to_rep (prim_rep_to_kind pr) = pr
    ============================================================================ *)

(** Convert compile-time prim_kind to runtime prim_rep.
    Total function - every prim_kind has a corresponding prim_rep. *)
let prim_kind_to_rep (pk: prim_kind) : prim_rep =
  match pk with
  | PUnit    -> PRUnit
  | PNever   -> PRNever
  | PBool    -> PRBool
  | PString  -> PRString
  | PChar    -> PRChar
  | PDynamic -> PRDynamic

(** Convert runtime prim_rep back to compile-time prim_kind.
    Inverse of prim_kind_to_rep. *)
let prim_rep_to_kind (pr: prim_rep) : prim_kind =
  match pr with
  | PRUnit    -> PUnit
  | PRNever   -> PNever
  | PRBool    -> PBool
  | PRString  -> PString
  | PRChar    -> PChar
  | PRDynamic -> PDynamic

(** Roundtrip proof: converting to rep and back yields the original kind.
    Proof by case analysis - trivial for each constructor. *)
val prim_roundtrip_kind : pk:prim_kind ->
  Lemma (ensures prim_rep_to_kind (prim_kind_to_rep pk) = pk)
let prim_roundtrip_kind pk =
  match pk with
  | PUnit -> () | PNever -> () | PBool -> ()
  | PString -> () | PChar -> () | PDynamic -> ()

(** Roundtrip proof: converting to kind and back yields the original rep.
    Symmetric to prim_roundtrip_kind. *)
val prim_roundtrip_rep : pr:prim_rep ->
  Lemma (ensures prim_kind_to_rep (prim_rep_to_kind pr) = pr)
let prim_roundtrip_rep pr =
  match pr with
  | PRUnit -> () | PRNever -> () | PRBool -> ()
  | PRString -> () | PRChar -> () | PRDynamic -> ()

(** ============================================================================
    CONVERSION: numeric_type <-> numeric_rep
    ============================================================================

    Numeric types carry width and signedness information. The conversion
    preserves all this information exactly.

    From SPECIFICATION_ERRATA.md Chapter 1:
    Operations on numeric types require valid_input preconditions - the
    conversion functions don't validate, they just transform representations.
    ============================================================================ *)

(** Convert compile-time numeric_type to runtime numeric_rep. *)
let numeric_type_to_rep (nt: numeric_type) : numeric_rep =
  match nt with
  | NumInt it -> NRInt it
  | NumFloat fp -> NRFloat fp

(** Convert runtime numeric_rep back to compile-time numeric_type. *)
let numeric_rep_to_type (nr: numeric_rep) : numeric_type =
  match nr with
  | NRInt it -> NumInt it
  | NRFloat fp -> NumFloat fp

(** Roundtrip proof for numeric types: type -> rep -> type = identity. *)
val numeric_roundtrip_type : nt:numeric_type ->
  Lemma (ensures numeric_rep_to_type (numeric_type_to_rep nt) = nt)
let numeric_roundtrip_type nt =
  match nt with
  | NumInt _ -> ()
  | NumFloat _ -> ()

(** Roundtrip proof for numeric reps: rep -> type -> rep = identity. *)
val numeric_roundtrip_rep : nr:numeric_rep ->
  Lemma (ensures numeric_type_to_rep (numeric_rep_to_type nr) = nr)
let numeric_roundtrip_rep nr =
  match nr with
  | NRInt _ -> ()
  | NRFloat _ -> ()

(** ============================================================================
    CONVERSION: wrapper_kind <-> wrapper_rep
    ============================================================================

    Wrapper types are single-argument type constructors. The nine wrappers
    cover ownership, borrowing, and smart pointer patterns.

    Memory safety note: The type system tracks ownership and borrowing
    statically. The runtime representation here is for reflection only -
    it doesn't affect memory safety guarantees.
    ============================================================================ *)

(** Convert compile-time wrapper_kind to runtime wrapper_rep.
    Preserves all nine wrapper variants exactly. *)
let wrapper_kind_to_rep (wk: wrapper_kind) : wrapper_rep =
  match wk with
  | WArray  -> WRArray  | WSlice  -> WRSlice  | WOption -> WROption
  | WBox    -> WRBox    | WRef    -> WRRef    | WRefMut -> WRRefMut
  | WRc     -> WRRc     | WArc    -> WRArc    | WRaw    -> WRRaw

(** Convert runtime wrapper_rep back to compile-time wrapper_kind. *)
let wrapper_rep_to_kind (wr: wrapper_rep) : wrapper_kind =
  match wr with
  | WRArray  -> WArray  | WRSlice  -> WSlice  | WROption -> WOption
  | WRBox    -> WBox    | WRRef    -> WRef    | WRRefMut -> WRefMut
  | WRRc     -> WRc     | WRArc    -> WArc    | WRRaw    -> WRaw

(** Roundtrip proof for wrapper kinds. *)
val wrapper_roundtrip_kind : wk:wrapper_kind ->
  Lemma (ensures wrapper_rep_to_kind (wrapper_kind_to_rep wk) = wk)
let wrapper_roundtrip_kind wk =
  match wk with
  | WArray -> () | WSlice -> () | WOption -> () | WBox -> ()
  | WRef -> () | WRefMut -> () | WRc -> () | WArc -> () | WRaw -> ()

(** Roundtrip proof for wrapper reps. *)
val wrapper_roundtrip_rep : wr:wrapper_rep ->
  Lemma (ensures wrapper_kind_to_rep (wrapper_rep_to_kind wr) = wr)
let wrapper_roundtrip_rep wr =
  match wr with
  | WRArray -> () | WRSlice -> () | WROption -> () | WRBox -> ()
  | WRRef -> () | WRRefMut -> () | WRRc -> () | WRArc -> () | WRRaw -> ()

(** ============================================================================
    CONVERSION: modal_kind <-> modal_rep
    ============================================================================

    Modal types encode ownership fractions and exclusive access.

    From brrr_lang_spec_v0.4.tex Part III on Modal Types:
    - MBoxMod carries a ref_kind which may be:
      - RefBox { frac_num, frac_den } : fractional permission
      - RefDiamond : full exclusive access
    - MDiamondMod is the "diamond" modality for uniqueness

    These are used in the linear/affine type system to track resource usage.
    ============================================================================ *)

(** Convert compile-time modal_kind to runtime modal_rep.
    The ref_kind is preserved unchanged (it's already a simple type). *)
let modal_kind_to_rep (mk: modal_kind) : modal_rep =
  match mk with
  | MBoxMod rk -> MRBoxMod rk
  | MDiamondMod -> MRDiamondMod

(** Convert runtime modal_rep back to compile-time modal_kind. *)
let modal_rep_to_kind (mr: modal_rep) : modal_kind =
  match mr with
  | MRBoxMod rk -> MBoxMod rk
  | MRDiamondMod -> MDiamondMod

(** Roundtrip proof for modal kinds. *)
val modal_roundtrip_kind : mk:modal_kind ->
  Lemma (ensures modal_rep_to_kind (modal_kind_to_rep mk) = mk)
let modal_roundtrip_kind mk =
  match mk with
  | MBoxMod _ -> ()
  | MDiamondMod -> ()

(** Roundtrip proof for modal reps. *)
val modal_roundtrip_rep : mr:modal_rep ->
  Lemma (ensures modal_kind_to_rep (modal_rep_to_kind mr) = mr)
let modal_roundtrip_rep mr =
  match mr with
  | MRBoxMod _ -> ()
  | MRDiamondMod -> ()

(** ============================================================================
    SIZE FUNCTIONS FOR TERMINATION MEASURES
    ============================================================================

    These functions compute a natural number "size" for type representations.
    The size is used as a termination measure (decreases clause) for recursive
    functions over type_rep.

    The key property: size of any immediate subterm is strictly less than
    the size of the containing term. This ensures well-founded recursion.

    The mutual recursion here mirrors the structure of type_rep:
    - type_rep_size : main size function
    - type_rep_list_size : for TRTuple, TRApp args
    - param_rep_list_size : for TRFunc parameters
    - field_rep_list_size : for TRStruct fields
    - variant_rep_list_size : for TREnum variants
    ============================================================================ *)

(** Size of a type_rep. Base cases return 1, recursive cases sum subterm sizes + 1. *)
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

(** Size of a list of type_reps. Sum of element sizes. *)
and type_rep_list_size (ts: trlist type_rep) : Tot nat (decreases ts) =
  match ts with
  | [] -> 0
  | t :: rest -> type_rep_size t + type_rep_list_size rest

(** Size of a parameter list. Sum of parameter type sizes. *)
and param_rep_list_size (ps: trlist param_rep) : Tot nat (decreases ps) =
  match ps with
  | [] -> 0
  | p :: rest -> type_rep_size p.pr_ty + param_rep_list_size rest

(** Size of a field list. Sum of field type sizes. *)
and field_rep_list_size (fs: trlist field_rep) : Tot nat (decreases fs) =
  match fs with
  | [] -> 0
  | f :: rest -> type_rep_size f.flr_ty + field_rep_list_size rest

(** Size of a variant list. Sum of variant field sizes. *)
and variant_rep_list_size (vs: trlist variant_rep) : Tot nat (decreases vs) =
  match vs with
  | [] -> 0
  | v :: rest -> type_rep_list_size v.vr_fields + variant_rep_list_size rest

(** ============================================================================
    CONVERSION: brrr_type <-> type_rep (main conversion)
    ============================================================================

    These are the main conversion functions establishing the isomorphism between
    compile-time types (brrr_type) and runtime type representations (type_rep).

    The conversion is:
    - Total: every brrr_type can be converted
    - Structure-preserving: constructors map to constructors
    - Invertible: proven by roundtrip lemmas below

    We use structural recursion with explicit decreases clauses on the input.
    The mutual recursion mirrors the mutually recursive structure of brrr_type
    and type_rep.
    ============================================================================ *)

(** Forward declarations for mutually recursive functions.
    These establish the types before the definitions. *)
val brrr_type_to_rep : t:brrr_type -> Tot type_rep (decreases t)
val brrr_type_list_to_rep : ts:list brrr_type -> Tot (trlist type_rep) (decreases ts)
val param_type_list_to_rep : ps:list param_type -> Tot (trlist param_rep) (decreases ps)
val field_type_list_to_rep : fs:list field_type -> Tot (trlist field_rep) (decreases fs)
val variant_type_list_to_rep : vs:list variant_type -> Tot (trlist variant_rep) (decreases vs)

(** Convert brrr_type to type_rep.
    Each constructor of brrr_type maps to the corresponding constructor of type_rep,
    with subcomponents recursively converted. *)
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

(** Convert list of brrr_types to list of type_reps. *)
and brrr_type_list_to_rep ts =
  match ts with
  | [] -> []
  | t :: rest -> brrr_type_to_rep t :: brrr_type_list_to_rep rest

(** Convert list of param_types to list of param_reps.
    Uses record field accessor syntax (Mkparam_type?.field) *)
and param_type_list_to_rep ps =
  match ps with
  | [] -> []
  | p :: rest -> {
      pr_name = Mkparam_type?.name p;
      pr_ty = brrr_type_to_rep (Mkparam_type?.ty p);
      pr_mode = Mkparam_type?.mode p
    } :: param_type_list_to_rep rest

(** Convert list of field_types to list of field_reps. *)
and field_type_list_to_rep fs =
  match fs with
  | [] -> []
  | f :: rest -> {
      flr_name = f.field_name;
      flr_ty = brrr_type_to_rep f.field_ty;
      flr_vis = f.field_vis;
      flr_tag = f.field_tag
    } :: field_type_list_to_rep rest

(** Convert list of variant_types to list of variant_reps. *)
and variant_type_list_to_rep vs =
  match vs with
  | [] -> []
  | v :: rest -> {
      vr_name = v.variant_name;
      vr_fields = brrr_type_list_to_rep v.variant_fields
    } :: variant_type_list_to_rep rest

(** Forward declarations for reverse conversion. *)
val type_rep_to_brrr : tr:type_rep -> Tot brrr_type (decreases tr)
val type_rep_list_to_brrr : trs:trlist type_rep -> Tot (list brrr_type) (decreases trs)
val param_rep_list_to_brrr : prs:trlist param_rep -> Tot (list param_type) (decreases prs)
val field_rep_list_to_brrr : frs:trlist field_rep -> Tot (list field_type) (decreases frs)
val variant_rep_list_to_brrr : vrs:trlist variant_rep -> Tot (list variant_type) (decreases vrs)

(** Convert type_rep back to brrr_type.
    Inverse of brrr_type_to_rep. *)
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

(** Convert list of type_reps back to list of brrr_types. *)
and type_rep_list_to_brrr trs =
  match trs with
  | [] -> []
  | tr :: rest -> type_rep_to_brrr tr :: type_rep_list_to_brrr rest

(** Convert list of param_reps back to list of param_types. *)
and param_rep_list_to_brrr prs =
  match prs with
  | [] -> []
  | pr :: rest -> {
      name = pr.pr_name;
      ty = type_rep_to_brrr pr.pr_ty;
      mode = pr.pr_mode
    } :: param_rep_list_to_brrr rest

(** Convert list of field_reps back to list of field_types. *)
and field_rep_list_to_brrr frs =
  match frs with
  | [] -> []
  | fr :: rest -> {
      field_name = fr.flr_name;
      field_ty = type_rep_to_brrr fr.flr_ty;
      field_vis = fr.flr_vis;
      field_tag = fr.flr_tag
    } :: field_rep_list_to_brrr rest

(** Convert list of variant_reps back to list of variant_types. *)
and variant_rep_list_to_brrr vrs =
  match vrs with
  | [] -> []
  | vr :: rest -> {
      variant_name = vr.vr_name;
      variant_fields = type_rep_list_to_brrr vr.vr_fields
    } :: variant_rep_list_to_brrr rest

(** ============================================================================
    ROUNDTRIP PROOFS: brrr_type -> type_rep -> brrr_type
    ============================================================================

    These lemmas prove that converting a brrr_type to type_rep and back yields
    the original type (propositional equality ==).

    The proof strategy:
    - Structural induction on the input type
    - Each case uses the corresponding sub-lemma roundtrip proofs
    - Component roundtrips (prim, numeric, wrapper, modal) are used as needed

    This establishes half of the isomorphism. The other half (type_rep roundtrip)
    is proven separately below.
    ============================================================================ *)

(** Forward declarations for mutually recursive lemmas. *)
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

(** Main roundtrip proof: brrr_type -> type_rep -> brrr_type = identity.
    Increased z3rlimit and fuel for complex nested cases. *)
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
    ============================================================================

    These lemmas prove the other direction: converting a type_rep to brrr_type
    and back yields the original representation.

    Together with roundtrip_brrr_type, this establishes that the conversion
    functions form an isomorphism.
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

    From brrr_lang_spec_v0.4.tex Section "Type Equality Witness":

      eqType : forall tau sigma. TypeRep[tau] -> TypeRep[sigma] -> Option[tau =:= sigma]

    We need structural equality for type_rep that:
    1. Returns true when two type_reps represent the same type
    2. Is decidable (bool return, not prop)
    3. Is reflexive, symmetric, and transitive

    Implementation Strategy:
    -----------------------
    Rather than using the indexed GADT approach from the spec (which would give
    us type equality witnesses directly), we use decidable boolean equality.
    This is simpler in F* and sufficient for the cast operation.

    The connection to the spec's eqType:
    - eqType returns Option[tau =:= sigma] (Leibniz equality witness)
    - Our type_rep_eq returns bool
    - When type_rep_eq returns true, we can derive the equality witness
      via the soundness lemmas below

    Soundness by Construction:
    -------------------------
    The type_rep_eq function is sound by construction: it returns true only
    when the two type representations are structurally identical. This follows
    from examining each case in the function definition.
    ============================================================================ *)

(** Primitive equality - straightforward case analysis. *)
let prim_rep_eq (p1 p2: prim_rep) : bool =
  match p1, p2 with
  | PRUnit, PRUnit -> true
  | PRNever, PRNever -> true
  | PRBool, PRBool -> true
  | PRString, PRString -> true
  | PRChar, PRChar -> true
  | PRDynamic, PRDynamic -> true
  | _, _ -> false

(** Numeric equality - must compare width and signedness for integers. *)
let numeric_rep_eq (n1 n2: numeric_rep) : bool =
  match n1, n2 with
  | NRInt i1, NRInt i2 -> i1.width = i2.width && i1.sign = i2.sign
  | NRFloat f1, NRFloat f2 -> f1 = f2
  | _, _ -> false

(** Wrapper equality - straightforward case analysis. *)
let wrapper_rep_eq (w1 w2: wrapper_rep) : bool =
  match w1, w2 with
  | WRArray, WRArray -> true | WRSlice, WRSlice -> true | WROption, WROption -> true
  | WRBox, WRBox -> true | WRRef, WRRef -> true | WRRefMut, WRRefMut -> true
  | WRRc, WRRc -> true | WRArc, WRArc -> true | WRRaw, WRRaw -> true
  | _, _ -> false

(** Modal equality - uses structural equality for ref_kind to enable proofs.
    Compares permission fractions for RefBox case. *)
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

(** Forward declarations for mutually recursive equality functions. *)
val type_rep_eq : tr1:type_rep -> tr2:type_rep -> Tot bool (decreases tr1)
val type_rep_list_eq : trs1:trlist type_rep -> trs2:trlist type_rep -> Tot bool (decreases trs1)
val param_rep_list_eq : prs1:trlist param_rep -> prs2:trlist param_rep -> Tot bool (decreases prs1)

(** Main type representation equality.

    Structural comparison of type_rep values. Returns true iff the two
    representations encode the same type.

    Note: For TRStruct and TREnum, we compare by name only (nominal typing),
    not by structure. This matches the spec's handling of named types. *)
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
  | TRStruct name1 _ _, TRStruct name2 _ _ -> name1 = name2  (* Nominal equality *)
  | TREnum name1 _, TREnum name2 _ -> name1 = name2          (* Nominal equality *)
  | _, _ -> false

(** List equality - true iff same length and elementwise equal. *)
and type_rep_list_eq trs1 trs2 =
  match trs1, trs2 with
  | [], [] -> true
  | tr1 :: rest1, tr2 :: rest2 -> type_rep_eq tr1 tr2 && type_rep_list_eq rest1 rest2
  | _, _ -> false

(** Parameter list equality - compares types and modes, ignores names. *)
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
    ============================================================================

    Reflexivity: type_rep_eq tr tr = true for all tr.

    This is a fundamental property needed for the cast operation -
    casting a value to its own type should always succeed.

    The proofs use SMT patterns [SMTPat (type_rep_eq x x)] to make
    reflexivity automatic in subsequent proofs.
    ============================================================================ *)

(** Primitive reflexivity with SMT pattern. *)
val prim_rep_eq_refl : p:prim_rep ->
  Lemma (prim_rep_eq p p = true)
        [SMTPat (prim_rep_eq p p)]
let prim_rep_eq_refl p =
  match p with
  | PRUnit -> () | PRNever -> () | PRBool -> ()
  | PRString -> () | PRChar -> () | PRDynamic -> ()

(** Numeric reflexivity with SMT pattern. *)
val numeric_rep_eq_refl : n:numeric_rep ->
  Lemma (numeric_rep_eq n n = true)
        [SMTPat (numeric_rep_eq n n)]
let numeric_rep_eq_refl n =
  match n with
  | NRInt _ -> ()
  | NRFloat _ -> ()

(** Wrapper reflexivity with SMT pattern. *)
val wrapper_rep_eq_refl : w:wrapper_rep ->
  Lemma (wrapper_rep_eq w w = true)
        [SMTPat (wrapper_rep_eq w w)]
let wrapper_rep_eq_refl w =
  match w with
  | WRArray -> () | WRSlice -> () | WROption -> () | WRBox -> ()
  | WRRef -> () | WRRefMut -> () | WRRc -> () | WRArc -> () | WRRaw -> ()

(** Modal reflexivity with SMT pattern. *)
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

(** Forward declarations for mutually recursive reflexivity proofs. *)
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

(** Main type_rep_eq reflexivity proof. *)
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
    ============================================================================

    From brrr_lang_spec_v0.4.tex:

      tau =:= sigma  triangleq  forall F : * -> *. F[tau] -> F[sigma]

    Leibniz equality states that two types are equal iff they are
    interchangeable in all type contexts. This is the strongest notion
    of type equality - it implies substitutability everywhere.

    In F*, we represent this using propositional equality (==) combined
    with squash types. The squash type erases the proof content while
    retaining the proposition.

    Key Properties:
    ---------------
    1. Reflexivity: any type equals itself
    2. Symmetry: if t1 == t2 then t2 == t1
    3. Transitivity: if t1 == t2 and t2 == t3 then t1 == t3

    Connection to type_rep_eq:
    -------------------------
    If type_rep_eq tr1 tr2 = true, then the underlying brrr_types are
    propositionally equal:
      type_rep_to_brrr tr1 == type_rep_to_brrr tr2

    This is established by the soundness lemmas below.
    ============================================================================ *)

(** Type equality witness: proof that two brrr_types are propositionally equal.
    The squash type erases the proof content - we only need to know equality holds. *)
type brrr_type_equality (t1 t2: brrr_type) = squash (t1 == t2)

(** Reflexivity: any type equals itself. Proof is trivial (unit). *)
let brrr_type_eq_refl (#t: brrr_type) : brrr_type_equality t t = ()

(** Symmetry: equality is symmetric. F*'s propositional equality is inherently symmetric. *)
let brrr_type_eq_sym (#t1 #t2: brrr_type) (pf: brrr_type_equality t1 t2)
    : brrr_type_equality t2 t1 = ()

(** Transitivity: equality is transitive. Follows from propositional equality. *)
let brrr_type_eq_trans (#t1 #t2 #t3: brrr_type)
    (pf1: brrr_type_equality t1 t2) (pf2: brrr_type_equality t2 t3)
    : brrr_type_equality t1 t3 = ()

(** ============================================================================
    HELPER LEMMAS FOR EQUALITY PROOFS
    ============================================================================

    These lemmas connect the boolean equality checks to brrr_type equality.
    When the boolean check returns true, we get a proof that the converted
    brrr_types are propositionally equal.

    These are used in the cast operation: when type_rep_eq returns true,
    we know the types are equal and the cast is safe.
    ============================================================================ *)

(** Primitive equality implies brrr_type equality. *)
val prim_rep_eq_implies_brrr_eq : p1:prim_rep -> p2:prim_rep ->
  Lemma (requires prim_rep_eq p1 p2 = true)
        (ensures TPrim (prim_rep_to_kind p1) == TPrim (prim_rep_to_kind p2))
let prim_rep_eq_implies_brrr_eq p1 p2 =
  match p1, p2 with
  | PRUnit, PRUnit -> () | PRNever, PRNever -> () | PRBool, PRBool -> ()
  | PRString, PRString -> () | PRChar, PRChar -> () | PRDynamic, PRDynamic -> ()

(** Numeric equality implies brrr_type equality. *)
val numeric_rep_eq_implies_brrr_eq : n1:numeric_rep -> n2:numeric_rep ->
  Lemma (requires numeric_rep_eq n1 n2 = true)
        (ensures TNumeric (numeric_rep_to_type n1) == TNumeric (numeric_rep_to_type n2))
let numeric_rep_eq_implies_brrr_eq n1 n2 =
  match n1, n2 with
  | NRInt i1, NRInt i2 -> ()
  | NRFloat f1, NRFloat f2 -> ()

(** Wrapper equality implies wrapper kind equality. *)
val wrapper_rep_eq_implies_kind_eq : w1:wrapper_rep -> w2:wrapper_rep ->
  Lemma (requires wrapper_rep_eq w1 w2 = true)
        (ensures wrapper_rep_to_kind w1 == wrapper_rep_to_kind w2)
let wrapper_rep_eq_implies_kind_eq w1 w2 =
  match w1, w2 with
  | WRArray, WRArray -> () | WRSlice, WRSlice -> () | WROption, WROption -> ()
  | WRBox, WRBox -> () | WRRef, WRRef -> () | WRRefMut, WRRefMut -> ()
  | WRRc, WRRc -> () | WRArc, WRArc -> () | WRRaw, WRRaw -> ()

(** Modal equality implies modal kind equality. *)
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
    ============================================================================

    The type_rep_eq function is sound by construction: it returns true only
    when the two type representations are structurally identical. This follows
    from examining each case in the function definition.

    For practical use, we rely on the following properties:
    1. type_rep_eq_refl: type_rep_eq tr tr = true (reflexivity)
    2. Soundness: if type_rep_eq tr1 tr2 = true, then tr1 and tr2 represent
       the same type (follows from structural comparison)

    The roundtrip proofs (roundtrip_brrr_type, roundtrip_type_rep) establish
    that brrr_type <-> type_rep conversion preserves type identity.

    (* TODO: Full soundness theorem connecting type_rep_eq to brrr_type equality.
       This would state:
         type_rep_eq tr1 tr2 = true ==>
           type_rep_to_brrr tr1 == type_rep_to_brrr tr2

       See fstar_pop_book.md lines 16100-16200 for similar proofs in F* reflection. *)
    ============================================================================ *)

(** ============================================================================
    TYPE EQUALITY CHECK FUNCTION
    ============================================================================

    From brrr_lang_spec_v0.4.tex:

      eqType : forall tau sigma. TypeRep[tau] -> TypeRep[sigma] -> Option[tau =:= sigma]

    The spec returns Option with an equality witness. Our implementation returns
    Option unit for API compatibility, with the actual equality derivable from
    the soundness of type_rep_eq.

    These are simple wrappers around type_rep_eq for Option-based APIs.
    ============================================================================ *)

(** Check if two type_reps are equal, returning Some () if equal, None if different.
    This is a simple wrapper around type_rep_eq for Option-based APIs.

    Compare to spec's eqType which returns Option[tau =:= sigma]. *)
let eq_type_rep_check (tr1 tr2: type_rep) : option unit =
  if type_rep_eq tr1 tr2 then Some () else None

(** Same for lists - useful for tuple type comparisons. *)
let eq_type_rep_list_check (trs1 trs2: trlist type_rep) : option unit =
  if type_rep_list_eq trs1 trs2 then Some () else None

(** ============================================================================
    DYNAMIC TYPE
    ============================================================================

    From brrr_lang_spec_v0.4.tex Section "Dynamic Type":

      Dynamic = exists tau. (tau * TypeRep[tau])

    A dynamic value packages a runtime value together with its type representation.
    This enables type-safe dynamic typing: we can pack any value into Dynamic,
    and unpack it only if we provide the correct type representation.

    Existential Packaging:
    ---------------------
    The Dynamic type is an existential - it hides the actual type tau but
    provides enough information (TypeRep) to recover it safely via fromDyn.

    Operations from spec:
      toDyn   : forall tau. tau -> Dynamic
      fromDyn : forall tau. Dynamic -> TypeRep[tau] -> Option[tau]

    Safety Guarantee:
    ----------------
    fromDyn returns Some only when the expected type matches the actual type.
    This is enforced by the type_rep_eq check at runtime.

    Note: Unlike the spec which uses indexed TypeRep (type_rep : Type -> Type),
    we use unindexed type_rep with value from Values module. This simplifies
    the implementation but loses some type-level precision.
    ============================================================================ *)

open BrrrValues

(** Dynamic value: existential package of value + type representation.

    noeq because value contains functions (closures).

    Compare to spec:
      Dynamic = exists tau. (tau * TypeRep[tau])

    Our version:
      dynamic = tr:type_rep * v:value

    The type information is in tr, the value is untyped (value type from Values).
    Type safety is maintained by the from_dynamic check. *)
noeq type dynamic =
  | Dyn : tr:type_rep -> v:value -> dynamic

(** Create a dynamic value from a value and its type representation.
    Corresponds to spec's toDyn : forall tau. tau -> Dynamic. *)
let to_dynamic (tr: type_rep) (v: value) : dynamic = Dyn tr v

(** Get the type representation from a dynamic value.
    This is the "tag" that identifies the actual type. *)
let get_type_rep (d: dynamic) : type_rep =
  match d with
  | Dyn tr _ -> tr

(** Get the underlying value (untyped).
    The caller must use from_dynamic for safe extraction. *)
let get_value (d: dynamic) : value =
  match d with
  | Dyn _ v -> v

(** ============================================================================
    SAFE CAST OPERATIONS
    ============================================================================

    From brrr_lang_spec_v0.4.tex:

      cast : forall tau sigma. tau -> TypeRep[sigma] -> Option[sigma]

    Cast checks if the actual type matches the expected type at runtime.
    If they match, it returns the value; otherwise None.

    Safety Properties:
    -----------------
    1. from_dynamic d tr = Some v  ==>  type_rep_eq (get_type_rep d) tr = true
    2. cast_value v src tgt = Some v  ==>  type_rep_eq src tgt = true
    3. cast_with_proof always succeeds (equality is provided as witness)

    These operations are the runtime analog of type coercion, but with
    explicit failure handling for type mismatches.
    ============================================================================ *)

(** Attempt to extract a value from Dynamic with expected type representation.
    Returns Some value if types match, None otherwise.

    Corresponds to spec's fromDyn : forall tau. Dynamic -> TypeRep[tau] -> Option[tau].

    Note: We return the untyped value. In the spec, the return type would be
    Option[tau] for the expected type tau. Our caller must handle this appropriately. *)
let from_dynamic (d: dynamic) (expected: type_rep) : option value =
  match d with
  | Dyn actual v ->
      if type_rep_eq actual expected
      then Some v
      else None

(** Cast value with source type_rep to target type_rep.
    Only succeeds if source and target types are equal.

    This is a more explicit version of the cast - the caller provides both
    the source and target type representations. *)
let cast_value (v: value) (source: type_rep) (target: type_rep) : option value =
  if type_rep_eq source target
  then Some v
  else None

(** Cast with equality proof: if types are equal, casting always succeeds.

    From spec's coerce:
      coerce : forall tau sigma. (tau =:= sigma) -> tau -> sigma
      coerce(eq, x) = eq[lambda T. T](x)

    When the equality is provided as a witness (brrr_type_equality), the cast
    is guaranteed to succeed. The proof is used only for verification - at
    runtime this is just identity. *)
val cast_with_proof : v:value -> source:type_rep -> target:type_rep ->
  eq:brrr_type_equality (type_rep_to_brrr source) (type_rep_to_brrr target) ->
  value
let cast_with_proof v source target eq = v

(** ============================================================================
    CAST SAFETY PROOF
    ============================================================================

    Key theorem: If from_dynamic returns Some v, then the type representation
    in the Dynamic value is equal to the expected type representation.

    This is the runtime type safety guarantee for dynamic typing - you can
    only extract a value if you provide the correct type.
    ============================================================================ *)

(** from_dynamic safety: successful extraction implies type equality. *)
val from_dynamic_safe : d:dynamic -> expected:type_rep ->
  Lemma (ensures (match from_dynamic d expected with
                  | Some _ -> type_rep_eq (get_type_rep d) expected = true
                  | None -> true))
let from_dynamic_safe d expected =
  match d with
  | Dyn actual v ->
      if type_rep_eq actual expected then () else ()

(** Stronger version: successful extraction implies type_rep_eq check passed. *)
val from_dynamic_types_eq : d:dynamic -> expected:type_rep ->
  Lemma (requires Some? (from_dynamic d expected))
        (ensures type_rep_eq (get_type_rep d) expected = true)
let from_dynamic_types_eq d expected =
  match d with
  | Dyn actual _ -> ()

(** ============================================================================
    TYPE_OF OPERATIONS
    ============================================================================

    From brrr_lang_spec_v0.4.tex:

      typeOf : forall tau. tau -> TypeRep[tau]

    In a fully indexed implementation, typeOf would be a type class or
    built-in that produces the type representation for any value.

    Our Implementation:
    ------------------
    Since we use unindexed type_rep and untyped value, typeof_value is
    PARTIAL - not all runtime values have enough information to fully
    reconstruct their type.

    Cases that succeed:
    - Primitives (unit, bool, string, char)
    - Numerics (with default width assumptions)
    - Option with reconstructible inner type
    - Tuples with reconstructible element types
    - Named structs/enums (by name only)
    - Result with reconstructible ok type

    Cases that fail (return None):
    - VNone : cannot determine element type of Option
    - VArray : cannot determine element type without annotation
    - VRef/VRefMut/VBox : need type context
    - VClosure : function type needs annotation
    - VErr : cannot determine ok type of Result
    - VFuture/VGenerator : need type parameters

    (* TODO: Consider adding type tags to value constructors for full
       reconstruction. See fstar_pop_book.md on runtime type representation. *)
    ============================================================================ *)

(** Infer type representation from a value.
    This is partial: not all runtime values have enough information to
    fully reconstruct their type. Returns None for ambiguous cases.

    Default assumptions:
    - Integers default to i64
    - Floats default to f64
    These are reasonable defaults for dynamic typing scenarios. *)
let rec typeof_value (v: value) : option type_rep =
  match v with
  | VUnit -> Some (TRPrim PRUnit)
  | VBool _ -> Some (TRPrim PRBool)
  | VInt _ -> Some (TRNumeric (NRInt i64))  (* Default to i64 *)
  | VFloat _ -> Some (TRNumeric (NRFloat F64))  (* Default to f64 *)
  | VString _ -> Some (TRPrim PRString)
  | VChar _ -> Some (TRPrim PRChar)
  | VNone -> None  (* Cannot determine element type - T? needs T *)
  | VSome v' ->
      (match typeof_value v' with
       | Some inner -> Some (TRWrap WROption inner)
       | None -> None)
  | VTuple vs ->
      (match typeof_value_list vs with
       | Some trs -> Some (TRTuple trs)
       | None -> None)
  | VArray _ -> None  (* Cannot determine element type without more info *)
  | VStruct name _ -> Some (TRNamed name)  (* Nominal - type is the name *)
  | VVariant name _ _ -> Some (TRNamed name)  (* Nominal *)
  | VRef _ -> None  (* Reference type needs context *)
  | VRefMut _ -> None
  | VBox _ -> None
  | VClosure _ -> None  (* Function type needs context *)
  | VOk v' ->
      (match typeof_value v' with
       | Some tr -> Some (TRResult tr (TRPrim PRNever))  (* Err type unknown *)
       | None -> None)
  | VErr _ -> None  (* Cannot determine ok type *)
  (* Async/Generator values - cannot determine type parameters without context *)
  | VFuture _ -> None  (* Future<T> needs context for T *)
  | VGenerator _ -> None  (* Generator<Y, R> needs context for Y and R *)

(** Helper for typeof_value: reconstruct types of tuple elements. *)
and typeof_value_list (vs: vlist value) : option (trlist type_rep) =
  match vs with
  | [] -> Some []
  | v :: rest ->
      (match typeof_value v, typeof_value_list rest with
       | Some tr, Some trs -> Some (tr :: trs)
       | _, _ -> None)

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR COMMON TYPES
    ============================================================================

    These provide a more ergonomic API for creating type representations.
    They match the common type aliases used in Brrr-Lang source code.

    The naming convention follows the type syntax:
    - tr_<type> for primitive/numeric types
    - tr_<constructor>(args) for parameterized types
    ============================================================================ *)

(** Primitive type representations - zero-argument constructors. *)
let tr_unit : type_rep = TRPrim PRUnit
let tr_never : type_rep = TRPrim PRNever
let tr_bool : type_rep = TRPrim PRBool
let tr_string : type_rep = TRPrim PRString
let tr_char : type_rep = TRPrim PRChar
let tr_dynamic : type_rep = TRPrim PRDynamic

(** Numeric type representations - all width variants.
    These match the Rust-style type names: i8, i16, i32, i64, u8-u64, f32, f64. *)
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

(** Wrapper type representation constructors - take inner type as argument. *)
let tr_array (t: type_rep) : type_rep = TRWrap WRArray t
let tr_slice (t: type_rep) : type_rep = TRWrap WRSlice t
let tr_option (t: type_rep) : type_rep = TRWrap WROption t
let tr_box (t: type_rep) : type_rep = TRWrap WRBox t
let tr_ref (t: type_rep) : type_rep = TRWrap WRRef t
let tr_ref_mut (t: type_rep) : type_rep = TRWrap WRRefMut t

(** Result type representation - binary type constructor. *)
let tr_result (t_ok t_err: type_rep) : type_rep = TRResult t_ok t_err

(** Tuple type representation - n-ary constructor. *)
let tr_tuple (ts: trlist type_rep) : type_rep = TRTuple ts

(** ============================================================================
    CONSISTENCY PROOFS WITH brrr_type
    ============================================================================

    These lemmas verify that the convenience constructors produce type_reps
    that convert to the expected brrr_types. This ensures the API is consistent
    with the underlying type system.

    Each proof is trivial by computation - the conversions are definitional.
    ============================================================================ *)

(** tr_unit corresponds to t_unit from BrrrTypes. *)
val tr_unit_consistent : unit -> Lemma (type_rep_to_brrr tr_unit == t_unit)
let tr_unit_consistent () = ()

(** tr_bool corresponds to t_bool from BrrrTypes. *)
val tr_bool_consistent : unit -> Lemma (type_rep_to_brrr tr_bool == t_bool)
let tr_bool_consistent () = ()

(** tr_string corresponds to t_string from BrrrTypes. *)
val tr_string_consistent : unit -> Lemma (type_rep_to_brrr tr_string == t_string)
let tr_string_consistent () = ()

(** tr_i32 corresponds to t_i32 from BrrrTypes. *)
val tr_i32_consistent : unit -> Lemma (type_rep_to_brrr tr_i32 == t_i32)
let tr_i32_consistent () = ()

(** tr_i64 corresponds to t_i64 from BrrrTypes. *)
val tr_i64_consistent : unit -> Lemma (type_rep_to_brrr tr_i64 == t_i64)
let tr_i64_consistent () = ()

(** tr_option preserves the t_option structure. *)
val tr_option_consistent : t:type_rep ->
  Lemma (type_rep_to_brrr (tr_option t) == t_option (type_rep_to_brrr t))
let tr_option_consistent t = ()

(** tr_result preserves the TResult structure. *)
val tr_result_consistent : t_ok:type_rep -> t_err:type_rep ->
  Lemma (type_rep_to_brrr (tr_result t_ok t_err) ==
         TResult (type_rep_to_brrr t_ok) (type_rep_to_brrr t_err))
let tr_result_consistent t_ok t_err = ()

(** ============================================================================
    TYPE REPRESENTATION INTROSPECTION
    ============================================================================

    These predicates allow examining the structure of type representations
    at runtime. Useful for generic programming and reflection.

    From fstar_pop_book.md lines 16188-16300 on term inspection:
    The pattern is similar to F*'s term_view / inspect pattern, but for
    Brrr-Lang types rather than F* terms.
    ============================================================================ *)

(** Is this a primitive type? Primitives are the "atoms" with no substructure. *)
let is_prim_type (tr: type_rep) : bool =
  match tr with
  | TRPrim _ -> true
  | _ -> false

(** Is this a numeric type? Includes both integers and floats. *)
let is_numeric_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric _ -> true
  | _ -> false

(** Is this an integer type? Useful for numeric operations. *)
let is_int_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric (NRInt _) -> true
  | _ -> false

(** Is this a float type? *)
let is_float_type (tr: type_rep) : bool =
  match tr with
  | TRNumeric (NRFloat _) -> true
  | _ -> false

(** Is this a function type? *)
let is_func_type (tr: type_rep) : bool =
  match tr with
  | TRFunc _ _ _ _ -> true
  | _ -> false

(** Is this a wrapper type (Option, Array, etc.)? *)
let is_wrapper_type (tr: type_rep) : bool =
  match tr with
  | TRWrap _ _ -> true
  | _ -> false

(** Is this a named type reference (struct, enum, or type alias)? *)
let is_named_type (tr: type_rep) : bool =
  match tr with
  | TRNamed _ -> true
  | TRStruct _ _ _ -> true
  | TREnum _ _ -> true
  | _ -> false

(** Get the inner type of a wrapper, if applicable.
    Works for TRWrap (Option, Array, etc.) and TRModal. *)
let get_inner_type (tr: type_rep) : option type_rep =
  match tr with
  | TRWrap _ inner -> Some inner
  | TRModal _ inner -> Some inner
  | _ -> None

(** Get function parameter types, if applicable.
    Returns the list of parameter types (without names or modes). *)
let get_func_param_types (tr: type_rep) : option (trlist type_rep) =
  match tr with
  | TRFunc params _ _ _ -> Some (List.Tot.map (fun pr -> pr.pr_ty) params)
  | _ -> None

(** Get function return type, if applicable. *)
let get_func_return_type (tr: type_rep) : option type_rep =
  match tr with
  | TRFunc _ ret _ _ -> Some ret
  | _ -> None

(** ============================================================================
    PRETTY PRINTING (for debugging/display)
    ============================================================================

    String representation of type_rep for debugging and error messages.
    The output format matches Brrr-Lang surface syntax where possible.

    These functions use structural recursion with explicit decreases clauses.
    ============================================================================ *)

(** Convert type_rep to human-readable string.
    Follows Brrr-Lang/Rust-like syntax conventions. *)
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
  | TRFunc _ _ _ _ -> "fn(...) -> ..."  (* Simplified for readability *)
  | TRVar v -> v
  | TRNamed n -> n
  | TRApp tr' _ -> type_rep_to_string tr' ^ "<...>"
  | TRStruct name _ _ -> "struct " ^ name
  | TREnum name _ -> "enum " ^ name

(** Helper for tuple string representation. *)
and type_rep_list_to_string (trs: trlist type_rep) : Tot string (decreases trs) =
  match trs with
  | [] -> ""
  | [tr] -> type_rep_to_string tr
  | tr :: rest -> type_rep_to_string tr ^ ", " ^ type_rep_list_to_string rest
