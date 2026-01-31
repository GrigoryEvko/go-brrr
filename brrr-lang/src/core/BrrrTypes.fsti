(**
 * BrrrLang.Core.Types - Interface
 *
 * Public interface for the Brrr-Lang type system with gradual typing support.
 * Based on brrr_lang_spec_v0.4.tex Parts II-III, Section 3 (Type System).
 *
 * GRADUAL TYPING OVERVIEW (Siek & Taha 2006):
 * ===========================================================================
 * Brrr-Lang implements gradual typing, allowing seamless mixing of static
 * and dynamic typing within the same program. Key concepts:
 *
 * - CONSISTENCY RELATION (~): Replaces strict equality for type checking
 *   * T ~ T (reflexivity)
 *   * Dynamic ~ T and T ~ Dynamic (dynamic is consistent with anything)
 *   * Unknown ~ T only via explicit casts
 *
 * - CASTS: Automatically inserted at static/dynamic boundaries
 *   * Compile-time: No overhead for consistent types
 *   * Runtime: Checked casts for Dynamic/Unknown conversions
 *
 * - BLAME TRACKING: Runtime errors point to the cast that failed
 *
 * DUAL TOP TYPES:
 * ===========================================================================
 * PDynamic (Dynamic): UNSAFE top type, like TypeScript's 'any'
 *   - Any operation allowed without type checking
 *   - Subtyping: forall T. T <: Dynamic
 *   - Use: FFI, unsafe code, legacy interop
 *   - WARNING: Bypasses type safety entirely!
 *
 * PUnknown (Unknown): SAFE top type, like TypeScript's 'unknown'
 *   - Operations require explicit type narrowing
 *   - Subtyping: forall T. T <: Unknown, but NOT Unknown <: T
 *   - Use: External input, deserialized data, safe heterogeneous containers
 *   - Safety: Must use type guards before operations
 *
 * F* INTERFACE PATTERNS (from HACL-star/EverParse):
 * ===========================================================================
 *   - unfold: Inline type aliases during verification (transparent to Z3)
 *   - inline_for_extraction: Inline during extraction to C/Rust/OCaml
 *   - [@(strict_on_arguments [n])]: Force evaluation of argument n
 *   - val ... : ... -> Tot ...: Total function (always terminates)
 *   - val ... : ... -> Lemma ...: Proof obligation (returns unit)
 *   - SMTPat: Z3 quantifier instantiation trigger
 *
 * SMT TRACTABILITY:
 * ===========================================================================
 * 12 type constructors (reduced from 27) for O(n^3) proof complexity:
 *   Original: 27^3 = 19,683 cases
 *   Optimized: 12^3 = 1,728 cases (91% reduction)
 *
 * REFERENCES:
 *   - Siek & Taha 2006: "Gradual Typing for Functional Languages"
 *   - Garcia et al. 2016: "Abstracting Gradual Typing" (POPL)
 *   - brrr_lang_spec_v0.4.tex Section 3 "Type System"
 *
 * Depends on: Primitives, Modes, Effects
 *)
module BrrrTypes

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open FStar.List.Tot

(* Z3 solver options for SMT tractability - following HACL-star/EverParse patterns
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

(** PRIMITIVE TYPE KINDS - 7 variants for atomic types

    These are the "base" types that don't contain other types.

    TYPE LATTICE POSITION (from bottom to top):
    - PNever:   Bottom type, subtype of all. No inhabitants.
    - PUnit:    Singleton type with single value ().
    - PBool/PString/PChar: Standard value types.
    - PUnknown: Safe top type - requires type guards for operations.
    - PDynamic: Unsafe top type - allows any operation unchecked.

    GRADUAL TYPING SEMANTICS (Siek & Taha 2006):

    PDynamic (UNSAFE top type):
      - Consistency: Dynamic ~ T for all T (bidirectional)
      - Subtyping: forall T. T <: Dynamic
      - Operations: Allowed WITHOUT runtime checks
      - Use cases: FFI, unsafe blocks, legacy code
      - DANGER: Defeats type safety guarantees!
      Example: let x: Dynamic = 42; x.someMethod() // No compile error!

    PUnknown (SAFE top type):
      - Consistency: T ~ Unknown only via explicit casts
      - Subtyping: forall T. T <: Unknown, but NOT Unknown <: T
      - Operations: REQUIRE type narrowing first
      - Use cases: User input, deserialized data, safe containers
      - Safety: Must use type guards or explicit casts
      Example:
        let x: Unknown = getUserInput();
        // x.someMethod()  // COMPILE ERROR: Unknown has no methods
        if let y: String = x as String {  // Runtime check
          y.len()  // OK: y is known to be String
        }

    Reference: brrr_lang_spec_v0.4.tex Section "Dynamic Type" and "Unknown Type"
*)
type prim_kind =
  | PUnit   : prim_kind   (** () - Unit type, single inhabitant. For side-effectful returns. *)
  | PNever  : prim_kind   (** ! - Bottom type, uninhabited. For diverging/panicking code. *)
  | PBool   : prim_kind   (** bool - Boolean: true or false. *)
  | PString : prim_kind   (** String - UTF-8 encoded text. *)
  | PChar   : prim_kind   (** char - Unicode scalar value (U+0000..U+10FFFF, no surrogates). *)
  | PDynamic: prim_kind   (** Dynamic - UNSAFE top (like 'any'). Operations unchecked. FFI use. *)
  | PUnknown: prim_kind   (** Unknown - SAFE top (like 'unknown'). Requires type guards. *)

(* Numeric types - integers and floats with width/precision
   Uses int_type and float_prec from Primitives module *)
type numeric_type =
  | NumInt   : int_type -> numeric_type    (* i8, i16, i32, i64, u8, u16, u32, u64 *)
  | NumFloat : float_prec -> numeric_type  (* f32, f64 *)

(* Numeric type equality - decidable, compares width and sign
   Exposed for type checking implementation *)
val numeric_eq : n1:numeric_type -> n2:numeric_type -> Tot bool

(** WRAPPER TYPE KINDS - 9 single-type wrappers

    Type constructors that wrap a single inner type.
    Critical property: VARIANCE (how inner subtyping affects outer subtyping).

    VARIANCE RULES:
    - Covariant (+): If A <: B then W<A> <: W<B>   [read-only]
    - Invariant (=): W<A> <: W<B> only if A = B   [read-write]

    WRAPPER VARIANCE:
    - WArray:   COVARIANT - [T] is read-only by default
    - WSlice:   COVARIANT - &[T] is a borrowed view
    - WOption:  COVARIANT - Option<A> <: Option<B> when A <: B
    - WBox:     COVARIANT - Box<T> owns but can be read as supertype
    - WRef:     COVARIANT - &T is shared (immutable) borrow
    - WRefMut:  INVARIANT - &mut T requires exact type for soundness!
    - WRc:      COVARIANT - Rc<T> is shared ownership
    - WArc:     COVARIANT - Arc<T> is thread-safe shared ownership
    - WRaw:     COVARIANT - *T raw pointer (unsafe defaults to covariant)

    WHY IS WRefMut INVARIANT?
    If &mut Cat <: &mut Animal were allowed:
      let cat: Cat = Cat();
      let animal_ref: &mut Animal = &mut cat;  // Hypothetically OK
      *animal_ref = Dog();  // Would write Dog into Cat storage!
    This violates memory safety. Hence &mut T is invariant in T.
*)
type wrapper_kind =
  | WArray  : wrapper_kind   (** [T] - Owned array, heap allocated, fixed size *)
  | WSlice  : wrapper_kind   (** &[T] - Borrowed slice, view into contiguous memory *)
  | WOption : wrapper_kind   (** T? / Option<T> - Optional value: None or Some(T) *)
  | WBox    : wrapper_kind   (** Box<T> - Owned heap allocation, single owner *)
  | WRef    : wrapper_kind   (** &T - Shared (immutable) borrow, COVARIANT *)
  | WRefMut : wrapper_kind   (** &mut T - Exclusive (mutable) borrow, INVARIANT *)
  | WRc     : wrapper_kind   (** Rc<T> - Reference counted, single-threaded sharing *)
  | WArc    : wrapper_kind   (** Arc<T> - Atomic ref counted, thread-safe sharing *)
  | WRaw    : wrapper_kind   (** *T - Raw pointer, requires unsafe to dereference *)

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

(** MODAL REFERENCE KINDS - Fractional permissions (Chapter 9)

    Encode FRACTIONAL PERMISSIONS from separation logic for fine-grained
    sharing control beyond Rust's simple borrow/own model.

    PERMISSION MODEL (Boyland 2003):
    - Permission 1 (full): exclusive read+write access
    - Permission 1/2: shared read-only access
    - Permission 1/4: shared with more parties
    - Permissions are ADDITIVE: 1/2 + 1/2 = 1

    MODAL KINDS:
    - MBoxMod (Box modality, []): Shared ref with permission fraction p
      * Syntax: []T @ p
      * p = 1: equivalent to exclusive ownership
      * p < 1: read-only shared access

    - MDiamondMod (Diamond modality, <>): Exclusive ref, full permission
      * Syntax: <>T
      * Always p = 1 (unique access)
      * Can read and write

    CONNECTION TO RUST:
    - &T is like []T @ (1/n) for n shared borrows
    - &mut T is like <>T (exclusive access)

    Reference: brrr_lang_spec_v0.4.tex Chapter 9 (Modal Types)
    Reference: Boyland 2003 "Checking Interference with Fractional Permissions"
*)
type modal_kind =
  | MBoxMod     : ref_kind -> modal_kind   (** []T @ p - Box modality: shared ref with permission p *)
  | MDiamondMod : modal_kind               (** <>T - Diamond modality: exclusive ref (permission = 1) *)

(** Modal kind equality - compares permission fractions.
    MBoxMod equal if permission fractions equal; MDiamondMod always equal. *)
val modal_eq : m1:modal_kind -> m2:modal_kind -> Tot bool

(** ============================================================================
    VISIBILITY - Access control for struct/enum fields and items
    ============================================================================

    Controls which code can access a field, method, or type definition.
    Follows Rust's visibility model with three access levels.

    SEMANTICS:
    - Public:  Accessible from any module in any crate (pub)
    - Private: Accessible only within the defining module (default)
    - Module:  Accessible within module hierarchy (pub(crate)/pub(super))

    IMPACT ON SUBTYPING:
    Private fields are NOT visible externally, so they don't affect
    structural subtyping relationships for external code.
*)

type visibility =
  | Public  : visibility   (** Accessible from anywhere - public API surface *)
  | Private : visibility   (** Accessible only within defining module - encapsulation *)
  | Module  : visibility   (** Accessible within module hierarchy - internal API *)

(** ============================================================================
    MEMORY REPRESENTATION ATTRIBUTES - ABI and layout control
    ============================================================================

    Control how structs and enums are laid out in memory.
    Corresponds to Rust's #[repr(...)] attributes.

    CRITICAL FOR:
    - FFI (Foreign Function Interface) with C code
    - Memory-mapped I/O and hardware registers
    - Network protocols with specific byte layouts
    - Performance optimization (cache alignment)

    REPR SEMANTICS:
    - ReprRust: Default, may reorder fields, NOT ABI stable
    - ReprC: C-compatible, declaration order, stable ABI
    - ReprPacked: No padding (alignment 1), may cause unaligned access
    - ReprTransparent: Same ABI as single non-ZST field (newtype wrapper)
    - ReprAlign(n): Minimum alignment of n bytes (power of 2)

    Reference: Rust Reference "Type Layout", Rustonomicon "repr(C)"
*)

(** Power of 2 check for alignment values.
    CPU memory alignment must be powers of 2 for efficient access. *)
val is_power_of_2 : n:pos -> Tot bool (decreases n)

(** Valid alignment: positive power of 2, at most 2^29 (536MB).
    Refinement type ensures only valid alignments can be constructed.
    The upper bound avoids overflow in alignment calculations. *)
unfold
type valid_alignment = n:pos{is_power_of_2 n && n <= 536870912}

(** Memory layout representation - affects ABI compatibility *)
type repr_attr =
  | ReprRust        : repr_attr   (** Default Rust layout - may reorder fields, not ABI stable *)
  | ReprC           : repr_attr   (** C-compatible layout - stable ABI, no field reordering *)
  | ReprPacked      : repr_attr   (** No padding - alignment 1, may cause unaligned access *)
  | ReprTransparent : repr_attr   (** Same ABI as single field - for FFI-safe newtype wrappers *)
  | ReprAlign       : valid_alignment -> repr_attr  (** Explicit alignment in bytes *)

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
  field_vis  : visibility;
  field_tag  : option string       (* Struct field tag metadata, e.g. Go `json:"name"` *)
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
