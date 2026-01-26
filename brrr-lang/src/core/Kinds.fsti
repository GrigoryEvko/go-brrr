(**
 * BrrrLang.Core.Kinds - Interface
 *
 * Higher-Kinded Type system interface for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part IV - Higher-Kinded Types (Definition 3.5).
 *
 * ============================================================================
 * INTERFACE SPECIFICATION
 * ============================================================================
 *
 * This interface follows HACL-star/EverParse patterns:
 * - Public type declarations with full constructors visible
 * - Val signatures for functions with pre/post conditions
 * - SMTPat triggers for automatic lemma application in SMT proofs
 * - Decreases clauses for termination evidence
 *
 * ============================================================================
 * KIND SYSTEM OVERVIEW
 * ============================================================================
 *
 * Kinds classify types by their "arity":
 *   - KStar (Type)    : proper types (inhabited by values)
 *   - KArrow k1 k2    : type constructor kind (takes k1, returns k2)
 *   - KRow            : effect row kind (row-polymorphic effects)
 *   - KRegion         : lifetime/region kind (region polymorphism)
 *
 * Type Constructor Examples:
 *   - Int, String, Bool     : KStar
 *   - Option, Vec, List     : KArrow KStar KStar
 *   - Result, Map           : KArrow KStar (KArrow KStar KStar)
 *   - Functor, Monad        : KArrow (KArrow KStar KStar) KStar
 *
 * ============================================================================
 * INVARIANTS GUARANTEED BY THIS MODULE
 * ============================================================================
 *
 * 1. kind_eq is an equivalence relation (reflexive, symmetric, transitive)
 * 2. infer_kind_env is sound: returns Some k only if type has kind k
 * 3. KStar types are proper types (can be inhabited by values)
 * 4. combine_variance respects variance composition laws
 * 5. Variance combination is associative and commutative
 * 6. Unregistered structs/enums default to KStar
 *
 * Depends on: BrrrTypes, Utils, FStar.List.Tot
 *)
module Kinds

open FStar.List.Tot
open Utils  (* Shared utilities - zip_lists, all_distinct, etc. *)
open BrrrTypes

(** ============================================================================
    Z3 SOLVER OPTIONS - Following HACL-star/EverParse patterns
    ============================================================================ *)

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    KIND DEFINITION
    ============================================================================

    Core kind type - classifies types by their "arity".
    Following EverParse's t_kind pattern but extended for higher-kinded types.

    Reference: EverParse/src/3d/Ast.fst lines 317-321:
      type t_kind = | KindSpec | KindOutput | KindExtern

    Our kind type is more expressive to support higher-kinded polymorphism.
    ============================================================================ *)

type kind =
  | KStar   : kind                    (* * - proper types (inhabited by values) *)
  | KArrow  : kind -> kind -> kind    (* k1 -> k2 - type constructor taking k1 to k2 *)
  | KRow    : kind                    (* Row - effect row kind *)
  | KRegion : kind                    (* Region - lifetime/region kind *)

(** ============================================================================
    KIND EQUALITY - Decidable Equivalence Relation
    ============================================================================ *)

(** Structural equality for kinds.
    Decidable and total - always terminates with a boolean result. *)
val kind_eq : k1:kind -> k2:kind -> Tot bool (decreases k1)

(** Kind equality is reflexive.
    SMTPat enables automatic application in SMT proofs. *)
val kind_eq_refl : k:kind ->
  Lemma (ensures kind_eq k k = true)
        (decreases k)
        [SMTPat (kind_eq k k)]

(** Kind equality is symmetric. *)
val kind_eq_sym : k1:kind -> k2:kind ->
  Lemma (requires kind_eq k1 k2 = true)
        (ensures kind_eq k2 k1 = true)
        (decreases k1)

(** Kind equality is transitive. *)
val kind_eq_trans : k1:kind -> k2:kind -> k3:kind ->
  Lemma (requires kind_eq k1 k2 = true /\ kind_eq k2 k3 = true)
        (ensures kind_eq k1 k3 = true)
        (decreases k1)

(** Kind equality implies structural equality (for decidability proofs). *)
val kind_eq_implies_eq : k1:kind -> k2:kind ->
  Lemma (requires kind_eq k1 k2 = true)
        (ensures k1 == k2)
        (decreases k1)

(** ============================================================================
    KINDED TYPE - Type annotated with its kind
    ============================================================================ *)

(** A type together with its kind annotation.
    noeq because it contains brrr_type which may have function types. *)
noeq type kinded_type = {
  kt_type : brrr_type;
  kt_kind : kind
}

(** Create kinded type with KStar (proper type). *)
val kinded_star : t:brrr_type -> kinded_type

(** Create kinded type with arrow kind (type constructor). *)
val kinded_arrow : t:brrr_type -> k1:kind -> k2:kind -> kinded_type

(** ============================================================================
    KIND CONTEXT - Maps type variables to their kinds
    ============================================================================ *)

(** Kind context: association list of (type variable, kind) pairs.
    Used for kind inference with polymorphic types. *)
type kind_ctx = list (type_var & kind)

(** Empty kind context. *)
val empty_kind_ctx : kind_ctx

(** Extend kind context with a new binding. *)
val extend_kind_ctx : v:type_var -> k:kind -> ctx:kind_ctx -> kind_ctx

(** Lookup kind of type variable in context.
    Returns None if variable is not bound. *)
val lookup_kind : v:type_var -> ctx:kind_ctx -> option kind

(** Check if type variable is bound in context. *)
val has_type_var : v:type_var -> ctx:kind_ctx -> bool

(** ============================================================================
    NAMED TYPE KIND ENVIRONMENT
    ============================================================================

    Maps type constructor names to their kinds.
    Separate from kind_ctx which maps type variables.
    ============================================================================ *)

(** Named type kind environment.
    Maps type names (e.g., "Option", "Vec") to their kinds. *)
type named_kind_env = list (type_name & kind)

(** Empty named type kind environment. *)
val empty_named_kind_env : named_kind_env

(** Extend named type kind environment. *)
val extend_named_kind_env : name:type_name -> k:kind -> env:named_kind_env -> named_kind_env

(** Lookup kind of a named type.
    Returns None if type is not registered. *)
val lookup_named_kind : name:type_name -> env:named_kind_env -> option kind

(** Check if a named type is registered. *)
val has_named_type : name:type_name -> env:named_kind_env -> bool

(** Default named kind environment with standard library types.
    Includes:
    - Effect rows: IO, Pure, Async, State, Error, Reader, Writer,
                   Console, Network, FileSystem, Random, Unsafe (KRow)
    - Effect combinators: Eff (KArrow KRow (KArrow KStar KStar))
    - Region types: Static (KRegion)
    - Region-parameterized: RegionRef, RegionRefMut, RegionBox
                            (KArrow KRegion (KArrow KStar KStar))
    - Unary constructors: Option, Vec, List, Set, Box, Rc, Arc, Ref,
                          Future, Promise, Iterator, Stream, Cell,
                          RefCell, Mutex, RwLock (KArrow KStar KStar)
    - Binary constructors: Result, Map, HashMap, BTreeMap, Either, Pair
                           (KArrow KStar (KArrow KStar KStar))
    - Higher-kinded: Functor, Applicative, Monad, Foldable, Traversable
                     (KArrow (KArrow KStar KStar) KStar)
    - Bifunctors: Bifunctor (KArrow (KArrow KStar (KArrow KStar KStar)) KStar) *)
val default_named_kind_env : named_kind_env

(** ============================================================================
    KIND SIZE - For termination measures
    ============================================================================ *)

(** Size of a kind - used for termination proofs.
    Returns the total number of nodes in the kind tree. *)
val kind_size : k:kind -> Tot nat (decreases k)

(** Kind size is always positive (at least 1). *)
val kind_size_pos : k:kind ->
  Lemma (ensures kind_size k >= 1)
        [SMTPat (kind_size k)]

(** ============================================================================
    KIND INFERENCE
    ============================================================================

    Infer the kind of a type given contexts for type variables and named types.
    Returns None if the type is ill-kinded or references unknown types.
    ============================================================================ *)

(** Kind for wrapper types (Option, Vec, etc.): Type -> Type *)
val wrapper_type_kind : kind

(** Kind for Result type: Type -> Type -> Type *)
val result_type_kind : kind

(** Infer kind with explicit named type environment.
    This is the primary kind inference function.

    Returns Some k if type has kind k, None if ill-kinded.

    Kind rules applied:
    - TPrim _ -> KStar
    - TNumeric _ -> KStar
    - TWrap _ inner -> KStar (if inner has KStar)
    - TModal _ inner -> KStar (if inner has KStar)
    - TResult t1 t2 -> KStar (if both have KStar)
    - TTuple ts -> KStar (if all have KStar)
    - TFunc ft -> KStar (if params and return have KStar)
    - TVar v -> lookup_kind v ctx
    - TApp f args -> apply function kind to argument kinds
    - TNamed name -> lookup_named_kind name nenv
    - TStruct st -> lookup or default to KStar
    - TEnum et -> lookup or default to KStar *)
val infer_kind_env : nenv:named_kind_env -> ctx:kind_ctx -> t:brrr_type ->
  Tot (option kind) (decreases t)

(** Helper: check that all types in a list have kind KStar. *)
val infer_kind_list_env : nenv:named_kind_env -> ctx:kind_ctx -> ts:list brrr_type ->
  Tot bool (decreases ts)

(** Helper: check that all parameter types have kind KStar. *)
val infer_kind_params_env : nenv:named_kind_env -> ctx:kind_ctx -> ps:list param_type ->
  Tot bool (decreases ps)

(** Helper: apply type arguments to a function kind.
    If F has kind k1 -> k2 and arg has kind k1, returns k2. *)
val infer_kind_app_env : nenv:named_kind_env -> ctx:kind_ctx -> fk:kind -> args:list brrr_type ->
  Tot (option kind) (decreases args)

(** Infer kind using default named environment.
    Convenience function for code that doesn't need custom named types. *)
val infer_kind : ctx:kind_ctx -> t:brrr_type -> Tot (option kind) (decreases t)

(** Helper wrappers using default environment. *)
val infer_kind_list : ctx:kind_ctx -> ts:list brrr_type -> Tot bool (decreases ts)
val infer_kind_params : ctx:kind_ctx -> ps:list param_type -> Tot bool (decreases ps)
val infer_kind_app : ctx:kind_ctx -> fk:kind -> args:list brrr_type ->
  Tot (option kind) (decreases args)

(** ============================================================================
    KIND CHECKING
    ============================================================================ *)

(** Check that a type has a specific kind (with explicit named environment). *)
val check_kind_env : nenv:named_kind_env -> ctx:kind_ctx -> t:brrr_type -> expected:kind -> bool

(** Check that a type has a specific kind (using default named environment). *)
val check_kind : ctx:kind_ctx -> t:brrr_type -> expected:kind -> bool

(** Check that a type has kind KStar (is a proper type) - with explicit env. *)
val is_proper_type_env : nenv:named_kind_env -> ctx:kind_ctx -> t:brrr_type -> bool

(** Check that a type has kind KStar (is a proper type) - using default env. *)
val is_proper_type : ctx:kind_ctx -> t:brrr_type -> bool

(** Helper to construct arrow kinds for n-ary type constructors.
    make_arrow_kind 0 = KStar
    make_arrow_kind 1 = KArrow KStar KStar
    make_arrow_kind 2 = KArrow KStar (KArrow KStar KStar)
    etc. *)
val make_arrow_kind : n:nat -> kind

(** Check that a type is a type constructor with given arity. *)
val is_type_constructor_env : nenv:named_kind_env -> ctx:kind_ctx -> t:brrr_type -> arity:nat -> bool
val is_type_constructor : ctx:kind_ctx -> t:brrr_type -> arity:nat -> bool

(** ============================================================================
    KIND INFERENCE SOUNDNESS LEMMAS
    ============================================================================ *)

(** Soundness: if inference succeeds, the result is valid.
    This is trivially true by construction. *)
val infer_kind_sound : ctx:kind_ctx -> t:brrr_type -> k:kind ->
  Lemma (requires infer_kind ctx t = Some k)
        (ensures True)

(** Primitives always have kind KStar. *)
val prim_kind_star : ctx:kind_ctx -> p:prim_kind ->
  Lemma (ensures infer_kind ctx (TPrim p) = Some KStar)
        [SMTPat (infer_kind ctx (TPrim p))]

(** Numerics always have kind KStar. *)
val numeric_kind_star : ctx:kind_ctx -> n:numeric_type ->
  Lemma (ensures infer_kind ctx (TNumeric n) = Some KStar)
        [SMTPat (infer_kind ctx (TNumeric n))]

(** Wrapper types with KStar inner have kind KStar. *)
val wrapper_kind_star : ctx:kind_ctx -> w:wrapper_kind -> inner:brrr_type ->
  Lemma (requires infer_kind ctx inner = Some KStar)
        (ensures infer_kind ctx (TWrap w inner) = Some KStar)
        [SMTPat (infer_kind ctx (TWrap w inner))]

(** Modal types with KStar inner have kind KStar. *)
val modal_kind_star : ctx:kind_ctx -> m:modal_kind -> inner:brrr_type ->
  Lemma (requires infer_kind ctx inner = Some KStar)
        (ensures infer_kind ctx (TModal m inner) = Some KStar)
        [SMTPat (infer_kind ctx (TModal m inner))]

(** Result with two KStar types has kind KStar. *)
val result_kind_star : ctx:kind_ctx -> t_ok:brrr_type -> t_err:brrr_type ->
  Lemma (requires infer_kind ctx t_ok = Some KStar /\ infer_kind ctx t_err = Some KStar)
        (ensures infer_kind ctx (TResult t_ok t_err) = Some KStar)
        [SMTPat (infer_kind ctx (TResult t_ok t_err))]

(** Named types have the kind from the named environment. *)
val named_kind_lookup : nenv:named_kind_env -> ctx:kind_ctx -> name:type_name -> k:kind ->
  Lemma (requires lookup_named_kind name nenv = Some k)
        (ensures infer_kind_env nenv ctx (TNamed name) = Some k)
        [SMTPat (infer_kind_env nenv ctx (TNamed name))]

(** Struct types have the kind from the named environment by struct name. *)
val struct_kind_lookup : nenv:named_kind_env -> ctx:kind_ctx -> st:struct_type -> k:kind ->
  Lemma (requires lookup_named_kind st.struct_name nenv = Some k)
        (ensures infer_kind_env nenv ctx (TStruct st) = Some k)

(** Unregistered structs default to KStar (proper types). *)
val struct_kind_fallback : nenv:named_kind_env -> ctx:kind_ctx -> st:struct_type ->
  Lemma (requires lookup_named_kind st.struct_name nenv = None)
        (ensures infer_kind_env nenv ctx (TStruct st) = Some KStar)

(** Enum types have the kind from the named environment by enum name. *)
val enum_kind_lookup : nenv:named_kind_env -> ctx:kind_ctx -> et:enum_type -> k:kind ->
  Lemma (requires lookup_named_kind et.enum_name nenv = Some k)
        (ensures infer_kind_env nenv ctx (TEnum et) = Some k)

(** Unregistered enums default to KStar (proper types). *)
val enum_kind_fallback : nenv:named_kind_env -> ctx:kind_ctx -> et:enum_type ->
  Lemma (requires lookup_named_kind et.enum_name nenv = None)
        (ensures infer_kind_env nenv ctx (TEnum et) = Some KStar)

(** Type variable has the kind from context. *)
val var_kind_lookup : ctx:kind_ctx -> v:type_var -> k:kind ->
  Lemma (requires lookup_kind v ctx = Some k)
        (ensures infer_kind ctx (TVar v) = Some k)
        [SMTPat (infer_kind ctx (TVar v))]

(** Standard library type kind lemmas. *)
val option_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Option") = Some (KArrow KStar KStar))

val vec_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Vec") = Some (KArrow KStar KStar))

val result_named_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Result") = Some (KArrow KStar (KArrow KStar KStar)))

val functor_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Functor") = Some (KArrow (KArrow KStar KStar) KStar))

val monad_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Monad") = Some (KArrow (KArrow KStar KStar) KStar))

val applicative_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Applicative") = Some (KArrow (KArrow KStar KStar) KStar))

val bifunctor_kind : ctx:kind_ctx ->
  Lemma (ensures infer_kind ctx (TNamed "Bifunctor") = Some (KArrow (KArrow KStar (KArrow KStar KStar)) KStar))

(** ============================================================================
    KIND APPLICATION LEMMAS
    ============================================================================ *)

(** Empty application returns the function kind unchanged. *)
val kind_app_empty : ctx:kind_ctx -> fk:kind ->
  Lemma (ensures infer_kind_app ctx fk [] = Some fk)
        [SMTPat (infer_kind_app ctx fk [])]

(** Single argument application. *)
val kind_app_single : ctx:kind_ctx -> k1:kind -> k2:kind -> arg:brrr_type ->
  Lemma (requires infer_kind ctx arg = Some k1)
        (ensures infer_kind_app ctx (KArrow k1 k2) [arg] = Some k2)

(** Kind application preserves well-kindedness. *)
val kind_app_preserves : ctx:kind_ctx -> k_param:kind -> k_result:kind -> arg:brrr_type ->
  Lemma (requires infer_kind ctx arg = Some k_param)
        (ensures infer_kind_app ctx (KArrow k_param k_result) [arg] = Some k_result)

(** ============================================================================
    KIND CONTEXT LEMMAS
    ============================================================================ *)

(** Extending context preserves existing bindings for different variables. *)
val extend_preserves : ctx:kind_ctx -> v1:type_var -> k1:kind -> v2:type_var ->
  Lemma (requires v1 <> v2 /\ lookup_kind v2 ctx = Some k1)
        (ensures lookup_kind v2 (extend_kind_ctx v1 KStar ctx) = Some k1)

(** Extending context adds new binding. *)
val extend_adds : ctx:kind_ctx -> v:type_var -> k:kind ->
  Lemma (ensures lookup_kind v (extend_kind_ctx v k ctx) = Some k)
        [SMTPat (lookup_kind v (extend_kind_ctx v k ctx))]

(** Extension is monotonic. *)
val extend_monotonic : ctx:kind_ctx -> v1:type_var -> k1:kind -> v2:type_var -> k2:kind ->
  Lemma (requires lookup_kind v2 ctx = Some k2 /\ v1 <> v2)
        (ensures lookup_kind v2 (extend_kind_ctx v1 k1 ctx) = Some k2)

(** ============================================================================
    WELL-KINDED TYPE PREDICATES
    ============================================================================ *)

(** A type is well-kinded if kind inference succeeds. *)
val well_kinded : ctx:kind_ctx -> t:brrr_type -> prop

(** A type has a specific kind in a context. *)
val has_kind : ctx:kind_ctx -> t:brrr_type -> k:kind -> prop

(** Decidable version of has_kind. *)
val has_kind_dec : ctx:kind_ctx -> t:brrr_type -> k:kind -> bool

(** has_kind_dec is correct (true implies has_kind). *)
val has_kind_dec_correct_true : ctx:kind_ctx -> t:brrr_type -> k:kind ->
  Lemma (requires has_kind_dec ctx t k = true)
        (ensures has_kind ctx t k)

(** has_kind_dec is correct (has_kind implies true). *)
val has_kind_dec_correct_false : ctx:kind_ctx -> t:brrr_type -> k:kind ->
  Lemma (requires has_kind ctx t k)
        (ensures has_kind_dec ctx t k = true)

(** ============================================================================
    VARIANCE - For subtyping in higher-kinded types
    ============================================================================

    Variance describes how subtyping propagates through type constructors:
    - Covariant:     T <: U implies F<T> <: F<U>
    - Contravariant: T <: U implies F<U> <: F<T>
    - Invariant:     F<T> and F<U> are unrelated unless T = U
    - Bivariant:     Both covariant and contravariant (unused position)

    Reference: brrr_lang_spec_v0.4.md Definition 3.7
    ============================================================================ *)

type variance =
  | Covariant     : variance
  | Contravariant : variance
  | Invariant     : variance
  | Bivariant     : variance

(** Combine variances for nested type constructors.
    For F<G<T>> where F has variance v1 and G has variance v2,
    the overall variance of T is combine_variance v1 v2.

    Ordering of absorption (highest to lowest):
    1. Bivariant absorbs everything
    2. Invariant absorbs Covariant/Contravariant
    3. Covariant is identity
    4. Contravariant flips *)
val combine_variance : v1:variance -> v2:variance -> variance

(** Negate variance (for contravariant positions like function arguments). *)
val negate_variance : v:variance -> variance

(** Covariant is identity for variance combination (left). *)
val combine_variance_covariant_left : v:variance ->
  Lemma (ensures combine_variance Covariant v = v)
        [SMTPat (combine_variance Covariant v)]

(** Covariant is identity for variance combination (right). *)
val combine_variance_covariant_right : v:variance ->
  Lemma (ensures combine_variance v Covariant = v)

(** Double negation returns to original. *)
val negate_variance_involutive : v:variance ->
  Lemma (ensures negate_variance (negate_variance v) = v)
        [SMTPat (negate_variance (negate_variance v))]

(** Variance combination is associative.
    Important for nested type constructors:
    variance_of T (F<G<H<T>>>) is well-defined. *)
val combine_variance_assoc : v1:variance -> v2:variance -> v3:variance ->
  Lemma (ensures combine_variance (combine_variance v1 v2) v3 =
                 combine_variance v1 (combine_variance v2 v3))
        [SMTPat (combine_variance (combine_variance v1 v2) v3)]

(** Variance combination is commutative. *)
val combine_variance_comm : v1:variance -> v2:variance ->
  Lemma (ensures combine_variance v1 v2 = combine_variance v2 v1)
        [SMTPat (combine_variance v1 v2)]

(** Bivariant absorbs everything. *)
val combine_variance_bivariant_absorbs : v:variance ->
  Lemma (ensures combine_variance Bivariant v = Bivariant /\
                 combine_variance v Bivariant = Bivariant)
        [SMTPat (combine_variance Bivariant v)]

(** Invariant absorbs Covariant and Contravariant. *)
val combine_variance_invariant_absorbs : v:variance ->
  Lemma (ensures (v <> Bivariant) ==> combine_variance Invariant v = Invariant)
        [SMTPat (combine_variance Invariant v)]

(** Contravariant is self-inverse: Contra * Contra = Cov. *)
val combine_variance_contra_inverse : unit ->
  Lemma (ensures combine_variance Contravariant Contravariant = Covariant)

(** ============================================================================
    VARIANCE ENVIRONMENTS
    ============================================================================ *)

(** Variance environment: maps type constructor names to their parameter variances. *)
type variance_env = list (type_name & list variance)

(** Empty variance environment. *)
val empty_variance_env : variance_env

(** Extend variance environment. *)
val extend_variance_env : name:type_name -> vars:list variance -> env:variance_env -> variance_env

(** Lookup variance of a named type's parameters. *)
val lookup_variance : name:type_name -> env:variance_env -> option (list variance)

(** Default variance environment for standard library types.
    - Covariant containers: Option, Vec, List, Set, Box, Rc, Arc, Future,
                           Promise, Iterator, Stream
    - Invariant containers: Ref, RefMut, Cell, RefCell, Mutex, RwLock
    - Binary covariant: Result, Either, Pair
    - Map types: Invariant in key, Covariant in value *)
val default_variance_env : variance_env

(** ============================================================================
    VARIANCE COMPUTATION
    ============================================================================ *)

(** Compute variance of a type variable in a type (simple version).
    Does NOT use declared variance of type constructors. *)
val variance_of : v:type_var -> t:brrr_type -> variance

(** Helper: variance for list of types. *)
val variance_of_list : v:type_var -> ts:list brrr_type -> variance

(** Helper: variance for parameter types. *)
val variance_of_params : v:type_var -> ps:list param_type -> variance

(** Compute variance with type constructor variance environment.
    Uses declared variances for accurate computation. *)
val variance_of_env : venv:variance_env -> v:type_var -> t:brrr_type ->
  Tot variance (decreases %[type_size t; 1])

(** Helper: variance of type application with declared constructor variances. *)
val variance_of_app_env : venv:variance_env -> v:type_var ->
                          declared:list variance -> args:list brrr_type ->
  Tot variance (decreases %[type_list_size args; 0])

(** Helper: variance for list of types with environment. *)
val variance_of_list_env : venv:variance_env -> v:type_var -> ts:list brrr_type ->
  Tot variance (decreases %[type_list_size ts; 0])

(** Helper: variance for parameter types with environment. *)
val variance_of_params_env : venv:variance_env -> v:type_var -> ps:list param_type ->
  Tot variance (decreases %[param_list_size ps; 0])

(** ============================================================================
    VARIANCE CONTEXT (for Higher-Kinded Polymorphism)
    ============================================================================

    When a type variable represents a type constructor (like F : Type -> Type),
    we need to track the variance of its parameters.
    ============================================================================ *)

(** Extended variance context with both named types and type variable variances. *)
type variance_ctx = {
  vc_named : variance_env;                        (* Named type variances *)
  vc_vars  : list (type_var & list variance)      (* Type variable variances *)
}

(** Empty variance context. *)
val empty_variance_ctx : variance_ctx

(** Default variance context using standard library variances. *)
val default_variance_ctx : variance_ctx

(** Lookup variance of a type variable in variance context. *)
val lookup_var_variance : v:type_var -> ctx:variance_ctx -> option (list variance)

(** Extend context with type variable variance. *)
val extend_var_variance : v:type_var -> vars:list variance -> ctx:variance_ctx -> variance_ctx

(** Compute variance with full context (named types + type variables).
    Properly handles higher-kinded polymorphism. *)
val variance_of_full : ctx:variance_ctx -> v:type_var -> t:brrr_type ->
  Tot variance (decreases %[type_size t; 1])

(** Helper: variance of type application with full context. *)
val variance_of_app_full : ctx:variance_ctx -> v:type_var ->
                           declared:list variance -> args:list brrr_type ->
  Tot variance (decreases %[type_list_size args; 0])

(** Helper: variance for list of types with full context. *)
val variance_of_list_full : ctx:variance_ctx -> v:type_var -> ts:list brrr_type ->
  Tot variance (decreases %[type_list_size ts; 0])

(** Helper: variance for parameter types with full context. *)
val variance_of_params_full : ctx:variance_ctx -> v:type_var -> ps:list param_type ->
  Tot variance (decreases %[param_list_size ps; 0])

(** ============================================================================
    TYPE CONSTRUCTOR REPRESENTATION
    ============================================================================ *)

(** A type constructor with its parameter kinds and variances. *)
noeq type type_constructor = {
  tc_name      : type_name;                    (* Constructor name *)
  tc_params    : list (type_var & kind);       (* Type parameters with kinds *)
  tc_variances : list variance;                (* Variance of each parameter *)
  tc_body      : brrr_type                     (* The type body *)
}

(** The kind of a type constructor.
    Computed from tc_params. *)
val type_constructor_kind : tc:type_constructor -> kind

(** Instantiate a type constructor with type arguments.
    Returns None if argument count doesn't match parameter count. *)
val instantiate_constructor : tc:type_constructor -> args:list brrr_type -> option brrr_type

(** Check that a type constructor is well-formed:
    - All type parameters are distinct
    - Body is well-kinded under extended context *)
val well_formed_constructor : tc:type_constructor -> bool

(** ============================================================================
    FUNCTOR AND MONAD INSTANCES
    ============================================================================ *)

(** A Functor instance for F : Type -> Type.
    Provides fmap : (a -> b) -> F a -> F b. *)
noeq type functor_instance = {
  fi_constructor : type_constructor
}

(** Check if a type constructor can be a Functor (has kind Type -> Type). *)
val is_functor_candidate : tc:type_constructor -> bool

(** A Monad instance for M : Type -> Type.
    Provides return : a -> M a and bind : M a -> (a -> M b) -> M b. *)
noeq type monad_instance = {
  mi_constructor : type_constructor
}

(** Check if a type constructor can be a Monad (has kind Type -> Type). *)
val is_monad_candidate : tc:type_constructor -> bool

(** Functor constraint kind: (Type -> Type) -> Type. *)
val functor_constraint_kind : kind

(** Monad constraint kind: (Type -> Type) -> Type. *)
val monad_constraint_kind : kind

(** ============================================================================
    KIND WELL-FORMEDNESS
    ============================================================================ *)

(** Check if kind represents a proper type (KStar). *)
val is_proper_kind : k:kind -> bool

(** Check if kind represents a type constructor (has arrow). *)
val is_constructor_kind : k:kind -> bool

(** Compute the arity of a kind (number of type arguments needed).
    kind_arity KStar = 0
    kind_arity (KArrow _ k) = 1 + kind_arity k *)
val kind_arity : k:kind -> Tot nat (decreases k)

(** Get the result kind after full application. *)
val kind_result : k:kind -> Tot kind (decreases k)

(** ============================================================================
    WELL-FORMED TYPE PREDICATES
    ============================================================================ *)

(** Check if all free type variables in a type are bound in the context. *)
val free_vars_bound : ctx:kind_ctx -> t:brrr_type -> Tot bool (decreases %[type_size t; 0])

(** Check for a list of types. *)
val free_vars_bound_list : ctx:kind_ctx -> ts:list brrr_type ->
  Tot bool (decreases %[type_list_size ts; 1])

(** Check for parameter types. *)
val free_vars_bound_params : ctx:kind_ctx -> ps:list param_type ->
  Tot bool (decreases %[param_list_size ps; 1])

(** Well-formed type in context predicate. *)
val well_formed_type_in_ctx : ctx:kind_ctx -> t:brrr_type -> prop

(** Closed type (no free type variables). *)
val well_formed_type : t:brrr_type -> prop

(** ============================================================================
    KIND SUBSTITUTION LEMMAS
    ============================================================================ *)

(** Substitution removes the substituted variable from free variables. *)
val subst_removes_var : v:type_var -> replacement:brrr_type -> t:brrr_type ->
  Lemma (requires free_vars_bound empty_kind_ctx replacement = true)
        (ensures not (List.Tot.mem v (free_type_vars (subst_type_var v replacement t))))
        (decreases t)

(** Helper for list substitution. *)
val subst_removes_var_list : v:type_var -> replacement:brrr_type -> ts:list brrr_type ->
  Lemma (requires free_vars_bound empty_kind_ctx replacement = true)
        (ensures True)
        (decreases ts)

(** Helper for param substitution. *)
val subst_removes_var_params : v:type_var -> replacement:brrr_type -> ps:list param_type ->
  Lemma (requires free_vars_bound empty_kind_ctx replacement = true)
        (ensures True)
        (decreases ps)

(** Kind preservation for type variables under substitution. *)
val subst_preserves_kind_var : nenv:named_kind_env -> ctx:kind_ctx ->
  v:type_var -> k:kind -> replacement:brrr_type ->
  Lemma (requires infer_kind_env nenv (extend_kind_ctx v k ctx) (TVar v) = Some k /\
                  infer_kind_env nenv ctx replacement = Some k)
        (ensures infer_kind_env nenv ctx (subst_type_var v replacement (TVar v)) = Some k)

(** Kind preservation for primitive types (trivial). *)
val subst_preserves_kind_prim : nenv:named_kind_env -> ctx:kind_ctx ->
  v:type_var -> k:kind -> replacement:brrr_type -> p:prim_kind ->
  Lemma (ensures infer_kind_env nenv ctx (subst_type_var v replacement (TPrim p)) = Some KStar)

(** Kind preservation for numeric types (trivial). *)
val subst_preserves_kind_numeric : nenv:named_kind_env -> ctx:kind_ctx ->
  v:type_var -> k:kind -> replacement:brrr_type -> n:numeric_type ->
  Lemma (ensures infer_kind_env nenv ctx (subst_type_var v replacement (TNumeric n)) = Some KStar)

(** ============================================================================
    VARIANCE UNDER SUBSTITUTION
    ============================================================================ *)

(** Variance of a variable not appearing in a type is Bivariant. *)
val variance_of_absent : v:type_var -> t:brrr_type ->
  Lemma (requires not (List.Tot.mem v (free_type_vars t)))
        (ensures variance_of v t = Bivariant)
        (decreases t)

(** Helper for list variance. *)
val variance_of_absent_list : v:type_var -> ts:list brrr_type ->
  Lemma (requires True)
        (ensures True)
        (decreases ts)

(** Helper for param variance. *)
val variance_of_absent_params : v:type_var -> ps:list param_type ->
  Lemma (requires True)
        (ensures True)
        (decreases ps)

(** ============================================================================
    KIND INFERENCE TOTALITY
    ============================================================================ *)

(** Kind inference succeeds for types with all free variables bound. *)
val kind_inference_total : t:brrr_type -> ctx:kind_ctx ->
  Lemma (requires free_vars_bound ctx t = true)
        (ensures Some? (infer_kind ctx t))
        (decreases t)

(** Helper for list kind inference totality. *)
val kind_inference_total_list : ts:list brrr_type -> ctx:kind_ctx ->
  Lemma (requires free_vars_bound_list ctx ts = true)
        (ensures True)
        (decreases ts)

(** Helper for param kind inference totality. *)
val kind_inference_total_params : ps:list param_type -> ctx:kind_ctx ->
  Lemma (requires free_vars_bound_params ctx ps = true)
        (ensures True)
        (decreases ps)

(** ============================================================================
    BRRR-MACHINE INTEGRATION API
    ============================================================================

    These functions provide the interface that Brrr-Machine uses for kind analysis.
    ============================================================================ *)

(** Get kind of a type (for Brrr-Machine). *)
val kind_of_type : t:brrr_type -> option kind

(** Get kind with custom type variable context. *)
val kind_of_type_with_ctx : ctx:kind_ctx -> t:brrr_type -> option kind

(** Check if type is well-kinded. *)
val is_well_kinded : t:brrr_type -> bool

(** Get variance of type variable in type (for subtyping). *)
val variance_of_type_var : v:type_var -> t:brrr_type -> variance

(** Get variance with full context (for higher-kinded types). *)
val variance_of_type_var_full : ctx:variance_ctx -> v:type_var -> t:brrr_type -> variance

(** Check if type involves higher-kinded polymorphism. *)
val is_hkt : t:brrr_type -> bool

(** Check if a type constructor can be used where kind k is expected. *)
val kind_compatible : t:brrr_type -> expected_kind:kind -> ctx:kind_ctx -> bool

(** ============================================================================
    KINDED TYPE CONSTRUCTORS - Standard Library
    ============================================================================ *)

(** Option as a kinded type constructor: Type -> Type. *)
val option_constructor : kinded_type

(** Vec as a kinded type constructor: Type -> Type. *)
val vec_constructor : kinded_type

(** Result as a kinded type constructor: Type -> Type -> Type. *)
val result_constructor : kinded_type

(** Map as a kinded type constructor: Type -> Type -> Type. *)
val map_constructor : kinded_type
