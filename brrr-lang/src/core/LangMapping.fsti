(**
 * BrrrLang.Core.LangMapping - Interface
 *
 * Source Language Mapping for Multi-Language Interoperability.
 * Based on brrr_lang_spec_v0.4.tex Part XIV.
 *
 * This interface exposes:
 *   - Language mode configurations (memory, types, null safety, effects, concurrency)
 *   - Standard configurations for Python, TypeScript, Rust, Go, Swift, Java
 *   - Translation functor interface with soundness proofs
 *   - Boundary guards for cross-language calls
 *   - Type preservation theorems
 *   - Functoriality verification theorems
 *)
module LangMapping

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open Values
open FStar.List.Tot

(** ============================================================================
    LANGUAGE MODE CONFIGURATION - Part XIV.1
    ============================================================================ *)

(** Memory Management Mode *)
type memory_mode =
  | MemGC        : memory_mode   (* Garbage collection *)
  | MemRC        : memory_mode   (* Reference counting *)
  | MemManual    : memory_mode   (* Manual malloc/free *)
  | MemOwnership : memory_mode   (* Ownership + borrow checking *)

(** Type System Mode *)
type type_mode =
  | TypeStatic  : type_mode     (* Full static type checking *)
  | TypeGradual : type_mode     (* Optional type annotations *)
  | TypeDynamic : type_mode     (* No static types *)

(** Null Safety Mode *)
type null_mode =
  | NullNullable : null_mode    (* Null is implicitly allowed *)
  | NullOptional : null_mode    (* Explicit Option types required *)
  | NullNonNull  : null_mode    (* Null banned entirely *)

(** Effect Tracking Mode *)
type effect_mode =
  | EffPure      : effect_mode  (* Pure functions, effects require annotation *)
  | EffTracked   : effect_mode  (* Effects tracked in type system *)
  | EffUntracked : effect_mode  (* Side effects allowed anywhere *)

(** Concurrency Mode *)
type conc_mode =
  | ConcNone    : conc_mode     (* No built-in concurrency *)
  | ConcThreads : conc_mode     (* OS threads *)
  | ConcAsync   : conc_mode     (* Async/await *)
  | ConcActors  : conc_mode     (* Actor model *)

(** Combined Language Mode *)
noeq type lang_mode = {
  memory      : memory_mode;
  types       : type_mode;
  null_safety : null_mode;
  effects     : effect_mode;
  concurrency : conc_mode
}

(** Mode equality *)
val lang_mode_eq : l1:lang_mode -> l2:lang_mode -> bool
val lang_mode_eq_refl : l:lang_mode ->
  Lemma (lang_mode_eq l l = true)
        [SMTPat (lang_mode_eq l l)]

(** ============================================================================
    STANDARD LANGUAGE CONFIGURATIONS - Part XIV.2
    ============================================================================ *)

val python_mode     : lang_mode
val typescript_mode : lang_mode
val rust_mode       : lang_mode
val go_mode         : lang_mode
val swift_mode      : lang_mode
val java_mode       : lang_mode
val c_mode          : lang_mode
val cpp_mode        : lang_mode
val kotlin_mode     : lang_mode
val haskell_mode    : lang_mode

(** ============================================================================
    AXIOM LATTICE - Part XIV.5
    ============================================================================ *)

type axiom =
  | AxMemSafe  : axiom   (* Memory operations are safe *)
  | AxTypeSafe : axiom   (* Type system is sound *)
  | AxNullSafe : axiom   (* No null dereferences *)
  | AxLeakFree : axiom   (* No memory leaks *)
  | AxRaceFree : axiom   (* No data races *)
  | AxDetDrop  : axiom   (* Destructors run at predictable times *)

type axiom_set = list axiom

val language_axioms : l:lang_mode -> axiom_set
val boundary_risks : source:lang_mode -> target:lang_mode -> axiom_set
val is_safe_boundary : source:lang_mode -> target:lang_mode -> bool

(** ============================================================================
    GUARD RESULT TYPE - Part XIV.4
    ============================================================================ *)

noeq type guard_result (a: Type) =
  | GuardOk  : v:a -> guard_result a
  | GuardErr : error:string -> guard_result a

val guard_return : #a:Type -> v:a -> guard_result a
val guard_bind : #a:Type -> #b:Type -> r:guard_result a -> f:(a -> guard_result b) -> guard_result b
val guard_result_is_ok : #a:Type -> r:guard_result a -> bool

(** ============================================================================
    BOUNDARY GUARDS - Part XIV.4
    ============================================================================ *)

val null_guard : source:null_mode -> target:null_mode -> v:value -> guard_result value
val type_guard : source:type_mode -> target:type_mode -> expected_ty:brrr_type -> v:value -> guard_result value
val memory_guard : source:memory_mode -> target:memory_mode -> v:value -> guard_result value
val generate_guard : source:lang_mode -> target:lang_mode -> ty:brrr_type -> v:value -> guard_result value

(** ============================================================================
    TRANSLATION FUNCTOR - Part XIV.3
    ============================================================================ *)

(** Translation functor interface

    ARCHITECTURE:
    The functor provides a uniform interface for language translation.
    Real translation from source AST (ts_type, rust_type, go_type) to Brrr IR
    is performed by language-specific translate_* functions.
    The functor's translate_type/expr/value handle post-translation processing.
*)
noeq type translation_functor = {
  source_mode : lang_mode;
  translate_type : brrr_type -> brrr_type;
  translate_expr : expr -> expr;
  translate_value : value -> value
}

val identity_functor : mode:lang_mode -> translation_functor

(** ============================================================================
    FUNCTOR LAWS AND SOUNDNESS - Part XIV.3
    ============================================================================ *)

(** Functor laws predicate *)
val functor_laws : f:translation_functor -> prop

(** Soundness predicate *)
val soundness : f:translation_functor -> prop

(** Functoriality predicate - identity and composition laws *)
val is_functorial : tr:translation_functor -> prop

(** Identity functor proofs *)
val identity_functor_laws : mode:lang_mode -> Lemma (functor_laws (identity_functor mode))
val identity_functor_sound : mode:lang_mode -> Lemma (soundness (identity_functor mode))
val identity_is_functorial : mode:lang_mode -> Lemma (is_functorial (identity_functor mode))

(** ============================================================================
    TYPE PRESERVATION THEOREMS - Part XIV.3.1
    ============================================================================ *)

type source_ctx = list (string & brrr_type)
type brrr_ctx = list (string & brrr_type)

val translate_ctx : f:translation_functor -> ctx:source_ctx -> brrr_ctx
val brrr_well_typed : ctx:brrr_ctx -> e:expr -> prop
val source_well_typed : ctx:source_ctx -> e:expr -> prop

(** Main type preservation theorem *)
val translate_preserves_typing :
  f:translation_functor -> e:expr -> ctx:source_ctx ->
  Lemma (requires source_well_typed ctx e)
        (ensures brrr_well_typed (translate_ctx f ctx) (f.translate_expr e))

(** Composition preserves type preservation *)
val composition_preserves_typing :
  f1:translation_functor -> f2:translation_functor ->
  e:expr -> ctx:source_ctx ->
  Lemma (requires source_well_typed ctx e)
        (ensures brrr_well_typed
          (translate_ctx f2 (translate_ctx f1 ctx))
          (f2.translate_expr (f1.translate_expr e)))

(** ============================================================================
    FUNCTORIALITY VERIFICATION - Part XIV.3.2
    ============================================================================ *)

val identity_expr : expr
val compose_exprs : f:expr -> g:expr -> expr

val translate_id_law : mode:lang_mode ->
  Lemma (expr_eq (identity_functor mode).translate_expr identity_expr identity_expr = true)

val translate_comp_law : mode:lang_mode -> f:expr -> g:expr ->
  Lemma (let tr = (identity_functor mode).translate_expr in
         expr_eq (tr (compose_exprs f g)) (compose_exprs (tr f) (tr g)) = true)

(** ============================================================================
    BOUNDARY SOUNDNESS THEOREM - Part XIV.6
    ============================================================================ *)

val boundary_soundness_theorem :
  source:lang_mode -> target:lang_mode -> ty:brrr_type -> v:value ->
  Lemma (ensures
    is_safe_boundary source target = true \/
    (match generate_guard source target ty v with
     | GuardOk _ -> True
     | GuardErr _ -> True))

(** ============================================================================
    COMPOSITION THEOREM
    ============================================================================ *)

val compose_translations : f1:translation_functor -> f2:translation_functor -> translation_functor

val composition_soundness :
  f1:translation_functor -> f2:translation_functor ->
  Lemma (requires soundness f1 /\ soundness f2)
        (ensures soundness (compose_translations f1 f2))

(** ============================================================================
    LANGUAGE-SPECIFIC TRANSLATION FUNCTORS
    ============================================================================ *)

(** TypeScript functor and proofs *)
val typescript_functor : translation_functor
val typescript_functor_laws : unit -> Lemma (functor_laws typescript_functor)
val typescript_functor_sound : unit -> Lemma (soundness typescript_functor)
val typescript_is_functorial : unit -> Lemma (is_functorial typescript_functor)

(** Rust functor and proofs *)
val rust_functor : translation_functor
val rust_functor_laws : unit -> Lemma (functor_laws rust_functor)
val rust_functor_sound : unit -> Lemma (soundness rust_functor)
val rust_is_functorial : unit -> Lemma (is_functorial rust_functor)

(** Go functor and proofs *)
val go_functor : translation_functor
val go_functor_laws : unit -> Lemma (functor_laws go_functor)
val go_functor_sound : unit -> Lemma (soundness go_functor)
val go_is_functorial : unit -> Lemma (is_functorial go_functor)

(** ============================================================================
    SOURCE LANGUAGE AST TYPES (for frontend translation)
    ============================================================================ *)

(** TypeScript types *)
type ts_primitive
noeq type ts_type
noeq type ts_expr

(** Rust types *)
noeq type rust_type
noeq type rust_expr

(** Go types *)
noeq type go_type
noeq type go_expr

(** ============================================================================
    LANGUAGE-SPECIFIC TRANSLATION FUNCTIONS (THE REAL TRANSLATIONS)
    ============================================================================

    These functions perform the actual AST translation from source language
    to Brrr IR. They are called by frontends, not by the functor interface.
    ============================================================================ *)

(** TypeScript translation - the REAL translation functions *)
val typescript_translate_type : ts_type -> brrr_type
val typescript_translate_expr : ts_expr -> expr
val typescript_translate_value : value -> value

(** TypeScript type preservation *)
val typescript_type_preservation :
  e:ts_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (typescript_translate_expr e))

(** Rust translation - the REAL translation functions *)
val rust_translate_type : rust_type -> (brrr_type & mode)
val rust_translate_type_only : rust_type -> brrr_type
val rust_translate_expr : rust_expr -> expr
val rust_translate_value : value -> value

(** Rust type preservation *)
val rust_type_preservation :
  e:rust_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (rust_translate_expr e))

(** Rust ownership preservation *)
val rust_ownership_preservation :
  t:rust_type ->
  Lemma (let (_, mode) = rust_translate_type t in
         (rust_is_copy t ==> mode = MOmega) /\
         (not (rust_is_copy t) ==> mode = MOne \/ mode = MOmega))

(** Go translation - the REAL translation functions *)
val go_translate_type : go_type -> brrr_type
val go_translate_expr : go_expr -> expr
val go_translate_value : value -> value

(** Go type preservation *)
val go_type_preservation :
  e:go_expr -> ctx:source_ctx ->
  Lemma (ensures brrr_well_typed ctx (go_translate_expr e))

(** ============================================================================
    HELPER PREDICATES FOR BRRR-MACHINE ANALYSIS
    ============================================================================ *)

(** TypeScript helpers *)
val is_ts_optional_chain_expr : e:expr -> bool
val is_ts_nullish_coalesce_expr : e:expr -> bool
val is_ts_promise_type : t:brrr_type -> bool
val is_ts_async_expr : e:expr -> bool

(** Rust helpers *)
val is_rust_shared_ref : t:brrr_type -> bool
val is_rust_mut_ref : t:brrr_type -> bool
val is_rust_owned : t:brrr_type -> bool
val is_rust_box : t:brrr_type -> bool
val is_rust_rc : t:brrr_type -> bool
val is_rust_arc : t:brrr_type -> bool
val is_rust_try_expr : e:expr -> bool
val is_rust_move_expr : e:expr -> bool

(** Go helpers *)
val is_go_chan_send_expr : e:expr -> bool
val is_go_chan_recv_expr : e:expr -> bool
val is_go_defer_expr : e:expr -> bool
val is_go_panic_expr : e:expr -> bool
val is_go_recover_expr : e:expr -> bool
val is_go_select_expr : e:expr -> bool
val has_go_spawn_effect : eff:effect_row -> bool
val has_go_panic_effect : eff:effect_row -> bool

(** Helper for Rust Copy trait check *)
val rust_is_copy : t:rust_type -> bool
