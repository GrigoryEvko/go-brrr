(**
 * Brrr-Lang Translation Layer Specification - Interface
 *
 * Public interface for multi-language translation to Brrr-Lang IR.
 * Provides translation functors for:
 *   - Rust (ownership model, lifetimes, traits)
 *   - TypeScript (union types, gradual typing, async)
 *   - Go (interfaces, goroutines, channels)
 *
 * For Python translation, see PythonTranslation.fsti which provides
 * a complete implementation with comprehensive typing module support.
 *
 * Based on brrr_lang_spec_v0.4.md Part VI (Source Language Mapping)
 *)
module TranslationSpec

(** Z3 solver options - conservative settings for translation proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions

(** ============================================================================
    SOURCE LANGUAGE IDENTIFIER
    ============================================================================ *)

(** Source language identifier *)
type source_language =
  | LangRust
  | LangTypeScript
  | LangPython
  | LangGo
  | LangSwift
  | LangJava
  | LangC
  | LangCpp

(** ============================================================================
    LANGUAGE CONFIGURATION
    ============================================================================ *)

(** Memory model *)
type memory_mode =
  | MemOwnership   (* Affine types, move semantics - Rust *)
  | MemRC          (* Reference counting - Swift *)
  | MemGC          (* Garbage collection - Python, Go, TypeScript, Java *)
  | MemManual      (* Manual allocation - C/C++ *)

(** Type discipline *)
type type_mode =
  | TypeStatic     (* Fully static - Rust, Go, Java *)
  | TypeGradual    (* Gradual typing - TypeScript *)
  | TypeDynamic    (* Fully dynamic - Python *)

(** Null handling *)
type null_mode =
  | NullNonNull    (* No null - Rust Option, Swift Optional *)
  | NullOptional   (* Explicit optional types - Kotlin *)
  | NullNullable   (* Implicit nullable - Python, Go, Java, TypeScript *)

(** Effect tracking *)
type effect_mode =
  | EffPure        (* Effects tracked precisely *)
  | EffTracked     (* Effects tracked coarsely *)
  | EffUntracked   (* Effects not tracked *)

(** Concurrency model *)
type concurrency_mode =
  | ConcNone       (* No concurrency primitives *)
  | ConcThreads    (* OS threads - C/C++, Java *)
  | ConcAsync      (* Async/await - TypeScript, Rust, Swift *)
  | ConcCSP        (* CSP channels - Go *)
  | ConcActors     (* Actor model - Swift actors *)

(** Language configuration parameters *)
type lang_config : Type0

(** Get configuration for a language *)
val lang_config_of : source_language -> lang_config

(** ============================================================================
    TRANSLATION CONTEXT
    ============================================================================ *)

(** Translation context - carries state during translation *)
noeq type trans_ctx : Type0

(** Create initial translation context *)
val init_ctx : source_language -> trans_ctx

(** ============================================================================
    TRANSLATION RESULT
    ============================================================================ *)

(** Translation result - carries translated item plus any diagnostics *)
noeq type trans_result (a: Type) =
  | TransOk    : value:a -> trans_result a
  | TransApprox: value:a -> reason:string -> trans_result a
  | TransError : reason:string -> trans_result a

(** ============================================================================
    DEFAULT EFFECTS
    ============================================================================ *)

(** Default effect row for each language *)
val default_effects : source_language -> effect_row

(** ============================================================================
    RUST TRANSLATION
    ============================================================================ *)

(** Rust ownership annotation *)
type rust_ownership =
  | RsOwned
  | RsRef       : lifetime:string -> rust_ownership
  | RsRefMut    : lifetime:string -> rust_ownership
  | RsRc
  | RsArc
  | RsBox

(** Rust base type *)
noeq type rust_type : Type0

(** Rust expression AST *)
noeq type rust_expr : Type0

(** Borrow context tracks what's borrowed *)
noeq type borrow_ctx : Type0

(** Empty borrow context *)
val empty_borrow_ctx : borrow_ctx

(** Translate Rust base type to Brrr-Lang type *)
val translate_rust_base : rust_type -> brrr_type

(** Translate Rust ownership to Brrr-Lang mode *)
val translate_rust_ownership : rust_ownership -> mode

(** Translate Rust lifetime to Brrr-Lang region *)
val translate_rust_lifetime : string -> trans_ctx -> region

(** Full Rust type translation with ownership and lifetime *)
val translate_rust_type : rust_type -> rust_ownership -> trans_ctx -> (brrr_type & mode & option region)

(** Translate Rust expression to Brrr-Lang *)
val translate_rust_expr : rust_expr -> borrow_ctx -> trans_ctx -> trans_result expr

(** ============================================================================
    TYPESCRIPT TRANSLATION
    ============================================================================ *)

(** TypeScript type AST *)
noeq type ts_type : Type0

(** TypeScript expression AST *)
noeq type ts_expr : Type0

(** Translate TypeScript type to Brrr-Lang *)
val translate_ts_type : ts_type -> brrr_type

(** Translate TypeScript expression to Brrr-Lang *)
val translate_ts_expr : ts_expr -> trans_ctx -> trans_result expr

(** ============================================================================
    GO TRANSLATION
    ============================================================================ *)

(** Go type AST *)
noeq type go_type : Type0

(** Go expression AST *)
noeq type go_expr : Type0

(** Translate Go type to Brrr-Lang *)
val translate_go_type : go_type -> brrr_type

(** Translate Go expression *)
val translate_go_expr : go_expr -> trans_ctx -> trans_result expr

(** ============================================================================
    CROSS-LANGUAGE BOUNDARY HANDLING
    ============================================================================ *)

(** Language axioms - properties guaranteed by the language *)
type lang_axiom =
  | AxMemSafe    (* Memory safety *)
  | AxTypeSafe   (* Type safety *)
  | AxNullSafe   (* Null safety *)
  | AxRaceFree   (* Race freedom *)
  | AxLeakFree   (* Leak freedom *)
  | AxDetDrop    (* Deterministic destruction *)

(** Get axioms for a language *)
val language_axioms : source_language -> list lang_axiom

(** Compute boundary risks when crossing from L1 to L2 *)
val boundary_risks : from_lang:source_language -> to_lang:source_language -> list lang_axiom

(** Generate guard for boundary crossing *)
val generate_boundary_guard : from_lang:source_language -> to_lang:source_language ->
                              value:expr -> ty:brrr_type -> expr

(** ============================================================================
    SOUNDNESS PROPERTIES (THEOREMS)
    ============================================================================ *)

(** Approximation annotations for unsound features *)
type approx_reason =
  | ApproxDynamic
  | ApproxUnion
  | ApproxIntersection
  | ApproxDuckTyping
  | ApproxDecorator
  | ApproxAsync
  | ApproxChannel
  | ApproxInterface
  | ApproxLifetime
  | ApproxMacro

(** ============================================================================
    TYPE PRESERVATION THEOREM
    ============================================================================

    If e : tau in source language L, then T_L(e) : T_L(tau) in Brrr-Lang.
    This is stated informally as the translations preserve typing judgments.
    ============================================================================ *)

(** ============================================================================
    SEMANTIC PRESERVATION THEOREM
    ============================================================================

    If [[e]]_L(rho) = v in language L, then
    [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v).

    The translation preserves operational semantics up to the approximations
    documented by TransApprox results.
    ============================================================================ *)

(** ============================================================================
    COMPOSITIONALITY THEOREM
    ============================================================================

    For any context C and expression e:
    T_L(C[e]) = T_L(C)[T_L(e)]

    The translation is compositional - it can be applied to sub-expressions
    independently and the results compose correctly.
    ============================================================================ *)
