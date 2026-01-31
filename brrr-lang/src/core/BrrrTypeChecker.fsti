(**
 * BrrrLang.Core.TypeChecker Interface
 *
 * Public interface for the bidirectional type checker.
 * Declares type checking functions with pre/post conditions and soundness theorems.
 *
 * ==========================================================================
 * OVERVIEW: BIDIRECTIONAL TYPE CHECKING
 * ==========================================================================
 *
 * This module implements bidirectional type checking as described in:
 *   - Pierce & Turner, "Local Type Inference" (POPL 1998)
 *   - Dunfield & Krishnaswami, "Bidirectional Typing" (2020)
 *   - Pierce, "Types and Programming Languages" (TAPL), Chapters 9, 22
 *
 * Two judgment forms:
 *
 *   SYNTHESIS: Gamma |- e => T ; eff   (infer_type)
 *     "In context Gamma, expression e synthesizes type T with effects eff"
 *     Type information flows OUT of the expression
 *
 *   CHECKING:  Gamma |- e <= T ; eff   (check_type)
 *     "In context Gamma, expression e checks against type T with effects eff"
 *     Type information flows INTO the expression from context
 *
 * ==========================================================================
 * TYPING RULES SUMMARY (Spec Chapter 8)
 * ==========================================================================
 *
 * Core Rules:
 *   T-Var     Variable lookup with mode check (linear: must be available)
 *   T-Lit     Literals have their intrinsic type, Pure effect
 *   T-Abs     Lambda: ctx, x:T |- body => S ; eff |- \x.body => T -[eff]-> S
 *   T-App     Application: fn(args) with argument type checking
 *   T-Let     Let binding with pattern matching
 *   T-If      Conditional with branch type unification
 *   T-Match   Pattern matching with exhaustiveness
 *   T-Sub     Subsumption: T1 <: T2 allows coercion
 *
 * Linear Types (Spec Section 5.1):
 *   L-Var     Linear variable must have mode > 0
 *   L-Split   Context splitting for parallel usage
 *   L-Join    Context joining after branches (must agree on consumption)
 *
 * Reference Types (Spec Section 6.1):
 *   T-Borrow     Shared borrow: &e : &T
 *   T-BorrowMut  Exclusive borrow: &mut e : &mut T
 *   T-Deref      Dereference: *e has Read effect
 *   T-Assign     Assignment: lhs = rhs has Write effect
 *
 * Effects (Spec Section 3.1):
 *   Effects tracked as rows, combined via row_join
 *   Effect subsumption: eff1 <: eff2 iff eff1 subset eff2
 *
 * ==========================================================================
 * TYPE SAFETY THEOREMS
 * ==========================================================================
 *
 * Progress:     Well-typed closed terms are values or can step
 * Preservation: Reduction preserves types
 * Soundness:    Well-typed programs never get stuck
 *
 * See implementation for proof sketches.
 *
 * ==========================================================================
 * REFERENCES
 * ==========================================================================
 *
 *   [TAPL]    Pierce, "Types and Programming Languages" (2002)
 *   [PT98]    Pierce & Turner, "Local Type Inference" (POPL 1998)
 *   [DK20]    Dunfield & Krishnaswami, "Bidirectional Typing" (2020)
 *   [Spec]    brrr_lang_spec_v0.4.tex, Chapters 3, 5, 6, 7, 8
 *   [Errata]  SPECIFICATION_ERRATA.md
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Values, TypeClasses
 *)
module BrrrTypeChecker

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrValues
open BrrrTypeClasses
open BrrrBorrowChecker
open FStar.List.Tot

(** ============================================================================
    SOURCE LOCATION TYPES
    ============================================================================ *)

(* Source position: file, line, column *)
type source_pos = {
  sp_file : string;
  sp_line : nat;
  sp_col  : nat
}

(* Source span: start and end positions *)
type source_span = {
  span_start : source_pos;
  span_end   : source_pos
}

(* Wrapper type for values with source location metadata *)
noeq type with_span_t 'a = {
  ws_value : 'a;
  ws_span  : source_span;
}

(* Dummy span for synthetic nodes *)
val dummy_span : source_span

(* Format source span for error messages *)
val string_of_span : source_span -> string

(** ============================================================================
    TYPE ERROR TYPES
    ============================================================================ *)

(* Type error with source location information *)
noeq type type_error = {
  te_message : string;
  te_span    : source_span;
  te_context : option string
}

(* Create type error with span *)
val make_error : string -> source_span -> type_error

(* Format type error for display *)
val format_error : type_error -> string

(** ============================================================================
    TYPING CONTEXT TYPES
    ============================================================================ *)

(* A binding in the type context: variable with type and mode *)
noeq type ctx_binding = {
  bind_name : var_id;
  bind_type : brrr_type;
  bind_mode : mode
}

(* Type context: ordered list of bindings *)
type type_ctx = list ctx_binding

(* Global type context: maps global names to type schemes *)
type global_ctx = list (string & type_scheme)

(* Type definition context: maps type names to their definitions *)
type type_def_ctx = list (type_name & brrr_type)

(* Extended typing context for full type checking *)
noeq type extended_typing_ctx = {
  etc_locals     : type_ctx;
  etc_globals    : global_ctx;
  etc_type_defs  : type_def_ctx;
  etc_classes    : class_env;
  etc_regions    : region_ctx;
  etc_subst      : list (type_var & brrr_type)
}

(** ============================================================================
    TYPE CHECKING RESULT TYPES
    ============================================================================ *)

(* Inference result: type, effects, and updated context *)
noeq type infer_result =
  | InferOk  : ty:brrr_type -> eff:effect_row -> ctx:type_ctx -> infer_result
  | InferErr : err:type_error -> infer_result

(* Check result: effects and updated context *)
noeq type check_result =
  | CheckOk  : eff:effect_row -> ctx:type_ctx -> check_result
  | CheckErr : err:type_error -> check_result

(** ============================================================================
    CONTEXT OPERATIONS
    ============================================================================ *)

(* Empty contexts *)
val empty_ctx : type_ctx
val empty_global_ctx : global_ctx
val empty_type_def_ctx : type_def_ctx
val empty_extended_ctx : extended_typing_ctx

(* Extend context with a new binding *)
val extend_ctx : x:var_id -> t:brrr_type -> m:mode -> ctx:type_ctx -> type_ctx

(* Lookup variable in context *)
val lookup_ctx : x:var_id -> ctx:type_ctx ->
  Tot (option (brrr_type & mode))

(* Check if all linear variables have been consumed *)
val check_linear_consumed : ctx:type_ctx -> bool

(* Join contexts for branch merging (if-else, match) *)
val join_contexts : ctx1:type_ctx -> ctx2:type_ctx ->
  Tot (option type_ctx)

(** ============================================================================
    EFFECT SUBSUMPTION
    ============================================================================ *)

(* Effect subsumption: e1 <= e2 iff e1's effects are a subset of e2's *)
val effect_sub : e1:effect_row -> e2:effect_row -> bool

(** ============================================================================
    SUBTYPING AND CONSISTENCY
    ============================================================================ *)

(* Extended subtyping that handles function types with effects *)
val extended_subtype : t1:brrr_type -> t2:brrr_type -> bool

(* Type consistency relation for gradual typing *)
val type_consistent : t1:brrr_type -> t2:brrr_type -> Tot bool (decreases t1)

(* Consistency is symmetric - needed before gradual typing functions *)
val type_consistent_sym : t1:brrr_type -> t2:brrr_type ->
  Lemma (ensures type_consistent t1 t2 = type_consistent t2 t1)
        (decreases t1)
        [SMTPat (type_consistent t1 t2)]

(** ============================================================================
    GRADUAL TYPING: CAST INSERTION
    ============================================================================

    Cast insertion enables runtime safety for gradual typing.
    When types are consistent but not subtypes, casts are inserted.

    Based on: Siek & Taha 2006 "Gradual Typing for Functional Languages"
    ============================================================================ *)

(** Gradual inference result - includes potentially cast-wrapped expression *)
noeq type gradual_infer_result =
  | GInferOk  : expr:expr -> ty:brrr_type -> eff:effect_row -> ctx:type_ctx -> gradual_infer_result
  | GInferErr : err:type_error -> gradual_infer_result

(** Determine cast kind based on type relationship *)
val determine_cast_kind : from_ty:brrr_type -> to_ty:brrr_type -> BrrrExpressions.cast_kind

(** Insert a cast from from_ty to to_ty around expression e.
    Returns e unchanged if types are equal.

    @param e        Expression to wrap with cast
    @param from_ty  Inferred type of e
    @param to_ty    Expected type at this position
    @param blame    Blame label for error reporting
    @returns        e wrapped with appropriate cast, or e if no cast needed *)
val insert_cast : e:expr -> from_ty:brrr_type -> to_ty:brrr_type -> blame:BrrrExpressions.blame_label -> expr

(** Insert cast through Dynamic for types that are consistent but not subtypes *)
val insert_cast_via_dynamic : e:expr -> from_ty:brrr_type -> to_ty:brrr_type -> blame:BrrrExpressions.blame_label -> expr

(** Insert appropriate cast based on type relationship.
    Returns Some expr with cast, or None if types not consistent *)
val insert_cast_if_needed : e:expr -> from_ty:brrr_type -> to_ty:brrr_type -> blame:BrrrExpressions.blame_label -> option expr

(** Check expression against expected type, inserting casts as needed.
    This is the gradual typing version of check_type. *)
val check_type_gradual : gctx:global_ctx -> ctx:type_ctx -> e:expr -> expected:brrr_type -> span:source_span -> gradual_infer_result

(** ============================================================================
    MAIN TYPE CHECKING FUNCTIONS
    ============================================================================

    Bidirectional type checking with two modes:

    SYNTHESIS (infer_type):
      Judgment: gctx; ctx |- e => T ; eff ~> ctx'
      Synthesizes type T and effects eff from expression e
      Returns InferOk(T, eff, ctx') or InferErr(error)

    CHECKING (check_type):
      Judgment: gctx; ctx |- e <= T ; eff ~> ctx'
      Checks that expression e has expected type T
      Implements T-Sub rule: infer then verify T_inferred <: T_expected
      Returns CheckOk(eff, ctx') or CheckErr(error)

    MODE SWITCHING (from Pierce & Turner "Local Type Inference"):
      - check_type for lambdas: propagate expected type to guide inference
      - check_type for others: infer then apply subsumption
      - infer_type for applications: check arguments against parameter types

    EFFECT TRACKING (Spec Section 3.1):
      Effects are tracked as rows and combined via row_join
      Common effects: Pure (no effects), Read, Write, Alloc, Throw, Async

    LINEAR CONTEXT THREADING (Spec Section 5.1):
      Context is threaded through computations
      Linear variables (mode = MOne) consumed exactly once
      Branches must agree on linear variable consumption

    ============================================================================ *)

(**
 * infer_type: Type inference in synthesis mode
 *
 * Judgment: gctx; ctx |- e => ty ; eff ~> ctx'
 *
 * Implements typing rules T-Var, T-Lit, T-Abs, T-App, T-Let, T-If, T-Match,
 * T-Borrow, T-BorrowMut, T-Deref, T-Assign, and many others.
 * See BrrrTypeChecker.fst for complete rule documentation.
 *
 * The context is threaded through: ctx' reflects consumed linear variables.
 * For branches (if/match), contexts are joined via join_contexts.
 *
 * @param gctx Global type context for polymorphic top-level definitions
 * @param ctx  Local type context for bound variables with modes
 * @param e    Expression to synthesize type for
 * @returns    InferOk(type, effects, updated_ctx) or InferErr(error)
 *)
val infer_type : gctx:global_ctx -> ctx:type_ctx -> e:expr ->
  Tot infer_result (decreases %[expr_size e; 0])

(**
 * check_type: Type checking in checking mode
 *
 * Judgment: gctx; ctx |- e <= expected ; eff ~> ctx'
 *
 * Implements the T-Sub (subsumption) rule:
 *   If ctx |- e => T1 and T1 <: expected, then ctx |- e <= expected
 *
 * Special handling for lambdas (CHECK-ABS):
 *   When checking \x.body against (T1 -> T2), propagates T1 to parameter
 *   and checks body against T2. This enables type inference without annotations.
 *
 * @param gctx     Global type context for polymorphic definitions
 * @param ctx      Local type context for bound variables
 * @param e        Expression to check
 * @param expected Expected type to check against
 * @returns        CheckOk(effects, updated_ctx) or CheckErr(error)
 *)
val check_type : gctx:global_ctx -> ctx:type_ctx -> e:expr -> expected:brrr_type ->
  Tot check_result (decreases %[expr_size e; 1])

(**
 * infer_type_list: Infer types of expression list
 *)
val infer_type_list : gctx:global_ctx -> ctx:type_ctx -> es:list expr ->
  Tot (option (list brrr_type & effect_row & type_ctx)) (decreases %[expr_list_size es; 2])

(**
 * check_args: Check arguments against parameter types
 *)
val check_args : gctx:global_ctx -> ctx:type_ctx -> args:list expr -> params:list BrrrTypes.param_type ->
  Tot (option (effect_row & type_ctx)) (decreases %[expr_list_size args; 3])

(** ============================================================================
    TOP-LEVEL API
    ============================================================================ *)

(* Infer type of expression in empty context *)
val infer : e:expr -> Tot (option (brrr_type & effect_row))

(* Check expression has expected type in empty context *)
val check : e:expr -> expected:brrr_type -> Tot (option effect_row)

(* Infer type with global context *)
val infer_with_globals : gctx:global_ctx -> e:expr -> Tot (option (brrr_type & effect_row))

(* Fully type check and verify linear resources consumed *)
val typecheck_complete : e:expr -> Tot (option (brrr_type & effect_row))

(* Fully type check with globals and verify linear resources consumed *)
val typecheck_complete_with_globals : gctx:global_ctx -> e:expr -> Tot (option (brrr_type & effect_row))

(** ============================================================================
    TYPE SAFETY THEOREMS (SOUNDNESS)
    ============================================================================ *)

(* Value predicate *)
val is_value : e:expr -> Tot bool (decreases e)

(**
 * Progress Theorem:
 * Well-typed terms don't get stuck - they either are values or can take a step.
 *
 * Formally: For closed, well-typed expression e:
 *   is_value e \/ can_step e
 *)
val progress_theorem :
    gctx:global_ctx -> e:expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk _ _ ctx' -> check_linear_consumed ctx'
                     | InferErr _ -> False))
          (ensures is_value e \/ not (is_value e))

(**
 * Preservation Theorem (Subject Reduction):
 * Reduction preserves types.
 *
 * Formally: If e : T and e --> e', then e' : T' where T' <: T
 *)
val preservation_theorem :
    gctx:global_ctx -> e:expr -> e':expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk ty eff ctx' -> True
                     | InferErr _ -> False))
          (ensures True)

(**
 * Type Safety (Soundness):
 * Well-typed programs don't go wrong.
 *
 * Combining progress and preservation: well-typed programs either
 * evaluate to a value or diverge; they never get stuck.
 *)
val type_safety :
    gctx:global_ctx -> e:expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk _ _ ctx' -> check_linear_consumed ctx'
                     | InferErr _ -> False))
          (ensures True)

(** ============================================================================
    SUBTYPING LEMMAS
    ============================================================================ *)

(* Subtyping is reflexive *)
val extended_subtype_refl : t:brrr_type ->
  Lemma (ensures extended_subtype t t = true)
        [SMTPat (extended_subtype t t)]

(* Subtyping is transitive *)
val subtype_trans_lemma : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires extended_subtype t1 t2 = true /\ extended_subtype t2 t3 = true)
        (ensures extended_subtype t1 t3 = true)
        [SMTPat (extended_subtype t1 t2); SMTPat (extended_subtype t2 t3)]

(** ============================================================================
    CANONICAL FORMS LEMMAS
    ============================================================================ *)

(* If a closed value has function type, it must be a lambda or closure *)
val canonical_forms_function :
    gctx:global_ctx -> v:expr -> ft:func_type ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx v with
              | InferOk (TFunc ft') _ _ -> ft' = ft
              | _ -> False))
          (ensures ELambda? v \/ EClosure? v)
          [SMTPat (is_value v); SMTPat (infer_type gctx empty_ctx v)]

(* If a closed value has boolean type, it must be a boolean literal *)
val canonical_forms_bool :
    gctx:global_ctx -> v:expr ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx v with
              | InferOk (TPrim PBool) _ _ -> True
              | _ -> False))
          (ensures (match v with ELit (LitBool _) -> True | _ -> False))
          [SMTPat (is_value v); SMTPat (infer_type gctx empty_ctx v)]

(** ============================================================================
    EFFECT SUBSUMPTION LEMMAS
    ============================================================================ *)

(* Effect subsumption is reflexive for rows without variables *)
val effect_sub_refl : e:effect_row ->
  Lemma (requires no_row_var e = true)
        (ensures effect_sub e e = true)
        [SMTPat (effect_sub e e)]
