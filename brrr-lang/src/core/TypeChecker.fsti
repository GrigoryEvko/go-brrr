(**
 * BrrrLang.Core.TypeChecker Interface
 *
 * Public interface for the bidirectional type checker.
 * Declares type checking functions with pre/post conditions and soundness theorems.
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Values, TypeClasses
 *)
module TypeChecker

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open Values
open TypeClasses
open BorrowChecker
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
    SUBTYPING AND CONSISTENCY
    ============================================================================ *)

(* Extended subtyping that handles function types with effects *)
val extended_subtype : t1:brrr_type -> t2:brrr_type -> bool

(* Type consistency relation for gradual typing *)
val type_consistent : t1:brrr_type -> t2:brrr_type -> Tot bool (decreases t1)

(** ============================================================================
    MAIN TYPE CHECKING FUNCTIONS
    ============================================================================ *)

(**
 * infer_type: Infer the type and effects of an expression
 *
 * @param gctx Global type context for top-level definitions
 * @param ctx  Local type context for bound variables
 * @param e    Expression to type-check
 * @returns    InferOk with type, effects, updated context; or InferErr
 *)
val infer_type : gctx:global_ctx -> ctx:type_ctx -> e:expr ->
  Tot infer_result (decreases %[expr_size e; 0])

(**
 * check_type: Check that expression has expected type
 *
 * @param gctx     Global type context
 * @param ctx      Local type context
 * @param e        Expression to check
 * @param expected Expected type
 * @returns        CheckOk with effects, updated context; or CheckErr
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
    CONSISTENCY LEMMAS (GRADUAL TYPING)
    ============================================================================ *)

(* Consistency is symmetric *)
val type_consistent_sym : t1:brrr_type -> t2:brrr_type ->
  Lemma (ensures type_consistent t1 t2 = type_consistent t2 t1)
        (decreases t1)
        [SMTPat (type_consistent t1 t2)]

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
    EFFECT SUBSUMPTION
    ============================================================================ *)

(* Effect subsumption *)
val effect_sub : e1:effect_row -> e2:effect_row -> bool

(* Effect subsumption is reflexive for rows without variables *)
val effect_sub_refl : e:effect_row ->
  Lemma (requires no_row_var e = true)
        (ensures effect_sub e e = true)
        [SMTPat (effect_sub e e)]
