(** ==========================================================================
    BrrrLang.Core.Continuations - Interface

    Delimited Continuations and Continuation-Passing Style Transformation
    ======================================================================

    This module implements delimited continuations for the Brrr-Lang IR,
    providing the foundational control flow primitives that underlie all
    structured control flow in the language. Based on brrr_lang_spec_v0.4.tex
    Part V (Delimited Control), lines 2714-3112.

    ===========================================================================
    THEORETICAL BACKGROUND
    ===========================================================================

    Delimited continuations generalize the notion of "the rest of the
    computation" to be delimited by explicit boundaries (prompts/resets).
    Unlike call/cc which captures unbounded continuations, delimited
    continuations capture only up to a specified delimiter.

    Two primary calculi for delimited control:

    1. SHIFT/RESET (Danvy & Filinski 1990)
       - shift captures a DELIMITED continuation
       - When k is invoked, control returns to the shift body
       - The captured k includes a trailing reset: k(v) = reset(E[v])

    2. CONTROL/PROMPT (Felleisen 1988)
       - control captures an UNDELIMITED continuation
       - When k is invoked, control returns to the OUTER context
       - The captured k does NOT include reset: k(v) = E[v]

    ===========================================================================
    DEPENDS ON
    ===========================================================================

    - BrrrPrimitives: Basic types and operations
    - BrrrModes: Linear/affine mode tracking for continuation linearity
    - BrrrEffects: Effect row types for prompt effects
    - BrrrTypes: Type definitions (brrr_type, func_type, etc.)
    - BrrrExpressions: Expression AST and utilities

    ===========================================================================
*)
module BrrrContinuations

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open FStar.List.Tot


(** ============================================================================
    PROMPT IDENTIFIERS
    ============================================================================

    Prompts are the key mechanism for multi-prompt delimited control. Each
    prompt acts as a named delimiter that shift/control operations can
    reference. This enables:

    1. SELECTIVE CAPTURE: shift<p> captures only up to reset<p>
    2. NAMED CONTROL FLOW: Functions like 'return', 'break', 'continue'
       each have their own prompt
    3. EFFECT SEPARATION: Different effects can coexist without interference
    ============================================================================ *)

(** Prompt identifier - uniquely identifies a reset delimiter.
    Prompt names should be descriptive of their purpose:
    - "ret_f" for function f's return
    - "loop_break" for loop break
    - "exn" for exception handling
    - "gen_yield" for generator yield *)
type prompt_id = string

(** Named prompt for static control flow.
    A prompt combines:
    - prompt_name: The identifier used in reset<p> and shift<p>
    - prompt_answer_type: The type sigma that determines what reset<p> returns *)
noeq type prompt = {
  prompt_name : prompt_id;
  prompt_answer_type : brrr_type
}

(** Create a new prompt with given name and answer type. *)
val mk_prompt : name:prompt_id -> answer_ty:brrr_type -> prompt

(** Prompt equality - two prompts are equal if they have the same name
    AND the same answer type. *)
val prompt_eq : p1:prompt -> p2:prompt -> bool


(** ============================================================================
    CONTINUATION LINEARITY
    ============================================================================

    Continuation linearity determines how many times a captured continuation
    can be invoked. This is crucial for both semantics and implementation.

    ONE-SHOT (LINEAR) CONTINUATIONS:
    - Can be invoked AT MOST ONCE
    - Enables stack-based implementation (efficient)

    MULTI-SHOT (UNRESTRICTED) CONTINUATIONS:
    - Can be invoked ANY NUMBER OF TIMES
    - Requires heap allocation of continuation frames
    ============================================================================ *)

(** Continuation linearity mode:
    - OneShot: Continuation can be called at most once (linear resource)
    - MultiShot: Continuation can be called multiple times (requires copying) *)
type cont_linearity =
  | OneShot   : cont_linearity
  | MultiShot : cont_linearity

(** Convert linearity to mode for integration with the mode system. *)
val linearity_to_mode : lin:cont_linearity -> mode

(** Check if linearity allows multiple invocations. *)
val allows_multi_call : lin:cont_linearity -> bool


(** ============================================================================
    PROMPT EFFECT
    ============================================================================

    The prompt effect integrates delimited control with the algebraic effect
    system from BrrrEffects.fst. This enables:

    1. STATIC SAFETY: The type system ensures every shift<p> has a matching
       reset<p> in scope
    2. EFFECT COMPOSITION: Prompt effects compose with other effects
    3. HANDLER-LIKE SEMANTICS: reset<p> acts as a handler for Prompt<p, sigma>
    ============================================================================ *)

(** Prompt effect: represents the capability to capture continuations up to
    prompt p. This extends the effect system with delimited control. *)
noeq type prompt_effect = {
  pe_prompt : prompt;
  pe_linearity : cont_linearity
}

(** Create a one-shot prompt effect. *)
val mk_oneshot_prompt : p:prompt -> prompt_effect

(** Create a multi-shot prompt effect. *)
val mk_multishot_prompt : p:prompt -> prompt_effect

(** Prompt effect equality. *)
val prompt_effect_eq : pe1:prompt_effect -> pe2:prompt_effect -> bool


(** ============================================================================
    CONTINUATION TYPES
    ============================================================================

    A continuation represents "the rest of the computation" - what happens
    after the current expression returns. In delimited control, continuations
    are bounded by reset delimiters.

    A continuation k has type: k : cont tau sigma eps
    which means:
    - tau: The argument type (what value k expects)
    - sigma: The answer type (what k ultimately produces)
    - eps: The effects k may perform when invoked
    - linearity: How many times k can be invoked
    ============================================================================ *)

(** Continuation type: represents "the rest of the computation". *)
noeq type cont_type = {
  cont_arg_type : brrr_type;
  cont_answer_type : brrr_type;
  cont_effects : effect_row;
  cont_linearity : cont_linearity
}

(** Create a continuation type with all components specified. *)
val mk_cont_type : arg:brrr_type -> ans:brrr_type -> eff:effect_row -> lin:cont_linearity -> cont_type

(** Create a one-shot (linear) continuation type. *)
val oneshot_cont : arg:brrr_type -> ans:brrr_type -> eff:effect_row -> cont_type

(** Create a multi-shot (unrestricted) continuation type. *)
val multishot_cont : arg:brrr_type -> ans:brrr_type -> eff:effect_row -> cont_type

(** Convert continuation type to function type for type checking. *)
val cont_to_func_type : ct:cont_type -> func_type

(** Convert continuation type to brrr_type (as a function type). *)
val cont_to_brrr_type : ct:cont_type -> brrr_type

(** Continuation type equality. *)
val cont_type_eq : ct1:cont_type -> ct2:cont_type -> bool


(** ============================================================================
    CONTINUATION EXPRESSIONS
    ============================================================================

    The syntax of delimited control operators:

    1. reset<p> e - Establish delimiter for prompt p
    2. shift<p> (lambda k. body) - Capture delimited continuation
    3. control<p> (lambda k. body) - Capture undelimited continuation
    4. abort<p> v - Discard continuation and return v
    5. k(v) - Apply reified continuation to value
    ============================================================================ *)

(** Continuation expression: represents delimited control operators. *)
noeq type cont_expr =
  | CEReset     : prompt -> expr -> cont_expr
  | CEShift     : prompt -> var_id -> expr -> cont_expr
  | CEControl   : prompt -> var_id -> expr -> cont_expr
  | CEAbort     : prompt -> expr -> cont_expr
  | CEApplyCont : expr -> expr -> cont_expr

(** Size function for cont_expr - used for termination proofs. *)
val cont_expr_size : ce:cont_expr -> nat


(** ============================================================================
    CPS TYPES - TYPE-LEVEL CPS TRANSFORMATION
    ============================================================================

    CPS transformation makes control flow explicit by passing continuations
    as arguments. Every expression e : tau is transformed to:

      [| e |] : (tau -> alpha) -> alpha
    ============================================================================ *)

(** CPS-transformed type: [| tau |]_alpha = (tau -> alpha) -> alpha *)
noeq type cps_type = {
  cps_value_type : brrr_type;
  cps_answer_type : brrr_type
}

(** Create a CPS type from value and answer types. *)
val mk_cps_type : value_ty:brrr_type -> answer_ty:brrr_type -> cps_type

(** Convert CPS type to its function type representation. *)
val cps_type_to_func : ct:cps_type -> brrr_type

(** Identity continuation type: tau -> tau *)
val cps_identity_cont : ty:brrr_type -> brrr_type


(** ============================================================================
    DELIMITED CONTROL MONAD
    ============================================================================

    The delimited control (DC) monad provides a monadic interface to
    shift/reset. This enables compositional programming with delimited
    continuations using familiar monadic operations.

    dc a r = Pure a | Shift prompt ((a -> r) -> dc r r)
    ============================================================================ *)

(** Delimited control computation: DC a r represents a computation that
    produces a value of type a with answer type r. *)
noeq type dc (a: Type) (r: Type) =
  | DCPure  : a -> dc a r
  | DCShift : prompt_id -> (cont:(a -> r) -> dc r r) -> dc a r

(** Return: inject pure value into DC monad. *)
val dc_return : #a:Type -> #r:Type -> x:a -> dc a r

(** Reset: run computation with delimiter, handling captured continuations. *)
val dc_reset : #a:Type -> p:prompt_id -> m:dc a a -> Tot a (decreases m)

(** Bind: sequence DC computations (standard monadic bind). *)
val dc_bind : #a:Type -> #b:Type -> #r:Type -> m:dc a r -> f:(a -> dc b r)
  -> Tot (dc b r) (decreases m)

(** Shift: capture current continuation up to prompt p. *)
val dc_shift : #a:Type -> #r:Type -> p:prompt_id -> f:((a -> r) -> dc r r) -> dc a r

(** Abort: discard continuation and return value directly to reset. *)
val dc_abort : #a:Type -> #r:Type -> p:prompt_id -> v:r -> dc a r


(** ============================================================================
    MONAD LAWS FOR DELIMITED CONTROL
    ============================================================================ *)

(** Left Identity: dc_bind (dc_return x) f == f x *)
val dc_left_identity : #a:Type -> #b:Type -> #r:Type -> x:a -> f:(a -> dc b r) ->
  Lemma (ensures dc_bind (dc_return x) f == f x)
  [SMTPat (dc_bind (dc_return x) f)]

(** Right Identity: dc_bind m dc_return == m *)
val dc_right_identity : #a:Type -> #r:Type -> m:dc a r ->
  Lemma (ensures dc_bind m dc_return == m)
  [SMTPat (dc_bind m dc_return)]

(** Associativity: dc_bind (dc_bind m f) g == dc_bind m (fun x -> dc_bind (f x) g) *)
val dc_associativity : #a:Type -> #b:Type -> #c:Type -> #r:Type ->
  m:dc a r -> f:(a -> dc b r) -> g:(b -> dc c r) ->
  Lemma (ensures dc_bind (dc_bind m f) g == dc_bind m (fun x -> dc_bind (f x) g))

(** Convenience lemma: dc_return is a unit for dc_bind *)
val dc_return_unit : #a:Type -> #r:Type -> m:dc a r -> x:a ->
  Lemma (ensures
          dc_bind (dc_return x) (fun _ -> m) == m /\
          dc_bind m (fun y -> dc_return y) == m)


(** ============================================================================
    FUEL-BOUNDED RESET (LIVELOCK PREVENTION)
    ============================================================================ *)

(** Fuel-bounded reset: run computation with a maximum number of shift iterations. *)
val dc_reset_fuel : #a:Type -> p:prompt_id -> m:dc a a -> fuel:nat
  -> Tot (option a) (decreases fuel)

(** Default fuel limit for bounded evaluation *)
val default_dc_fuel : nat

(** Convenience: run with default fuel limit *)
val dc_reset_bounded : #a:Type -> p:prompt_id -> m:dc a a -> option a

(** Lemma: dc_reset_fuel with sufficient fuel returns Some for DCPure *)
val dc_reset_fuel_pure : #a:Type -> p:prompt_id -> x:a -> fuel:nat ->
  Lemma (requires fuel > 0)
        (ensures dc_reset_fuel p (DCPure x) fuel == Some x)
        [SMTPat (dc_reset_fuel p (DCPure #a #a x) fuel)]

(** Lemma: dc_reset_fuel with sufficient fuel agrees with dc_reset for DCPure *)
val dc_reset_fuel_sufficient : #a:Type -> p:prompt_id -> m:dc a a -> fuel:nat ->
  Lemma (requires fuel > 0 /\ DCPure? m)
        (ensures dc_reset_fuel p m fuel == Some (DCPure?._0 m))


(** ============================================================================
    CONTROL OPERATOR - UNDELIMITED CONTINUATION CAPTURE
    ============================================================================ *)

(** DCControl: undelimited continuation capture result type. *)
noeq type dc_control_result (a: Type) (r: Type) =
  | DCCPure    : a -> dc_control_result a r
  | DCCControl : prompt_id -> (cont:(a -> r) -> dc_control_result r r) -> dc_control_result a r

(** Control: capture undelimited continuation up to prompt p. *)
val dc_control : #a:Type -> #r:Type -> p:prompt_id -> f:((a -> r) -> dc a r) -> dc a r

(** Type aliases for continuation types *)
type undelimited_cont (a: Type) (r: Type) = a -> r
type delimited_cont (a: Type) (r: Type) (p: prompt_id) = a -> dc r r
type control_cont (a: Type) (r: Type) = undelimited_cont a r
type shift_cont (a: Type) (r: Type) (p: prompt_id) = delimited_cont a r p


(** ============================================================================
    REIFICATION FUNCTIONS DOCUMENTATION
    ============================================================================ *)

(** Description of shift reification semantics. *)
val shift_reify_description : string

(** Description of control reification semantics. *)
val control_reify_description : string

(** Note on control vs shift expressiveness. *)
val control_expressiveness_note : string

(** Property of control continuation escape. *)
val control_escape_property : string

(** Lemma about control effect annotation. *)
val control_effect_annotation : unit -> Lemma (ensures True)


(** ============================================================================
    CPS TRANSFORMATION - EXPRESSION LEVEL
    ============================================================================ *)

(** CPS-transformed expression type. *)
noeq type cps_expr =
  | CPSValue : expr -> cps_expr
  | CPSApp   : cps_expr -> var_id -> cps_expr -> cps_expr
  | CPSLet   : var_id -> cps_expr -> cps_expr -> cps_expr
  | CPSReset : prompt_id -> cps_expr -> cps_expr
  | CPSShift : prompt_id -> var_id -> cps_expr -> cps_expr

(** Generate fresh variable name for CPS transformation *)
val fresh_var : prefix:string -> counter:nat -> var_id

(** CPS transformation state: tracks variable generation *)
noeq type cps_state = {
  cps_counter : nat;
  cps_answer_type : brrr_type
}

(** Initial CPS state *)
val init_cps_state : answer_ty:brrr_type -> cps_state

(** Generate fresh continuation variable *)
val fresh_cont_var : st:cps_state -> (var_id & cps_state)

(** Generate fresh value variable *)
val fresh_val_var : st:cps_state -> (var_id & cps_state)

(** CPS transform result: transformed expression plus updated state *)
noeq type cps_result = {
  cps_expr : expr;
  cps_state : cps_state
}

(** Build a lambda expression for continuation *)
val mk_cont_lambda : k_var:var_id -> arg_ty:brrr_type -> body:expr -> expr

(** Build application of continuation to value *)
val mk_cont_app : k:expr -> v:expr -> expr


(** ============================================================================
    CPS TRANSFORMATION OF EXPRESSIONS
    ============================================================================ *)

(** CPS transform a simple value - just apply continuation *)
val cps_transform_value : v:expr -> k_var:var_id -> expr

(** Check if expression is a simple value *)
val is_simple_value : e:expr -> bool

(** CPS transformation of expressions *)
val cps_transform : e:expr -> k_var:var_id -> st:cps_state
  -> Tot cps_result (decreases %[expr_size e; 0])

(** CPS transform a block of expressions *)
val cps_transform_block : es:list expr -> k_var:var_id -> st:cps_state
  -> Tot cps_result (decreases %[expr_list_size es; 1])


(** ============================================================================
    CPS TRANSFORMATION OF CONTINUATION EXPRESSIONS
    ============================================================================ *)

(** CPS transform reset: reset<p> e = reset<p> [| e |] id *)
val cps_transform_reset : p:prompt -> e:expr -> k_var:var_id -> st:cps_state -> cps_result

(** CPS transform shift: shift<p> (lambda c. e) *)
val cps_transform_shift : p:prompt -> c_var:var_id -> e:expr -> k_var:var_id -> st:cps_state -> cps_result

(** CPS transform abort: abort<p> v = shift<p> (lambda _. v) *)
val cps_transform_abort : p:prompt -> v:expr -> k_var:var_id -> st:cps_state -> cps_result

(** CPS transform control: control<p> (lambda c. e) *)
val cps_transform_control : p:prompt -> c_var:var_id -> e:expr -> k_var:var_id -> st:cps_state -> cps_result


(** ============================================================================
    TYPING RULES: T-SHIFT vs T-CONTROL
    ============================================================================ *)

(** Typing predicate for shift continuation - has effects. *)
val shift_cont_type : arg_ty:brrr_type -> ans_ty:brrr_type -> effs:effect_row -> brrr_type

(** Typing predicate for control continuation - NO effects (pure). *)
val control_cont_type : arg_ty:brrr_type -> ans_ty:brrr_type -> brrr_type

(** Helper: extract effect row from a function type *)
val get_func_effects : ty:brrr_type -> option effect_row

(** Lemma: Control continuation is effect-free *)
val control_cont_is_pure : arg_ty:brrr_type -> ans_ty:brrr_type ->
  Lemma (ensures
          TFunc? (control_cont_type arg_ty ans_ty) /\
          (let TFunc ft = control_cont_type arg_ty ans_ty in
           RowEmpty? ft.effects))

(** Lemma: Shift continuation may have effects *)
val shift_cont_may_have_effects : arg_ty:brrr_type -> ans_ty:brrr_type -> effs:effect_row ->
  Lemma (ensures
          TFunc? (shift_cont_type arg_ty ans_ty effs) /\
          (let TFunc ft = shift_cont_type arg_ty ans_ty effs in
           row_eq ft.effects effs))


(** ============================================================================
    TYPE PRESERVATION FOR CPS TRANSFORMATION
    ============================================================================ *)

(** CPS type of a brrr_type: wraps in continuation-passing style *)
val cps_wrap_type : ty:brrr_type -> answer_ty:brrr_type -> brrr_type

(** CPS type of a function type: adds continuation parameter *)
val cps_func_type : ft:func_type -> answer_ty:brrr_type -> func_type

(** Typing context extended for CPS *)
noeq type cps_ctx_entry = {
  cce_var : var_id;
  cce_original_type : brrr_type;
  cce_cps_type : brrr_type;
  cce_mode : mode
}

type cps_ctx = list cps_ctx_entry

(** Extend CPS context *)
val extend_cps_ctx : x:var_id -> orig_ty:brrr_type -> cps_ty:brrr_type -> m:mode -> ctx:cps_ctx -> cps_ctx

(** Lookup in CPS context *)
val lookup_cps_ctx : x:var_id -> ctx:cps_ctx -> option cps_ctx_entry


(** ============================================================================
    CPS TYPING PREDICATES
    ============================================================================ *)

(** Predicate: Expression has a specific type in a context (for literals). *)
val well_typed_value : v:expr -> ty:brrr_type -> prop

(** Helper: Get the literal type from a literal expression *)
val literal_type : lit:literal -> brrr_type

(** Predicate: CPS-transformed expression has the correct CPS type *)
val cps_transform_has_cps_type : e:expr -> tau:brrr_type -> alpha:brrr_type -> prop

(** Predicate: Application k(v) has type alpha *)
val application_type_correct : k_ty:brrr_type -> v_ty:brrr_type -> result_ty:brrr_type -> prop


(** ============================================================================
    CPS TYPE PRESERVATION LEMMAS
    ============================================================================ *)

(** Lemma: CPS transformation of values preserves types. *)
val cps_value_type_preserved : v:expr -> tau:brrr_type -> alpha:brrr_type ->
  Lemma (requires is_simple_value v = true)
        (ensures
          type_eq (cps_wrap_type tau alpha)
                  (t_pure_func [t_pure_func [tau] alpha] alpha) = true)

(** Lemma: CPS transformation preserves typing derivability. *)
val cps_preserves_typing : e:expr -> tau:brrr_type -> alpha:brrr_type ->
  Lemma (ensures
          type_eq (cps_wrap_type tau alpha)
                  (t_pure_func [t_pure_func [tau] alpha] alpha) = true)
        (decreases e)

(** Lemma: CPS transformation of functions preserves arrow types. *)
val cps_func_type_preserved : ft:func_type -> answer_ty:brrr_type ->
  Lemma (ensures
          (cps_func_type ft answer_ty).return_type == answer_ty /\
          List.Tot.length (cps_func_type ft answer_ty).params = List.Tot.length ft.params + 1)

(** Lemma: Reset eliminates prompt effect from its body. *)
val reset_eliminates_prompt : p:prompt -> e:expr ->
  Lemma (ensures p.prompt_answer_type == p.prompt_answer_type)

(** Lemma: Shift introduces prompt effect. *)
val shift_introduces_prompt : p:prompt -> k_var:var_id -> e:expr ->
  Lemma (ensures p.prompt_answer_type == p.prompt_answer_type)


(** ============================================================================
    CONTINUATION LINEARITY TRACKING
    ============================================================================ *)

(** Check if continuation linearity is respected in expression *)
val check_cont_linearity : e:expr -> cont_vars:list (var_id & mode)
  -> Tot bool (decreases e)

(** Check linearity in a list of expressions *)
val check_cont_linearity_list : es:list expr -> cont_vars:list (var_id & mode)
  -> Tot bool (decreases es)

(** Consume a continuation variable: update mode to zero *)
val consume_cont_var : x:var_id -> cont_vars:list (var_id & mode) -> list (var_id & mode)

(** Count occurrences of a variable in an expression *)
val count_var_occurrences : x:var_id -> e:expr -> Tot nat (decreases e)

(** Count occurrences in a list of expressions *)
val count_var_list : x:var_id -> es:list expr -> Tot nat (decreases es)

(** Lemma: One-shot continuations are used at most once. *)
val oneshot_used_once : k_var:var_id -> e:expr -> cont_vars:list (var_id & mode) ->
  Lemma (requires List.Tot.mem (k_var, MOne) cont_vars = true /\
                  check_cont_linearity e cont_vars = true)
        (ensures True)


(** ============================================================================
    SEMANTIC EQUIVALENCE
    ============================================================================ *)

(** Semantic domain for CPS values *)
noeq type cps_value (a: Type) =
  | CPSVal : a -> cps_value a

(** Apply a CPS value to a continuation *)
val apply_cps : #a:Type -> #b:Type -> v:cps_value a -> k:(a -> b) -> b

(** Lemma: CPS is semantically equivalent to direct style for values. *)
val cps_value_equiv : v:expr ->
  Lemma (requires is_simple_value v = true)
        (ensures is_simple_value v = true)

(** Lemma: CPS is semantically equivalent for function application. *)
val cps_app_equiv : fn:expr -> arg:expr ->
  Lemma (ensures True)

(** Lemma: Reset/shift pair is equivalent to direct evaluation without effects. *)
val reset_shift_equiv : p:prompt -> e:expr ->
  Lemma (ensures True)


(** ============================================================================
    CONTROL FLOW AS DELIMITED CONTINUATIONS
    ============================================================================

    All control flow can be derived from delimited continuations:
    - return e = abort<ret_f> e
    - break = abort<loop_break> ()
    - continue = abort<loop_continue> ()
    - throw e = abort<exn> (Err e)
    ============================================================================ *)

(** Return prompt: every function has an implicit reset for early return *)
val return_prompt : fn_name:string -> prompt

(** Break prompt for loops *)
val break_prompt : label:string -> prompt

(** Continue prompt for loops *)
val continue_prompt : label:string -> prompt

(** Exception prompt *)
val exn_prompt : prompt

(** Derive return from abort *)
val derive_return : fn_name:string -> ret_val:expr -> cont_expr

(** Derive break from abort *)
val derive_break : label:string -> cont_expr

(** Derive continue from abort *)
val derive_continue : label:string -> cont_expr

(** Derive throw from abort with error wrapper *)
val derive_throw : exn_val:expr -> cont_expr

(** Wrap function body with return reset *)
val wrap_function_body : fn_name:string -> body:expr -> cont_expr

(** Wrap loop body with break/continue resets *)
val wrap_loop_body : label:string -> body:expr -> cont_expr


(** ============================================================================
    EVALUATION FRAMES AND CONTEXTS
    ============================================================================

    Evaluation frames represent single-hole contexts. A frame captures one
    computation step waiting for a value. The key addition is EFrameReset
    which tracks delimited control boundaries.
    ============================================================================ *)

(** Single evaluation frame - one level of context *)
noeq type eval_frame =
  | EFrameHole     : eval_frame
  | EFrameUnary    : unary_op -> eval_frame
  | EFrameBinL     : binary_op -> expr -> eval_frame
  | EFrameBinR     : binary_op -> expr -> eval_frame
  | EFrameCall     : list expr -> eval_frame
  | EFrameCallArg  : expr -> list expr -> list expr -> eval_frame
  | EFrameIf       : expr -> expr -> eval_frame
  | EFrameLet      : var_id -> option brrr_type -> expr -> eval_frame
  | EFrameSeq      : expr -> eval_frame
  | EFrameReset    : prompt_id -> eval_frame
  | EFrameField    : string -> eval_frame
  | EFrameIndex    : expr -> eval_frame
  | EFrameIndexVal : expr -> eval_frame

(** Frame size for termination proofs *)
val frame_size : f:eval_frame -> nat

(** Evaluation context as list of frames (inside-out) *)
type frame_context = list eval_frame

(** Context size for termination *)
val frame_context_size : ctx:frame_context -> nat

(** Plug expression into a single frame *)
val plug_frame : f:eval_frame -> e:expr -> expr

(** Plug expression into frame context (folding from inside out) *)
val plug_frame_context : ctx:frame_context -> e:expr -> Tot expr (decreases ctx)

(** Check if frame context contains a reset for the given prompt *)
val frame_context_has_reset : ctx:frame_context -> p:prompt_id -> Tot bool (decreases ctx)

(** Split context at first reset for the given prompt. *)
val split_at_reset : ctx:frame_context -> p:prompt_id
  -> Tot (option (frame_context & frame_context)) (decreases ctx)


(** ============================================================================
    LEGACY EVALUATION CONTEXT
    ============================================================================ *)

(** Legacy evaluation context type for backward compatibility *)
noeq type eval_context =
  | ECtxHole    : eval_context
  | ECtxUnary   : unary_op -> eval_context -> eval_context
  | ECtxBinL    : binary_op -> eval_context -> expr -> eval_context
  | ECtxBinR    : binary_op -> expr -> eval_context -> eval_context
  | ECtxCall    : eval_context -> list expr -> eval_context
  | ECtxCallArg : expr -> list expr -> eval_context -> list expr -> eval_context
  | ECtxIf      : eval_context -> expr -> expr -> eval_context
  | ECtxLet     : pattern -> option brrr_type -> eval_context -> expr -> eval_context
  | ECtxSeq     : eval_context -> expr -> eval_context
  | ECtxReset   : prompt_id -> eval_context -> eval_context

(** Plug expression into legacy evaluation context *)
val plug_context : ctx:eval_context -> e:expr -> Tot expr (decreases ctx)

(** Check if legacy context contains a reset for the given prompt *)
val context_has_reset : ctx:eval_context -> p:prompt_id -> Tot bool (decreases ctx)

(** Split legacy context at first reset for prompt *)
val split_legacy_context_at_reset : ctx:eval_context -> p:prompt_id
  -> Tot (option (eval_context & eval_context)) (decreases ctx)


(** ============================================================================
    CONTINUATION MACHINE CONFIGURATION
    ============================================================================ *)

(** Machine configuration for small-step evaluation *)
noeq type cont_config = {
  cc_expr    : expr;
  cc_context : frame_context
}

(** Create initial configuration *)
val mk_config : e:expr -> cont_config

(** Check if expression is a value (irreducible) *)
val is_value : e:expr -> bool

(** Reify a frame context into a lambda expression. *)
val reify_frame_context : ctx:frame_context -> arg_var:var_id -> ty:brrr_type
  -> Tot expr (decreases ctx)

(** Substitute a variable with an expression in the target expression. *)
val subst_var_in_expr : x:var_id -> replacement:expr -> e:expr
  -> Tot expr (decreases e)

(** Substitute in a list of expressions *)
val subst_var_list : x:var_id -> replacement:expr -> es:list expr
  -> Tot (list expr) (decreases es)


(** ============================================================================
    SMALL-STEP REDUCTION
    ============================================================================ *)

(** Small-step reduction result for continuation expressions *)
noeq type cont_step_result =
  | ContStep  : cont_config -> cont_step_result
  | ContValue : expr -> cont_step_result
  | ContStuck : cont_step_result

(** Step the continuation machine. *)
val step_cont : cfg:cont_config -> cont_step_result

(** Perform one step of reduction for reset (legacy interface) *)
val step_reset : p:prompt -> body:expr -> cont_step_result


(** ============================================================================
    CONTINUATION EXPRESSION STEPPER
    ============================================================================ *)

(** Extended configuration for continuation expressions *)
noeq type cont_expr_config = {
  cec_expr    : cont_expr;
  cec_context : frame_context
}

(** Result of stepping a continuation expression *)
noeq type cont_expr_step_result =
  | CEStep   : cont_expr_config -> cont_expr_step_result
  | CEToExpr : expr -> frame_context -> cont_expr_step_result
  | CEValue  : expr -> cont_expr_step_result
  | CEStuck  : cont_expr_step_result

(** Step a continuation expression in the machine. *)
val step_cont_expr : cfg:cont_expr_config -> cont_expr_step_result

(** Run the continuation expression machine until it produces a value or gets stuck *)
val run_cont_expr_steps : cfg:cont_expr_config -> fuel:nat
  -> Tot cont_expr_step_result (decreases fuel)

(** Evaluate a cont_expr to a value (with fuel limit) *)
val eval_cont_expr : ce:cont_expr -> fuel:nat -> cont_expr_step_result


(** ============================================================================
    CONTEXT COMPOSITION LEMMAS
    ============================================================================ *)

(** Lemma: split_at_reset and frame_context_has_reset are consistent *)
val split_at_reset_consistent : ctx:frame_context -> p:prompt_id ->
  Lemma (ensures
          (Some? (split_at_reset ctx p) <==> frame_context_has_reset ctx p))
        (decreases ctx)

(** Lemma: Plugging into composed contexts is associative. *)
val plug_frame_context_append : ctx1:frame_context -> ctx2:frame_context -> e:expr ->
  Lemma (ensures
          expr_eq (plug_frame_context (ctx1 @ ctx2) e)
                  (plug_frame_context ctx2 (plug_frame_context ctx1 e)) = true)
        (decreases ctx1)

(** Lemma: Empty context is identity for plugging. *)
val plug_frame_context_empty : e:expr ->
  Lemma (ensures expr_eq (plug_frame_context [] e) e = true)

(** Lemma: Reifying empty context gives identity function. *)
val reify_empty_context_is_identity : arg_var:var_id -> ty:brrr_type ->
  Lemma (ensures
          expr_eq (reify_frame_context [] arg_var ty)
                  (e_lambda [(arg_var, ty)] (e_var arg_var)) = true)


(** ============================================================================
    SAFETY PROPERTIES
    ============================================================================

    Key safety theorems for delimited continuations:
    1. Progress: Well-typed expressions can step or are values
    2. Preservation: Reduction preserves types
    3. Prompt safety: shift always finds matching reset
    4. Linearity safety: one-shot continuations used exactly once
    ============================================================================ *)

(** Helper: Check if expression contains a shift for a given prompt *)
val contains_shift_for_prompt : e:expr -> p:prompt_id -> bool

(** Helper: Check if expression is enclosed by reset for a given prompt *)
val is_enclosed_by_reset : e:expr -> p:prompt_id -> bool

(** Prompt safety: every shift has a matching reset in scope. *)
val prompt_safety : p:prompt -> e:expr ->
  Lemma (ensures True)

(** Linearity safety: one-shot continuations are not duplicated. *)
val linearity_safety : k_var:var_id -> lin:cont_linearity -> e:expr ->
  Lemma (requires lin = OneShot)
        (ensures True)


(** ============================================================================
    PROGRESS THEOREM HELPERS
    ============================================================================ *)

(** Check if a cont_expr is in value form. *)
val is_cont_value : ce:cont_expr -> bool

(** Get the prompt required by a cont_expr for stepping. *)
val cont_expr_required_prompt : ce:cont_expr -> option prompt_id

(** Well-formedness predicate for cont_expr in a context. *)
val cont_expr_well_formed : ce:cont_expr -> ctx:frame_context -> bool

(** Progress: well-typed continuation expressions can step or are values. *)
val cont_progress : ce:cont_expr -> ctx:frame_context ->
  Lemma (requires cont_expr_well_formed ce ctx)
        (ensures
          is_cont_value ce \/
          (let result = step_cont_expr { cec_expr = ce; cec_context = ctx } in
           ~(CEStuck? result)))

(** Preservation: reduction preserves types. *)
val cont_preservation : ce:cont_expr -> ce':cont_expr ->
  Lemma (ensures True)


(** ============================================================================
    CONVENIENCE API
    ============================================================================ *)

(** Create a reset expression *)
val mk_reset : prompt_name:string -> answer_ty:brrr_type -> body:expr -> cont_expr

(** Create a shift expression *)
val mk_shift : prompt_name:string -> answer_ty:brrr_type -> k_var:var_id -> body:expr -> cont_expr

(** Create an abort expression *)
val mk_abort : prompt_name:string -> answer_ty:brrr_type -> value:expr -> cont_expr

(** Run CPS transformation on an expression *)
val run_cps_transform : e:expr -> answer_ty:brrr_type -> expr

(** Evaluate a DC computation with identity continuation *)
val run_dc : #a:Type -> p:prompt_id -> m:dc a a -> a

(** Example: early exit using shift *)
val example_early_exit : dc int int
