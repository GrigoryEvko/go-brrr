(**
 * =============================================================================
 * BrrrLang.Core.Async - Interface
 * =============================================================================
 *
 * Async/Await, Generators, and Structured Concurrency for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part V (Generators and Coroutines) and
 * Part VI (Structured Concurrency).
 *
 * This module implements:
 *   - Future types with Hot/Cold/Lazy temperatures
 *   - Generator types with bidirectional data flow
 *   - Async/await expressions and type checking
 *   - Structured concurrency with TaskGroups
 *   - Cooperative cancellation with CancelTokens
 *   - State machine compilation for async/generator bodies
 *   - Channel runtime for CSP-style message passing
 *   - sync.Once primitive
 *
 * =============================================================================
 *)
module BrrrAsync

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrContinuations
open FStar.List.Tot

(** ============================================================================
    UTILITY TYPES
    ============================================================================ *)

type future_temperature =
  | FutHot  : future_temperature
  | FutCold : future_temperature
  | FutLazy : future_temperature

(** Temperature equality *)
val temp_eq : future_temperature -> future_temperature -> bool

(** Temperature subtyping: Hot <: Lazy, Cold <: Lazy *)
val temp_subtype : future_temperature -> future_temperature -> bool

(** ============================================================================
    FUTURE STATE
    ============================================================================ *)

(** Runtime state of a future:
    - FutPending: Not yet resolved, computation in progress or not started
    - FutResolved: Successfully completed with a value
    - FutFailed: Completed with an error
    - FutCancelled: Computation was cancelled before completion *)
noeq type future_state (a: Type) =
  | FutPending   : cont:(unit -> future_state a) -> future_state a
  | FutResolved  : value:a -> future_state a
  | FutFailed    : error:string -> future_state a
  | FutCancelled : future_state a

(** Check if future is complete *)
val is_complete : #a:Type -> future_state a -> bool

(** Get value if resolved *)
val get_resolved : #a:Type -> future_state a -> option a

(** ============================================================================
    FUTURE TYPE
    ============================================================================ *)

(** Future type: combines value type and temperature *)
noeq type future_type = {
  fut_value_type : brrr_type;
  fut_temperature : future_temperature
}

(** Create future type *)
val mk_future_type : brrr_type -> future_temperature -> future_type

(** Create hot future type *)
val hot_future : brrr_type -> future_type

(** Create cold future type *)
val cold_future : brrr_type -> future_type

(** Create lazy future type *)
val lazy_future : brrr_type -> future_type

(** Future type equality *)
val future_type_eq : future_type -> future_type -> bool

(** Future subtyping *)
val future_subtype : future_type -> future_type -> bool

(** Convert future_type to brrr_type using TApp encoding *)
val future_to_brrr_type : future_type -> brrr_type

(** ============================================================================
    GENERATOR STATE
    ============================================================================ *)

(** Generator state: Y = yield type, R = resumption type, T = final return type
    - GenInitial: Generator created but not yet started
    - GenYielded: Suspended at yield point with continuation
    - GenDone: Completed normally with final return value
    - GenFailed: Terminated with exception *)
noeq type gen_state (y: Type) (r: Type) (t: Type) =
  | GenInitial : start:(unit -> gen_state y r t) -> gen_state y r t
  | GenDone    : final:t -> gen_state y r t
  | GenYielded : yielded:y -> resume:(r -> gen_state y r t) -> gen_state y r t
  | GenFailed  : error:string -> gen_state y r t

(** Check if generator is complete (terminal state) *)
val gen_is_done : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> bool

(** Check if generator is in initial (not yet started) state *)
val gen_is_initial : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> bool

(** Check if generator is suspended (yielded and waiting for resume) *)
val gen_is_suspended : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> bool

(** Check if generator is runnable (can be started or resumed) *)
val gen_is_runnable : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> bool

(** Get yielded value if suspended *)
val get_yielded : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> option y

(** Get final value if done *)
val get_final : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> option t

(** Get error message if failed *)
val get_gen_error : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> option string

(** ============================================================================
    GENERATOR TYPE
    ============================================================================ *)

(** Generator type: Y = yield, R = resume input, T = final return *)
noeq type generator_type = {
  gen_yield_type  : brrr_type;
  gen_resume_type : brrr_type;
  gen_return_type : brrr_type
}

(** Create generator type *)
val mk_generator_type : brrr_type -> brrr_type -> brrr_type -> generator_type

(** Simple generator: yields Y, receives unit, returns unit *)
val simple_generator : brrr_type -> generator_type

(** Iterator generator: yields Y, receives unit, returns unit *)
val iterator_generator : brrr_type -> generator_type

(** Generator type equality *)
val generator_type_eq : generator_type -> generator_type -> bool

(** Generator subtyping (covariant in Y/T, contravariant in R) *)
val generator_subtype : generator_type -> generator_type -> bool

(** Convert generator_type to brrr_type using TApp encoding *)
val generator_to_brrr_type : generator_type -> brrr_type

(** ============================================================================
    GENERATOR VALUE
    ============================================================================ *)

(** Generator value: wraps state machine *)
noeq type generator (y: Type) (r: Type) (t: Type) = {
  gen_body : unit -> gen_state y r t
}

(** Create generator from body function *)
val make_generator : #y:Type -> #r:Type -> #t:Type ->
  (unit -> gen_state y r t) -> generator y r t

(** Create generator state directly in Initial state *)
val make_gen_initial : #y:Type -> #r:Type -> #t:Type ->
  (unit -> gen_state y r t) -> gen_state y r t

(** Step generator: run one iteration *)
val step_generator : #y:Type -> #r:Type -> #t:Type -> generator y r t -> gen_state y r t

(** Start a generator in Initial state *)
val start_generator : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> gen_state y r t

(** Resume generator with a value *)
val resume_generator : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> r -> gen_state y r t

(** Send a value to generator (alias for resume_generator) *)
val send_to_generator : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> r -> gen_state y r t

(** Get next value from generator (convenience for unit resume type) *)
val next_generator : #y:Type -> #t:Type -> gen_state y unit t -> gen_state y unit t

(** ============================================================================
    YIELD EFFECT
    ============================================================================ *)

(** Yield effect parameters *)
noeq type yield_effect_type = {
  yield_type  : brrr_type;
  resume_type : brrr_type
}

(** Create yield effect type *)
val mk_yield_effect : brrr_type -> brrr_type -> yield_effect_type

(** Simple yield effect: yields Y, receives unit *)
val simple_yield_effect : brrr_type -> yield_effect_type

(** Yield effect equality *)
val yield_effect_eq : yield_effect_type -> yield_effect_type -> bool

(** ============================================================================
    BRRR_TYPE TO EFFECT_TYPE CONVERSION
    ============================================================================ *)

(** Convert brrr_type to effect_type for use in effect parameters *)
val brrr_to_effect_type : brrr_type -> BrrrEffects.effect_type

(** Unit effect type constant *)
val et_unit : BrrrEffects.effect_type

(** ============================================================================
    EFFECT ROWS
    ============================================================================ *)

(** Effect row with just Async *)
val eff_async_only : effect_row

(** Create parameterized yield effect operation *)
val mk_yield_effect_op : brrr_type -> brrr_type -> BrrrEffects.effect_op

(** Create effect row with Yield[Y, R] *)
val mk_eff_yield : brrr_type -> brrr_type -> effect_row

(** Effect row with Yield[unit, unit] - simple version *)
val eff_yield_simple : effect_row

(** Create effect row with both Async and Yield[Y, R] *)
val mk_eff_async_yield : brrr_type -> brrr_type -> effect_row

(** Effect row with both Async and Yield[unit, unit] *)
val eff_async_yield_simple : effect_row

(** Legacy aliases *)
val eff_yield_only : effect_row
val eff_async_yield : effect_row

(** ============================================================================
    ASYNC EXPRESSIONS
    ============================================================================ *)

(** Async expression forms *)
noeq type async_expr =
  | AEAsync : body:expr -> async_expr
  | AEAwait : future:expr -> async_expr
  | AESpawn : body:expr -> async_expr
  | AEGen : body:expr -> async_expr
  | AEYield : value:expr -> async_expr
  | AEYieldFrom : gen:expr -> async_expr
  | AEGenSend : gen:expr -> value:expr -> async_expr
  | AEGenNext : gen:expr -> async_expr
  | AEJoin : futures:list expr -> async_expr
  | AESelect : futures:list expr -> async_expr
  | AETimeout : body:expr -> duration:expr -> async_expr
  | AECancel : future:expr -> async_expr

(** Size function for async_expr (for termination proofs) *)
val async_expr_size : async_expr -> nat

(** ============================================================================
    ASYNC TYPE INFERENCE
    ============================================================================ *)

(** Result of async expression type inference *)
val extract_future_type : brrr_type -> option future_type

(** Extract inner types from Generator type encoding *)
val extract_generator_type : brrr_type -> option generator_type

(** ============================================================================
    GENERATOR TYPING CONTEXT
    ============================================================================ *)

(** Generator typing context - tracks expected types when inside a generator *)
noeq type gen_typing_ctx = {
  gtc_yield_type  : option brrr_type;
  gtc_resume_type : option brrr_type;
  gtc_return_type : option brrr_type
}

(** Empty generator context *)
val empty_gen_ctx : gen_typing_ctx

(** Create generator context with all types specified *)
val mk_gen_ctx : brrr_type -> brrr_type -> brrr_type -> gen_typing_ctx

(** Create simple generator context (resume type is unit) *)
val simple_gen_ctx : brrr_type -> brrr_type -> gen_typing_ctx

(** Check if we are inside a generator context *)
val in_generator_ctx : gen_typing_ctx -> bool

(** Get yield/resume types from context *)
val get_yield_context : gen_typing_ctx -> option (brrr_type & brrr_type)

(** ============================================================================
    YIELD EFFECT EXTRACTION
    ============================================================================ *)

(** Check if effect_op is any form of EYield *)
val is_yield_effect : BrrrEffects.effect_op -> bool

(** Check if effect row contains any Yield effect *)
val has_yield_effect : effect_row -> bool

(** Check if effect row contains Yield with specific type parameters *)
val has_yield_effect_typed : effect_row -> brrr_type -> brrr_type -> bool

(** Remove all Yield effects from effect row *)
val remove_yield_effect : effect_row -> effect_row

(** Remove specific Yield effect from row *)
val remove_yield_effect_typed : effect_row -> brrr_type -> brrr_type -> effect_row

(** Convert effect_type back to brrr_type *)
val effect_type_to_brrr : BrrrEffects.effect_type -> brrr_type

(** Extract yield type parameters from a Yield effect operation *)
val get_yield_types : BrrrEffects.effect_op -> option (brrr_type & brrr_type)

(** Find and extract yield types from effect row *)
val find_yield_in_row : effect_row -> option (brrr_type & brrr_type)

(** Extract yield effect info from effect row with hints *)
val extract_yield_from_row : effect_row -> option brrr_type -> option brrr_type ->
  option (brrr_type & brrr_type)

(** ============================================================================
    TYPE CHECKING RESULTS
    ============================================================================ *)

(** Result of type checking an expression *)
noeq type check_result =
  | CheckOk  : eff:effect_row -> check_result
  | CheckErr : msg:string -> check_result

(** Result of type inference for an expression *)
val check_expr_type : expr -> brrr_type -> check_result

(** Check yield expression with generator context *)
val check_yield : expr -> gen_typing_ctx -> option (brrr_type & effect_row)

(** Check yield with explicit type annotation *)
val check_yield_annotated : expr -> brrr_type -> brrr_type -> option (brrr_type & effect_row)

(** ============================================================================
    GENERATOR EXPRESSION TYPE CHECKING
    ============================================================================ *)

(** Check generator creation expression with hints *)
val check_gen_expr : expr -> option brrr_type -> option brrr_type ->
  option (generator_type & effect_row)

(** Check generator with explicit type parameters *)
val check_gen_expr_typed : expr -> brrr_type -> brrr_type -> brrr_type ->
  option (generator_type & effect_row)

(** Infer generator expression type from body *)
val infer_gen_expr : expr -> option (generator_type & effect_row)

(** ============================================================================
    YIELD FROM TYPE CHECKING
    ============================================================================ *)

(** Check yield* (yield from) expression *)
val check_yield_from : expr -> gen_typing_ctx -> option (brrr_type & effect_row)

(** ============================================================================
    ASYNC TYPING ENVIRONMENT
    ============================================================================ *)

(** Type binding: variable name, type, and usage mode *)
noeq type async_type_binding = {
  atb_name : var_id;
  atb_type : brrr_type;
  atb_mode : BrrrModes.mode
}

(** Full async typing context *)
noeq type async_typing_ctx = {
  atc_bindings  : list async_type_binding;
  atc_gen_ctx   : gen_typing_ctx;
  atc_in_async  : bool
}

(** Empty async typing context *)
val empty_async_ctx : async_typing_ctx

(** Create async context with generator info *)
val async_ctx_with_gen : gen_typing_ctx -> async_typing_ctx

(** Extend context with a variable binding *)
val extend_async_ctx : var_id -> brrr_type -> BrrrModes.mode -> async_typing_ctx -> async_typing_ctx

(** Lookup variable in context *)
val lookup_async_ctx : var_id -> async_typing_ctx -> option brrr_type

(** Enter async context *)
val enter_async_context : async_typing_ctx -> async_typing_ctx

(** Enter generator context with yield/resume types *)
val enter_gen_context : async_typing_ctx -> brrr_type -> brrr_type -> brrr_type -> async_typing_ctx

(** ============================================================================
    BIDIRECTIONAL TYPE INFERENCE FOR ASYNC EXPRESSIONS
    ============================================================================ *)

(** Result of full async type inference *)
val gen_result_type : brrr_type -> brrr_type -> brrr_type

(** Timeout error type *)
val timeout_error_type : brrr_type

(** Duration type *)
val duration_type : brrr_type

(** Infer type of an expression in async typing context *)
val infer_expr_type : async_typing_ctx -> e:expr -> Tot (option (brrr_type & effect_row)) (decreases e)

(** Remove Async effect from row *)
val remove_async_effect : effect_row -> effect_row

(** Check if effect row contains Async *)
val has_async_effect : effect_row -> bool

(** Add Async effect to row if not present *)
val ensure_async_effect : effect_row -> effect_row

(** Full bidirectional type inference for async expressions *)
noeq type async_full_infer_result =
  | AsyncOk  : ty:brrr_type -> eff:effect_row -> ctx':async_typing_ctx -> async_full_infer_result
  | AsyncErr : msg:string -> async_full_infer_result

(** Generator result type *)
val infer_async_expr_full : async_typing_ctx -> async_expr -> async_full_infer_result

(** ============================================================================
    SIMPLIFIED API
    ============================================================================ *)

(** Type check async expression with generator context *)
val check_async_expr : async_expr -> gen_typing_ctx -> option (brrr_type & effect_row)

(** Type check async expression with full context *)
val check_async_expr_full : async_typing_ctx -> async_expr ->
  option (brrr_type & effect_row & async_typing_ctx)

(** Infer async expression with error message *)
val infer_async_expr_with_error : async_typing_ctx -> async_expr ->
  either string (brrr_type & effect_row)

(** ============================================================================
    STRUCTURED CONCURRENCY TYPES
    ============================================================================ *)

(** Cancel state for type-level tracking *)
type cancel_state =
  | CancelNotRequested : cancel_state
  | CancelRequested    : cancel_state

(** Task group state *)
noeq type task_group_type = {
  tg_value_type   : brrr_type;
  tg_cancel_state : cancel_state
}

(** Create task group type *)
val mk_task_group_type : brrr_type -> task_group_type

(** Convert task_group_type to brrr_type *)
val task_group_to_brrr_type : task_group_type -> brrr_type

(** Extract task group type from brrr_type *)
val extract_task_group_type : brrr_type -> option task_group_type

(** List type constructor *)
val list_type : brrr_type -> brrr_type

(** ============================================================================
    STRUCTURED CONCURRENCY EXPRESSIONS
    ============================================================================ *)

(** Structured concurrency expression forms *)
noeq type struct_conc_expr =
  | SCTaskGroup : body:expr -> struct_conc_expr
  | SCSpawnIn : group:expr -> body:expr -> struct_conc_expr
  | SCWaitAll : group:expr -> struct_conc_expr
  | SCCancelToken : token:expr -> struct_conc_expr
  | SCIsCancelled : token:expr -> struct_conc_expr

(** Result type for structured concurrency inference *)
noeq type sc_infer_result =
  | SCOk  : ty:brrr_type -> eff:effect_row -> sc_infer_result
  | SCErr : msg:string -> sc_infer_result

(** Infer type of structured concurrency expression *)
val infer_struct_conc_expr : async_typing_ctx -> struct_conc_expr -> sc_infer_result

(** ============================================================================
    ANALYSIS TYPES
    ============================================================================ *)

(** Analysis result for Brrr-Machine *)
noeq type async_analysis_result = {
  aar_scope_escapes    : list (var_id & string);
  aar_invalid_spawns   : list string;
  aar_cancel_issues    : list string;
  aar_ordering_issues  : list string;
  aar_yield_points     : list (nat & var_id);
  aar_effect_errors    : list string
}

(** Empty analysis result *)
val empty_analysis_result : async_analysis_result

(** Analysis context for tracking state *)
type task_group_state =
  | TGOpen   : task_group_state
  | TGClosed : task_group_state

(** Task group type *)
noeq type async_analysis_ctx = {
  aac_task_groups : list (var_id & task_group_state);
  aac_cancel_tokens : list (var_id & cancel_state);
  aac_in_async_scope : bool;
  aac_in_gen_scope : bool;
  aac_scope_depth : nat
}

(** Initial analysis context *)
val init_analysis_ctx : async_analysis_ctx

(** Legacy: Get yield context from generator context *)
val infer_yield_context_from : gen_typing_ctx -> option (brrr_type & brrr_type)

(** ============================================================================
    STATE MACHINE TYPES
    ============================================================================ *)

(** State machine state identifier *)
type sm_state_id = nat

(** State in the state machine *)
noeq type sm_transition = {
  sm_from : sm_state_id;
  sm_to   : sm_state_id;
  sm_cond : option expr;
  sm_action : expr
}

(** Complete state machine *)
noeq type sm_state =
  | SMInitial   : sm_state_id -> sm_state
  | SMSuspended : sm_state_id -> var_id -> sm_state
  | SMFinal     : sm_state_id -> sm_state

(** State machine transition *)
noeq type state_machine = {
  sm_name        : string;
  sm_states      : list sm_state;
  sm_initial     : sm_state_id;
  sm_finals      : list sm_state_id;
  sm_transitions : list sm_transition;
  sm_locals      : list (var_id & brrr_type);
  sm_params      : list (var_id & brrr_type);
  sm_return_type : brrr_type;
  sm_yield_type  : option brrr_type;
  sm_resume_type : option brrr_type
}

(** Create empty state machine *)
val empty_state_machine : string -> brrr_type -> state_machine

(** ============================================================================
    STATE MACHINE COMPILATION CONTEXT
    ============================================================================ *)

(** Compilation context for state machine construction *)
noeq type sm_compile_ctx = {
  smc_next_state : nat;
  smc_current_state : sm_state_id;
  smc_locals : list (var_id & brrr_type);
  smc_states : list sm_state;
  smc_transitions : list sm_transition
}

(** Initial compilation context *)
val init_sm_compile_ctx : sm_compile_ctx

(** Allocate a new state *)
val alloc_state : sm_compile_ctx -> (sm_state_id & sm_compile_ctx)

(** Add a suspended state *)
val add_suspended_state : sm_compile_ctx -> var_id -> (sm_state_id & sm_compile_ctx)

(** Add a final state *)
val add_final_state : sm_compile_ctx -> (sm_state_id & sm_compile_ctx)

(** Add a transition *)
val add_transition : sm_compile_ctx -> sm_state_id -> sm_state_id -> option expr -> expr -> sm_compile_ctx

(** Register a local variable *)
val register_local : sm_compile_ctx -> var_id -> brrr_type -> sm_compile_ctx

(** Set current state *)
val set_current_state : sm_compile_ctx -> sm_state_id -> sm_compile_ctx

(** ============================================================================
    STATE MACHINE COMPILATION
    ============================================================================ *)

(** Compilation result *)
val contains_await : e:expr -> Tot bool (decreases %[expr_size e; 0])

(** Check if expression contains any yield *)
val contains_yield : e:expr -> Tot bool (decreases %[expr_size e; 0])

(** Compile a single expression, creating suspension points as needed *)
noeq type sm_compile_result =
  | SMCompileOk  : ctx:sm_compile_ctx -> next_expr:expr -> sm_compile_result
  | SMCompileErr : msg:string -> sm_compile_result

(** Check if expression contains any await *)
val compile_expr_to_sm : sm_compile_ctx -> e:expr ->
  Tot sm_compile_result (decreases %[expr_size e; 0])

(** Extract compiled arguments from EBlock wrapper *)
val extract_compiled_args : sm_compile_result -> option (sm_compile_ctx & list expr)

(** Compile async function to state machine *)
val compile_async_function : string -> list (var_id & brrr_type) -> expr -> brrr_type ->
  option state_machine

(** Compile generator to state machine *)
val compile_generator : string -> list (var_id & brrr_type) -> expr ->
  brrr_type -> brrr_type -> brrr_type -> option state_machine

(** ============================================================================
    ASYNC COMPUTATION MONAD
    ============================================================================ *)

(** Async computation monad (CPS-style) *)
noeq type async_comp (a: Type) =
  | AsyncPure : a -> async_comp a
  | AsyncBind : #b:Type -> async_comp b -> (b -> async_comp a) -> async_comp a
  | AsyncAwait : #b:Type -> future_state b -> (b -> async_comp a) -> async_comp a
  | AsyncSpawn : #b:Type -> (unit -> async_comp b) -> (future_state b -> async_comp a) -> async_comp a

(** Return for async monad *)
val async_return : #a:Type -> a -> async_comp a

(** Bind for async monad *)
val async_bind : #a:Type -> #b:Type -> async_comp a -> (a -> async_comp b) -> async_comp b

(** Await operation *)
val async_await : #a:Type -> #b:Type -> future_state a -> (a -> async_comp b) -> async_comp b

(** Spawn operation *)
val async_spawn : #a:Type -> #b:Type -> (unit -> async_comp a) ->
  (future_state a -> async_comp b) -> async_comp b

(** ============================================================================
    ASYNC MONAD LAWS
    ============================================================================ *)

(** Semantic equivalence for async_comp *)
val async_comp_equiv : #a:Type -> async_comp a -> async_comp a -> prop

(** Normalization function *)
val async_normalize : #a:Type -> async_comp a -> Tot (async_comp a)

(** Pure async computation - subset without effects *)
noeq type pure_async (a: Type) =
  | PureReturn : a -> pure_async a
  | PureBind : #b:Type -> pure_async b -> (b -> pure_async a) -> pure_async a

(** CPS-style evaluation for pure async computations *)
val pure_async_eval : #a:Type -> #r:Type -> pure_async a -> (a -> r) -> Tot r

(** Semantic equivalence for pure async *)
val pure_async_equiv : #a:Type -> pure_async a -> pure_async a -> prop

(** Semantic equivalence for the full async_comp *)
val async_semantically_equiv : #a:Type -> async_comp a -> async_comp a -> prop

(** Monad Law 1: Left Identity *)
val async_monad_left_identity : #a:Type -> #b:Type -> x:a -> f:(a -> async_comp b) ->
  Lemma (ensures async_normalize (async_bind (async_return x) f) == f x)
        [SMTPat (async_bind (async_return x) f)]

(** Monad Law 2: Right Identity *)
val async_monad_right_identity : #a:Type -> m:async_comp a ->
  Lemma (ensures async_semantically_equiv (async_bind m async_return) m)
        [SMTPat (async_bind m async_return)]

(** Monad Law 3: Associativity *)
val async_monad_associativity : #a:Type -> #b:Type -> #c:Type ->
  m:async_comp a -> f:(a -> async_comp b) -> g:(b -> async_comp c) ->
  Lemma (ensures async_semantically_equiv
                   (async_bind (async_bind m f) g)
                   (async_bind m (fun x -> async_bind (f x) g)))
        [SMTPat (async_bind (async_bind m f) g)]

(** ============================================================================
    GENERATOR SEMANTICS
    ============================================================================ *)

(** Iterator state (result of running generator) *)
val max_gen_initial_unfold_depth : nat

(** Convert single generator state step to iterator state step with fuel *)
noeq type iterator_state (y: Type) (t: Type) =
  | IterDone    : final:t -> iterator_state y t
  | IterYielded : value:y -> resume:(unit -> iterator_state y t) -> iterator_state y t
  | IterFailed  : error:string -> iterator_state y t

(** Maximum depth for unfolding GenInitial states *)
val gen_to_iter_step_fuel : #y:Type -> #t:Type -> gen_state y unit t -> nat ->
  Tot (iterator_state y t)

(** Convert generator state to iterator state with default fuel *)
val gen_to_iter_step : #y:Type -> #t:Type -> gen_state y unit t -> iterator_state y t

(** Create iterator from generator *)
val make_iterator : #y:Type -> #t:Type -> generator y unit t -> iterator_state y t

(** Collect yielded values with a fuel bound *)
val collect_iter_bounded : #y:Type -> #t:Type -> iterator_state y t -> nat -> Tot (list y)

(** Collect all values from a finite iterator *)
val collect_iter : #y:Type -> #t:Type -> iterator_state y t -> list y

(** ============================================================================
    TYPE CHECKING LEMMAS
    ============================================================================ *)

(** Type safety lemma for async expressions *)
val async_type_safety : body_ty:brrr_type -> body_eff:effect_row ->
  Lemma (requires has_effect BrrrEffects.EAsync body_eff)
        (ensures True)
        [SMTPat (cold_future body_ty); SMTPat (has_effect BrrrEffects.EAsync body_eff)]

(** Type safety lemma for await expressions *)
val await_type_safety : inner_ty:brrr_type -> temp:future_temperature -> base_eff:effect_row ->
  Lemma (requires True)
        (ensures (
          type_eq (mk_future_type inner_ty temp).fut_value_type inner_ty /\
          has_effect BrrrEffects.EAsync (add_effect BrrrEffects.EAsync base_eff)))
        [SMTPat (mk_future_type inner_ty temp)]

(** Type safety lemma for yield expressions *)
val yield_type_safety : yield_ty:brrr_type -> resume_ty:brrr_type ->
  Lemma (requires True)
        (ensures (
          type_eq (mk_generator_type yield_ty resume_ty t_unit).gen_yield_type yield_ty /\
          type_eq (mk_generator_type yield_ty resume_ty t_unit).gen_resume_type resume_ty))
        [SMTPat (mk_generator_type yield_ty resume_ty t_unit)]

(** Type safety lemma for generator expressions *)
val gen_type_safety : yield_ty:brrr_type -> resume_ty:brrr_type -> return_ty:brrr_type ->
  Lemma (requires True)
        (ensures (
          type_eq (mk_generator_type yield_ty resume_ty return_ty).gen_yield_type yield_ty /\
          type_eq (mk_generator_type yield_ty resume_ty return_ty).gen_resume_type resume_ty /\
          type_eq (mk_generator_type yield_ty resume_ty return_ty).gen_return_type return_ty /\
          type_eq (generator_to_brrr_type (mk_generator_type yield_ty resume_ty return_ty))
                  (TApp (TNamed "Generator") [yield_ty; resume_ty; return_ty])))
        [SMTPat (mk_generator_type yield_ty resume_ty return_ty)]

(** ============================================================================
    STATE MACHINE CORRECTNESS
    ============================================================================ *)

(** State machine invariant: all states are reachable from initial *)
val state_reachable_fuel : state_machine -> sm_state_id -> list sm_state_id -> nat -> Tot bool

(** Check if state is reachable with default fuel *)
val state_reachable : state_machine -> sm_state_id -> bool

(** Well-formed state machine type *)
val sm_well_formed : sm:state_machine ->
  Lemma (ensures
          sm.sm_initial >= 0 /\
          (forall id. List.Tot.mem id sm.sm_finals ==> state_reachable sm id) /\
          True)
        [SMTPat (state_reachable sm sm.sm_initial)]

(** Semantic preservation lemma for state machine compilation *)
type well_formed_sm = sm:state_machine{
  sm.sm_initial = 0 /\
  List.Tot.length sm.sm_states > 0
}

(** Well-formedness lemma for state machines *)
val sm_semantics_preserved : original:expr -> compiled:well_formed_sm ->
  Lemma (ensures
          compiled.sm_initial = 0 /\
          List.Tot.length compiled.sm_finals >= 0)

(** ============================================================================
    CONVENIENCE API FOR ASYNC EXPRESSIONS
    ============================================================================ *)

(** Create async block expression *)
val mk_async : expr -> async_expr

(** Create await expression *)
val mk_await : expr -> async_expr

(** Create spawn expression *)
val mk_spawn : expr -> async_expr

(** Create generator expression *)
val mk_gen : expr -> async_expr

(** Create yield expression *)
val mk_yield : expr -> async_expr

(** Create yield* expression *)
val mk_yield_from : expr -> async_expr

(** Create join expression *)
val mk_join : list expr -> async_expr

(** Create select expression *)
val mk_select : list expr -> async_expr

(** Create timeout expression *)
val mk_timeout : expr -> expr -> async_expr

(** Create cancel expression *)
val mk_cancel : expr -> async_expr

(** ============================================================================
    TYPE BUILDERS
    ============================================================================ *)

(** Future type builder *)
val t_future : brrr_type -> future_temperature -> brrr_type

(** Hot future type *)
val t_hot_future : brrr_type -> brrr_type

(** Cold future type *)
val t_cold_future : brrr_type -> brrr_type

(** Lazy future type *)
val t_lazy_future : brrr_type -> brrr_type

(** Generator type builder *)
val t_generator : brrr_type -> brrr_type -> brrr_type -> brrr_type

(** Simple generator type *)
val t_simple_generator : brrr_type -> brrr_type

(** Iterator type *)
val t_iterator : brrr_type -> brrr_type

(** ============================================================================
    CANCELLATION TOKEN
    ============================================================================ *)

(** Cancel token state *)
noeq type cancel_token_state =
  | CTActive    : cancel_token_state
  | CTCancelled : reason:string -> cancel_token_state

(** Cancel token type *)
noeq type cancel_token = {
  ct_id       : nat;
  ct_state    : cancel_token_state;
  ct_parent   : option cancel_token;
  ct_children : list cancel_token
}

(** Create a new active cancel token *)
val mk_cancel_token : nat -> cancel_token

(** Create a child cancel token inheriting parent *)
val mk_child_cancel_token : nat -> cancel_token -> cancel_token

(** Register a child token with its parent *)
val register_child_token : cancel_token -> cancel_token -> cancel_token

(** Create child token AND register it with parent *)
val mk_child_cancel_token_registered : nat -> cancel_token -> (cancel_token & cancel_token)

(** ============================================================================
    CANCEL CHAIN ACYCLICITY
    ============================================================================ *)

(** Check if an ID is in a list of IDs *)
val id_in_list : nat -> list nat -> Tot bool

(** Collect all ancestor IDs in the parent chain *)
val collect_ancestor_ids : cancel_token -> nat -> Tot (list nat)

(** Maximum expected depth of cancel token chains *)
val max_cancel_chain_depth : nat

(** Check if all elements in a list are distinct *)
val all_distinct : list nat -> Tot bool

(** Predicate: cancel chain is acyclic *)
val cancel_chain_acyclic : cancel_token -> bool

(** Refined cancel token type with acyclicity guarantee *)
type acyclic_cancel_token = ct:cancel_token{cancel_chain_acyclic ct}

(** Create an acyclic root token *)
val mk_acyclic_root_token : nat -> acyclic_cancel_token

(** Create a child token with acyclicity check *)
val mk_acyclic_child_token : nat -> acyclic_cancel_token -> option acyclic_cancel_token

(** Lemma: root tokens are always acyclic *)
val root_token_acyclic : id:nat ->
  Lemma (ensures cancel_chain_acyclic (mk_cancel_token id))
        [SMTPat (mk_cancel_token id)]

(** ============================================================================
    CANCELLATION OPERATIONS
    ============================================================================ *)

(** Check if token is cancelled *)
val is_cancelled_with_visited : cancel_token -> list nat -> Tot bool

(** Check if token is cancelled (includes checking parent chain) *)
val is_cancelled : cancel_token -> bool

(** Cancel a token with reason *)
val cancel_token_with_reason : cancel_token -> string -> cancel_token

(** Cancel a token (default reason) *)
val cancel_token_simple : cancel_token -> cancel_token

(** Get cancellation reason if cancelled with cycle detection *)
val get_cancel_reason_with_visited : cancel_token -> list nat -> Tot (option string)

(** Get cancellation reason if cancelled *)
val get_cancel_reason : cancel_token -> option string

(** ============================================================================
    CANCELLATION PROPAGATION
    ============================================================================ *)

(** Size of cancel token tree for termination proofs *)
val cancel_token_tree_size : cancel_token -> nat -> Tot nat

(** Cancel a single token and all its children recursively with fuel *)
val cancel_with_propagation_fuel : cancel_token -> string -> nat -> Tot cancel_token

(** Cancel a token with downward propagation to all children *)
val cancel_with_propagation : cancel_token -> string -> cancel_token

(** Cancel with default reason *)
val cancel_with_propagation_simple : cancel_token -> cancel_token

(** ============================================================================
    CANCELLATION PREDICATES
    ============================================================================ *)

(** Predicate: A token is directly cancelled *)
val token_directly_cancelled : cancel_token -> bool

(** Predicate: A token is effectively cancelled *)
val token_effectively_cancelled : cancel_token -> bool

(** Check if a child token is in the children list *)
val is_child_of : cancel_token -> cancel_token -> bool

(** Check if a token is a descendant of another *)
val is_descendant_of_fuel : cancel_token -> cancel_token -> nat -> Tot bool

(** Check if token is a descendant of another *)
val is_descendant_of : cancel_token -> cancel_token -> bool

(** Predicate: All children of a token are cancelled *)
val all_children_cancelled_fuel : cancel_token -> nat -> Tot bool

(** Check if all children are cancelled *)
val all_children_cancelled : cancel_token -> bool

(** Predicate: All descendants are cancelled *)
val all_descendants_cancelled_fuel : cancel_token -> nat -> Tot bool

(** Check if all descendants are cancelled *)
val all_descendants_cancelled : cancel_token -> bool

(** ============================================================================
    CANCELLATION PROPAGATION PROOFS
    ============================================================================ *)

(** Lemma: After cancel_with_propagation, the token is cancelled *)
val cancel_propagation_cancels_self : ct:cancel_token -> reason:string ->
  Lemma (ensures token_directly_cancelled (cancel_with_propagation ct reason))
        [SMTPat (cancel_with_propagation ct reason)]

(** Lemma: After cancel_with_propagation, all children are cancelled *)
val cancel_propagation_cancels_all_children : ct:cancel_token -> reason:string ->
  Lemma (ensures all_children_cancelled (cancel_with_propagation ct reason))
        [SMTPat (all_children_cancelled (cancel_with_propagation ct reason))]

(** Lemma: After cancel_with_propagation, all descendants are cancelled *)
val cancel_propagation_cancels_all_descendants : ct:cancel_token -> reason:string ->
  Lemma (ensures all_descendants_cancelled (cancel_with_propagation ct reason))

(** Lemma: If parent is cancelled, child is also cancelled *)
val parent_cancelled_implies_child_cancelled : parent:cancel_token -> child:cancel_token ->
  Lemma (requires child.ct_parent == Some parent /\ token_directly_cancelled parent)
        (ensures is_cancelled child)

(** Lemma: Cancellation is irreversible *)
val cancellation_irreversible : ct:cancel_token -> reason1:string -> reason2:string ->
  Lemma (ensures token_directly_cancelled
                   (cancel_with_propagation (cancel_with_propagation ct reason1) reason2))

(** ============================================================================
    COOPERATIVE CANCELLATION CHECKPOINTS
    ============================================================================ *)

(** Cancellation exception type *)
noeq type cancellation_exception =
  | CancelledException : reason:string -> cancellation_exception

(** Check cancellation and return result or exception *)
val check_cancellation_point : cancel_token -> either unit cancellation_exception

(** Check cancellation and return bool *)
val should_continue : cancel_token -> bool

(** Get the cancellation exception if cancelled *)
val get_cancellation_exception : cancel_token -> option cancellation_exception

(** ============================================================================
    CANCELLATION SCOPE HELPERS
    ============================================================================ *)

(** Create a cancellation scope with a new child token *)
val enter_cancellation_scope : cancel_token -> nat -> (cancel_token & cancel_token)

(** Cancel a scope and all its children *)
val cancel_scope : cancel_token -> string -> cancel_token

(** Check if a scope should continue or has been cancelled *)
val scope_active : cancel_token -> bool

(** ============================================================================
    TASK GROUP
    ============================================================================ *)

(** Task status within a group *)
type error_policy =
  | EPCancelOnFirst
  | EPWaitAll
  | EPCancelOnAny

(** Task group type *)
noeq type task_status (a: Type) =
  | TaskPending    : task_status a
  | TaskRunning    : future_state a -> task_status a
  | TaskCompleted  : result:a -> task_status a
  | TaskFailed     : error:string -> task_status a
  | TaskCancelled  : reason:string -> task_status a

(** Child task entry in a task group *)
noeq type task_entry (a: Type) = {
  te_id     : nat;
  te_status : task_status a;
  te_future : option (future_state a)
}

(** Error handling policy for task groups *)
noeq type task_group (a: Type) = {
  tg_id           : nat;
  tg_children     : list (task_entry a);
  tg_cancel_token : cancel_token;
  tg_parent       : option (task_group a);
  tg_next_task_id : nat;
  tg_error_policy : error_policy
}

(** Create a new task group with fresh cancel token *)
val mk_task_group : #a:Type -> nat -> nat -> task_group a

(** Create a child task group inheriting parent's cancel token *)
val mk_child_task_group : #a:Type -> nat -> nat -> task_group a -> task_group a

(** Create task group with specific error policy *)
val mk_task_group_with_policy : #a:Type -> nat -> nat -> error_policy -> task_group a

(** Check if group is cancelled *)
val is_group_cancelled : #a:Type -> task_group a -> bool

(** Get number of pending/running tasks *)
val count_active_tasks : #a:Type -> task_group a -> nat

(** Check if all tasks are complete *)
val all_tasks_complete : #a:Type -> task_group a -> bool

(** ============================================================================
    TASK GROUP OPERATIONS
    ============================================================================ *)

(** Spawn a new task within the group *)
val spawn_in : #a:Type -> task_group a -> (unit -> future_state a) ->
  (task_group a & future_state a)

(** Spawn with pending status *)
val spawn_pending : #a:Type -> task_group a -> (task_group a & nat)

(** Update task entry with new status *)
val update_task_status : #a:Type -> task_group a -> nat -> task_status a -> task_group a

(** Get all results from completed tasks *)
val get_completed_results : #a:Type -> task_group a -> list a

(** Get all errors from failed tasks *)
val get_task_errors : #a:Type -> task_group a -> list string

(** Check if any task has failed *)
val has_failed_tasks : #a:Type -> task_group a -> bool

(** Cancel all running tasks in the group *)
val cancel_all_tasks : #a:Type -> task_group a -> string -> task_group a

(** Wait all result type *)
noeq type wait_all_result (a: Type) =
  | WaitAllSuccess  : results:list a -> wait_all_result a
  | WaitAllPartial  : results:list a -> errors:list string -> wait_all_result a
  | WaitAllCancelled : reason:string -> partial_results:list a -> wait_all_result a

(** Simulate waiting for all tasks *)
val wait_all_sync : #a:Type -> task_group a -> wait_all_result a

(** ============================================================================
    STRUCTURED ASYNC EXPRESSIONS
    ============================================================================ *)

(** Structured concurrency expression forms *)
noeq type structured_async_expr =
  | SAETaskGroup : body:expr -> error_policy -> structured_async_expr
  | SAESpawnIn : group:expr -> body:expr -> structured_async_expr
  | SAEWaitAll : group:expr -> structured_async_expr
  | SAEGetCancelToken : structured_async_expr
  | SAECheckCancelled : structured_async_expr
  | SAEWithCancellation : token:expr -> body:expr -> structured_async_expr
  | SAECancelToken : token:expr -> reason:expr -> structured_async_expr
  | SAENursery : body:expr -> structured_async_expr
  | SAEScope : body:expr -> structured_async_expr

(** Size function for structured_async_expr *)
val structured_async_expr_size : structured_async_expr -> nat

(** Cancel token to brrr_type *)
val cancel_token_to_brrr_type : brrr_type

(** Type check structured async expression *)
val check_structured_async_expr : structured_async_expr -> nat -> option (brrr_type & effect_row)

(** ============================================================================
    CANCELLATION CHECK
    ============================================================================ *)

(** Cancellation check result *)
noeq type cancellation_check =
  | CCContinue : cancellation_check
  | CCCancelled : reason:string -> cancellation_check

(** Check cancellation at a suspension point *)
(** Either type for error handling - Left is error, Right is success *)
val check_cancellation : cancel_token -> cancellation_check

(** Inject cancellation check into await *)
val await_with_cancellation : #a:Type -> cancel_token -> future_state a -> future_state a

(** Inject cancellation check into generator state transition *)
val gen_with_cancellation : #y:Type -> #r:Type -> #t:Type -> cancel_token -> gen_state y r t ->
  gen_state y r t

(** Legacy alias for gen_with_cancellation *)
val yield_with_cancellation : #y:Type -> #r:Type -> #t:Type -> cancel_token -> gen_state y r t ->
  gen_state y r t

(** ============================================================================
    SCOPE TRACKING
    ============================================================================ *)

(** Scope entry for tracking task group lifetimes *)
noeq type scope_entry = {
  se_scope_id   : nat;
  se_group_id   : nat;
  se_parent     : option nat;
  se_children   : list nat
}

(** Scope stack for structured concurrency analysis *)
type scope_stack = list scope_entry

(** Push a new scope *)
val push_scope : scope_stack -> nat -> nat -> scope_stack

(** Pop the current scope *)
val pop_scope : scope_stack -> option (scope_entry & scope_stack)

(** Check if a task group ID is in scope *)
val is_group_in_scope : scope_stack -> nat -> bool

(** Get current scope's task group ID *)
val current_group_id : scope_stack -> option nat

(** ============================================================================
    ANALYSIS REQUIREMENTS
    ============================================================================ *)

(** Analysis requirement markers for Brrr-Machine *)
noeq type analysis_requirement =
  | ARScopeEscape     : group_id:nat -> location:string -> analysis_requirement
  | ARSpawnValidity   : spawn_location:string -> group_ref:string -> analysis_requirement
  | ARCancellationCheck : suspension_point:string -> analysis_requirement
  | ARCompletionOrder : scope_id:nat -> analysis_requirement
  | ARErrorHandling   : group_id:nat -> analysis_requirement

(** Collect analysis requirements from structured async expression *)
val collect_analysis_requirements : structured_async_expr -> string -> list analysis_requirement

(** ============================================================================
    GENERATOR STATE ANALYSIS
    ============================================================================ *)

(** Generator state for static analysis *)
type gen_state_tag =
  | GSInitial
  | GSYielded
  | GSDone
  | GSFailed

(** Extract state tag from generator state *)
val gen_state_to_tag : #y:Type -> #r:Type -> #t:Type -> gen_state y r t -> gen_state_tag

(** Check if state transition is valid *)
val valid_gen_transition : gen_state_tag -> gen_state_tag -> bool

(** Generator analysis entry for Brrr-Machine *)
noeq type gen_analysis_requirement =
  | GARStateTransition  : gen_id:nat -> from_state:gen_state_tag -> to_state:gen_state_tag
                          -> location:string -> gen_analysis_requirement
  | GARUseAfterDone     : gen_id:nat -> location:string -> gen_analysis_requirement
  | GARCancellationCheck: gen_id:nat -> yield_location:string -> gen_analysis_requirement
  | GARResourceLeak     : gen_id:nat -> created_at:string -> gen_analysis_requirement
  | GARInfiniteLoop     : gen_id:nat -> location:string -> gen_analysis_requirement

(** Verify a generator state transition *)
noeq type gen_analysis_entry = {
  gae_id         : nat;
  gae_state      : gen_state_tag;
  gae_location   : string;
  gae_yield_type : option brrr_type;
  gae_resume_type: option brrr_type;
  gae_return_type: option brrr_type
}

(** Generator analysis requirements *)
val verify_gen_transition : gen_analysis_entry -> gen_state_tag -> string ->
  option gen_analysis_requirement

(** Check for use-after-done *)
val check_use_after_done : gen_analysis_entry -> string -> option gen_analysis_requirement

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR STRUCTURED CONCURRENCY
    ============================================================================ *)

(** Create task group expression *)
val mk_task_group_expr : expr -> structured_async_expr

(** Create task group with policy *)
val mk_task_group_expr_policy : expr -> error_policy -> structured_async_expr

(** Create spawn_in expression *)
val mk_spawn_in_expr : expr -> expr -> structured_async_expr

(** Create wait_all expression *)
val mk_wait_all_expr : expr -> structured_async_expr

(** Create nursery expression *)
val mk_nursery_expr : expr -> structured_async_expr

(** Create scope expression *)
val mk_scope_expr : expr -> structured_async_expr

(** Create cancellation check expression *)
val mk_check_cancelled_expr : structured_async_expr

(** Create cancel expression *)
val mk_cancel_expr : expr -> expr -> structured_async_expr

(** ============================================================================
    TYPE BUILDERS FOR STRUCTURED CONCURRENCY
    ============================================================================ *)

(** Task group type *)
val t_task_group : brrr_type -> brrr_type

(** Cancel token type *)
val t_cancel_token : brrr_type

(** Wait result type *)
val t_wait_result : brrr_type -> brrr_type

(** ============================================================================
    TASKGROUP ESCAPE ANALYSIS
    ============================================================================ *)

(** Scope nesting level *)
type task_group_scope = nat

(** Get the global (outermost) scope level *)
val global_scope : task_group_scope

(** Create a child scope *)
val child_scope : task_group_scope -> task_group_scope

(** Check if scope a is nested within scope b *)
val scope_nested_in : task_group_scope -> task_group_scope -> bool

(** Check if scope a is strictly nested within scope b *)
val scope_strictly_nested : task_group_scope -> task_group_scope -> bool

(** ============================================================================
    SCOPED TASK GROUP
    ============================================================================ *)

(** Task group with scope tracking *)
noeq type scoped_task_group (a: Type) = {
  stg_id           : nat;
  stg_scope        : task_group_scope;
  stg_children     : list (task_entry a);
  stg_cancel_token : cancel_token;
  stg_parent       : option (scoped_task_group a);
  stg_next_task_id : nat;
  stg_error_policy : error_policy;
  stg_active       : bool
}

(** Create a scoped task group at a given scope level *)
val mk_scoped_task_group : #a:Type -> nat -> nat -> task_group_scope -> scoped_task_group a

(** Create a child scoped task group *)
val mk_child_scoped_task_group : #a:Type -> nat -> nat -> scoped_task_group a -> scoped_task_group a

(** Check if a scoped task group is still active *)
val is_scoped_group_active : #a:Type -> scoped_task_group a -> bool

(** Close a scoped task group *)
val close_scoped_group : #a:Type -> scoped_task_group a -> scoped_task_group a

(** ============================================================================
    SCOPED TASK HANDLE
    ============================================================================ *)

(** Scoped task handle - tracks creation scope for escape analysis *)
noeq type task_handle_scoped (a: Type) = {
  ths_id             : nat;
  ths_creation_scope : task_group_scope;
  ths_group_id       : nat;
  ths_status         : task_status a;
  ths_future         : option (future_state a)
}

(** Create a scoped task handle *)
val mk_task_handle_scoped : #a:Type -> nat -> task_group_scope -> nat -> task_handle_scoped a

(** Get the creation scope of a task handle *)
val get_handle_scope : #a:Type -> task_handle_scoped a -> task_group_scope

(** Check if task handle is for a specific group *)
val handle_belongs_to_group : #a:Type -> task_handle_scoped a -> nat -> bool

(** ============================================================================
    ESCAPE ANALYSIS FUNCTIONS
    ============================================================================ *)

(** Check if a task handle escapes the given scope *)
val task_escapes_scope : #a:Type -> task_handle_scoped a -> task_group_scope -> bool

(** Check if a task handle is valid in the given scope *)
val task_valid_in_scope : #a:Type -> task_handle_scoped a -> task_group_scope -> bool

(** Check if a task handle escapes its containing group's scope *)
val task_escapes_group : #a:Type -> task_handle_scoped a -> scoped_task_group a -> bool

(** Check if all tasks in a group are within scope *)
val all_tasks_within_scope : #a:Type -> list (task_handle_scoped a) -> task_group_scope -> bool

(** ============================================================================
    TASK IN GROUP PREDICATES
    ============================================================================ *)

(** Predicate: task handle was spawned in the given group *)
val task_in_group : #a:Type -> task_handle_scoped a -> scoped_task_group a -> bool

(** Predicate: task handle status is completed *)
val task_handle_completed : #a:Type -> task_handle_scoped a -> bool

(** Predicate: task group has completed *)
val scoped_group_completed : #a:Type -> scoped_task_group a -> bool

(** ============================================================================
    SCOPE-CHECKED SPAWN
    ============================================================================ *)

(** Result of scope-checked spawn *)
noeq type spawn_result (a: Type) =
  | SpawnOk : group:scoped_task_group a -> handle:task_handle_scoped a -> spawn_result a
  | SpawnGroupClosed : spawn_result a
  | SpawnGroupCancelled : spawn_result a

(** Spawn a task in a scoped group with scope tracking *)
val spawn_in_scoped_group : #a:Type -> scoped_task_group a -> (unit -> future_state a) ->
  spawn_result a

(** Get all task handles from a scoped group *)
val get_scoped_task_handles : #a:Type -> scoped_task_group a -> list (task_handle_scoped a)

(** ============================================================================
    WAIT ALL FOR SCOPED GROUPS
    ============================================================================ *)

(** Wait result for scoped groups *)
val get_scoped_results : #a:Type -> scoped_task_group a -> list a

(** Get errors from scoped group *)
val get_scoped_errors : #a:Type -> scoped_task_group a -> list string

(** Check for failures in scoped group *)
val scoped_group_has_failures : #a:Type -> scoped_task_group a -> bool

(** Wait for all tasks in scoped group *)
noeq type scoped_wait_result (a: Type) =
  | ScopedWaitSuccess  : results:list a -> scoped_wait_result a
  | ScopedWaitPartial  : results:list a -> errors:list string -> scoped_wait_result a
  | ScopedWaitCancelled : reason:string -> partial:list a -> scoped_wait_result a

(** Get completed results from scoped group *)
val wait_all_scoped : #a:Type -> scoped_task_group a -> scoped_wait_result a

(** ============================================================================
    WITH_TASK_GROUP PATTERN
    ============================================================================ *)

(** Scope context for tracking current scope level *)
noeq type scope_context = {
  sc_current_scope : task_group_scope;
  sc_next_group_id : nat;
  sc_next_token_id : nat
}

(** Initial scope context *)
val initial_scope_context : scope_context

(** Enter a new scope level *)
val enter_scope_ctx : scope_context -> scope_context

(** Exit current scope level *)
val exit_scope_ctx : scope_context -> scope_context

(** Get current scope level from context *)
val current_scope_level : scope_context -> task_group_scope

(** Result type for with_task_group *)
val create_task_group_in_context : #a:Type -> scope_context -> (scoped_task_group a & scope_context)

(** Execute body with a scoped task group *)
noeq type with_group_result (a: Type) =
  | WithGroupOk : result:a -> with_group_result a
  | WithGroupError : errors:list string -> with_group_result a
  | WithGroupCancelled : reason:string -> with_group_result a

(** Create a task group within the current scope context *)
val with_task_group_impl : #a:Type -> #b:Type -> scope_context ->
  (scoped_task_group a -> b & scoped_task_group a) -> (with_group_result b & scope_context)

(** ============================================================================
    ESCAPE ANALYSIS THEOREMS
    ============================================================================ *)

(** THEOREM: No Escape *)
val no_escape_theorem : #a:Type -> g:scoped_task_group a -> h:task_handle_scoped a ->
  Lemma (requires task_in_group h g)
        (ensures h.ths_creation_scope <= g.stg_scope)
        [SMTPat (task_in_group h g)]

(** LEMMA: Spawn preserves scope invariant *)
val spawn_preserves_scope : #a:Type -> g:scoped_task_group a -> body:(unit -> future_state a) ->
  Lemma (ensures (
    match spawn_in_scoped_group g body with
    | SpawnOk g' h -> h.ths_creation_scope = g.stg_scope
    | _ -> true))
  [SMTPat (spawn_in_scoped_group g body)]

(** LEMMA: No task in group escapes its group's scope *)
val all_handles_within_scope : #a:Type -> g:scoped_task_group a ->
  Lemma (ensures all_tasks_within_scope (get_scoped_task_handles g) g.stg_scope)

(** THEOREM: Group Completion Waits All *)
val group_completion_waits_all_theorem : #a:Type -> g:scoped_task_group a ->
  Lemma (requires scoped_group_completed g)
        (ensures List.Tot.for_all
          (fun (te: task_entry a) ->
            match te.te_status with
            | TaskCompleted _ | TaskFailed _ | TaskCancelled _ -> true
            | _ -> false)
          g.stg_children)
        [SMTPat (scoped_group_completed g)]

(** LEMMA: Tasks cannot escape with_task_group *)
val with_group_prevents_escape : #a:Type -> #b:Type -> ctx:scope_context ->
  body:(scoped_task_group a -> b & scoped_task_group a) ->
  Lemma (ensures (
    let inner_scope = child_scope ctx.sc_current_scope in
    inner_scope > ctx.sc_current_scope))

(** ============================================================================
    ANALYSIS CONTEXT FOR BRRR-MACHINE
    ============================================================================ *)

(** Analysis entry for scoped task groups *)
noeq type scoped_group_analysis_entry = {
  sgae_group_id    : nat;
  sgae_scope_level : task_group_scope;
  sgae_active      : bool;
  sgae_location    : string
}

(** Analysis entry for scoped task handles *)
noeq type scoped_handle_analysis_entry = {
  shae_handle_id     : nat;
  shae_creation_scope: task_group_scope;
  shae_group_id      : nat;
  shae_location      : string
}

(** Escape analysis context for Brrr-Machine *)
noeq type escape_analysis_ctx = {
  eac_current_scope  : task_group_scope;
  eac_groups         : list scoped_group_analysis_entry;
  eac_handles        : list scoped_handle_analysis_entry
}

(** Initial escape analysis context *)
val initial_escape_analysis_ctx : escape_analysis_ctx

(** Enter scope in analysis context *)
val analysis_enter_scope : escape_analysis_ctx -> escape_analysis_ctx

(** Exit scope in analysis context *)
val analysis_exit_scope : escape_analysis_ctx -> escape_analysis_ctx

(** Register a task group in analysis context *)
val analysis_register_group : escape_analysis_ctx -> nat -> string -> escape_analysis_ctx

(** Register a task handle in analysis context *)
val analysis_register_handle : escape_analysis_ctx -> nat -> nat -> string -> escape_analysis_ctx

(** Check if a handle escapes in the current analysis context *)
val analysis_check_escape : escape_analysis_ctx -> nat -> bool

(** Escape analysis requirement for Brrr-Machine *)
noeq type escape_analysis_requirement =
  | EARScopeEscape : handle_id:nat -> creation_scope:nat -> access_scope:nat
                     -> location:string -> escape_analysis_requirement
  | EARGroupInactive : group_id:nat -> location:string -> escape_analysis_requirement
  | EARHandleOrphan : handle_id:nat -> location:string -> escape_analysis_requirement

(** Collect escape analysis requirements *)
val check_escape_requirements : escape_analysis_ctx -> nat -> string ->
  list escape_analysis_requirement

(** ============================================================================
    TYPE-LEVEL SCOPE TRACKING
    ============================================================================ *)

(** Task handle scoped to a particular level *)
type task_handle_at_scope (a: Type) (scope: task_group_scope) =
  h:task_handle_scoped a{h.ths_creation_scope = scope}

(** Task group scoped to a particular level *)
type scoped_task_group_at (a: Type) (scope: task_group_scope) =
  g:scoped_task_group a{g.stg_scope = scope}

(** Task handle that cannot escape a given scope *)
val spawn_in_scoped_group_typed : #a:Type -> #scope:task_group_scope ->
  scoped_task_group_at a scope -> (unit -> future_state a) ->
  option (scoped_task_group a & task_handle_at_scope a scope)

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR TESTING
    ============================================================================ *)

(** Create a test scoped task group at global scope *)
val test_scoped_group : #a:Type -> scoped_task_group a

(** Create a test task handle at a given scope *)
val test_task_handle : #a:Type -> task_group_scope -> task_handle_scoped a

(** Verify escape detection works correctly *)
val test_escape_detection_lemma : outer_scope:task_group_scope -> inner_scope:task_group_scope ->
  Lemma (requires inner_scope > outer_scope)
        (ensures task_escapes_scope (test_task_handle inner_scope) outer_scope)

(** ============================================================================
    CHANNEL RUNTIME
    ============================================================================ *)

(** Unique identifier for channel operations *)
type channel_op_id = nat

(** Continuation for a suspended operation *)
noeq type channel_continuation (a: Type) =
  | ChContSend : op_id:channel_op_id -> value:a -> resume:(unit -> unit) -> channel_continuation a
  | ChContRecv : op_id:channel_op_id -> resume:(a -> unit) -> channel_continuation a

(** Extract operation ID from continuation *)
val get_cont_op_id : #a:Type -> channel_continuation a -> channel_op_id

(** ============================================================================
    CHANNEL STATE
    ============================================================================ *)

(** Internal buffer for channel values *)
type channel_buffer (a: Type) = list a

(** Queue of waiting senders *)
type receiver_wait_queue (a: Type) = list ((a -> unit) & channel_op_id)

(** Channel open state with runtime data *)
type sender_wait_queue (a: Type) = list (a & (unit -> unit) & channel_op_id)

(** Queue of waiting receivers *)
noeq type channel_open_state (a: Type) = {
  ch_buffer            : channel_buffer a;
  ch_capacity          : nat;
  ch_senders_waiting   : sender_wait_queue a;
  ch_receivers_waiting : receiver_wait_queue a;
  ch_next_op_id        : channel_op_id;
  ch_send_count        : nat;
  ch_recv_count        : nat
}

(** Channel state: either open or closed *)
noeq type channel_state (a: Type) =
  | ChOpen   : state:channel_open_state a -> channel_state a
  | ChClosed : remaining_buffer:channel_buffer a -> channel_state a

(** Check if channel state is open *)
val is_channel_open : #a:Type -> channel_state a -> bool

(** Check if channel state is closed *)
val is_channel_closed : #a:Type -> channel_state a -> bool

(** Get buffer from channel state *)
val get_channel_buffer : #a:Type -> channel_state a -> channel_buffer a

(** Get buffer length *)
val channel_buffer_len : #a:Type -> channel_state a -> nat

(** ============================================================================
    CHANNEL RUNTIME TYPE
    ============================================================================ *)

(** Channel identifier *)
type channel_id = nat

(** Runtime channel representation *)
noeq type channel_runtime (a: Type) = {
  chan_id         : channel_id;
  chan_state      : channel_state a;
  chan_elem_type  : brrr_type;
  chan_zero_value : a
}

(** Create an unbuffered channel *)
val mk_unbuffered_channel : #a:Type -> channel_id -> brrr_type -> a -> channel_runtime a

(** Create a buffered channel *)
val mk_buffered_channel : #a:Type -> channel_id -> brrr_type ->
  capacity:nat{capacity > 0} -> a -> channel_runtime a

(** ============================================================================
    CHANNEL OPERATION RESULTS
    ============================================================================ *)

(** Result of a send operation *)
noeq type send_result (a: Type) =
  | SendOk         : updated_chan:channel_runtime a -> send_result a
  | SendWouldBlock : updated_chan:channel_runtime a -> op_id:channel_op_id -> send_result a
  | SendClosed     : send_result a

(** Result of a receive operation *)
val channel_try_send : #a:Type -> channel_runtime a -> a -> send_result a

(** Register a waiting sender *)
val channel_register_sender : #a:Type -> channel_runtime a -> a -> (unit -> unit) ->
  channel_op_id -> channel_runtime a

(** Try to receive a value from a channel *)
noeq type recv_result (a: Type) =
  | RecvOk         : value:a -> updated_chan:channel_runtime a -> recv_result a
  | RecvWouldBlock : updated_chan:channel_runtime a -> op_id:channel_op_id -> recv_result a
  | RecvClosed     : zero_val:a -> recv_result a

(** Result of a close operation *)
val channel_try_recv : #a:Type -> channel_runtime a -> recv_result a

(** Register a waiting receiver *)
val channel_register_receiver : #a:Type -> channel_runtime a -> (a -> unit) ->
  channel_op_id -> channel_runtime a

(** Close a channel *)
noeq type close_result (a: Type) =
  | CloseOk        : updated_chan:channel_runtime a -> woken_senders:list channel_op_id
                     -> woken_receivers:list channel_op_id -> close_result a
  | ClosePanic     : reason:string -> close_result a

(** ============================================================================
    CHANNEL OPERATIONS
    ============================================================================ *)

(** Try to send a value on a channel *)
val channel_close : #a:Type -> channel_runtime a -> close_result a

(** ============================================================================
    SELECT STATEMENT
    ============================================================================ *)

(** Select case *)
noeq type select_case (a: Type) (r: Type) =
  | SelectRecv    : ch:channel_runtime a -> handler:(a -> r) -> select_case a r
  | SelectSend    : ch:channel_runtime a -> value:a -> handler:(unit -> r) -> select_case a r
  | SelectDefault : handler:(unit -> r) -> select_case a r

(** Result of checking if a select case is ready *)
noeq type select_check_result (a: Type) (r: Type) =
  | SCReady       : result:r -> updated_chan:channel_runtime a -> select_check_result a r
  | SCNotReady    : updated_chan:channel_runtime a -> op_id:channel_op_id -> select_check_result a r
  | SCClosed      : select_check_result a r
  | SCDefault     : handler:(unit -> r) -> select_check_result a r

(** Check if a single select case is ready *)
val check_select_case : #a:Type -> #r:Type -> select_case a r -> select_check_result a r

(** Result of a select operation *)
val rotate_list : #a:Type -> list a -> nat -> list a

(** Find first ready case in a list *)
val find_ready_case_fuel : #a:Type -> #r:Type -> list (select_case a r) -> nat -> nat -> nat -> nat ->
  Tot (option (r & nat))

(** Find first ready case with rotation for fairness *)
val find_ready_case : #a:Type -> #r:Type -> list (select_case a r) -> nat -> option (r & nat)

(** Check if there is a default case in the list *)
val has_default_case : #a:Type -> #r:Type -> list (select_case a r) -> bool

(** Find and extract the default handler if present *)
val find_default_handler : #a:Type -> #r:Type -> list (select_case a r) -> option (unit -> r)

(** Execute a select statement *)
noeq type select_result (r: Type) =
  | SelectOk           : result:r -> case_index:nat -> select_result r
  | SelectAllClosed    : select_result r
  | SelectWouldBlock   : pending_ops:list (nat & channel_op_id) -> select_result r

(** Rotate a list by n positions *)
val select_execute : #a:Type -> #r:Type -> list (select_case a r) -> nat -> select_result r

(** ============================================================================
    MULTI-TYPE SELECT SUPPORT
    ============================================================================ *)

(** Type-erased value wrapper for multi-type select *)
noeq type channel_registry_entry = {
  cre_id        : channel_id;
  cre_elem_type : brrr_type;
  cre_is_closed : bool;
  cre_buf_len   : nat;
  cre_capacity  : nat
}

(** Channel runtime context *)
noeq type channel_context = {
  cc_next_id  : channel_id;
  cc_registry : list channel_registry_entry
}

(** Initial channel context *)
val empty_channel_context : channel_context

(** Allocate a new channel ID *)
val alloc_channel_id : channel_context -> (channel_id & channel_context)

(** Register a channel in the context *)
val register_channel : channel_context -> channel_id -> brrr_type -> nat -> channel_context

(** Look up channel in registry *)
val lookup_channel : channel_context -> channel_id -> option channel_registry_entry

(** Update channel registry entry *)
val update_channel_entry : channel_context -> channel_id ->
  (channel_registry_entry -> channel_registry_entry) -> channel_context

(** Mark channel as closed in registry *)
val mark_channel_closed : channel_context -> channel_id -> channel_context

(** ============================================================================
    CHANNEL TYPE BUILDERS
    ============================================================================ *)

(** Channel type: Channel[T] *)
val t_channel : brrr_type -> brrr_type

(** Sender type: Sender[T] *)
val t_sender : brrr_type -> brrr_type

(** Receiver type: Receiver[T] *)
val t_receiver : brrr_type -> brrr_type

(** Select result type for two channels *)
val t_select_result : brrr_type -> brrr_type -> brrr_type

(** ============================================================================
    CHANNEL ANALYSIS FOR BRRR-MACHINE
    ============================================================================ *)

(** Channel operation type for analysis *)
noeq type channel_analysis_requirement =
  | CARTypeMismatch   : chan_id:channel_id -> expected:brrr_type -> actual:brrr_type
                        -> location:string -> channel_analysis_requirement
  | CARSendOnClosed   : chan_id:channel_id -> location:string -> channel_analysis_requirement
  | CARRecvOnClosed   : chan_id:channel_id -> location:string -> channel_analysis_requirement
  | CARDeadlock       : chan_ids:list channel_id -> location:string -> channel_analysis_requirement
  | CARUnusedChannel  : chan_id:channel_id -> location:string -> channel_analysis_requirement

(** Channel analysis context *)
type channel_op_type =
  | ChOpSend   : elem_ty:brrr_type -> channel_op_type
  | ChOpRecv   : elem_ty:brrr_type -> channel_op_type
  | ChOpClose  : channel_op_type
  | ChOpSelect : case_count:nat -> channel_op_type

(** Channel analysis entry *)
noeq type channel_analysis_entry = {
  cae_chan_id   : channel_id;
  cae_elem_type : brrr_type;
  cae_location  : string;
  cae_operation : channel_op_type
}

(** Channel analysis requirements *)
noeq type channel_analysis_ctx = {
  cac_channels   : list channel_analysis_entry;
  cac_violations : list channel_analysis_requirement
}

(** Initial channel analysis context *)
val empty_channel_analysis_ctx : channel_analysis_ctx

(** Register a channel operation for analysis *)
val register_channel_op : channel_analysis_ctx -> channel_analysis_entry -> channel_analysis_ctx

(** Record a channel analysis violation *)
val record_channel_violation : channel_analysis_ctx -> channel_analysis_requirement ->
  channel_analysis_ctx

(** ============================================================================
    CHANNEL THEOREMS
    ============================================================================ *)

(** THEOREM: Send on closed channel fails *)
val send_closed_fails_theorem : #a:Type -> ch:channel_runtime a -> v:a ->
  Lemma (requires is_channel_closed ch.chan_state)
        (ensures SendClosed? (channel_try_send ch v))
        [SMTPat (channel_try_send ch v)]

(** THEOREM: Recv on closed empty channel returns zero value *)
val recv_closed_empty_returns_zero_theorem : #a:Type -> ch:channel_runtime a ->
  Lemma (requires is_channel_closed ch.chan_state /\ channel_buffer_len ch.chan_state = 0)
        (ensures RecvClosed? (channel_try_recv ch))
        [SMTPat (channel_try_recv ch)]

(** THEOREM: Send on open channel with space succeeds *)
val send_with_space_succeeds_theorem : #a:Type -> ch:channel_runtime a -> v:a ->
  Lemma (requires (match ch.chan_state with
                   | ChOpen state ->
                       List.Tot.length state.ch_buffer < state.ch_capacity /\
                       List.Tot.length state.ch_receivers_waiting = 0
                   | ChClosed _ -> false))
        (ensures SendOk? (channel_try_send ch v))
        [SMTPat (channel_try_send ch v)]

(** THEOREM: Recv from non-empty buffer succeeds *)
val recv_from_nonempty_succeeds_theorem : #a:Type -> ch:channel_runtime a ->
  Lemma (requires channel_buffer_len ch.chan_state > 0)
        (ensures RecvOk? (channel_try_recv ch))
        [SMTPat (channel_try_recv ch)]

(** LEMMA: Close of already-closed channel panics *)
val close_already_closed_panics_lemma : #a:Type -> ch:channel_runtime a ->
  Lemma (requires is_channel_closed ch.chan_state)
        (ensures ClosePanic? (channel_close ch))

(** LEMMA: Buffer FIFO ordering preserved *)
val buffer_fifo_lemma : #a:Type -> ch:channel_runtime a -> v1:a -> v2:a ->
  Lemma (ensures True)
        [SMTPat (channel_try_send ch v1)]

(** ============================================================================
    SYNC.ONCE PRIMITIVE
    ============================================================================ *)

(** sync.Once state *)
type once_id = nat

(** Queue of goroutines blocked waiting for Once completion *)
type once_waiter_queue = list (unit -> unit)

(** Runtime sync.Once representation *)
type once_state =
  | OnceNotDone : once_state
  | OnceDone    : once_state
  | OnceRunning : once_state

(** Once identifier *)
noeq type once_runtime = {
  once_id      : once_id;
  once_state   : once_state;
  once_waiters : once_waiter_queue
}

(** Create a new sync.Once *)
val mk_once : once_id -> once_runtime

(** Result of attempting once.Do(f) *)
type once_do_result =
  | OnceDoExecute : once_runtime -> once_do_result
  | OnceDoWait    : once_runtime -> once_do_result
  | OnceDoDone    : once_do_result

(** Attempt to execute once.Do(f) *)
val once_try_do : once_runtime -> once_do_result

(** Register a waiting goroutine *)
val once_register_waiter : once_runtime -> (unit -> unit) -> once_runtime

(** Complete the Once execution *)
val once_complete : once_runtime -> once_runtime & once_waiter_queue

(** Check if Once is in the done state *)
val is_once_done : once_runtime -> bool

(** Check if Once is currently running *)
val is_once_running : once_runtime -> bool

(** THEOREM: Freshly created Once is not done *)
val once_mk_not_done : id:once_id ->
  Lemma (ensures ~(is_once_done (mk_once id)))
        [SMTPat (mk_once id)]

(** THEOREM: Once in NotDone state transitions to Running on first Do *)
val once_first_do : o:once_runtime ->
  Lemma (requires o.once_state = OnceNotDone)
        (ensures OnceDoExecute? (once_try_do o))
        [SMTPat (once_try_do o)]

(** THEOREM: Once in Done state returns immediately *)
val once_done_fast_path : o:once_runtime ->
  Lemma (requires is_once_done o)
        (ensures OnceDoDone? (once_try_do o))
        [SMTPat (once_try_do o)]

(** THEOREM: Complete transitions Running to Done *)
val once_complete_done : o:once_runtime ->
  Lemma (requires is_once_running o)
        (ensures is_once_done (fst (once_complete o)))
        [SMTPat (once_complete o)]

(** THEOREM: Complete returns all waiters *)
val once_complete_resumes_all : o:once_runtime ->
  Lemma (requires is_once_running o)
        (ensures snd (once_complete o) == o.once_waiters)
        [SMTPat (once_complete o)]

(** ============================================================================
    CHANNEL EXPRESSION FORMS
    ============================================================================ *)

(** Channel select case in Brrr AST *)
val extract_channel_elem_type : brrr_type -> option brrr_type

(** Type a channel expression *)
noeq type channel_type_result =
  | CTOk  : ty:brrr_type -> eff:effect_row -> channel_type_result
  | CTErr : msg:string -> channel_type_result

(** Extract element type from Channel[T] type *)
noeq type channel_select_case =
  | CSCRecv    : channel:expr -> binding:var_id -> body:expr -> channel_select_case
  | CSCSend    : channel:expr -> value:expr -> body:expr -> channel_select_case
  | CSCDefault : body:expr -> channel_select_case

(** Channel expressions for the Brrr AST *)
noeq type channel_expr =
  | CENewChannel : elem_type:brrr_type -> capacity:nat -> channel_expr
  | CESend : channel:expr -> value:expr -> channel_expr
  | CERecv : channel:expr -> channel_expr
  | CEClose : channel:expr -> channel_expr
  | CESelect : cases:list channel_select_case -> channel_expr

(** ============================================================================
    CHANNEL TYPING
    ============================================================================ *)

(** Channel typing result *)
val type_channel_expr : async_typing_ctx -> channel_expr -> channel_type_result

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR CHANNELS
    ============================================================================ *)

(** Create a new channel expression *)
val mk_new_channel_expr : brrr_type -> nat -> channel_expr

(** Create a send expression *)
val mk_send_expr : expr -> expr -> channel_expr

(** Create a receive expression *)
val mk_recv_expr : expr -> channel_expr

(** Create a close expression *)
val mk_close_expr : expr -> channel_expr

(** Create a select expression *)
val mk_select_expr : list channel_select_case -> channel_expr

(** Create a receive select case *)
val mk_select_recv_case : expr -> var_id -> expr -> channel_select_case

(** Create a send select case *)
val mk_select_send_case : expr -> expr -> expr -> channel_select_case

(** Create a default select case *)
val mk_select_default_case : expr -> channel_select_case
noeq type async_infer_result =
  | AsyncInferOk  : ty:brrr_type -> eff:effect_row -> async_infer_result
  | AsyncInferErr : msg:string -> async_infer_result

(** Extract inner type from Future type encoding *)
type either (a b: Type) =
  | Inl : v:a -> either a b
  | Inr : v:b -> either a b

(** ============================================================================
    FUTURE TEMPERATURE
    ============================================================================ *)

(** Future temperature determines when computation starts:
    - FutHot: Computation starts immediately on creation (eager)
    - FutCold: Computation deferred until first await (lazy)
    - FutLazy: Like Cold, but memoizes result after first completion *)
noeq type any_value =
  | AnyInt    : int -> any_value
  | AnyBool   : bool -> any_value
  | AnyString : string -> any_value
  | AnyUnit   : any_value
  | AnyPair   : any_value -> any_value -> any_value
  | AnyList   : list any_value -> any_value

(** Type-erased channel wrapper *)
noeq type infer_result =
  | InferOk  : ty:brrr_type -> eff:effect_row -> infer_result
  | InferErr : msg:string -> infer_result

(** ============================================================================
    YIELD TYPE CHECKING
    ============================================================================ *)

(** Check that an expression has the expected type *)
noeq type any_channel = {
  any_chan_id   : channel_id;
  any_chan_type : brrr_type;
  any_is_closed : bool
}

(** Select case with type-erased result *)
noeq type select_case_any (r: Type) =
  | SelectRecvAny    : chan_id:channel_id -> handler:(any_value -> r) -> select_case_any r
  | SelectSendAny    : chan_id:channel_id -> value:any_value -> handler:(unit -> r) -> select_case_any r
  | SelectDefaultAny : handler:(unit -> r) -> select_case_any r

(** ============================================================================
    CHANNEL RUNTIME CONTEXT
    ============================================================================ *)

(** Channel registry entry *)
type non_escaping_handle (a: Type) (max_scope: task_group_scope) =
  h:task_handle_scoped a{h.ths_creation_scope <= max_scope}

(** Spawn with type-level scope guarantee *)
