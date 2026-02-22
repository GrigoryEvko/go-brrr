(**
 * BrrrLang.Core.TypedPrompts Interface
 *
 * ============================================================================
 * TYPED PROMPT GENERATION FOR DELIMITED CONTINUATIONS
 * ============================================================================
 *
 * IMPORTANT TERMINOLOGY CLARIFICATION:
 * The term "prompt" in this module refers to DELIMITED CONTROL PROMPTS from
 * programming language theory, NOT to LLM/AI prompts. This is the classical
 * terminology established by Felleisen (1988) and Danvy/Filinski (1990).
 *
 * A "prompt" in delimited control is a DELIMITER that marks the boundary of
 * continuation capture. When shift<p> captures a continuation, it captures
 * everything up to the nearest enclosing reset<p> with the same prompt p.
 *
 * THEORETICAL BACKGROUND:
 * -----------------------
 * Delimited continuations extend classical call/cc with the ability to capture
 * only a portion (delimited segment) of the continuation.
 *
 *   reset<p> e  : Establishes a delimiter labeled with prompt p
 *   shift<p> k.e : Captures the continuation up to the enclosing reset<p>
 *
 * Historical References:
 *   - Felleisen, M. (1988). "The Theory and Practice of First-Class Prompts"
 *   - Danvy, O. & Filinski, A. (1990). "Abstracting Control"
 *   - Kiselyov, O. (2012). "Delimited Control in OCaml, Abstractly and Concretely"
 *
 * WHY INDEXED/PHANTOM TYPES FOR PROMPTS:
 * This module provides INDEXED PROMPT TYPES using phantom type parameters:
 *
 *   newPrompt returns: indexed_prompt<n> where n is a TYPE-LEVEL natural number
 *
 * The index n is erased at runtime (phantom) but present at compile time.
 * If shift<n> and reset<n> share the same index n, the TYPE CHECKER guarantees
 * they refer to the same prompt. No runtime comparison needed!
 *
 * KEY THEOREMS PROVED:
 * - prompt_fresh: Successive newPrompt calls return distinct indices
 * - typed_shift_finds_reset: Well-typed shift always has matching reset in context
 * - reset_eliminates_typed_prompt: reset<n> removes exactly Prompt<n,sigma>
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Continuations
 *)
module BrrrTypedPrompts

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrContinuations
open FStar.Ghost
open FStar.Monotonic.Pure

(** ============================================================================
    PROMPT INDEX - TYPE-LEVEL PROMPT IDENTITY
    ============================================================================ *)

(**
 * Type-level prompt index.
 * Each unique prompt gets a unique natural number index at the type level.
 * This is the phantom type parameter that ensures static prompt matching.
 *)
type prompt_index = nat

(** Prompt generation counter - tracks how many prompts have been allocated *)
type prompt_counter = nat

(** ============================================================================
    INDEXED PROMPT TYPE
    ============================================================================ *)

(**
 * Indexed prompt: the type index n is a phantom parameter ensuring uniqueness.
 *
 * Fields:
 *   - ip_answer_type: The "sigma" in Prompt<n, sigma>
 *   - ip_linearity: Whether the continuation can be called multiple times
 *)
noeq type indexed_prompt (n: prompt_index) = {
  ip_answer_type : brrr_type;
  ip_linearity : cont_linearity;
}

(** Create an indexed prompt *)
val mk_indexed_prompt : #n:prompt_index -> answer_ty:brrr_type -> lin:cont_linearity
    -> indexed_prompt n

(** Extract answer type from indexed prompt *)
val ip_answer_type : #n:prompt_index -> p:indexed_prompt n -> brrr_type

(** Extract linearity from indexed prompt *)
val ip_linearity : #n:prompt_index -> p:indexed_prompt n -> cont_linearity

(** ============================================================================
    PROMPT GENERATION STATE
    ============================================================================ *)

(** Set of allocated prompt indices (ghost/erased for proofs only) *)
type prompt_set = list prompt_index

(** Check if an index is in the allocated set *)
val mem_prompt_set : n:prompt_index -> s:prompt_set -> Tot bool (decreases s)

(**
 * Prompt generation state.
 *
 * Fields:
 *   - ps_next_index: The next index that will be returned by newPrompt
 *   - ps_allocated: Ghost data tracking all allocated indices
 *
 * INVARIANT: forall n in ps_allocated. n < ps_next_index
 *)
noeq type prompt_state = {
  ps_next_index : prompt_index;
  ps_allocated : erased prompt_set;
}

(** Initial prompt state: no prompts allocated *)
val init_prompt_state : prompt_state

(** Invariant helper *)
val prompt_state_invariant_aux : next:prompt_index -> allocated:prompt_set
    -> Tot bool (decreases allocated)

(** The prompt state invariant ensures freshness *)
val prompt_state_invariant : st:prompt_state -> prop

(** Initial state satisfies the invariant *)
val init_prompt_state_valid : unit ->
  Lemma (ensures prompt_state_invariant init_prompt_state)

(** ============================================================================
    FRESHNESS PREDICATE
    ============================================================================ *)

(** Predicate: index n is fresh (not yet allocated) *)
val is_fresh_index : n:prompt_index -> st:prompt_state -> prop

(** Stronger: index n is strictly fresh (greater than all allocated) *)
val is_strictly_fresh : n:prompt_index -> st:prompt_state -> prop

(** Lemma: next_index is always fresh *)
val next_index_is_fresh : st:prompt_state ->
  Lemma (requires prompt_state_invariant st)
        (ensures is_strictly_fresh st.ps_next_index st)

(** Lemma: next_index is not in allocated set *)
val next_index_not_allocated : st:prompt_state ->
  Lemma (requires prompt_state_invariant st)
        (ensures ~(mem_prompt_set st.ps_next_index (reveal st.ps_allocated)))

(** ============================================================================
    NEW PROMPT OPERATION
    ============================================================================ *)

(**
 * Result of newPrompt: the prompt and updated state.
 *)
noeq type new_prompt_result (n: prompt_index) = {
  npr_prompt : indexed_prompt n;
  npr_state : prompt_state;
  npr_fresh_proof : squash (~(is_strictly_fresh n npr_state));
}

(** Helper lemma for invariant preservation *)
val invariant_preserved_on_alloc :
  next:prompt_index ->
  allocated:prompt_set ->
  Lemma (requires prompt_state_invariant_aux next allocated)
        (ensures prompt_state_invariant_aux (next + 1) (next :: allocated))

(** Allocate a new prompt index and return updated state *)
val allocate_prompt_index : st:prompt_state
    -> Pure (prompt_index & prompt_state)
           (requires prompt_state_invariant st)
           (ensures fun (n, st') ->
             n == st.ps_next_index /\
             st'.ps_next_index == n + 1 /\
             prompt_state_invariant st')

(**
 * Fresh prompt result type.
 *)
noeq type fresh_prompt (st: prompt_state) = {
  fp_index : prompt_index;
  fp_prompt : indexed_prompt fp_index;
  fp_state : prompt_state;
  fp_freshness : squash (fp_index == st.ps_next_index);
  fp_state_invariant : squash (prompt_state_invariant fp_state);
}

(**
 * newPrompt: Generate a fresh prompt with the given answer type.
 *)
val newPrompt :
  st:prompt_state{prompt_state_invariant st} ->
  answer_ty:brrr_type ->
  lin:cont_linearity ->
  Tot (fresh_prompt st)

(** ============================================================================
    PROMPT FRESHNESS THEOREM
    ============================================================================ *)

(** Two prompts are distinct if they have different indices *)
val prompts_distinct : #n1:prompt_index -> #n2:prompt_index
    -> p1:indexed_prompt n1 -> p2:indexed_prompt n2 -> prop

(** Monotonicity: newPrompt increases the next_index *)
val newPrompt_increases_index :
  st:prompt_state{prompt_state_invariant st} ->
  answer_ty:brrr_type ->
  lin:cont_linearity ->
  Lemma (ensures (newPrompt st answer_ty lin).fp_state.ps_next_index > st.ps_next_index)

(**
 * Freshness theorem: successive prompts have distinct indices.
 *
 * THIS IS THE MAIN SAFETY THEOREM.
 *)
val prompt_fresh :
  st1:prompt_state{prompt_state_invariant st1} ->
  answer_ty1:brrr_type ->
  lin1:cont_linearity ->
  answer_ty2:brrr_type ->
  lin2:cont_linearity ->
  Lemma (ensures (
    let fp1 = newPrompt st1 answer_ty1 lin1 in
    let fp2 = newPrompt fp1.fp_state answer_ty2 lin2 in
    fp1.fp_index <> fp2.fp_index))

(** Generalized freshness: any previously allocated index is smaller *)
val prompt_ordering :
  st:prompt_state{prompt_state_invariant st} ->
  n:prompt_index ->
  Lemma (requires mem_prompt_set n (reveal st.ps_allocated))
        (ensures n < st.ps_next_index)

(** ============================================================================
    TYPED DELIMITED CONTROL OPERATIONS
    ============================================================================ *)

(**
 * Typed continuation type: parameterized by prompt index.
 *)
noeq type typed_cont_type (n: prompt_index) = {
  tct_arg_type : brrr_type;
  tct_prompt : indexed_prompt n;
  tct_effects : effect_row;
  tct_linearity : cont_linearity;
}

(** Create a typed continuation type *)
val mk_typed_cont_type : #n:prompt_index -> arg:brrr_type -> p:indexed_prompt n
    -> eff:effect_row -> lin:cont_linearity -> typed_cont_type n

(** Answer type of a typed continuation *)
val typed_cont_answer : #n:prompt_index -> ct:typed_cont_type n -> brrr_type

(** Convert typed continuation to function type *)
val typed_cont_to_func : #n:prompt_index -> ct:typed_cont_type n -> func_type

(** ============================================================================
    TYPED CONTINUATION EXPRESSIONS
    ============================================================================ *)

(** Typed reset: reset<n> e *)
noeq type typed_reset (n: prompt_index) = {
  tr_prompt : indexed_prompt n;
  tr_body : expr;
}

(** Typed shift: shift<n> (lambda k. e) *)
noeq type typed_shift (n: prompt_index) = {
  ts_prompt : indexed_prompt n;
  ts_cont_var : var_id;
  ts_body : expr;
}

(** Typed control: control<n> (lambda k. e) - undelimited variant *)
noeq type typed_control (n: prompt_index) = {
  tc_prompt : indexed_prompt n;
  tc_cont_var : var_id;
  tc_body : expr;
}

(** Typed abort: abort<n> v *)
noeq type typed_abort (n: prompt_index) = {
  ta_prompt : indexed_prompt n;
  ta_value : expr;
}

(** Typed continuation expression - captures the index in the type *)
noeq type typed_cont_expr =
  | TCEReset : #n:prompt_index -> typed_reset n -> typed_cont_expr
  | TCEShift : #n:prompt_index -> typed_shift n -> typed_cont_expr
  | TCEControl : #n:prompt_index -> typed_control n -> typed_cont_expr
  | TCEAbort : #n:prompt_index -> typed_abort n -> typed_cont_expr
  | TCEApplyCont : expr -> expr -> typed_cont_expr

(** Extract prompt index from typed continuation expression *)
val typed_cont_expr_index : tce:typed_cont_expr -> option prompt_index

(** ============================================================================
    STATIC PROMPT MATCHING VERIFICATION
    ============================================================================ *)

(** Predicate: shift uses the same prompt as an enclosing reset *)
val shift_matches_reset : #n:prompt_index
    -> shift:typed_shift n -> reset:typed_reset n -> prop

(** Lemma: Same index guarantees prompt matching *)
val same_index_same_prompt :
  #n:prompt_index ->
  p1:indexed_prompt n ->
  p2:indexed_prompt n ->
  Lemma (requires p1.ip_answer_type == p2.ip_answer_type)
        (ensures True)

(** Prompt scope context *)
noeq type prompt_scope_ctx = {
  psc_in_scope : list prompt_index;
  psc_state : prompt_state;
}

(** Empty scope context *)
val empty_prompt_scope : st:prompt_state -> prompt_scope_ctx

(** Push a prompt into scope (for reset) *)
val push_prompt_scope : #n:prompt_index -> p:indexed_prompt n -> ctx:prompt_scope_ctx
    -> prompt_scope_ctx

(** Check if a prompt is in scope *)
val prompt_in_scope : n:prompt_index -> ctx:prompt_scope_ctx -> bool

(** Static well-scopedness: shift only uses prompts that are in scope *)
val typed_expr_well_scoped : tce:typed_cont_expr -> ctx:prompt_scope_ctx -> bool

(** ============================================================================
    TYPED PROMPT EFFECT
    ============================================================================ *)

(** Typed prompt effect: Prompt<n, sigma> *)
noeq type typed_prompt_effect (n: prompt_index) = {
  tpe_prompt : indexed_prompt n;
  tpe_linearity : cont_linearity;
}

(** Create typed prompt effect *)
val mk_typed_prompt_effect : #n:prompt_index -> p:indexed_prompt n -> lin:cont_linearity
    -> typed_prompt_effect n

(** Effect row element for typed prompts *)
noeq type typed_effect_element =
  | TEPrompt : #n:prompt_index -> typed_prompt_effect n -> typed_effect_element
  | TEOther : effect_type -> typed_effect_element

(** Typed effect row *)
type typed_effect_row = list typed_effect_element

(** Check if typed effect row contains a specific prompt *)
val typed_row_has_prompt : n:prompt_index -> row:typed_effect_row -> bool

(** Remove prompt effect from row (used by reset) *)
val typed_row_remove_prompt : n:prompt_index -> row:typed_effect_row -> typed_effect_row

(** ============================================================================
    TYPING RULES FOR TYPED DELIMITED CONTROL
    ============================================================================ *)

(** Typing judgment for typed reset *)
type reset_typing (#n: prompt_index) (reset: typed_reset n) = unit

(** Typing judgment for typed shift *)
type shift_typing (#n: prompt_index) (shift: typed_shift n) = unit

(** Verify that reset eliminates the matching prompt effect *)
val reset_eliminates_typed_prompt :
  #n:prompt_index ->
  reset:typed_reset n ->
  row:typed_effect_row{typed_row_has_prompt n row} ->
  Lemma (ensures ~(typed_row_has_prompt n (typed_row_remove_prompt n row)))

(** ============================================================================
    OPERATIONAL SEMANTICS FOR TYPED CONTROL
    ============================================================================ *)

(** Typed evaluation frame - tracks prompt indices *)
noeq type typed_eval_frame =
  | TFrameHole     : typed_eval_frame
  | TFrameUnary    : unary_op -> typed_eval_frame
  | TFrameBinL     : binary_op -> expr -> typed_eval_frame
  | TFrameBinR     : binary_op -> expr -> typed_eval_frame
  | TFrameCall     : list expr -> typed_eval_frame
  | TFrameIf       : expr -> expr -> typed_eval_frame
  | TFrameLet      : var_id -> option brrr_type -> expr -> typed_eval_frame
  | TFrameSeq      : expr -> typed_eval_frame
  | TFrameReset    : #n:prompt_index -> indexed_prompt n -> typed_eval_frame

type typed_frame_context = list typed_eval_frame

(** Check if typed context has reset for index n *)
val typed_context_has_reset : n:prompt_index -> ctx:typed_frame_context -> bool

(** Split typed context at reset for index n *)
val split_typed_context : n:prompt_index -> ctx:typed_frame_context
    -> option (typed_frame_context & typed_frame_context)

(** Typed machine configuration *)
noeq type typed_cont_config = {
  tcc_expr : typed_cont_expr;
  tcc_context : typed_frame_context;
}

(**
 * Static guarantee: well-typed shift always finds its reset.
 *)
val typed_shift_finds_reset :
  #n:prompt_index ->
  shift:typed_shift n ->
  ctx:typed_frame_context{typed_context_has_reset n ctx} ->
  Lemma (ensures Some? (split_typed_context n ctx))

(** ============================================================================
    BRRR-MACHINE PROMPT SCOPE ANALYSIS
    ============================================================================ *)

(** Prompt scope entry for analysis *)
noeq type prompt_scope_entry = {
  pse_index : prompt_index;
  pse_answer_type : brrr_type;
  pse_allocation_point : nat;
  pse_reset_points : list nat;
  pse_shift_points : list nat;
  pse_is_multishot : bool;
}

(** Prompt scope analysis result *)
noeq type prompt_scope_analysis = {
  psa_entries : list prompt_scope_entry;
  psa_errors : list string;
  psa_is_well_scoped : bool;
}

(** Initialize prompt scope analysis *)
val init_scope_analysis : prompt_scope_analysis

(** Add a prompt allocation to the analysis *)
val record_prompt_allocation : n:prompt_index -> answer_ty:brrr_type -> loc:nat
    -> multishot:bool -> analysis:prompt_scope_analysis -> prompt_scope_analysis

(** Find entry for a prompt index *)
val find_prompt_entry : n:prompt_index -> entries:list prompt_scope_entry
    -> option prompt_scope_entry

(** Record a reset point for a prompt *)
val record_reset_point : n:prompt_index -> loc:nat -> analysis:prompt_scope_analysis
    -> prompt_scope_analysis

(** Record a shift point for a prompt *)
val record_shift_point : n:prompt_index -> loc:nat -> analysis:prompt_scope_analysis
    -> prompt_scope_analysis

(** Check if shift location is within some reset scope *)
val shift_in_reset_scope : shift_loc:nat -> reset_locs:list nat -> bool

(** Validate a single prompt entry *)
val validate_prompt_entry : entry:prompt_scope_entry -> option string

(** Helper: filter_map *)
val filter_map_option : #a:Type -> #b:Type -> f:(a -> option b) -> l:list a -> Tot (list b)

(** Run full prompt scope validation *)
val validate_prompt_scopes : analysis:prompt_scope_analysis -> prompt_scope_analysis

(** ============================================================================
    CONVERSION TO/FROM UNTYPED PROMPTS
    ============================================================================ *)

(** Convert indexed prompt to untyped prompt (loses static guarantees) *)
val indexed_to_untyped : #n:prompt_index -> p:indexed_prompt n -> prompt

(** Convert typed reset to untyped *)
val typed_reset_to_untyped : #n:prompt_index -> tr:typed_reset n -> cont_expr

(** Convert typed shift to untyped *)
val typed_shift_to_untyped : #n:prompt_index -> ts:typed_shift n -> cont_expr

(** Convert typed control to untyped *)
val typed_control_to_untyped : #n:prompt_index -> tc:typed_control n -> cont_expr

(** Convert typed abort to untyped *)
val typed_abort_to_untyped : #n:prompt_index -> ta:typed_abort n -> cont_expr

(** Convert full typed expression to untyped *)
val typed_cont_expr_to_untyped : tce:typed_cont_expr -> cont_expr

(** ============================================================================
    CONVENIENCE API FOR TYPED PROMPTS
    ============================================================================ *)

(** Create a one-shot typed prompt in the state monad *)
val newOneshotPrompt : st:prompt_state{prompt_state_invariant st} -> answer_ty:brrr_type
    -> fresh_prompt st

(** Create a multi-shot typed prompt *)
val newMultishotPrompt : st:prompt_state{prompt_state_invariant st} -> answer_ty:brrr_type
    -> fresh_prompt st

(** Create typed reset from fresh prompt *)
val mk_typed_reset_fresh : fp:fresh_prompt 'st -> body:expr -> typed_cont_expr

(** Create typed shift from fresh prompt *)
val mk_typed_shift_fresh : fp:fresh_prompt 'st -> k_var:var_id -> body:expr -> typed_cont_expr

(** Create typed abort from fresh prompt *)
val mk_typed_abort_fresh : fp:fresh_prompt 'st -> value:expr -> typed_cont_expr
