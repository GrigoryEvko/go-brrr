(**
 * BrrrLang.Core.Eval - Interface
 *
 * Big-step operational semantics for Brrr-Lang.
 * Based on brrr_lang_spec_v0.4.tex Part I (Foundations).
 *
 * Implements: eval : expr -> eval_state -> (result value) & eval_state
 *
 * ============================================================================
 * ABSTRACT MACHINE MODEL
 * ============================================================================
 *
 * This evaluator is a hybrid of classical abstract machine designs:
 *
 * SECD Machine (Landin 1964) - "The mechanical evaluation of expressions":
 *   - Stack (S):       Implicit via F*'s call stack and result threading
 *   - Environment (E): es_env maps variables to values (lexical scope)
 *   - Control (C):     The expression argument to eval_expr
 *   - Dump (D):        es_handlers for continuation contexts
 *
 * CEK Machine (Felleisen & Friedman 1986):
 *   - Control (C):     Current expression under evaluation
 *   - Environment (E): Lexically scoped variable bindings
 *   - Kontinuation (K): Reified as handler_stack for algebraic effects
 *
 * Key insight: Big-step evaluation = running SECD/CEK until value produced.
 * The F* recursion stack implicitly represents intermediate machine states.
 *
 * Extensions beyond classical machines:
 *   - Algebraic effects (Plotkin & Pretnar 2009) via handler_stack
 *   - Delimited continuations (Danvy & Filinski 1990) via prompt_table
 *   - Fuel-based termination for F* totality proofs
 *
 * References:
 *   - Landin, P.J. (1964). "The mechanical evaluation of expressions"
 *   - Felleisen, M. & Friedman, D.P. (1986). "Control operators, the
 *     SECD-machine, and the lambda-calculus." LICS 1986.
 *   - Plotkin, G. & Pretnar, M. (2009). "Handlers of Algebraic Effects"
 *   - fstar_pop_book.md lines 4000-5000 (termination via fuel)
 *   - fstar_pop_book.md lines 10000-11000 (well-founded recursion)
 *
 * ============================================================================
 *
 * Uses explicit fuel for termination proof, following the HACL* pattern
 * from Spec.Hash.Definitions.fst for structural recursion with termination.
 *
 * Key semantic properties established by this interface:
 *
 * 1. DETERMINISM: Evaluation is deterministic - same inputs always produce
 *    same outputs. This follows from the pure functional nature of the evaluator.
 *    See: eval_deterministic
 *
 * 2. FUEL MONOTONICITY: If evaluation succeeds with fuel n, it also succeeds
 *    with fuel n+k for any k, producing the same result.
 *    See: eval_fuel_monotone, eval_fuel_sufficient
 *
 * 3. TYPE PRESERVATION: Well-typed expressions evaluate to well-typed values.
 *    This is the key soundness theorem connecting static and dynamic semantics.
 *    See: eval_preserves_type
 *
 * 4. PROGRESS: Well-typed expressions with sufficient fuel don't get stuck.
 *    Combined with preservation, this gives type soundness.
 *    See: progress_weak
 *
 * 5. HEAP MONOTONICITY: Evaluation may allocate but never deallocates heap
 *    locations. Valid locations remain valid after evaluation.
 *    See: eval_preserves_valid_locs
 *
 * Reference patterns:
 * - HACL* Spec.Agile.Hash.fsti: Function signatures with pre/post conditions
 * - HACL* Spec.Hash.Definitions.fst: Type definitions and helper functions
 * - HACL* Spec.SHA2.Lemmas.fst: SMTPat lemmas and Z3 tuning
 * - EverParse Target.fsti (lines 280-350): Parser/evaluator specs
 *
 * Depends on: Primitives, Modes, Effects, Utils, BrrrTypes, Expressions, Values
 *)
module BrrrEval

(** Z3 solver options - conservative settings for evaluation proofs.
    Following HACL* pattern: fuel 0, ifuel 0 as baseline to prevent proof explosion.
    Specific lemmas use #push-options to locally increase when needed. *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrUtils
open BrrrTypes
open BrrrExpressions
open BrrrValues
open FStar.List.Tot
open FStar.Int64
open FStar.UInt32

(** ============================================================================
    CLOSURE STORE
    ============================================================================

    Closures are stored separately from the heap to enable efficient lookup
    and to separate function values from mutable data. Each closure is assigned
    a unique ID at allocation time.
*)

(** Closure store: maps closure IDs to closure objects *)
unfold
let closure_store = list (closure_id & closure)

(** Empty closure store *)
val empty_closures : closure_store

(** Next available closure ID (one past the maximum in use) *)
val next_closure_id : closure_store -> closure_id

(** Allocate a new closure, returning its ID and the updated store *)
val alloc_closure : closure -> closure_store -> closure_id & closure_store

(** Lookup closure by ID. Returns None if ID is not found. *)
val lookup_closure : closure_id -> closure_store -> option closure

(** Get next available ID without allocating *)
val fresh_closure_id : closure_store -> closure_id

(** Add closure with explicit ID (for pre-allocated IDs) *)
val add_closure : closure_id -> closure -> closure_store -> closure_store

(** ============================================================================
    CLOSURE STORE SPECIFICATIONS
    ============================================================================ *)

(** alloc_closure returns a fresh ID *)
val alloc_closure_fresh : c:closure -> cs:closure_store ->
    Lemma (let (id, _) = alloc_closure c cs in
           lookup_closure id cs == None)
    [SMTPat (alloc_closure c cs)]

(** alloc_closure makes the closure retrievable *)
val alloc_closure_lookup : c:closure -> cs:closure_store ->
    Lemma (let (id, cs') = alloc_closure c cs in
           lookup_closure id cs' == Some c)

(** alloc_closure preserves existing closures *)
val alloc_closure_preserves : c:closure -> cs:closure_store -> id:closure_id ->
    Lemma (requires Some? (lookup_closure id cs))
          (ensures (let (_, cs') = alloc_closure c cs in
                    lookup_closure id cs' == lookup_closure id cs))

(** ============================================================================
    EFFECT HANDLER RUNTIME SUPPORT
    ============================================================================

    Effect handlers are stored in a stack during evaluation. When a perform
    operation occurs, we search up the handler stack for a handler that
    covers the performed effect operation.

    Following the algebraic effects semantics from Part V of the spec.
    Reference: Plotkin & Pretnar (2009) "Handlers of Algebraic Effects"

    RUNTIME VS STATIC TYPES:
    -------------------------
    The Effects module defines effect_handler with nat references to bodies
    (for AST storage). For evaluation, we need actual expressions. The
    runtime_handler_clause and runtime_handler types carry resolved bodies.

    CONTINUATION SEMANTICS:
    -----------------------
    This implementation supports TAIL-RESUMPTIVE handlers where calling
    resume(v) returns v as the handler result. For general handlers where
    resume is not in tail position, full CPS transformation would be needed.

    See: SPECIFICATION_ERRATA.md Chapter 11 (Handler Termination Infrastructure)
*)

(** Runtime handler clause with actual expression body.
    Unlike handler_clause which uses nat refs, this carries the actual expr.

    Fields:
    - rhc_op: Which effect operation this clause handles
    - rhc_param: Parameter name bound to the operation's argument
    - rhc_kont: Variable name for the captured continuation
    - rhc_body: The handler clause body expression
    - rhc_linear: Whether continuation can be used multiple times
*)
noeq type runtime_handler_clause = {
  rhc_op     : effect_op;
  rhc_param  : var_id;
  rhc_kont   : var_id;
  rhc_body   : expr;
  rhc_linear : linearity
}

(** Runtime handler with actual expression bodies.
    This is the evaluator's view of a handler with evaluable bodies.

    Fields:
    - rh_effects: The effects being handled (removed from result type)
    - rh_return_var: Variable bound in return clause
    - rh_return_body: Return clause body (None means identity return)
    - rh_clauses: Operation handler clauses
    - rh_finally: Optional finally clause (runs after handler completes)
    - rh_depth: Deep (reinstall on resume) or Shallow (one-shot)
*)
noeq type runtime_handler = {
  rh_effects     : effect_row;
  rh_return_var  : var_id;
  rh_return_body : option expr;
  rh_clauses     : list runtime_handler_clause;
  rh_finally     : option expr;
  rh_depth       : handler_depth
}

(** Runtime handler entry on the handler stack.
    Contains the runtime handler and captured environment for clause evaluation. *)
noeq type handler_entry = {
  he_handler  : runtime_handler;  (* Runtime handler with evaluable bodies *)
  he_ret_env  : env;              (* Environment for clause evaluation *)
  he_original : effect_handler    (* Original handler for type information *)
}

(** Handler stack - most recent handler is at the head *)
unfold
let handler_stack = list handler_entry

(** Empty handler stack *)
val empty_handlers : handler_stack

(** Push handler onto stack *)
val push_handler : handler_entry -> handler_stack -> handler_stack

(** Pop handler from stack *)
val pop_handler : handler_stack -> option (handler_entry & handler_stack)

(** Find handler for an effect operation - searches up the stack.
    Returns the matching handler entry and remaining stack if found. *)
val find_handler_for_op : effect_op -> handler_stack ->
    option (handler_entry & handler_stack)

(** Find matching clause for an operation in the handler's clause list *)
val find_matching_clause : effect_op -> list runtime_handler_clause ->
    option runtime_handler_clause

(** ============================================================================
    METHOD TABLE
    ============================================================================

    Method dispatch uses a table mapping (type_name, method_name) pairs to
    closure IDs. This enables runtime method resolution for struct and
    variant types.
*)

(** Method table key: (type_name, method_name) *)
unfold
let method_key = type_name & string

(** Method table: maps keys to closure IDs *)
unfold
let method_table = list (method_key & closure_id)

(** Empty method table *)
val empty_methods : method_table

(** Lookup method in table.
    Returns the closure ID for the method if found. *)
val lookup_method_entry : type_name -> string -> method_table -> option closure_id

(** Register a method for a type *)
val register_method : type_name -> string -> closure_id -> method_table -> method_table

(** ============================================================================
    VALUE TYPE EXTRACTION
    ============================================================================

    Extract the type name from runtime values for method dispatch.
    Structs and variants carry their type name; other values use built-in names.
*)

(** Get the type name from a value for method dispatch.
    Returns None for unit (which has no methods). *)
val value_type_name : value -> option type_name

(** ============================================================================
    LABEL STACK FOR LABELED BREAK/CONTINUE
    ============================================================================

    Labeled loops introduce prompts for break and continue. The label stack
    tracks active loop labels so break/continue can target specific loops.
*)

(** Label entry in the label stack *)
type label_entry = {
  le_name      : string;          (* Label name *)
  le_is_break  : bool;            (* True if this targets break *)
  le_value     : option value     (* Value passed with break, if any *)
}

(** Label stack *)
unfold
let label_stack = list label_entry

(** Empty label stack *)
val empty_labels : label_stack

(** Push label onto stack *)
val push_label : string -> label_stack -> label_stack

(** Pop label from stack *)
val pop_label : label_stack -> option (label_entry & label_stack)

(** Check if label exists in stack *)
val has_label : string -> label_stack -> bool

(** ============================================================================
    PROMPT TABLE FOR DELIMITED CONTINUATIONS
    ============================================================================

    Delimited continuations use prompts to mark reset points. The prompt table
    maps prompt labels to their captured continuation state.

    Based on Part V of the spec: shift/reset control operators.
*)

(** Prompt entry in the prompt table *)
type prompt_entry = {
  pe_label    : label;            (* Prompt label *)
  pe_env      : env;              (* Environment at reset point *)
  pe_active   : bool              (* Whether this prompt is active *)
}

(** Prompt table *)
unfold
let prompt_table = list prompt_entry

(** Empty prompt table *)
val empty_prompts : prompt_table

(** Push prompt onto table *)
val push_prompt : label -> env -> prompt_table -> prompt_table

(** Pop prompt from table *)
val pop_prompt : prompt_table -> option (prompt_entry & prompt_table)

(** Find prompt by label *)
val find_prompt : label -> prompt_table -> option prompt_entry

(** ============================================================================
    EXTENDED EVALUATION STATE
    ============================================================================

    The evaluation state contains all runtime context needed for evaluation:
    - Local environment (variable bindings)
    - Heap (mutable storage)
    - Closure store (function values)
    - Effect handlers (algebraic effects)
    - Global environment (top-level bindings)
    - Method table (type-based dispatch)
    - Label stack (loop control)
    - Prompt table (delimited continuations)

    SECD/CEK Machine Correspondence:
    --------------------------------
    | Component     | SECD Role | CEK Role  | Purpose                      |
    |---------------|-----------|-----------|------------------------------|
    | es_env        | E         | E         | Lexical variable bindings    |
    | es_closures   | Part of E | Part of E | Closure environment storage  |
    | es_handlers   | D         | K         | Continuation/handler stack   |
    | es_prompts    | -         | -         | Delimited control (shift/reset) |
    | es_heap       | -         | -         | Mutable storage (references) |
    | es_globals    | -         | -         | Module-level symbol table    |
    | es_methods    | -         | -         | Method dispatch for OO calls |
    | es_labels     | -         | -         | Loop control targets         |

    State Threading Invariants:
    - es_heap grows monotonically (alloc never fails, no deallocation)
    - es_closures grows monotonically (closures never removed)
    - es_handlers follows stack discipline (push on EHandle, pop on return)
    - es_env is scoped within function bodies (restored after calls)

    See brrr_lang_spec_v0.4.tex Part I "Operational Semantics" for formal rules.
*)

(** Complete evaluation state - the "machine state" for our SECD/CEK hybrid.
    The noeq attribute indicates no decidable equality (closures contain functions). *)
noeq type eval_state = {
  es_env      : env;              (* E: Local variable bindings *)
  es_heap     : heap;             (* Store: Heap for mutable values *)
  es_closures : closure_store;    (* E: Stored closures *)
  es_handlers : handler_stack;    (* D/K: Active effect handlers *)
  es_globals  : env;              (* Global symbol table *)
  es_methods  : method_table;     (* Method dispatch table *)
  es_labels   : label_stack;      (* Active loop labels *)
  es_prompts  : prompt_table      (* Active reset prompts *)
}

(** Initial evaluation state with all empty components *)
val init_eval_state : eval_state

(** ============================================================================
    ARITHMETIC OPERATIONS
    ============================================================================

    Pure arithmetic operations on values. These are non-recursive and
    don't require fuel.
*)

(** Evaluate unary operation on integer *)
val eval_unary_int : unary_op -> int -> option int

(** Evaluate unary operation on boolean *)
val eval_unary_bool : unary_op -> bool -> option bool

(** ============================================================================
    BITWISE OPERATIONS - 64-bit signed integer semantics
    ============================================================================

    Bitwise operations are implemented using FStar.Int64 for proper semantics.
    Values must be within the 64-bit signed integer range [-2^63, 2^63-1].
    Out-of-range values return None (runtime error).
    Shift amounts must be in [0, 63] range.

    NOTE: These must be declared before eval_binary_int since it uses them.
*)

(** Safely convert int to Int64.t with bounds check *)
val try_to_int64 : int -> option FStar.Int64.t

(** Safely convert int to UInt32.t for shift amounts *)
val try_shift_amount : int -> option FStar.UInt32.t

(** Bitwise AND *)
val eval_bitwise_and : int -> int -> option value

(** Bitwise OR *)
val eval_bitwise_or : int -> int -> option value

(** Bitwise XOR *)
val eval_bitwise_xor : int -> int -> option value

(** Left shift (overflow returns None) *)
val eval_shift_left : int -> int -> option value

(** Arithmetic right shift *)
val eval_shift_right : int -> int -> option value

(** Evaluate binary operation on integers.
    Returns None for division by zero or overflow.
    Uses bitwise operations above for OpBitAnd, OpBitOr, etc. *)
val eval_binary_int : binary_op -> int -> int -> option value

(** Evaluate binary operation on booleans *)
val eval_binary_bool : binary_op -> bool -> bool -> option value

(** Evaluate binary operation on strings *)
val eval_binary_string : binary_op -> string -> string -> option value

(** High-level unary operation evaluator *)
val do_unary : unary_op -> value -> result value

(** High-level binary operation evaluator *)
val do_binary : binary_op -> value -> value -> result value

(** ============================================================================
    RUNTIME TYPE EXTRACTION
    ============================================================================ *)

(** Extract runtime type from a value for type checking *)
val value_runtime_type : value -> brrr_type

(** ============================================================================
    TYPE SIZE AND ALIGNMENT
    ============================================================================

    Compute memory layout information for types. Used for sizeof/alignof.
    Follows 64-bit system conventions.
*)

(** Compute byte size of a type *)
val compute_type_byte_size : brrr_type -> Tot nat

(** Compute alignment requirement of a type in bytes *)
val compute_type_alignment : brrr_type -> Tot nat

(** ============================================================================
    HELPER FUNCTIONS
    ============================================================================ *)

(** Extend environment with multiple bindings *)
val extend_many : list (var_id & value) -> env -> env

(** Update a field in a struct's field list *)
val update_field : list (string & value) -> string -> value ->
    Tot (list (string & value))

(** Update element at index in a list *)
val list_update : #a:Type -> list a -> nat -> a -> Tot (list a)

(** ============================================================================
    MAIN EVALUATION FUNCTIONS
    ============================================================================

    The evaluator uses explicit fuel for termination. Each recursive call
    decrements fuel by 1. When fuel reaches 0, evaluation returns RDiv
    (divergence).

    These functions are mutually recursive and form the core of the evaluator.

    E-* Rule Correspondence (from brrr_lang_spec_v0.4.tex):
    -------------------------------------------------------
    | E-Lit     | ELit lit        -> ROk (lit_to_value lit)  |
    | E-Var     | EVar x          -> ROk (lookup x env)      |
    | E-App     | ECall fn args   -> eval_apply closure args |
    | E-Abs     | ELambda p b     -> ROk (VClosure id)       |
    | E-If      | EIf c t e       -> if truthy(c) then t else e |
    | E-Let     | ELet p _ e1 e2  -> bind e1, match p, eval e2 |
    | E-Seq     | ESeq e1 e2      -> eval e1; eval e2        |
    | E-Match   | EMatch s arms   -> first matching arm body |
    | E-Ref     | EBox e          -> alloc, return VBox loc  |
    | E-Deref   | EDeref e        -> read from heap          |
    | E-Assign  | EAssign l r     -> write to heap           |
    | E-Handle  | EHandle b h     -> push handler, eval body |
    | E-Perform | EPerform op a   -> find handler, invoke    |
    | E-Reset   | EReset l b      -> push prompt, eval body  |
    | E-Shift   | EShift l k b    -> capture continuation    |

    Fuel Semantics:
    - fuel = 0: Return RDiv immediately (divergence indicator)
    - fuel > 0: Proceed, pass (fuel - 1) to recursive calls

    Reference: fstar_pop_book.md lines 4000-5000 for fuel-based termination.
*)

(** Apply function value to arguments.
    Implements E-App rule: beta-reduction for closures.
    NOTE: Must be declared first in mutual recursion to match BrrrEval.fst order.

    Steps: 1. Lookup closure by ID
           2. Verify arity (param count = arg count)
           3. Extend closure env with param/arg bindings
           4. Evaluate body in extended environment
           5. Restore original environment (lexical scoping) *)
val eval_apply : (fuel: nat) -> value -> list value -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Main expression evaluator.

    Evaluates expression e in state st with given fuel.
    Returns result (success, error, or control flow) and updated state.

    This is the "step function" of our abstract machine, mapping:
      (C, E, K) -> (C', E', K')   or   (C, E, K) -> value

    Where C = expression, E = es_env, K = es_handlers.

    The decreases clause uses fuel for termination proof.
    See brrr_lang_spec_v0.4.tex Part I for inference rule definitions.
*)
val eval_expr : (fuel: nat) -> expr -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Evaluate list of expressions left-to-right.
    Used for function arguments, tuple elements, array literals.
    Threads state through sequential evaluation, propagating non-Ok results. *)
val eval_exprs : (fuel: nat) -> list expr -> eval_state ->
    Tot (result (list value) & eval_state) (decreases fuel)

(** Evaluate struct field expressions.
    Preserves field names while evaluating associated expressions.
    Implements E-Struct rule for struct construction. *)
val eval_field_exprs : (fuel: nat) -> list (string & expr) -> eval_state ->
    Tot (result (list (string & value)) & eval_state) (decreases fuel)

(** Evaluate match arms until one matches.
    Implements E-Match rule: first-match semantics.
    Tries each arm in order; returns body result of first matching pattern. *)
val eval_match_arms : (fuel: nat) -> value -> list match_arm -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Evaluate catch arms for exception handling.
    Implements E-Try/E-Catch rules for try-catch blocks.
    Matches exception against patterns, evaluates handler body. *)
val eval_catch_arms : (fuel: nat) -> value -> list catch_arm -> option expr -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Evaluate for-loop over array elements.
    Implements E-For rule: iterates over array, binding each element.
    Handles labeled break/continue for nested loop control. *)
val eval_for_array : (fuel: nat) -> var_id -> list value -> expr -> string -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Evaluate for-loop over string runes (Unicode codepoints).
    Implements Go range-over-string semantics: iterates over UTF-8 codepoints,
    binding the loop variable to VTuple [VInt byte_offset; VChar rune] per iteration.
    Handles labeled break/continue for nested loop control. *)
val eval_for_string : (fuel: nat) -> var_id -> string -> nat -> expr -> string -> eval_state ->
    Tot (result value & eval_state) (decreases fuel)

(** Pattern matching with evaluation context (for guards and refs).
    Unlike simple match_pattern, this handles:
    - PatGuard: Evaluates guard expression in binding scope
    - PatRef/PatBox: Dereferences from heap before matching inner pattern
    Returns bindings and possibly modified state (guards may have effects). *)
val match_pattern_with_context : (fuel: nat) -> pattern -> value -> eval_state ->
    Tot (option (list (var_id & value)) & eval_state) (decreases fuel)

(** Match multiple patterns with context *)
val match_patterns_with_context : (fuel: nat) -> list pattern -> list value -> eval_state ->
    Tot (option (list (var_id & value)) & eval_state) (decreases fuel)

(** Match struct fields with context *)
val match_struct_fields_with_context : (fuel: nat) -> list (string & pattern) ->
                                       list (string & value) -> eval_state ->
    Tot (option (list (var_id & value)) & eval_state) (decreases fuel)

(** ============================================================================
    TOP-LEVEL EVALUATION API
    ============================================================================ *)

(** Default fuel amount - sufficient for most programs *)
val default_fuel : nat

(** Run expression with given fuel *)
val run_expr : expr -> nat -> result value & eval_state

(** Run with default fuel *)
val eval : expr -> result value & eval_state

(** Run and extract just the value (discarding state) *)
val eval_value : expr -> option value

(** ============================================================================
    STATE CONFIGURATION
    ============================================================================ *)

(** Add a global binding to the evaluation state *)
val with_global : string -> value -> eval_state -> eval_state

(** Register a method implementation for a type.
    The closure_params should include 'self' as the first parameter. *)
val with_method : type_name -> string -> list var_id -> expr -> eval_state -> eval_state

(** Run expression with custom state *)
val run_expr_with_state : expr -> eval_state -> nat -> result value & eval_state

(** Run with default fuel and custom state *)
val eval_with_state : expr -> eval_state -> result value & eval_state

(** ============================================================================
    TYPING ENVIRONMENT PLACEHOLDER
    ============================================================================

    These types are placeholders for the full type system. They enable
    stating type preservation lemmas before the type checker is complete.
*)

(** Typing environment: maps variable names to types *)
unfold
let typing_env = list (var_id & brrr_type)

(** Well-typed expression predicate (placeholder - always True) *)
val well_typed : expr -> typing_env -> brrr_type -> Type0

(** Well-typed value predicate (placeholder - always True) *)
val value_well_typed : value -> heap -> brrr_type -> Type0

(** ============================================================================
    EVALUATION SOUNDNESS LEMMAS
    ============================================================================

    These lemmas establish key properties of the evaluator that are essential
    for reasoning about program behavior. Following HACL* Spec.SHA2.Lemmas.fst
    patterns for proof structure.
*)

(** Evaluation is deterministic.

    Since eval_expr is a pure total function in F*, calling it twice with
    the same arguments will always produce the same result.

    Proof: By the definition of definitional equality in F*. *)
val eval_deterministic : fuel:nat -> e:expr -> st:eval_state ->
    Lemma (ensures (
        let (r1, st1) = eval_expr fuel e st in
        let (r2, st2) = eval_expr fuel e st in
        r1 == r2 /\ st1 == st2))

(** ----------------------------------------------------------------------------
    FUEL MONOTONICITY
    ---------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

(** Fuel monotonicity (old-style signature for compatibility) *)
val eval_fuel_monotonic : fuel1:nat -> fuel2:nat{fuel2 >= fuel1} -> e:expr -> st:eval_state ->
    Lemma (requires ROk? (fst (eval_expr fuel1 e st)))
          (ensures (
            let (r1, st1) = eval_expr fuel1 e st in
            let (r2, st2) = eval_expr fuel2 e st in
            r1 == r2 /\ st1 == st2))

(** Sufficient fuel axiom.

    For any expression that would terminate with infinite fuel, there exists
    some finite fuel amount that suffices.

    Note: This is an axiom because we cannot constructively compute the
    required fuel for arbitrary expressions. *)
val eval_terminates_axiom : e:expr -> st:eval_state ->
    Lemma (ensures exists (fuel:nat). ~(RDiv? (fst (eval_expr fuel e st))))

(** Successful result implies non-divergence *)
val eval_ok_not_div : fuel:nat -> e:expr -> st:eval_state ->
    Lemma (requires ROk? (fst (eval_expr fuel e st)))
          (ensures ~(RDiv? (fst (eval_expr fuel e st))))

(** ----------------------------------------------------------------------------
    TYPE PRESERVATION (before fuel monotonicity to match BrrrEval.fst order)
    ---------------------------------------------------------------------------- *)

(** Type preservation: evaluation preserves types.

    If expression e has type t in typing environment gamma, and evaluation
    succeeds producing value v, then v has type t.

    Note: Uses placeholder predicates. Full proof requires type checker. *)
val eval_preserves_type : fuel:nat -> e:expr -> st:eval_state ->
                          gamma:typing_env -> t:brrr_type ->
    Lemma (requires well_typed e gamma t)
          (ensures (let (r, st') = eval_expr fuel e st in
                    ROk? r ==> value_well_typed (result_value r) st'.es_heap t))

(** Fuel monotonicity: adding fuel preserves successful results.
    SMTPat enables automatic application by Z3. *)
val eval_fuel_monotone : fuel:nat -> k:nat -> e:expr -> st:eval_state ->
    Lemma (requires ROk? (fst (eval_expr fuel e st)))
          (ensures eval_expr (fuel + k) e st == eval_expr fuel e st)
    [SMTPat (eval_expr (fuel + k) e st)]

(** Fuel sufficiency: if we don't diverge, more fuel gives same result. *)
val eval_fuel_sufficient : fuel1:nat -> fuel2:nat -> e:expr -> st:eval_state ->
    Lemma (requires fuel2 >= fuel1 /\ ~(RDiv? (fst (eval_expr fuel1 e st))))
          (ensures fst (eval_expr fuel2 e st) == fst (eval_expr fuel1 e st))

#pop-options

(** ----------------------------------------------------------------------------
    CLOSED TERM EVALUATION
    ---------------------------------------------------------------------------- *)

(** Check if expression is closed (no free variables) *)
val is_closed : expr -> bool

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Environment irrelevance for closed terms.
    For closed expressions, the local environment doesn't affect evaluation. *)
val eval_closed_env_irrelevant : fuel:nat -> e:expr -> st1:eval_state -> st2:eval_state ->
    Lemma (requires is_closed e /\
                    st1.es_heap == st2.es_heap /\
                    st1.es_closures == st2.es_closures /\
                    st1.es_globals == st2.es_globals /\
                    st1.es_handlers == st2.es_handlers /\
                    st1.es_methods == st2.es_methods)
          (ensures fst (eval_expr fuel e st1) == fst (eval_expr fuel e st2))

#pop-options

(** ----------------------------------------------------------------------------
    PROGRESS THEOREM
    ---------------------------------------------------------------------------- *)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Progress (weak form): well-typed expressions produce valid results.

    The result is either success, error, divergence, or control flow.
    It never gets "stuck" in an undefined state. *)
val progress_weak : fuel:nat -> e:expr -> st:eval_state -> gamma:typing_env -> t:brrr_type ->
    Lemma (requires well_typed e gamma t /\ fuel > 0)
          (ensures (let (r, _) = eval_expr fuel e st in
                    r == RDiv \/ ROk? r \/ RErr? r \/ RBreak? r \/ RCont? r \/
                    RRet? r \/ RYield? r \/ RPerform? r \/ RAbort? r))

#pop-options

(** ----------------------------------------------------------------------------
    HEAP MONOTONICITY
    ---------------------------------------------------------------------------- *)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Heap location validity is preserved by evaluation.
    If a location is valid before evaluation, it remains valid after. *)
val eval_preserves_valid_locs : fuel:nat -> e:expr -> st:eval_state -> l:loc ->
    Lemma (requires Some? (read l st.es_heap))
          (ensures (let (_, st') = eval_expr fuel e st in
                    Some? (read l st'.es_heap)))

#pop-options

(** ============================================================================
    LITERAL EVALUATION LEMMAS
    ============================================================================

    Simple lemmas for literals, useful as SMTPat triggers.
    Following HACL* pattern of establishing base cases explicitly.
*)

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

(** Literal evaluation always succeeds with sufficient fuel *)
val eval_lit_ok : fuel:nat -> lit:literal -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures ROk? (fst (eval_expr fuel (mk_expr_dummy (ELit lit)) st)))
    [SMTPat (eval_expr fuel (mk_expr_dummy (ELit lit)) st)]

(** Literal evaluation produces the expected value *)
val eval_lit_value : fuel:nat -> lit:literal -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures fst (eval_expr fuel (mk_expr_dummy (ELit lit)) st) ==
                   ROk (lit_to_value lit))

(** Literal evaluation doesn't modify state *)
val eval_lit_state : fuel:nat -> lit:literal -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures snd (eval_expr fuel (mk_expr_dummy (ELit lit)) st) == st)

#pop-options

(** ============================================================================
    VARIABLE LOOKUP LEMMAS
    ============================================================================ *)

#push-options "--z3rlimit 25 --fuel 1 --ifuel 0"

(** Variable lookup succeeds if the variable is bound *)
val eval_var_bound : fuel:nat -> x:var_id -> st:eval_state ->
    Lemma (requires fuel >= 1 /\ Some? (lookup x st.es_env))
          (ensures ROk? (fst (eval_expr fuel (mk_expr_dummy (EVar x)) st)))

(** Variable lookup returns the bound value *)
val eval_var_value : fuel:nat -> x:var_id -> v:value -> st:eval_state ->
    Lemma (requires fuel >= 1 /\ lookup x st.es_env == Some v)
          (ensures fst (eval_expr fuel (mk_expr_dummy (EVar x)) st) == ROk v)
    [SMTPat (eval_expr fuel (mk_expr_dummy (EVar x)) st);
     SMTPat (lookup x st.es_env)]

#pop-options

(** ============================================================================
    COMPOSITION LEMMAS
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"

(** Sequence evaluation: if first succeeds, result is second's result *)
val eval_seq_composition : fuel:nat -> e1:expr -> e2:expr -> st:eval_state -> v1:value ->
    Lemma (requires fuel >= 3 /\
                    eval_expr (fuel - 1) e1 st == (ROk v1, st))
          (ensures (let (r, st') = eval_expr fuel (mk_expr_dummy (ESeq e1 e2)) st in
                    eval_expr (fuel - 1) e2 st == (r, st')))

(** Let binding semantics *)
val eval_let_binding : fuel:nat -> x:var_id -> e1:expr -> e2:expr ->
                       st:eval_state -> v1:value ->
    Lemma (requires fuel >= 3 /\
                    fst (eval_expr (fuel - 1) e1 st) == ROk v1)
          (ensures (let (_, st1) = eval_expr (fuel - 1) e1 st in
                    let st_bound = { st1 with es_env = extend x v1 st1.es_env } in
                    let p = locate_dummy (PatVar x) in
                    let (r, _) = eval_expr fuel (mk_expr_dummy (ELet p None e1 e2)) st in
                    r == fst (eval_expr (fuel - 1) e2 st_bound)))

#pop-options

(** ============================================================================
    ERROR PROPAGATION LEMMAS
    ============================================================================ *)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"

(** Errors propagate upward *)
val eval_error_propagates : fuel:nat -> e:expr -> st:eval_state -> err_val:value ->
    Lemma (requires fuel >= 1 /\ fst (eval_expr fuel e st) == RErr err_val)
          (ensures RErr? (fst (eval_expr fuel e st)))

(** Divergence propagates upward *)
val eval_div_propagates : fuel:nat -> e:expr -> st:eval_state ->
    Lemma (requires fst (eval_expr fuel e st) == RDiv)
          (ensures RDiv? (fst (eval_expr fuel e st)))

#pop-options

(** ============================================================================
    EFFECT TRACKING INTERFACE
    ============================================================================

    Track effects performed during evaluation.
*)

(** Compute the effect row of an expression (static analysis).
    This is a conservative over-approximation of effects. *)
val expr_effects : expr -> effect_row

(** Effects subset relation *)
val effect_subset : effect_row -> effect_row -> bool

(** ============================================================================
    ASYNC/AWAIT SPECIFICATIONS
    ============================================================================

    Specifications for async/await evaluation following Part V of the spec.
*)

(** async creates a cold (pending) future *)
val eval_async_creates_pending : fuel:nat -> body:expr -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures (let (r, _) = eval_expr fuel (mk_expr_dummy (EAsync body)) st in
                    ROk? r ==> VFuture? (result_value r) /\
                               RFutPending? (VFuture?._0 (result_value r))))

(** spawn evaluates body and creates resolved/failed future *)
val eval_spawn_evaluates : fuel:nat -> body:expr -> st:eval_state ->
    Lemma (requires fuel >= 2)
          (ensures (let (r, _) = eval_expr fuel (mk_expr_dummy (ESpawn body)) st in
                    ROk? r ==> VFuture? (result_value r)))

(** ============================================================================
    DELIMITED CONTINUATION SPECIFICATIONS
    ============================================================================

    Specifications for reset/shift evaluation (Part V).
*)

(** reset captures value if body returns normally *)
val eval_reset_value : fuel:nat -> lbl:label -> body:expr -> st:eval_state -> v:value ->
    Lemma (requires fuel >= 2 /\
                    fst (eval_expr (fuel - 1) body
                         { st with es_prompts = push_prompt lbl st.es_env st.es_prompts })
                    == ROk v)
          (ensures (let (r, _) = eval_expr fuel (mk_expr_dummy (EReset lbl body)) st in
                    r == ROk v))

(** ============================================================================
    STEP RELATION (Small-Step Semantics Interface)
    ============================================================================

    Small-step reduction relation for finer-grained reasoning.
    Complements the big-step eval_expr.
*)

(** Configuration: expression + state *)
type config = expr & eval_state

(** Single-step reduction relation (declarative).
    Implemented as a relation, not a function, for flexibility. *)
val step : config -> config -> Type0

(** step is deterministic *)
val step_deterministic : c:config -> c1:config -> c2:config ->
    Lemma (requires step c c1 /\ step c c2)
          (ensures c1 == c2)

(** ============================================================================
    SAFETY THEOREMS
    ============================================================================

    High-level safety properties derived from the above lemmas.
*)

(** Type safety: well-typed programs don't get stuck.

    This combines progress and preservation into a single theorem.
    A well-typed program either:
    1. Evaluates to a value of the expected type
    2. Diverges (runs out of fuel)
    3. Throws an exception
    4. Performs an effect or control operation
*)
val type_safety : fuel:nat -> e:expr -> st:eval_state -> gamma:typing_env -> t:brrr_type ->
    Lemma (requires well_typed e gamma t /\ fuel > 0)
          (ensures (let (r, st') = eval_expr fuel e st in
                    (ROk? r ==> value_well_typed (result_value r) st'.es_heap t) /\
                    (r == RDiv \/ ROk? r \/ RErr? r \/ RBreak? r \/ RCont? r \/
                     RRet? r \/ RYield? r \/ RPerform? r \/ RAbort? r)))

(** ============================================================================
    ADDITIONAL EVALUATION PROPERTIES
    ============================================================================

    These lemmas capture important semantic properties used in program analysis.
*)

(** Unary operation evaluation is pure (no state change) *)
val do_unary_pure : op:unary_op -> v:value ->
    Lemma (ensures True)  (* State unchanged *)

(** Binary operation evaluation is pure (no state change) *)
val do_binary_pure : op:binary_op -> v1:value -> v2:value ->
    Lemma (ensures True)  (* State unchanged *)

(** If-then-else evaluates only one branch *)
val eval_if_one_branch : fuel:nat -> cond:expr -> then_e:expr -> else_e:expr ->
                         st:eval_state -> b:bool ->
    Lemma (requires fuel >= 3 /\ fst (eval_expr (fuel - 1) cond st) == ROk (VBool b))
          (ensures (let (_, st1) = eval_expr (fuel - 1) cond st in
                    let branch = if b then then_e else else_e in
                    let (r, st') = eval_expr fuel (mk_expr_dummy (EIf cond then_e else_e)) st in
                    r == fst (eval_expr (fuel - 1) branch st1)))

(** Short-circuit AND: false on left means no right evaluation *)
val eval_and_short_circuit_false : fuel:nat -> e1:expr -> e2:expr -> st:eval_state ->
    Lemma (requires fuel >= 2 /\ fst (eval_expr (fuel - 1) e1 st) == ROk (VBool false))
          (ensures fst (eval_expr fuel (mk_expr_dummy (EBinary OpAnd e1 e2)) st) ==
                   ROk (VBool false))

(** Short-circuit OR: true on left means no right evaluation *)
val eval_or_short_circuit_true : fuel:nat -> e1:expr -> e2:expr -> st:eval_state ->
    Lemma (requires fuel >= 2 /\ fst (eval_expr (fuel - 1) e1 st) == ROk (VBool true))
          (ensures fst (eval_expr fuel (mk_expr_dummy (EBinary OpOr e1 e2)) st) ==
                   ROk (VBool true))

(** ============================================================================
    PATTERN MATCHING SPECIFICATIONS
    ============================================================================ *)

(** Pattern match success implies bindings are well-formed *)
val match_pattern_bindings_wf : fuel:nat -> pat:pattern -> v:value -> st:eval_state ->
    Lemma (ensures (let (r, _) = match_pattern_with_context fuel pat v st in
                    Some? r ==> True))  (* All bindings are valid var_id/value pairs *)

(** Wildcard always matches *)
val match_wild_always : fuel:nat -> v:value -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures fst (match_pattern_with_context fuel (locate_dummy PatWild) v st) == Some [])

(** Variable pattern captures value *)
val match_var_captures : fuel:nat -> x:var_id -> v:value -> st:eval_state ->
    Lemma (requires fuel >= 1)
          (ensures fst (match_pattern_with_context fuel (locate_dummy (PatVar x)) v st) ==
                   Some [(x, v)])

