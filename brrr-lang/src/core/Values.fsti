(**
 * BrrrLang.Core.Values - Interface
 *
 * Runtime values and computation domains.
 * Based on brrr_lang_spec_v0.4.tex Part I (Foundations).
 *
 * Following HACL* Spec.Agile.Hash.fsti and Lib.Buffer.fsti patterns for:
 * - Type abstraction with unfold aliases
 * - val declarations with pre/post conditions
 * - Inversion lemmas with SMTPat triggers
 * - Canonical form lemmas for type preservation
 *
 * Depends on: Primitives, Types, Expressions
 *)
module Values

(** Z3 solver options - following HACL* pattern for value proofs.
    Higher fuel needed for recursive value lemmas. *)
#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open FStar.List.Tot

(** ============================================================================
    HELPER FUNCTIONS
    ============================================================================ *)

(** Check predicate holds for corresponding elements of two lists.
    Returns true if lists have equal length and f(x,y) for all pairs. *)
val for_all2 : #a:Type -> #b:Type -> (a -> b -> bool) -> list a -> list b -> bool

(** ============================================================================
    LOCATION AND CLOSURE IDENTIFIERS
    ============================================================================ *)

(** Heap location - abstract index into the heap.
    Using nat ensures non-negative locations. *)
unfold
let loc = nat

(** Closure identifier - index into closure store.
    Each closure gets a unique ID at creation time. *)
unfold
let closure_id = nat

(** ============================================================================
    STRICTLY POSITIVE LIST WRAPPER
    ============================================================================

    F*'s positivity checker requires this wrapper to allow mutual recursion
    between value and list types. This is semantically equivalent to list
    but tells the checker the type parameter appears strictly positively.
*)
unfold
let vlist ([@@@strictly_positive] a: Type) = list a

(** ============================================================================
    RUNTIME FUTURE STATE
    ============================================================================

    Runtime representation of future state for the async evaluator.
    Mirrors the future_state type from Async.fst but with concrete runtime
    representation using heap locations instead of direct values.

    State transitions:
    - RFutPending   ->  RFutResolved | RFutFailed | RFutCancelled
    - Terminal states: RFutResolved, RFutFailed, RFutCancelled
*)

noeq type runtime_future_state =
  | RFutPending   : runtime_future_state
  | RFutResolved  : loc -> runtime_future_state
  | RFutFailed    : error:string -> runtime_future_state
  | RFutCancelled : runtime_future_state

(** ============================================================================
    RUNTIME GENERATOR STATE
    ============================================================================

    Runtime representation of generator state for the evaluator.
    Implements the 4-state model from Async.fst:

    State transitions:
      RGenInitial --[next()]--> RGenYielded | RGenDone | RGenFailed
      RGenYielded --[next()]--> RGenYielded | RGenDone | RGenFailed
      RGenDone, RGenFailed are terminal states

    Values stored via heap locations to avoid mutual recursion issues.
*)

noeq type runtime_gen_state =
  | RGenInitial   : body_closure:closure_id -> runtime_gen_state
  | RGenYielded   : yielded_loc:loc -> resume_closure:closure_id -> runtime_gen_state
  | RGenDone      : final_loc:loc -> runtime_gen_state
  | RGenFailed    : error:string -> runtime_gen_state

(** ============================================================================
    RUNTIME VALUE TYPE
    ============================================================================

    Following HACL* Lib.IntTypes pattern for type-safe value representation:
    - VInt preserves int_type (width + signedness) from the literal
    - VFloat preserves float_prec from the literal

    This ensures no type information is lost during evaluation, critical for:
    - Correct overflow/underflow behavior during arithmetic
    - Proper type checking at runtime
    - Accurate serialization/deserialization
    ============================================================================ *)

noeq type value =
  (* Primitives - preserve type information following HACL* patterns *)
  | VUnit   : value
  | VBool   : bool -> value
  | VInt    : n:int -> ty:int_type -> value
  | VFloat  : f:float_repr -> prec:float_prec -> value
  | VString : string -> value
  | VChar   : FStar.Char.char -> value

  (* Compound - use vlist for positivity *)
  | VTuple  : vlist value -> value
  | VArray  : vlist value -> value
  | VStruct : type_name -> vlist (string & value) -> value
  | VVariant : type_name -> string -> vlist value -> value

  (* References *)
  | VRef    : loc -> value
  | VRefMut : loc -> value
  | VBox    : loc -> value

  (* Functions *)
  | VClosure : closure_id -> value
  | VBoundMethod : receiver:value -> method_closure:closure_id -> value  (* Bound method: receiver + method *)

  (* Option/Result *)
  | VNone   : value
  | VSome   : value -> value
  | VOk     : value -> value
  | VErr    : value -> value

  (* Async/Generators - Part V: Async and Effects *)
  | VFuture    : runtime_future_state -> value
  | VGenerator : runtime_gen_state -> value

(** ============================================================================
    ENVIRONMENT TYPE
    ============================================================================ *)

(** Environment: maps variable identifiers to their values.
    Implemented as association list for simplicity.
    Later bindings shadow earlier ones (head of list takes precedence). *)
unfold
let env = list (var_id & value)

(** ============================================================================
    CLOSURE TYPE
    ============================================================================ *)

(** Closure: a captured function value with its environment.
    Represents a function that has captured its lexical scope. *)
noeq type closure = {
  closure_env    : env;           (* Captured variable bindings *)
  closure_params : list var_id;   (* Parameter names *)
  closure_body   : expr           (* Function body expression *)
}

(** ============================================================================
    ENVIRONMENT OPERATIONS
    ============================================================================ *)

(** Empty environment *)
val empty_env : env

(** Lookup variable in environment.
    Returns None if variable is not bound. *)
val lookup : var_id -> env -> option value

(** Extend environment with a new binding.
    New binding shadows any existing binding for the same variable. *)
val extend : var_id -> value -> env -> env

(** Extend environment with multiple bindings.
    Later bindings in the list shadow earlier ones. *)
val extend_many : list (var_id & value) -> env -> env

(** extend_many with singleton list equals extend.
    This is used in let-binding proofs. *)
val extend_many_singleton : x:var_id -> v:value -> e:env ->
    Lemma (ensures extend_many [(x, v)] e == extend x v e)
    [SMTPat (extend_many [(x, v)] e)]

(** Remove variable from environment.
    Removes all bindings for the given variable. *)
val remove : var_id -> env -> env

(** Domain of environment: list of bound variable identifiers *)
val dom : env -> list var_id

(** ============================================================================
    HEAP TYPE AND OPERATIONS
    ============================================================================ *)

(** Heap: maps locations to stored values.
    Implemented as association list. *)
unfold
let heap = list (loc & value)

(** Empty heap *)
val empty_heap : heap

(** Next available location in heap.
    Returns 1 + maximum location currently in use. *)
val next_loc : heap -> loc

(** Allocate value on heap, returning new location and updated heap *)
val alloc : value -> heap -> loc & heap

(** Read value at location.
    Returns None if location is not allocated. *)
val read : loc -> heap -> option value

(** Write value at location, returning updated heap.
    Creates or updates the binding at the given location. *)
val write : loc -> value -> heap -> heap

(** Deallocate location, returning updated heap *)
val dealloc : loc -> heap -> heap

(** ============================================================================
    COMPUTATION RESULTS
    ============================================================================

    Result type for computations that may:
    - Succeed with a value (ROk)
    - Fail with an exception (RErr)
    - Diverge (RDiv)
    - Break from a loop (RBreak)
    - Continue in a loop (RCont)
    - Return from a function (RRet)
    - Yield from a generator (RYield)
    - Perform an algebraic effect (RPerform)
    - Abort to a prompt (RAbort)
*)

noeq type result (a: Type) =
  | ROk      : a -> result a
  | RErr     : value -> result a
  | RDiv     : result a
  | RBreak   : option string -> option value -> result a
  | RCont    : option string -> result a
  | RRet     : option value -> result a
  | RYield   : value -> result a
  | RPerform : Effects.effect_op -> list value -> result a
  | RAbort   : string -> value -> result a
  | RGoto    : string -> result a  (* Jump to labeled statement *)

(** Result monad: return *)
val return : #a:Type -> a -> result a

(** Result monad: bind *)
val bind : #a:Type -> #b:Type -> result a -> (a -> result b) -> result b

(** Map function over result *)
val map_result : #a:Type -> #b:Type -> (a -> b) -> result a -> result b

(** Extract value from ROk result. Requires ROk? r as precondition. *)
val result_value : #a:Type -> r:result a{ROk? r} -> a

(** ============================================================================
    STATE TYPE AND MONAD
    ============================================================================ *)

(** State: environment + heap *)
noeq type state = {
  st_env  : env;
  st_heap : heap
}

(** Initial state with empty environment and heap *)
val init_state : state

(** State computation monad *)
unfold
let comp (a: Type) = state -> result a & state

(** State monad: return *)
val st_return : #a:Type -> a -> comp a

(** State monad: bind *)
val st_bind : #a:Type -> #b:Type -> comp a -> (a -> comp b) -> comp b

(** Get current environment *)
val get_env : comp env

(** Set environment *)
val set_env : env -> comp unit

(** Get current heap *)
val get_heap : comp heap

(** Set heap *)
val set_heap : heap -> comp unit

(** Lookup variable in current state *)
val st_lookup : var_id -> comp (option value)

(** Extend current environment with binding *)
val st_extend : var_id -> value -> comp unit

(** Allocate on heap in current state *)
val st_alloc : value -> comp loc

(** Read from heap in current state *)
val st_read : loc -> comp (option value)

(** Write to heap in current state *)
val st_write : loc -> value -> comp unit

(** ============================================================================
    VALUE OPERATIONS
    ============================================================================ *)

(** Convert literal to value - preserves type information.

    Type preservation:
    - LitInt n ty  ->  VInt n ty   (preserves int_type)
    - LitFloat f p ->  VFloat f p  (preserves float_prec)
*)
val lit_to_value : literal -> value

(** ============================================================================
    VALUE SIZE (for termination measures)
    ============================================================================ *)

(** Size of a value - used for termination proofs in recursive functions *)
val value_size : value -> Tot nat

(** Size of a value list *)
val value_list_size : vlist value -> Tot nat

(** Size of field value list *)
val field_value_list_size : vlist (string & value) -> Tot nat

(** value_size is always positive *)
val value_size_pos : v:value ->
    Lemma (ensures value_size v >= 1)
          [SMTPat (value_size v)]

(** ============================================================================
    RUNTIME STATE EQUALITY
    ============================================================================ *)

(** Future state equality *)
val runtime_future_state_eq : runtime_future_state -> runtime_future_state -> bool

(** Generator state equality *)
val runtime_gen_state_eq : runtime_gen_state -> runtime_gen_state -> bool

(** ============================================================================
    VALUE EQUALITY - IEEE 754 COMPLIANT
    ============================================================================

    CRITICAL: Float comparison follows IEEE 754 semantics:
    - NaN is not equal to anything, including itself
    - Two floats must have matching precision for equality

    For bit-exact comparison (serialization), use value_eq_bits.
*)

(** Value equality - IEEE 754 compliant.
    Warning: Due to NaN semantics, this is NOT reflexive for all values. *)
val value_eq : value -> value -> Tot bool

(** Value list equality *)
val value_list_eq : vlist value -> vlist value -> Tot bool

(** Bit-exact value equality - ignores IEEE 754 NaN semantics.
    This IS reflexive for all values.
    Use for serialization, hashing, or when bit-exact comparison is needed. *)
val value_eq_bits : value -> value -> Tot bool

(** Bit-exact list equality *)
val value_list_eq_bits : vlist value -> vlist value -> Tot bool

(** ============================================================================
    VALUE COMPARISON
    ============================================================================ *)

(** Value comparison - returns -1, 0, or 1.
    IEEE 754 compliant for floats: NaN comparisons return 0 (unordered). *)
val value_compare : value -> value -> int

(** Truthy check - determines if value is "truthy" in boolean context.

    Truthy values:
    - VBool true
    - VInt n _ where n <> 0
    - VFloat f _ where f is not NaN and f <> 0
    - VSome _
    - Most other values (except VNone, VBool false, etc.)
*)
val is_truthy : value -> bool

(** ============================================================================
    NAN-FREE PREDICATE
    ============================================================================

    Required for reflexivity of value_eq (since NaN != NaN per IEEE 754).
*)

(** Predicate: value contains no NaN floats *)
val value_is_nan_free : value -> Tot bool

(** Predicate: value list contains no NaN floats *)
val value_list_is_nan_free : vlist value -> Tot bool

(** Predicate: field value list contains no NaN floats *)
val field_value_list_is_nan_free : vlist (string & value) -> Tot bool

(** ============================================================================
    VALUE EQUALITY LEMMAS
    ============================================================================

    These lemmas establish the algebraic properties of value equality.

    IMPORTANT: Due to IEEE 754 semantics (NaN != NaN), value_eq does NOT
    form a true equivalence relation. Use value_eq_bits for full equivalence.
*)

(** value_eq_bits is reflexive (always holds - SMTPat for automatic application) *)
val value_eq_bits_refl : v:value ->
    Lemma (ensures value_eq_bits v v = true)
          [SMTPat (value_eq_bits v v)]

(** value_list_eq_bits is reflexive *)
val value_list_eq_bits_refl : vs:vlist value ->
    Lemma (ensures value_list_eq_bits vs vs = true)

(** value_eq is reflexive FOR NAN-FREE VALUES ONLY.
    This does NOT hold for values containing NaN floats. *)
val value_eq_refl : v:value ->
    Lemma (requires value_is_nan_free v)
          (ensures value_eq v v = true)
          [SMTPat (value_eq v v)]

(** value_list_eq is reflexive for NaN-free lists *)
val value_list_eq_refl : vs:vlist value ->
    Lemma (requires value_list_is_nan_free vs)
          (ensures value_list_eq vs vs = true)

(** value_eq is symmetric: if v1 = v2 then v2 = v1 *)
val value_eq_sym : v1:value -> v2:value ->
    Lemma (requires value_eq v1 v2 = true)
          (ensures value_eq v2 v1 = true)
          [SMTPat (value_eq v1 v2); SMTPat (value_eq v2 v1)]

(** value_list_eq is symmetric *)
val value_list_eq_sym : vs1:vlist value -> vs2:vlist value ->
    Lemma (requires value_list_eq vs1 vs2 = true)
          (ensures value_list_eq vs2 vs1 = true)

(** value_eq is transitive: if v1 = v2 and v2 = v3 then v1 = v3 *)
val value_eq_trans : v1:value -> v2:value -> v3:value ->
    Lemma (requires value_eq v1 v2 = true /\ value_eq v2 v3 = true)
          (ensures value_eq v1 v3 = true)

(** value_list_eq is transitive *)
val value_list_eq_trans : vs1:vlist value -> vs2:vlist value -> vs3:vlist value ->
    Lemma (requires value_list_eq vs1 vs2 = true /\ value_list_eq vs2 vs3 = true)
          (ensures value_list_eq vs1 vs3 = true)

(** ============================================================================
    VALUE CANONICAL FORM LEMMAS
    ============================================================================

    These lemmas establish that each value constructor uniquely determines
    the observable properties of that value. Following HACL* pattern for
    type-driven refinement proofs.
*)

(** VUnit is the unique unit value *)
val vunit_canonical : v:value ->
    Lemma (requires VUnit? v)
          (ensures v == VUnit)
          [SMTPat (VUnit? v)]

(** VBool values are determined by their boolean *)
val vbool_canonical : v:value -> b:bool ->
    Lemma (requires VBool? v /\ VBool?._0 v = b)
          (ensures v == VBool b)
          [SMTPat (VBool? v)]

(** VInt values preserve their type information *)
val vint_type_preserved : v:value -> n:int -> ty:int_type ->
    Lemma (requires VInt? v /\ VInt?.n v = n /\ VInt?.ty v = ty)
          (ensures v == VInt n ty)

(** VFloat values preserve their precision *)
val vfloat_prec_preserved : v:value -> f:float_repr -> p:float_prec ->
    Lemma (requires VFloat? v /\ VFloat?.f v = f /\ VFloat?.prec v = p)
          (ensures v == VFloat f p)

(** VRef locations are non-negative *)
val vref_loc_nonneg : v:value ->
    Lemma (requires VRef? v)
          (ensures VRef?._0 v >= 0)
          [SMTPat (VRef? v)]

(** VRefMut locations are non-negative *)
val vrefmut_loc_nonneg : v:value ->
    Lemma (requires VRefMut? v)
          (ensures VRefMut?._0 v >= 0)
          [SMTPat (VRefMut? v)]

(** VBox locations are non-negative *)
val vbox_loc_nonneg : v:value ->
    Lemma (requires VBox? v)
          (ensures VBox?._0 v >= 0)
          [SMTPat (VBox? v)]

(** VClosure IDs are non-negative *)
val vclosure_id_nonneg : v:value ->
    Lemma (requires VClosure? v)
          (ensures VClosure?._0 v >= 0)
          [SMTPat (VClosure? v)]

(** ============================================================================
    VALUE TYPE INVERSION LEMMA
    ============================================================================

    Master inversion lemma that connects value constructor to its observable
    properties. This enables automatic reasoning about value structure.

    Following the pattern from the task specification for comprehensive
    value type tracking.
*)

(** Value constructor determines discriminator.
    This lemma is triggered automatically via SMTPat. *)
val value_type_inversion : v:value ->
    Lemma (ensures
           (VUnit? v    ==> v == VUnit) /\
           (VNone? v    ==> v == VNone) /\
           (VBool? v    ==> (exists (b:bool). v == VBool b)) /\
           (VInt? v     ==> (exists (n:int) (ty:int_type). v == VInt n ty)) /\
           (VFloat? v   ==> (exists (f:float_repr) (p:float_prec). v == VFloat f p)) /\
           (VString? v  ==> (exists (s:string). v == VString s)) /\
           (VChar? v    ==> (exists (c:FStar.Char.char). v == VChar c)) /\
           (VTuple? v   ==> (exists (vs:vlist value). v == VTuple vs)) /\
           (VArray? v   ==> (exists (vs:vlist value). v == VArray vs)) /\
           (VStruct? v  ==> (exists (tn:type_name) (fs:vlist (string & value)). v == VStruct tn fs)) /\
           (VVariant? v ==> (exists (tn:type_name) (vn:string) (vs:vlist value). v == VVariant tn vn vs)) /\
           (VRef? v     ==> (exists (l:loc). v == VRef l /\ l >= 0)) /\
           (VRefMut? v  ==> (exists (l:loc). v == VRefMut l /\ l >= 0)) /\
           (VBox? v     ==> (exists (l:loc). v == VBox l /\ l >= 0)) /\
           (VClosure? v ==> (exists (id:closure_id). v == VClosure id /\ id >= 0)) /\
           (VSome? v    ==> (exists (v':value). v == VSome v')) /\
           (VOk? v      ==> (exists (v':value). v == VOk v')) /\
           (VErr? v     ==> (exists (v':value). v == VErr v')) /\
           (VFuture? v  ==> (exists (fs:runtime_future_state). v == VFuture fs)) /\
           (VGenerator? v ==> (exists (gs:runtime_gen_state). v == VGenerator gs)))
          [SMTPat (VUnit? v); SMTPat (VNone? v); SMTPat (VBool? v);
           SMTPat (VInt? v); SMTPat (VFloat? v)]

(** ============================================================================
    PATTERN MATCHING
    ============================================================================ *)

(** Match result: optional list of bindings from successful match *)
unfold
let match_result = option (list (var_id & value))

(** Pattern size for termination measures *)
val pattern_size : pattern -> Tot nat

(** Pattern list size *)
val pattern_list_size : list pattern -> Tot nat

(** Field pattern list size *)
val field_pattern_list_size : list (string & pattern) -> Tot nat

(** Match value against pattern.

    Returns Some bindings on successful match, None on failure.

    Note: PatRef and PatBox match the wrapper, not dereferenced content.
    Dereferencing requires heap access - use eval_match_pattern in Eval.fst.

    Note: PatGuard patterns always return None here since guards require
    expression evaluation context.
*)
val match_pattern : pattern -> value -> Tot match_result

(** PatVar patterns always match and bind the value.
    This is a fundamental property used in let-binding proofs. *)
val match_pattern_patvar : x:var_id -> v:value ->
    Lemma (ensures match_pattern (locate_dummy (PatVar x)) v == Some [(x, v)])
    [SMTPat (match_pattern (locate_dummy (PatVar x)) v)]

(** Match multiple patterns against multiple values *)
val match_patterns : list pattern -> list value -> Tot match_result

(** Match struct field patterns *)
val match_struct_fields : list (string & pattern) -> list (string & value) -> Tot match_result

(** ============================================================================
    LITERAL-VALUE TYPE PRESERVATION LEMMAS
    ============================================================================

    These lemmas ensure lit_to_value preserves type information correctly.
    Following HACL* pattern for compile-time constant lemmas.
*)

(** Unit literal produces unit value *)
val lit_to_value_unit : unit ->
    Lemma (lit_to_value LitUnit == VUnit)

(** Bool literal produces bool value with same boolean *)
val lit_to_value_bool : b:bool ->
    Lemma (lit_to_value (LitBool b) == VBool b)
          [SMTPat (lit_to_value (LitBool b))]

(** Int literal preserves integer type *)
val lit_to_value_int : n:int -> ty:int_type ->
    Lemma (lit_to_value (LitInt n ty) == VInt n ty)
          [SMTPat (lit_to_value (LitInt n ty))]

(** Float literal preserves precision *)
val lit_to_value_float : f:float_repr -> p:float_prec ->
    Lemma (lit_to_value (LitFloat f p) == VFloat f p)
          [SMTPat (lit_to_value (LitFloat f p))]

(** String literal produces string value *)
val lit_to_value_string : s:string ->
    Lemma (lit_to_value (LitString s) == VString s)
          [SMTPat (lit_to_value (LitString s))]

(** Char literal produces char value *)
val lit_to_value_char : c:FStar.Char.char ->
    Lemma (lit_to_value (LitChar c) == VChar c)
          [SMTPat (lit_to_value (LitChar c))]

(** ============================================================================
    HEAP OPERATION SPECIFICATIONS
    ============================================================================

    These specifications ensure heap operations maintain invariants.
*)

(** alloc returns a fresh location not in the original heap *)
val alloc_fresh : v:value -> h:heap ->
    Lemma (let (l, h') = alloc v h in
           read l h == None /\
           read l h' == Some v)
          [SMTPat (alloc v h)]

(** alloc preserves existing heap bindings *)
val alloc_preserves : v:value -> h:heap -> l':loc ->
    Lemma (requires (let (l, _) = alloc v h in l <> l'))
          (ensures (let (_, h') = alloc v h in read l' h' == read l' h))

(** write updates the specified location *)
val write_updates : l:loc -> v:value -> h:heap ->
    Lemma (read l (write l v h) == Some v)
          [SMTPat (read l (write l v h))]

(** write preserves other locations *)
val write_preserves : l:loc -> v:value -> h:heap -> l':loc ->
    Lemma (requires l <> l')
          (ensures read l' (write l v h) == read l' h)
          [SMTPat (read l' (write l v h))]

(** dealloc removes the specified location *)
val dealloc_removes : l:loc -> h:heap ->
    Lemma (read l (dealloc l h) == None)
          [SMTPat (read l (dealloc l h))]

(** dealloc preserves other locations *)
val dealloc_preserves : l:loc -> h:heap -> l':loc ->
    Lemma (requires l <> l')
          (ensures read l' (dealloc l h) == read l' h)
          [SMTPat (read l' (dealloc l h))]

(** ============================================================================
    ENVIRONMENT OPERATION SPECIFICATIONS
    ============================================================================ *)

(** lookup after extend finds the extended binding *)
val extend_lookup : x:var_id -> v:value -> e:env ->
    Lemma (lookup x (extend x v e) == Some v)
          [SMTPat (lookup x (extend x v e))]

(** lookup after extend for different variable is unchanged *)
val extend_lookup_other : x:var_id -> y:var_id -> v:value -> e:env ->
    Lemma (requires x <> y)
          (ensures lookup y (extend x v e) == lookup y e)

(** lookup in empty_env always returns None *)
val empty_env_lookup : x:var_id ->
    Lemma (lookup x empty_env == None)
          [SMTPat (lookup x empty_env)]

(** remove eliminates the binding *)
val remove_lookup : x:var_id -> e:env ->
    Lemma (lookup x (remove x e) == None)
          [SMTPat (lookup x (remove x e))]

(** ============================================================================
    RESULT MONAD LAWS
    ============================================================================

    These lemmas establish that result forms a proper monad.
*)

(** Left identity: return a >>= f  ===  f a *)
val result_left_identity : #a:Type -> #b:Type -> x:a -> f:(a -> result b) ->
    Lemma (bind (return x) f == f x)

(** Right identity: m >>= return  ===  m *)
val result_right_identity : #a:Type -> m:result a ->
    Lemma (bind m return == m)

(** Associativity: (m >>= f) >>= g  ===  m >>= (\x -> f x >>= g) *)
val result_assoc : #a:Type -> #b:Type -> #c:Type ->
    m:result a -> f:(a -> result b) -> g:(b -> result c) ->
    Lemma (bind (bind m f) g == bind m (fun x -> bind (f x) g))

(** ============================================================================
    TYPE INFERENCE FROM VALUES
    ============================================================================

    Following HACL* Lib.Sequence.Lemmas patterns for type preservation proofs.
    The type_of_value function computes the static type from a runtime value.
    ============================================================================ *)

(** Compute the static type of a runtime value.
    This is the bridge between runtime values and static types for type preservation. *)
val type_of_value : value -> Tot brrr_type

(** Helper: compute types for a list of values *)
val type_of_value_list : vlist value -> Tot (list brrr_type)

(** Helper: infer element type for arrays.
    Returns element type if homogeneous, Unknown otherwise. *)
val infer_array_element_type : vlist value -> Tot brrr_type

(** ============================================================================
    INTEGER ARITHMETIC OPERATIONS
    ============================================================================ *)

(** Integer widening: promote narrower type to wider.
    Returns wider type if same signedness, None if incompatible. *)
val int_type_widen : int_type -> int_type -> option int_type

(** Integer addition with type preservation *)
val int_add : v1:value{VInt? v1} -> v2:value{VInt? v2} -> value

(** Integer subtraction with type preservation *)
val int_sub : v1:value{VInt? v1} -> v2:value{VInt? v2} -> value

(** Integer multiplication with type preservation *)
val int_mul : v1:value{VInt? v1} -> v2:value{VInt? v2} -> value

(** Integer division with type preservation.
    Returns VErr on division by zero. *)
val int_div : v1:value{VInt? v1} -> v2:value{VInt? v2} -> value

(** ============================================================================
    TYPE PRESERVATION LEMMAS
    ============================================================================ *)

(** Type preservation for integer addition *)
val int_add_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_add v1 v2) ==> TNumeric? (type_of_value (int_add v1 v2))) /\
    (VErr? (int_add v1 v2) ==> TResult? (type_of_value (int_add v1 v2))))
  [SMTPat (int_add v1 v2)]

(** Type preservation: addition of same-typed integers produces same type *)
val int_add_same_type : v1:value -> v2:value -> ty:int_type ->
  Lemma (requires VInt? v1 /\ VInt? v2 /\ VInt?.ty v1 = ty /\ VInt?.ty v2 = ty)
        (ensures VInt? (int_add v1 v2) /\ VInt?.ty (int_add v1 v2) = ty)
  [SMTPat (int_add v1 v2); SMTPat (VInt?.ty v1)]

(** Type preservation for subtraction *)
val int_sub_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_sub v1 v2) ==> TNumeric? (type_of_value (int_sub v1 v2))) /\
    (VErr? (int_sub v1 v2) ==> TResult? (type_of_value (int_sub v1 v2))))
  [SMTPat (int_sub v1 v2)]

(** Type preservation for multiplication *)
val int_mul_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_mul v1 v2) ==> TNumeric? (type_of_value (int_mul v1 v2))) /\
    (VErr? (int_mul v1 v2) ==> TResult? (type_of_value (int_mul v1 v2))))
  [SMTPat (int_mul v1 v2)]

(** Type preservation for division *)
val int_div_preserves_type : v1:value{VInt? v1} -> v2:value{VInt? v2} ->
  Lemma (ensures
    (VInt? (int_div v1 v2) ==> TNumeric? (type_of_value (int_div v1 v2))) /\
    (VErr? (int_div v1 v2) ==> TResult? (type_of_value (int_div v1 v2))))
  [SMTPat (int_div v1 v2)]

(** ============================================================================
    CANONICAL FORM LEMMAS
    ============================================================================ *)

(** Canonical form for integers *)
val canonical_int : v:value ->
  Lemma (requires TNumeric? (type_of_value v) /\ NumInt? (TNumeric?._0 (type_of_value v)))
        (ensures VInt? v)
  [SMTPat (type_of_value v); SMTPat (TNumeric? (type_of_value v))]

(** Canonical form for floats *)
val canonical_float : v:value ->
  Lemma (requires TNumeric? (type_of_value v) /\ NumFloat? (TNumeric?._0 (type_of_value v)))
        (ensures VFloat? v)
  [SMTPat (type_of_value v); SMTPat (NumFloat? (TNumeric?._0 (type_of_value v)))]

(** Canonical form for booleans *)
val canonical_bool : v:value ->
  Lemma (requires type_of_value v == TPrim PBool)
        (ensures VBool? v)
  [SMTPat (type_of_value v)]

(** Canonical form for unit *)
val canonical_unit : v:value ->
  Lemma (requires type_of_value v == TPrim PUnit)
        (ensures v == VUnit)
  [SMTPat (type_of_value v)]

(** Canonical form for strings *)
val canonical_string : v:value ->
  Lemma (requires type_of_value v == TPrim PString)
        (ensures VString? v)
  [SMTPat (type_of_value v)]

(** Canonical form for chars *)
val canonical_char : v:value ->
  Lemma (requires type_of_value v == TPrim PChar)
        (ensures VChar? v)
  [SMTPat (type_of_value v)]

(** Canonical form for tuples *)
val canonical_tuple : v:value ->
  Lemma (requires TTuple? (type_of_value v))
        (ensures VTuple? v)
  [SMTPat (type_of_value v); SMTPat (TTuple? (type_of_value v))]

(** Canonical form for Some values *)
val canonical_some : v:value ->
  Lemma (requires TWrap? (type_of_value v) /\
                  TWrap?._0 (type_of_value v) = WOption /\
                  not (TPrim? (TWrap?._1 (type_of_value v)) &&
                       TPrim?._0 (TWrap?._1 (type_of_value v)) = PUnknown))
        (ensures VSome? v)

(** ============================================================================
    TUPLE TYPE PROJECTION LEMMAS
    ============================================================================ *)

(** type_of_value_list length preservation *)
val type_of_value_list_length : vs:vlist value ->
  Lemma (ensures length (type_of_value_list vs) = length vs)
  [SMTPat (type_of_value_list vs)]

(** Tuple type projection: nth element of value list corresponds to nth type *)
val tuple_proj_type : vs:vlist value -> i:nat{i < length vs} ->
  Lemma (ensures type_of_value (index vs i) == index (type_of_value_list vs) i)
  [SMTPat (type_of_value (index vs i))]

(** Tuple type structure *)
val tuple_type_structure : vs:vlist value ->
  Lemma (ensures type_of_value (VTuple vs) == TTuple (type_of_value_list vs))
  [SMTPat (type_of_value (VTuple vs))]

(** ============================================================================
    ARRAY HOMOGENEITY LEMMAS
    ============================================================================ *)

(** Helper: check if a type is Unknown *)
val is_unknown_type : brrr_type -> bool

(** Homogeneous array lemma *)
val array_homogeneous : vs:vlist value ->
  Lemma (requires not (is_unknown_type (infer_array_element_type vs)))
        (ensures forall (i:nat{i < length vs}).
                   type_eq (type_of_value (index vs i)) (infer_array_element_type vs) = true)

(** Array with single element has that element's type *)
val singleton_array_type : v:value ->
  Lemma (ensures infer_array_element_type [v] == type_of_value v)
  [SMTPat (infer_array_element_type [v])]

(** Empty array has Unknown element type *)
val empty_array_type : unit ->
  Lemma (ensures infer_array_element_type [] == TPrim PUnknown)

(** ============================================================================
    VALUE-TYPE CORRESPONDENCE LEMMAS
    ============================================================================ *)

(** VInt corresponds to TNumeric NumInt *)
val vint_type_correspondence : n:int -> ty:int_type ->
  Lemma (ensures type_of_value (VInt n ty) == TNumeric (NumInt ty))
  [SMTPat (type_of_value (VInt n ty))]

(** VFloat corresponds to TNumeric NumFloat *)
val vfloat_type_correspondence : f:float_repr -> prec:float_prec ->
  Lemma (ensures type_of_value (VFloat f prec) == TNumeric (NumFloat prec))
  [SMTPat (type_of_value (VFloat f prec))]

(** VBool corresponds to TPrim PBool *)
val vbool_type_correspondence : b:bool ->
  Lemma (ensures type_of_value (VBool b) == TPrim PBool)
  [SMTPat (type_of_value (VBool b))]

(** VSome corresponds to TWrap WOption *)
val vsome_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VSome v) == TWrap WOption (type_of_value v))
  [SMTPat (type_of_value (VSome v))]

(** VOk corresponds to TResult with ok type *)
val vok_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VOk v) == TResult (type_of_value v) (TPrim PUnknown))
  [SMTPat (type_of_value (VOk v))]

(** VErr corresponds to TResult with error type *)
val verr_type_correspondence : v:value ->
  Lemma (ensures type_of_value (VErr v) == TResult (TPrim PUnknown) (type_of_value v))
  [SMTPat (type_of_value (VErr v))]

(** ============================================================================
    LITERAL TYPE PRESERVATION LEMMAS
    ============================================================================ *)

(** lit_to_value preserves integer type exactly *)
val lit_to_value_int_type : n:int -> ty:int_type ->
  Lemma (ensures type_of_value (lit_to_value (LitInt n ty)) == TNumeric (NumInt ty))
  [SMTPat (lit_to_value (LitInt n ty))]

(** lit_to_value preserves float precision exactly *)
val lit_to_value_float_type : f:float_repr -> prec:float_prec ->
  Lemma (ensures type_of_value (lit_to_value (LitFloat f prec)) == TNumeric (NumFloat prec))
  [SMTPat (lit_to_value (LitFloat f prec))]

(** lit_to_value for bool produces TPrim PBool *)
val lit_to_value_bool_type : b:bool ->
  Lemma (ensures type_of_value (lit_to_value (LitBool b)) == TPrim PBool)
  [SMTPat (lit_to_value (LitBool b))]

(** lit_to_value for unit produces TPrim PUnit *)
val lit_to_value_unit_type : unit ->
  Lemma (ensures type_of_value (lit_to_value LitUnit) == TPrim PUnit)

(** lit_to_value for string produces TPrim PString *)
val lit_to_value_string_type : s:string ->
  Lemma (ensures type_of_value (lit_to_value (LitString s)) == TPrim PString)
  [SMTPat (lit_to_value (LitString s))]

(** lit_to_value for char produces TPrim PChar *)
val lit_to_value_char_type : c:FStar.Char.char ->
  Lemma (ensures type_of_value (lit_to_value (LitChar c)) == TPrim PChar)
  [SMTPat (lit_to_value (LitChar c))]

(** ============================================================================
    TYPE OF VALUE STRUCTURAL LEMMAS
    ============================================================================ *)

(** type_of_value for VStruct returns TNamed *)
val vstruct_type_is_named : name:type_name -> fields:vlist (string & value) ->
  Lemma (ensures type_of_value (VStruct name fields) == TNamed name)
  [SMTPat (type_of_value (VStruct name fields))]

(** type_of_value for VVariant returns TNamed *)
val vvariant_type_is_named : ty_name:type_name -> var_name:string -> args:vlist value ->
  Lemma (ensures type_of_value (VVariant ty_name var_name args) == TNamed ty_name)
  [SMTPat (type_of_value (VVariant ty_name var_name args))]

(** type_of_value is deterministic *)
val type_of_value_deterministic : v:value ->
  Lemma (ensures type_of_value v == type_of_value v)
  [SMTPat (type_of_value v)]
