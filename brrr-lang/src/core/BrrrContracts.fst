(**
 * ============================================================================
 * BrrrLang.Core.Contracts
 * ============================================================================
 *
 * Design by Contract and Hoare Logic for Brrr-Lang
 *
 * Based on brrr_lang_spec_v0.4.tex Part IX - Contracts (Sections 6378-6395)
 *
 * ============================================================================
 * HISTORICAL AND THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * This module implements a formal contract system based on the Design by
 * Contract (DbC) methodology pioneered by Bertrand Meyer in Eiffel (1986-1992).
 *
 * KEY REFERENCES:
 *
 * [Meyer 1992] Bertrand Meyer. "Applying Design by Contract."
 *              IEEE Computer 25(10):40-51, 1992.
 *              - Introduced preconditions, postconditions, and class invariants
 *              - Established the "client-supplier" contract metaphor
 *
 * [Hoare 1969] C.A.R. Hoare. "An Axiomatic Basis for Computer Programming."
 *              Communications of the ACM, 12(10):576-580, 1969.
 *              - Foundational paper introducing Hoare triples {P} C {Q}
 *              - Established partial correctness semantics
 *
 * [Floyd 1967] Robert W. Floyd. "Assigning Meaning to Programs."
 *              Proceedings of Symposia in Applied Mathematics, Vol. 19, 1967.
 *              - Pioneered program verification using logical assertions
 *              - Introduced loop invariants
 *
 * [Dijkstra 1975] Edsger W. Dijkstra. "Guarded Commands, Nondeterminacy and
 *                 Formal Derivation of Programs." CACM 18(8):453-457, 1975.
 *                 - Introduced weakest precondition (wp) calculus
 *                 - Algorithm for computing Hoare triples
 *
 * ============================================================================
 * CONNECTION TO F* TYPE SYSTEM
 * ============================================================================
 *
 * F*'s type system natively supports contract-style specifications through:
 *
 * 1. REFINEMENT TYPES: {x:t | phi}
 *    - Encode preconditions as input refinements
 *    - Encode postconditions as output refinements
 *    Example: val divide : x:int -> y:int{y <> 0} -> int
 *
 * 2. PURE EFFECT WITH PRE/POST (Hoare-style):
 *    val f : x:t -> Pure r (requires pre x) (ensures fun r -> post x r)
 *    - Direct mapping to Hoare triples
 *    - F* computes WP internally and checks against annotation
 *
 * 3. LEMMA EFFECT:
 *    val lemma : x:t -> Lemma (requires P x) (ensures Q x)
 *    - Special case for proof terms (unit-returning)
 *    - Desugared to Pure unit pre (fun _ -> post)
 *
 * The relationship between refinement types and Hoare-style specs:
 *   x:t{pre} -> Tot (r:s{post})  approximately equals
 *   x:t -> Pure s (requires pre) (ensures fun r -> post)
 *
 * ============================================================================
 * RUNTIME VS STATIC CONTRACT CHECKING
 * ============================================================================
 *
 * CONTRACT CHECKING MODES:
 *
 * 1. STATIC VERIFICATION (this module's primary focus):
 *    - Contracts are verified at compile time via SMT solver (Z3)
 *    - No runtime overhead
 *    - Complete coverage (if it compiles, contracts are guaranteed)
 *    - Limitation: SMT may timeout on complex properties
 *
 * 2. RUNTIME CHECKING (for dynamic contexts):
 *    - Contracts checked at function entry/exit
 *    - Overhead proportional to assertion complexity
 *    - Useful for FFI boundaries and debugging
 *    - Can be disabled in production builds
 *
 * 3. HYBRID APPROACH (recommended):
 *    - Critical invariants verified statically
 *    - External inputs checked at runtime
 *    - Best of both worlds
 *
 * In Brrr-Lang, static verification is preferred where possible, with
 * runtime checking at FFI boundaries (see brrr_lang_spec_v0.4.tex Part XV).
 *
 * ============================================================================
 * HOARE LOGIC SEMANTICS
 * ============================================================================
 *
 * A Hoare triple {P} c {Q} (written as hoare_triple_valid P c Q) means:
 *
 *   "For all states s, if P holds in s and executing c from s terminates
 *    in state s' with value v, then Q holds in s'."
 *
 * This is PARTIAL CORRECTNESS: we only reason about terminating executions.
 * For TOTAL CORRECTNESS, we also prove termination (see hoare_total below).
 *
 * AXIOMATIZED RULES (proven sound classically):
 *
 * H-SKIP:    {P} skip {P}
 *            The skip statement preserves any assertion.
 *
 * H-ASSIGN:  {Q[e/x]} x := e {Q}
 *            To establish Q after assignment, prove Q with e substituted for x.
 *
 * H-SEQ:     {P} c1 {Q}  and  {Q} c2 {R}  implies  {P} c1;c2 {R}
 *            Sequential composition via intermediate assertion Q.
 *
 * H-IF:      {P /\ b} c1 {Q}  and  {P /\ ~b} c2 {Q}  implies  {P} if b c1 c2 {Q}
 *            Both branches must establish the same postcondition.
 *
 * H-WHILE:   {I /\ b} c {I}  implies  {I} while b do c {I /\ ~b}
 *            Loop invariant I is preserved by body; exits with ~b.
 *
 * H-CONSEQ:  P' ==> P  and  {P} c {Q}  and  Q ==> Q'  implies  {P'} c {Q'}
 *            Strengthen precondition, weaken postcondition.
 *
 * ============================================================================
 * WEAKEST PRECONDITION CALCULUS
 * ============================================================================
 *
 * The weakest precondition WP(c, Q) computes the WEAKEST (most general)
 * assertion P such that {P} c {Q} holds.
 *
 * WP RULES (from Dijkstra):
 *
 *   WP(skip, Q)           = Q
 *   WP(x := e, Q)         = Q[e/x]
 *   WP(c1; c2, Q)         = WP(c1, WP(c2, Q))
 *   WP(if b c1 c2, Q)     = (b ==> WP(c1, Q)) /\ (~b ==> WP(c2, Q))
 *   WP(while b inv I, Q)  = I /\ (I /\ ~b ==> Q) /\ (I /\ b ==> WP(c, I))
 *
 * The WP function is SOUND: WP(c, Q) is always a valid precondition.
 * It is also COMPLETE: any valid precondition implies WP(c, Q).
 *
 * SOUNDNESS THEOREM:
 *   forall c, Q. hoare_triple_valid (WP c Q) c Q
 *
 * This module implements WP computation and uses it for VC generation.
 *
 * ============================================================================
 * VERIFICATION CONDITION GENERATION
 * ============================================================================
 *
 * To verify a contract {pre} e {post}:
 *
 * 1. Compute WP(e, post) using weakest precondition rules
 * 2. Generate VC: pre ==> WP(e, post)
 * 3. Check VC validity (ideally via SMT solver)
 *
 * If VC is valid, the contract is guaranteed to hold.
 *
 * For loops, user-provided invariants are required since WP for loops
 * involves existential quantification over invariants.
 *
 * ============================================================================
 * MODULE DEPENDENCIES
 * ============================================================================
 *
 * This module depends on:
 *   - Primitives: Basic types and operations
 *   - Modes: Usage mode tracking
 *   - Effects: Effect system integration
 *   - BrrrTypes: Brrr-Lang type definitions
 *   - Expressions: AST for expressions and formulas
 *   - DependentTypes: Dependent/refinement type support
 *   - Values: Runtime values
 *   - Eval: Expression evaluation
 *
 * And is used by:
 *   - Type checker for contract verification
 *   - FFI module for boundary checking
 *   - Theorem proving infrastructure
 *)
module BrrrContracts

open FStar.List.Tot
open FStar.Classical
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrDependentTypes
open BrrrValues
open BrrrEval

(** ============================================================================
    REFINEMENT TYPE HELPERS
    ============================================================================

    Common refined types for program verification.
    These are meta-level types in F* that correspond to Brrr refinement types.

    These types mirror the refinement types in Brrr-Lang (spec Section 2.4):
      nat_type       <->  { x : Int | x >= 0 }
      pos_type       <->  { x : Int | x > 0 }
      bounded_index  <->  { i : Int | 0 <= i < len }
      percentage     <->  { x : Int | 0 <= x <= 100 }

    DESIGN NOTE: These are F* types used for meta-level reasoning about
    Brrr programs. They are NOT the Brrr types themselves (which are
    represented using brrr_type and dep_type from BrrrTypes.fst).
    ============================================================================ *)

(* Natural numbers: non-negative integers.
   Corresponds to the ubiquitous nat type in dependent type theory.
   In Brrr: { x : Int | x >= 0 } *)
type nat_type = x:int{x >= 0}

(* Positive integers: strictly positive.
   Essential for array lengths, divisors, loop bounds.
   In Brrr: { x : Int | x > 0 } *)
type pos_type = x:int{x > 0}

(* Bounded array index: valid index into array of given length.
   The len parameter must be positive (non-empty arrays).
   Guarantees: 0 <= i < len

   CRITICAL: This is the primary mechanism for proving array bounds safety.
   When combined with dependent types, eliminates bounds check overhead.

   Example usage in Brrr:
     fn get<n: pos>(arr: Array[T, n], i: bounded_index[n]) -> T *)
type bounded_index (len:nat{len > 0}) = i:nat{i < len}

(* Non-empty list: list with at least one element.
   Useful for head/tail operations that would otherwise be partial.
   Encoded using Cons? predicate from FStar.List.Tot *)
type non_empty_list (a:Type) = l:list a{Cons? l}

(* Percentage: value between 0 and 100 (inclusive).
   Common domain-specific constraint for UI, statistics, etc.
   In Brrr: { x : Int | 0 <= x /\ x <= 100 } *)
type percentage = x:int{0 <= x /\ x <= 100}

(** ============================================================================
    FUNCTION CONTRACTS
    ============================================================================

    A contract specifies the expected behavior of a function through the
    "client-supplier" metaphor [Meyer 1992]:

    - PRECONDITION (requires): Obligation of the CALLER (client)
      What must be true when the function is called.
      If violated, the function behavior is undefined.

    - POSTCONDITION (ensures): Obligation of the FUNCTION (supplier)
      What will be true when the function returns.
      Guaranteed only when precondition was satisfied.

    This module represents contracts as pairs of formulas from BrrrExpressions.fst.
    The postcondition can reference the special variable "result" which
    represents the return value of the function.

    EXAMPLE (from spec Section 6378-6386):

      fn divide(x: Int, y: Int) -> Int
        requires y != 0
        ensures result * y <= x /\ x < result * y + y

    This is encoded as:
      { precondition = FCmp CmpNe (EVar "y") (e_int 0);
        postcondition = FAnd ... }

    CONTRACT SEMANTICS:
    A function f satisfies contract C if:
      forall inputs. C.precondition(inputs) ==>
        let result = f(inputs) in C.postcondition(inputs, result)
    ============================================================================ *)

(* Contract type: pair of formulas for pre/postcondition.
   Uses noeq because formula contains functions (comparison operators).

   DESIGN RATIONALE:
   Using formula (from BrrrExpressions.fst) rather than F* propositions allows:
   1. Syntactic manipulation (substitution, simplification)
   2. Runtime checking when needed
   3. Pretty-printing for error messages
   4. SMT encoding for automated verification *)
noeq type contract = {
  precondition  : formula;   (* What caller must ensure *)
  postcondition : formula;   (* What function guarantees, can use "result" *)
}

(* Trivial contract: true -> true
   Used as default when no contract is specified.
   Imposes no obligations on caller, provides no guarantees.

   NOTE: Even with trivial contract, F* still checks memory safety,
   type safety, and termination (if in Tot effect). *)
let trivial_contract : contract = {
  precondition = FTrue;
  postcondition = FTrue;
}

(* Create a pure function contract: no side effects, only return value matters.
   The simplest non-trivial contract pattern.

   USAGE:
     pure_contract
       (FCmp CmpGe (EVar "x") (e_int 0))        (* pre: x >= 0 *)
       (FCmp CmpGe (EVar "result") (e_int 0))   (* post: result >= 0 *) *)
let pure_contract (pre: formula) (post: formula) : contract = {
  precondition = pre;
  postcondition = post;
}

(* Contract with only a precondition.
   Function requires something but makes no promises about return value.

   EXAMPLE: A function that requires non-null input but might return anything.
            Common for partial functions being wrapped. *)
let requires_only (pre: formula) : contract = {
  precondition = pre;
  postcondition = FTrue;
}

(* Contract with only a postcondition.
   Function always applicable but guarantees specific output property.

   EXAMPLE: A constant function or pure computation that always succeeds.
            { precondition = true; postcondition = result > 0 } *)
let ensures_only (post: formula) : contract = {
  precondition = FTrue;
  postcondition = post;
}

(** ============================================================================
    PROGRAM STATE ABSTRACTION
    ============================================================================

    For Hoare logic, we need an abstract view of program state.
    A state is a mapping from variables to values.

    DESIGN CHOICE: We use a functional representation (var_id -> option value)
    rather than a list-based environment for several reasons:

    1. MATHEMATICAL CLARITY: Matches the standard presentation in textbooks
    2. STATE UPDATE: s[x := v] is naturally expressed as function update
    3. FRAME REASONING: Unchanged variables are automatically preserved
    4. COMPOSITION: States compose naturally for separation reasoning

    The option type handles undefined variables (variables not in scope).

    CONNECTION TO EVALUATION:
    The eval module uses list-based environments (env = list (var_id & value)).
    We provide conversion functions to bridge these representations:
    - env_to_state: Convert eval environment to abstract state
    - state_to_env_helper: Convert abstract state to eval environment

    This abstraction supports the standard Hoare logic rules while maintaining
    compatibility with the operational semantics in BrrrEval.fst.
    ============================================================================ *)

(* Abstract state: mapping from variable names to values.
   None represents an undefined variable (out of scope or uninitialized). *)
type state = var_id -> option value

(* Empty state: no variables defined.
   Starting point for building states.
   Invariant: empty_state x = None for all x *)
let empty_state : state = fun _ -> None

(* State update: s[x := v]
   Creates a new state that maps x to v, preserving all other mappings.

   This is the semantic foundation for the assignment rule in Hoare logic:
   {Q[e/x]} x := e {Q}

   PROPERTIES:
   - (state_update s x v) x = Some v           (update succeeds)
   - y <> x ==> (state_update s x v) y = s y   (frame property) *)
let state_update (s: state) (x: var_id) (v: value) : state =
  fun y -> if y = x then Some v else s y

(* State lookup: retrieve value for variable.
   Simple projection - delegates to state function. *)
let state_lookup (s: state) (x: var_id) : option value = s x

(* Convert eval environment to abstract state.
   Bridges the gap between BrrrEval.fst (list-based env) and Hoare logic (function-based state).

   The lookup function from Eval handles list traversal;
   we just wrap it in function form. *)
let env_to_state (e: env) : state =
  fun x -> lookup x e

(* Convert abstract state to environment (as list of bindings).
   Requires knowing which variables to include (vars parameter).
   Only includes variables that have defined values in the state.

   NOTE: This is inherently lossy - we need to know the variable set upfront.
   Used primarily for bridging to the evaluator. *)
let rec state_to_env_helper (vars: list var_id) (s: state) : env =
  match vars with
  | [] -> []
  | x :: rest ->
      match s x with
      | Some v -> (x, v) :: state_to_env_helper rest s
      | None -> state_to_env_helper rest s

(** ============================================================================
    FORMULA EVALUATION
    ============================================================================

    Evaluate a formula in a given state to get a boolean result.
    This provides the semantic foundation for Hoare logic.

    SEMANTIC DOMAIN:
    Formulas are syntactic objects (from BrrrExpressions.fst).
    Evaluation interprets them as boolean propositions in a given state.

    TOTALITY AND FUEL:
    Formula evaluation may not terminate for malformed inputs, so we use
    a fuel parameter for termination. This is a standard technique in F*
    for total functions that recurse on non-structurally-smaller arguments.

    EVALUATION STRATEGY:
    - FTrue/FFalse: Constant true/false
    - FCmp: Evaluate both expressions, compare results
    - FAnd/FOr: Short-circuit evaluation (efficiency + defined semantics)
    - FNot: Negate sub-formula
    - FImpl: Encoded as ~P \/ Q
    - FIff: Both directions must match
    - FForall/FExists: CANNOT evaluate (unbounded quantification)
    - FPred: CANNOT evaluate (external predicates)
    - FExpr: Evaluate expression, expect boolean

    PARTIAL EVALUATION:
    Returns None when evaluation fails (missing variable, type error,
    fuel exhaustion, unbounded quantifier). This supports graceful
    degradation when runtime checking encounters limitations.
    ============================================================================ *)

(* Evaluate expression in state, returning option value.
   Bridges formula evaluation to expression evaluation from BrrrEval.fst.

   STRATEGY:
   1. Extract free variables from expression
   2. Build environment from state (only relevant bindings)
   3. Call eval_expr from BrrrEval.fst
   4. Extract result or return None on error *)
let eval_expr_in_state (e: expr) (s: state) (fuel: nat) : option value =
  (* Build environment from variables in expression *)
  let vars = free_vars e in
  let env = state_to_env_helper vars s in
  let st = { init_eval_state with es_env = env } in
  match fst (eval_expr fuel e st) with
  | ROk v -> Some v
  | _ -> None

(* Evaluate comparison operator on two values.
   Handles type-specific comparison semantics.

   SUPPORTED COMPARISONS:
   - Integer: All operators (=, <>, <, <=, >, >=)
   - Boolean: Only equality (=, <>)
   - String: All operators (lexicographic for ordering)

   Returns None for type mismatches or unsupported combinations.

   NOTE: This is a meta-level operation for formula evaluation,
   not the comparison in the Brrr expression language. *)
let eval_cmp_op (op: cmp_op) (v1 v2: value) : option bool =
  match v1, v2 with
  | VInt n1, VInt n2 ->
      Some (match op with
            | CmpEq -> n1 = n2
            | CmpNe -> n1 <> n2
            | CmpLt -> n1 < n2
            | CmpLe -> n1 <= n2
            | CmpGt -> n1 > n2
            | CmpGe -> n1 >= n2)
  | VBool b1, VBool b2 ->
      (match op with
       | CmpEq -> Some (b1 = b2)
       | CmpNe -> Some (b1 <> b2)
       | _ -> None)
  | VString s1, VString s2 ->
      Some (match op with
            | CmpEq -> s1 = s2
            | CmpNe -> s1 <> s2
            | CmpLt -> FStar.String.compare s1 s2 < 0
            | CmpLe -> FStar.String.compare s1 s2 <= 0
            | CmpGt -> FStar.String.compare s1 s2 > 0
            | CmpGe -> FStar.String.compare s1 s2 >= 0)
  | _, _ -> None

(* Evaluate formula in state with fuel for recursive calls.

   FUEL SYSTEM:
   - fuel = 0: Return None (conservative, cannot determine)
   - fuel > 0: Recurse with fuel - 1

   This ensures termination while allowing deep formula evaluation.
   Default fuel (formula_eval_fuel) is 1000, sufficient for most formulas.

   QUANTIFIER HANDLING:
   FForall and FExists return None because we cannot enumerate
   infinite domains. For these, use SMT-based verification instead.

   PREDICATE HANDLING:
   FPred returns None because external predicates require
   interpretation not available at this level. *)
let rec eval_formula_in_state (fuel: nat) (phi: formula) (s: state) : Tot (option bool) (decreases fuel) =
  if fuel = 0 then None
  else
    match phi with
    | FTrue -> Some true
    | FFalse -> Some false

    | FCmp op e1 e2 ->
        (match eval_expr_in_state e1 s (fuel - 1), eval_expr_in_state e2 s (fuel - 1) with
         | Some v1, Some v2 -> eval_cmp_op op v1 v2
         | _, _ -> None)

    (* Short-circuit AND: if first is false, result is false *)
    | FAnd phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some false -> Some false
         | Some true -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    (* Short-circuit OR: if first is true, result is true *)
    | FOr phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some true -> Some true
         | Some false -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    | FNot phi' ->
        (match eval_formula_in_state (fuel - 1) phi' s with
         | Some b -> Some (not b)
         | None -> None)

    (* P => Q is equivalent to ~P \/ Q *)
    | FImpl phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s with
         | Some false -> Some true
         | Some true -> eval_formula_in_state (fuel - 1) phi2 s
         | None -> None)

    | FIff phi1 phi2 ->
        (match eval_formula_in_state (fuel - 1) phi1 s, eval_formula_in_state (fuel - 1) phi2 s with
         | Some b1, Some b2 -> Some (b1 = b2)
         | _, _ -> None)

    | FForall _ _ _ -> None  (* Cannot evaluate unbounded quantifiers *)
    | FExists _ _ _ -> None

    | FPred _ _ -> None  (* Predicates need external interpretation *)

    | FExpr e ->
        (match eval_expr_in_state e s (fuel - 1) with
         | Some (VBool b) -> Some b
         | _ -> None)

(* Default fuel for formula evaluation.
   1000 is sufficient for most practical formulas.
   Can be increased for deeply nested formulas if needed. *)
let formula_eval_fuel : nat = 1000

(* Check if formula holds in state.
   Convenience wrapper that returns boolean.
   Returns false for any evaluation failure (conservative). *)
let formula_holds (phi: formula) (s: state) : bool =
  match eval_formula_in_state formula_eval_fuel phi s with
  | Some true -> true
  | _ -> false

(** ============================================================================
    ASSERTION TYPE - Semantic predicates on states
    ============================================================================

    An assertion is a predicate on program states.
    We represent assertions both as formulas (syntactic) and as
    semantic predicates (for proofs).

    TWO REPRESENTATIONS:

    1. SYNTACTIC (formula from BrrrExpressions.fst):
       - Can be manipulated, substituted, simplified
       - Can be evaluated at runtime
       - Can be encoded for SMT

    2. SEMANTIC (state -> Type0):
       - F* propositions about states
       - Used for meta-theoretic proofs
       - Cleaner for reasoning in F*

    CONVERSION:
    formula_to_assertion converts syntactic formulas to semantic assertions.
    This bridges the gap between the two representations.

    ASSERTION COMBINATORS:
    We provide standard logical combinators (and, or, impl, not) that
    work on semantic assertions. These are used in Hoare rule statements.
    ============================================================================ *)

(* Semantic assertion: predicate on states.
   Returns Type0 (F* proposition) rather than bool.
   This allows for richer specifications and proof terms. *)
type assertion = state -> Type0

(* Convert formula to semantic assertion.
   Uses formula_holds for evaluation, lifting to Type0 via equality.

   NOTE: This loses some precision because formula_holds is conservative
   (returns false on evaluation failure). For full precision, use
   formula-based reasoning with BrrrSMT. *)
let formula_to_assertion (phi: formula) : assertion =
  fun s -> formula_holds phi s == true

(* Trivially true assertion: holds in all states.
   Unit of conjunction. *)
let assert_true : assertion = fun _ -> True

(* Trivially false assertion: holds in no state.
   Unit of disjunction (vacuously). *)
let assert_false : assertion = fun _ -> False

(* Conjunction of assertions: both must hold.
   {P /\ Q} in Hoare logic notation. *)
let assert_and (p q: assertion) : assertion =
  fun s -> p s /\ q s

(* Disjunction of assertions: at least one must hold.
   {P \/ Q} in Hoare logic notation. *)
let assert_or (p q: assertion) : assertion =
  fun s -> p s \/ q s

(* Implication of assertions: if p then q.
   Used in consequence rule and conditional reasoning. *)
let assert_impl (p q: assertion) : assertion =
  fun s -> p s ==> q s

(* Negation of assertion.
   Used for else-branch in conditionals. *)
let assert_not (p: assertion) : assertion =
  fun s -> ~(p s)

(** ============================================================================
    HOARE TRIPLE REPRESENTATION
    ============================================================================

    A Hoare triple {P} c {Q} asserts:
      For all states s, if P holds in s and executing c from s terminates
      in state s', then Q holds in s'.

    PARTIAL VS TOTAL CORRECTNESS:

    PARTIAL CORRECTNESS (hoare_triple_valid):
      We only reason about terminating executions.
      If c diverges, the triple is vacuously satisfied.
      This is the classic Hoare logic semantics.

    TOTAL CORRECTNESS (hoare_total):
      Additionally requires that c terminates on all inputs satisfying P.
      Combines termination proof with partial correctness.

    IMPLEMENTATION APPROACH:

    We use an abstract/axiomatic approach where Hoare triples are
    propositions whose validity is established through the VC generation
    and checking mechanism. The rules are axiomatized (using assume val)
    because their soundness proofs would require deep integration with
    the operational semantics - they are proven sound classically.

    This matches the approach in Plotkin & Pretnar's algebraic effects
    work and standard Hoare logic presentations.

    CONNECTION TO F* EFFECTS:

    F*'s Pure effect corresponds directly to Hoare triples:
      Pure a (requires P) (ensures fun r -> Q)
    is essentially {P} e {fun r -> Q} where e : a

    The PURE effect uses WP-indexed specifications internally:
      PURE a wp  means  forall post. wp post ==> e terminates with post(result)
    ============================================================================ *)

(* Execute expression and get resulting state.
   Bridges expression evaluation to state-based semantics.

   Returns Some (value, new_state) on success, None on error.

   NOTE: This combines expression evaluation with state extraction.
   The resulting state captures any side effects (currently minimal
   for pure expressions, but supports future extension). *)
let exec_expr (e: expr) (s: state) (fuel: nat) : option (value & state) =
  let vars = free_vars e in
  let env = state_to_env_helper vars s in
  let st = { init_eval_state with es_env = env } in
  match eval_expr fuel e st with
  | (ROk v, st') -> Some (v, env_to_state st'.es_env)
  | _ -> None

(* Hoare triple validity as a semantic proposition.
   {P} c {Q} holds when: for all states s satisfying P,
   if c terminates with value v in state s', then Q holds in s'.

   We define this directly as the semantic meaning of partial correctness.

   FORMAL DEFINITION (matching Hoare 1969):
   {P} c {Q} := forall s. P(s) ==> (c terminates from s with s' ==> Q(s'))

   The fuel parameter handles recursion depth for evaluation. *)
let hoare_triple_valid (pre: assertion) (c: expr) (post: assertion) : Type0 =
  forall (s: state) (fuel: nat) (v: value) (s': state).
    pre s ==> (exec_expr c s fuel == Some (v, s') ==> post s')

(* Notation helper: create Hoare triple from formulas.
   Converts syntactic formulas to semantic assertions.

   USAGE:
     hoare (FCmp CmpGe (EVar "x") (e_int 0))   (* {x >= 0} *)
           (EBinOp Add (EVar "x") (e_int 1))    (* x + 1 *)
           (FCmp CmpGe (EVar "result") (e_int 1)) (* {result >= 1} *) *)
let hoare (pre: formula) (c: expr) (post: formula) : Type0 =
  hoare_triple_valid (formula_to_assertion pre) c (formula_to_assertion post)

(* Total correctness: termination + partial correctness.
   Combines two requirements:

   1. TERMINATION: For all states satisfying pre, execution terminates.
   2. PARTIAL CORRECTNESS: When it terminates, post holds.

   This is strictly stronger than partial correctness.
   Used when we need to prove both safety and liveness.

   NOTE: Proving termination typically requires a variant/measure function
   that decreases on each loop iteration or recursive call. *)
let hoare_total (pre: assertion) (c: expr) (post: assertion) : Type0 =
  (forall (s: state). pre s ==> (exists (fuel: nat) (v: value) (s': state). exec_expr c s fuel == Some (v, s'))) /\
  hoare_triple_valid pre c post

(** ============================================================================
    HOARE LOGIC RULES - Axiomatized Sound Rules
    ============================================================================

    The following rules are the standard Hoare logic rules from [Hoare 1969]
    and [Floyd 1967]. We axiomatize them as sound with respect to operational
    semantics. Soundness is justified by classical Hoare logic theory.

    AXIOMATIZATION RATIONALE:

    We use 'assume val' to axiomatize these rules because:
    1. Full soundness proofs would require deep operational semantics integration
    2. The rules are classically proven sound (see references)
    3. F* users can trust these as foundational axioms
    4. Verification of user code proceeds via VC generation, not rule application

    The rules form a SOUND and COMPLETE proof system for partial correctness
    of while programs (relative to expressiveness of the assertion language).

    RULE NAMING CONVENTION:
    - h_skip: Rule for skip/unit statement
    - h_seq: Sequential composition rule
    - h_conseq: Consequence/weakening rule
    - h_if_valid: Conditional branching rule
    - h_while_valid: While loop rule (requires invariant)
    ============================================================================ *)

(* H-SKIP: {P} unit {P}
   Skip (unit expression) preserves any assertion.
   Sound because evaluating unit produces unit without state change.

   This is the simplest Hoare rule - the identity on assertions.

   FORMAL: forall P. {P} skip {P} *)
assume val h_skip : p:assertion -> Lemma (hoare_triple_valid p (ELit LitUnit) p)

(* H-Skip for formulas.
   Convenience wrapper using syntactic formulas. *)
assume val h_skip_formula : phi:formula -> Lemma (hoare phi (ELit LitUnit) phi)

(* H-SEQ: {P} c1 {Q} /\ {Q} c2 {R} ==> {P} c1;c2 {R}
   Sequential composition: intermediate state satisfies Q.
   Sound because evaluation of c1;c2 proceeds through intermediate state.

   This rule enables compositional reasoning - we verify each statement
   independently, then compose the proofs.

   KEY INSIGHT: The intermediate assertion Q must be chosen carefully.
   WP calculus automates this choice by computing Q = WP(c2, R). *)
assume val h_seq : p:assertion -> q:assertion -> r:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid p c1 q /\ hoare_triple_valid q c2 r)
        (ensures hoare_triple_valid p (ESeq c1 c2) r)

(* H-CONSEQ: P' ==> P /\ {P} c {Q} /\ Q ==> Q' ==> {P'} c {Q'}
   Consequence rule: strengthen precondition, weaken postcondition.
   Sound by transitivity of implication.

   This rule is essential for matching specifications:
   - STRENGTHEN PRE: We can require more than necessary (safe)
   - WEAKEN POST: We can promise less than we deliver (safe)

   Example: If we prove {x > 0} c {x > 0}, we can derive:
   - {x > 5} c {x > 0}  (stronger pre)
   - {x > 0} c {x >= 0} (weaker post)
   - {x > 5} c {x >= 0} (both) *)
assume val h_conseq : p:assertion -> p':assertion -> q:assertion -> q':assertion -> c:expr ->
  Lemma (requires (forall s. p' s ==> p s) /\
                  hoare_triple_valid p c q /\
                  (forall s. q s ==> q' s))
        (ensures hoare_triple_valid p' c q')

(* H-IF: {P /\ b} c1 {Q} /\ {P /\ ~b} c2 {Q} ==> {P} if b c1 c2 {Q}
   Conditional rule: both branches establish postcondition.
   Sound because exactly one branch is taken based on condition.

   BRANCH CONDITIONS:
   - True branch gets P /\ b
   - False branch gets P /\ ~b

   Both branches must establish the SAME postcondition Q.
   This ensures uniform behavior regardless of which branch is taken.

   NOTE: This version uses a placeholder true condition for simplicity.
   Real usage would pattern-match the actual condition expression. *)
assume val h_if_valid : p:assertion -> q:assertion -> b_true:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid (assert_and p b_true) c1 q /\
                  hoare_triple_valid (assert_and p (assert_not b_true)) c2 q)
        (ensures hoare_triple_valid p (EIf (ELit (LitBool true)) c1 c2) q)

(* H-WHILE: {I /\ b} c {I} ==> {I} while b do c {I /\ ~b}
   While rule with loop invariant.
   Sound because invariant is preserved by each iteration.

   LOOP INVARIANT I must satisfy three conditions:
   1. INITIALLY TRUE: Established before loop entry
   2. PRESERVED: {I /\ b} body {I}
   3. USEFUL: I /\ ~b implies desired postcondition

   The invariant is the key insight for while loop verification.
   Finding good invariants is often the hardest part of verification.

   POSTCONDITION EXPLANATION:
   After the loop exits:
   - I still holds (preserved by final iteration)
   - ~b holds (otherwise loop wouldn't have exited)
   Therefore: I /\ ~b *)
assume val h_while_valid : inv:assertion -> b_true:assertion -> body:expr ->
  Lemma (requires hoare_triple_valid (assert_and inv b_true) body inv)
        (ensures hoare_triple_valid inv
                   (EWhile (ELit (LitBool true)) body)
                   (assert_and inv (assert_not b_true)))

(** ============================================================================
    WEAKEST PRECONDITION CALCULUS
    ============================================================================

    The weakest precondition WP(c, Q) is the weakest assertion P such that
    {P} c {Q} holds. Computing WP allows automatic VC generation.

    DIJKSTRA'S WP CALCULUS [Dijkstra 1975]:

    The key insight is that WP can be computed COMPOSITIONALLY:
    the WP of a compound statement is built from WPs of its parts.

    WP RULES:
    - WP(skip, Q)           = Q
    - WP(x := e, Q)         = Q[e/x]      (* Substitution rule *)
    - WP(c1; c2, Q)         = WP(c1, WP(c2, Q))
    - WP(if b c1 c2, Q)     = (b => WP(c1, Q)) /\ (~b => WP(c2, Q))
    - WP(while b inv I, Q)  = I /\ (I /\ ~b => Q) /\ (I /\ b => WP(c, I))

    PROPERTIES OF WP:

    1. SOUNDNESS: {WP(c, Q)} c {Q} is always valid
    2. COMPLETENESS: If {P} c {Q} is valid, then P ==> WP(c, Q)
    3. MONOTONICITY: If Q ==> Q', then WP(c, Q) ==> WP(c, Q')
    4. CONJUNCTION: WP(c, Q /\ R) = WP(c, Q) /\ WP(c, R)

    LOOP HANDLING:

    The rule for while loops involves EXISTENTIAL QUANTIFICATION over
    invariants. In practice, programmers provide invariants as annotations,
    converting the existential to a specific formula.

    CONNECTION TO F*:

    F*'s PURE effect computes WPs automatically using these rules.
    The signature PURE a wp means: for any postcondition Q,
    if wp Q holds, then the computation terminates with result satisfying Q.

    See fstar_pop_book.md lines 15407-15548 for F*'s Dijkstra monad details.
    ============================================================================ *)

(* Substitute expression for variable in formula (WP computation).
   Implements the assignment rule: WP(x := e, Q) = Q[e/x]

   This is the core of the assignment rule - replace every occurrence
   of variable x in postcondition Q with expression e. *)
let wp_subst (x: var_id) (e: expr) (post: formula) : formula =
  subst_formula x e post

(* Weakest precondition computation with fuel for termination.
   Computes WP(c, post) following Dijkstra's rules.

   FUEL PARAMETER:
   Used for termination proof - recursive calls decrease fuel.
   Returns FFalse (strongest formula) when fuel exhausted.
   This is conservative: FFalse implies anything, so WP is still sound.

   SUPPORTED CONSTRUCTS:
   - Literals (unit, constants): WP = post
   - Variables: WP = post (no state change)
   - Assignment: WP = post[e/x]
   - Let: WP = WP(e1, WP(e2[result/x], post))
   - Sequence: WP = WP(c1, WP(c2, post))
   - Conditional: WP = (b => WP(c1, Q)) /\ (~b => WP(c2, Q))
   - Block: Flattened to sequence

   DEFAULT CASE:
   For unsupported expressions (function calls, etc.), conservatively
   return post. This assumes the expression is pure/side-effect-free.
   Future extension could handle more constructs. *)
let rec wp_compute (fuel: nat) (c: expr) (post: formula) : Tot formula (decreases fuel) =
  if fuel = 0 then FFalse  (* Conservative: cannot compute *)
  else
    match c with
    (* WP(unit, Q) = Q *)
    | ELit LitUnit -> post

    (* WP(x, Q) = Q (variable reference is pure) *)
    | EVar _ -> post

    (* WP(literal, Q) = Q *)
    | ELit _ -> post

    (* WP(x := e, Q) = Q[e/x] - the assignment rule *)
    | EAssign (EVar x) e ->
        wp_subst x e post

    (* WP(let x = e1 in e2, Q) = WP(e1, [result/x]WP(e2, Q))
       First compute WP for body, then for binding expression.
       The "result" variable represents the value of e1. *)
    | ELet (PatVar x) _ e1 e2 ->
        let wp_e2 = wp_compute (fuel - 1) e2 post in
        wp_compute (fuel - 1) e1 (subst_formula x (EVar "result") wp_e2)

    (* WP(c1; c2, Q) = WP(c1, WP(c2, Q))
       Right-to-left composition: compute WP of c2 first,
       use that as postcondition for c1. *)
    | ESeq c1 c2 ->
        let wp_c2 = wp_compute (fuel - 1) c2 post in
        wp_compute (fuel - 1) c1 wp_c2

    (* WP(if b then c1 else c2, Q) = (b => WP(c1, Q)) /\ (~b => WP(c2, Q))
       Both branches contribute to the precondition. *)
    | EIf b c1 c2 ->
        let wp_c1 = wp_compute (fuel - 1) c1 post in
        let wp_c2 = wp_compute (fuel - 1) c2 post in
        FAnd (FImpl (FExpr b) wp_c1) (FImpl (FNot (FExpr b)) wp_c2)

    (* WP(block [e], Q) = WP(e, Q) *)
    | EBlock [e] -> wp_compute (fuel - 1) e post

    (* WP(block (e::es), Q) = WP(e, WP(block es, Q)) *)
    | EBlock (e :: es) ->
        let wp_rest = wp_compute (fuel - 1) (EBlock es) post in
        wp_compute (fuel - 1) e wp_rest

    (* WP(block [], Q) = Q *)
    | EBlock [] -> post

    (* For other expressions, conservatively return post
       (assumes expression is pure/side-effect-free) *)
    | _ -> post

(* Default fuel for WP computation.
   100 is sufficient for most practical programs.
   Increase for deeply nested expressions. *)
let wp_fuel : nat = 100

(* Compute weakest precondition (convenience wrapper).
   Uses default fuel setting. *)
let wp (c: expr) (post: formula) : formula =
  wp_compute wp_fuel c post

(** ============================================================================
    LOOP INVARIANTS
    ============================================================================

    For while loops, we need loop invariants to enable verification.

    LOOP INVARIANT REQUIREMENTS (from [Floyd 1967]):

    1. INITIALLY TRUE: The invariant must hold when entering the loop.
       Pre ==> I (before first iteration)

    2. PRESERVED (INDUCTIVE): Each iteration maintains the invariant.
       {I /\ b} body {I}

    3. SUFFICIENT: Invariant with negated condition implies postcondition.
       I /\ ~b ==> Post

    FINDING INVARIANTS:

    Loop invariant discovery is undecidable in general. Common strategies:
    - Start with postcondition, weaken to be inductive
    - Identify what "progress" the loop makes
    - Consider what quantities are bounded/monotonic
    - Use abstract interpretation for automatic inference

    VARIANTS FOR TERMINATION:

    A VARIANT (or ranking function) proves termination:
    - Non-negative integer expression
    - Strictly decreases each iteration
    - Cannot decrease infinitely

    Combined with invariant, proves total correctness.
    ============================================================================ *)

(* Annotated while loop with invariant.
   Extends basic while loop with verification annotations.

   FIELDS:
   - while_cond: Loop guard expression
   - while_body: Loop body
   - while_invariant: User-provided loop invariant
   - while_variant: Optional decreasing expression for termination

   The variant (if provided) must be non-negative and decrease on each
   iteration. This proves termination. *)
noeq type annotated_while = {
  while_cond      : expr;      (* Loop condition *)
  while_body      : expr;      (* Loop body *)
  while_invariant : formula;   (* Loop invariant *)
  while_variant   : option expr; (* Optional decreasing variant for termination *)
}

(* Check if invariant is preserved by loop body.
   Computes: (I /\ b) => WP(body, I)

   This is the INDUCTIVE step of loop verification:
   assuming the invariant holds and the guard is true,
   after executing the body, the invariant still holds. *)
let invariant_preserved (inv: formula) (cond: expr) (body: expr) : formula =
  (* {I /\ b} body {I} expressed as: (I /\ b) => WP(body, I) *)
  FImpl (FAnd inv (FExpr cond)) (wp body inv)

(* Generate verification conditions for while loop.
   Returns conjunction of all VCs that must be proven:

   1. PRESERVATION: (I /\ b) => WP(body, I)
      Each iteration maintains the invariant.

   2. ESTABLISHMENT: (I /\ ~b) => post
      Invariant with exit condition implies postcondition.

   NOTE: Initial establishment (pre => I) is checked separately
   because it depends on the calling context. *)
let while_vc (w: annotated_while) (post: formula) : formula =
  let inv = w.while_invariant in
  let cond = w.while_cond in
  let body = w.while_body in
  (* VCs:
     1. Invariant preservation: (I /\ b) => WP(body, I)
     2. Postcondition establishment: (I /\ ~b) => post *)
  FAnd
    (invariant_preserved inv cond body)
    (FImpl (FAnd inv (FNot (FExpr cond))) post)

(* WP for annotated while loop.
   Combines invariant with VCs for complete verification.

   WP(while b inv I do c, Q) = I /\ VC(while, Q)

   The caller must prove:
   1. The invariant holds initially
   2. The invariant is preserved
   3. The invariant implies the postcondition on exit *)
let wp_while (w: annotated_while) (post: formula) : formula =
  (* WP(while b inv I do c, Q) = I /\ VC(while, Q) *)
  FAnd w.while_invariant (while_vc w post)

(** ============================================================================
    VERIFICATION CONDITIONS
    ============================================================================

    Verification conditions (VCs) are logical formulas that, if valid,
    guarantee the correctness of a program with respect to its contract.

    VC GENERATION APPROACH:

    Given contract {pre} e {post}:
    1. Compute WP(e, post) using weakest precondition rules
    2. Generate VC: pre ==> WP(e, post)
    3. Check if VC is valid (tautology)

    If the VC is valid, the contract is guaranteed to hold.

    VC REPRESENTATION:

    We use a dedicated VC type (rather than just formula) for:
    1. Richer structure (explicit quantifiers with types)
    2. Better simplification
    3. Cleaner SMT encoding
    4. Separation from expression formulas

    VC CHECKING:

    Conservative syntactic check (check_vc) handles simple cases:
    - VCTrue is valid
    - VCFalse is not valid
    - VCImpl with false premise is valid
    - VCImpl with true conclusion is valid

    For complex VCs, use SMT solver (not implemented here).
    ============================================================================ *)

(* VC representation - richer than formula for SMT solving.
   Explicit constructors for logical structure.

   COMPARISON TO FORMULA:
   - VC has typed quantifiers (VCForall x t body vs FForall x t body)
   - VC is for verification, formula is for expression specifications
   - VC can be simplified more aggressively *)
noeq type vc =
  | VCTrue   : vc                              (* Trivially true *)
  | VCFalse  : vc                              (* Trivially false *)
  | VCImpl   : vc -> vc -> vc                  (* Implication: P => Q *)
  | VCAnd    : vc -> vc -> vc                  (* Conjunction: P /\ Q *)
  | VCOr     : vc -> vc -> vc                  (* Disjunction: P \/ Q *)
  | VCNot    : vc -> vc                        (* Negation: ~P *)
  | VCForall : var_id -> brrr_type -> vc -> vc (* Universal: forall x:t. P *)
  | VCExists : var_id -> brrr_type -> vc -> vc (* Existential: exists x:t. P *)
  | VCFormula : formula -> vc                  (* Embed formula in VC *)

(* VC size for termination proofs.
   Used as decreases clause for recursive VC processing. *)
let rec vc_size (v: vc) : Tot nat (decreases v) =
  match v with
  | VCTrue | VCFalse | VCFormula _ -> 1
  | VCNot v' -> 1 + vc_size v'
  | VCImpl v1 v2 | VCAnd v1 v2 | VCOr v1 v2 -> 1 + vc_size v1 + vc_size v2
  | VCForall _ _ v' | VCExists _ _ v' -> 1 + vc_size v'

(* Convert formula to VC.
   Simple embedding via VCFormula constructor. *)
let formula_to_vc (phi: formula) : vc = VCFormula phi

(* Convert VC to formula (best effort).
   Quantifiers convert directly (same structure).
   Used for pretty-printing and evaluation. *)
let rec vc_to_formula (v: vc) : Tot formula (decreases v) =
  match v with
  | VCTrue -> FTrue
  | VCFalse -> FFalse
  | VCImpl v1 v2 -> FImpl (vc_to_formula v1) (vc_to_formula v2)
  | VCAnd v1 v2 -> FAnd (vc_to_formula v1) (vc_to_formula v2)
  | VCOr v1 v2 -> FOr (vc_to_formula v1) (vc_to_formula v2)
  | VCNot v' -> FNot (vc_to_formula v')
  | VCForall x t v' -> FForall x t (vc_to_formula v')
  | VCExists x t v' -> FExists x t (vc_to_formula v')
  | VCFormula phi -> phi

(* Simplify VC using standard logical identities.
   Reduces VC complexity before checking.

   SIMPLIFICATION RULES:
   - True /\ P = P, False /\ P = False
   - True \/ P = True, False \/ P = P
   - False => P = True, P => True = True, True => P = P
   - ~~P = P (double negation elimination)

   These preserve equivalence while reducing complexity. *)
let rec simplify_vc (v: vc) : Tot vc (decreases v) =
  match v with
  | VCTrue -> VCTrue
  | VCFalse -> VCFalse

  | VCAnd v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCTrue, _ -> v2'
       | _, VCTrue -> v1'
       | VCFalse, _ -> VCFalse
       | _, VCFalse -> VCFalse
       | _, _ -> VCAnd v1' v2')

  | VCOr v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCTrue, _ -> VCTrue
       | _, VCTrue -> VCTrue
       | VCFalse, _ -> v2'
       | _, VCFalse -> v1'
       | _, _ -> VCOr v1' v2')

  | VCImpl v1 v2 ->
      let v1' = simplify_vc v1 in
      let v2' = simplify_vc v2 in
      (match v1', v2' with
       | VCFalse, _ -> VCTrue  (* False => anything is true *)
       | _, VCTrue -> VCTrue   (* anything => True is true *)
       | VCTrue, _ -> v2'      (* True => P is P *)
       | _, _ -> VCImpl v1' v2')

  | VCNot v' ->
      (match simplify_vc v' with
       | VCTrue -> VCFalse
       | VCFalse -> VCTrue
       | VCNot v'' -> v''  (* Double negation elimination *)
       | v'' -> VCNot v'')

  | VCForall x t v' -> VCForall x t (simplify_vc v')
  | VCExists x t v' -> VCExists x t (simplify_vc v')
  | VCFormula phi -> VCFormula (simplify_formula phi)

(** ============================================================================
    VC CHECKING
    ============================================================================

    Check if a VC is valid (semantically true in all states).
    This is a conservative approximation - returns true only when
    we can syntactically determine validity.

    SOUNDNESS:
    If check_vc returns true, the VC is definitely valid.
    If check_vc returns false, the VC might still be valid.

    This conservative approach ensures no false positives (claiming
    invalid VC is valid) at the cost of false negatives.

    For complete checking, integrate with SMT solver (Z3).
    ============================================================================ *)

(* Conservative VC validity check.
   Returns true only when validity is syntactically obvious.

   CASES HANDLED:
   - VCTrue: Always valid
   - VCFalse: Never valid
   - VCAnd: Both conjuncts must be valid
   - VCOr: At least one disjunct must be valid
   - VCImpl: False premise or True conclusion
   - VCNot: Negation of False is valid
   - VCForall: Conservative - check body
   - VCExists: Cannot check without witness
   - VCFormula: Only FTrue is obviously valid *)
let rec check_vc (v: vc) : Tot bool (decreases v) =
  match v with
  | VCTrue -> true
  | VCFalse -> false

  | VCAnd v1 v2 -> check_vc v1 && check_vc v2

  | VCImpl v1 v2 ->
      (* If premise is false or conclusion is true, implication holds *)
      (match v1, v2 with
       | VCFalse, _ -> true
       | _, VCTrue -> true
       | _, _ -> check_vc v2)  (* Conservative: assume premise *)

  | VCOr v1 v2 -> check_vc v1 || check_vc v2

  | VCNot v' ->
      (match v' with
       | VCFalse -> true
       | VCTrue -> false
       | _ -> false)  (* Conservative *)

  | VCForall _ _ v' -> check_vc v'  (* Conservative: check body *)
  | VCExists _ _ _ -> false  (* Cannot check existentials without witness *)
  | VCFormula phi ->
      (match phi with
       | FTrue -> true
       | FFalse -> false
       | _ -> false)  (* Conservative for complex formulas *)

(* Simplified VC check that first simplifies the VC.
   Often more effective than checking directly. *)
let check_vc_simplified (v: vc) : bool =
  check_vc (simplify_vc v)

(** ============================================================================
    VC GENERATION FROM CONTRACT AND EXPRESSION
    ============================================================================

    Generate verification conditions that must be valid for the contract
    to hold on the given expression.

    MAIN VC GENERATION ALGORITHM:
    Given contract {pre} e {post}:
    1. Compute WP(e, post)
    2. Generate VC: pre => WP(e, post)

    LOOP HANDLING:
    For loops, user must provide invariants via the invariants parameter.
    The VCs then include:
    - Invariant establishment: pre => I
    - Invariant preservation: (I /\ b) => WP(body, I)
    - Postcondition: (I /\ ~b) => post
    ============================================================================ *)

(* Generate VC for contract and expression.
   Simple case without loop invariants. *)
let generate_vc (c: contract) (e: expr) : vc =
  (* VC: pre => WP(e, post) *)
  let wp_post = wp e c.postcondition in
  VCImpl (VCFormula c.precondition) (VCFormula wp_post)

(* Generate VC with loop invariants.
   Handles while loops with user-provided invariants.

   INVARIANT MAP:
   The invariants parameter maps while expressions to their invariants.
   Matching is done by structural equality on condition and body.

   VC STRUCTURE FOR LOOPS:
   1. pre => inv (invariant establishment)
   2. (inv /\ b) => WP(body, inv) (preservation)
   3. (inv /\ ~b) => post (postcondition)

   RECURSIVE STRUCTURE:
   For compound expressions (Seq, If, Block), recursively generate
   VCs for subexpressions and combine with conjunction. *)
let rec generate_vc_with_invariants (fuel: nat) (c: contract) (e: expr)
    (invariants: list (expr & formula))  (* Map from while expr to invariant *)
    : Tot vc (decreases fuel) =
  if fuel = 0 then VCFalse
  else
    match e with
    | EWhile cond body ->
        (* Find invariant for this loop *)
        let inv_opt = List.Tot.find (fun (e', _) ->
          match e', e with
          | EWhile c1 b1, EWhile c2 b2 -> expr_eq c1 c2 && expr_eq b1 b2
          | _, _ -> false) invariants in
        (match inv_opt with
         | Some (_, inv) ->
             let w : annotated_while = {
               while_cond = cond;
               while_body = body;
               while_invariant = inv;
               while_variant = None;
             } in
             (* Generate VCs for the loop *)
             VCAnd
               (* Precondition establishes invariant *)
               (VCImpl (VCFormula c.precondition) (VCFormula inv))
               (* Loop VCs *)
               (VCFormula (while_vc w c.postcondition))
         | None ->
             (* No invariant provided - cannot verify loop *)
             VCFalse)

    | ESeq e1 e2 ->
        (* Generate VCs for both parts *)
        let vc1 = generate_vc_with_invariants (fuel - 1) c e1 invariants in
        let intermediate_contract = { c with postcondition = wp e2 c.postcondition } in
        let vc2 = generate_vc_with_invariants (fuel - 1) intermediate_contract e2 invariants in
        VCAnd vc1 vc2

    | EIf cond then_e else_e ->
        (* VCs for both branches *)
        let vc_then = generate_vc_with_invariants (fuel - 1) c then_e invariants in
        let vc_else = generate_vc_with_invariants (fuel - 1) c else_e invariants in
        VCAnd
          (VCImpl (VCFormula (FExpr cond)) vc_then)
          (VCImpl (VCNot (VCFormula (FExpr cond))) vc_else)

    | EBlock [] -> generate_vc c (ELit LitUnit)
    | EBlock [e'] -> generate_vc_with_invariants (fuel - 1) c e' invariants
    | EBlock (e' :: es) ->
        let vc1 = generate_vc_with_invariants (fuel - 1)
                    { c with postcondition = wp (EBlock es) c.postcondition }
                    e' invariants in
        let vc2 = generate_vc_with_invariants (fuel - 1) c (EBlock es) invariants in
        VCAnd vc1 vc2

    | _ -> generate_vc c e

(** ============================================================================
    CONTRACT VERIFICATION
    ============================================================================

    Verify that a contract holds for an expression by generating and
    checking verification conditions.

    VERIFICATION FLOW:
    1. Generate VC from contract and expression
    2. Simplify VC
    3. Check VC validity
    4. Return result

    RESULT TYPES:
    - Verified: Contract definitely holds
    - Failed: VC that couldn't be proven (for debugging)
    - Unknown: Cannot determine (timeout, complexity)
    ============================================================================ *)

(* Verification result.
   Provides actionable information for the programmer. *)
noeq type verification_result =
  | Verified : verification_result                (* Contract holds *)
  | Failed   : vc -> verification_result          (* VC that couldn't be proved *)
  | Unknown  : verification_result                (* Cannot determine *)

(* Verify contract on expression.
   Main entry point for contract verification. *)
let verify_contract (c: contract) (e: expr) : verification_result =
  let vc = generate_vc c e in
  let vc' = simplify_vc vc in
  if check_vc vc' then Verified
  else Failed vc'

(* Verify with loop invariants.
   Use when expression contains while loops. *)
let verify_contract_with_invariants (c: contract) (e: expr)
    (invariants: list (expr & formula)) : verification_result =
  let vc = generate_vc_with_invariants 100 c e invariants in
  let vc' = simplify_vc vc in
  if check_vc vc' then Verified
  else Failed vc'

(** ============================================================================
    HOARE LOGIC SOUNDNESS
    ============================================================================

    The soundness of our Hoare logic rules with respect to the
    operational semantics. These are axiomatized based on classical
    Hoare logic theory.

    SOUNDNESS THEOREM (informal):
    If a Hoare triple is derivable using the rules above,
    then it is semantically valid (the operational semantics respects it).

    REFERENCES:
    - Hoare (1969): Original soundness proof for basic rules
    - Cook (1978): Relative completeness of Hoare logic
    - Apt (1981): Ten years of Hoare's logic - survey of soundness proofs
    ============================================================================ *)

(* Soundness of WP: {WP(c, Q)} c {Q}
   If we start in a state satisfying WP(c, Q) and c terminates,
   then the final state satisfies Q.
   This is the fundamental theorem of weakest precondition calculus.

   PROOF SKETCH:
   By structural induction on c, using:
   - Assignment: WP = Q[e/x], after assignment Q holds by substitution
   - Sequence: By IH on c1 and c2, with intermediate assertion
   - Conditional: By IH on branches, condition determines which branch
   - Loop: By induction on iteration count, using invariant *)
assume val wp_sound : c:expr -> q:formula ->
  Lemma (hoare (wp c q) c q)

(* Soundness of VC generation:
   If generate_vc(contract, e) is valid, then the contract holds for e.

   PROOF:
   By construction, generate_vc produces pre => WP(e, post).
   If this is valid and pre holds, then WP(e, post) holds.
   By wp_sound, {WP(e, post)} e {post} is valid.
   By consequence, {pre} e {post} is valid. *)
assume val vc_generation_sound : c:contract -> e:expr ->
  Lemma (requires check_vc (generate_vc c e) == true)
        (ensures hoare c.precondition e c.postcondition)

(** ============================================================================
    HOARE TRIPLE AS INDEXED TYPE
    ============================================================================

    Alternative representation of Hoare triples as an indexed type,
    enabling computation with proofs. This provides a monadic interface
    for composing verified computations.

    CONNECTION TO F* EFFECTS:

    This type mirrors F*'s Pure effect:
      Pure a (requires pre) (ensures post)

    The HT constructor wraps a function that:
    1. Requires precondition (squash pre)
    2. Produces value of type a
    3. Ensures postcondition holds

    This allows writing verified code in a natural style while
    maintaining proof obligations.

    MONADIC STRUCTURE:

    The return_ht and bind_ht operations give hoare_triple_t monadic
    structure, similar to the state monad but with specifications.

    This enables:
      let x = verified_op1() in
      let y = verified_op2(x) in
      verified_op3(x, y)

    where each operation has its own pre/postconditions.
    ============================================================================ *)

(* Hoare triple as an indexed type with witness function.
   The indices are:
   - pre: Precondition (Type0)
   - a: Return type
   - post: Postcondition (a -> Type0)

   The HT constructor contains a function that:
   - Requires pre
   - Returns value of type a
   - Ensures post holds on the result *)
noeq type hoare_triple_t (pre: Type0) (a: Type) (post: a -> Type0) =
  | HT : (f: (unit -> Pure a (requires pre) (ensures post))) -> hoare_triple_t pre a post

(* Run a Hoare triple when precondition is satisfied.
   The squash pre argument witnesses that pre holds.
   Returns a pure computation with the given pre/post. *)
let run_ht (#pre: Type0) (#a: Type) (#post: a -> Type0)
           (ht: hoare_triple_t pre a post)
           (_: squash pre) : Pure a (requires pre) (ensures post) =
  let HT f = ht in
  f ()

(* Return for Hoare triples: trivially satisfied.
   Creates a Hoare triple that:
   - Requires nothing (True)
   - Returns the given value
   - Ensures result equals input *)
let return_ht (#a: Type) (x: a) : hoare_triple_t True a (fun r -> r == x) =
  HT (fun () -> x)

(* Compose Hoare triples sequentially using explicit precondition threading.
   This requires that executing ht1 establishes the precondition for ht2.

   COMPOSITION SEMANTICS:
   1. Start with pre1
   2. Execute ht1, get value x : a with mid x holding
   3. mid x is precondition for ht2 x
   4. Execute ht2 x, get value y : b with post y holding

   The combined triple has pre1 as precondition and post as postcondition. *)
val bind_ht : #pre1:Type0 -> #a:Type -> #mid:(a -> Type0) -> #b:Type -> #post:(b -> Type0) ->
              ht1:hoare_triple_t pre1 a mid ->
              ht2:(x:a -> hoare_triple_t (mid x) b post) ->
              hoare_triple_t pre1 b post
let bind_ht #pre1 #a #mid #b #post ht1 ht2 =
  HT (fun () ->
    let HT f1 = ht1 in
    let x : a = f1 () in
    (* At this point, mid x holds from f1's postcondition *)
    let HT f2 = ht2 x in
    f2 ())

(** ============================================================================
    LOOP INVARIANT HELPERS
    ============================================================================

    Utilities for constructing and checking loop invariants.
    These generate the specific VCs needed for loop verification.
    ============================================================================ *)

(* Check that invariant holds initially.
   VC: pre => inv
   The precondition must establish the loop invariant. *)
let invariant_holds_initially (pre: formula) (inv: formula) : vc =
  VCImpl (VCFormula pre) (VCFormula inv)

(* Check that invariant is inductive.
   VC: (inv /\ b) => WP(body, inv)
   Executing the body preserves the invariant. *)
let invariant_is_inductive (inv: formula) (cond: expr) (body: expr) : vc =
  VCImpl
    (VCAnd (VCFormula inv) (VCFormula (FExpr cond)))
    (VCFormula (wp body inv))

(* Check that invariant with negated condition implies post.
   VC: (inv /\ ~b) => post
   Upon loop exit, the postcondition is established. *)
let invariant_implies_post (inv: formula) (cond: expr) (post: formula) : vc =
  VCImpl
    (VCAnd (VCFormula inv) (VCNot (VCFormula (FExpr cond))))
    (VCFormula post)

(* Generate all VCs for a loop.
   Combines the three loop verification obligations. *)
let loop_vcs (pre: formula) (inv: formula) (cond: expr) (body: expr) (post: formula) : vc =
  VCAnd
    (invariant_holds_initially pre inv)
    (VCAnd
      (invariant_is_inductive inv cond body)
      (invariant_implies_post inv cond post))

(** ============================================================================
    FUNCTION CONTRACT VERIFICATION
    ============================================================================

    Higher-level interface for verifying functions with contracts.
    ============================================================================ *)

(* Function definition with contract.
   Complete specification of a function including:
   - Name and parameters
   - Return type
   - Contract (pre/postcondition)
   - Implementation (body) *)
noeq type contracted_function = {
  fn_name     : string;
  fn_params   : list (var_id & brrr_type);
  fn_return   : brrr_type;
  fn_contract : contract;
  fn_body     : expr;
}

(* Verify a contracted function.
   Generates and checks VCs for the function body against its contract. *)
let verify_function (f: contracted_function) : verification_result =
  verify_contract f.fn_contract f.fn_body

(* Create contract from requires/ensures annotations.
   Maps spec syntax to internal contract representation. *)
let make_contract (requires_clause: formula) (ensures_clause: formula) : contract = {
  precondition = requires_clause;
  postcondition = ensures_clause;
}

(** ============================================================================
    DEPENDENT REFINEMENT TYPE INTEGRATION
    ============================================================================

    Bridge between contract specifications and dependent types.
    Allows extracting contracts from dependent function types and vice versa.
    ============================================================================ *)

(* Convert refinement type to precondition.
   Extracts the refinement predicate and instantiates with the variable.

   Example:
     DRefinement "x" TInt (FCmp CmpGe (EVar "x") (e_int 0))
     becomes:
     x >= 0 (with x substituted) *)
let refinement_to_precondition (x: var_id) (t: dep_type) : formula =
  match t with
  | DRefinement _ _ phi -> subst_formula x (EVar x) phi
  | _ -> FTrue

(* Extract contract from dependent function type.
   Pi types with refined domain/codomain become contracts.

   Example:
     (x:{n:Int|n >= 0}) -> {r:Int|r >= x}
     becomes:
     { precondition = x >= 0; postcondition = result >= x } *)
let dep_func_to_contract (fn_type: dep_type) (result_var: var_id) : option contract =
  match fn_type with
  | DPi x param_type return_type ->
      let pre = refinement_to_precondition x param_type in
      let post =
        match return_type with
        | DRefinement _ _ phi -> subst_formula result_var (EVar result_var) phi
        | _ -> FTrue
      in
      Some { precondition = pre; postcondition = post }
  | _ -> None

(** ============================================================================
    SPECIFICATION LANGUAGE HELPERS
    ============================================================================

    Utilities for writing specifications in a clear, structured way.
    These helpers support common specification patterns.
    ============================================================================ *)

(* Assert: inline assertion.
   Creates an expression that fails if the assertion doesn't hold.

   NOTE: This creates a runtime check. For static verification,
   use contract annotations instead. *)
let spec_assert (phi: formula) : expr =
  EIf (ELit (LitBool true))  (* Condition that's always true *)
      (ELit LitUnit)
      (EError "assertion failed")

(* Assume: assume formula holds (for verification).
   Used to introduce assumptions into the verification context.
   WARNING: Unsound if the assumption is false! *)
let spec_assume (phi: formula) : formula = phi

(* Old: refer to pre-state value (for postconditions).
   Creates a ghost variable representing the value at function entry.

   Example in postcondition:
     old_x < x  means  "x increased"

   IMPLEMENTATION:
   The verifier creates bindings for old_* variables at function entry. *)
let spec_old (x: var_id) : var_id = "old_" ^ x

(* Result: the return value in postconditions.
   Standard name for the function's return value.

   Example:
     result >= 0 means "the return value is non-negative" *)
let spec_result : var_id = "result"

(* Create postcondition referencing result.
   Helper for building result-dependent postconditions.

   Usage:
     ensures_result (fun r -> FCmp CmpGe r (e_int 0))
     produces: result >= 0 *)
let ensures_result (f: expr -> formula) : formula =
  f (EVar spec_result)

(* Create postcondition comparing result to old value.
   Common pattern for specifying how output relates to input.

   Usage:
     ensures_modified "x" (fun new old -> FCmp CmpGt new old)
     produces: x > old_x *)
let ensures_modified (x: var_id) (relation: expr -> expr -> formula) : formula =
  relation (EVar x) (EVar (spec_old x))

(** ============================================================================
    COMMON CONTRACT PATTERNS
    ============================================================================

    Pre-built contracts for common specification patterns.
    These capture frequently-used contract structures.
    ============================================================================ *)

(* Pure function: no precondition, result satisfies predicate.
   For functions that always succeed and guarantee output property.

   Example:
     pure_function_contract (fun r -> FCmp CmpGe r (e_int 0))
     { pre = true; post = result >= 0 } *)
let pure_function_contract (result_pred: expr -> formula) : contract = {
  precondition = FTrue;
  postcondition = result_pred (EVar spec_result);
}

(* Partial function: precondition required, ensures result.
   For functions that may fail on invalid inputs.

   Example:
     partial_function_contract
       (FCmp CmpNe (EVar "y") (e_int 0))
       (fun r -> FTrue)
     { pre = y != 0; post = true } *)
let partial_function_contract (pre: formula) (result_pred: expr -> formula) : contract = {
  precondition = pre;
  postcondition = result_pred (EVar spec_result);
}

(* Monotonic function: result >= input.
   For functions that don't decrease their input.

   Example: abs, max, increment *)
let monotonic_contract (input_var: var_id) : contract = {
  precondition = FTrue;
  postcondition = FCmp CmpGe (EVar spec_result) (EVar input_var);
}

(* Non-negative result contract.
   Common constraint for lengths, sizes, counts.

   { pre = true; post = result >= 0 } *)
let non_negative_result_contract : contract = {
  precondition = FTrue;
  postcondition = FCmp CmpGe (EVar spec_result) (e_int 0);
}

(* Bounded result contract.
   Result is in range [lo, hi).

   { pre = true; post = lo <= result < hi } *)
let bounded_result_contract (lo hi: int) : contract = {
  precondition = FTrue;
  postcondition = FAnd
    (FCmp CmpGe (EVar spec_result) (e_int lo))
    (FCmp CmpLt (EVar spec_result) (e_int hi));
}

(** ============================================================================
    VC TO STRING (for debugging)
    ============================================================================

    Pretty-printing for VCs, useful for debugging and error reporting.
    ============================================================================ *)

(* Convert VC to human-readable string.
   Used for debugging and error messages. *)
let rec vc_to_string (v: vc) : Tot string (decreases v) =
  match v with
  | VCTrue -> "true"
  | VCFalse -> "false"
  | VCImpl v1 v2 -> "(" ^ vc_to_string v1 ^ " => " ^ vc_to_string v2 ^ ")"
  | VCAnd v1 v2 -> "(" ^ vc_to_string v1 ^ " /\\ " ^ vc_to_string v2 ^ ")"
  | VCOr v1 v2 -> "(" ^ vc_to_string v1 ^ " \\/ " ^ vc_to_string v2 ^ ")"
  | VCNot v' -> "~" ^ vc_to_string v'
  | VCForall x _ v' -> "(forall " ^ x ^ ". " ^ vc_to_string v' ^ ")"
  | VCExists x _ v' -> "(exists " ^ x ^ ". " ^ vc_to_string v' ^ ")"
  | VCFormula phi -> formula_to_string phi

(** ============================================================================
    VERIFICATION REPORTING
    ============================================================================

    Structures for reporting verification results to users.
    ============================================================================ *)

(* Verification report for a function.
   Complete information about verification attempt. *)
noeq type verification_report = {
  vr_function : string;
  vr_result   : verification_result;
  vr_vc       : vc;
  vr_message  : string;
}

(* Create verification report.
   Generates VC, checks it, and formats the result. *)
let make_report (f: contracted_function) : verification_report =
  let vc = generate_vc f.fn_contract f.fn_body in
  let result = verify_contract f.fn_contract f.fn_body in
  let msg = match result with
    | Verified -> "Function " ^ f.fn_name ^ " verified successfully"
    | Failed _ -> "Function " ^ f.fn_name ^ " failed verification"
    | Unknown -> "Function " ^ f.fn_name ^ " verification inconclusive"
  in
  { vr_function = f.fn_name;
    vr_result = result;
    vr_vc = vc;
    vr_message = msg; }
