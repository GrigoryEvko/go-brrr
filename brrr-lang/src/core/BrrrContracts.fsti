(**
 * ============================================================================
 * BrrrLang.Core.Contracts - Interface
 * ============================================================================
 *
 * Design by Contract and Hoare Logic for Brrr-Lang
 *
 * Based on brrr_lang_spec_v0.4.tex Part IX - Contracts (Sections 6378-6395)
 *
 * ============================================================================
 * THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * This module implements a formal contract system based on:
 *
 * [Meyer 1992] Bertrand Meyer. "Applying Design by Contract."
 *              IEEE Computer 25(10):40-51, 1992.
 *
 * [Hoare 1969] C.A.R. Hoare. "An Axiomatic Basis for Computer Programming."
 *              Communications of the ACM, 12(10):576-580, 1969.
 *
 * [Floyd 1967] Robert W. Floyd. "Assigning Meaning to Programs."
 *              Proceedings of Symposia in Applied Mathematics, Vol. 19, 1967.
 *
 * [Dijkstra 1975] Edsger W. Dijkstra. "Guarded Commands, Nondeterminacy and
 *                 Formal Derivation of Programs." CACM 18(8):453-457, 1975.
 *
 * ============================================================================
 * MODULE OVERVIEW
 * ============================================================================
 *
 * This interface provides:
 *   - Refinement type helpers for common verification patterns
 *   - Function contracts (preconditions and postconditions)
 *   - Program state abstraction for Hoare logic
 *   - Formula evaluation in states
 *   - Hoare triple representation and soundness rules
 *   - Weakest precondition calculus
 *   - Verification condition generation and checking
 *   - Contract verification infrastructure
 *   - Integration with dependent types
 *   - Specification language utilities
 *
 * ============================================================================
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

    Common refined types for program verification at the meta-level.
    These are F* types used for reasoning about Brrr programs.

    DESIGN NOTE: These mirror Brrr-Lang refinement types:
      nat_type       <->  { x : Int | x >= 0 }
      pos_type       <->  { x : Int | x > 0 }
      bounded_index  <->  { i : Int | 0 <= i < len }
      percentage     <->  { x : Int | 0 <= x <= 100 }
    ============================================================================ *)

(** Natural numbers: non-negative integers.
    Corresponds to { x : Int | x >= 0 } in Brrr-Lang. *)
type nat_type = x:int{x >= 0}

(** Positive integers: strictly positive.
    Essential for array lengths, divisors, loop bounds.
    Corresponds to { x : Int | x > 0 } in Brrr-Lang. *)
type pos_type = x:int{x > 0}

(** Bounded array index: valid index into array of given length.
    The len parameter must be positive (non-empty arrays).
    Guarantees: 0 <= i < len

    CRITICAL: Primary mechanism for proving array bounds safety.
    When combined with dependent types, eliminates bounds check overhead. *)
type bounded_index (len:nat{len > 0}) = i:nat{i < len}

(** Non-empty list: list with at least one element.
    Useful for head/tail operations that would otherwise be partial. *)
type non_empty_list (a:Type) = l:list a{Cons? l}

(** Percentage: value between 0 and 100 (inclusive).
    Common domain-specific constraint for UI, statistics, etc. *)
type percentage = x:int{0 <= x /\ x <= 100}


(** ============================================================================
    FUNCTION CONTRACTS
    ============================================================================

    A contract specifies the expected behavior of a function through:

    - PRECONDITION (requires): Obligation of the CALLER (client)
      What must be true when the function is called.

    - POSTCONDITION (ensures): Obligation of the FUNCTION (supplier)
      What will be true when the function returns.

    The postcondition can reference the special variable "result" which
    represents the return value of the function.
    ============================================================================ *)

(** Contract type: pair of formulas for pre/postcondition.
    Uses noeq because formula contains functions.

    SEMANTICS:
    A function f satisfies contract C if:
      forall inputs. C.precondition(inputs) ==>
        let result = f(inputs) in C.postcondition(inputs, result) *)
noeq type contract = {
  precondition  : formula;   (* What caller must ensure *)
  postcondition : formula;   (* What function guarantees, can use "result" *)
}

(** Trivial contract: true -> true
    Used as default when no contract is specified.
    Imposes no obligations on caller, provides no guarantees. *)
val trivial_contract : contract

(** Create a pure function contract: no side effects, only return value matters.

    @param pre  Precondition formula
    @param post Postcondition formula (may reference "result")
    @return Contract with given pre/postcondition *)
val pure_contract : pre:formula -> post:formula -> contract

(** Contract with only a precondition.
    Function requires something but makes no promises about return value.

    @param pre Precondition formula
    @return Contract with precondition and true postcondition *)
val requires_only : pre:formula -> contract

(** Contract with only a postcondition.
    Function always applicable but guarantees specific output property.

    @param post Postcondition formula
    @return Contract with true precondition and given postcondition *)
val ensures_only : post:formula -> contract


(** ============================================================================
    PROGRAM STATE ABSTRACTION
    ============================================================================

    For Hoare logic, we need an abstract view of program state.
    A state is a mapping from variables to values.

    DESIGN CHOICE: Functional representation (var_id -> option value)
    rather than list-based environment for mathematical clarity and
    natural state update operations.

    CONNECTION TO EVALUATION:
    The eval module uses list-based environments. Conversion functions
    bridge these representations.
    ============================================================================ *)

(** Abstract state: mapping from variable names to values.
    None represents an undefined variable (out of scope or uninitialized). *)
type state = var_id -> option value

(** Empty state: no variables defined.
    Starting point for building states.
    Invariant: empty_state x = None for all x *)
val empty_state : state

(** State update: s[x := v]
    Creates a new state that maps x to v, preserving all other mappings.

    PROPERTIES:
    - (state_update s x v) x = Some v           (update succeeds)
    - y <> x ==> (state_update s x v) y = s y   (frame property)

    @param s Current state
    @param x Variable to update
    @param v New value for x
    @return Updated state *)
val state_update : s:state -> x:var_id -> v:value -> state

(** State lookup: retrieve value for variable.

    @param s State to query
    @param x Variable name
    @return Some v if x is defined, None otherwise *)
val state_lookup : s:state -> x:var_id -> option value

(** Convert eval environment to abstract state.
    Bridges BrrrEval.fst (list-based env) and Hoare logic (function-based state).

    @param e Evaluation environment
    @return Corresponding abstract state *)
val env_to_state : e:env -> state

(** Convert abstract state to environment (as list of bindings).
    Requires knowing which variables to include.
    Only includes variables that have defined values in the state.

    NOTE: Inherently lossy - variable set must be known upfront.

    @param vars List of variables to include
    @param s State to convert
    @return Evaluation environment *)
val state_to_env_helper : vars:list var_id -> s:state -> env


(** ============================================================================
    FORMULA EVALUATION
    ============================================================================

    Evaluate a formula in a given state to get a boolean result.
    Provides the semantic foundation for Hoare logic.

    EVALUATION STRATEGY:
    - FTrue/FFalse: Constant true/false
    - FCmp: Evaluate both expressions, compare results
    - FAnd/FOr: Short-circuit evaluation
    - FNot: Negate sub-formula
    - FImpl: Encoded as ~P \/ Q
    - FIff: Both directions must match
    - FForall/FExists: CANNOT evaluate (unbounded quantification)
    - FPred: CANNOT evaluate (external predicates)
    - FExpr: Evaluate expression, expect boolean

    Returns None when evaluation fails (missing variable, type error,
    fuel exhaustion, unbounded quantifier).
    ============================================================================ *)

(** Evaluate expression in state, returning option value.
    Bridges formula evaluation to expression evaluation from BrrrEval.fst.

    @param e Expression to evaluate
    @param s State containing variable bindings
    @param fuel Recursion fuel for termination
    @return Some value if evaluation succeeds, None otherwise *)
val eval_expr_in_state : e:expr -> s:state -> fuel:nat -> option value

(** Evaluate comparison operator on two values.
    Handles type-specific comparison semantics.

    SUPPORTED COMPARISONS:
    - Integer: All operators (=, <>, <, <=, >, >=)
    - Boolean: Only equality (=, <>)
    - String: All operators (lexicographic for ordering)

    @param op Comparison operator
    @param v1 First value
    @param v2 Second value
    @return Some bool if comparison succeeds, None for type mismatch *)
val eval_cmp_op : op:cmp_op -> v1:value -> v2:value -> option bool

(** Evaluate formula in state with fuel for recursive calls.

    FUEL SYSTEM:
    - fuel = 0: Return None (conservative, cannot determine)
    - fuel > 0: Recurse with fuel - 1

    QUANTIFIER HANDLING:
    FForall and FExists return None (cannot enumerate infinite domains).

    @param fuel Recursion fuel for termination
    @param phi Formula to evaluate
    @param s State containing variable bindings
    @return Some bool if evaluation succeeds, None otherwise *)
val eval_formula_in_state : fuel:nat -> phi:formula -> s:state -> Tot (option bool) (decreases fuel)

(** Default fuel for formula evaluation.
    1000 is sufficient for most practical formulas. *)
val formula_eval_fuel : nat

(** Check if formula holds in state.
    Convenience wrapper that returns boolean.
    Returns false for any evaluation failure (conservative).

    @param phi Formula to check
    @param s State for evaluation
    @return true if formula definitely holds, false otherwise *)
val formula_holds : phi:formula -> s:state -> bool


(** ============================================================================
    ASSERTION TYPE - Semantic predicates on states
    ============================================================================

    An assertion is a predicate on program states.
    Represented both as formulas (syntactic) and semantic predicates (for proofs).

    TWO REPRESENTATIONS:
    1. SYNTACTIC (formula): Can be manipulated, evaluated, encoded for SMT
    2. SEMANTIC (state -> Type0): F* propositions for meta-theoretic proofs

    CONVERSION:
    formula_to_assertion converts syntactic formulas to semantic assertions.
    ============================================================================ *)

(** Semantic assertion: predicate on states.
    Returns Type0 (F* proposition) rather than bool for richer specifications. *)
type assertion = state -> Type0

(** Convert formula to semantic assertion.
    Uses formula_holds for evaluation, lifting to Type0.

    @param phi Formula to convert
    @return Semantic assertion *)
val formula_to_assertion : phi:formula -> assertion

(** Trivially true assertion: holds in all states.
    Unit of conjunction. *)
val assert_true : assertion

(** Trivially false assertion: holds in no state.
    Unit of disjunction (vacuously). *)
val assert_false : assertion

(** Conjunction of assertions: both must hold.
    {P /\ Q} in Hoare logic notation.

    @param p First assertion
    @param q Second assertion
    @return Combined assertion requiring both *)
val assert_and : p:assertion -> q:assertion -> assertion

(** Disjunction of assertions: at least one must hold.
    {P \/ Q} in Hoare logic notation.

    @param p First assertion
    @param q Second assertion
    @return Combined assertion requiring at least one *)
val assert_or : p:assertion -> q:assertion -> assertion

(** Implication of assertions: if p then q.
    Used in consequence rule and conditional reasoning.

    @param p Antecedent assertion
    @param q Consequent assertion
    @return Implication assertion *)
val assert_impl : p:assertion -> q:assertion -> assertion

(** Negation of assertion.
    Used for else-branch in conditionals.

    @param p Assertion to negate
    @return Negated assertion *)
val assert_not : p:assertion -> assertion


(** ============================================================================
    HOARE TRIPLE REPRESENTATION
    ============================================================================

    A Hoare triple {P} c {Q} asserts:
      For all states s, if P holds in s and executing c from s terminates
      in state s', then Q holds in s'.

    PARTIAL VS TOTAL CORRECTNESS:
    - PARTIAL CORRECTNESS (hoare_triple_valid): Only for terminating executions
    - TOTAL CORRECTNESS (hoare_total): Also requires termination
    ============================================================================ *)

(** Execute expression and get resulting state.
    Bridges expression evaluation to state-based semantics.

    @param e Expression to execute
    @param s Initial state
    @param fuel Recursion fuel
    @return Some (value, new_state) on success, None on error *)
val exec_expr : e:expr -> s:state -> fuel:nat -> option (value & state)

(** Hoare triple validity as a semantic proposition.
    {P} c {Q} holds when: for all states s satisfying P,
    if c terminates with value v in state s', then Q holds in s'.

    FORMAL DEFINITION (matching Hoare 1969):
    {P} c {Q} := forall s. P(s) ==> (c terminates from s with s' ==> Q(s'))

    @param pre Precondition assertion
    @param c Expression to execute
    @param post Postcondition assertion
    @return Type0 proposition for triple validity *)
val hoare_triple_valid : pre:assertion -> c:expr -> post:assertion -> Type0

(** Notation helper: create Hoare triple from formulas.
    Converts syntactic formulas to semantic assertions.

    @param pre Precondition formula
    @param c Expression to execute
    @param post Postcondition formula
    @return Type0 proposition for triple validity *)
val hoare : pre:formula -> c:expr -> post:formula -> Type0

(** Total correctness: termination + partial correctness.
    Combines termination proof with partial correctness.

    @param pre Precondition assertion
    @param c Expression to execute
    @param post Postcondition assertion
    @return Type0 proposition for total correctness *)
val hoare_total : pre:assertion -> c:expr -> post:assertion -> Type0


(** ============================================================================
    HOARE LOGIC RULES - Axiomatized Sound Rules
    ============================================================================

    Standard Hoare logic rules from [Hoare 1969] and [Floyd 1967].
    Axiomatized as sound with respect to operational semantics.

    The rules form a SOUND and COMPLETE proof system for partial correctness
    of while programs (relative to assertion language expressiveness).
    ============================================================================ *)

(** H-SKIP: {P} unit {P}
    Skip (unit expression) preserves any assertion.
    Sound because evaluating unit produces unit without state change.

    @param p Any assertion
    @return Lemma that {p} unit {p} *)
val h_skip : p:assertion -> Lemma (hoare_triple_valid p (ELit LitUnit) p)

(** H-Skip for formulas.
    Convenience wrapper using syntactic formulas.

    @param phi Any formula
    @return Lemma that {phi} unit {phi} *)
val h_skip_formula : phi:formula -> Lemma (hoare phi (ELit LitUnit) phi)

(** H-SEQ: {P} c1 {Q} /\ {Q} c2 {R} ==> {P} c1;c2 {R}
    Sequential composition via intermediate assertion Q.

    @param p Precondition
    @param q Intermediate assertion
    @param r Postcondition
    @param c1 First expression
    @param c2 Second expression
    @return Lemma for sequential composition *)
val h_seq : p:assertion -> q:assertion -> r:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid p c1 q /\ hoare_triple_valid q c2 r)
        (ensures hoare_triple_valid p (ESeq c1 c2) r)

(** H-CONSEQ: P' ==> P /\ {P} c {Q} /\ Q ==> Q' ==> {P'} c {Q'}
    Consequence rule: strengthen precondition, weaken postcondition.

    @param p Original precondition
    @param p' Stronger precondition
    @param q Original postcondition
    @param q' Weaker postcondition
    @param c Expression
    @return Lemma for consequence rule *)
val h_conseq : p:assertion -> p':assertion -> q:assertion -> q':assertion -> c:expr ->
  Lemma (requires (forall s. p' s ==> p s) /\
                  hoare_triple_valid p c q /\
                  (forall s. q s ==> q' s))
        (ensures hoare_triple_valid p' c q')

(** H-IF: {P /\ b} c1 {Q} /\ {P /\ ~b} c2 {Q} ==> {P} if b c1 c2 {Q}
    Conditional rule: both branches establish postcondition.

    @param p Precondition
    @param q Postcondition
    @param b_true Condition as assertion
    @param c1 Then branch
    @param c2 Else branch
    @return Lemma for conditional *)
val h_if_valid : p:assertion -> q:assertion -> b_true:assertion -> c1:expr -> c2:expr ->
  Lemma (requires hoare_triple_valid (assert_and p b_true) c1 q /\
                  hoare_triple_valid (assert_and p (assert_not b_true)) c2 q)
        (ensures hoare_triple_valid p (EIf (ELit (LitBool true)) c1 c2) q)

(** H-WHILE: {I /\ b} c {I} ==> {I} while b do c {I /\ ~b}
    While rule with loop invariant.

    LOOP INVARIANT I must satisfy:
    1. INITIALLY TRUE: Established before loop entry
    2. PRESERVED: {I /\ b} body {I}
    3. USEFUL: I /\ ~b implies desired postcondition

    @param inv Loop invariant
    @param b_true Loop condition as assertion
    @param body Loop body
    @return Lemma for while loop *)
val h_while_valid : inv:assertion -> b_true:assertion -> body:expr ->
  Lemma (requires hoare_triple_valid (assert_and inv b_true) body inv)
        (ensures hoare_triple_valid inv
                   (EWhile (ELit (LitBool true)) body)
                   (assert_and inv (assert_not b_true)))


(** ============================================================================
    WEAKEST PRECONDITION CALCULUS
    ============================================================================

    The weakest precondition WP(c, Q) is the weakest assertion P such that
    {P} c {Q} holds. Computing WP allows automatic VC generation.

    WP RULES (from Dijkstra):
    - WP(skip, Q)           = Q
    - WP(x := e, Q)         = Q[e/x]
    - WP(c1; c2, Q)         = WP(c1, WP(c2, Q))
    - WP(if b c1 c2, Q)     = (b => WP(c1, Q)) /\ (~b => WP(c2, Q))
    - WP(while b inv I, Q)  = I /\ (I /\ ~b => Q) /\ (I /\ b => WP(c, I))

    PROPERTIES:
    1. SOUNDNESS: {WP(c, Q)} c {Q} is always valid
    2. COMPLETENESS: If {P} c {Q} is valid, then P ==> WP(c, Q)
    3. MONOTONICITY: If Q ==> Q', then WP(c, Q) ==> WP(c, Q')
    4. CONJUNCTION: WP(c, Q /\ R) = WP(c, Q) /\ WP(c, R)
    ============================================================================ *)

(** Substitute expression for variable in formula (WP computation).
    Implements the assignment rule: WP(x := e, Q) = Q[e/x]

    @param x Variable to substitute
    @param e Expression to substitute with
    @param post Postcondition formula
    @return Formula with substitution applied *)
val wp_subst : x:var_id -> e:expr -> post:formula -> formula

(** Weakest precondition computation with fuel for termination.
    Computes WP(c, post) following Dijkstra's rules.

    FUEL PARAMETER:
    Used for termination - returns FFalse when exhausted.
    This is conservative: FFalse implies anything, so WP is still sound.

    @param fuel Recursion fuel
    @param c Expression to compute WP for
    @param post Postcondition formula
    @return Weakest precondition formula *)
val wp_compute : fuel:nat -> c:expr -> post:formula -> Tot formula (decreases fuel)

(** Default fuel for WP computation.
    100 is sufficient for most practical programs. *)
val wp_fuel : nat

(** Compute weakest precondition (convenience wrapper).
    Uses default fuel setting.

    @param c Expression to compute WP for
    @param post Postcondition formula
    @return Weakest precondition formula *)
val wp : c:expr -> post:formula -> formula


(** ============================================================================
    LOOP INVARIANTS
    ============================================================================

    For while loops, we need loop invariants to enable verification.

    LOOP INVARIANT REQUIREMENTS (from [Floyd 1967]):
    1. INITIALLY TRUE: pre => I
    2. PRESERVED (INDUCTIVE): {I /\ b} body {I}
    3. SUFFICIENT: I /\ ~b => post

    VARIANTS FOR TERMINATION:
    A VARIANT (ranking function) proves termination:
    - Non-negative integer expression
    - Strictly decreases each iteration
    ============================================================================ *)

(** Annotated while loop with invariant.
    Extends basic while loop with verification annotations. *)
noeq type annotated_while = {
  while_cond      : expr;         (* Loop condition *)
  while_body      : expr;         (* Loop body *)
  while_invariant : formula;      (* Loop invariant *)
  while_variant   : option expr;  (* Optional decreasing variant for termination *)
}

(** Check if invariant is preserved by loop body.
    Computes: (I /\ b) => WP(body, I)

    @param inv Loop invariant formula
    @param cond Loop condition expression
    @param body Loop body expression
    @return Formula expressing invariant preservation *)
val invariant_preserved : inv:formula -> cond:expr -> body:expr -> formula

(** Generate verification conditions for while loop.
    Returns conjunction of all VCs that must be proven.

    @param w Annotated while loop
    @param post Postcondition formula
    @return Combined VC formula *)
val while_vc : w:annotated_while -> post:formula -> formula

(** WP for annotated while loop.
    Combines invariant with VCs for complete verification.

    @param w Annotated while loop
    @param post Postcondition formula
    @return Weakest precondition for loop *)
val wp_while : w:annotated_while -> post:formula -> formula


(** ============================================================================
    VERIFICATION CONDITIONS
    ============================================================================

    Verification conditions (VCs) are logical formulas that, if valid,
    guarantee the correctness of a program with respect to its contract.

    VC GENERATION:
    Given contract {pre} e {post}:
    1. Compute WP(e, post)
    2. Generate VC: pre => WP(e, post)
    3. Check if VC is valid (tautology)
    ============================================================================ *)

(** VC representation - richer than formula for SMT solving.
    Explicit constructors for logical structure. *)
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

(** VC size for termination proofs.
    Used as decreases clause for recursive VC processing.

    @param v Verification condition
    @return Natural number size metric *)
val vc_size : v:vc -> Tot nat (decreases v)

(** Convert formula to VC.
    Simple embedding via VCFormula constructor.

    @param phi Formula to convert
    @return VC embedding the formula *)
val formula_to_vc : phi:formula -> vc

(** Convert VC to formula (best effort).
    Quantifiers convert directly.

    @param v Verification condition
    @return Corresponding formula *)
val vc_to_formula : v:vc -> Tot formula (decreases v)

(** Simplify VC using standard logical identities.

    SIMPLIFICATION RULES:
    - True /\ P = P, False /\ P = False
    - True \/ P = True, False \/ P = P
    - False => P = True, P => True = True, True => P = P
    - ~~P = P (double negation elimination)

    @param v Verification condition to simplify
    @return Simplified verification condition *)
val simplify_vc : v:vc -> Tot vc (decreases v)


(** ============================================================================
    VC CHECKING
    ============================================================================

    Check if a VC is valid (semantically true in all states).
    Conservative approximation - returns true only when validity is
    syntactically obvious.

    SOUNDNESS:
    If check_vc returns true, the VC is definitely valid.
    If check_vc returns false, the VC might still be valid.
    ============================================================================ *)

(** Conservative VC validity check.
    Returns true only when validity is syntactically obvious.

    @param v Verification condition to check
    @return true if definitely valid, false if uncertain *)
val check_vc : v:vc -> Tot bool (decreases v)

(** Simplified VC check that first simplifies the VC.
    Often more effective than checking directly.

    @param v Verification condition to check
    @return true if definitely valid after simplification *)
val check_vc_simplified : v:vc -> bool


(** ============================================================================
    VC GENERATION FROM CONTRACT AND EXPRESSION
    ============================================================================ *)

(** Generate VC for contract and expression.
    Simple case without loop invariants.

    @param c Contract to verify
    @param e Expression to check
    @return Verification condition *)
val generate_vc : c:contract -> e:expr -> vc

(** Generate VC with loop invariants.
    Handles while loops with user-provided invariants.

    INVARIANT MAP:
    The invariants parameter maps while expressions to their invariants.

    @param fuel Recursion fuel
    @param c Contract to verify
    @param e Expression to check
    @param invariants List of (while_expr, invariant) pairs
    @return Verification condition *)
val generate_vc_with_invariants : fuel:nat -> c:contract -> e:expr ->
    invariants:list (expr & formula) -> Tot vc (decreases fuel)


(** ============================================================================
    CONTRACT VERIFICATION
    ============================================================================ *)

(** Verification result.
    Provides actionable information for the programmer. *)
noeq type verification_result =
  | Verified : verification_result                (* Contract holds *)
  | Failed   : vc -> verification_result          (* VC that couldn't be proved *)
  | Unknown  : verification_result                (* Cannot determine *)

(** Verify contract on expression.
    Main entry point for contract verification.

    @param c Contract to verify
    @param e Expression to check
    @return Verification result *)
val verify_contract : c:contract -> e:expr -> verification_result

(** Verify with loop invariants.
    Use when expression contains while loops.

    @param c Contract to verify
    @param e Expression to check
    @param invariants List of (while_expr, invariant) pairs
    @return Verification result *)
val verify_contract_with_invariants : c:contract -> e:expr ->
    invariants:list (expr & formula) -> verification_result


(** ============================================================================
    HOARE LOGIC SOUNDNESS
    ============================================================================

    Soundness of Hoare logic rules with respect to operational semantics.
    Axiomatized based on classical Hoare logic theory.
    ============================================================================ *)

(** Soundness of WP: {WP(c, Q)} c {Q}
    If we start in a state satisfying WP(c, Q) and c terminates,
    then the final state satisfies Q.

    @param c Expression
    @param q Postcondition formula
    @return Lemma establishing WP soundness *)
val wp_sound : c:expr -> q:formula ->
  Lemma (hoare (wp c q) c q)

(** Soundness of VC generation:
    If generate_vc(contract, e) is valid, then the contract holds for e.

    @param c Contract
    @param e Expression
    @return Lemma establishing VC generation soundness *)
val vc_generation_sound : c:contract -> e:expr ->
  Lemma (requires check_vc (generate_vc c e) == true)
        (ensures hoare c.precondition e c.postcondition)


(** ============================================================================
    HOARE TRIPLE AS INDEXED TYPE
    ============================================================================

    Alternative representation of Hoare triples as an indexed type,
    enabling computation with proofs. Provides monadic interface
    for composing verified computations.

    CONNECTION TO F* EFFECTS:
    Mirrors F*'s Pure effect: Pure a (requires pre) (ensures post)
    ============================================================================ *)

(** Hoare triple as an indexed type with witness function.
    The indices are:
    - pre: Precondition (Type0)
    - a: Return type
    - post: Postcondition (a -> Type0) *)
noeq type hoare_triple_t (pre: Type0) (a: Type) (post: a -> Type0) =
  | HT : (f: (unit -> Pure a (requires pre) (ensures post))) -> hoare_triple_t pre a post

(** Run a Hoare triple when precondition is satisfied.
    The squash pre argument witnesses that pre holds.

    @param ht Hoare triple to run
    @param _ Proof that precondition holds
    @return Pure computation with given pre/post *)
val run_ht : #pre:Type0 -> #a:Type -> #post:(a -> Type0) ->
             ht:hoare_triple_t pre a post ->
             _:squash pre -> Pure a (requires pre) (ensures post)

(** Return for Hoare triples: trivially satisfied.
    Creates a Hoare triple that requires nothing, returns the given value,
    and ensures result equals input.

    @param x Value to return
    @return Trivial Hoare triple *)
val return_ht : #a:Type -> x:a -> hoare_triple_t True a (fun r -> r == x)

(** Compose Hoare triples sequentially using explicit precondition threading.
    Requires that executing ht1 establishes the precondition for ht2.

    COMPOSITION SEMANTICS:
    1. Start with pre1
    2. Execute ht1, get value x with mid x holding
    3. Execute ht2 x, get value y with post y holding

    @param ht1 First Hoare triple
    @param ht2 Second Hoare triple (dependent on first's result)
    @return Composed Hoare triple *)
val bind_ht : #pre1:Type0 -> #a:Type -> #mid:(a -> Type0) -> #b:Type -> #post:(b -> Type0) ->
              ht1:hoare_triple_t pre1 a mid ->
              ht2:(x:a -> hoare_triple_t (mid x) b post) ->
              hoare_triple_t pre1 b post


(** ============================================================================
    LOOP INVARIANT HELPERS
    ============================================================================

    Utilities for constructing and checking loop invariants.
    Generate specific VCs needed for loop verification.
    ============================================================================ *)

(** Check that invariant holds initially.
    VC: pre => inv

    @param pre Precondition formula
    @param inv Invariant formula
    @return VC for initial establishment *)
val invariant_holds_initially : pre:formula -> inv:formula -> vc

(** Check that invariant is inductive.
    VC: (inv /\ b) => WP(body, inv)

    @param inv Invariant formula
    @param cond Loop condition expression
    @param body Loop body expression
    @return VC for inductiveness *)
val invariant_is_inductive : inv:formula -> cond:expr -> body:expr -> vc

(** Check that invariant with negated condition implies post.
    VC: (inv /\ ~b) => post

    @param inv Invariant formula
    @param cond Loop condition expression
    @param post Postcondition formula
    @return VC for postcondition establishment *)
val invariant_implies_post : inv:formula -> cond:expr -> post:formula -> vc

(** Generate all VCs for a loop.
    Combines the three loop verification obligations.

    @param pre Precondition formula
    @param inv Invariant formula
    @param cond Loop condition expression
    @param body Loop body expression
    @param post Postcondition formula
    @return Combined VC for loop *)
val loop_vcs : pre:formula -> inv:formula -> cond:expr -> body:expr -> post:formula -> vc


(** ============================================================================
    FUNCTION CONTRACT VERIFICATION
    ============================================================================ *)

(** Function definition with contract.
    Complete specification of a function. *)
noeq type contracted_function = {
  fn_name     : string;
  fn_params   : list (var_id & brrr_type);
  fn_return   : brrr_type;
  fn_contract : contract;
  fn_body     : expr;
}

(** Verify a contracted function.
    Generates and checks VCs for the function body against its contract.

    @param f Contracted function to verify
    @return Verification result *)
val verify_function : f:contracted_function -> verification_result

(** Create contract from requires/ensures annotations.
    Maps spec syntax to internal contract representation.

    @param requires_clause Precondition formula
    @param ensures_clause Postcondition formula
    @return Contract *)
val make_contract : requires_clause:formula -> ensures_clause:formula -> contract


(** ============================================================================
    DEPENDENT REFINEMENT TYPE INTEGRATION
    ============================================================================

    Bridge between contract specifications and dependent types.
    ============================================================================ *)

(** Convert refinement type to precondition.
    Extracts the refinement predicate and instantiates with the variable.

    @param x Variable name for substitution
    @param t Dependent type (possibly refined)
    @return Precondition formula *)
val refinement_to_precondition : x:var_id -> t:dep_type -> formula

(** Extract contract from dependent function type.
    Pi types with refined domain/codomain become contracts.

    @param fn_type Dependent function type
    @param result_var Variable name for result in postcondition
    @return Some contract if extraction succeeds, None otherwise *)
val dep_func_to_contract : fn_type:dep_type -> result_var:var_id -> option contract


(** ============================================================================
    SPECIFICATION LANGUAGE HELPERS
    ============================================================================

    Utilities for writing specifications in a clear, structured way.
    ============================================================================ *)

(** Assert: inline assertion expression.
    Creates an expression that fails if the assertion doesn't hold.

    NOTE: Creates a runtime check. For static verification,
    use contract annotations instead.

    @param phi Assertion formula
    @return Expression that checks the assertion *)
val spec_assert : phi:formula -> expr

(** Assume: assume formula holds (for verification).
    Used to introduce assumptions into the verification context.
    WARNING: Unsound if the assumption is false!

    @param phi Formula to assume
    @return The formula (for use in verification context) *)
val spec_assume : phi:formula -> formula

(** Old: refer to pre-state value (for postconditions).
    Creates a ghost variable representing the value at function entry.

    @param x Variable name
    @return "old_" prefixed variable name *)
val spec_old : x:var_id -> var_id

(** Result: the return value in postconditions.
    Standard name for the function's return value. *)
val spec_result : var_id

(** Create postcondition referencing result.
    Helper for building result-dependent postconditions.

    @param f Function from result expression to formula
    @return Formula with result variable *)
val ensures_result : f:(expr -> formula) -> formula

(** Create postcondition comparing result to old value.
    Common pattern for specifying how output relates to input.

    @param x Variable name
    @param relation Relation between new and old values
    @return Postcondition formula *)
val ensures_modified : x:var_id -> relation:(expr -> expr -> formula) -> formula


(** ============================================================================
    COMMON CONTRACT PATTERNS
    ============================================================================

    Pre-built contracts for common specification patterns.
    ============================================================================ *)

(** Pure function: no precondition, result satisfies predicate.
    For functions that always succeed and guarantee output property.

    @param result_pred Predicate on result
    @return Contract *)
val pure_function_contract : result_pred:(expr -> formula) -> contract

(** Partial function: precondition required, ensures result.
    For functions that may fail on invalid inputs.

    @param pre Precondition formula
    @param result_pred Predicate on result
    @return Contract *)
val partial_function_contract : pre:formula -> result_pred:(expr -> formula) -> contract

(** Monotonic function: result >= input.
    For functions that don't decrease their input.

    @param input_var Input variable name
    @return Contract *)
val monotonic_contract : input_var:var_id -> contract

(** Non-negative result contract.
    Common constraint for lengths, sizes, counts.
    { pre = true; post = result >= 0 } *)
val non_negative_result_contract : contract

(** Bounded result contract.
    Result is in range [lo, hi).

    @param lo Lower bound (inclusive)
    @param hi Upper bound (exclusive)
    @return Contract *)
val bounded_result_contract : lo:int -> hi:int -> contract


(** ============================================================================
    VC TO STRING (for debugging)
    ============================================================================ *)

(** Convert VC to human-readable string.
    Used for debugging and error messages.

    @param v Verification condition
    @return String representation *)
val vc_to_string : v:vc -> Tot string (decreases v)


(** ============================================================================
    VERIFICATION REPORTING
    ============================================================================ *)

(** Verification report for a function.
    Complete information about verification attempt. *)
noeq type verification_report = {
  vr_function : string;
  vr_result   : verification_result;
  vr_vc       : vc;
  vr_message  : string;
}

(** Create verification report.
    Generates VC, checks it, and formats the result.

    @param f Contracted function to report on
    @return Verification report *)
val make_report : f:contracted_function -> verification_report
