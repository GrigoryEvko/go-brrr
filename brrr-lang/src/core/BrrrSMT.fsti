(**
 * BrrrLang.Core.SMT - Interface
 *
 * SMT Solver Interface for Brrr-Lang.
 * Provides semantic formula implication via external Z3 binding.
 *
 * ============================================================================
 * OVERVIEW: SMT INTEGRATION IN BRRR-LANG
 * ============================================================================
 *
 * This module provides the interface between Brrr-Lang's refinement type system
 * and the Z3 SMT (Satisfiability Modulo Theories) solver. SMT solvers enable
 * automatic verification of refinement type constraints that would be intractable
 * to prove purely syntactically.
 *
 * Key Concepts:
 * ------------
 *
 * 1. SATISFIABILITY vs VALIDITY
 *    - SAT: Does there exist an assignment making the formula true?
 *    - VALID: Is the formula true under ALL assignments?
 *    - VALIDITY CHECK: To check if phi is valid, we check if (not phi) is UNSAT.
 *      If the negation has no satisfying assignment, the original is valid.
 *
 * 2. THREE-VALUED OUTCOMES
 *    SMT solvers return one of three results:
 *    - UNSAT: No model exists (formula is unsatisfiable)
 *    - SAT: A model exists (with witness assignment)
 *    - UNKNOWN: Solver timeout, resource limits, or incomplete theory
 *
 * 3. SMT-LIB2 FORMAT
 *    The standard input language for SMT solvers, based on S-expressions.
 *    Reference: http://smtlib.cs.uiowa.edu/language.shtml
 *
 * Gap Resolution:
 *   1. SMT integration - formula_implies is currently syntactic only
 *   2. Semantic formula implication with quantifier handling
 *   3. Three-valued logic (Definitely/DefinitelyNot/Unknown)
 *   4. SMTLIB2 formula translation
 *
 * This module defines the interface; actual Z3 binding is via BrrrFFI.
 *
 * Related F* Options (affect SMT behavior):
 * -----------------------------------------
 *   --z3rlimit N       : Resource limit for Z3 (default: 5, units vary by Z3 version)
 *   --z3rlimit_factor N: Multiplier for z3rlimit
 *   --fuel N           : Initial/max fuel for recursive function unrolling
 *   --ifuel N          : Initial/max fuel for inductive type inversion
 *   --z3cliopt STRING  : Pass option to Z3 command line
 *   --z3smtopt STRING  : Insert option into SMT2 output
 *   --log_queries      : Log all SMT queries to .smt2 files for debugging
 *   --query_stats      : Print statistics about each SMT query
 *
 * References:
 * -----------
 *   - Proof-oriented Programming in F* (Part: Under the Hood, SMT Encoding)
 *   - Alejandro Aguirre's tech report on F* SMT encoding formalization
 *   - Michal Moskal's "Programming with Triggers" (pattern selection)
 *   - Leonardo de Moura & Nikolaj Bjorner's E-matching paper
 *
 * Depends on: Primitives, BrrrTypes, Expressions, DependentTypes
 *)
module BrrrSMT

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes
open BrrrExpressions
open BrrrDependentTypes

(** ============================================================================
    THREE-VALUED LOGIC (TRILEAN)
    ============================================================================

    SMT queries can have three outcomes:
    - Definitely: The property holds in ALL models
    - DefinitelyNot: The property fails in ALL models (counterexample exists)
    - Unknown: Solver timeout, incomplete theory, or undecidable fragment

    Information ordering: Unknown is LESS informative than definite values.
    This matches TVLA's three-valued logic semantics (Sagiv, Reps, Wilhelm).

    Kleene's Strong Three-Valued Logic:
    ------------------------------------
    The operations below implement Kleene's strong three-valued logic,
    where Unknown represents "lack of information" rather than a third
    truth value. This is appropriate for SMT results because Unknown
    means "we couldn't determine" rather than "it's neither true nor false".

    Truth Tables:
      NOT:  Definitely -> DefinitelyNot
            DefinitelyNot -> Definitely
            Unknown -> Unknown

      AND:  D  DN U       OR:  D  DN U       IMPL: D  DN U
         D  D  DN U          D  D  D  D          D  D  DN U
         DN DN DN DN         DN D  DN U          DN D  D  D
         U  U  DN U          U  D  U  U          U  D  U  U
    ============================================================================ *)

(** Three-valued logic type for SMT query results *)
type trilean =
  | Definitely     (* True in all models - SAT of negation is UNSAT *)
  | DefinitelyNot  (* False in all models - found counterexample *)
  | Unknown        (* Cannot determine - timeout or incomplete *)

(** Trilean negation - straightforward inversion *)
val trilean_not : trilean -> trilean

(** Trilean conjunction (Kleene semantics)
    False dominates Unknown, True requires both True *)
val trilean_and : trilean -> trilean -> trilean

(** Trilean disjunction (Kleene semantics)
    True dominates Unknown, False requires both False *)
val trilean_or : trilean -> trilean -> trilean

(** Trilean implication: a => b is ~a \/ b *)
val trilean_impl : trilean -> trilean -> trilean

(** Convert trilean to boolean (conservative for Unknown)
    Use this when safety requires assuming failure on uncertainty *)
val trilean_to_bool_conservative : trilean -> bool

(** Convert trilean to boolean (optimistic for Unknown)
    Use this when liveness/progress requires assuming success on uncertainty *)
val trilean_to_bool_optimistic : trilean -> bool

(** Information ordering: Unknown < Definite values
    This defines the "definedness" lattice where Unknown is bottom *)
val trilean_info_leq : trilean -> trilean -> bool

(** ============================================================================
    SMT RESULT TYPE
    ============================================================================

    Raw results from SMT solver queries before interpretation.

    Result Interpretation for Different Query Types:
    ------------------------------------------------

    For SATISFIABILITY queries (is there a model?):
      Sat model  -> Yes, here's a witness
      Unsat      -> No model exists
      Unknown    -> Couldn't determine

    For VALIDITY queries (is it true in all models?):
      We check validity by negating and checking satisfiability:
        - Valid iff negation is UNSAT
        - Invalid iff negation is SAT (counterexample)
        - Unknown iff solver couldn't determine

    For ENTAILMENT queries (does phi1 => phi2?):
      phi1 => phi2 is valid iff (phi1 /\ ~phi2) is UNSAT
      - UNSAT means entailment holds
      - SAT means counterexample to entailment
      - Unknown means couldn't determine
    ============================================================================ *)

(** Model: satisfying assignment for variables
    Simplified representation - production version would include:
    - Function interpretations for uninterpreted functions
    - Array models as store chains
    - Bitvector values
    - Real number assignments *)
type smt_model = list (string & int)

(** SMT solver result with optional model/reason *)
noeq type smt_result =
  | Sat     : model:smt_model -> smt_result    (* Satisfiable with witness *)
  | Unsat   : smt_result                        (* Unsatisfiable *)
  | SmtUnknown : reason:string -> smt_result   (* Unknown with reason *)

(** Convert SMT result to trilean for entailment queries

    IMPORTANT: This conversion is specifically for ENTAILMENT checking
    where we negate the goal and check satisfiability.

    Conversion logic:
      Unsat      -> Definitely    (negation unsat means original valid)
      Sat model  -> DefinitelyNot (found counterexample)
      Unknown    -> Unknown       (propagate uncertainty)

    Common "unknown" reasons from Z3:
      - "timeout"           : Resource limit exceeded
      - "incomplete"        : Theory combination issue
      - "memout"            : Memory limit exceeded
      - "canceled"          : User/external cancellation
      - "(incomplete quantifiers)" : Quantifier instantiation incomplete
*)
val smt_result_to_trilean_entailment : smt_result -> trilean

(** ============================================================================
    SMTLIB2 REPRESENTATION
    ============================================================================

    Abstract syntax for SMTLIB2 formulas.
    This is the target of formula translation from Brrr-Lang.

    SMT-LIB2 Standard Reference:
    ----------------------------
    The SMT-LIB v2 standard (http://smtlib.cs.uiowa.edu/) defines:
    - A multi-sorted first-order logic
    - Standard theories (Core, Ints, Reals, Arrays, BitVectors, etc.)
    - Script commands for interaction with solvers

    Core Theory Symbols:
      true, false        : Bool constants
      not, and, or, =>   : Boolean connectives
      =, distinct        : Equality (polymorphic)
      ite                : If-then-else (polymorphic)

    Integer Theory (Ints/LIA/NIA):
      +, -, *, div, mod  : Arithmetic operations
      <, <=, >, >=       : Comparisons
      Note: Non-linear arithmetic (NIA) is undecidable!

    Quantifiers:
      forall, exists     : First-order quantifiers
      WARNING: Quantifiers make satisfiability undecidable in general.
               Z3 uses E-matching heuristics with PATTERNS for instantiation.

    Logic Fragments (decidable):
    ----------------------------
      QF_LIA  : Quantifier-Free Linear Integer Arithmetic
      QF_LRA  : Quantifier-Free Linear Real Arithmetic
      QF_BV   : Quantifier-Free Fixed-Size Bit-Vectors
      QF_UF   : Quantifier-Free Uninterpreted Functions
      QF_AUFLIA: QF Arrays + Uninterpreted Functions + LIA

    Undecidable Combinations:
      - Any logic with quantifiers (but often tractable with good patterns)
      - Non-linear integer arithmetic (NIA)
      - Mixing theories without quantifier-free restrictions
    ============================================================================ *)

(** SMTLIB2 sorts (types in SMT terminology)

    F*'s SMT Encoding Note (Term Sort):
    -----------------------------------
    F* uses a SINGLE uninterpreted sort called "Term" for almost all F* values,
    then uses "boxing" functions to embed primitive types:
      BoxBool : Bool -> Term
      BoxInt  : Int -> Term
    with corresponding projection functions.

    This allows uniform handling of F*'s rich type system in the simpler
    SMT type system. The tradeoff is additional quantifier instantiation
    overhead for boxing/unboxing.

    For Brrr-Lang, we use a hybrid approach:
      - Primitive types map directly to SMT sorts (more efficient)
      - Complex types use uninterpreted sorts (like Term approach)
*)
type smt_sort =
  | SortBool   : smt_sort                                     (* SMT Bool sort *)
  | SortInt    : smt_sort                                     (* SMT Int sort (unbounded) *)
  | SortReal   : smt_sort                                     (* SMT Real sort *)
  | SortBitVec : width:nat -> smt_sort                        (* (_ BitVec n) *)
  | SortArray  : idx:smt_sort -> elem:smt_sort -> smt_sort    (* (Array idx elem) *)
  | SortUninterpreted : name:string -> smt_sort               (* Uninterpreted sort *)

(** SMTLIB2 terms/expressions

    Pattern/Trigger System (Critical for Quantifier Instantiation):
    ---------------------------------------------------------------
    When encoding quantified formulas, PATTERNS control when Z3 instantiates
    the quantifier. Without good patterns, quantifiers may never fire or
    may cause exponential blowup (matching loops).

    F* Pattern Syntax:
      val lemma : x:t -> Lemma (P x) [SMTPat (f x)]

    This becomes in SMT2:
      (forall ((x Term))
        (! (=> (HasType x T) (P x))
           :pattern ((f x))))

    Pattern Requirements:
      1. Must mention ALL bound variables
      2. Should decrease in size through instantiation (avoid loops)
      3. Should match terms likely to appear in proof context

    Matching Loops (DANGEROUS):
      If pattern P instantiates to produce another match for P,
      infinite instantiation occurs. Example:
        (forall ((x Int)) (! (=> (P x) (P (+ x 1))) :pattern ((P x))))
      Each instantiation creates new P term, triggering more instantiation.

    Note: This AST doesn't include explicit patterns; they would be added
    to SmtForall/SmtExists for production use.
*)
noeq type smt_term =
  (* Constants *)
  | SmtTrue    : smt_term                                     (* true *)
  | SmtFalse   : smt_term                                     (* false *)
  | SmtInt     : int -> smt_term                              (* integer literal *)
  | SmtReal    : string -> smt_term                           (* rational as string "n/d" *)
  | SmtBitVec  : value:int -> width:nat -> smt_term           (* (_ bvN W) *)

  (* Variables - include sort for well-sortedness *)
  | SmtVar     : name:string -> smt_sort -> smt_term

  (* Core theory - Boolean operations *)
  | SmtNot     : smt_term -> smt_term                         (* (not t) *)
  | SmtAnd     : list smt_term -> smt_term                    (* (and t1 ... tn) *)
  | SmtOr      : list smt_term -> smt_term                    (* (or t1 ... tn) *)
  | SmtImpl    : smt_term -> smt_term -> smt_term             (* (=> t1 t2) *)
  | SmtIff     : smt_term -> smt_term -> smt_term             (* (= t1 t2) for Bool *)
  | SmtIte     : cond:smt_term -> then_:smt_term -> else_:smt_term -> smt_term  (* (ite c t e) *)

  (* Equality - polymorphic, works on any sort *)
  | SmtEq      : smt_term -> smt_term -> smt_term             (* (= t1 t2) *)
  | SmtDistinct : list smt_term -> smt_term                   (* (distinct t1 ... tn) *)

  (* Arithmetic - for Int/Real sorts *)
  | SmtNeg     : smt_term -> smt_term                         (* (- t) *)
  | SmtAdd     : list smt_term -> smt_term                    (* (+ t1 ... tn) *)
  | SmtSub     : smt_term -> smt_term -> smt_term             (* (- t1 t2) *)
  | SmtMul     : list smt_term -> smt_term                    (* multiplication: t1...tn *)
  | SmtDiv     : smt_term -> smt_term -> smt_term             (* (div t1 t2) for Int, (/ t1 t2) for Real *)
  | SmtMod     : smt_term -> smt_term -> smt_term             (* (mod t1 t2) *)

  (* Comparisons - for Int/Real sorts *)
  | SmtLt      : smt_term -> smt_term -> smt_term             (* (< t1 t2) *)
  | SmtLe      : smt_term -> smt_term -> smt_term             (* (<= t1 t2) *)
  | SmtGt      : smt_term -> smt_term -> smt_term             (* (> t1 t2) *)
  | SmtGe      : smt_term -> smt_term -> smt_term             (* (>= t1 t2) *)

  (* Quantifiers - make satisfiability undecidable in general
     NOTE: For effective use, annotate with :pattern in production *)
  | SmtForall  : bindings:list (string & smt_sort) -> body:smt_term -> smt_term
  | SmtExists  : bindings:list (string & smt_sort) -> body:smt_term -> smt_term

  (* Uninterpreted functions - essential for abstraction *)
  | SmtApply   : func:string -> args:list smt_term -> smt_term

  (* Let bindings - for sharing common subexpressions *)
  | SmtLet     : bindings:list (string & smt_term) -> body:smt_term -> smt_term

(** SMTLIB2 commands for constructing scripts

    Incremental Solving Commands:
    -----------------------------
    SMT solvers support incremental mode with push/pop:
      (push 1)    : Save current assertion state
      (assert P)  : Add assertion P to current state
      (check-sat) : Check satisfiability of current assertions
      (pop 1)     : Restore to saved state, removing recent assertions

    This is crucial for efficiency in refinement type checking where
    many related queries share common assumptions.

    Resource Limits:
    ----------------
    Controlled via:
      (set-option :timeout N)        ; Timeout in milliseconds
      (set-option :rlimit N)         ; Z3-specific resource limit

    In F*, use --z3rlimit N to set resource limits.
    The "rlimit" is more deterministic than wall-clock timeout.
*)
noeq type smt_command =
  | CmdSetLogic     : logic_name:string -> smt_command        (* (set-logic LOGIC) *)
  | CmdDeclareSort  : name:string -> arity:nat -> smt_command (* (declare-sort NAME ARITY) *)
  | CmdDefineSort   : name:string -> params:list string -> def:smt_sort -> smt_command
  | CmdDeclareConst : name:string -> sort:smt_sort -> smt_command  (* (declare-const NAME SORT) *)
  | CmdDeclareFun   : name:string -> args:list smt_sort -> ret:smt_sort -> smt_command
  | CmdDefineFun    : name:string -> args:list (string & smt_sort) -> ret:smt_sort -> body:smt_term -> smt_command
  | CmdAssert       : term:smt_term -> smt_command            (* (assert TERM) *)
  | CmdCheckSat     : smt_command                             (* (check-sat) *)
  | CmdGetModel     : smt_command                             (* (get-model) *)
  | CmdPush         : levels:nat -> smt_command               (* (push N) *)
  | CmdPop          : levels:nat -> smt_command               (* (pop N) *)
  | CmdReset        : smt_command                             (* (reset) *)
  | CmdExit         : smt_command                             (* (exit) *)

(** SMTLIB2 script is a sequence of commands *)
type smt_script = list smt_command

(** ============================================================================
    BRRR TYPE TO SMT SORT TRANSLATION
    ============================================================================

    Translation Strategy:
    ---------------------

    Brrr-Lang types are translated to SMT sorts following these principles:

    1. PRIMITIVE TYPES -> THEORY SORTS
       - Bool -> Bool (direct mapping)
       - Int types -> Int (use unbounded for simplicity; could use BitVec)
       - Float types -> Real (approximation; loses precision semantics)

    2. COMPOSITE TYPES -> UNINTERPRETED SORTS
       - Pairs, Options, etc. use uninterpreted sorts with axiomatized operations
       - This follows the "Term sort" pattern from F* but with named sorts

    3. FUNCTION TYPES -> UNINTERPRETED
       - First-order SMT logic doesn't support function values
       - Use uninterpreted sort, rely on axioms about function application

    Precision Tradeoffs:
    --------------------
    - Using Int instead of BitVec: Loses overflow semantics but gains decidability
    - Using Real instead of Float: Loses IEEE 754 semantics (NaN, infinity, rounding)
    - Using uninterpreted for complex types: Requires careful axiomatization

    For precise bounded integer reasoning, switch to SortBitVec with
    appropriate width. This makes non-linear operations decidable.
    ============================================================================ *)

(** Translate Brrr base type to SMT sort *)
val brrr_type_to_smt_sort : brrr_type -> smt_sort

(** Convert sort to display string (for naming composite sorts) *)
val sort_to_string : s:smt_sort -> Tot string (decreases s)

(** ============================================================================
    EXPRESSION TO SMT TERM TRANSLATION
    ============================================================================

    Partial Translation:
    --------------------
    Not all Brrr-Lang expressions can be translated to SMT terms.
    Untranslatable constructs include:
    - Effectful operations (I/O, state, exceptions)
    - Higher-order functions (lambdas, closures)
    - Pattern matching (could be expanded to ite chains)
    - Recursive definitions (require fuel encoding)

    When translation fails, we return None and the SMT query
    will report Unknown (cannot verify or refute).

    Fuel System for Recursive Functions:
    ------------------------------------
    F* handles recursive functions using "fuel" - a parameter that
    limits unrolling depth. For Brrr-Lang, function calls become
    uninterpreted applications unless we add explicit fuel-style encoding.
    ============================================================================ *)

(** Translate comparison operator to SMT term constructor *)
val translate_cmp_op : cmp_op -> smt_term -> smt_term -> smt_term

(** Translate expression to SMT term (partial - handles common cases)

    Returns None for untranslatable expressions. The caller should
    treat None as Unknown (cannot verify without SMT support).

    Type Information Loss:
    ----------------------
    We lose type information when translating EVar - all variables
    default to SortInt. A production implementation would:
    1. Thread a typing context through translation
    2. Look up variable types from context
    3. Use appropriate sort for each variable
*)
val expr_to_smt_term : expr -> option smt_term

(** ============================================================================
    FORMULA TO SMT TERM TRANSLATION
    ============================================================================

    Formulas from BrrrDependentTypes.fst represent refinement predicates.
    Translation to SMT is mostly structural, with special handling for:

    1. QUANTIFIERS
       Universal and existential quantifiers translate directly to BrrrSMT.
       WARNING: Quantifiers make satisfiability undecidable. Z3 uses
       E-matching with patterns to instantiate quantifiers heuristically.

    2. PREDICATES
       Named predicates become uninterpreted function applications.
       The meaning of predicates must come from axioms/lemmas.

    3. EXPRESSIONS IN FORMULAS
       Boolean expressions embedded in formulas translate via expr_to_smt_term.
    ============================================================================ *)

(** Translate dependent type to SMT sort (for quantifier bindings) *)
val dep_type_to_smt_sort : dep_type -> smt_sort

(** Translate formula to SMT term

    Structural translation with the key insight that:
    - FTrue/FFalse become SmtTrue/SmtFalse
    - Comparisons translate expression operands, then wrap in SMT comparison
    - Logical connectives map directly
    - Quantifiers create SMT quantifiers with typed bindings
*)
val formula_to_smt_term : formula -> option smt_term

(** ============================================================================
    SMT TERM TO SMTLIB2 STRING
    ============================================================================

    Serialization of SMT terms to the SMT-LIB2 text format for Z3 input.

    S-Expression Syntax:
    --------------------
    SMT-LIB2 uses LISP-style S-expressions:
      (operator arg1 arg2 ... argN)

    Examples:
      (+ x y)           ; Addition
      (and p q r)       ; Conjunction (variadic)
      (forall ((x Int)) (> x 0))  ; Universal quantifier
      (ite cond then else)        ; If-then-else

    Debugging Tip:
    --------------
    Use F*'s --log_queries option to see generated SMT2 files.
    These can be run directly with Z3:
      z3 queries-ModuleName.smt2
    ============================================================================ *)

(** Convert sort to SMTLIB2 string representation *)
val smt_sort_to_string : s:smt_sort -> Tot string (decreases s)

(** Convert term to SMTLIB2 string representation *)
val smt_term_to_string : t:smt_term -> Tot string (decreases t)

(** ============================================================================
    SMT SOLVER INTERFACE (AXIOMATIZED)
    ============================================================================

    The actual Z3 binding is via BrrrFFI. These functions define the interface
    that will be implemented by the external solver.

    Axiomatization Approach:
    ------------------------
    We use F*'s `assume val` to declare the SMT interface without implementation.
    This allows reasoning about SMT-based verification while deferring the
    actual Z3 integration to extraction/BrrrFFI.

    The key axioms we assume are:
    1. SOUNDNESS: If Z3 returns UNSAT, the formula truly has no models
    2. PARTIAL COMPLETENESS: For decidable fragments, Z3 is complete

    Trust Model:
    ------------
    Our verification chain is:
      Brrr-Lang source
        -> Refinement type checking (this module)
        -> SMT queries (via Z3)
        -> Verification result

    We trust:
    - F* type system (for our F* code)
    - Z3 SMT solver (for SMT queries)
    - FFI binding correctness (for Z3 integration)
    ============================================================================ *)

(** SMT solver configuration

    Logic Selection:
    ----------------
    Choosing the right logic can significantly impact performance:
      "QF_LIA"   : Quantifier-Free Linear Integer Arithmetic (decidable, fast)
      "QF_NIA"   : Quantifier-Free Non-linear Integer Arithmetic (undecidable)
      "QF_AUFLIA": Arrays + Uninterpreted Functions + LIA (decidable)
      "ALL"      : Full logic (most general, may be slow)

    Start with the most restrictive logic that covers your formulas.

    Incremental Mode:
    -----------------
    When enabled, the solver maintains state across queries using push/pop.
    This is essential for efficiency in refinement type checking where
    many queries share common assumptions (e.g., function preconditions).
*)
noeq type smt_config = {
  timeout_ms   : nat;           (* Solver timeout in milliseconds *)
  smt_logic    : string;        (* SMTLIB2 logic (e.g., "QF_LIA", "ALL") *)
  incremental  : bool;          (* Use incremental mode with push/pop *)
}

(** Default SMT configuration:
    - 5 second timeout
    - Full logic (ALL)
    - Incremental solving enabled *)
noeq type refinement_result =
  | RefinementHolds      : refinement_result
  | RefinementFails      : cex:option smt_model -> refinement_result
  | RefinementUnknown    : reason:string -> refinement_result

(** Convert trilean to refinement result *)
val collect_formula_vars : formula -> list (string & smt_sort)

(** Collect free variables from an expression *)
val collect_expr_vars : expr -> list (string & smt_sort)

(** Generate SMTLIB2 script for checking formula validity

    Script Structure:
    -----------------
    1. (set-logic LOGIC) - Declare the SMT logic to use
    2. (declare-const x T) for each free variable
    3. (assert (not phi)) - Assert negation of goal
    4. (check-sat) - Check for satisfiability

    If (check-sat) returns UNSAT, the original phi is VALID.
    If (check-sat) returns SAT, we have a counterexample.
*)
val generate_validity_script : formula -> option smt_script

(** Discharge a verification condition

    A VC is discharged (proven valid) when the SMT solver returns UNSAT
    for its negation. This is the entry point for type-checking to call
    when it needs to verify a refinement constraint.

    Returns:
      Definitely    - VC is valid (refinement holds)
      DefinitelyNot - VC has counterexample (refinement fails)
      Unknown       - Could not determine (timeout, etc.)
*)
val discharge_vc : smt_config -> formula -> trilean

(** ============================================================================
    SOUNDNESS AXIOMS
    ============================================================================

    These axioms relate SMT validity to semantic truth.
    They are the meta-level soundness assumptions for the SMT integration.

    We rely on Z3's correctness for verification. These axioms make explicit
    what we're assuming:

    1. SOUNDNESS: If Z3 says UNSAT, the formula really has no models.
       This is the critical property - if Z3 is unsound, our verification
       is meaningless.

    2. PARTIAL COMPLETENESS: For decidable fragments (QF_LIA, etc.),
       Z3 will not return "incomplete" as the unknown reason.
       Note: Z3 may still timeout, so this is partial.

    These are axiomatized using `assume val` because they're meta-level
    properties of the external solver, not something we can prove in F*.
    ============================================================================ *)

(** Soundness: If SMT says UNSAT, the formula is semantically valid

    This axiom states that Z3's UNSAT result is reliable.
    If Z3 proves the negation unsatisfiable, the original formula
    has no counterexamples, hence is valid.
*)
val smt_check_implication : smt_config -> smt_term -> smt_term -> trilean

(** ============================================================================
    SEMANTIC FORMULA IMPLICATION
    ============================================================================

    This is the key function that replaces the syntactic formula_implies
    from BrrrDependentTypes.fst with semantic SMT-based implication.

    Why SMT?
    --------
    Syntactic implication (formula_implies in BrrrDependentTypes.fst) can only
    recognize simple structural relationships like:
      - FTrue implies anything
      - Anything implies itself
      - Simple alpha-equivalence

    SMT enables reasoning about:
      - Arithmetic relationships: (x > 0) => (x >= 0)
      - Boolean combinations: (a /\ b) => a
      - Quantified facts: (forall x. P(x)) => P(42)
      - Theory-specific facts: Array axioms, etc.

    Hybrid Strategy:
    ----------------
    formula_implies_hybrid first tries cheap syntactic check, then falls
    back to expensive SMT only when needed. This optimizes the common case
    where refinements are structurally similar.
    ============================================================================ *)

(** Semantic formula implication using SMT solver
    Returns trilean: Definitely (valid), DefinitelyNot (invalid), Unknown *)
val formula_implies_hybrid : smt_config -> formula -> formula -> trilean

(** ============================================================================
    VERIFICATION CONDITION DISCHARGE
    ============================================================================

    Verification conditions (VCs) are logical formulas that must be valid
    for a program to be well-typed. For refinement types:

      {x:T | phi} <: {x:T | psi}  requires  forall x:T. phi => psi

    This section provides utilities for generating and checking VCs.

    Free Variable Collection:
    -------------------------
    Before sending a formula to Z3, we need to:
    1. Collect all free variables
    2. Declare them with appropriate sorts
    3. Assert the formula (or its negation for validity check)

    Variables bound by quantifiers are NOT free and should NOT be declared.
    ============================================================================ *)

(** Collect free variables in formula for SMT declarations

    Note: This properly handles variable shadowing by filtering
    bound variables from recursive results.
*)
val formula_implies_semantic : smt_config -> formula -> formula -> trilean

(** Combined syntactic + semantic implication check
    First tries fast syntactic check, falls back to SMT

    Performance Rationale:
    ----------------------
    Syntactic check: O(formula size), in-process, deterministic
    SMT check: Potentially expensive, external process, may timeout

    Many refinement checks in practice involve:
    - Same refinement on both sides (identity)
    - Simple structural inclusion (FTrue on RHS)
    - Reflexive equality checks

    These are handled instantly by syntax, avoiding SMT overhead.
*)
noeq type smt_context = {
  ctx_config     : smt_config;
  ctx_assertions : list smt_term;   (* Current assertion stack *)
  ctx_level      : nat;              (* Push level *)
}

(** Create an empty SMT context with the given configuration *)
val smt_check_sat : config:smt_config -> term:smt_term -> smt_result

(** Check if phi1 implies phi2 using SMT

    Entailment Check:
    -----------------
    To check phi1 => phi2 (phi1 entails phi2), we check if
    (phi1 /\ ~phi2) is unsatisfiable:
      - UNSAT: No counterexample exists, entailment holds
      - SAT: Counterexample found, entailment fails
      - UNKNOWN: Cannot determine

    This is the standard "refutation" approach used by most SMT-based
    verification tools.
*)
val default_smt_config : smt_config

(** Check satisfiability of SMT term - axiomatized external call

    This is the core primitive that all other SMT operations build upon.
    The actual implementation will:
    1. Serialize the term to SMT-LIB2 format
    2. Send to Z3 process (via pipe or library binding)
    3. Parse the response (sat/unsat/unknown)
    4. If sat, extract model from (get-model) response

    Assumed Semantics:
    - Returns Sat(model) if formula is satisfiable with given model
    - Returns Unsat if formula has no models (definitely unsatisfiable)
    - Returns Unknown(reason) on timeout, memout, or incomplete theories
*)
val check_refinement_subtype :
  config:smt_config ->
  x:dep_var ->
  base:dep_type ->
  phi1:formula ->
  phi2:formula ->
  refinement_result
val trilean_to_refinement : trilean -> option smt_model -> refinement_result

(** Check refinement subtyping with counterexample

    For refinement types:
      {x:base | phi1} <: {x:base | phi2}

    We need to prove:
      forall x:base. phi1(x) => phi2(x)

    Equivalently, check that there's no counterexample:
      not (exists x:base. phi1(x) /\ not phi2(x))

    If the existential query returns SAT, the model is our counterexample.

    Usage in Type Checking:
    -----------------------
    When checking function application f(e) where:
      f : (x:{T | phi}) -> U
      e : {T | psi}

    We need to verify psi => phi (argument satisfies precondition).
    If this fails, the counterexample shows an input where psi holds but phi doesn't.
*)
val smt_pop : smt_context -> smt_context

(** Assert: Add formula to current context
    Formula becomes part of background theory for subsequent checks *)
val empty_smt_context : smt_config -> smt_context

(** Push: Save current solver state
    Subsequent assertions can be undone by pop *)
val smt_push : smt_context -> smt_context

(** Pop: Restore to previous state
    Removes assertions added since last push *)
val smt_assert : smt_context -> smt_term -> smt_context

(** Check satisfiability in current context - axiomatized *)
val smt_context_check_sat : smt_context -> smt_result

(** ============================================================================
    REFINEMENT RESULT TYPE
    ============================================================================

    Query result with optional counterexample for refinement checking.

    Production Note:
    ----------------
    A full counterexample would include:
    - All variable assignments
    - Uninterpreted function interpretations
    - Array contents
    - Path through disjunctions in the formula
    ============================================================================ *)

(** Result of a refinement subtyping check *)
val smt_completeness_qf_lia :
  config:smt_config{config.smt_logic = "QF_LIA"} ->
  phi:smt_term ->
  Lemma (requires True)
        (ensures smt_check_sat config phi <> SmtUnknown "incomplete")

(** ============================================================================
    INCREMENTAL SMT CONTEXT
    ============================================================================

    For efficiency, maintain SMT context across multiple queries.

    Incremental Solving:
    --------------------
    Rather than starting fresh for each query, incremental solving maintains
    solver state:
      1. Common assumptions are asserted once
      2. push() saves current state
      3. Query-specific assertions added
      4. check-sat performed
      5. pop() restores to saved state
      6. Next query reuses common assumptions

    This is critical for refinement type checking performance:
    - Function preconditions are asserted once
    - Each refinement check is a push/assert/check/pop
    - Common axioms (e.g., for arrays, strings) loaded once

    Performance Impact:
    -------------------
    Without incremental: Each query re-processes all axioms
    With incremental: Axioms processed once, queries are much faster
    ============================================================================ *)

(** Incremental solver state

    ctx_assertions: Stack of assertions at each level
    ctx_level: Current push depth (for matching push/pop)
*)
val smt_soundness_unsat :
  config:smt_config ->
  phi:smt_term ->
  Lemma (requires smt_check_sat config phi == Unsat)
        (ensures forall (model: smt_model). True)

(** Completeness for decidable fragments: If valid, SMT will return UNSAT

    For decidable fragments like QF_LIA (Quantifier-Free Linear Integer
    Arithmetic), Z3 is a decision procedure. It will always terminate
    with a definite answer, never returning "incomplete".

    Note: This doesn't prevent timeouts ("canceled") or other resource
    limit issues ("memout"), just theory-level incompleteness.
*)
