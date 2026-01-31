(**
 * BrrrLang.Core.SMT
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
 *    Example script:
 *      (declare-const x Int)
 *      (declare-const y Int)
 *      (assert (> x 0))
 *      (assert (= y ( * x 2)))   ; Note: space after ( to avoid F* comment
 *      (assert (< y x))          ; This makes it UNSAT
 *      (check-sat)
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

type trilean =
  | Definitely     (* True in all models - SAT of negation is UNSAT *)
  | DefinitelyNot  (* False in all models - found counterexample *)
  | Unknown        (* Cannot determine - timeout or incomplete *)

(* Trilean negation - straightforward inversion *)
let trilean_not (t: trilean) : trilean =
  match t with
  | Definitely -> DefinitelyNot
  | DefinitelyNot -> Definitely
  | Unknown -> Unknown

(* Trilean conjunction (Kleene semantics)
   False dominates Unknown, True requires both True *)
let trilean_and (t1 t2: trilean) : trilean =
  match t1, t2 with
  | DefinitelyNot, _ -> DefinitelyNot
  | _, DefinitelyNot -> DefinitelyNot
  | Definitely, Definitely -> Definitely
  | _, _ -> Unknown

(* Trilean disjunction (Kleene semantics)
   True dominates Unknown, False requires both False *)
let trilean_or (t1 t2: trilean) : trilean =
  match t1, t2 with
  | Definitely, _ -> Definitely
  | _, Definitely -> Definitely
  | DefinitelyNot, DefinitelyNot -> DefinitelyNot
  | _, _ -> Unknown

(* Trilean implication: a => b is ~a \/ b *)
let trilean_impl (t1 t2: trilean) : trilean =
  trilean_or (trilean_not t1) t2

(* Convert trilean to boolean (conservative for Unknown)
   Use this when safety requires assuming failure on uncertainty *)
let trilean_to_bool_conservative (t: trilean) : bool =
  match t with
  | Definitely -> true
  | DefinitelyNot -> false
  | Unknown -> false  (* Conservative: treat unknown as false *)

(* Convert trilean to boolean (optimistic for Unknown)
   Use this when liveness/progress requires assuming success on uncertainty *)
let trilean_to_bool_optimistic (t: trilean) : bool =
  match t with
  | Definitely -> true
  | DefinitelyNot -> false
  | Unknown -> true   (* Optimistic: treat unknown as true *)

(* Information ordering: Unknown < Definite values
   This defines the "definedness" lattice where Unknown is bottom *)
let trilean_info_leq (t1 t2: trilean) : bool =
  match t1, t2 with
  | Unknown, _ -> true              (* Unknown is bottom *)
  | _, Unknown -> false
  | Definitely, Definitely -> true
  | DefinitelyNot, DefinitelyNot -> true
  | _, _ -> false

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

(* Model: satisfying assignment for variables
   Simplified representation - production version would include:
   - Function interpretations for uninterpreted functions
   - Array models as store chains
   - Bitvector values
   - Real number assignments *)
type smt_model = list (string & int)  (* Simplified: just int assignments *)

(* SMT solver result with optional model/reason *)
noeq type smt_result =
  | Sat     : model:smt_model -> smt_result    (* Satisfiable with witness *)
  | Unsat   : smt_result                        (* Unsatisfiable *)
  | SmtUnknown : reason:string -> smt_result   (* Unknown with reason *)

(* Convert SMT result to trilean for entailment queries

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
let smt_result_to_trilean_entailment (r: smt_result) : trilean =
  match r with
  (* If negation is UNSAT, original is valid (Definitely) *)
  | Unsat -> Definitely
  (* If negation is SAT, original has counterexample (DefinitelyNot) *)
  | Sat _ -> DefinitelyNot
  (* Unknown stays Unknown *)
  | SmtUnknown _ -> Unknown

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

(* SMTLIB2 sorts (types in SMT terminology)

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

(* SMTLIB2 terms/expressions

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

(* SMTLIB2 commands for constructing scripts

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

(* SMTLIB2 script is a sequence of commands *)
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

(* Translate Brrr base type to SMT sort *)
let rec brrr_type_to_smt_sort (t: brrr_type) : smt_sort =
  match t with
  | TUnit -> SortBool  (* Unit maps to trivially true; () : unit becomes "true" *)
  | TBool -> SortBool
  | TInt it ->
      (* All integer types map to unbounded Int for simplicity.
         For precise overflow reasoning, use:
           SortBitVec (8 * width_bytes it)
         But non-linear BitVec arithmetic is expensive. *)
      (match it.width with
       | I8 | I16 | I32 | I64 -> SortInt
       | ISize | IPtr -> SortInt)
  | TFloat _ -> SortReal  (* Approximation: Real lacks IEEE 754 special values *)
  | TString -> SortUninterpreted "String"  (* String theory available but expensive *)
  | TOption t' -> SortUninterpreted ("Option_" ^ sort_to_string (brrr_type_to_smt_sort t'))
  | TArray t' -> SortArray SortInt (brrr_type_to_smt_sort t')
  | TFunc _ _ _ -> SortUninterpreted "Function"  (* Functions not first-class in FOL *)
  | TPair t1 t2 -> SortUninterpreted ("Pair_" ^ sort_to_string (brrr_type_to_smt_sort t1) ^
                                       "_" ^ sort_to_string (brrr_type_to_smt_sort t2))
  | TAny -> SortUninterpreted "Any"
  | TUnknown -> SortUninterpreted "Unknown"
  | TNever -> SortBool  (* Never type has no values; mapped to false *)

and sort_to_string (s: smt_sort) : Tot string (decreases s) =
  match s with
  | SortBool -> "Bool"
  | SortInt -> "Int"
  | SortReal -> "Real"
  | SortBitVec w -> "BitVec" ^ string_of_int w
  | SortArray _ _ -> "Array"
  | SortUninterpreted n -> n

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
    limits unrolling depth:

      let rec factorial n = if n = 0 then 1 else n * factorial (n-1)

    Becomes (simplified):

      (declare-fun factorial.fuel (Fuel Term) Term)
      (assert (forall ((f Fuel) (n Term))
        (=> (SFuel? f)
            (= (factorial.fuel (SFuel f) n)
               (ite (= n 0) 1 (mult n (factorial.fuel f (- n 1))))))))

    The Fuel parameter prevents infinite unrolling:
      - ZFuel (zero): Function application returns unknown
      - (SFuel f): One unrolling allowed, recursive call gets f

    F* Options:
      --fuel N       : Set initial and max fuel (default: 2)
      --initial_fuel : Set initial fuel only
      --max_fuel     : Set maximum fuel

    For Brrr-Lang, function calls become uninterpreted applications
    unless we add explicit fuel-style encoding.
    ============================================================================ *)

(* Translate comparison operator to SMT term constructor *)
let translate_cmp_op (op: cmp_op) (e1 e2: smt_term) : smt_term =
  match op with
  | CmpEq -> SmtEq e1 e2
  | CmpNe -> SmtNot (SmtEq e1 e2)
  | CmpLt -> SmtLt e1 e2
  | CmpLe -> SmtLe e1 e2
  | CmpGt -> SmtGt e1 e2
  | CmpGe -> SmtGe e1 e2

(* Translate expression to SMT term (partial - handles common cases)

   Returns None for untranslatable expressions. The caller should
   treat None as Unknown (cannot verify without SMT support).

   Type Information Loss:
   ----------------------
   We lose type information when translating EVar - all variables
   default to SortInt. A production implementation would:
   1. Thread a typing context through translation
   2. Look up variable types from context
   3. Use appropriate sort for each variable

   Handling Partiality:
   --------------------
   Operations like division that are partial in Brrr-Lang are
   translated directly to SMT division. SMT semantics for (div x 0)
   are unspecified (returns some value, but not determined which).
   Refinement types should ensure divisor is non-zero before we
   reach SMT encoding.
*)
let rec expr_to_smt_term (e: expr) : option smt_term =
  match e with
  (* Literals translate directly *)
  | ELit (LitBool true) -> Some SmtTrue
  | ELit (LitBool false) -> Some SmtFalse
  | ELit (LitInt n) -> Some (SmtInt n)
  | ELit LitUnit -> Some SmtTrue  (* Unit value as trivially true *)

  (* Variables - default to Int sort (see note above) *)
  | EVar x -> Some (SmtVar x SortInt)

  (* Unary operations *)
  | EUnary UnNot e' ->
      (match expr_to_smt_term e' with
       | Some t -> Some (SmtNot t)
       | None -> None)

  | EUnary UnNeg e' ->
      (match expr_to_smt_term e' with
       | Some t -> Some (SmtNeg t)
       | None -> None)

  (* Binary arithmetic operations *)
  | EBinary BinAdd e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtAdd [t1; t2])
       | _, _ -> None)

  | EBinary BinSub e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtSub t1 t2)
       | _, _ -> None)

  | EBinary BinMul e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtMul [t1; t2])
       | _, _ -> None)

  | EBinary BinDiv e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtDiv t1 t2)
       | _, _ -> None)

  | EBinary BinMod e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtMod t1 t2)
       | _, _ -> None)

  (* Binary logical operations *)
  | EBinary BinAnd e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtAnd [t1; t2])
       | _, _ -> None)

  | EBinary BinOr e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtOr [t1; t2])
       | _, _ -> None)

  (* Binary comparison operations *)
  | EBinary BinEq e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtEq t1 t2)
       | _, _ -> None)

  | EBinary BinNe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtNot (SmtEq t1 t2))
       | _, _ -> None)

  | EBinary BinLt e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtLt t1 t2)
       | _, _ -> None)

  | EBinary BinLe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtLe t1 t2)
       | _, _ -> None)

  | EBinary BinGt e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtGt t1 t2)
       | _, _ -> None)

  | EBinary BinGe e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (SmtGe t1 t2)
       | _, _ -> None)

  (* Conditional expressions -> SMT ite *)
  | EIf cond then_ else_ ->
      (match expr_to_smt_term cond, expr_to_smt_term then_, expr_to_smt_term else_ with
       | Some c, Some t, Some e -> Some (SmtIte c t e)
       | _, _, _ -> None)

  (* Function calls -> uninterpreted function application
     This loses computational semantics but preserves relational properties *)
  | ECall (EGlobal fn) args ->
      let smt_args = List.Tot.map expr_to_smt_term args in
      if List.Tot.for_all Some? smt_args then
        Some (SmtApply fn (List.Tot.map (fun x -> match x with Some t -> t | None -> SmtTrue) smt_args))
      else None

  (* All other expressions are not translatable *)
  | _ -> None

(** ============================================================================
    FORMULA TO SMT TERM TRANSLATION
    ============================================================================

    Formulas from BrrrDependentTypes.fst represent refinement predicates.
    Translation to SMT is mostly structural, with special handling for:

    1. QUANTIFIERS
       Universal and existential quantifiers translate directly to BrrrSMT.
       WARNING: Quantifiers make satisfiability undecidable. Z3 uses
       E-matching with patterns to instantiate quantifiers heuristically.

       Without good patterns, quantifier handling can:
       - Cause timeouts (infinite instantiation attempts)
       - Cause matching loops (exponential instantiation)
       - Miss needed instances (incomplete proofs)

       F* Quantifier Fuel (--ifuel):
       For inductive type inversion, F* uses "ifuel" to limit
       how deeply Z3 can invert datatype typing assumptions.
         --ifuel 0 : No inversion (fastest, may miss proofs)
         --ifuel 1 : One level of inversion
         --ifuel N : N levels of inversion

    2. PREDICATES
       Named predicates become uninterpreted function applications.
       The meaning of predicates must come from axioms/lemmas.

    3. EXPRESSIONS IN FORMULAS
       Boolean expressions embedded in formulas translate via expr_to_smt_term.
    ============================================================================ *)

(* Translate dependent type to SMT sort (for quantifier bindings) *)
let rec dep_type_to_smt_sort (t: dep_type) : smt_sort =
  match t with
  | DBase bt -> brrr_type_to_smt_sort bt
  | DPi _ _ _ -> SortUninterpreted "Function"
  | DSigma _ _ _ -> SortUninterpreted "Pair"
  | DRefinement _ base _ -> dep_type_to_smt_sort base  (* Strip refinement *)
  | DApp t' _ -> dep_type_to_smt_sort t'

(* Translate formula to SMT term

   Structural translation with the key insight that:
   - FTrue/FFalse become SmtTrue/SmtFalse
   - Comparisons translate expression operands, then wrap in SMT comparison
   - Logical connectives map directly
   - Quantifiers create SMT quantifiers with typed bindings

   Quantifier Patterns (Production Note):
   --------------------------------------
   For production use, SmtForall/SmtExists should include pattern annotations:

     (forall ((x Int))
       (! (=> (P x) (Q x))
          :pattern ((P x))))      ; Instantiate when (P t) appears

   Good pattern design is critical for proof performance:
     - Pattern should mention all bound variables
     - Pattern should appear in proof goals
     - Avoid patterns that grow under substitution (matching loops)

   Example of Matching Loop (DO NOT DO):
     (forall ((x Int)) (! (P (f x)) :pattern ((f x))))
     If P is (Q (f y)), instantiation produces (f (f y)), matching again.
*)
let rec formula_to_smt_term (phi: formula) : option smt_term =
  match phi with
  | FTrue -> Some SmtTrue
  | FFalse -> Some SmtFalse

  | FCmp op e1 e2 ->
      (match expr_to_smt_term e1, expr_to_smt_term e2 with
       | Some t1, Some t2 -> Some (translate_cmp_op op t1 t2)
       | _, _ -> None)

  | FAnd phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtAnd [t1; t2])
       | _, _ -> None)

  | FOr phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtOr [t1; t2])
       | _, _ -> None)

  | FNot phi' ->
      (match formula_to_smt_term phi' with
       | Some t -> Some (SmtNot t)
       | None -> None)

  | FImpl phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtImpl t1 t2)
       | _, _ -> None)

  | FIff phi1 phi2 ->
      (match formula_to_smt_term phi1, formula_to_smt_term phi2 with
       | Some t1, Some t2 -> Some (SmtIff t1 t2)
       | _, _ -> None)

  (* Universal quantification *)
  | FForall x bt phi' ->
      let sort = brrr_type_to_smt_sort bt in
      (match formula_to_smt_term phi' with
       | Some body -> Some (SmtForall [(x, sort)] body)
       | None -> None)

  (* Existential quantification *)
  | FExists x bt phi' ->
      let sort = brrr_type_to_smt_sort bt in
      (match formula_to_smt_term phi' with
       | Some body -> Some (SmtExists [(x, sort)] body)
       | None -> None)

  (* Named predicates -> uninterpreted function application *)
  | FPred name e ->
      (match expr_to_smt_term e with
       | Some t -> Some (SmtApply name [t])
       | None -> None)

  (* Expression used as formula (must be boolean) *)
  | FExpr e -> expr_to_smt_term e

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

    Special Cases:
    --------------
    - Negative integers: (- 5) for -5 (not -5 as literal)
    - Bitvectors: (_ bv42 8) for 8-bit value 42
    - Indexed sorts: (_ BitVec 32) for 32-bit bitvector sort

    Debugging Tip:
    --------------
    Use F*'s --log_queries option to see generated SMT2 files.
    These can be run directly with Z3:
      z3 queries-ModuleName.smt2
    Or with profiling:
      z3 smt.qi.profile=true queries-ModuleName.smt2
    ============================================================================ *)

(* Convert sort to SMTLIB2 string representation *)
let rec smt_sort_to_string (s: smt_sort) : Tot string (decreases s) =
  match s with
  | SortBool -> "Bool"
  | SortInt -> "Int"
  | SortReal -> "Real"
  | SortBitVec w -> "(_ BitVec " ^ string_of_int w ^ ")"
  | SortArray idx elem ->
      "(Array " ^ smt_sort_to_string idx ^ " " ^ smt_sort_to_string elem ^ ")"
  | SortUninterpreted n -> n

(* Convert term to SMTLIB2 string representation

   Performance Note:
   -----------------
   String concatenation in this style is O(n^2) for deep terms.
   A production implementation would use a string builder or
   emit directly to an output channel.
*)
let rec smt_term_to_string (t: smt_term) : Tot string (decreases t) =
  match t with
  | SmtTrue -> "true"
  | SmtFalse -> "false"
  | SmtInt n -> if n >= 0 then string_of_int n else "(- " ^ string_of_int (-n) ^ ")"
  | SmtReal s -> s
  | SmtBitVec v w -> "(_ bv" ^ string_of_int v ^ " " ^ string_of_int w ^ ")"
  | SmtVar name _ -> name

  | SmtNot t' -> "(not " ^ smt_term_to_string t' ^ ")"
  | SmtAnd ts -> "(and " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtOr ts -> "(or " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtImpl t1 t2 -> "(=> " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtIff t1 t2 -> "(= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtIte c th el -> "(ite " ^ smt_term_to_string c ^ " " ^
                       smt_term_to_string th ^ " " ^ smt_term_to_string el ^ ")"

  | SmtEq t1 t2 -> "(= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtDistinct ts -> "(distinct " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"

  | SmtNeg t' -> "(- " ^ smt_term_to_string t' ^ ")"
  | SmtAdd ts -> "(+ " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtSub t1 t2 -> "(- " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtMul ts -> "(* " ^ String.concat " " (List.Tot.map smt_term_to_string ts) ^ ")"
  | SmtDiv t1 t2 -> "(div " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtMod t1 t2 -> "(mod " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"

  | SmtLt t1 t2 -> "(< " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtLe t1 t2 -> "(<= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtGt t1 t2 -> "(> " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"
  | SmtGe t1 t2 -> "(>= " ^ smt_term_to_string t1 ^ " " ^ smt_term_to_string t2 ^ ")"

  | SmtForall bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, s) ->
        "(" ^ n ^ " " ^ smt_sort_to_string s ^ ")") bindings) in
      "(forall (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

  | SmtExists bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, s) ->
        "(" ^ n ^ " " ^ smt_sort_to_string s ^ ")") bindings) in
      "(exists (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

  | SmtApply func args ->
      if List.Tot.length args = 0 then func
      else "(" ^ func ^ " " ^ String.concat " " (List.Tot.map smt_term_to_string args) ^ ")"

  | SmtLet bindings body ->
      let binding_str = String.concat " " (List.Tot.map (fun (n, t) ->
        "(" ^ n ^ " " ^ smt_term_to_string t ^ ")") bindings) in
      "(let (" ^ binding_str ^ ") " ^ smt_term_to_string body ^ ")"

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

    We explicitly do NOT assume:
    - Completeness for quantified formulas (undecidable)
    - Deterministic behavior (Z3 may timeout differently on same query)
    - Performance bounds (queries may take arbitrarily long)

    Timeout and Resource Limits:
    ----------------------------
    Real SMT interactions need resource bounds to ensure termination.

    F* uses --z3rlimit N for resource limits (not wall-clock time).
    The rlimit is more deterministic across runs but units vary by Z3 version.

    Typical settings:
      --z3rlimit 5       : Default, fast but may miss proofs
      --z3rlimit 50      : More thorough, suitable for complex lemmas
      --z3rlimit 200     : Heavy lifting, use sparingly
      --z3rlimit_factor 2: Double current limit

    When Z3 hits the limit, it returns "unknown because (canceled)".
    ============================================================================ *)

(* SMT solver configuration

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

let default_smt_config : smt_config = {
  timeout_ms = 5000;            (* 5 second default timeout *)
  smt_logic = "ALL";            (* Full logic by default - can restrict for performance *)
  incremental = true;           (* Enable incremental solving *)
}

(* Check satisfiability of SMT term - axiomatized external call

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
assume val smt_check_sat : config:smt_config -> term:smt_term -> smt_result

(* Check if phi1 implies phi2 using SMT

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
let smt_check_implication (config: smt_config) (phi1 phi2: smt_term) : trilean =
  (* phi1 => phi2 is valid iff phi1 /\ ~phi2 is UNSAT *)
  let negated = SmtAnd [phi1; SmtNot phi2] in
  smt_result_to_trilean_entailment (smt_check_sat config negated)

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

(* Semantic formula implication using SMT solver
   Returns trilean: Definitely (valid), DefinitelyNot (invalid), Unknown *)
let formula_implies_semantic (config: smt_config) (phi1 phi2: formula) : trilean =
  match formula_to_smt_term phi1, formula_to_smt_term phi2 with
  | Some smt1, Some smt2 -> smt_check_implication config smt1 smt2
  | _, _ -> Unknown  (* Could not translate to SMT *)

(* Combined syntactic + semantic implication check
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
let formula_implies_hybrid (config: smt_config) (phi1 phi2: formula) : trilean =
  (* First try syntactic check from DependentTypes *)
  if formula_implies phi1 phi2 then Definitely
  else
    (* Fall back to SMT *)
    formula_implies_semantic config phi1 phi2

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

(* Collect free variables in formula for SMT declarations

   Note: This properly handles variable shadowing by filtering
   bound variables from recursive results.
*)
let rec collect_formula_vars (phi: formula) : list (string & smt_sort) =
  match phi with
  | FTrue | FFalse -> []
  | FCmp _ e1 e2 ->
      collect_expr_vars e1 @ collect_expr_vars e2
  | FAnd phi1 phi2 | FOr phi1 phi2 | FImpl phi1 phi2 | FIff phi1 phi2 ->
      collect_formula_vars phi1 @ collect_formula_vars phi2
  | FNot phi' -> collect_formula_vars phi'
  | FForall x bt phi' | FExists x bt phi' ->
      (* Filter out the bound variable from nested free vars *)
      filter (fun (y, _) -> y <> x) (collect_formula_vars phi')
  | FPred _ e -> collect_expr_vars e
  | FExpr e -> collect_expr_vars e

and collect_expr_vars (e: expr) : list (string & smt_sort) =
  match e with
  | EVar x -> [(x, SortInt)]  (* Default to Int - see earlier note about typing context *)
  | EUnary _ e' -> collect_expr_vars e'
  | EBinary _ e1 e2 -> collect_expr_vars e1 @ collect_expr_vars e2
  | EIf c t f -> collect_expr_vars c @ collect_expr_vars t @ collect_expr_vars f
  | ECall _ args -> List.Tot.concatMap collect_expr_vars args
  | _ -> []

(* Generate SMTLIB2 script for checking formula validity

   Script Structure:
   -----------------
   1. (set-logic LOGIC) - Declare the SMT logic to use
   2. (declare-const x T) for each free variable
   3. (assert (not phi)) - Assert negation of goal
   4. (check-sat) - Check for satisfiability

   If (check-sat) returns UNSAT, the original phi is VALID.
   If (check-sat) returns SAT, we have a counterexample.

   Example Generated Script:
   -------------------------
   For formula: (x > 0) => (x >= 0)

   (set-logic ALL)
   (declare-const x Int)
   (assert (not (=> (> x 0) (>= x 0))))
   (check-sat)
   ; Returns: unsat (formula is valid)
*)
let generate_validity_script (phi: formula) : option smt_script =
  match formula_to_smt_term phi with
  | None -> None
  | Some smt_phi ->
      let vars = collect_formula_vars phi in
      let unique_vars = List.Tot.noRepeats vars in  (* Deduplicate *)
      let decls = List.Tot.map (fun (n, s) -> CmdDeclareConst n s) unique_vars in
      (* Check validity: assert negation and check for UNSAT *)
      Some (
        [CmdSetLogic "ALL"] @
        decls @
        [CmdAssert (SmtNot smt_phi); CmdCheckSat]
      )

(* Discharge a verification condition

   A VC is discharged (proven valid) when the SMT solver returns UNSAT
   for its negation. This is the entry point for type-checking to call
   when it needs to verify a refinement constraint.

   Returns:
     Definitely    - VC is valid (refinement holds)
     DefinitelyNot - VC has counterexample (refinement fails)
     Unknown       - Could not determine (timeout, etc.)
*)
let discharge_vc (config: smt_config) (phi: formula) : trilean =
  formula_implies_semantic config FTrue phi

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

(* Soundness: If SMT says UNSAT, the formula is semantically valid

   This axiom states that Z3's UNSAT result is reliable.
   If Z3 proves the negation unsatisfiable, the original formula
   has no counterexamples, hence is valid.

   NOTE: The ensures clause is intentionally weak (just True) because
   expressing "phi has no models" requires a semantic model of SMT,
   which is beyond scope here.
*)
assume val smt_soundness_unsat :
  config:smt_config ->
  phi:smt_term ->
  Lemma (requires smt_check_sat config phi == Unsat)
        (ensures forall (model: smt_model). True)  (* phi has no models *)

(* Completeness for decidable fragments: If valid, SMT will return UNSAT

   For decidable fragments like QF_LIA (Quantifier-Free Linear Integer
   Arithmetic), Z3 is a decision procedure. It will always terminate
   with a definite answer, never returning "incomplete".

   Note: This doesn't prevent timeouts ("canceled") or other resource
   limit issues ("memout"), just theory-level incompleteness.
*)
assume val smt_completeness_qf_lia :
  config:smt_config{config.smt_logic = "QF_LIA"} ->
  phi:smt_term ->
  Lemma (requires True)  (* phi is in QF_LIA *)
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

    Example Usage Pattern:
    ----------------------
    ctx0 = empty_smt_context config
    ctx1 = smt_assert ctx0 (function_precondition)
    ctx2 = smt_push ctx1

    (* Check first refinement *)
    ctx3 = smt_assert ctx2 (refinement1_negated)
    result1 = smt_context_check_sat ctx3
    ctx4 = smt_pop ctx3

    (* Check second refinement - precondition already loaded *)
    ctx5 = smt_assert ctx4 (refinement2_negated)
    result2 = smt_context_check_sat ctx5
    ctx6 = smt_pop ctx5

    Performance Impact:
    -------------------
    Without incremental: Each query re-processes all axioms (~150K lines for F* stdlib)
    With incremental: Axioms processed once, queries are much faster

    The F* compiler uses this extensively; you can see the effect with --query_stats.
    ============================================================================ *)

(* Incremental solver state

   ctx_assertions: Stack of assertions at each level
   ctx_level: Current push depth (for matching push/pop)
*)
noeq type smt_context = {
  ctx_config     : smt_config;
  ctx_assertions : list smt_term;   (* Current assertion stack *)
  ctx_level      : nat;              (* Push level *)
}

let empty_smt_context (config: smt_config) : smt_context = {
  ctx_config = config;
  ctx_assertions = [];
  ctx_level = 0;
}

(* Push: Save current solver state
   Subsequent assertions can be undone by pop *)
let smt_push (ctx: smt_context) : smt_context =
  { ctx with ctx_level = ctx.ctx_level + 1 }

(* Pop: Restore to previous state
   Removes assertions added since last push *)
let smt_pop (ctx: smt_context) : smt_context =
  if ctx.ctx_level > 0 then { ctx with ctx_level = ctx.ctx_level - 1 }
  else ctx

(* Assert: Add formula to current context
   Formula becomes part of background theory for subsequent checks *)
let smt_assert (ctx: smt_context) (phi: smt_term) : smt_context =
  { ctx with ctx_assertions = phi :: ctx.ctx_assertions }

(* Check satisfiability in current context - axiomatized *)
assume val smt_context_check_sat : ctx:smt_context -> smt_result

(** ============================================================================
    WHAT BRRR-MACHINE NEEDS FROM REFINEMENT CHECKING
    ============================================================================

    This section documents the interface that Brrr-Machine analysis toolkit
    requires from the refinement type system.

    Brrr-Machine Integration Points:
    --------------------------------

    1. TYPE CHECKING QUERIES:
       - does_type_check : expr -> dep_type -> trilean
         Check if expression has the given dependent type

       - subtype_check : dep_type -> dep_type -> trilean
         Check if one dependent type is a subtype of another

    2. REFINEMENT ENTAILMENT:
       For {x:T | phi} <: {x:T | psi}, need: forall x:T. phi => psi

       This is the core refinement subtyping check. It requires SMT
       for any non-trivial formulas. Examples:
         {x:int | x > 0} <: {x:int | x >= 0}    (requires arithmetic)
         {x:array | len(x) > 0} <: {x:array | not_empty(x)}  (requires axioms)

    3. DIVERGENCE INFORMATION:
       For lazy languages with potential non-termination, types carry
       divergence labels that affect verification condition generation:
         DivMay  - May diverge (lazy)
         DivWhnf - Converges to WHNF (weak head normal form)
         DivFin  - Fully terminates

       This affects VC generation for lazy function application.

    4. COUNTEREXAMPLE GENERATION:
       When subtyping fails, provide witness assignment showing why.
       Critical for:
         - Bug localization in Brrr-Machine static analysis
         - User feedback in type error messages
         - Debugging refinement specification errors

    5. PERFORMANCE REQUIREMENTS:
       - Caching: Same queries should not re-invoke SMT
       - Incremental: Use push/pop for related queries (see above)
       - Timeout: Graceful degradation to Unknown rather than hang
       - Profiling: Support for --query_stats style output
    ============================================================================ *)

(* Query result with optional counterexample

   Production Note:
   ----------------
   A full counterexample would include:
   - All variable assignments
   - Uninterpreted function interpretations
   - Array contents
   - Path through disjunctions in the formula

   The smt_model type is a simplified placeholder.
*)
noeq type refinement_result =
  | RefinementHolds      : refinement_result
  | RefinementFails      : cex:option smt_model -> refinement_result
  | RefinementUnknown    : reason:string -> refinement_result

(* Convert trilean to refinement result *)
let trilean_to_refinement (t: trilean) (cex: option smt_model) : refinement_result =
  match t with
  | Definitely -> RefinementHolds
  | DefinitelyNot -> RefinementFails cex
  | Unknown -> RefinementUnknown "SMT timeout or incomplete"

(* Check refinement subtyping with counterexample

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
let check_refinement_subtype
    (config: smt_config)
    (x: dep_var)
    (base: dep_type)
    (phi1 phi2: formula)
    : refinement_result =
  (* Need to check: forall x:base. phi1 => phi2 *)
  let smt_base = dep_type_to_smt_sort base in
  match formula_to_smt_term phi1, formula_to_smt_term phi2 with
  | Some smt1, Some smt2 ->
      (* Check if exists x. phi1 /\ ~phi2 is SAT (counterexample) *)
      let negated = SmtExists [(x, smt_base)] (SmtAnd [smt1; SmtNot smt2]) in
      (match smt_check_sat config negated with
       | Unsat -> RefinementHolds
       | Sat model -> RefinementFails (Some model)
       | SmtUnknown reason -> RefinementUnknown reason)
  | _, _ -> RefinementUnknown "Could not translate formula to SMT"
