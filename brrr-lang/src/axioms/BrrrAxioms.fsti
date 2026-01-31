(**
 * BrrrLang.Axioms - Interface
 *
 * SINGLE SOURCE OF TRUTH for all axioms in brrr-lang.
 *
 * This module declares properties that are:
 *   - TRUE_AXIOM: Fundamentally unprovable (halting, external systems, Gödel)
 *   - SEMANTIC_AXIOM: Depend on external invariants (parser, programmer intent)
 *   - DEFERRED_PROOF: Provable but complex, deferred for future work
 *
 * NO CORE MODULE IMPORTS - avoids circular dependencies.
 * Uses polymorphic signatures instantiated by client modules.
 *
 * Implementation uses admit() - these are axioms by design.
 *
 * References: AXIOMS_REPORT.md for full justifications.
 *)
(**
 * ============================================================================
 * CRITICAL SOUNDNESS WARNING
 * ============================================================================
 *
 * This interface declares 36 TRUE AXIOMS that form the irreducible Trusted
 * Computing Base (TCB) of brrr-lang. Each axiom represents a trust assumption
 * that CANNOT be proven within the F* verification framework.
 *
 * SOUNDNESS IMPLICATIONS:
 *
 *   If ANY axiom in this file is FALSE, proofs built upon it are UNSOUND.
 *   For example:
 *     - If SMT solver (Z3) has a bug, ALL verified lemmas may be invalid
 *     - If memory model correspondence fails, ownership proofs break
 *     - If parser produces incorrect AST, analysis operates on wrong program
 *
 * WHY THESE AXIOMS ARE NECESSARY:
 *
 *   1. FUNDAMENTAL LIMITS (Turing, Gödel, Rice):
 *      Certain properties are mathematically undecidable. No amount of
 *      engineering can prove the halting problem decidable.
 *
 *   2. EXTERNAL SYSTEMS:
 *      We verify F* code, but cannot verify Z3, CPython, hardware, etc.
 *      We MUST trust these external components at some level.
 *
 *   3. PROGRAMMER INTENT:
 *      Security policies and declassification intent exist in the programmer's
 *      mind - outside any formal system.
 *
 * HOW TO USE THIS MODULE SAFELY:
 *
 *   1. NEVER add new axioms without thorough justification
 *   2. AUDIT this file regularly against the specification
 *   3. Document WHY each axiom cannot be proven
 *   4. Prefer DEFERRED_PROOF over TRUE_AXIOM when possible
 *   5. Keep axiom count MINIMAL - currently 36, target is no increase
 *
 * F* IMPLEMENTATION PATTERN:
 *
 *   Interface (.fsti):  val my_axiom : unit -> Lemma (ensures True)
 *   Implementation (.fst): let my_axiom () = admit ()
 *
 *   The admit() is intentional - axioms CANNOT be proven. Using admit() for
 *   axioms is the correct F* pattern. See FSTAR_REFERENCE.md Section 13.
 *
 *   From Proof of Fstar (fstar_pop_book.md, line 4581-4589):
 *   "Both `assume` and `admit` can be helpful when you're working through
 *    a proof, but a proof isn't done until it's free of them."
 *
 *   EXCEPTION: Axioms are DESIGNED to use admit(). They represent trust
 *   assumptions, not incomplete proofs.
 *
 * RELATIONSHIP TO SPEC:
 *
 *   brrr_lang_spec_v0.4.tex, Chapter "Cross-Language Boundaries" defines
 *   an Axiom Lattice for language safety guarantees:
 *
 *       AxAll
 *      /  |  \
 *   AxMemSafe AxTypeSafe AxNullSafe
 *      \  |  /
 *      AxPartial
 *         |
 *      AxNone
 *
 *   Different languages provide different guarantees:
 *     axioms(Python) = {AxMemSafe, AxLeakFree}
 *     axioms(Rust) = {AxMemSafe, AxTypeSafe, AxRaceFree, AxLeakFree}
 *     axioms(C) = {AxNone}  -- unsafe, manual memory
 *
 *   This Axioms module declares the MECHANIZATION-LEVEL trust assumptions,
 *   which are orthogonal to but underlie the language-level axiom lattice.
 *
 * ERRATA AND KNOWN ISSUES (see SPECIFICATION_ERRATA.md):
 *
 *   - Honda 2008 session type formulation contains errors (Chapter 5)
 *   - Association relation replaces coherence (Scalas & Yoshida 2019)
 *   - Mode context join requires extended mode compatibility (Chapter 2)
 *   - Integer division needs explicit input range preconditions (Chapter 1)
 *
 * ============================================================================
 *)
module BrrrAxioms

open FStar.List.Tot

(* ============================================================================
   CLASSIFICATION TYPES
   ============================================================================

   These types classify WHY a property is assumed rather than proven.

   USAGE IN CLIENT MODULES:

     let check_axiom_class () =
       match termination_fuel_exists_class () with
       | TrueAxiom -> "Fundamentally unprovable"
       | SemanticAxiom -> "Depends on external invariants"
       | DeferredProof -> "Provable but deferred"

   ============================================================================ *)

(** Axiom classification - why this property is assumed rather than proven

    TrueAxiom:
      Property is MATHEMATICALLY UNPROVABLE within any formal system.
      Examples: Halting problem, Gödel incompleteness, Rice's theorem.
      These represent fundamental limits of computation and logic.
      NO amount of engineering effort can prove these.

    SemanticAxiom:
      Property depends on EXTERNAL INVARIANTS not captured in the type system.
      Examples: Parser correctness, programmer intent, policy validity.
      These could theoretically be proven with a sufficiently expressive system,
      but require trusting external components or human judgment.

    DeferredProof:
      Property IS PROVABLE but requires significant mechanization effort.
      Examples: CompCert-style translation proofs, metatheory mechanization.
      These are "IOUs" - proofs we commit to doing but haven't finished.
      Track these for eventual completion.
*)
type axiom_class =
  | TrueAxiom      (* Fundamentally unprovable: halting, Gödel, external systems *)
  | SemanticAxiom  (* Depends on external invariants not in type system *)
  | DeferredProof  (* Provable but requires significant mechanization effort *)

(** Decidability status for analysis problems

    This classification helps determine what KIND of approximation
    is theoretically possible for each analysis problem.

    Decidable:
      An algorithm exists that ALWAYS terminates with CORRECT answer.
      Analysis can be EXACT (no false positives or negatives).
      Example: Type checking for simple type systems.

    SemiDecidable:
      Can CONFIRM positive instances (will eventually say "yes" if true).
      May DIVERGE on negative instances (run forever if false).
      Example: "Does this Turing machine halt on input X?"

    Undecidable:
      NO algorithm exists - proven impossible by reduction to halting.
      Analysis MUST over-approximate or under-approximate.
      Example: "Does program P terminate on all inputs?"

    ComplexityBounded:
      Decidable but INTRACTABLE - requires exponential/worse resources.
      Practical analysis requires approximation or heuristics.
      Example: SAT (NP-complete), QBF (PSPACE-complete).
*)
type decidability =
  | Decidable           (* Algorithm exists that always terminates with correct answer *)
  | SemiDecidable       (* Can confirm positive instances, may diverge on negative *)
  | Undecidable         (* No algorithm exists - halting problem, Rice's theorem *)
  | ComplexityBounded   (* Decidable but intractable: NP-complete, PSPACE-complete *)

(** Why a property is fundamentally unprovable

    This provides the THEORETICAL JUSTIFICATION for each TRUE_AXIOM.
    Every axiom should cite the specific impossibility result.

    HaltingProblem (Turing 1936):
      Reduces to "Does TM M halt on input X?"
      Affects: Termination analysis, loop bounds, fuel sufficiency.

    RicesTheorem (Rice 1953):
      "Any non-trivial semantic property of programs is undecidable."
      Affects: Almost all program analyses (constant propagation, etc.)

    GodelIncompleteness (Gödel 1931):
      "Sufficiently powerful systems cannot prove their own consistency."
      Affects: F* soundness, SMT correctness within F*.

    ExternalSystem:
      Property depends on behavior of code/hardware outside formal model.
      Affects: Parser, runtime, compiler, hardware.

    InfiniteEnumeration:
      Would require checking infinitely many cases.
      Affects: Data-race freedom (all interleavings), exhaustive testing.

    ComplexityBarrier:
      Decidable but requires infeasible resources (NP-hard, PSPACE).
      Affects: SAT-based analyses, model checking.

    ProgrammerIntent:
      Property exists in programmer's mind, not in formal artifacts.
      Affects: Declassification, security label assignment.

    EnvironmentDependent:
      Property varies with target platform/environment.
      Affects: ABI, calling conventions, OS behavior.

    PolicySpecification:
      Property is a SPECIFICATION, not a theorem.
      User DEFINES the policy; we enforce it, not derive it.
      Affects: Security labels, access control lists.

    FoundationalMath:
      Property is a MATHEMATICAL AXIOM at the foundations of the theory.
      Examples: Kolmogorov probability axioms, Peano axioms, ZFC.
      Cannot prove axioms - they DEFINE the system.
*)
type unprovability_reason =
  | HaltingProblem      (* Reduces to halting problem (Turing 1936) *)
  | RicesTheorem        (* Non-trivial semantic property (Rice 1953) *)
  | GodelIncompleteness (* Self-referential consistency (Gödel 1931) *)
  | ExternalSystem      (* Property of hardware/runtime/parser outside formal model *)
  | InfiniteEnumeration (* Would require enumerating infinite set *)
  | ComplexityBarrier   (* Intractable: NP-hard, PSPACE-complete, etc. *)
  | ProgrammerIntent    (* Exists in programmer's mind, outside formal reasoning *)
  | EnvironmentDependent (* Depends on target environment/platform *)
  | PolicySpecification (* User-provided policy, not a theorem *)
  | FoundationalMath    (* Mathematical axioms: Kolmogorov, Peano, ZFC - cannot be proven *)


(* ============================================================================
   CATEGORY 1: HALTING AND DECIDABILITY
   ============================================================================
   TRUE_AXIOM: Fundamental computational limitations (Turing, Rice, Gödel).

   THEORETICAL FOUNDATION:

     These axioms encode the fundamental limits of computation discovered
     by Turing (1936), Rice (1953), and Gödel (1931). No verification system
     can escape these limits.

   IMPACT ON ANALYSIS:

     Because these properties are undecidable, brrr-lang analyses MUST:
     1. Over-approximate (sound but incomplete) - report possible issues
     2. Under-approximate (complete but unsound) - miss some issues
     3. Use bounded techniques (fuel, depth limits) - may timeout

   USAGE PATTERN:

     When an analysis uses one of these axioms, document:
       - Which axiom is assumed
       - What the consequence of violation would be
       - What mitigations exist (bounds, timeouts, warnings)

   ============================================================================ *)

(** 1.1 Program Termination Axiom - Halting Problem

    STATEMENT: If a program terminates mathematically, sufficient fuel exists.

    FORMAL: forall p. terminates(p) ==> exists fuel. eval(p, fuel) <> Diverged

    WHY UNPROVABLE (HaltingProblem):
      This is EXACTLY the halting problem. If we could prove/disprove this
      for arbitrary programs, we could decide halting.

    USAGE IN BRRR-LANG:
      The big-step evaluator uses fuel to bound recursion. This axiom
      says that if the mathematical semantics says a program terminates,
      SOME fuel value is sufficient. We cannot COMPUTE that fuel.

    MITIGATION:
      - Use generous default fuel (e.g., 2^20)
      - Allow user-specified fuel bounds
      - Report "timeout" rather than "loops forever"

    LOCATION: BrrrEval.fst
    AFFECTS: All termination-dependent proofs
*)
val termination_fuel_exists : unit ->
  Lemma (ensures True)  (* Actual: terminates ==> exists fuel. ~diverged *)

val termination_fuel_exists_class : unit -> Tot axiom_class
val termination_fuel_exists_reason : unit -> Tot unprovability_reason

(** 1.2 Loop Divergence Effect - Halting Problem

    STATEMENT: While loops always carry the Diverge effect.

    FORMAL: while c {b} : Unit [Div]

    WHY UNPROVABLE (HaltingProblem):
      Determining if a while loop terminates is exactly the halting problem.
      A terminating while loop would have effect Tot, not Div.

    SPECIFICATION REFERENCE:
      brrr_lang_spec_v0.4.tex:2676-2680
      "While loops are conservatively marked Div because termination
       is undecidable in general."

    DESIGN DECISION:
      Rather than require termination proofs for all loops, brrr-lang
      conservatively assigns Div effect. Users wanting Tot must:
      1. Use recursion with a decreases clause
      2. Prove loop termination externally
*)
val loop_divergence_conservative : unit ->
  Lemma (ensures True)  (* Actual: while c {b} : Unit [Div] *)

val loop_divergence_class : unit -> Tot axiom_class
val loop_divergence_reason : unit -> Tot unprovability_reason

(** 1.3 Exhaustiveness with Guards - Halting Problem

    STATEMENT: Pattern exhaustiveness is undecidable when guards are present.

    FORMAL: guards can encode arbitrary computation

    WHY UNPROVABLE (HaltingProblem):
      Pattern guards like `| x when f(x) -> ...` can encode arbitrary
      computation. Checking if guards cover all cases = halting problem.

    SPECIFICATION REFERENCE:
      brrr_lang_spec_v0.4.tex:3505-3517
      "When pattern guards are present, exhaustiveness checking is
       necessarily incomplete. The checker may reject valid exhaustive
       patterns or fail to detect non-exhaustive ones."

    MITIGATION:
      - Warn when guards present
      - Require explicit wildcard for guarded matches
      - Static analysis may approximate (over/under)
*)
val exhaustiveness_with_guards : unit ->
  Lemma (ensures True)  (* Actual: guards can encode arbitrary computation *)

val exhaustiveness_guards_class : unit -> Tot axiom_class
val exhaustiveness_guards_reason : unit -> Tot unprovability_reason

(** 1.4 Deadlock Detection - Undecidable/PSPACE-complete

    STATEMENT: General deadlock detection is undecidable for infinite state.

    WHY UNPROVABLE:
      - Infinite state spaces: Undecidable (reduces to halting)
      - Finite state spaces: PSPACE-complete (exponential blowup)

    SPECIFICATION REFERENCE:
      synthesis_part6.tex:518

    PRACTICAL APPROACH:
      - Use bounded model checking
      - Apply type-based deadlock freedom (priority annotations)
      - Over-approximate with static analysis
*)
val deadlock_detection : unit ->
  Lemma (ensures True)

val deadlock_detection_class : unit -> Tot axiom_class
val deadlock_detection_decidability : unit -> Tot decidability

(** 1.5 Liveness Properties - Rice's Theorem

    STATEMENT: "Eventually reaches good state" is undecidable.

    WHY UNPROVABLE (RicesTheorem):
      Liveness is a semantic property of programs. By Rice's theorem,
      non-trivial semantic properties are undecidable.

    SPECIFICATION REFERENCE:
      synthesis_part14.tex:1910-1913

    RELATION TO SAFETY:
      Safety: "Bad thing never happens" - can over-approximate
      Liveness: "Good thing eventually happens" - harder to approximate
*)
val liveness_undecidable : unit ->
  Lemma (ensures True)

val liveness_class : unit -> Tot axiom_class
val liveness_reason : unit -> Tot unprovability_reason

(** 1.6 Termination Channel Detection - Halting Problem variant

    STATEMENT: Termination-sensitive noninterference (TSNI) is undecidable.

    WHY UNPROVABLE (HaltingProblem):
      TSNI asks: "Can an attacker distinguish secret values by observing
      whether the program terminates?" This requires deciding termination.

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:689-693

    SECURITY IMPLICATION:
      Termination channels can leak secrets. Example:
        if secret then while(true){} else return
      Attacker learns secret bit from termination behavior.
*)
val termination_channel_detection : unit ->
  Lemma (ensures True)

val termination_channel_class : unit -> Tot axiom_class
val termination_channel_reason : unit -> Tot unprovability_reason

(** 1.7 Timing Channel Freedom - External System + Halting

    STATEMENT: Constant-time verification is necessarily approximate.

    WHY UNPROVABLE:
      1. Microarchitectural timing (caches, branch predictors) is external
      2. Even source-level constant-time reduces to halting

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:1124-1138

    MITIGATION:
      - Verify against abstract cost model
      - Use hardware support (constant-time instructions)
      - Test empirically
*)
val timing_channel_freedom : unit ->
  Lemma (ensures True)

val timing_channel_class : unit -> Tot axiom_class
val timing_channel_reason : unit -> Tot unprovability_reason

(** 1.8 Ranking Function Synthesis - Halting Problem

    STATEMENT: Auto-synthesizing ranking functions equals proving termination.

    WHY UNPROVABLE (HaltingProblem):
      A ranking function proves termination. If we could automatically
      synthesize one for any terminating program, we'd solve halting.

    SPECIFICATION REFERENCE:
      synthesis_part7.tex:1455-1461

    PRACTICAL APPROACH:
      - Require user-provided decreases clauses
      - Use heuristics for common patterns
      - Template-based synthesis for restricted classes
*)
val ranking_function_synthesis : unit ->
  Lemma (ensures True)

val ranking_function_class : unit -> Tot axiom_class
val ranking_function_reason : unit -> Tot unprovability_reason

(** 1.9 Linearizability Verification - NP-complete

    STATEMENT: Finding valid linearization is NP-complete.

    WHY BOUNDED (ComplexityBarrier):
      Given a concurrent execution history, checking if it's linearizable
      requires finding a sequential ordering. This is NP-complete.

    SPECIFICATION REFERENCE:
      synthesis_part7.tex:1316-1323

    PRACTICAL APPROACH:
      - SAT-based linearizability checking (exponential worst case)
      - Proof-based approach (user provides linearization points)
*)
val linearizability_verification : unit ->
  Lemma (ensures True)

val linearizability_class : unit -> Tot axiom_class
val linearizability_decidability : unit -> Tot decidability

(** 1.10 Magic Wand Reasoning - PSPACE-complete

    STATEMENT: Full separation logic magic wand is PSPACE-complete.

    WHY BOUNDED (ComplexityBarrier):
      The magic wand (P -* Q) represents "if given P, can produce Q".
      Checking validity with unrestricted magic wand is PSPACE-complete.

    SPECIFICATION REFERENCE:
      synthesis_part7.tex:1664

    PRACTICAL APPROACH:
      - Restrict magic wand usage
      - Use symbolic execution for common patterns
      - Frame rule avoids magic wand in many cases
*)
val magic_wand_reasoning : unit ->
  Lemma (ensures True)

val magic_wand_class : unit -> Tot axiom_class
val magic_wand_decidability : unit -> Tot decidability

(** 1.11 Widening Termination - Design Axiom

    STATEMENT: Ascending chain condition for widening operators.

    WHY AXIOMATIC:
      Widening is a DESIGN CHOICE that trades precision for termination.
      We DEFINE widening operators to satisfy ascending chain condition.

    SPECIFICATION REFERENCE:
      synthesis_part2.tex:828-834

    THEORETICAL BACKGROUND:
      Cousot & Cousot (1977): Widening forces termination by bounding
      the height of ascending chains in the abstract domain.
*)
val widening_termination : unit ->
  Lemma (ensures True)

val widening_class : unit -> Tot axiom_class
val widening_reason : unit -> Tot unprovability_reason

(** 1.12 Transfer Function Monotonicity - Rice's Theorem

    STATEMENT: Cannot verify arbitrary functions are monotonic.

    WHY UNPROVABLE (RicesTheorem):
      Monotonicity is a semantic property. By Rice's theorem, checking
      "is f monotonic?" for arbitrary f is undecidable.

    SPECIFICATION REFERENCE:
      synthesis_part2.tex:737-741

    PRACTICAL APPROACH:
      - Construct transfer functions from monotonic primitives
      - Prove monotonicity for each hand-written function
*)
val transfer_monotonicity : unit ->
  Lemma (ensures True)

val transfer_monotonicity_class : unit -> Tot axiom_class
val transfer_monotonicity_reason : unit -> Tot unprovability_reason

(** 1.13 Call Graph Completeness - Halting + Rice

    STATEMENT: Call graphs necessarily over-approximate.

    WHY UNPROVABLE:
      - Indirect calls through function pointers: need points-to analysis
      - Virtual dispatch: need type hierarchy + actual types
      - Both reduce to undecidable problems

    SPECIFICATION REFERENCE:
      synthesis_part12.tex:768-769

    CONSEQUENCE:
      Taint analysis, escape analysis, etc. that depend on call graph
      inherit this imprecision. Sound analyses MUST over-approximate.
*)
val call_graph_completeness : unit ->
  Lemma (ensures True)

val call_graph_class : unit -> Tot axiom_class
val call_graph_reason : unit -> Tot unprovability_reason

(** 1.14 Points-To Analysis Soundness - Rice's Theorem

    STATEMENT: May-alias is a non-trivial semantic property.

    WHY UNPROVABLE (RicesTheorem):
      "Can pointer p alias pointer q?" is a semantic property of the
      program's execution, hence undecidable by Rice's theorem.

    SPECIFICATION REFERENCE:
      synthesis_part12.tex:686-687

    PRACTICAL APPROACH:
      - Over-approximate: report "may alias" conservatively
      - Use context/flow sensitivity to reduce false positives
*)
val points_to_soundness : unit ->
  Lemma (ensures True)

val points_to_class : unit -> Tot axiom_class
val points_to_reason : unit -> Tot unprovability_reason

(** 1.15 Data-Race Freedom - Infinite Enumeration

    STATEMENT: DRF requires enumerating all interleavings.

    WHY UNPROVABLE (InfiniteEnumeration):
      Concurrent programs have exponentially many (or infinite) interleavings.
      Checking each for data races is infeasible.

    SPECIFICATION REFERENCE:
      synthesis_part12.tex:541

    PRACTICAL APPROACH:
      - Type-based DRF (ownership, modes)
      - Dynamic race detection (samples interleavings)
      - Bounded model checking
*)
val drf_determination : unit ->
  Lemma (ensures True)

val drf_class : unit -> Tot axiom_class
val drf_reason : unit -> Tot unprovability_reason

(** 1.16 Effect Divergence Absence - Halting Problem

    STATEMENT: Proving no Div effect equals proving termination.

    WHY UNPROVABLE (HaltingProblem):
      The Div effect indicates potential non-termination.
      Proving a function is Tot (no Div) requires proving termination.

    SPECIFICATION REFERENCE:
      synthesis_part12.tex:617-625
*)
val divergence_absence : unit ->
  Lemma (ensures True)

val divergence_absence_class : unit -> Tot axiom_class
val divergence_absence_reason : unit -> Tot unprovability_reason

(** 1.17 Taint Analysis Completeness - Rice's Theorem

    STATEMENT: "Data reaches sink unsanitized" is a non-trivial property.

    WHY UNPROVABLE (RicesTheorem):
      Whether tainted data flows to a sink through all possible paths
      is a semantic property of the program.

    SPECIFICATION REFERENCE:
      synthesis_part12.tex:141-147

    PRACTICAL APPROACH:
      - IFDS framework provides polynomial-time SOUND analysis
      - May report false positives (flows that can't happen)
*)
val taint_completeness : unit ->
  Lemma (ensures True)

val taint_class : unit -> Tot axiom_class
val taint_reason : unit -> Tot unprovability_reason

(** 1.18 Interleaved Dyck Undecidability - Post Correspondence

    STATEMENT: Context + field sensitivity reduces to PCP.

    WHY UNPROVABLE (HaltingProblem derivative):
      Interleaved Dyck languages (matching brackets from different alphabets)
      are undecidable. CFL-reachability with both context and field sensitivity
      requires interleaved Dyck languages.

    SPECIFICATION REFERENCE:
      synthesis_appendices.tex:351

    PRACTICAL APPROACH:
      - Choose one: context OR field sensitivity, not both
      - Use k-limiting to bound precision
*)
val interleaved_dyck : unit ->
  Lemma (ensures True)

val interleaved_dyck_class : unit -> Tot axiom_class
val interleaved_dyck_reason : unit -> Tot unprovability_reason


(* ============================================================================
   END OF CATEGORY 1: 18 TRUE_AXIOM declarations

   SUMMARY: These 18 axioms encode fundamental computational limits.
   They are NOT bugs or missing proofs - they represent mathematical truths
   about what can and cannot be computed.
   ============================================================================ *)


(* ============================================================================
   CATEGORY 2: EXTERNAL SYSTEM TRUST (MINIMAL)
   ============================================================================
   These are the irreducible trust assumptions about external systems.
   We minimize trust by:
   1. Using abstract interfaces instead of trusting implementations
   2. Unifying GC/manual memory under one memory model axiom
   3. Making trust boundaries explicit and auditable

   TRUST LEVELS:
   - Level 0: Unavoidable (CPU, OS, F*, Z3)
   - Level 1: Memory Model (unified for ALL languages)
   - Level 2: Parser/Frontend (AST construction)
   - Level 3: Hardware Semantics (atomics, floats)

   DESIGN PRINCIPLE (from SPECIFICATION_ERRATA.md):

     "We minimize trust by unifying GC/manual memory under one memory model
      axiom. GC languages have the SAME trust base as manual memory languages."

   ============================================================================ *)

(* ----------------------------------------------------------------------------
   LEVEL 0: UNAVOIDABLE TRUSTED COMPUTING BASE
   These cannot be removed - they are the foundation of verification itself.
   ---------------------------------------------------------------------------- *)

(** 2.1 SMT Solver Correctness (Z3)

    STATEMENT: Z3 is ~500k lines of C++. We trust its SAT/UNSAT answers.

    WHY UNPROVABLE (GodelIncompleteness + ExternalSystem):
      1. Z3 is external code not verified in F*
      2. By Gödel, no system can prove its own consistency

    TRUST JUSTIFICATION:
      - Z3 is heavily tested
      - Used by many verification tools (Dafny, Boogie, Corral)
      - Active development and bug fixing
      - Critical bugs would likely be discovered

    IF THIS FAILS:
      ALL F* proofs could be invalid. A Z3 bug that incorrectly
      returns UNSAT would cause F* to accept invalid proofs.

    MITIGATION:
      - Use multiple SMT solvers
      - Proof logging and replay
      - Random testing of Z3 answers
*)
val smt_solver_correctness : unit ->
  Lemma (ensures True)
  (* Actual: Z3 returns UNSAT ==> formula is unsatisfiable *)

val smt_solver_class : unit -> Tot axiom_class
val smt_solver_reason : unit -> Tot unprovability_reason

(** 2.2 F* Type System Soundness

    STATEMENT: F*'s consistency, SMT encoding, and extraction are correct.

    WHY UNPROVABLE (GodelIncompleteness):
      F* cannot prove its own consistency within F*. This is a direct
      consequence of Gödel's second incompleteness theorem.

    TRUST JUSTIFICATION:
      - F* has extensive test suites
      - Used in high-assurance projects (HACL*, EverParse)
      - Subject to academic scrutiny
      - Bugs are reported and fixed

    IF THIS FAILS:
      Well-typed programs could "go wrong" (crash, have undefined behavior).
      Verified security properties might not hold at runtime.
*)
val fstar_soundness : unit ->
  Lemma (ensures True)
  (* Actual: well-typed F* programs don't go wrong *)

val fstar_soundness_class : unit -> Tot axiom_class
val fstar_soundness_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   LEVEL 1: MEMORY MODEL CORRESPONDENCE
   This REPLACES all GC-specific trust with ONE unified axiom.
   GC languages have the SAME trust base as manual memory languages.
   ---------------------------------------------------------------------------- *)

(** 2.3 Memory Model Correspondence (THE KEY AXIOM)

    UNIFIED MEMORY TRUST FOR ALL LANGUAGES (GC and manual).

    STATEMENT: Memory behaves as a mathematical function.

    FORMAL:
      read(write(m, l, v), l) = v
      read(write(m, l, v), l') = read(m, l')  when l != l'
      fresh(m) returns location not in domain(m)

    WHY UNPROVABLE (ExternalSystem):
      This trusts that hardware + runtime correctly implement memory.
      We cannot verify silicon or runtime C code in F*.

    WHAT WE DO NOT ASSUME (important for GC languages):
      - GC algorithm correctness (reachability, timing, policy)
      - Manual allocator correctness (malloc/free implementation)
      - Specific runtime behavior

    WHAT WE ONLY ASSUME:
      Memory operations have their mathematical meaning.
      This is equivalent to trusting hardware provides correct memory,
      which is required for ANY language including C and assembly.

    WHAT IS VERIFIED (not axioms):
      - Ownership tracking: PROVEN in separation logic
      - Region/lifetime safety: PROVEN in borrow checker
      - Linear resource usage: PROVEN in mode system
      - Frame isolation: PROVEN in separation logic
      - Use-after-free (for tracked refs): PROVEN

    DESIGN PHILOSOPHY:
      By unifying memory trust, we show that brrr-lang's multi-language
      verification has NO ADDITIONAL memory trust over single-language
      verified systems like HACL*.
*)
val memory_model_correspondence : unit ->
  Lemma (ensures True)
  (* Actual: abstract_memory_ops = concrete_memory_behavior *)

val memory_model_class : unit -> Tot axiom_class
val memory_model_reason : unit -> Tot unprovability_reason

(** What this axiom REPLACES (no longer separate axioms):
    - GC runtime memory safety (Python, Java, Go, JS, Ruby)
    - Python GC safety (CPython refcount + cyclic GC)
    - GC isomorphism preservation
    - GC-to-manual memory soundness

    All unified under: "memory behaves as a function" *)

(* ----------------------------------------------------------------------------
   LEVEL 2: PARSER AND FRONTEND TRUST
   These trust external parsers to produce correct ASTs.
   ---------------------------------------------------------------------------- *)

(** 2.4 Parser Correctness (Tree-sitter)

    STATEMENT: Tree-sitter grammars produce ASTs matching language grammar.

    WHY UNPROVABLE (ExternalSystem):
      Tree-sitter grammars are external, unverified code.
      If parsing is wrong, analysis operates on incorrect AST.

    TRUST JUSTIFICATION:
      - Tree-sitter is battle-tested (GitHub, VSCode, Neovim)
      - Extensive grammar test suites
      - Active community maintenance

    MITIGATION:
      - Post-parse AST validation
      - Differential testing against reference parsers

    COMPARISON:
      Even CompCert trusts an unverified parser. This is a common
      point in the TCB of all verified systems.
*)
val parser_correctness : unit ->
  Lemma (ensures True)
  (* Actual: parse(source) produces AST matching grammar *)

val parser_class : unit -> Tot axiom_class
val parser_reason : unit -> Tot unprovability_reason

(** 2.5 Language Frontend Correctness

    STATEMENT: Language-specific frontends produce correct typed ASTs.

    FRONTENDS TRUSTED:
      - C/C++: clang's libtooling (~2M lines)
      - TypeScript: TypeScript compiler API
      - Python: ast module
      - Rust: rustc/syn

    WHY UNPROVABLE (ExternalSystem):
      These are multi-million line codebases we cannot verify.

    MITIGATION:
      - Use well-maintained, widely-used frontends
      - Limit analysis to features parsed correctly
      - Round-trip testing (parse -> unparse -> parse)
*)
val frontend_correctness : unit ->
  Lemma (ensures True)
  (* Actual: frontend produces correct typed AST *)

val frontend_class : unit -> Tot axiom_class
val frontend_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   LEVEL 3: HARDWARE SEMANTICS
   These trust that hardware behaves according to specifications.
   ---------------------------------------------------------------------------- *)

(** 2.6 Hardware Atomicity Guarantees

    STATEMENT: CPU atomic operations behave per memory model spec.

    OPERATIONS COVERED:
      - Compare-and-swap (CAS)
      - Load-acquire / Store-release
      - Memory fences
      - Atomic read-modify-write

    WHY UNPROVABLE (ExternalSystem):
      Software cannot verify cache coherence protocols.
      Hardware behavior is specified, not proven.

    TRUST JUSTIFICATION:
      - CPU vendors extensively test and validate
      - Memory model specifications are well-documented
      - Rare errata are published and worked around
*)
val hardware_atomicity : unit ->
  Lemma (ensures True)
  (* Actual: atomic ops have specified memory ordering *)

val hardware_atomicity_class : unit -> Tot axiom_class
val hardware_atomicity_reason : unit -> Tot unprovability_reason

(** 2.7 IEEE 754 Floating Point Semantics

    STATEMENT: F* has no native floats; we trust hardware IEEE 754.

    WHY UNPROVABLE (ExternalSystem):
      Floating point semantics depend on hardware FPU implementation.
      NaN handling, rounding modes, denormals are hardware-determined.

    IMPLICATION FOR ANALYSIS:
      Floating point analysis in brrr-lang assumes IEEE 754.
      Non-compliant hardware could violate assumed properties.
*)
val ieee754_semantics : unit ->
  Lemma (ensures True)
  (* Actual: float ops match IEEE 754 spec *)

val ieee754_class : unit -> Tot axiom_class
val ieee754_reason : unit -> Tot unprovability_reason

(** 2.8 Memory Ordering Models (x86-TSO, ARM, RISC-V)

    STATEMENT: Hardware memory models match documented behavior.

    MODELS TRUSTED:
      - x86-TSO (Total Store Order)
      - ARM relaxed memory model
      - RISC-V RVWMO

    WHY UNPROVABLE (ExternalSystem):
      Hardware memory models are reverse-engineered from observations.
      Errata exist. We trust documented behavior is complete.

    REFERENCE:
      Promising Semantics (Kang et al. 2017) provides formal model
      that we assume hardware implements.
*)
val memory_ordering_model : unit ->
  Lemma (ensures True)
  (* Actual: Promising Semantics subset of hardware behaviors *)

val memory_ordering_class : unit -> Tot axiom_class
val memory_ordering_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   LEVEL 4: COMPILER AND TOOLCHAIN
   These trust that compilers preserve semantics.
   ---------------------------------------------------------------------------- *)

(** 2.9 Compiler Semantics Preservation

    STATEMENT: Non-verified compilers (GCC, Clang, rustc) may have bugs.

    WHY UNPROVABLE (ExternalSystem):
      Compilers are millions of lines of unverified code.
      CompCert is verified but only for C.

    IMPLICATION:
      Compiler optimization bugs could invalidate source-level analysis.
      A program proven safe in source could be unsafe in binary.

    MITIGATION:
      - Use conservative optimization levels
      - Test compiled code
      - Consider CompCert for critical C code
*)
val compiler_correctness : unit ->
  Lemma (ensures True)
  (* Actual: compiled code = source semantics *)

val compiler_class : unit -> Tot axiom_class
val compiler_reason : unit -> Tot unprovability_reason

(** 2.10 ABI/Platform Behavior

    STATEMENT: Platform ABIs are external specifications.

    ABIs TRUSTED:
      - System V AMD64 ABI (Linux x86-64)
      - Windows x64 calling convention
      - ARM AAPCS

    COVERED PROPERTIES:
      - Struct layout and padding
      - Calling conventions
      - Register usage
      - Stack alignment

    WHY UNPROVABLE (ExternalSystem + EnvironmentDependent):
      ABIs are platform specifications, not theorems.
      Different platforms have different ABIs.
*)
val abi_correctness : unit ->
  Lemma (ensures True)
  (* Actual: runtime follows platform ABI *)

val abi_class : unit -> Tot axiom_class
val abi_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   CATEGORY 2 SUMMARY
   ----------------------------------------------------------------------------

   TOTAL: 10 axioms (down from 24 in original report)

   KEY CHANGE: GC trust eliminated by unifying under memory model.

   TRUST HIERARCHY:

   +-------------------------------------------------------------+
   | Level 0: F*/Z3 (2 axioms) - unavoidable verification base  |
   +-------------------------------------------------------------+
   | Level 1: Memory Model (1 axiom) - unified for ALL langs    |
   +-------------------------------------------------------------+
   | Level 2: Parser/Frontend (2 axioms) - AST construction     |
   +-------------------------------------------------------------+
   | Level 3: Hardware (3 axioms) - atomics, floats, ordering   |
   +-------------------------------------------------------------+
   | Level 4: Toolchain (2 axioms) - compiler, ABI              |
   +-------------------------------------------------------------+

   VERIFIED WITHOUT ADDITIONAL TRUST:
   [x] Ownership tracking (separation logic)
   [x] Region/lifetime safety (borrow checker)
   [x] Linear resource usage (mode system)
   [x] Frame isolation (separation logic)
   [x] Borrow validity (borrow checker)

   ---------------------------------------------------------------------------- *)

(* ============================================================================
   END OF CATEGORY 2: 10 axioms with minimal trust
   ============================================================================ *)


(* ============================================================================
   CATEGORY 3: PROGRAMMER INTENT AND ENVIRONMENT (REDUCED)
   ============================================================================
   These are the irreducible trust assumptions about programmer intent and
   environment-specific properties.

   UPDATED 2026-01-26: Reduced from 12 to 4 axioms based on literature review.

   What was ELIMINATED:
   - Range axioms (3.1-3.3) -> Covered by Parser Trust (2.4)
   - Galois Connection Soundness -> DEFINITIONAL (Cousot 1977)
   - Representation Predicate -> Redundant with Memory Model (2.3)
   - Security Label Assignment -> Policy parameterization
   - Concrete Semantics -> Redundant with Memory Model + Compiler
   - Translation Functor -> DEFERRED_PROOF (CompCert-style)
   - FTG/JARVIS -> DEFERRED_PROOF (provable with effort)

   KEY INSIGHT (Chong & Myers 2004):
   "Sound analysis can ENFORCE a policy, but cannot DERIVE the policy."

   What's PROVABLE (not axioms):
   - Noninterference (Volpano 1996)
   - Robustness (Chong 2004)
   - IFDS soundness (Reps 1995)
   - Galois connection properties (Cousot 1977)
   - Taint propagation mechanics

   What's AXIOMATIC (programmer intent):
   - Declassification intent
   - Source/sink completeness
   - Sanitizer effectiveness
   - Policy validity
   ============================================================================ *)

(** 3.1 Declassification Intentionality (PROGRAMMER INTENT)

    STATEMENT: declassify() annotations reflect programmer's actual intent.

    THE FOUR DIMENSIONS (Sabelfeld & Sands 2009):
      - WHAT: What information is released?
      - WHERE: At what program point?
      - WHO: To which principals?
      - WHEN: Under what conditions?

    WHY UNPROVABLE (ProgrammerIntent):
      Whether a declassify() call represents intentional release or a bug
      exists in programmer's mind - outside formal reasoning.

    WHAT IS PROVABLE:
      - Robustness: attacker cannot influence WHAT gets declassified (Chong 2004)
      - Type soundness: well-typed programs satisfy noninterference until declass
      - Condition truth: declassification occurs only when conditions hold

    LITERATURE:
      Chong & Myers 2004, Sabelfeld & Sands 2009

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:837-840, 952-972
*)
val declassification_intentionality : unit ->
  Lemma (ensures True)
  (* Actual: programmer's declassify() annotations reflect actual intent *)

val declassification_intentionality_class : unit -> Tot axiom_class
val declassification_intentionality_reason : unit -> Tot unprovability_reason

(** 3.2 Taint Source/Sink Completeness (ENVIRONMENT ENUMERATION)

    STATEMENT: Source/sink enumeration is complete for target environment.

    FORMAL:
      "ALL untrusted data enters through declared sources;
       ALL dangerous operations are declared sinks."

    WHY UNPROVABLE (EnvironmentDependent):
      - New APIs introduce new sources/sinks
      - Framework-specific entry points
      - Platform-specific behaviors

    WHAT IS PROVABLE:
      - IFDS framework soundness (Reps 1995): IF enumeration complete, analysis finds all flows
      - Explicit flow propagation: taint correctly tracks through code
      - Lattice properties: taint lattice is well-formed

    LITERATURE:
      Livshits & Lam 2005 (Section 3.2):
      "The problem of obtaining a complete specification for a tainted object
       propagation problem is an important one."

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:167-203
*)
val taint_source_sink_completeness : unit ->
  Lemma (ensures True)
  (* Actual: source/sink enumeration is complete for target environment *)

val taint_source_sink_class : unit -> Tot axiom_class
val taint_source_sink_reason : unit -> Tot unprovability_reason

(** 3.3 Sanitizer Effectiveness (EXTERNAL LIBRARY + ATTACK MODEL)

    STATEMENT: Sanitizer implementations correctly neutralize threats.

    DEPENDS ON:
      1. External library implementation - is escaping function bug-free?
      2. Context-specific encoding - HTML attr vs HTML text vs JS string
      3. Parser differentials - browsers parse HTML differently
      4. Attack model completeness - are all attack vectors known?

    WHY UNPROVABLE (ExternalSystem + PolicySpecification):
      We cannot verify external sanitizer libraries.
      Attack models evolve as new vulnerabilities are discovered.

    WHAT IS PROVABLE:
      - Sanitizer REMOVES specified taint kinds (from IFDSTaint.fst)
      - Type of sanitizer matches type of sink
      - Sanitizer is applied before sink access

    LITERATURE:
      Sabelfeld & Myers 2003 (Section IV-D):
      "Declassification is inherently dangerous... sanitizers depend on
       context-specific semantics."

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:240-272
*)
val sanitizer_effectiveness : unit ->
  Lemma (ensures True)
  (* Actual: sanitizer implementations correctly neutralize specified threats *)

val sanitizer_effectiveness_class : unit -> Tot axiom_class
val sanitizer_effectiveness_reason : unit -> Tot unprovability_reason

(** 3.4 Security Policy Validity (USER-PROVIDED POLICY)

    STATEMENT: User-provided security policy reflects actual requirements.

    FORMAL:
      Security labels correctly capture confidentiality/integrity requirements.

    WHY UNPROVABLE (PolicySpecification):
      Security policy is a SPECIFICATION, not a theorem:
      - Whether "password" should be High depends on business requirements
      - Whether certain flows are acceptable is domain-specific
      - Organizational trust hierarchies are external

    WHAT IS PROVABLE:
      - Policy CONSISTENCY: labels form a valid lattice
      - Policy ENFORCEMENT: well-typed programs respect the policy
      - Policy ROBUSTNESS: attackers cannot subvert via low-integrity influence

    LITERATURE:
      Myers 1997 (DLM):
      "The principal hierarchy correctly reflects organizational trust...
       modifications to the principal structure are extremely powerful."

    SPECIFICATION REFERENCE:
      synthesis_part8.tex:150-155
*)
val security_policy_validity : unit ->
  Lemma (ensures True)
  (* Actual: user-provided policy correctly captures application requirements *)

val security_policy_validity_class : unit -> Tot axiom_class
val security_policy_validity_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   CATEGORY 3 SUMMARY
   ----------------------------------------------------------------------------

   TOTAL: 4 axioms (reduced from 12)

   KEY ACHIEVEMENT: Separated MECHANISM (provable) from POLICY (axiomatic).

   +----------------------------------+-----------------------------------+
   | What's PROVABLE                  | What's AXIOMATIC                  |
   +----------------------------------+-----------------------------------+
   | Noninterference (Volpano 1996)   | Declassification intent           |
   | Robustness (Chong 2004)          | Source/sink completeness          |
   | IFDS soundness (Reps 1995)       | Sanitizer effectiveness           |
   | Galois connection (Cousot 1977)  | Policy validity                   |
   | Taint propagation mechanics      | Environment enumeration           |
   +----------------------------------+-----------------------------------+

   MOVED TO DEFERRED_PROOF:
   - Translation Functor Soundness (CompCert-style, ~40K lines Coq)
   - FTG/JARVIS Type Inference (requires formal Python semantics)

   ---------------------------------------------------------------------------- *)

(* ============================================================================
   END OF CATEGORY 3: 4 axioms (programmer intent and environment)
   ============================================================================ *)


(* ============================================================================
   CATEGORY 4: META-THEORETIC FOUNDATIONS (MASSIVELY REDUCED)
   ============================================================================
   UPDATED 2026-01-26: Reduced from 15 to 1 TRUE AXIOM.

   What was ELIMINATED or moved to DEFERRED_PROOF:

   F* BUILTINS (not our concern):
   - Axiom K / UIP - F* assumes this
   - Function Extensionality - FStar.FunctionalExtensionality

   DEFERRED_PROOF (we'll prove these in brrr-lang):
   - Type Equality Symmetry - basic equality
   - Step-Indexing Properties - definitional + induction
   - Global Completeness Impossibility - formalize Rice's theorem
   - Type System Soundness - progress + preservation
   - Progress Guarantee - induction (Honda 2008)
   - Duality Involution - induction on session types
   - Abstract Interpretation Soundness - Cousot 1977 T1/T2
   - AGT-Siek Equivalence - Garcia 2016
   - Realizability Soundness - logical relations
   - Denotational Adequacy - domain theory
   - Effect Join Commutativity - case analysis
   - Functor Map Laws - induction

   TRUE AXIOM (only 1):
   - Kolmogorov Probability Axioms - foundational mathematics

   KEY INSIGHT: "Meta-theoretic foundations" are mostly:
   1. F*'s job (UIP, FunExt)
   2. Literature theorems we'll re-prove
   3. Standard metatheory we'll mechanize
   ============================================================================ *)

(** 4.1 Probability Measure Axioms (Kolmogorov)

    THE ONLY TRUE AXIOM IN CATEGORY 4.

    STATEMENT: Probability measures satisfy Kolmogorov axioms.

    KOLMOGOROV AXIOMS (1933):
      1. Non-negativity: P(E) >= 0 for all events E
      2. Unitarity: P(Omega) = 1 for sample space Omega
      3. Countable Additivity: P(union of disjoint events) = sum of P(events)

    WHY UNPROVABLE (FoundationalMath):
      Kolmogorov axioms are FOUNDATIONAL MATHEMATICS - on the same level as:
      - Peano axioms for natural numbers
      - ZFC axioms for set theory

      You cannot PROVE axioms - you can only POSTULATE them.
      They DEFINE probability theory; without them, probability is undefined.

    USAGE IN BRRR-LANG:
      - Probabilistic abstract interpretation
      - Uncertainty quantification
      - Randomized algorithm analysis

    SPECIFICATION REFERENCE:
      synthesis_part2.tex:1003-1014
*)
val kolmogorov_probability_axioms : unit ->
  Lemma (ensures True)
  (* Actual: probability measure satisfies Kolmogorov axioms *)

val kolmogorov_class : unit -> Tot axiom_class
val kolmogorov_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   CATEGORY 4 SUMMARY
   ----------------------------------------------------------------------------

   TOTAL: 1 TRUE AXIOM (reduced from 15)

   The only irreducible axiom is Kolmogorov - foundational mathematics that
   defines probability theory itself. You cannot prove the axioms of probability,
   just as you cannot prove the Peano axioms or ZFC axioms.

   Everything else from original Category 4 is either:
   - Provided by F* (Axiom K, FunExt)
   - Proven in literature -> DEFERRED_PROOF
   - Standard metatheory -> DEFERRED_PROOF

   ---------------------------------------------------------------------------- *)

(* ============================================================================
   END OF CATEGORY 4: 1 axiom (Kolmogorov probability)
   ============================================================================ *)


(* ============================================================================
   CATEGORY 10: CROSS-LANGUAGE / FFI RUNTIME TRUST
   ============================================================================
   These axioms cover cross-language interoperability where we must trust
   runtime systems that cannot be verified within brrr-lang.

   UPDATED 2026-01-26: Reduced from 11 to 3 TRUE AXIOMS.

   What was ELIMINATED or moved to DEFERRED_PROOF:
   - Convertibility Soundness -> DEFERRED_PROOF (Patterson 2022 Lemma 3.1)
   - Matthews-Findler Boundaries -> DEFERRED_PROOF (M-F 2007 Theorems 1-6)
   - Round-Trip Preservation -> DEFERRED_PROOF (CompCert-style)
   - Control Flow Modeling -> DEFERRED_PROOF (standard CFG theory)
   - Qilin Algorithm Soundness -> DEFERRED_PROOF (conditional on call graph)
   - External Input Classification -> Covered by 2.4 (Parser)
   - ABI Marshalling -> Covered by 2.10 (ABI)

   What remains as TRUE_AXIOM:
   - Pointer Conversion: Memory model bridging across languages
   - Runtime Interop: Trust in runtime APIs (CPython, JVM, V8)
   - Dispatch Resolution: Dynamic dispatch semantics (vtables, MRO, prototypes)

   These represent EXTERNAL TRUST in runtime systems - not provable within brrr-lang.

   RELATION TO SPEC AXIOM LATTICE:

     brrr_lang_spec_v0.4.tex defines language-level axioms:
       axioms(Python) = {AxMemSafe, AxLeakFree}
       axioms(Rust) = {AxMemSafe, AxTypeSafe, AxRaceFree, AxLeakFree}

     Boundary guards are generated based on axiom differences:
       guard(L1, L2, v:t) = type_check(v,t) if AxTypeSafe in axioms(L2)\axioms(L1)

     Category 10 axioms trust that the RUNTIME correctly implements these guards.

   ============================================================================ *)

(** 10.1 Pointer Conversion Soundness (MEMORY MODEL BRIDGING)

    STATEMENT: Cross-language pointer conversion preserves aliasing invariants.

    THE PROBLEM:
      - Rust `&mut T` has noalias guarantee (exclusive access)
      - C `T*` can alias freely
      - Converting Rust &mut to C *mut and back must preserve exclusivity

    WHY UNPROVABLE (ExternalSystem):
      This is memory model BRIDGING - connecting two different models.
      Neither language's type system can verify the other's invariants.

    NOT COVERED BY 2.3 (Memory Model):
      Axiom 2.3 covers memory behavior WITHIN a single model.
      This axiom covers BRIDGING between different models.

    NOT COVERED BY 2.10 (ABI):
      ABI specifies data layout, not aliasing semantics.

    LITERATURE:
      Patterson et al. 2022 (PLDI) discusses semantic interoperability
      but does not prove cross-model aliasing preservation.

    SPECIFICATION REFERENCE:
      synthesis_part11.tex, FFI boundary handling
*)
val pointer_conversion_soundness : unit ->
  Lemma (ensures True)
  (* Actual: Converting Rust &mut to C *mut and back preserves exclusivity *)

val pointer_conversion_class : unit -> Tot axiom_class
val pointer_conversion_reason : unit -> Tot unprovability_reason

(** 10.2 Python/Rust Runtime Interop (RUNTIME API TRUST)

    STATEMENT: CPython C API functions behave correctly.

    THE PROBLEM:
      - PyO3/rust-cpython call CPython C API functions
      - PyLong_AsLong, PyList_GetItem, PyDict_SetItem, etc.
      - These are implemented in CPython (~400K lines of C)

    WHY UNPROVABLE (ExternalSystem):
      CPython is an external runtime - we cannot verify its implementation.
      We must trust that:
      - Reference counting is correct
      - Type checks return accurate results
      - Memory management doesn't corrupt the heap

    NOT COVERED BY 2.9 (Compiler):
      Compilers transform source to binary.
      This is about runtime API behavior, not compilation.

    NOT COVERED BY 2.10 (ABI):
      ABI specifies calling conventions.
      This is about semantic behavior of API functions.

    APPLIES TO: Any runtime with C API
      - CPython (Python)
      - JNI (Java)
      - V8 C++ API (JavaScript/Node.js)
      - Ruby C API

    SPECIFICATION REFERENCE:
      synthesis_part11.tex, cross-language FFI
*)
val runtime_interop_correctness : unit ->
  Lemma (ensures True)
  (* Actual: Runtime C API functions behave as documented *)

val runtime_interop_class : unit -> Tot axiom_class
val runtime_interop_reason : unit -> Tot unprovability_reason

(** 10.3 Dynamic Dispatch Resolution (RUNTIME DISPATCH SEMANTICS)

    STATEMENT: Runtime dispatch mechanisms follow language specifications.

    THE PROBLEM:
      - Python: Method Resolution Order (MRO) via C3 linearization
      - Java: vtable dispatch for virtual methods
      - JavaScript: prototype chain lookup
      - C++: vtable + RTTI for virtual calls

    WHY UNPROVABLE (ExternalSystem):
      Dispatch resolution happens at RUNTIME based on:
      - Object's actual type (not static type)
      - Class hierarchy at time of call
      - Prototype chain state

      We cannot verify that runtimes correctly implement these algorithms.

    NOT COVERED BY 2.5 (Frontend):
      Frontend handles STATIC type checking.
      This is about DYNAMIC dispatch at runtime.

    NOT COVERED BY 2.9 (Compiler):
      Compiler generates vtable/dispatch code.
      This is about runtime EXECUTION of that code.

    IMPACT ON ANALYSIS:
      Call graph construction must over-approximate possible dispatch targets.
      Axiom 1.13 (Call Graph Completeness) depends on this.

    SPECIFICATION REFERENCE:
      synthesis_part11.tex, dynamic dispatch handling
*)
val dispatch_resolution_correctness : unit ->
  Lemma (ensures True)
  (* Actual: Python MRO, Java vtables, JS prototype chain work correctly *)

val dispatch_resolution_class : unit -> Tot axiom_class
val dispatch_resolution_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   CATEGORY 10 SUMMARY
   ----------------------------------------------------------------------------

   TOTAL: 3 TRUE AXIOMS (reduced from 11)

   These represent trust in RUNTIME SYSTEMS that we cannot verify:

   +-------------------------------------------------------------+
   | 10.1 Pointer Conversion    - Memory model bridging          |
   | 10.2 Runtime Interop       - Runtime API trust (CPython)    |
   | 10.3 Dispatch Resolution   - Dynamic dispatch semantics     |
   +-------------------------------------------------------------+

   MOVED TO DEFERRED_PROOF:
   - Convertibility Soundness (Patterson 2022) - 8-16h
   - Matthews-Findler Boundaries (2007) - 8-16h
   - Round-Trip Preservation - 40-80h (CompCert-style)
   - Control Flow Modeling - 8-16h
   - Qilin Algorithm Soundness - 4-8h (conditional)

   KEY INSIGHT: FFI trust is about RUNTIME behavior, not static properties.
   Static properties (types, ABI layout) are covered by other axioms.
   Dynamic behavior (dispatch, API semantics, aliasing) requires runtime trust.

   ---------------------------------------------------------------------------- *)

(* ============================================================================
   END OF CATEGORY 10: 3 axioms (FFI runtime trust)
   ============================================================================ *)


(* ============================================================================
   GRAND TOTAL: 36 TRUE AXIOMS
   ============================================================================

   Category 1 (Halting/Decidability):     18 axioms
   Category 2 (External System Trust):    10 axioms
   Category 3 (Programmer Intent):         4 axioms
   Category 4 (Meta-Theoretic):            1 axiom
   Category 10 (FFI Runtime Trust):        3 axioms
   ---------------------------------------------
   TOTAL:                                 36 axioms

   These form the IRREDUCIBLE TRUSTED COMPUTING BASE of brrr-lang.

   Everything else is either:
   - DEFINITIONAL (establishes meaning, not assumption)
   - DEFERRED_PROOF (provable with mechanization effort)
   - REDUNDANT (covered by another axiom)
   - F* BUILTIN (handled by F* itself)

   See AXIOMS_REPORT_v2.md for full justifications and literature references.

   ============================================================================
   VERIFICATION CHECKLIST
   ============================================================================

   To verify this module compiles:
     fstar.exe --lax BrrrAxioms.fsti

   To verify the implementation matches:
     fstar.exe --lax BrrrAxioms.fst

   KNOWN ISSUES:
     None currently. All 36 axioms are intentionally admit()-based.

   ============================================================================
   CHANGE LOG
   ============================================================================

   2026-01-26: Major reduction from ~75 to 36 axioms
     - Unified GC/manual memory under single memory model axiom
     - Moved 12 Category 3 axioms to DEFERRED_PROOF
     - Moved 14 Category 4 axioms to DEFERRED_PROOF or F* builtins
     - Moved 8 Category 10 axioms to DEFERRED_PROOF

   2026-01-29: Added comprehensive documentation
     - Added soundness warnings
     - Added usage guidelines
     - Added relationship to spec axiom lattice
     - Added errata references
     - Added literature citations per axiom

   ============================================================================ *)
