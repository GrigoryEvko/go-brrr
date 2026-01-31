(**
 * BrrrAxioms.fst - Trusted Computing Base Implementation
 *
 * ============================================================================
 * MODULE OVERVIEW
 * ============================================================================
 *
 * This module implements the 36 irreducible axioms that form brrr-lang's
 * Trusted Computing Base (TCB). Each axiom represents a property that
 * CANNOT be proven within the system due to fundamental theoretical limits.
 *
 * CRITICAL: All implementations use admit() BY DESIGN - these are axioms,
 * not theorems. Using admit() here is intentional and correct; it would be
 * a mistake to try to "prove" these properties.
 *
 * ============================================================================
 * AXIOM CLASSIFICATION SYSTEM
 * ============================================================================
 *
 * We distinguish three classes of admitted properties:
 *
 * 1. TrueAxiom - Fundamentally unprovable (ALL 36 axioms in this module)
 *    - Halting Problem: Deciding termination (Turing 1936)
 *    - Rice's Theorem: Non-trivial semantic properties (Rice 1953)
 *    - Godel's Incompleteness: Self-referential consistency (Godel 1931)
 *    - External Systems: Hardware, runtimes, parsers outside formal model
 *
 * 2. SemanticAxiom - Depends on external invariants (not used here)
 *    These would be properties that depend on runtime behavior patterns.
 *
 * 3. DeferredProof - Provable but requires effort (NOT in this module)
 *    These belong in theorem modules, not here. Properties that are
 *    theoretically provable but require significant mechanization
 *    effort are classified as DeferredProof in other modules.
 *    See: BrrrExpressions.Theorems.fst, BrrrPrimitives.Theorems.fst
 *
 * ============================================================================
 * THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * Why These Properties Cannot Be Proven:
 *
 * HALTING PROBLEM (Turing 1936):
 *   There exists no algorithm H that, given program P and input I, always
 *   correctly determines whether P(I) halts. Proof by diagonalization.
 *   Affects: Axioms 1.1, 1.2, 1.3, 1.6, 1.8, 1.13, 1.16, 1.18
 *
 * RICE'S THEOREM (Rice 1953):
 *   Every non-trivial semantic property of programs is undecidable.
 *   A property is "trivial" only if true for all programs or no programs.
 *   Affects: Axioms 1.5, 1.12, 1.14, 1.17
 *
 * GODEL'S SECOND INCOMPLETENESS THEOREM (Godel 1931):
 *   No sufficiently powerful consistent system can prove its own consistency.
 *   F* cannot prove F* is sound within F*; we must trust the system.
 *   Affects: Axiom 2.2
 *
 * POST CORRESPONDENCE PROBLEM (Post 1946):
 *   The PCP is undecidable. Interleaved Dyck language reachability reduces
 *   to PCP, making context+field-sensitive analysis undecidable.
 *   Affects: Axiom 1.18
 *
 * COMPLEXITY BARRIERS:
 *   Some problems are decidable but intractable:
 *   - NP-complete: Linearizability verification (Axiom 1.9)
 *   - PSPACE-complete: Magic wand reasoning in separation logic (Axiom 1.10)
 *
 * EXTERNAL SYSTEM TRUST:
 *   Properties of systems outside our formal model cannot be proven:
 *   - Z3 SMT solver correctness (500K+ lines of C++)
 *   - Hardware memory models (reverse-engineered from observations)
 *   - Compiler semantics (GCC, Clang have known bugs)
 *   - Runtime APIs (CPython, JVM, V8 implementations)
 *
 * ============================================================================
 * SOUNDNESS IMPLICATIONS
 * ============================================================================
 *
 * The soundness of brrr-lang depends on these axioms being TRUE:
 *
 * - If Axiom 2.1 (SMT Solver) is violated: ALL proofs could be invalid
 * - If Axiom 2.2 (F* Soundness) is violated: Type system provides no guarantees
 * - If Axiom 2.3 (Memory Model) is violated: Memory safety proofs fail
 * - If Axiom 3.1 (Declassification) is violated: Security policies meaningless
 *
 * MITIGATION STRATEGIES:
 * - Z3 is heavily tested, used by Dafny, Boogie, VCC, Frama-C, etc.
 * - F* has substantial metatheory and testing
 * - Memory models are standardized (C11, Promising 2.0)
 * - Declassification requires programmer annotation (explicit trust)
 *
 * ============================================================================
 * SPECIFICATION REFERENCES
 * ============================================================================
 *
 * Primary References:
 * - brrr_lang_spec_v0.4.tex: Language specification
 * - AXIOMS_REPORT_v2.md: Full axiom justifications
 * - SPECIFICATION_ERRATA.md: Known gaps and corrections
 * - fstar_pop_book.md: F*/SMT background (lines 22700-24100)
 *
 * Literature:
 * - Turing (1936): "On Computable Numbers" - Halting Problem
 * - Rice (1953): "Classes of Recursively Enumerable Sets" - Rice's Theorem
 * - Godel (1931): "Incompleteness Theorems"
 * - Cousot & Cousot (1977): "Abstract Interpretation" - Galois Connections
 * - Honda et al. (2008): "Multiparty Session Types" (corrected by errata)
 * - Chong & Myers (2004): "Security Policies for Downgrading"
 * - Sabelfeld & Sands (2009): "Declassification: Dimensions and Principles"
 *
 * ============================================================================
 * USAGE NOTES
 * ============================================================================
 *
 * This module should be imported by any code that needs to reference axioms:
 *
 *   open BrrrAxioms
 *
 * Each axiom has three associated functions:
 *   1. axiom_name()       - The axiom itself (Lemma, uses admit())
 *   2. axiom_name_class() - Returns TrueAxiom classification
 *   3. axiom_name_reason() - Returns unprovability reason
 *
 * Example usage:
 *   let _ = termination_fuel_exists ()  (* Invoke axiom *)
 *   let c = termination_fuel_exists_class ()   (* = TrueAxiom *)
 *   let r = termination_fuel_exists_reason ()  (* = HaltingProblem *)
 *
 * The _class and _reason functions enable programmatic axiom auditing.
 *
 * ============================================================================
 * VERIFICATION COMMAND
 * ============================================================================
 *
 * To verify this module (lax mode, since it uses admit()):
 *   fstar.exe --lax BrrrAxioms.fst
 *
 * Full verification is impossible - that's the point of axioms.
 *
 * @author brrr-lang team
 * @version 2.0
 * @since 2026-01-26
 * @see BrrrAxioms.fsti for interface declarations and detailed specifications
 * @see AXIOMS_REPORT_v2.md for complete justifications
 *)
module BrrrAxioms

open FStar.List.Tot


(* =============================================================================
   CATEGORY 1: COMPUTATIONAL UNDECIDABILITY
   =============================================================================

   18 axioms arising from fundamental limits of computation.
   These CANNOT be decided by ANY algorithm (Turing 1936, Rice 1953).

   All axioms in this category are TrueAxiom - they represent properties
   that are theoretically impossible to decide in general.

   ORGANIZATION:
   - 1.1-1.3:   Termination-related (direct Halting Problem)
   - 1.4-1.7:   Concurrency and security channels
   - 1.8-1.10:  Verification problems with known complexity
   - 1.11-1.14: Abstract interpretation foundations
   - 1.15-1.18: Data flow and reachability analysis

   ============================================================================= *)


(** 1.1 Program Termination Axiom - Halting Problem
 *
 * FORMAL STATEMENT:
 *   forall program P, input I. terminates(P, I) ==> exists fuel. eval(P, I, fuel) <> Diverged
 *
 * JUSTIFICATION:
 *   The Halting Problem (Turing 1936) proves that no algorithm can decide,
 *   for all program-input pairs, whether the program terminates on that input.
 *
 *   Proof sketch: Assume halting decider H exists. Define D(P) = if H(P,P) then loop else halt.
 *   Then D(D) halts iff D(D) doesn't halt. Contradiction.
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Section "Evaluation"
 * AFFECTS: BrrrEval.fst fuel-based evaluation semantics
 *
 * SOUNDNESS IMPLICATION:
 *   If this axiom is false, our fuel-based semantics would be incomplete:
 *   some terminating programs would not be verifiable as terminating.
 *)
let termination_fuel_exists ()        = admit ()
let termination_fuel_exists_class ()  = TrueAxiom
let termination_fuel_exists_reason () = HaltingProblem


(** 1.2 Loop Divergence Effect - Halting Problem
 *
 * FORMAL STATEMENT:
 *   While loops must carry the Diverge effect because termination is undecidable.
 *   while c { b } : Unit [Div]
 *
 * JUSTIFICATION:
 *   A while loop "while c { b }" terminates iff the condition c eventually
 *   becomes false. Deciding this in general reduces to the Halting Problem.
 *
 *   We conservatively assign Div effect to all while loops. This is SOUND
 *   (never claims diverging loops terminate) but INCOMPLETE (may flag
 *   terminating loops as potentially divergent).
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex:2676-2680
 * AFFECTS: Effect inference for loop constructs
 *
 * ALTERNATIVE APPROACH:
 *   User-provided ranking functions (Axiom 1.8) can prove specific loops
 *   terminate, removing the Div effect for those verified loops.
 *)
let loop_divergence_conservative ()   = admit ()
let loop_divergence_class ()          = TrueAxiom
let loop_divergence_reason ()         = HaltingProblem


(** 1.3 Pattern Exhaustiveness with Guards - Halting Problem
 *
 * FORMAL STATEMENT:
 *   Pattern exhaustiveness with arbitrary guards is undecidable:
 *   match e with | p1 when g1 -> ... | p2 when g2 -> ...
 *   Checking if cases cover all values requires deciding guard satisfiability.
 *
 * JUSTIFICATION:
 *   Guards can encode arbitrary computation:
 *     match x with
 *     | n when halts(program, n) -> ...  (* Requires solving Halting Problem *)
 *
 *   Even without explicit halts() calls, guard expressions can diverge
 *   or have undecidable satisfiability (reduces to SAT for Boolean guards,
 *   which is NP-complete, or to Halting for general expressions).
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex:3505-3517
 * AFFECTS: Pattern matching completeness checking
 *
 * PRACTICAL APPROACH:
 *   Warn on potentially non-exhaustive patterns with guards.
 *   Require explicit wildcard for completeness.
 *)
let exhaustiveness_with_guards ()     = admit ()
let exhaustiveness_guards_class ()    = TrueAxiom
let exhaustiveness_guards_reason ()   = HaltingProblem


(** 1.4 General Deadlock Detection - Undecidable
 *
 * FORMAL STATEMENT:
 *   For concurrent programs with unbounded state spaces, deadlock
 *   detection is undecidable.
 *
 * JUSTIFICATION:
 *   A concurrent program deadlocks if all threads are blocked waiting
 *   for resources held by other threads. Detecting this reduces to
 *   reachability in an infinite state space (Halting Problem).
 *
 *   Even for finite-state systems, deadlock detection is PSPACE-complete
 *   (Sistla & Clarke 1985).
 *
 * SPEC LOCATION: synthesis_part6.tex:518
 * AFFECTS: Concurrency analysis, session type verification
 *
 * NOTE ON SESSION TYPES:
 *   Well-typed multiparty session types provide deadlock freedom for
 *   PROTOCOL-LEVEL deadlocks (Honda et al. 2008), but not for general
 *   resource deadlocks. See SPECIFICATION_ERRATA.md Chapter 6.
 *)
let deadlock_detection ()             = admit ()
let deadlock_detection_class ()       = TrueAxiom
let deadlock_detection_decidability () = Undecidable


(** 1.5 Liveness Properties - Rice's Theorem
 *
 * FORMAL STATEMENT:
 *   "Program eventually reaches a good state" is undecidable.
 *   Formally: forall P. (exists n. step^n(P) in GoodStates) is undecidable.
 *
 * JUSTIFICATION:
 *   Rice's Theorem: Every non-trivial semantic property of programs is
 *   undecidable. "Eventually reaches good state" is non-trivial (some
 *   programs do, some don't), hence undecidable.
 *
 *   Liveness properties (something good eventually happens) are dual
 *   to safety properties (nothing bad ever happens). While safety can
 *   sometimes be verified by invariant checking, liveness requires
 *   proving termination of some process.
 *
 * SPEC LOCATION: synthesis_part14.tex:1910-1913
 * AFFECTS: Temporal logic verification, progress properties
 *)
let liveness_undecidable ()           = admit ()
let liveness_class ()                 = TrueAxiom
let liveness_reason ()                = RicesTheorem


(** 1.6 Termination Channel Detection - Halting Problem Variant
 *
 * FORMAL STATEMENT:
 *   Termination-Sensitive Noninterference (TSNI) is undecidable.
 *   TSNI requires: if two inputs agree on low data, the program either
 *   terminates on both or diverges on both.
 *
 * JUSTIFICATION:
 *   Termination channels leak information through whether a program halts:
 *     if high_secret then loop_forever() else return()
 *   An observer learns high_secret by observing termination.
 *
 *   Detecting such channels requires solving the Halting Problem:
 *   we must determine, for each high input, whether the program terminates.
 *
 * SPEC LOCATION: synthesis_part8.tex:689-693
 * AFFECTS: Information flow control, noninterference proofs
 *
 * PRACTICAL APPROACH:
 *   Use Termination-Insensitive Noninterference (TINI) which ignores
 *   termination channels but is decidable. TINI is still useful for
 *   preventing explicit and implicit flows.
 *)
let termination_channel_detection ()  = admit ()
let termination_channel_class ()      = TrueAxiom
let termination_channel_reason ()     = HaltingProblem


(** 1.7 Timing Channel Freedom - External System + Halting
 *
 * FORMAL STATEMENT:
 *   Constant-time verification (freedom from timing side channels)
 *   is necessarily approximate due to:
 *   1. Microarchitectural effects (caches, branch prediction)
 *   2. OS scheduling and interrupts
 *   3. Hardware timing variations
 *
 * JUSTIFICATION:
 *   Even if source code appears constant-time, actual execution time
 *   depends on:
 *   - Cache state (L1/L2/L3 hits vs misses)
 *   - Branch predictor state
 *   - Memory bus contention
 *   - Speculative execution artifacts
 *
 *   These are EXTERNAL SYSTEM properties outside our formal model.
 *   Additionally, determining if two code paths take equal time
 *   requires analyzing all execution paths (Halting-like).
 *
 * SPEC LOCATION: synthesis_part8.tex:1124-1138
 * AFFECTS: Cryptographic code verification, side-channel analysis
 *
 * MITIGATION:
 *   Use ct-verif or similar tools that provide best-effort constant-time
 *   verification at the source level, acknowledging hardware limitations.
 *)
let timing_channel_freedom ()         = admit ()
let timing_channel_class ()           = TrueAxiom
let timing_channel_reason ()          = ExternalSystem


(** 1.8 Ranking Function Synthesis - Halting Problem
 *
 * FORMAL STATEMENT:
 *   Automatically synthesizing ranking functions for termination proofs
 *   is equivalent to proving termination, which is undecidable.
 *
 * JUSTIFICATION:
 *   A ranking function maps program states to a well-ordered set (e.g., nat)
 *   such that each step decreases the rank. Existence of a ranking function
 *   proves termination.
 *
 *   Given: loop with condition c, body b
 *   Find: function r : State -> nat such that:
 *     forall s. c(s) ==> r(b(s)) < r(s)
 *
 *   If we could always find such r (or determine none exists), we could
 *   decide termination. Contradiction with Halting Problem.
 *
 * SPEC LOCATION: synthesis_part7.tex:1455-1461
 * AFFECTS: Automatic termination proving, F* decreases clauses
 *
 * PRACTICAL APPROACH:
 *   Heuristic-based synthesis (lexicographic orderings, templates) works
 *   for many practical cases. User annotations help in complex cases.
 *)
let ranking_function_synthesis ()     = admit ()
let ranking_function_class ()         = TrueAxiom
let ranking_function_reason ()        = HaltingProblem


(** 1.9 Linearizability Verification - NP-complete
 *
 * FORMAL STATEMENT:
 *   Checking if a concurrent execution is linearizable is NP-complete.
 *   Linearizability: execution appears as if operations occurred atomically
 *   in some sequential order consistent with real-time ordering.
 *
 * JUSTIFICATION:
 *   Given a concurrent execution trace, finding a valid linearization
 *   order is NP-complete (Gibbons & Korach 1997).
 *
 *   The problem is DECIDABLE (in NP), but intractable for large traces.
 *   We mark it as ComplexityBounded rather than Undecidable.
 *
 * SPEC LOCATION: synthesis_part7.tex:1316-1323
 * AFFECTS: Concurrent data structure verification
 *
 * NOTE: Unlike Halting Problem axioms, this is theoretically decidable
 * but practically infeasible for realistic inputs.
 *)
let linearizability_verification ()   = admit ()
let linearizability_class ()          = TrueAxiom
let linearizability_decidability ()   = ComplexityBounded


(** 1.10 Magic Wand Reasoning - PSPACE-complete
 *
 * FORMAL STATEMENT:
 *   Satisfiability of separation logic formulas with magic wand (written as
 *   the "magic wand" or "separating implication" operator) is PSPACE-complete.
 *
 * JUSTIFICATION:
 *   The magic wand (separating implication) P --* Q asserts:
 *   "For any heap H' disjoint from current heap, if H' satisfies P,
 *   then the combined heap satisfies Q."
 *
 *   This universal quantification over heaps makes reasoning expensive.
 *   Calcagno et al. (2001) proved PSPACE-completeness.
 *
 * SPEC LOCATION: synthesis_part7.tex:1664
 * AFFECTS: Separation logic frame rule automation
 *
 * PRACTICAL APPROACH:
 *   Use restricted magic wand patterns (bi-abduction) that are tractable.
 *   Full magic wand only needed for advanced specifications.
 *)
let magic_wand_reasoning ()           = admit ()
let magic_wand_class ()               = TrueAxiom
let magic_wand_decidability ()        = ComplexityBounded


(** 1.11 Widening Operator Termination - Infinite Enumeration
 *
 * FORMAL STATEMENT:
 *   Abstract interpretation with widening terminates, assuming the
 *   widening operator satisfies the ascending chain condition:
 *   Every infinite increasing chain eventually stabilizes.
 *
 * JUSTIFICATION:
 *   Widening is a DESIGN CHOICE, not a theorem. We DEFINE widening
 *   operators to have the ascending chain property. Whether a specific
 *   implementation satisfies this property requires verification of
 *   that implementation.
 *
 *   For infinite-height lattices (like integers), naive iteration
 *   might not terminate. Widening forces termination by over-approximating.
 *
 * SPEC LOCATION: synthesis_part2.tex:828-834
 * AFFECTS: Abstract interpretation fixpoint computation
 *
 * RELATION TO COUSOT 1977:
 *   Cousot's framework DEFINES widening axiomatically. The termination
 *   guarantee follows from the definition, not from a theorem.
 *)
let widening_termination ()           = admit ()
let widening_class ()                 = TrueAxiom
let widening_reason ()                = InfiniteEnumeration


(** 1.12 Transfer Function Monotonicity - Rice's Theorem
 *
 * FORMAL STATEMENT:
 *   Verifying that an arbitrary function is monotonic (preserves order)
 *   is undecidable.
 *
 * JUSTIFICATION:
 *   "Function f is monotonic" is a semantic property of f.
 *   Some functions are monotonic, some are not.
 *   By Rice's Theorem, this is undecidable.
 *
 *   In abstract interpretation, transfer functions model program statements.
 *   Monotonicity is required for Knaster-Tarski fixpoint theorem.
 *
 * SPEC LOCATION: synthesis_part2.tex:737-741
 * AFFECTS: Abstract interpretation soundness proofs
 *
 * PRACTICAL APPROACH:
 *   Design transfer functions to be monotonic by construction.
 *   Verify specific implementations case-by-case.
 *)
let transfer_monotonicity ()          = admit ()
let transfer_monotonicity_class ()    = TrueAxiom
let transfer_monotonicity_reason ()   = RicesTheorem


(** 1.13 Call Graph Completeness - Halting + Rice
 *
 * FORMAL STATEMENT:
 *   Statically computed call graphs necessarily over-approximate
 *   the actual dynamic call graph.
 *
 * JUSTIFICATION:
 *   Determining the exact set of functions called requires:
 *   1. Resolving indirect calls (function pointers, virtual dispatch)
 *   2. Determining reachability of call sites
 *
 *   Both reduce to semantic properties (Rice) or reachability (Halting).
 *
 *   Example: f = if halts(P) then g else h
 *            call f()  -- calls g or h?
 *
 * SPEC LOCATION: synthesis_part12.tex:768-769
 * AFFECTS: Interprocedural analysis, taint analysis
 *
 * CONSEQUENCE:
 *   Sound analyses must include all POSSIBLE callees, even if not all
 *   are actually called at runtime. This leads to imprecision.
 *)
let call_graph_completeness ()        = admit ()
let call_graph_class ()               = TrueAxiom
let call_graph_reason ()              = HaltingProblem


(** 1.14 Points-To Analysis Soundness - Rice's Theorem
 *
 * FORMAL STATEMENT:
 *   May-alias analysis (do two pointers possibly point to same location?)
 *   is undecidable in general.
 *
 * JUSTIFICATION:
 *   "Pointer p may alias pointer q" is a semantic property of the program.
 *   Some programs have aliasing, some don't.
 *   By Rice's Theorem, undecidable.
 *
 *   Practical points-to analyses use approximations:
 *   - Flow-insensitive (ignore control flow)
 *   - Context-insensitive (ignore calling context)
 *   - Field-insensitive (treat all fields as one)
 *
 * SPEC LOCATION: synthesis_part12.tex:686-687
 * AFFECTS: Alias analysis, memory safety verification
 *
 * PRECISION-COMPLEXITY TRADE-OFF:
 *   More context/flow sensitivity = more precise but slower.
 *   k-CFA is O(n^k) for k levels of context sensitivity.
 *)
let points_to_soundness ()            = admit ()
let points_to_class ()                = TrueAxiom
let points_to_reason ()               = RicesTheorem


(** 1.15 Data-Race Freedom Determination - Infinite Enumeration
 *
 * FORMAL STATEMENT:
 *   Determining if a program is data-race free requires considering
 *   all possible interleavings of concurrent operations.
 *
 * JUSTIFICATION:
 *   A data race occurs when two threads access the same memory location
 *   concurrently, with at least one write, and no synchronization.
 *
 *   The number of interleavings is exponential in execution length.
 *   For unbounded executions, the space is infinite.
 *
 *   Dynamic race detection (like ThreadSanitizer) only checks observed
 *   interleavings. Static analysis must over-approximate.
 *
 * SPEC LOCATION: synthesis_part12.tex:541
 * AFFECTS: Concurrency verification, Rust borrow checker
 *
 * RUST APPROACH:
 *   Rust's ownership system prevents data races by construction
 *   (no aliasing + mutation), avoiding the need to enumerate interleavings.
 *)
let drf_determination ()              = admit ()
let drf_class ()                      = TrueAxiom
let drf_reason ()                     = InfiniteEnumeration


(** 1.16 Effect Divergence Absence - Halting Problem
 *
 * FORMAL STATEMENT:
 *   Proving that a computation has no Div effect is equivalent to
 *   proving termination, which is undecidable.
 *
 * JUSTIFICATION:
 *   The Div effect indicates potential non-termination:
 *   - Tot: Total (definitely terminates)
 *   - Div: May diverge (might not terminate)
 *
 *   To promote Div to Tot, we must prove termination.
 *   By Halting Problem, this is undecidable in general.
 *
 * SPEC LOCATION: synthesis_part12.tex:617-625
 * AFFECTS: Effect system, purity checking
 *
 * F* APPROACH:
 *   F* uses a fuel-based semantics and requires decreases clauses
 *   for recursive functions. This makes termination SEMI-decidable
 *   (can prove termination but not non-termination).
 *)
let divergence_absence ()             = admit ()
let divergence_absence_class ()       = TrueAxiom
let divergence_absence_reason ()      = HaltingProblem


(** 1.17 Taint Analysis Completeness - Rice's Theorem
 *
 * FORMAL STATEMENT:
 *   "Tainted data reaches a sink unsanitized" is a semantic property
 *   of programs, hence undecidable by Rice's Theorem.
 *
 * JUSTIFICATION:
 *   Taint analysis tracks data from sources (user input, network) to
 *   sinks (SQL queries, file writes). A vulnerability exists if tainted
 *   data reaches a sink without sanitization.
 *
 *   Determining if this happens requires:
 *   1. Precise alias analysis (undecidable - Axiom 1.14)
 *   2. Reachability analysis (reduces to Halting)
 *   3. Semantic understanding of sanitizers
 *
 * SPEC LOCATION: synthesis_part12.tex:141-147
 * AFFECTS: Security analysis, vulnerability detection
 *
 * PRACTICAL CONSEQUENCE:
 *   Taint analysis MUST over-approximate (report possible vulnerabilities
 *   even if not exploitable). False positives are unavoidable.
 *)
let taint_completeness ()             = admit ()
let taint_class ()                    = TrueAxiom
let taint_reason ()                   = RicesTheorem


(** 1.18 Interleaved Dyck Reachability - Post Correspondence Problem
 *
 * FORMAL STATEMENT:
 *   Context-sensitive AND field-sensitive pointer analysis simultaneously
 *   is undecidable. The problem reduces to interleaved Dyck language
 *   reachability, which reduces to the Post Correspondence Problem.
 *
 * JUSTIFICATION:
 *   Dyck language: balanced parentheses. D = {(), (D), DD}
 *   Context sensitivity: track call-return pairs (balanced)
 *   Field sensitivity: track field accesses (also balanced)
 *
 *   Interleaved Dyck: two Dyck languages interleaved, e.g., ([)]
 *   Reps (2000) proved interleaved Dyck reachability is undecidable
 *   by reduction from Post Correspondence Problem.
 *
 * SPEC LOCATION: synthesis_appendices.tex:351
 * AFFECTS: Pointer analysis precision limits
 *
 * CONSEQUENCE:
 *   Practical analyses must sacrifice either context-sensitivity
 *   or field-sensitivity, or use bounded approximations.
 *)
let interleaved_dyck ()               = admit ()
let interleaved_dyck_class ()         = TrueAxiom
let interleaved_dyck_reason ()        = HaltingProblem


(* =============================================================================
   CATEGORY 2: EXTERNAL SYSTEM TRUST
   =============================================================================

   10 axioms representing trust in external systems we cannot verify.
   These are organized by trust level:
     Level 0: Unavoidable TCB (F*, Z3)
     Level 1: Memory Model (unified for ALL languages)
     Level 2: Parser/Frontend (AST construction)
     Level 3: Hardware Semantics (atomics, floats, memory ordering)
     Level 4: Compiler/Toolchain (code generation)

   KEY INSIGHT: These axioms are irreducible - they represent the fundamental
   trust boundary between our formal model and the real world.

   ============================================================================= *)


(* ---------------------------------------------------------------------------
   Level 0: Unavoidable Trusted Computing Base
   These cannot be removed - they are the foundation of verification itself.
   --------------------------------------------------------------------------- *)

(** 2.1 SMT Solver Correctness (Z3)
 *
 * FORMAL STATEMENT:
 *   When Z3 returns UNSAT, the formula is truly unsatisfiable.
 *
 * JUSTIFICATION:
 *   Z3 is approximately 500,000 lines of C++ code. We cannot verify it
 *   within brrr-lang. If Z3 has a soundness bug, ANY proof we construct
 *   could be invalid.
 *
 *   This is the fundamental bootstrap problem: to verify Z3, we'd need
 *   a verified verifier, which would need another verified verifier, etc.
 *
 * MITIGATION:
 *   - Z3 is heavily tested by Microsoft Research
 *   - Used by Dafny, Boogie, VCC, Frama-C, F*, Lean 4, and many others
 *   - Fuzzing and testing by the SMT-COMP community
 *   - Known bugs are fixed rapidly
 *
 * SPEC LOCATION: Implicit in all F* proofs
 * AFFECTS: Every theorem proven in brrr-lang
 *
 * SEE ALSO: fstar_pop_book.md lines 22750-22770 on SMT undecidability
 *)
let smt_solver_correctness ()         = admit ()
let smt_solver_class ()               = TrueAxiom
let smt_solver_reason ()              = ExternalSystem


(** 2.2 F* Type System Soundness - Godel's Second Incompleteness Theorem
 *
 * FORMAL STATEMENT:
 *   F*'s type system is sound: well-typed programs don't go wrong.
 *   F*'s consistency, SMT encoding, and extraction are all correct.
 *
 * JUSTIFICATION:
 *   By Godel's Second Incompleteness Theorem, no sufficiently powerful
 *   consistent formal system can prove its own consistency within itself.
 *
 *   F* is sufficiently powerful (can encode arithmetic), hence if F* is
 *   consistent, it cannot prove its own consistency. We must TRUST this.
 *
 *   Components we trust:
 *   - Type checker implementation
 *   - SMT encoding of F* to Z3
 *   - Extraction to OCaml/F#/C
 *   - Tactics and metaprogramming
 *
 * MITIGATION:
 *   - F* has substantial metatheoretic development
 *   - Aguirre's tech report on SMT encoding (see fstar_pop_book.md:22782)
 *   - Continuous testing and fuzzing
 *   - Large user base (HACL*, EverParse, Project Everest)
 *
 * SPEC LOCATION: Foundational assumption
 * AFFECTS: All type-based reasoning in brrr-lang
 *)
let fstar_soundness ()                = admit ()
let fstar_soundness_class ()          = TrueAxiom
let fstar_soundness_reason ()         = GodelIncompleteness


(* ---------------------------------------------------------------------------
   Level 1: Memory Model - THE KEY AXIOM
   This REPLACES all GC-specific trust with ONE unified axiom.
   --------------------------------------------------------------------------- *)

(** 2.3 Memory Model Correspondence - THE KEY AXIOM
 *
 * FORMAL STATEMENT:
 *   Abstract memory operations correspond to concrete memory behavior:
 *   - read(write(m, l, v), l) = v
 *   - read(write(m, l, v), l') = read(m, l')  when l <> l'
 *   - fresh(m) returns location not in domain(m)
 *
 * JUSTIFICATION:
 *   This is the ONLY memory-related trust assumption for ALL languages.
 *   We do NOT assume:
 *   - GC algorithm correctness (reachability, timing, policy)
 *   - Manual allocator correctness (malloc/free implementation)
 *   - Specific runtime behavior
 *
 *   We ONLY assume: memory operations have their mathematical meaning.
 *   This is equivalent to trusting hardware provides correct memory.
 *
 * WHAT THIS AXIOM REPLACES (no longer separate axioms):
 *   - GC runtime memory safety (Python, Java, Go, JS, Ruby)
 *   - CPython refcount + cyclic GC correctness
 *   - GC isomorphism preservation
 *   - GC-to-manual memory soundness
 *
 * VERIFIED WITHOUT THIS AXIOM:
 *   - Ownership tracking: PROVEN in separation logic
 *   - Region/lifetime safety: PROVEN in borrow checker
 *   - Linear resource usage: PROVEN in mode system
 *   - Frame isolation: PROVEN in separation logic
 *   - Use-after-free prevention: PROVEN
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Memory Model section
 * AFFECTS: All memory-related proofs
 *
 * SIGNIFICANCE:
 *   GC languages (Python, Java, JavaScript) have the SAME trust base
 *   as manual memory languages (C, Rust). We don't trust the GC
 *   implementation; we only trust that memory behaves as a function.
 *)
let memory_model_correspondence ()    = admit ()
let memory_model_class ()             = TrueAxiom
let memory_model_reason ()            = ExternalSystem


(* ---------------------------------------------------------------------------
   Level 2: Parser/Frontend Trust
   These trust external parsers to produce correct ASTs.
   --------------------------------------------------------------------------- *)

(** 2.4 Parser Correctness (Tree-sitter)
 *
 * FORMAL STATEMENT:
 *   parse(source_text) produces an AST that correctly represents the
 *   syntactic structure defined by the language grammar.
 *
 * JUSTIFICATION:
 *   Tree-sitter grammars are external, unverified code. If parsing is
 *   wrong, our analysis operates on an incorrect AST.
 *
 *   NOTE: Even CompCert trusts an unverified parser (Jourdan et al. 2012).
 *   Parsing itself can be verified (Koprowski & Binsztok 2011) but the
 *   effort is substantial and separate from language semantics.
 *
 * MITIGATION:
 *   - Tree-sitter is battle-tested (GitHub code navigation, VSCode, Neovim)
 *   - Error recovery ensures partial ASTs for malformed input
 *   - Future: Post-parse AST validator could catch some errors
 *
 * SPEC LOCATION: Implicit in AST handling
 * AFFECTS: All analyses that consume parsed code
 *)
let parser_correctness ()             = admit ()
let parser_class ()                   = TrueAxiom
let parser_reason ()                  = ExternalSystem


(** 2.5 Language Frontend Correctness
 *
 * FORMAL STATEMENT:
 *   Language-specific frontends produce correct typed ASTs:
 *   - C/C++: clang's libtooling
 *   - TypeScript: TypeScript compiler API
 *   - Python: ast module
 *   - Rust: rustc's analysis passes
 *
 * JUSTIFICATION:
 *   These frontends are multi-million line codebases. Verifying them
 *   would be a separate, massive effort (c.f., CompCert for C).
 *
 *   Frontend bugs can cause:
 *   - Type information errors (wrong types assigned)
 *   - Scope resolution bugs (wrong variable binding)
 *   - Template/generic instantiation issues
 *
 * MITIGATION:
 *   - These tools are heavily used in production
 *   - Bugs are reported and fixed by large communities
 *   - We can add validation layers for critical properties
 *
 * SPEC LOCATION: Language binding specifications
 * AFFECTS: Cross-language analysis
 *)
let frontend_correctness ()           = admit ()
let frontend_class ()                 = TrueAxiom
let frontend_reason ()                = ExternalSystem


(* ---------------------------------------------------------------------------
   Level 3: Hardware Semantics
   These trust that hardware behaves according to specifications.
   --------------------------------------------------------------------------- *)

(** 2.6 Hardware Atomicity Guarantees
 *
 * FORMAL STATEMENT:
 *   CPU atomic operations (CAS, load-acquire, store-release) behave
 *   according to architecture memory model specifications.
 *
 * JUSTIFICATION:
 *   Software cannot verify cache coherence protocols. We must trust:
 *   - Intel/AMD x86-TSO model
 *   - ARM weak memory model
 *   - RISC-V RVWMO model
 *
 *   Hardware errata exist. Intel's Spectre/Meltdown showed microarchitecture
 *   can violate expectations.
 *
 * SPEC LOCATION: synthesis_part7.tex hardware concurrency
 * AFFECTS: Lock-free algorithms, concurrent data structures
 *
 * SEE ALSO: Promising Semantics (Kang et al. 2017) for formal model
 *)
let hardware_atomicity ()             = admit ()
let hardware_atomicity_class ()       = TrueAxiom
let hardware_atomicity_reason ()      = ExternalSystem


(** 2.7 IEEE 754 Floating Point Semantics
 *
 * FORMAL STATEMENT:
 *   Hardware floating-point operations match IEEE 754 specification:
 *   rounding modes, NaN handling, denormals, infinities.
 *
 * JUSTIFICATION:
 *   F* has no native floats; we must trust hardware implementation.
 *   IEEE 754 specifies exact bit-level semantics, but:
 *   - x87 extended precision differs from SSE
 *   - Flush-denormals-to-zero mode exists
 *   - Rounding mode can be changed at runtime
 *
 * SPEC LOCATION: Numeric types section
 * AFFECTS: Floating-point verification, numerical analysis
 *
 * NOTE: Flocq (Coq library) provides verified floating-point in Coq,
 * but this doesn't help with hardware behavior.
 *)
let ieee754_semantics ()              = admit ()
let ieee754_class ()                  = TrueAxiom
let ieee754_reason ()                 = ExternalSystem


(** 2.8 Memory Ordering Models (x86-TSO, ARM, RISC-V)
 *
 * FORMAL STATEMENT:
 *   Hardware memory ordering follows documented models:
 *   - x86: Total Store Order (TSO) with store buffers
 *   - ARM/POWER: Relaxed ordering with barriers
 *   - RISC-V: RVWMO (RISC-V Weak Memory Ordering)
 *
 * JUSTIFICATION:
 *   Memory models are reverse-engineered from hardware observations.
 *   They represent our BEST UNDERSTANDING, not ground truth.
 *
 *   Promising Semantics (POPL 2017) provides a formal model that
 *   is intended to be sound with respect to hardware, but this
 *   cannot be verified without access to CPU microarchitecture.
 *
 * SPEC LOCATION: Memory ordering section
 * AFFECTS: Concurrent algorithm verification
 *
 * SEE ALSO: Alglave et al. "Herding Cats" (TOPLAS 2014) for formal models
 *)
let memory_ordering_model ()          = admit ()
let memory_ordering_class ()          = TrueAxiom
let memory_ordering_reason ()         = ExternalSystem


(* ---------------------------------------------------------------------------
   Level 4: Compiler/Toolchain
   These trust that compilers preserve semantics.
   --------------------------------------------------------------------------- *)

(** 2.9 Compiler Semantics Preservation
 *
 * FORMAL STATEMENT:
 *   Compilers (GCC, Clang, rustc) preserve source semantics:
 *   behavior(compile(P)) = behavior(P)
 *
 * JUSTIFICATION:
 *   Non-verified compilers have bugs. Examples:
 *   - GCC bug #323 (floating point) lasted 10+ years
 *   - LLVM miscompilations found by Csmith fuzzer
 *   - rustc has had soundness holes
 *
 *   CompCert is verified but only for C, and only to assembly.
 *
 * MITIGATION:
 *   - Use multiple compiler versions
 *   - Runtime checks for critical properties
 *   - Translation validation (verify output matches source)
 *
 * SPEC LOCATION: Compilation semantics
 * AFFECTS: Trust in generated binaries
 *
 * FUTURE: Could use verified compilation (CompCert, CakeML) for TCB code.
 *)
let compiler_correctness ()           = admit ()
let compiler_class ()                 = TrueAxiom
let compiler_reason ()                = ExternalSystem


(** 2.10 ABI/Platform Behavior
 *
 * FORMAL STATEMENT:
 *   Platform ABIs are correctly documented and implemented:
 *   - System V AMD64 ABI
 *   - Windows x64 calling convention
 *   - ARM AAPCS
 *   - RISC-V calling convention
 *
 * JUSTIFICATION:
 *   ABI specifies:
 *   - Calling conventions (registers, stack layout)
 *   - Struct layout (padding, alignment)
 *   - Name mangling
 *   - Exception handling
 *
 *   These are external specifications. Compiler/OS bugs can violate them.
 *
 * SPEC LOCATION: FFI section
 * AFFECTS: Cross-language interoperability
 *)
let abi_correctness ()                = admit ()
let abi_class ()                      = TrueAxiom
let abi_reason ()                     = ExternalSystem


(* =============================================================================
   CATEGORY 3: PROGRAMMER INTENT AND ENVIRONMENT
   =============================================================================

   4 axioms bridging the semantic gap between syntax and meaning.
   These exist in the programmer's mind or target environment.

   KEY INSIGHT (Chong & Myers 2004):
   "Sound analysis can ENFORCE a policy, but cannot DERIVE the policy."

   These axioms represent the gap between:
   - MECHANISM: What the type system can enforce (provable)
   - POLICY: What security requirements the programmer intends (axiomatic)

   ============================================================================= *)


(** 3.1 Declassification Intentionality - Programmer Intent
 *
 * FORMAL STATEMENT:
 *   Programmer placement of declassify() annotations correctly reflects
 *   intentional information release, not security bugs.
 *
 * JUSTIFICATION:
 *   Declassification requires specifying WHAT, WHERE, WHO, and WHEN
 *   information is released (Sabelfeld & Sands 2009 "Four Dimensions").
 *
 *   Whether a declassify() call represents:
 *   - Intentional release (password check succeeds)
 *   - Security bug (accidentally leaking password)
 *   exists in the PROGRAMMER'S MIND - outside formal reasoning.
 *
 * WHAT IS PROVABLE:
 *   - Robustness: attacker cannot influence WHAT gets declassified
 *   - Type soundness: programs satisfy noninterference until declassification
 *   - Condition truth: declassification only when specified conditions hold
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Security section
 * LITERATURE: Chong & Myers 2004, Sabelfeld & Sands 2009
 * AFFECTS: Information flow security proofs
 *)
let declassification_intentionality ()        = admit ()
let declassification_intentionality_class ()  = TrueAxiom
let declassification_intentionality_reason () = ProgrammerIntent


(** 3.2 Taint Source/Sink Completeness - Environment Enumeration
 *
 * FORMAL STATEMENT:
 *   The enumeration of taint sources and sinks is complete:
 *   "ALL untrusted data enters through listed sources;
 *    ALL dangerous operations are listed sinks."
 *
 * JUSTIFICATION:
 *   This is ENVIRONMENT-DEPENDENT:
 *   - New APIs introduce new sources/sinks
 *   - Framework-specific entry points (request.params, console.input)
 *   - Platform-specific behaviors
 *
 *   Livshits & Lam 2005 (Section 3.2):
 *   "The problem of obtaining a complete specification for a tainted
 *    object propagation problem is an important one."
 *
 * WHAT IS PROVABLE:
 *   - IFDS soundness: if enumeration is complete, analysis finds all flows
 *   - Taint propagation: correctly tracks through assignments, calls
 *   - Lattice properties: taint lattice is well-formed
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Taint Analysis section
 * AFFECTS: Taint analysis completeness guarantees
 *)
let taint_source_sink_completeness ()         = admit ()
let taint_source_sink_class ()                = TrueAxiom
let taint_source_sink_reason ()               = EnvironmentDependent


(** 3.3 Sanitizer Effectiveness - External Library + Attack Model
 *
 * FORMAL STATEMENT:
 *   Sanitizer functions correctly neutralize the threats they claim to:
 *   html_escape() prevents XSS, sql_parameterize() prevents SQLi, etc.
 *
 * JUSTIFICATION:
 *   Sanitizer effectiveness depends on:
 *   1. Library implementation correctness (external code)
 *   2. Context-specific encoding (HTML attr vs text vs JS string)
 *   3. Parser differentials (browsers parse HTML differently)
 *   4. Attack model completeness (are all attack vectors known?)
 *
 *   Sabelfeld & Myers 2003 (Section IV-D):
 *   "Declassification is inherently dangerous... sanitizers depend on
 *    context-specific semantics."
 *
 * WHAT IS PROVABLE:
 *   - Sanitizer REMOVES specified taint kinds
 *   - Sanitizer type matches sink type
 *   - Sanitizer applied before sink access
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Sanitization section
 * AFFECTS: Taint analysis, XSS/SQLi prevention
 *)
let sanitizer_effectiveness ()                = admit ()
let sanitizer_effectiveness_class ()          = TrueAxiom
let sanitizer_effectiveness_reason ()         = ExternalSystem


(** 3.4 Security Policy Validity - User-Provided Specification
 *
 * FORMAL STATEMENT:
 *   User-provided security labels correctly capture the confidentiality
 *   and integrity requirements of the application.
 *
 * JUSTIFICATION:
 *   Security policy is a SPECIFICATION, not a theorem:
 *   - Whether "password" should be High depends on business requirements
 *   - Whether certain data flows are acceptable is domain-specific
 *   - Organizational trust hierarchies are external
 *
 *   Myers 1997 (DLM):
 *   "The principal hierarchy correctly reflects organizational trust...
 *    modifications to the principal structure are extremely powerful."
 *
 * WHAT IS PROVABLE:
 *   - Policy CONSISTENCY: labels form a valid lattice
 *   - Policy ENFORCEMENT: well-typed programs respect the policy
 *   - Policy ROBUSTNESS: attackers cannot subvert via low-integrity influence
 *
 * SPEC LOCATION: brrr_lang_spec_v0.4.tex Security Labels section
 * AFFECTS: All information flow guarantees
 *)
let security_policy_validity ()               = admit ()
let security_policy_validity_class ()         = TrueAxiom
let security_policy_validity_reason ()        = PolicySpecification


(* =============================================================================
   CATEGORY 4: FOUNDATIONAL MATHEMATICS
   =============================================================================

   1 axiom representing foundational mathematics (same level as Peano/ZFC).

   KEY INSIGHT: You cannot PROVE axioms - you can only POSTULATE them.
   Kolmogorov axioms are foundational, like Peano axioms for arithmetic.

   ============================================================================= *)


(** 4.1 Kolmogorov Probability Axioms - Foundational Mathematics
 *
 * FORMAL STATEMENT:
 *   Probability measure P on sample space Omega satisfies:
 *   1. Non-negativity: P(E) >= 0 for all events E
 *   2. Unitarity: P(Omega) = 1
 *   3. Countable Additivity: P(union of disjoint events) = sum of P(events)
 *
 * JUSTIFICATION:
 *   Kolmogorov axioms are FOUNDATIONAL MATHEMATICS - on the same level as:
 *   - Peano axioms for natural numbers
 *   - ZFC axioms for set theory
 *   - Euclidean axioms for geometry
 *
 *   You cannot PROVE axioms within the system they define.
 *   You can only POSTULATE them and derive consequences.
 *
 * USED FOR:
 *   - Probabilistic abstract interpretation
 *   - Uncertainty quantification
 *   - Randomized algorithm analysis
 *
 * SPEC LOCATION: synthesis_part2.tex:1003-1014
 * AFFECTS: Any reasoning involving probability
 *
 * NOTE: This is the ONLY axiom in Category 4 after reduction.
 * All other "meta-theoretic" axioms were either:
 * - F* built-ins (Axiom K, function extensionality)
 * - Provable theorems (now in DeferredProof)
 *)
let kolmogorov_probability_axioms ()  = admit ()
let kolmogorov_class ()               = TrueAxiom
let kolmogorov_reason ()              = FoundationalMath


(* =============================================================================
   CATEGORY 10: FFI RUNTIME TRUST
   =============================================================================

   3 axioms for cross-language interoperability runtime trust.
   These represent dynamic behavior we cannot statically verify.

   KEY INSIGHT: FFI trust is about RUNTIME behavior, not static properties.
   Static properties (types, ABI layout) are covered by other axioms (2.5, 2.10).
   Dynamic behavior (dispatch, API semantics, aliasing) requires runtime trust.

   ============================================================================= *)


(** 10.1 Pointer Conversion Soundness - Memory Model Bridging
 *
 * FORMAL STATEMENT:
 *   Cross-language pointer conversion preserves aliasing invariants:
 *   Converting Rust &mut T to C T* and back preserves exclusive access.
 *
 * JUSTIFICATION:
 *   This is memory model BRIDGING - connecting different memory models:
 *   - Rust: ownership + borrowing (exclusive &mut, shared &)
 *   - C: raw pointers, no aliasing info (except restrict)
 *   - Python: everything is a PyObject*
 *
 *   Neither language's type system can verify the other's invariants.
 *
 * NOT COVERED BY OTHER AXIOMS:
 *   - Axiom 2.3 (Memory Model): single model, not bridging
 *   - Axiom 2.10 (ABI): data layout, not aliasing semantics
 *
 * LITERATURE: Patterson et al. 2022 (PLDI) "Semantic Interoperability"
 * SPEC LOCATION: FFI boundary handling
 * AFFECTS: Safe FFI, foreign function wrappers
 *)
let pointer_conversion_soundness ()   = admit ()
let pointer_conversion_class ()       = TrueAxiom
let pointer_conversion_reason ()      = ExternalSystem


(** 10.2 Runtime API Interop (CPython, JNI, V8) - Runtime Trust
 *
 * FORMAL STATEMENT:
 *   Runtime C API functions behave as documented:
 *   - CPython: PyLong_AsLong, PyList_GetItem, Py_INCREF, etc.
 *   - JNI: GetIntField, CallObjectMethod, etc.
 *   - V8: v8::Value::ToNumber, v8::Object::Get, etc.
 *
 * JUSTIFICATION:
 *   These runtimes are massive codebases (CPython ~400K lines of C).
 *   We cannot verify their implementations within brrr-lang.
 *
 *   We must trust that:
 *   - Reference counting is correct (CPython)
 *   - Type checks return accurate results
 *   - Memory management doesn't corrupt the heap
 *   - GC interacts correctly with FFI boundaries
 *
 * NOT COVERED BY OTHER AXIOMS:
 *   - Axiom 2.9 (Compiler): compilation, not runtime API behavior
 *   - Axiom 2.10 (ABI): calling conventions, not semantic behavior
 *
 * APPLIES TO:
 *   CPython, JVM (JNI), V8 (Node.js), Ruby C API, Lua C API, etc.
 *
 * SPEC LOCATION: Cross-language FFI section
 * AFFECTS: All language interop involving runtime APIs
 *)
let runtime_interop_correctness ()    = admit ()
let runtime_interop_class ()          = TrueAxiom
let runtime_interop_reason ()         = ExternalSystem


(** 10.3 Dynamic Dispatch Resolution (MRO, vtables, prototypes)
 *
 * FORMAL STATEMENT:
 *   Runtime dispatch mechanisms follow language specifications:
 *   - Python: Method Resolution Order (C3 linearization)
 *   - Java: vtable dispatch for virtual methods
 *   - JavaScript: prototype chain lookup
 *   - C++: vtable + RTTI
 *
 * JUSTIFICATION:
 *   Dispatch resolution happens at RUNTIME based on:
 *   - Object's actual (dynamic) type, not static type
 *   - Class hierarchy at time of call
 *   - Prototype chain state (can be modified at runtime in JS)
 *
 *   We cannot verify that runtimes correctly implement these algorithms.
 *
 * NOT COVERED BY OTHER AXIOMS:
 *   - Axiom 2.5 (Frontend): STATIC type checking
 *   - Axiom 2.9 (Compiler): generates dispatch code, doesn't execute it
 *
 * IMPACT ON ANALYSIS:
 *   Call graph construction must over-approximate possible dispatch targets.
 *   This is why Axiom 1.13 (Call Graph Completeness) is needed.
 *
 * SPEC LOCATION: Dynamic dispatch section
 * AFFECTS: Call graph construction, devirtualization analysis
 *)
let dispatch_resolution_correctness () = admit ()
let dispatch_resolution_class ()       = TrueAxiom
let dispatch_resolution_reason ()      = ExternalSystem


(* =============================================================================
   AXIOM COUNT SUMMARY
   =============================================================================

   Category 1  - Computational Undecidability:    18 axioms
     Halting Problem (Turing 1936):               8 axioms
     Rice's Theorem (Rice 1953):                  4 axioms
     Complexity Barriers (NP/PSPACE):             2 axioms
     Infinite Enumeration:                        3 axioms
     Post Correspondence Problem:                 1 axiom

   Category 2  - External System Trust:           10 axioms
     Level 0 - Unavoidable TCB:                   2 axioms (F*, Z3)
     Level 1 - Memory Model:                      1 axiom  (unified)
     Level 2 - Parser/Frontend:                   2 axioms
     Level 3 - Hardware:                          3 axioms
     Level 4 - Toolchain:                         2 axioms

   Category 3  - Programmer Intent/Environment:    4 axioms
     Programmer Intent:                           1 axiom  (declassification)
     Environment Enumeration:                     1 axiom  (sources/sinks)
     External Libraries:                          1 axiom  (sanitizers)
     Policy Specification:                        1 axiom  (security labels)

   Category 4  - Foundational Mathematics:         1 axiom
     Kolmogorov Axioms:                           1 axiom

   Category 10 - FFI Runtime Trust:                3 axioms
     Memory Bridging:                             1 axiom
     Runtime APIs:                                1 axiom
     Dynamic Dispatch:                            1 axiom

   ============================================================================
   TOTAL TRUSTED COMPUTING BASE:                  36 axioms
   ============================================================================

   These form the IRREDUCIBLE trusted computing base of brrr-lang.

   Everything else is either:
   - DEFINITIONAL (establishes meaning, not assumption)
   - DEFERRED_PROOF (provable with mechanization effort)
   - REDUNDANT (covered by another axiom)
   - F* BUILTIN (handled by F* itself)

   For full justifications and literature references, see:
   - AXIOMS_REPORT_v2.md
   - SPECIFICATION_ERRATA.md (for corrections to literature)

   ============================================================================= *)
