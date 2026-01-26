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
module Axioms

open FStar.List.Tot

(* ============================================================================
   CLASSIFICATION TYPES
   ============================================================================ *)

(** Axiom classification - why this property is assumed rather than proven *)
type axiom_class =
  | TrueAxiom      (* Fundamentally unprovable: halting, Gödel, external systems *)
  | SemanticAxiom  (* Depends on external invariants not in type system *)
  | DeferredProof  (* Provable but requires significant mechanization effort *)

(** Decidability status for analysis problems *)
type decidability =
  | Decidable           (* Algorithm exists that always terminates with correct answer *)
  | SemiDecidable       (* Can confirm positive instances, may diverge on negative *)
  | Undecidable         (* No algorithm exists - halting problem, Rice's theorem *)
  | ComplexityBounded   (* Decidable but intractable: NP-complete, PSPACE-complete *)

(** Why a property is fundamentally unprovable *)
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
   ============================================================================ *)

(** 1.1 Program Termination Axiom - Halting Problem
    If a program terminates mathematically, sufficient fuel exists.
    Location: Eval.fst *)
val termination_fuel_exists : unit ->
  Lemma (ensures True)  (* Actual: terminates ==> exists fuel. ~diverged *)

val termination_fuel_exists_class : unit -> Tot axiom_class
val termination_fuel_exists_reason : unit -> Tot unprovability_reason

(** 1.2 Loop Divergence Effect - Halting Problem
    While loops always carry Diverge effect (termination undecidable).
    Location: brrr_lang_spec_v0.4.tex:2676-2680 *)
val loop_divergence_conservative : unit ->
  Lemma (ensures True)  (* Actual: while c {b} : Unit [Div] *)

val loop_divergence_class : unit -> Tot axiom_class
val loop_divergence_reason : unit -> Tot unprovability_reason

(** 1.3 Exhaustiveness with Guards - Halting Problem
    Pattern exhaustiveness undecidable when guards present.
    Location: brrr_lang_spec_v0.4.tex:3505-3517 *)
val exhaustiveness_with_guards : unit ->
  Lemma (ensures True)  (* Actual: guards can encode arbitrary computation *)

val exhaustiveness_guards_class : unit -> Tot axiom_class
val exhaustiveness_guards_reason : unit -> Tot unprovability_reason

(** 1.4 Deadlock Detection - Undecidable/PSPACE-complete
    General deadlock detection undecidable for infinite state.
    Location: synthesis_part6.tex:518 *)
val deadlock_detection : unit ->
  Lemma (ensures True)

val deadlock_detection_class : unit -> Tot axiom_class
val deadlock_detection_decidability : unit -> Tot decidability

(** 1.5 Liveness Properties - Rice's Theorem
    "Eventually reaches good state" undecidable.
    Location: synthesis_part14.tex:1910-1913 *)
val liveness_undecidable : unit ->
  Lemma (ensures True)

val liveness_class : unit -> Tot axiom_class
val liveness_reason : unit -> Tot unprovability_reason

(** 1.6 Termination Channel Detection - Halting Problem variant
    TSNI (termination-sensitive noninterference) undecidable.
    Location: synthesis_part8.tex:689-693 *)
val termination_channel_detection : unit ->
  Lemma (ensures True)

val termination_channel_class : unit -> Tot axiom_class
val termination_channel_reason : unit -> Tot unprovability_reason

(** 1.7 Timing Channel Freedom - External System + Halting
    Constant-time verification necessarily approximate.
    Location: synthesis_part8.tex:1124-1138 *)
val timing_channel_freedom : unit ->
  Lemma (ensures True)

val timing_channel_class : unit -> Tot axiom_class
val timing_channel_reason : unit -> Tot unprovability_reason

(** 1.8 Ranking Function Synthesis - Halting Problem
    Auto-synthesizing ranking functions = proving termination.
    Location: synthesis_part7.tex:1455-1461 *)
val ranking_function_synthesis : unit ->
  Lemma (ensures True)

val ranking_function_class : unit -> Tot axiom_class
val ranking_function_reason : unit -> Tot unprovability_reason

(** 1.9 Linearizability Verification - NP-complete
    Finding valid linearization is NP-complete.
    Location: synthesis_part7.tex:1316-1323 *)
val linearizability_verification : unit ->
  Lemma (ensures True)

val linearizability_class : unit -> Tot axiom_class
val linearizability_decidability : unit -> Tot decidability

(** 1.10 Magic Wand Reasoning - PSPACE-complete
    Full separation logic magic wand is PSPACE-complete.
    Location: synthesis_part7.tex:1664 *)
val magic_wand_reasoning : unit ->
  Lemma (ensures True)

val magic_wand_class : unit -> Tot axiom_class
val magic_wand_decidability : unit -> Tot decidability

(** 1.11 Widening Termination - Design Axiom
    Ascending chain condition for widening operators.
    Location: synthesis_part2.tex:828-834 *)
val widening_termination : unit ->
  Lemma (ensures True)

val widening_class : unit -> Tot axiom_class
val widening_reason : unit -> Tot unprovability_reason

(** 1.12 Transfer Function Monotonicity - Rice's Theorem
    Cannot verify arbitrary functions are monotonic.
    Location: synthesis_part2.tex:737-741 *)
val transfer_monotonicity : unit ->
  Lemma (ensures True)

val transfer_monotonicity_class : unit -> Tot axiom_class
val transfer_monotonicity_reason : unit -> Tot unprovability_reason

(** 1.13 Call Graph Completeness - Halting + Rice
    Call graphs necessarily over-approximate.
    Location: synthesis_part12.tex:768-769 *)
val call_graph_completeness : unit ->
  Lemma (ensures True)

val call_graph_class : unit -> Tot axiom_class
val call_graph_reason : unit -> Tot unprovability_reason

(** 1.14 Points-To Analysis Soundness - Rice's Theorem
    May-alias is non-trivial semantic property.
    Location: synthesis_part12.tex:686-687 *)
val points_to_soundness : unit ->
  Lemma (ensures True)

val points_to_class : unit -> Tot axiom_class
val points_to_reason : unit -> Tot unprovability_reason

(** 1.15 Data-Race Freedom - Infinite Enumeration
    DRF requires enumerating all interleavings.
    Location: synthesis_part12.tex:541 *)
val drf_determination : unit ->
  Lemma (ensures True)

val drf_class : unit -> Tot axiom_class
val drf_reason : unit -> Tot unprovability_reason

(** 1.16 Effect Divergence Absence - Halting Problem
    Proving no Div effect = proving termination.
    Location: synthesis_part12.tex:617-625 *)
val divergence_absence : unit ->
  Lemma (ensures True)

val divergence_absence_class : unit -> Tot axiom_class
val divergence_absence_reason : unit -> Tot unprovability_reason

(** 1.17 Taint Analysis Completeness - Rice's Theorem
    "Reaches unsanitized" is non-trivial semantic property.
    Location: synthesis_part12.tex:141-147 *)
val taint_completeness : unit ->
  Lemma (ensures True)

val taint_class : unit -> Tot axiom_class
val taint_reason : unit -> Tot unprovability_reason

(** 1.18 Interleaved Dyck Undecidability - Post Correspondence
    Context+field sensitivity reduces to PCP.
    Location: synthesis_appendices.tex:351 *)
val interleaved_dyck : unit ->
  Lemma (ensures True)

val interleaved_dyck_class : unit -> Tot axiom_class
val interleaved_dyck_reason : unit -> Tot unprovability_reason


(* ============================================================================
   END OF CATEGORY 1: 18 TRUE_AXIOM declarations
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
   ============================================================================ *)

(* ----------------------------------------------------------------------------
   LEVEL 0: UNAVOIDABLE TRUSTED COMPUTING BASE
   These cannot be removed - they are the foundation of verification itself.
   ---------------------------------------------------------------------------- *)

(** 2.1 SMT Solver Correctness (Z3)

    Z3 is ~500k lines of C++. We trust its SAT/UNSAT answers.
    This is unavoidable - F* verification depends on Z3.

    If Z3 has a soundness bug, ALL our proofs could be invalid.
    Mitigation: Z3 is heavily tested, used by many verification tools.
*)
val smt_solver_correctness : unit ->
  Lemma (ensures True)
  (* Actual: Z3 returns UNSAT ==> formula is unsatisfiable *)

val smt_solver_class : unit -> Tot axiom_class
val smt_solver_reason : unit -> Tot unprovability_reason

(** 2.2 F* Type System Soundness

    F*'s consistency, SMT encoding, and extraction correctness
    form an irreducible trust base.

    By Gödel, F* cannot prove its own consistency within F*.
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

    We assume memory behaves as a mathematical function:
    - read(write(m, l, v), l) = v
    - read(write(m, l, v), l') = read(m, l')  when l != l'
    - fresh(m) returns location not in domain(m)

    This is the ONLY memory-related trust assumption.

    We do NOT assume:
    - GC algorithm correctness (reachability, timing, policy)
    - Manual allocator correctness (malloc/free implementation)
    - Specific runtime behavior

    We ONLY assume: memory operations have their mathematical meaning.

    This is equivalent to trusting hardware provides correct memory,
    which is required for ANY language including C and assembly.

    EVERYTHING ELSE IS VERIFIED:
    - Ownership tracking: PROVEN in separation logic
    - Region/lifetime safety: PROVEN in borrow checker
    - Linear resource usage: PROVEN in mode system
    - Frame isolation: PROVEN in separation logic
    - Use-after-free (for tracked refs): PROVEN
*)
val memory_model_correspondence : unit ->
  Lemma (ensures True)
  (* Actual: abstract_memory_ops ≡ concrete_memory_behavior *)

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

    Tree-sitter grammars are external, unverified code.
    If parsing is wrong, analysis operates on incorrect AST.

    Mitigation: Tree-sitter is battle-tested (GitHub, VSCode, Neovim).
    Future: Could add post-parse AST validator in F*.

    Note: Even CompCert trusts an unverified parser.
*)
val parser_correctness : unit ->
  Lemma (ensures True)
  (* Actual: parse(source) produces AST matching grammar *)

val parser_class : unit -> Tot axiom_class
val parser_reason : unit -> Tot unprovability_reason

(** 2.5 Language Frontend Correctness

    Language-specific frontends (clang, tsc, python ast):
    - C/C++: clang's libtooling
    - TypeScript: TypeScript compiler API
    - Python: ast module

    These are multi-million line codebases.
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

    CPU atomic operations (CAS, load-acquire, store-release)
    behave according to memory model specifications.

    Software cannot verify cache coherence protocols.
*)
val hardware_atomicity : unit ->
  Lemma (ensures True)
  (* Actual: atomic ops have specified memory ordering *)

val hardware_atomicity_class : unit -> Tot axiom_class
val hardware_atomicity_reason : unit -> Tot unprovability_reason

(** 2.7 IEEE 754 Floating Point Semantics

    F* has no native floats. We trust hardware implements
    IEEE 754 correctly (NaN, rounding, denormals, etc.).
*)
val ieee754_semantics : unit ->
  Lemma (ensures True)
  (* Actual: float ops match IEEE 754 spec *)

val ieee754_class : unit -> Tot axiom_class
val ieee754_reason : unit -> Tot unprovability_reason

(** 2.8 Memory Ordering Models (x86-TSO, ARM, RISC-V)

    Hardware memory models are reverse-engineered from observations.
    Errata exist. We trust documented behavior is complete.
*)
val memory_ordering_model : unit ->
  Lemma (ensures True)
  (* Actual: Promising Semantics ⊆ hardware behaviors *)

val memory_ordering_class : unit -> Tot axiom_class
val memory_ordering_reason : unit -> Tot unprovability_reason

(* ----------------------------------------------------------------------------
   LEVEL 4: COMPILER AND TOOLCHAIN
   These trust that compilers preserve semantics.
   ---------------------------------------------------------------------------- *)

(** 2.9 Compiler Semantics Preservation

    Non-verified compilers (GCC, Clang, rustc) may have bugs.
    CompCert is verified but only for C.

    Compiler optimization bugs could invalidate source-level analysis.
*)
val compiler_correctness : unit ->
  Lemma (ensures True)
  (* Actual: compiled code ≡ source semantics *)

val compiler_class : unit -> Tot axiom_class
val compiler_reason : unit -> Tot unprovability_reason

(** 2.10 ABI/Platform Behavior

    Platform ABIs (System V AMD64, Windows x64) are external specs.
    Struct layout, calling conventions, etc.
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

   ┌─────────────────────────────────────────────────────────────┐
   │ Level 0: F*/Z3 (2 axioms) - unavoidable verification base  │
   ├─────────────────────────────────────────────────────────────┤
   │ Level 1: Memory Model (1 axiom) - unified for ALL langs    │
   ├─────────────────────────────────────────────────────────────┤
   │ Level 2: Parser/Frontend (2 axioms) - AST construction     │
   ├─────────────────────────────────────────────────────────────┤
   │ Level 3: Hardware (3 axioms) - atomics, floats, ordering   │
   ├─────────────────────────────────────────────────────────────┤
   │ Level 4: Toolchain (2 axioms) - compiler, ABI              │
   └─────────────────────────────────────────────────────────────┘

   VERIFIED WITHOUT ADDITIONAL TRUST:
   ✓ Ownership tracking (separation logic)
   ✓ Region/lifetime safety (borrow checker)
   ✓ Linear resource usage (mode system)
   ✓ Frame isolation (separation logic)
   ✓ Borrow validity (borrow checker)

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

    Declassification requires precise specification of WHAT, WHERE, WHO, and WHEN
    information is released. The programmer's placement of declassify() must
    accurately reflect the intended security policy.

    Why Unprovable:
    Whether a declassify() call represents intentional release or a bug exists
    in programmer's mind - outside formal reasoning. This is the "Four Dimensions"
    problem (Sabelfeld & Sands 2009).

    What IS Provable:
    - Robustness: attacker cannot influence WHAT gets declassified (Chong 2004)
    - Type soundness: well-typed programs satisfy noninterference until declassification
    - Condition truth: declassification occurs only when specified conditions hold

    Literature: Chong & Myers 2004, Sabelfeld & Sands 2009
    Location: synthesis_part8.tex:837-840, 952-972
*)
val declassification_intentionality : unit ->
  Lemma (ensures True)
  (* Actual: programmer's declassify() annotations reflect actual intent *)

val declassification_intentionality_class : unit -> Tot axiom_class
val declassification_intentionality_reason : unit -> Tot unprovability_reason

(** 3.2 Taint Source/Sink Completeness (ENVIRONMENT ENUMERATION)

    The enumeration of taint sources and sinks claims:
    "ALL untrusted data enters through these sources;
     ALL dangerous operations are these sinks."

    This is environment-dependent:
    - New APIs introduce new sources/sinks
    - Framework-specific entry points
    - Platform-specific behaviors

    What IS Provable:
    - IFDS framework soundness (Reps 1995): if enumeration is complete, analysis finds all flows
    - Explicit flow propagation: taint correctly tracks through assignments, calls, returns
    - Lattice properties: taint lattice is well-formed

    Literature: Livshits & Lam 2005 (Section 3.2):
    "The problem of obtaining a complete specification for a tainted object
     propagation problem is an important one."

    Location: synthesis_part8.tex:167-203
*)
val taint_source_sink_completeness : unit ->
  Lemma (ensures True)
  (* Actual: source/sink enumeration is complete for target environment *)

val taint_source_sink_class : unit -> Tot axiom_class
val taint_source_sink_reason : unit -> Tot unprovability_reason

(** 3.3 Sanitizer Effectiveness (EXTERNAL LIBRARY + ATTACK MODEL)

    Sanitizer effectiveness depends on:
    1. External library implementation - is the escaping function bug-free?
    2. Context-specific encoding - HTML attribute vs HTML text vs JS string
    3. Parser differentials - browsers parse HTML differently
    4. Attack model completeness - are all attack vectors known?

    What IS Provable:
    - Sanitizer REMOVES specified taint kinds (from IFDSTaint.fst)
    - Type of sanitizer matches type of sink
    - Sanitizer is applied before sink access

    Literature: Sabelfeld & Myers 2003 (Section IV-D):
    "Declassification is inherently dangerous... sanitizers depend on
     context-specific semantics."

    Location: synthesis_part8.tex:240-272
*)
val sanitizer_effectiveness : unit ->
  Lemma (ensures True)
  (* Actual: sanitizer implementations correctly neutralize specified threats *)

val sanitizer_effectiveness_class : unit -> Tot axiom_class
val sanitizer_effectiveness_reason : unit -> Tot unprovability_reason

(** 3.4 Security Policy Validity (USER-PROVIDED POLICY)

    Security labels correctly capture the confidentiality and integrity
    requirements of the application. The user-provided security policy
    reflects actual security needs.

    Security policy is a SPECIFICATION, not a theorem:
    - Whether "password" should be High depends on business requirements
    - Whether certain data flows are acceptable is domain-specific
    - Organizational trust hierarchies are external

    What IS Provable:
    - Policy CONSISTENCY: labels form a valid lattice
    - Policy ENFORCEMENT: well-typed programs respect the policy
    - Policy ROBUSTNESS: attackers cannot subvert policy through low-integrity influence

    Literature: Myers 1997 (DLM):
    "The principal hierarchy correctly reflects organizational trust...
     modifications to the principal structure are extremely powerful."

    Location: synthesis_part8.tex:150-155
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

   ┌─────────────────────────────────┬──────────────────────────────────┐
   │ What's PROVABLE                 │ What's AXIOMATIC                 │
   ├─────────────────────────────────┼──────────────────────────────────┤
   │ Noninterference (Volpano 1996)  │ Declassification intent          │
   │ Robustness (Chong 2004)         │ Source/sink completeness         │
   │ IFDS soundness (Reps 1995)      │ Sanitizer effectiveness          │
   │ Galois connection (Cousot 1977) │ Policy validity                  │
   │ Taint propagation mechanics     │ Environment enumeration          │
   └─────────────────────────────────┴──────────────────────────────────┘

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

    Kolmogorov axioms are FOUNDATIONAL MATHEMATICS - on the same level as:
    - Peano axioms for natural numbers
    - ZFC axioms for set theory

    You cannot PROVE axioms - you can only POSTULATE them.

    Kolmogorov Axioms:
    1. Non-negativity: P(E) >= 0 for all events E
    2. Unitarity: P(Omega) = 1 for sample space Omega
    3. Countable Additivity: P(union of disjoint events) = sum of P(events)

    Used For: Probabilistic abstract interpretation, uncertainty quantification.

    Location: synthesis_part2.tex:1003-1014
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
   - Proven in literature → DEFERRED_PROOF
   - Standard metatheory → DEFERRED_PROOF

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
   ============================================================================ *)

(** 10.1 Pointer Conversion Soundness (MEMORY MODEL BRIDGING)

    Cross-language pointer conversion preserves aliasing invariants.

    The Problem:
    - Rust `&mut T` has noalias guarantee (exclusive access)
    - C `T*` can alias freely
    - Converting Rust &mut to C *mut and back must preserve exclusivity

    Why Unprovable:
    This is memory model BRIDGING - we're connecting two different
    memory models (Rust's ownership vs C's raw pointers). Neither
    language's type system can verify the other's invariants.

    Not Covered by 2.3 (Memory Model):
    Axiom 2.3 covers memory behavior WITHIN a single model.
    This axiom covers BRIDGING between different models.

    Not Covered by 2.10 (ABI):
    ABI specifies data layout, not aliasing semantics.

    Literature: Patterson et al. 2022 (PLDI) discusses semantic interoperability
    but does not prove cross-model aliasing preservation.

    Location: synthesis_part11.tex, FFI boundary handling
*)
val pointer_conversion_soundness : unit ->
  Lemma (ensures True)
  (* Actual: Converting Rust &mut to C *mut and back preserves exclusivity *)

val pointer_conversion_class : unit -> Tot axiom_class
val pointer_conversion_reason : unit -> Tot unprovability_reason

(** 10.2 Python/Rust Runtime Interop (RUNTIME API TRUST)

    CPython C API functions behave correctly.

    The Problem:
    - PyO3/rust-cpython call CPython C API functions
    - PyLong_AsLong, PyList_GetItem, PyDict_SetItem, etc.
    - These are implemented in CPython (~400K lines of C)

    Why Unprovable:
    CPython is an external runtime - we cannot verify its implementation.
    We must trust that:
    - Reference counting is correct
    - Type checks return accurate results
    - Memory management doesn't corrupt the heap

    Not Covered by 2.9 (Compiler):
    Compilers transform source to binary.
    This is about runtime API behavior, not compilation.

    Not Covered by 2.10 (ABI):
    ABI specifies calling conventions.
    This is about semantic behavior of API functions.

    Applies To: Any runtime with C API
    - CPython (Python)
    - JNI (Java)
    - V8 C++ API (JavaScript/Node.js)
    - Ruby C API

    Location: synthesis_part11.tex, cross-language FFI
*)
val runtime_interop_correctness : unit ->
  Lemma (ensures True)
  (* Actual: Runtime C API functions behave as documented *)

val runtime_interop_class : unit -> Tot axiom_class
val runtime_interop_reason : unit -> Tot unprovability_reason

(** 10.3 Dynamic Dispatch Resolution (RUNTIME DISPATCH SEMANTICS)

    Runtime dispatch mechanisms follow language specifications.

    The Problem:
    - Python: Method Resolution Order (MRO) via C3 linearization
    - Java: vtable dispatch for virtual methods
    - JavaScript: prototype chain lookup
    - C++: vtable + RTTI for virtual calls

    Why Unprovable:
    Dispatch resolution happens at RUNTIME based on:
    - Object's actual type (not static type)
    - Class hierarchy at time of call
    - Prototype chain state

    We cannot verify that runtimes correctly implement these algorithms.

    Not Covered by 2.5 (Frontend):
    Frontend handles STATIC type checking.
    This is about DYNAMIC dispatch at runtime.

    Not Covered by 2.9 (Compiler):
    Compiler generates vtable/dispatch code.
    This is about runtime EXECUTION of that code.

    Impact on Analysis:
    Call graph construction must over-approximate possible dispatch targets.
    Axiom 1.13 (Call Graph Completeness) depends on this.

    Location: synthesis_part11.tex, dynamic dispatch handling
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

   ┌─────────────────────────────────────────────────────────────┐
   │ 10.1 Pointer Conversion    - Memory model bridging         │
   │ 10.2 Runtime Interop       - Runtime API trust (CPython)   │
   │ 10.3 Dispatch Resolution   - Dynamic dispatch semantics    │
   └─────────────────────────────────────────────────────────────┘

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
   ─────────────────────────────────────────────────
   TOTAL:                                 36 axioms

   These form the IRREDUCIBLE TRUSTED COMPUTING BASE of brrr-lang.

   Everything else is either:
   - DEFINITIONAL (establishes meaning, not assumption)
   - DEFERRED_PROOF (provable with mechanization effort)
   - REDUNDANT (covered by another axiom)
   - F* BUILTIN (handled by F* itself)

   See AXIOMS_REPORT_v2.md for full justifications and literature references.

   ============================================================================ *)
