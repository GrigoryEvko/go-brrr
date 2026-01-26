(**
 * Axioms.fst - Trusted Computing Base Implementation
 *
 * This module implements the 36 irreducible axioms that form brrr-lang's
 * Trusted Computing Base (TCB). Each axiom represents a property that
 * cannot be proven within the system due to:
 *
 *   - Computational limits (Halting Problem, Rice's Theorem)
 *   - External system trust (hardware, runtimes, parsers)
 *   - Semantic gaps (programmer intent, policy specification)
 *   - Foundational mathematics (Kolmogorov axioms)
 *
 * All implementations use admit() by design - these are axioms, not theorems.
 *
 * Reference: AXIOMS_REPORT_v2.md for full justifications and literature.
 *
 * @author brrr-lang team
 * @version 2.0
 * @since 2026-01-26
 *)
module Axioms

open FStar.List.Tot


(* ═══════════════════════════════════════════════════════════════════════════
   CATEGORY 1: COMPUTATIONAL UNDECIDABILITY
   ═══════════════════════════════════════════════════════════════════════════
   18 axioms arising from fundamental limits of computation.
   These cannot be decided by any algorithm (Turing 1936, Rice 1953).
   ═══════════════════════════════════════════════════════════════════════════ *)

(** 1.1  Program termination - Halting Problem *)
let termination_fuel_exists ()        = admit ()
let termination_fuel_exists_class ()  = TrueAxiom
let termination_fuel_exists_reason () = HaltingProblem

(** 1.2  Loop divergence - Halting Problem *)
let loop_divergence_conservative ()   = admit ()
let loop_divergence_class ()          = TrueAxiom
let loop_divergence_reason ()         = HaltingProblem

(** 1.3  Pattern exhaustiveness with guards - Halting Problem *)
let exhaustiveness_with_guards ()     = admit ()
let exhaustiveness_guards_class ()    = TrueAxiom
let exhaustiveness_guards_reason ()   = HaltingProblem

(** 1.4  General deadlock detection - Undecidable *)
let deadlock_detection ()             = admit ()
let deadlock_detection_class ()       = TrueAxiom
let deadlock_detection_decidability () = Undecidable

(** 1.5  Liveness properties - Rice's Theorem *)
let liveness_undecidable ()           = admit ()
let liveness_class ()                 = TrueAxiom
let liveness_reason ()                = RicesTheorem

(** 1.6  Termination channel detection - Halting Problem *)
let termination_channel_detection ()  = admit ()
let termination_channel_class ()      = TrueAxiom
let termination_channel_reason ()     = HaltingProblem

(** 1.7  Timing channel freedom - External + Halting *)
let timing_channel_freedom ()         = admit ()
let timing_channel_class ()           = TrueAxiom
let timing_channel_reason ()          = ExternalSystem

(** 1.8  Ranking function synthesis - Halting Problem *)
let ranking_function_synthesis ()     = admit ()
let ranking_function_class ()         = TrueAxiom
let ranking_function_reason ()        = HaltingProblem

(** 1.9  Linearizability verification - NP-complete *)
let linearizability_verification ()   = admit ()
let linearizability_class ()          = TrueAxiom
let linearizability_decidability ()   = ComplexityBounded

(** 1.10 Magic wand reasoning - PSPACE-complete *)
let magic_wand_reasoning ()           = admit ()
let magic_wand_class ()               = TrueAxiom
let magic_wand_decidability ()        = ComplexityBounded

(** 1.11 Widening operator termination - Infinite enumeration *)
let widening_termination ()           = admit ()
let widening_class ()                 = TrueAxiom
let widening_reason ()                = InfiniteEnumeration

(** 1.12 Transfer function monotonicity - Rice's Theorem *)
let transfer_monotonicity ()          = admit ()
let transfer_monotonicity_class ()    = TrueAxiom
let transfer_monotonicity_reason ()   = RicesTheorem

(** 1.13 Call graph completeness - Halting + Rice *)
let call_graph_completeness ()        = admit ()
let call_graph_class ()               = TrueAxiom
let call_graph_reason ()              = HaltingProblem

(** 1.14 Points-to analysis soundness - Rice's Theorem *)
let points_to_soundness ()            = admit ()
let points_to_class ()                = TrueAxiom
let points_to_reason ()               = RicesTheorem

(** 1.15 Data-race freedom determination - Infinite enumeration *)
let drf_determination ()              = admit ()
let drf_class ()                      = TrueAxiom
let drf_reason ()                     = InfiniteEnumeration

(** 1.16 Effect divergence absence - Halting Problem *)
let divergence_absence ()             = admit ()
let divergence_absence_class ()       = TrueAxiom
let divergence_absence_reason ()      = HaltingProblem

(** 1.17 Taint analysis completeness - Rice's Theorem *)
let taint_completeness ()             = admit ()
let taint_class ()                    = TrueAxiom
let taint_reason ()                   = RicesTheorem

(** 1.18 Interleaved Dyck reachability - Post Correspondence *)
let interleaved_dyck ()               = admit ()
let interleaved_dyck_class ()         = TrueAxiom
let interleaved_dyck_reason ()        = HaltingProblem


(* ═══════════════════════════════════════════════════════════════════════════
   CATEGORY 2: EXTERNAL SYSTEM TRUST
   ═══════════════════════════════════════════════════════════════════════════
   10 axioms representing trust in external systems we cannot verify.
   Organized by trust level (0 = unavoidable, 4 = toolchain).
   ═══════════════════════════════════════════════════════════════════════════ *)

(* --- Level 0: Unavoidable TCB -------------------------------------------- *)

(** 2.1  SMT solver correctness (Z3) *)
let smt_solver_correctness ()         = admit ()
let smt_solver_class ()               = TrueAxiom
let smt_solver_reason ()              = ExternalSystem

(** 2.2  F* type system soundness - Gödel's Second Incompleteness *)
let fstar_soundness ()                = admit ()
let fstar_soundness_class ()          = TrueAxiom
let fstar_soundness_reason ()         = GodelIncompleteness

(* --- Level 1: Memory Model ----------------------------------------------- *)

(** 2.3  Memory model correspondence - THE KEY AXIOM *)
let memory_model_correspondence ()    = admit ()
let memory_model_class ()             = TrueAxiom
let memory_model_reason ()            = ExternalSystem

(* --- Level 2: Parser/Frontend -------------------------------------------- *)

(** 2.4  Parser correctness (Tree-sitter) *)
let parser_correctness ()             = admit ()
let parser_class ()                   = TrueAxiom
let parser_reason ()                  = ExternalSystem

(** 2.5  Language frontend correctness (clang, tsc, etc.) *)
let frontend_correctness ()           = admit ()
let frontend_class ()                 = TrueAxiom
let frontend_reason ()                = ExternalSystem

(* --- Level 3: Hardware Semantics ----------------------------------------- *)

(** 2.6  Hardware atomicity guarantees *)
let hardware_atomicity ()             = admit ()
let hardware_atomicity_class ()       = TrueAxiom
let hardware_atomicity_reason ()      = ExternalSystem

(** 2.7  IEEE 754 floating-point semantics *)
let ieee754_semantics ()              = admit ()
let ieee754_class ()                  = TrueAxiom
let ieee754_reason ()                 = ExternalSystem

(** 2.8  Memory ordering models (x86-TSO, ARM, RISC-V) *)
let memory_ordering_model ()          = admit ()
let memory_ordering_class ()          = TrueAxiom
let memory_ordering_reason ()         = ExternalSystem

(* --- Level 4: Compiler/Toolchain ----------------------------------------- *)

(** 2.9  Compiler semantics preservation *)
let compiler_correctness ()           = admit ()
let compiler_class ()                 = TrueAxiom
let compiler_reason ()                = ExternalSystem

(** 2.10 ABI/platform behavior *)
let abi_correctness ()                = admit ()
let abi_class ()                      = TrueAxiom
let abi_reason ()                     = ExternalSystem


(* ═══════════════════════════════════════════════════════════════════════════
   CATEGORY 3: PROGRAMMER INTENT AND ENVIRONMENT
   ═══════════════════════════════════════════════════════════════════════════
   4 axioms bridging the semantic gap between syntax and meaning.
   These exist in the programmer's mind or target environment.
   ═══════════════════════════════════════════════════════════════════════════ *)

(** 3.1  Declassification intentionality - Programmer intent *)
let declassification_intentionality ()        = admit ()
let declassification_intentionality_class ()  = TrueAxiom
let declassification_intentionality_reason () = ProgrammerIntent

(** 3.2  Taint source/sink completeness - Environment enumeration *)
let taint_source_sink_completeness ()         = admit ()
let taint_source_sink_class ()                = TrueAxiom
let taint_source_sink_reason ()               = EnvironmentDependent

(** 3.3  Sanitizer effectiveness - External library + attack model *)
let sanitizer_effectiveness ()                = admit ()
let sanitizer_effectiveness_class ()          = TrueAxiom
let sanitizer_effectiveness_reason ()         = ExternalSystem

(** 3.4  Security policy validity - User-provided specification *)
let security_policy_validity ()               = admit ()
let security_policy_validity_class ()         = TrueAxiom
let security_policy_validity_reason ()        = PolicySpecification


(* ═══════════════════════════════════════════════════════════════════════════
   CATEGORY 4: FOUNDATIONAL MATHEMATICS
   ═══════════════════════════════════════════════════════════════════════════
   1 axiom representing foundational mathematics (same level as Peano/ZFC).
   ═══════════════════════════════════════════════════════════════════════════ *)

(** 4.1  Kolmogorov probability axioms - Foundational mathematics *)
let kolmogorov_probability_axioms ()  = admit ()
let kolmogorov_class ()               = TrueAxiom
let kolmogorov_reason ()              = FoundationalMath


(* ═══════════════════════════════════════════════════════════════════════════
   CATEGORY 10: FFI RUNTIME TRUST
   ═══════════════════════════════════════════════════════════════════════════
   3 axioms for cross-language interoperability runtime trust.
   These represent dynamic behavior we cannot statically verify.
   ═══════════════════════════════════════════════════════════════════════════ *)

(** 10.1 Pointer conversion soundness - Memory model bridging *)
let pointer_conversion_soundness ()   = admit ()
let pointer_conversion_class ()       = TrueAxiom
let pointer_conversion_reason ()      = ExternalSystem

(** 10.2 Runtime API interop (CPython, JNI, V8) - Runtime trust *)
let runtime_interop_correctness ()    = admit ()
let runtime_interop_class ()          = TrueAxiom
let runtime_interop_reason ()         = ExternalSystem

(** 10.3 Dynamic dispatch resolution (MRO, vtables, prototypes) *)
let dispatch_resolution_correctness () = admit ()
let dispatch_resolution_class ()       = TrueAxiom
let dispatch_resolution_reason ()      = ExternalSystem


(* ═══════════════════════════════════════════════════════════════════════════
   AXIOM COUNT SUMMARY
   ═══════════════════════════════════════════════════════════════════════════

   Category 1  - Computational Undecidability:    18 axioms
   Category 2  - External System Trust:           10 axioms
   Category 3  - Programmer Intent/Environment:    4 axioms
   Category 4  - Foundational Mathematics:         1 axiom
   Category 10 - FFI Runtime Trust:                3 axioms
   ────────────────────────────────────────────────────────────
   TOTAL TRUSTED COMPUTING BASE:                  36 axioms

   ═══════════════════════════════════════════════════════════════════════════ *)
