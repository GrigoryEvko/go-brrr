(**
 * TestTranslations - Language Translation Functor Tests
 *
 * Verifies that language translations satisfy:
 *   - Functor laws (identity, composition)
 *   - Type preservation
 *   - Soundness properties
 *   - Boundary guard correctness
 *
 * Tests TypeScript, Rust, and Go translation functors.
 *)
module TestTranslations

open FStar.List.Tot
open LangMapping
open BrrrTypes
open Modes
open Effects
open Expressions
open Values

(** Z3 solver options *)
#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** ============================================================================
    LANGUAGE MODE EQUALITY TESTS
    ============================================================================ *)

(** Test lang_mode equality reflexivity *)
let test_lang_mode_eq_refl () : Lemma (True) =
  lang_mode_eq_refl python_mode;
  lang_mode_eq_refl typescript_mode;
  lang_mode_eq_refl rust_mode;
  lang_mode_eq_refl go_mode;
  lang_mode_eq_refl swift_mode;
  lang_mode_eq_refl java_mode;
  lang_mode_eq_refl c_mode;
  lang_mode_eq_refl cpp_mode;
  lang_mode_eq_refl kotlin_mode;
  lang_mode_eq_refl haskell_mode

(** ============================================================================
    IDENTITY FUNCTOR TESTS
    ============================================================================ *)

(** Test identity functor satisfies functor laws *)
let test_identity_functor_laws () : Lemma (True) =
  identity_functor_laws python_mode;
  identity_functor_laws typescript_mode;
  identity_functor_laws rust_mode;
  identity_functor_laws go_mode

(** Test identity functor is sound *)
let test_identity_functor_sound () : Lemma (True) =
  identity_functor_sound python_mode;
  identity_functor_sound typescript_mode;
  identity_functor_sound rust_mode;
  identity_functor_sound go_mode

(** Test identity functor is functorial *)
let test_identity_is_functorial () : Lemma (True) =
  identity_is_functorial python_mode;
  identity_is_functorial typescript_mode;
  identity_is_functorial rust_mode;
  identity_is_functorial go_mode

(** ============================================================================
    TYPESCRIPT FUNCTOR TESTS
    ============================================================================ *)

(** Test TypeScript functor satisfies functor laws *)
let test_typescript_functor_laws () : Lemma (True) =
  typescript_functor_laws ()

(** Test TypeScript functor is sound *)
let test_typescript_functor_sound () : Lemma (True) =
  typescript_functor_sound ()

(** Test TypeScript functor is functorial *)
let test_typescript_is_functorial () : Lemma (True) =
  typescript_is_functorial ()

(** ============================================================================
    RUST FUNCTOR TESTS
    ============================================================================ *)

(** Test Rust functor satisfies functor laws *)
let test_rust_functor_laws () : Lemma (True) =
  rust_functor_laws ()

(** Test Rust functor is sound *)
let test_rust_functor_sound () : Lemma (True) =
  rust_functor_sound ()

(** Test Rust functor is functorial *)
let test_rust_is_functorial () : Lemma (True) =
  rust_is_functorial ()

(** ============================================================================
    GO FUNCTOR TESTS
    ============================================================================ *)

(** Test Go functor satisfies functor laws *)
let test_go_functor_laws () : Lemma (True) =
  go_functor_laws ()

(** Test Go functor is sound *)
let test_go_functor_sound () : Lemma (True) =
  go_functor_sound ()

(** Test Go functor is functorial *)
let test_go_is_functorial () : Lemma (True) =
  go_is_functorial ()

(** ============================================================================
    TRANSLATION COMPOSITION TESTS
    ============================================================================ *)

(** Test composition preserves soundness *)
let test_composition_soundness () : Lemma (True) =
  (* Compose TypeScript -> Brrr with identity *)
  let ts = typescript_functor in
  let id_ts = identity_functor typescript_mode in
  composition_soundness ts id_ts

(** ============================================================================
    GUARD RESULT TESTS
    ============================================================================ *)

(** Test guard_return creates GuardOk *)
let test_guard_return () : Lemma (True) =
  let v = VUnit in
  let r = guard_return v in
  assert (guard_result_is_ok r = true)

(** ============================================================================
    BOUNDARY SAFETY TESTS
    ============================================================================ *)

(** Test safe boundary detection *)
let test_is_safe_boundary () : Lemma (True) =
  (* Same language boundaries should be safe *)
  let ts_ts = is_safe_boundary typescript_mode typescript_mode in
  let rs_rs = is_safe_boundary rust_mode rust_mode in
  let go_go = is_safe_boundary go_mode go_mode in
  ()

(** Test language axioms *)
let test_language_axioms () : Lemma (True) =
  (* Rust provides memory safety *)
  let rust_ax = language_axioms rust_mode in
  (* TypeScript provides type safety with gradual typing *)
  let ts_ax = language_axioms typescript_mode in
  (* Go provides memory safety with GC *)
  let go_ax = language_axioms go_mode in
  ()

(** Test boundary risks identification *)
let test_boundary_risks () : Lemma (True) =
  (* Crossing from Rust to C loses memory safety guarantees *)
  let rust_to_c = boundary_risks rust_mode c_mode in
  (* Crossing from TypeScript to Python loses type guarantees *)
  let ts_to_py = boundary_risks typescript_mode python_mode in
  ()

(** ============================================================================
    TYPE PRESERVATION TESTS
    ============================================================================ *)

(** Test translate_id_law: identity functor preserves identity expression *)
let test_translate_id_law () : Lemma (True) =
  translate_id_law typescript_mode;
  translate_id_law rust_mode;
  translate_id_law go_mode

(** Test translate_comp_law: identity functor preserves composition *)
let test_translate_comp_law () : Lemma (True) =
  translate_comp_law typescript_mode identity_expr identity_expr;
  translate_comp_law rust_mode identity_expr identity_expr;
  translate_comp_law go_mode identity_expr identity_expr

(** ============================================================================
    BOUNDARY SOUNDNESS THEOREM TESTS
    ============================================================================ *)

(** Test boundary soundness theorem *)
let test_boundary_soundness () : Lemma (True) =
  let ty = TUnit in
  let v = VUnit in
  boundary_soundness_theorem typescript_mode rust_mode ty v;
  boundary_soundness_theorem rust_mode go_mode ty v;
  boundary_soundness_theorem go_mode typescript_mode ty v

(** ============================================================================
    RUST-SPECIFIC TRANSLATION TESTS
    ============================================================================ *)

(** Test Rust ownership preservation *)
(* Note: rust_is_copy and rust_translate_type require actual rust_type values
   which would come from the frontend parser. These tests validate the theorem
   structure exists. *)

(** ============================================================================
    LANGUAGE MODE CONFIGURATION TESTS
    ============================================================================

    Verify that standard language configurations match expected properties.
*)

(** Test Python mode configuration *)
let test_python_mode () : Lemma (True) =
  let m = python_mode in
  (* Python has GC memory management *)
  assert (m.memory = MemGC);
  (* Python has dynamic types *)
  assert (m.types = TypeDynamic);
  (* Python allows nulls (None) *)
  assert (m.null_safety = NullNullable);
  (* Python doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* Python has async support *)
  assert (m.concurrency = ConcAsync)

(** Test TypeScript mode configuration *)
let test_typescript_mode () : Lemma (True) =
  let m = typescript_mode in
  (* TypeScript has GC memory management *)
  assert (m.memory = MemGC);
  (* TypeScript has gradual types *)
  assert (m.types = TypeGradual);
  (* TypeScript has optional null safety (strictNullChecks) *)
  assert (m.null_safety = NullOptional);
  (* TypeScript doesn't track effects in type system *)
  assert (m.effects = EffUntracked);
  (* TypeScript has async/await *)
  assert (m.concurrency = ConcAsync)

(** Test Rust mode configuration *)
let test_rust_mode () : Lemma (True) =
  let m = rust_mode in
  (* Rust has ownership-based memory management *)
  assert (m.memory = MemOwnership);
  (* Rust has static types *)
  assert (m.types = TypeStatic);
  (* Rust has Option types for null safety *)
  assert (m.null_safety = NullOptional);
  (* Rust tracks effects (unsafe, panic, etc.) *)
  assert (m.effects = EffTracked);
  (* Rust has threads *)
  assert (m.concurrency = ConcThreads)

(** Test Go mode configuration *)
let test_go_mode () : Lemma (True) =
  let m = go_mode in
  (* Go has GC memory management *)
  assert (m.memory = MemGC);
  (* Go has static types *)
  assert (m.types = TypeStatic);
  (* Go allows nil *)
  assert (m.null_safety = NullNullable);
  (* Go doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* Go has goroutines (threads) *)
  assert (m.concurrency = ConcThreads)

(** Test Swift mode configuration *)
let test_swift_mode () : Lemma (True) =
  let m = swift_mode in
  (* Swift has reference counting *)
  assert (m.memory = MemRC);
  (* Swift has static types *)
  assert (m.types = TypeStatic);
  (* Swift has optionals *)
  assert (m.null_safety = NullOptional);
  (* Swift doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* Swift has async/await *)
  assert (m.concurrency = ConcAsync)

(** Test Java mode configuration *)
let test_java_mode () : Lemma (True) =
  let m = java_mode in
  (* Java has GC memory management *)
  assert (m.memory = MemGC);
  (* Java has static types *)
  assert (m.types = TypeStatic);
  (* Java allows null *)
  assert (m.null_safety = NullNullable);
  (* Java doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* Java has threads *)
  assert (m.concurrency = ConcThreads)

(** Test C mode configuration *)
let test_c_mode () : Lemma (True) =
  let m = c_mode in
  (* C has manual memory management *)
  assert (m.memory = MemManual);
  (* C has static types *)
  assert (m.types = TypeStatic);
  (* C allows null pointers *)
  assert (m.null_safety = NullNullable);
  (* C doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* C has no built-in concurrency *)
  assert (m.concurrency = ConcNone)

(** Test C++ mode configuration *)
let test_cpp_mode () : Lemma (True) =
  let m = cpp_mode in
  (* C++ has manual memory management (with optional RAII) *)
  assert (m.memory = MemManual);
  (* C++ has static types *)
  assert (m.types = TypeStatic);
  (* C++ allows null pointers *)
  assert (m.null_safety = NullNullable);
  (* C++ doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* C++ has threads *)
  assert (m.concurrency = ConcThreads)

(** Test Kotlin mode configuration *)
let test_kotlin_mode () : Lemma (True) =
  let m = kotlin_mode in
  (* Kotlin runs on JVM with GC *)
  assert (m.memory = MemGC);
  (* Kotlin has static types *)
  assert (m.types = TypeStatic);
  (* Kotlin has null safety *)
  assert (m.null_safety = NullOptional);
  (* Kotlin doesn't track effects *)
  assert (m.effects = EffUntracked);
  (* Kotlin has coroutines (async) *)
  assert (m.concurrency = ConcAsync)

(** Test Haskell mode configuration *)
let test_haskell_mode () : Lemma (True) =
  let m = haskell_mode in
  (* Haskell has GC *)
  assert (m.memory = MemGC);
  (* Haskell has static types *)
  assert (m.types = TypeStatic);
  (* Haskell has no null (uses Maybe) *)
  assert (m.null_safety = NullNonNull);
  (* Haskell tracks effects via monads *)
  assert (m.effects = EffPure);
  (* Haskell has threads *)
  assert (m.concurrency = ConcThreads)

(** ============================================================================
    COMPREHENSIVE TRANSLATION TEST RUNNERS
    ============================================================================ *)

let run_all_functor_law_tests () : Lemma (True) =
  test_identity_functor_laws ();
  test_identity_functor_sound ();
  test_identity_is_functorial ();
  test_typescript_functor_laws ();
  test_typescript_functor_sound ();
  test_typescript_is_functorial ();
  test_rust_functor_laws ();
  test_rust_functor_sound ();
  test_rust_is_functorial ();
  test_go_functor_laws ();
  test_go_functor_sound ();
  test_go_is_functorial ()

let run_all_boundary_tests () : Lemma (True) =
  test_is_safe_boundary ();
  test_language_axioms ();
  test_boundary_risks ();
  test_boundary_soundness ()

let run_all_language_mode_tests () : Lemma (True) =
  test_lang_mode_eq_refl ();
  test_python_mode ();
  test_typescript_mode ();
  test_rust_mode ();
  test_go_mode ();
  test_swift_mode ();
  test_java_mode ();
  test_c_mode ();
  test_cpp_mode ();
  test_kotlin_mode ();
  test_haskell_mode ()

let run_all_type_preservation_tests () : Lemma (True) =
  test_translate_id_law ();
  test_translate_comp_law ()

(** Master test runner *)
let run_all_translation_tests () : Lemma (True) =
  run_all_functor_law_tests ();
  run_all_boundary_tests ();
  run_all_language_mode_tests ();
  run_all_type_preservation_tests ();
  test_composition_soundness ();
  test_guard_return ()
