(**
 * TestLattices - Comprehensive Lattice Law Tests
 *
 * Verifies that all lattice structures in brrr-lang satisfy:
 *   - Reflexivity, Transitivity, Antisymmetry (partial order)
 *   - Commutativity, Associativity, Idempotence (lattice operations)
 *   - Absorption laws (lattice identity)
 *   - Semiring laws for modes
 *
 * Following HACL*/EverParse testing patterns with SMTPat triggers.
 *)
module TestLattices

open FStar.List.Tot
open TaintAnalysis
open SecurityTypes
open Modes
open Effects

(** Z3 solver options for test tractability *)
#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** ============================================================================
    TAINT LATTICE TESTS
    ============================================================================ *)

(** Test taint_kind equality is reflexive *)
let test_taint_kind_eq_refl () : Lemma (True) =
  taint_kind_eq_refl TaintSQLi;
  taint_kind_eq_refl TaintXSS;
  taint_kind_eq_refl TaintCMDi;
  taint_kind_eq_refl TaintPathTraversal;
  taint_kind_eq_refl TaintSSRF

(** Test taint status equality reflexivity *)
let test_taint_status_eq_refl () : Lemma (True) =
  taint_status_eq_refl Untainted;
  taint_status_eq_refl (Tainted [TaintSQLi]);
  taint_status_eq_refl (Tainted [TaintSQLi; TaintXSS]);
  taint_status_eq_refl (Tainted [])

(** Test taint_join is commutative via taint_contains *)
let test_taint_join_comm () : Lemma (True) =
  let t1 = Tainted [TaintSQLi] in
  let t2 = Tainted [TaintXSS] in
  taint_join_comm_contains t1 t2 TaintSQLi;
  taint_join_comm_contains t1 t2 TaintXSS;
  taint_join_comm_contains t1 t2 TaintCMDi

(** Test taint_join is associative via taint_contains *)
let test_taint_join_assoc () : Lemma (True) =
  let t1 = Tainted [TaintSQLi] in
  let t2 = Tainted [TaintXSS] in
  let t3 = Tainted [TaintCMDi] in
  taint_join_assoc_contains t1 t2 t3 TaintSQLi;
  taint_join_assoc_contains t1 t2 t3 TaintXSS;
  taint_join_assoc_contains t1 t2 t3 TaintCMDi

(** Test taint_join is idempotent via taint_contains *)
let test_taint_join_idem () : Lemma (True) =
  let t = Tainted [TaintSQLi; TaintXSS] in
  taint_join_idem_contains t TaintSQLi;
  taint_join_idem_contains t TaintXSS;
  taint_join_idempotent t

(** Test taint_meet is idempotent via taint_contains *)
let test_taint_meet_idem () : Lemma (True) =
  let t = Tainted [TaintSQLi; TaintXSS] in
  taint_meet_idem_contains t TaintSQLi;
  taint_meet_idem_contains t TaintXSS;
  taint_meet_idempotent t

(** Test taint absorption laws *)
let test_taint_absorption () : Lemma (True) =
  let t1 = Tainted [TaintSQLi; TaintXSS] in
  let t2 = Tainted [TaintSQLi] in
  (* Absorption 1: join(t, meet(t, s)) = t *)
  taint_absorption1 t1 t2;
  taint_absorption1_contains t1 t2 TaintSQLi;
  taint_absorption1_contains t1 t2 TaintXSS;
  (* Absorption 2: meet(t, join(t, s)) = t *)
  taint_absorption2 t1 t2;
  taint_absorption2_contains t1 t2 TaintSQLi;
  taint_absorption2_contains t1 t2 TaintXSS

(** Test taint ordering reflexivity *)
let test_taint_leq_refl () : Lemma (True) =
  taint_leq_refl Untainted;
  taint_leq_refl (Tainted [TaintSQLi]);
  taint_leq_refl (Tainted [TaintSQLi; TaintXSS])

(** Test Untainted is bottom element *)
let test_taint_leq_bot () : Lemma (True) =
  taint_leq_bot Untainted;
  taint_leq_bot (Tainted [TaintSQLi]);
  taint_leq_bot (Tainted [TaintSQLi; TaintXSS; TaintCMDi])

(** Test taint ordering transitivity *)
let test_taint_leq_trans () : Lemma (True) =
  let t1 = Untainted in
  let t2 = Tainted [TaintSQLi] in
  let t3 = Tainted [TaintSQLi; TaintXSS] in
  (* t1 <= t2 and t2 <= t3 implies t1 <= t3 *)
  taint_leq_trans t1 t2 t3

(** Test taint_join is least upper bound *)
let test_taint_join_lub () : Lemma (True) =
  let t1 = Tainted [TaintSQLi] in
  let t2 = Tainted [TaintXSS] in
  taint_join_lub t1 t2

(** ============================================================================
    SECURITY LABEL LATTICE TESTS
    ============================================================================ *)

(** Test confidentiality ordering reflexivity *)
let test_conf_leq_refl () : Lemma (True) =
  conf_leq_refl CPublic;
  conf_leq_refl CSecret

(** Test integrity ordering reflexivity *)
let test_integ_leq_refl () : Lemma (True) =
  integ_leq_refl ITrusted;
  integ_leq_refl IUntrusted

(** Test security label ordering reflexivity *)
let test_sec_label_leq_refl () : Lemma (True) =
  sec_label_leq_refl sec_bot;
  sec_label_leq_refl sec_top;
  sec_label_leq_refl sec_public_trusted;
  sec_label_leq_refl sec_secret_trusted

(** Test confidentiality transitivity *)
let test_conf_leq_trans () : Lemma (True) =
  (* CPublic <= CPublic and CPublic <= CSecret implies CPublic <= CSecret *)
  conf_leq_trans CPublic CPublic CSecret

(** Test integrity transitivity *)
let test_integ_leq_trans () : Lemma (True) =
  (* IUntrusted <= IUntrusted and IUntrusted <= ITrusted implies IUntrusted <= ITrusted *)
  integ_leq_trans IUntrusted IUntrusted ITrusted

(** Test security label transitivity *)
let test_sec_label_leq_trans () : Lemma (True) =
  let l1 = sec_bot in
  let l2 = sec_public_trusted in
  let l3 = sec_top in
  sec_label_leq_trans l1 l2 l3

(** Test confidentiality antisymmetry *)
let test_conf_leq_antisym () : Lemma (True) =
  conf_leq_antisym CPublic CPublic;
  conf_leq_antisym CSecret CSecret

(** Test integrity antisymmetry *)
let test_integ_leq_antisym () : Lemma (True) =
  integ_leq_antisym ITrusted ITrusted;
  integ_leq_antisym IUntrusted IUntrusted

(** Test security label join is upper bound (left) *)
let test_sec_label_join_upper_l () : Lemma (True) =
  let l1 = sec_public_trusted in
  let l2 = sec_secret_trusted in
  sec_label_join_upper_l l1 l2

(** Test security label join is upper bound (right) *)
let test_sec_label_join_upper_r () : Lemma (True) =
  let l1 = sec_public_trusted in
  let l2 = sec_secret_trusted in
  sec_label_join_upper_r l1 l2

(** Test security label join is least upper bound *)
let test_sec_label_join_lub () : Lemma (True) =
  let l1 = sec_public_trusted in
  let l2 = sec_tainted TkSQLi in
  let u = sec_top in
  sec_label_join_lub l1 l2 u

(** Test security label meet is lower bound (left) *)
let test_sec_label_meet_lower_l () : Lemma (True) =
  let l1 = sec_top in
  let l2 = sec_secret_trusted in
  sec_label_meet_lower_l l1 l2

(** Test security label meet is lower bound (right) *)
let test_sec_label_meet_lower_r () : Lemma (True) =
  let l1 = sec_top in
  let l2 = sec_secret_trusted in
  sec_label_meet_lower_r l1 l2

(** Test security label join commutativity *)
let test_sec_label_join_comm () : Lemma (True) =
  let l1 = sec_public_trusted in
  let l2 = sec_tainted TkXSS in
  sec_label_join_comm l1 l2

(** Test security label join idempotence *)
let test_sec_label_join_idem () : Lemma (True) =
  sec_label_join_idem sec_bot;
  sec_label_join_idem sec_top;
  sec_label_join_idem sec_public_trusted;
  sec_label_join_idem (sec_tainted TkSQLi)

(** Test security label meet commutativity *)
let test_sec_label_meet_comm () : Lemma (True) =
  let l1 = sec_public_trusted in
  let l2 = sec_tainted TkCMDi in
  sec_label_meet_comm l1 l2

(** Test security label meet idempotence *)
let test_sec_label_meet_idem () : Lemma (True) =
  sec_label_meet_idem sec_bot;
  sec_label_meet_idem sec_top;
  sec_label_meet_idem sec_public_trusted;
  sec_label_meet_idem (sec_tainted TkPathTraversal)

(** ============================================================================
    MODE SEMIRING TESTS
    ============================================================================ *)

(** Test mode addition commutativity *)
let test_mode_add_comm () : Lemma (True) =
  mode_add_comm MZero MOne;
  mode_add_comm MOne MOmega;
  mode_add_comm MZero MOmega

(** Test mode addition associativity *)
let test_mode_add_assoc () : Lemma (True) =
  mode_add_assoc MZero MOne MOmega;
  mode_add_assoc MOne MOne MOne;
  mode_add_assoc MOmega MZero MOne

(** Test zero is additive identity *)
let test_mode_add_zero () : Lemma (True) =
  mode_add_zero MZero;
  mode_add_zero MOne;
  mode_add_zero MOmega

(** Test mode multiplication associativity *)
let test_mode_mul_assoc () : Lemma (True) =
  mode_mul_assoc MZero MOne MOmega;
  mode_mul_assoc MOne MOne MOne;
  mode_mul_assoc MOmega MOmega MOmega

(** Test one is multiplicative identity *)
let test_mode_mul_one () : Lemma (True) =
  mode_mul_one MZero;
  mode_mul_one MOne;
  mode_mul_one MOmega

(** Test zero annihilates *)
let test_mode_mul_zero () : Lemma (True) =
  mode_mul_zero MZero;
  mode_mul_zero MOne;
  mode_mul_zero MOmega

(** Test mode distributivity: m1 * (m2 + m3) = (m1 * m2) + (m1 * m3) *)
let test_mode_distrib () : Lemma (True) =
  mode_distrib MOne MZero MOmega;
  mode_distrib MOmega MOne MOne;
  mode_distrib MZero MOne MOmega

(** Test mode ordering reflexivity *)
let test_mode_leq_refl () : Lemma (True) =
  mode_leq_refl MZero;
  mode_leq_refl MOne;
  mode_leq_refl MOmega

(** Test mode ordering transitivity *)
let test_mode_leq_trans () : Lemma (True) =
  mode_leq_trans MZero MZero MOne;
  mode_leq_trans MZero MOne MOmega

(** Test mode join commutativity *)
let test_mode_join_comm () : Lemma (True) =
  mode_join_comm MZero MOne;
  mode_join_comm MOne MOmega;
  mode_join_comm MZero MOmega

(** Test mode join associativity *)
let test_mode_join_assoc () : Lemma (True) =
  mode_join_assoc MZero MOne MOmega;
  mode_join_assoc MOne MOne MOne

(** Test mode join with zero (identity) *)
let test_mode_join_zero () : Lemma (True) =
  mode_join_zero MZero;
  mode_join_zero MOne;
  mode_join_zero MOmega

(** Test mode join with omega (top) *)
let test_mode_join_omega () : Lemma (True) =
  mode_join_omega MZero;
  mode_join_omega MOne;
  mode_join_omega MOmega

(** Test mode join idempotence *)
let test_mode_join_idemp () : Lemma (True) =
  mode_join_idemp MZero;
  mode_join_idemp MOne;
  mode_join_idemp MOmega

(** Test mode meet commutativity *)
let test_mode_meet_comm () : Lemma (True) =
  mode_meet_comm MZero MOne;
  mode_meet_comm MOne MOmega;
  mode_meet_comm MZero MOmega

(** Test mode meet associativity *)
let test_mode_meet_assoc () : Lemma (True) =
  mode_meet_assoc MZero MOne MOmega;
  mode_meet_assoc MOne MOne MOne

(** Test mode meet with omega (identity) *)
let test_mode_meet_omega () : Lemma (True) =
  mode_meet_omega MZero;
  mode_meet_omega MOne;
  mode_meet_omega MOmega

(** Test mode meet with zero (bottom) *)
let test_mode_meet_zero () : Lemma (True) =
  mode_meet_zero MZero;
  mode_meet_zero MOne;
  mode_meet_zero MOmega

(** Test mode meet idempotence *)
let test_mode_meet_idemp () : Lemma (True) =
  mode_meet_idemp MZero;
  mode_meet_idemp MOne;
  mode_meet_idemp MOmega

(** Test mode ordering antisymmetry *)
let test_mode_leq_antisym () : Lemma (True) =
  mode_leq_antisym MZero MZero;
  mode_leq_antisym MOne MOne;
  mode_leq_antisym MOmega MOmega

(** Test mode absorption: join(m, meet(m, n)) = m *)
let test_mode_absorb_join_meet () : Lemma (True) =
  mode_absorb_join_meet MZero MOne;
  mode_absorb_join_meet MOne MOmega;
  mode_absorb_join_meet MOmega MZero

(** Test mode absorption: meet(m, join(m, n)) = m *)
let test_mode_absorb_meet_join () : Lemma (True) =
  mode_absorb_meet_join MZero MOne;
  mode_absorb_meet_join MOne MOmega;
  mode_absorb_meet_join MOmega MZero

(** Test mode ordering via join *)
let test_mode_leq_join () : Lemma (True) =
  mode_leq_join MZero MOne;
  mode_leq_join MOne MOmega;
  mode_leq_join MZero MOmega

(** Test mode ordering via meet *)
let test_mode_leq_meet () : Lemma (True) =
  mode_leq_meet MZero MOne;
  mode_leq_meet MOne MOmega;
  mode_leq_meet MZero MOmega

(** ============================================================================
    EFFECT ROW LATTICE TESTS
    ============================================================================ *)

(** Test effect operation equality reflexivity *)
let test_effect_op_eq_refl () : Lemma (True) =
  effect_op_eq_refl EAlloc;
  effect_op_eq_refl EDiv;
  effect_op_eq_refl EPanic;
  effect_op_eq_refl EIO;
  effect_op_eq_refl (ERead LocUnknown);
  effect_op_eq_refl (EWrite LocUnknown)

(** Test effect row equality reflexivity *)
let test_row_eq_refl () : Lemma (True) =
  row_eq_refl RowEmpty;
  row_eq_refl (RowExt EAlloc RowEmpty);
  row_eq_refl (RowExt EDiv (RowExt EPanic RowEmpty))

(** Test row_join with pure (identity) *)
let test_row_join_pure () : Lemma (True) =
  row_join_pure RowEmpty;
  row_join_pure (RowExt EAlloc RowEmpty);
  row_join_pure (RowExt EDiv (RowExt EPanic RowEmpty))

(** Test has_effect on extended row *)
let test_has_effect_head () : Lemma (True) =
  has_effect_head EAlloc RowEmpty;
  has_effect_head EDiv (RowExt EAlloc RowEmpty);
  has_effect_head EPanic (RowExt EDiv RowEmpty)

(** Test row_join idempotence *)
let test_row_join_idem () : Lemma (True) =
  row_join_idem RowEmpty;
  row_join_idem (RowExt EAlloc RowEmpty);
  row_join_idem (RowExt EDiv (RowExt EPanic RowEmpty))

(** Test row_subset reflexivity *)
let test_row_subset_refl () : Lemma (True) =
  row_subset_refl RowEmpty;
  row_subset_refl (RowExt EAlloc RowEmpty)

(** Test row equality symmetry *)
let test_row_eq_sym () : Lemma (True) =
  let r = RowExt EAlloc RowEmpty in
  row_eq_sym r r

(** Test row equality transitivity *)
let test_row_eq_trans () : Lemma (True) =
  let r = RowExt EAlloc RowEmpty in
  row_eq_trans r r r

(** ============================================================================
    FRACTION PERMISSION TESTS
    ============================================================================ *)

(** Test fraction equality reflexivity *)
let test_frac_eq_refl () : Lemma (True) =
  frac_eq_refl frac_full;
  frac_eq_refl frac_half

(** Test fraction equality symmetry *)
let test_frac_eq_sym () : Lemma (True) =
  frac_eq_sym frac_full frac_full;
  frac_eq_sym frac_half frac_half

(** Test fraction equality transitivity *)
let test_frac_eq_trans () : Lemma (True) =
  frac_eq_trans frac_full frac_full frac_full;
  frac_eq_trans frac_half frac_half frac_half

(** Test fraction ordering transitivity *)
let test_frac_leq_trans () : Lemma (True) =
  frac_leq_trans frac_half frac_half frac_full

(** ============================================================================
    TAINT PROPAGATION SOUNDNESS TESTS
    ============================================================================ *)

(** Test sanitize removes the targeted taint *)
let test_sanitize_removes_taint () : Lemma (True) =
  let t : tainted string = tainted_with "user input" TaintSQLi in
  let escape_fn (s: string) : string = s in  (* placeholder *)
  sanitize_removes_taint TaintSQLi t escape_fn

(** Test sanitize preserves other taints *)
let test_sanitize_preserves_other () : Lemma (True) =
  let t : tainted string = { value = "input"; taint = Tainted [TaintSQLi; TaintXSS] } in
  let escape_fn (s: string) : string = s in
  (* After sanitizing SQLi, XSS should remain *)
  sanitize_preserves_other_taints TaintSQLi TaintXSS t escape_fn

(** Test sink soundness: sink succeeds iff taint not present *)
let test_sink_soundness () : Lemma (True) =
  let safe : tainted string = untainted "safe" in
  let unsafe : tainted string = tainted_with "unsafe" TaintSQLi in
  sink_soundness TaintSQLi safe;
  sink_soundness TaintSQLi unsafe

(** Test sanitize then sink succeeds *)
let test_sanitize_then_sink () : Lemma (True) =
  let t : tainted string = tainted_with "input" TaintSQLi in
  let escape_fn (s: string) : string = s in
  sanitize_then_sink TaintSQLi t escape_fn

(** Test taint_map preserves taint status *)
let test_taint_map_preserves () : Lemma (True) =
  let t : tainted int = tainted_with 42 TaintSQLi in
  let f (x: int) : int = x + 1 in
  taint_map_preserves_taint f t

(** Test taint_map2 combines taints correctly *)
let test_taint_map2_combines () : Lemma (True) =
  let t1 : tainted int = tainted_with 1 TaintSQLi in
  let t2 : tainted int = tainted_with 2 TaintXSS in
  let f (x: int) (y: int) : int = x + y in
  taint_map2_combines_taints f t1 t2 TaintSQLi;
  taint_map2_combines_taints f t1 t2 TaintXSS

(** ============================================================================
    SECURITY LABEL TAINT OPERATIONS
    ============================================================================ *)

(** Test remove_taint correctness *)
let test_remove_taint_correct () : Lemma (True) =
  remove_taint_correct TkSQLi [TkSQLi; TkXSS];
  remove_taint_correct TkXSS [TkSQLi; TkXSS];
  remove_taint_correct TkCMDi []

(** Test remove_taint preserves other taints *)
let test_remove_taint_preserves () : Lemma (True) =
  remove_taint_preserves TkSQLi TkXSS [TkSQLi; TkXSS];
  remove_taint_preserves TkXSS TkCMDi [TkXSS; TkCMDi]

(** Test sanitize enables sink check *)
let test_sanitize_enables_sink () : Lemma (True) =
  let l = sec_tainted TkSQLi in
  sanitize_enables_sink [TkSQLi] l

(** ============================================================================
    COMPREHENSIVE LATTICE LAW VALIDATION
    ============================================================================

    Run all lattice tests to validate the algebraic structure.
    Each test corresponds to a fundamental lattice/semiring law.
*)

let run_all_taint_tests () : Lemma (True) =
  test_taint_kind_eq_refl ();
  test_taint_status_eq_refl ();
  test_taint_join_comm ();
  test_taint_join_assoc ();
  test_taint_join_idem ();
  test_taint_meet_idem ();
  test_taint_absorption ();
  test_taint_leq_refl ();
  test_taint_leq_bot ();
  test_taint_leq_trans ();
  test_taint_join_lub ()

let run_all_security_label_tests () : Lemma (True) =
  test_conf_leq_refl ();
  test_integ_leq_refl ();
  test_sec_label_leq_refl ();
  test_conf_leq_trans ();
  test_integ_leq_trans ();
  test_sec_label_leq_trans ();
  test_conf_leq_antisym ();
  test_integ_leq_antisym ();
  test_sec_label_join_upper_l ();
  test_sec_label_join_upper_r ();
  test_sec_label_join_lub ();
  test_sec_label_meet_lower_l ();
  test_sec_label_meet_lower_r ();
  test_sec_label_join_comm ();
  test_sec_label_join_idem ();
  test_sec_label_meet_comm ();
  test_sec_label_meet_idem ()

let run_all_mode_tests () : Lemma (True) =
  test_mode_add_comm ();
  test_mode_add_assoc ();
  test_mode_add_zero ();
  test_mode_mul_assoc ();
  test_mode_mul_one ();
  test_mode_mul_zero ();
  test_mode_distrib ();
  test_mode_leq_refl ();
  test_mode_leq_trans ();
  test_mode_join_comm ();
  test_mode_join_assoc ();
  test_mode_join_zero ();
  test_mode_join_omega ();
  test_mode_join_idemp ();
  test_mode_meet_comm ();
  test_mode_meet_assoc ();
  test_mode_meet_omega ();
  test_mode_meet_zero ();
  test_mode_meet_idemp ();
  test_mode_leq_antisym ();
  test_mode_absorb_join_meet ();
  test_mode_absorb_meet_join ();
  test_mode_leq_join ();
  test_mode_leq_meet ()

let run_all_effect_tests () : Lemma (True) =
  test_effect_op_eq_refl ();
  test_row_eq_refl ();
  test_row_join_pure ();
  test_has_effect_head ();
  test_row_join_idem ();
  test_row_subset_refl ();
  test_row_eq_sym ();
  test_row_eq_trans ()

let run_all_taint_propagation_tests () : Lemma (True) =
  test_sanitize_removes_taint ();
  test_sanitize_preserves_other ();
  test_sink_soundness ();
  test_sanitize_then_sink ();
  test_taint_map_preserves ();
  test_taint_map2_combines ()

(** Master test runner *)
let run_all_lattice_tests () : Lemma (True) =
  run_all_taint_tests ();
  run_all_security_label_tests ();
  run_all_mode_tests ();
  run_all_effect_tests ();
  run_all_taint_propagation_tests ()
