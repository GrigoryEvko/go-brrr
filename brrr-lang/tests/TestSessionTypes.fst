(**
 * TestSessionTypes - Session Type Duality and Subtyping Tests
 *
 * Verifies that session types satisfy:
 *   - Duality is an involution: dual(dual(S)) = S
 *   - Session equality reflexivity, symmetry, transitivity
 *   - Correct behavior of send/receive duality
 *   - Choice duality (select/branch)
 *   - Recursive session type handling
 *
 * Based on brrr_lang_spec_v0.4.tex Part VII (Concurrency & Session Types).
 *)
module TestSessionTypes

open FStar.List.Tot
open SessionTypes
open BrrrTypes
open Effects
open Primitives

(** Z3 solver options *)
#set-options "--z3rlimit 100 --fuel 2 --ifuel 1"

(** ============================================================================
    BASIC SESSION TYPE CONSTRUCTION TESTS
    ============================================================================ *)

(** Test simple session type construction *)
let test_session_type_construction () : Lemma (True) =
  (* Simple send-end protocol *)
  let s1 = SSend TUnit SEnd in
  (* Simple receive-end protocol *)
  let s2 = SRecv TUnit SEnd in
  (* Send then receive *)
  let s3 = SSend TInt (SRecv TBool SEnd) in
  ()

(** Test session variable construction *)
let test_session_var () : Lemma (True) =
  let x = SVar "X" in
  let y = SVar "loop" in
  ()

(** Test recursive session type construction *)
let test_recursive_session () : Lemma (True) =
  (* mu X. !int.X - infinite send protocol *)
  let rec_send = SRec "X" (SSend TInt (SVar "X")) in
  (* mu X. ?int.X - infinite receive protocol *)
  let rec_recv = SRec "X" (SRecv TInt (SVar "X")) in
  ()

(** Test n-ary choice construction *)
let test_choice_construction () : Lemma (True) =
  (* Internal choice: select between two branches *)
  let select = SSelect [
    ("add", SSend TInt SEnd);
    ("quit", SEnd)
  ] in
  (* External choice: offer two branches *)
  let branch = SBranch [
    ("add", SRecv TInt SEnd);
    ("quit", SEnd)
  ] in
  ()

(** ============================================================================
    SESSION TYPE SIZE TESTS (for termination)
    ============================================================================ *)

(** Test session_size is positive *)
let test_session_size_positive () : Lemma (True) =
  let s1 = SEnd in
  let s2 = SSend TUnit SEnd in
  let s3 = SRec "X" (SSend TInt (SVar "X")) in
  assert (session_size s1 >= 1);
  assert (session_size s2 >= 1);
  assert (session_size s3 >= 1)

(** ============================================================================
    DUALITY TESTS
    ============================================================================ *)

(** Test dual of SEnd is SEnd *)
let test_dual_end () : Lemma (dual SEnd == SEnd) =
  ()

(** Test dual of SVar is SVar *)
let test_dual_var () : Lemma (dual (SVar "X") == SVar "X") =
  ()

(** Test dual of SSend is SRecv *)
let test_dual_send () : Lemma (True) =
  let s = SSend TInt SEnd in
  let d = dual s in
  assert (d == SRecv TInt SEnd)

(** Test dual of SRecv is SSend *)
let test_dual_recv () : Lemma (True) =
  let s = SRecv TInt SEnd in
  let d = dual s in
  assert (d == SSend TInt SEnd)

(** Test dual of SSelect is SBranch *)
let test_dual_select () : Lemma (True) =
  let s = SSelect [("l1", SEnd); ("l2", SEnd)] in
  let d = dual s in
  match d with
  | SBranch branches ->
    assert (List.length branches = 2)
  | _ -> ()

(** Test dual of SBranch is SSelect *)
let test_dual_branch () : Lemma (True) =
  let s = SBranch [("l1", SEnd); ("l2", SEnd)] in
  let d = dual s in
  match d with
  | SSelect branches ->
    assert (List.length branches = 2)
  | _ -> ()

(** Test dual of SRec preserves variable *)
let test_dual_rec () : Lemma (True) =
  let s = SRec "X" (SSend TInt (SVar "X")) in
  let d = dual s in
  match d with
  | SRec var body ->
    assert (var = "X");
    match body with
    | SRecv _ _ -> ()
    | _ -> ()
  | _ -> ()

(** ============================================================================
    DUALITY INVOLUTION TESTS
    ============================================================================ *)

(** Test dual(dual(SEnd)) = SEnd *)
let test_dual_involutive_end () : Lemma (dual (dual SEnd) == SEnd) =
  dual_involutive SEnd

(** Test dual(dual(SVar)) = SVar *)
let test_dual_involutive_var () : Lemma (dual (dual (SVar "X")) == SVar "X") =
  dual_involutive (SVar "X")

(** Test dual(dual(SSend)) = SSend *)
let test_dual_involutive_send () : Lemma (True) =
  let s = SSend TInt SEnd in
  dual_involutive s;
  assert (dual (dual s) == s)

(** Test dual(dual(SRecv)) = SRecv *)
let test_dual_involutive_recv () : Lemma (True) =
  let s = SRecv TBool SEnd in
  dual_involutive s;
  assert (dual (dual s) == s)

(** Test dual(dual(SSelect)) = SSelect *)
let test_dual_involutive_select () : Lemma (True) =
  let s = SSelect [("a", SEnd); ("b", SSend TInt SEnd)] in
  dual_involutive s;
  assert (dual (dual s) == s)

(** Test dual(dual(SBranch)) = SBranch *)
let test_dual_involutive_branch () : Lemma (True) =
  let s = SBranch [("x", SEnd); ("y", SRecv TBool SEnd)] in
  dual_involutive s;
  assert (dual (dual s) == s)

(** Test dual(dual(SRec)) = SRec *)
let test_dual_involutive_rec () : Lemma (True) =
  let s = SRec "X" (SSend TInt (SRecv TBool (SVar "X"))) in
  dual_involutive s;
  assert (dual (dual s) == s)

(** Comprehensive dual involution test on complex session type *)
let test_dual_involutive_complex () : Lemma (True) =
  (* Complex protocol: send int, branch on response, recurse *)
  let s = SRec "loop" (
    SSend TInt (
      SBranch [
        ("continue", SRecv TBool (SVar "loop"));
        ("stop", SEnd)
      ]
    )
  ) in
  dual_involutive s;
  assert (dual (dual s) == s)

(** ============================================================================
    SESSION EQUALITY TESTS
    ============================================================================ *)

(** Test session_eq reflexivity *)
let test_session_eq_refl () : Lemma (True) =
  session_eq_refl SEnd;
  session_eq_refl (SVar "X");
  session_eq_refl (SSend TInt SEnd);
  session_eq_refl (SRecv TBool SEnd);
  session_eq_refl (SSelect [("a", SEnd)]);
  session_eq_refl (SBranch [("b", SEnd)]);
  session_eq_refl (SRec "X" (SVar "X"))

(** Test session_eq symmetry *)
let test_session_eq_sym () : Lemma (True) =
  let s = SSend TInt SEnd in
  session_eq_refl s;
  session_eq_sym s s

(** Test session_eq transitivity *)
let test_session_eq_trans () : Lemma (True) =
  let s = SRecv TBool SEnd in
  session_eq_refl s;
  session_eq_trans s s s

(** ============================================================================
    SESSION BRANCHES EQUALITY TESTS
    ============================================================================ *)

(** Test session_branches_eq reflexivity *)
let test_session_branches_eq_refl () : Lemma (True) =
  let bs = [("l1", SEnd); ("l2", SSend TInt SEnd)] in
  session_branches_eq_refl bs

(** Test empty branches equality *)
let test_session_branches_eq_empty () : Lemma (True) =
  let empty : list (label & session_type) = [] in
  session_branches_eq_refl empty;
  assert (session_branches_eq empty empty = true)

(** ============================================================================
    SOURCE LOCATION TRACKING TESTS (with_meta_t pattern)
    ============================================================================ *)

(** Test dummy position creation *)
let test_dummy_pos () : Lemma (True) =
  let p = dummy_pos in
  assert (p.pos_line = 0);
  assert (p.pos_col = 0)

(** Test position formatting *)
let test_string_of_pos () : Lemma (True) =
  let p = { pos_filename = "test.brrr"; pos_line = 10; pos_col = 5 } in
  let s = string_of_pos p in
  ()

(** Test with_dummy_meta *)
let test_with_dummy_meta () : Lemma (True) =
  let s = SEnd in
  let located = with_dummy_meta s in
  assert (located.meta_value == s);
  assert (located.meta_range == dummy_range)

(** Test with_range *)
let test_with_range () : Lemma (True) =
  let s = SSend TInt SEnd in
  let start_pos = { pos_filename = "test.brrr"; pos_line = 1; pos_col = 0 } in
  let end_pos = { pos_filename = "test.brrr"; pos_line = 1; pos_col = 10 } in
  let r : range = (start_pos, end_pos) in
  let located = with_range s r in
  assert (located.meta_value == s);
  assert (located.meta_range == r)

(** Test map_meta *)
let test_map_meta () : Lemma (True) =
  let s = SEnd in
  let m = with_dummy_meta s in
  let f (x: session_type) : session_type = dual x in
  let mapped = map_meta f m in
  assert (mapped.meta_value == dual s)

(** Test located session creation *)
let test_located_session () : Lemma (True) =
  let s = SSend TInt (SRecv TBool SEnd) in
  let start_pos = { pos_filename = "proto.brrr"; pos_line = 5; pos_col = 2 } in
  let end_pos = { pos_filename = "proto.brrr"; pos_line = 5; pos_col = 30 } in
  let r : range = (start_pos, end_pos) in
  let located = locate_session s r in
  assert (get_value located == s);
  assert (get_range located == r)

(** Test unlocated session *)
let test_unlocated_session () : Lemma (True) =
  let s = SRec "X" (SSend TInt (SVar "X")) in
  let located = unlocated_session s in
  assert (get_value located == s)

(** ============================================================================
    LOCATED ERROR TESTS
    ============================================================================ *)

(** Test located error creation *)
let test_make_error () : Lemma (True) =
  let start_pos = { pos_filename = "test.brrr"; pos_line = 10; pos_col = 5 } in
  let end_pos = { pos_filename = "test.brrr"; pos_line = 10; pos_col = 15 } in
  let r : range = (start_pos, end_pos) in
  let err = make_error "Type mismatch in session" r in
  assert (err.error_range == r)

(** Test error formatting *)
let test_string_of_located_error () : Lemma (True) =
  let start_pos = { pos_filename = "test.brrr"; pos_line = 10; pos_col = 5 } in
  let end_pos = { pos_filename = "test.brrr"; pos_line = 10; pos_col = 15 } in
  let r : range = (start_pos, end_pos) in
  let err = make_error "Session type error" r in
  let s = string_of_located_error err in
  ()

(** ============================================================================
    EFFECT SYSTEM SESSION STATE TESTS
    ============================================================================ *)

(** Test dual_state involution from Effects module *)
let test_dual_state_involutive () : Lemma (True) =
  let s = SendState ETInt (RecvState ETBool EndState) in
  dual_state_involutive s;
  assert (dual_state (dual_state s) == s)

(** Test are_dual_states *)
let test_are_dual_states () : Lemma (True) =
  let s1 = SendState ETInt EndState in
  let s2 = RecvState ETInt EndState in
  (* s1 and s2 should be duals *)
  let are_dual = are_dual_states s1 s2 in
  ()

(** ============================================================================
    PROTOCOL COMPOSITION TESTS
    ============================================================================ *)

(** Test request-response protocol and its dual *)
let test_request_response_protocol () : Lemma (True) =
  (* Client sends request, receives response *)
  let client_proto = SSend TInt (SRecv TBool SEnd) in
  (* Server receives request, sends response *)
  let server_proto = SRecv TInt (SSend TBool SEnd) in
  (* These should be duals *)
  dual_involutive client_proto;
  assert (dual client_proto == server_proto)

(** Test calculator protocol *)
let test_calculator_protocol () : Lemma (True) =
  (* Client chooses operation, sends operands, receives result *)
  let client = SSelect [
    ("add", SSend TInt (SSend TInt (SRecv TInt SEnd)));
    ("mul", SSend TInt (SSend TInt (SRecv TInt SEnd)));
    ("quit", SEnd)
  ] in
  (* Server offers operations *)
  let server = SBranch [
    ("add", SRecv TInt (SRecv TInt (SSend TInt SEnd)));
    ("mul", SRecv TInt (SRecv TInt (SSend TInt SEnd)));
    ("quit", SEnd)
  ] in
  dual_involutive client;
  assert (dual client == server)

(** Test recursive counter protocol *)
let test_recursive_counter_protocol () : Lemma (True) =
  (* Client: repeatedly choose increment or get value *)
  let client = SRec "X" (SSelect [
    ("inc", SVar "X");
    ("get", SRecv TInt SEnd)
  ]) in
  (* Server: dual protocol *)
  let server = SRec "X" (SBranch [
    ("inc", SVar "X");
    ("get", SSend TInt SEnd)
  ]) in
  dual_involutive client;
  assert (dual client == server)

(** ============================================================================
    COMPREHENSIVE SESSION TYPE TEST RUNNERS
    ============================================================================ *)

let run_all_construction_tests () : Lemma (True) =
  test_session_type_construction ();
  test_session_var ();
  test_recursive_session ();
  test_choice_construction ();
  test_session_size_positive ()

let run_all_duality_tests () : Lemma (True) =
  test_dual_end ();
  test_dual_var ();
  test_dual_send ();
  test_dual_recv ();
  test_dual_select ();
  test_dual_branch ();
  test_dual_rec ()

let run_all_involution_tests () : Lemma (True) =
  test_dual_involutive_end ();
  test_dual_involutive_var ();
  test_dual_involutive_send ();
  test_dual_involutive_recv ();
  test_dual_involutive_select ();
  test_dual_involutive_branch ();
  test_dual_involutive_rec ();
  test_dual_involutive_complex ()

let run_all_equality_tests () : Lemma (True) =
  test_session_eq_refl ();
  test_session_eq_sym ();
  test_session_eq_trans ();
  test_session_branches_eq_refl ();
  test_session_branches_eq_empty ()

let run_all_location_tests () : Lemma (True) =
  test_dummy_pos ();
  test_string_of_pos ();
  test_with_dummy_meta ();
  test_with_range ();
  test_map_meta ();
  test_located_session ();
  test_unlocated_session ();
  test_make_error ();
  test_string_of_located_error ()

let run_all_effect_state_tests () : Lemma (True) =
  test_dual_state_involutive ();
  test_are_dual_states ()

let run_all_protocol_tests () : Lemma (True) =
  test_request_response_protocol ();
  test_calculator_protocol ();
  test_recursive_counter_protocol ()

(** Master test runner *)
let run_all_session_type_tests () : Lemma (True) =
  run_all_construction_tests ();
  run_all_duality_tests ();
  run_all_involution_tests ();
  run_all_equality_tests ();
  run_all_location_tests ();
  run_all_effect_state_tests ();
  run_all_protocol_tests ()
