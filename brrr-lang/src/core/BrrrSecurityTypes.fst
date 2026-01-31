(**
 * =============================================================================
 * BrrrLang.Core.SecurityTypes - Implementation
 * =============================================================================
 *
 * Implementation of the Unified Security Type System for Brrr-Lang IR.
 * Integrates taint tracking and information flow with the core type system.
 *
 * This file implements all val declarations from BrrrSecurityTypes.fsti.
 * Types are declared in the interface; this file provides implementations.
 *
 * =============================================================================
 * THEORETICAL FOUNDATION
 * =============================================================================
 *
 * Based on foundational work in information flow security:
 *
 *   [1] Denning, D.E. (1976). "A Lattice Model of Secure Information Flow."
 *       Communications of the ACM, 19(5):236-243.
 *
 *   [2] Denning, D.E. and Denning, P.J. (1977). "Certification of Programs
 *       for Secure Information Flow." Communications of the ACM, 20(7):504-513.
 *
 *   [3] Myers, A.C. (1999). "JFlow: Practical Mostly-Static Information
 *       Flow Control." POPL 1999.
 *
 *   [4] Livshits, V.B. and Lam, M.S. (2005). "Finding Security Vulnerabilities
 *       in Java Applications with Static Analysis." USENIX Security 2005.
 *
 * For specification details, see:
 *   - brrr_lang_spec_v0.4.tex, Part IX (Information Flow)
 *   - SPECIFICATION_ERRATA.md for known corrections
 *
 * =============================================================================
 * IMPLEMENTATION NOTES
 * =============================================================================
 *
 * Types (taint_kind, confidentiality, integrity, sec_label, etc.) are
 * declared in BrrrSecurityTypes.fsti. This file provides only implementations
 * for the val declarations in the interface.
 *
 * The product lattice structure is:
 *   sec_label = Confidentiality x Integrity x TaintSet
 *
 * Where:
 *   - Confidentiality: CPublic < CSecret
 *   - Integrity: ITrusted < IUntrusted (inverted for taint propagation)
 *   - TaintSet: subset ordering (lattice under set union/intersection)
 *
 * =============================================================================
 *)
module BrrrSecurityTypes

open FStar.List.Tot
open FStar.Classical
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes

(** Z3 solver options - tuned for finite lattice case analysis.
    Must match settings in interface. *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


(** ****************************************************************************
    SECTION 1: TAINT KIND OPERATIONS
    **************************************************************************** *)

(**
 * Decidable equality for taint kinds.
 * Direct case analysis on all 13x13 combinations.
 * TkCustom comparison is string-based.
 *)
let taint_kind_eq (k1 k2: taint_kind) : bool =
  match k1, k2 with
  | TkSQLi, TkSQLi -> true
  | TkXSS, TkXSS -> true
  | TkCMDi, TkCMDi -> true
  | TkPathTraversal, TkPathTraversal -> true
  | TkSSRF, TkSSRF -> true
  | TkLDAPi, TkLDAPi -> true
  | TkXMLi, TkXMLi -> true
  | TkHeaderi, TkHeaderi -> true
  | TkLogi, TkLogi -> true
  | TkTemplatei, TkTemplatei -> true
  | TkDeserial, TkDeserial -> true
  | TkRedirect, TkRedirect -> true
  | TkCustom s1, TkCustom s2 -> s1 = s2
  | _, _ -> false


(** ****************************************************************************
    SECTION 2: SECURITY LABEL CONSTRUCTORS
    **************************************************************************** *)

(**
 * Bottom element: Public, trusted, no taints.
 * Data can flow to ANY other label.
 *)
let sec_public_trusted : sec_label = {
  confidentiality = CPublic;
  integrity = ITrusted;
  taints = [];
}

(** Secret but trusted: Confidential but clean data. *)
let sec_secret_trusted : sec_label = {
  confidentiality = CSecret;
  integrity = ITrusted;
  taints = [];
}

(**
 * Public but tainted: Non-confidential but untrusted data.
 * @param ks  The set of taint kinds this data carries.
 *)
let sec_public_untrusted (ks: taint_set) : sec_label = {
  confidentiality = CPublic;
  integrity = IUntrusted;
  taints = ks;
}

(** Create label tainted with a single kind. *)
let sec_tainted (k: taint_kind) : sec_label = {
  confidentiality = CPublic;
  integrity = IUntrusted;
  taints = [k];
}

(** Lattice BOTTOM element (most permissive). *)
let sec_bot : sec_label = sec_public_trusted

(**
 * Lattice TOP element (most restrictive).
 * Secret + untrusted + common vulnerability taints.
 *)
let sec_top : sec_label = {
  confidentiality = CSecret;
  integrity = IUntrusted;
  taints = [TkSQLi; TkXSS; TkCMDi; TkPathTraversal; TkSSRF];
}


(** ****************************************************************************
    SECTION 3: SECURITY LABEL ORDERING
    ****************************************************************************

    The ordering l1 <= l2 defines when data can flow from l1 to l2.
    This is a PRODUCT ORDER on all three components.
    **************************************************************************** *)

(**
 * Confidentiality ordering: CPublic < CSecret.
 * Public data can flow to secret, not vice versa (no leaks).
 *)
let conf_leq (c1 c2: confidentiality) : bool =
  match c1, c2 with
  | CPublic, _ -> true          (* CPublic is bottom *)
  | CSecret, CSecret -> true    (* reflexive *)
  | CSecret, CPublic -> false   (* cannot declassify! *)

(**
 * Integrity ordering: ITrusted < IUntrusted (for taint flow).
 * Trusted can become tainted, tainted cannot become trusted without endorsement.
 *)
let integ_leq (i1 i2: integrity) : bool =
  match i1, i2 with
  | ITrusted, _ -> true             (* ITrusted is bottom *)
  | IUntrusted, IUntrusted -> true  (* reflexive *)
  | IUntrusted, ITrusted -> false   (* cannot endorse implicitly! *)

(**
 * Check if a taint kind is in a taint set.
 * Uses taint_kind_eq for element comparison.
 *)
let rec taint_in_set (k: taint_kind) (ks: taint_set) : bool =
  match ks with
  | [] -> false
  | k' :: rest -> taint_kind_eq k k' || taint_in_set k rest

(**
 * Check if one taint set is a subset of another.
 * ks1 subset ks2 iff every element of ks1 is in ks2.
 *)
let rec taint_set_subset (ks1 ks2: taint_set) : bool =
  match ks1 with
  | [] -> true
  | k :: rest -> taint_in_set k ks2 && taint_set_subset rest ks2

(**
 * Security label ordering (product order).
 * l1 <= l2 iff all components satisfy their orderings.
 * This is the FUNDAMENTAL flow check.
 *)
let sec_label_leq (l1 l2: sec_label) : bool =
  conf_leq l1.confidentiality l2.confidentiality &&
  integ_leq l1.integrity l2.integrity &&
  taint_set_subset l1.taints l2.taints


(** ****************************************************************************
    SECTION 4: LATTICE OPERATIONS (JOIN/MEET)
    **************************************************************************** *)

(** Confidentiality join: Returns the MORE restrictive level. *)
let conf_join (c1 c2: confidentiality) : confidentiality =
  match c1, c2 with
  | CSecret, _ | _, CSecret -> CSecret
  | CPublic, CPublic -> CPublic

(** Confidentiality meet: Returns the LESS restrictive level. *)
let conf_meet (c1 c2: confidentiality) : confidentiality =
  match c1, c2 with
  | CPublic, _ | _, CPublic -> CPublic
  | CSecret, CSecret -> CSecret

(**
 * Integrity join: Returns the LESS trusted level (taint propagates).
 * This is KEY for taint propagation: any untrusted input taints the result.
 *)
let integ_join (i1 i2: integrity) : integrity =
  match i1, i2 with
  | IUntrusted, _ | _, IUntrusted -> IUntrusted
  | ITrusted, ITrusted -> ITrusted

(** Integrity meet: Returns the MORE trusted level. *)
let integ_meet (i1 i2: integrity) : integrity =
  match i1, i2 with
  | ITrusted, _ | _, ITrusted -> ITrusted
  | IUntrusted, IUntrusted -> IUntrusted

(**
 * Taint set union (join operation).
 * Combines all taints from both sets, maintaining uniqueness.
 *)
let rec taint_set_union (ks1 ks2: taint_set) : taint_set =
  match ks1 with
  | [] -> ks2
  | k :: rest ->
      if taint_in_set k ks2 then taint_set_union rest ks2
      else k :: taint_set_union rest ks2

(** Taint set intersection (meet operation). *)
let rec taint_set_intersect (ks1 ks2: taint_set) : taint_set =
  match ks1 with
  | [] -> []
  | k :: rest ->
      if taint_in_set k ks2 then k :: taint_set_intersect rest ks2
      else taint_set_intersect rest ks2

(**
 * Security label join (least upper bound).
 * This is the KEY operation for taint propagation in expressions.
 *)
let sec_label_join (l1 l2: sec_label) : sec_label = {
  confidentiality = conf_join l1.confidentiality l2.confidentiality;
  integrity = integ_join l1.integrity l2.integrity;
  taints = taint_set_union l1.taints l2.taints;
}

(** Security label meet (greatest lower bound). *)
let sec_label_meet (l1 l2: sec_label) : sec_label = {
  confidentiality = conf_meet l1.confidentiality l2.confidentiality;
  integrity = integ_meet l1.integrity l2.integrity;
  taints = taint_set_intersect l1.taints l2.taints;
}


(** ****************************************************************************
    SECTION 5: REFLEXIVITY LEMMAS
    ****************************************************************************

    Prove that all ordering relations are reflexive: x <= x.
    SMTPat triggers enable automatic instantiation by Z3.
    **************************************************************************** *)

let taint_kind_eq_refl (k: taint_kind)
    : Lemma (ensures taint_kind_eq k k = true)
            [SMTPat (taint_kind_eq k k)] =
  match k with
  | TkSQLi -> () | TkXSS -> () | TkCMDi -> () | TkPathTraversal -> ()
  | TkSSRF -> () | TkLDAPi -> () | TkXMLi -> () | TkHeaderi -> ()
  | TkLogi -> () | TkTemplatei -> () | TkDeserial -> () | TkRedirect -> ()
  | TkCustom _ -> ()

let conf_leq_refl (c: confidentiality)
    : Lemma (ensures conf_leq c c = true)
            [SMTPat (conf_leq c c)] =
  match c with CPublic -> () | CSecret -> ()

let integ_leq_refl (i: integrity)
    : Lemma (ensures integ_leq i i = true)
            [SMTPat (integ_leq i i)] =
  match i with ITrusted -> () | IUntrusted -> ()

let taint_in_set_head (k: taint_kind) (rest: taint_set)
    : Lemma (ensures taint_in_set k (k :: rest) = true)
            [SMTPat (taint_in_set k (k :: rest))] =
  taint_kind_eq_refl k

let rec taint_set_subset_refl (ks: taint_set)
    : Lemma (ensures taint_set_subset ks ks = true)
            (decreases ks)
            [SMTPat (taint_set_subset ks ks)] =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_in_set_head k rest;
      taint_set_subset_refl rest

let sec_label_leq_refl (l: sec_label)
    : Lemma (ensures sec_label_leq l l = true)
            [SMTPat (sec_label_leq l l)] =
  conf_leq_refl l.confidentiality;
  integ_leq_refl l.integrity;
  taint_set_subset_refl l.taints


(** ****************************************************************************
    SECTION 6: TRANSITIVITY LEMMAS
    ****************************************************************************

    Prove that all ordering relations are transitive:
    x <= y /\ y <= z ==> x <= z
    **************************************************************************** *)

let conf_leq_trans (c1 c2 c3: confidentiality)
    : Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c3 = true)
            (ensures conf_leq c1 c3 = true) =
  match c1, c2, c3 with
  | CPublic, _, _ -> ()
  | CSecret, CSecret, CSecret -> ()
  | _, _, _ -> ()

let integ_leq_trans (i1 i2 i3: integrity)
    : Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i3 = true)
            (ensures integ_leq i1 i3 = true) =
  match i1, i2, i3 with
  | ITrusted, _, _ -> ()
  | IUntrusted, IUntrusted, IUntrusted -> ()
  | _, _, _ -> ()

#push-options "--fuel 1 --ifuel 1"
let rec taint_in_set_trans (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (requires taint_in_set k ks1 = true /\ taint_set_subset ks1 ks2 = true)
            (ensures taint_in_set k ks2 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then ()
      else taint_in_set_trans k rest ks2

let rec taint_set_subset_trans (ks1 ks2 ks3: taint_set)
    : Lemma (requires taint_set_subset ks1 ks2 = true /\ taint_set_subset ks2 ks3 = true)
            (ensures taint_set_subset ks1 ks3 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      taint_in_set_trans k ks2 ks3;
      taint_set_subset_trans rest ks2 ks3
#pop-options

let sec_label_leq_trans (l1 l2 l3: sec_label)
    : Lemma (requires sec_label_leq l1 l2 = true /\ sec_label_leq l2 l3 = true)
            (ensures sec_label_leq l1 l3 = true) =
  conf_leq_trans l1.confidentiality l2.confidentiality l3.confidentiality;
  integ_leq_trans l1.integrity l2.integrity l3.integrity;
  taint_set_subset_trans l1.taints l2.taints l3.taints


(** ****************************************************************************
    SECTION 7: ANTISYMMETRY LEMMAS
    **************************************************************************** *)

let conf_leq_antisym (c1 c2: confidentiality)
    : Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c1 = true)
            (ensures c1 = c2) =
  match c1, c2 with
  | CPublic, CPublic -> ()
  | CSecret, CSecret -> ()
  | _, _ -> ()

let integ_leq_antisym (i1 i2: integrity)
    : Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i1 = true)
            (ensures i1 = i2) =
  match i1, i2 with
  | ITrusted, ITrusted -> ()
  | IUntrusted, IUntrusted -> ()
  | _, _ -> ()


(** ****************************************************************************
    SECTION 8: HELPER LEMMAS FOR TAINT SET OPERATIONS
    **************************************************************************** *)

#push-options "--fuel 1 --ifuel 1"
let rec taint_set_union_includes_left (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (requires taint_in_set k ks1 = true)
            (ensures taint_in_set k (taint_set_union ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then
        if taint_in_set k' ks2 then taint_set_union_includes_left k rest ks2
        else taint_kind_eq_refl k
      else taint_set_union_includes_left k rest ks2

let rec taint_set_union_includes_right (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (requires taint_in_set k ks2 = true)
            (ensures taint_in_set k (taint_set_union ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_in_set k' ks2 then taint_set_union_includes_right k rest ks2
      else taint_set_union_includes_right k rest ks2

let rec taint_set_union_subset (ks1 ks2 ks3: taint_set)
    : Lemma (requires taint_set_subset ks1 ks3 = true /\ taint_set_subset ks2 ks3 = true)
            (ensures taint_set_subset (taint_set_union ks1 ks2) ks3 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      if taint_in_set k ks2 then taint_set_union_subset rest ks2 ks3
      else taint_set_union_subset rest ks2 ks3

let rec taint_set_intersect_subset_left (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_subset (taint_set_intersect ks1 ks2) ks1 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      taint_set_intersect_subset_left rest ks2;
      if taint_in_set k ks2 then taint_kind_eq_refl k
      else ()

let rec taint_set_intersect_subset_right (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_subset (taint_set_intersect ks1 ks2) ks2 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      taint_set_intersect_subset_right rest ks2;
      if taint_in_set k ks2 then ()
      else ()
#pop-options


(** ****************************************************************************
    SECTION 9: JOIN / MEET UPPER BOUND AND LOWER BOUND LEMMAS
    **************************************************************************** *)

let conf_join_upper_l (c1 c2: confidentiality)
    : Lemma (ensures conf_leq c1 (conf_join c1 c2) = true) =
  match c1, c2 with CPublic, _ -> () | CSecret, _ -> ()

let conf_join_upper_r (c1 c2: confidentiality)
    : Lemma (ensures conf_leq c2 (conf_join c1 c2) = true) =
  match c1, c2 with _, CPublic -> () | _, CSecret -> ()

let integ_join_upper_l (i1 i2: integrity)
    : Lemma (ensures integ_leq i1 (integ_join i1 i2) = true) =
  match i1, i2 with ITrusted, _ -> () | IUntrusted, _ -> ()

let integ_join_upper_r (i1 i2: integrity)
    : Lemma (ensures integ_leq i2 (integ_join i1 i2) = true) =
  match i1, i2 with _, ITrusted -> () | _, IUntrusted -> ()

let conf_meet_lower_l (c1 c2: confidentiality)
    : Lemma (ensures conf_leq (conf_meet c1 c2) c1 = true) =
  match c1, c2 with CPublic, _ -> () | CSecret, _ -> ()

let conf_meet_lower_r (c1 c2: confidentiality)
    : Lemma (ensures conf_leq (conf_meet c1 c2) c2 = true) =
  match c1, c2 with _, CPublic -> () | _, CSecret -> ()

let integ_meet_lower_l (i1 i2: integrity)
    : Lemma (ensures integ_leq (integ_meet i1 i2) i1 = true) =
  match i1, i2 with ITrusted, _ -> () | IUntrusted, _ -> ()

let integ_meet_lower_r (i1 i2: integrity)
    : Lemma (ensures integ_leq (integ_meet i1 i2) i2 = true) =
  match i1, i2 with _, ITrusted -> () | _, IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
let sec_label_join_upper_l (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq l1 (sec_label_join l1 l2) = true)
            [SMTPat (sec_label_join l1 l2)] =
  conf_join_upper_l l1.confidentiality l2.confidentiality;
  integ_join_upper_l l1.integrity l2.integrity;
  let rec aux (ks1 ks2: taint_set)
      : Lemma (ensures taint_set_subset ks1 (taint_set_union ks1 ks2) = true)
              (decreases ks1) =
    match ks1 with
    | [] -> ()
    | k :: rest ->
        taint_kind_eq_refl k;
        taint_set_union_includes_left k ks1 ks2;
        aux rest ks2
  in
  aux l1.taints l2.taints

let sec_label_join_upper_r (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq l2 (sec_label_join l1 l2) = true) =
  conf_join_upper_r l1.confidentiality l2.confidentiality;
  integ_join_upper_r l1.integrity l2.integrity;
  let rec aux (ks1 ks2: taint_set)
      : Lemma (ensures taint_set_subset ks2 (taint_set_union ks1 ks2) = true)
              (decreases ks1) =
    match ks1 with
    | [] -> taint_set_subset_refl ks2
    | k :: rest ->
        if taint_in_set k ks2 then aux rest ks2
        else aux rest ks2
  in
  aux l1.taints l2.taints
#pop-options

let sec_label_join_lub (l1 l2 u: sec_label)
    : Lemma (requires sec_label_leq l1 u = true /\ sec_label_leq l2 u = true)
            (ensures sec_label_leq (sec_label_join l1 l2) u = true) =
  let conf_lub (c1 c2 cu: confidentiality)
      : Lemma (requires conf_leq c1 cu = true /\ conf_leq c2 cu = true)
              (ensures conf_leq (conf_join c1 c2) cu = true) =
    match c1, c2, cu with
    | _, _, CSecret -> ()
    | CPublic, CPublic, CPublic -> ()
    | _, _, _ -> ()
  in
  let integ_lub (i1 i2 iu: integrity)
      : Lemma (requires integ_leq i1 iu = true /\ integ_leq i2 iu = true)
              (ensures integ_leq (integ_join i1 i2) iu = true) =
    match i1, i2, iu with
    | _, _, IUntrusted -> ()
    | ITrusted, ITrusted, ITrusted -> ()
    | _, _, _ -> ()
  in
  conf_lub l1.confidentiality l2.confidentiality u.confidentiality;
  integ_lub l1.integrity l2.integrity u.integrity;
  taint_set_union_subset l1.taints l2.taints u.taints

let sec_label_meet_lower_l (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l1 = true)
            [SMTPat (sec_label_meet l1 l2)] =
  conf_meet_lower_l l1.confidentiality l2.confidentiality;
  integ_meet_lower_l l1.integrity l2.integrity;
  taint_set_intersect_subset_left l1.taints l2.taints

let sec_label_meet_lower_r (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l2 = true) =
  conf_meet_lower_r l1.confidentiality l2.confidentiality;
  integ_meet_lower_r l1.integrity l2.integrity;
  taint_set_intersect_subset_right l1.taints l2.taints

#push-options "--fuel 1 --ifuel 1"
let sec_label_meet_glb (l1 l2 lb: sec_label)
    : Lemma (requires sec_label_leq lb l1 = true /\ sec_label_leq lb l2 = true)
            (ensures sec_label_leq lb (sec_label_meet l1 l2) = true) =
  let conf_glb (c1 c2 clb: confidentiality)
      : Lemma (requires conf_leq clb c1 = true /\ conf_leq clb c2 = true)
              (ensures conf_leq clb (conf_meet c1 c2) = true) =
    match clb, c1, c2 with
    | CPublic, _, _ -> ()
    | CSecret, CSecret, CSecret -> ()
    | _, _, _ -> ()
  in
  let integ_glb (i1 i2 ilb: integrity)
      : Lemma (requires integ_leq ilb i1 = true /\ integ_leq ilb i2 = true)
              (ensures integ_leq ilb (integ_meet i1 i2) = true) =
    match ilb, i1, i2 with
    | ITrusted, _, _ -> ()
    | IUntrusted, IUntrusted, IUntrusted -> ()
    | _, _, _ -> ()
  in
  let rec taints_glb (ks1 ks2 kslb: taint_set)
      : Lemma (requires taint_set_subset kslb ks1 = true /\ taint_set_subset kslb ks2 = true)
              (ensures taint_set_subset kslb (taint_set_intersect ks1 ks2) = true)
              (decreases kslb) =
    match kslb with
    | [] -> ()
    | k :: rest -> taints_glb ks1 ks2 rest
  in
  conf_glb l1.confidentiality l2.confidentiality lb.confidentiality;
  integ_glb l1.integrity l2.integrity lb.integrity;
  taints_glb l1.taints l2.taints lb.taints
#pop-options


(** ****************************************************************************
    SECTION 10: COMMUTATIVITY AND IDEMPOTENCE LEMMAS
    **************************************************************************** *)

let conf_join_comm (c1 c2: confidentiality)
    : Lemma (ensures conf_join c1 c2 = conf_join c2 c1) =
  match c1, c2 with
  | CPublic, CPublic | CPublic, CSecret | CSecret, CPublic | CSecret, CSecret -> ()

let integ_join_comm (i1 i2: integrity)
    : Lemma (ensures integ_join i1 i2 = integ_join i2 i1) =
  match i1, i2 with
  | ITrusted, ITrusted | ITrusted, IUntrusted | IUntrusted, ITrusted | IUntrusted, IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec taint_set_union_membership (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (ensures taint_in_set k (taint_set_union ks1 ks2) =
                     (taint_in_set k ks1 || taint_in_set k ks2))
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      taint_set_union_membership k rest ks2;
      if taint_kind_eq k k' then taint_kind_eq_refl k
      else ()

let rec taint_set_union_equiv_comm (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_subset (taint_set_union ks1 ks2) (taint_set_union ks2 ks1) = true /\
                     taint_set_subset (taint_set_union ks2 ks1) (taint_set_union ks1 ks2) = true)
            (decreases %[List.Tot.length ks1 + List.Tot.length ks2]) =
  let u12 = taint_set_union ks1 ks2 in
  let u21 = taint_set_union ks2 ks1 in
  let rec aux1 (acc: taint_set)
      : Lemma (requires taint_set_subset acc u12 = true)
              (ensures taint_set_subset acc u21 = true)
              (decreases acc) =
    match acc with
    | [] -> ()
    | k :: rest ->
        taint_set_union_membership k ks1 ks2;
        taint_set_union_membership k ks2 ks1;
        aux1 rest
  in
  let rec aux2 (acc: taint_set)
      : Lemma (requires taint_set_subset acc u21 = true)
              (ensures taint_set_subset acc u12 = true)
              (decreases acc) =
    match acc with
    | [] -> ()
    | k :: rest ->
        taint_set_union_membership k ks2 ks1;
        taint_set_union_membership k ks1 ks2;
        aux2 rest
  in
  taint_set_subset_refl u12;
  aux1 u12;
  taint_set_subset_refl u21;
  aux2 u21
#pop-options

let sec_label_join_comm_equiv (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_join l1 l2) (sec_label_join l2 l1) = true /\
                     sec_label_leq (sec_label_join l2 l1) (sec_label_join l1 l2) = true) =
  conf_join_comm l1.confidentiality l2.confidentiality;
  integ_join_comm l1.integrity l2.integrity;
  taint_set_union_equiv_comm l1.taints l2.taints

let conf_join_idem (c: confidentiality)
    : Lemma (ensures conf_join c c = c) =
  match c with CPublic -> () | CSecret -> ()

let integ_join_idem (i: integrity)
    : Lemma (ensures integ_join i i = i) =
  match i with ITrusted -> () | IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
let rec taint_set_union_idem (ks: taint_set)
    : Lemma (ensures taint_set_union ks ks == ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_eq_refl k;
      taint_set_union_idem rest
#pop-options

let sec_label_join_idem (l: sec_label)
    : Lemma (ensures sec_label_join l l == l) =
  conf_join_idem l.confidentiality;
  integ_join_idem l.integrity;
  taint_set_union_idem l.taints

let conf_meet_comm (c1 c2: confidentiality)
    : Lemma (ensures conf_meet c1 c2 = conf_meet c2 c1) =
  match c1, c2 with
  | CPublic, CPublic | CPublic, CSecret | CSecret, CPublic | CSecret, CSecret -> ()

let integ_meet_comm (i1 i2: integrity)
    : Lemma (ensures integ_meet i1 i2 = integ_meet i2 i1) =
  match i1, i2 with
  | ITrusted, ITrusted | ITrusted, IUntrusted | IUntrusted, ITrusted | IUntrusted, IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
let rec taint_set_intersect_equiv_comm (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_subset (taint_set_intersect ks1 ks2) (taint_set_intersect ks2 ks1) = true /\
                     taint_set_subset (taint_set_intersect ks2 ks1) (taint_set_intersect ks1 ks2) = true)
            (decreases %[List.Tot.length ks1 + List.Tot.length ks2]) =
  let i12 = taint_set_intersect ks1 ks2 in
  let i21 = taint_set_intersect ks2 ks1 in
  let rec intersect_membership (k: taint_kind) (a b: taint_set)
      : Lemma (ensures taint_in_set k (taint_set_intersect a b) =
                       (taint_in_set k a && taint_in_set k b))
              (decreases a) =
    match a with
    | [] -> ()
    | k' :: rest ->
        intersect_membership k rest b;
        if taint_kind_eq k k' then taint_kind_eq_refl k
        else ()
  in
  let rec aux1 (acc: taint_set)
      : Lemma (requires taint_set_subset acc i12 = true)
              (ensures taint_set_subset acc i21 = true)
              (decreases acc) =
    match acc with
    | [] -> ()
    | k :: rest ->
        intersect_membership k ks1 ks2;
        intersect_membership k ks2 ks1;
        aux1 rest
  in
  let rec aux2 (acc: taint_set)
      : Lemma (requires taint_set_subset acc i21 = true)
              (ensures taint_set_subset acc i12 = true)
              (decreases acc) =
    match acc with
    | [] -> ()
    | k :: rest ->
        intersect_membership k ks2 ks1;
        intersect_membership k ks1 ks2;
        aux2 rest
  in
  taint_set_subset_refl i12;
  aux1 i12;
  taint_set_subset_refl i21;
  aux2 i21
#pop-options

let sec_label_meet_comm_equiv (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) (sec_label_meet l2 l1) = true /\
                     sec_label_leq (sec_label_meet l2 l1) (sec_label_meet l1 l2) = true) =
  conf_meet_comm l1.confidentiality l2.confidentiality;
  integ_meet_comm l1.integrity l2.integrity;
  taint_set_intersect_equiv_comm l1.taints l2.taints

let conf_meet_idem (c: confidentiality)
    : Lemma (ensures conf_meet c c = c) =
  match c with CPublic -> () | CSecret -> ()

let integ_meet_idem (i: integrity)
    : Lemma (ensures integ_meet i i = i) =
  match i with ITrusted -> () | IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
let rec taint_set_intersect_idem (ks: taint_set)
    : Lemma (ensures taint_set_intersect ks ks == ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_eq_refl k;
      taint_set_intersect_idem rest
#pop-options

let sec_label_meet_idem (l: sec_label)
    : Lemma (ensures sec_label_meet l l == l) =
  conf_meet_idem l.confidentiality;
  integ_meet_idem l.integrity;
  taint_set_intersect_idem l.taints


(** ****************************************************************************
    SECTION 11: SECURITY-TYPED TYPES
    **************************************************************************** *)

let mk_sec_type (t: brrr_type) (l: sec_label) : sec_type = {
  base = t;
  label = l;
}

let untainted_type (t: brrr_type) : sec_type = {
  base = t;
  label = sec_public_trusted;
}

let tainted_type (t: brrr_type) (k: taint_kind) : sec_type = {
  base = t;
  label = sec_tainted k;
}

let secret_type (t: brrr_type) : sec_type = {
  base = t;
  label = sec_secret_trusted;
}

let sec_type_subtype (st1 st2: sec_type) : bool =
  subtype st1.base st2.base && sec_label_leq st1.label st2.label

let sec_type_subtype_refl (st: sec_type)
    : Lemma (ensures sec_type_subtype st st = true)
            [SMTPat (sec_type_subtype st st)] =
  subtype_refl st.base;
  sec_label_leq_refl st.label


(** ****************************************************************************
    SECTION 12: PC LABEL AND FLOW CHECKING
    **************************************************************************** *)

let initial_pc : pc_label = sec_public_trusted

let raise_pc (pc: pc_label) (guard_label: sec_label) : pc_label =
  sec_label_join pc guard_label

let check_flow (pc: pc_label) (rhs: sec_label) (lhs: sec_label) : bool =
  sec_label_leq (sec_label_join pc rhs) lhs


(** ****************************************************************************
    SECTION 13: TAINT REMOVAL (SANITIZATION)
    **************************************************************************** *)

let rec remove_taint (k: taint_kind) (ks: taint_set) : taint_set =
  match ks with
  | [] -> []
  | k' :: rest ->
      if taint_kind_eq k k' then remove_taint k rest
      else k' :: remove_taint k rest

let rec remove_taints (to_remove: list taint_kind) (ks: taint_set) : taint_set =
  match to_remove with
  | [] -> ks
  | k :: rest -> remove_taints rest (remove_taint k ks)

let sanitize_label (to_remove: list taint_kind) (l: sec_label) : sec_label = {
  l with taints = remove_taints to_remove l.taints
}

let sanitize_sec_type (to_remove: list taint_kind) (st: sec_type) : sec_type = {
  st with label = sanitize_label to_remove st.label
}

let has_any_taint (ks: list taint_kind) (l: sec_label) : bool =
  List.Tot.existsb (fun k -> taint_in_set k l.taints) ks


(** ****************************************************************************
    SECTION 14: TAINT REMOVAL LEMMAS
    **************************************************************************** *)

let rec remove_taint_correct (k: taint_kind) (ks: taint_set)
    : Lemma (ensures taint_in_set k (remove_taint k ks) = false)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then remove_taint_correct k rest
      else remove_taint_correct k rest

let rec remove_taint_preserves (k k': taint_kind) (ks: taint_set)
    : Lemma (requires taint_kind_eq k k' = false)
            (ensures taint_in_set k' (remove_taint k ks) = taint_in_set k' ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k'' :: rest -> remove_taint_preserves k k' rest

let sanitize_enables_sink (to_remove: list taint_kind) (l: sec_label)
    : Lemma (ensures not (has_any_taint to_remove (sanitize_label to_remove l))) =
  ()


(** ****************************************************************************
    SECTION 15: I/O TAINT MAPPING
    **************************************************************************** *)

let io_source_taints (src: io_source) : taint_set =
  match src with
  | IOStdin -> [TkCMDi; TkSQLi; TkXSS; TkPathTraversal]
  | IOEnvVar _ -> [TkCMDi; TkPathTraversal]
  | IOFileInput _ -> [TkPathTraversal]
  | IONetworkIn -> [TkSSRF; TkSQLi; TkXSS; TkCMDi]
  | IOUserInput -> [TkCMDi; TkSQLi; TkXSS; TkPathTraversal; TkSSRF]

let io_sink_requirements (snk: io_sink) : taint_set =
  match snk with
  | IOStdout -> []
  | IOStderr -> []
  | IOFileOutput _ -> [TkPathTraversal]
  | IONetworkOut -> [TkSSRF]
  | IODatabase _ -> [TkSQLi]

let effect_input_label (src: io_source) : sec_label =
  sec_public_untrusted (io_source_taints src)

let effect_output_allowed (snk: io_sink) (l: sec_label) : bool =
  let required_absent = io_sink_requirements snk in
  not (List.Tot.existsb (fun k -> taint_in_set k l.taints) required_absent)


(** ****************************************************************************
    SECTION 16: SECURITY TYPE OPERATIONS
    **************************************************************************** *)

let sec_unary_result (st: sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = st.label;
}

let sec_binary_result (st1 st2: sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = sec_label_join st1.label st2.label;
}

let rec sec_nary_label (sts: list sec_type) : sec_label =
  match sts with
  | [] -> sec_bot
  | st :: rest -> sec_label_join st.label (sec_nary_label rest)

let sec_nary_result (sts: list sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = sec_nary_label sts;
}


(** ****************************************************************************
    SECTION 17: SECURITY CONTEXT
    **************************************************************************** *)

let empty_sec_ctx : sec_ctx = []

let extend_sec_ctx (x: string) (st: sec_type) (ctx: sec_ctx) : sec_ctx =
  (x, st) :: ctx

let rec lookup_sec_ctx (x: string) (ctx: sec_ctx) : option sec_type =
  match ctx with
  | [] -> None
  | (y, st) :: rest ->
      if x = y then Some st
      else lookup_sec_ctx x rest


(** ****************************************************************************
    SECTION 18: SINK CHECKING
    **************************************************************************** *)

let sink_check (snk: sink_annotation) (arg_labels: list sec_label) : bool =
  let check_param (idx: nat) =
    if idx < List.Tot.length arg_labels then
      let l = List.Tot.index arg_labels idx in
      not (has_any_taint snk.snk_rejects l)
    else true
  in
  List.Tot.for_all check_param snk.snk_params


(** ****************************************************************************
    SECTION 19: WELL-FORMEDNESS PREDICATES
    **************************************************************************** *)

let sec_label_wf (l: sec_label) : bool =
  match l.integrity with
  | ITrusted -> List.Tot.length l.taints = 0
  | IUntrusted -> true

let sec_type_wf (st: sec_type) : bool =
  sec_label_wf st.label

let taint_effect_to_string (te: taint_effect) : string =
  match te with
  | ETaintSource _ -> "taint_source"
  | ETaintSink _ -> "taint_sink"
  | ETaintSanitize _ -> "taint_sanitize"
  | ETaintPropagate -> "taint_propagate"
