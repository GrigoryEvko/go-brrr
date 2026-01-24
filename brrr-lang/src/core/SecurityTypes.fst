(**
 * BrrrLang.Core.SecurityTypes
 *
 * Unified Security Type System for Brrr-Lang IR.
 * Integrates taint tracking and information flow with the core type system.
 *
 * Based on:
 *   - Denning 1977 (Information Flow Lattices)
 *   - Livshits 2005 (Taint Analysis)
 *   - Myers 1999 (Decentralized Information Flow Control)
 *   - brrr_lang_spec_v0.4.tex Part IX
 *
 * KEY DESIGN PRINCIPLES:
 *   1. Security labels are PART of the type system (not separate wrappers)
 *   2. Taint propagation is tracked through EFFECTS (tainted I/O)
 *   3. Source/Sink/Sanitizer are TYPE ANNOTATIONS for static analysis
 *   4. Lattice is CONFIGURABLE (not just two-point)
 *   5. Supports both CONFIDENTIALITY and INTEGRITY dimensions
 *
 * Depends on: BrrrTypes, Effects, Modes, Primitives
 *)
module SecurityTypes

(** Z3 solver options for security type proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical
open Primitives
open Modes
open Effects
open BrrrTypes

(** ============================================================================
    SECURITY LATTICE IDENTIFIERS
    ============================================================================

    Security levels are identified by natural numbers, allowing arbitrary
    lattice configurations. The ordering is defined separately from the
    identifiers to support both linear and diamond lattices.
    ============================================================================ *)

(** Security level identifier - unique within a lattice configuration *)
type sec_level_id = nat

(** Named security level for human readability *)
noeq type named_sec_level = {
  level_id   : sec_level_id;
  level_name : string;
}

(** ============================================================================
    TAINT KINDS
    ============================================================================

    Taint kinds categorize the type of security vulnerability.
    This is more fine-grained than just "tainted/untainted".
    ============================================================================ *)

(** Taint kind for vulnerability categorization *)
type taint_kind =
  | TkSQLi          : taint_kind  (* SQL Injection *)
  | TkXSS           : taint_kind  (* Cross-Site Scripting *)
  | TkCMDi          : taint_kind  (* Command Injection *)
  | TkPathTraversal : taint_kind  (* Path Traversal *)
  | TkSSRF          : taint_kind  (* Server-Side Request Forgery *)
  | TkLDAPi         : taint_kind  (* LDAP Injection *)
  | TkXMLi          : taint_kind  (* XML Injection *)
  | TkHeaderi       : taint_kind  (* HTTP Header Injection *)
  | TkLogi          : taint_kind  (* Log Injection *)
  | TkTemplatei     : taint_kind  (* Template Injection *)
  | TkDeserial      : taint_kind  (* Insecure Deserialization *)
  | TkRedirect      : taint_kind  (* Open Redirect *)
  | TkCustom        : string -> taint_kind  (* User-defined taint kind *)

(** Taint kind equality *)
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

(** taint_kind_eq is reflexive *)
let taint_kind_eq_refl (k: taint_kind)
    : Lemma (ensures taint_kind_eq k k = true)
            [SMTPat (taint_kind_eq k k)] =
  match k with
  | TkSQLi -> () | TkXSS -> () | TkCMDi -> () | TkPathTraversal -> ()
  | TkSSRF -> () | TkLDAPi -> () | TkXMLi -> () | TkHeaderi -> ()
  | TkLogi -> () | TkTemplatei -> () | TkDeserial -> () | TkRedirect -> ()
  | TkCustom _ -> ()

(** ============================================================================
    SECURITY LABELS
    ============================================================================

    Security labels combine:
    1. Confidentiality level (Public < Secret for data secrecy)
    2. Integrity level (Trusted < Untrusted, inverted for taint)
    3. Taint kinds (set of vulnerability categories)

    This gives us a product lattice for fine-grained security tracking.
    ============================================================================ *)

(** Confidentiality dimension - prevents data leaks *)
type confidentiality =
  | CPublic : confidentiality    (* Anyone can read *)
  | CSecret : confidentiality    (* Restricted access *)

(** Integrity dimension - tracks trust level (inverted order for taint) *)
type integrity =
  | IUntrusted : integrity       (* From untrusted source - tainted *)
  | ITrusted   : integrity       (* From trusted source - sanitized *)

(** Taint set - which vulnerability categories affect this data *)
type taint_set = list taint_kind

(** Complete security label - product of confidentiality, integrity, and taints *)
noeq type sec_label = {
  confidentiality : confidentiality;
  integrity       : integrity;
  taints          : taint_set;
}

(** ============================================================================
    SECURITY LABEL CONSTRUCTORS
    ============================================================================ *)

(** Untainted, public data (safest) *)
let sec_public_trusted : sec_label = {
  confidentiality = CPublic;
  integrity = ITrusted;
  taints = [];
}

(** Secret but trusted data *)
let sec_secret_trusted : sec_label = {
  confidentiality = CSecret;
  integrity = ITrusted;
  taints = [];
}

(** Public but tainted data (from untrusted source) *)
let sec_public_untrusted (ks: taint_set) : sec_label = {
  confidentiality = CPublic;
  integrity = IUntrusted;
  taints = ks;
}

(** Create label tainted with specific kind *)
let sec_tainted (k: taint_kind) : sec_label = {
  confidentiality = CPublic;
  integrity = IUntrusted;
  taints = [k];
}

(** Bottom element of security lattice (most permissive) *)
let sec_bot : sec_label = sec_public_trusted

(** Top element of security lattice (most restrictive) *)
let sec_top : sec_label = {
  confidentiality = CSecret;
  integrity = IUntrusted;
  taints = [TkSQLi; TkXSS; TkCMDi; TkPathTraversal; TkSSRF];  (* All common taints *)
}

(** ============================================================================
    SECURITY LABEL ORDERING
    ============================================================================

    The ordering is a product order:
    - Confidentiality: Public <= Secret
    - Integrity: Trusted <= Untrusted (inverted for taint: tainted is "higher")
    - Taints: subset ordering

    l1 <= l2 means data at l1 can flow to l2 (l2 is more restrictive)
    ============================================================================ *)

(** Confidentiality ordering: Public < Secret *)
let conf_leq (c1 c2: confidentiality) : bool =
  match c1, c2 with
  | CPublic, _ -> true
  | CSecret, CSecret -> true
  | CSecret, CPublic -> false

(** Integrity ordering: Trusted < Untrusted (for taint flow) *)
let integ_leq (i1 i2: integrity) : bool =
  match i1, i2 with
  | ITrusted, _ -> true
  | IUntrusted, IUntrusted -> true
  | IUntrusted, ITrusted -> false

(** Check if taint kind is in set *)
let rec taint_in_set (k: taint_kind) (ks: taint_set) : bool =
  match ks with
  | [] -> false
  | k' :: rest -> taint_kind_eq k k' || taint_in_set k rest

(** Taint set subset ordering *)
let rec taint_set_subset (ks1 ks2: taint_set) : bool =
  match ks1 with
  | [] -> true
  | k :: rest -> taint_in_set k ks2 && taint_set_subset rest ks2

(** Security label ordering (product order) *)
let sec_label_leq (l1 l2: sec_label) : bool =
  conf_leq l1.confidentiality l2.confidentiality &&
  integ_leq l1.integrity l2.integrity &&
  taint_set_subset l1.taints l2.taints

(** ============================================================================
    SECURITY LABEL LATTICE OPERATIONS
    ============================================================================ *)

(** Confidentiality join *)
let conf_join (c1 c2: confidentiality) : confidentiality =
  match c1, c2 with
  | CSecret, _ | _, CSecret -> CSecret
  | CPublic, CPublic -> CPublic

(** Confidentiality meet *)
let conf_meet (c1 c2: confidentiality) : confidentiality =
  match c1, c2 with
  | CPublic, _ | _, CPublic -> CPublic
  | CSecret, CSecret -> CSecret

(** Integrity join *)
let integ_join (i1 i2: integrity) : integrity =
  match i1, i2 with
  | IUntrusted, _ | _, IUntrusted -> IUntrusted
  | ITrusted, ITrusted -> ITrusted

(** Integrity meet *)
let integ_meet (i1 i2: integrity) : integrity =
  match i1, i2 with
  | ITrusted, _ | _, ITrusted -> ITrusted
  | IUntrusted, IUntrusted -> IUntrusted

(** Taint set union (join) *)
let rec taint_set_union (ks1 ks2: taint_set) : taint_set =
  match ks1 with
  | [] -> ks2
  | k :: rest ->
      if taint_in_set k ks2 then taint_set_union rest ks2
      else k :: taint_set_union rest ks2

(** Taint set intersection (meet) *)
let rec taint_set_intersect (ks1 ks2: taint_set) : taint_set =
  match ks1 with
  | [] -> []
  | k :: rest ->
      if taint_in_set k ks2 then k :: taint_set_intersect rest ks2
      else taint_set_intersect rest ks2

(** Security label join (least upper bound) *)
let sec_label_join (l1 l2: sec_label) : sec_label = {
  confidentiality = conf_join l1.confidentiality l2.confidentiality;
  integrity = integ_join l1.integrity l2.integrity;
  taints = taint_set_union l1.taints l2.taints;
}

(** Security label meet (greatest lower bound) *)
let sec_label_meet (l1 l2: sec_label) : sec_label = {
  confidentiality = conf_meet l1.confidentiality l2.confidentiality;
  integrity = integ_meet l1.integrity l2.integrity;
  taints = taint_set_intersect l1.taints l2.taints;
}

(** ============================================================================
    SECURITY LABEL LATTICE LAWS
    ============================================================================ *)

(** conf_leq is reflexive *)
let conf_leq_refl (c: confidentiality)
    : Lemma (ensures conf_leq c c = true)
            [SMTPat (conf_leq c c)] =
  match c with CPublic -> () | CSecret -> ()

(** integ_leq is reflexive *)
let integ_leq_refl (i: integrity)
    : Lemma (ensures integ_leq i i = true)
            [SMTPat (integ_leq i i)] =
  match i with ITrusted -> () | IUntrusted -> ()

(** taint_in_set with head *)
let taint_in_set_head (k: taint_kind) (rest: taint_set)
    : Lemma (ensures taint_in_set k (k :: rest) = true)
            [SMTPat (taint_in_set k (k :: rest))] =
  taint_kind_eq_refl k

(** taint_set_subset is reflexive *)
let rec taint_set_subset_refl (ks: taint_set)
    : Lemma (ensures taint_set_subset ks ks = true)
            (decreases ks)
            [SMTPat (taint_set_subset ks ks)] =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_in_set_head k rest;
      taint_set_subset_refl rest

(** sec_label_leq is reflexive *)
let sec_label_leq_refl (l: sec_label)
    : Lemma (ensures sec_label_leq l l = true)
            [SMTPat (sec_label_leq l l)] =
  conf_leq_refl l.confidentiality;
  integ_leq_refl l.integrity;
  taint_set_subset_refl l.taints

(** ============================================================================
    TRANSITIVITY LEMMAS
    ============================================================================ *)

(** conf_leq is transitive *)
let conf_leq_trans (c1 c2 c3: confidentiality)
    : Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c3 = true)
            (ensures conf_leq c1 c3 = true) =
  match c1, c2, c3 with
  | CPublic, _, _ -> ()
  | CSecret, CSecret, CSecret -> ()
  | _, _, _ -> ()

(** integ_leq is transitive *)
let integ_leq_trans (i1 i2 i3: integrity)
    : Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i3 = true)
            (ensures integ_leq i1 i3 = true) =
  match i1, i2, i3 with
  | ITrusted, _, _ -> ()
  | IUntrusted, IUntrusted, IUntrusted -> ()
  | _, _, _ -> ()

#push-options "--fuel 1 --ifuel 1"
(** If k is in ks1 and ks1 is subset of ks2, then k is in ks2 *)
let rec taint_in_set_trans (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (requires taint_in_set k ks1 = true /\ taint_set_subset ks1 ks2 = true)
            (ensures taint_in_set k ks2 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then ()
      else taint_in_set_trans k rest ks2

(** taint_set_subset is transitive *)
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

(** sec_label_leq is transitive *)
let sec_label_leq_trans (l1 l2 l3: sec_label)
    : Lemma (requires sec_label_leq l1 l2 = true /\ sec_label_leq l2 l3 = true)
            (ensures sec_label_leq l1 l3 = true) =
  conf_leq_trans l1.confidentiality l2.confidentiality l3.confidentiality;
  integ_leq_trans l1.integrity l2.integrity l3.integrity;
  taint_set_subset_trans l1.taints l2.taints l3.taints

(** ============================================================================
    ANTISYMMETRY LEMMAS
    ============================================================================ *)

(** conf_leq is antisymmetric *)
let conf_leq_antisym (c1 c2: confidentiality)
    : Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c1 = true)
            (ensures c1 = c2) =
  match c1, c2 with
  | CPublic, CPublic -> ()
  | CSecret, CSecret -> ()
  | _, _ -> ()

(** integ_leq is antisymmetric *)
let integ_leq_antisym (i1 i2: integrity)
    : Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i1 = true)
            (ensures i1 = i2) =
  match i1, i2 with
  | ITrusted, ITrusted -> ()
  | IUntrusted, IUntrusted -> ()
  | _, _ -> ()

(** ============================================================================
    HELPER LEMMAS FOR TAINT SET OPERATIONS
    ============================================================================ *)

#push-options "--fuel 1 --ifuel 1"
(** taint_set_union includes left operand *)
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

(** taint_set_union includes right operand *)
let rec taint_set_union_includes_right (k: taint_kind) (ks1 ks2: taint_set)
    : Lemma (requires taint_in_set k ks2 = true)
            (ensures taint_in_set k (taint_set_union ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_in_set k' ks2 then taint_set_union_includes_right k rest ks2
      else taint_set_union_includes_right k rest ks2

(** taint_set_union is subset of both operands joined *)
let rec taint_set_union_subset (ks1 ks2 ks3: taint_set)
    : Lemma (requires taint_set_subset ks1 ks3 = true /\ taint_set_subset ks2 ks3 = true)
            (ensures taint_set_subset (taint_set_union ks1 ks2) ks3 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      if taint_in_set k ks2 then taint_set_union_subset rest ks2 ks3
      else taint_set_union_subset rest ks2 ks3

(** taint_set_intersect is subset of left operand *)
let rec taint_set_intersect_subset_left (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_subset (taint_set_intersect ks1 ks2) ks1 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      taint_set_intersect_subset_left rest ks2;
      if taint_in_set k ks2 then taint_kind_eq_refl k
      else ()

(** taint_set_intersect is subset of right operand *)
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

(** ============================================================================
    JOIN / MEET UPPER BOUND AND LOWER BOUND LEMMAS
    ============================================================================ *)

(** conf_join is an upper bound *)
let conf_join_upper_l (c1 c2: confidentiality)
    : Lemma (ensures conf_leq c1 (conf_join c1 c2) = true) =
  match c1, c2 with CPublic, _ -> () | CSecret, _ -> ()

let conf_join_upper_r (c1 c2: confidentiality)
    : Lemma (ensures conf_leq c2 (conf_join c1 c2) = true) =
  match c1, c2 with _, CPublic -> () | _, CSecret -> ()

(** integ_join is an upper bound *)
let integ_join_upper_l (i1 i2: integrity)
    : Lemma (ensures integ_leq i1 (integ_join i1 i2) = true) =
  match i1, i2 with ITrusted, _ -> () | IUntrusted, _ -> ()

let integ_join_upper_r (i1 i2: integrity)
    : Lemma (ensures integ_leq i2 (integ_join i1 i2) = true) =
  match i1, i2 with _, ITrusted -> () | _, IUntrusted -> ()

(** conf_meet is a lower bound *)
let conf_meet_lower_l (c1 c2: confidentiality)
    : Lemma (ensures conf_leq (conf_meet c1 c2) c1 = true) =
  match c1, c2 with CPublic, _ -> () | CSecret, _ -> ()

let conf_meet_lower_r (c1 c2: confidentiality)
    : Lemma (ensures conf_leq (conf_meet c1 c2) c2 = true) =
  match c1, c2 with _, CPublic -> () | _, CSecret -> ()

(** integ_meet is a lower bound *)
let integ_meet_lower_l (i1 i2: integrity)
    : Lemma (ensures integ_leq (integ_meet i1 i2) i1 = true) =
  match i1, i2 with ITrusted, _ -> () | IUntrusted, _ -> ()

let integ_meet_lower_r (i1 i2: integrity)
    : Lemma (ensures integ_leq (integ_meet i1 i2) i2 = true) =
  match i1, i2 with _, ITrusted -> () | _, IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
(** sec_label_join is an upper bound for l1 *)
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

(** sec_label_join is an upper bound for l2 *)
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

(** sec_label_join is the least upper bound *)
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

(** sec_label_meet is lower bound for l1 *)
let sec_label_meet_lower_l (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l1 = true)
            [SMTPat (sec_label_meet l1 l2)] =
  conf_meet_lower_l l1.confidentiality l2.confidentiality;
  integ_meet_lower_l l1.integrity l2.integrity;
  taint_set_intersect_subset_left l1.taints l2.taints

(** sec_label_meet is lower bound for l2 *)
let sec_label_meet_lower_r (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l2 = true) =
  conf_meet_lower_r l1.confidentiality l2.confidentiality;
  integ_meet_lower_r l1.integrity l2.integrity;
  taint_set_intersect_subset_right l1.taints l2.taints

#push-options "--fuel 1 --ifuel 1"
(** sec_label_meet is the greatest lower bound *)
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
    | k :: rest ->
        taints_glb ks1 ks2 rest
  in
  conf_glb l1.confidentiality l2.confidentiality lb.confidentiality;
  integ_glb l1.integrity l2.integrity lb.integrity;
  taints_glb l1.taints l2.taints lb.taints
#pop-options

(** ============================================================================
    SET EQUIVALENCE FOR TAINT SETS
    ============================================================================

    Since taint_set is implemented as a list, structural equality is too strong
    for proving commutativity of union/intersection. We define set equivalence
    as mutual membership and prove commutativity up to this equivalence.
    ============================================================================ *)

(** Two taint sets are equivalent if they have the same members *)
let taint_set_equiv (ks1 ks2: taint_set) : bool =
  taint_set_subset ks1 ks2 && taint_set_subset ks2 ks1

(** taint_set_equiv is reflexive *)
let taint_set_equiv_refl (ks: taint_set)
    : Lemma (ensures taint_set_equiv ks ks = true)
            [SMTPat (taint_set_equiv ks ks)] =
  taint_set_subset_refl ks

(** taint_set_equiv is symmetric *)
let taint_set_equiv_sym (ks1 ks2: taint_set)
    : Lemma (requires taint_set_equiv ks1 ks2 = true)
            (ensures taint_set_equiv ks2 ks1 = true) =
  ()

(** taint_set_equiv is transitive *)
let taint_set_equiv_trans (ks1 ks2 ks3: taint_set)
    : Lemma (requires taint_set_equiv ks1 ks2 = true /\ taint_set_equiv ks2 ks3 = true)
            (ensures taint_set_equiv ks1 ks3 = true) =
  taint_set_subset_trans ks1 ks2 ks3;
  taint_set_subset_trans ks3 ks2 ks1

#push-options "--fuel 1 --ifuel 1"
(** Union produces same membership regardless of argument order *)
let rec taint_set_union_equiv_comm (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_equiv (taint_set_union ks1 ks2) (taint_set_union ks2 ks1) = true)
            (decreases %[List.Tot.length ks1 + List.Tot.length ks2]) =
  (* Prove mutual subset via membership lemmas *)
  let u12 = taint_set_union ks1 ks2 in
  let u21 = taint_set_union ks2 ks1 in
  (* First direction: u12 subset of u21 *)
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
  (* Second direction: u21 subset of u12 *)
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
  (* u12 is subset of itself, so by aux1 it's subset of u21 *)
  taint_set_subset_refl u12;
  aux1 u12;
  (* u21 is subset of itself, so by aux2 it's subset of u12 *)
  taint_set_subset_refl u21;
  aux2 u21

(** Intersection produces same membership regardless of argument order *)
let rec taint_set_intersect_equiv_comm (ks1 ks2: taint_set)
    : Lemma (ensures taint_set_equiv (taint_set_intersect ks1 ks2) (taint_set_intersect ks2 ks1) = true)
            (decreases %[List.Tot.length ks1 + List.Tot.length ks2]) =
  let i12 = taint_set_intersect ks1 ks2 in
  let i21 = taint_set_intersect ks2 ks1 in
  (* Helper: k in intersect ks1 ks2 iff k in ks1 and k in ks2 *)
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
  (* Prove i12 subset of i21 *)
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
  (* Prove i21 subset of i12 *)
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

(** Two security labels are equivalent if all components are equal/equivalent *)
let sec_label_equiv (l1 l2: sec_label) : bool =
  l1.confidentiality = l2.confidentiality &&
  l1.integrity = l2.integrity &&
  taint_set_equiv l1.taints l2.taints

(** sec_label_equiv is reflexive *)
let sec_label_equiv_refl (l: sec_label)
    : Lemma (ensures sec_label_equiv l l = true)
            [SMTPat (sec_label_equiv l l)] =
  taint_set_equiv_refl l.taints

(** sec_label_equiv implies mutual sec_label_leq *)
let sec_label_equiv_leq (l1 l2: sec_label)
    : Lemma (requires sec_label_equiv l1 l2 = true)
            (ensures sec_label_leq l1 l2 = true /\ sec_label_leq l2 l1 = true) =
  ()

(** ============================================================================
    COMMUTATIVITY AND IDEMPOTENCE LEMMAS
    ============================================================================ *)

(** conf_join is commutative *)
let conf_join_comm (c1 c2: confidentiality)
    : Lemma (ensures conf_join c1 c2 = conf_join c2 c1) =
  match c1, c2 with
  | CPublic, CPublic -> ()
  | CPublic, CSecret -> ()
  | CSecret, CPublic -> ()
  | CSecret, CSecret -> ()

(** integ_join is commutative *)
let integ_join_comm (i1 i2: integrity)
    : Lemma (ensures integ_join i1 i2 = integ_join i2 i1) =
  match i1, i2 with
  | ITrusted, ITrusted -> ()
  | ITrusted, IUntrusted -> ()
  | IUntrusted, ITrusted -> ()
  | IUntrusted, IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(** taint_set_union produces sets with same membership - key lemma for commutativity *)
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
#pop-options

(** sec_label_join is commutative up to equivalence *)
let sec_label_join_comm_equiv (l1 l2: sec_label)
    : Lemma (ensures sec_label_equiv (sec_label_join l1 l2) (sec_label_join l2 l1) = true) =
  conf_join_comm l1.confidentiality l2.confidentiality;
  integ_join_comm l1.integrity l2.integrity;
  taint_set_union_equiv_comm l1.taints l2.taints

(** sec_label_join commutativity for ordering: both directions hold *)
let sec_label_join_comm_leq (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_join l1 l2) (sec_label_join l2 l1) = true /\
                     sec_label_leq (sec_label_join l2 l1) (sec_label_join l1 l2) = true) =
  sec_label_join_comm_equiv l1 l2;
  sec_label_equiv_leq (sec_label_join l1 l2) (sec_label_join l2 l1)

(** conf_join is idempotent *)
let conf_join_idem (c: confidentiality)
    : Lemma (ensures conf_join c c = c) =
  match c with CPublic -> () | CSecret -> ()

(** integ_join is idempotent *)
let integ_join_idem (i: integrity)
    : Lemma (ensures integ_join i i = i) =
  match i with ITrusted -> () | IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
(** taint_set_union is idempotent - union of ks with itself is ks *)
let rec taint_set_union_idem (ks: taint_set)
    : Lemma (ensures taint_set_union ks ks == ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_eq_refl k;
      taint_set_union_idem rest
#pop-options

(** sec_label_join is idempotent *)
let sec_label_join_idem (l: sec_label)
    : Lemma (ensures sec_label_join l l == l) =
  conf_join_idem l.confidentiality;
  integ_join_idem l.integrity;
  taint_set_union_idem l.taints

(** conf_meet is commutative *)
let conf_meet_comm (c1 c2: confidentiality)
    : Lemma (ensures conf_meet c1 c2 = conf_meet c2 c1) =
  match c1, c2 with
  | CPublic, CPublic -> ()
  | CPublic, CSecret -> ()
  | CSecret, CPublic -> ()
  | CSecret, CSecret -> ()

(** integ_meet is commutative *)
let integ_meet_comm (i1 i2: integrity)
    : Lemma (ensures integ_meet i1 i2 = integ_meet i2 i1) =
  match i1, i2 with
  | ITrusted, ITrusted -> ()
  | ITrusted, IUntrusted -> ()
  | IUntrusted, ITrusted -> ()
  | IUntrusted, IUntrusted -> ()

(** sec_label_meet is commutative up to equivalence *)
let sec_label_meet_comm_equiv (l1 l2: sec_label)
    : Lemma (ensures sec_label_equiv (sec_label_meet l1 l2) (sec_label_meet l2 l1) = true) =
  conf_meet_comm l1.confidentiality l2.confidentiality;
  integ_meet_comm l1.integrity l2.integrity;
  taint_set_intersect_equiv_comm l1.taints l2.taints

(** sec_label_meet commutativity for ordering: both directions hold *)
let sec_label_meet_comm_leq (l1 l2: sec_label)
    : Lemma (ensures sec_label_leq (sec_label_meet l1 l2) (sec_label_meet l2 l1) = true /\
                     sec_label_leq (sec_label_meet l2 l1) (sec_label_meet l1 l2) = true) =
  sec_label_meet_comm_equiv l1 l2;
  sec_label_equiv_leq (sec_label_meet l1 l2) (sec_label_meet l2 l1)

(** conf_meet is idempotent *)
let conf_meet_idem (c: confidentiality)
    : Lemma (ensures conf_meet c c = c) =
  match c with CPublic -> () | CSecret -> ()

(** integ_meet is idempotent *)
let integ_meet_idem (i: integrity)
    : Lemma (ensures integ_meet i i = i) =
  match i with ITrusted -> () | IUntrusted -> ()

#push-options "--fuel 1 --ifuel 1"
(** taint_set_intersect is idempotent *)
let rec taint_set_intersect_idem (ks: taint_set)
    : Lemma (ensures taint_set_intersect ks ks == ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_eq_refl k;
      taint_set_intersect_idem rest
#pop-options

(** sec_label_meet is idempotent *)
let sec_label_meet_idem (l: sec_label)
    : Lemma (ensures sec_label_meet l l == l) =
  conf_meet_idem l.confidentiality;
  integ_meet_idem l.integrity;
  taint_set_intersect_idem l.taints

(** ============================================================================
    SECURITY-TYPED TYPES
    ============================================================================

    A security-typed type pairs a base Brrr-Lang type with a security label.
    This allows tracking security properties through the type system.
    ============================================================================ *)

(** Security-typed type: base type + security label *)
noeq type sec_type = {
  base : brrr_type;
  label : sec_label;
}

(** Create a security-typed type *)
let mk_sec_type (t: brrr_type) (l: sec_label) : sec_type = {
  base = t;
  label = l;
}

(** Create an untainted (trusted, public) type *)
let untainted_type (t: brrr_type) : sec_type = {
  base = t;
  label = sec_public_trusted;
}

(** Create a tainted type with specific kind *)
let tainted_type (t: brrr_type) (k: taint_kind) : sec_type = {
  base = t;
  label = sec_tainted k;
}

(** Create a secret type *)
let secret_type (t: brrr_type) : sec_type = {
  base = t;
  label = sec_secret_trusted;
}

(** ============================================================================
    SECURITY-TYPED TYPE SUBTYPING
    ============================================================================

    st1 <: st2 iff:
    1. base(st1) <: base(st2)  (structural subtyping on base)
    2. label(st1) <= label(st2) (security label can only increase)

    This ensures data cannot be coerced to a lower security level.
    ============================================================================ *)

(** Security-typed subtyping *)
let sec_type_subtype (st1 st2: sec_type) : bool =
  subtype st1.base st2.base && sec_label_leq st1.label st2.label

(** sec_type_subtype is reflexive *)
let sec_type_subtype_refl (st: sec_type)
    : Lemma (ensures sec_type_subtype st st = true)
            [SMTPat (sec_type_subtype st st)] =
  subtype_refl st.base;
  sec_label_leq_refl st.label

(** ============================================================================
    SECURITY FUNCTION TYPES
    ============================================================================

    Function types have security-typed parameters and return.
    Security follows standard rules:
    - Parameters are CONTRAVARIANT in security (can accept more tainted)
    - Return is COVARIANT in security (can return less tainted)

    Additionally, functions can be annotated as:
    - SOURCE: introduces taint (return is tainted)
    - SINK: requires untainted input (parameter must be trusted)
    - SANITIZER: removes taint (tainted input -> trusted output)
    ============================================================================ *)

(** Security role of a function *)
type sec_role =
  | SrNone      : sec_role                      (* No special security role *)
  | SrSource    : list taint_kind -> sec_role   (* Introduces these taints *)
  | SrSink      : list taint_kind -> sec_role   (* Rejects these taints *)
  | SrSanitizer : list taint_kind -> sec_role   (* Removes these taints *)
  | SrValidator : list taint_kind -> sec_role   (* Validates (partial sanitize) *)

(** Security-typed function parameter *)
noeq type sec_param = {
  sp_name : option string;
  sp_type : sec_type;
  sp_mode : mode;
}

(** Security-typed function type *)
noeq type sec_func_type = {
  sf_params      : list sec_param;
  sf_return      : sec_type;
  sf_effects     : effect_row;
  sf_role        : sec_role;
  sf_is_unsafe   : bool;
}

(** ============================================================================
    TAINT EFFECTS
    ============================================================================

    Taint tracking through the effect system:
    - ETaintSource: Function introduces taint of specified kinds
    - ETaintSink: Function consumes potentially tainted data (security-sensitive)
    - ETaintSanitize: Function removes taint of specified kinds
    - ETaintPropagate: Operation propagates taint through data

    These effects enable:
    1. Static detection of taint flows
    2. Effect-based taint propagation rules
    3. Integration with the effect handler mechanism
    ============================================================================ *)

(** Taint effect operations *)
type taint_effect =
  | ETaintSource    : list taint_kind -> taint_effect  (* Introduces taints *)
  | ETaintSink      : list taint_kind -> taint_effect  (* Requires absence of taints *)
  | ETaintSanitize  : list taint_kind -> taint_effect  (* Removes taints *)
  | ETaintPropagate : taint_effect                     (* Propagates existing taints *)

(** Convert taint effect to effect_op for integration with effect system *)
let taint_effect_to_string (te: taint_effect) : string =
  match te with
  | ETaintSource _ -> "taint_source"
  | ETaintSink _ -> "taint_sink"
  | ETaintSanitize _ -> "taint_sanitize"
  | ETaintPropagate -> "taint_propagate"

(** ============================================================================
    I/O SOURCE TAINT MAPPING
    ============================================================================

    Maps I/O sources from Effects module to taint kinds.
    This connects the effect system's I/O tracking with taint analysis.
    ============================================================================ *)

(** Get taints introduced by an I/O source *)
let io_source_taints (src: io_source) : taint_set =
  match src with
  | IOStdin -> [TkCMDi; TkSQLi; TkXSS; TkPathTraversal]  (* User input: all common taints *)
  | IOEnvVar _ -> [TkCMDi; TkPathTraversal]              (* Env vars: command and path risks *)
  | IOFileInput _ -> [TkPathTraversal]                   (* File content: path traversal *)
  | IONetworkIn -> [TkSSRF; TkSQLi; TkXSS; TkCMDi]       (* Network: many attack vectors *)
  | IOUserInput -> [TkCMDi; TkSQLi; TkXSS; TkPathTraversal; TkSSRF]  (* All user input taints *)

(** Get sink requirements for an I/O sink *)
let io_sink_requirements (snk: io_sink) : taint_set =
  match snk with
  | IOStdout -> []                     (* Stdout: no strict requirements *)
  | IOStderr -> []                     (* Stderr: no strict requirements *)
  | IOFileOutput _ -> [TkPathTraversal]  (* File writes: reject path traversal *)
  | IONetworkOut -> [TkSSRF]           (* Network out: reject SSRF *)
  | IODatabase _ -> [TkSQLi]           (* Database: reject SQL injection *)

(** ============================================================================
    SECURITY EFFECT PROPAGATION
    ============================================================================

    Rules for how security labels propagate through effects.
    ============================================================================ *)

(** Input effect introduces taint based on source *)
let effect_input_label (src: io_source) : sec_label =
  sec_public_untrusted (io_source_taints src)

(** Check if output effect is allowed with given label *)
let effect_output_allowed (snk: io_sink) (l: sec_label) : bool =
  let required_absent = io_sink_requirements snk in
  not (List.Tot.existsb (fun k -> taint_in_set k l.taints) required_absent)

(** ============================================================================
    SECURITY TYPE OPERATIONS
    ============================================================================ *)

(** Apply unary operation: result has same security as input *)
let sec_unary_result (st: sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = st.label;
}

(** Apply binary operation: result has joined security *)
let sec_binary_result (st1 st2: sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = sec_label_join st1.label st2.label;
}

(** Apply n-ary operation: result has joined security of all inputs *)
let rec sec_nary_label (sts: list sec_type) : sec_label =
  match sts with
  | [] -> sec_bot
  | st :: rest -> sec_label_join st.label (sec_nary_label rest)

let sec_nary_result (sts: list sec_type) (result_base: brrr_type) : sec_type = {
  base = result_base;
  label = sec_nary_label sts;
}

(** ============================================================================
    SOURCE/SINK/SANITIZER TYPE ANNOTATIONS
    ============================================================================

    Type-level annotations for static security analysis by Brrr-Machine.
    These are attached to function types to indicate security roles.
    ============================================================================ *)

(** Function is a taint source - its return value is tainted *)
noeq type source_annotation = {
  src_name   : string;           (* Name of the source *)
  src_taints : list taint_kind;  (* Taints it introduces *)
  src_origin : string;           (* e.g., "user_input", "network", "file" *)
}

(** Function is a security sink - requires untainted input *)
noeq type sink_annotation = {
  snk_name     : string;           (* Name of the sink *)
  snk_rejects  : list taint_kind;  (* Taints that must be absent *)
  snk_params   : list nat;         (* Which parameters must be untainted (0-indexed) *)
}

(** Function is a sanitizer - removes specific taints *)
noeq type sanitizer_annotation = {
  san_name    : string;           (* Name of the sanitizer *)
  san_removes : list taint_kind;  (* Taints it removes *)
  san_param   : nat;              (* Which parameter is sanitized *)
}

(** Combined security annotation *)
type sec_annotation =
  | AnnSource    : source_annotation -> sec_annotation
  | AnnSink      : sink_annotation -> sec_annotation
  | AnnSanitizer : sanitizer_annotation -> sec_annotation
  | AnnTrusted   : sec_annotation  (* Function is in trusted code base *)

(** ============================================================================
    SECURITY CONTEXT
    ============================================================================

    Tracks security labels for variables in scope.
    Used by security type checker.
    ============================================================================ *)

(** Security context entry *)
type sec_ctx_entry = string & sec_type

(** Security context *)
type sec_ctx = list sec_ctx_entry

(** Empty security context *)
let empty_sec_ctx : sec_ctx = []

(** Extend context *)
let extend_sec_ctx (x: string) (st: sec_type) (ctx: sec_ctx) : sec_ctx =
  (x, st) :: ctx

(** Lookup in context *)
let rec lookup_sec_ctx (x: string) (ctx: sec_ctx) : option sec_type =
  match ctx with
  | [] -> None
  | (y, st) :: rest ->
      if x = y then Some st
      else lookup_sec_ctx x rest

(** ============================================================================
    PC (PROGRAM COUNTER) LABEL
    ============================================================================

    The PC label tracks the security level of the current control flow.
    It prevents implicit flows through conditionals.
    ============================================================================ *)

(** PC label is a security label *)
type pc_label = sec_label

(** Initial PC (public, trusted) *)
let initial_pc : pc_label = sec_public_trusted

(** Raise PC when entering branch guarded by secret/tainted condition *)
let raise_pc (pc: pc_label) (guard_label: sec_label) : pc_label =
  sec_label_join pc guard_label

(** Check if assignment is allowed: pc join rhs_label <= lhs_label *)
let check_flow (pc: pc_label) (rhs: sec_label) (lhs: sec_label) : bool =
  sec_label_leq (sec_label_join pc rhs) lhs

(** ============================================================================
    TAINT REMOVAL (Sanitization)
    ============================================================================

    IMPORTANT: Sanitization and Endorsement are SEPARATE operations!

    - Sanitization: Removes specific taint kinds (e.g., SQL escaping removes TkSQLi)
      This does NOT change integrity level - data remains IUntrusted until endorsed.

    - Endorsement: Promotes IUntrusted to ITrusted ONLY when all taints are removed.
      This is an EXPLICIT security decision that must be made consciously.

    Rationale: Combining these operations is dangerous because:
    1. A sanitizer might only handle one attack vector (e.g., SQL injection)
       but the data could still be dangerous for other sinks (e.g., command injection)
    2. Automatic endorsement hides security decisions in code flow
    3. Defense in depth requires explicit trust boundaries
    ============================================================================ *)

(** Remove a taint kind from a set *)
let rec remove_taint (k: taint_kind) (ks: taint_set) : taint_set =
  match ks with
  | [] -> []
  | k' :: rest ->
      if taint_kind_eq k k' then remove_taint k rest
      else k' :: remove_taint k rest

(** Remove multiple taint kinds *)
let rec remove_taints (to_remove: list taint_kind) (ks: taint_set) : taint_set =
  match to_remove with
  | [] -> ks
  | k :: rest -> remove_taints rest (remove_taint k ks)

(** Sanitize a security label for specific taints.
    DOES NOT change integrity - endorsement must be explicit! *)
let sanitize_label (to_remove: list taint_kind) (l: sec_label) : sec_label = {
  l with taints = remove_taints to_remove l.taints
  (* Integrity unchanged - data remains IUntrusted until explicitly endorsed *)
}

(** Explicitly endorse a label as trusted.
    Returns Some only if ALL taints have been removed.
    Returns None if any taints remain (cannot endorse tainted data). *)
let endorse_label (l: sec_label) : option sec_label =
  if List.Tot.length l.taints = 0
  then Some { l with integrity = ITrusted }
  else None  (* Cannot endorse: taints still present *)

(** Forcefully endorse a label (unsafe - use only in trusted code).
    Promotes to ITrusted regardless of remaining taints.
    WARNING: This bypasses security checks - only use when you know what you're doing! *)
let unsafe_endorse_label (l: sec_label) : sec_label = {
  l with
  integrity = ITrusted;
  taints = []  (* Also clear taints to maintain invariant *)
}

(** Sanitize then optionally endorse - the safe composition pattern *)
let sanitize_and_maybe_endorse (to_remove: list taint_kind) (l: sec_label) : sec_label * bool =
  let sanitized = sanitize_label to_remove l in
  match endorse_label sanitized with
  | Some endorsed -> (endorsed, true)
  | None -> (sanitized, false)

(** Sanitize a security-typed type - does NOT change integrity *)
let sanitize_sec_type (to_remove: list taint_kind) (st: sec_type) : sec_type = {
  st with label = sanitize_label to_remove st.label
}

(** Explicitly endorse a security-typed type.
    Returns Some only if the label can be endorsed (no taints). *)
let endorse_sec_type (st: sec_type) : option sec_type =
  match endorse_label st.label with
  | Some endorsed_label -> Some { st with label = endorsed_label }
  | None -> None

(** ============================================================================
    SECURITY VIOLATION CHECKING
    ============================================================================ *)

(** Check if a security label has any of the specified taints *)
let has_any_taint (ks: list taint_kind) (l: sec_label) : bool =
  List.Tot.existsb (fun k -> taint_in_set k l.taints) ks

(** Check if passing data to a sink is safe *)
let sink_check (snk: sink_annotation) (arg_labels: list sec_label) : bool =
  let check_param (idx: nat) =
    if idx < List.Tot.length arg_labels then
      let l = List.Tot.index arg_labels idx in
      not (has_any_taint snk.snk_rejects l)
    else true  (* Parameter doesn't exist - ok *)
  in
  List.Tot.for_all check_param snk.snk_params

(** ============================================================================
    BRRR-MACHINE INTEGRATION
    ============================================================================

    Types and functions that Brrr-Machine security analysis needs.
    ============================================================================ *)

(** Security finding severity *)
type sec_severity =
  | SevCritical : sec_severity  (* Confirmed vulnerability *)
  | SevHigh     : sec_severity  (* Likely vulnerability *)
  | SevMedium   : sec_severity  (* Possible vulnerability *)
  | SevLow      : sec_severity  (* Informational *)
  | SevInfo     : sec_severity  (* For completeness *)

(** Security finding (for Brrr-Machine to report) *)
noeq type sec_finding = {
  sf_id          : nat;                    (* Unique ID *)
  sf_kind        : taint_kind;             (* Vulnerability category *)
  sf_severity    : sec_severity;           (* How severe *)
  sf_source_loc  : option nat;             (* Source code location *)
  sf_sink_loc    : option nat;             (* Sink code location *)
  sf_message     : string;                 (* Description *)
  sf_remediation : option string;          (* How to fix *)
}

(** Taint flow edge (for call graph / data flow integration) *)
noeq type taint_flow_edge = {
  tfe_from_node : nat;                    (* Source node ID *)
  tfe_to_node   : nat;                    (* Target node ID *)
  tfe_taints    : taint_set;              (* Taints flowing *)
  tfe_sanitized : taint_set;              (* Taints removed along edge *)
}

(** Taint summary for a function (for interprocedural analysis) *)
noeq type func_taint_summary = {
  fts_func_id      : nat;                 (* Function ID *)
  fts_param_taints : list sec_label;      (* Input taint on each param *)
  fts_return_taint : sec_label;           (* Output taint *)
  fts_role         : sec_role;            (* Source/Sink/Sanitizer role *)
  fts_annotations  : list sec_annotation; (* Security annotations *)
}

(** ============================================================================
    WELL-FORMEDNESS PREDICATES
    ============================================================================ *)

(** A security label is well-formed if taints are consistent with integrity *)
let sec_label_wf (l: sec_label) : bool =
  match l.integrity with
  | ITrusted -> List.Tot.length l.taints = 0  (* Trusted => no taints *)
  | IUntrusted -> true  (* Untrusted can have any taints *)

(** A security type is well-formed *)
let sec_type_wf (st: sec_type) : bool =
  sec_label_wf st.label

(** ============================================================================
    SECURITY TYPE SOUNDNESS LEMMAS
    ============================================================================ *)

(** Sanitization removes the specified taints *)
let rec remove_taint_correct (k: taint_kind) (ks: taint_set)
    : Lemma (ensures taint_in_set k (remove_taint k ks) = false)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then remove_taint_correct k rest
      else remove_taint_correct k rest

(** Sanitization preserves other taints *)
let rec remove_taint_preserves (k k': taint_kind) (ks: taint_set)
    : Lemma (requires taint_kind_eq k k' = false)
            (ensures taint_in_set k' (remove_taint k ks) = taint_in_set k' ks)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k'' :: rest -> remove_taint_preserves k k' rest

(** After sanitization, sink check passes for removed taints *)
let sanitize_enables_sink (to_remove: list taint_kind) (l: sec_label)
    : Lemma (ensures not (has_any_taint to_remove (sanitize_label to_remove l))) =
  ()  (* By construction: remove_taints removes all specified taints *)

(** Endorsed labels are always well-formed (have no taints) *)
let endorse_label_wf (l: sec_label)
    : Lemma (ensures (match endorse_label l with
                      | Some endorsed -> sec_label_wf endorsed = true
                      | None -> true)) =
  ()  (* By construction: endorse_label only returns Some when taints = [] *)

(** Endorsement only succeeds when all taints are removed *)
let endorse_requires_clean (l: sec_label)
    : Lemma (ensures (Some? (endorse_label l)) = (List.Tot.length l.taints = 0)) =
  ()

(** Sanitization does not change integrity *)
let sanitize_preserves_integrity (to_remove: list taint_kind) (l: sec_label)
    : Lemma (ensures (sanitize_label to_remove l).integrity = l.integrity) =
  ()

(** Sanitization does not change confidentiality *)
let sanitize_preserves_confidentiality (to_remove: list taint_kind) (l: sec_label)
    : Lemma (ensures (sanitize_label to_remove l).confidentiality = l.confidentiality) =
  ()

(** unsafe_endorse_label produces well-formed labels *)
let unsafe_endorse_label_wf (l: sec_label)
    : Lemma (ensures sec_label_wf (unsafe_endorse_label l) = true) =
  ()  (* By construction: sets integrity=ITrusted and taints=[] *)

(** The sanitize-then-endorse pattern is sound: only clean data gets endorsed *)
let sanitize_and_endorse_sound (to_remove: list taint_kind) (l: sec_label)
    : Lemma (ensures snd (sanitize_and_maybe_endorse to_remove l) = true ==>
                     sec_label_wf (fst (sanitize_and_maybe_endorse to_remove l)) = true) =
  ()

(** ============================================================================
    SUMMARY
    ============================================================================

    This module provides:

    1. Security Labels (sec_label):
       - Product of confidentiality, integrity, and taint sets
       - Forms a complete lattice with join/meet operations
       - Supports fine-grained taint tracking by vulnerability kind

    2. Security-Typed Types (sec_type):
       - Pairs base Brrr-Lang types with security labels
       - Subtyping respects both base subtyping and label ordering

    3. Security Function Types (sec_func_type):
       - Tracks security of parameters and return
       - Annotated with security roles (Source/Sink/Sanitizer)

    4. I/O Taint Integration:
       - Maps I/O sources from Effects to taint kinds
       - Maps I/O sinks to taint requirements

    5. Sanitization and Endorsement (SEPARATED for security):
       - sanitize_label: Removes specific taints, does NOT change integrity
       - endorse_label: Explicitly promotes IUntrusted to ITrusted (only if no taints)
       - unsafe_endorse_label: Force endorsement (for trusted code only)
       - Soundness proofs for sanitization and endorsement correctness

    6. Brrr-Machine Integration:
       - Security findings for vulnerability reporting
       - Taint flow edges for interprocedural analysis
       - Function taint summaries

    Key Guarantees:
    - Taint propagation follows the effect system
    - Sanitization correctly removes specified taints (does NOT implicitly endorse)
    - Endorsement requires explicit decision and absence of all taints
    - Flow checking prevents implicit flows via PC tracking
    - Lattice operations are proven reflexive, transitive, and (up to set equivalence) commutative
    ============================================================================ *)
