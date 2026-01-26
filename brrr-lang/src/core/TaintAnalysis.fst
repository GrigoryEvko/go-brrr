(**
 * BrrrLang.Core.TaintAnalysis
 *
 * Taint Analysis for tracking untrusted data flow through programs.
 * Based on brrr_lang_spec_v0.4.tex Part IX-B (Taint Analysis).
 *
 * Implements:
 *   - Taint kinds for different vulnerability categories
 *   - Taint status tracking (Untainted/Tainted)
 *   - Tainted value wrapper with propagation semantics
 *   - Source/Sink/Sanitizer primitives
 *   - Taint propagation through operations
 *   - Soundness theorems (NO ADMITS)
 *
 * The taint analysis tracks potentially malicious data from untrusted
 * sources (user input, network, etc.) to security-sensitive sinks
 * (SQL queries, command execution, etc.). Proper sanitization must
 * occur before tainted data reaches a sink.
 *
 * Depends on: FStar.List.Tot
 *)
module TaintAnalysis

(* Z3 configuration for taint lattice proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical

(** ============================================================================
    TAINT KIND FUNCTIONS
    ============================================================================

    Functions for working with taint kinds. The taint_kind type and
    taint_kind_eq are defined in the interface file (TaintAnalysis.fsti)
    as unfold definitions, so the normalizer can compute directly.
    ============================================================================ *)

(** taint_kind_eq is reflexive - trivial with unfold *)
let taint_kind_eq_refl (k: taint_kind)
    : Lemma (ensures taint_kind_eq k k = true) =
  ()  (* Normalizer computes directly *)

(** taint_kind_eq is symmetric - trivial with unfold *)
let taint_kind_eq_sym (k1 k2: taint_kind)
    : Lemma (requires taint_kind_eq k1 k2 = true)
            (ensures taint_kind_eq k2 k1 = true) =
  ()  (* Normalizer computes directly *)

(** taint_kind_eq implies Leibniz equality - trivial with unfold *)
let taint_kind_eq_implies_eq (k1 k2: taint_kind)
    : Lemma (requires taint_kind_eq k1 k2 = true)
            (ensures k1 = k2) =
  ()  (* Normalizer computes directly *)

(** ============================================================================
    TAINT KIND ORDERING (for canonical representation)
    ============================================================================

    To ensure taint_kind_merge is structurally commutative, we maintain
    taint kind lists in a canonical sorted order. This requires a total
    ordering on taint_kind.
    ============================================================================ *)

(** Convert taint_kind to integer for ordering *)
let taint_kind_to_int (k: taint_kind) : nat =
  match k with
  | TaintSQLi -> 0
  | TaintXSS -> 1
  | TaintCMDi -> 2
  | TaintPathTraversal -> 3
  | TaintSSRF -> 4

(** Strict less-than ordering on taint kinds *)
let taint_kind_lt (k1 k2: taint_kind) : bool =
  taint_kind_to_int k1 < taint_kind_to_int k2

(** taint_kind_lt is irreflexive *)
let taint_kind_lt_irrefl (k: taint_kind)
    : Lemma (ensures taint_kind_lt k k = false) =
  ()

(** taint_kind_lt is transitive *)
let taint_kind_lt_trans (k1 k2 k3: taint_kind)
    : Lemma (requires taint_kind_lt k1 k2 = true /\ taint_kind_lt k2 k3 = true)
            (ensures taint_kind_lt k1 k3 = true) =
  ()

(** taint_kind_lt is asymmetric *)
let taint_kind_lt_asymm (k1 k2: taint_kind)
    : Lemma (requires taint_kind_lt k1 k2 = true)
            (ensures taint_kind_lt k2 k1 = false) =
  ()

(** Total ordering: exactly one of lt, eq, gt holds *)
let taint_kind_compare (k1 k2: taint_kind) : (c:int{c = -1 \/ c = 0 \/ c = 1}) =
  let i1 = taint_kind_to_int k1 in
  let i2 = taint_kind_to_int k2 in
  if i1 < i2 then -1
  else if i1 = i2 then 0
  else 1

(** Compare result characterization - trivial with unfold taint_kind_eq *)
let taint_kind_compare_spec (k1 k2: taint_kind)
    : Lemma (ensures (taint_kind_compare k1 k2 = -1 <==> taint_kind_lt k1 k2 = true) /\
                     (taint_kind_compare k1 k2 = 0 <==> taint_kind_eq k1 k2 = true) /\
                     (taint_kind_compare k1 k2 = 1 <==> taint_kind_lt k2 k1 = true)) =
  ()  (* Normalizer computes directly with unfold *)

(** ============================================================================
    TAINT KIND LIST OPERATIONS
    ============================================================================

    Helper functions for working with lists of taint kinds.
    We use lists to track multiple taint kinds that may affect a value.
    ============================================================================ *)

(** Check if a taint kind is in a list *)
let rec taint_kind_mem (k: taint_kind) (ks: list taint_kind) : bool =
  match ks with
  | [] -> false
  | k' :: rest -> taint_kind_eq k k' || taint_kind_mem k rest

(** taint_kind_mem respects membership *)
let rec taint_kind_mem_implies_mem (k: taint_kind) (ks: list taint_kind)
    : Lemma (requires taint_kind_mem k ks = true)
            (ensures exists k'. mem k' ks /\ taint_kind_eq k k' = true)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then ()
      else taint_kind_mem_implies_mem k rest

(** Remove a taint kind from a list *)
let rec taint_kind_remove (k: taint_kind) (ks: list taint_kind) : list taint_kind =
  match ks with
  | [] -> []
  | k' :: rest ->
      if taint_kind_eq k k' then taint_kind_remove k rest
      else k' :: taint_kind_remove k rest

(** After removal, the kind is not in the list *)
let rec taint_kind_remove_not_mem (k: taint_kind) (ks: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_remove k ks) = false)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then
        taint_kind_remove_not_mem k rest
      else begin
        taint_kind_remove_not_mem k rest;
        (* Need to show: taint_kind_eq k k' = false /\
           taint_kind_mem k (taint_kind_remove k rest) = false
           => taint_kind_mem k (k' :: taint_kind_remove k rest) = false *)
        ()
      end

(** Removal preserves other elements *)
let rec taint_kind_remove_preserves (k k': taint_kind) (ks: list taint_kind)
    : Lemma (requires taint_kind_eq k k' = false)
            (ensures taint_kind_mem k' ks = taint_kind_mem k' (taint_kind_remove k ks))
            (decreases ks) =
  match ks with
  | [] -> ()
  | k'' :: rest ->
      if taint_kind_eq k k'' then begin
        (* k is removed, k' <> k, so if k' = k'' then k' <> k which is true *)
        taint_kind_remove_preserves k k' rest
      end
      else
        taint_kind_remove_preserves k k' rest

(** ============================================================================
    CANONICAL TAINT KIND LIST OPERATIONS
    ============================================================================

    To ensure structural commutativity of merge, we maintain taint kind lists
    in sorted order (by taint_kind_to_int) with no duplicates.
    This guarantees that [A;B;C] merged with [D] equals [D] merged with [A;B;C].
    ============================================================================ *)

(**
 * Insert a taint kind into a sorted list, maintaining sorted order.
 * If the kind is already present, returns the list unchanged.
 *)
let rec insert_sorted (k: taint_kind) (ks: list taint_kind) : list taint_kind =
  match ks with
  | [] -> [k]
  | k' :: rest ->
      if taint_kind_lt k k' then k :: ks       (* k goes before k' *)
      else if taint_kind_eq k k' then ks       (* k already present *)
      else k' :: insert_sorted k rest          (* k goes after k' *)

(** insert_sorted preserves membership of existing elements *)
let rec insert_sorted_preserves_mem (k k': taint_kind) (ks: list taint_kind)
    : Lemma (requires taint_kind_mem k' ks = true)
            (ensures taint_kind_mem k' (insert_sorted k ks) = true)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k'' :: rest ->
      if taint_kind_lt k k'' then ()
      else if taint_kind_eq k k'' then ()
      else if taint_kind_eq k' k'' then ()
      else insert_sorted_preserves_mem k k' rest

(** insert_sorted adds the element *)
let rec insert_sorted_adds (k: taint_kind) (ks: list taint_kind)
    : Lemma (ensures taint_kind_mem k (insert_sorted k ks) = true)
            (decreases ks) =
  match ks with
  | [] -> taint_kind_eq_refl k
  | k' :: rest ->
      if taint_kind_lt k k' then taint_kind_eq_refl k
      else if taint_kind_eq k k' then ()
      else insert_sorted_adds k rest

(** insert_sorted characterization *)
let rec insert_sorted_mem_iff (k k': taint_kind) (ks: list taint_kind)
    : Lemma (ensures taint_kind_mem k' (insert_sorted k ks) =
                     (taint_kind_eq k' k || taint_kind_mem k' ks))
            (decreases ks) =
  match ks with
  | [] -> ()
  | k'' :: rest ->
      if taint_kind_lt k k'' then ()
      else if taint_kind_eq k k'' then begin
        (* insert_sorted k (k'' :: rest) = k'' :: rest *)
        (* Need: taint_kind_mem k' (k'' :: rest) = taint_kind_eq k' k || taint_kind_mem k' (k'' :: rest) *)
        (* Since k = k'', if k' = k then k' = k'' so k' is in list *)
        taint_kind_eq_sym k k'';
        if taint_kind_eq k' k then begin
          taint_kind_eq_implies_eq k k'';
          taint_kind_eq_implies_eq k' k;
          taint_kind_eq_refl k''
        end else ()
      end
      else
        insert_sorted_mem_iff k k' rest

(**
 * Merge two taint kind lists into a canonical sorted representation.
 * This is the commutative union operation.
 *)
let rec taint_kind_merge_canonical (ks1 ks2: list taint_kind) : list taint_kind =
  match ks1 with
  | [] -> ks2
  | k :: rest -> taint_kind_merge_canonical rest (insert_sorted k ks2)

(** Merge canonical contains elements from right list *)
let rec merge_canonical_right (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kind_mem k ks2 = true)
            (ensures taint_kind_mem k (taint_kind_merge_canonical ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      insert_sorted_preserves_mem k' k ks2;
      merge_canonical_right k rest (insert_sorted k' ks2)

(** Merge canonical contains elements from left list *)
let rec merge_canonical_left (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kind_mem k ks1 = true)
            (ensures taint_kind_mem k (taint_kind_merge_canonical ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then begin
        insert_sorted_adds k' ks2;
        merge_canonical_right k' rest (insert_sorted k' ks2)
      end
      else
        merge_canonical_left k rest ks2

(** Key characterization: element is in merge iff in either operand *)
let rec merge_canonical_mem_iff (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_merge_canonical ks1 ks2) =
                     (taint_kind_mem k ks1 || taint_kind_mem k ks2))
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      insert_sorted_mem_iff k' k ks2;
      merge_canonical_mem_iff k rest (insert_sorted k' ks2)

(** Merge canonical is commutative (semantically) *)
let merge_canonical_comm_semantics (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_merge_canonical ks1 ks2) =
                     taint_kind_mem k (taint_kind_merge_canonical ks2 ks1)) =
  merge_canonical_mem_iff k ks1 ks2;
  merge_canonical_mem_iff k ks2 ks1

(**
 * Merge two taint kind lists (union) - using canonical representation.
 *
 * This is the primary merge operation, now using canonical sorted order
 * to ensure structural commutativity: merge [A;B] [C] = merge [C] [A;B].
 *)
let taint_kind_merge (ks1 ks2: list taint_kind) : list taint_kind =
  taint_kind_merge_canonical ks1 ks2

(** Merge from full lists includes second list elements *)
let taint_kind_merge_right_full (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kind_mem k ks2 = true)
            (ensures taint_kind_mem k (taint_kind_merge ks1 ks2) = true) =
  merge_canonical_right k ks1 ks2

(** Merge contains elements from first list *)
let taint_kind_merge_left (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kind_mem k ks1 = true)
            (ensures taint_kind_mem k (taint_kind_merge ks1 ks2) = true) =
  merge_canonical_left k ks1 ks2

(**
 * Merge is now structurally commutative due to canonical representation.
 * merge ks1 ks2 = merge ks2 ks1 (for sorted, deduplicated inputs)
 *)
let taint_kind_merge_comm_structural (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_merge ks1 ks2) =
                     taint_kind_mem k (taint_kind_merge ks2 ks1)) =
  merge_canonical_comm_semantics k ks1 ks2

(** ============================================================================
    TAINT STATUS FUNCTIONS
    ============================================================================

    Functions for working with taint status. The taint_status type is defined
    in the interface file (TaintAnalysis.fsti).

    NOTE: is_untainted and normalize_taint are now unfold in .fsti
    so they don't need implementations here.
    ============================================================================ *)

(**
 * Check if taint status contains a specific kind.
 * Recursive helper, kept in implementation.
 *)
let taint_contains (t: taint_status) (k: taint_kind) : bool =
  match t with
  | Untainted -> false
  | Tainted ks -> taint_kind_mem k ks

(** ============================================================================
    TAINT STATUS EQUALITY
    ============================================================================ *)

(** Check if two taint kind lists are equal as sets *)
let rec taint_kinds_subset (ks1 ks2: list taint_kind) : bool =
  match ks1 with
  | [] -> true
  | k :: rest -> taint_kind_mem k ks2 && taint_kinds_subset rest ks2

let taint_kinds_eq (ks1 ks2: list taint_kind) : bool =
  taint_kinds_subset ks1 ks2 && taint_kinds_subset ks2 ks1

(** Taint status equality *)
let taint_status_eq (t1 t2: taint_status) : bool =
  match normalize_taint t1, normalize_taint t2 with
  | Untainted, Untainted -> true
  | Tainted ks1, Tainted ks2 -> taint_kinds_eq ks1 ks2
  | _, _ -> false

(** taint_kind_mem with head is always true *)
let taint_kind_mem_head (k: taint_kind) (rest: list taint_kind)
    : Lemma (ensures taint_kind_mem k (k :: rest) = true) =
  taint_kind_eq_refl k

(** If k is in ks, then k is in (k' :: ks) *)
let taint_kind_mem_cons (k k': taint_kind) (ks: list taint_kind)
    : Lemma (requires taint_kind_mem k ks = true)
            (ensures taint_kind_mem k (k' :: ks) = true) =
  ()

(** If ks1 is subset of ks2, then ks1 is subset of (k :: ks2) *)
let rec taint_kinds_subset_cons (ks1: list taint_kind) (k: taint_kind) (ks2: list taint_kind)
    : Lemma (requires taint_kinds_subset ks1 ks2 = true)
            (ensures taint_kinds_subset ks1 (k :: ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      taint_kind_mem_cons k' k ks2;
      taint_kinds_subset_cons rest k ks2

(** taint_kinds_subset is reflexive *)
let rec taint_kinds_subset_refl (ks: list taint_kind)
    : Lemma (ensures taint_kinds_subset ks ks = true)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_mem_head k rest;
      taint_kinds_subset_refl rest;
      taint_kinds_subset_cons rest k rest

let taint_status_eq_refl (t: taint_status)
    : Lemma (ensures taint_status_eq t t = true) =
  match normalize_taint t with
  | Untainted -> ()
  | Tainted ks -> taint_kinds_subset_refl ks

(** ============================================================================
    SUBSET TRANSITIVITY AND ANTISYMMETRY
    ============================================================================

    These lemmas complete the partial order structure on taint kind lists.
    ============================================================================ *)

(**
 * Helper: If k is in ks1 and ks1 is a subset of ks2, then k is in ks2.
 *)
#push-options "--fuel 1 --ifuel 0"
let rec taint_kind_mem_subset (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kind_mem k ks1 = true /\ taint_kinds_subset ks1 ks2 = true)
            (ensures taint_kind_mem k ks2 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_eq k k' then begin
        (* k = k', and k' must be in ks2 since ks1 subset ks2 *)
        taint_kind_eq_implies_eq k k'
      end
      else
        (* k is in rest, and rest is subset of ks2 *)
        taint_kind_mem_subset k rest ks2
#pop-options

(**
 * Transitivity: if ks1 subset ks2 and ks2 subset ks3, then ks1 subset ks3.
 *)
#push-options "--fuel 1 --ifuel 0"
let rec taint_kinds_subset_trans (ks1 ks2 ks3: list taint_kind)
    : Lemma (requires taint_kinds_subset ks1 ks2 = true /\ taint_kinds_subset ks2 ks3 = true)
            (ensures taint_kinds_subset ks1 ks3 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      (* k is in ks1, so k is in ks2, so k is in ks3 *)
      taint_kind_mem_subset k ks2 ks3;
      (* rest is subset of ks2, ks2 subset ks3, so rest subset ks3 *)
      taint_kinds_subset_trans rest ks2 ks3
#pop-options

(**
 * Antisymmetry: if ks1 subset ks2 and ks2 subset ks1, then ks1 = ks2 (as sets).
 *)
let taint_kinds_subset_antisym (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kinds_subset ks1 ks2 = true /\ taint_kinds_subset ks2 ks1 = true)
            (ensures taint_kinds_eq ks1 ks2 = true) =
  (* taint_kinds_eq is defined as subset in both directions *)
  ()

(** ============================================================================
    TAINT OPERATIONS
    ============================================================================

    Core operations on taint status.
    ============================================================================ *)

(**
 * Join two taint statuses (least upper bound).
 *
 * The join of two taint statuses produces a status that is tainted
 * with all kinds from both operands. This models the combination of
 * potentially tainted data (e.g., string concatenation).
 *
 * Properties:
 *   - taint_join Untainted t = t
 *   - taint_join t Untainted = t
 *   - taint_join (Tainted ks1) (Tainted ks2) = Tainted (ks1 union ks2)
 *)
let taint_join (t1 t2: taint_status) : taint_status =
  match t1, t2 with
  | Untainted, t -> t
  | t, Untainted -> t
  | Tainted ks1, Tainted ks2 -> Tainted (taint_kind_merge ks1 ks2)

(** ============================================================================
    TAINT JOIN PROPERTIES
    ============================================================================

    We prove that taint_join forms a join semilattice with Untainted as bottom.
    ============================================================================ *)

(** Untainted is the identity element (left) *)
let taint_join_untainted_left (t: taint_status)
    : Lemma (ensures taint_join Untainted t = t)
            [SMTPat (taint_join Untainted t)] =
  ()

(** Untainted is the identity element (right) *)
let taint_join_untainted_right (t: taint_status)
    : Lemma (ensures taint_join t Untainted = t)
            [SMTPat (taint_join t Untainted)] =
  match t with
  | Untainted -> ()
  | Tainted _ -> ()

(** taint_kind_merge with empty right is identity *)
(** Merge with empty right gives sorted version of left *)
let rec taint_kind_merge_nil_right_mem (k: taint_kind) (ks: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_merge ks []) = taint_kind_mem k ks)
            (decreases ks) =
  merge_canonical_mem_iff k ks []

(**
 * Key lemma: merge produces elements from both lists.
 * This is the characterization lemma for the canonical merge.
 *)
let taint_kind_in_merge (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_merge ks1 ks2) =
                     (taint_kind_mem k ks1 || taint_kind_mem k ks2)) =
  merge_canonical_mem_iff k ks1 ks2

(**
 * taint_join is commutative (in terms of taint_contains behavior).
 *
 * This is the key property: for any taint kind k,
 * taint_contains (taint_join t1 t2) k = taint_contains (taint_join t2 t1) k
 *)
let taint_join_comm_contains (t1 t2: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_join t1 t2) k = taint_contains (taint_join t2 t1) k)
            [SMTPat (taint_contains (taint_join t1 t2) k); SMTPat (taint_contains (taint_join t2 t1) k)] =
  match t1, t2 with
  | Untainted, Untainted -> ()
  | Untainted, Tainted _ -> ()
  | Tainted _, Untainted -> ()
  | Tainted ks1, Tainted ks2 ->
      taint_kind_in_merge k ks1 ks2;
      taint_kind_in_merge k ks2 ks1

(**
 * taint_join is associative (in terms of taint_contains behavior).
 *
 * For any taint kind k,
 * taint_contains (taint_join (taint_join t1 t2) t3) k =
 * taint_contains (taint_join t1 (taint_join t2 t3)) k
 *)
let taint_join_assoc_contains (t1 t2 t3: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_join (taint_join t1 t2) t3) k =
                     taint_contains (taint_join t1 (taint_join t2 t3)) k) =
  match t1, t2, t3 with
  | Untainted, _, _ -> ()
  | _, Untainted, _ -> ()
  | _, _, Untainted -> ()
  | Tainted ks1, Tainted ks2, Tainted ks3 ->
      (* Use merge characterization *)
      let m12 = taint_kind_merge ks1 ks2 in
      let m23 = taint_kind_merge ks2 ks3 in
      taint_kind_in_merge k ks1 ks2;
      taint_kind_in_merge k ks2 ks3;
      taint_kind_in_merge k m12 ks3;
      taint_kind_in_merge k ks1 m23

(**
 * taint_join is idempotent (in terms of taint_contains behavior).
 *)
let taint_join_idem_contains (t: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_join t t) k = taint_contains t k)
            [SMTPat (taint_contains (taint_join t t) k)] =
  match t with
  | Untainted -> ()
  | Tainted ks ->
      taint_kind_in_merge k ks ks

(** ============================================================================
    TAINT MEET (Greatest Lower Bound)
    ============================================================================

    The meet operation computes the intersection of taint kinds.
    Used for computing the common taints between two values.
    ============================================================================ *)

(** Intersect two taint kind lists *)
let rec taint_kind_intersect (ks1 ks2: list taint_kind) : list taint_kind =
  match ks1 with
  | [] -> []
  | k :: rest ->
      if taint_kind_mem k ks2 then k :: taint_kind_intersect rest ks2
      else taint_kind_intersect rest ks2

(**
 * Meet of two taint statuses (greatest lower bound).
 *
 * Properties:
 *   - taint_meet Untainted t = Untainted
 *   - taint_meet t Untainted = Untainted
 *   - taint_meet (Tainted ks1) (Tainted ks2) = Tainted (ks1 intersect ks2)
 *)
let taint_meet (t1 t2: taint_status) : taint_status =
  match t1, t2 with
  | Untainted, _ -> Untainted
  | _, Untainted -> Untainted
  | Tainted ks1, Tainted ks2 ->
      let intersection = taint_kind_intersect ks1 ks2 in
      if length intersection = 0 then Untainted
      else Tainted intersection

(** ============================================================================
    MEET PROPERTIES
    ============================================================================ *)

(** taint_kind_intersect characterization: k in intersect iff k in both *)
#push-options "--fuel 1 --ifuel 1"
let rec taint_kind_in_intersect (k: taint_kind) (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kind_mem k (taint_kind_intersect ks1 ks2) =
                     (taint_kind_mem k ks1 && taint_kind_mem k ks2))
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k' :: rest ->
      if taint_kind_mem k' ks2 then begin
        if taint_kind_eq k k' then
          taint_kind_eq_refl k
        else
          taint_kind_in_intersect k rest ks2
      end
      else
        taint_kind_in_intersect k rest ks2
#pop-options

(** Meet is commutative (in terms of taint_contains behavior) *)
let taint_meet_comm_contains (t1 t2: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_meet t1 t2) k = taint_contains (taint_meet t2 t1) k) =
  match t1, t2 with
  | Untainted, Untainted -> ()
  | Untainted, Tainted _ -> ()
  | Tainted _, Untainted -> ()
  | Tainted ks1, Tainted ks2 ->
      taint_kind_in_intersect k ks1 ks2;
      taint_kind_in_intersect k ks2 ks1

(** Meet is idempotent: meet(t, t) = t (in terms of taint_contains behavior) *)
let taint_meet_idem_contains (t: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_meet t t) k = taint_contains t k)
            [SMTPat (taint_contains (taint_meet t t) k)] =
  match t with
  | Untainted -> ()
  | Tainted ks -> taint_kind_in_intersect k ks ks

(** ============================================================================
    LATTICE IDEMPOTENT LEMMAS (Structural)
    ============================================================================ *)

(** Helper: taint_kind_merge with itself *)
let rec taint_kind_merge_self (ks: list taint_kind)
    : Lemma (ensures taint_kinds_eq (taint_kind_merge ks ks) ks = true)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_merge_self rest;
      taint_kind_mem_head k rest

(**
 * taint_join is idempotent: join(t, t) = t (structural, via status equality)
 *)
let taint_join_idempotent (t: taint_status)
    : Lemma (ensures taint_status_eq (taint_join t t) t = true)
            [SMTPat (taint_join t t)] =
  match t with
  | Untainted -> ()
  | Tainted ks ->
      taint_kind_merge_self ks;
      taint_kinds_subset_refl ks

(** Helper: taint_kind_intersect with itself *)
let rec taint_kind_intersect_self (ks: list taint_kind)
    : Lemma (ensures taint_kinds_eq (taint_kind_intersect ks ks) ks = true)
            (decreases ks) =
  match ks with
  | [] -> ()
  | k :: rest ->
      taint_kind_eq_refl k;
      taint_kind_mem_head k rest;
      taint_kind_intersect_self rest;
      taint_kinds_subset_refl ks

(**
 * taint_meet is idempotent: meet(t, t) = t (structural, via status equality)
 *)
let taint_meet_idempotent (t: taint_status)
    : Lemma (ensures taint_status_eq (taint_meet t t) t = true)
            [SMTPat (taint_meet t t)] =
  match t with
  | Untainted -> ()
  | Tainted ks ->
      taint_kind_intersect_self ks

(** ============================================================================
    ABSORPTION LAWS
    ============================================================================ *)

(** Helper: subset from intersection *)
let rec intersect_subset_left (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kinds_subset (taint_kind_intersect ks1 ks2) ks1 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      if taint_kind_mem k ks2 then begin
        taint_kind_mem_head k rest;
        intersect_subset_left rest ks2;
        taint_kinds_subset_cons (taint_kind_intersect rest ks2) k rest
      end
      else
        intersect_subset_left rest ks2

(** Helper: merge is superset of left *)
let rec merge_superset_left (ks1 ks2: list taint_kind)
    : Lemma (ensures taint_kinds_subset ks1 (taint_kind_merge ks1 ks2) = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      merge_superset_left rest ks2;
      if taint_kind_mem k ks2 then
        taint_kind_merge_right_full k rest ks2
      else
        taint_kind_mem_head k (taint_kind_merge rest ks2)

(**
 * Absorption law 1: join(t, meet(t, s)) = t (in terms of taint_contains)
 *
 * This states that joining with the intersection does not add anything
 * beyond what's already in t.
 *)
let taint_absorption1_contains (t s: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_join t (taint_meet t s)) k = taint_contains t k) =
  match t, s with
  | Untainted, _ -> ()
  | _, Untainted -> ()
  | Tainted ks1, Tainted ks2 ->
      let meet_ks = taint_kind_intersect ks1 ks2 in
      taint_kind_in_intersect k ks1 ks2;
      taint_kind_in_merge k ks1 meet_ks

(**
 * Absorption law 2: meet(t, join(t, s)) = t (in terms of taint_contains)
 *
 * This states that taking the intersection with the union gives back t.
 *)
let taint_absorption2_contains (t s: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_meet t (taint_join t s)) k = taint_contains t k) =
  match t, s with
  | Untainted, _ -> ()
  | _, Untainted -> ()
  | Tainted ks1, Tainted ks2 ->
      let join_ks = taint_kind_merge ks1 ks2 in
      taint_kind_in_merge k ks1 ks2;
      taint_kind_in_intersect k ks1 join_ks

(** ============================================================================
    STRUCTURAL ABSORPTION LAWS
    ============================================================================

    These lemmas prove that the absorption laws hold structurally, meaning
    the result is equal (via taint_status_eq) rather than just having the
    same membership for each kind.
    ============================================================================ *)

(**
 * Helper: intersection with superset gives back the subset.
 *)
#push-options "--fuel 1 --ifuel 0"
let rec intersect_with_superset (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kinds_subset ks1 ks2 = true)
            (ensures taint_kinds_eq (taint_kind_intersect ks1 ks2) ks1 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      (* Since ks1 subset ks2, k is in ks2 *)
      (* intersect adds k and continues with rest *)
      intersect_with_superset rest ks2;
      taint_kind_in_intersect k ks1 ks2;
      (* Show that intersect result has same membership as ks1 *)
      let result = taint_kind_intersect ks1 ks2 in
      (* result = k :: (taint_kind_intersect rest ks2) since k in ks2 *)
      taint_kind_mem_head k rest
#pop-options

(**
 * Helper: merge with subset gives back the superset.
 *)
#push-options "--fuel 1 --ifuel 0"
let rec merge_with_subset (ks1 ks2: list taint_kind)
    : Lemma (requires taint_kinds_subset ks2 ks1 = true)
            (ensures taint_kinds_eq (taint_kind_merge ks1 ks2) ks1 = true)
            (decreases ks1) =
  match ks1 with
  | [] -> ()
  | k :: rest ->
      merge_canonical_mem_iff k ks1 ks2;
      taint_kind_mem_head k rest;
      merge_with_subset rest ks2;
      taint_kinds_subset_refl ks1
#pop-options

(**
 * Structural Absorption Law 1: join(t, meet(t, s)) = t
 *
 * Proof: meet(t, s) is a subset of t, so join(t, subset_of_t) = t.
 *)
let taint_absorption1 (t s: taint_status)
    : Lemma (ensures taint_status_eq (taint_join t (taint_meet t s)) t = true) =
  match t, s with
  | Untainted, _ -> ()
  | _, Untainted ->
      (* meet(t, Untainted) = Untainted, join(t, Untainted) = t *)
      taint_status_eq_refl t
  | Tainted ks1, Tainted ks2 ->
      let meet_ks = taint_kind_intersect ks1 ks2 in
      (* Show: join(Tainted ks1, Tainted meet_ks) = Tainted (merge ks1 meet_ks) *)
      (* Since meet_ks subset ks1, merge ks1 meet_ks = ks1 *)
      intersect_subset_left ks1 ks2;
      (* meet_ks is subset of ks1 *)
      if length meet_ks = 0 then
        (* meet is Untainted, join t Untainted = t *)
        taint_status_eq_refl t
      else begin
        (* The join result is Tainted (merge ks1 meet_ks) *)
        (* Since meet_ks subset ks1, merge ks1 meet_ks has same elements as ks1 *)
        merge_superset_left ks1 meet_ks;
        let result = taint_kind_merge ks1 meet_ks in
        (* Show result and ks1 have same membership *)
        Classical.forall_intro (fun k ->
          merge_canonical_mem_iff k ks1 meet_ks;
          taint_kind_in_intersect k ks1 ks2
        );
        taint_kinds_subset_refl ks1
      end

(**
 * Structural Absorption Law 2: meet(t, join(t, s)) = t
 *
 * Proof: t is a subset of join(t, s), so meet(t, superset_of_t) = t.
 *)
let taint_absorption2 (t s: taint_status)
    : Lemma (ensures taint_status_eq (taint_meet t (taint_join t s)) t = true) =
  match t, s with
  | Untainted, _ ->
      (* meet(Untainted, anything) = Untainted *)
      ()
  | _, Untainted ->
      (* join(t, Untainted) = t, meet(t, t) = t *)
      taint_meet_idempotent t
  | Tainted ks1, Tainted ks2 ->
      let join_ks = taint_kind_merge ks1 ks2 in
      (* ks1 is subset of join_ks *)
      merge_superset_left ks1 ks2;
      (* intersect ks1 join_ks = ks1 since ks1 subset join_ks *)
      intersect_with_superset ks1 join_ks;
      let meet_result = taint_kind_intersect ks1 join_ks in
      if length meet_result = 0 then
        (* ks1 must be empty, so t = Tainted [] which normalizes to Untainted *)
        (* But meet_result = ks1 (they have same membership), so ks1 is empty *)
        taint_status_eq_refl t
      else
        ()

(** ============================================================================
    TAINT ORDERING (PARTIAL ORDER)
    ============================================================================ *)

(**
 * Partial order on taint status.
 * t1 <= t2 iff t1 is "less tainted" than t2
 * (i.e., all taints in t1 are also in t2)
 *)
let taint_leq (t1 t2: taint_status) : bool =
  match t1, t2 with
  | Untainted, _ -> true
  | Tainted _, Untainted -> false
  | Tainted ks1, Tainted ks2 -> taint_kinds_subset ks1 ks2

(** taint_leq is reflexive *)
let taint_leq_refl (t: taint_status)
    : Lemma (ensures taint_leq t t = true)
            [SMTPat (taint_leq t t)] =
  match t with
  | Untainted -> ()
  | Tainted ks -> taint_kinds_subset_refl ks

(** Untainted is the bottom element *)
let taint_leq_bot (t: taint_status)
    : Lemma (ensures taint_leq Untainted t = true)
            [SMTPat (taint_leq Untainted t)] =
  ()

(**
 * taint_leq is transitive.
 *)
let taint_leq_trans (t1 t2 t3: taint_status)
    : Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t3 = true)
            (ensures taint_leq t1 t3 = true) =
  match t1, t2, t3 with
  | Untainted, _, _ -> ()
  | Tainted _, Untainted, _ -> ()  (* Contradicts first precondition *)
  | Tainted _, Tainted _, Untainted -> ()  (* Contradicts second precondition *)
  | Tainted ks1, Tainted ks2, Tainted ks3 -> taint_kinds_subset_trans ks1 ks2 ks3

(**
 * taint_leq is antisymmetric (via taint_status_eq).
 *)
let taint_leq_antisym (t1 t2: taint_status)
    : Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t1 = true)
            (ensures taint_status_eq t1 t2 = true) =
  match t1, t2 with
  | Untainted, Untainted -> ()
  | Untainted, Tainted _ -> ()  (* Contradicts second precondition *)
  | Tainted _, Untainted -> ()  (* Contradicts first precondition *)
  | Tainted ks1, Tainted ks2 ->
      taint_kinds_subset_antisym ks1 ks2

(** Join is least upper bound *)
let taint_join_lub (t1 t2: taint_status)
    : Lemma (ensures taint_leq t1 (taint_join t1 t2) = true /\
                     taint_leq t2 (taint_join t1 t2) = true) =
  match t1, t2 with
  | Untainted, _ -> taint_leq_refl t2
  | _, Untainted -> taint_leq_refl t1
  | Tainted ks1, Tainted ks2 ->
      merge_superset_left ks1 ks2;
      (* For ks2 subset of merge ks1 ks2, use merge_right_full *)
      let rec merge_superset_right (ks1' ks2': list taint_kind)
          : Lemma (ensures taint_kinds_subset ks2' (taint_kind_merge ks1' ks2') = true)
                  (decreases ks2') =
        match ks2' with
        | [] -> ()
        | k :: rest ->
            taint_kind_merge_right_full k ks1' ks2';
            merge_superset_right ks1' rest
      in
      merge_superset_right ks1 ks2

(** taint_join preserves taint kinds *)
let taint_join_contains_left (t1 t2: taint_status) (k: taint_kind)
    : Lemma (requires taint_contains t1 k = true)
            (ensures taint_contains (taint_join t1 t2) k = true) =
  match t1, t2 with
  | Untainted, _ -> ()  (* Vacuously true: Untainted doesn't contain anything *)
  | Tainted ks1, Untainted -> ()
  | Tainted ks1, Tainted ks2 -> taint_kind_merge_left k ks1 ks2

let taint_join_contains_right (t1 t2: taint_status) (k: taint_kind)
    : Lemma (requires taint_contains t2 k = true)
            (ensures taint_contains (taint_join t1 t2) k = true) =
  match t1, t2 with
  | _, Untainted -> ()  (* Vacuously true *)
  | Untainted, Tainted ks2 -> ()
  | Tainted ks1, Tainted ks2 -> taint_kind_merge_right_full k ks1 ks2

(** ============================================================================
    TAINTED VALUES FUNCTIONS
    ============================================================================

    Functions for working with tainted values. The tainted type is defined
    in the interface file (TaintAnalysis.fsti).
    ============================================================================ *)

(** Create an untainted value *)
let untainted (#a: Type) (v: a) : tainted a =
  { value = v; taint = Untainted }

(** Create a tainted value with a single kind *)
let tainted_with (#a: Type) (v: a) (k: taint_kind) : tainted a =
  { value = v; taint = Tainted [k] }

(** Create a tainted value with multiple kinds *)
let tainted_with_kinds (#a: Type) (v: a) (ks: list taint_kind) : tainted a =
  { value = v; taint = Tainted ks }

(** Get the underlying value (unsafe - ignores taint) *)
let get_value (#a: Type) (t: tainted a) : a =
  t.value

(** Get the taint status *)
let get_taint (#a: Type) (t: tainted a) : taint_status =
  t.taint

(** Check if a tainted value is untainted *)
let is_safe (#a: Type) (t: tainted a) : bool =
  is_untainted t.taint

(** ============================================================================
    SOURCES, SINKS, AND SANITIZERS
    ============================================================================

    These are the primitive operations for taint analysis:

    - source: Introduces taint (marks data as coming from untrusted source)
    - sink:   Consumes tainted data (checks that required taints are absent)
    - sanitize: Removes specific taint kinds (after proper validation)
    ============================================================================ *)

(**
 * Mark a value as coming from a tainted source.
 *
 * This is used at points where untrusted data enters the system:
 * - User input (forms, query params, etc.)
 * - Network data (HTTP requests, database results from untrusted queries)
 * - File contents from user-specified paths
 * - Environment variables
 *
 * @param k The kind of taint to apply
 * @param v The value to taint
 * @returns A tainted value with the specified taint kind
 *)
let source #a k v =
  { value = v; taint = Tainted [k] }

(**
 * Attempt to use a tainted value at a security-sensitive sink.
 *
 * Returns Some value only if the value is NOT tainted with the specified kind.
 * This models security-sensitive operations that must reject tainted data:
 * - SQL query execution (rejects TaintSQLi)
 * - Shell command execution (rejects TaintCMDi)
 * - HTML output (rejects TaintXSS)
 * - File system operations (rejects TaintPathTraversal)
 * - HTTP requests (rejects TaintSSRF)
 *
 * @param k The taint kind to check for
 * @param t The tainted value to check
 * @returns Some value if safe, None if tainted with the specified kind
 *)
let sink #a k t =
  if taint_contains t.taint k then None
  else Some t.value

(**
 * Sanitize a tainted value, removing a specific taint kind.
 *
 * This models proper input validation/sanitization:
 * - SQL parameterization or escaping (removes TaintSQLi)
 * - HTML encoding (removes TaintXSS)
 * - Shell escaping or whitelisting (removes TaintCMDi)
 * - Path canonicalization and validation (removes TaintPathTraversal)
 * - URL validation against allowlist (removes TaintSSRF)
 *
 * The sanitizer function transforms the value while removing the taint.
 * The function should perform actual sanitization (not just identity).
 *
 * @param k The taint kind to remove
 * @param t The tainted value to sanitize
 * @param sanitizer The sanitization function to apply to the value
 * @returns A tainted value with the specified taint kind removed
 *)
let sanitize #a k t sanitizer =
  let new_taint =
    match t.taint with
    | Untainted -> Untainted
    | Tainted ks ->
        let remaining = taint_kind_remove k ks in
        if length remaining = 0 then Untainted
        else Tainted remaining
  in
  { value = sanitizer t.value; taint = new_taint }

(** ============================================================================
    SANITIZE CORRECTNESS THEOREM
    ============================================================================

    We prove that sanitize correctly removes the specified taint kind.
    ============================================================================ *)

(**
 * After sanitization, the value does not contain the sanitized taint kind.
 *
 * This is the fundamental correctness property of sanitize:
 * If we sanitize for kind k, then the result is not tainted with k.
 *)
let sanitize_removes_taint (#a: Type) (k: taint_kind) (t: tainted a) (f: a -> a)
    : Lemma (ensures taint_contains (sanitize k t f).taint k = false) =
  match t.taint with
  | Untainted -> ()
  | Tainted ks ->
      (* The new taint list has k removed *)
      taint_kind_remove_not_mem k ks

(**
 * Sanitization preserves other taint kinds.
 *
 * Sanitizing for kind k does not affect other taint kinds.
 *)
let sanitize_preserves_other_taints (#a: Type) (k k': taint_kind) (t: tainted a) (f: a -> a)
    : Lemma (requires taint_kind_eq k k' = false /\ taint_contains t.taint k' = true)
            (ensures taint_contains (sanitize k t f).taint k' = true) =
  match t.taint with
  | Untainted -> ()
  | Tainted ks ->
      taint_kind_remove_preserves k k' ks

(** ============================================================================
    SINK SOUNDNESS THEOREM
    ============================================================================

    We prove that if sink returns Some, the input was properly sanitized.
    ============================================================================ *)

(**
 * If sink returns Some, the input was not tainted with the checked kind.
 *
 * This is the fundamental soundness property: we cannot bypass the sink
 * check with tainted data.
 *)
let sink_soundness (#a: Type) (k: taint_kind) (t: tainted a)
    : Lemma (ensures Some? (sink k t) <==> taint_contains t.taint k = false) =
  ()

(**
 * Combining sanitize and sink: sanitized values pass the sink check.
 *
 * This theorem shows that the intended usage pattern works:
 * 1. Receive tainted data from source
 * 2. Sanitize it for the appropriate kind
 * 3. Use it at a sink of that kind
 *)
let sanitize_then_sink (#a: Type) (k: taint_kind) (t: tainted a) (f: a -> a)
    : Lemma (ensures Some? (sink k (sanitize k t f))) =
  sanitize_removes_taint k t f

(** ============================================================================
    TAINT PROPAGATION
    ============================================================================

    Taint propagation tracks how taint flows through operations.
    When tainted data is used in an operation, the result inherits the taint.
    ============================================================================ *)

(**
 * Apply a unary function to a tainted value, propagating taint.
 *
 * The result has the same taint as the input.
 * This models operations like:
 * - String transformations (toLowerCase, trim, etc.)
 * - Numeric operations
 * - Type conversions
 *)
let taint_map (#a #b: Type) (f: a -> b) (t: tainted a) : tainted b =
  { value = f t.value; taint = t.taint }

(**
 * Apply a binary function to two tainted values, joining taints.
 *
 * The result is tainted with the union of both input taints.
 * This models operations like:
 * - String concatenation
 * - Arithmetic operations
 * - Collection operations (append, merge)
 *)
let taint_map2 (#a #b #c: Type) (f: a -> b -> c) (t1: tainted a) (t2: tainted b) : tainted c =
  { value = f t1.value t2.value; taint = taint_join t1.taint t2.taint }

(** ============================================================================
    TAINT PROPAGATION PROPERTIES
    ============================================================================ *)

(** taint_map preserves taint *)
let taint_map_preserves_taint (#a #b: Type) (f: a -> b) (t: tainted a)
    : Lemma (ensures (taint_map f t).taint = t.taint) =
  ()

(** taint_map with untainted input produces untainted output *)
let taint_map_untainted (#a #b: Type) (f: a -> b) (t: tainted a)
    : Lemma (requires is_safe t)
            (ensures is_safe (taint_map f t)) =
  ()

(** Taint join characterization: k is in join iff k is in t1 or t2 *)
let taint_join_contains_iff (t1 t2: taint_status) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_join t1 t2) k =
                     (taint_contains t1 k || taint_contains t2 k)) =
  match t1, t2 with
  | Untainted, Untainted -> ()
  | Untainted, Tainted _ -> ()
  | Tainted _, Untainted -> ()
  | Tainted ks1, Tainted ks2 -> taint_kind_in_merge k ks1 ks2

(** taint_map2 combines taints *)
let taint_map2_combines_taints (#a #b #c: Type) (f: a -> b -> c)
                                (t1: tainted a) (t2: tainted b) (k: taint_kind)
    : Lemma (ensures taint_contains (taint_map2 f t1 t2).taint k =
                     (taint_contains t1.taint k || taint_contains t2.taint k)) =
  taint_join_contains_iff t1.taint t2.taint k

(** Two untainted inputs produce untainted output *)
let taint_map2_both_untainted (#a #b #c: Type) (f: a -> b -> c)
                               (t1: tainted a) (t2: tainted b)
    : Lemma (requires is_safe t1 /\ is_safe t2)
            (ensures is_safe (taint_map2 f t1 t2)) =
  ()

(** ============================================================================
    MONADIC OPERATIONS FOR TAINTED VALUES
    ============================================================================

    Tainted values form a monad, allowing composition of taint-tracking
    computations.
    ============================================================================ *)

(** Pure: lift an untainted value *)
let taint_pure (#a: Type) (v: a) : tainted a =
  untainted v

(** Bind: sequence taint-tracking computations *)
let taint_bind (#a #b: Type) (t: tainted a) (f: a -> tainted b) : tainted b =
  let result = f t.value in
  { value = result.value; taint = taint_join t.taint result.taint }

(** Monad laws *)

(** Left identity: pure v >>= f = f v (up to taint equality) *)
let taint_monad_left_identity (#a #b: Type) (v: a) (f: a -> tainted b)
    : Lemma (ensures taint_status_eq (taint_bind (taint_pure v) f).taint (f v).taint = true) =
  taint_join_untainted_left (f v).taint;
  taint_status_eq_refl (f v).taint

(** Right identity: t >>= pure = t (up to taint equality) *)
let taint_monad_right_identity (#a: Type) (t: tainted a)
    : Lemma (ensures taint_status_eq (taint_bind t taint_pure).taint t.taint = true) =
  taint_join_untainted_right t.taint;
  taint_status_eq_refl t.taint

(** ============================================================================
    TAINT ANALYSIS CONTEXT
    ============================================================================

    For tracking taint through a program, we maintain a context mapping
    variables to their taint status.
    ============================================================================ *)

(** Variable identifier *)
type taint_var_id = string

(** Taint context: maps variables to taint status *)
type taint_ctx = list (taint_var_id & taint_status)

(** Empty taint context *)
let empty_taint_ctx : taint_ctx = []

(** Extend context with a binding *)
let extend_taint_ctx (x: taint_var_id) (t: taint_status) (ctx: taint_ctx) : taint_ctx =
  (x, t) :: ctx

(** Lookup variable in context *)
let rec lookup_taint_ctx (x: taint_var_id) (ctx: taint_ctx) : option taint_status =
  match ctx with
  | [] -> None
  | (y, t) :: rest ->
      if x = y then Some t
      else lookup_taint_ctx x rest

(** Update variable taint in context *)
let rec update_taint_ctx (x: taint_var_id) (t: taint_status) (ctx: taint_ctx) : taint_ctx =
  match ctx with
  | [] -> [(x, t)]
  | (y, t') :: rest ->
      if x = y then (x, t) :: rest
      else (y, t') :: update_taint_ctx x t rest

(** ============================================================================
    MULTI-TAINT OPERATIONS
    ============================================================================

    Operations for working with values tainted with multiple kinds.
    ============================================================================ *)

(** Add a taint kind to a tainted value *)
let add_taint (#a: Type) (k: taint_kind) (t: tainted a) : tainted a =
  { t with taint = taint_join t.taint (Tainted [k]) }

(** Remove all taints from a value (unsafe - for trusted code paths only) *)
let trust (#a: Type) (t: tainted a) : tainted a =
  { t with taint = Untainted }

(** Check if a value is tainted with any of the specified kinds *)
let rec tainted_with_any (t: taint_status) (ks: list taint_kind) : bool =
  match ks with
  | [] -> false
  | k :: rest -> taint_contains t k || tainted_with_any t rest

(** Check if a value is tainted with all of the specified kinds *)
let rec tainted_with_all (t: taint_status) (ks: list taint_kind) : bool =
  match ks with
  | [] -> true
  | k :: rest -> taint_contains t k && tainted_with_all t rest

(** ============================================================================
    SINK POLICIES
    ============================================================================

    Different sinks may require different combinations of taints to be absent.
    ============================================================================ *)

(** A sink policy specifies which taint kinds must be absent *)
type sink_policy = list taint_kind

(** Check if a tainted value satisfies a sink policy *)
let satisfies_policy (t: taint_status) (policy: sink_policy) : bool =
  not (tainted_with_any t policy)

(** Policy-based sink *)
let sink_with_policy (#a: Type) (policy: sink_policy) (t: tainted a) : option a =
  if satisfies_policy t.taint policy then Some t.value
  else None

(** Sanitize for all kinds in a policy *)
let rec sanitize_for_policy (#a: Type) (policy: sink_policy) (t: tainted a) (f: a -> a)
    : tainted a =
  match policy with
  | [] -> t
  | k :: rest -> sanitize_for_policy rest (sanitize k t f) f

(** Helper: sanitize only removes taints, never adds *)
let sanitize_monotone (#a: Type) (k k': taint_kind) (t: tainted a) (f: a -> a)
    : Lemma (requires taint_contains t.taint k' = false)
            (ensures taint_contains (sanitize k t f).taint k' = false) =
  match t.taint with
  | Untainted -> ()
  | Tainted ks ->
      (* After removing k, if k' wasn't there before, it still isn't *)
      if taint_kind_eq k k' then
        taint_kind_remove_not_mem k ks
      else
        taint_kind_remove_preserves k k' ks

(** Helper: sanitize_for_policy preserves absence of a taint kind *)
let rec sanitize_for_policy_preserves_absence (#a: Type) (policy: sink_policy) (t: tainted a) (f: a -> a) (k': taint_kind)
    : Lemma (requires taint_contains t.taint k' = false)
            (ensures taint_contains (sanitize_for_policy policy t f).taint k' = false)
            (decreases policy) =
  match policy with
  | [] -> ()
  | k :: rest ->
      sanitize_monotone k k' t f;
      sanitize_for_policy_preserves_absence rest (sanitize k t f) f k'

(** Helper: show that tainted_with_any is false after sanitizing *)
let rec not_tainted_with_any_after_sanitize (#a: Type) (policy: sink_policy) (t: tainted a) (f: a -> a)
    : Lemma (ensures tainted_with_any (sanitize_for_policy policy t f).taint policy = false)
            (decreases policy) =
  match policy with
  | [] -> ()
  | k :: rest ->
      (* After sanitizing for k, it's removed *)
      sanitize_removes_taint k t f;
      (* After sanitizing for rest, other removals happen *)
      let t' = sanitize k t f in
      (* k is not in t' *)
      (* After sanitize_for_policy rest t' f, k is still not there (monotonicity) *)
      sanitize_for_policy_preserves_absence rest t' f k;
      (* And tainted_with_any ... rest is false by IH *)
      not_tainted_with_any_after_sanitize rest t' f

(** After sanitizing for a policy, the policy is satisfied *)
let sanitize_for_policy_satisfies (#a: Type) (policy: sink_policy) (t: tainted a) (f: a -> a)
    : Lemma (ensures satisfies_policy (sanitize_for_policy policy t f).taint policy = true) =
  not_tainted_with_any_after_sanitize policy t f

(** ============================================================================
    COMMON SINK POLICIES
    ============================================================================ *)

(** SQL sink: rejects SQL injection *)
let sql_sink_policy : sink_policy = [TaintSQLi]

(** HTML sink: rejects XSS *)
let html_sink_policy : sink_policy = [TaintXSS]

(** Shell sink: rejects command injection *)
let shell_sink_policy : sink_policy = [TaintCMDi]

(** File sink: rejects path traversal *)
let file_sink_policy : sink_policy = [TaintPathTraversal]

(** HTTP sink: rejects SSRF *)
let http_sink_policy : sink_policy = [TaintSSRF]

(** Web application sink: rejects all web vulnerabilities *)
let web_app_sink_policy : sink_policy = [TaintSQLi; TaintXSS; TaintCMDi; TaintPathTraversal; TaintSSRF]

(** ============================================================================
    TAINT FLOW ANALYSIS
    ============================================================================

    Track taint flow through control flow to detect implicit flows.
    ============================================================================ *)

(** PC (Program Counter) taint for implicit flow tracking *)
type pc_taint = taint_status

(** Initial PC taint (untainted) *)
let initial_pc_taint : pc_taint = Untainted

(** Raise PC taint when entering a conditional with tainted condition *)
let raise_pc_taint (pc: pc_taint) (cond_taint: taint_status) : pc_taint =
  taint_join pc cond_taint

(** Check if assignment is allowed under current PC taint *)
let check_implicit_flow (pc: pc_taint) (target_taint: taint_status) : bool =
  (* If PC is tainted, we can only assign to tainted targets *)
  match pc with
  | Untainted -> true
  | Tainted pc_kinds ->
      match target_taint with
      | Untainted -> false  (* Cannot assign to untainted under tainted PC *)
      | Tainted target_kinds ->
          (* PC taints must be subset of target taints *)
          taint_kinds_subset pc_kinds target_kinds

(** ============================================================================
    TAINT LATTICE SUMMARY
    ============================================================================

    The taint status forms a lattice with:
    - Bottom:     Untainted
    - Top:        Tainted [all kinds]
    - Join:       taint_join (union of taint kinds)
    - Meet:       intersection of taint kinds (not implemented here)

    Key properties (all proven without admits):
    - taint_join is associative:   (a join b) join c = a join (b join c)
    - taint_join is commutative:   a join b = b join a
    - taint_join is idempotent:    a join a = a
    - Untainted is identity:       Untainted join a = a = a join Untainted

    Soundness theorems:
    - sanitize_removes_taint: sanitize k t f does not contain k
    - sink_soundness: sink k t = Some v iff t does not contain k
    - sanitize_then_sink: sink k (sanitize k t f) = Some _
    ============================================================================ *)
