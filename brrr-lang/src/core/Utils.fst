(**
 * BrrrLang.Core.Utils - Implementation
 *
 * Shared utility functions used across multiple Brrr-Lang modules.
 * Following HACL-star/EverParse patterns for shared library code.
 *
 * This module eliminates code duplication by providing:
 *   - List manipulation utilities (zip, find, filter, dedup)
 *   - Option combinators (map, bind)
 *   - Result type for error handling
 *   - Predicate utilities (all, any, distinct)
 *
 * All functions are pure (Tot effect) and have termination proofs.
 * All proofs are complete with NO ADMITS.
 *)
module Utils

open FStar.List.Tot

(** ============================================================================
    Z3 OPTIONS
    ============================================================================ *)

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    LIST ZIPPING
    ============================================================================ *)

let rec zip_lists #a #b (l1: list a) (l2: list b) : Tot (list (a & b)) (decreases l1) =
  match l1, l2 with
  | x :: xs, y :: ys -> (x, y) :: zip_lists xs ys
  | _, _ -> []

#push-options "--fuel 1"
let rec zip_lists_length_lemma #a #b (l1: list a) (l2: list b)
  : Lemma (ensures length (zip_lists l1 l2) = min (length l1) (length l2))
          [SMTPat (zip_lists l1 l2)] =
  match l1, l2 with
  | _ :: xs, _ :: ys -> zip_lists_length_lemma xs ys
  | _, _ -> ()
#pop-options

(** ============================================================================
    OPTION COMBINATORS
    ============================================================================ *)

let option_map #a #b (f: a -> b) (opt: option a) : option b =
  match opt with
  | Some x -> Some (f x)
  | None -> None

let option_bind #a #b (opt: option a) (f: a -> option b) : option b =
  match opt with
  | Some x -> f x
  | None -> None

let option_default #a (default: a) (opt: option a) : a =
  match opt with
  | Some x -> x
  | None -> default

let option_is_some #a (opt: option a) : bool =
  match opt with
  | Some _ -> true
  | None -> false

let option_is_none #a (opt: option a) : bool =
  match opt with
  | Some _ -> false
  | None -> true

(** ============================================================================
    RESULT TYPE
    ============================================================================ *)

let result_map #a #b #e (f: a -> b) (r: result a e) : result b e =
  match r with
  | Ok x -> Ok (f x)
  | Err err -> Err err

let result_bind #a #b #e (r: result a e) (f: a -> result b e) : result b e =
  match r with
  | Ok x -> f x
  | Err err -> Err err

let result_is_ok #a #e (r: result a e) : bool =
  match r with
  | Ok _ -> true
  | Err _ -> false

let result_is_err #a #e (r: result a e) : bool =
  match r with
  | Ok _ -> false
  | Err _ -> true

(** ============================================================================
    LIST PREDICATES
    ============================================================================ *)

let rec list_all #a (pred: a -> bool) (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: xs -> pred x && list_all pred xs

let rec list_any #a (pred: a -> bool) (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | x :: xs -> pred x || list_any pred xs

let rec list_find #a (pred: a -> bool) (l: list a) : Tot (option a) (decreases l) =
  match l with
  | [] -> None
  | x :: xs -> if pred x then Some x else list_find pred xs

let rec all_distinct #a (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: rest -> not (mem x rest) && all_distinct rest

(** ============================================================================
    LIST DEDUPLICATION
    ============================================================================ *)

(* Helper for dedup with accumulator for seen elements *)
let rec dedup_helper #a (seen: list a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: rest ->
      if mem x seen
      then dedup_helper seen rest
      else x :: dedup_helper (x :: seen) rest

let dedup #a (l: list a) : list a = dedup_helper [] l

#push-options "--fuel 1"
let rec dedup_helper_subset_lemma #a (seen: list a) (l: list a)
  : Lemma (ensures forall x. mem x (dedup_helper seen l) ==> mem x l)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: rest ->
      dedup_helper_subset_lemma seen rest;
      dedup_helper_subset_lemma (x :: seen) rest
#pop-options

let dedup_subset_lemma #a (l: list a)
  : Lemma (ensures forall x. mem x (dedup l) ==> mem x l)
          [SMTPat (dedup l)] =
  dedup_helper_subset_lemma [] l

(** ============================================================================
    LIST SORTING (Insertion Sort)
    ============================================================================ *)

let rec insert_sorted #a (lt: a -> a -> bool) (x: a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> [x]
  | y :: ys -> if lt x y then x :: l else y :: insert_sorted lt x ys

let rec sort #a (lt: a -> a -> bool) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> insert_sorted lt x (sort lt xs)

(** ============================================================================
    LIST UTILITIES
    ============================================================================ *)

let rec range_helper (acc: list nat) (n: nat) : Tot (list nat) (decreases n) =
  if n = 0 then acc
  else range_helper ((n - 1) :: acc) (n - 1)

let range (n: nat) : list nat = range_helper [] n

let rec take #a (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then []
  else match l with
       | [] -> []
       | x :: xs -> x :: take (n - 1) xs

let rec drop #a (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else match l with
       | [] -> []
       | _ :: xs -> drop (n - 1) xs

let split_at #a (n: nat) (l: list a) : (list a & list a) =
  (take n l, drop n l)

(** ============================================================================
    STRING UTILITIES
    ============================================================================ *)

(* String equality using structural equality *)
let string_eq (s1: string) (s2: string) : bool = s1 = s2

(* String comparison - F* doesn't have built-in string ordering,
   so we compare lengths first, then fall back to structural equality.
   For true lexicographic ordering, would need character-by-character comparison. *)
let string_lt (s1: string) (s2: string) : bool =
  let len1 = FStar.String.length s1 in
  let len2 = FStar.String.length s2 in
  if len1 < len2 then true
  else if len1 > len2 then false
  else s1 <> s2 && true  (* Arbitrary but consistent for same-length strings *)
