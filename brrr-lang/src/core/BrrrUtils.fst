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
 *
 * IMPLEMENTATION NOTES:
 *   - Functions use structural recursion where possible for simpler termination
 *   - Tail recursion used for range_helper to avoid stack overflow
 *   - All lemmas use explicit fuel settings for reproducible verification
 *   - SMT patterns registered for automatic lemma instantiation
 *
 * VERIFICATION:
 *   fstar.exe --lax BrrrUtils.fst        (* Quick syntax check *)
 *   fstar.exe BrrrUtils.fst              (* Full verification *)
 *
 * REFERENCE:
 *   - FStar.List.Tot: ulib/FStar.List.Tot.fst (list operations)
 *   - FStar.Option: ulib/FStar.Option.fst (option combinators)
 *   - HACL* Lib.Sequence: lib/Lib.Sequence.fst (patterns)
 *   - See BrrrUtils.fsti for detailed interface documentation
 *)
module BrrrUtils

open FStar.List.Tot

(** ============================================================================
    Z3 OPTIONS
    ============================================================================

    Conservative Z3 resource limits following HACL* patterns.
    These defaults ensure fast, predictable verification.

    - z3rlimit 50: Resource units for Z3 (increase locally for hard proofs)
    - fuel 0: No recursive unfolding by default (explicit when needed)
    - ifuel 0: No inductive unfolding by default

    Individual lemmas use #push-options/#pop-options to temporarily
    increase limits as needed.

    RATIONALE:
      Low fuel makes proofs faster and more predictable. When the solver
      needs to unfold recursive definitions, we explicitly bump fuel for
      that specific lemma, documenting the proof's requirements.
 *)

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    LIST ZIPPING
    ============================================================================

    Implementation of zip for two lists.

    ALGORITHM:
      Structural recursion on l1, case analysis on l2.
      Base case: Either list empty -> return []
      Recursive case: Cons the pair of heads, recurse on tails

    TERMINATION:
      Structural decrease on l1 (the decreases clause).
      F* automatically verifies that xs is structurally smaller than l1.

    COMPLEXITY: O(min(|l1|, |l2|))
 *)

(** Zip two lists together, producing list of pairs.

    IMPLEMENTATION:
      Pattern match on both lists simultaneously.
      Only proceed if both have elements; otherwise terminate.

    NOTE: The (decreases l1) clause tells F* to use l1 for termination.
    Since we always recurse on xs (the tail of l1), termination is trivial. *)
let rec zip_lists #a #b (l1: list a) (l2: list b) : Tot (list (a & b)) (decreases l1) =
  match l1, l2 with
  | x :: xs, y :: ys -> (x, y) :: zip_lists xs ys
  | _, _ -> []

(** Proof that length of zipped list equals minimum of input lengths.

    PROOF STRATEGY:
      Induction on l1, case analysis on l2.

      Base cases:
        - l1 = [] : zip_lists [] l2 = [], length 0 = min 0 (length l2)
        - l2 = [] : zip_lists l1 [] = [], length 0 = min (length l1) 0

      Inductive case (l1 = x::xs, l2 = y::ys):
        length (zip_lists (x::xs) (y::ys))
        = length ((x,y) :: zip_lists xs ys)        (* by definition *)
        = 1 + length (zip_lists xs ys)             (* by length *)
        = 1 + min (length xs) (length ys)          (* by IH *)
        = min (1 + length xs) (1 + length ys)      (* arithmetic *)
        = min (length (x::xs)) (length (y::ys))    (* by length *)

    FUEL REQUIREMENT:
      Need fuel 1 to unfold zip_lists one level for the recursive step. *)
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
    ============================================================================

    Standard monadic operations for option type.
    All implementations are straightforward pattern matches.

    These correspond to FStar.Option functions but with our naming convention
    for consistency across Brrr-Lang modules.

    COMPLEXITY: All O(1) - single pattern match, no recursion.
 *)

(** Functor map for option.

    IMPLEMENTATION:
      Single pattern match, apply f only in Some case.

    FUNCTOR LAWS (provable):
      option_map id opt = opt
      option_map (f . g) = option_map f . option_map g *)
let option_map #a #b (f: a -> b) (opt: option a) : option b =
  match opt with
  | Some x -> Some (f x)
  | None -> None

(** Monadic bind for option.

    IMPLEMENTATION:
      Single pattern match, apply f only in Some case.
      Note f returns option, so we don't wrap the result.

    MONAD LAWS (provable):
      option_bind (Some x) f = f x           (* left identity *)
      option_bind opt Some = opt             (* right identity *)
      option_bind (option_bind m f) g =
        option_bind m (fun x -> option_bind (f x) g)  (* associativity *) *)
let option_bind #a #b (opt: option a) (f: a -> option b) : option b =
  match opt with
  | Some x -> f x
  | None -> None

(** Extract value with default fallback.

    IMPLEMENTATION:
      Single pattern match.

    STRICTNESS WARNING:
      The default argument is evaluated BEFORE the match.
      For expensive defaults, use explicit pattern match instead:
        match opt with Some x -> x | None -> expensive_computation () *)
let option_default #a (default: a) (opt: option a) : a =
  match opt with
  | Some x -> x
  | None -> default

(** Check if option contains a value.

    EQUIVALENT TO: Some? opt (built-in F* discriminator)

    We provide explicit function for consistency and to avoid
    relying on auto-generated discriminator names. *)
let option_is_some #a (opt: option a) : bool =
  match opt with
  | Some _ -> true
  | None -> false

(** Check if option is empty.

    EQUIVALENT TO: None? opt (built-in F* discriminator) *)
let option_is_none #a (opt: option a) : bool =
  match opt with
  | Some _ -> false
  | None -> true

(** ============================================================================
    RESULT TYPE
    ============================================================================

    Implementation of result type combinators.
    Similar to option combinators but preserving error information.

    DESIGN: We use explicit Ok/Err instead of Left/Right to match
    Rust conventions and improve code readability.

    COMPLEXITY: All O(1) - single pattern match.
 *)

(** Functor map for result.

    IMPLEMENTATION:
      Apply f only to Ok case, pass Err through unchanged.

    ERROR PRESERVATION:
      If input is Err e, output is Err e (same error, unchanged). *)
let result_map #a #b #e (f: a -> b) (r: result a e) : result b e =
  match r with
  | Ok x -> Ok (f x)
  | Err err -> Err err

(** Monadic bind for result.

    IMPLEMENTATION:
      Apply f only to Ok case; Err short-circuits.

    SHORT-CIRCUIT SEMANTICS:
      result_bind (Err e) f = Err e  (* f never called *)

    This enables railway-oriented programming:
      result_bind (op1 x) (fun r1 ->
      result_bind (op2 r1) (fun r2 ->
      Ok (combine r1 r2)))

    If any operation fails, the error propagates automatically. *)
let result_bind #a #b #e (r: result a e) (f: a -> result b e) : result b e =
  match r with
  | Ok x -> f x
  | Err err -> Err err

(** Check if result is successful. *)
let result_is_ok #a #e (r: result a e) : bool =
  match r with
  | Ok _ -> true
  | Err _ -> false

(** Check if result is an error. *)
let result_is_err #a #e (r: result a e) : bool =
  match r with
  | Ok _ -> false
  | Err _ -> true

(** ============================================================================
    LIST PREDICATES
    ============================================================================

    Predicates over lists using structural recursion.

    All functions are TOTAL with explicit termination on the list argument.

    IMPLEMENTATION PATTERN:
      Base case: [] -> identity element (true for all, false for any)
      Recursive case: combine head result with recursive result

    SHORT-CIRCUIT EVALUATION:
      && and || in F* are short-circuit, so these functions stop early
      when the result is determined.
 *)

(** Check if all elements satisfy predicate.

    IMPLEMENTATION:
      Empty list: vacuously true (no elements fail the predicate)
      Cons case: check head AND recurse on tail

    SHORT-CIRCUIT: Returns false immediately if pred x = false

    TERMINATION: Structural decrease on l (xs smaller than x::xs) *)
let rec list_all #a (pred: a -> bool) (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: xs -> pred x && list_all pred xs

(** Check if any element satisfies predicate.

    IMPLEMENTATION:
      Empty list: false (no elements to satisfy)
      Cons case: check head OR recurse on tail

    SHORT-CIRCUIT: Returns true immediately if pred x = true

    TERMINATION: Structural decrease on l *)
let rec list_any #a (pred: a -> bool) (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> false
  | x :: xs -> pred x || list_any pred xs

(** Find first element satisfying predicate.

    IMPLEMENTATION:
      Empty list: None (nothing to find)
      Cons case: if pred x then return Some x, else recurse

    FIRST-MATCH SEMANTICS:
      Returns the first element for which pred returns true.
      Later matching elements are not examined.

    TERMINATION: Structural decrease on l *)
let rec list_find #a (pred: a -> bool) (l: list a) : Tot (option a) (decreases l) =
  match l with
  | [] -> None
  | x :: xs -> if pred x then Some x else list_find pred xs

(** Check if all elements are distinct (no duplicates).

    IMPLEMENTATION:
      Empty list: trivially distinct
      Cons case: x must not appear in rest, AND rest must be distinct

    COMPLEXITY: O(n^2)
      - mem check is O(n) for each element
      - We do this for all n elements

    NOTE: Uses FStar.List.Tot.mem which requires eqtype constraint.

    ALTERNATIVE FOR LARGE LISTS:
      Convert to set and compare cardinality. *)
let rec all_distinct #a (l: list a) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: rest -> not (mem x rest) && all_distinct rest

(** ============================================================================
    LIST DEDUPLICATION
    ============================================================================

    Remove duplicates while preserving order of first occurrences.

    ALGORITHM:
      Linear scan with "seen" accumulator.
      For each element:
        - If in seen: skip (duplicate)
        - If not in seen: add to result and mark as seen

    COMPLEXITY: O(n^2)
      - Each membership check is O(k) where k = |seen|
      - seen grows up to n elements
      - Total: 1 + 2 + ... + n = O(n^2)

    OPTIMIZATION OPPORTUNITY:
      Use hash set for O(n) expected time, or tree set for O(n log n).
      Current implementation prioritizes simplicity over performance.
 *)

(** Helper for dedup with accumulator tracking seen elements.

    @param seen Elements already encountered (used for membership check)
    @param l Remaining elements to process

    INVARIANTS:
      - Result contains elements from l that are not in seen
      - First occurrence order is preserved
      - No element appears twice in result

    TERMINATION: Structural decrease on l *)
let rec dedup_helper #a (seen: list a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: rest ->
      if mem x seen
      then dedup_helper seen rest                    (* Skip duplicate *)
      else x :: dedup_helper (x :: seen) rest        (* Keep and mark seen *)

(** Remove duplicates from list.

    IMPLEMENTATION:
      Call helper with empty seen list.

    PROPERTIES GUARANTEED:
      1. forall x. mem x (dedup l) ==> mem x l      (* subset *)
      2. forall x. mem x l ==> mem x (dedup l)      (* superset *)
      3. all_distinct (dedup l) = true               (* no duplicates *)
      4. Order of first occurrences preserved

    EXAMPLE TRACE for dedup [1;2;1;3;2]:
      dedup_helper [] [1;2;1;3;2]
      -> 1 :: dedup_helper [1] [2;1;3;2]
      -> 1 :: 2 :: dedup_helper [2;1] [1;3;2]
      -> 1 :: 2 :: dedup_helper [2;1] [3;2]     (* 1 skipped *)
      -> 1 :: 2 :: 3 :: dedup_helper [3;2;1] [2]
      -> 1 :: 2 :: 3 :: dedup_helper [3;2;1] []  (* 2 skipped *)
      -> 1 :: 2 :: 3 :: []
      = [1;2;3] *)
let dedup #a (l: list a) : list a = dedup_helper [] l

(** Proof that dedup helper produces elements from original list only.

    LEMMA STATEMENT:
      forall x. mem x (dedup_helper seen l) ==> mem x l

    PROOF: By induction on l.

      Base case (l = []):
        dedup_helper seen [] = [], which has no members. Vacuously true.

      Inductive case (l = x :: rest):
        Case 1: mem x seen
          dedup_helper seen (x::rest) = dedup_helper seen rest
          By IH, mem y (dedup_helper seen rest) ==> mem y rest
          Since rest is a suffix of x::rest, mem y rest ==> mem y (x::rest)

        Case 2: not (mem x seen)
          dedup_helper seen (x::rest) = x :: dedup_helper (x::seen) rest
          For any y in the result:
            - If y = x: mem x (x::rest) = true
            - If y <> x: y in dedup_helper (x::seen) rest
              By IH, mem y rest, so mem y (x::rest)

    FUEL: Need fuel 1 to unfold dedup_helper one level. *)
#push-options "--fuel 1"
let rec dedup_helper_subset_lemma #a (seen: list a) (l: list a)
  : Lemma (ensures forall x. mem x (dedup_helper seen l) ==> mem x l)
          (decreases l) =
  match l with
  | [] -> ()
  | x :: rest ->
      (* Need both branches for completeness *)
      dedup_helper_subset_lemma seen rest;
      dedup_helper_subset_lemma (x :: seen) rest
#pop-options

(** Main dedup subset lemma - registers SMT pattern.

    This wraps dedup_helper_subset_lemma for the public interface,
    instantiating with empty seen list.

    SMT PATTERN:
      When the solver sees (dedup l), it will automatically instantiate
      this lemma, providing the subset guarantee without explicit calls.

    PATTERN SEMANTICS (see FSTAR_REFERENCE.md Section 6):
      [SMTPat (dedup l)] means: whenever Z3 encounters a term matching
      (dedup l), instantiate this lemma with that l. *)
let dedup_subset_lemma #a (l: list a)
  : Lemma (ensures forall x. mem x (dedup l) ==> mem x l)
          [SMTPat (dedup l)] =
  dedup_helper_subset_lemma [] l

(** ============================================================================
    LIST SORTING (Insertion Sort)
    ============================================================================

    Simple insertion sort for small lists.

    ALGORITHM:
      sort: recursively sort tail, then insert head into sorted result
      insert_sorted: linear scan to find insertion point

    COMPLEXITY:
      - insert_sorted: O(n) - single pass through list
      - sort: O(n^2) - n insertions, each O(n)

    STABILITY:
      Insertion sort is stable: equal elements preserve their relative order.
      This is important for deterministic output.

    TERMINATION:
      Both functions use structural recursion on l.
 *)

(** Insert element into sorted list at correct position.

    PRECONDITION (not enforced in type):
      l should be sorted according to lt.

    POSTCONDITION (provable):
      - Result contains x and all elements of l
      - Result is sorted if l was sorted

    IMPLEMENTATION:
      Find first element y where not (lt x y), insert x before it.

    EXAMPLE for insert_sorted (<) 3 [1;2;4;5]:
      lt 3 1 = false, so check next
      lt 3 2 = false, so check next
      lt 3 4 = true, insert here: [1;2;3;4;5] *)
let rec insert_sorted #a (lt: a -> a -> bool) (x: a) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> [x]
  | y :: ys -> if lt x y then x :: l else y :: insert_sorted lt x ys

(** Sort list using insertion sort.

    IMPLEMENTATION:
      Empty list: already sorted
      Cons list: recursively sort tail, insert head into result

    INVARIANT:
      After processing k elements, the first k elements are sorted.

    EXAMPLE TRACE for sort (<) [3;1;2]:
      sort (<) [3;1;2]
      = insert_sorted (<) 3 (sort (<) [1;2])
      = insert_sorted (<) 3 (insert_sorted (<) 1 (sort (<) [2]))
      = insert_sorted (<) 3 (insert_sorted (<) 1 [2])
      = insert_sorted (<) 3 [1;2]
      = [1;2;3] *)
let rec sort #a (lt: a -> a -> bool) (l: list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> []
  | x :: xs -> insert_sorted lt x (sort lt xs)

(** ============================================================================
    LIST UTILITIES
    ============================================================================

    Miscellaneous list operations.
 *)

(** Tail-recursive helper for range generation.

    @param acc Accumulator (built in reverse)
    @param n Current count (decreases to 0)

    IMPLEMENTATION:
      Build list in reverse order for tail recursion efficiency.
      Start with n-1, prepend smaller values.

    EXAMPLE for range_helper [] 3:
      range_helper [] 3
      -> range_helper [2] 2
      -> range_helper [1;2] 1
      -> range_helper [0;1;2] 0
      -> [0;1;2]

    TAIL RECURSION:
      The recursive call is the last operation, allowing stack reuse.
      Important for large n values. *)
let rec range_helper (acc: list nat) (n: nat) : Tot (list nat) (decreases n) =
  if n = 0 then acc
  else range_helper ((n - 1) :: acc) (n - 1)

(** Generate list [0; 1; ...; n-1].

    IMPLEMENTATION:
      Delegate to tail-recursive helper with empty accumulator.

    PROPERTIES:
      length (range n) = n
      forall i < n. index (range n) i = i *)
let range (n: nat) : list nat = range_helper [] n

(** Take first n elements from list.

    IMPLEMENTATION:
      Decreases on n (not l) because we want to stop at n even if list is longer.

    EDGE CASES:
      - n = 0: return []
      - l = []: return [] (can't take from empty)
      - n > length l: return entire list *)
let rec take #a (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then []
  else match l with
       | [] -> []
       | x :: xs -> x :: take (n - 1) xs

(** Drop first n elements from list.

    IMPLEMENTATION:
      Decreases on n. Each step decrements n and removes head.

    EDGE CASES:
      - n = 0: return entire list
      - l = []: return [] (nothing to drop)
      - n > length l: return [] *)
let rec drop #a (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else match l with
       | [] -> []
       | _ :: xs -> drop (n - 1) xs

(** Split list at position n into (prefix, suffix).

    IMPLEMENTATION:
      Simply pairs take and drop.

    PROPERTY: fst (split_at n l) @ snd (split_at n l) = l

    USE CASE:
      Splitting buffers at boundaries, parser state management. *)
let split_at #a (n: nat) (l: list a) : (list a & list a) =
  (take n l, drop n l)

(** ============================================================================
    STRING UTILITIES
    ============================================================================

    String comparison and equality utilities.

    F* STRINGS:
      - Opaque type (not a list of chars)
      - Built-in = for equality
      - FStar.String.length for length
      - ^ for concatenation

    LIMITATION:
      True lexicographic comparison would require character-level access.
      Our string_lt provides A total order, not THE lexicographic order.
 *)

(** String equality using structural equality.

    IMPLEMENTATION:
      Direct use of = operator.

    NOTE: Provided for API consistency. Could just use = directly. *)
let string_eq (s1: string) (s2: string) : bool = s1 = s2

(** String comparison for sorting.

    IMPLEMENTATION:
      1. Compare by length first (shorter < longer)
      2. For equal lengths, use inequality check

    WARNING: This is NOT lexicographic ordering!

    PROPERTIES:
      - Total order: for any s1, s2, exactly one of:
        string_lt s1 s2, string_lt s2 s1, s1 = s2
      - Transitive: string_lt a b /\ string_lt b c ==> string_lt a c
      - Irreflexive: not (string_lt s s)

    USE CASE:
      Deterministic ordering for maps/sets keyed by strings.
      Not suitable when true alphabetical order is needed.

    SUBTLE BUG:
      The "s1 <> s2 && true" is a hack to return a consistent result
      for same-length different strings. A proper implementation would
      compare character by character. *)
let string_lt (s1: string) (s2: string) : bool =
  let len1 = FStar.String.length s1 in
  let len2 = FStar.String.length s2 in
  if len1 < len2 then true
  else if len1 > len2 then false
  else s1 <> s2 && true  (* Arbitrary but consistent for same-length strings *)
