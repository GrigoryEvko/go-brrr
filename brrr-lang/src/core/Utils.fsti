(**
 * BrrrLang.Core.Utils - Interface
 *
 * Shared utility functions used across multiple Brrr-Lang modules.
 * Following HACL*/EverParse patterns for shared library code.
 *
 * This module eliminates code duplication by providing:
 *   - List manipulation utilities (zip, find, filter, dedup)
 *   - Option combinators (map, bind)
 *   - Result type for error handling
 *   - Predicate utilities (all, any, distinct)
 *
 * All functions are pure (Tot effect) and have termination proofs.
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

(** Zip two lists together, truncating to shorter length.

    @param l1 First list
    @param l2 Second list
    @returns List of pairs (x, y) where x from l1, y from l2

    Example: zip_lists [1;2;3] ["a";"b"] = [(1,"a"); (2,"b")]

    Termination: Decreases on l1 length. *)
val zip_lists : #a:Type -> #b:Type -> l1:list a -> l2:list b -> Tot (list (a & b)) (decreases l1)

(** Lemma: Length of zipped list equals minimum of input lengths. *)
val zip_lists_length_lemma : #a:Type -> #b:Type -> l1:list a -> l2:list b ->
  Lemma (ensures length (zip_lists l1 l2) = min (length l1) (length l2))
        [SMTPat (zip_lists l1 l2)]

(** ============================================================================
    OPTION COMBINATORS
    ============================================================================ *)

(** Map a function over an option value.

    @param f Function to apply
    @param opt Option to transform
    @returns Some (f x) if opt = Some x, None otherwise *)
val option_map : #a:Type -> #b:Type -> f:(a -> b) -> opt:option a -> Tot (option b)

(** Monadic bind for option.

    @param opt Option value
    @param f Function returning option
    @returns f x if opt = Some x, None otherwise *)
val option_bind : #a:Type -> #b:Type -> opt:option a -> f:(a -> option b) -> Tot (option b)

(** Get value from option with default.

    @param default Default value if None
    @param opt Option to unwrap
    @returns x if opt = Some x, default otherwise *)
val option_default : #a:Type -> default:a -> opt:option a -> Tot a

(** Check if option is Some. *)
val option_is_some : #a:Type -> opt:option a -> Tot bool

(** Check if option is None. *)
val option_is_none : #a:Type -> opt:option a -> Tot bool

(** ============================================================================
    RESULT TYPE
    ============================================================================ *)

(** Result type for computations that may fail.
    More informative than option - carries error information. *)
type result (a: Type) (e: Type) =
  | Ok : v:a -> result a e
  | Err : err:e -> result a e

(** Map a function over a successful result. *)
val result_map : #a:Type -> #b:Type -> #e:Type -> f:(a -> b) -> r:result a e -> Tot (result b e)

(** Monadic bind for result. *)
val result_bind : #a:Type -> #b:Type -> #e:Type -> r:result a e -> f:(a -> result b e) -> Tot (result b e)

(** Check if result is Ok. *)
val result_is_ok : #a:Type -> #e:Type -> r:result a e -> Tot bool

(** Check if result is Err. *)
val result_is_err : #a:Type -> #e:Type -> r:result a e -> Tot bool

(** ============================================================================
    LIST PREDICATES
    ============================================================================ *)

(** Check if all elements satisfy predicate.

    @param pred Predicate to test
    @param l List to check
    @returns true iff pred x holds for all x in l *)
val list_all : #a:Type -> pred:(a -> bool) -> l:list a -> Tot bool (decreases l)

(** Check if any element satisfies predicate.

    @param pred Predicate to test
    @param l List to check
    @returns true iff pred x holds for some x in l *)
val list_any : #a:Type -> pred:(a -> bool) -> l:list a -> Tot bool (decreases l)

(** Find first element satisfying predicate.

    @param pred Predicate to test
    @param l List to search
    @returns Some x for first x where pred x, None if not found *)
val list_find : #a:Type -> pred:(a -> bool) -> l:list a -> Tot (option a) (decreases l)

(** Check if all elements in list are distinct.

    @param l List to check
    @returns true iff no duplicates exist *)
val all_distinct : #a:eqtype -> l:list a -> Tot bool (decreases l)

(** ============================================================================
    LIST DEDUPLICATION
    ============================================================================ *)

(** Remove duplicates from list, preserving first occurrence order.

    @param l List to deduplicate
    @returns List with duplicates removed

    Example: dedup [1;2;1;3;2] = [1;2;3] *)
val dedup : #a:eqtype -> l:list a -> Tot (list a)

(** Lemma: Dedup produces subset of original. *)
val dedup_subset_lemma : #a:eqtype -> l:list a ->
  Lemma (ensures forall x. mem x (dedup l) ==> mem x l)
        [SMTPat (dedup l)]

(** ============================================================================
    LIST SORTING (Insertion Sort)
    ============================================================================

    Simple insertion sort for small lists. For large lists, consider
    merge sort. Used for canonical representations (e.g., effect rows). *)

(** Insert element into sorted list maintaining order.

    @param lt Less-than comparison function
    @param x Element to insert
    @param l Sorted list
    @returns Sorted list containing x *)
val insert_sorted : #a:Type -> lt:(a -> a -> bool) -> x:a -> l:list a -> Tot (list a) (decreases l)

(** Sort list using insertion sort.

    @param lt Less-than comparison function
    @param l List to sort
    @returns Sorted list

    Complexity: O(n^2) - suitable for small lists only. *)
val sort : #a:Type -> lt:(a -> a -> bool) -> l:list a -> Tot (list a) (decreases l)

(** ============================================================================
    LIST UTILITIES
    ============================================================================ *)

(** Generate range [0, n).

    @param n Upper bound (exclusive)
    @returns [0; 1; ...; n-1] *)
val range : n:nat -> Tot (list nat)

(** Take first n elements from list.

    @param n Number of elements to take
    @param l Source list
    @returns First n elements (or all if l shorter than n) *)
val take : #a:Type -> n:nat -> l:list a -> Tot (list a) (decreases n)

(** Drop first n elements from list.

    @param n Number of elements to drop
    @param l Source list
    @returns Remaining elements after dropping n *)
val drop : #a:Type -> n:nat -> l:list a -> Tot (list a) (decreases n)

(** Split list at position n.

    @param n Split position
    @param l List to split
    @returns (first n elements, remaining elements) *)
val split_at : #a:Type -> n:nat -> l:list a -> Tot (list a & list a)

(** ============================================================================
    STRING UTILITIES
    ============================================================================ *)

(** String equality (using built-in). *)
val string_eq : s1:string -> s2:string -> Tot bool

(** String comparison for sorting.
    Note: Returns true if s1 < s2 lexicographically.
    F* strings use built-in comparison. *)
val string_lt : s1:string -> s2:string -> Tot bool
