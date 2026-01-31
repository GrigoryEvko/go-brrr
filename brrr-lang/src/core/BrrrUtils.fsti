(**
 * BrrrLang.Core.Utils - Interface
 *
 * Shared utility functions used across multiple Brrr-Lang modules.
 * Following HACL-star/EverParse patterns for shared library code (see Lib.Sequence).
 *
 * This module eliminates code duplication by providing:
 *   - List manipulation utilities (zip, find, filter, dedup)
 *   - Option combinators (map, bind)
 *   - Result type for error handling
 *   - Predicate utilities (all, any, distinct)
 *
 * All functions are pure (Tot effect) and have termination proofs.
 *
 * DESIGN PRINCIPLES:
 *   1. All functions are TOTAL - no exceptions, no divergence
 *   2. Follows FStar.List.Tot patterns for list operations
 *   3. Follows FStar.Option patterns for option combinators
 *   4. Provides SMT patterns where beneficial for proof automation
 *   5. Explicit termination measures via (decreases ...) clauses
 *
 * F* STANDARD LIBRARY CORRESPONDENCE:
 *   - list_all     ~ FStar.List.Tot.for_all
 *   - list_any     ~ FStar.List.Tot.existsb
 *   - list_find    ~ FStar.List.Tot.find (but returns option, not refined)
 *   - dedup        ~ similar to FStar.List.Tot.noRepeats check + filter
 *   - option_map   ~ FStar.Option.mapTot
 *   - option_bind  ~ monadic bind for option
 *   - zip_lists    ~ custom (FStar has no standard zip)
 *
 * RATIONALE FOR CUSTOM IMPLEMENTATIONS:
 *   - zip_lists: FStar.List.Tot lacks a zip function
 *   - dedup: No efficient deduplication in FStar stdlib
 *   - list_find: Our version returns plain option, not refined option
 *   - result type: FStar uses Either, we prefer explicit Ok/Err names
 *
 * REFERENCE:
 *   - FStar.List.Tot: ulib/FStar.List.Tot.fst
 *   - FStar.Option: ulib/FStar.Option.fst
 *   - FStar.Seq: ulib/FStar.Seq.fst (for sequence lemma patterns)
 *   - HACL* Lib.Sequence: lib/Lib.Sequence.fst (documentation patterns)
 *   - Brrr-Lang Spec v0.4, Section "Type Primitives" (utility usage)
 *
 * VERIFICATION STATUS: All proofs complete, NO ADMITS
 *)
module BrrrUtils

open FStar.List.Tot

(** ============================================================================
    Z3 OPTIONS
    ============================================================================

    Conservative Z3 resource limits following HACL* patterns:
      - z3rlimit 50: Sufficient for most lemmas, increase locally if needed
      - fuel 0: Minimal recursive unfolding (faster, more predictable)
      - ifuel 0: Minimal inductive unfolding

    These defaults ensure fast verification. Individual lemmas may
    use #push-options to temporarily increase limits.

    See: FSTAR_REFERENCE.md Section 13 "Fuel Control"
 *)

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    LIST ZIPPING
    ============================================================================

    Zips two lists together into a list of pairs. Unlike Haskell's zip,
    F* standard library lacks this operation, so we provide it here.

    SPECIFICATION:
      zip_lists [a1;a2;a3] [b1;b2] = [(a1,b1); (a2,b2)]

    The result length is min(length l1, length l2), i.e., we truncate
    to the shorter list's length.

    COMPLEXITY: O(min(n, m)) where n = length l1, m = length l2

    TERMINATION: Structural recursion on l1
 *)

(** Zip two lists together, truncating to shorter length.

    @param l1 First list of type 'a
    @param l2 Second list of type 'b
    @returns List of pairs (x, y) where x from l1, y from l2

    Example:
      zip_lists [1;2;3] ["a";"b"] = [(1,"a"); (2,"b")]
      zip_lists [] [1;2;3] = []
      zip_lists [1;2] [] = []

    Termination: Decreases on l1 length (structural recursion).

    Note: Unlike some languages, this does NOT raise an error for
    mismatched lengths - it simply truncates to the shorter list. *)
val zip_lists : #a:Type -> #b:Type -> l1:list a -> l2:list b -> Tot (list (a & b)) (decreases l1)

(** Lemma: Length of zipped list equals minimum of input lengths.

    This lemma is registered as an SMT pattern, so the solver will
    automatically instantiate it when zip_lists appears in goals.

    MATHEMATICAL STATEMENT:
      forall l1 l2. length (zip_lists l1 l2) = min (length l1) (length l2)

    PROOF: By induction on l1, case analysis on l2.

    SMT PATTERN: Triggers on (zip_lists l1 l2) - see FSTAR_REFERENCE.md
    Section 6 "SMT Patterns" for pattern semantics. *)
val zip_lists_length_lemma : #a:Type -> #b:Type -> l1:list a -> l2:list b ->
  Lemma (ensures length (zip_lists l1 l2) = min (length l1) (length l2))
        [SMTPat (zip_lists l1 l2)]

(** ============================================================================
    OPTION COMBINATORS
    ============================================================================

    Monadic operations for the option type, following FStar.Option patterns.

    The option type in F* is defined as:
      type option a = | None : option a | Some : v:a -> option a

    These combinators allow chaining optional computations without
    explicit pattern matching at each step.

    MONAD LAWS (option satisfies):
      1. Left identity:  option_bind (Some x) f  =  f x
      2. Right identity: option_bind opt Some    =  opt
      3. Associativity:  option_bind (option_bind m f) g  =
                         option_bind m (fun x -> option_bind (f x) g)

    FUNCTOR LAW (option_map satisfies):
      option_map id opt = opt
      option_map (f . g) opt = option_map f (option_map g opt)

    REFERENCE: FStar.Option module (ulib/FStar.Option.fst)

    COMPLEXITY: All O(1) - single pattern match
 *)

(** Map a function over an option value.

    This is the Functor 'fmap' operation for option.

    @param f Function to apply: a -> b
    @param opt Option to transform
    @returns Some (f x) if opt = Some x, None otherwise

    Example:
      option_map (fun x -> x + 1) (Some 5) = Some 6
      option_map (fun x -> x + 1) None = None

    Corresponds to: FStar.Option.mapTot *)
val option_map : #a:Type -> #b:Type -> f:(a -> b) -> opt:option a -> Tot (option b)

(** Monadic bind for option.

    This is the Monad 'bind' (>>=) operation for option.
    Chains computations that may fail.

    @param opt Option value
    @param f Function returning option: a -> option b
    @returns f x if opt = Some x, None otherwise

    Example:
      option_bind (Some 5) (fun x -> Some (x + 1)) = Some 6
      option_bind (Some 5) (fun _ -> None) = None
      option_bind None (fun x -> Some (x + 1)) = None

    Use case: Chaining dictionary lookups
      option_bind (lookup k1 dict1) (fun v1 ->
      option_bind (lookup v1 dict2) (fun v2 ->
      Some (process v1 v2)))

    Note: F* also supports let? syntax in some contexts for this pattern. *)
val option_bind : #a:Type -> #b:Type -> opt:option a -> f:(a -> option b) -> Tot (option b)

(** Get value from option with default.

    Safe unwrapping that provides a fallback value for None case.

    @param default Default value to return if opt is None
    @param opt Option to unwrap
    @returns x if opt = Some x, default otherwise

    Example:
      option_default 0 (Some 5) = 5
      option_default 0 None = 0

    Corresponds to: FStar.Option.dflt

    WARNING: The default is always evaluated (strict evaluation).
    For expensive defaults, consider pattern matching instead. *)
val option_default : #a:Type -> default:a -> opt:option a -> Tot a

(** Check if option is Some.

    @param opt Option to test
    @returns true iff opt = Some _

    Equivalent to: Some? opt (F* built-in discriminator)

    PROPERTY: option_is_some opt = not (option_is_none opt) *)
val option_is_some : #a:Type -> opt:option a -> Tot bool

(** Check if option is None.

    @param opt Option to test
    @returns true iff opt = None

    Equivalent to: None? opt (F* built-in discriminator)

    PROPERTY: option_is_none opt = not (option_is_some opt) *)
val option_is_none : #a:Type -> opt:option a -> Tot bool

(** ============================================================================
    RESULT TYPE
    ============================================================================

    Result type for computations that may fail with an error value.
    More informative than option - carries error information.

    This is similar to Rust's Result<T, E> or Haskell's Either.

    DESIGN CHOICE: We use explicit Ok/Err constructors rather than
    Left/Right (as in FStar.Either) for better readability and to
    match Rust conventions (important for Brrr-Lang's multi-language
    interop goals).

    MONAD LAWS (result satisfies for fixed error type):
      1. Left identity:  result_bind (Ok x) f  =  f x
      2. Right identity: result_bind r Ok      =  r
      3. Associativity:  result_bind (result_bind m f) g  =
                         result_bind m (fun x -> result_bind (f x) g)

    USAGE IN BRRR-LANG:
      - Type checking returns result expr type_error
      - Parsing returns result ast parse_error
      - Evaluation returns result value runtime_error

    COMPLEXITY: All operations O(1)
 *)

(** Result type for computations that may fail.

    @param a Success value type
    @param e Error value type

    Example:
      type parse_result = result ast string
      let parse s = if valid s then Ok (make_ast s) else Err "syntax error"
 *)
type result (a: Type) (e: Type) =
  | Ok : v:a -> result a e
  | Err : err:e -> result a e

(** Map a function over a successful result.

    Applies f only to Ok values, passes through Err unchanged.

    @param f Function to apply to success value
    @param r Result to transform
    @returns Ok (f x) if r = Ok x, Err err if r = Err err

    This is the Functor 'fmap' for result. *)
val result_map : #a:Type -> #b:Type -> #e:Type -> f:(a -> b) -> r:result a e -> Tot (result b e)

(** Monadic bind for result.

    Chains computations that may fail. Short-circuits on first error.

    @param r Result value
    @param f Function returning result: a -> result b e
    @returns f x if r = Ok x, Err err if r = Err err

    Example:
      result_bind (parse input) (fun ast ->
      result_bind (typecheck ast) (fun typed ->
      Ok (compile typed)))

    Error propagation: If parse fails, typecheck is never called. *)
val result_bind : #a:Type -> #b:Type -> #e:Type -> r:result a e -> f:(a -> result b e) -> Tot (result b e)

(** Check if result is Ok. *)
val result_is_ok : #a:Type -> #e:Type -> r:result a e -> Tot bool

(** Check if result is Err. *)
val result_is_err : #a:Type -> #e:Type -> r:result a e -> Tot bool

(** ============================================================================
    LIST PREDICATES
    ============================================================================

    Predicates over lists, following FStar.List.Tot patterns.

    These functions apply a predicate to list elements and compute
    a boolean result. All are TOTAL and have explicit termination
    measures.

    CORRESPONDENCE TO STDLIB:
      list_all  ~ FStar.List.Tot.for_all
      list_any  ~ FStar.List.Tot.existsb
      list_find ~ FStar.List.Tot.find (but different return type)

    WHY CUSTOM VERSIONS?
      1. Consistent naming across Brrr-Lang modules
      2. Explicit termination measures in signatures
      3. list_find returns option a, not option (x:a{f x})
         (the refined return type complicates some use cases)

    COMPLEXITY:
      - list_all, list_any: O(n) in list length, short-circuits
      - list_find: O(n) worst case, O(1) best case (found at head)
      - all_distinct: O(n^2) due to nested membership checks
 *)

(** Check if all elements satisfy predicate.

    @param pred Predicate to test: a -> bool
    @param l List to check
    @returns true iff pred x holds for ALL x in l

    PROPERTIES:
      list_all pred [] = true                              (* vacuously true *)
      list_all pred (x::xs) = pred x && list_all pred xs   (* recursive def *)

    SHORT-CIRCUIT: Returns false as soon as pred returns false.

    Example:
      list_all (fun x -> x > 0) [1;2;3] = true
      list_all (fun x -> x > 0) [1;-2;3] = false
      list_all (fun _ -> false) [] = true  (* empty list case! *)

    Corresponds to: FStar.List.Tot.for_all *)
val list_all : #a:Type -> pred:(a -> bool) -> l:list a -> Tot bool (decreases l)

(** Check if any element satisfies predicate.

    @param pred Predicate to test: a -> bool
    @param l List to check
    @returns true iff pred x holds for SOME x in l

    PROPERTIES:
      list_any pred [] = false                             (* no elements *)
      list_any pred (x::xs) = pred x || list_any pred xs   (* recursive def *)

    DUALITY: list_any pred l = not (list_all (fun x -> not (pred x)) l)

    SHORT-CIRCUIT: Returns true as soon as pred returns true.

    Example:
      list_any (fun x -> x > 0) [-1;2;-3] = true
      list_any (fun x -> x > 0) [-1;-2;-3] = false
      list_any (fun _ -> true) [] = false  (* empty list case! *)

    Corresponds to: FStar.List.Tot.existsb *)
val list_any : #a:Type -> pred:(a -> bool) -> l:list a -> Tot bool (decreases l)

(** Find first element satisfying predicate.

    @param pred Predicate to test: a -> bool
    @param l List to search
    @returns Some x for first x where pred x = true, None if not found

    PROPERTIES:
      list_find pred [] = None
      list_find pred (x::xs) = if pred x then Some x else list_find pred xs

    FOUNDEDNESS:
      If list_find pred l = Some x, then:
        1. x is in l (mem x l = true)
        2. pred x = true
        3. x is the FIRST such element (all earlier elements fail pred)

    Example:
      list_find (fun x -> x > 5) [1;2;7;8] = Some 7
      list_find (fun x -> x > 10) [1;2;7;8] = None

    DIFFERENCE FROM FStar.List.Tot.find:
      FStar's find returns: option (x:a{f x})
      Ours returns: option a

      The refined return type is useful for proofs but can complicate
      code that just wants to check existence. *)
val list_find : #a:Type -> pred:(a -> bool) -> l:list a -> Tot (option a) (decreases l)

(** Check if all elements in list are distinct.

    Requires 'a to be an eqtype (decidable equality).

    @param l List to check
    @returns true iff no duplicates exist

    DEFINITION:
      all_distinct [] = true
      all_distinct (x::xs) = not (mem x xs) && all_distinct xs

    PROPERTIES:
      all_distinct l = true  <==>  length (dedup l) = length l
      all_distinct l = true  <==>  forall i j. i <> j ==> l[i] <> l[j]

    COMPLEXITY: O(n^2) where n = length l
      - For each element, we check membership in the tail: O(n)
      - We do this for all n elements
      - Consider using a set-based approach for large lists

    Example:
      all_distinct [1;2;3] = true
      all_distinct [1;2;1] = false
      all_distinct [] = true *)
val all_distinct : #a:eqtype -> l:list a -> Tot bool (decreases l)

(** ============================================================================
    LIST DEDUPLICATION
    ============================================================================

    Remove duplicates from a list while preserving first-occurrence order.

    ALGORITHM: Linear scan with "seen" set (implemented as list).
    For each element, check if already seen; if not, add to result
    and mark as seen.

    COMPLEXITY: O(n^2) where n = length l
      - For each element, membership check in seen list is O(n)
      - Consider using FStar.Set for O(n log n) if performance critical

    PROPERTIES:
      1. SUBSET: forall x. mem x (dedup l) ==> mem x l
      2. SUPERSET: forall x. mem x l ==> mem x (dedup l)
         (combined with 1: same elements, just unique)
      3. NO DUPLICATES: all_distinct (dedup l) = true
      4. ORDER PRESERVED: first occurrence order maintained
      5. IDEMPOTENT: dedup (dedup l) = dedup l

    NOTE: Requires eqtype constraint for membership testing.
 *)

(** Remove duplicates from list, preserving first occurrence order.

    @param l List to deduplicate (requires eqtype for equality)
    @returns List with duplicates removed

    SPECIFICATION:
      - Output contains exactly the unique elements of input
      - Order matches first occurrence in input

    Example:
      dedup [1;2;1;3;2;4] = [1;2;3;4]
      dedup [3;1;4;1;5;9;2;6;5] = [3;1;4;5;9;2;6]
      dedup [] = []
      dedup [1] = [1]

    Implementation uses helper with accumulator for seen elements.
    See dedup_helper in BrrrUtils.fst for details. *)
val dedup : #a:eqtype -> l:list a -> Tot (list a)

(** Lemma: Dedup produces subset of original.

    STATEMENT: forall x. mem x (dedup l) ==> mem x l

    This lemma establishes that dedup never introduces new elements.
    Combined with the converse (which also holds), dedup preserves
    the SET of elements while removing duplicates.

    PROOF: By induction on l, using helper lemma for dedup_helper.

    SMT PATTERN: Triggers when (dedup l) appears in goal. *)
val dedup_subset_lemma : #a:eqtype -> l:list a ->
  Lemma (ensures forall x. mem x (dedup l) ==> mem x l)
        [SMTPat (dedup l)]

(** ============================================================================
    LIST SORTING (Insertion Sort)
    ============================================================================

    Simple insertion sort implementation for small lists.

    WHY INSERTION SORT?
      - Simple to verify (proof is straightforward induction)
      - O(1) extra space (in-place conceptually)
      - Excellent for small lists (< ~20 elements)
      - Stable sort (preserves relative order of equal elements)

    COMPLEXITY:
      - Time: O(n^2) worst/average case, O(n) best case (already sorted)
      - Space: O(n) due to list construction (not truly in-place)

    FOR LARGE LISTS:
      Consider FStar.List.Tot.sortWith which may use merge sort.
      Our insertion sort is primarily for canonicalizing small structures
      like effect rows (typically < 10 elements).

    USAGE IN BRRR-LANG:
      - Canonical effect row representation: sort effect labels
      - Session type branch ordering
      - Deterministic output generation

    COMPARISON FUNCTION REQUIREMENTS:
      The lt function should be a strict partial order:
        - Irreflexive: not (lt x x)
        - Asymmetric: lt x y ==> not (lt y x)
        - Transitive: lt x y /\ lt y z ==> lt x z

      For a total order, also need: x <> y ==> lt x y \/ lt y x
 *)

(** Insert element into sorted list maintaining order.

    @param lt Less-than comparison function (strict)
    @param x Element to insert
    @param l Sorted list (precondition: l sorted by lt)
    @returns Sorted list containing x

    PRECONDITION: l must be sorted according to lt
    POSTCONDITION: result is sorted and contains x plus all elements of l

    Example (with (<) on int):
      insert_sorted (<) 3 [1;2;4;5] = [1;2;3;4;5]
      insert_sorted (<) 0 [1;2;3] = [0;1;2;3]
      insert_sorted (<) 5 [1;2;3] = [1;2;3;5]

    COMPLEXITY: O(n) where n = length l *)
val insert_sorted : #a:Type -> lt:(a -> a -> bool) -> x:a -> l:list a -> Tot (list a) (decreases l)

(** Sort list using insertion sort.

    @param lt Less-than comparison function (strict)
    @param l List to sort
    @returns Sorted list

    POSTCONDITIONS:
      1. Result is sorted according to lt
      2. Result is a permutation of input (same elements)
      3. Sort is stable (equal elements preserve relative order)

    Example (with (<) on int):
      sort (<) [3;1;4;1;5;9;2;6] = [1;1;2;3;4;5;6;9]
      sort (<) [] = []
      sort (<) [1] = [1]

    COMPLEXITY: O(n^2) - suitable for small lists only.

    NOTE: For large lists, consider FStar.List.Tot.sortWith *)
val sort : #a:Type -> lt:(a -> a -> bool) -> l:list a -> Tot (list a) (decreases l)

(** ============================================================================
    LIST UTILITIES
    ============================================================================

    General-purpose list operations not covered by FStar.List.Tot.

    These functions provide common operations for working with
    list indices and slicing.
 *)

(** Generate range [0, n).

    @param n Upper bound (exclusive)
    @returns [0; 1; 2; ...; n-1]

    PROPERTIES:
      length (range n) = n
      forall i. i < n ==> index (range n) i = i

    Example:
      range 5 = [0; 1; 2; 3; 4]
      range 0 = []
      range 1 = [0]

    IMPLEMENTATION: Uses tail-recursive helper with accumulator.

    USE CASES:
      - Indexing into lists: List.map (index l) (range (length l))
      - Generating test inputs
      - Enumerating positions *)
val range : n:nat -> Tot (list nat)

(** Take first n elements from list.

    @param n Number of elements to take
    @param l Source list
    @returns First n elements (or all if length l < n)

    PROPERTIES:
      length (take n l) = min n (length l)
      forall i. i < length (take n l) ==> index (take n l) i = index l i

    Example:
      take 2 [1;2;3;4;5] = [1;2]
      take 10 [1;2;3] = [1;2;3]   (* n > length l *)
      take 0 [1;2;3] = []

    Corresponds to: Seq.slice s 0 n (for sequences)

    COMPLEXITY: O(min(n, length l)) *)
val take : #a:Type -> n:nat -> l:list a -> Tot (list a) (decreases n)

(** Drop first n elements from list.

    @param n Number of elements to drop
    @param l Source list
    @returns Remaining elements after dropping first n

    PROPERTIES:
      length (drop n l) = max 0 (length l - n)
      forall i. i < length (drop n l) ==> index (drop n l) i = index l (n + i)

    RELATIONSHIP: take n l @ drop n l = l  (for n <= length l)

    Example:
      drop 2 [1;2;3;4;5] = [3;4;5]
      drop 10 [1;2;3] = []         (* n > length l *)
      drop 0 [1;2;3] = [1;2;3]

    Corresponds to: FStar.List.Tot.tl iterated n times

    COMPLEXITY: O(min(n, length l)) *)
val drop : #a:Type -> n:nat -> l:list a -> Tot (list a) (decreases n)

(** Split list at position n.

    @param n Split position (0-indexed)
    @param l List to split
    @returns (first n elements, remaining elements)

    EQUIVALENCE: split_at n l = (take n l, drop n l)

    PROPERTIES:
      let (prefix, suffix) = split_at n l in
        prefix @ suffix = l
        length prefix = min n (length l)

    Example:
      split_at 2 [1;2;3;4;5] = ([1;2], [3;4;5])
      split_at 0 [1;2;3] = ([], [1;2;3])
      split_at 10 [1;2;3] = ([1;2;3], [])

    USE CASE: Splitting at boundaries (e.g., parser state) *)
val split_at : #a:Type -> n:nat -> l:list a -> Tot (list a & list a)

(** ============================================================================
    STRING UTILITIES
    ============================================================================

    String manipulation utilities. F* strings are opaque with limited
    operations, so we provide common helpers here.

    NOTE ON F* STRINGS:
      - F* strings are NOT lists of characters (unlike Haskell)
      - String comparison uses built-in = operator
      - String length via FStar.String.length
      - Concatenation via ^ operator
      - Character access is limited

    LIMITATION: True lexicographic ordering would require character-by-
    character comparison. Our string_lt is a simplified total order
    suitable for sorting but not true lexicographic comparison.
 *)

(** String equality (using built-in structural equality).

    @param s1 First string
    @param s2 Second string
    @returns true iff s1 and s2 are identical strings

    NOTE: This is just (=) for strings, provided for consistency
    with the other predicates in this module. *)
val string_eq : s1:string -> s2:string -> Tot bool

(** String comparison for sorting purposes.

    @param s1 First string
    @param s2 Second string
    @returns true if s1 should sort before s2

    ORDERING:
      1. Shorter strings come first
      2. For same-length strings, an arbitrary but consistent order

    WARNING: This is NOT lexicographic ordering!
    For true lexicographic comparison, use FStar.String functions.

    USE CASE: This is sufficient for canonicalizing string-keyed maps
    where we just need SOME deterministic order, not specifically
    lexicographic. *)
val string_lt : s1:string -> s2:string -> Tot bool
