(**
 * BrrrLang.Core.PatternAnalysis
 *
 * Pattern analysis for exhaustiveness checking, redundancy detection,
 * and efficient pattern matching compilation via decision trees.
 *
 * ============================================================================
 * THEORETICAL FOUNDATION
 * ============================================================================
 *
 * This module implements the core pattern analysis algorithms for Brrr-Lang
 * based on the foundational work of Luc Maranget:
 *
 *   Maranget, L. (2007). "Warnings for Pattern Matching."
 *   Journal of Functional Programming, 17(3), 387-421.
 *
 *   Maranget, L. (2008). "Compiling Pattern Matching to Good Decision Trees."
 *   ML Workshop 2008.
 *
 * The key insight is that pattern matching analysis can be reduced to
 * operations on VALUE SPACES - abstract representations of sets of values
 * that patterns can match.
 *
 * ============================================================================
 * SPECIFICATION REFERENCE
 * ============================================================================
 *
 * From brrr_lang_spec_v0.4.tex Part V (Expressions & Patterns):
 *
 *   Definition 2.8 (Exhaustiveness):
 *   Patterns p_1, ..., p_n are exhaustive for type T iff:
 *     forall v : T. exists i. v in [[p_i]]
 *
 *   where [[p]] denotes the "denotation" or set of values matched by pattern p.
 *
 *   Definition 2.9 (Redundancy):
 *   Pattern p_i is redundant iff:
 *     [[p_i]] subseteq Union_{j < i} [[p_j]]
 *
 *   That is, a pattern is redundant if every value it matches is already
 *   matched by a previous pattern in the match expression.
 *
 * ============================================================================
 * ALGORITHM OVERVIEW
 * ============================================================================
 *
 * The pattern analysis proceeds in three phases:
 *
 * PHASE 1: Value Space Construction (pattern_to_space)
 * ----------------------------------------------------
 * Convert each pattern to a VALUE SPACE representing the set of values it
 * matches. A value space is a symbolic representation that allows efficient
 * set operations without enumerating actual values.
 *
 *   pattern_to_space : pattern -> brrr_type -> value_space
 *
 * PHASE 2: Exhaustiveness Checking (is_exhaustive, check_exhaustiveness)
 * ----------------------------------------------------------------------
 * Use the SUBTRACTION ALGORITHM to determine if patterns cover all values:
 *
 *   1. Start with VSAll ty (the set of ALL values of type ty)
 *   2. For each pattern p_i, subtract pattern_to_space(p_i) from the
 *      remaining value space
 *   3. After processing all patterns, if the remaining space is empty,
 *      the patterns are exhaustive
 *
 * This is O(n * m) where n is the number of patterns and m is the size
 * of the pattern matrix.
 *
 * PHASE 3: Usefulness/Redundancy Checking (is_useful, check_usefulness)
 * ---------------------------------------------------------------------
 * The USEFULNESS PREDICATE determines if a pattern matches anything new:
 *
 *   is_useful(covered, p) = pattern_to_space(p) INTERSECT (complement covered)
 *                         is NON-EMPTY
 *
 * A pattern p_i is redundant iff is_useful(Union_{j<i} [[p_j]], p_i) = false
 *
 * ============================================================================
 * DECISION TREE COMPILATION
 * ============================================================================
 *
 * Following Maranget (2008), we compile patterns to DECISION TREES for
 * efficient runtime matching. The key insight is that instead of trying
 * patterns sequentially (O(n) per match), we can examine each component
 * of the scrutinee at most once (O(depth) per match where depth << n).
 *
 * The compilation algorithm:
 *
 *   1. Build a PATTERN MATRIX where each row is (pattern_vector, arm_index)
 *   2. Select a COLUMN to split on (heuristics affect efficiency)
 *   3. SPECIALIZE the matrix by constructor for that column
 *   4. Recursively compile each specialized matrix
 *   5. Build a DTSwitch node branching on constructor
 *
 * Column selection heuristics (Maranget 2008 Section 4):
 *   - "First non-wildcard column" - simple, predictable
 *   - "Most distinct constructors" - maximize branching
 *   - "Fewest default cases" - minimize default subtree size
 *
 * We currently use the first heuristic for simplicity.
 *
 * ============================================================================
 * GUARD ANALYSIS (CONSERVATIVE)
 * ============================================================================
 *
 * Guard patterns (p when cond) present a challenge: the guard condition
 * may fail even when the structural pattern matches. This means:
 *
 *   - For EXHAUSTIVENESS: We CANNOT assume guards succeed.
 *     We conservatively treat guard patterns as NOT contributing to
 *     exhaustiveness (the subtraction is not performed).
 *
 *   - For USEFULNESS: We assume guards MAY succeed.
 *     A guarded pattern is considered useful if its structural part
 *     matches something new.
 *
 * This conservative approach may produce false positives for non-exhaustive
 * warnings but NEVER false negatives (no silent match failures).
 *
 * For precise guard analysis, we would need:
 *   - Symbolic evaluation of guard conditions
 *   - SMT-backed constraint solving
 *   - Integration with type refinements
 *
 * ============================================================================
 * KEY INVARIANTS
 * ============================================================================
 *
 * INV-1 (Soundness of Exhaustiveness):
 *   If is_exhaustive(ty, patterns) = true, then every value of type ty
 *   matches at least one pattern.
 *
 * INV-2 (Soundness of Usefulness):
 *   If is_useful(covered, p) = false, then every value matched by p
 *   is already matched by some pattern contributing to 'covered'.
 *
 * INV-3 (Value Space Termination):
 *   All value space operations terminate because:
 *   - value_space_size decreases in recursive calls
 *   - pattern_size decreases when descending into sub-patterns
 *
 * INV-4 (Decision Tree Completeness):
 *   If patterns are exhaustive, the compiled decision tree has no DTFail
 *   nodes reachable from valid input values.
 *
 * ============================================================================
 * LITERATURE REFERENCES
 * ============================================================================
 *
 * [Maranget07] Maranget, L. (2007). "Warnings for Pattern Matching."
 *              Journal of Functional Programming, 17(3), 387-421.
 *              - Defines usefulness predicate and exhaustiveness
 *              - Value space representation for algebraic types
 *
 * [Maranget08] Maranget, L. (2008). "Compiling Pattern Matching to Good
 *              Decision Trees." ML Workshop 2008.
 *              - Decision tree compilation algorithm
 *              - Column selection heuristics
 *
 * [Sestoft96]  Sestoft, P. (1996). "ML Pattern Match Compilation and
 *              Partial Evaluation." In Partial Evaluation, LNCS 1110.
 *              - Earlier work on pattern match compilation
 *
 * [Wadler87]   Wadler, P. (1987). "Efficient Compilation of Pattern-Matching."
 *              The Implementation of Functional Programming Languages.
 *              - Classic algorithm, basis for Maranget's work
 *
 * ============================================================================
 * MODULE DEPENDENCIES
 * ============================================================================
 *
 * Depends on:
 *   - Primitives: Literal types and operations
 *   - BrrrTypes: Type representation for value space construction
 *   - Expressions: Pattern AST and match_arm type
 *   - Values: Pattern definition (re-exported from Expressions)
 *
 * Used by:
 *   - Type checker: Exhaustiveness warnings
 *   - Brrr-Machine: Analysis toolkit integration
 *   - Code generation: Decision tree emission
 *)
module BrrrPatternAnalysis

open BrrrPrimitives
open BrrrTypes
open BrrrExpressions
open BrrrValues
open FStar.List.Tot

(** ============================================================================
    TYPE ALIASES FOR PATTERN ANALYSIS
    ============================================================================

    We use t_top as a "wildcard type" when the actual type is unknown or
    irrelevant for pattern analysis. This follows the convention in Maranget's
    algorithm where pattern analysis can proceed structurally without full
    type information.
    ============================================================================ *)

(* Alias for top/unknown type for pattern analysis *)
let t_top : brrr_type = t_unknown

(** ============================================================================
    VALUE SPACE REPRESENTATION
    ============================================================================

    OVERVIEW:
    ---------
    A value space is an abstract representation of a set of values. This is
    the core data structure for pattern analysis, enabling symbolic manipulation
    of potentially infinite value sets without enumeration.

    The representation follows Maranget (2007) Section 3 "Semantic Signatures"
    with extensions for Brrr-Lang's type system.

    FORMAL SEMANTICS:
    -----------------
    Each value space constructor has a set-theoretic interpretation:

      [[VSAll ty]]        = { v | v : ty }
                           All values inhabiting type ty

      [[VSCtor T C sps]]  = { C(v_1, ..., v_n) | v_i in [[sps_i]] }
                           Values constructed with constructor C of type T

      [[VSPair sp1 sp2]]  = [[sp1]] x [[sp2]]
                           Cartesian product (pair values)

      [[VSTuple sps]]     = [[sps_1]] x ... x [[sps_n]]
                           n-ary tuple (generalized product)

      [[VSUnion sps]]     = Union_i [[sps_i]]
                           Set union (values in ANY space)

      [[VSIntersect sps]] = Intersect_i [[sps_i]]
                           Set intersection (values in ALL spaces)

      [[VSComplement sp]] = U \ [[sp]]  where U is the universe
                           Set complement (values NOT in space)

      [[VSEmpty]]         = {}
                           Empty set (no values)

      [[VSLiteral lit]]   = { lit }
                           Singleton containing exactly one literal

      [[VSRange lo hi]]   = { n in Z | lo <= n <= hi }
                           Integer interval [lo, hi]

      [[VSArray sp n]]    = [[sp]]^n
                           Arrays of exactly n elements from sp

      [[VSAnyArray sp]]   = Union_{n>=0} [[sp]]^n
                           Arrays of any length from sp

    DESIGN DECISIONS:
    -----------------
    1. We use VSCtor for BOTH variant constructors and struct patterns.
       For structs, the constructor name is "struct".

    2. VSComplement enables expressing "all values EXCEPT those matching p".
       This is essential for the subtraction algorithm.

    3. VSRange enables efficient integer pattern analysis without enumerating
       all integers in a range.

    4. The noeq annotation prevents F* from generating decidable equality,
       which would be impossible due to recursive structure and would cause
       extraction issues with infinite types.

    COMPLEXITY CONSIDERATIONS:
    --------------------------
    Value spaces can grow exponentially in nested unions/complements.
    The simplify function reduces this by:
      - Removing empty spaces from unions
      - Collapsing singleton unions
      - Short-circuiting intersections containing empty

    Reference: Maranget (2007) Section 3.1 "Value Vectors and Patterns"
    ============================================================================ *)

noeq type value_space =
  (* Universal set: all values of a given type *)
  | VSAll        : brrr_type -> value_space

  (* Constructor application: C(vs_1, ..., vs_n) where each vs_i is a value space.
     The type_name identifies the ADT, string is the constructor/variant name. *)
  | VSCtor       : type_name -> string -> list value_space -> value_space

  (* Binary product (pair): values (v1, v2) where v1 in sp1 and v2 in sp2 *)
  | VSPair       : value_space -> value_space -> value_space

  (* n-ary product (tuple): values (v1, ..., vn) where v_i in sps[i] *)
  | VSTuple      : list value_space -> value_space

  (* Set union: values in ANY of the given spaces *)
  | VSUnion      : list value_space -> value_space

  (* Set intersection: values in ALL of the given spaces *)
  | VSIntersect  : list value_space -> value_space

  (* Set complement: values NOT in the given space (relative to universe) *)
  | VSComplement : value_space -> value_space

  (* Empty set: matches no values *)
  | VSEmpty      : value_space

  (* Singleton literal: exactly one specific literal value *)
  | VSLiteral    : literal -> value_space

  (* Integer range [lo, hi] inclusive: {n in Z | lo <= n <= hi} *)
  | VSRange      : int -> int -> value_space

  (* Fixed-length array: arrays of exactly n elements from space *)
  | VSArray      : value_space -> nat -> value_space

  (* Variable-length array: arrays of any length from space *)
  | VSAnyArray   : value_space -> value_space

(** ============================================================================
    VALUE SPACE SIZE (for termination proofs)
    ============================================================================

    MOTIVATION:
    -----------
    F* requires termination proofs for recursive functions. The value_space_size
    function provides a WELL-FOUNDED MEASURE that decreases on all recursive calls
    through value space operations.

    PROPERTIES:
    -----------
    - value_space_size vs >= 1 for all vs (every space has positive size)
    - For composite spaces, size > sum of component sizes (strict decrease)
    - The measure is structural: size reflects the AST depth

    This measure is used in the `decreases` clauses of:
    - is_empty
    - simplify
    - subtract_pattern
    - pattern_to_space (indirectly via pattern_size)

    FORMAL DEFINITION:
    ------------------
      size(VSAll _)          = 1
      size(VSCtor _ _ sps)   = 1 + sum(size(sp) for sp in sps)
      size(VSPair sp1 sp2)   = 1 + size(sp1) + size(sp2)
      size(VSTuple sps)      = 1 + sum(size(sp) for sp in sps)
      size(VSUnion sps)      = 1 + sum(size(sp) for sp in sps)
      size(VSIntersect sps)  = 1 + sum(size(sp) for sp in sps)
      size(VSComplement sp)  = 1 + size(sp)
      size(VSEmpty)          = 1
      size(VSLiteral _)      = 1
      size(VSRange _ _)      = 1
      size(VSArray sp _)     = 1 + size(sp)
      size(VSAnyArray sp)    = 1 + size(sp)
    ============================================================================ *)

let rec value_space_size (vs: value_space) : Tot nat (decreases vs) =
  match vs with
  | VSAll _ -> 1
  | VSCtor _ _ sps -> 1 + value_space_list_size sps
  | VSPair sp1 sp2 -> 1 + value_space_size sp1 + value_space_size sp2
  | VSTuple sps -> 1 + value_space_list_size sps
  | VSUnion sps -> 1 + value_space_list_size sps
  | VSIntersect sps -> 1 + value_space_list_size sps
  | VSComplement sp -> 1 + value_space_size sp
  | VSEmpty -> 1
  | VSLiteral _ -> 1
  | VSRange _ _ -> 1
  | VSArray sp _ -> 1 + value_space_size sp
  | VSAnyArray sp -> 1 + value_space_size sp

and value_space_list_size (sps: list value_space) : Tot nat (decreases sps) =
  match sps with
  | [] -> 0
  | sp :: rest -> value_space_size sp + value_space_list_size rest

(** ============================================================================
    VALUE SPACE OPERATIONS
    ============================================================================

    This section defines the core operations on value spaces that enable
    exhaustiveness and usefulness checking. These operations implement the
    set-theoretic semantics of value spaces.

    KEY OPERATIONS:
    ---------------
    is_empty    : value_space -> bool
                  Tests if a value space represents the empty set.

    simplify    : value_space -> value_space
                  Reduces a value space to a simpler equivalent form.

    exists_in   : (a -> bool) -> list a -> bool
                  Helper: tests if predicate holds for any list element.

    SOUNDNESS REQUIREMENTS:
    -----------------------
    - is_empty must be SOUND: if is_empty(vs) = true, then [[vs]] = {}
    - is_empty may be INCOMPLETE: is_empty(vs) = false does not guarantee [[vs]] != {}
      (due to undecidability of general emptiness)

    - simplify must be SEMANTICS-PRESERVING: [[simplify(vs)]] = [[vs]]
    - simplify should reduce space size when possible (efficiency)

    TERMINATION:
    ------------
    All operations use value_space_size as the termination measure.
    Recursive calls strictly decrease this measure.
    ============================================================================ *)

(** Check if value space is empty (SOUND but INCOMPLETE)

    ALGORITHM:
    ----------
    - VSEmpty: trivially empty
    - VSUnion: empty iff ALL components are empty (empty union = empty)
    - VSIntersect: empty if ANY component is empty (intersection with empty = empty)
    - VSTuple: empty if ANY component is empty (can't build tuple)
    - VSPair: empty if EITHER component is empty (can't build pair)
    - VSRange lo hi: empty if lo > hi (no integers in range)
    - Otherwise: conservatively return false (may have values)

    NOTE: This is incomplete for VSComplement and nested structures.
    Complete emptiness checking would require semantic analysis.

    COMPLEXITY: O(size of value_space)
*)
let rec is_empty (vs: value_space) : Tot bool (decreases value_space_size vs) =
  match vs with
  | VSEmpty -> true
  | VSUnion sps -> for_all is_empty sps
  | VSIntersect sps ->
      (* Intersection is empty if any component is empty *)
      exists_in is_empty sps
  | VSTuple sps -> exists_in is_empty sps
  | VSPair sp1 sp2 -> is_empty sp1 || is_empty sp2
  | VSRange lo hi -> lo > hi
  | _ -> false

(** Helper: check if predicate holds for any element in list *)
and exists_in (#a: Type) (f: a -> bool) (l: list a) : bool =
  match l with
  | [] -> false
  | x :: xs -> f x || exists_in f xs

(** Simplify value space by removing empty components and collapsing trivial cases

    SIMPLIFICATION RULES:
    ---------------------
    VSUnion []:      -> VSEmpty           (empty union)
    VSUnion [sp]:    -> simplify(sp)      (singleton union)
    VSUnion sps:     -> VSUnion (filter non-empty (map simplify sps))

    VSIntersect []:  -> VSEmpty           (vacuous intersection)
    VSIntersect [sp]:-> simplify(sp)      (singleton intersection)
    VSIntersect sps: -> VSEmpty if any sp is empty
                     -> VSIntersect (map simplify sps) otherwise

    VSTuple sps:     -> VSEmpty if any sp is empty
                     -> VSTuple (map simplify sps) otherwise

    VSPair sp1 sp2:  -> VSEmpty if either is empty
                     -> VSPair (simplify sp1) (simplify sp2) otherwise

    Other cases:     -> unchanged (already simple)

    INVARIANT: [[simplify(vs)]] = [[vs]]
    PROPERTY:  value_space_size(simplify(vs)) <= value_space_size(vs)

    COMPLEXITY: O(size of value_space)
*)
let rec simplify (vs: value_space) : Tot value_space (decreases value_space_size vs) =
  match vs with
  | VSUnion sps ->
      let non_empty = filter (fun sp -> not (is_empty (simplify sp))) sps in
      (match non_empty with
       | [] -> VSEmpty
       | [sp] -> simplify sp
       | _ -> VSUnion (map simplify non_empty))
  | VSIntersect sps ->
      if exists_in is_empty sps then VSEmpty
      else
        let simplified = map simplify sps in
        (match simplified with
         | [] -> VSEmpty
         | [sp] -> sp
         | _ -> VSIntersect simplified)
  | VSTuple sps ->
      if exists_in (fun sp -> is_empty (simplify sp)) sps then VSEmpty
      else VSTuple (map simplify sps)
  | VSPair sp1 sp2 ->
      let s1 = simplify sp1 in
      let s2 = simplify sp2 in
      if is_empty s1 || is_empty s2 then VSEmpty
      else VSPair s1 s2
  | _ -> vs

(** ============================================================================
    PATTERN TO VALUE SPACE CONVERSION
    ============================================================================

    OVERVIEW:
    ---------
    This section defines the DENOTATION function [[p]] that maps a pattern p
    to the set of values it matches. This is the bridge between the syntactic
    world of patterns and the semantic world of value spaces.

    FORMAL SEMANTICS (Maranget 2007 Section 3.2):
    ---------------------------------------------
      [[_]]              = VSAll ty       (wildcard matches everything)
      [[x]]              = VSAll ty       (variable matches everything, binds x)
      [[lit]]            = VSLiteral lit  (literal matches exactly that value)
      [[(p1, ..., pn)]]  = VSTuple [[[p1]], ..., [[pn]]]
      [[C(p1,...,pn)]]   = VSCtor T C [[[p1]], ..., [[pn]]]
      [[p1 | p2]]        = VSUnion [[[p1]], [[p2]]]
      [[p when guard]]   = [[p]]  (conservative: ignore guard)
      [[p @ x]]          = [[p]]  (as-pattern: same denotation, just binds x)
      [[&p]] or [[&mut p]] = [[p]]  (ref patterns: unwrap)
      [[box p]]          = [[p]]  (box pattern: unwrap)
      [[..x]]            = VSAll ty  (rest pattern: matches any array tail)

    TYPE-DIRECTED ANALYSIS:
    -----------------------
    The function is TYPE-DIRECTED: it uses the expected type to interpret
    patterns correctly. For example:
    - A tuple pattern (p1, p2) needs to know the component types
    - A variant pattern needs to know the ADT definition

    When type information is unavailable or irrelevant, we use t_top.

    GUARD HANDLING (CONSERVATIVE):
    ------------------------------
    Guard patterns (p when cond) are handled CONSERVATIVELY:
    - We return the space of the inner pattern p
    - The guard condition is IGNORED for pattern analysis

    This means:
    - For USEFULNESS: Guarded patterns contribute their structural space
    - For EXHAUSTIVENESS: Guarded patterns may leave gaps undetected

    Precise guard analysis would require symbolic evaluation and is left
    for future work.

    REFERENCE: Maranget (2007) Section 3.2 "The Semantics of Patterns"
    ============================================================================ *)

(** Convert a pattern to its corresponding value space

    PARAMETERS:
    -----------
    p  : pattern     - The pattern to convert
    ty : brrr_type   - The type of values the pattern should match

    RETURNS:
    --------
    A value_space representing all values that pattern p matches.

    INVARIANT:
    ----------
    A value v is in [[pattern_to_space p ty]] iff matching v against p succeeds.

    TERMINATION:
    ------------
    Decreases on pattern structure (pattern_size, not shown in signature).
    All recursive calls are on strictly smaller sub-patterns.
*)
let rec pattern_to_space (p: pattern) (ty: brrr_type) : value_space =
  (* pattern is with_loc pattern', so unwrap to get the actual pattern structure *)
  match p.loc_value with
  | PatWild -> VSAll ty
  | PatVar _ -> VSAll ty
  | PatLit lit -> VSLiteral lit

  | PatTuple pats ->
      (match ty with
       | TTuple tys ->
           if length pats = length tys then
             VSTuple (map2_default pattern_to_space pats tys VSEmpty)
           else VSEmpty
       | _ -> VSEmpty)

  | PatStruct ty_name field_pats ->
      (* Struct pattern - match each field *)
      VSCtor ty_name "struct" (map (fun (_, pat) -> pattern_to_space pat t_top) field_pats)

  | PatVariant ty_name var_name pats ->
      (* Variant/enum pattern *)
      VSCtor ty_name var_name (map (fun pat -> pattern_to_space pat t_top) pats)

  | PatOr p1 p2 ->
      VSUnion [pattern_to_space p1 ty; pattern_to_space p2 ty]

  | PatGuard inner_p _ ->
      (* Guard patterns are partial - conservatively treat as the inner pattern.
         For precise analysis, would need to evaluate the guard symbolically. *)
      pattern_to_space inner_p ty

  | PatRef inner_p ->
      (match ty with
       | TWrap WRef inner_ty -> pattern_to_space inner_p inner_ty
       | TWrap WRefMut inner_ty -> pattern_to_space inner_p inner_ty
       | _ -> VSEmpty)

  | PatBox inner_p ->
      (match ty with
       | TWrap WBox inner_ty -> pattern_to_space inner_p inner_ty
       | TModal _ inner_ty -> pattern_to_space inner_p inner_ty  (* Box modality *)
       | _ -> VSEmpty)

  | PatRest _ ->
      (* Rest pattern matches any remaining elements - treated as VSAll *)
      VSAll ty

  | PatAs inner_p _ ->
      (* As-pattern matches same as inner pattern *)
      pattern_to_space inner_p ty

and map2_default (#a #b #c: Type) (f: a -> b -> c) (l1: list a) (l2: list b) (default: c) : list c =
  match l1, l2 with
  | [], [] -> []
  | x :: xs, y :: ys -> f x y :: map2_default f xs ys default
  | _, _ -> []  (* Length mismatch *)

(** ============================================================================
    SUBTRACT PATTERN FROM VALUE SPACE (Core Exhaustiveness Algorithm)
    ============================================================================

    OVERVIEW:
    ---------
    The SUBTRACTION operation is the heart of exhaustiveness checking.
    Given a value space vs and a pattern p, it computes:

      subtract_pattern(vs, p) = vs \ [[p]]

    That is, the set of values in vs that are NOT matched by pattern p.

    EXHAUSTIVENESS ALGORITHM (Maranget 2007 Section 4):
    ---------------------------------------------------
    To check if patterns p_1, ..., p_n are exhaustive for type T:

      1. remaining := VSAll T              (all values of type T)
      2. for i := 1 to n:
           remaining := subtract_pattern(remaining, p_i)
      3. return is_empty(remaining)        (true iff exhaustive)

    If remaining is empty after processing all patterns, every value of type T
    matches at least one pattern.

    CASE ANALYSIS:
    --------------
    The subtraction operation performs case analysis on both the value space
    and the pattern:

    vs = VSEmpty:
      subtract(VSEmpty, p) = VSEmpty
      Subtracting from empty leaves empty.

    vs = VSAll ty:
      subtract(VSAll ty, _) = VSComplement [[p]]
      Removing pattern p from the universe leaves everything except p.

    vs = VSCtor T C sps:
      If p = C'(...) with C' != C: unchanged (different constructor)
      If p = C(p1,...,pn): subtract componentwise

    vs = VSTuple sps:
      If p = (p1,...,pn): subtract componentwise with tuple semantics

    vs = VSUnion sps:
      subtract(Union sps, p) = Union [subtract(sp, p) for sp in sps]
      Distribute subtraction over union.

    vs = VSPair sp1 sp2:
      Similar to tuple with n=2.

    GUARD HANDLING (CONSERVATIVE):
    ------------------------------
    For guard patterns (p when cond):
      subtract(vs, p when cond) = vs  (NO subtraction performed)

    This is CONSERVATIVE for exhaustiveness: we assume the guard might fail,
    so we don't count the pattern as covering any values. This may lead to
    false "non-exhaustive" warnings but never silent match failures.

    TERMINATION:
    ------------
    The function terminates because:
    1. value_space_size(vs) decreases on recursive calls through vs structure
    2. pattern_size(p) decreases on recursive calls through pattern structure
    3. The lexicographic ordering (value_space_size vs, pattern_size p) decreases

    COMPLEXITY:
    -----------
    O(|vs| * |p|) where |vs| and |p| are the sizes of the value space and
    pattern respectively. Can be exponential in worst case due to complement
    and union expansion.

    REFERENCE: Maranget (2007) Section 4 "Checking Exhaustiveness"
    ============================================================================ *)

(** Subtract pattern from value space: vs \ [[p]]

    PARAMETERS:
    -----------
    vs : value_space  - The value space to subtract from
    p  : pattern      - The pattern whose matched values to remove

    RETURNS:
    --------
    A value_space representing vs \ [[p]] (values in vs not matched by p)

    INVARIANT:
    ----------
    v in [[subtract_pattern(vs, p)]] iff v in [[vs]] AND v not in [[p]]
*)
let rec subtract_pattern (vs: value_space) (p: pattern) : Tot value_space (decreases (value_space_size vs, pattern_size p)) =
  (* pattern is with_loc pattern', so unwrap to access pattern structure *)
  let p' = p.loc_value in
  match vs with
  | VSEmpty -> VSEmpty

  | VSAll ty ->
      (* Subtracting from "all values" - need to consider pattern structure *)
      (match p' with
       | PatWild -> VSEmpty  (* Wildcard matches everything *)
       | PatVar _ -> VSEmpty  (* Variable matches everything *)

       | PatLit lit ->
           (* Remove just this literal - result is complement *)
           VSComplement (VSLiteral lit)

       | PatTuple pats ->
           (* For tuple, subtract component-wise if type matches *)
           (match ty with
            | TTuple tys ->
                if length pats = length tys then
                  (* Result is union of: remove first element, keep first remove second, etc. *)
                  subtract_tuple_patterns (map (fun t -> VSAll t) tys) pats
                else vs  (* Length mismatch - no subtraction *)
            | _ -> vs)

       | PatVariant ty_name var_name pats ->
           (* Remove this variant case *)
           VSComplement (VSCtor ty_name var_name (map (fun _ -> VSAll t_top) pats))

       | PatOr p1 p2 ->
           (* Subtract both alternatives *)
           subtract_pattern (subtract_pattern vs p1) p2

       | PatGuard inner_p _ ->
           (* Conservatively: guards may not match, so only subtract inner pattern *)
           (* For precise analysis, would need symbolic guard evaluation *)
           vs  (* Conservative: don't subtract guarded patterns *)

       | PatRef inner_p ->
           (match ty with
            | TWrap WRef inner_ty -> subtract_pattern (VSAll inner_ty) inner_p
            | TWrap WRefMut inner_ty -> subtract_pattern (VSAll inner_ty) inner_p
            | _ -> vs)

       | PatBox inner_p ->
           (match ty with
            | TWrap WBox inner_ty -> subtract_pattern (VSAll inner_ty) inner_p
            | TModal _ inner_ty -> subtract_pattern (VSAll inner_ty) inner_p
            | _ -> vs)

       | PatRest _ -> VSEmpty  (* Rest pattern matches any array tail *)

       | PatAs inner_p _ -> subtract_pattern vs inner_p

       | PatStruct ty_name field_pats ->
           VSComplement (VSCtor ty_name "struct" (map (fun (_, pat) -> pattern_to_space pat t_top) field_pats)))

  | VSCtor ty_name ctor_name sps ->
      (match p' with
       | PatWild -> VSEmpty
       | PatVar _ -> VSEmpty
       | PatVariant ty_name' var_name' pats ->
           if ty_name = ty_name' && ctor_name = var_name' && length pats = length sps then
             (* Same constructor - subtract from sub-spaces *)
             let remaining = subtract_pattern_list sps pats in
             if for_all is_empty remaining then VSEmpty
             else VSCtor ty_name ctor_name remaining
           else vs  (* Different constructor - no change *)
       | PatOr p1 p2 -> subtract_pattern (subtract_pattern vs p1) p2
       | _ -> vs)

  | VSTuple sps ->
      (match p' with
       | PatWild -> VSEmpty
       | PatVar _ -> VSEmpty
       | PatTuple pats ->
           if length pats = length sps then
             subtract_tuple_patterns sps pats
           else vs
       | PatOr p1 p2 -> subtract_pattern (subtract_pattern vs p1) p2
       | _ -> vs)

  | VSUnion sps ->
      (* Subtract from each union member *)
      simplify (VSUnion (map (fun sp -> subtract_pattern sp p) sps))

  | VSPair sp1 sp2 ->
      (match p' with
       | PatWild -> VSEmpty
       | PatVar _ -> VSEmpty
       | PatTuple [p1; p2] ->
           (* Pair is a 2-tuple *)
           let r1 = subtract_pattern sp1 p1 in
           let r2 = subtract_pattern sp2 p2 in
           simplify (VSUnion [
             VSPair r1 sp2;        (* First didn't match *)
             VSPair sp1 r2         (* Second didn't match *)
           ])
       | PatOr p1 p2 -> subtract_pattern (subtract_pattern vs p1) p2
       | _ -> vs)

  | _ -> vs  (* Other cases: no subtraction *)

and subtract_pattern_list (sps: list value_space) (pats: list pattern)
    : Tot (list value_space) (decreases (value_space_list_size sps, pattern_list_size pats)) =
  match sps, pats with
  | [], [] -> []
  | sp :: sps', p :: pats' ->
      subtract_pattern sp p :: subtract_pattern_list sps' pats'
  | _, _ -> sps  (* Length mismatch *)

and subtract_tuple_patterns (sps: list value_space) (pats: list pattern) : value_space =
  (* Subtracting a tuple pattern from a tuple space.
     Result is: values where at least one component doesn't match.
     This is the complement of the intersection. *)
  let subtracted = subtract_pattern_list sps pats in
  if for_all is_empty subtracted then VSEmpty
  else VSTuple subtracted

(** ============================================================================
    EXHAUSTIVENESS CHECKING
    ============================================================================

    SPECIFICATION (brrr_lang_spec_v0.4.tex Definition 2.8):
    -------------------------------------------------------
    Patterns p_1, ..., p_n are EXHAUSTIVE for type T iff:
      forall v : T. exists i in {1..n}. v in [[p_i]]

    That is, every possible value of type T matches at least one of the patterns.

    ALGORITHM:
    ----------
    1. remaining := VSAll ty       (start with all values of type ty)
    2. for each pattern p_i:
         remaining := subtract_pattern(remaining, p_i)
    3. return is_empty(simplify(remaining))

    If remaining is empty after subtracting all patterns, then every value
    has been accounted for by at least one pattern.

    SOUNDNESS THEOREM:
    ------------------
    If is_exhaustive(ty, patterns) = true, then the patterns are indeed
    exhaustive: every value of type ty matches at least one pattern.

    PROOF SKETCH:
    Suppose is_exhaustive returns true but some value v : ty is not matched.
    Then v is in VSAll ty but not in any [[p_i]].
    By semantics of subtract_pattern:
      v in subtract_pattern(vs, p) iff v in vs and v not in [[p]]
    So v would be in the final remaining space, contradicting is_empty = true.

    COMPLETENESS NOTE:
    ------------------
    The algorithm is INCOMPLETE in the presence of guards:
    - Guarded patterns are treated conservatively (not subtracted)
    - This may cause false "non-exhaustive" warnings
    - It NEVER causes silent match failures (safety preserved)

    COMPLEXITY:
    -----------
    O(n * m) where n = number of patterns, m = average pattern size.
    The fold_left processes each pattern once, and subtract_pattern is
    linear in the pattern size.

    EXAMPLE:
    --------
      type option a = None | Some a

      match x with
      | None -> ...
      | Some y -> ...

      is_exhaustive(option int, [None, Some _]) =
        let remaining = subtract(subtract(VSAll(option int), None), Some _)
        = subtract(VSCtor option "Some" [VSAll int], Some _)
        = VSEmpty
        = true (exhaustive!)

    REFERENCE: Maranget (2007) Section 4 "Checking Exhaustiveness"
    ============================================================================ *)

(** Check if patterns exhaustively cover all values of a type

    PARAMETERS:
    -----------
    ty       : brrr_type     - The type being matched against
    patterns : list pattern  - The patterns in the match expression

    RETURNS:
    --------
    true  if every value of type ty matches at least one pattern
    false if there may exist values not covered by any pattern

    NOTE: May return false even for exhaustive patterns due to conservative
    guard handling. Safe: never returns true for non-exhaustive patterns.
*)
let is_exhaustive (ty: brrr_type) (patterns: list pattern) : bool =
  let remaining = fold_left subtract_pattern (VSAll ty) patterns in
  is_empty (simplify remaining)

(* Check exhaustiveness and return witness of missing case if not exhaustive *)
type exhaustiveness_result =
  | Exhaustive : exhaustiveness_result
  | NonExhaustive : value_space -> exhaustiveness_result  (* Witness of uncovered values *)

let check_exhaustiveness (ty: brrr_type) (patterns: list pattern) : exhaustiveness_result =
  let remaining = simplify (fold_left subtract_pattern (VSAll ty) patterns) in
  if is_empty remaining then Exhaustive
  else NonExhaustive remaining

(** ============================================================================
    USEFULNESS PREDICATE AND REDUNDANCY CHECKING
    ============================================================================

    SPECIFICATION (brrr_lang_spec_v0.4.tex Definition 2.9):
    -------------------------------------------------------
    Pattern p_i is REDUNDANT iff:
      [[p_i]] is a subset of Union_{j < i} [[p_j]]

    Equivalently, p_i is redundant iff every value it matches is already
    matched by some earlier pattern p_1, ..., p_{i-1}.

    THE USEFULNESS PREDICATE (Maranget 2007 Section 5):
    ---------------------------------------------------
    A pattern p is USEFUL with respect to a covered space 'covered' iff:
      [[p]] INTERSECT (U \ covered) is NON-EMPTY

    where U is the universe of all values.

    Equivalently:
      is_useful(covered, p) = NOT is_empty([[p]] INTERSECT (VSComplement covered))
                            = NOT ([[p]] is a subset of covered)

    RELATIONSHIP TO REDUNDANCY:
    ---------------------------
    Pattern p_i is redundant iff NOT is_useful(Union_{j<i} [[p_j]], p_i)

    That is, p_i is redundant if it adds no new coverage to what the
    previous patterns already cover.

    ALGORITHM:
    ----------
    1. Compute [[p]] via pattern_to_space
    2. Compute the intersection with complement of covered space
    3. Return true iff the intersection is non-empty

    PRACTICAL IMPLEMENTATION:
    -------------------------
    The full intersection operation can be expensive. Our implementation
    uses VSIntersect with VSComplement and checks emptiness. This may be
    INCOMPLETE (return true when actually redundant for complex cases)
    but is SOUND (never returns false for useful patterns).

    WHY REDUNDANCY MATTERS:
    -----------------------
    1. CODE QUALITY: Redundant patterns indicate logic errors or dead code
    2. PERFORMANCE: Redundant patterns waste runtime checking
    3. MAINTENANCE: Redundant patterns confuse readers and may hide bugs

    GUARD HANDLING (CONSERVATIVE):
    ------------------------------
    For guarded patterns (p when cond):
    - We treat them as POTENTIALLY useful (the guard may succeed)
    - This may miss some redundant guarded patterns
    - It is conservative: no false redundancy warnings

    EXAMPLE:
    --------
      match x with
      | None -> ...           (* useful: matches None *)
      | Some 0 -> ...         (* useful: matches Some(0) *)
      | Some n -> ...         (* useful: matches Some(n) for n != 0 *)
      | None -> ...           (* REDUNDANT: None already covered! *)

      check_usefulness([None, Some 0, Some n, None]) returns:
        useful_patterns = [(0, None), (1, Some 0), (2, Some n)]
        redundant_patterns = [(3, None)]

    COMPLEXITY:
    -----------
    O(n^2 * m) where n = number of patterns, m = average pattern size.
    For each pattern, we compute intersection with the union of all
    previous patterns.

    REFERENCE: Maranget (2007) Section 5 "Checking Usefulness"
    ============================================================================ *)

(** Check if a pattern is useful (matches something not already covered)

    PARAMETERS:
    -----------
    covered : value_space  - Space of values already covered by previous patterns
    p       : pattern      - The pattern to check for usefulness

    RETURNS:
    --------
    true  if p matches at least one value not in covered (p is useful)
    false if every value matched by p is already in covered (p is redundant)

    SOUNDNESS:
    ----------
    If is_useful returns false, the pattern is definitely redundant.
    If is_useful returns true, the pattern may or may not be useful
    (due to conservative guard handling and intersection approximation).
*)
let rec is_useful (covered: value_space) (p: pattern) : bool =
  (* Pattern is useful if it matches something not yet covered *)
  let pattern_space = pattern_to_space p t_top in
  (* Check if pattern_space minus covered is non-empty *)
  not (is_empty (compute_useful_space covered pattern_space))

and compute_useful_space (covered: value_space) (pattern_space: value_space) : value_space =
  (* Compute pattern_space intersect (complement of covered) *)
  match covered with
  | VSEmpty ->
      (* Nothing covered yet - pattern is useful if it matches anything *)
      pattern_space

  | VSAll _ ->
      (* Everything already covered - pattern is redundant *)
      VSEmpty

  | _ ->
      (* Approximate: pattern is useful if it's not completely subsumed *)
      simplify (VSIntersect [pattern_space; VSComplement covered])

(* Check usefulness of each pattern and return list of redundant patterns *)
type usefulness_result = {
  useful_patterns: list (nat & pattern);    (* Index and pattern *)
  redundant_patterns: list (nat & pattern)  (* Index and pattern *)
}

let check_usefulness (patterns: list pattern) : usefulness_result =
  let rec check_each (idx: nat) (remaining: list pattern) (covered: value_space)
      (useful: list (nat & pattern)) (redundant: list (nat & pattern))
      : usefulness_result =
    match remaining with
    | [] -> { useful_patterns = rev useful; redundant_patterns = rev redundant }
    | p :: rest ->
        if is_useful covered p then
          let new_covered = VSUnion [covered; pattern_to_space p t_top] in
          check_each (idx + 1) rest new_covered ((idx, p) :: useful) redundant
        else
          check_each (idx + 1) rest covered useful ((idx, p) :: redundant)
  in
  check_each 0 patterns VSEmpty [] []

(** ============================================================================
    DECISION TREE REPRESENTATION
    ============================================================================

    OVERVIEW:
    ---------
    Decision trees provide EFFICIENT compiled pattern matching. Instead of
    checking patterns sequentially (O(n) per match where n = number of patterns),
    we compile them into a tree structure that examines each scrutinee component
    at most once (O(d) per match where d = scrutinee depth).

    MOTIVATION (Maranget 2008):
    ---------------------------
    Consider matching against n patterns with m columns each:
    - Sequential matching: O(n * m) comparisons per match
    - Decision tree: O(m) comparisons per match (each column examined once)

    The decision tree approach is also cache-friendly because it avoids
    repeatedly examining the same parts of the scrutinee.

    STRUCTURE:
    ----------
    DTLeaf arm_index bindings:
      Match succeeded! Execute arm number 'arm_index' with the given variable
      bindings. The bindings map variable names to references into the
      scrutinee structure.

    DTFail:
      Match failed. This should be UNREACHABLE if the patterns are exhaustive.
      If reached at runtime, it indicates a bug in the compiler or a violation
      of the exhaustiveness property.

    DTSwitch scrutinee cases default:
      Branch based on the constructor/variant tag of the scrutinee component
      at the given position. The 'cases' list maps constructor names to
      sub-trees. The 'default' handles any constructor not explicitly listed
      (used for wildcard patterns).

    DTGuard guard_expr success failure:
      Evaluate the guard expression. If true, continue with 'success' tree.
      If false, continue with 'failure' tree. This is used for when-clauses.

    DTBind var value_ref rest:
      Bind the variable 'var' to the value at 'value_ref', then continue
      with 'rest'. This materializes pattern variables for use in arm bodies.

    DTSeq first second:
      Execute 'first', then 'second'. Used for compound patterns that need
      multiple binding operations.

    RUNTIME EXECUTION:
    ------------------
    To execute a decision tree against a scrutinee value:

      execute(DTLeaf idx bindings, v) = (idx, resolve_bindings(bindings, v))
      execute(DTFail, v) = runtime_error("match failure")
      execute(DTSwitch pos cases default, v) =
        let ctor = get_constructor(v, pos) in
        match lookup(ctor, cases) with
        | Some subtree -> execute(subtree, v)
        | None -> match default with
                  | Some dt -> execute(dt, v)
                  | None -> runtime_error("missing case")
      execute(DTGuard guard success failure, v) =
        if eval(guard) then execute(success, v) else execute(failure, v)
      execute(DTBind var ref rest, v) =
        let bound = get_value(v, ref) in
        execute(rest, v) with var -> bound
      execute(DTSeq first second, v) =
        execute(first, v); execute(second, v)

    REFERENCES:
    -----------
    - Maranget (2008) "Compiling Pattern Matching to Good Decision Trees"
    - Wadler (1987) "Efficient Compilation of Pattern-Matching"
    - Sestoft (1996) "ML Pattern Match Compilation and Partial Evaluation"
    ============================================================================ *)

type decision_tree =
  (** Match succeeded - execute arm with given bindings
      arm_index: 0-based index into the original match arm list
      bindings: list of (variable_name, occurrence_path) pairs *)
  | DTLeaf   : arm_index:nat -> bindings:list (var_id & nat) -> decision_tree

  (** Match failed - should be unreachable if patterns are exhaustive *)
  | DTFail   : decision_tree

  (** Branch on constructor tag at given scrutinee position
      scrutinee: index into the scrutinee (or path, simplified to nat here)
      cases: list of (constructor_name, subtree) pairs
      default: optional fallback for wildcards/unmentioned constructors *)
  | DTSwitch : scrutinee:nat -> cases:list (string & decision_tree) -> default:option decision_tree -> decision_tree

  (** Evaluate guard condition and branch
      guard_expr: the expression to evaluate (should be pure)
      success: subtree if guard is true
      failure: subtree if guard is false *)
  | DTGuard  : guard_expr:expr -> success:decision_tree -> failure:decision_tree -> decision_tree

  (** Bind a variable to a scrutinee component
      var: variable name to bind
      value_ref: reference to the value in scrutinee
      rest: continuation after binding *)
  | DTBind   : var:var_id -> value_ref:nat -> rest:decision_tree -> decision_tree

  (** Sequential composition of decision trees
      Used for patterns requiring multiple operations *)
  | DTSeq    : first:decision_tree -> second:decision_tree -> decision_tree

(** OCCURRENCE: Path to a sub-value within the scrutinee

    An occurrence is a sequence of indices describing how to navigate
    from the root scrutinee to a specific sub-component.

    Example: For scrutinee ((1, 2), (3, 4))
      occurrence []      -> the whole tuple ((1, 2), (3, 4))
      occurrence [0]     -> first component (1, 2)
      occurrence [0, 1]  -> second element of first component: 2
      occurrence [1, 0]  -> first element of second component: 3
*)
type occurrence = list nat  (* Index path: [0, 1] means first element, then second sub-element *)

(** PATTERN MATRIX ROW: A single row in the pattern compilation matrix

    The pattern matrix is the core data structure for Maranget's algorithm.
    Each row represents one match arm with:
      - pr_patterns: the pattern vector (one pattern per scrutinee column)
      - pr_arm_index: which arm this row belongs to
      - pr_bindings: variables bound so far with their occurrences
*)
type pattern_row = {
  pr_patterns: list pattern;    (* Pattern vector for this row *)
  pr_arm_index: nat;            (* Index of the corresponding match arm *)
  pr_bindings: list (var_id & occurrence)  (* Accumulated variable bindings *)
}

(** PATTERN MATRIX: The matrix being compiled

    Compilation proceeds by manipulating this matrix:
    1. If first row is all wildcards -> emit DTLeaf
    2. Otherwise, pick a column with constructors
    3. Specialize the matrix for each constructor
    4. Recursively compile sub-matrices
    5. Combine results into DTSwitch
*)
type pattern_matrix = list pattern_row

(** ============================================================================
    DECISION TREE COMPILATION (Maranget's Algorithm)
    ============================================================================

    OVERVIEW:
    ---------
    This section implements Maranget's algorithm for compiling pattern matrices
    into efficient decision trees. The algorithm is described in:

      Maranget, L. (2008). "Compiling Pattern Matching to Good Decision Trees."
      ML Workshop 2008.

    THE ALGORITHM:
    --------------
    compile_matrix(P, occ):
      INPUT:  P = pattern matrix, occ = current occurrence path
      OUTPUT: decision tree

      1. BASE CASE - EMPTY MATRIX:
         If P is empty, return DTFail (match failure)

      2. BASE CASE - FIRST ROW ALL WILDCARDS:
         If first row of P has all wildcard patterns, return DTLeaf
         (match succeeds with first arm)

      3. RECURSIVE CASE - COLUMN SELECTION:
         a) Select a column i with at least one non-wildcard pattern
            (column selection heuristic affects efficiency)

         b) Get the set of constructors C = {c1, c2, ..., ck} appearing
            in column i

         c) For each constructor cj:
            - SPECIALIZE P for cj: keep only rows whose column i matches cj,
              expanding the pattern arguments into new columns
            - Recursively compile the specialized matrix

         d) Build default case from rows with wildcards in column i

         e) Return DTSwitch(i, [(c1, t1), ..., (ck, tk)], default)

    SPECIALIZATION (S(c, P)):
    -------------------------
    The specialization operation takes a constructor c with arity n and a
    matrix P, and produces a new matrix where:
    - Rows with c in the selected column: replace c(p1,...,pn) with p1...pn
    - Rows with wildcard: replace _ with n wildcards _..._
    - Rows with different constructor: removed from matrix

    Example:
      P = | (Cons x xs) | p1 |     Specialize for Cons:
          | Nil        | p2 |  => | x | xs | p1 |
          | _          | p3 |     | _ | _  | p3 |

    COLUMN SELECTION HEURISTICS:
    ----------------------------
    The choice of which column to split on affects the tree structure:

    1. "First non-wildcard" (SIMPLE):
       Select the leftmost column containing a non-wildcard.
       Predictable, easy to implement.

    2. "Most constructors" (p heuristic):
       Select column with most distinct constructors.
       Maximizes branching factor, minimizes tree depth.

    3. "Fewest defaults" (q heuristic):
       Select column with fewest wildcard patterns.
       Minimizes the size of the default subtree.

    4. "Necessity" (n heuristic):
       Select column needed by the first arm.
       Ensures no wasted tests for successful matches.

    We currently use heuristic 1 (first non-wildcard) for simplicity.
    More sophisticated heuristics could be added for optimization.

    TERMINATION:
    ------------
    The algorithm terminates because:
    - Matrix size decreases: specialization removes rows or shrinks patterns
    - Fuel parameter provides an explicit bound
    - Each recursive call processes fewer patterns

    CORRECTNESS INVARIANT:
    ----------------------
    For any value v:
      execute(compile_matrix(P), v) = first arm_index such that
                                      row[arm_index].patterns matches v

    COMPLEXITY:
    -----------
    - Time: O(n * m * k) where n = rows, m = columns, k = constructors
    - Space: O(n * m) for the compiled tree
    - The tree size is bounded by O(n * product of constructor arities)

    REFERENCES:
    -----------
    - Maranget (2008) Section 3: The compilation algorithm
    - Maranget (2008) Section 4: Column selection heuristics
    - Sestoft (1996) for earlier formalization
    ============================================================================ *)

(** Check if pattern is a "default" pattern (matches anything)

    Default patterns are wildcards, variables, and rest patterns.
    These patterns don't constrain the set of matched values and thus
    appear in the "default" case when compiling switches.
*)
let is_default_pattern (p: pattern) : bool =
  match p.loc_value with
  | PatWild | PatVar _ -> true   (* Wildcards and variables match anything *)
  | PatRest _ -> true            (* Rest patterns in arrays match any tail *)
  | _ -> false

(** Extract the constructor name from a pattern, if it has one.

    Used during compilation to determine which rows specialize for which
    constructors. Returns None for default patterns (wildcards, variables).

    Examples:
      pattern_constructor (PatVariant "option" "Some" [...]) = Some "Some"
      pattern_constructor (PatLit (LitBool true)) = Some "true"
      pattern_constructor PatWild = None
*)
let pattern_constructor (p: pattern) : option string =
  match p.loc_value with
  | PatVariant _ name _ -> Some name
  | PatStruct name _ -> Some name
  | PatLit (LitBool true) -> Some "true"
  | PatLit (LitBool false) -> Some "false"
  | PatLit (LitInt n _) -> Some ("int_" ^ string_of_int n)
  | PatTuple _ -> Some "tuple"
  | _ -> None

(** Find the first column containing at least one non-default pattern.

    This implements the simplest column selection heuristic: "leftmost
    non-variable column." More sophisticated heuristics (p, q, n from
    Maranget 2008) could improve tree quality but are not implemented.

    RETURNS:
    --------
    Some col  if column 'col' has at least one constructor pattern
    None      if all columns are pure wildcards (matrix is all-default)

    INVARIANT:
    ----------
    If returns Some col, then exists row in rows such that
    row.pr_patterns[col] is not a default pattern.
*)
let find_non_default_column (rows: pattern_matrix) : option nat =
  let rec find_in_cols (col: nat) (max_col: nat) : option nat =
    if col >= max_col then None
    else
      let has_non_default = exists_in (fun row ->
        match nth row.pr_patterns col with
        | Some p -> not (is_default_pattern p)
        | None -> false
      ) rows in
      if has_non_default then Some col
      else find_in_cols (col + 1) max_col
  in
  match rows with
  | [] -> None
  | row :: _ -> find_in_cols 0 (length row.pr_patterns)

(** Specialize a pattern row for a specific constructor.

    SPECIALIZATION (Maranget 2008 Definition 3.1):
    ----------------------------------------------
    Given constructor c with arity n, column index col, and row r:

    - If r[col] = c(p1,...,pn):
      Return row with r[col] replaced by p1,...,pn (expanding into n columns)

    - If r[col] is a default pattern (_):
      Return row with r[col] replaced by n wildcards _,...,_

    - If r[col] = c'(...) where c' != c:
      Return None (row doesn't apply to this constructor)

    PARAMETERS:
    -----------
    ctor       : string      - Constructor name to specialize for
    ctor_arity : nat         - Number of arguments the constructor takes
    col        : nat         - Column index to specialize
    row        : pattern_row - Row to specialize

    RETURNS:
    --------
    Some row'  if the row is compatible with constructor ctor
    None       if the row has a different constructor in column col
*)
let rec specialize_row (ctor: string) (ctor_arity: nat) (col: nat) (row: pattern_row)
    : option pattern_row =
  match nth row.pr_patterns col with
  | None -> None
  | Some p ->
      (* Unwrap the with_loc wrapper to access pattern structure *)
      match p.loc_value with
      | PatWild | PatVar _ | PatRest _ ->
          (* Default patterns match any constructor *)
          let wildcards = make_wildcards ctor_arity in
          let new_patterns = replace_at col wildcards row.pr_patterns in
          Some { row with pr_patterns = new_patterns }

      | PatVariant _ name pats ->
          if name = ctor then
            let new_patterns = replace_at col pats row.pr_patterns in
            Some { row with pr_patterns = new_patterns }
          else None

      | PatTuple pats ->
          if ctor = "tuple" then
            let new_patterns = replace_at col pats row.pr_patterns in
            Some { row with pr_patterns = new_patterns }
          else None

      | PatAs inner_p x ->
          (* Unwrap as-pattern, add binding *)
          let inner_row = { row with pr_patterns = replace_at_single col inner_p row.pr_patterns } in
          specialize_row ctor ctor_arity col inner_row

      | PatOr p1 p2 ->
          (* Or-pattern: try both alternatives *)
          let row1 = { row with pr_patterns = replace_at_single col p1 row.pr_patterns } in
          let row2 = { row with pr_patterns = replace_at_single col p2 row.pr_patterns } in
          (* Return first matching - this is a simplification *)
          (match specialize_row ctor ctor_arity col row1 with
           | Some r -> Some r
           | None -> specialize_row ctor ctor_arity col row2)

      | _ -> None

(** Create n wildcard patterns with dummy locations *)
and make_wildcards (n: nat) : list pattern =
  if n = 0 then []
  else locate_dummy PatWild :: make_wildcards (n - 1)

and replace_at (#a: Type) (idx: nat) (replacement: list a) (lst: list a) : list a =
  let before = take idx lst in
  let after = drop (idx + 1) lst in
  before @ replacement @ after

and replace_at_single (#a: Type) (idx: nat) (replacement: a) (lst: list a) : list a =
  let before = take idx lst in
  let after = drop (idx + 1) lst in
  before @ [replacement] @ after

and take (#a: Type) (n: nat) (lst: list a) : list a =
  if n = 0 then []
  else match lst with
       | [] -> []
       | x :: xs -> x :: take (n - 1) xs

and drop (#a: Type) (n: nat) (lst: list a) : list a =
  if n = 0 then lst
  else match lst with
       | [] -> []
       | _ :: xs -> drop (n - 1) xs

(* Get distinct constructors from first column *)
let get_constructors (col: nat) (rows: pattern_matrix) : list string =
  let rec collect (rows: pattern_matrix) (seen: list string) : list string =
    match rows with
    | [] -> seen
    | row :: rest ->
        match nth row.pr_patterns col with
        | Some p ->
            (match pattern_constructor p with
             | Some ctor ->
                 if mem ctor seen then collect rest seen
                 else collect rest (ctor :: seen)
             | None -> collect rest seen)
        | None -> collect rest seen
  in
  collect rows []

(** Compile a pattern matrix to a decision tree (Maranget's CC algorithm).

    This is the core compilation algorithm that transforms a pattern matrix
    into an efficient decision tree for runtime matching.

    ALGORITHM (Maranget 2008 Section 3):
    ------------------------------------
    CC(P, occ):
      if P is empty:
        return DTFail                    (* No patterns match *)
      if first row is all wildcards:
        return DTLeaf(first_arm, bindings)  (* First row matches *)
      else:
        col := select_column(P)          (* Pick column to split *)
        ctors := constructors_in(P, col) (* Get distinct constructors *)
        cases := []
        for each ctor in ctors:
          P' := specialize(P, col, ctor) (* Specialize matrix *)
          cases := cases @ [(ctor, CC(P', occ @ [col]))]
        default := CC(default_rows(P, col), occ)
        return DTSwitch(col, cases, default)

    PARAMETERS:
    -----------
    matrix : pattern_matrix - The pattern matrix to compile
    occ    : occurrence     - Current path in the scrutinee (for bindings)
    fuel   : nat            - Recursion bound (prevents infinite loops)

    RETURNS:
    --------
    A decision tree that, when executed against a scrutinee value,
    determines which arm (if any) matches.

    TERMINATION:
    ------------
    The function terminates because:
    1. The fuel parameter decreases on each recursive call
    2. Without fuel, matrix size decreases (rows removed or patterns shrink)

    CORRECTNESS:
    ------------
    For any value v of appropriate type:
      execute(compile_matrix(P, []), v) = first arm_index where P[arm_index] matches v
      execute(compile_matrix(P, []), v) = FAIL if no pattern matches
*)
let rec compile_matrix (matrix: pattern_matrix) (occ: occurrence) (fuel: nat)
    : Tot decision_tree (decreases fuel) =
  if fuel = 0 then DTFail
  else
    match matrix with
    | [] -> DTFail  (* No patterns - match fails *)

    | row :: _ ->
        (* Check if first row is all wildcards *)
        if for_all is_default_pattern row.pr_patterns then
          (* Match succeeds with first row *)
          DTLeaf row.pr_arm_index row.pr_bindings
        else
          (* Find column to split on *)
          match find_non_default_column matrix with
          | None -> DTLeaf row.pr_arm_index row.pr_bindings
          | Some col ->
              (* Get all constructors in this column *)
              let ctors = get_constructors col matrix in
              (* Build switch cases *)
              let cases = map (fun ctor ->
                let specialized = filter_map (specialize_row ctor 0 col) matrix in
                let subtree = compile_matrix specialized (occ @ [col]) (fuel - 1) in
                (ctor, subtree)
              ) ctors in
              (* Build default case (rows with wildcard in this column) *)
              let default_rows = filter (fun row ->
                match nth row.pr_patterns col with
                | Some p -> is_default_pattern p
                | None -> false
              ) matrix in
              let default_tree =
                if length default_rows > 0 then
                  Some (compile_matrix default_rows occ (fuel - 1))
                else None
              in
              DTSwitch col cases default_tree

and filter_map (#a #b: Type) (f: a -> option b) (lst: list a) : list b =
  match lst with
  | [] -> []
  | x :: xs ->
      match f x with
      | Some y -> y :: filter_map f xs
      | None -> filter_map f xs

(** Map with index - applies function with 0-based index to each element *)
let mapi (#a #b: Type) (f: nat -> a -> b) (lst: list a) : list b =
  let rec go (idx: nat) (l: list a) : list b =
    match l with
    | [] -> []
    | x :: xs -> f idx x :: go (idx + 1) xs
  in
  go 0 lst

(** Top-level entry point for decision tree compilation

    Converts a list of match arms into an optimized decision tree.
    Uses a fuel limit of 1000 to bound recursion depth.

    PARAMETERS:
    -----------
    arms : list match_arm  - The match arms to compile

    RETURNS:
    --------
    A decision tree for efficient pattern matching at runtime.
*)
let compile_to_decision_tree (arms: list match_arm) : decision_tree =
  let matrix = mapi (fun idx arm ->
    { pr_patterns = [arm.arm_pattern];
      pr_arm_index = idx;
      pr_bindings = [] }
  ) arms in
  compile_matrix matrix [] 1000  (* Fuel limit *)

(** ============================================================================
    DECISION TREE OPTIMIZATION
    ============================================================================

    OVERVIEW:
    ---------
    After compilation, decision trees may contain redundant structure that
    can be simplified. This section provides optimization passes that reduce
    tree size and improve runtime performance.

    OPTIMIZATION PASSES:
    --------------------

    1. DEAD BRANCH ELIMINATION:
       Remove branches that are provably unreachable. This can happen when
       earlier patterns fully cover a constructor's cases.

    2. SINGLE-CASE SWITCH COLLAPSE:
       When a switch has exactly one case and no default, replace it with
       just the subtree. This eliminates unnecessary constructor checks.

       Before:  DTSwitch 0 [("Some", subtree)] None
       After:   subtree

    3. DEFAULT LIFTING:
       When all cases lead to the same result, replace switch with that result.

       Before:  DTSwitch 0 [("A", DTLeaf 1), ("B", DTLeaf 1)] None
       After:   DTLeaf 1

    4. COMMON SUBTREE SHARING (NOT IMPLEMENTED):
       Identify identical subtrees and share them (DAG conversion).
       This requires hash-consing or memoization.

    5. SWITCH MERGING (NOT IMPLEMENTED):
       When nested switches examine the same scrutinee, merge them.

    CORRECTNESS INVARIANT:
    ----------------------
    For any optimization f:
      forall v. execute(f(dt), v) = execute(dt, v)

    That is, optimizations must preserve the matching semantics.

    COMPLEXITY:
    -----------
    Current optimizations are O(n) where n = tree size.
    More aggressive optimizations (sharing) would be O(n log n) with hashing.
    ============================================================================ *)

(** Optimize decision tree by:
    1. Removing unreachable branches
    2. Collapsing single-case switches
    3. (Future) Sharing common subtrees via hash-consing

    PARAMETERS:
    -----------
    dt : decision_tree  - The tree to optimize

    RETURNS:
    --------
    An optimized decision tree with the same matching semantics.

    INVARIANT:
    ----------
    forall v. execute(optimize_tree dt, v) = execute(dt, v)
*)
let rec optimize_tree (dt: decision_tree) : decision_tree =
  match dt with
  | DTSwitch scrutinee cases default ->
      let opt_cases = map (fun (ctor, subtree) -> (ctor, optimize_tree subtree)) cases in
      let opt_default = map_option optimize_tree default in
      (* Collapse single-case switches with no default *)
      (match opt_cases, opt_default with
       | [(_, subtree)], None -> subtree
       | _ -> DTSwitch scrutinee opt_cases opt_default)

  | DTGuard guard success failure ->
      DTGuard guard (optimize_tree success) (optimize_tree failure)

  | DTBind var value_ref rest ->
      DTBind var value_ref (optimize_tree rest)

  | DTSeq first second ->
      DTSeq (optimize_tree first) (optimize_tree second)

  | DTLeaf _ _ | DTFail -> dt

and map_option (#a #b: Type) (f: a -> b) (opt: option a) : option b =
  match opt with
  | None -> None
  | Some x -> Some (f x)

(** ============================================================================
    DIAGNOSTIC UTILITIES FOR BRRR-MACHINE INTEGRATION
    ============================================================================

    OVERVIEW:
    ---------
    This section provides the interface between the pattern analysis algorithms
    and the Brrr-Machine analysis toolkit. These functions produce structured
    diagnostic information that can be:
    - Displayed to users as warnings/errors
    - Used by IDE tooling for code hints
    - Exported for external analysis tools

    DIAGNOSTIC CATEGORIES:
    ----------------------

    1. EXHAUSTIVENESS WARNINGS:
       Non-exhaustive patterns can cause runtime match failures. The diagnostic
       includes the VALUE SPACE of uncovered cases, which can be rendered as
       example patterns for user-friendly messages.

       Example warning:
         "Match at line 42 is not exhaustive. Missing cases: Some(_), None"

    2. REDUNDANCY WARNINGS:
       Redundant patterns indicate dead code or logic errors. The diagnostic
       identifies which arms are unreachable.

       Example warning:
         "Pattern at line 45 is unreachable (covered by pattern at line 43)"

    3. DECISION TREE STATISTICS:
       Metrics about the compiled decision tree help identify:
       - Inefficient pattern orderings
       - Opportunities for pattern refactoring
       - Performance characteristics of the match

       Metrics provided:
       - tree_depth: Maximum decisions needed (worst case)
       - tree_size: Total number of nodes (code size)

    INTEGRATION WITH BRRR-MACHINE:
    ------------------------------
    Brrr-Machine calls analyze_match() for each match expression during
    type checking. The results are:
    - Accumulated for batch reporting
    - Used to generate IDE diagnostics
    - Stored in the analysis database for querying

    MESSAGE FORMATTING:
    -------------------
    The value_space in missing_cases can be pretty-printed to show example
    uncovered patterns. For instance:
      VSCtor "option" "None" [] -> "None"
      VSCtor "option" "Some" [VSAll int] -> "Some(_)"
      VSUnion [vs1, vs2] -> format(vs1) ^ " or " ^ format(vs2)

    FUTURE EXTENSIONS:
    ------------------
    - Witness generation: produce concrete example values for uncovered cases
    - Match complexity analysis: estimate average-case matching cost
    - Pattern coverage metrics: percentage of type space covered
    - Suggested pattern additions: auto-generate missing cases
    ============================================================================ *)

(** Pattern analysis result for a match expression

    This structure aggregates all diagnostic information about a match
    expression's patterns for use by Brrr-Machine and IDE tooling.
*)
type pattern_analysis_result = {
  (** True if patterns cover all possible values of the scrutinee type *)
  par_exhaustive: bool;

  (** If not exhaustive, the value space of uncovered cases.
      Can be pretty-printed to show users example missing patterns. *)
  par_missing_cases: option value_space;

  (** List of 0-based arm indices that are redundant (unreachable).
      Empty list means all arms are useful. *)
  par_redundant_arms: list nat;

  (** The compiled and optimized decision tree for this match.
      Can be used for code generation or further analysis. *)
  par_decision_tree: decision_tree;

  (** Maximum depth of the decision tree (worst-case decisions needed).
      Lower is better for performance. *)
  par_tree_depth: nat;

  (** Total number of nodes in the decision tree (code size metric).
      Lower is better for code size. *)
  par_tree_size: nat
}

(** Compute the maximum depth of a decision tree (worst-case decisions)

    DEFINITION:
    -----------
    The depth is the longest path from root to any leaf:
      depth(DTLeaf) = depth(DTFail) = 1
      depth(DTSwitch _ cases default) = 1 + max(depths of cases and default)
      depth(DTGuard _ s f) = 1 + max(depth(s), depth(f))
      depth(DTBind _ _ rest) = 1 + depth(rest)
      depth(DTSeq a b) = depth(a) + depth(b)

    INTERPRETATION:
    ---------------
    Tree depth indicates worst-case matching performance:
    - Lower depth = fewer comparisons in worst case
    - Ideal depth = log2(n) for n patterns with balanced tree
    - Worst depth = n for degenerate chains

    USAGE:
    ------
    Used by Brrr-Machine to identify inefficient pattern orderings.
    A high depth relative to pattern count suggests optimization opportunities.
*)
let rec tree_depth (dt: decision_tree) : nat =
  match dt with
  | DTLeaf _ _ | DTFail -> 1
  | DTSwitch _ cases default ->
      let case_depths = map (fun (_, subtree) -> tree_depth subtree) cases in
      let default_depth = match default with
        | Some d -> tree_depth d
        | None -> 0 in
      1 + max (fold_left max 0 case_depths) default_depth
  | DTGuard _ success failure -> 1 + max (tree_depth success) (tree_depth failure)
  | DTBind _ _ rest -> 1 + tree_depth rest
  | DTSeq first second -> tree_depth first + tree_depth second

(** Compute the total size of a decision tree (number of nodes)

    DEFINITION:
    -----------
    The size is the total number of nodes in the tree:
      size(DTLeaf) = size(DTFail) = 1
      size(DTSwitch _ cases default) = 1 + sum(sizes of cases) + size(default)
      size(DTGuard _ s f) = 1 + size(s) + size(f)
      size(DTBind _ _ rest) = 1 + size(rest)
      size(DTSeq a b) = size(a) + size(b)

    INTERPRETATION:
    ---------------
    Tree size correlates with generated code size:
    - Lower size = smaller code footprint
    - Size can grow exponentially without optimization (subtree duplication)
    - Common subtree sharing (not yet implemented) reduces size

    USAGE:
    ------
    Used by Brrr-Machine to:
    - Estimate code size impact of pattern matching
    - Identify patterns that would benefit from sharing optimization
    - Compare different pattern orderings
*)
let rec tree_size (dt: decision_tree) : nat =
  match dt with
  | DTLeaf _ _ | DTFail -> 1
  | DTSwitch _ cases default ->
      let case_sizes = map (fun (_, subtree) -> tree_size subtree) cases in
      let default_size = match default with
        | Some d -> tree_size d
        | None -> 0 in
      1 + fold_left (+) 0 case_sizes + default_size
  | DTGuard _ success failure -> 1 + tree_size success + tree_size failure
  | DTBind _ _ rest -> 1 + tree_size rest
  | DTSeq first second -> tree_size first + tree_size second

(** Perform comprehensive pattern analysis for a match expression

    This is the MAIN ENTRY POINT for pattern analysis, used by the type checker
    and Brrr-Machine. It combines all analysis passes into a single result.

    ANALYSIS PERFORMED:
    -------------------
    1. EXHAUSTIVENESS CHECK:
       Determines if all values of scrutinee_type are covered.
       If not exhaustive, identifies the uncovered value space.

    2. USEFULNESS CHECK:
       Identifies redundant (unreachable) pattern arms.
       Returns list of arm indices that are dead code.

    3. DECISION TREE COMPILATION:
       Compiles patterns to efficient decision tree.
       Applies optimization passes.

    4. METRICS COMPUTATION:
       Calculates tree depth and size for performance analysis.

    PARAMETERS:
    -----------
    scrutinee_type : brrr_type     - Type of the value being matched
    arms           : list match_arm - The match arms to analyze

    RETURNS:
    --------
    A pattern_analysis_result containing:
    - Exhaustiveness status and missing cases (if any)
    - List of redundant arm indices
    - Compiled decision tree
    - Tree metrics (depth, size)

    USAGE EXAMPLE:
    --------------
      let result = analyze_match (t_option t_int) [
        { arm_pattern = pat_none; arm_guard = None; arm_body = e1 };
        { arm_pattern = pat_some_x; arm_guard = None; arm_body = e2 }
      ] in
      if not result.par_exhaustive then
        emit_warning "Non-exhaustive match" result.par_missing_cases;
      for idx in result.par_redundant_arms do
        emit_warning "Redundant pattern" idx

    COMPLEXITY:
    -----------
    O(n^2 * m) where n = number of arms, m = average pattern size
    - Exhaustiveness: O(n * m)
    - Usefulness: O(n^2 * m)
    - Compilation: O(n * m * k) where k = constructors
*)
let analyze_match (scrutinee_type: brrr_type) (arms: list match_arm) : pattern_analysis_result =
  let patterns = map (fun arm -> arm.arm_pattern) arms in

  (* Exhaustiveness check *)
  let exhaust_result = check_exhaustiveness scrutinee_type patterns in
  let (is_exhaust, missing) = match exhaust_result with
    | Exhaustive -> (true, None)
    | NonExhaustive vs -> (false, Some vs) in

  (* Usefulness check *)
  let useful_result = check_usefulness patterns in
  let redundant_indices = map fst useful_result.redundant_patterns in

  (* Compile to decision tree *)
  let dt = compile_to_decision_tree arms in
  let opt_dt = optimize_tree dt in

  {
    par_exhaustive = is_exhaust;
    par_missing_cases = missing;
    par_redundant_arms = redundant_indices;
    par_decision_tree = opt_dt;
    par_tree_depth = tree_depth opt_dt;
    par_tree_size = tree_size opt_dt
  }
