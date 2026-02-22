(**
 * BrrrLang.Core.PatternAnalysis Interface
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
 *   Definition 2.9 (Redundancy):
 *   Pattern p_i is redundant iff:
 *     [[p_i]] subseteq Union_{j < i} [[p_j]]
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
    irrelevant for pattern analysis.
    ============================================================================ *)

(** Alias for top/unknown type for pattern analysis. Used when type
    information is unavailable or irrelevant for structural pattern matching. *)
val t_top : brrr_type

(** ============================================================================
    VALUE SPACE REPRESENTATION
    ============================================================================

    A value space is an abstract representation of a set of values. This is
    the core data structure for pattern analysis, enabling symbolic manipulation
    of potentially infinite value sets without enumeration.

    FORMAL SEMANTICS:
    -----------------
    Each value space constructor has a set-theoretic interpretation:

      [[VSAll ty]]        = { v | v : ty }
      [[VSCtor T C sps]]  = { C(v_1, ..., v_n) | v_i in [[sps_i]] }
      [[VSPair sp1 sp2]]  = [[sp1]] x [[sp2]]
      [[VSTuple sps]]     = [[sps_1]] x ... x [[sps_n]]
      [[VSUnion sps]]     = Union_i [[sps_i]]
      [[VSIntersect sps]] = Intersect_i [[sps_i]]
      [[VSComplement sp]] = U \ [[sp]]
      [[VSEmpty]]         = {}
      [[VSLiteral lit]]   = { lit }
      [[VSRange lo hi]]   = { n in Z | lo <= n <= hi }
      [[VSArray sp n]]    = [[sp]]^n
      [[VSAnyArray sp]]   = Union_{n>=0} [[sp]]^n
    ============================================================================ *)

(** Abstract representation of a set of values for pattern analysis.
    Uses noeq to prevent F* from generating decidable equality,
    which would be impossible due to recursive structure. *)
noeq type value_space =
  (** Universal set: all values of a given type *)
  | VSAll        : brrr_type -> value_space

  (** Constructor application: C(vs_1, ..., vs_n) where each vs_i is a value space.
      The type_name identifies the ADT, string is the constructor/variant name. *)
  | VSCtor       : type_name -> string -> list value_space -> value_space

  (** Binary product (pair): values (v1, v2) where v1 in sp1 and v2 in sp2 *)
  | VSPair       : value_space -> value_space -> value_space

  (** n-ary product (tuple): values (v1, ..., vn) where v_i in sps[i] *)
  | VSTuple      : list value_space -> value_space

  (** Set union: values in ANY of the given spaces *)
  | VSUnion      : list value_space -> value_space

  (** Set intersection: values in ALL of the given spaces *)
  | VSIntersect  : list value_space -> value_space

  (** Set complement: values NOT in the given space (relative to universe) *)
  | VSComplement : value_space -> value_space

  (** Empty set: matches no values *)
  | VSEmpty      : value_space

  (** Singleton literal: exactly one specific literal value *)
  | VSLiteral    : literal -> value_space

  (** Integer range [lo, hi] inclusive: {n in Z | lo <= n <= hi} *)
  | VSRange      : int -> int -> value_space

  (** Fixed-length array: arrays of exactly n elements from space *)
  | VSArray      : value_space -> nat -> value_space

  (** Variable-length array: arrays of any length from space *)
  | VSAnyArray   : value_space -> value_space

(** ============================================================================
    VALUE SPACE SIZE (for termination proofs)
    ============================================================================

    The value_space_size function provides a well-founded measure that
    decreases on all recursive calls through value space operations.
    Used in decreases clauses of recursive functions.

    PROPERTIES:
    -----------
    - value_space_size vs >= 1 for all vs
    - For composite spaces, size > sum of component sizes
    ============================================================================ *)

(** Compute the structural size of a value space.
    Used as termination measure for recursive operations.
    Guaranteed to be at least 1 for all value spaces. *)
val value_space_size (vs: value_space) : Tot nat (decreases vs)

(** Compute the total size of a list of value spaces.
    Helper for value_space_size on composite spaces. *)
val value_space_list_size (sps: list value_space) : Tot nat (decreases sps)

(** ============================================================================
    VALUE SPACE OPERATIONS
    ============================================================================

    Core operations on value spaces for exhaustiveness and usefulness checking.
    ============================================================================ *)

(** Check if a value space represents the empty set (SOUND but INCOMPLETE).

    ALGORITHM:
    ----------
    - VSEmpty: trivially empty
    - VSUnion: empty iff ALL components are empty
    - VSIntersect: empty if ANY component is empty
    - VSTuple/VSPair: empty if ANY component is empty
    - VSRange lo hi: empty if lo > hi

    NOTE: May return false for empty spaces due to incompleteness.
    Complete emptiness checking would require semantic analysis.

    COMPLEXITY: O(size of value_space) *)
val is_empty (vs: value_space) : Tot bool (decreases value_space_size vs)

(** Check if predicate holds for any element in list.
    Short-circuits on first match. *)
val exists_in (#a: Type) (f: a -> bool) (l: list a) : bool

(** Simplify value space by removing empty components and collapsing trivial cases.

    SIMPLIFICATION RULES:
    ---------------------
    - VSUnion []: VSEmpty
    - VSUnion [sp]: simplify(sp)
    - VSUnion sps: filter out empty components
    - VSIntersect with empty: VSEmpty
    - VSTuple/VSPair with empty component: VSEmpty

    INVARIANT: [[simplify(vs)]] = [[vs]]

    COMPLEXITY: O(size of value_space) *)
val simplify (vs: value_space) : Tot value_space (decreases value_space_size vs)

(** ============================================================================
    PATTERN TO VALUE SPACE CONVERSION
    ============================================================================

    The denotation function [[p]] that maps a pattern p to the set of values
    it matches. This bridges the syntactic world of patterns and the semantic
    world of value spaces.
    ============================================================================ *)

(** Convert a pattern to its corresponding value space.

    PARAMETERS:
    -----------
    p  : pattern    - The pattern to convert
    ty : brrr_type  - The type of values the pattern should match

    RETURNS:
    --------
    A value_space representing all values that pattern p matches.

    INVARIANT:
    ----------
    A value v is in [[pattern_to_space p ty]] iff matching v against p succeeds.

    GUARD HANDLING (CONSERVATIVE):
    ------------------------------
    Guard patterns (p when cond) return the space of the inner pattern p.
    The guard condition is ignored for analysis. *)
val pattern_to_space (p: pattern) (ty: brrr_type) : value_space

(** Map two lists with a function, returning empty list on length mismatch. *)
val map2_default (#a #b #c: Type) (f: a -> b -> c) (l1: list a) (l2: list b) (default: c) : list c

(** ============================================================================
    SUBTRACT PATTERN FROM VALUE SPACE (Core Exhaustiveness Algorithm)
    ============================================================================

    The subtraction operation computes: vs \ [[p]]
    That is, the set of values in vs that are NOT matched by pattern p.

    EXHAUSTIVENESS ALGORITHM:
    -------------------------
    1. remaining := VSAll T
    2. for each pattern p_i: remaining := subtract_pattern(remaining, p_i)
    3. return is_empty(remaining)
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

    GUARD HANDLING (CONSERVATIVE):
    ------------------------------
    For guard patterns (p when cond), no subtraction is performed.
    This is conservative: may produce false non-exhaustive warnings
    but never silent match failures.

    COMPLEXITY: O(|vs| * |p|) *)
val subtract_pattern (vs: value_space) (p: pattern)
  : Tot value_space (decreases (value_space_size vs, pattern_size p))

(** Subtract patterns from corresponding value spaces element-wise. *)
val subtract_pattern_list (sps: list value_space) (pats: list pattern)
  : Tot (list value_space) (decreases (value_space_list_size sps, pattern_list_size pats))

(** Subtract a tuple pattern from a tuple value space. *)
val subtract_tuple_patterns (sps: list value_space) (pats: list pattern) : value_space

(** ============================================================================
    EXHAUSTIVENESS CHECKING
    ============================================================================

    Check if patterns exhaustively cover all values of a type.
    ============================================================================ *)

(** Check if patterns exhaustively cover all values of a type.

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

    COMPLEXITY: O(n * m) where n = patterns, m = pattern size *)
val is_exhaustive (ty: brrr_type) (patterns: list pattern) : bool

(** Result of exhaustiveness checking with witness for non-exhaustive cases *)
type exhaustiveness_result =
  | Exhaustive : exhaustiveness_result
  | NonExhaustive : value_space -> exhaustiveness_result

(** Check exhaustiveness and return witness of missing case if not exhaustive.

    Returns Exhaustive if all values are covered.
    Returns NonExhaustive with the uncovered value space otherwise. *)
val check_exhaustiveness (ty: brrr_type) (patterns: list pattern) : exhaustiveness_result

(** ============================================================================
    USEFULNESS PREDICATE AND REDUNDANCY CHECKING
    ============================================================================

    A pattern is useful if it matches at least one value not covered by
    previous patterns. A redundant pattern is one that is not useful.
    ============================================================================ *)

(** Check if a pattern is useful (matches something not already covered).

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
    If is_useful returns false, the pattern is definitely redundant. *)
val is_useful (covered: value_space) (p: pattern) : bool

(** Compute the useful portion of a pattern space.
    Returns pattern_space intersected with complement of covered. *)
val compute_useful_space (covered: value_space) (pattern_space: value_space) : value_space

(** Result of usefulness checking for all patterns *)
type usefulness_result = {
  useful_patterns: list (nat & pattern);    (** 0-based index and useful pattern *)
  redundant_patterns: list (nat & pattern)  (** 0-based index and redundant pattern *)
}

(** Check usefulness of each pattern and return categorized results.

    RETURNS:
    --------
    A usefulness_result containing:
    - useful_patterns: (index, pattern) pairs for patterns that add coverage
    - redundant_patterns: (index, pattern) pairs for unreachable patterns

    COMPLEXITY: O(n^2 * m) where n = patterns, m = pattern size *)
val check_usefulness (patterns: list pattern) : usefulness_result

(** ============================================================================
    DECISION TREE REPRESENTATION
    ============================================================================

    Decision trees provide efficient compiled pattern matching.
    O(d) per match where d = scrutinee depth, instead of O(n) sequential.
    ============================================================================ *)

(** Decision tree for compiled pattern matching.

    STRUCTURE:
    ----------
    DTLeaf: Match succeeded, execute arm with bindings
    DTFail: Match failed (unreachable if patterns exhaustive)
    DTSwitch: Branch on constructor tag
    DTGuard: Evaluate guard condition and branch
    DTBind: Bind variable to scrutinee component
    DTSeq: Sequential composition *)
type decision_tree =
  (** Match succeeded - execute arm with given bindings
      arm_index: 0-based index into the original match arm list
      bindings: list of (variable_name, occurrence_index) pairs *)
  | DTLeaf   : arm_index:nat -> bindings:list (var_id & nat) -> decision_tree

  (** Match failed - should be unreachable if patterns are exhaustive *)
  | DTFail   : decision_tree

  (** Branch on constructor tag at given scrutinee position
      scrutinee: index into the scrutinee
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

(** Occurrence: Path to a sub-value within the scrutinee.
    Example: [0, 1] means first element, then second sub-element *)
type occurrence = list nat

(** A row in the pattern compilation matrix *)
type pattern_row = {
  pr_patterns: list pattern;               (** Pattern vector for this row *)
  pr_arm_index: nat;                       (** Index of the corresponding match arm *)
  pr_bindings: list (var_id & occurrence)  (** Accumulated variable bindings *)
}

(** The pattern matrix being compiled *)
type pattern_matrix = list pattern_row

(** ============================================================================
    DECISION TREE COMPILATION
    ============================================================================

    Maranget's algorithm for compiling pattern matrices into decision trees.
    ============================================================================ *)

(** Check if pattern is a "default" pattern (matches anything).
    Default patterns are wildcards, variables, and rest patterns. *)
val is_default_pattern (p: pattern) : bool

(** Extract constructor name from a pattern, if it has one.
    Returns None for default patterns. *)
val pattern_constructor (p: pattern) : option string

(** Find the first column containing at least one non-default pattern.
    Implements the simplest column selection heuristic. *)
val find_non_default_column (rows: pattern_matrix) : option nat

(** Specialize a pattern row for a specific constructor.

    PARAMETERS:
    -----------
    ctor       : string      - Constructor name to specialize for
    ctor_arity : nat         - Number of arguments the constructor takes
    col        : nat         - Column index to specialize
    row        : pattern_row - Row to specialize

    RETURNS:
    --------
    Some row'  if the row is compatible with constructor ctor
    None       if the row has a different constructor in column col *)
val specialize_row (ctor: string) (ctor_arity: nat) (col: nat) (row: pattern_row)
  : option pattern_row

(** Create n wildcard patterns with dummy locations *)
val make_wildcards (n: nat) : list pattern

(** Replace element at index with a list of replacements *)
val replace_at (#a: Type) (idx: nat) (replacement: list a) (lst: list a) : list a

(** Replace single element at index *)
val replace_at_single (#a: Type) (idx: nat) (replacement: a) (lst: list a) : list a

(** Take first n elements from list *)
val take (#a: Type) (n: nat) (lst: list a) : list a

(** Drop first n elements from list *)
val drop (#a: Type) (n: nat) (lst: list a) : list a

(** Get distinct constructors from specified column in pattern matrix *)
val get_constructors (col: nat) (rows: pattern_matrix) : list string

(** Compile a pattern matrix to a decision tree.

    PARAMETERS:
    -----------
    matrix : pattern_matrix - The pattern matrix to compile
    occ    : occurrence     - Current path in the scrutinee
    fuel   : nat            - Recursion bound

    RETURNS:
    --------
    A decision tree for runtime pattern matching.

    ALGORITHM (Maranget 2008):
    --------------------------
    1. Empty matrix: DTFail
    2. First row all wildcards: DTLeaf
    3. Otherwise: split on selected column, specialize, recurse

    COMPLEXITY: O(n * m * k) where n = rows, m = columns, k = constructors *)
val compile_matrix (matrix: pattern_matrix) (occ: occurrence) (fuel: nat)
  : Tot decision_tree (decreases fuel)

(** Filter list keeping only elements where function returns Some *)
val filter_map (#a #b: Type) (f: a -> option b) (lst: list a) : list b

(** Map with 0-based index *)
val mapi (#a #b: Type) (f: nat -> a -> b) (lst: list a) : list b

(** Top-level entry point for decision tree compilation.

    PARAMETERS:
    -----------
    arms : list match_arm  - The match arms to compile

    RETURNS:
    --------
    A decision tree for efficient pattern matching at runtime.
    Uses fuel limit of 1000 to bound recursion depth. *)
val compile_to_decision_tree (arms: list match_arm) : decision_tree

(** ============================================================================
    DECISION TREE OPTIMIZATION
    ============================================================================

    Optimization passes that reduce tree size and improve runtime performance.
    ============================================================================ *)

(** Optimize decision tree by removing redundant structure.

    OPTIMIZATION PASSES:
    --------------------
    1. Dead branch elimination
    2. Single-case switch collapse
    3. Default lifting (when all cases are identical)

    INVARIANT:
    ----------
    forall v. execute(optimize_tree dt, v) = execute(dt, v) *)
val optimize_tree (dt: decision_tree) : decision_tree

(** Map function over option value *)
val map_option (#a #b: Type) (f: a -> b) (opt: option a) : option b

(** ============================================================================
    DIAGNOSTIC UTILITIES FOR BRRR-MACHINE INTEGRATION
    ============================================================================

    Interface between pattern analysis algorithms and Brrr-Machine toolkit.
    ============================================================================ *)

(** Comprehensive pattern analysis result for a match expression *)
type pattern_analysis_result = {
  (** True if patterns cover all possible values of the scrutinee type *)
  par_exhaustive: bool;

  (** If not exhaustive, the value space of uncovered cases.
      Can be pretty-printed to show example missing patterns. *)
  par_missing_cases: option value_space;

  (** List of 0-based arm indices that are redundant (unreachable) *)
  par_redundant_arms: list nat;

  (** The compiled and optimized decision tree for this match *)
  par_decision_tree: decision_tree;

  (** Maximum depth of the decision tree (worst-case decisions needed) *)
  par_tree_depth: nat;

  (** Total number of nodes in the decision tree (code size metric) *)
  par_tree_size: nat
}

(** Compute the maximum depth of a decision tree.

    INTERPRETATION:
    ---------------
    Tree depth indicates worst-case matching performance:
    - Lower depth = fewer comparisons in worst case
    - Ideal depth = log2(n) for n patterns with balanced tree *)
val tree_depth (dt: decision_tree) : nat

(** Compute the total size of a decision tree (number of nodes).

    INTERPRETATION:
    ---------------
    Tree size correlates with generated code size:
    - Lower size = smaller code footprint *)
val tree_size (dt: decision_tree) : nat

(** Perform comprehensive pattern analysis for a match expression.

    This is the MAIN ENTRY POINT for pattern analysis, used by the type checker
    and Brrr-Machine.

    ANALYSIS PERFORMED:
    -------------------
    1. Exhaustiveness check with uncovered value space
    2. Usefulness check with redundant arm identification
    3. Decision tree compilation with optimization
    4. Tree metrics computation (depth, size)

    PARAMETERS:
    -----------
    scrutinee_type : brrr_type      - Type of the value being matched
    arms           : list match_arm - The match arms to analyze

    RETURNS:
    --------
    A pattern_analysis_result containing all diagnostic information.

    COMPLEXITY:
    -----------
    O(n^2 * m) where n = number of arms, m = average pattern size *)
val analyze_match (scrutinee_type: brrr_type) (arms: list match_arm) : pattern_analysis_result
