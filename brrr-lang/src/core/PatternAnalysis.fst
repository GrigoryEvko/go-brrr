(**
 * BrrrLang.Core.PatternAnalysis
 *
 * Pattern analysis for exhaustiveness checking, redundancy detection,
 * and efficient pattern matching via decision trees.
 *
 * Based on brrr_lang_spec_v0.4.tex Definition 2.8 (Exhaustiveness) and
 * Definition 2.9 (Redundancy).
 *
 * Key algorithms:
 * - is_exhaustive: Check if patterns cover all values of a type
 * - is_useful: Check if a pattern matches something not yet covered
 * - compile_to_decision_tree: Compile patterns to efficient matching code
 *
 * Depends on: Primitives, BrrrTypes, Expressions, Values
 *)
module PatternAnalysis

open Primitives
open BrrrTypes
open Expressions
open Values
open FStar.List.Tot

(* Alias for top/unknown type for pattern analysis *)
let t_top : brrr_type = t_unknown

(** ============================================================================
    VALUE SPACE REPRESENTATION
    ============================================================================

    A value space represents a set of values that could be matched.
    Used for both exhaustiveness checking (what values remain uncovered)
    and usefulness checking (does a pattern cover anything new).

    - VSAll ty:        All values of type ty
    - VSCtor name sps: Values matching constructor name with sub-spaces for args
    - VSPair sp1 sp2:  Product space (tuples/pairs)
    - VSUnion sps:     Union of value spaces
    - VSIntersect sps: Intersection of value spaces
    - VSComplement sp: Complement of a space
    - VSEmpty:         No values (empty set)
    - VSLiteral lit:   Single literal value
    - VSRange lo hi:   Integer range [lo, hi]
*)

noeq type value_space =
  | VSAll        : brrr_type -> value_space
  | VSCtor       : type_name -> string -> list value_space -> value_space
  | VSPair       : value_space -> value_space -> value_space
  | VSTuple      : list value_space -> value_space
  | VSUnion      : list value_space -> value_space
  | VSIntersect  : list value_space -> value_space
  | VSComplement : value_space -> value_space
  | VSEmpty      : value_space
  | VSLiteral    : literal -> value_space
  | VSRange      : int -> int -> value_space  (* Integer range [lo, hi] inclusive *)
  | VSArray      : value_space -> nat -> value_space  (* Array of n elements from space *)
  | VSAnyArray   : value_space -> value_space  (* Array of any length *)

(** ============================================================================
    VALUE SPACE SIZE (for termination)
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
    ============================================================================ *)

(* Check if value space is empty *)
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

and exists_in (#a: Type) (f: a -> bool) (l: list a) : bool =
  match l with
  | [] -> false
  | x :: xs -> f x || exists_in f xs

(* Simplify value space by removing empty components *)
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

    Convert a pattern to the value space it matches.
    Used for exhaustiveness and usefulness checking.
*)

let rec pattern_to_space (p: pattern) (ty: brrr_type) : value_space =
  match p with
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
      VSCtor ty_name "struct" (map (fun (_, p) -> pattern_to_space p t_top) field_pats)

  | PatVariant ty_name var_name pats ->
      (* Variant/enum pattern *)
      VSCtor ty_name var_name (map (fun p -> pattern_to_space p t_top) pats)

  | PatOr p1 p2 ->
      VSUnion [pattern_to_space p1 ty; pattern_to_space p2 ty]

  | PatGuard p _ ->
      (* Guard patterns are partial - conservatively treat as the inner pattern.
         For precise analysis, would need to evaluate the guard symbolically. *)
      pattern_to_space p ty

  | PatRef p' ->
      (match ty with
       | TWrap WRef inner_ty -> pattern_to_space p' inner_ty
       | TWrap WRefMut inner_ty -> pattern_to_space p' inner_ty
       | _ -> VSEmpty)

  | PatBox p' ->
      (match ty with
       | TWrap WBox inner_ty -> pattern_to_space p' inner_ty
       | TModal _ inner_ty -> pattern_to_space p' inner_ty  (* Box modality *)
       | _ -> VSEmpty)

  | PatRest _ ->
      (* Rest pattern matches any remaining elements - treated as VSAll *)
      VSAll ty

  | PatAs p' _ ->
      (* As-pattern matches same as inner pattern *)
      pattern_to_space p' ty

and map2_default (#a #b #c: Type) (f: a -> b -> c) (l1: list a) (l2: list b) (default: c) : list c =
  match l1, l2 with
  | [], [] -> []
  | x :: xs, y :: ys -> f x y :: map2_default f xs ys default
  | _, _ -> []  (* Length mismatch *)

(** ============================================================================
    SUBTRACT PATTERN FROM VALUE SPACE
    ============================================================================

    Given a value space and a pattern, compute the remaining value space
    after removing all values that match the pattern.

    This is the core operation for exhaustiveness checking:
    - Start with VSAll ty
    - Subtract each pattern in order
    - If result is VSEmpty, patterns are exhaustive
*)

let rec subtract_pattern (vs: value_space) (p: pattern) : Tot value_space (decreases (value_space_size vs, pattern_size p)) =
  match vs with
  | VSEmpty -> VSEmpty

  | VSAll ty ->
      (* Subtracting from "all values" - need to consider pattern structure *)
      (match p with
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
           VSComplement (VSCtor ty_name "struct" (map (fun (_, p) -> pattern_to_space p t_top) field_pats)))

  | VSCtor ty_name ctor_name sps ->
      (match p with
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
      (match p with
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
      (match p with
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

    Check if a list of patterns exhaustively covers all values of a type.

    Algorithm:
    1. Start with VSAll ty (all values of the type)
    2. For each pattern, subtract the matched values
    3. If result is VSEmpty, patterns are exhaustive

    Definition 2.8 from spec:
    Patterns p_1, ..., p_n are exhaustive for type T iff:
    forall v : T. exists i. v in [[p_i]]
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
    USEFULNESS / REDUNDANCY CHECKING
    ============================================================================

    Check if a pattern is useful (matches something not covered by previous patterns).
    A pattern is redundant if it's not useful.

    Definition 2.9 from spec:
    Pattern p_i is redundant iff:
    [[p_i]] subseteq Union_{j < i} [[p_j]]

    Equivalently, p_i is useful iff:
    [[p_i]] intersect (complement of Union_{j < i} [[p_j]]) is non-empty
*)

(* Check if a pattern is useful given already-covered space *)
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

    Decision trees provide efficient compiled pattern matching.
    Instead of checking patterns sequentially, we compile them into
    a tree structure that examines each scrutinee component at most once.

    Structure:
    - DTLeaf: Match succeeded, execute arm body with bindings
    - DTFail: Match failed (should be unreachable if exhaustive)
    - DTSwitch: Branch based on constructor/variant tag
    - DTGuard: Check a guard condition
    - DTBind: Bind a value to a variable, continue
*)

type decision_tree =
  | DTLeaf   : arm_index:nat -> bindings:list (var_id & nat) -> decision_tree
  | DTFail   : decision_tree
  | DTSwitch : scrutinee:nat -> cases:list (string & decision_tree) -> default:option decision_tree -> decision_tree
  | DTGuard  : guard_expr:expr -> success:decision_tree -> failure:decision_tree -> decision_tree
  | DTBind   : var:var_id -> value_ref:nat -> rest:decision_tree -> decision_tree
  | DTSeq    : first:decision_tree -> second:decision_tree -> decision_tree

(* Occurrence: path to a sub-value in the scrutinee *)
type occurrence = list nat  (* Index path: [0, 1] means first element, then second sub-element *)

(* Pattern matrix row: pattern with arm index *)
type pattern_row = {
  pr_patterns: list pattern;
  pr_arm_index: nat;
  pr_bindings: list (var_id & occurrence)
}

type pattern_matrix = list pattern_row

(** ============================================================================
    DECISION TREE COMPILATION
    ============================================================================

    The algorithm is based on Maranget's "Compiling Pattern Matching to
    Good Decision Trees" (ML Workshop 2008).

    Key insight: Pick a column to examine, partition the matrix by
    constructor, and recurse. The choice of column affects efficiency.

    Heuristics for column selection:
    1. First non-variable column (simple, predictable)
    2. Column with most distinct constructors (maximize branching)
    3. Column with most non-default cases (minimize default case size)
*)

(* Check if pattern is a "default" pattern (matches anything) *)
let is_default_pattern (p: pattern) : bool =
  match p with
  | PatWild | PatVar _ -> true
  | PatRest _ -> true
  | _ -> false

(* Get the constructor name for a pattern, if any *)
let pattern_constructor (p: pattern) : option string =
  match p with
  | PatVariant _ name _ -> Some name
  | PatStruct name _ -> Some name
  | PatLit (LitBool true) -> Some "true"
  | PatLit (LitBool false) -> Some "false"
  | PatLit (LitInt n _) -> Some ("int_" ^ string_of_int n)
  | PatTuple _ -> Some "tuple"
  | _ -> None

(* Find first column with a non-default pattern *)
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

(* Specialize pattern matrix for a constructor *)
let specialize_row (ctor: string) (ctor_arity: nat) (col: nat) (row: pattern_row)
    : option pattern_row =
  match nth row.pr_patterns col with
  | None -> None
  | Some p ->
      match p with
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

and make_wildcards (n: nat) : list pattern =
  if n = 0 then []
  else PatWild :: make_wildcards (n - 1)

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

(* Compile pattern matrix to decision tree *)
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

(* Top-level compilation entry point *)
let compile_to_decision_tree (arms: list match_arm) : decision_tree =
  let matrix = mapi (fun idx arm ->
    { pr_patterns = [arm.arm_pattern];
      pr_arm_index = idx;
      pr_bindings = [] }
  ) arms in
  compile_matrix matrix [] 1000  (* Fuel limit *)

and mapi (#a #b: Type) (f: nat -> a -> b) (lst: list a) : list b =
  let rec go (idx: nat) (l: list a) : list b =
    match l with
    | [] -> []
    | x :: xs -> f idx x :: go (idx + 1) xs
  in
  go 0 lst

(** ============================================================================
    DECISION TREE OPTIMIZATION
    ============================================================================ *)

(* Optimize decision tree by:
   1. Removing unreachable branches
   2. Collapsing single-case switches
   3. Sharing common subtrees (not implemented - would need memoization)
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
    DIAGNOSTIC UTILITIES FOR BRRR-MACHINE
    ============================================================================

    These functions provide pattern analysis information that Brrr-Machine
    (the analysis toolkit) needs:
    1. Exhaustiveness warnings
    2. Redundancy warnings
    3. Decision tree statistics for optimization guidance
*)

(* Pattern analysis result for a match expression *)
type pattern_analysis_result = {
  par_exhaustive: bool;
  par_missing_cases: option value_space;
  par_redundant_arms: list nat;
  par_decision_tree: decision_tree;
  par_tree_depth: nat;
  par_tree_size: nat
}

(* Compute tree depth *)
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

(* Compute tree size (number of nodes) *)
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

(* Full pattern analysis for a match expression *)
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
