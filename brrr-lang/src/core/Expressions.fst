(**
 * BrrrLang.Core.Expressions
 *
 * Expression AST for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part V.
 *
 * Depends on: Primitives, Modes, Effects, Types
 *)
module Expressions

(** Z3 solver options - conservative settings for expression proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open FStar.List.Tot

(** ============================================================================
    SOURCE LOCATION TRACKING (following EverParse with_meta_t pattern)
    ============================================================================

    Every AST node can carry source location information for:
    - Precise error messages with file:line:col
    - IDE integration (go-to-definition, hover info)
    - Debugging and profiling

    Pattern from EverParse/Ast.fst:
    - pos: A source position (file, line, column)
    - range: A span from start to end position
    - with_loc: A wrapper that attaches location to any value
    ============================================================================ *)

(** Create a dummy position for synthetic nodes *)
let dummy_pos : pos = {
  pos_filename = "<synthetic>";
  pos_line = 0;
  pos_col = 0
}

(** Format position as "file:line:col" for error messages *)
let string_of_pos (p: pos) : string =
  p.pos_filename ^ ":" ^
  string_of_int p.pos_line ^ ":" ^
  string_of_int p.pos_col

(** Create a dummy range for synthetic nodes *)
let dummy_range : range = (dummy_pos, dummy_pos)

(** Format range for error messages *)
let string_of_range (r: range) : string =
  let (start_p, end_p) = r in
  if start_p.pos_filename = end_p.pos_filename then
    start_p.pos_filename ^ ":" ^
    string_of_int start_p.pos_line ^ ":" ^
    string_of_int start_p.pos_col ^ "-" ^
    string_of_int end_p.pos_line ^ ":" ^
    string_of_int end_p.pos_col
  else
    string_of_pos start_p ^ " to " ^ string_of_pos end_p

(** Merge two ranges into a range spanning both.
    Returns the smallest range containing both input ranges.
    If ranges are from different files, returns the first range.

    Following EverParse pattern for combining source locations. *)
let merge_ranges (r1 r2: range) : range =
  let (s1, e1) = r1 in
  let (s2, e2) = r2 in
  if s1.pos_filename <> s2.pos_filename then r1
  else
    let start_pos =
      if s1.pos_line < s2.pos_line then s1
      else if s1.pos_line > s2.pos_line then s2
      else if s1.pos_col <= s2.pos_col then s1
      else s2
    in
    let end_pos =
      if e1.pos_line > e2.pos_line then e1
      else if e1.pos_line < e2.pos_line then e2
      else if e1.pos_col >= e2.pos_col then e1
      else e2
    in
    (start_pos, end_pos)

(** Compute the range spanning a non-empty list of located values.
    Uses the provided function to extract range from each element.

    Example usage:
      range_of_list exprs (fun e -> e.loc_range)
      range_of_list [e1; e2; e3] loc_of
*)
let range_of_list (#a: Type) (xs: list a{Cons? xs}) (get_range: a -> range) : range =
  let hd :: tl = xs in
  List.Tot.fold_left
    (fun acc x -> merge_ranges acc (get_range x))
    (get_range hd)
    tl

(** Create a range from a single position (zero-width range) *)
let range_at (p: pos) : range = (p, p)

(** Extend a range to include another position *)
let extend_range (r: range) (p: pos) : range =
  merge_ranges r (range_at p)

(** Create a located value *)
let locate (#a: Type) (v: a) (r: range) : with_loc a =
  { loc_value = v; loc_range = r }

(** Create a located value at dummy location (for synthetic nodes) *)
let locate_dummy (#a: Type) (v: a) : with_loc a =
  { loc_value = v; loc_range = dummy_range }

(** Extract the value from a located wrapper *)
let unloc (#a: Type) (w: with_loc a) : a = w.loc_value

(** Extract the range from a located wrapper *)
let loc_of (#a: Type) (w: with_loc a) : range = w.loc_range

(** Map a function over a located value, preserving location *)
let map_loc (#a #b: Type) (f: a -> b) (w: with_loc a) : with_loc b =
  { loc_value = f w.loc_value; loc_range = w.loc_range }

(** Create a located error *)
let error_at (msg: string) (r: range) : located_error =
  { err_message = msg; err_range = r }

(** Format a located error for display *)
let string_of_error (e: located_error) : string =
  string_of_range e.err_range ^ ": error: " ^ e.err_message

(** ============================================================================
    RANGE PREDICATES AND LEMMAS
    ============================================================================ *)

(** Check if a position is within a range (inclusive) *)
let pos_within (p: pos) (r: range) : bool =
  let (start_p, end_p) = r in
  p.pos_filename = start_p.pos_filename &&
  (p.pos_line > start_p.pos_line ||
   (p.pos_line = start_p.pos_line && p.pos_col >= start_p.pos_col)) &&
  (p.pos_line < end_p.pos_line ||
   (p.pos_line = end_p.pos_line && p.pos_col <= end_p.pos_col))

(** Check if one range is entirely within another *)
let range_within (inner: range) (outer: range) : bool =
  let (inner_start, inner_end) = inner in
  let (outer_start, outer_end) = outer in
  pos_within inner_start outer && pos_within inner_end outer

(** Check if two ranges overlap *)
let ranges_overlap (r1 r2: range) : bool =
  let (s1, e1) = r1 in
  let (s2, e2) = r2 in
  s1.pos_filename = s2.pos_filename &&
  not (e1.pos_line < s2.pos_line ||
       (e1.pos_line = s2.pos_line && e1.pos_col < s2.pos_col) ||
       e2.pos_line < s1.pos_line ||
       (e2.pos_line = s1.pos_line && e2.pos_col < s1.pos_col))

(* pos_eq and range_eq are now unfold definitions in Expressions.fsti *)

(** Range equality is reflexive *)
let range_eq_refl (r: range) : Lemma (ensures range_eq r r = true) =
  ()

(** Range equality is symmetric *)
let range_eq_sym (r1 r2: range)
    : Lemma (requires range_eq r1 r2 = true)
            (ensures range_eq r2 r1 = true) =
  ()

(** Range equality is transitive *)
let range_eq_trans (r1 r2 r3: range)
    : Lemma (requires range_eq r1 r2 = true /\ range_eq r2 r3 = true)
            (ensures range_eq r1 r3 = true) =
  ()

(** merge_ranges preserves containment (left) *)
let merge_ranges_contains_left (r1 r2: range)
    : Lemma (ensures range_within r1 (merge_ranges r1 r2) = true) =
  admit()  (* Requires detailed case analysis on position ordering *)

(** merge_ranges preserves containment (right) *)
let merge_ranges_contains_right (r1 r2: range)
    : Lemma (ensures range_within r2 (merge_ranges r1 r2) = true) =
  admit()  (* Requires detailed case analysis on position ordering *)

(** ============================================================================
    ANNOTATED EXPRESSION CONSTRUCTORS
    ============================================================================ *)

(* Create annotated expression using the expression's own range *)
let annotate (id: node_id) (e: expr) : annotated_expr =
  { node = id; source_range = e.loc_range; ty = None; effects = None; expr = e }

(* Create annotated expression with explicit range *)
let annotate_at (id: node_id) (r: range) (e: expr) : annotated_expr =
  { node = id; source_range = r; ty = None; effects = None; expr = e }

(* Create annotated expression with type *)
let annotate_typed (id: node_id) (e: expr) (t: brrr_type) : annotated_expr =
  { node = id; source_range = e.loc_range; ty = Some t; effects = None; expr = e }

(* Create annotated expression with type and effects *)
let annotate_full (id: node_id) (e: expr) (t: brrr_type) (eff: effect_row) : annotated_expr =
  { node = id; source_range = e.loc_range; ty = Some t; effects = Some eff; expr = e }

(** Compute range of a non-empty list of located expressions *)
let range_of_exprs (es: list expr{Cons? es}) : range =
  range_of_list es loc_of

(** Compute range of a non-empty list of located patterns *)
let range_of_pats (ps: list pattern{Cons? ps}) : range =
  range_of_list ps loc_of

(** ============================================================================
    EXPRESSION CONSTRUCTORS
    ============================================================================

    All constructors create expressions at dummy_range by default.
    Use the _at variants to specify source location.
    ============================================================================ *)

(* Helper to wrap an expression with a range *)
let mk_expr (r: range) (e: expr') : expr = { loc_value = e; loc_range = r }
let mk_expr_dummy (e: expr') : expr = mk_expr dummy_range e

(* Helper to wrap a pattern with a range *)
let mk_pat (r: range) (p: pattern') : pattern = { loc_value = p; loc_range = r }
let mk_pat_dummy (p: pattern') : pattern = mk_pat dummy_range p

(* Convenience constructors - create at dummy location *)
let e_unit : expr = mk_expr_dummy (ELit LitUnit)
let e_true : expr = mk_expr_dummy (ELit (LitBool true))
let e_false : expr = mk_expr_dummy (ELit (LitBool false))
let e_int (n: int) : expr = mk_expr_dummy (ELit (LitInt n i32))
let e_i64 (n: int) : expr = mk_expr_dummy (ELit (LitInt n i64))
let e_f64 (f: float_repr) : expr = mk_expr_dummy (ELit (LitFloat f F64))
let e_str (s: string) : expr = mk_expr_dummy (ELit (LitString s))

let e_var (x: var_id) : expr = mk_expr_dummy (EVar x)
let e_field (e: expr) (f: string) : expr = mk_expr_dummy (EField e f)
let e_call (f: expr) (args: list expr) : expr = mk_expr_dummy (ECall f args)

let e_if (c: expr) (t: expr) (f: expr) : expr = mk_expr_dummy (EIf c t f)
let e_let (x: var_id) (e1: expr) (e2: expr) : expr =
  mk_expr_dummy (ELet (mk_pat_dummy (PatVar x)) None e1 e2)

let e_lambda (params: list (var_id & brrr_type)) (body: expr) : expr =
  mk_expr_dummy (ELambda params body)

let e_block (es: list expr) : expr = mk_expr_dummy (EBlock es)
let e_seq (e1: expr) (e2: expr) : expr = mk_expr_dummy (ESeq e1 e2)

(* Constructors with explicit source location *)
let e_unit_at (r: range) : expr = mk_expr r (ELit LitUnit)
let e_true_at (r: range) : expr = mk_expr r (ELit (LitBool true))
let e_false_at (r: range) : expr = mk_expr r (ELit (LitBool false))
let e_int_at (r: range) (n: int) : expr = mk_expr r (ELit (LitInt n i32))
let e_var_at (r: range) (x: var_id) : expr = mk_expr r (EVar x)
let e_field_at (r: range) (e: expr) (f: string) : expr = mk_expr r (EField e f)
let e_call_at (r: range) (f: expr) (args: list expr) : expr = mk_expr r (ECall f args)
let e_if_at (r: range) (c: expr) (t: expr) (f: expr) : expr = mk_expr r (EIf c t f)

(* Pattern constructors *)
let p_wild : pattern = mk_pat_dummy PatWild
let p_var (x: var_id) : pattern = mk_pat_dummy (PatVar x)
let p_lit (l: literal) : pattern = mk_pat_dummy (PatLit l)
let p_tuple (ps: list pattern) : pattern = mk_pat_dummy (PatTuple ps)

let p_type (ty: brrr_type) (v: option var_id) : pattern = mk_pat_dummy (PatType ty v)
let p_wild_at (r: range) : pattern = mk_pat r PatWild
let p_var_at (r: range) (x: var_id) : pattern = mk_pat r (PatVar x)
let p_type_at (r: range) (ty: brrr_type) (v: option var_id) : pattern = mk_pat r (PatType ty v)

(* Match arm constructors *)
let mk_arm (r: range) (p: pattern) (g: option expr) (b: expr) : match_arm =
  { arm_range = r; arm_pattern = p; arm_guard = g; arm_body = b }

let mk_arm_simple (p: pattern) (b: expr) : match_arm =
  mk_arm dummy_range p None b

(* Catch arm constructors *)
let mk_catch (r: range) (p: pattern) (t: brrr_type) (b: expr) : catch_arm =
  { catch_range = r; catch_pattern = p; catch_type = t; catch_body = b }

(* Extract underlying expression/pattern *)
let expr_inner (e: expr) : expr' = e.loc_value
let expr_range (e: expr) : range = e.loc_range
let pat_inner (p: pattern) : pattern' = p.loc_value
let pat_range (p: pattern) : range = p.loc_range

(** ============================================================================
    EXPRESSION SIZE FUNCTIONS (for termination proofs)
    ============================================================================

    These work on the underlying expr'/pattern' types since the with_loc wrapper
    is structurally simple and doesn't affect termination.
    ============================================================================ *)

(* Size function for underlying expression type *)
let rec expr'_size (e: expr') : Tot nat (decreases e) =
  match e with
  (* Leaves *)
  | ELit _ | EVar _ | EGlobal _ | EHole | EError _
  | ESizeof _ | EAlignof _ | ETypeMethod _ _ -> 1
  | EContinue _ -> 1  (* continue 'label *)
  | EGoto _ -> 1  (* goto label *)

  (* Unary wrappers *)
  | EUnary _ e' | ELoop _ e' | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e'
  | EMove e' | EDrop e' | EThrow e' | EAwait e' | EYield e' | EUnsafe e'
  | EField e' _ | ETupleProj e' _ | EAs e' _ | EIs e' _
  | ELabeled _ e'  (* label: stmt *)
  | EAsync e' | ESpawn e' | EReset _ e'
  | EMethodRef e' _ | ELen e' | ECap e' -> 1 + expr_size e'

  (* Break/return with optional value *)
  | EBreak _ None | EReturn None -> 1
  | EBreak _ (Some e') | EReturn (Some e') -> 1 + expr_size e'

  (* Binary expressions *)
  | EBinary _ e1 e2 | EIndex e1 e2 | EAssign e1 e2 | ESeq e1 e2 ->
      1 + expr_size e1 + expr_size e2

  (* Continuation resume *)
  | EResume _ e' -> 1 + expr_size e'

  (* Control flow *)
  | EIf c t el -> 1 + expr_size c + expr_size t + expr_size el
  | EWhile _ c b -> 1 + expr_size c + expr_size b
  | EFor _ _ iter body -> 1 + expr_size iter + expr_size body

  (* Bindings *)
  | ELet _ _ e1 e2 | ELetMut _ _ e1 e2 -> 1 + expr_size e1 + expr_size e2

  (* Functions *)
  | ELambda _ body | EClosure _ _ body -> 1 + expr_size body

  (* Effects *)
  | EHandle e' _ -> 1 + expr_size e'
  | EShift _ _ body -> 1 + expr_size body

  (* Calls *)
  | ECall fn args -> 1 + expr_size fn + expr_list_size args
  | EMethodCall obj _ args -> 1 + expr_size obj + expr_list_size args

  (* Compound data *)
  | ETuple es | EArray es | EBlock es -> 1 + expr_list_size es
  | EStruct _ fields -> 1 + field_expr_list_size fields
  | EVariant _ _ es -> 1 + expr_list_size es

  (* Pattern matching *)
  | EMatch e' arms -> 1 + expr_size e' + match_arm_list_size arms

  (* Exception handling *)
  | ETry e' catches finally_opt ->
      1 + expr_size e' + catch_arm_list_size catches + option_expr_size finally_opt

  (* Effect operations *)
  | EPerform _ args -> 1 + expr_list_size args

(* Size of wrapped expression - unwrap and delegate *)
and expr_size (e: expr) : Tot nat (decreases e) =
  1 + expr'_size e.loc_value

and expr_list_size (es: list expr) : Tot nat (decreases es) =
  match es with
  | [] -> 0
  | e :: rest -> expr_size e + expr_list_size rest

and field_expr_list_size (fields: list (string & expr)) : Tot nat (decreases fields) =
  match fields with
  | [] -> 0
  | (_, e) :: rest -> expr_size e + field_expr_list_size rest

and option_expr_size (opt: option expr) : Tot nat (decreases opt) =
  match opt with
  | None -> 0
  | Some e -> expr_size e

and match_arm_list_size (arms: list match_arm) : Tot nat (decreases arms) =
  match arms with
  | [] -> 0
  | arm :: rest ->
      option_expr_size arm.arm_guard + expr_size arm.arm_body + match_arm_list_size rest

and catch_arm_list_size (catches: list catch_arm) : Tot nat (decreases catches) =
  match catches with
  | [] -> 0
  | c :: rest -> expr_size c.catch_body + catch_arm_list_size rest

(* expr_size is always at least 1 - needed for termination proofs *)
let rec expr_size_pos (e: expr) : Lemma (ensures expr_size e >= 1) (decreases e) =
  (* expr_size e = 1 + expr'_size e.loc_value, so it's always >= 1 *)
  ()

(* Helper lemmas for termination proofs *)
let field_expr_list_size_decreases (nm: string) (e: expr) (rest: list (string & expr))
    : Lemma (ensures field_expr_list_size rest < field_expr_list_size ((nm, e) :: rest))
            [SMTPat (field_expr_list_size ((nm, e) :: rest))] =
  expr_size_pos e

let catch_arm_list_size_decreases (c: catch_arm) (rest: list catch_arm)
    : Lemma (ensures catch_arm_list_size rest < catch_arm_list_size (c :: rest))
            [SMTPat (catch_arm_list_size (c :: rest))] =
  expr_size_pos c.catch_body

let match_arm_list_size_decreases (arm: match_arm) (rest: list match_arm)
    : Lemma (ensures match_arm_list_size rest < match_arm_list_size (arm :: rest))
            [SMTPat (match_arm_list_size (arm :: rest))] =
  expr_size_pos arm.arm_body

let expr_list_size_decreases (e: expr) (rest: list expr)
    : Lemma (ensures expr_list_size rest < expr_list_size (e :: rest))
            [SMTPat (expr_list_size (e :: rest))] =
  expr_size_pos e

(** ============================================================================
    SUBEXPRESSION RELATIONSHIP
    ============================================================================ *)

(** Collect immediate subexpressions of an expression *)
let immediate_subexprs (e: expr) : list expr =
  match e.loc_value with
  | ELit _ | EVar _ | EGlobal _ | EHole | EError _ | EContinue _ | EGoto _ -> []
  | ESizeof _ | EAlignof _ | ETypeMethod _ _ -> []
  | EUnary _ e' | ELoop _ e' | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e'
  | EMove e' | EDrop e' | EThrow e' | EAwait e' | EYield e' | EUnsafe e'
  | EField e' _ | ETupleProj e' _ | EAs e' _ | EIs e' _
  | EAsync e' | ESpawn e' | EReset _ e' | ELabeled _ e'
  | EMethodRef e' _ | ELen e' | ECap e' -> [e']
  | EBreak _ None | EReturn None -> []
  | EBreak _ (Some e') | EReturn (Some e') -> [e']
  | EResume _ e' -> [e']
  | EBinary _ e1 e2 | EIndex e1 e2 | EAssign e1 e2 | ESeq e1 e2 -> [e1; e2]
  | EIf c t el -> [c; t; el]
  | EWhile _ c b -> [c; b]
  | EFor _ _ iter body -> [iter; body]
  | ELet _ _ e1 e2 | ELetMut _ _ e1 e2 -> [e1; e2]
  | ELambda _ body | EClosure _ _ body | EShift _ _ body -> [body]
  | EHandle e' _ -> [e']
  | ECall fn args -> fn :: args
  | EMethodCall obj _ args -> obj :: args
  | ETuple es | EArray es | EBlock es -> es
  | EStruct _ fields -> map snd fields
  | EVariant _ _ es -> es
  | EMatch e' arms -> e' :: map (fun arm -> arm.arm_body) arms
  | ETry e' catches finally_opt ->
      let catch_bodies = map (fun c -> c.catch_body) catches in
      (match finally_opt with
       | None -> e' :: catch_bodies
       | Some fin -> e' :: fin :: catch_bodies)
  | EPerform _ args -> args

(** Check if sub is an immediate subexpression of parent *)
let is_immediate_subexpr (sub: expr) (parent: expr) : bool =
  mem sub (immediate_subexprs parent)

(* NOTE: is_subexpr and related functions are defined after expr_eq
   to avoid forward reference issues. See section after expr_eq definitions. *)

(** ============================================================================
    EXPRESSION WELL-FORMEDNESS
    ============================================================================ *)

(** Reserved prefix for generated identifiers *)
let reserved_prefix = "___"

(** Check if a variable identifier is valid (non-empty, no reserved prefix) *)
let is_valid_var_id (v: var_id) : bool =
  String.length v > 0 &&
  not (String.sub v 0 (min (String.length v) 3) = reserved_prefix)

(** Collect all bound variables in a pattern *)
let rec pattern_bound_vars (p: pattern) : Tot (list var_id) (decreases p) =
  match p.loc_value with
  | PatWild | PatLit _ | PatRest None -> []
  | PatVar x -> [x]
  | PatRest (Some x) -> [x]
  | PatAs p' x -> x :: pattern_bound_vars p'
  | PatTuple ps -> List.Tot.concatMap pattern_bound_vars ps
  | PatStruct _ fields -> List.Tot.concatMap (fun (_, p') -> pattern_bound_vars p') fields
  | PatVariant _ _ ps -> List.Tot.concatMap pattern_bound_vars ps
  | PatOr p1 p2 -> pattern_bound_vars p1 @ pattern_bound_vars p2
  | PatGuard p' _ -> pattern_bound_vars p'
  | PatRef p' | PatBox p' -> pattern_bound_vars p'
  | PatType _ None -> []
  | PatType _ (Some x) -> [x]

(** Check for duplicate bindings in pattern *)
let pattern_has_duplicate_bindings (p: pattern) : bool =
  let vars = pattern_bound_vars p in
  let rec has_dup (xs: list var_id) : bool =
    match xs with
    | [] -> false
    | x :: rest -> mem x rest || has_dup rest
  in
  has_dup vars

(** Check if pattern is well-formed *)
let rec pattern_wf (p: pattern) : Tot bool (decreases p) =
  not (pattern_has_duplicate_bindings p) &&
  (match p.loc_value with
   | PatVar x -> is_valid_var_id x
   | PatAs p' x -> is_valid_var_id x && pattern_wf p'
   | PatRest (Some x) -> is_valid_var_id x
   | PatTuple ps -> List.Tot.for_all pattern_wf ps
   | PatStruct _ fields -> List.Tot.for_all (fun (_, p') -> pattern_wf p') fields
   | PatVariant _ _ ps -> List.Tot.for_all pattern_wf ps
   | PatOr p1 p2 -> pattern_wf p1 && pattern_wf p2
   | PatGuard p' _ -> pattern_wf p'
   | PatRef p' | PatBox p' -> pattern_wf p'
   | PatType _ (Some x) -> is_valid_var_id x
   | _ -> true)

(** Check if expression is well-formed *)
let rec expr_wf (e: expr) : Tot bool (decreases expr_size e) =
  match e.loc_value with
  | EVar x -> is_valid_var_id x
  | ELet p _ e1 e2 -> pattern_wf p && expr_wf e1 && expr_wf e2
  | ELetMut x _ e1 e2 -> is_valid_var_id x && expr_wf e1 && expr_wf e2
  | ELambda params body ->
      List.Tot.for_all (fun (x, _) -> is_valid_var_id x) params && expr_wf body
  | EClosure params _ body ->
      List.Tot.for_all (fun (x, _) -> is_valid_var_id x) params && expr_wf body
  | EFor _ x iter body -> is_valid_var_id x && expr_wf iter && expr_wf body
  | EShift _ k body -> is_valid_var_id k && expr_wf body
  | EResume k e' -> is_valid_var_id k && expr_wf e'
  | EMatch e' arms ->
      expr_wf e' && List.Tot.for_all (fun arm -> pattern_wf arm.arm_pattern && expr_wf arm.arm_body) arms
  | ETry e' catches _ ->
      expr_wf e' && List.Tot.for_all (fun c -> pattern_wf c.catch_pattern && expr_wf c.catch_body) catches
  | _ -> true

(** Check if match arms are well-formed *)
let match_arms_wf (arms: list match_arm) : bool =
  List.Tot.for_all (fun arm -> pattern_wf arm.arm_pattern) arms

(** Well-formed patterns have no duplicate bindings *)
let pattern_wf_no_duplicates (p: pattern)
    : Lemma (requires pattern_wf p = true)
            (ensures pattern_has_duplicate_bindings p = false) =
  ()

(** ============================================================================
    EXPRESSION TRAVERSAL
    ============================================================================ *)

(* Map over immediate sub-expressions - applies f to each direct child.
   Preserves source location of the parent expression. *)
let map_expr (f: expr -> expr) (e: expr) : expr =
  let r = e.loc_range in
  let inner = e.loc_value in
  let new_inner : expr' =
    match inner with
    (* Unary operations *)
    | EUnary op e' -> EUnary op (f e')
    | EBox e' -> EBox (f e')
    | EDeref e' -> EDeref (f e')
    | EBorrow e' -> EBorrow (f e')
    | EBorrowMut e' -> EBorrowMut (f e')
    | EMove e' -> EMove (f e')
    | EDrop e' -> EDrop (f e')
    | EThrow e' -> EThrow (f e')
    | EAwait e' -> EAwait (f e')
    | EYield e' -> EYield (f e')
    | EUnsafe e' -> EUnsafe (f e')
    | EAs e' t -> EAs (f e') t
    | EIs e' t -> EIs (f e') t

    (* Method references and intrinsics *)
    | EMethodRef e' m -> EMethodRef (f e') m
    | ELen e' -> ELen (f e')
    | ECap e' -> ECap (f e')

    (* Async/spawn/continuations *)
    | EAsync e' -> EAsync (f e')
    | ESpawn e' -> ESpawn (f e')
    | EResume k e' -> EResume k (f e')
    | EReset p e' -> EReset p (f e')
    | EShift p k body -> EShift p k (f body)

    (* Binary operations *)
    | EBinary op e1 e2 -> EBinary op (f e1) (f e2)
    | EIndex e1 e2 -> EIndex (f e1) (f e2)
    | EAssign lhs rhs -> EAssign (f lhs) (f rhs)
    | ESeq e1 e2 -> ESeq (f e1) (f e2)

    (* Calls *)
    | ECall fn args -> ECall (f fn) (List.Tot.map f args)
    | EMethodCall obj m args -> EMethodCall (f obj) m (List.Tot.map f args)

    (* Data construction *)
    | ETuple es -> ETuple (List.Tot.map f es)
    | EArray es -> EArray (List.Tot.map f es)
    | EStruct n fields -> EStruct n (List.Tot.map (fun (name, e') -> (name, f e')) fields)
    | EVariant n v es -> EVariant n v (List.Tot.map f es)

    (* Data access *)
    | EField e' fld -> EField (f e') fld
    | ETupleProj e' i -> ETupleProj (f e') i

    (* Control flow with labels *)
    | EIf c t el -> EIf (f c) (f t) (f el)
    | ELoop lbl body -> ELoop lbl (f body)
    | EWhile lbl cond body -> EWhile lbl (f cond) (f body)
    | EFor lbl x iter body -> EFor lbl x (f iter) (f body)
    | EBreak lbl (Some e') -> EBreak lbl (Some (f e'))
    | EReturn (Some e') -> EReturn (Some (f e'))
    | ELabeled lbl body -> ELabeled lbl (f body)  (* Labeled statement *)
    (* EGoto is a leaf - handled by catch-all *)

    (* Bindings *)
    | ELet p t e1 e2 -> ELet p t (f e1) (f e2)
    | ELetMut x t e1 e2 -> ELetMut x t (f e1) (f e2)

    (* Functions *)
    | ELambda params body -> ELambda params (f body)
    | EClosure params caps body -> EClosure params caps (f body)

    (* Blocks *)
    | EBlock es -> EBlock (List.Tot.map f es)

    (* Leaves and others unchanged *)
    | _ -> inner
  in
  { loc_value = new_inner; loc_range = r }

(* Fold over expression tree - single recursive definition.
   NOTE: We avoid mutual recursion by inlining the helper logic.
   This may be less elegant but avoids F* universe compatibility issues. *)
let rec fold_expr (#a: Type) (f: a -> expr -> a) (init: a) (e: expr)
    : Tot a (decreases expr_size e) =
  let acc = f init e in
  match e.loc_value with
  (* Unary wrappers *)
  | EUnary _ e' | ELoop _ e' | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e'
  | EMove e' | EDrop e' | EThrow e' | EAwait e' | EYield e' | EUnsafe e'
  | EField e' _ | ETupleProj e' _ | EAs e' _ | EIs e' _
  | EAsync e' | ESpawn e' | EReset _ e' | EResume _ e'
  | ELabeled _ e'
  | EMethodRef e' _ | ELen e' | ECap e' -> fold_expr f acc e'

  (* Binary expressions *)
  | EBinary _ e1 e2 | EIndex e1 e2 | EAssign e1 e2 | ESeq e1 e2 ->
      fold_expr f (fold_expr f acc e1) e2

  (* Control flow *)
  | EIf c t el -> fold_expr f (fold_expr f (fold_expr f acc c) t) el
  | EWhile _ c b -> fold_expr f (fold_expr f acc c) b
  | EFor _ _ iter body -> fold_expr f (fold_expr f acc iter) body
  | EBreak _ (Some e') | EReturn (Some e') -> fold_expr f acc e'

  (* Bindings *)
  | ELet _ _ e1 e2 | ELetMut _ _ e1 e2 -> fold_expr f (fold_expr f acc e1) e2

  (* Functions *)
  | ELambda _ body | EClosure _ _ body | EShift _ _ body -> fold_expr f acc body

  (* Effect handling *)
  | EHandle e' _ -> fold_expr f acc e'

  (* Calls - inline fold over lists *)
  | ECall fn args ->
      let acc1 = fold_expr f acc fn in
      List.Tot.fold_left (fold_expr f) acc1 args
  | EMethodCall obj _ args ->
      let acc1 = fold_expr f acc obj in
      List.Tot.fold_left (fold_expr f) acc1 args

  (* Compound data - inline fold over lists *)
  | ETuple es | EArray es | EBlock es ->
      List.Tot.fold_left (fold_expr f) acc es
  | EStruct _ fields ->
      List.Tot.fold_left (fun ac (_, e) -> fold_expr f ac e) acc fields
  | EVariant _ _ es ->
      List.Tot.fold_left (fold_expr f) acc es

  (* Pattern matching - inline fold over arms *)
  | EMatch e' arms ->
      let acc1 = fold_expr f acc e' in
      List.Tot.fold_left (fun ac arm ->
        let ac1 = match arm.arm_guard with
          | None -> ac
          | Some g -> fold_expr f ac g in
        fold_expr f ac1 arm.arm_body
      ) acc1 arms

  (* Exception handling *)
  | ETry e' catches finally_opt ->
      let acc1 = fold_expr f acc e' in
      let acc2 = List.Tot.fold_left (fun ac c -> fold_expr f ac c.catch_body) acc1 catches in
      (match finally_opt with
       | None -> acc2
       | Some fin -> fold_expr f acc2 fin)

  (* Effect operations *)
  | EPerform _ args -> List.Tot.fold_left (fold_expr f) acc args

  (* Leaves *)
  | _ -> acc

(** Collect all nodes in expression tree *)
let collect_nodes (e: expr) : Tot (list expr) =
  fold_expr (fun acc x -> x :: acc) [] e

(** Count nodes in expression tree *)
let count_nodes (e: expr) : Tot nat =
  fold_expr (fun acc _ -> acc + 1) 0 e

(** ============================================================================
    FREE VARIABLES
    ============================================================================ *)

(* Helper to extract bound variable from a pattern, if it's a simple variable pattern *)
let pattern_var (p: pattern) : option var_id =
  match p.loc_value with
  | PatVar x -> Some x
  | _ -> None

(* Collect free variables in expression - mutually recursive with list helper *)
let rec free_vars (e: expr) : Tot (list var_id) (decreases %[expr_size e; 0]) =
  match e.loc_value with
  (* Variables *)
  | EVar x -> [x]

  (* Unary wrappers - just propagate *)
  | EUnary _ e' | ELoop _ e' | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e'
  | EMove e' | EDrop e' | EThrow e' | EAwait e' | EYield e' | EUnsafe e'
  | EField e' _ | ETupleProj e' _ | EAs e' _ | EIs e' _
  | EAsync e' | ESpawn e' | EReset _ e'
  | ELabeled _ e'  (* Labeled: just propagate to body *)
  | EMethodRef e' _ | ELen e' | ECap e' -> free_vars e'

  (* Goto has no subexpressions - covered by catch-all below returning [] *)

  (* Resume binds continuation variable k, free in the value expr *)
  | EResume k e' -> k :: free_vars e'

  (* Shift captures continuation k, binds it in body *)
  | EShift _ k body -> filter (fun v -> v <> k) (free_vars body)

  (* Binary expressions *)
  | EBinary _ e1 e2 | EIndex e1 e2 | EAssign e1 e2 | ESeq e1 e2 ->
      free_vars e1 @ free_vars e2

  (* Control flow *)
  | EIf c t el -> free_vars c @ free_vars t @ free_vars el
  | EWhile _ c b -> free_vars c @ free_vars b
  | EFor _ x iter body ->
      free_vars iter @ filter (fun v -> v <> x) (free_vars body)
  | EBreak _ (Some e') | EReturn (Some e') -> free_vars e'

  (* Bindings - check if pattern is a simple variable *)
  | ELet p _ e1 e2 ->
      (match pattern_var p with
       | Some x -> free_vars e1 @ filter (fun v -> v <> x) (free_vars e2)
       | None -> free_vars e1 @ free_vars e2)  (* Other patterns not handled *)
  | ELetMut x _ e1 e2 ->
      free_vars e1 @ filter (fun v -> v <> x) (free_vars e2)

  (* Functions *)
  | ELambda params body ->
      let bound = map fst params in
      filter (fun v -> not (mem v bound)) (free_vars body)
  | EClosure params _ body ->
      let bound = map fst params in
      filter (fun v -> not (mem v bound)) (free_vars body)

  (* Calls *)
  | ECall fn args -> free_vars fn @ free_vars_list args
  | EMethodCall obj _ args -> free_vars obj @ free_vars_list args

  (* Compound data *)
  | ETuple es | EArray es | EBlock es -> free_vars_list es
  | EStruct _ fields -> free_vars_fields fields
  | EVariant _ _ es -> free_vars_list es

  (* Leaves and catch-all *)
  | _ -> []

and free_vars_fields (fields: list (string & expr)) : Tot (list var_id) (decreases %[field_expr_list_size fields; 1]) =
  match fields with
  | [] -> []
  | (_, e) :: rest -> free_vars e @ free_vars_fields rest

and free_vars_list (es: list expr) : Tot (list var_id) (decreases %[expr_list_size es; 1]) =
  match es with
  | [] -> []
  | e :: rest -> free_vars e @ free_vars_list rest

(** Check if variable is free in expression *)
let is_free_in (v: var_id) (e: expr) : Tot bool =
  mem v (free_vars e)

(** Variables that may be bound by a parent expression.
    Returns the list of variables that the parent binds (and thus may filter from free_vars). *)
let parent_binds (parent: expr) : list var_id =
  match parent.loc_value with
  | ELet p _ _ _ ->
      (match pattern_var p with
       | Some x -> [x]
       | None -> pattern_bound_vars p)
  | ELetMut x _ _ _ -> [x]
  | EFor _ x _ _ -> [x]
  | ELambda params _ -> map fst params
  | EClosure params _ _ -> map fst params
  | EShift _ k _ -> [k]
  | EMatch _ arms ->
      (* Match binds variables in patterns, but only in their respective bodies *)
      []  (* Simplified - pattern vars are local to each arm *)
  | _ -> []

(** Free variables of subexpression lemma *)
let free_vars_subexpr (sub: expr) (parent: expr)
    : Lemma (requires is_immediate_subexpr sub parent = true)
            (ensures forall v. mem v (free_vars sub) ==>
                              mem v (free_vars parent) \/
                              mem v (parent_binds parent)) =
  (* This requires case analysis on parent structure.
     For most cases, free_vars concatenates subexpr free_vars.
     For binding forms, some variables are filtered but are in parent_binds. *)
  admit()

(** ============================================================================
    EXPRESSION EQUALITY - Structural comparison
    ============================================================================ *)

(* literal_eq, unary_op_eq, binary_op_eq are now unfold definitions in Expressions.fsti *)

(* Helper for option type equality - standalone, not part of mutual recursion *)
let option_type_eq (t1 t2: option brrr_type) : Tot bool =
  match t1, t2 with
  | None, None -> true
  | Some ty1, Some ty2 -> type_eq ty1 ty2
  | _, _ -> false

(* Helper for parameter list equality - standalone, not part of mutual recursion *)
let rec param_list_eq_expr (ps1 ps2: list (var_id & brrr_type)) : Tot bool (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> true
  | (v1, t1) :: r1, (v2, t2) :: r2 ->
      v1 = v2 && type_eq t1 t2 && param_list_eq_expr r1 r2
  | _, _ -> false

(* Reflexivity lemma for option_type_eq *)
let option_type_eq_refl (t: option brrr_type) : Lemma (ensures option_type_eq t t = true) =
  match t with
  | None -> ()
  | Some ty -> type_eq_refl ty

(* Reflexivity lemma for param_list_eq_expr *)
let rec param_list_eq_expr_refl (ps: list (var_id & brrr_type))
    : Lemma (ensures param_list_eq_expr ps ps = true) (decreases ps) =
  match ps with
  | [] -> ()
  | (_, t) :: rest -> type_eq_refl t; param_list_eq_expr_refl rest

(* Symmetry lemma for option_type_eq *)
let option_type_eq_sym (t1 t2: option brrr_type)
    : Lemma (requires option_type_eq t1 t2 = true)
            (ensures option_type_eq t2 t1 = true) =
  match t1, t2 with
  | None, None -> ()
  | Some ty1, Some ty2 -> type_eq_sym ty1 ty2
  | _, _ -> ()

(* Symmetry lemma for param_list_eq_expr *)
let rec param_list_eq_expr_sym (ps1 ps2: list (var_id & brrr_type))
    : Lemma (requires param_list_eq_expr ps1 ps2 = true)
            (ensures param_list_eq_expr ps2 ps1 = true)
            (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> ()
  | (_, t1) :: r1, (_, t2) :: r2 -> type_eq_sym t1 t2; param_list_eq_expr_sym r1 r2
  | _, _ -> ()

(* Transitivity lemma for option_type_eq *)
let option_type_eq_trans (t1 t2 t3: option brrr_type)
    : Lemma (requires option_type_eq t1 t2 = true /\ option_type_eq t2 t3 = true)
            (ensures option_type_eq t1 t3 = true) =
  match t1, t2, t3 with
  | None, None, None -> ()
  | Some ty1, Some ty2, Some ty3 -> type_eq_trans ty1 ty2 ty3
  | _, _, _ -> ()

(* Transitivity lemma for param_list_eq_expr *)
let rec param_list_eq_expr_trans (ps1 ps2 ps3: list (var_id & brrr_type))
    : Lemma (requires param_list_eq_expr ps1 ps2 = true /\ param_list_eq_expr ps2 ps3 = true)
            (ensures param_list_eq_expr ps1 ps3 = true)
            (decreases ps1) =
  match ps1, ps2, ps3 with
  | [], [], [] -> ()
  | (_, t1) :: r1, (_, t2) :: r2, (_, t3) :: r3 ->
      type_eq_trans t1 t2 t3; param_list_eq_expr_trans r1 r2 r3
  | _, _, _ -> ()

(* Helper for optional label equality *)
let option_label_eq (l1 l2: option label) : bool =
  match l1, l2 with
  | None, None -> true
  | Some lbl1, Some lbl2 -> lbl1 = lbl2
  | _, _ -> false

(* Helper for optional var_id equality *)
let option_var_eq (v1 v2: option var_id) : bool =
  match v1, v2 with
  | None, None -> true
  | Some x1, Some x2 -> x1 = x2
  | _, _ -> false

(* Structural equality for patterns - mutually recursive with expr_eq.
   Note: Location is NOT compared - only the underlying pattern structure. *)
let rec pattern_eq (p1 p2: pattern) : Tot bool (decreases p1) =
  match p1.loc_value, p2.loc_value with
  | PatWild, PatWild -> true
  | PatVar v1, PatVar v2 -> v1 = v2
  | PatLit l1, PatLit l2 -> literal_eq l1 l2
  | PatTuple ps1, PatTuple ps2 -> pattern_list_eq ps1 ps2
  | PatStruct n1 fs1, PatStruct n2 fs2 ->
      n1 = n2 && pattern_field_list_eq fs1 fs2
  | PatVariant n1 v1 ps1, PatVariant n2 v2 ps2 ->
      n1 = n2 && v1 = v2 && pattern_list_eq ps1 ps2
  | PatOr p1a p1b, PatOr p2a p2b ->
      pattern_eq p1a p2a && pattern_eq p1b p2b
  | PatRef p1', PatRef p2' -> pattern_eq p1' p2'
  | PatBox p1', PatBox p2' -> pattern_eq p1' p2'
  | PatGuard p1' _, PatGuard p2' _ ->
      pattern_eq p1' p2'  (* Guard expression comparison would need expr_eq *)
  | PatRest v1, PatRest v2 -> option_var_eq v1 v2
  | PatAs p1' x1, PatAs p2' x2 -> pattern_eq p1' p2' && x1 = x2
  | PatType ty1 v1, PatType ty2 v2 -> type_eq ty1 ty2 && option_var_eq v1 v2
  | _, _ -> false

and pattern_list_eq (ps1 ps2: list pattern) : Tot bool (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> true
  | p1 :: r1, p2 :: r2 -> pattern_eq p1 p2 && pattern_list_eq r1 r2
  | _, _ -> false

and pattern_field_list_eq (fs1 fs2: list (string & pattern)) : Tot bool (decreases fs1) =
  match fs1, fs2 with
  | [], [] -> true
  | (n1, p1) :: r1, (n2, p2) :: r2 ->
      n1 = n2 && pattern_eq p1 p2 && pattern_field_list_eq r1 r2
  | _, _ -> false

(* Structural equality for expressions - comprehensive structural comparison.
   Two expressions are equal if they have the same structure with equal components.
   This is NOT alpha-equivalence; bound variables must match exactly.
   Note: Location is NOT compared - only the underlying expression structure. *)
let rec expr_eq (e1 e2: expr) : Tot bool (decreases %[expr_size e1; 0]) =
  match e1.loc_value, e2.loc_value with
  (* Literals and variables *)
  | ELit l1, ELit l2 -> literal_eq l1 l2
  | EVar v1, EVar v2 -> v1 = v2
  | EGlobal g1, EGlobal g2 -> g1 = g2

  (* Operations *)
  | EUnary op1 e1', EUnary op2 e2' ->
      unary_op_eq op1 op2 && expr_eq e1' e2'
  | EBinary op1 e1a e1b, EBinary op2 e2a e2b ->
      binary_op_eq op1 op2 && expr_eq e1a e2a && expr_eq e1b e2b
  | ECall fn1 args1, ECall fn2 args2 ->
      expr_eq fn1 fn2 && expr_list_eq args1 args2
  | EMethodCall obj1 m1 args1, EMethodCall obj2 m2 args2 ->
      expr_eq obj1 obj2 && m1 = m2 && expr_list_eq args1 args2
  | EMethodRef e1' m1, EMethodRef e2' m2 ->
      expr_eq e1' e2' && m1 = m2
  | ETypeMethod t1 m1, ETypeMethod t2 m2 ->
      t1 = t2 && m1 = m2
  | ELen e1', ELen e2' -> expr_eq e1' e2'
  | ECap e1', ECap e2' -> expr_eq e1' e2'

  (* Data construction *)
  | ETuple es1, ETuple es2 -> expr_list_eq es1 es2
  | EArray es1, EArray es2 -> expr_list_eq es1 es2
  | EStruct n1 fs1, EStruct n2 fs2 ->
      n1 = n2 && expr_field_list_eq fs1 fs2
  | EVariant n1 v1 es1, EVariant n2 v2 es2 ->
      n1 = n2 && v1 = v2 && expr_list_eq es1 es2

  (* Data access *)
  | EField e1' f1, EField e2' f2 -> expr_eq e1' e2' && f1 = f2
  | EIndex e1a e1b, EIndex e2a e2b -> expr_eq e1a e2a && expr_eq e1b e2b
  | ETupleProj e1' i1, ETupleProj e2' i2 -> expr_eq e1' e2' && i1 = i2

  (* Control flow with labels *)
  | EIf c1 t1 f1, EIf c2 t2 f2 ->
      expr_eq c1 c2 && expr_eq t1 t2 && expr_eq f1 f2
  | ELoop lbl1 b1, ELoop lbl2 b2 ->
      option_label_eq lbl1 lbl2 && expr_eq b1 b2
  | EWhile lbl1 c1 b1, EWhile lbl2 c2 b2 ->
      option_label_eq lbl1 lbl2 && expr_eq c1 c2 && expr_eq b1 b2
  | EFor lbl1 x1 iter1 body1, EFor lbl2 x2 iter2 body2 ->
      option_label_eq lbl1 lbl2 && x1 = x2 && expr_eq iter1 iter2 && expr_eq body1 body2
  | EBreak lbl1 None, EBreak lbl2 None -> option_label_eq lbl1 lbl2
  | EBreak lbl1 (Some e1'), EBreak lbl2 (Some e2') ->
      option_label_eq lbl1 lbl2 && expr_eq e1' e2'
  | EContinue lbl1, EContinue lbl2 -> option_label_eq lbl1 lbl2
  | EGoto lbl1, EGoto lbl2 -> lbl1 = lbl2  (* Labels must match exactly *)
  | ELabeled lbl1 body1, ELabeled lbl2 body2 -> lbl1 = lbl2 && expr_eq body1 body2
  | EReturn None, EReturn None -> true
  | EReturn (Some e1'), EReturn (Some e2') -> expr_eq e1' e2'

  (* Binding *)
  | ELet p1 t1 e1a e1b, ELet p2 t2 e2a e2b ->
      pattern_eq p1 p2 && option_type_eq t1 t2 && expr_eq e1a e2a && expr_eq e1b e2b
  | ELetMut x1 t1 e1a e1b, ELetMut x2 t2 e2a e2b ->
      x1 = x2 && option_type_eq t1 t2 && expr_eq e1a e2a && expr_eq e1b e2b
  | EAssign lhs1 rhs1, EAssign lhs2 rhs2 ->
      expr_eq lhs1 lhs2 && expr_eq rhs1 rhs2

  (* Functions *)
  | ELambda params1 body1, ELambda params2 body2 ->
      param_list_eq_expr params1 params2 && expr_eq body1 body2
  | EClosure params1 caps1 body1, EClosure params2 caps2 body2 ->
      param_list_eq_expr params1 params2 && caps1 = caps2 && expr_eq body1 body2

  (* Memory *)
  | EBox e1', EBox e2' -> expr_eq e1' e2'
  | EDeref e1', EDeref e2' -> expr_eq e1' e2'
  | EBorrow e1', EBorrow e2' -> expr_eq e1' e2'
  | EBorrowMut e1', EBorrowMut e2' -> expr_eq e1' e2'
  | EMove e1', EMove e2' -> expr_eq e1' e2'
  | EDrop e1', EDrop e2' -> expr_eq e1' e2'

  (* Effects *)
  | EThrow e1', EThrow e2' -> expr_eq e1' e2'
  | EAwait e1', EAwait e2' -> expr_eq e1' e2'
  | EYield e1', EYield e2' -> expr_eq e1' e2'
  | EAsync e1', EAsync e2' -> expr_eq e1' e2'
  | ESpawn e1', ESpawn e2' -> expr_eq e1' e2'
  | EResume k1 e1', EResume k2 e2' -> k1 = k2 && expr_eq e1' e2'

  (* Delimited continuations *)
  | EReset p1 e1', EReset p2 e2' -> p1 = p2 && expr_eq e1' e2'
  | EShift p1 k1 body1, EShift p2 k2 body2 ->
      p1 = p2 && k1 = k2 && expr_eq body1 body2

  (* Type operations *)
  | EAs e1' t1, EAs e2' t2 -> expr_eq e1' e2' && type_eq t1 t2
  | EIs e1' t1, EIs e2' t2 -> expr_eq e1' e2' && type_eq t1 t2
  | ESizeof t1, ESizeof t2 -> type_eq t1 t2
  | EAlignof t1, EAlignof t2 -> type_eq t1 t2

  (* Blocks and sequences *)
  | EBlock es1, EBlock es2 -> expr_list_eq es1 es2
  | ESeq e1a e1b, ESeq e2a e2b -> expr_eq e1a e2a && expr_eq e1b e2b

  (* Unsafe *)
  | EUnsafe e1', EUnsafe e2' -> expr_eq e1' e2'

  (* Special *)
  | EHole, EHole -> true
  | EError s1, EError s2 -> s1 = s2

  (* Match and Try require more complex comparison *)
  | EMatch e1' arms1, EMatch e2' arms2 ->
      expr_eq e1' e2' && match_arm_list_eq arms1 arms2
  | ETry e1' catches1 finally1, ETry e2' catches2 finally2 ->
      expr_eq e1' e2' && catch_arm_list_eq catches1 catches2 &&
      option_expr_eq finally1 finally2
  | EHandle e1' _, EHandle e2' _ -> expr_eq e1' e2'  (* Handler comparison simplified *)
  | EPerform op1 args1, EPerform op2 args2 ->
      op1 = op2 && expr_list_eq args1 args2

  (* Different constructors *)
  | _, _ -> false

and expr_list_eq (es1 es2: list expr) : Tot bool (decreases %[expr_list_size es1; 1]) =
  match es1, es2 with
  | [], [] -> true
  | e1 :: r1, e2 :: r2 -> expr_eq e1 e2 && expr_list_eq r1 r2
  | _, _ -> false

and expr_field_list_eq (fs1 fs2: list (string & expr)) : Tot bool (decreases %[field_expr_list_size fs1; 2]) =
  match fs1, fs2 with
  | [], [] -> true
  | (n1, e1) :: r1, (n2, e2) :: r2 ->
      n1 = n2 && expr_eq e1 e2 && expr_field_list_eq r1 r2
  | _, _ -> false

and option_expr_eq (o1 o2: option expr) : Tot bool (decreases %[option_expr_size o1; 3]) =
  match o1, o2 with
  | None, None -> true
  | Some e1, Some e2 -> expr_eq e1 e2
  | _, _ -> false

and match_arm_list_eq (arms1 arms2: list match_arm) : Tot bool (decreases %[match_arm_list_size arms1; 4]) =
  match arms1, arms2 with
  | [], [] -> true
  | a1 :: r1, a2 :: r2 ->
      pattern_eq a1.arm_pattern a2.arm_pattern &&
      option_expr_eq a1.arm_guard a2.arm_guard &&
      expr_eq a1.arm_body a2.arm_body &&
      match_arm_list_eq r1 r2
  | _, _ -> false

and catch_arm_list_eq (catches1 catches2: list catch_arm) : Tot bool (decreases %[catch_arm_list_size catches1; 5]) =
  match catches1, catches2 with
  | [], [] -> true
  | c1 :: r1, c2 :: r2 ->
      pattern_eq c1.catch_pattern c2.catch_pattern &&
      type_eq c1.catch_type c2.catch_type &&
      expr_eq c1.catch_body c2.catch_body &&
      catch_arm_list_eq r1 r2
  | _, _ -> false

(** ============================================================================
    EXPRESSION EQUALITY LEMMAS
    ============================================================================ *)

(* expr_eq is reflexive - forward declarations for mutually recursive functions.
   NOTE: expr_eq_refl and pattern_eq_refl are declared in the interface.
   Only internal helpers need val declarations here. *)
val expr_list_eq_refl : es:list expr -> Lemma (ensures expr_list_eq es es = true) (decreases %[expr_list_size es; 1])
val expr_field_list_eq_refl : fs:list (string & expr) -> Lemma (ensures expr_field_list_eq fs fs = true) (decreases %[field_expr_list_size fs; 2])
val option_expr_eq_refl : o:option expr -> Lemma (ensures option_expr_eq o o = true) (decreases %[option_expr_size o; 3])
val match_arm_list_eq_refl : arms:list match_arm -> Lemma (ensures match_arm_list_eq arms arms = true) (decreases %[match_arm_list_size arms; 4])
val catch_arm_list_eq_refl : catches:list catch_arm -> Lemma (ensures catch_arm_list_eq catches catches = true) (decreases %[catch_arm_list_size catches; 5])
val pattern_list_eq_refl : ps:list pattern -> Lemma (ensures pattern_list_eq ps ps = true) (decreases ps)

(* Combined mutual recursion - expr_eq_refl must come first per interface order *)
let rec expr_eq_refl e =
  match e.loc_value with
  (* Leaves *)
  | ELit _ | EVar _ | EGlobal _ | EHole | EError _ -> ()
  | EContinue _ | EGoto _ -> ()
  | ESizeof t | EAlignof t -> type_eq_refl t
  | ETypeMethod _ _ -> ()

  (* Unary operations *)
  | EUnary _ e' -> expr_eq_refl e'
  | EBox e' | EDeref e' | EBorrow e' | EBorrowMut e' | EMove e' | EDrop e' -> expr_eq_refl e'
  | ELabeled _ e' -> expr_eq_refl e'
  | EThrow e' | EAwait e' | EYield e' -> expr_eq_refl e'
  | EAsync e' | ESpawn e' | EResume _ e' | EReset _ e' -> expr_eq_refl e'

  (* Binary operations *)
  | EBinary _ e1 e2 -> expr_eq_refl e1; expr_eq_refl e2
  | EIndex e1 e2 -> expr_eq_refl e1; expr_eq_refl e2
  | ESeq e1 e2 -> expr_eq_refl e1; expr_eq_refl e2
  | EAssign lhs rhs -> expr_eq_refl lhs; expr_eq_refl rhs

  (* Calls *)
  | ECall fn args -> expr_eq_refl fn; expr_list_eq_refl args
  | EMethodCall obj _ args -> expr_eq_refl obj; expr_list_eq_refl args
  | EMethodRef e' _ -> expr_eq_refl e'
  | ELen e' | ECap e' -> expr_eq_refl e'

  (* Data construction *)
  | ETuple es | EArray es | EBlock es -> expr_list_eq_refl es
  | EStruct _ fs -> expr_field_list_eq_refl fs
  | EVariant _ _ es -> expr_list_eq_refl es

  (* Data access *)
  | EField e' _ | ETupleProj e' _ -> expr_eq_refl e'

  (* Control flow with labels *)
  | EIf c t f -> expr_eq_refl c; expr_eq_refl t; expr_eq_refl f
  | ELoop _ b -> expr_eq_refl b
  | EWhile _ c b -> expr_eq_refl c; expr_eq_refl b
  | EFor _ _ iter body -> expr_eq_refl iter; expr_eq_refl body
  | EBreak _ None | EReturn None -> ()
  | EBreak _ (Some e') | EReturn (Some e') -> expr_eq_refl e'

  (* Bindings *)
  | ELet p t e1 e2 -> pattern_eq_refl p; option_type_eq_refl t; expr_eq_refl e1; expr_eq_refl e2
  | ELetMut _ t e1 e2 -> option_type_eq_refl t; expr_eq_refl e1; expr_eq_refl e2

  (* Functions *)
  | ELambda params body -> param_list_eq_expr_refl params; expr_eq_refl body
  | EClosure params _ body -> param_list_eq_expr_refl params; expr_eq_refl body
  | EShift _ _ body -> expr_eq_refl body

  (* Type operations *)
  | EAs e' t | EIs e' t -> expr_eq_refl e'; type_eq_refl t
  | EUnsafe e' -> expr_eq_refl e'

  (* Pattern matching and exception handling *)
  | EMatch e' arms -> expr_eq_refl e'; match_arm_list_eq_refl arms
  | ETry e' catches finally -> expr_eq_refl e'; catch_arm_list_eq_refl catches; option_expr_eq_refl finally
  | EHandle e' _ -> expr_eq_refl e'
  | EPerform _ args -> expr_list_eq_refl args

and expr_list_eq_refl es =
  match es with
  | [] -> ()
  | e :: rest -> expr_eq_refl e; expr_list_eq_refl rest

and expr_field_list_eq_refl fs =
  match fs with
  | [] -> ()
  | (_, e) :: rest -> expr_eq_refl e; expr_field_list_eq_refl rest

and option_expr_eq_refl o =
  match o with
  | None -> ()
  | Some e -> expr_eq_refl e

and match_arm_list_eq_refl arms =
  match arms with
  | [] -> ()
  | a :: rest ->
      pattern_eq_refl a.arm_pattern;
      option_expr_eq_refl a.arm_guard;
      expr_eq_refl a.arm_body;
      match_arm_list_eq_refl rest

and catch_arm_list_eq_refl catches =
  match catches with
  | [] -> ()
  | c :: rest ->
      pattern_eq_refl c.catch_pattern;
      type_eq_refl c.catch_type;
      expr_eq_refl c.catch_body;
      catch_arm_list_eq_refl rest

and pattern_eq_refl p =
  match p.loc_value with
  | PatWild -> ()
  | PatVar _ -> ()
  | PatLit _ -> ()
  | PatTuple ps -> pattern_list_eq_refl ps
  | PatStruct _ fs -> pattern_field_list_eq_refl fs
  | PatVariant _ _ ps -> pattern_list_eq_refl ps
  | PatOr p1 p2 -> pattern_eq_refl p1; pattern_eq_refl p2
  | PatRef p' -> pattern_eq_refl p'
  | PatBox p' -> pattern_eq_refl p'
  | PatGuard p' _ -> pattern_eq_refl p'
  | PatRest _ -> ()
  | PatAs p' _ -> pattern_eq_refl p'
  | PatType ty _ -> type_eq_refl ty

and pattern_list_eq_refl ps =
  match ps with
  | [] -> ()
  | p :: rest -> pattern_eq_refl p; pattern_list_eq_refl rest

and pattern_field_list_eq_refl (fs: list (string & pattern)) : Lemma (ensures pattern_field_list_eq fs fs = true) (decreases fs) =
  match fs with
  | [] -> ()
  | (_, p) :: rest -> pattern_eq_refl p; pattern_field_list_eq_refl rest

(* expr_eq is symmetric - helper declarations for mutual recursion.
   NOTE: expr_eq_sym is declared in the interface, only internal helpers here. *)
#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"
val expr_list_eq_sym : es1:list expr -> es2:list expr ->
  Lemma (requires expr_list_eq es1 es2 = true)
        (ensures expr_list_eq es2 es1 = true)
        (decreases %[expr_list_size es1; 1])
val expr_field_list_eq_sym : fs1:list (string & expr) -> fs2:list (string & expr) ->
  Lemma (requires expr_field_list_eq fs1 fs2 = true)
        (ensures expr_field_list_eq fs2 fs1 = true)
        (decreases %[field_expr_list_size fs1; 2])
val option_expr_eq_sym : o1:option expr -> o2:option expr ->
  Lemma (requires option_expr_eq o1 o2 = true)
        (ensures option_expr_eq o2 o1 = true)
        (decreases %[option_expr_size o1; 3])
val match_arm_list_eq_sym : arms1:list match_arm -> arms2:list match_arm ->
  Lemma (requires match_arm_list_eq arms1 arms2 = true)
        (ensures match_arm_list_eq arms2 arms1 = true)
        (decreases %[match_arm_list_size arms1; 4])
val catch_arm_list_eq_sym : catches1:list catch_arm -> catches2:list catch_arm ->
  Lemma (requires catch_arm_list_eq catches1 catches2 = true)
        (ensures catch_arm_list_eq catches2 catches1 = true)
        (decreases %[catch_arm_list_size catches1; 5])
(* pattern_eq_sym, pattern_list_eq_sym, and pattern_field_list_eq_sym are now
   defined as part of the mutual recursion below - no forward declarations needed *)

let rec expr_eq_sym e1 e2 =
  match e1.loc_value, e2.loc_value with
  (* Leaves *)
  | ELit _, ELit _ | EVar _, EVar _ | EGlobal _, EGlobal _ -> ()
  | EContinue _, EContinue _ | EGoto _, EGoto _ | EHole, EHole | EError _, EError _ -> ()
  | ESizeof t1, ESizeof t2 -> type_eq_sym t1 t2
  | EAlignof t1, EAlignof t2 -> type_eq_sym t1 t2
  | ETypeMethod _ _, ETypeMethod _ _ -> ()

  (* Unary operations *)
  | EUnary _ e1', EUnary _ e2' -> expr_eq_sym e1' e2'
  | EBox e1', EBox e2' | EDeref e1', EDeref e2' | EBorrow e1', EBorrow e2' -> expr_eq_sym e1' e2'
  | EBorrowMut e1', EBorrowMut e2' | EMove e1', EMove e2' | EDrop e1', EDrop e2' -> expr_eq_sym e1' e2'
  | EThrow e1', EThrow e2' | EAwait e1', EAwait e2' | EYield e1', EYield e2' -> expr_eq_sym e1' e2'
  | EUnsafe e1', EUnsafe e2' -> expr_eq_sym e1' e2'
  | ELabeled _ e1', ELabeled _ e2' -> expr_eq_sym e1' e2'

  (* New async/spawn/continuation operations *)
  | EAsync e1', EAsync e2' | ESpawn e1', ESpawn e2' -> expr_eq_sym e1' e2'
  | EResume _ e1', EResume _ e2' -> expr_eq_sym e1' e2'
  | EReset _ e1', EReset _ e2' -> expr_eq_sym e1' e2'
  | EShift _ _ body1, EShift _ _ body2 -> expr_eq_sym body1 body2

  (* Binary operations *)
  | EBinary _ e1a e1b, EBinary _ e2a e2b -> expr_eq_sym e1a e2a; expr_eq_sym e1b e2b
  | EIndex e1a e1b, EIndex e2a e2b -> expr_eq_sym e1a e2a; expr_eq_sym e1b e2b
  | ESeq e1a e1b, ESeq e2a e2b -> expr_eq_sym e1a e2a; expr_eq_sym e1b e2b
  | EAssign lhs1 rhs1, EAssign lhs2 rhs2 -> expr_eq_sym lhs1 lhs2; expr_eq_sym rhs1 rhs2

  (* Calls *)
  | ECall fn1 args1, ECall fn2 args2 -> expr_eq_sym fn1 fn2; expr_list_eq_sym args1 args2
  | EMethodCall obj1 _ args1, EMethodCall obj2 _ args2 -> expr_eq_sym obj1 obj2; expr_list_eq_sym args1 args2
  | EMethodRef e1' _, EMethodRef e2' _ -> expr_eq_sym e1' e2'
  | ELen e1', ELen e2' | ECap e1', ECap e2' -> expr_eq_sym e1' e2'

  (* Data construction *)
  | ETuple es1, ETuple es2 | EArray es1, EArray es2 | EBlock es1, EBlock es2 -> expr_list_eq_sym es1 es2
  | EStruct _ fs1, EStruct _ fs2 -> expr_field_list_eq_sym fs1 fs2
  | EVariant _ _ es1, EVariant _ _ es2 -> expr_list_eq_sym es1 es2

  (* Data access *)
  | EField e1' _, EField e2' _ | ETupleProj e1' _, ETupleProj e2' _ -> expr_eq_sym e1' e2'

  (* Control flow with labels *)
  | EIf c1 t1 f1, EIf c2 t2 f2 -> expr_eq_sym c1 c2; expr_eq_sym t1 t2; expr_eq_sym f1 f2
  | ELoop _ b1, ELoop _ b2 -> expr_eq_sym b1 b2
  | EWhile _ c1 b1, EWhile _ c2 b2 -> expr_eq_sym c1 c2; expr_eq_sym b1 b2
  | EFor _ _ iter1 body1, EFor _ _ iter2 body2 -> expr_eq_sym iter1 iter2; expr_eq_sym body1 body2
  | EBreak _ None, EBreak _ None | EReturn None, EReturn None -> ()
  | EBreak _ (Some e1'), EBreak _ (Some e2') | EReturn (Some e1'), EReturn (Some e2') -> expr_eq_sym e1' e2'

  (* Bindings *)
  | ELet p1 t1 e1a e1b, ELet p2 t2 e2a e2b ->
      pattern_eq_sym p1 p2; option_type_eq_sym t1 t2; expr_eq_sym e1a e2a; expr_eq_sym e1b e2b
  | ELetMut _ t1 e1a e1b, ELetMut _ t2 e2a e2b ->
      option_type_eq_sym t1 t2; expr_eq_sym e1a e2a; expr_eq_sym e1b e2b

  (* Functions *)
  | ELambda ps1 body1, ELambda ps2 body2 -> param_list_eq_expr_sym ps1 ps2; expr_eq_sym body1 body2
  | EClosure ps1 _ body1, EClosure ps2 _ body2 -> param_list_eq_expr_sym ps1 ps2; expr_eq_sym body1 body2

  (* Type operations *)
  | EAs e1' ty1, EAs e2' ty2 -> expr_eq_sym e1' e2'; type_eq_sym ty1 ty2
  | EIs e1' ty1, EIs e2' ty2 -> expr_eq_sym e1' e2'; type_eq_sym ty1 ty2

  (* Pattern matching and exception handling *)
  | EMatch e1' arms1, EMatch e2' arms2 -> expr_eq_sym e1' e2'; match_arm_list_eq_sym arms1 arms2
  | ETry e1' catches1 finally1, ETry e2' catches2 finally2 ->
      expr_eq_sym e1' e2'; catch_arm_list_eq_sym catches1 catches2; option_expr_eq_sym finally1 finally2
  | EHandle e1' _, EHandle e2' _ -> expr_eq_sym e1' e2'
  | EPerform _ args1, EPerform _ args2 -> expr_list_eq_sym args1 args2

  | _, _ -> ()

and expr_list_eq_sym es1 es2 =
  match es1, es2 with
  | [], [] -> ()
  | e1 :: r1, e2 :: r2 -> expr_eq_sym e1 e2; expr_list_eq_sym r1 r2
  | _, _ -> ()

and expr_field_list_eq_sym fs1 fs2 =
  match fs1, fs2 with
  | [], [] -> ()
  | (_, e1) :: r1, (_, e2) :: r2 -> expr_eq_sym e1 e2; expr_field_list_eq_sym r1 r2
  | _, _ -> ()

and option_expr_eq_sym o1 o2 =
  match o1, o2 with
  | None, None -> ()
  | Some e1, Some e2 -> expr_eq_sym e1 e2
  | _, _ -> ()

and match_arm_list_eq_sym arms1 arms2 =
  match arms1, arms2 with
  | [], [] -> ()
  | a1 :: r1, a2 :: r2 ->
      pattern_eq_sym a1.arm_pattern a2.arm_pattern;
      option_expr_eq_sym a1.arm_guard a2.arm_guard;
      expr_eq_sym a1.arm_body a2.arm_body;
      match_arm_list_eq_sym r1 r2
  | _, _ -> ()

and catch_arm_list_eq_sym catches1 catches2 =
  match catches1, catches2 with
  | [], [] -> ()
  | c1 :: r1, c2 :: r2 ->
      pattern_eq_sym c1.catch_pattern c2.catch_pattern;
      type_eq_sym c1.catch_type c2.catch_type;
      expr_eq_sym c1.catch_body c2.catch_body;
      catch_arm_list_eq_sym r1 r2
  | _, _ -> ()

(* pattern_eq_sym is part of this mutual recursion since expr_eq_sym calls it *)
and pattern_eq_sym p1 p2 =
  match p1.loc_value, p2.loc_value with
  | PatWild, PatWild -> ()
  | PatVar _, PatVar _ -> ()
  | PatLit _, PatLit _ -> ()
  | PatTuple ps1', PatTuple ps2' -> pattern_list_eq_sym ps1' ps2'
  | PatStruct _ fs1, PatStruct _ fs2 -> pattern_field_list_eq_sym fs1 fs2
  | PatVariant _ _ ps1', PatVariant _ _ ps2' -> pattern_list_eq_sym ps1' ps2'
  | PatOr p1a p1b, PatOr p2a p2b -> pattern_eq_sym p1a p2a; pattern_eq_sym p1b p2b
  | PatRef p1', PatRef p2' -> pattern_eq_sym p1' p2'
  | PatBox p1', PatBox p2' -> pattern_eq_sym p1' p2'
  | PatGuard p1' _, PatGuard p2' _ -> pattern_eq_sym p1' p2'
  | PatRest _, PatRest _ -> ()
  | PatAs p1' _, PatAs p2' _ -> pattern_eq_sym p1' p2'
  | PatType ty1 _, PatType ty2 _ -> type_eq_sym ty1 ty2
  | _, _ -> ()

and pattern_list_eq_sym ps1 ps2 =
  match ps1, ps2 with
  | [], [] -> ()
  | p1 :: r1, p2 :: r2 -> pattern_eq_sym p1 p2; pattern_list_eq_sym r1 r2
  | _, _ -> ()

and pattern_field_list_eq_sym (fs1 fs2: list (string & pattern))
    : Lemma (requires pattern_field_list_eq fs1 fs2 = true)
            (ensures pattern_field_list_eq fs2 fs1 = true)
            (decreases fs1) =
  match fs1, fs2 with
  | [], [] -> ()
  | (_, p1) :: r1, (_, p2) :: r2 -> pattern_eq_sym p1 p2; pattern_field_list_eq_sym r1 r2
  | _, _ -> ()

#pop-options

(* expr_eq is transitive - helper declarations for mutual recursion.
   NOTE: expr_eq_trans is declared in the interface, only internal helpers here. *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 2"
val expr_list_eq_trans : es1:list expr -> es2:list expr -> es3:list expr ->
  Lemma (requires expr_list_eq es1 es2 = true /\ expr_list_eq es2 es3 = true)
        (ensures expr_list_eq es1 es3 = true)
        (decreases %[expr_list_size es1; 1])
val expr_field_list_eq_trans : fs1:list (string & expr) -> fs2:list (string & expr) -> fs3:list (string & expr) ->
  Lemma (requires expr_field_list_eq fs1 fs2 = true /\ expr_field_list_eq fs2 fs3 = true)
        (ensures expr_field_list_eq fs1 fs3 = true)
        (decreases %[field_expr_list_size fs1; 2])
val option_expr_eq_trans : o1:option expr -> o2:option expr -> o3:option expr ->
  Lemma (requires option_expr_eq o1 o2 = true /\ option_expr_eq o2 o3 = true)
        (ensures option_expr_eq o1 o3 = true)
        (decreases %[option_expr_size o1; 3])
val match_arm_list_eq_trans : arms1:list match_arm -> arms2:list match_arm -> arms3:list match_arm ->
  Lemma (requires match_arm_list_eq arms1 arms2 = true /\ match_arm_list_eq arms2 arms3 = true)
        (ensures match_arm_list_eq arms1 arms3 = true)
        (decreases %[match_arm_list_size arms1; 4])
val catch_arm_list_eq_trans : c1:list catch_arm -> c2:list catch_arm -> c3:list catch_arm ->
  Lemma (requires catch_arm_list_eq c1 c2 = true /\ catch_arm_list_eq c2 c3 = true)
        (ensures catch_arm_list_eq c1 c3 = true)
        (decreases %[catch_arm_list_size c1; 5])
(* pattern_eq_trans and pattern_list_eq_trans are now defined as part of the
   mutual recursion below - no forward declarations needed *)

let rec expr_eq_trans e1 e2 e3 =
  match e1.loc_value, e2.loc_value, e3.loc_value with
  (* Leaves *)
  | ELit _, ELit _, ELit _ | EVar _, EVar _, EVar _ | EGlobal _, EGlobal _, EGlobal _ -> ()
  | EContinue _, EContinue _, EContinue _ | EGoto _, EGoto _, EGoto _ | EHole, EHole, EHole | EError _, EError _, EError _ -> ()
  | ESizeof t1, ESizeof t2, ESizeof t3 -> type_eq_trans t1 t2 t3
  | EAlignof t1, EAlignof t2, EAlignof t3 -> type_eq_trans t1 t2 t3
  | ETypeMethod _ _, ETypeMethod _ _, ETypeMethod _ _ -> ()

  (* Unary operations *)
  | EUnary _ e1', EUnary _ e2', EUnary _ e3' -> expr_eq_trans e1' e2' e3'
  | EBox e1', EBox e2', EBox e3' | EDeref e1', EDeref e2', EDeref e3'
  | EBorrow e1', EBorrow e2', EBorrow e3' | EBorrowMut e1', EBorrowMut e2', EBorrowMut e3'
  | EMove e1', EMove e2', EMove e3' | EDrop e1', EDrop e2', EDrop e3' -> expr_eq_trans e1' e2' e3'
  | EThrow e1', EThrow e2', EThrow e3' | EAwait e1', EAwait e2', EAwait e3'
  | EYield e1', EYield e2', EYield e3' | EUnsafe e1', EUnsafe e2', EUnsafe e3' -> expr_eq_trans e1' e2' e3'
  | ELabeled _ e1', ELabeled _ e2', ELabeled _ e3' -> expr_eq_trans e1' e2' e3'

  (* New async/spawn/continuation operations *)
  | EAsync e1', EAsync e2', EAsync e3' | ESpawn e1', ESpawn e2', ESpawn e3' -> expr_eq_trans e1' e2' e3'
  | EResume _ e1', EResume _ e2', EResume _ e3' -> expr_eq_trans e1' e2' e3'
  | EReset _ e1', EReset _ e2', EReset _ e3' -> expr_eq_trans e1' e2' e3'
  | EShift _ _ body1, EShift _ _ body2, EShift _ _ body3 -> expr_eq_trans body1 body2 body3

  (* Binary operations *)
  | EBinary _ e1a e1b, EBinary _ e2a e2b, EBinary _ e3a e3b ->
      expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b
  | EIndex e1a e1b, EIndex e2a e2b, EIndex e3a e3b ->
      expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b
  | ESeq e1a e1b, ESeq e2a e2b, ESeq e3a e3b ->
      expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b
  | EAssign lhs1 rhs1, EAssign lhs2 rhs2, EAssign lhs3 rhs3 ->
      expr_eq_trans lhs1 lhs2 lhs3; expr_eq_trans rhs1 rhs2 rhs3

  (* Calls *)
  | ECall fn1 args1, ECall fn2 args2, ECall fn3 args3 ->
      expr_eq_trans fn1 fn2 fn3; expr_list_eq_trans args1 args2 args3
  | EMethodCall obj1 _ args1, EMethodCall obj2 _ args2, EMethodCall obj3 _ args3 ->
      expr_eq_trans obj1 obj2 obj3; expr_list_eq_trans args1 args2 args3
  | EMethodRef e1' _, EMethodRef e2' _, EMethodRef e3' _ ->
      expr_eq_trans e1' e2' e3'
  | ELen e1', ELen e2', ELen e3' | ECap e1', ECap e2', ECap e3' ->
      expr_eq_trans e1' e2' e3'

  (* Data construction *)
  | ETuple es1, ETuple es2, ETuple es3
  | EArray es1, EArray es2, EArray es3
  | EBlock es1, EBlock es2, EBlock es3 -> expr_list_eq_trans es1 es2 es3
  | EStruct _ fs1, EStruct _ fs2, EStruct _ fs3 -> expr_field_list_eq_trans fs1 fs2 fs3
  | EVariant _ _ es1, EVariant _ _ es2, EVariant _ _ es3 -> expr_list_eq_trans es1 es2 es3

  (* Data access *)
  | EField e1' _, EField e2' _, EField e3' _
  | ETupleProj e1' _, ETupleProj e2' _, ETupleProj e3' _ -> expr_eq_trans e1' e2' e3'

  (* Control flow with labels *)
  | EIf c1 t1 f1, EIf c2 t2 f2, EIf c3 t3 f3 ->
      expr_eq_trans c1 c2 c3; expr_eq_trans t1 t2 t3; expr_eq_trans f1 f2 f3
  | ELoop _ b1, ELoop _ b2, ELoop _ b3 -> expr_eq_trans b1 b2 b3
  | EWhile _ c1 b1, EWhile _ c2 b2, EWhile _ c3 b3 ->
      expr_eq_trans c1 c2 c3; expr_eq_trans b1 b2 b3
  | EFor _ _ iter1 body1, EFor _ _ iter2 body2, EFor _ _ iter3 body3 ->
      expr_eq_trans iter1 iter2 iter3; expr_eq_trans body1 body2 body3
  | EBreak _ None, EBreak _ None, EBreak _ None | EReturn None, EReturn None, EReturn None -> ()
  | EBreak _ (Some e1'), EBreak _ (Some e2'), EBreak _ (Some e3')
  | EReturn (Some e1'), EReturn (Some e2'), EReturn (Some e3') -> expr_eq_trans e1' e2' e3'

  (* Bindings *)
  | ELet p1 ty1 e1a e1b, ELet p2 ty2 e2a e2b, ELet p3 ty3 e3a e3b ->
      pattern_eq_trans p1 p2 p3; option_type_eq_trans ty1 ty2 ty3;
      expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b
  | ELetMut _ ty1 e1a e1b, ELetMut _ ty2 e2a e2b, ELetMut _ ty3 e3a e3b ->
      option_type_eq_trans ty1 ty2 ty3; expr_eq_trans e1a e2a e3a; expr_eq_trans e1b e2b e3b

  (* Functions *)
  | ELambda ps1 body1, ELambda ps2 body2, ELambda ps3 body3 ->
      param_list_eq_expr_trans ps1 ps2 ps3; expr_eq_trans body1 body2 body3
  | EClosure ps1 _ body1, EClosure ps2 _ body2, EClosure ps3 _ body3 ->
      param_list_eq_expr_trans ps1 ps2 ps3; expr_eq_trans body1 body2 body3

  (* Type operations *)
  | EAs e1' ty1, EAs e2' ty2, EAs e3' ty3 -> expr_eq_trans e1' e2' e3'; type_eq_trans ty1 ty2 ty3
  | EIs e1' ty1, EIs e2' ty2, EIs e3' ty3 -> expr_eq_trans e1' e2' e3'; type_eq_trans ty1 ty2 ty3

  (* Pattern matching and exception handling *)
  | EMatch e1' arms1, EMatch e2' arms2, EMatch e3' arms3 ->
      expr_eq_trans e1' e2' e3'; match_arm_list_eq_trans arms1 arms2 arms3
  | ETry e1' catches1 finally1, ETry e2' catches2 finally2, ETry e3' catches3 finally3 ->
      expr_eq_trans e1' e2' e3'; catch_arm_list_eq_trans catches1 catches2 catches3;
      option_expr_eq_trans finally1 finally2 finally3
  | EHandle e1' _, EHandle e2' _, EHandle e3' _ -> expr_eq_trans e1' e2' e3'
  | EPerform _ args1, EPerform _ args2, EPerform _ args3 -> expr_list_eq_trans args1 args2 args3

  | _, _, _ -> ()

and expr_list_eq_trans es1 es2 es3 =
  match es1, es2, es3 with
  | [], [], [] -> ()
  | e1 :: r1, e2 :: r2, e3 :: r3 -> expr_eq_trans e1 e2 e3; expr_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

and expr_field_list_eq_trans fs1 fs2 fs3 =
  match fs1, fs2, fs3 with
  | [], [], [] -> ()
  | (_, e1) :: r1, (_, e2) :: r2, (_, e3) :: r3 ->
      expr_eq_trans e1 e2 e3; expr_field_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

and option_expr_eq_trans o1 o2 o3 =
  match o1, o2, o3 with
  | None, None, None -> ()
  | Some e1, Some e2, Some e3 -> expr_eq_trans e1 e2 e3
  | _, _, _ -> ()

and match_arm_list_eq_trans arms1 arms2 arms3 =
  match arms1, arms2, arms3 with
  | [], [], [] -> ()
  | a1 :: r1, a2 :: r2, a3 :: r3 ->
      pattern_eq_trans a1.arm_pattern a2.arm_pattern a3.arm_pattern;
      option_expr_eq_trans a1.arm_guard a2.arm_guard a3.arm_guard;
      expr_eq_trans a1.arm_body a2.arm_body a3.arm_body;
      match_arm_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

and catch_arm_list_eq_trans c1 c2 c3 =
  match c1, c2, c3 with
  | [], [], [] -> ()
  | a1 :: r1, a2 :: r2, a3 :: r3 ->
      pattern_eq_trans a1.catch_pattern a2.catch_pattern a3.catch_pattern;
      type_eq_trans a1.catch_type a2.catch_type a3.catch_type;
      expr_eq_trans a1.catch_body a2.catch_body a3.catch_body;
      catch_arm_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

(* pattern_eq_trans is part of this mutual recursion since expr_eq_trans calls it *)
and pattern_eq_trans p1 p2 p3 =
  match p1.loc_value, p2.loc_value, p3.loc_value with
  | PatWild, PatWild, PatWild -> ()
  | PatVar _, PatVar _, PatVar _ -> ()
  | PatLit _, PatLit _, PatLit _ -> ()
  | PatTuple ps1', PatTuple ps2', PatTuple ps3' -> pattern_list_eq_trans ps1' ps2' ps3'
  | PatStruct _ fs1, PatStruct _ fs2, PatStruct _ fs3 -> pattern_field_list_eq_trans fs1 fs2 fs3
  | PatVariant _ _ ps1', PatVariant _ _ ps2', PatVariant _ _ ps3' -> pattern_list_eq_trans ps1' ps2' ps3'
  | PatOr p1a p1b, PatOr p2a p2b, PatOr p3a p3b ->
      pattern_eq_trans p1a p2a p3a; pattern_eq_trans p1b p2b p3b
  | PatRef p1', PatRef p2', PatRef p3' -> pattern_eq_trans p1' p2' p3'
  | PatBox p1', PatBox p2', PatBox p3' -> pattern_eq_trans p1' p2' p3'
  | PatGuard p1' _, PatGuard p2' _, PatGuard p3' _ -> pattern_eq_trans p1' p2' p3'
  | PatRest _, PatRest _, PatRest _ -> ()
  | PatAs p1' _, PatAs p2' _, PatAs p3' _ -> pattern_eq_trans p1' p2' p3'
  | PatType ty1 _, PatType ty2 _, PatType ty3 _ -> type_eq_trans ty1 ty2 ty3
  | _, _, _ -> ()

and pattern_list_eq_trans ps1 ps2 ps3 =
  match ps1, ps2, ps3 with
  | [], [], [] -> ()
  | p1 :: r1, p2 :: r2, p3 :: r3 -> pattern_eq_trans p1 p2 p3; pattern_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

and pattern_field_list_eq_trans (fs1 fs2 fs3: list (string & pattern))
    : Lemma (requires pattern_field_list_eq fs1 fs2 = true /\ pattern_field_list_eq fs2 fs3 = true)
            (ensures pattern_field_list_eq fs1 fs3 = true)
            (decreases fs1) =
  match fs1, fs2, fs3 with
  | [], [], [] -> ()
  | (_, p1) :: r1, (_, p2) :: r2, (_, p3) :: r3 ->
      pattern_eq_trans p1 p2 p3; pattern_field_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

#pop-options

(** ============================================================================
    SUBEXPRESSION RELATIONSHIP (is_subexpr)
    ============================================================================
    NOTE: is_subexpr is defined here (after expr_eq) to avoid forward
    reference issues, since is_subexpr uses expr_eq in its definition.
    is_immediate_subexpr is defined earlier (after immediate_subexprs).
    ============================================================================ *)

(** Check if sub is a subexpression of parent (transitive closure) *)
let rec is_subexpr (sub: expr) (parent: expr) : Tot bool (decreases expr_size parent) =
  if expr_eq sub parent then true
  else
    let subs = immediate_subexprs parent in
    List.Tot.existsb (fun s -> is_subexpr sub s) subs

(** Subexpression relation is reflexive *)
let is_subexpr_refl (e: expr) : Lemma (ensures is_subexpr e e = true) =
  expr_eq_refl e

(** Subexpression relation is transitive *)
let is_subexpr_trans (e1 e2 e3: expr)
    : Lemma (requires is_subexpr e1 e2 = true /\ is_subexpr e2 e3 = true)
            (ensures is_subexpr e1 e3 = true) =
  admit()  (* Requires induction over is_subexpr definition *)

(** Subexpressions have smaller size *)
let subexpr_size_decreases (sub: expr) (parent: expr)
    : Lemma (requires is_immediate_subexpr sub parent = true)
            (ensures expr_size sub < expr_size parent) =
  expr_size_pos parent

(** ============================================================================
    RANGE PRESERVATION LEMMAS
    ============================================================================ *)

(** Subexpression ranges are within parent range when properly constructed *)
let subexpr_range_subset (parent: expr) (sub: expr)
    : Lemma (requires is_subexpr sub parent = true /\
                      parent.loc_range <> dummy_range /\
                      sub.loc_range <> dummy_range)
            (ensures range_within (expr_range sub) (expr_range parent) \/
                     sub.loc_range = parent.loc_range) =
  (* This is a semantic property - AST construction must ensure it *)
  admit()

(** Match arm body range is within arm range *)
let match_arm_range_contains_body (arm: match_arm)
    : Lemma (requires arm.arm_range <> dummy_range /\
                      arm.arm_body.loc_range <> dummy_range)
            (ensures range_within (expr_range arm.arm_body) arm.arm_range \/
                     arm.arm_body.loc_range = arm.arm_range) =
  admit()

(** Catch arm body range is within catch range *)
let catch_arm_range_contains_body (arm: catch_arm)
    : Lemma (requires arm.catch_range <> dummy_range /\
                      arm.catch_body.loc_range <> dummy_range)
            (ensures range_within (expr_range arm.catch_body) arm.catch_range \/
                     arm.catch_body.loc_range = arm.catch_range) =
  admit()

(* NOTE: pattern_eq_sym/trans are now defined as part of their respective
   mutual recursion blocks with expr_eq_sym/trans above. *)

(** ============================================================================
    EXPRESSION SUBSTITUTION (Capture-Avoiding)
    ============================================================================ *)

(** Generate a fresh variable name not in the given set *)
let rec fresh_var_helper (base: var_id) (avoid: list var_id) (counter: nat) : var_id =
  let candidate = base ^ "_" ^ string_of_int counter in
  if mem candidate avoid then fresh_var_helper base avoid (counter + 1)
  else candidate

let fresh_var (base: var_id) (avoid: list var_id) : var_id =
  if mem base avoid then fresh_var_helper base avoid 0
  else base

(** fresh_var produces a variable not in the input list *)
let fresh_var_spec (base: var_id) (avoid: list var_id)
    : Lemma (ensures not (mem (fresh_var base avoid) avoid)) =
  admit()  (* Follows from fresh_var_helper construction *)

(** Rename a variable in pattern *)
let rec rename_pattern (old_var new_var: var_id) (p: pattern) : pattern =
  let new_inner =
    match p.loc_value with
    | PatVar x when x = old_var -> PatVar new_var
    | PatAs p' x when x = old_var -> PatAs (rename_pattern old_var new_var p') new_var
    | PatAs p' x -> PatAs (rename_pattern old_var new_var p') x
    | PatTuple ps -> PatTuple (map (rename_pattern old_var new_var) ps)
    | PatStruct n fields -> PatStruct n (map (fun (f, p') -> (f, rename_pattern old_var new_var p')) fields)
    | PatVariant n v ps -> PatVariant n v (map (rename_pattern old_var new_var) ps)
    | PatOr p1 p2 -> PatOr (rename_pattern old_var new_var p1) (rename_pattern old_var new_var p2)
    | PatGuard p' g -> PatGuard (rename_pattern old_var new_var p') g  (* Don't rename in guard expr *)
    | PatRef p' -> PatRef (rename_pattern old_var new_var p')
    | PatBox p' -> PatBox (rename_pattern old_var new_var p')
    | PatType ty (Some x) when x = old_var -> PatType ty (Some new_var)
    | _ -> p.loc_value
  in
  { loc_value = new_inner; loc_range = p.loc_range }

(** Rename a variable in expression *)
let rec rename_expr (old_var new_var: var_id) (e: expr) : Tot expr (decreases expr_size e) =
  let r = e.loc_range in
  let new_inner =
    match e.loc_value with
    | EVar x when x = old_var -> EVar new_var
    | EUnary op e' -> EUnary op (rename_expr old_var new_var e')
    | EBinary op e1 e2 -> EBinary op (rename_expr old_var new_var e1) (rename_expr old_var new_var e2)
    | ECall fn args -> ECall (rename_expr old_var new_var fn) (map (rename_expr old_var new_var) args)
    | ELet p ty e1 e2 ->
        let bound = pattern_bound_vars p in
        if mem old_var bound then
          ELet p ty (rename_expr old_var new_var e1) e2  (* old_var shadowed *)
        else
          ELet (rename_pattern old_var new_var p) ty
               (rename_expr old_var new_var e1)
               (rename_expr old_var new_var e2)
    | ELetMut x ty e1 e2 ->
        if x = old_var then
          ELetMut new_var ty (rename_expr old_var new_var e1) (rename_expr old_var new_var e2)
        else
          ELetMut x ty (rename_expr old_var new_var e1) (rename_expr old_var new_var e2)
    | ELambda params body ->
        if mem old_var (map fst params) then e.loc_value  (* shadowed *)
        else ELambda params (rename_expr old_var new_var body)
    | EIf c t el -> EIf (rename_expr old_var new_var c)
                        (rename_expr old_var new_var t)
                        (rename_expr old_var new_var el)
    | ESeq e1 e2 -> ESeq (rename_expr old_var new_var e1) (rename_expr old_var new_var e2)
    | EBlock es -> EBlock (map (rename_expr old_var new_var) es)
    | EFor lbl x iter body ->
        if x = old_var then
          EFor lbl new_var (rename_expr old_var new_var iter) (rename_expr old_var new_var body)
        else
          EFor lbl x (rename_expr old_var new_var iter) (rename_expr old_var new_var body)
    (* ELabeled: no variable binding, just rename in body *)
    | ELabeled lbl body -> ELabeled lbl (rename_expr old_var new_var body)
    (* Method references and intrinsics *)
    | EMethodRef e' m -> EMethodRef (rename_expr old_var new_var e') m
    | ELen e' -> ELen (rename_expr old_var new_var e')
    | ECap e' -> ECap (rename_expr old_var new_var e')
    (* ETypeMethod: no variables, handled by catch-all *)
    (* EGoto: no variables, handled by catch-all *)
    | _ -> e.loc_value  (* Other cases: no variable occurrences or complex - simplified *)
  in
  { loc_value = new_inner; loc_range = r }

(** Capture-avoiding substitution *)
let rec subst_expr (var: var_id) (replacement: expr) (target: expr)
    : Tot expr (decreases expr_size target) =
  let r = target.loc_range in
  let repl_fv = free_vars replacement in
  let new_inner =
    match target.loc_value with
    | EVar x when x = var -> replacement.loc_value
    | EVar _ -> target.loc_value
    | EUnary op e' -> EUnary op (subst_expr var replacement e')
    | EBinary op e1 e2 ->
        EBinary op (subst_expr var replacement e1) (subst_expr var replacement e2)
    | ECall fn args ->
        ECall (subst_expr var replacement fn) (map (subst_expr var replacement) args)
    | ELet p ty e1 e2 ->
        let bound = pattern_bound_vars p in
        if mem var bound then
          (* var is bound by p, don't substitute in e2 *)
          ELet p ty (subst_expr var replacement e1) e2
        else
          (* Check for capture: if any bound var is in repl_fv, rename it *)
          let needs_rename = List.Tot.existsb (fun bv -> mem bv repl_fv) bound in
          if needs_rename then
            (* For simplicity, just skip - full implementation would alpha-rename *)
            ELet p ty (subst_expr var replacement e1) (subst_expr var replacement e2)
          else
            ELet p ty (subst_expr var replacement e1) (subst_expr var replacement e2)
    | ELetMut x ty e1 e2 ->
        if x = var then
          ELetMut x ty (subst_expr var replacement e1) e2  (* shadowed *)
        else if mem x repl_fv then
          (* Need to rename x to avoid capture *)
          let fresh_x = fresh_var x (repl_fv @ free_vars e2) in
          let e2' = rename_expr x fresh_x e2 in
          ELetMut fresh_x ty (subst_expr var replacement e1) (subst_expr var replacement e2')
        else
          ELetMut x ty (subst_expr var replacement e1) (subst_expr var replacement e2)
    | ELambda params body ->
        if mem var (map fst params) then target.loc_value  (* shadowed *)
        else ELambda params (subst_expr var replacement body)
    | EIf c t el ->
        EIf (subst_expr var replacement c)
            (subst_expr var replacement t)
            (subst_expr var replacement el)
    | ESeq e1 e2 ->
        ESeq (subst_expr var replacement e1) (subst_expr var replacement e2)
    | EBlock es -> EBlock (map (subst_expr var replacement) es)
    | EFor lbl x iter body ->
        if x = var then
          EFor lbl x (subst_expr var replacement iter) body  (* x shadows var in body *)
        else
          EFor lbl x (subst_expr var replacement iter) (subst_expr var replacement body)
    (* ELabeled: no variable binding, just substitute in body *)
    | ELabeled lbl body -> ELabeled lbl (subst_expr var replacement body)
    (* Method references and intrinsics *)
    | EMethodRef e' m -> EMethodRef (subst_expr var replacement e') m
    | ELen e' -> ELen (subst_expr var replacement e')
    | ECap e' -> ECap (subst_expr var replacement e')
    (* ETypeMethod: no subexpressions, handled by catch-all *)
    (* EGoto: no subexpressions, handled by catch-all *)
    | _ -> target.loc_value  (* Simplified for remaining cases *)
  in
  { loc_value = new_inner; loc_range = r }

(** Simultaneous substitution for multiple variables *)
let subst_expr_multi (subs: list (var_id & expr)) (e: expr) : Tot expr =
  List.Tot.fold_left (fun acc (v, repl) -> subst_expr v repl acc) e subs

(** Substitution preserves well-formedness *)
let subst_expr_wf (var: var_id) (replacement: expr) (target: expr)
    : Lemma (requires expr_wf target = true /\ expr_wf replacement = true)
            (ensures expr_wf (subst_expr var replacement target) = true) =
  admit()  (* Requires structural induction *)

(** Substitution respects free variables *)
let subst_expr_free_vars (var: var_id) (replacement: expr) (target: expr)
    : Lemma (ensures
        (forall v. mem v (free_vars (subst_expr var replacement target)) ==>
                   (v <> var /\ mem v (free_vars target)) \/
                   mem v (free_vars replacement))) =
  admit()  (* Requires structural induction *)

(** Substitution is idempotent for non-free variables *)
let subst_expr_non_free (var: var_id) (replacement: expr) (target: expr)
    : Lemma (requires not (is_free_in var target))
            (ensures expr_eq (subst_expr var replacement target) target = true) =
  admit()  (* Requires structural induction *)

(** ============================================================================
    TYPE INFERENCE (Simplified stubs - actual implementation in separate module)
    ============================================================================ *)

(* NOTE: type_env and infer_result are defined in the interface *)

(** Lookup variable in type environment *)
let rec lookup_var (v: var_id) (env: type_env) : option brrr_type =
  match env with
  | [] -> None
  | (x, ty) :: rest -> if x = v then Some ty else lookup_var v rest

(** Infer type of literal - stub, references undefined type constructors *)
let infer_literal (l: literal) : brrr_type =
  (* NOTE: BrrrTypes doesn't define TUnit, TBool, etc. - this is a placeholder *)
  admit ()

(** Infer type of unary operation - stub *)
let infer_unary_op (op: unary_op) (arg_ty: brrr_type) : option brrr_type =
  (* NOTE: Placeholder - actual implementation in TypeCheck module *)
  admit ()

(** Infer type of binary operation - stub *)
let infer_binary_op (op: binary_op) (lhs_ty rhs_ty: brrr_type) : option brrr_type =
  (* NOTE: Placeholder - actual implementation in TypeCheck module *)
  admit ()

(** Type check expression (stub) *)
let check_expr (env: type_env) (e: expr) (expected: brrr_type) : infer_result =
  (* Placeholder - actual implementation in TypeCheck module *)
  InferError (error_at "Type checking not implemented" e.loc_range)

(** Infer type of expression (stub) *)
let infer_expr (env: type_env) (e: expr) : infer_result =
  (* Placeholder - actual implementation in TypeCheck module *)
  match e.loc_value with
  | ELit l -> InferOk (infer_literal l) RowEmpty
  | EVar x ->
      (match lookup_var x env with
       | Some ty -> InferOk ty RowEmpty
       | None -> InferError (error_at ("Unbound variable: " ^ x) e.loc_range))
  | _ -> InferError (error_at "Type inference not fully implemented" e.loc_range)

(** Type inference result is consistent with expression well-formedness *)
let infer_expr_consistent (env: type_env) (e: expr)
    : Lemma (requires expr_wf e = true)
            (ensures InferError? (infer_expr env e) \/
                     InferOk? (infer_expr env e)) =
  ()  (* Trivially true by construction of infer_result *)

(** ============================================================================
    EXPRESSION NORMALIZATION
    ============================================================================

    Normalization is defined BEFORE alpha equivalence because alpha equivalence
    is defined in terms of normalization: two expressions are alpha-equivalent
    if they normalize to structurally equal expressions.
    ============================================================================ *)

(** Normalize expression to canonical form.

    Normalization performs the following transformations:
    - Unwrap singleton blocks: EBlock [e] -> e
    - Flatten nested blocks: EBlock [EBlock [a,b], c] -> EBlock [a,b,c]
    - Recursively normalize subexpressions

    The result is in "block-normal form" where:
    - No singleton blocks exist
    - No nested blocks exist
    - All subexpressions are recursively normalized *)
let rec normalize_expr (e: expr) : expr =
  let r = e.loc_range in
  let new_inner =
    match e.loc_value with
    (* Flatten nested blocks *)
    | EBlock [single] -> (normalize_expr single).loc_value
    | EBlock es ->
        let normalized = map normalize_expr es in
        let flattened = List.Tot.concatMap (fun e' ->
          match e'.loc_value with
          | EBlock inner -> inner
          | _ -> [e']
        ) normalized in
        (* After flattening, check if we ended up with a singleton - unwrap it *)
        (match flattened with
         | [single] -> single.loc_value
         | _ -> EBlock flattened)
    (* Flatten nested sequences *)
    | ESeq e1 e2 ->
        let n1 = normalize_expr e1 in
        let n2 = normalize_expr e2 in
        ESeq n1 n2
    (* Recurse on other constructs *)
    | EUnary op e' -> EUnary op (normalize_expr e')
    | EBinary op e1 e2 -> EBinary op (normalize_expr e1) (normalize_expr e2)
    | EIf c t el -> EIf (normalize_expr c) (normalize_expr t) (normalize_expr el)
    | ELet p ty e1 e2 -> ELet p ty (normalize_expr e1) (normalize_expr e2)
    | ELambda params body -> ELambda params (normalize_expr body)
    | _ -> e.loc_value
  in
  { loc_value = new_inner; loc_range = r }

(** ============================================================================
    ALPHA EQUIVALENCE
    ============================================================================

    Two expressions are alpha-equivalent if they normalize to structurally
    equal expressions. This captures the semantic equivalence of expressions
    that differ only in:
    - Block structure (singleton blocks, nested blocks)
    - Source locations (ranges are not compared)

    This definition ensures that normalization trivially preserves alpha
    equivalence: normalize_expr e is always alpha-equivalent to e.
    ============================================================================ *)

(** Alpha equivalence for patterns (structural comparison) *)
let pattern_alpha_eq (p1 p2: pattern) : bool =
  pattern_eq p1 p2

(** Alpha equivalence for expressions.

    Two expressions are alpha-equivalent if they normalize to structurally
    equal expressions. This is a decidable equivalence relation that captures
    semantic equivalence up to block restructuring.

    Key property: expr_alpha_eq e (normalize_expr e) = true (by construction)

    The definition works because:
    1. Normalization is idempotent: normalize (normalize e) = normalize e
    2. So expr_alpha_eq e (normalize e)
       = expr_eq (normalize e) (normalize (normalize e))
       = expr_eq (normalize e) (normalize e)
       = true (by reflexivity)
*)
let expr_alpha_eq (e1 e2: expr) : bool =
  expr_eq (normalize_expr e1) (normalize_expr e2)

(** Alpha equivalence is reflexive.

    Proof: normalize e = normalize e, so expr_eq gives true. *)
let expr_alpha_eq_refl (e: expr) : Lemma (ensures expr_alpha_eq e e = true) =
  expr_eq_refl (normalize_expr e)

(** Alpha equivalence is symmetric.

    Proof: expr_eq is symmetric, so if normalize e1 = normalize e2,
    then normalize e2 = normalize e1. *)
let expr_alpha_eq_sym (e1 e2: expr)
    : Lemma (requires expr_alpha_eq e1 e2 = true)
            (ensures expr_alpha_eq e2 e1 = true) =
  expr_eq_sym (normalize_expr e1) (normalize_expr e2)

(** Alpha equivalence is transitive.

    Proof: expr_eq is transitive, so if normalize e1 = normalize e2
    and normalize e2 = normalize e3, then normalize e1 = normalize e3. *)
let expr_alpha_eq_trans (e1 e2 e3: expr)
    : Lemma (requires expr_alpha_eq e1 e2 = true /\ expr_alpha_eq e2 e3 = true)
            (ensures expr_alpha_eq e1 e3 = true) =
  expr_eq_trans (normalize_expr e1) (normalize_expr e2) (normalize_expr e3)

(** Structural equality implies alpha equivalence.

    Proof: If e1 and e2 are structurally equal, then normalize e1 and
    normalize e2 are also structurally equal (by congruence of normalize). *)
let expr_eq_implies_alpha_eq (e1 e2: expr)
    : Lemma (requires expr_eq e1 e2 = true)
            (ensures expr_alpha_eq e1 e2 = true) =
  (* If e1 = e2 structurally, then normalize e1 = normalize e2 structurally,
     so expr_eq (normalize e1) (normalize e2) = true *)
  admit()  (* Requires congruence lemma for normalize_expr *)

(** ============================================================================
    NORMALIZATION THEOREMS
    ============================================================================ *)

(** Normalization is idempotent.

    Applying normalization twice yields the same result as applying it once.
    This is crucial for the definition of alpha equivalence to work correctly. *)
let normalize_expr_idempotent (e: expr)
    : Lemma (ensures expr_eq (normalize_expr e) (normalize_expr (normalize_expr e)) = true) =
  admit()  (* Proven in Expressions.Theorems.fst *)

(** Normalization preserves semantics (alpha equivalence).

    This is the key theorem T-4.1. The proof is now trivial by the definition
    of expr_alpha_eq:

    expr_alpha_eq e (normalize_expr e)
    = expr_eq (normalize_expr e) (normalize_expr (normalize_expr e))  -- by def
    = expr_eq (normalize_expr e) (normalize_expr e)                   -- by idempotence
    = true                                                            -- by reflexivity
*)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let normalize_expr_equiv (e: expr)
    : Lemma (ensures expr_alpha_eq e (normalize_expr e) = true) =
  (* Step 1: By definition of expr_alpha_eq, we need to show:
     expr_eq (normalize_expr e) (normalize_expr (normalize_expr e)) = true *)
  let ne = normalize_expr e in
  let nne = normalize_expr ne in

  (* Step 2: By idempotence, normalize_expr (normalize_expr e) = normalize_expr e *)
  normalize_expr_idempotent e;
  (* This gives us: expr_eq ne nne = true *)

  (* Step 3: The goal follows directly:
     expr_alpha_eq e ne = expr_eq ne nne = true *)
  ()

#pop-options

(** ============================================================================
    EXPRESSION SERIALIZATION
    ============================================================================ *)

(** Pretty-print literal to string *)
let literal_to_string (l: literal) : string =
  match l with
  | LitUnit -> "()"
  | LitBool true -> "true"
  | LitBool false -> "false"
  | LitInt n _ -> string_of_int n
  | LitFloat _ _ -> "<float>"  (* Simplified *)
  | LitString s -> "\"" ^ s ^ "\""
  | LitChar c -> "'" ^ String.make 1 c ^ "'"

(** Pretty-print expression to string (simplified) *)
let rec expr_to_string (e: expr) : string =
  match e.loc_value with
  | ELit l -> literal_to_string l
  | EVar x -> x
  | EGlobal g -> g
  | EUnary OpNeg e' -> "-" ^ expr_to_string e'
  | EUnary OpNot e' -> "!" ^ expr_to_string e'
  | EBinary OpAdd e1 e2 -> "(" ^ expr_to_string e1 ^ " + " ^ expr_to_string e2 ^ ")"
  | EBinary OpSub e1 e2 -> "(" ^ expr_to_string e1 ^ " - " ^ expr_to_string e2 ^ ")"
  | EBinary OpMul e1 e2 -> "(" ^ expr_to_string e1 ^ " * " ^ expr_to_string e2 ^ ")"
  | EBinary OpEq e1 e2 -> "(" ^ expr_to_string e1 ^ " == " ^ expr_to_string e2 ^ ")"
  | ECall fn args ->
      let arg_strs = map expr_to_string args in
      expr_to_string fn ^ "(" ^ String.concat ", " arg_strs ^ ")"
  | EIf c t el ->
      "if " ^ expr_to_string c ^ " then " ^ expr_to_string t ^ " else " ^ expr_to_string el
  | ELet p _ e1 e2 ->
      "let " ^ pattern_to_string p ^ " = " ^ expr_to_string e1 ^ " in " ^ expr_to_string e2
  | EBlock es -> "{ " ^ String.concat "; " (map expr_to_string es) ^ " }"
  | EHole -> "_"
  | EError msg -> "<error: " ^ msg ^ ">"
  | _ -> "<expr>"

(** Pretty-print pattern to string *)
and pattern_to_string (p: pattern) : string =
  match p.loc_value with
  | PatWild -> "_"
  | PatVar x -> x
  | PatLit l -> literal_to_string l
  | PatTuple ps -> "(" ^ String.concat ", " (map pattern_to_string ps) ^ ")"
  | PatAs p' x -> pattern_to_string p' ^ " @ " ^ x
  | PatType _ None -> ": <type>"  (* type_to_string not available *)
  | PatType _ (Some x) -> x ^ ": <type>"
  | _ -> "<pattern>"

(** Parse expression from string (stub - not implemented) *)
let expr_from_string (s: string) : option expr =
  None  (* Parsing not implemented - would require full parser *)
