(**
 * BrrrLang.Core.Expressions - Interface
 *
 * Expression AST for Brrr-Lang IR with source location tracking.
 * Based on brrr_lang_spec_v0.4.tex Part V.
 *
 * Following the EverParse with_meta_t pattern (EverParse/Ast.fst lines 107-111),
 * all AST nodes carry source location information for:
 * - Precise error messages with file:line:col
 * - IDE integration (go-to-definition, hover info)
 * - Debugging and profiling
 *
 * Type hierarchy:
 * - pattern' is the underlying pattern structure
 * - pattern = with_loc pattern' carries source location
 * - expr' is the underlying expression structure
 * - expr = with_loc expr' carries source location
 *
 * Reference patterns:
 * - EverParse Ast.fst: with_meta_t, range/pos, expr/expr' separation
 * - EverParse Binding.fst: check_expr pattern with environment threading
 * - HACL* Lib.Buffer.fsti: complex pre/post conditions with SMTPat
 *
 * Depends on: Primitives, Modes, Effects, Types
 *)
module Expressions

(** Z3 solver options - conservative settings for expression proofs.
    Following HACL* pattern of --fuel 0 --ifuel 0 as baseline. *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open FStar.List.Tot

(** ============================================================================
    SOURCE LOCATION TRACKING
    ============================================================================

    Following EverParse Ast.fst pattern (lines 34-111):
    - pos: Source position (file, line, column)
    - range: Span from start to end position
    - with_loc: Generic wrapper attaching location to any value
    ============================================================================ *)

(** Source position: file, line, column *)
type pos = {
  pos_filename : string;
  pos_line     : nat;
  pos_col      : nat
}

(** Dummy position for synthetic nodes *)
val dummy_pos : pos

(** Format position as string for error messages *)
val string_of_pos : pos -> string

(** Source range: span from start to end *)
type range = pos & pos

(** Dummy range for synthetic nodes *)
val dummy_range : range

(** Format range as string *)
val string_of_range : range -> string

(** Merge two ranges into a range spanning both.
    Returns the smallest range containing both input ranges.
    If ranges are from different files, returns the first range. *)
val merge_ranges : range -> range -> range

(** Wrapper type that attaches source location to any value.
    Following EverParse's with_meta_t pattern. *)
noeq type with_loc 'a = {
  loc_value : 'a;
  loc_range : range
}

(** Create a located value *)
val locate : #a:Type -> a -> range -> with_loc a

(** Create a located value at dummy location *)
val locate_dummy : #a:Type -> a -> with_loc a

(** Extract value from location wrapper *)
val unloc : #a:Type -> with_loc a -> a

(** Extract range from location wrapper *)
val loc_of : #a:Type -> with_loc a -> range

(** Map function over located value *)
val map_loc : #a:Type -> #b:Type -> (a -> b) -> with_loc a -> with_loc b

(** Located error with message and source range *)
noeq type located_error = {
  err_message : string;
  err_range   : range
}

(** Create located error *)
val error_at : string -> range -> located_error

(** Format error for display *)
val string_of_error : located_error -> string

(** ============================================================================
    RANGE PREDICATES AND LEMMAS
    ============================================================================ *)

(** Check if a position is within a range (inclusive) *)
val pos_within : pos -> range -> bool

(** Check if one range is entirely within another *)
val range_within : inner:range -> outer:range -> bool

(** Check if two ranges overlap *)
val ranges_overlap : range -> range -> bool

(** Check if a position equals another *)
val pos_eq : pos -> pos -> bool

(** Check if two ranges are equal *)
val range_eq : range -> range -> bool

(** Range equality is reflexive *)
val range_eq_refl : r:range ->
  Lemma (ensures range_eq r r = true)
  [SMTPat (range_eq r r)]

(** Range equality is symmetric *)
val range_eq_sym : r1:range -> r2:range ->
  Lemma (requires range_eq r1 r2 = true)
        (ensures range_eq r2 r1 = true)

(** Range equality is transitive *)
val range_eq_trans : r1:range -> r2:range -> r3:range ->
  Lemma (requires range_eq r1 r2 = true /\ range_eq r2 r3 = true)
        (ensures range_eq r1 r3 = true)

(** merge_ranges preserves containment *)
val merge_ranges_contains_left : r1:range -> r2:range ->
  Lemma (ensures range_within r1 (merge_ranges r1 r2) = true)
  [SMTPat (merge_ranges r1 r2)]

val merge_ranges_contains_right : r1:range -> r2:range ->
  Lemma (ensures range_within r2 (merge_ranges r1 r2) = true)

(** ============================================================================
    NODE IDENTIFIERS
    ============================================================================ *)

(** Unique node ID in the IR *)
type node_id = nat

(** Variable identifier *)
type var_id = string

(** Label for control flow *)
type label = string

(** ============================================================================
    LITERAL VALUES
    ============================================================================ *)

(** Literal expressions *)
noeq type literal =
  | LitUnit   : literal
  | LitBool   : bool -> literal
  | LitInt    : int -> int_type -> literal
  | LitFloat  : float_repr -> float_prec -> literal
  | LitString : string -> literal
  | LitChar   : FStar.Char.char -> literal

(** ============================================================================
    OPERATORS
    ============================================================================ *)

(** Unary operators *)
type unary_op =
  | OpNeg    : unary_op
  | OpNot    : unary_op
  | OpBitNot : unary_op
  | OpDeref  : unary_op
  | OpRef    : unary_op
  | OpRefMut : unary_op

(** Binary operators *)
type binary_op =
  | OpAdd : binary_op
  | OpSub : binary_op
  | OpMul : binary_op
  | OpDiv : binary_op
  | OpMod : binary_op
  | OpEq  : binary_op
  | OpNe  : binary_op
  | OpLt  : binary_op
  | OpLe  : binary_op
  | OpGt  : binary_op
  | OpGe  : binary_op
  | OpAnd : binary_op
  | OpOr  : binary_op
  | OpBitAnd : binary_op
  | OpBitOr  : binary_op
  | OpBitXor : binary_op
  | OpShl    : binary_op
  | OpShr    : binary_op

(** ============================================================================
    PATTERNS AND EXPRESSIONS (mutually recursive with source location)
    ============================================================================

    Following EverParse Ast.fst pattern (lines 300-309):
    - expr' is the underlying expression structure (ADT)
    - expr = with_loc expr' carries source location
    ============================================================================ *)

(** Pattern underlying type *)
noeq type pattern' =
  | PatWild    : pattern'
  | PatVar     : var_id -> pattern'
  | PatLit     : literal -> pattern'
  | PatTuple   : list pattern -> pattern'
  | PatStruct  : type_name -> list (string & pattern) -> pattern'
  | PatVariant : type_name -> string -> list pattern -> pattern'
  | PatOr      : pattern -> pattern -> pattern'
  | PatGuard   : pattern -> expr -> pattern'
  | PatRef     : pattern -> pattern'
  | PatBox     : pattern -> pattern'
  | PatRest    : option var_id -> pattern'
  | PatAs      : pattern -> var_id -> pattern'

(** Expression underlying type *)
and expr' =
  | ELit      : literal -> expr'
  | EVar      : var_id -> expr'
  | EGlobal   : string -> expr'
  | EUnary    : unary_op -> expr -> expr'
  | EBinary   : binary_op -> expr -> expr -> expr'
  | ECall     : expr -> list expr -> expr'
  | EMethodCall : expr -> string -> list expr -> expr'
  | ETuple    : list expr -> expr'
  | EArray    : list expr -> expr'
  | EStruct   : type_name -> list (string & expr) -> expr'
  | EVariant  : type_name -> string -> list expr -> expr'
  | EField    : expr -> string -> expr'
  | EIndex    : expr -> expr -> expr'
  | ETupleProj : expr -> nat -> expr'
  | EIf       : expr -> expr -> expr -> expr'
  | EMatch    : expr -> list match_arm -> expr'
  | ELoop     : option label -> expr -> expr'
  | EWhile    : option label -> expr -> expr -> expr'
  | EFor      : option label -> var_id -> expr -> expr -> expr'
  | EBreak    : option label -> option expr -> expr'
  | EContinue : option label -> expr'
  | EReturn   : option expr -> expr'
  | ELet      : pattern -> option brrr_type -> expr -> expr -> expr'
  | ELetMut   : var_id -> option brrr_type -> expr -> expr -> expr'
  | EAssign   : expr -> expr -> expr'
  | ELambda   : list (var_id & brrr_type) -> expr -> expr'
  | EClosure  : list (var_id & brrr_type) -> list var_id -> expr -> expr'
  | EBox      : expr -> expr'
  | EDeref    : expr -> expr'
  | EBorrow   : expr -> expr'
  | EBorrowMut : expr -> expr'
  | EMove     : expr -> expr'
  | EDrop     : expr -> expr'
  | EThrow    : expr -> expr'
  | ETry      : expr -> list catch_arm -> option expr -> expr'
  | EAwait    : expr -> expr'
  | EYield    : expr -> expr'
  | EHandle   : expr -> effect_handler -> expr'
  | EPerform  : effect_op -> list expr -> expr'
  | EAsync    : expr -> expr'
  | ESpawn    : expr -> expr'
  | EResume   : var_id -> expr -> expr'
  | EReset    : label -> expr -> expr'
  | EShift    : label -> var_id -> expr -> expr'
  | EAs       : expr -> brrr_type -> expr'
  | EIs       : expr -> brrr_type -> expr'
  | ESizeof   : brrr_type -> expr'
  | EAlignof  : brrr_type -> expr'
  | EBlock    : list expr -> expr'
  | ESeq      : expr -> expr -> expr'
  | EUnsafe   : expr -> expr'
  | EHole     : expr'
  | EError    : string -> expr'

(** Match arm with source location *)
and match_arm = {
  arm_range   : range;
  arm_pattern : pattern;
  arm_guard   : option expr;
  arm_body    : expr
}

(** Try-catch arm with source location *)
and catch_arm = {
  catch_range   : range;
  catch_pattern : pattern;
  catch_type    : brrr_type;
  catch_body    : expr
}

(** Pattern with source location - following EverParse pattern *)
and pattern = with_loc pattern'

(** Expression with source location - following EverParse pattern *)
and expr = with_loc expr'

(** ============================================================================
    ANNOTATED EXPRESSIONS (with additional metadata)
    ============================================================================ *)

(** Expression with full metadata (node ID, type, effects) *)
noeq type annotated_expr = {
  node    : node_id;
  span    : span;
  ty      : option brrr_type;
  effects : option effect_row;
  expr    : expr
}

(** Create annotated expression using the expression's range *)
val annotate : node_id -> span -> expr -> annotated_expr

(** Create annotated expression with type *)
val annotate_typed : node_id -> expr -> brrr_type -> annotated_expr

(** Create annotated expression with type and effects *)
val annotate_full : node_id -> expr -> brrr_type -> effect_row -> annotated_expr

(** ============================================================================
    EXPRESSION CONSTRUCTORS
    ============================================================================ *)

(** Create expression/pattern with range *)
val mk_expr : range -> expr' -> expr
val mk_expr_dummy : expr' -> expr
val mk_pat : range -> pattern' -> pattern
val mk_pat_dummy : pattern' -> pattern

(** Convenience constructors at dummy location *)
val e_unit : expr
val e_true : expr
val e_false : expr
val e_int : int -> expr
val e_i64 : int -> expr
val e_f64 : float_repr -> expr
val e_str : string -> expr
val e_var : var_id -> expr
val e_field : expr -> string -> expr
val e_call : expr -> list expr -> expr
val e_if : expr -> expr -> expr -> expr
val e_let : var_id -> expr -> expr -> expr
val e_lambda : list (var_id & brrr_type) -> expr -> expr
val e_block : list expr -> expr
val e_seq : expr -> expr -> expr

(** Constructors with explicit location *)
val e_unit_at : range -> expr
val e_true_at : range -> expr
val e_false_at : range -> expr
val e_int_at : range -> int -> expr
val e_var_at : range -> var_id -> expr
val e_field_at : range -> expr -> string -> expr
val e_call_at : range -> expr -> list expr -> expr
val e_if_at : range -> expr -> expr -> expr -> expr

(** Pattern constructors *)
val p_wild : pattern
val p_var : var_id -> pattern
val p_lit : literal -> pattern
val p_tuple : list pattern -> pattern
val p_wild_at : range -> pattern
val p_var_at : range -> var_id -> pattern

(** Match/catch arm constructors *)
val mk_arm : range -> pattern -> option expr -> expr -> match_arm
val mk_arm_simple : pattern -> expr -> match_arm
val mk_catch : range -> pattern -> brrr_type -> expr -> catch_arm

(** Extractors *)
val expr_inner : expr -> expr'
val expr_range : expr -> range
val pat_inner : pattern -> pattern'
val pat_range : pattern -> range

(** ============================================================================
    EXPRESSION SIZE FUNCTIONS (for termination proofs)
    ============================================================================ *)

(** Size of underlying expression *)
val expr'_size : expr' -> Tot nat

(** Size of an expression - always >= 1 *)
val expr_size : e:expr -> Tot nat

(** Size of expression list *)
val expr_list_size : list expr -> Tot nat

(** Size of field-expression list *)
val field_expr_list_size : list (string & expr) -> Tot nat

(** Size of optional expression *)
val option_expr_size : option expr -> Tot nat

(** Size of match arms *)
val match_arm_list_size : list match_arm -> Tot nat

(** Size of catch arms *)
val catch_arm_list_size : list catch_arm -> Tot nat

(** expr_size is always positive *)
val expr_size_pos : e:expr -> Lemma (ensures expr_size e >= 1)

(** ============================================================================
    SUBEXPRESSION RELATIONSHIP
    ============================================================================ *)

(** Check if e2 is an immediate subexpression of e1 *)
val is_immediate_subexpr : sub:expr -> parent:expr -> Tot bool

(** Check if e2 is a subexpression of e1 (transitive closure) *)
val is_subexpr : sub:expr -> parent:expr -> Tot bool (decreases expr_size parent)

(** Subexpression relation is reflexive *)
val is_subexpr_refl : e:expr ->
  Lemma (ensures is_subexpr e e = true)
  [SMTPat (is_subexpr e e)]

(** Subexpression relation is transitive *)
val is_subexpr_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires is_subexpr e1 e2 = true /\ is_subexpr e2 e3 = true)
        (ensures is_subexpr e1 e3 = true)

(** Subexpressions have smaller size *)
val subexpr_size_decreases : sub:expr -> parent:expr ->
  Lemma (requires is_immediate_subexpr sub parent = true)
        (ensures expr_size sub < expr_size parent)

(** ============================================================================
    RANGE PRESERVATION LEMMAS
    ============================================================================ *)

(** Subexpression ranges are within parent range (when properly constructed)
    Note: This is a semantic property that depends on correct AST construction.
    For synthetic expressions, this may not hold. *)
val subexpr_range_subset : parent:expr -> sub:expr ->
  Lemma (requires is_subexpr sub parent = true /\
                  parent.loc_range <> dummy_range /\
                  sub.loc_range <> dummy_range)
        (ensures range_within (expr_range sub) (expr_range parent) \/
                 sub.loc_range = parent.loc_range)

(** Match arm body range is within arm range *)
val match_arm_range_contains_body : arm:match_arm ->
  Lemma (requires arm.arm_range <> dummy_range /\
                  arm.arm_body.loc_range <> dummy_range)
        (ensures range_within (expr_range arm.arm_body) arm.arm_range \/
                 arm.arm_body.loc_range = arm.arm_range)

(** Catch arm body range is within catch range *)
val catch_arm_range_contains_body : arm:catch_arm ->
  Lemma (requires arm.catch_range <> dummy_range /\
                  arm.catch_body.loc_range <> dummy_range)
        (ensures range_within (expr_range arm.catch_body) arm.catch_range \/
                 arm.catch_body.loc_range = arm.catch_range)

(** ============================================================================
    EXPRESSION WELL-FORMEDNESS
    ============================================================================ *)

(** Well-formedness predicate for expressions.
    An expression is well-formed if:
    1. All variable references are valid identifiers
    2. Pattern bindings are consistent
    3. Type annotations (if present) are well-formed
    4. Control flow constructs are properly structured *)

(** Check if a variable identifier is valid (non-empty, no reserved prefix) *)
val is_valid_var_id : var_id -> bool

(** Check if pattern is well-formed (no duplicate bindings in tuples, etc.) *)
val pattern_wf : pattern -> Tot bool

(** Check if expression is well-formed (structural validity) *)
val expr_wf : e:expr -> Tot bool (decreases expr_size e)

(** Check if match arms are exhaustive (requires external type info) *)
val match_arms_wf : list match_arm -> bool

(** Collect all bound variables in a pattern *)
val pattern_bound_vars : pattern -> Tot (list var_id)

(** Check for duplicate bindings in pattern *)
val pattern_has_duplicate_bindings : pattern -> bool

(** Well-formed patterns have no duplicate bindings *)
val pattern_wf_no_duplicates : p:pattern ->
  Lemma (requires pattern_wf p = true)
        (ensures pattern_has_duplicate_bindings p = false)

(** ============================================================================
    EXPRESSION TRAVERSAL
    ============================================================================ *)

(** Map over immediate sub-expressions (preserves location) *)
val map_expr : (expr -> expr) -> expr -> expr

(** Fold over expression tree *)
val fold_expr : #a:Type -> (a -> expr -> a) -> a -> expr -> Tot a

(** Collect all nodes in expression tree *)
val collect_nodes : expr -> Tot (list expr)

(** Count nodes in expression tree *)
val count_nodes : expr -> Tot nat

(** ============================================================================
    FREE VARIABLES
    ============================================================================ *)

(** Extract bound variable from pattern if it's a simple PatVar *)
val pattern_var : pattern -> option var_id

(** Collect free variables in expression *)
val free_vars : expr -> Tot (list var_id)

(** Check if variable is free in expression *)
val is_free_in : var_id -> expr -> Tot bool

(** Free variables of subexpression are subset of parent free variables
    (modulo bindings in between) *)
val free_vars_subexpr : sub:expr -> parent:expr ->
  Lemma (requires is_immediate_subexpr sub parent = true)
        (ensures forall v. mem v (free_vars sub) ==>
                          mem v (free_vars parent) \/
                          (exists p. ELet? parent.loc_value /\ Some? (pattern_var p)))

(** ============================================================================
    EXPRESSION EQUALITY
    ============================================================================ *)

(** Literal equality *)
val literal_eq : literal -> literal -> bool

(** Operator equality *)
val unary_op_eq : unary_op -> unary_op -> bool
val binary_op_eq : binary_op -> binary_op -> bool

(** Pattern equality (ignores location, compares structure) *)
val pattern_eq : pattern -> pattern -> Tot bool

(** Expression structural equality (ignores location, compares structure) *)
val expr_eq : e1:expr -> e2:expr -> Tot bool

(** ============================================================================
    EQUALITY LEMMAS
    ============================================================================ *)

(** expr_eq is reflexive *)
val expr_eq_refl : e:expr ->
  Lemma (ensures expr_eq e e = true)

(** expr_eq is symmetric *)
val expr_eq_sym : e1:expr -> e2:expr ->
  Lemma (requires expr_eq e1 e2 = true)
        (ensures expr_eq e2 e1 = true)

(** expr_eq is transitive *)
val expr_eq_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires expr_eq e1 e2 = true /\ expr_eq e2 e3 = true)
        (ensures expr_eq e1 e3 = true)

(** pattern_eq is reflexive *)
val pattern_eq_refl : p:pattern ->
  Lemma (ensures pattern_eq p p = true)

(** pattern_eq is symmetric *)
val pattern_eq_sym : p1:pattern -> p2:pattern ->
  Lemma (requires pattern_eq p1 p2 = true)
        (ensures pattern_eq p2 p1 = true)

(** pattern_eq is transitive *)
val pattern_eq_trans : p1:pattern -> p2:pattern -> p3:pattern ->
  Lemma (requires pattern_eq p1 p2 = true /\ pattern_eq p2 p3 = true)
        (ensures pattern_eq p1 p3 = true)

(** ============================================================================
    EXPRESSION SUBSTITUTION (Capture-Avoiding)
    ============================================================================

    Substitution of expressions, following the standard capture-avoiding
    substitution algorithm. Bound variables are renamed if necessary to
    avoid capture.
    ============================================================================ *)

(** Generate a fresh variable name not in the given set *)
val fresh_var : var_id -> list var_id -> var_id

(** fresh_var produces a variable not in the input list *)
val fresh_var_spec : base:var_id -> avoid:list var_id ->
  Lemma (ensures not (mem (fresh_var base avoid) avoid))

(** Rename a variable in pattern *)
val rename_pattern : old_var:var_id -> new_var:var_id -> pattern -> pattern

(** Rename a variable in expression *)
val rename_expr : old_var:var_id -> new_var:var_id -> e:expr ->
  Tot expr (decreases expr_size e)

(** Capture-avoiding substitution: replace var with replacement in target.
    If the replacement expression contains free variables that would be
    captured by bindings in target, those bindings are alpha-renamed first. *)
val subst_expr : var:var_id -> replacement:expr -> target:expr ->
  Tot expr (decreases expr_size target)

(** Simultaneous substitution for multiple variables *)
val subst_expr_multi : list (var_id & expr) -> expr ->
  Tot expr

(** Substitution preserves well-formedness *)
val subst_expr_wf : var:var_id -> replacement:expr -> target:expr ->
  Lemma (requires expr_wf target = true /\ expr_wf replacement = true)
        (ensures expr_wf (subst_expr var replacement target) = true)

(** Substitution respects free variables *)
val subst_expr_free_vars : var:var_id -> replacement:expr -> target:expr ->
  Lemma (ensures
    (forall v. mem v (free_vars (subst_expr var replacement target)) ==>
               (v <> var /\ mem v (free_vars target)) \/
               mem v (free_vars replacement)))

(** Substitution is idempotent for non-free variables *)
val subst_expr_non_free : var:var_id -> replacement:expr -> target:expr ->
  Lemma (requires not (is_free_in var target))
        (ensures expr_eq (subst_expr var replacement target) target = true)

(** ============================================================================
    TYPE INFERENCE SIGNATURES
    ============================================================================

    Type inference for expressions. These signatures define the interface
    for the type checker. The actual implementation is in a separate module.
    ============================================================================ *)

(** Type environment: maps variable names to their types *)
type type_env = list (var_id & brrr_type)

(** Type inference result: either a type with effects, or an error *)
noeq type infer_result =
  | InferOk     : ty:brrr_type -> eff:effect_row -> infer_result
  | InferError  : err:located_error -> infer_result

(** Lookup variable in type environment *)
val lookup_var : var_id -> type_env -> option brrr_type

(** Infer type of literal *)
val infer_literal : literal -> brrr_type

(** Infer type of unary operation *)
val infer_unary_op : unary_op -> brrr_type -> option brrr_type

(** Infer type of binary operation *)
val infer_binary_op : binary_op -> brrr_type -> brrr_type -> option brrr_type

(** Type check expression against expected type *)
val check_expr : type_env -> expr -> brrr_type -> infer_result

(** Infer type of expression (bidirectional type inference) *)
val infer_expr : type_env -> expr -> infer_result

(** Type inference result is consistent with expression well-formedness *)
val infer_expr_consistent : env:type_env -> e:expr ->
  Lemma (requires expr_wf e = true)
        (ensures InferError? (infer_expr env e) \/
                 InferOk? (infer_expr env e))

(** ============================================================================
    ALPHA EQUIVALENCE
    ============================================================================

    Two expressions are alpha-equivalent if they are equal up to renaming
    of bound variables. This is a weaker notion than expr_eq which requires
    exact match of variable names.
    ============================================================================ *)

(** Alpha equivalence for patterns *)
val pattern_alpha_eq : pattern -> pattern -> bool

(** Alpha equivalence for expressions *)
val expr_alpha_eq : expr -> expr -> bool

(** Alpha equivalence is an equivalence relation *)
val expr_alpha_eq_refl : e:expr ->
  Lemma (ensures expr_alpha_eq e e = true)

val expr_alpha_eq_sym : e1:expr -> e2:expr ->
  Lemma (requires expr_alpha_eq e1 e2 = true)
        (ensures expr_alpha_eq e2 e1 = true)

val expr_alpha_eq_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires expr_alpha_eq e1 e2 = true /\ expr_alpha_eq e2 e3 = true)
        (ensures expr_alpha_eq e1 e3 = true)

(** Structural equality implies alpha equivalence *)
val expr_eq_implies_alpha_eq : e1:expr -> e2:expr ->
  Lemma (requires expr_eq e1 e2 = true)
        (ensures expr_alpha_eq e1 e2 = true)

(** ============================================================================
    EXPRESSION NORMALIZATION
    ============================================================================ *)

(** Normalize expression to a canonical form:
    - Flatten nested blocks
    - Simplify constant operations where possible
    - Canonicalize associative operations *)
val normalize_expr : expr -> expr

(** Normalization preserves semantics (alpha equivalence) *)
val normalize_expr_equiv : e:expr ->
  Lemma (ensures expr_alpha_eq e (normalize_expr e) = true)

(** Normalization is idempotent *)
val normalize_expr_idempotent : e:expr ->
  Lemma (ensures expr_eq (normalize_expr e) (normalize_expr (normalize_expr e)) = true)

(** ============================================================================
    EXPRESSION SERIALIZATION (for debugging/display)
    ============================================================================ *)

(** Pretty-print expression to string *)
val expr_to_string : expr -> string

(** Pretty-print pattern to string *)
val pattern_to_string : pattern -> string

(** Parse expression from string (may fail) *)
val expr_from_string : string -> option expr
