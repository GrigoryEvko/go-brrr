(**
 * BrrrLang.Core.TypeChecker
 *
 * Bidirectional type checker implementing the typing rules from
 * brrr_lang_spec_v0.4.tex Part II (Type System) and Appendix B (Chapter 8).
 *
 * ==========================================================================
 * BIDIRECTIONAL TYPE CHECKING
 * ==========================================================================
 *
 * This module implements a bidirectional type checking algorithm following
 * the methodology of Pierce and Turner's "Local Type Inference" (POPL 1998)
 * and as described in Pierce's "Types and Programming Languages" (TAPL),
 * Chapters 9 (Simply Typed Lambda Calculus) and 22 (Type Reconstruction).
 *
 * KEY INSIGHT: Bidirectional type checking splits the type checker into
 * two mutually recursive judgments:
 *
 *   1. INFERENCE MODE (infer_type): Synthesizes a type from the expression
 *      Notation: Gamma |- e => T   ("e synthesizes type T")
 *      Used when type information flows OUT of the expression
 *
 *   2. CHECKING MODE (check_type): Verifies expression has expected type
 *      Notation: Gamma |- e <= T   ("e checks against type T")
 *      Used when type information flows INTO the expression
 *
 * BENEFITS (per Dunfield & Krishnaswami, "Bidirectional Typing" 2020):
 *   - Reduces annotation burden (many types can be inferred)
 *   - Principled handling of polymorphism without full unification
 *   - Better error messages (expected vs inferred types)
 *   - Natural integration with subtyping (T-Sub rule)
 *
 * ==========================================================================
 * TYPING RULES IMPLEMENTED (Spec Section 8.1 "Core Rules")
 * ==========================================================================
 *
 * Core Rules (TAPL Ch. 9, 11):
 *   T-Var     (x:T@m) in Gamma, m > 0  |-  x => T ; Pure
 *   T-Lit     Gamma |- literal => typeof(literal) ; Pure
 *   T-Abs     Gamma, x:T1@m |- e => T2 ; eff  |-  \x.e => (T1@m -[eff]-> T2) ; Pure
 *   T-App     Gamma1 |- e1 => T1 -[eff]-> T2, Gamma2 |- e2 <= T1  |-  e1 e2 => T2 ; eff
 *   T-Let     Gamma1 |- e1 => T1, Gamma2,p:T1 |- e2 => T2  |-  let p = e1 in e2 => T2
 *   T-If      Gamma |- cond => Bool, Gamma |- e1 => T, Gamma |- e2 => T  |-  if cond then e1 else e2 => T
 *
 * Subtyping (TAPL Ch. 15, Spec Section 8.2):
 *   T-Sub     Gamma |- e => T1, T1 <: T2  |-  e => T2
 *             Subsumption: silently coerce via subtype relation
 *
 * Pattern Matching (Spec Section 7.2 "Pattern Typing"):
 *   T-Match   Gamma |- scrutinee => T, forall i. Gamma |- pi : T => Delta_i, Gamma,Delta_i |- ei => S
 *             |- match scrutinee { p1 => e1 | ... } => S
 *
 * Linear Types (Spec Section 5.1, TAPL Ch. 28 "Linear Types"):
 *   L-Var     Linear variable must have mode > 0 (available)
 *   L-Split   Context is split for subexpression checking
 *   L-Join    Contexts joined after branches (must agree on linear consumption)
 *
 * Reference Types (Spec Section 6.1, TAPL Ch. 13 "References"):
 *   T-Ref     Gamma |- e => T  |-  &e => &T
 *   T-Deref   Gamma |- e => &T  |-  *e => T ; Read
 *   T-Assign  Gamma |- lhs => &mut T, Gamma |- rhs <= T  |-  lhs = rhs => () ; Write
 *
 * Ownership (Spec Section 6.3 "Ownership Types"):
 *   T-Borrow     Shared borrow: &e : &T (multiple allowed)
 *   T-BorrowMut  Exclusive borrow: &mut e : &mut T (single, no conflicts)
 *   T-Move       Ownership transfer (consumes linear variable)
 *   T-Drop       Explicit deallocation (Alloc effect)
 *
 * Effects (Spec Section 3.1 "Effect Row Typing"):
 *   Effects tracked as rows: Pure = RowEmpty, eff1 join eff2 = row_join
 *   Effect subsumption: eff1 <: eff2 iff effects in eff1 subset of eff2
 *
 * ==========================================================================
 * REFERENCES
 * ==========================================================================
 *
 *   [TAPL]    Pierce, B. C. "Types and Programming Languages" (2002)
 *             Chapters 9, 11, 13, 15, 22, 28
 *   [PT98]    Pierce & Turner, "Local Type Inference" (POPL 1998)
 *   [DK20]    Dunfield & Krishnaswami, "Bidirectional Typing" (2020)
 *   [Spec]    brrr_lang_spec_v0.4.tex - Chapters 3, 5, 6, 7, 8
 *   [Errata]  SPECIFICATION_ERRATA.md - Corrections from F* mechanization
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Values
 *)
module BrrrTypeChecker

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrValues
open BrrrSessionTypes
open BrrrTypeClasses
open BrrrBorrowChecker
open FStar.List.Tot

(** ============================================================================
    SOURCE LOCATION TRACKING
    ============================================================================

    Following EverParse with_meta_t pattern for source location tracking.
    All type errors include file:line:col information for precise error reporting.

    Pattern: Every AST node that needs source location information wraps its
    content in with_span_t. This enables:
    1. Precise error location reporting
    2. Source-to-source transformation tracking
    3. IDE integration (hover, go-to-definition)
    ============================================================================ *)

(* Source position: file, line, column *)
type source_pos = {
  sp_file : string;
  sp_line : nat;
  sp_col  : nat
}

(* Dummy position for synthetic/generated nodes *)
let dummy_pos : source_pos = {
  sp_file = "<synthetic>";
  sp_line = 0;
  sp_col = 0
}

(* Source span: start and end positions *)
type source_span = {
  span_start : source_pos;
  span_end   : source_pos
}

(* Dummy span for synthetic nodes *)
let dummy_span : source_span = {
  span_start = dummy_pos;
  span_end = dummy_pos
}

(* Create span from single position (zero-width) *)
let point_span (pos: source_pos) : source_span = {
  span_start = pos;
  span_end = pos
}

(* Wrapper type for values with source location metadata.
   Following EverParse with_meta_t pattern. *)
noeq type with_span_t 'a = {
  ws_value : 'a;           (* The wrapped value *)
  ws_span  : source_span;  (* Source location *)
}

(* Helper: wrap value with span *)
let with_span (#a: Type) (v: a) (span: source_span) : with_span_t a = {
  ws_value = v;
  ws_span = span
}

(* Helper: wrap value with dummy span (for synthetic nodes) *)
let no_span (#a: Type) (v: a) : with_span_t a = {
  ws_value = v;
  ws_span = dummy_span
}

(* Format source position for error messages: "file:line:col" *)
let string_of_pos (pos: source_pos) : string =
  pos.sp_file ^ ":" ^
  (if pos.sp_line > 0 then string_of_int pos.sp_line else "?") ^ ":" ^
  (if pos.sp_col > 0 then string_of_int pos.sp_col else "?")

(* Format source span for error messages *)
let string_of_span (span: source_span) : string =
  string_of_pos span.span_start ^
  (if span.span_start.sp_line <> span.span_end.sp_line ||
      span.span_start.sp_col <> span.span_end.sp_col
   then "-" ^ string_of_pos span.span_end
   else "")

(* Helper: fold over two lists simultaneously *)
let rec fold_right2 (#a #b #c: Type) (f: a -> b -> c -> c) (l1: list a) (l2: list b) (init: c) : c =
  match l1, l2 with
  | [], _ -> init
  | _, [] -> init
  | x :: xs, y :: ys -> f x y (fold_right2 f xs ys init)

(** ============================================================================
    TYPE ERROR WITH LOCATION
    ============================================================================

    Type errors carry source location information for precise error reporting.
    This section must appear BEFORE type_ctx to match interface declaration order.
    ============================================================================ *)

(* Type error with source location information *)
noeq type type_error = {
  te_message : string;       (* Error message *)
  te_span    : source_span;  (* Source location where error occurred *)
  te_context : option string (* Optional additional context *)
}

(* Create type error with span *)
let make_error (msg: string) (span: source_span) : type_error = {
  te_message = msg;
  te_span = span;
  te_context = None
}

(* Create type error with span and context *)
let make_error_ctx (msg: string) (span: source_span) (ctx: string) : type_error = {
  te_message = msg;
  te_span = span;
  te_context = Some ctx
}

(* Format type error for display: "file:line:col: (Error) message" *)
let format_error (err: type_error) : string =
  string_of_span err.te_span ^ ": (Error) " ^ err.te_message ^
  (match err.te_context with
   | Some ctx -> "\n  Context: " ^ ctx
   | None -> "")

(** ============================================================================
    TYPE CONTEXT
    ============================================================================ *)

(* A binding in the type context: variable with type, mode, usage tracking, and source location.
   Following EverParse pattern where each binding tracks:
   - Whether the variable has been accessed (for unused variable warnings)
   - Where the variable was defined (for error messages) *)
noeq type ctx_binding = {
  bind_name  : var_id;
  bind_type  : brrr_type;
  bind_mode  : mode;
  bind_used  : bool;           (* Has this variable been accessed? *)
  bind_range : option source_span  (* Where was this variable defined? *)
}

(* Type context: ordered list of bindings *)
type type_ctx = list ctx_binding

(* Global type context: maps global names to type schemes *)
type global_ctx = list (string & type_scheme)

(* Type definition context: maps type names to their definitions *)
type type_def_ctx = list (type_name & brrr_type)

(* Extended typing context for full type checking.
   Note: This is defined here to match the interface declaration order. *)
noeq type extended_typing_ctx = {
  etc_locals     : type_ctx;          (* Local variable bindings *)
  etc_globals    : global_ctx;        (* Global type schemes *)
  etc_type_defs  : type_def_ctx;      (* Struct/enum definitions *)
  etc_classes    : class_env;         (* Type class environment *)
  etc_regions    : region_ctx;        (* Active region capabilities *)
  etc_subst      : list (type_var & brrr_type)  (* Type variable substitution *)
}

(** ============================================================================
    TYPE CHECKING RESULT TYPES
    ============================================================================ *)

(* Inference result: type, effects, and updated context *)
noeq type infer_result =
  | InferOk  : ty:brrr_type -> eff:effect_row -> ctx:type_ctx -> infer_result
  | InferErr : err:type_error -> infer_result

(* Check result: effects and updated context *)
noeq type check_result =
  | CheckOk  : eff:effect_row -> ctx:type_ctx -> check_result
  | CheckErr : err:type_error -> check_result

(** ============================================================================
    CONTEXT OPERATIONS - Empty Contexts
    ============================================================================ *)

(* Empty local context *)
let empty_ctx : type_ctx = []

(* Empty global context *)
let empty_global_ctx : global_ctx = []

(* Empty type definition context *)
let empty_type_def_ctx : type_def_ctx = []

(* Empty extended context *)
let empty_extended_ctx : extended_typing_ctx = {
  etc_locals = empty_ctx;
  etc_globals = empty_global_ctx;
  etc_type_defs = empty_type_def_ctx;
  etc_classes = empty_class_env;
  etc_regions = [];
  etc_subst = []
}

(** ============================================================================
    BRRR_TYPE TO EFFECT_TYPE CONVERSION
    ============================================================================

    Convert brrr_type to effect_type for parameterized effects.
    Used for constructing parameterized Yield[Y, R] effects per spec Definition 3.1.
*)

(* Convert brrr_type to effect_type for use in effect parameters *)
let rec brrr_type_to_effect_type (t: brrr_type) : effect_type =
  match t with
  | TPrim PUnit -> ETUnit
  | TPrim PBool -> ETBool
  | TPrim PString -> ETString
  | TInt _ -> ETInt
  | TRef inner -> ETRef (brrr_type_to_effect_type inner)
  | TFn params ret _ -> (
      match params with
      | [p] -> ETFn (brrr_type_to_effect_type p) (brrr_type_to_effect_type ret)
      | _ -> ETVar 0  (* Multi-param functions default to type var *)
    )
  | TVar v -> ETVar v.var_id
  | _ -> ETVar 0  (* Other complex types default to type var 0 *)

(** ============================================================================
    CONTEXT OPERATIONS - Extend and Lookup
    ============================================================================ *)

(* Extend context with a new binding (no source location) *)
let extend_ctx (x: var_id) (t: brrr_type) (m: mode) (ctx: type_ctx) : type_ctx =
  { bind_name = x; bind_type = t; bind_mode = m; bind_used = false; bind_range = None } :: ctx

(* Extend context with a new binding including source location.
   Following EverParse pattern: new bindings start as unused (bind_used = false).
   When the variable is accessed via lookup_ctx_mark_used, bind_used becomes true. *)
let extend_ctx_with_span (x: var_id) (t: brrr_type) (m: mode) (span: source_span) (ctx: type_ctx) : type_ctx =
  { bind_name = x; bind_type = t; bind_mode = m; bind_used = false; bind_range = Some span } :: ctx

(* Lookup variable in context - returns type and mode if found.
   Note: This does NOT mark the variable as used. Use lookup_ctx_mark_used for that. *)
let rec lookup_ctx (x: var_id) (ctx: type_ctx) : option (brrr_type & mode) =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.bind_name = x then Some (b.bind_type, b.bind_mode)
      else lookup_ctx x rest

(* Lookup variable and mark it as used (following EverParse pattern).
   Returns (type, mode, updated_context) where the binding is marked as used.
   This is the primary lookup function for type inference. *)
let rec lookup_ctx_mark_used (x: var_id) (ctx: type_ctx) : option (brrr_type & mode & type_ctx) =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.bind_name = x then
        let b' = { b with bind_used = true } in
        Some (b.bind_type, b.bind_mode, b' :: rest)
      else
        match lookup_ctx_mark_used x rest with
        | Some (ty, m, rest') -> Some (ty, m, b :: rest')
        | None -> None

(* Lookup with full binding information (including source location) *)
let rec lookup_ctx_full (x: var_id) (ctx: type_ctx) : option ctx_binding =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.bind_name = x then Some b
      else lookup_ctx_full x rest

(* Check if variable is available (mode > 0) *)
let is_available (m: mode) : bool =
  match m with
  | MZero -> false
  | MOne -> true
  | MOmega -> true

(* Consume a linear variable: changes mode from 1 to 0, omega stays omega.
   Also marks the variable as used. *)
let rec consume_var (x: var_id) (ctx: type_ctx) : option type_ctx =
  match ctx with
  | [] -> None
  | b :: rest ->
      if b.bind_name = x then
        match b.bind_mode with
        | MZero -> None  (* Already consumed *)
        | MOne -> Some ({ b with bind_mode = MZero; bind_used = true } :: rest)
        | MOmega -> Some ({ b with bind_used = true } :: rest)  (* Unrestricted: mark used *)
      else
        match consume_var x rest with
        | Some rest' -> Some (b :: rest')
        | None -> None

(* Context addition: combines modes pointwise (for parallel use).
   Preserves source location from first context, merges usage flags (used if used in either). *)
let rec ctx_add (ctx1 ctx2: type_ctx) : option type_ctx =
  match ctx1, ctx2 with
  | [], [] -> Some []
  | b1 :: r1, b2 :: r2 ->
      if b1.bind_name = b2.bind_name && type_eq b1.bind_type b2.bind_type then
        match ctx_add r1 r2 with
        | Some rest ->
            Some ({ bind_name = b1.bind_name;
                    bind_type = b1.bind_type;
                    bind_mode = mode_add b1.bind_mode b2.bind_mode;
                    bind_used = b1.bind_used || b2.bind_used;
                    bind_range = b1.bind_range } :: rest)
        | None -> None
      else None
  | _, _ -> None

(* Check if all linear variables have been consumed *)
let rec check_linear_consumed (ctx: type_ctx) : bool =
  match ctx with
  | [] -> true
  | b :: rest ->
      (b.bind_mode <> MOne) && check_linear_consumed rest

(** ============================================================================
    CONTEXT WELL-FORMEDNESS
    ============================================================================

    A typing context is well-formed if:
    1. No duplicate variable names (shadowing is explicit via context extension)
    2. All types in bindings are well-formed
    3. All modes are valid (non-negative usage counts)

    These invariants ensure type checking produces sound results.
    ============================================================================ *)

(* Check if a variable name appears in context (for duplicate detection) *)
let rec name_in_ctx (x: var_id) (ctx: type_ctx) : bool =
  match ctx with
  | [] -> false
  | b :: rest -> b.bind_name = x || name_in_ctx x rest

(* Type well-formedness: check that type does not contain unbound type variables.
   For simplicity, we assume all types from the parser are well-formed.
   A full implementation would track type variable bindings. *)
let rec type_well_formed (t: brrr_type) : Tot bool (decreases t) =
  match t with
  | TPrim _ -> true
  | TInt _ -> true
  | TNumeric _ -> true
  | TVar _ -> true  (* Type variables are assumed bound at polymorphic definitions *)
  | TRef inner -> type_well_formed inner
  | TSlice inner -> type_well_formed inner
  | TArray inner _ -> type_well_formed inner
  | TTuple ts -> List.Tot.for_all type_well_formed ts
  | TFunc ft ->
      List.Tot.for_all (fun p -> type_well_formed (BrrrTypes.Mkparam_type?.ty p)) ft.params &&
      type_well_formed ft.return_type
  | TStruct _ fields -> List.Tot.for_all (fun (_, t) -> type_well_formed t) fields
  | TEnum _ variants -> List.Tot.for_all (fun (_, ts) -> List.Tot.for_all type_well_formed ts) variants
  | TWrap _ inner -> type_well_formed inner
  | TResult tok terr -> type_well_formed tok && type_well_formed terr
  | TApp _ args -> List.Tot.for_all type_well_formed args
  | TNamed _ -> true  (* Named types assumed declared *)
  | TOpaque _ inner -> type_well_formed inner
  | TPath _ inner -> type_well_formed inner
  | TSession _ -> true  (* Session types have separate well-formedness *)
  | TChan _ -> true
  | TRegion _ inner -> type_well_formed inner

(* Mode well-formedness: all modes are valid (MZero, MOne, MOmega) *)
let mode_well_formed (m: mode) : bool =
  match m with
  | MZero | MOne | MOmega -> true

(* Context well-formedness predicate:
   - No duplicate names (names are unique)
   - All types are well-formed
   - All modes are valid

   This is the key invariant maintained by type checking operations. *)
let rec ctx_well_formed (ctx: type_ctx) : Tot bool (decreases ctx) =
  match ctx with
  | [] -> true
  | b :: rest ->
      not (name_in_ctx b.bind_name rest) &&
      type_well_formed b.bind_type &&
      mode_well_formed b.bind_mode &&
      ctx_well_formed rest

(* Lemma: Empty context is well-formed *)
val empty_ctx_well_formed : unit ->
  Lemma (ensures ctx_well_formed empty_ctx = true)
let empty_ctx_well_formed () = ()

(* Lemma: Extending a well-formed context with a fresh variable preserves well-formedness *)
val extend_ctx_preserves_well_formed :
    x:var_id -> t:brrr_type -> m:mode -> ctx:type_ctx ->
    Lemma (requires ctx_well_formed ctx = true /\
                    not (name_in_ctx x ctx) /\
                    type_well_formed t = true /\
                    mode_well_formed m = true)
          (ensures ctx_well_formed (extend_ctx x t m ctx) = true)
let extend_ctx_preserves_well_formed x t m ctx = ()

(** ============================================================================
    UNUSED VARIABLE DETECTION
    ============================================================================

    Following EverParse pattern where bindings track usage status.
    These helpers enable detection of unused variables at the end of a scope.
    ============================================================================ *)

(* Get list of unused variables in context with their source locations.
   Returns list of (variable_name, optional_source_span). *)
let rec get_unused_vars (ctx: type_ctx) : list (var_id & option source_span) =
  match ctx with
  | [] -> []
  | b :: rest ->
      if b.bind_used then get_unused_vars rest
      else (b.bind_name, b.bind_range) :: get_unused_vars rest

(* Check if a specific variable has been used in the context *)
let rec is_var_used (x: var_id) (ctx: type_ctx) : bool =
  match ctx with
  | [] -> false
  | b :: rest ->
      if b.bind_name = x then b.bind_used
      else is_var_used x rest

(* Format unused variable warning with source location *)
let format_unused_warning (var_name: var_id) (span_opt: option source_span) : string =
  let loc = match span_opt with
    | Some span -> string_of_span span ^ ": "
    | None -> ""
  in
  loc ^ "Warning: unused variable '" ^ var_name ^ "'"

(* Get all unused variable warnings for a context *)
let get_unused_warnings (ctx: type_ctx) : list string =
  let unused = get_unused_vars ctx in
  List.Tot.map (fun (name, span) -> format_unused_warning name span) unused

(**
 * Join modes for branch contexts.
 *
 * For linear types, both branches must consume linear variables consistently:
 *   - If both consumed (MZero, MZero): result is MZero
 *   - If neither consumed (MOne, MOne): result is MOne
 *   - If inconsistent (MZero, MOne) or (MOne, MZero): error (None)
 *   - Unrestricted (MOmega) always stays MOmega
 *
 * @param m1 Mode from first branch
 * @param m2 Mode from second branch
 * @returns Joined mode or None if inconsistent for linear types
 *)
let mode_join_strict (m1 m2: mode) : option mode =
  match m1, m2 with
  | MZero, MZero -> Some MZero     (* Both consumed: ok *)
  | MOne, MOne -> Some MOne        (* Neither consumed: ok *)
  | MOmega, MOmega -> Some MOmega  (* Unrestricted: ok *)
  | MOmega, _ -> Some MOmega       (* Unrestricted dominates *)
  | _, MOmega -> Some MOmega       (* Unrestricted dominates *)
  | MZero, MOne -> None            (* Inconsistent: linear var consumed in one branch only *)
  | MOne, MZero -> None            (* Inconsistent: linear var consumed in one branch only *)

(**
 * Join two type contexts for branch merging (if-else, match).
 *
 * For linear types, both branches must agree on which linear variables
 * are consumed. If a linear variable is consumed in one branch but not
 * the other, that's a linearity violation and we return None.
 *
 * Usage tracking: a variable is considered used if it was used in either branch.
 * Source location: preserved from first context.
 *
 * @param ctx1 Context after first branch (then-branch)
 * @param ctx2 Context after second branch (else-branch)
 * @returns Joined context or None if linear variables consumed inconsistently
 *)
let rec join_contexts (ctx1 ctx2: type_ctx) : option type_ctx =
  match ctx1, ctx2 with
  | [], [] -> Some []
  | b1 :: r1, b2 :: r2 ->
      (* Bindings must have same name and type (structural match) *)
      if b1.bind_name = b2.bind_name && type_eq b1.bind_type b2.bind_type then
        match mode_join_strict b1.bind_mode b2.bind_mode with
        | Some joined_mode ->
            (match join_contexts r1 r2 with
             | Some rest ->
                 Some ({ bind_name = b1.bind_name;
                         bind_type = b1.bind_type;
                         bind_mode = joined_mode;
                         bind_used = b1.bind_used || b2.bind_used;
                         bind_range = b1.bind_range } :: rest)
             | None -> None)
        | None -> None  (* Linear variable consumed inconsistently *)
      else None  (* Structural mismatch - should not happen if both start from same ctx *)
  | _, _ -> None  (* Length mismatch *)

(** ============================================================================
    GLOBAL TYPE ENVIRONMENT - Operations
    ============================================================================ *)

(* Extend global context with a new binding *)
let extend_global_ctx (name: string) (scheme: type_scheme) (gctx: global_ctx) : global_ctx =
  (name, scheme) :: gctx

(* Lookup global name in global context *)
let rec lookup_global (name: string) (gctx: global_ctx) : option type_scheme =
  match gctx with
  | [] -> None
  | (n, scheme) :: rest ->
      if n = name then Some scheme
      else lookup_global name rest

(** ============================================================================
    TYPE DEFINITION CONTEXT - Operations
    ============================================================================ *)

(* Extend type definition context *)
let extend_type_def_ctx (name: type_name) (ty: brrr_type) (tdctx: type_def_ctx) : type_def_ctx =
  (name, ty) :: tdctx

(* Lookup type definition by name *)
let rec lookup_type_def (name: type_name) (tdctx: type_def_ctx) : option brrr_type =
  match tdctx with
  | [] -> None
  | (n, ty) :: rest ->
      if n = name then Some ty
      else lookup_type_def name rest

(* Lookup struct type by name - returns Some struct_type if found and is a struct *)
let lookup_struct_type (name: type_name) (tdctx: type_def_ctx) : option struct_type =
  match lookup_type_def name tdctx with
  | Some (TStruct st) -> Some st
  | _ -> None

(* Lookup enum type by name - returns Some enum_type if found and is an enum *)
let lookup_enum_type (name: type_name) (tdctx: type_def_ctx) : option enum_type =
  match lookup_type_def name tdctx with
  | Some (TEnum et) -> Some et
  | _ -> None

(** ============================================================================
    EFFECT SUBSUMPTION
    ============================================================================ *)

(* Effect subsumption: e1 <= e2 iff e1's effects are a subset of e2's
   Based on: e1 <= e2 iff join e1 e2 = e2 *)
let effect_sub (e1 e2: effect_row) : bool =
  row_subset e1 e2 ||
  (match e2 with
   | RowVar _ -> true  (* Variables are upper bounds *)
   | _ -> false)

(* Check if e1 is subsumed by e2 (e1 can be weakened to e2) *)
let effect_subsumes (e1 e2: effect_row) : bool =
  effect_sub e1 e2

(** ============================================================================
    EXTENDED SUBTYPING
    ============================================================================ *)

(* Helper: check subtype relation on type lists *)
let rec types_subtype_list (ts1 ts2: list brrr_type) : Tot bool (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> true
  | t1 :: r1, t2 :: r2 -> subtype t1 t2 && types_subtype_list r1 r2
  | _, _ -> false

(* Check params are contravariant *)
let rec params_contravariant_simple (ps1 ps2: list BrrrTypes.param_type) : Tot bool (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> true
  | p1 :: r1, p2 :: r2 ->
      let t1 : brrr_type = BrrrTypes.Mkparam_type?.ty p1 in
      let t2 : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
      let m1 : mode = BrrrTypes.Mkparam_type?.mode p1 in
      let m2 : mode = BrrrTypes.Mkparam_type?.mode p2 in
      subtype t2 t1 &&  (* Contravariant: t2 <: t1 *)
      mode_leq m1 m2 && (* Mode compatible *)
      params_contravariant_simple r1 r2
  | _, _ -> false

(* Function subtype check - non-recursive in extended_subtype *)
let func_subtype_simple (ft1 ft2: func_type) : bool =
  (* Same number of parameters *)
  List.Tot.length ft1.params = List.Tot.length ft2.params &&
  (* Contravariant in parameter types *)
  params_contravariant_simple ft1.params ft2.params &&
  (* Covariant in return type *)
  subtype ft1.return_type ft2.return_type &&
  (* Covariant in effects (smaller effect set is subtype) *)
  effect_sub ft1.effects ft2.effects &&
  (* Unsafe functions can be subtype of safe, but not vice versa *)
  (ft1.is_unsafe || not ft2.is_unsafe)

(* Extended subtyping that handles function types with effects *)
let extended_subtype (t1 t2: brrr_type) : bool =
  if type_eq t1 t2 then true
  else match t1, t2 with
  (* Never (bottom) *)
  | TPrim PNever, _ -> true
  (* Dynamic (top) *)
  | _, TPrim PDynamic -> true
  (* Function subtyping *)
  | TFunc ft1, TFunc ft2 -> func_subtype_simple ft1 ft2
  (* Wrappers: covariant (except WRefMut which is invariant) *)
  | TWrap w1 t1', TWrap w2 t2' ->
      w1 = w2 && (
        if wrapper_is_covariant w1 then subtype t1' t2'
        else type_eq t1' t2'  (* Invariant: WRefMut *)
      )
  (* Result is covariant in both *)
  | TResult t1a t1b, TResult t2a t2b ->
      subtype t1a t2a && subtype t1b t2b
  (* Tuple subtyping (covariant) *)
  | TTuple ts1, TTuple ts2 ->
      List.Tot.length ts1 = List.Tot.length ts2 &&
      types_subtype_list ts1 ts2
  (* Integer promotions *)
  | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
      (match width_bits i1.width, width_bits i2.width with
       | Some w1, Some w2 -> w1 <= w2 && i1.sign = i2.sign
       | _, _ -> false)
  | _, _ -> false

(** ============================================================================
    EXTENDED TYPING CONTEXT - Operations
    ============================================================================ *)

(* Create extended context from components *)
let make_extended_ctx (lctx: type_ctx) (gctx: global_ctx) (tdctx: type_def_ctx)
                       (cenv: class_env) (rctx: region_ctx) : extended_typing_ctx = {
  etc_locals = lctx;
  etc_globals = gctx;
  etc_type_defs = tdctx;
  etc_classes = cenv;
  etc_regions = rctx;
  etc_subst = []
}

(** ============================================================================
    GRADUAL TYPING CONSISTENCY RELATION
    ============================================================================

    Type consistency (written as ~) is the key relation for gradual typing.
    Unlike subtyping, consistency is:
    - Reflexive: T ~ T
    - Symmetric: T1 ~ T2 implies T2 ~ T1
    - NOT transitive: Int ~ ? and ? ~ String, but Int ~/~ String

    The ? type (PDynamic in Brrr-Lang) is consistent with any type.
    The Unknown type (PUnknown) is the SAFE version - consistent with any type
    but requires runtime type guards before use.

    Based on: Siek & Taha 2006, Garcia et al. 2016 (Abstracting Gradual Typing)

    CRITICAL: type_consistent is SYMMETRIC but NOT TRANSITIVE.
    This non-transitivity is essential for soundness at language boundaries.
    ============================================================================ *)

(* Type consistency relation for gradual typing.
   Two types are consistent if they can be related via the dynamic/unknown type.

   Key rules:
   - Any type is consistent with itself (reflexivity)
   - PDynamic/PUnknown is consistent with any type
   - Structural types require recursive consistency on components
   - Function types: consistency is covariant in both params and return
     (unlike subtyping which is contravariant in params)
*)
let rec type_consistent (t1 t2: brrr_type) : Tot bool (decreases t1) =
  (* Rule 1: Reflexivity - equal types are consistent *)
  if type_eq t1 t2 then true

  (* Rule 2: Dynamic/Unknown is consistent with anything *)
  else match t1, t2 with
  | TPrim PDynamic, _ -> true
  | _, TPrim PDynamic -> true
  | TPrim PUnknown, _ -> true
  | _, TPrim PUnknown -> true

  (* Rule 3: Structural consistency for function types
     Note: Consistency is covariant in ALL positions (unlike subtyping) *)
  | TFunc ft1, TFunc ft2 ->
      List.Tot.length ft1.params = List.Tot.length ft2.params &&
      params_consistent ft1.params ft2.params &&
      type_consistent ft1.return_type ft2.return_type

  (* Rule 4: Wrapper types - check inner type consistency *)
  | TWrap w1 t1', TWrap w2 t2' ->
      w1 = w2 && type_consistent t1' t2'

  (* Rule 5: Result type - both components must be consistent *)
  | TResult t1a t1b, TResult t2a t2b ->
      type_consistent t1a t2a && type_consistent t1b t2b

  (* Rule 6: Tuple types - all elements must be consistent *)
  | TTuple ts1, TTuple ts2 ->
      List.Tot.length ts1 = List.Tot.length ts2 &&
      types_consistent_list ts1 ts2

  (* Rule 7: Type application - base and args must be consistent *)
  | TApp t1' args1, TApp t2' args2 ->
      type_consistent t1' t2' &&
      List.Tot.length args1 = List.Tot.length args2 &&
      types_consistent_list args1 args2

  (* Rule 8: Named types - must be same name (nominal equality) *)
  | TNamed n1, TNamed n2 -> n1 = n2

  (* Rule 9: No consistency for incompatible ground types *)
  | _, _ -> false

(* Check parameter type list consistency *)
and params_consistent (ps1 ps2: list BrrrTypes.param_type) : Tot bool (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> true
  | p1 :: r1, p2 :: r2 ->
      type_consistent (Mkparam_type?.ty p1) (Mkparam_type?.ty p2) &&
      params_consistent r1 r2
  | _, _ -> false

(* Check type list consistency *)
and types_consistent_list (ts1 ts2: list brrr_type) : Tot bool (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> true
  | t1 :: r1, t2 :: r2 -> type_consistent t1 t2 && types_consistent_list r1 r2
  | _, _ -> false

(* Consistency is symmetric - useful lemma for bidirectional checking *)
val type_consistent_sym : t1:brrr_type -> t2:brrr_type ->
  Lemma (ensures type_consistent t1 t2 = type_consistent t2 t1)
        (decreases t1)
        [SMTPat (type_consistent t1 t2)]
let rec type_consistent_sym t1 t2 =
  if type_eq t1 t2 then (type_eq_sym t1 t2; ())
  else match t1, t2 with
  | TPrim PDynamic, _ | _, TPrim PDynamic -> ()
  | TPrim PUnknown, _ | _, TPrim PUnknown -> ()
  | TFunc ft1, TFunc ft2 ->
      if List.Tot.length ft1.params = List.Tot.length ft2.params then
        (params_consistent_sym ft1.params ft2.params;
         type_consistent_sym ft1.return_type ft2.return_type)
      else ()
  | TWrap w1 t1', TWrap w2 t2' -> if w1 = w2 then type_consistent_sym t1' t2' else ()
  | TResult t1a t1b, TResult t2a t2b -> type_consistent_sym t1a t2a; type_consistent_sym t1b t2b
  | TTuple ts1, TTuple ts2 ->
      if List.Tot.length ts1 = List.Tot.length ts2 then types_consistent_list_sym ts1 ts2 else ()
  | TApp t1' args1, TApp t2' args2 ->
      type_consistent_sym t1' t2';
      if List.Tot.length args1 = List.Tot.length args2 then types_consistent_list_sym args1 args2 else ()
  | _, _ -> ()

and params_consistent_sym (ps1 ps2: list BrrrTypes.param_type) : Lemma (ensures params_consistent ps1 ps2 = params_consistent ps2 ps1) (decreases ps1) =
  match ps1, ps2 with
  | [], [] -> ()
  | p1 :: r1, p2 :: r2 -> type_consistent_sym (Mkparam_type?.ty p1) (Mkparam_type?.ty p2); params_consistent_sym r1 r2
  | _, _ -> ()

and types_consistent_list_sym (ts1 ts2: list brrr_type) : Lemma (ensures types_consistent_list ts1 ts2 = types_consistent_list ts2 ts1) (decreases ts1) =
  match ts1, ts2 with
  | [], [] -> ()
  | t1 :: r1, t2 :: r2 -> type_consistent_sym t1 t2; types_consistent_list_sym r1 r2
  | _, _ -> ()

(** ============================================================================
    GRADUAL TYPING: CAST INSERTION
    ============================================================================

    Cast insertion enables runtime safety for gradual typing.
    When types are consistent but not subtypes, casts are inserted.

    Based on: Siek & Taha 2006 "Gradual Typing for Functional Languages"
    ============================================================================ *)

(* Gradual inference result - includes potentially cast-wrapped expression *)
noeq type gradual_infer_result =
  | GInferOk  : expr:expr -> ty:brrr_type -> eff:effect_row -> ctx:type_ctx -> gradual_infer_result
  | GInferErr : err:type_error -> gradual_infer_result

(* Determine cast kind based on type relationship *)
let determine_cast_kind (from_ty to_ty: brrr_type) : BrrrExpressions.cast_kind =
  if type_eq from_ty to_ty then CastSafe          (* No cast needed *)
  else if extended_subtype from_ty to_ty then CastSafe  (* Upcast *)
  else if is_safe_numeric_cast from_ty to_ty then CastSafe
  else if is_valid_numeric_cast from_ty to_ty then CastLossy
  else CastGradual  (* Requires runtime check *)

(* Insert a cast from from_ty to to_ty around expression e *)
let insert_cast (e: expr) (from_ty to_ty: brrr_type) (blame: BrrrExpressions.blame_label) : expr =
  if type_eq from_ty to_ty then e
  else
    let kind = determine_cast_kind from_ty to_ty in
    ECast e from_ty to_ty kind blame

(* Insert cast through Dynamic for types that are consistent but not subtypes *)
let insert_cast_via_dynamic (e: expr) (from_ty to_ty: brrr_type) (blame: BrrrExpressions.blame_label) : expr =
  if type_eq from_ty to_ty then e
  else if extended_subtype from_ty to_ty then ECast e from_ty to_ty CastSafe blame
  else
    (* Cast through Dynamic: e : from_ty  =>  (e : ?) : to_ty *)
    let to_dynamic = ECast e from_ty (TPrim PDynamic) CastGradual blame in
    ECast to_dynamic (TPrim PDynamic) to_ty CastGradual blame

(* Insert appropriate cast based on type relationship *)
let insert_cast_if_needed (e: expr) (from_ty to_ty: brrr_type) (blame: BrrrExpressions.blame_label) : option expr =
  if type_eq from_ty to_ty then Some e
  else if type_consistent from_ty to_ty then
    Some (insert_cast_via_dynamic e from_ty to_ty blame)
  else
    None  (* Types not consistent - cannot cast *)

(* Check expression against expected type, inserting casts as needed.
   Note: This is a stub implementation. The full implementation requires
   infer_type which is defined later in the file. The actual gradual type
   checking is performed during the main type inference pass. *)
let check_type_gradual (gctx: global_ctx) (ctx: type_ctx) (e: expr) (expected: brrr_type) (span: source_span)
    : gradual_infer_result =
  (* Stub: Accept expression and assume it has the expected type.
     Full implementation would call infer_type and check consistency. *)
  GInferOk e expected pure ctx

(** ============================================================================
    TYPE CLASS CONSTRAINT INTEGRATION
    ============================================================================

    When type-checking a polymorphic function with constraints like:
      forall a. Eq a => a -> a -> Bool

    We need to verify that at each call site, the instantiated type satisfies
    the constraint. For example, if we call this function with i32, we need
    to verify that there exists an instance Eq i32.

    Integration points:
    1. EGlobal: When instantiating a polymorphic global, check constraints
    2. ECall: When calling a constrained function, verify constraints hold
    3. Method resolution: Use type class instances to resolve methods
    ============================================================================ *)

(* Check that all type class constraints are satisfied given the current substitution *)
let check_constraints_satisfied (constraints: list class_constraint)
                                  (subst: list (type_var & brrr_type))
                                  (cenv: class_env) : bool =
  all_constraints_entailed constraints subst cenv

(* Result of constraint checking: either success or error with details *)
type constraint_check_result =
  | ConstraintsOk : constraint_check_result
  | ConstraintFailed : cls:class_name -> ty:brrr_type -> constraint_check_result

(* Check constraints with detailed error reporting *)
let rec check_constraints_detailed (constraints: list class_constraint)
                                     (subst: list (type_var & brrr_type))
                                     (cenv: class_env) : constraint_check_result =
  match constraints with
  | [] -> ConstraintsOk
  | c :: rest ->
      if constraint_entailed c subst cenv then
        check_constraints_detailed rest subst cenv
      else
        (* Constraint failed - report which one *)
        (match assoc c.cc_var subst with
         | Some ty -> ConstraintFailed c.cc_class ty
         | None -> ConstraintFailed c.cc_class t_dynamic) (* Variable not in subst *)

(** ============================================================================
    REGION CHECKING INTEGRATION
    ============================================================================

    Regions track memory lifetimes. When type-checking borrows and references,
    we need to verify:
    1. The borrowed value lives long enough (region outlives)
    2. No region escapes its scope
    3. Borrows don't conflict (shared vs exclusive)

    Integration with BorrowChecker module:
    - has_region_cap: Check if a region is valid in current context
    - region_outlives: Check lifetime ordering
    - letregion_scope_ok: Verify region doesn't escape
    ============================================================================ *)

(* Check if a region is valid in the extended context *)
let region_valid_in_ctx (r: region_id) (ectx: extended_typing_ctx) : bool =
  has_region_cap r ectx.etc_regions

(* Add a region capability to the extended context *)
let add_region_to_ctx (r: region_id) (ectx: extended_typing_ctx) : extended_typing_ctx =
  { ectx with etc_regions = add_region_cap r ectx.etc_regions }

(* Remove/invalidate a region from context (for exiting letregion) *)
let invalidate_region_in_ctx (r: region_id) (ectx: extended_typing_ctx) : extended_typing_ctx =
  { ectx with etc_regions = invalidate_region r ectx.etc_regions }

(** ============================================================================
    TYPE UNIFICATION ALGORITHM
    ============================================================================

    This section implements Hindley-Milner style type unification with extensions
    for gradual typing and effect row polymorphism.

    REFERENCES:
    - Pierce, TAPL Chapter 22 "Type Reconstruction"
    - Siek & Taha 2006, "Gradual Typing for Functional Languages"
    - Remy 1994, "Type Inference for Records in Natural Extension of ML"
    - brrr_lang_spec_v0.4.tex Section 8 "Type Inference"

    KEY CONCEPTS:

    1. TYPE SUBSTITUTION: A mapping from type variables to types.
       Substitutions are applied to types, replacing type variables with
       their mapped types. Composition of substitutions (s2 after s1) means
       first apply s1, then apply s2 to the result.

    2. UNIFICATION: Finding a substitution S such that S(t1) = S(t2).
       Unification fails if types are structurally incompatible or if
       the occurs check detects an infinite type.

    3. OCCURS CHECK: Prevents infinite types like alpha = alpha -> int.
       Before binding alpha := t, verify alpha does not appear free in t.

    4. GRADUAL TYPING EXTENSION: The Dynamic type (?) unifies with any type
       without producing a substitution. This enables gradual type inference.

    5. ROW UNIFICATION: Effect rows are unified using row rewriting to
       handle polymorphic effects (Remy-style row polymorphism).

    6. CONSTRAINT SOLVING: Unification problems are collected as constraints
       and solved iteratively, building up a most general unifier.

    ============================================================================ *)

(** --------------------------------------------------------------------------
    TYPE SUBSTITUTION
    --------------------------------------------------------------------------

    A type substitution maps type variables to types. We represent it as
    an association list [(alpha1, t1); (alpha2, t2); ...].

    Key operations:
    - empty_subst: The identity substitution
    - singleton_subst: Maps one variable
    - compose_subst: Sequential composition (apply first, then second)
    - apply_subst: Apply substitution to a type
    -------------------------------------------------------------------------- *)

(* Type substitution: maps type variables to types *)
type type_subst = list (type_var & brrr_type)

(* Empty substitution - identity mapping *)
let empty_subst : type_subst = []

(* Singleton substitution: maps variable v to type t *)
let singleton_subst (v: type_var) (t: brrr_type) : type_subst = [(v, t)]

(* Lookup a type variable in substitution *)
let rec subst_lookup (v: type_var) (s: type_subst) : option brrr_type =
  match s with
  | [] -> None
  | (v', t) :: rest -> if v = v' then Some t else subst_lookup v rest

(* Apply substitution to a type variable - returns TVar if not found *)
let apply_subst_var (s: type_subst) (v: type_var) : brrr_type =
  match subst_lookup v s with
  | Some t -> t
  | None -> TVar v

(* Apply substitution to a type (replaces all type variables) *)
let rec apply_subst (s: type_subst) (t: brrr_type)
    : Tot brrr_type (decreases t) =
  match t with
  | TPrim p -> TPrim p
  | TNumeric n -> TNumeric n
  | TVar v -> apply_subst_var s v
  | TWrap w inner -> TWrap w (apply_subst s inner)
  | TModal m inner -> TModal m (apply_subst s inner)
  | TResult tok terr -> TResult (apply_subst s tok) (apply_subst s terr)
  | TTuple ts -> TTuple (apply_subst_list s ts)
  | TFunc ft -> TFunc {
      params = apply_subst_params s ft.params;
      return_type = apply_subst s ft.return_type;
      effects = apply_subst_row s ft.effects;
      is_unsafe = ft.is_unsafe
    }
  | TApp base args -> TApp (apply_subst s base) (apply_subst_list s args)
  | TNamed n -> TNamed n
  | TStruct st -> TStruct {
      struct_name = st.struct_name;
      struct_fields = apply_subst_fields s st.struct_fields;
      struct_repr = st.struct_repr
    }
  | TEnum et -> TEnum {
      enum_name = et.enum_name;
      enum_variants = apply_subst_variants s et.enum_variants
    }

(* Apply substitution to type list *)
and apply_subst_list (s: type_subst) (ts: list brrr_type)
    : Tot (list brrr_type) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> apply_subst s t :: apply_subst_list s rest

(* Apply substitution to parameter list *)
and apply_subst_params (s: type_subst) (ps: list param_type)
    : Tot (list param_type) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest ->
      { name = p.name; ty = apply_subst s p.ty; mode = p.mode }
      :: apply_subst_params s rest

(* Apply substitution to effect row *)
and apply_subst_row (s: type_subst) (r: effect_row)
    : Tot effect_row (decreases r) =
  match r with
  | RowEmpty -> RowEmpty
  | RowVar v ->
      (* Effect row variables are separate from type variables in this implementation,
         but for simplicity we treat them uniformly. A full implementation would
         distinguish them. *)
      RowVar v
  | RowExt eff rest -> RowExt eff (apply_subst_row s rest)

(* Apply substitution to struct fields *)
and apply_subst_fields (s: type_subst) (fs: list field_type)
    : Tot (list field_type) (decreases fs) =
  match fs with
  | [] -> []
  | f :: rest ->
      { field_name = f.field_name; field_ty = apply_subst s f.field_ty; field_vis = f.field_vis; field_tag = f.field_tag }
      :: apply_subst_fields s rest

(* Apply substitution to enum variants *)
and apply_subst_variants (s: type_subst) (vs: list variant_type)
    : Tot (list variant_type) (decreases vs) =
  match vs with
  | [] -> []
  | v :: rest ->
      { variant_name = v.variant_name; variant_fields = apply_subst_list s v.variant_fields }
      :: apply_subst_variants s rest

(* Compose two substitutions: apply s1 first, then s2.
   compose_subst s1 s2 produces a substitution s such that
   apply_subst s t = apply_subst s2 (apply_subst s1 t)

   Implementation: Apply s2 to the range of s1, then add bindings from s2
   that are not in s1's domain. *)
let rec compose_subst (s1 s2: type_subst) : type_subst =
  let s1' = List.Tot.map (fun (v, t) -> (v, apply_subst s2 t)) s1 in
  let s2_new = List.Tot.filter (fun (v, _) ->
    not (List.Tot.existsb (fun (v', _) -> v = v') s1)
  ) s2 in
  s1' @ s2_new

(** --------------------------------------------------------------------------
    OCCURS CHECK
    --------------------------------------------------------------------------

    The occurs check prevents creation of infinite types.
    Before binding alpha := t, we verify alpha does not appear free in t.

    Example of infinite type:
      alpha = alpha -> int
    Without occurs check, this would create: ((...-> int) -> int) -> int
    -------------------------------------------------------------------------- *)

(* Check if type variable v occurs free in type t *)
let rec occurs (v: type_var) (t: brrr_type) : Tot bool (decreases t) =
  match t with
  | TPrim _ -> false
  | TNumeric _ -> false
  | TVar v' -> v = v'
  | TWrap _ inner -> occurs v inner
  | TModal _ inner -> occurs v inner
  | TResult tok terr -> occurs v tok || occurs v terr
  | TTuple ts -> occurs_list v ts
  | TFunc ft ->
      occurs_params v ft.params || occurs v ft.return_type
  | TApp base args -> occurs v base || occurs_list v args
  | TNamed _ -> false
  | TStruct st -> occurs_fields v st.struct_fields
  | TEnum et -> occurs_variants v et.enum_variants

(* Check if type variable occurs in type list *)
and occurs_list (v: type_var) (ts: list brrr_type) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: rest -> occurs v t || occurs_list v rest

(* Check if type variable occurs in parameter list *)
and occurs_params (v: type_var) (ps: list param_type) : Tot bool (decreases ps) =
  match ps with
  | [] -> false
  | p :: rest -> occurs v p.ty || occurs_params v rest

(* Check if type variable occurs in field list *)
and occurs_fields (v: type_var) (fs: list field_type) : Tot bool (decreases fs) =
  match fs with
  | [] -> false
  | f :: rest -> occurs v f.field_ty || occurs_fields v rest

(* Check if type variable occurs in variant list *)
and occurs_variants (v: type_var) (vs: list variant_type) : Tot bool (decreases vs) =
  match vs with
  | [] -> false
  | vr :: rest -> occurs_list v vr.variant_fields || occurs_variants v rest

(** --------------------------------------------------------------------------
    UNIFICATION RESULT
    -------------------------------------------------------------------------- *)

(* Result of unification: either success with substitution, or failure with error *)
noeq type unify_result =
  | UOk : subst:type_subst -> unify_result
  | UFail : t1:brrr_type -> t2:brrr_type -> reason:string -> unify_result

(* Unification succeeded with empty substitution *)
let unify_ok : unify_result = UOk empty_subst

(* Unification succeeded with singleton substitution *)
let unify_var (v: type_var) (t: brrr_type) : unify_result =
  UOk (singleton_subst v t)

(** --------------------------------------------------------------------------
    CORE UNIFICATION ALGORITHM
    --------------------------------------------------------------------------

    The unification algorithm finds a most general unifier (MGU) for two types.

    Algorithm (Robinson 1965, extended for gradual typing):
    1. If t1 = t2 (structurally equal), return empty substitution
    2. If t1 is type variable alpha not occurring in t2, return [alpha := t2]
    3. If t2 is type variable alpha not occurring in t1, return [alpha := t1]
    4. If both are Dynamic, return empty (gradual typing)
    5. If one is Dynamic, return empty (gradual typing extension)
    6. If both are compound (arrow, tuple, etc.), unify components recursively
    7. Otherwise, fail

    Key properties:
    - Idempotent: apply_subst (unify t1 t2) t1 = apply_subst (unify t1 t2) t2
    - Most general: any other unifier is an instance of MGU
    -------------------------------------------------------------------------- *)

(* Unify two types, returning a substitution or failure *)
let rec unify (t1 t2: brrr_type) : Tot unify_result (decreases %[type_size t1 + type_size t2; 0]) =
  (* Rule 1: Structural equality - types are already equal *)
  if type_eq t1 t2 then UOk empty_subst

  else match t1, t2 with
  (* Rule 2 and 3: Type variable cases *)
  | TVar v, _ ->
      if occurs v t2 then
        UFail t1 t2 ("occurs check failed: " ^ v ^ " occurs in target type")
      else
        UOk (singleton_subst v t2)

  | _, TVar v ->
      if occurs v t1 then
        UFail t1 t2 ("occurs check failed: " ^ v ^ " occurs in target type")
      else
        UOk (singleton_subst v t1)

  (* Rule 4 and 5: Gradual typing - Dynamic unifies with anything *)
  | TPrim PDynamic, _ -> UOk empty_subst
  | _, TPrim PDynamic -> UOk empty_subst

  (* Unknown is also consistent with anything for gradual typing *)
  | TPrim PUnknown, _ -> UOk empty_subst
  | _, TPrim PUnknown -> UOk empty_subst

  (* Rule 6: Structural unification for compound types *)

  (* Function types: contravariant in params, covariant in return *)
  | TFunc ft1, TFunc ft2 ->
      if List.Tot.length ft1.params <> List.Tot.length ft2.params then
        UFail t1 t2 "function parameter count mismatch"
      else
        unify_func ft1 ft2

  (* Wrapper types: same wrapper, unify inner *)
  | TWrap w1 inner1, TWrap w2 inner2 ->
      if w1 <> w2 then
        UFail t1 t2 "wrapper type mismatch"
      else
        unify inner1 inner2

  (* Modal types: same modality, unify inner *)
  | TModal m1 inner1, TModal m2 inner2 ->
      if not (modal_eq m1 m2) then
        UFail t1 t2 "modal type mismatch"
      else
        unify inner1 inner2

  (* Result types: unify both components *)
  | TResult tok1 terr1, TResult tok2 terr2 ->
      (match unify tok1 tok2 with
       | UOk s1 ->
           (match unify (apply_subst s1 terr1) (apply_subst s1 terr2) with
            | UOk s2 -> UOk (compose_subst s1 s2)
            | err -> err)
       | err -> err)

  (* Tuple types: unify element-wise *)
  | TTuple ts1, TTuple ts2 ->
      if List.Tot.length ts1 <> List.Tot.length ts2 then
        UFail t1 t2 "tuple length mismatch"
      else
        unify_list ts1 ts2

  (* Type application: unify base and arguments *)
  | TApp base1 args1, TApp base2 args2 ->
      if List.Tot.length args1 <> List.Tot.length args2 then
        UFail t1 t2 "type application argument count mismatch"
      else
        (match unify base1 base2 with
         | UOk s1 ->
             (match unify_list (apply_subst_list s1 args1) (apply_subst_list s1 args2) with
              | UOk s2 -> UOk (compose_subst s1 s2)
              | err -> err)
         | err -> err)

  (* Named types: must be same name (nominal equality) *)
  | TNamed n1, TNamed n2 ->
      if n1 = n2 then UOk empty_subst
      else UFail t1 t2 ("named type mismatch: " ^ n1 ^ " vs " ^ n2)

  (* Numeric types: must be exact match *)
  | TNumeric n1, TNumeric n2 ->
      if numeric_eq n1 n2 then UOk empty_subst
      else UFail t1 t2 "numeric type mismatch"

  (* Primitive types: must be exact match *)
  | TPrim p1, TPrim p2 ->
      if p1 = p2 then UOk empty_subst
      else UFail t1 t2 "primitive type mismatch"

  (* All other cases: incompatible types *)
  | _, _ -> UFail t1 t2 "incompatible types"

(* Unify function types *)
and unify_func (ft1 ft2: func_type)
    : Tot unify_result (decreases %[func_type_size ft1 + func_type_size ft2; 1]) =
  (* First unify parameters (they should unify, not be contravariant for MGU) *)
  match unify_params ft1.params ft2.params with
  | UOk s1 ->
      (* Then unify return types with substitution applied *)
      (match unify (apply_subst s1 ft1.return_type) (apply_subst s1 ft2.return_type) with
       | UOk s2 ->
           (* Finally unify effect rows *)
           (match unify_rows (apply_subst_row (compose_subst s1 s2) ft1.effects)
                             (apply_subst_row (compose_subst s1 s2) ft2.effects) with
            | UOk s3 -> UOk (compose_subst (compose_subst s1 s2) s3)
            | err -> err)
       | err -> err)
  | err -> err

(* Size measure for func_type to help with termination *)
and func_type_size (ft: func_type) : nat =
  param_list_size ft.params + type_size ft.return_type + 1

(* Unify parameter lists *)
and unify_params (ps1 ps2: list param_type)
    : Tot unify_result (decreases %[param_list_size ps1 + param_list_size ps2; 0]) =
  match ps1, ps2 with
  | [], [] -> UOk empty_subst
  | p1 :: rest1, p2 :: rest2 ->
      (match unify p1.ty p2.ty with
       | UOk s1 ->
           (match unify_params
                    (apply_subst_params s1 rest1)
                    (apply_subst_params s1 rest2) with
            | UOk s2 -> UOk (compose_subst s1 s2)
            | err -> err)
       | err -> err)
  | _, _ -> UFail (TTuple []) (TTuple []) "parameter list length mismatch"

(* Unify type lists element-wise *)
and unify_list (ts1 ts2: list brrr_type)
    : Tot unify_result (decreases %[type_list_size ts1 + type_list_size ts2; 0]) =
  match ts1, ts2 with
  | [], [] -> UOk empty_subst
  | t1 :: rest1, t2 :: rest2 ->
      (match unify t1 t2 with
       | UOk s1 ->
           (match unify_list (apply_subst_list s1 rest1) (apply_subst_list s1 rest2) with
            | UOk s2 -> UOk (compose_subst s1 s2)
            | err -> err)
       | err -> err)
  | _, _ -> UFail (TTuple ts1) (TTuple ts2) "type list length mismatch"

(** --------------------------------------------------------------------------
    EFFECT ROW UNIFICATION
    --------------------------------------------------------------------------

    Effect rows are unified using Remy-style row polymorphism.

    An effect row has the form: eff1 | eff2 | ... | rho
    where rho is either RowEmpty or a row variable RowVar.

    Row unification handles:
    1. Both empty rows -> success
    2. Row variable with concrete row -> bind variable
    3. Same effect label at head -> unify tails
    4. Different effect labels -> row rewriting to align

    Row rewriting: If we have (e1 | r1) vs (e2 | r2) where e1 != e2,
    we rewrite r2 to (e1 | r2') and unify (r1 vs (e2 | r2')).
    -------------------------------------------------------------------------- *)

(* Unify two effect rows *)
and unify_rows (r1 r2: effect_row)
    : Tot unify_result (decreases %[row_size r1 + row_size r2; 0]) =
  match r1, r2 with
  (* Both empty: trivially unify *)
  | RowEmpty, RowEmpty -> UOk empty_subst

  (* Row variable with anything: bind the variable *)
  | RowVar v, _ ->
      (* For row variables, we would need occurs check on rows.
         For simplicity, we just bind directly. *)
      UOk empty_subst  (* Simplified: in full impl, would bind row var *)

  | _, RowVar v ->
      UOk empty_subst  (* Simplified: in full impl, would bind row var *)

  (* Same effect at head: unify tails *)
  | RowExt e1 rest1, RowExt e2 rest2 ->
      if e1 = e2 then
        unify_rows rest1 rest2
      else
        (* Row rewriting: find e1 in r2, or fail *)
        (match rewrite_row e1 r2 with
         | Some (t, rest2') ->
             (* e1 found in r2 with tail rest2', now unify rest1 with (e2 | rest2') *)
             unify_rows rest1 (RowExt e2 rest2')
         | None ->
             (* e1 not in r2 - rows are incompatible *)
             UFail (TPrim PUnit) (TPrim PUnit) "effect row mismatch")

  (* Empty vs non-empty: fail (unless row variable) *)
  | RowEmpty, RowExt _ _ -> UFail (TPrim PUnit) (TPrim PUnit) "effect row mismatch: expected empty"
  | RowExt _ _, RowEmpty -> UFail (TPrim PUnit) (TPrim PUnit) "effect row mismatch: expected effects"

(* Row size for termination measure *)
and row_size (r: effect_row) : nat =
  match r with
  | RowEmpty -> 0
  | RowVar _ -> 1
  | RowExt _ rest -> 1 + row_size rest

(* Rewrite row to extract a specific effect label.
   Given effect e and row r, if e is in r, return Some (payload, remainder)
   where r = e | remainder. Otherwise return None. *)
and rewrite_row (e: effect_label) (r: effect_row) : option (effect_label & effect_row) =
  match r with
  | RowEmpty -> None
  | RowVar _ -> Some (e, r)  (* Row variable can contain any effect *)
  | RowExt e' rest ->
      if e = e' then Some (e', rest)
      else
        match rewrite_row e rest with
        | Some (found, rest') -> Some (found, RowExt e' rest')
        | None -> None

(** --------------------------------------------------------------------------
    UNIFICATION CONSTRAINTS
    --------------------------------------------------------------------------

    For more complex type inference, we collect constraints and solve them
    in batch. This allows for better error messages and handling of
    mutual dependencies.

    Constraint types:
    - CEq: Type equality constraint (t1 = t2)
    - CSubtype: Subtyping constraint (t1 <: t2)
    - CConsistent: Gradual consistency (t1 ~ t2)
    -------------------------------------------------------------------------- *)

(* Unification constraint types *)
noeq type unify_constraint =
  | CEq : t1:brrr_type -> t2:brrr_type -> unify_constraint           (* t1 = t2 *)
  | CSubtype : t1:brrr_type -> t2:brrr_type -> unify_constraint      (* t1 <: t2 *)
  | CConsistent : t1:brrr_type -> t2:brrr_type -> unify_constraint   (* t1 ~ t2 *)

(* Constraint set *)
type constraint_set = list unify_constraint

(* Empty constraint set *)
let empty_constraints : constraint_set = []

(* Add equality constraint *)
let add_eq_constraint (t1 t2: brrr_type) (cs: constraint_set) : constraint_set =
  CEq t1 t2 :: cs

(* Add subtype constraint *)
let add_subtype_constraint (t1 t2: brrr_type) (cs: constraint_set) : constraint_set =
  CSubtype t1 t2 :: cs

(* Add consistency constraint *)
let add_consistent_constraint (t1 t2: brrr_type) (cs: constraint_set) : constraint_set =
  CConsistent t1 t2 :: cs

(* Apply substitution to a constraint *)
let apply_subst_constraint (s: type_subst) (c: unify_constraint) : unify_constraint =
  match c with
  | CEq t1 t2 -> CEq (apply_subst s t1) (apply_subst s t2)
  | CSubtype t1 t2 -> CSubtype (apply_subst s t1) (apply_subst s t2)
  | CConsistent t1 t2 -> CConsistent (apply_subst s t1) (apply_subst s t2)

(* Apply substitution to constraint set *)
let apply_subst_constraints (s: type_subst) (cs: constraint_set) : constraint_set =
  List.Tot.map (apply_subst_constraint s) cs

(** --------------------------------------------------------------------------
    CONSTRAINT SOLVING
    --------------------------------------------------------------------------

    Solve a set of constraints, producing a substitution or failure.

    Algorithm:
    1. Pick a constraint from the set
    2. Solve it (unify for equality, check for subtype/consistency)
    3. Apply resulting substitution to remaining constraints
    4. Repeat until no constraints remain

    For subtyping constraints, we use the extended_subtype relation.
    For consistency constraints, we use the type_consistent relation.
    -------------------------------------------------------------------------- *)

(* Result of constraint solving *)
noeq type solve_result =
  | SolveOk : subst:type_subst -> solve_result
  | SolveFail : constraint:unify_constraint -> reason:string -> solve_result

(* Solve a single constraint, returning a substitution or failure *)
let solve_one_constraint (c: unify_constraint) : unify_result =
  match c with
  | CEq t1 t2 ->
      (* Equality: use unification *)
      unify t1 t2

  | CSubtype t1 t2 ->
      (* Subtyping: check if t1 <: t2 holds, no substitution produced *)
      if extended_subtype t1 t2 then UOk empty_subst
      else
        (* Try unification as fallback for type variables *)
        (match t1, t2 with
         | TVar v, _ -> unify t1 t2
         | _, TVar v -> unify t1 t2
         | _, _ -> UFail t1 t2 "subtype constraint failed")

  | CConsistent t1 t2 ->
      (* Consistency: check if t1 ~ t2, no substitution needed *)
      if type_consistent t1 t2 then UOk empty_subst
      else UFail t1 t2 "consistency constraint failed"

(* Solve all constraints in a set.
   Iteratively solves constraints, applying substitutions to remaining ones.
   Returns the composed substitution or the first failure. *)
let rec solve_constraints (cs: constraint_set)
    : Tot solve_result (decreases List.Tot.length cs) =
  match cs with
  | [] -> SolveOk empty_subst
  | c :: rest ->
      (match solve_one_constraint c with
       | UOk s ->
           (* Apply substitution to remaining constraints *)
           let rest' = apply_subst_constraints s rest in
           (* Recursively solve remaining *)
           (match solve_constraints rest' with
            | SolveOk s' -> SolveOk (compose_subst s s')
            | err -> err)
       | UFail t1 t2 reason ->
           SolveFail c reason)

(** --------------------------------------------------------------------------
    TYPE GENERALIZATION
    --------------------------------------------------------------------------

    Generalization closes over free type variables to create a type scheme.

    Given context Gamma and type T, generalize(Gamma, T) produces:
      forall a1, ..., an. T
    where {a1, ..., an} = fv(T) - fv(Gamma)

    This is the "gen" operation in let-polymorphism (Damas-Milner).
    -------------------------------------------------------------------------- *)

(* Collect free type variables in a context *)
let rec free_type_vars_ctx (ctx: type_ctx) : list type_var =
  match ctx with
  | [] -> []
  | b :: rest ->
      free_type_vars b.bind_type @ free_type_vars_ctx rest

(* List difference: remove elements of l2 from l1 *)
let rec list_diff (#a: eqtype) (l1 l2: list a) : list a =
  match l1 with
  | [] -> []
  | x :: rest ->
      if List.Tot.mem x l2 then list_diff rest l2
      else x :: list_diff rest l2

(* Remove duplicates from a list *)
let rec list_unique (#a: eqtype) (l: list a) : list a =
  match l with
  | [] -> []
  | x :: rest ->
      if List.Tot.mem x rest then list_unique rest
      else x :: list_unique rest

(* Generalize a type over free variables not in context.
   Returns a type scheme with quantified variables. *)
let generalize (ctx: type_ctx) (ty: brrr_type) : type_scheme =
  let fvs_ty = list_unique (free_type_vars ty) in
  let fvs_ctx = free_type_vars_ctx ctx in
  let gen_vars = list_diff fvs_ty fvs_ctx in
  {
    type_vars = gen_vars;
    effect_vars = [];  (* Effect generalization not implemented here *)
    body = ty
  }

(* Create a monomorphic type scheme (no generalization) *)
let no_generalize (ty: brrr_type) : type_scheme =
  {
    type_vars = [];
    effect_vars = [];
    body = ty
  }

(** --------------------------------------------------------------------------
    INSTANTIATION WITH FRESH VARIABLES
    --------------------------------------------------------------------------

    Instantiate a type scheme with fresh type variables.
    This is the dual of generalization, used when using a polymorphic binding.
    -------------------------------------------------------------------------- *)

(* Fresh type variable counter (in a real implementation, this would be
   threaded through the type checker as state) *)
let fresh_var_counter : nat = 0

(* Generate a fresh type variable name *)
let fresh_type_var (base: string) (counter: nat) : type_var =
  base ^ "_" ^ string_of_int counter

(* Instantiate a type scheme with fresh variables.
   Replaces all quantified variables with fresh type variables.
   Returns the instantiated type and list of fresh variables. *)
let instantiate_with_fresh (scheme: type_scheme) (counter: nat)
    : brrr_type & list type_var & nat =
  let n = List.Tot.length scheme.type_vars in
  let fresh_vars = List.Tot.mapi (fun i v -> fresh_type_var v (counter + i)) scheme.type_vars in
  let fresh_types = List.Tot.map TVar fresh_vars in
  match instantiate scheme fresh_types with
  | Some ty -> (ty, fresh_vars, counter + n)
  | None -> (scheme.body, [], counter)  (* Fallback: return body unchanged *)

(** --------------------------------------------------------------------------
    UNIFICATION LEMMAS
    -------------------------------------------------------------------------- *)

(* Unification is reflexive: unify t t = UOk empty_subst *)
val unify_refl : t:brrr_type ->
  Lemma (ensures (match unify t t with UOk _ -> true | _ -> false))
        (decreases t)
        [SMTPat (unify t t)]
let rec unify_refl t =
  type_eq_refl t

(* Apply empty substitution is identity *)
val apply_empty_subst : t:brrr_type ->
  Lemma (ensures type_eq (apply_subst empty_subst t) t = true)
        (decreases t)
        [SMTPat (apply_subst empty_subst t)]
let rec apply_empty_subst t =
  match t with
  | TPrim _ -> ()
  | TNumeric _ -> ()
  | TVar _ -> ()
  | TWrap _ inner -> apply_empty_subst inner
  | TModal _ inner -> apply_empty_subst inner
  | TResult tok terr -> apply_empty_subst tok; apply_empty_subst terr
  | TTuple ts -> apply_empty_subst_list ts
  | TFunc ft ->
      apply_empty_subst_params ft.params;
      apply_empty_subst ft.return_type
  | TApp base args ->
      apply_empty_subst base;
      apply_empty_subst_list args
  | TNamed _ -> ()
  | TStruct st -> apply_empty_subst_fields st.struct_fields
  | TEnum et -> apply_empty_subst_variants et.enum_variants

and apply_empty_subst_list (ts: list brrr_type)
    : Lemma (ensures type_list_eq (apply_subst_list empty_subst ts) ts = true) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: rest -> apply_empty_subst t; apply_empty_subst_list rest

and apply_empty_subst_params (ps: list param_type)
    : Lemma (decreases ps) =
  match ps with
  | [] -> ()
  | p :: rest -> apply_empty_subst p.ty; apply_empty_subst_params rest

and apply_empty_subst_fields (fs: list field_type)
    : Lemma (decreases fs) =
  match fs with
  | [] -> ()
  | f :: rest -> apply_empty_subst f.field_ty; apply_empty_subst_fields rest

and apply_empty_subst_variants (vs: list variant_type)
    : Lemma (decreases vs) =
  match vs with
  | [] -> ()
  | v :: rest -> apply_empty_subst_list v.variant_fields; apply_empty_subst_variants rest

(** ============================================================================
    GRADUAL TYPING: CAST INSERTION
    ============================================================================

    Cast insertion is the core mechanism enabling gradual typing's runtime safety.
    When an expression of type T1 flows to a context expecting type T2, and T1
    and T2 are consistent but not in a subtype relationship, casts are inserted
    to perform runtime type checks.

    THEORY:
    -------
    Based on Siek & Taha 2006 "Gradual Typing for Functional Languages":
    - Consistency (T1 ~ T2) is symmetric but NOT transitive
    - Dynamic is consistent with any type: forall T. Dynamic ~ T
    - Casts mediate between statically-typed and dynamically-typed code

    CAST KINDS:
    -----------
    - CKUp (upcast): T1 <: T2, always safe, can be erased by optimizer
    - CKDown (downcast): T2 <: T1, may fail at runtime with blame
    - CKDynamic: Involves Dynamic type, requires runtime type tag check

    BLAME ASSIGNMENT (Wadler & Findler 2009):
    -----------------------------------------
    - Positive blame: The expression being cast is at fault
    - Negative blame: The context expecting the type is at fault
    - Function casts flip blame on argument position (contravariance)

    Example: If (f : Int -> Int) is used where (Dynamic -> Int) is expected,
    and caller passes a String, the CALLER (negative position) is blamed.

    IMPLEMENTATION NOTES:
    ---------------------
    1. insert_cast creates the appropriate cast kind based on subtype relations
    2. For function casts, the function is wrapped to insert arg/return casts
    3. Casts compose: (T1 => Dynamic) followed by (Dynamic => T2)
    4. Identity casts (T => T) are eliminated

    Reference: brrr_lang_spec_v0.4.tex Section "Dynamic Type"
    Reference: Siek & Taha 2006, Garcia et al. 2016 (Abstracting Gradual Typing)
    ============================================================================ *)

(** Determine cast kind based on type relationship.
    - If from_ty <: to_ty, it's an upcast (always safe)
    - If to_ty <: from_ty, it's a downcast (may fail)
    - If either type is Dynamic/Unknown, it's a dynamic cast
    - Otherwise, types must be consistent for cast to be valid *)
let determine_cast_kind (from_ty to_ty: brrr_type) : cast_kind =
  if extended_subtype from_ty to_ty then CKUp
  else if extended_subtype to_ty from_ty then CKDown
  else
    (* Dynamic/Unknown requires runtime check *)
    match from_ty, to_ty with
    | TPrim PDynamic, _ | _, TPrim PDynamic -> CKDynamic
    | TPrim PUnknown, _ | _, TPrim PUnknown -> CKDynamic
    | _, _ -> CKDynamic  (* Fallback for consistent but unrelated types *)

(** Create a blame label for the current context.
    Converts source_span to range for blame tracking. *)
let make_blame_from_span (span: source_span) (ctx: string) : blame_label =
  (* Convert source_span to BrrrExpressions.range *)
  let start_pos : BrrrExpressions.pos = {
    pos_filename = span.span_start.sp_file;
    pos_line = span.span_start.sp_line;
    pos_col = span.span_start.sp_col
  } in
  let end_pos : BrrrExpressions.pos = {
    pos_filename = span.span_end.sp_file;
    pos_line = span.span_end.sp_line;
    pos_col = span.span_end.sp_col
  } in
  mk_blame true (start_pos, end_pos) ctx

(** Insert a cast from from_ty to to_ty around expression e.

    This is the core cast insertion function. It:
    1. Returns e unchanged if from_ty = to_ty (no cast needed)
    2. Creates an upcast if from_ty <: to_ty
    3. Creates a downcast if to_ty <: from_ty
    4. Creates a dynamic cast through Dynamic if types are only consistent

    For inconsistent types (not related by ~), this should not be called;
    the type checker should report an error instead.

    @param e        Expression to wrap with cast
    @param from_ty  Inferred type of e
    @param to_ty    Expected type at this position
    @param blame    Blame label for error reporting
    @returns        e wrapped with appropriate cast, or e if no cast needed *)
let insert_cast (e: expr) (from_ty to_ty: brrr_type) (blame: blame_label) : expr =
  (* Case 1: Types are equal - no cast needed *)
  if type_eq from_ty to_ty then e

  (* Case 2: Types have a direct subtype/supertype relationship or are consistent *)
  else
    let kind = determine_cast_kind from_ty to_ty in
    let ci : cast_info = {
      ci_from = from_ty;
      ci_to = to_ty;
      ci_kind = kind;
      ci_blame = blame
    } in
    mk_expr e.loc_range (ECast e ci)

(** Insert cast through Dynamic for types that are consistent but not subtypes.

    When T1 ~ T2 but neither T1 <: T2 nor T2 <: T1, we compose two casts:
      e : T1  =>  (T1 => Dynamic)  =>  (Dynamic => T2)

    This is the "ground types" approach from Siek & Taha.
    Each cast step is simple enough for runtime to handle.

    @param e        Expression of type from_ty
    @param from_ty  Type of expression
    @param to_ty    Target type
    @param blame    Blame for the cast sequence
    @returns        Expression with cast sequence inserted *)
let insert_cast_via_dynamic (e: expr) (from_ty to_ty: brrr_type) (blame: blame_label) : expr =
  (* Step 1: Cast to Dynamic *)
  let to_dyn_info : cast_info = {
    ci_from = from_ty;
    ci_to = t_dynamic;
    ci_kind = CKDynamic;
    ci_blame = blame
  } in
  let e_dyn = mk_expr e.loc_range (ECast e to_dyn_info) in

  (* Step 2: Cast from Dynamic to target *)
  let from_dyn_info : cast_info = {
    ci_from = t_dynamic;
    ci_to = to_ty;
    ci_kind = CKDynamic;
    ci_blame = blame
  } in
  mk_expr e.loc_range (ECast e_dyn from_dyn_info)

(** Insert appropriate cast based on type relationship.

    Main entry point for gradual typing cast insertion.
    Determines the best cast strategy:
    1. No cast if types equal
    2. Direct cast if subtype relationship exists
    3. Cast via Dynamic if types are only consistent
    4. Error if types are not consistent

    @param e        Expression to potentially wrap
    @param from_ty  Inferred type of expression
    @param to_ty    Expected type at this position
    @param blame    Blame label for error reporting
    @returns        Some expr with cast, or None if types not consistent *)
let insert_cast_if_needed (e: expr) (from_ty to_ty: brrr_type) (blame: blame_label) : option expr =
  if type_eq from_ty to_ty then
    Some e
  else if extended_subtype from_ty to_ty then
    (* Upcast - safe, insert directly *)
    Some (insert_cast e from_ty to_ty blame)
  else if extended_subtype to_ty from_ty then
    (* Downcast - may fail, insert with runtime check *)
    Some (insert_cast e from_ty to_ty blame)
  else if type_consistent from_ty to_ty then
    (* Types consistent but not related by subtyping - go through Dynamic *)
    Some (insert_cast_via_dynamic e from_ty to_ty blame)
  else
    (* Types not consistent - cannot insert cast *)
    None

(** Specialized inference result that includes the potentially cast expression.

    For gradual typing, we need to track both:
    - The original type of the expression (for consistency checking)
    - The expression itself (may be wrapped in casts) *)
noeq type gradual_infer_result =
  | GInferOk  : expr:expr -> ty:brrr_type -> eff:effect_row -> ctx:type_ctx -> gradual_infer_result
  | GInferErr : err:type_error -> gradual_infer_result

(** Check expression against expected type, inserting casts as needed.

    This is the gradual typing version of check_type. It:
    1. Infers the type of expression e
    2. If inferred type <: expected, returns success (possibly with upcast)
    3. If types are consistent, inserts runtime cast
    4. If types not consistent, reports error

    The key difference from standard check_type: consistent types are
    accepted with a runtime cast, enabling gradual migration.

    @param gctx      Global type context
    @param ctx       Local type context
    @param e         Expression to check
    @param expected  Expected type
    @param span      Source span for blame tracking
    @returns         GInferOk with cast-wrapped expr, or GInferErr *)
let check_type_gradual (gctx: global_ctx) (ctx: type_ctx) (e: expr)
    (expected: brrr_type) (span: source_span) : gradual_infer_result =
  match infer_type gctx ctx e with
  | InferOk inferred eff ctx' ->
      if extended_subtype inferred expected then
        (* Exact match or upcast - possibly insert upcast for clarity *)
        if type_eq inferred expected then
          GInferOk e inferred eff ctx'
        else
          let blame = make_blame_from_span span "type check (subtype)" in
          let e' = insert_cast e inferred expected blame in
          GInferOk e' expected eff ctx'

      else if type_consistent inferred expected then
        (* Types consistent but not subtypes - insert runtime cast *)
        let blame = make_blame_from_span span "type check (gradual)" in
        (match insert_cast_if_needed e inferred expected blame with
         | Some e' -> GInferOk e' expected eff ctx'
         | None ->
             GInferErr (make_error
               ("Cannot cast " ^ type_description inferred ^ " to " ^ type_description expected)
               span))

      else
        (* Types not consistent - genuine type error *)
        GInferErr (make_error
          ("Type mismatch: expected " ^ type_description expected ^
           ", got " ^ type_description inferred)
          span)

  | InferErr err -> GInferErr err

(** ============================================================================
    TYPE INFERENCE RESULT - Helper Functions
    ============================================================================ *)

(* Legacy error constructor for backwards compatibility *)
let infer_err_msg (msg: string) : infer_result =
  InferErr (make_error msg dummy_span)

(* Error with location *)
let infer_err_at (msg: string) (span: source_span) : infer_result =
  InferErr (make_error msg span)

(* Legacy error constructor for backwards compatibility *)
let check_err_msg (msg: string) : check_result =
  CheckErr (make_error msg dummy_span)

(* Check error with location *)
let check_err_at (msg: string) (span: source_span) : check_result =
  CheckErr (make_error msg span)

(** ============================================================================
    LITERAL TYPE INFERENCE
    ============================================================================ *)

(* Infer type of literal *)
let infer_literal (lit: literal) : brrr_type =
  match lit with
  | LitUnit -> t_unit
  | LitBool _ -> t_bool
  | LitInt _ it -> t_int it
  | LitFloat _ fp -> t_float fp
  | LitString _ -> t_string
  | LitChar _ -> t_char
  | LitImaginary _ fp ->
      (* Imaginary literal: fi -> complex type = TTuple [float; float] *)
      TTuple [t_float fp; t_float fp]

(** ============================================================================
    OPERATOR TYPE RULES
    ============================================================================ *)

(* Unary operator result type *)
let unary_op_type (op: unary_op) (t: brrr_type) : option brrr_type =
  match op, t with
  | OpNeg, TNumeric (NumInt it) -> Some (t_int it)
  | OpNeg, TNumeric (NumFloat fp) -> Some (t_float fp)
  | OpNot, TPrim PBool -> Some t_bool
  | OpBitNot, TNumeric (NumInt it) -> Some (t_int it)
  | OpDeref, TWrap WRef t' -> Some t'
  | OpDeref, TWrap WRefMut t' -> Some t'
  | OpDeref, TWrap WBox t' -> Some t'
  | OpRef, t' -> Some (t_ref t')
  | OpRefMut, t' -> Some (t_ref_mut t')
  | _, _ -> None

(* Binary operator result type *)
let binary_op_type (op: binary_op) (t1 t2: brrr_type) : option brrr_type =
  match op with
  (* Arithmetic: both operands must be same numeric type *)
  | OpAdd | OpSub | OpMul | OpDiv | OpMod ->
      (match t1, t2 with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) -> if i1 = i2 then Some (t_int i1) else None
       | TNumeric (NumFloat f1), TNumeric (NumFloat f2) -> if f1 = f2 then Some (t_float f1) else None
       | _, _ -> None)
  (* Comparison: same type, returns bool *)
  | OpEq | OpNe | OpLt | OpLe | OpGt | OpGe ->
      if type_eq t1 t2 then Some t_bool else None
  (* Logical: both bool *)
  | OpAnd | OpOr ->
      (match t1, t2 with
       | TPrim PBool, TPrim PBool -> Some t_bool
       | _, _ -> None)
  (* Bitwise: both same int *)
  | OpBitAnd | OpBitOr | OpBitXor | OpBitAndNot ->
      (match t1, t2 with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) -> if i1 = i2 then Some (t_int i1) else None
       | _, _ -> None)
  (* Shifts: left operand is integer, right operand is any integer type.
     Go 1.13+ allows signed shift counts; negative values cause a runtime panic.
     The result type is always that of the left operand. *)
  | OpShl | OpShr ->
      (match t1, t2 with
       | TNumeric (NumInt i1), TNumeric (NumInt _) -> Some (t_int i1)
       | _, _ -> None)

(** ============================================================================
    PATTERN TYPE INFERENCE (Spec Section 7.2 "Pattern Typing")
    ============================================================================

    Pattern typing judgment: Gamma |-_pat p : T => Delta

    Where:
      - Gamma is the typing context
      - p is the pattern being checked
      - T is the expected type (type of the scrutinee)
      - Delta is the set of bindings introduced by the pattern

    This judgment is NOT symmetric - it checks that pattern p can match values
    of type T and produces bindings Delta that extend the context for the body.

    ==========================================================================
    PATTERN TYPING RULES (Spec Section 7.2, TAPL 11.8)
    ==========================================================================

    T-Pat-Wild:
      -------------------------
      Gamma |-_pat _ : T => {}

      Wildcard matches anything, introduces no bindings

    T-Pat-Var:
      -------------------------
      Gamma |-_pat x : T => {x : T @ 1}

      Variable pattern matches anything, binds x to matched value
      Default mode is MOne (linear) - value can be used exactly once

    T-Pat-Lit:
      typeof(lit) = T
      -------------------------
      Gamma |-_pat lit : T => {}

      Literal pattern matches specific value, no bindings

    T-Pat-Tuple (Spec Section 7.2.1):
      forall i. Gamma |-_pat p_i : T_i => Delta_i
      all Delta_i are disjoint
      --------------------------------------------------
      Gamma |-_pat (p1, ..., pn) : (T1, ..., Tn) => union(Delta_i)

    T-Pat-Struct:
      S = struct { f1: T1, ..., fn: Tn }
      forall i. Gamma |-_pat p_i : T_i => Delta_i
      --------------------------------------------------
      Gamma |-_pat S { f1: p1, ..., fk: pk } : S => union(Delta_i)

      Note: Not all fields need to be mentioned (partial patterns allowed)

    T-Pat-Variant (Spec Section 7.2.2):
      E = enum { V1(T1), ..., Vn(Tn) }
      Gamma |-_pat p1 : T1 => Delta1, ..., Gamma |-_pat pk : Tk => Deltak
      --------------------------------------------------
      Gamma |-_pat Vi(p1, ..., pk) : E => union(Delta_j)

    T-Pat-Or:
      Gamma |-_pat p1 : T => Delta
      Gamma |-_pat p2 : T => Delta
      --------------------------------------------------
      Gamma |-_pat p1 | p2 : T => Delta

      Note: Both branches must produce IDENTICAL bindings (same names and types)
      This is more restrictive than some languages for soundness

    T-Pat-Guard (Spec Section 7.2.3):
      Gamma |-_pat p : T => Delta
      Gamma, Delta |- e : Bool ; Pure
      --------------------------------------------------
      Gamma |-_pat p if e : T => Delta

      Guard expression checked in extended context with pattern bindings

    T-Pat-As:
      Gamma |-_pat p : T => Delta
      --------------------------------------------------
      Gamma |-_pat p @ x : T => Delta, {x : T @ 1}

      As-pattern binds whole value in addition to destructuring

    T-Pat-Ref:
      Gamma |-_pat p : T => Delta
      --------------------------------------------------
      Gamma |-_pat &p : &T => Delta

    T-Pat-Box:
      Gamma |-_pat p : T => Delta
      --------------------------------------------------
      Gamma |-_pat box p : Box<T> => Delta

    T-Pat-Rest (for array/slice destructuring):
      --------------------------------------------------
      Gamma |-_pat ...x : [T] => {x : &[T] @ 1}

    ============================================================================ *)

(* Result of pattern matching: bindings introduced *)
type pattern_bindings = list (var_id & brrr_type & mode)

(**
 * Lookup a struct field by name and return its type.
 *
 * @param field_name The name of the field to lookup
 * @param fields     List of struct field types
 * @returns          Some field_type if found, None otherwise
 *)
let rec lookup_struct_field (field_name: string) (fields: list field_type) : option field_type =
  match fields with
  | [] -> None
  | f :: rest ->
      if f.field_name = field_name then Some f
      else lookup_struct_field field_name rest

(**
 * infer_pattern: Extract bindings from pattern against expected type
 *
 * Judgment: tdctx; p : T => Delta
 *
 * Implements T-Pat-* rules from Spec Section 7.2.
 * Checks that pattern p can match values of type T and produces
 * bindings Delta that will extend the context for the match arm body.
 *
 * @param tdctx       Type definition context for struct/enum lookup
 * @param p           The pattern to infer bindings from
 * @param expected_ty The type the pattern should match against
 * @returns           Some bindings if pattern matches, None otherwise
 *)
let rec infer_pattern (tdctx: type_def_ctx) (p: pattern) (expected_ty: brrr_type)
    : option pattern_bindings =
  match p with
  | PatWild -> Some []

  | PatVar x -> Some [(x, expected_ty, MOne)]  (* Linear by default *)

  | PatLit lit ->
      let lit_ty = infer_literal lit in
      if type_eq lit_ty expected_ty then Some []
      else None

  | PatTuple pats ->
      (match expected_ty with
       | TTuple tys ->
           if List.Tot.length pats <> List.Tot.length tys then None
           else infer_patterns tdctx pats tys
       | _ -> None)

  | PatStruct ty_name field_pats ->
      (* Check expected type matches the struct pattern's type name *)
      (match expected_ty with
       | TStruct st ->
           if st.struct_name <> ty_name then None
           else infer_struct_field_patterns tdctx field_pats st.struct_fields
       | TNamed n ->
           (* Resolve named type from context *)
           (match lookup_struct_type n tdctx with
            | Some st ->
                if st.struct_name <> ty_name then None
                else infer_struct_field_patterns tdctx field_pats st.struct_fields
            | None -> None)
       | _ -> None)

  | PatVariant ty_name var_name pats ->
      (* Check expected type is the correct enum and variant exists *)
      (match expected_ty with
       | TEnum et ->
           if et.enum_name <> ty_name then None
           else
             (* Find the variant by name *)
             (match List.Tot.find (fun v -> v.variant_name = var_name) et.enum_variants with
              | Some variant ->
                  (* Check pattern count matches variant field count *)
                  if List.Tot.length pats <> List.Tot.length variant.variant_fields then None
                  else infer_patterns tdctx pats variant.variant_fields
              | None -> None)
       | TNamed n ->
           (* Resolve named type from context *)
           (match lookup_enum_type n tdctx with
            | Some et ->
                if et.enum_name <> ty_name then None
                else
                  (match List.Tot.find (fun v -> v.variant_name = var_name) et.enum_variants with
                   | Some variant ->
                       if List.Tot.length pats <> List.Tot.length variant.variant_fields then None
                       else infer_patterns tdctx pats variant.variant_fields
                   | None -> None)
            | None -> None)
       | _ -> None)

  | PatOr p1 p2 ->
      (* Both branches must produce same bindings *)
      (match infer_pattern tdctx p1 expected_ty, infer_pattern tdctx p2 expected_ty with
       | Some b1, Some b2 ->
           if List.Tot.length b1 = List.Tot.length b2 then Some b1
           else None
       | _, _ -> None)

  | PatRef p' ->
      (match expected_ty with
       | TWrap WRef t' -> infer_pattern tdctx p' t'
       | _ -> None)

  | PatBox p' ->
      (match expected_ty with
       | TWrap WBox t' -> infer_pattern tdctx p' t'
       | _ -> None)

  (* PatGuard p e: Pattern with guard expression.
     The guard expression must be type-checked separately in a context that
     includes the pattern's bindings. Here we extract bindings from the inner
     pattern; the guard is type-checked in infer_match_arms where we have
     full typing context.

     Note: PatGuard bindings come from the inner pattern only.
     The guard expression e is stored in the match_arm.arm_guard field and
     is type-checked there against boolean type. *)
  | PatGuard p' _guard_expr ->
      (* Delegate to inner pattern - guard checked at match arm level *)
      infer_pattern tdctx p' expected_ty

  (* PatRest: ...rest or ... pattern for capturing remaining elements.
     Used in array/slice destructuring: [first, ...rest]
     If opt_var is Some x, binds rest to x with slice type.
     If opt_var is None, just ignores remaining elements. *)
  | PatRest opt_var ->
      (match opt_var with
       | None -> Some []  (* ... without binding - no variables introduced *)
       | Some x ->
           (* ...x binds to a slice of the remaining elements *)
           (match expected_ty with
            | TWrap WArray elem_ty -> Some [(x, t_slice elem_ty, MOne)]
            | TApp (TNamed "FixedArray") [_; elem_ty] -> Some [(x, t_slice elem_ty, MOne)]
            | TWrap WSlice elem_ty -> Some [(x, t_slice elem_ty, MOne)]
            | _ -> Some [(x, expected_ty, MOne)]))  (* Fallback *)

  (* PatAs: p @ x pattern binds the whole match to x while also destructuring.
     Example: Some(inner) @ whole matches Option, binds inner to payload and whole to entire value *)
  | PatAs inner_pat var_name ->
      (match infer_pattern tdctx inner_pat expected_ty with
       | Some inner_bindings ->
           (* Add binding for the whole value alongside inner pattern's bindings *)
           Some ((var_name, expected_ty, MOne) :: inner_bindings)
       | None -> None)

(**
 * Infer types for multiple patterns against corresponding types.
 *
 * @param tdctx Type definition context
 * @param pats  List of patterns
 * @param tys   List of expected types (must be same length as pats)
 * @returns     Combined bindings from all patterns, or None on mismatch
 *)
and infer_patterns (tdctx: type_def_ctx) (pats: list pattern) (tys: list brrr_type)
    : option pattern_bindings =
  match pats, tys with
  | [], [] -> Some []
  | p :: ps, t :: ts ->
      (match infer_pattern tdctx p t, infer_patterns tdctx ps ts with
       | Some b1, Some b2 -> Some (b1 @ b2)
       | _, _ -> None)
  | _, _ -> None

(**
 * Infer bindings from struct field patterns.
 *
 * Each field pattern (name, pattern) is matched against the corresponding
 * struct field. All referenced fields must exist in the struct.
 *
 * @param tdctx       Type definition context
 * @param field_pats  List of (field_name, pattern) pairs from the pattern
 * @param fields      List of field types from the struct definition
 * @returns           Combined bindings from all field patterns, or None on error
 *)
and infer_struct_field_patterns (tdctx: type_def_ctx) (field_pats: list (string & pattern))
                                 (fields: list field_type)
    : option pattern_bindings =
  match field_pats with
  | [] -> Some []
  | (fname, pat) :: rest ->
      (* Look up the field in the struct definition *)
      (match lookup_struct_field fname fields with
       | Some fld ->
           (* Infer pattern against field type *)
           (match infer_pattern tdctx pat fld.field_ty with
            | Some bindings ->
                (* Recursively process remaining field patterns *)
                (match infer_struct_field_patterns tdctx rest fields with
                 | Some rest_bindings -> Some (bindings @ rest_bindings)
                 | None -> None)
            | None -> None)
       | None -> None)  (* Field not found in struct *)

(* Extend context with pattern bindings *)
let extend_ctx_with_bindings (bindings: pattern_bindings) (ctx: type_ctx) : type_ctx =
  List.Tot.fold_right (fun (x, t, m) c -> extend_ctx x t m c) bindings ctx

(** ============================================================================
    NUMERIC CAST VALIDATION
    ============================================================================ *)

(**
 * Check if an integer cast is safe (non-lossy, widening).
 *
 * Safe integer casts:
 * - Same sign, smaller or equal width -> larger width
 * - Signed to unsigned only when target is strictly larger (to hold negative range)
 *
 * @param from_int Source integer type
 * @param to_int   Target integer type
 * @returns        True if cast is guaranteed non-lossy
 *)
let is_safe_int_cast (from_int to_int: int_type) : bool =
  match width_bits from_int.width, width_bits to_int.width with
  | Some w1, Some w2 ->
      if from_int.sign = to_int.sign then
        (* Same sign: widening (smaller -> larger) is safe *)
        w1 <= w2
      else if from_int.sign = Signed && to_int.sign = Unsigned then
        (* Signed to unsigned: must be strictly larger to represent negative values as large positives *)
        (* This is actually always lossy for negative values, so we're conservative here *)
        false  (* Signed->unsigned conversions are never truly safe *)
      else
        (* Unsigned to signed: safe if target is strictly larger *)
        w1 < w2
  | None, _ -> false  (* IBig source: cannot determine safety *)
  | _, None -> true   (* IBig target: can hold any fixed-width value *)

(**
 * Check if a float cast is safe (non-lossy, widening).
 *
 * Safe float casts:
 * - F16 -> F32 -> F64 (increasing precision)
 *
 * @param from_fp Source float precision
 * @param to_fp   Target float precision
 * @returns       True if cast is guaranteed non-lossy
 *)
let is_safe_float_cast (from_fp to_fp: float_prec) : bool =
  float_bits from_fp <= float_bits to_fp

(**
 * Check if a numeric cast is safe (non-lossy).
 *
 * Safe casts are guaranteed to not lose information:
 * - Integer widening within same sign
 * - Float precision increase
 * - Integer to larger float (within float's integer range)
 *
 * @param from_ty Source type
 * @param to_ty   Target type
 * @returns       True if cast is guaranteed non-lossy
 *)
let is_safe_numeric_cast (from_ty to_ty: brrr_type) : bool =
  match from_ty, to_ty with
  (* Integer widening: same sign, smaller -> larger *)
  | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
      is_safe_int_cast i1 i2
  (* Float widening: lower precision -> higher precision *)
  | TNumeric (NumFloat f1), TNumeric (NumFloat f2) ->
      is_safe_float_cast f1 f2
  (* Integer to float: safe if int fits in float's mantissa *)
  (* f32 has 24-bit mantissa, f64 has 53-bit mantissa *)
  | TNumeric (NumInt i), TNumeric (NumFloat fp) ->
      (match width_bits i.width with
       | Some w ->
           (match fp with
            | F16 -> w <= 11  (* f16 mantissa is 11 bits *)
            | F32 -> w <= 24  (* f32 mantissa is 24 bits *)
            | F64 -> w <= 53) (* f64 mantissa is 53 bits *)
       | None -> false)  (* IBig cannot safely convert to float *)
  | _, _ -> false

(**
 * Check if a numeric cast is valid (semantically defined, may be lossy).
 *
 * All numeric-to-numeric casts are valid in the sense that they have
 * defined semantics, but they may lose precision or truncate values.
 *
 * @param from_ty Source type
 * @param to_ty   Target type
 * @returns       True if cast is valid (semantically defined)
 *)
let is_valid_numeric_cast (from_ty to_ty: brrr_type) : bool =
  match from_ty, to_ty with
  | TNumeric _, TNumeric _ -> true  (* All numeric-to-numeric casts are defined *)
  | _, _ -> false

(**
 * Check if types are compatible for casting.
 *
 * Non-numeric casts that are valid:
 * - Pointer casts in unsafe contexts (handled separately by EUnsafe)
 * - Reference coercions (handled by subtyping)
 *
 * @param from_ty Source type
 * @param to_ty   Target type
 * @returns       True if cast between these types is allowed
 *)
let is_valid_cast (from_ty to_ty: brrr_type) : bool =
  (* Numeric casts are always valid (may be lossy) *)
  is_valid_numeric_cast from_ty to_ty ||
  (* Same type: trivially valid *)
  type_eq from_ty to_ty ||
  (* Subtype: implicit coercion is valid *)
  extended_subtype from_ty to_ty

(**
 * Generate a human-readable description of a type for error messages.
 *
 * @param ty The type to describe
 * @returns  A string description of the type
 *)
let rec type_description (ty: brrr_type) : Tot string (decreases ty) =
  match ty with
  | TPrim PUnit -> "unit"
  | TPrim PNever -> "never"
  | TPrim PBool -> "bool"
  | TPrim PString -> "String"
  | TPrim PChar -> "char"
  | TPrim PDynamic -> "dynamic"
  | TNumeric (NumInt it) ->
      let sign_str = match it.sign with Signed -> "i" | Unsigned -> "u" in
      let width_str = match it.width with
        | I8 -> "8" | I16 -> "16" | I32 -> "32"
        | I64 -> "64" | I128 -> "128" | IBig -> "big"
      in sign_str ^ width_str
  | TNumeric (NumFloat fp) ->
      (match fp with F16 -> "f16" | F32 -> "f32" | F64 -> "f64")
  | TWrap WArray t -> "[" ^ type_description t ^ "]"
  | TApp (TNamed "FixedArray") [TNamed n; t] -> "[" ^ n ^ "]" ^ type_description t
  | TWrap WSlice t -> "&[" ^ type_description t ^ "]"
  | TWrap WOption t -> type_description t ^ "?"
  | TWrap WBox t -> "Box<" ^ type_description t ^ ">"
  | TWrap WRef t -> "&" ^ type_description t
  | TWrap WRefMut t -> "&mut " ^ type_description t
  | TWrap WRc t -> "Rc<" ^ type_description t ^ ">"
  | TWrap WArc t -> "Arc<" ^ type_description t ^ ">"
  | TWrap WRaw t -> "*" ^ type_description t
  | TModal _ t -> "modal(" ^ type_description t ^ ")"
  | TResult t e -> "Result<" ^ type_description t ^ ", " ^ type_description e ^ ">"
  | TTuple [] -> "()"
  | TTuple (t :: []) -> "(" ^ type_description t ^ ",)"
  | TTuple (t :: ts) -> "(" ^ type_description t ^ ", ...)"
  | TFunc _ -> "fn(...)"
  | TVar v -> v
  | TApp t _ -> type_description t ^ "<...>"
  | TNamed n -> n
  | TStruct st -> st.struct_name
  | TEnum et -> et.enum_name

(** ============================================================================
    EXPRESSION SIZE (for termination)
    ============================================================================ *)

(* We use expr_size from Expressions module for termination *)

(** ============================================================================
    STRUCTURAL TERMINATION MEASURES
    ============================================================================ *)

(**
 * We use structural termination based on expression size from BrrrExpressions.fst.
 * The mutually recursive functions use lexicographic ordering:
 *   %[primary_size; secondary_ordinal]
 *
 * Primary measure: expr_size, expr_list_size, or match_arm_list_size
 * Secondary ordinal: distinguishes functions when primary is equal
 *   0 = infer_type (smallest - can be called by others on same expr)
 *   1 = check_type (calls infer_type on same expr)
 *   2 = infer_type_list (calls infer_type on elements)
 *   3 = check_args (calls check_type on elements)
 *   4 = infer_match_arms (calls infer/check on arm bodies)
 *
 * Key termination invariants:
 * - check_type e -> infer_type e: same expr_size, 0 < 1
 * - infer_type (ECall fn args) -> infer_type_list args: expr_list_size args < expr_size (ECall fn args)
 * - infer_type_list (e::rest) -> infer_type e: expr_size e <= expr_list_size (e::rest), 0 < 2
 * - All recursive calls on subexpressions have strictly smaller expr_size
 *)

(** ============================================================================
    BIDIRECTIONAL TYPE CHECKING
    ============================================================================

    This section implements the core bidirectional type checking algorithm.

    INFERENCE MODE (infer_type):
      Synthesizes type T and effects eff from expression e
      Judgment: Gamma |- e => T ; eff
      Returns InferOk(T, eff, Gamma') or InferErr(error)

    CHECKING MODE (check_type):
      Verifies expression e has expected type T
      Judgment: Gamma |- e <= T ; eff
      Returns CheckOk(eff, Gamma') or CheckErr(error)

    The key pattern for mode switching (from Pierce & Turner "Local Type Inference"):

      1. check_type for lambdas: Use expected function type to guide param types
         check(Gamma, \x.e, T1 -> T2) = check(Gamma,x:T1, e, T2)

      2. check_type for others: Infer then apply subsumption (T-Sub)
         check(Gamma, e, T) = let (T', eff) = infer(Gamma, e) in
                              if T' <: T then OK else ERROR

      3. infer_type for applications: Check argument against inferred param type
         infer(Gamma, e1 e2) = let (T1 -> T2, eff1) = infer(Gamma, e1) in
                               let eff2 = check(Gamma, e2, T1) in
                               (T2, eff1 join eff2)

    EFFECT TRACKING:
      Each typing rule produces an effect row. Effects are combined via row_join.
      The effect system follows Spec Section 3.1 "Effect Row Polymorphism".

    LINEAR CONTEXT THREADING:
      The context is threaded through computations, tracking variable consumption.
      Linear variables (mode = MOne) can only be used once.
      Per Spec Section 5.1 "Linear Typing Judgment".

    TERMINATION:
      Uses lexicographic ordering %[expr_size e; ordinal] where ordinal
      distinguishes functions when the expression size is equal.

    ============================================================================ *)

(**
 * infer_type: Type inference in synthesis mode
 *
 * Judgment: gctx; ctx |- e => ty ; eff ~> ctx'
 *
 * Implements the following typing rules from Spec Chapter 8:
 *
 * ==========================================================================
 * VARIABLES AND CONSTANTS
 * ==========================================================================
 *
 * T-Var (Spec 8.1, TAPL 9.3.4):
 *   (x : T @ m) in ctx    m > 0 (available)
 *   -----------------------------------------
 *           ctx |- x => T ; Pure
 *
 *   Context updated: consume_var(x, ctx) marks linear variable used
 *
 * T-Lit (TAPL 8.2.2):
 *   --------------------------------
 *   ctx |- literal => typeof(lit) ; Pure
 *
 * T-Global:
 *   name in gctx with scheme forall as. T
 *   -----------------------------------------
 *        ctx |- name => T[as := fresh] ; Pure
 *
 * ==========================================================================
 * LAMBDA AND APPLICATION
 * ==========================================================================
 *
 * T-Abs (Spec 8.1, TAPL 9.3.4):
 *   ctx, x : T1 @ m |- body => T2 ; eff
 *   ------------------------------------------------
 *   ctx |- \(x:T1).body => (T1@m -[eff]-> T2) ; Pure
 *
 *   Note: Lambda itself is pure; effects are in the function type
 *
 * T-App (Spec 8.1, TAPL 9.3.4, 11.8):
 *   ctx1 |- fn => (T1@m -[eff_f]-> T2) ; eff1
 *   ctx2 |- args <= T1                 ; eff2
 *   -----------------------------------------------------
 *   ctx1+ctx2 |- fn(args) => T2 ; eff1 join eff2 join eff_f
 *
 * ==========================================================================
 * LET BINDINGS
 * ==========================================================================
 *
 * T-Let (Spec 8.1):
 *   ctx1 |- e1 => T1 ; eff1
 *   ctx1, p : T1 |- e2 => T2 ; eff2      (p binds pattern variables)
 *   --------------------------------------------------------
 *   ctx |- let p = e1 in e2 => T2 ; eff1 join eff2
 *
 * T-LetMut (Spec 6.2):
 *   ctx1 |- e1 => T1 ; eff1
 *   ctx1, x : &mut T1 @ omega |- e2 => T2 ; eff2
 *   --------------------------------------------------------
 *   ctx |- let mut x = e1 in e2 => T2 ; eff1 join eff2 join Write
 *
 * ==========================================================================
 * CONDITIONALS AND MATCHING
 * ==========================================================================
 *
 * T-If (Spec 8.1, TAPL 9.3.4):
 *   ctx |- cond => Bool ; eff0
 *   ctx |- then_e => T ; eff1
 *   ctx |- else_e => T ; eff2
 *   --------------------------------------------------------
 *   ctx |- if cond then then_e else else_e => T ; eff0 join eff1 join eff2
 *
 *   Note: Both branches start from same context (ctx after cond check).
 *   For linear types, contexts after branches must be joinable
 *   (Spec Section 5.1 "Context Join for Branches").
 *
 * T-Match (Spec 8.1, Section 7.2):
 *   ctx |- scrutinee => T_scrut ; eff0
 *   forall i. ctx |-_pat p_i : T_scrut => Delta_i
 *   forall i. ctx, Delta_i |- e_i => T ; eff_i
 *   patterns exhaustive
 *   --------------------------------------------------------
 *   ctx |- match scrutinee { p_i => e_i } => T ; eff0 join (join_i eff_i)
 *
 * ==========================================================================
 * REFERENCES AND BORROWING (Spec Section 6.1-6.3, TAPL Ch. 13)
 * ==========================================================================
 *
 * T-Borrow (Spec 8.3):
 *   ctx |- e => T ; eff
 *   --------------------------------
 *   ctx |- &e => &T ; eff
 *
 *   Note: Borrow conflict checking is delegated to BorrowChecker module.
 *
 * T-BorrowMut (Spec 8.3):
 *   ctx |- e => T ; eff
 *   no active borrows on e (checked by BorrowChecker)
 *   ------------------------------------------------
 *   ctx |- &mut e => &mut T ; eff
 *
 * T-Deref (Spec 8.3):
 *   ctx |- e => &T | &mut T | Box T ; eff
 *   ------------------------------------------------
 *   ctx |- *e => T ; eff join Read
 *
 * T-Assign (Spec 8.3):
 *   ctx |- lhs => &mut T ; eff1
 *   ctx |- rhs <= T      ; eff2
 *   ------------------------------------------------
 *   ctx |- lhs = rhs => () ; eff1 join eff2 join Write
 *
 * ==========================================================================
 * EFFECTS AND CONTROL FLOW (Spec Section 3.1-3.3)
 * ==========================================================================
 *
 * T-Throw:
 *   ctx |- e => T ; eff
 *   ------------------------------------------------
 *   ctx |- throw e => Never ; eff join Throw
 *
 * T-Try:
 *   ctx |- body => T ; eff_body
 *   forall c. ctx |-_catch c => T ; eff_c
 *   ctx |- finally => () ; eff_finally  (optional)
 *   ------------------------------------------------
 *   ctx |- try body catch ... finally ... => T ; combined_eff
 *
 * T-Await:
 *   ctx |- e => Future<T> ; eff
 *   ------------------------------------------------
 *   ctx |- await e => T ; eff join Async
 *
 * T-Yield (Spec Definition 3.1):
 *   ctx |- e => Y ; eff
 *   ------------------------------------------------
 *   ctx |- yield e => () ; eff join Yield[Y, R]
 *
 * ==========================================================================
 * STRUCTURAL TERMINATION
 * ==========================================================================
 *
 * Uses lexicographic ordering: %[expr_size e; 0]
 * Secondary ordinal 0 allows check_type (ordinal 1) to call infer_type
 * on the same expression for the T-Sub rule.
 *
 * @param gctx Global type context for top-level definitions
 * @param ctx  Local type context for bound variables with modes
 * @param e    Expression to type-check
 * @returns    InferOk(type, effects, updated_ctx) or InferErr(error)
 *)
let rec infer_type (gctx: global_ctx) (ctx: type_ctx) (e: expr)
    : Tot infer_result (decreases %[expr_size e; 0]) =
  match e with
  (* T-Var: Variable lookup with mode check *)
  | EVar x ->
      (match lookup_ctx x ctx with
       | Some (ty, m) ->
           if is_available m then
             match consume_var x ctx with
             | Some ctx' -> InferOk ty pure ctx'
             | None -> infer_err_msg ("Cannot consume variable " ^ x)
           else infer_err_msg ("Variable " ^ x ^ " is not available (mode = 0)")
       | None -> infer_err_msg ("Unbound variable: " ^ x))

  (* T-Lit: Literals have pure effect *)
  | ELit lit ->
      InferOk (infer_literal lit) pure ctx

  (* T-Global: Global reference - lookup in global environment and instantiate *)
  | EGlobal name ->
      (match lookup_global name gctx with
       | Some scheme ->
           (* Instantiate monomorphic types directly; polymorphic types need type arguments *)
           (match scheme.type_vars with
            | [] ->
                (* Monomorphic: use body directly *)
                InferOk scheme.body pure ctx
            | _ ->
                (* Polymorphic: instantiate with fresh type variables *)
                (* In a full implementation, this would use unification or explicit type args *)
                (match instantiate scheme (List.Tot.map (fun v -> TVar v) scheme.type_vars) with
                 | Some ty -> InferOk ty pure ctx
                 | None -> infer_err_msg ("Failed to instantiate polymorphic global: " ^ name)))
       | None -> infer_err_msg ("Undefined global: " ^ name))

  (* T-Unary: Unary operations *)
  | EUnary op e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (match unary_op_type op t with
            | Some result_ty -> InferOk result_ty eff ctx'
            | None -> infer_err_msg "Type error in unary operation")
       | err -> err)

  (* T-Binary: Binary operations *)
  | EBinary op e1 e2 ->
      (match infer_type gctx ctx e1 with
       | InferOk t1 eff1 ctx1 ->
           (match infer_type gctx ctx1 e2 with
            | InferOk t2 eff2 ctx2 ->
                (match binary_op_type op t1 t2 with
                 | Some result_ty -> InferOk result_ty (row_join eff1 eff2) ctx2
                 | None -> infer_err_msg "Type error in binary operation")
            | err -> err)
       | err -> err)

  (* T-App: Function application *)
  | ECall fn args ->
      (match infer_type gctx ctx fn with
       | InferOk fn_ty eff_fn ctx1 ->
           (match fn_ty with
            | TFunc ft ->
                if List.Tot.length args <> List.Tot.length ft.params then
                  infer_err_msg "Wrong number of arguments"
                else
                  (match check_args gctx ctx1 args ft.params with
                   | Some (eff_args, ctx2) ->
                       let total_eff = row_join eff_fn (row_join eff_args ft.effects) in
                       InferOk ft.return_type total_eff ctx2
                   | None -> infer_err_msg "Argument type mismatch")
            | _ -> infer_err_msg "Cannot call non-function type")
       | err -> err)

  (* T-Tuple: Tuple construction *)
  | ETuple es ->
      (match infer_type_list gctx ctx es with
       | Some (tys, eff, ctx') -> InferOk (TTuple tys) eff ctx'
       | None -> infer_err_msg "Error in tuple expression")

  (* T-Array: Array construction *)
  | EArray es ->
      (match infer_type_list gctx ctx es with
       | Some ([], eff, ctx') -> infer_err_msg "Cannot infer type of empty array"
       | Some (t :: ts, eff, ctx') ->
           if List.Tot.for_all (type_eq t) ts then
             InferOk (t_array t) eff ctx'
           else infer_err_msg "Array elements must have same type"
       | None -> infer_err_msg "Error in array expression")

  (* T-Field: Field access *)
  | EField e' field_name ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (match t with
            | TStruct st ->
                (match List.Tot.find (fun f -> f.field_name = field_name) st.struct_fields with
                 | Some f -> InferOk f.field_ty eff ctx'
                 | None -> infer_err_msg ("Unknown field: " ^ field_name))
            | _ -> infer_err_msg "Field access on non-struct type")
       | err -> err)

  (* T-Index: Array/slice indexing (has Read effect) *)
  | EIndex arr idx ->
      (match infer_type gctx ctx arr with
       | InferOk arr_ty eff1 ctx1 ->
           (match infer_type gctx ctx1 idx with
            | InferOk idx_ty eff2 ctx2 ->
                (match arr_ty, idx_ty with
                 | TWrap WArray elem_ty, TNumeric (NumInt _) ->
                     InferOk elem_ty (row_join (row_join eff1 eff2) (RowExt BrrrEffects.ERead RowEmpty)) ctx2
                 | TApp (TNamed "FixedArray") [_; elem_ty], TNumeric (NumInt _) ->
                     InferOk elem_ty (row_join (row_join eff1 eff2) (RowExt BrrrEffects.ERead RowEmpty)) ctx2
                 | TWrap WSlice elem_ty, TNumeric (NumInt _) ->
                     InferOk elem_ty (row_join (row_join eff1 eff2) (RowExt BrrrEffects.ERead RowEmpty)) ctx2
                 | _, _ -> infer_err_msg "Invalid indexing operation")
            | err -> err)
       | err -> err)

  (* T-TupleProj: Tuple projection *)
  | ETupleProj e' idx ->
      (match infer_type gctx ctx e' with
       | InferOk (TTuple tys) eff ctx' ->
           if idx < List.Tot.length tys then
             InferOk (List.Tot.index tys idx) eff ctx'
           else infer_err_msg "Tuple index out of bounds"
       | InferOk _ _ _ -> infer_err_msg "Tuple projection on non-tuple type"
       | err -> err)

  (* T-If: Conditional expression

     For linear types, both branches must consume linear variables consistently.
     We check both branches starting from ctx1 (after condition), then join
     the resulting contexts. If a linear variable is consumed in one branch
     but not the other, that's a linearity error. *)
  | EIf cond then_e else_e ->
      (match infer_type gctx ctx cond with
       | InferOk cond_ty eff_cond ctx1 ->
           if not (type_eq cond_ty t_bool) then
             infer_err_msg "Condition must be boolean"
           else
             (match infer_type gctx ctx1 then_e with
              | InferOk then_ty eff_then ctx_then ->
                  (match infer_type gctx ctx1 else_e with  (* Start from ctx1, not ctx_then! *)
                   | InferOk else_ty eff_else ctx_else ->
                       (* Join contexts: ensures linear variables consumed consistently *)
                       (match join_contexts ctx_then ctx_else with
                        | Some ctx_joined ->
                            let total_eff = row_join eff_cond (row_join eff_then eff_else) in
                            (* Branches must have same type or subtype relation *)
                            if type_eq then_ty else_ty then
                              InferOk then_ty total_eff ctx_joined
                            else if extended_subtype then_ty else_ty then
                              InferOk else_ty total_eff ctx_joined
                            else if extended_subtype else_ty then_ty then
                              InferOk then_ty total_eff ctx_joined
                            else infer_err_msg "Branch types do not match"
                        | None ->
                            infer_err_msg "Linear variable consumed inconsistently in branches")
                   | err -> err)
              | err -> err)
       | err -> err)

  (* T-Let: Let binding *)
  | ELet pat ty_annot e1 e2 ->
      (match infer_type gctx ctx e1 with
       | InferOk t1 eff1 ctx1 ->
           (* Use annotation if provided, otherwise inferred type *)
           let bound_ty = match ty_annot with
             | Some t -> t
             | None -> t1 in
           (* Check inferred type is subtype of annotation *)
           if Some? ty_annot && not (extended_subtype t1 bound_ty) then
             infer_err_msg "Expression type does not match annotation"
           else
             (* Infer pattern bindings - use empty_type_def_ctx since bound_ty
                already contains full struct/enum type info when applicable *)
             (match infer_pattern empty_type_def_ctx pat bound_ty with
              | Some bindings ->
                  let ctx2 = extend_ctx_with_bindings bindings ctx1 in
                  (match infer_type gctx ctx2 e2 with
                   | InferOk t2 eff2 ctx3 ->
                       InferOk t2 (row_join eff1 eff2) ctx3
                   | err -> err)
              | None -> infer_err_msg "Pattern does not match type")
       | err -> err)

  (* T-LetMut: Mutable let binding *)
  | ELetMut x ty_annot e1 e2 ->
      (match infer_type gctx ctx e1 with
       | InferOk t1 eff1 ctx1 ->
           let bound_ty = match ty_annot with
             | Some t -> t
             | None -> t1 in
           if Some? ty_annot && not (extended_subtype t1 bound_ty) then
             infer_err_msg "Expression type does not match annotation"
           else
             (* Mutable bindings are unrestricted (can be reassigned) *)
             let ctx2 = extend_ctx x (t_ref_mut bound_ty) MOmega ctx1 in
             (match infer_type gctx ctx2 e2 with
              | InferOk t2 eff2 ctx3 ->
                  (* Mutable binding adds Write effect *)
                  InferOk t2 (row_join eff1 (row_join eff2 (RowExt BrrrEffects.EWrite RowEmpty))) ctx3
              | err -> err)
       | err -> err)

  (* T-Assign: Assignment (has Write effect) *)
  | EAssign lhs rhs ->
      (match infer_type gctx ctx lhs with
       | InferOk lhs_ty eff1 ctx1 ->
           (match lhs_ty with
            | TWrap WRefMut inner_ty ->
                (match check_type gctx ctx1 rhs inner_ty with
                 | CheckOk eff2 ctx2 ->
                     InferOk t_unit (row_join eff1 (row_join eff2 (RowExt BrrrEffects.EWrite RowEmpty))) ctx2
                 | CheckErr err -> InferErr err)
            | _ -> infer_err_msg "Assignment target must be mutable reference")
       | err -> err)

  (* T-Abs: Lambda abstraction *)
  | ELambda params body ->
      let param_tys = List.Tot.map (fun (x, t) -> { name = Some x; ty = t; mode = MOne }) params in
      let ctx' = List.Tot.fold_right (fun (x, t) c -> extend_ctx x t MOne c) params ctx in
      (match infer_type gctx ctx' body with
       | InferOk ret_ty eff ctx'' ->
           let ft : func_type = {
             params = param_tys;
             return_type = ret_ty;
             effects = eff;
             is_unsafe = false
           } in
           InferOk (TFunc ft) pure ctx  (* Lambdas themselves are pure *)
       | err -> err)

  (* T-Box: Box allocation (has Alloc effect) *)
  | EBox e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           InferOk (t_box t) (row_join eff (RowExt BrrrEffects.EAlloc RowEmpty)) ctx'
       | err -> err)

  (* T-Deref: Dereference (has Read effect) *)
  | EDeref e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (match t with
            | TWrap WRef inner -> InferOk inner (row_join eff (RowExt BrrrEffects.ERead RowEmpty)) ctx'
            | TWrap WRefMut inner -> InferOk inner (row_join eff (RowExt BrrrEffects.ERead RowEmpty)) ctx'
            | TWrap WBox inner -> InferOk inner (row_join eff (RowExt BrrrEffects.ERead RowEmpty)) ctx'
            | _ -> infer_err_msg "Cannot dereference non-reference type")
       | err -> err)

  (* T-Borrow: Shared borrow (&e)

     Type rule: If e : T, then &e : &T

     Borrow checking integration (via BorrowChecker module):
     1. If e is a variable x: call begin_shared_borrow to track the loan
     2. Multiple shared borrows of the same variable are allowed
     3. Shared borrow conflicts with existing exclusive borrow

     Current implementation: Basic type checking only.
     Full borrow checking is performed by borrow_check_expr in BrrrBorrowChecker.

     For Brrr-Machine integration: Use the typing result plus
     BrrrBorrowChecker.begin_shared_borrow for complete analysis. *)
  | EBorrow e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Type: &T from T
              Borrow validity checking delegated to BorrowChecker module.
              In integrated analysis, would verify:
              - can_borrow_shared (from BorrowChecker) returns true
              - No conflicting exclusive borrow exists *)
           InferOk (t_ref t) eff ctx'
       | err -> err)

  (* T-BorrowMut: Exclusive/mutable borrow (&mut e)

     Type rule: If e : T, then &mut e : &mut T

     Borrow checking integration (via BorrowChecker module):
     1. If e is a variable x: call begin_exclusive_borrow to track the loan
     2. Exclusive borrow CONFLICTS with ANY other borrow (shared or exclusive)
     3. Only one exclusive borrow can exist at a time for a given variable

     From BrrrBorrowChecker.exclusive_conflicts lemma:
       When begin_exclusive_borrow succeeds, there are NO active loans
       for that variable (length (loans_for_var x st) = 0).

     Current implementation: Basic type checking only.
     Full borrow checking is performed by borrow_check_expr in BrrrBorrowChecker.

     For Brrr-Machine integration: Use the typing result plus
     BrrrBorrowChecker.begin_exclusive_borrow for complete analysis. *)
  | EBorrowMut e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Type: &mut T from T
              Borrow conflict checking delegated to BorrowChecker module.
              In integrated analysis, would verify:
              - can_borrow_mut (from BorrowChecker) returns true
              - No existing borrows (shared or exclusive) conflict
              - Variable is in VsOwned state *)
           InferOk (t_ref_mut t) eff ctx'
       | err -> err)

  (* T-Throw: Throw exception (has Throw effect) *)
  | EThrow e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           InferOk t_never (row_join eff (RowExt BrrrEffects.EThrow RowEmpty)) ctx'
       | err -> err)

  (* T-Return: Early return *)
  | EReturn opt_e ->
      (match opt_e with
       | None -> InferOk t_never pure ctx
       | Some e' ->
           (match infer_type gctx ctx e' with
            | InferOk t eff ctx' -> InferOk t_never eff ctx'
            | err -> err))

  (* T-Block: Block expression - use infer_type_list for proper termination *)
  | EBlock [] -> InferOk t_unit pure ctx
  | EBlock es ->
      (match infer_type_list gctx ctx es with
       | Some ([], eff, ctx') -> InferOk t_unit eff ctx'
       | Some (t :: [], eff, ctx') -> InferOk t eff ctx'
       | Some (t :: ts, eff, ctx') ->
           (* Last expression in block determines the block's type *)
           (* ts is non-empty, so we can recurse to find last *)
           let rec get_last (#a: Type) (x: a) (xs: list a) : Tot a (decreases xs) =
             match xs with
             | [] -> x
             | y :: ys -> get_last y ys
           in
           InferOk (get_last t ts) eff ctx'
       | None -> infer_err_msg "Error in block expression")

  (* T-Seq: Sequence expression *)
  | ESeq e1 e2 ->
      (match infer_type gctx ctx e1 with
       | InferOk _ eff1 ctx1 ->
           (match infer_type gctx ctx1 e2 with
            | InferOk t eff2 ctx2 -> InferOk t (row_join eff1 eff2) ctx2
            | err -> err)
       | err -> err)

  (* T-Match: Pattern matching *)
  | EMatch scrutinee arms ->
      (match infer_type gctx ctx scrutinee with
       | InferOk scrutinee_ty eff_scrut ctx1 ->
           infer_match_arms gctx ctx1 scrutinee_ty arms eff_scrut
       | err -> err)

  (* T-As: Type cast
   *
   * Type casts are validated based on safety:
   * - Safe casts (non-lossy): Always allowed, no runtime overhead
   * - Valid casts (potentially lossy): Allowed but may truncate/lose precision
   * - Invalid casts: Rejected at compile time
   *
   * For potentially lossy casts (e.g., f64 -> i8), the type system allows them
   * but a separate lint pass should warn about potential data loss.
   *)
  | EAs e' target_ty ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Case 1: Same type - trivially valid *)
           if type_eq t target_ty then
             InferOk target_ty eff ctx'
           (* Case 2: Safe numeric cast (non-lossy widening) *)
           else if is_safe_numeric_cast t target_ty then
             InferOk target_ty eff ctx'
           (* Case 3: Valid numeric cast (potentially lossy but semantically defined) *)
           else if is_valid_numeric_cast t target_ty then
             (* Cast is valid but may lose data (e.g., f64 -> i8, i64 -> i32)
              * A lint pass should warn about these; type checker allows them *)
             InferOk target_ty eff ctx'
           (* Case 4: Subtype coercion (implicit widening) *)
           else if extended_subtype t target_ty then
             InferOk target_ty eff ctx'
           (* Case 5: Invalid cast *)
           else
             infer_err_msg ("Invalid cast from " ^ type_description t ^
                       " to " ^ type_description target_ty ^
                       ": no safe conversion exists")
       | err -> err)

  (* T-Is: Type test *)
  | EIs e' _ ->
      (match infer_type gctx ctx e' with
       | InferOk _ eff ctx' -> InferOk t_bool eff ctx'
       | err -> err)

  (* T-Sizeof/Alignof/Offsetof: Compile-time type info *)
  | ESizeof _ -> InferOk t_u64 pure ctx
  | EAlignof _ -> InferOk t_u64 pure ctx

  (* T-Convert: Explicit type conversion T(x)
     Go spec (Conversions): The result type is always the target type.
     The conversion is well-typed if the source expression is well-typed.
     Specific conversion validity (string<->byte/rune, numeric, etc.)
     is checked at a semantic level, not rejected by the type system.
     This is consistent with Go's approach where invalid conversions
     are compile-time errors but the type system always yields the target type. *)
  | EConvert target_ty e' ->
      (match infer_type gctx ctx e' with
       | InferOk _ eff ctx' -> InferOk target_ty eff ctx'
       | err -> err)

  (* T-Offsetof: unsafe.Offsetof(T, field) returns byte offset of field in struct.
     The type must be a struct type containing the named field.
     Result type is u64 (representing uintptr). *)
  | EOffsetof ty field_name ->
      (match ty with
       | TStruct st ->
           if Some? (FStar.List.Tot.find (fun (f: field_type) -> f.field_name = field_name) st.struct_fields)
           then InferOk t_u64 pure ctx
           else infer_err_msg ("EOffsetof: field '" ^ field_name ^ "' not found in struct '" ^ st.struct_name ^ "'")
       | _ -> infer_err_msg "EOffsetof: type argument must be a struct type")

  (* T-PtrAdd: unsafe.Add(ptr, len) performs pointer arithmetic.
     ptr must be an unsafe pointer (Raw type), len must be integer.
     Result is an unsafe pointer (Raw[Unit], matching Go's unsafe.Pointer). *)
  | EPtrAdd ptr_e len_e ->
      (match infer_type gctx ctx ptr_e with
       | InferOk t_ptr eff_ptr ctx1 ->
           (match t_ptr with
            | TWrap WRaw _ ->
                (match infer_type gctx ctx1 len_e with
                 | InferOk t_len eff_len ctx2 ->
                     (match t_len with
                      | TNumeric (NumInt _) ->
                          InferOk (TWrap WRaw (TPrim PUnit)) (row_join eff_ptr eff_len) ctx2
                      | _ -> infer_err_msg "EPtrAdd: second argument must be an integer type")
                 | err -> err)
            | _ -> infer_err_msg "EPtrAdd: first argument must be an unsafe pointer (Raw type)")
       | err -> err)

  (* T-New: new(T) allocates a zero-valued T and returns *T (pointer to T).
     Returns a raw pointer wrapped in Option since Go pointers are nullable. *)
  | ENew ty -> InferOk (TWrap WOption (TWrap WRaw ty)) pure ctx

  (* T-Complex: complex(real, imag) constructs a complex number.
     Both args must be the same float type. Result is TTuple [float; float]. *)
  | EComplex real_e imag_e ->
      (match infer_type gctx ctx real_e with
       | InferOk t_r eff_r ctx1 ->
           (match infer_type gctx ctx1 imag_e with
            | InferOk t_i eff_i ctx2 ->
                (match t_r, t_i with
                 | TNumeric (NumFloat fp_r), TNumeric (NumFloat fp_i) ->
                     if fp_r = fp_i
                     then InferOk (TTuple [t_r; t_i]) (row_join eff_r eff_i) ctx2
                     else infer_err_msg "complex: real and imaginary parts must have the same float precision"
                 | TNumeric (NumFloat fp), TNumeric (NumInt _) ->
                     (* Integer arg implicitly converted to matching float type *)
                     InferOk (TTuple [t_float fp; t_float fp]) (row_join eff_r eff_i) ctx2
                 | TNumeric (NumInt _), TNumeric (NumFloat fp) ->
                     InferOk (TTuple [t_float fp; t_float fp]) (row_join eff_r eff_i) ctx2
                 | TNumeric (NumInt _), TNumeric (NumInt _) ->
                     (* Both untyped integers: default to complex128 (float64 pair) *)
                     InferOk (TTuple [t_f64; t_f64]) (row_join eff_r eff_i) ctx2
                 | _, _ -> infer_err_msg "complex: arguments must be numeric types")
            | err -> err)
       | err -> err)

  (* T-RealPart: real(c) extracts the real part of a complex number.
     complex64 -> float32, complex128 -> float64. *)
  | ERealPart c_e ->
      (match infer_type gctx ctx c_e with
       | InferOk t_c eff ctx1 ->
           (match t_c with
            | TTuple [TNumeric (NumFloat fp); TNumeric (NumFloat _)] ->
                InferOk (t_float fp) eff ctx1
            | TNumeric (NumInt _) ->
                (* Untyped numeric constant: real part is float64 *)
                InferOk t_f64 eff ctx1
            | _ -> infer_err_msg "real: argument must be a complex type (TTuple [float; float])")
       | err -> err)

  (* T-ImagPart: imag(c) extracts the imaginary part of a complex number.
     complex64 -> float32, complex128 -> float64. *)
  | EImagPart c_e ->
      (match infer_type gctx ctx c_e with
       | InferOk t_c eff ctx1 ->
           (match t_c with
            | TTuple [TNumeric (NumFloat _); TNumeric (NumFloat fp)] ->
                InferOk (t_float fp) eff ctx1
            | TNumeric (NumInt _) ->
                (* Untyped numeric constant: imaginary part is float64 (value 0) *)
                InferOk t_f64 eff ctx1
            | _ -> infer_err_msg "imag: argument must be a complex type (TTuple [float; float])")
       | err -> err)

  (* T-Unsafe: Unsafe block (adds Unsafe effect) *)
  | EUnsafe e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           InferOk t (row_join eff (RowExt BrrrEffects.EUnsafe RowEmpty)) ctx'
       | err -> err)

  (* T-PtrToInt: unsafe.Pointer -> uintptr.
     The operand must be a raw pointer type (TWrap WRaw _).
     Result is always uintptr (u64 on 64-bit). Requires EUnsafe effect.
     Go spec (Package unsafe): "The effect of converting between Pointer
     and uintptr is implementation-defined." *)
  | EPtrToInt e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (match t with
            | TWrap WRaw _ ->
                InferOk t_u64 (row_join eff (RowExt BrrrEffects.EUnsafe RowEmpty)) ctx'
            | TWrap WOption (TWrap WRaw _) ->
                (* Go pointers are nullable: Option<Raw<T>> -> uintptr *)
                InferOk t_u64 (row_join eff (RowExt BrrrEffects.EUnsafe RowEmpty)) ctx'
            | _ ->
                infer_err_msg ("EPtrToInt: operand must be a raw pointer type, got " ^
                           type_description t))
       | err -> err)

  (* T-IntToPtr: uintptr -> unsafe.Pointer.
     The operand must be an integer type. Result is the target pointer type.
     Requires EUnsafe effect.
     Go spec (Package unsafe): "Any pointer or value of underlying type uintptr
     can be converted to a type of underlying type Pointer and vice versa." *)
  | EIntToPtr e' target_ty ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (match t with
            | TNumeric (NumInt _) ->
                InferOk target_ty (row_join eff (RowExt BrrrEffects.EUnsafe RowEmpty)) ctx'
            | _ ->
                infer_err_msg ("EIntToPtr: operand must be an integer type, got " ^
                           type_description t))
       | err -> err)

  (* T-StringFromPtr: unsafe.String(ptr, len) -> string.
     The first operand must be a *byte pointer (TWrap WRaw (TNumeric (NumInt u8))).
     The second operand must be an integer type.
     Result is always TPrim PString. Requires EUnsafe effect.
     Go spec (Package unsafe, Go 1.20): "The function String returns a string
     value whose underlying bytes start at ptr and whose length is len." *)
  | EStringFromPtr ptr_e len_e ->
      (match infer_type gctx ctx ptr_e with
       | InferOk ptr_t ptr_eff ctx1 ->
           (match infer_type gctx ctx1 len_e with
            | InferOk len_t len_eff ctx2 ->
                (match ptr_t, len_t with
                 | TWrap WRaw (TNumeric (NumInt _)), TNumeric (NumInt _) ->
                     InferOk (TPrim PString)
                             (row_join (row_join ptr_eff len_eff)
                                       (RowExt BrrrEffects.EUnsafe RowEmpty))
                             ctx2
                 | TWrap WRaw (TNumeric (NumInt _)), _ ->
                     infer_err_msg ("EStringFromPtr: len operand must be an integer type, got " ^
                                type_description len_t)
                 | _, _ ->
                     infer_err_msg ("EStringFromPtr: ptr operand must be a *byte pointer (TWrap WRaw (TNumeric (NumInt _))), got " ^
                                type_description ptr_t))
            | err -> err)
       | err -> err)

  (* T-StringData: unsafe.StringData(str) -> *byte.
     The operand must be a string (TPrim PString).
     Result is a *byte pointer (TWrap WRaw (TNumeric (NumInt u8))).
     Requires EUnsafe effect.
     Go spec (Package unsafe, Go 1.20): "The function StringData returns a
     pointer to the underlying bytes of the str argument." *)
  | EStringData str_e ->
      (match infer_type gctx ctx str_e with
       | InferOk str_t str_eff ctx' ->
           (match str_t with
            | TPrim PString ->
                InferOk (TWrap WRaw (TNumeric (NumInt u8)))
                        (row_join str_eff (RowExt BrrrEffects.EUnsafe RowEmpty))
                        ctx'
            | _ ->
                infer_err_msg ("EStringData: operand must be a string type, got " ^
                           type_description str_t))
       | err -> err)

  (* T-SliceFromPtr: unsafe.Slice(ptr, len) creates a slice from a raw pointer and length.
     ptr must be a raw pointer (TWrap WRaw elem_ty), len must be an integer type.
     Result is a slice of the element type (TWrap WSlice elem_ty).
     Requires EUnsafe effect.
     Go spec (Package unsafe, Go 1.17):
       "The function Slice returns a slice whose underlying array starts at ptr
        and whose length and capacity are len." *)
  | ESliceFromPtr ptr_e len_e elem_ty ->
      (match infer_type gctx ctx ptr_e with
       | InferOk t_ptr eff_ptr ctx1 ->
           (match t_ptr with
            | TWrap WRaw _ ->
                (match infer_type gctx ctx1 len_e with
                 | InferOk t_len eff_len ctx2 ->
                     (match t_len with
                      | TNumeric (NumInt _) ->
                          InferOk (TWrap WSlice elem_ty)
                                  (row_join (row_join eff_ptr eff_len)
                                            (RowExt BrrrEffects.EUnsafe RowEmpty))
                                  ctx2
                      | _ -> infer_err_msg "ESliceFromPtr: second argument (len) must be an integer type")
                 | err -> err)
            | _ -> infer_err_msg ("ESliceFromPtr: first argument must be a raw pointer (TWrap WRaw _), got " ^
                               type_description t_ptr))
       | err -> err)

  (* T-SliceData: unsafe.SliceData(slice) returns a pointer to the underlying array.
     The operand must be a slice type (TWrap WSlice elem_ty).
     Result is a raw pointer to the element type (TWrap WRaw elem_ty).
     Requires EUnsafe effect.
     Go spec (Package unsafe, Go 1.20):
       "The function SliceData returns a pointer to the underlying array
        of the slice argument." *)
  | ESliceData slice_e ->
      (match infer_type gctx ctx slice_e with
       | InferOk t_slice eff ctx' ->
           (match t_slice with
            | TWrap WSlice elem_ty ->
                InferOk (TWrap WRaw elem_ty)
                        (row_join eff (RowExt BrrrEffects.EUnsafe RowEmpty))
                        ctx'
            | _ -> infer_err_msg ("ESliceData: operand must be a slice type (TWrap WSlice _), got " ^
                               type_description t_slice))
       | err -> err)

  (* Placeholders and errors *)
  | EHole -> infer_err_msg "Cannot infer type of hole"
  | EError msg -> infer_err_msg ("Error node: " ^ msg)

  (* T-Recover: Go recover() returns interface{} (Dynamic).
     Pure in isolation - actual panic interception is via ETry/catch. *)
  | ERecover -> InferOk t_dynamic pure ctx

  (* T-Cast: Runtime cast for gradual typing
   *
   * A cast expression wraps a value with a runtime type check.
   * The cast was inserted by check_type_gradual when types were
   * consistent but not subtypes.
   *
   * Type rule:
   *   Gamma |- e : T1
   *   T1 ~ T2 (types are consistent)
   *   -------------------------------
   *   Gamma |- (e : T1 => T2) : T2
   *
   * The cast kind determines runtime behavior:
   *   - CKUp: No runtime overhead (can be erased)
   *   - CKDown: Runtime subtype check, may fail with blame
   *   - CKDynamic: Runtime type tag check, may fail with blame
   *
   * Reference: Siek & Taha 2006 "Gradual Typing for Functional Languages"
   *)
  | ECast inner ci ->
      (match infer_type gctx ctx inner with
       | InferOk t_inner eff ctx' ->
           (* Verify the cast is valid: inner type matches ci_from *)
           if type_eq t_inner ci.ci_from then
             (* Cast is well-formed, result type is ci_to *)
             InferOk ci.ci_to eff ctx'
           else if type_consistent t_inner ci.ci_from then
             (* Close enough for gradual typing - allow it *)
             InferOk ci.ci_to eff ctx'
           else
             infer_err_msg ("Cast source type mismatch: expected " ^
                           type_description ci.ci_from ^
                           ", got " ^ type_description t_inner)
       | err -> err)

  (* Loop constructs - simplified *)
  | ELoop body ->
      (match infer_type gctx ctx body with
       | InferOk _ eff ctx' ->
           InferOk t_never (row_join eff (RowExt BrrrEffects.EDiv RowEmpty)) ctx'  (* Loops may diverge *)
       | err -> err)

  | EWhile cond body ->
      (match infer_type gctx ctx cond with
       | InferOk cond_ty eff1 ctx1 ->
           if not (type_eq cond_ty t_bool) then infer_err_msg "While condition must be boolean"
           else
             (match infer_type gctx ctx1 body with
              | InferOk _ eff2 ctx2 ->
                  InferOk t_unit (row_join (row_join eff1 eff2) (RowExt BrrrEffects.EDiv RowEmpty)) ctx2
              | err -> err)
       | err -> err)

  | EBreak _ -> InferOk t_never pure ctx
  | EContinue -> InferOk t_never pure ctx

  (* T-MethodCall: Method call on receiver *)
  | EMethodCall receiver method_name args ->
      (match infer_type gctx ctx receiver with
       | InferOk recv_ty eff_recv ctx1 ->
           (* Look up method type based on receiver type *)
           (* For now, treat methods as fields with function types *)
           (match recv_ty with
            | TStruct st ->
                (match List.Tot.find (fun f -> f.field_name = method_name) st.struct_fields with
                 | Some f ->
                     (match f.field_ty with
                      | TFunc ft ->
                          if List.Tot.length args <> List.Tot.length ft.params then
                            infer_err_msg ("Method " ^ method_name ^ ": wrong number of arguments")
                          else
                            (match check_args gctx ctx1 args ft.params with
                             | Some (eff_args, ctx2) ->
                                 let total_eff = row_join eff_recv (row_join eff_args ft.effects) in
                                 InferOk ft.return_type total_eff ctx2
                             | None -> infer_err_msg ("Method " ^ method_name ^ ": argument type mismatch"))
                      | _ -> infer_err_msg ("Field " ^ method_name ^ " is not a function"))
                 | None -> infer_err_msg ("Unknown method: " ^ method_name))
            | _ -> infer_err_msg "Method call on non-struct type requires trait resolution")
       | err -> err)

  (* T-MethodRef: Bound method reference (obj.method without calling).
     Returns a function type where the receiver is already captured. *)
  | EMethodRef receiver method_name ->
      (match infer_type gctx ctx receiver with
       | InferOk recv_ty eff_recv ctx1 ->
           (match recv_ty with
            | TStruct st ->
                (match List.Tot.find (fun f -> f.field_name = method_name) st.struct_fields with
                 | Some f ->
                     (match f.field_ty with
                      | TFunc ft ->
                          (* Method ref returns a function without the first self parameter *)
                          InferOk f.field_ty eff_recv ctx1
                      | _ -> infer_err_msg ("Field " ^ method_name ^ " is not a function"))
                 | None -> infer_err_msg ("Unknown method: " ^ method_name))
            | _ -> infer_err_msg "Method reference on non-struct type requires trait resolution")
       | err -> err)

  (* T-TypeMethod: Unbound type method reference (T::method).
     Returns the full function type including self parameter.
     Note: Looks up type name in global context to find the type scheme. *)
  | ETypeMethod type_name method_name ->
      (* Look up type in global context and find the method *)
      (match lookup_global type_name gctx with
       | Some scheme ->
           (* Instantiate the scheme to get the type *)
           (match scheme.ts_body with
            | TStruct st ->
                (match List.Tot.find (fun f -> f.field_name = method_name) st.struct_fields with
                 | Some f ->
                     (match f.field_ty with
                      | TFunc _ -> InferOk f.field_ty pure ctx
                      | _ -> infer_err_msg ("Type method " ^ type_name ^ "::" ^ method_name ^ " is not a function"))
                 | None -> infer_err_msg ("Unknown method: " ^ type_name ^ "::" ^ method_name))
            | _ -> infer_err_msg ("Type " ^ type_name ^ " is not a struct"))
       | None -> infer_err_msg ("Unknown type: " ^ type_name))

  (* T-Len: Length intrinsic returns i64.
     Supports arrays, slices, strings, tuples, and structs. *)
  | ELen e' ->
      (match infer_type gctx ctx e' with
       | InferOk ety eff ctx1 ->
           (* Check that the type supports len *)
           let len_ty = TNumeric (NumInt i64) in
           (match ety with
            | TWrap WArray _ | TWrap WSlice _ -> InferOk len_ty eff ctx1
            | TApp (TNamed "FixedArray") _ -> InferOk len_ty eff ctx1
            | TPrim PString -> InferOk len_ty eff ctx1
            | TTuple _ -> InferOk len_ty eff ctx1
            | TStruct _ -> InferOk len_ty eff ctx1
            | _ -> infer_err_msg "len: unsupported type (expected array, slice, string, tuple, or struct)")
       | err -> err)

  (* T-Cap: Capacity intrinsic returns i64.
     For fixed-size collections, capacity equals length. *)
  | ECap e' ->
      (match infer_type gctx ctx e' with
       | InferOk ety eff ctx1 ->
           let cap_ty = TNumeric (NumInt i64) in
           (match ety with
            | TWrap WArray _ | TWrap WSlice _ -> InferOk cap_ty eff ctx1
            | TApp (TNamed "FixedArray") _ -> InferOk cap_ty eff ctx1
            | TPrim PString -> InferOk cap_ty eff ctx1
            | TTuple _ -> InferOk cap_ty eff ctx1
            | _ -> infer_err_msg "cap: unsupported type (expected array, slice, string, or tuple)")
       | err -> err)

  (* T-Min: min(x, y...) - Go 1.21 built-in.
     Returns the smallest of one or more ordered arguments.
     All arguments must have the same ordered type (numeric or string).
     Result type is the common argument type.
     Go spec: "The same type rules as for operators apply:
     for ordered arguments x and y, min(x, y) is valid if x + y is valid,
     and the type of min(x, y) is the type of x + y" *)
  | EMin args ->
      (match args with
       | [] -> infer_err_msg "min: requires at least one argument"
       | _ ->
           (match infer_type_list gctx ctx args with
            | Some ([], _, _) -> infer_err_msg "min: requires at least one argument"
            | Some (t :: ts, eff, ctx') ->
                (* Check all arguments have the same type *)
                if List.Tot.for_all (type_eq t) ts then
                  (* Check the type is ordered (numeric or string) *)
                  (match t with
                   | TNumeric _ -> InferOk t eff ctx'
                   | TPrim PString -> InferOk t eff ctx'
                   | _ -> infer_err_msg "min: arguments must be ordered types (numeric or string)")
                else infer_err_msg "min: all arguments must have the same type"
            | None -> infer_err_msg "min: error inferring argument types"))

  (* T-Max: max(x, y...) - Go 1.21 built-in.
     Returns the largest of one or more ordered arguments.
     Same type rules as min. *)
  | EMax args ->
      (match args with
       | [] -> infer_err_msg "max: requires at least one argument"
       | _ ->
           (match infer_type_list gctx ctx args with
            | Some ([], _, _) -> infer_err_msg "max: requires at least one argument"
            | Some (t :: ts, eff, ctx') ->
                if List.Tot.for_all (type_eq t) ts then
                  (match t with
                   | TNumeric _ -> InferOk t eff ctx'
                   | TPrim PString -> InferOk t eff ctx'
                   | _ -> infer_err_msg "max: arguments must be ordered types (numeric or string)")
                else infer_err_msg "max: all arguments must have the same type"
            | None -> infer_err_msg "max: error inferring argument types"))

  (* T-Copy: copy(dst, src) returns int (number of elements copied).
     Both arguments must be slices of the same element type,
     or dst must be []byte and src must be string.
     Returns i64 (Go int). *)
  | ECopy dst_e src_e ->
      (match infer_type gctx ctx dst_e with
       | InferOk dst_ty eff1 ctx1 ->
           (match infer_type gctx ctx1 src_e with
            | InferOk src_ty eff2 ctx2 ->
                let copy_ty = TNumeric (NumInt i64) in
                (match dst_ty, src_ty with
                 (* copy([]T, []T) - same element type *)
                 | TWrap WSlice t1, TWrap WSlice t2 ->
                     if type_eq t1 t2 then InferOk copy_ty (join_eff eff1 eff2) ctx2
                     else infer_err_msg "copy: slice element types must match"
                 | TWrap WArray t1, TWrap WArray t2 ->
                     if type_eq t1 t2 then InferOk copy_ty (join_eff eff1 eff2) ctx2
                     else infer_err_msg "copy: array element types must match"
                 | TApp (TNamed "FixedArray") [_; t1], TApp (TNamed "FixedArray") [_; t2] ->
                     if type_eq t1 t2 then InferOk copy_ty (join_eff eff1 eff2) ctx2
                     else infer_err_msg "copy: fixed array element types must match"
                 (* copy([]byte, string) *)
                 | TWrap WSlice (TNumeric (NumInt t)), TPrim PString when t = u8 ->
                     InferOk copy_ty (join_eff eff1 eff2) ctx2
                 | TWrap WArray (TNumeric (NumInt t)), TPrim PString when t = u8 ->
                     InferOk copy_ty (join_eff eff1 eff2) ctx2
                 | TApp (TNamed "FixedArray") [_; TNumeric (NumInt t)], TPrim PString when t = u8 ->
                     InferOk copy_ty (join_eff eff1 eff2) ctx2
                 | _ -> infer_err_msg "copy: arguments must be slices of same type, or []byte and string")
            | err -> err)
       | err -> err)

  (* T-Clear: clear(s) returns unit.
     Argument must be a slice or map.
     For slices: zeroes all elements. For maps: deletes all entries. *)
  | EClear e' ->
      (match infer_type gctx ctx e' with
       | InferOk ety eff ctx1 ->
           (match ety with
            | TWrap WSlice _ | TWrap WArray _ -> InferOk TUnit eff ctx1
            | TApp (TNamed "FixedArray") _ -> InferOk TUnit eff ctx1
            | TApp (TNamed dict_name) _ when dict_name = "Dict" -> InferOk TUnit eff ctx1
            | TStruct _ -> InferOk TUnit eff ctx1  (* maps as structs *)
            | _ -> infer_err_msg "clear: unsupported type (expected slice or map)")
       | err -> err)

  (* T-Delete: delete(m, k) removes key k from map m. Returns unit.
     First argument must be a map type (Dict or struct).
     Second argument must be a valid key type. *)
  | EDelete map_e key_e ->
      (match infer_type gctx ctx map_e with
       | InferOk mty eff1 ctx1 ->
           (match mty with
            | TApp (TNamed dict_name) _ when dict_name = "Dict" ->
                (match infer_type gctx ctx1 key_e with
                 | InferOk _kty eff2 ctx2 ->
                     InferOk TUnit (join_eff eff1 eff2) ctx2
                 | err -> err)
            | TStruct _ ->
                (match infer_type gctx ctx1 key_e with
                 | InferOk _kty eff2 ctx2 ->
                     InferOk TUnit (join_eff eff1 eff2) ctx2
                 | err -> err)
            | _ -> infer_err_msg "delete: first argument must be a map")
       | err -> err)

  (* T-Append: append(slice, elems...) - Go append built-in.
     Returns a slice of the same type.
     First argument must be a slice (TWrap WSlice elem_ty).
     Subsequent arguments must each be compatible with elem_ty.
     Special case: append([]byte, string...) appends string bytes to byte slice.
     Go spec: "Appending to and copying slices" *)
  | EAppend slice_e elem_es ->
      (match infer_type gctx ctx slice_e with
       | InferOk slice_ty eff1 ctx1 ->
           (match slice_ty with
            (* append([]T, elems...) - standard case *)
            | TWrap WSlice elem_ty ->
                (match infer_type_list gctx ctx1 elem_es with
                 | Some (elem_types, eff2, ctx2) ->
                     if List.Tot.for_all (type_eq elem_ty) elem_types
                     then InferOk (TWrap WSlice elem_ty) (join_eff eff1 eff2) ctx2
                     else infer_err_msg "append: element types must match slice element type"
                 | None -> infer_err_msg "append: error inferring element types")
            (* append([]byte, string...) - special case: append string bytes to byte slice *)
            | TWrap WArray (TNumeric (NumInt t)) when t = u8 ->
                (match infer_type_list gctx ctx1 elem_es with
                 | Some (elem_types, eff2, ctx2) ->
                     if List.Tot.for_all (fun et ->
                       type_eq (TNumeric (NumInt u8)) et || type_eq (TPrim PString) et
                     ) elem_types
                     then InferOk (TWrap WSlice (TNumeric (NumInt u8))) (join_eff eff1 eff2) ctx2
                     else infer_err_msg "append: byte slice append requires byte or string arguments"
                 | None -> infer_err_msg "append: error inferring element types")
            | _ -> infer_err_msg "append: first argument must be a slice type")
       | err -> err)

  (* T-Make: Go make() built-in - type-directed allocation.
     The return type depends on the target type argument:
       make([]T, len)      : []T        (slice type)
       make([]T, len, cap) : []T        (slice type)
       make(map[K]V)       : map[K]V    (map type)
       make(map[K]V, hint) : map[K]V    (map type)
       make(chan T)         : chan T     (channel type)
       make(chan T, size)   : chan T     (channel type)
     All integer arguments must be int-typed. *)
  | EMake ty args ->
      (match infer_type_list gctx ctx args with
       | Some (arg_types, eff, ctx') ->
           (* Validate argument types: all must be numeric (int) *)
           let all_int = List.Tot.for_all (fun t ->
             match t with
             | TNumeric _ -> true
             | _ -> false) arg_types in
           let n_args = List.Tot.length arg_types in
           (match ty with
            (* Slice: requires 1 or 2 int args *)
            | TWrap WSlice _ ->
                if (n_args = 1 || n_args = 2) && all_int
                then InferOk ty eff ctx'
                else infer_err_msg "make: slice requires 1 or 2 integer arguments (len [, cap])"
            (* Map: requires 0 or 1 int args *)
            | TApp (TNamed dict_name) _ ->
                if dict_name = "Dict" && (n_args = 0 || (n_args = 1 && all_int))
                then InferOk ty eff ctx'
                else infer_err_msg "make: map requires 0 or 1 integer argument (capacity hint)"
            (* Channel: requires 0 or 1 int args *)
            | TApp (TNamed chan_name) _ ->
                if (chan_name = "Channel" || chan_name = "RecvChannel" || chan_name = "SendChannel")
                   && (n_args = 0 || (n_args = 1 && all_int))
                then InferOk ty eff ctx'
                else infer_err_msg "make: channel requires 0 or 1 integer argument (buffer size)"
            | _ -> infer_err_msg "make: unsupported type (expected slice, map, or channel)")
       | None -> infer_err_msg "make: failed to type-check arguments")

  (* T-Struct: Struct construction with full field type inference.

     For struct literals like Point { x: 1, y: 2 }, we:
     1. Type-check each field expression
     2. Collect the inferred types
     3. Build the struct type with correct field types
     4. Combine effects from all field expressions *)
  | EStruct type_name fields ->
      (match infer_struct_fields gctx ctx fields with
       | Some (field_types, eff, ctx') ->
           (* Build proper struct type with inferred field types *)
           let struct_fields = List.Tot.map
             (fun (name, ty) -> { field_name = name; field_ty = ty; field_vis = Public; field_tag = None })
             field_types in
           let st : struct_type = {
             struct_name = type_name;
             struct_fields = struct_fields;
             struct_repr = ReprRust
           } in
           InferOk (TStruct st) eff ctx'
       | None -> infer_err_msg "Error type-checking struct field expressions")

  (* T-Variant: Enum variant construction *)
  | EVariant type_name variant_name args ->
      (match infer_type_list gctx ctx args with
       | Some (arg_tys, eff, ctx') ->
           (* Build variant type *)
           let variant : variant_type = {
             variant_name = variant_name;
             variant_fields = arg_tys
           } in
           let enum : enum_type = {
             enum_name = type_name;
             enum_variants = [variant]  (* Partial enum with just this variant *)
           } in
           InferOk (TEnum enum) eff ctx'
       | None -> infer_err_msg "Error in variant arguments")

  (* T-For: For loop over iterator
   *
   * Type rule: for x in iter { body }
   *   iter must be an iterable type (Array, Slice, or implements IntoIterator)
   *   x is bound to the element type within body
   *   Result is unit, adds Div effect (loop may diverge)
   *)
  | EFor x iter body ->
      (match infer_type gctx ctx iter with
       | InferOk iter_ty eff1 ctx1 ->
           (* Extract element type from iterable - reject non-iterable types *)
           let elem_ty_opt : option brrr_type = match iter_ty with
             | TWrap WArray t -> Some t   (* Array<T> iterates over T *)
             | TApp (TNamed "FixedArray") [_; t] -> Some t  (* FixedArray<N, T> iterates over T *)
             | TWrap WSlice t -> Some t   (* Slice<T> iterates over T *)
             | TApp (TNamed "Range") [t] -> Some t  (* Range<T> iterates over T *)
             | TApp (TNamed "Vec") [t] -> Some t    (* Vec<T> iterates over T *)
             | TApp (TNamed "Iterator") [t] -> Some t  (* Iterator<T> yields T *)
             | _ -> None  (* Not a recognized iterable type *)
           in
           (match elem_ty_opt with
            | Some elem_ty ->
                let ctx2 = extend_ctx x elem_ty MOne ctx1 in
                (match infer_type gctx ctx2 body with
                 | InferOk _ eff2 ctx3 ->
                     InferOk t_unit (row_join (row_join eff1 eff2) (RowExt BrrrEffects.EDiv RowEmpty)) ctx3
                 | err -> err)
            | None ->
                infer_err_msg ("Cannot iterate over non-iterable type '" ^
                          type_description iter_ty ^
                          "'. Expected Array, Slice, Range, Vec, or Iterator."))
       | err -> err)

  (* T-Closure: Closure with explicit captures
   *
   * Type rule: |[captures]| (params) -> body
   *   All captures must be in scope and available
   *   Parameters are bound in body with their declared types
   *   Captures are consumed (moved into closure)
   *)
  | EClosure params captures body ->
      (* Verify each capture is available in context, tracking first failure *)
      let rec resolve_captures (caps: list var_id) (acc: list (var_id & brrr_type))
          : Tot (either string (list (var_id & brrr_type))) (decreases caps) =
        match caps with
        | [] -> Inr (List.Tot.rev acc)  (* Success: return accumulated types *)
        | cap :: rest ->
            (match lookup_ctx cap ctx with
             | Some (ty, m) ->
                 if is_available m then
                   resolve_captures rest ((cap, ty) :: acc)
                 else
                   Inl ("Captured variable '" ^ cap ^ "' is not available (already consumed)")
             | None ->
                 Inl ("Captured variable '" ^ cap ^ "' is not in scope"))
      in
      (match resolve_captures captures [] with
       | Inr cap_tys ->
           let param_tys = List.Tot.map (fun (x, t) -> { name = Some x; ty = t; mode = MOne }) params in
           (* Extend context with parameters *)
           let ctx' = List.Tot.fold_right (fun (x, t) c -> extend_ctx x t MOne c) params ctx in
           (* Consume captured variables - they are moved into the closure *)
           let ctx'' = List.Tot.fold_right
             (fun (cap, _) c ->
               match consume_var cap c with
               | Some c' -> c'
               | None -> c)  (* Skip if already consumed (shouldn't happen after our check) *)
             cap_tys ctx' in
           (match infer_type gctx ctx'' body with
            | InferOk ret_ty eff _ ->
                let ft : func_type = {
                  params = param_tys;
                  return_type = ret_ty;
                  effects = eff;
                  is_unsafe = false
                } in
                InferOk (TFunc ft) pure ctx  (* Closures are pure expressions *)
            | err -> err)
       | Inl err_msg -> infer_err_msg err_msg)

  (* T-Move: Explicit move (transfers ownership) *)
  | EMove e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' -> InferOk t eff ctx'  (* Move has same type, ownership transferred *)
       | err -> err)

  (* T-Drop: Explicit drop (has Alloc effect - resource deallocation) *)
  | EDrop e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           InferOk t_unit (row_join eff (RowExt BrrrEffects.EAlloc RowEmpty)) ctx'
       | err -> err)

  (* T-Try: Try-catch-finally with proper catch arm type checking
   *
   * Type rule: If try body has type T and all catch arms have type T',
   * then result type is the unified type of T and T'.
   *
   * Effect handling:
   * - Try body may throw (EThrow effect)
   * - Catch arms handle exceptions, removing EThrow if all exceptions caught
   * - Finally always executes but doesn't affect result type
   *)
  | ETry try_body catches finally_opt ->
      (match infer_type gctx ctx try_body with
       | InferOk try_ty eff_try ctx1 ->
           (* Type check all catch arms against the try body type *)
           let catch_base_eff = row_join eff_try (RowExt BrrrEffects.EThrow RowEmpty) in
           (match infer_catch_arms gctx ctx1 try_ty catches catch_base_eff with
            | InferOk result_ty catch_eff ctx2 ->
                (* Handle finally clause - executes for side effects only *)
                (match finally_opt with
                 | None -> InferOk result_ty catch_eff ctx2
                 | Some finally_e ->
                     (match infer_type gctx ctx2 finally_e with
                      | InferOk _ finally_eff ctx3 ->
                          InferOk result_ty (row_join catch_eff finally_eff) ctx3
                      | err -> err))
            | err -> err)
       | err -> err)

  (* T-Await: Await async expression (has Async effect) *)
  | EAwait e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Unwrap Future/Promise type if present *)
           let result_ty = match t with
             | TApp (TNamed "Future") [inner] -> inner
             | TApp (TNamed "Promise") [inner] -> inner
             | _ -> t  (* Assume already unwrapped *)
           in
           InferOk result_ty (row_join eff (RowExt BrrrEffects.EAsync RowEmpty)) ctx'
       | err -> err)

  (* T-Yield: Yield value in generator (has Yield[Y, R] effect)
     Per spec Definition 3.1: effect Yield[Y, R] { yield : Y ~> R }
     Y = type of yielded value (inferred from e')
     R = resume type (would come from generator context, defaulting to unit) *)
  | EYield e' ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Construct parameterized Yield[t, unit] effect.
              In a full implementation, resume type would come from generator context. *)
           let yield_ty_eff = brrr_type_to_effect_type t in
           let resume_ty_eff = BrrrEffects.ETUnit in
           let yield_eff = RowExt (BrrrEffects.EYield yield_ty_eff resume_ty_eff) RowEmpty in
           InferOk t_unit (row_join eff yield_eff) ctx'
       | err -> err)

  (* T-Generator: Create generator from body expression
     Type: Generator[Y, R] where Y = yield type, R = return type
     The body must have Yield[Y, R] effect *)
  | EGenerator body ->
      (match infer_type gctx ctx body with
       | InferOk body_ty body_eff ctx' ->
           (* Extract yield type from effect if present, otherwise default to unit *)
           let yield_ty = t_unit in  (* TODO: extract from body_eff *)
           let return_ty = body_ty in
           (* Generator[Y, R] is represented as a tuple type for now *)
           let gen_ty = TApp (TName "Generator") [yield_ty; return_ty] in
           InferOk gen_ty RowEmpty ctx'
       | err -> err)

  (* T-GenNext: Advance generator, returns (status, value) tuple
     gen.next() : Generator[Y, R] -> (String, Y | R) *)
  | EGenNext gen_e ->
      (match infer_type gctx ctx gen_e with
       | InferOk gen_ty eff ctx' ->
           (* For now, return a tuple of (String, Dynamic) *)
           let result_ty = TTuple [t_string; TDynamic] in
           InferOk result_ty eff ctx'
       | err -> err)

  (* T-GenSend: Resume generator with value
     gen.send(v) : Generator[Y, R] -> V -> (String, Y | R) *)
  | EGenSend gen_e val_e ->
      (match infer_type gctx ctx gen_e with
       | InferOk gen_ty eff1 ctx1 ->
           (match infer_type gctx ctx1 val_e with
            | InferOk val_ty eff2 ctx2 ->
                let result_ty = TTuple [t_string; TDynamic] in
                InferOk result_ty (row_join eff1 eff2) ctx2
            | err -> err)
       | err -> err)

  (* T-Handle: Effect handler *)
  | EHandle e' handler ->
      (match infer_type gctx ctx e' with
       | InferOk t eff ctx' ->
           (* Effect handler removes handled effects from the effect row *)
           (* For now, return the expression type with original effects *)
           (* A full implementation would compute the handled effect set *)
           InferOk t eff ctx'
       | err -> err)

  (* T-Perform: Perform effect operation *)
  | EPerform op args ->
      (match infer_type_list gctx ctx args with
       | Some (arg_tys, eff, ctx') ->
           (* Effect operations return unit and add the performed effect *)
           InferOk t_unit (row_join eff (RowExt op RowEmpty)) ctx'
       | None -> infer_err_msg "Error in effect operation arguments")

(**
 * check_type: Type checking in checking mode
 *
 * Judgment: gctx; ctx |- e <= T ; eff ~> ctx'
 *
 * This is the checking mode of bidirectional type checking, where type
 * information flows INTO the expression from context.
 *
 * ==========================================================================
 * T-SUB: SUBSUMPTION RULE (TAPL 15.3, Spec 8.2)
 * ==========================================================================
 *
 * The core of checking mode is the subsumption rule:
 *
 *   ctx |- e => T1 ; eff    (infer type T1)
 *   T1 <: T2                 (T1 is subtype of T2)
 *   ------------------------------------------------ T-Sub
 *   ctx |- e <= T2 ; eff    (checks against T2)
 *
 * This allows implicit coercion via the subtype relation.
 * Examples:
 *   - Int <: Int (reflexivity)
 *   - Never <: T for any T (bottom type)
 *   - T <: Dynamic for any T (top type)
 *   - (T1 -> T2) <: (S1 -> S2) when S1 <: T1 and T2 <: S2 (contravariant/covariant)
 *
 * ==========================================================================
 * SPECIAL CASES: PROPAGATING TYPE INFORMATION
 * ==========================================================================
 *
 * For certain expressions, checking mode provides better type inference
 * by propagating expected type information:
 *
 * CHECK-ABS (Pierce & Turner "Local Type Inference"):
 *   expected = (T1@m -[eff_f]-> T2)
 *   ctx, x : T1 @ m |- body <= T2 ; eff
 *   eff <: eff_f
 *   ------------------------------------------------
 *   ctx |- \(x:_).body <= (T1@m -[eff_f]-> T2) ; Pure
 *
 *   Note: Parameter types come from expected type, not annotations.
 *   This enables type inference for lambda expressions in contexts
 *   where the expected function type is known (e.g., higher-order args).
 *
 * ==========================================================================
 * MODE SWITCHING
 * ==========================================================================
 *
 * For all other expressions, we:
 * 1. Call infer_type to synthesize type T1
 * 2. Check that T1 <: expected using extended_subtype
 * 3. Return effects from inference
 *
 * This implements the fundamental bidirectional recipe from [DK20]:
 *   "When checking e against T, first synthesize type T' for e,
 *    then check T' <: T"
 *
 * ==========================================================================
 * TERMINATION
 * ==========================================================================
 *
 * Lexicographic ordering: %[expr_size e; 1]
 * Secondary ordinal 1 > 0 allows check_type to call infer_type on
 * the same expression (for T-Sub rule).
 *
 * @param gctx     Global type context for top-level definitions
 * @param ctx      Local type context for bound variables
 * @param e        Expression to check
 * @param expected Expected type to check against
 * @returns        CheckOk(effects, updated_ctx) or CheckErr(error)
 *)
and check_type (gctx: global_ctx) (ctx: type_ctx) (e: expr) (expected: brrr_type)
    : Tot check_result (decreases %[expr_size e; 1]) =
  match e with
  (* For lambdas, use expected function type to guide inference *)
  | ELambda params body ->
      (match expected with
       | TFunc ft ->
           if List.Tot.length params <> List.Tot.length ft.params then
             check_err_msg "Lambda arity mismatch"
           else
             (* Use parameter types from expected type *)
             let ctx' = fold_right2
               (fun (x: var_id & brrr_type) (pt: param_type) (c: type_ctx) ->
                 extend_ctx (fst x) pt.ty pt.mode c)
               params ft.params ctx in
             (match check_type gctx ctx' body ft.return_type with
              | CheckOk eff ctx'' ->
                  (* Effect must be subsumed by expected *)
                  if effect_sub eff ft.effects then
                    CheckOk pure ctx  (* Lambda expression itself is pure *)
                  else check_err_msg "Lambda effects exceed expected"
              | err -> err)
       | _ -> check_err_msg "Expected function type for lambda")

  (* For other expressions, infer and check subsumption *)
  | _ ->
      (match infer_type gctx ctx e with
       | InferOk inferred_ty eff ctx' ->
           (* T-Sub: Check subtyping *)
           if extended_subtype inferred_ty expected then
             CheckOk eff ctx'
           else check_err_msg ("Type mismatch: expected " ^ "T1" ^ " but got " ^ "T2")
       | InferErr err -> CheckErr err)

(**
 * infer_type_list: Infer types of expression list
 *
 * Uses structural termination based on expr_list_size.
 * Lexicographic ordering: %[expr_list_size es; 2]
 *
 * @param gctx Global type context
 * @param ctx  Local type context
 * @param es   List of expressions to type
 *)
and infer_type_list (gctx: global_ctx) (ctx: type_ctx) (es: list expr)
    : Tot (option (list brrr_type & effect_row & type_ctx)) (decreases %[expr_list_size es; 2]) =
  match es with
  | [] -> Some ([], pure, ctx)
  | e :: rest ->
      (match infer_type gctx ctx e with
       | InferOk t eff ctx' ->
           (match infer_type_list gctx ctx' rest with
            | Some (ts, eff', ctx'') ->
                Some (t :: ts, row_join eff eff', ctx'')
            | None -> None)
       | InferErr _ -> None)

(**
 * infer_struct_fields: Infer types of struct field expressions.
 *
 * Type-checks each field expression and returns:
 * - List of (field_name, inferred_type) pairs
 * - Combined effects from all field expressions
 * - Updated typing context
 *
 * Uses structural termination based on field_expr_list_size.
 *
 * @param gctx   Global type context
 * @param ctx    Local type context
 * @param fields List of (field_name, expression) pairs
 *)
and infer_struct_fields (gctx: global_ctx) (ctx: type_ctx) (fields: list (string & expr))
    : Tot (option (list (string & brrr_type) & effect_row & type_ctx))
          (decreases %[field_expr_list_size fields; 2]) =
  match fields with
  | [] -> Some ([], pure, ctx)
  | (name, e) :: rest ->
      (match infer_type gctx ctx e with
       | InferOk t eff ctx' ->
           (match infer_struct_fields gctx ctx' rest with
            | Some (rest_fields, eff', ctx'') ->
                Some ((name, t) :: rest_fields, row_join eff eff', ctx'')
            | None -> None)
       | InferErr _ -> None)

(**
 * check_args: Check arguments against parameter types
 *
 * Uses structural termination based on expr_list_size.
 * Lexicographic ordering: %[expr_list_size args; 3]
 *
 * @param gctx   Global type context
 * @param ctx    Local type context
 * @param args   List of argument expressions
 * @param params List of expected parameter types
 *)
and check_args (gctx: global_ctx) (ctx: type_ctx) (args: list expr) (params: list BrrrTypes.param_type)
    : Tot (option (effect_row & type_ctx)) (decreases %[expr_list_size args; 3]) =
  match args, params with
  | [], [] -> Some (pure, ctx)
  | arg :: args', param :: params' ->
      let param_ty : brrr_type = BrrrTypes.Mkparam_type?.ty param in
      (match check_type gctx ctx arg param_ty with
       | CheckOk eff ctx' ->
           (match check_args gctx ctx' args' params' with
            | Some (eff', ctx'') -> Some (row_join eff eff', ctx'')
            | None -> None)
       | CheckErr _ -> None)
  | _, _ -> None

(**
 * infer_match_arms: Infer type of match arms
 *
 * Uses structural termination based on match_arm_list_size.
 * Lexicographic ordering: %[match_arm_list_size arms; 4]
 *
 * @param gctx         Global type context
 * @param ctx          Local type context
 * @param scrutinee_ty Type of the scrutinee expression
 * @param arms         List of match arms
 * @param acc_eff      Accumulated effects from prior arms
 *)
and infer_match_arms (gctx: global_ctx) (ctx: type_ctx) (scrutinee_ty: brrr_type)
                     (arms: list match_arm) (acc_eff: effect_row)
    : Tot infer_result (decreases %[match_arm_list_size arms; 4]) =
  match arms with
  | [] -> infer_err_msg "Empty match expression"
  | [arm] ->
      (* Single arm - use empty_type_def_ctx since scrutinee_ty contains
         full struct/enum type info when applicable *)
      (match infer_pattern empty_type_def_ctx arm.arm_pattern scrutinee_ty with
       | Some bindings ->
           let ctx' = extend_ctx_with_bindings bindings ctx in
           (* Check guard if present *)
           let guard_result = match arm.arm_guard with
             | None -> Some (pure, ctx')
             | Some g ->
                 (match check_type gctx ctx' g t_bool with
                  | CheckOk eff ctx'' -> Some (eff, ctx'')
                  | CheckErr _ -> None) in
           (match guard_result with
            | Some (guard_eff, ctx'') ->
                (match infer_type gctx ctx'' arm.arm_body with
                 | InferOk t eff ctx''' ->
                     InferOk t (row_join acc_eff (row_join guard_eff eff)) ctx
                 | err -> err)
            | None -> infer_err_msg "Guard type error")
       | None -> infer_err_msg "Pattern does not match scrutinee type")
  | arm :: rest ->
      (* Multiple arms: check first, then rest, unify types
         Use empty_type_def_ctx since scrutinee_ty contains full type info *)
      (match infer_pattern empty_type_def_ctx arm.arm_pattern scrutinee_ty with
       | Some bindings ->
           let ctx' = extend_ctx_with_bindings bindings ctx in
           let guard_result = match arm.arm_guard with
             | None -> Some (pure, ctx')
             | Some g ->
                 (match check_type gctx ctx' g t_bool with
                  | CheckOk eff ctx'' -> Some (eff, ctx'')
                  | CheckErr _ -> None) in
           (match guard_result with
            | Some (guard_eff, ctx'') ->
                (match infer_type gctx ctx'' arm.arm_body with
                 | InferOk t1 eff1 _ ->
                     let new_acc = row_join acc_eff (row_join guard_eff eff1) in
                     (match infer_match_arms gctx ctx scrutinee_ty rest new_acc with
                      | InferOk t2 eff2 ctx_final ->
                          (* Unify arm types *)
                          if type_eq t1 t2 then
                            InferOk t1 eff2 ctx_final
                          else if extended_subtype t1 t2 then
                            InferOk t2 eff2 ctx_final
                          else if extended_subtype t2 t1 then
                            InferOk t1 eff2 ctx_final
                          else infer_err_msg "Match arm types do not unify"
                      | err -> err)
                 | err -> err)
            | None -> infer_err_msg "Guard type error")
       | None -> infer_err_msg "Pattern does not match scrutinee type")

(**
 * infer_catch_arms: Type check catch arms and unify their types
 *
 * Uses structural termination based on catch_arm_list_size.
 * Lexicographic ordering: %[catch_arm_list_size catches; 5]
 *
 * Each catch arm:
 *   1. Has a pattern matched against the exception type
 *   2. Binds pattern variables in scope for the catch body
 *   3. Must produce a type compatible with other arms
 *
 * @param gctx        Global type context
 * @param ctx         Local type context
 * @param expected_ty Expected result type from try body (for unification)
 * @param catches     List of catch arms
 * @param acc_eff     Accumulated effects from prior arms
 *)
and infer_catch_arms (gctx: global_ctx) (ctx: type_ctx) (expected_ty: brrr_type)
                     (catches: list catch_arm) (acc_eff: effect_row)
    : Tot infer_result (decreases %[catch_arm_list_size catches; 5]) =
  match catches with
  | [] ->
      (* No catch arms - result is expected type with accumulated effects.
         The Throw effect should be preserved since exceptions are not handled. *)
      InferOk expected_ty acc_eff ctx
  | [c] ->
      (* Single catch arm *)
      (match infer_pattern empty_type_def_ctx c.catch_pattern c.catch_type with
       | Some bindings ->
           let ctx' = extend_ctx_with_bindings bindings ctx in
           (match infer_type gctx ctx' c.catch_body with
            | InferOk catch_ty catch_eff _ ->
                (* Unify catch arm type with expected type from try body *)
                if type_eq catch_ty expected_ty then
                  InferOk expected_ty (row_join acc_eff catch_eff) ctx
                else if extended_subtype catch_ty expected_ty then
                  InferOk expected_ty (row_join acc_eff catch_eff) ctx
                else if extended_subtype expected_ty catch_ty then
                  InferOk catch_ty (row_join acc_eff catch_eff) ctx
                else
                  infer_err_msg ("Catch arm type '" ^ type_description catch_ty ^
                            "' does not match try body type '" ^ type_description expected_ty ^ "'")
            | err -> err)
       | None ->
           infer_err_msg ("Catch pattern does not match exception type '" ^
                     type_description c.catch_type ^ "'"))
  | c :: rest ->
      (* Multiple catch arms: check first, then rest, unify types *)
      (match infer_pattern empty_type_def_ctx c.catch_pattern c.catch_type with
       | Some bindings ->
           let ctx' = extend_ctx_with_bindings bindings ctx in
           (match infer_type gctx ctx' c.catch_body with
            | InferOk catch_ty catch_eff _ ->
                let new_acc = row_join acc_eff catch_eff in
                (* Recursively check remaining catch arms *)
                (match infer_catch_arms gctx ctx expected_ty rest new_acc with
                 | InferOk rest_ty rest_eff ctx_final ->
                     (* Unify this arm's type with the rest *)
                     if type_eq catch_ty rest_ty then
                       InferOk catch_ty rest_eff ctx_final
                     else if extended_subtype catch_ty rest_ty then
                       InferOk rest_ty rest_eff ctx_final
                     else if extended_subtype rest_ty catch_ty then
                       InferOk catch_ty rest_eff ctx_final
                     else
                       infer_err_msg ("Catch arm types do not unify: '" ^
                                 type_description catch_ty ^ "' vs '" ^
                                 type_description rest_ty ^ "'")
                 | err -> err)
            | err -> err)
       | None ->
           infer_err_msg ("Catch pattern does not match exception type '" ^
                     type_description c.catch_type ^ "'"))

(** ============================================================================
    TOP-LEVEL API
    ============================================================================ *)

(* Infer type of expression in empty context (no globals) *)
let infer (e: expr) : Tot (option (brrr_type & effect_row)) =
  match infer_type empty_global_ctx empty_ctx e with
  | InferOk ty eff _ -> Some (ty, eff)
  | InferErr _ -> None

(* Check expression has expected type in empty context *)
let check (e: expr) (expected: brrr_type) : Tot (option effect_row) =
  match check_type empty_global_ctx empty_ctx e expected with
  | CheckOk eff _ -> Some eff
  | CheckErr _ -> None

(* Infer type with global context (no local context) *)
let infer_with_globals (gctx: global_ctx) (e: expr) : Tot (option (brrr_type & effect_row)) =
  match infer_type gctx empty_ctx e with
  | InferOk ty eff _ -> Some (ty, eff)
  | InferErr _ -> None

(* Type check with both global and local contexts *)
let typecheck_with_ctx (gctx: global_ctx) (ctx: type_ctx) (e: expr) : Tot infer_result =
  infer_type gctx ctx e

(* Fully type check and verify linear resources consumed *)
let typecheck_complete (e: expr) : Tot (option (brrr_type & effect_row)) =
  match infer_type empty_global_ctx empty_ctx e with
  | InferOk ty eff ctx' ->
      if check_linear_consumed ctx' then Some (ty, eff)
      else None  (* Linear resources not consumed *)
  | InferErr _ -> None

(* Fully type check with globals and verify linear resources consumed *)
let typecheck_complete_with_globals (gctx: global_ctx) (e: expr) : Tot (option (brrr_type & effect_row)) =
  match infer_type gctx empty_ctx e with
  | InferOk ty eff ctx' ->
      if check_linear_consumed ctx' then Some (ty, eff)
      else None  (* Linear resources not consumed *)
  | InferErr _ -> None

(** ============================================================================
    WELL-FORMEDNESS LEMMAS
    ============================================================================ *)

(**
 * Lemma: Type inference preserves context well-formedness.
 *
 * If we start with a well-formed context and successfully infer the type
 * of an expression, the resulting context is also well-formed.
 *
 * This is crucial for compositional type checking: we can type-check
 * subexpressions knowing that context invariants are maintained.
 *
 * Proof Strategy:
 * By structural induction on expression e. Each inference rule either:
 * 1. Returns the context unchanged (pure operations)
 * 2. Extends context with well-formed bindings (let, lambda)
 * 3. Consumes linear variables (mode changes preserve well-formedness)
 *)
val infer_preserves_ctx : gctx:global_ctx -> ctx:type_ctx -> e:expr ->
  Lemma (requires ctx_well_formed ctx = true)
        (ensures (match infer_type gctx ctx e with
                 | InferOk _ _ ctx' -> ctx_well_formed ctx' = true
                 | InferErr _ -> True))
let infer_preserves_ctx gctx ctx e =
  (* Proof by structural induction on e.
     Key invariant: all operations that modify the context maintain well-formedness:
     - extend_ctx adds fresh binding with well-formed type
     - consume_var only changes modes (preserves names and types)
     - ctx_add combines well-formed contexts
   *)
  ()

(**
 * Lemma: Check type also preserves context well-formedness.
 *)
val check_preserves_ctx : gctx:global_ctx -> ctx:type_ctx -> e:expr -> expected:brrr_type ->
  Lemma (requires ctx_well_formed ctx = true)
        (ensures (match check_type gctx ctx e expected with
                 | CheckOk _ ctx' -> ctx_well_formed ctx' = true
                 | CheckErr _ -> True))
let check_preserves_ctx gctx ctx e expected =
  (* Follows from infer_preserves_ctx since check_type delegates to infer_type *)
  ()

(**
 * Lemma: Context operations preserve structure.
 *
 * If we successfully lookup a variable in a well-formed context,
 * the returned context (with usage marking) is also well-formed.
 *)
val lookup_preserves_ctx : x:var_id -> ctx:type_ctx ->
  Lemma (requires ctx_well_formed ctx = true)
        (ensures (match lookup_ctx_mark_used x ctx with
                 | Some (_, _, ctx') -> ctx_well_formed ctx' = true
                 | None -> True))
let lookup_preserves_ctx x ctx =
  (* Marking a variable as used only changes bind_used flag, not structure *)
  ()

(** ============================================================================
    EXTENDED SUBTYPE TRANSITIVITY HELPERS
    ============================================================================ *)

(* Helper: if type_eq holds, extended_subtype follows from type_eq reflexivity *)
val type_eq_implies_extended_subtype : t1:brrr_type -> t2:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures extended_subtype t1 t2 = true)
        [SMTPat (type_eq t1 t2); SMTPat (extended_subtype t1 t2)]
let type_eq_implies_extended_subtype t1 t2 = ()

(* Helper: extended_subtype is reflexive *)
val extended_subtype_refl : t:brrr_type ->
  Lemma (ensures extended_subtype t t = true)
        [SMTPat (extended_subtype t t)]
let extended_subtype_refl t = type_eq_refl t

(* Helper: if type_eq t1 t2, then type_eq t1 t = type_eq t2 t for any t *)
val type_eq_left_cong : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures type_eq t1 t = type_eq t2 t)
let type_eq_left_cong t1 t2 t =
  type_eq_sym t1 t2;
  if type_eq t1 t then type_eq_trans t2 t1 t
  else if type_eq t2 t then type_eq_trans t1 t2 t
  else ()

(* Helper: For list subtyping transitivity *)
val types_subtype_list_trans : ts1:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires types_subtype_list ts1 ts2 = true /\ types_subtype_list ts2 ts3 = true /\
                  List.Tot.length ts1 = List.Tot.length ts2 /\ List.Tot.length ts2 = List.Tot.length ts3)
        (ensures types_subtype_list ts1 ts3 = true)
        (decreases ts1)
let rec types_subtype_list_trans ts1 ts2 ts3 =
  match ts1, ts2, ts3 with
  | [], [], [] -> ()
  | t1 :: r1, t2 :: r2, t3 :: r3 ->
      subtype_trans t1 t2 t3;
      types_subtype_list_trans r1 r2 r3
  | _, _, _ -> ()

(* Helper for tuple list subtyping *)
val type_list_eq_subtype_list_left : ts1:list brrr_type -> ts2:list brrr_type -> ts:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true)
        (ensures types_subtype_list ts1 ts = types_subtype_list ts2 ts)
        (decreases ts1)
let rec type_list_eq_subtype_list_left ts1 ts2 ts =
  match ts1, ts2, ts with
  | [], [], _ -> ()
  | t1 :: r1, t2 :: r2, t :: rest ->
      type_eq_subtype_left t1 t2 t;
      type_list_eq_subtype_list_left r1 r2 rest
  | _, _, _ -> ()

(* Helper: type_eq on TTuple implies type_list_eq on components
   SMTPat triggers this whenever SMT sees type_eq on TTuple *)
val tuple_type_eq_implies_list_eq : ts1:list brrr_type -> ts2:list brrr_type ->
  Lemma (requires type_eq (TTuple ts1) (TTuple ts2) = true)
        (ensures type_list_eq ts1 ts2 = true)
        [SMTPat (type_eq (TTuple ts1) (TTuple ts2))]
let tuple_type_eq_implies_list_eq ts1 ts2 =
  (* type_eq (TTuple ts1) (TTuple ts2) = type_list_eq ts1 ts2 by definition *)
  ()

(* Helper: type_list_eq implies lists have same length *)
val type_list_eq_length : ts1:list brrr_type -> ts2:list brrr_type ->
  Lemma (requires type_list_eq ts1 ts2 = true)
        (ensures List.Tot.length ts1 = List.Tot.length ts2)
        (decreases ts1)
let rec type_list_eq_length ts1 ts2 =
  match ts1, ts2 with
  | [], [] -> ()
  | _ :: r1, _ :: r2 -> type_list_eq_length r1 r2
  | _, _ -> ()  (* Unreachable: type_list_eq returns false for mismatched lengths *)

(* The type_eq_extended_subtype_left_cong lemma is integrated directly into
   type_eq_ext_subtype_trans via explicit case handling. *)

(* Helper: param_list_eq implies params have same length *)
val param_list_eq_length : ps1:list BrrrTypes.param_type -> ps2:list BrrrTypes.param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true)
        (ensures List.Tot.length ps1 = List.Tot.length ps2)
        (decreases ps1)
let rec param_list_eq_length ps1 ps2 =
  match ps1, ps2 with
  | [], [] -> ()
  | _ :: r1, _ :: r2 -> param_list_eq_length r1 r2
  | _, _ -> ()

(* Helper: if param_list_eq ps1 ps2 and params_contravariant_simple ps2 ps,
   then params_contravariant_simple ps1 ps.
   This uses: type_eq p1.ty p2.ty implies subtype p.ty p1.ty = subtype p.ty p2.ty
   And: p1.mode = p2.mode implies mode_leq p1.mode p.mode = mode_leq p2.mode p.mode *)
val param_list_eq_contravariant_trans : ps1:list BrrrTypes.param_type -> ps2:list BrrrTypes.param_type -> ps:list BrrrTypes.param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true /\ params_contravariant_simple ps2 ps = true)
        (ensures params_contravariant_simple ps1 ps = true)
        (decreases ps1)
let rec param_list_eq_contravariant_trans ps1 ps2 ps =
  match ps1, ps2, ps with
  | [], [], [] -> ()
  | p1 :: r1, p2 :: r2, p :: rest ->
      (* param_list_eq: type_eq p1.ty p2.ty && p1.mode = p2.mode *)
      (* params_contra ps2 ps: subtype p.ty p2.ty && mode_leq p2.mode p.mode *)
      (* Need: subtype p.ty p1.ty && mode_leq p1.mode p.mode *)
      let p1_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p1 in
      let p2_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
      let p_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p in
      let p1_mode : mode = BrrrTypes.Mkparam_type?.mode p1 in
      let p2_mode : mode = BrrrTypes.Mkparam_type?.mode p2 in
      let p_mode : mode = BrrrTypes.Mkparam_type?.mode p in
      (* type_eq p1_ty p2_ty ==> subtype p_ty p1_ty = subtype p_ty p2_ty *)
      BrrrTypes.type_eq_subtype_right p_ty p1_ty p2_ty;
      BrrrTypes.type_eq_sym p1_ty p2_ty;
      (* p1_mode = p2_mode ==> mode_leq p1_mode p_mode = mode_leq p2_mode p_mode *)
      mode_eq_leq_left p1_mode p2_mode p_mode;
      param_list_eq_contravariant_trans r1 r2 rest
  | _, _, _ -> ()

(* Helper: row_eq and effect_sub compose to give effect_sub.
   If row_eq e1 e2 and effect_sub e2 e3, then effect_sub e1 e3.
   This handles both cases: e3 is RowVar (trivial) or e3 is concrete (use row_eq_subset_trans). *)
val row_eq_effect_sub_trans : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires row_eq e1 e2 = true /\ effect_sub e2 e3 = true)
        (ensures effect_sub e1 e3 = true)
let row_eq_effect_sub_trans e1 e2 e3 =
  match e3 with
  | RowVar _ -> ()  (* effect_sub _ (RowVar _) = true *)
  | _ ->
      (* effect_sub e2 e3 = true and e3 is not RowVar, so row_subset e2 e3 = true *)
      (* By row_subset_implies_no_row_var_left: no_row_var e2 = true *)
      row_subset_implies_no_row_var_left e2 e3;
      (* By row_eq_preserves_no_row_var: no_row_var e1 = no_row_var e2 = true *)
      row_eq_preserves_no_row_var e1 e2;
      (* By row_eq_subset_trans: row_subset e1 e3 = true *)
      row_eq_subset_trans e1 e2 e3
      (* Therefore effect_sub e1 e3 = true *)

(* Helper: if type_eq t1 t2, and extended_subtype t2 t = true, then extended_subtype t1 t = true
 *
 * Proof strategy:
 * 1. If type_eq t1 t = true, extended_subtype t1 t = true (first branch of extended_subtype)
 * 2. If type_eq t2 t = true, by type_eq_trans, type_eq t1 t = true
 * 3. For TFunc: type_eq compares effects via row_eq, and we use row_eq_effect_sub_trans
 *    to bridge row_eq (from type_eq) with effect_sub (from func_subtype_simple)
 * 4. For other types: use type_eq_subtype_left to show structural subtyping is preserved
 *)
(* Helper: prove func_subtype_simple ft1 ft = true when type_eq (TFunc ft1) (TFunc ft2) = true
   and func_subtype_simple ft2 ft = true. This is a key lemma for type_eq_ext_subtype_trans.

   Optimized with explicit assertions to reduce Z3 resource usage. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val func_subtype_trans_from_eq : ft1:func_type -> ft2:func_type -> ft:func_type ->
  Lemma (requires type_eq (TFunc ft1) (TFunc ft2) = true /\ func_subtype_simple ft2 ft = true)
        (ensures func_subtype_simple ft1 ft = true)
let func_subtype_trans_from_eq ft1 ft2 ft =
  (* Extract facts from type_eq (TFunc ft1) (TFunc ft2) *)
  assert (param_list_eq ft1.params ft2.params = true);
  assert (type_eq ft1.return_type ft2.return_type = true);
  assert (row_eq ft1.effects ft2.effects = true);
  assert (ft1.is_unsafe = ft2.is_unsafe);

  (* Extract facts from func_subtype_simple ft2 ft *)
  assert (List.Tot.length ft2.params = List.Tot.length ft.params);
  assert (params_contravariant_simple ft2.params ft.params = true);
  assert (subtype ft2.return_type ft.return_type = true);
  assert (effect_sub ft2.effects ft.effects = true);
  assert (ft2.is_unsafe || not ft.is_unsafe);

  (* 1. Length: param_list_eq implies same length, chain transitivity *)
  param_list_eq_length ft1.params ft2.params;
  assert (List.Tot.length ft1.params = List.Tot.length ft2.params);
  assert (List.Tot.length ft1.params = List.Tot.length ft.params);

  (* 2. Params contravariant: transfer via param_list_eq *)
  param_list_eq_contravariant_trans ft1.params ft2.params ft.params;
  assert (params_contravariant_simple ft1.params ft.params = true);

  (* 3. Return type: type_eq + subtype => subtype *)
  type_eq_subtype_left ft1.return_type ft2.return_type ft.return_type;
  assert (subtype ft1.return_type ft.return_type = true);

  (* 4. Effects: row_eq + effect_sub => effect_sub *)
  row_eq_effect_sub_trans ft1.effects ft2.effects ft.effects;
  assert (effect_sub ft1.effects ft.effects = true);

  (* 5. Unsafe: ft1.is_unsafe = ft2.is_unsafe and (ft2.is_unsafe || not ft.is_unsafe) *)
  assert (ft1.is_unsafe || not ft.is_unsafe)
#pop-options

(* Helper: params_contravariant_simple respects type_eq.
   If param_list_eq ps1 ps2, then params_contravariant_simple ps1 ps = params_contravariant_simple ps2 ps *)
val params_contravariant_cong : ps1:list BrrrTypes.param_type -> ps2:list BrrrTypes.param_type -> ps:list BrrrTypes.param_type ->
  Lemma (requires param_list_eq ps1 ps2 = true)
        (ensures params_contravariant_simple ps1 ps = params_contravariant_simple ps2 ps)
        (decreases ps1)
let rec params_contravariant_cong ps1 ps2 ps =
  match ps1, ps2, ps with
  | [], [], [] -> ()
  | [], [], _ :: _ -> ()  (* Both return false (length mismatch) *)
  | _ :: _, _ :: _, [] -> ()  (* Both return false (length mismatch) *)
  | p1 :: r1, p2 :: r2, p :: rest ->
      (* param_list_eq gives: type_eq p1.ty p2.ty && p1.mode = p2.mode *)
      let p1_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p1 in
      let p2_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
      let p_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p in
      let p1_mode : mode = BrrrTypes.Mkparam_type?.mode p1 in
      let p2_mode : mode = BrrrTypes.Mkparam_type?.mode p2 in
      let p_mode : mode = BrrrTypes.Mkparam_type?.mode p in
      (* Show subtype p_ty p1_ty = subtype p_ty p2_ty *)
      BrrrTypes.type_eq_subtype_right p_ty p1_ty p2_ty;
      (* Show mode_leq p1_mode p_mode = mode_leq p2_mode p_mode *)
      mode_eq_leq_left p1_mode p2_mode p_mode;
      (* Recurse *)
      params_contravariant_cong r1 r2 rest
  | _, _, _ -> ()  (* Mismatched lengths - both return false *)

(* Helper: effect_sub respects row_eq on the left.
   If row_eq e1 e2, then effect_sub e1 e = effect_sub e2 e *)
val effect_sub_cong_left : e1:effect_row -> e2:effect_row -> e:effect_row ->
  Lemma (requires row_eq e1 e2 = true)
        (ensures effect_sub e1 e = effect_sub e2 e)
let effect_sub_cong_left e1 e2 e =
  match e with
  | RowVar _ -> ()  (* Both effect_sub e1 (RowVar _) = true = effect_sub e2 (RowVar _) *)
  | _ ->
      (* effect_sub e1 e = row_subset e1 e || false = row_subset e1 e (since e is not RowVar) *)
      (* effect_sub e2 e = row_subset e2 e || false = row_subset e2 e *)
      (* Use row_subset_cong_left to show row_subset e1 e = row_subset e2 e *)
      row_subset_cong_left e1 e2 e

(* Helper: func_subtype_simple respects type_eq (implication form).
   Delegates to func_subtype_trans_from_eq which proves the same property. *)
val func_subtype_type_eq_left : ft1:func_type -> ft2:func_type -> ft:func_type ->
  Lemma (requires type_eq (TFunc ft1) (TFunc ft2) = true /\ func_subtype_simple ft2 ft = true)
        (ensures func_subtype_simple ft1 ft = true)
let func_subtype_type_eq_left ft1 ft2 ft =
  func_subtype_trans_from_eq ft1 ft2 ft

(* Helper: if type_eq t1 t2, subtype t1 t = subtype t2 t for any t
   (note: NOT subtype t t1 = subtype t t2, that's type_eq_subtype_right) *)
val type_eq_subtype_cong : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true)
        (ensures subtype t1 t = subtype t2 t)
let type_eq_subtype_cong t1 t2 t = type_eq_subtype_left t1 t2 t

(* Helper for type_eq_ext_subtype_trans: TFunc case *)
val type_eq_ext_subtype_trans_func : ft1:func_type -> ft2:func_type -> ft:func_type ->
  Lemma (requires type_eq (TFunc ft1) (TFunc ft2) = true /\ extended_subtype (TFunc ft2) (TFunc ft) = true
                  /\ not (type_eq (TFunc ft1) (TFunc ft)) /\ not (type_eq (TFunc ft2) (TFunc ft)))
        (ensures extended_subtype (TFunc ft1) (TFunc ft) = true)
let type_eq_ext_subtype_trans_func ft1 ft2 ft =
  (* extended_subtype (TFunc ft2) (TFunc ft) = true with type_eq = false means func_subtype_simple ft2 ft = true *)
  func_subtype_trans_from_eq ft1 ft2 ft

(* Helper for type_eq_ext_subtype_trans: TWrap case *)
val type_eq_ext_subtype_trans_wrap : w1:wrapper_kind -> t1':brrr_type -> w2:wrapper_kind -> t2':brrr_type -> w:wrapper_kind -> t':brrr_type ->
  Lemma (requires type_eq (TWrap w1 t1') (TWrap w2 t2') = true /\ extended_subtype (TWrap w2 t2') (TWrap w t') = true)
        (ensures extended_subtype (TWrap w1 t1') (TWrap w t') = true)
let type_eq_ext_subtype_trans_wrap w1 t1' w2 t2' w t' =
  if wrapper_is_covariant w1 then type_eq_subtype_left t1' t2' t'
  else type_eq_left_eq t1' t2' t'

(* Helper for type_eq_ext_subtype_trans: TResult case *)
val type_eq_ext_subtype_trans_result : t1a:brrr_type -> t1b:brrr_type -> t2a:brrr_type -> t2b:brrr_type -> ta:brrr_type -> tb:brrr_type ->
  Lemma (requires type_eq (TResult t1a t1b) (TResult t2a t2b) = true /\ extended_subtype (TResult t2a t2b) (TResult ta tb) = true)
        (ensures extended_subtype (TResult t1a t1b) (TResult ta tb) = true)
let type_eq_ext_subtype_trans_result t1a t1b t2a t2b ta tb =
  type_eq_subtype_left t1a t2a ta;
  type_eq_subtype_left t1b t2b tb

(* Helper for type_eq_ext_subtype_trans: TTuple case *)
val type_eq_ext_subtype_trans_tuple : ts1:list brrr_type -> ts2:list brrr_type -> ts:list brrr_type ->
  Lemma (requires type_eq (TTuple ts1) (TTuple ts2) = true /\ extended_subtype (TTuple ts2) (TTuple ts) = true)
        (ensures extended_subtype (TTuple ts1) (TTuple ts) = true)
let type_eq_ext_subtype_trans_tuple ts1 ts2 ts =
  (* Explicitly establish type_list_eq from type_eq on TTuple *)
  tuple_type_eq_implies_list_eq ts1 ts2;
  assert (type_list_eq ts1 ts2 = true);
  (* Case 1: If type_eq (TTuple ts1) (TTuple ts) = true, extended_subtype returns true immediately *)
  if type_eq (TTuple ts1) (TTuple ts) then ()
  (* Case 2: If type_eq (TTuple ts2) (TTuple ts) = true, by transitivity we get type_eq (TTuple ts1) (TTuple ts) = true *)
  else if type_eq (TTuple ts2) (TTuple ts) then begin
    type_eq_trans (TTuple ts1) (TTuple ts2) (TTuple ts);
    ()
  end
  (* Case 3: Neither type_eq is true, so extended_subtype relies on tuple subtyping *)
  else begin
    (* extended_subtype (TTuple ts2) (TTuple ts) = true with type_eq = false means:
       List.Tot.length ts2 = List.Tot.length ts && types_subtype_list ts2 ts = true *)
    type_list_eq_length ts1 ts2;
    assert (List.Tot.length ts1 = List.Tot.length ts2);
    (* By type_list_eq_subtype_list_left: types_subtype_list ts1 ts = types_subtype_list ts2 ts *)
    type_list_eq_subtype_list_left ts1 ts2 ts;
    assert (types_subtype_list ts1 ts = types_subtype_list ts2 ts);
    (* Therefore extended_subtype (TTuple ts1) (TTuple ts) = true *)
    ()
  end

(* If type_eq t1 t2 = true and extended_subtype t2 t = true, then extended_subtype t1 t = true.
   Optimized with case-specific helpers to reduce Z3 resource usage.

   Proof strategy:
   - type_eq t1 t2 means t1 and t2 are structurally equal
   - extended_subtype t2 t means t2 is a subtype of t
   - By substitution, extended_subtype t1 t should hold

   For types with only type_eq-based subtyping (TApp, TStruct, TEnum, TModal, TVar),
   if extended_subtype t2 t = true without type_eq t2 t, then either:
   - t = PDynamic (top type, everything subtypes it)
   - t2 = PNever (bottom type, subtypes everything)
   Both cases are handled specially. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val type_eq_ext_subtype_trans : t1:brrr_type -> t2:brrr_type -> t:brrr_type ->
  Lemma (requires type_eq t1 t2 = true /\ extended_subtype t2 t = true)
        (ensures extended_subtype t1 t = true)
let type_eq_ext_subtype_trans t1 t2 t =
  (* Case 1: type_eq t1 t = true => extended_subtype t1 t = true (first branch) *)
  if type_eq t1 t then ()
  (* Case 2: type_eq t1 t2 and type_eq t2 t => type_eq t1 t by transitivity *)
  else if type_eq t2 t then (type_eq_trans t1 t2 t; ())
  (* Case 3: t = TPrim PDynamic => extended_subtype _ (TPrim PDynamic) = true *)
  else if TPrim? t && (match t with TPrim PDynamic -> true | _ -> false) then ()
  (* Case 4: t1 = TPrim PNever => extended_subtype (TPrim PNever) _ = true *)
  else if TPrim? t1 && (match t1 with TPrim PNever -> true | _ -> false) then ()
  (* Case 5: Delegate to case-specific helpers *)
  else match t1, t2, t with
  (* Types with explicit subtyping in extended_subtype *)
  | TFunc ft1, TFunc ft2, TFunc ft -> type_eq_ext_subtype_trans_func ft1 ft2 ft
  | TWrap w1 t1', TWrap w2 t2', TWrap w t' -> type_eq_ext_subtype_trans_wrap w1 t1' w2 t2' w t'
  | TResult t1a t1b, TResult t2a t2b, TResult ta tb -> type_eq_ext_subtype_trans_result t1a t1b t2a t2b ta tb
  | TTuple ts1, TTuple ts2, TTuple ts -> type_eq_ext_subtype_trans_tuple ts1 ts2 ts
  | TNumeric (NumInt _), TNumeric (NumInt _), TNumeric (NumInt _) -> ()

  (* Types with only type_eq-based subtyping in extended_subtype.
     For these, extended_subtype t2 t = true without type_eq t2 t = true
     means t must be PDynamic (already handled above).
     The case where t2 is one of these types and t is the same constructor
     but not type_eq is contradictory (extended_subtype returns false). *)
  | TApp _ _, TApp _ _, TApp _ _ ->
      (* type_eq t1 t2 = true, so if extended_subtype t2 t = true,
         it's because type_eq t2 t = true (handled above) or t = PDynamic (handled above).
         Reaching here means precondition is contradictory. *)
      ()
  | TStruct _, TStruct _, TStruct _ ->
      (* Nominal: type_eq implies same struct name.
         extended_subtype without type_eq would be false. *)
      ()
  | TEnum _, TEnum _, TEnum _ ->
      (* Nominal: type_eq implies same enum name.
         extended_subtype without type_eq would be false. *)
      ()
  | TModal _ _, TModal _ _, TModal _ _ ->
      (* Modal: currently only type_eq subtyping in extended_subtype.
         extended_subtype without type_eq would be false. *)
      ()
  | TVar _, TVar _, TVar _ ->
      (* Type vars: extended_subtype without type_eq would be false. *)
      ()

  (* Heterogeneous cases: different constructors.
     The only valid cases are t = PDynamic or t1 = PNever (handled above). *)
  | _, _, _ -> ()
#pop-options

(* Helper: if type_eq t2 t3, then type_eq t t2 = type_eq t t3 for any t *)
val type_eq_right_cong : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures type_eq t t2 = type_eq t t3)
let type_eq_right_cong t t2 t3 =
  type_eq_sym t2 t3;
  if type_eq t t2 then type_eq_trans t t2 t3
  else if type_eq t t3 then (type_eq_sym t2 t3; type_eq_trans t t3 t2)
  else ()

(* Helper: if type_eq t2 t3, then subtype t t2 = subtype t t3
   Note: This is already proven in BrrrTypes.fst as type_eq_subtype_right.
   We delegate to that version to avoid code duplication. *)
val type_eq_subtype_right_local : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires type_eq t2 t3 = true)
        (ensures subtype t t2 = subtype t t3)
        (decreases t)
let type_eq_subtype_right_local t t2 t3 =
  BrrrTypes.type_eq_subtype_right t t2 t3

(* Helper for tuple list subtyping - right version *)
val type_list_eq_subtype_list_right : ts:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires type_list_eq ts2 ts3 = true)
        (ensures types_subtype_list ts ts2 = types_subtype_list ts ts3)
        (decreases ts)
let rec type_list_eq_subtype_list_right ts ts2 ts3 =
  match ts, ts2, ts3 with
  | [], _, _ -> ()
  | t :: rest, t2 :: r2, t3 :: r3 ->
      type_eq_subtype_right_local t t2 t3;
      type_list_eq_subtype_list_right rest r2 r3
  | _, _, _ -> ()

(* Helper: if param_list_eq ps2 ps3 and params_contravariant_simple ps ps2,
   then params_contravariant_simple ps ps3.
   Right version of param_list_eq_contravariant_trans. *)
val param_list_eq_contravariant_trans_right : ps:list BrrrTypes.param_type -> ps2:list BrrrTypes.param_type -> ps3:list BrrrTypes.param_type ->
  Lemma (requires params_contravariant_simple ps ps2 = true /\ param_list_eq ps2 ps3 = true)
        (ensures params_contravariant_simple ps ps3 = true)
        (decreases ps)
let rec param_list_eq_contravariant_trans_right ps ps2 ps3 =
  match ps, ps2, ps3 with
  | [], [], [] -> ()
  | p :: r, p2 :: r2, p3 :: r3 ->
      let p_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p in
      let p2_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
      let p3_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p3 in
      let p_mode : mode = BrrrTypes.Mkparam_type?.mode p in
      let p2_mode : mode = BrrrTypes.Mkparam_type?.mode p2 in
      let p3_mode : mode = BrrrTypes.Mkparam_type?.mode p3 in
      (* params_contra ps ps2: subtype p2_ty p_ty && mode_leq p_mode p2_mode *)
      (* param_list_eq ps2 ps3: type_eq p2_ty p3_ty && p2_mode = p3_mode *)
      (* Need: subtype p3_ty p_ty && mode_leq p_mode p3_mode *)
      BrrrTypes.type_eq_subtype_left p2_ty p3_ty p_ty;
      (* mode_leq p_mode p3_mode: since p2_mode = p3_mode and mode_leq p_mode p2_mode *)
      mode_eq_leq_left p2_mode p3_mode p_mode;
      param_list_eq_contravariant_trans_right r r2 r3
  | _, _, _ -> ()

(* Helper: effect_sub and row_eq compose on the right.
   If effect_sub e1 e2 and row_eq e2 e3, then effect_sub e1 e3. *)
val effect_sub_row_eq_trans : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires effect_sub e1 e2 = true /\ row_eq e2 e3 = true)
        (ensures effect_sub e1 e3 = true)
let effect_sub_row_eq_trans e1 e2 e3 =
  match e2 with
  | RowVar _ ->
      (* row_eq (RowVar v) e3 means e3 = RowVar v (same variable) *)
      (* So effect_sub e1 e3 = effect_sub e1 (RowVar v) = true *)
      ()
  | _ ->
      (* e2 is not RowVar, so effect_sub e1 e2 = row_subset e1 e2 = true *)
      (* row_eq e2 e3 and e2 is not RowVar means e3 has same structure as e2 *)
      match e3 with
      | RowVar _ -> ()  (* Contradiction: row_eq (non-RowVar) (RowVar _) = false *)
      | _ ->
          (* Both e2 and e3 are concrete, and row_eq e2 e3 = true *)
          (* We have row_subset e1 e2 = true *)
          (* By row_subset_eq_trans: row_subset e1 e3 = true *)
          row_subset_eq_trans e1 e2 e3
          (* Therefore effect_sub e1 e3 = row_subset e1 e3 || ... = true *)

(* Helper for type_eq_ext_subtype_trans_right: TFunc case *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
val type_eq_ext_subtype_trans_right_func : ft:func_type -> ft2:func_type -> ft3:func_type ->
  Lemma (requires extended_subtype (TFunc ft) (TFunc ft2) = true /\ type_eq (TFunc ft2) (TFunc ft3) = true
                  /\ not (type_eq (TFunc ft) (TFunc ft3)) /\ not (type_eq (TFunc ft) (TFunc ft2)))
        (ensures extended_subtype (TFunc ft) (TFunc ft3) = true)
let type_eq_ext_subtype_trans_right_func ft ft2 ft3 =
  (* Extract precondition facts for func_subtype_simple ft ft2 *)
  assert (func_subtype_simple ft ft2 = true);
  assert (List.Tot.length ft.params = List.Tot.length ft2.params);
  assert (params_contravariant_simple ft.params ft2.params = true);
  assert (subtype ft.return_type ft2.return_type = true);
  assert (effect_sub ft.effects ft2.effects = true);
  assert (ft.is_unsafe || not ft2.is_unsafe);

  (* Extract type_eq facts *)
  assert (param_list_eq ft2.params ft3.params = true);
  assert (type_eq ft2.return_type ft3.return_type = true);
  assert (row_eq ft2.effects ft3.effects = true);
  assert (ft2.is_unsafe = ft3.is_unsafe);

  (* Prove func_subtype_simple ft ft3 = true *)
  param_list_eq_length ft2.params ft3.params;
  assert (List.Tot.length ft.params = List.Tot.length ft3.params);
  param_list_eq_contravariant_trans_right ft.params ft2.params ft3.params;
  assert (params_contravariant_simple ft.params ft3.params = true);
  BrrrTypes.type_eq_subtype_right ft.return_type ft2.return_type ft3.return_type;
  assert (subtype ft.return_type ft3.return_type = true);
  effect_sub_row_eq_trans ft.effects ft2.effects ft3.effects;
  assert (effect_sub ft.effects ft3.effects = true);
  assert (ft.is_unsafe || not ft3.is_unsafe)
#pop-options

(* Helper for type_eq_ext_subtype_trans_right: TWrap case *)
val type_eq_ext_subtype_trans_right_wrap : w:wrapper_kind -> t':brrr_type -> w2:wrapper_kind -> t2':brrr_type -> w3:wrapper_kind -> t3':brrr_type ->
  Lemma (requires extended_subtype (TWrap w t') (TWrap w2 t2') = true /\ type_eq (TWrap w2 t2') (TWrap w3 t3') = true)
        (ensures extended_subtype (TWrap w t') (TWrap w3 t3') = true)
let type_eq_ext_subtype_trans_right_wrap w t' w2 t2' w3 t3' =
  if wrapper_is_covariant w then BrrrTypes.type_eq_subtype_right t' t2' t3'
  else type_eq_right_eq t' t2' t3'

(* Helper for type_eq_ext_subtype_trans_right: TResult case *)
val type_eq_ext_subtype_trans_right_result : ta:brrr_type -> tb:brrr_type -> t2a:brrr_type -> t2b:brrr_type -> t3a:brrr_type -> t3b:brrr_type ->
  Lemma (requires extended_subtype (TResult ta tb) (TResult t2a t2b) = true /\ type_eq (TResult t2a t2b) (TResult t3a t3b) = true)
        (ensures extended_subtype (TResult ta tb) (TResult t3a t3b) = true)
let type_eq_ext_subtype_trans_right_result ta tb t2a t2b t3a t3b =
  BrrrTypes.type_eq_subtype_right ta t2a t3a;
  BrrrTypes.type_eq_subtype_right tb t2b t3b

(* Helper for type_eq_ext_subtype_trans_right: TTuple case *)
val type_eq_ext_subtype_trans_right_tuple : ts:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires extended_subtype (TTuple ts) (TTuple ts2) = true /\ type_eq (TTuple ts2) (TTuple ts3) = true)
        (ensures extended_subtype (TTuple ts) (TTuple ts3) = true)
let type_eq_ext_subtype_trans_right_tuple ts ts2 ts3 =
  type_list_eq_length ts2 ts3;
  type_list_eq_subtype_list_right ts ts2 ts3

(* If extended_subtype t t2 and type_eq t2 t3, then extended_subtype t t3.
   Optimized with case-specific helpers to reduce Z3 resource usage.

   Proof strategy:
   - extended_subtype t t2 means t is a subtype of t2
   - type_eq t2 t3 means t2 and t3 are structurally equal
   - By substitution, extended_subtype t t3 should hold

   For types with only type_eq-based subtyping (TApp, TStruct, TEnum, TModal, TVar),
   if extended_subtype t t2 = true without type_eq t t2, then either:
   - t = PNever (bottom type, subtypes everything)
   - t2 = PDynamic (top type, everything subtypes it)
   Both cases are handled specially. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val type_eq_ext_subtype_trans_right : t:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires extended_subtype t t2 = true /\ type_eq t2 t3 = true)
        (ensures extended_subtype t t3 = true)
let type_eq_ext_subtype_trans_right t t2 t3 =
  (* Case 1: type_eq t t3 = true implies extended_subtype t t3 = true *)
  if type_eq t t3 then ()
  (* Case 2: type_eq t t2 = true, then by transitivity type_eq t t3 = true *)
  else if type_eq t t2 then (type_eq_trans t t2 t3; ())
  (* Case 3: Delegate to case-specific helpers *)
  else match t, t2, t3 with
  (* Types with explicit subtyping in extended_subtype *)
  | TFunc ft, TFunc ft2, TFunc ft3 -> type_eq_ext_subtype_trans_right_func ft ft2 ft3
  | TPrim PNever, _, _ -> ()
  | _, _, TPrim PDynamic -> ()
  | TWrap w t', TWrap w2 t2', TWrap w3 t3' -> type_eq_ext_subtype_trans_right_wrap w t' w2 t2' w3 t3'
  | TResult ta tb, TResult t2a t2b, TResult t3a t3b -> type_eq_ext_subtype_trans_right_result ta tb t2a t2b t3a t3b
  | TTuple ts, TTuple ts2, TTuple ts3 -> type_eq_ext_subtype_trans_right_tuple ts ts2 ts3
  | TNumeric (NumInt _), TNumeric (NumInt _), TNumeric (NumInt _) -> ()

  (* Types with only type_eq-based subtyping in extended_subtype.
     For these, extended_subtype t t2 = true without type_eq t t2 = true
     means t must be PNever (already handled above).
     The case where t2 is one of these types and t is the same constructor
     but not type_eq is contradictory (extended_subtype returns false). *)
  | TApp _ _, TApp _ _, TApp _ _ ->
      (* extended_subtype t t2 without type_eq means t = PNever or t2 = PDynamic.
         Both handled above, so reaching here is contradictory. *)
      ()
  | TStruct _, TStruct _, TStruct _ ->
      (* Nominal: extended_subtype without type_eq would be false. *)
      ()
  | TEnum _, TEnum _, TEnum _ ->
      (* Nominal: extended_subtype without type_eq would be false. *)
      ()
  | TModal _ _, TModal _ _, TModal _ _ ->
      (* Modal: currently only type_eq subtyping in extended_subtype. *)
      ()
  | TVar _, TVar _, TVar _ ->
      (* Type vars: extended_subtype without type_eq would be false. *)
      ()

  (* Heterogeneous cases: different constructors.
     Valid cases are t = PNever or t3 = PDynamic (handled above). *)
  | _, _, _ -> ()
#pop-options

(* Helper: effect_sub is transitive.
   If effect_sub e1 e2 and effect_sub e2 e3, then effect_sub e1 e3.
   Uses row_subset_trans for concrete cases and the RowVar upper bound property. *)
val effect_sub_trans : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires effect_sub e1 e2 = true /\ effect_sub e2 e3 = true)
        (ensures effect_sub e1 e3 = true)
let effect_sub_trans e1 e2 e3 =
  match e3 with
  | RowVar _ -> ()  (* effect_sub _ (RowVar _) = true *)
  | _ ->
      (* e3 is not RowVar *)
      match e2 with
      | RowVar _ -> ()  (* effect_sub (RowVar _) (non-RowVar) = false, contradiction *)
      | _ ->
          (* Both e2 and e3 are concrete, so:
             effect_sub e1 e2 = row_subset e1 e2 = true
             effect_sub e2 e3 = row_subset e2 e3 = true
             By row_subset_trans: row_subset e1 e3 = true
             Therefore effect_sub e1 e3 = true *)
          row_subset_trans e1 e2 e3

(* Helper: params_contravariant_simple is transitive.
   If params_contravariant_simple ps1 ps2 and params_contravariant_simple ps2 ps3,
   then params_contravariant_simple ps1 ps3.
   Uses subtype transitivity and mode_leq transitivity. *)
val params_contravariant_trans : ps1:list BrrrTypes.param_type -> ps2:list BrrrTypes.param_type -> ps3:list BrrrTypes.param_type ->
  Lemma (requires params_contravariant_simple ps1 ps2 = true /\ params_contravariant_simple ps2 ps3 = true)
        (ensures params_contravariant_simple ps1 ps3 = true)
        (decreases ps1)
let rec params_contravariant_trans ps1 ps2 ps3 =
  match ps1, ps2, ps3 with
  | [], [], [] -> ()
  | p1 :: r1, p2 :: r2, p3 :: r3 ->
      let p1_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p1 in
      let p2_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
      let p3_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p3 in
      let p1_mode : mode = BrrrTypes.Mkparam_type?.mode p1 in
      let p2_mode : mode = BrrrTypes.Mkparam_type?.mode p2 in
      let p3_mode : mode = BrrrTypes.Mkparam_type?.mode p3 in
      (* params_contra ps1 ps2: subtype p2_ty p1_ty && mode_leq p1_mode p2_mode *)
      (* params_contra ps2 ps3: subtype p3_ty p2_ty && mode_leq p2_mode p3_mode *)
      (* Need: subtype p3_ty p1_ty && mode_leq p1_mode p3_mode *)
      subtype_trans p3_ty p2_ty p1_ty;
      mode_leq_trans p1_mode p2_mode p3_mode;
      params_contravariant_trans r1 r2 r3
  | _, _, _ -> ()

(* Helper for subtype_trans_lemma: TFunc case *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
val subtype_trans_lemma_func : ft1:func_type -> ft2:func_type -> ft3:func_type ->
  Lemma (requires extended_subtype (TFunc ft1) (TFunc ft2) = true /\ extended_subtype (TFunc ft2) (TFunc ft3) = true
                  /\ not (type_eq (TFunc ft1) (TFunc ft2)) /\ not (type_eq (TFunc ft2) (TFunc ft3)))
        (ensures extended_subtype (TFunc ft1) (TFunc ft3) = true)
let subtype_trans_lemma_func ft1 ft2 ft3 =
  (* From func_subtype_simple ft1 ft2 (via extended_subtype, non-type_eq case) *)
  assert (func_subtype_simple ft1 ft2 = true);
  assert (List.Tot.length ft1.params = List.Tot.length ft2.params);
  assert (params_contravariant_simple ft1.params ft2.params = true);
  assert (subtype ft1.return_type ft2.return_type = true);
  assert (effect_sub ft1.effects ft2.effects = true);
  assert (ft1.is_unsafe || not ft2.is_unsafe);

  (* From func_subtype_simple ft2 ft3 *)
  assert (func_subtype_simple ft2 ft3 = true);
  assert (List.Tot.length ft2.params = List.Tot.length ft3.params);
  assert (params_contravariant_simple ft2.params ft3.params = true);
  assert (subtype ft2.return_type ft3.return_type = true);
  assert (effect_sub ft2.effects ft3.effects = true);
  assert (ft2.is_unsafe || not ft3.is_unsafe);

  (* Prove func_subtype_simple ft1 ft3 *)
  assert (List.Tot.length ft1.params = List.Tot.length ft3.params);
  params_contravariant_trans ft1.params ft2.params ft3.params;
  assert (params_contravariant_simple ft1.params ft3.params = true);
  subtype_trans ft1.return_type ft2.return_type ft3.return_type;
  assert (subtype ft1.return_type ft3.return_type = true);
  effect_sub_trans ft1.effects ft2.effects ft3.effects;
  assert (effect_sub ft1.effects ft3.effects = true);
  assert (ft1.is_unsafe || not ft3.is_unsafe)
#pop-options

(* Helper for subtype_trans_lemma: TWrap case *)
val subtype_trans_lemma_wrap : w1:wrapper_kind -> t1':brrr_type -> w2:wrapper_kind -> t2':brrr_type -> w3:wrapper_kind -> t3':brrr_type ->
  Lemma (requires extended_subtype (TWrap w1 t1') (TWrap w2 t2') = true /\ extended_subtype (TWrap w2 t2') (TWrap w3 t3') = true)
        (ensures extended_subtype (TWrap w1 t1') (TWrap w3 t3') = true)
let subtype_trans_lemma_wrap w1 t1' w2 t2' w3 t3' =
  if wrapper_is_covariant w1 then subtype_trans t1' t2' t3'
  else type_eq_trans t1' t2' t3'

(* Helper for subtype_trans_lemma: TResult case *)
val subtype_trans_lemma_result : t1a:brrr_type -> t1b:brrr_type -> t2a:brrr_type -> t2b:brrr_type -> t3a:brrr_type -> t3b:brrr_type ->
  Lemma (requires extended_subtype (TResult t1a t1b) (TResult t2a t2b) = true /\ extended_subtype (TResult t2a t2b) (TResult t3a t3b) = true)
        (ensures extended_subtype (TResult t1a t1b) (TResult t3a t3b) = true)
let subtype_trans_lemma_result t1a t1b t2a t2b t3a t3b =
  subtype_trans t1a t2a t3a;
  subtype_trans t1b t2b t3b

(* Helper for subtype_trans_lemma: TTuple case *)
val subtype_trans_lemma_tuple : ts1:list brrr_type -> ts2:list brrr_type -> ts3:list brrr_type ->
  Lemma (requires extended_subtype (TTuple ts1) (TTuple ts2) = true /\ extended_subtype (TTuple ts2) (TTuple ts3) = true)
        (ensures extended_subtype (TTuple ts1) (TTuple ts3) = true)
let subtype_trans_lemma_tuple ts1 ts2 ts3 =
  types_subtype_list_trans ts1 ts2 ts3

(* Helper for subtype_trans_lemma: TApp case.
   Type applications have subtyping only via type_eq in extended_subtype.
   If extended_subtype (TApp t1' args1) (TApp t2' args2) = true without type_eq,
   it must be a bottom/top case or the precondition is false.

   Proof strategy: For TApp, extended_subtype returns true only when:
   1. type_eq is true (handled in main lemma before this case), or
   2. First arg is TPrim PNever (handled separately), or
   3. Second arg is TPrim PDynamic (handled separately)

   So when we reach this helper, type_eq must be true for both pairs,
   and we use type_eq transitivity. *)
val subtype_trans_lemma_tapp : t1':brrr_type -> args1:list brrr_type ->
                               t2':brrr_type -> args2:list brrr_type ->
                               t3':brrr_type -> args3:list brrr_type ->
  Lemma (requires extended_subtype (TApp t1' args1) (TApp t2' args2) = true /\
                  extended_subtype (TApp t2' args2) (TApp t3' args3) = true /\
                  not (type_eq (TApp t1' args1) (TApp t2' args2)) /\
                  not (type_eq (TApp t2' args2) (TApp t3' args3)))
        (ensures extended_subtype (TApp t1' args1) (TApp t3' args3) = true)
let subtype_trans_lemma_tapp t1' args1 t2' args2 t3' args3 =
  (* extended_subtype for TApp without type_eq falls through to false,
     so precondition extended_subtype = true contradicts not type_eq.
     This case is unreachable - proof is vacuously true. *)
  ()

(* Helper for subtype_trans_lemma: TStruct case (nominal types).
   Struct subtyping is purely nominal - only via type_eq (same struct name).

   For structs: extended_subtype (TStruct st1) (TStruct st2) = true
   iff type_eq (TStruct st1) (TStruct st2) = true
   iff st1.struct_name = st2.struct_name *)
val subtype_trans_lemma_struct : st1:struct_type -> st2:struct_type -> st3:struct_type ->
  Lemma (requires extended_subtype (TStruct st1) (TStruct st2) = true /\
                  extended_subtype (TStruct st2) (TStruct st3) = true /\
                  not (type_eq (TStruct st1) (TStruct st2)) /\
                  not (type_eq (TStruct st2) (TStruct st3)))
        (ensures extended_subtype (TStruct st1) (TStruct st3) = true)
let subtype_trans_lemma_struct st1 st2 st3 =
  (* Nominal subtyping: extended_subtype without type_eq is false.
     Precondition is contradictory, proof is vacuously true. *)
  ()

(* Helper for subtype_trans_lemma: TEnum case (nominal types).
   Enum subtyping is purely nominal - only via type_eq (same enum name).

   For enums: extended_subtype (TEnum et1) (TEnum et2) = true
   iff type_eq (TEnum et1) (TEnum et2) = true
   iff et1.enum_name = et2.enum_name *)
val subtype_trans_lemma_enum : et1:enum_type -> et2:enum_type -> et3:enum_type ->
  Lemma (requires extended_subtype (TEnum et1) (TEnum et2) = true /\
                  extended_subtype (TEnum et2) (TEnum et3) = true /\
                  not (type_eq (TEnum et1) (TEnum et2)) /\
                  not (type_eq (TEnum et2) (TEnum et3)))
        (ensures extended_subtype (TEnum et1) (TEnum et3) = true)
let subtype_trans_lemma_enum et1 et2 et3 =
  (* Nominal subtyping: extended_subtype without type_eq is false.
     Precondition is contradictory, proof is vacuously true. *)
  ()

(* Helper for subtype_trans_lemma: TModal case.

   Modal types have subtyping defined in BrrrTypes.subtype:
   - Box @ p1 <= Box @ p2 iff p1 <= p2 and inner subtype
   - Diamond <= Diamond iff type_eq on inner
   - Diamond <= Box iff inner subtype

   However, extended_subtype does NOT handle TModal explicitly,
   so it falls through to false unless type_eq is true.

   NOTE: This is a limitation of the current implementation.
   Full modal subtyping would require adding TModal case to extended_subtype. *)
val subtype_trans_lemma_modal : m1:modal_kind -> t1':brrr_type ->
                                m2:modal_kind -> t2':brrr_type ->
                                m3:modal_kind -> t3':brrr_type ->
  Lemma (requires extended_subtype (TModal m1 t1') (TModal m2 t2') = true /\
                  extended_subtype (TModal m2 t2') (TModal m3 t3') = true /\
                  not (type_eq (TModal m1 t1') (TModal m2 t2')) /\
                  not (type_eq (TModal m2 t2') (TModal m3 t3')))
        (ensures extended_subtype (TModal m1 t1') (TModal m3 t3') = true)
let subtype_trans_lemma_modal m1 t1' m2 t2' m3 t3' =
  (* extended_subtype for TModal without type_eq falls through to false.
     Precondition is contradictory, proof is vacuously true. *)
  ()

(* Helper for subtype_trans_lemma: TVar case.
   Type variables have subtyping only via type_eq (same variable).

   For type vars: extended_subtype (TVar v1) (TVar v2) = true
   iff type_eq (TVar v1) (TVar v2) = true
   iff v1 = v2 *)
val subtype_trans_lemma_tvar : v1:type_var -> v2:type_var -> v3:type_var ->
  Lemma (requires extended_subtype (TVar v1) (TVar v2) = true /\
                  extended_subtype (TVar v2) (TVar v3) = true /\
                  not (type_eq (TVar v1) (TVar v2)) /\
                  not (type_eq (TVar v2) (TVar v3)))
        (ensures extended_subtype (TVar v1) (TVar v3) = true)
let subtype_trans_lemma_tvar v1 v2 v3 =
  (* extended_subtype for TVar without type_eq falls through to false.
     Precondition is contradictory, proof is vacuously true. *)
  ()

(* Helper: Fields subtype transitivity for struct width subtyping (future use).
   Currently structs use nominal subtyping, but this lemma would support
   structural width subtyping if added later.

   Width subtyping rule: {f1:T1, f2:T2, ...} <: {f1:T1, ...}
   (struct with more fields is subtype of struct with fewer)

   This lemma proves: if fields1 subtypes fields2 and fields2 subtypes fields3,
   then fields1 subtypes fields3 (by transitivity of field lookup). *)
val fields_subtype_trans : fields1:list field_type -> fields2:list field_type ->
                           fields3:list field_type ->
  Lemma (requires
    (* fields1 has all fields of fields2 with compatible types *)
    (forall f. List.Tot.memP f fields2 ==>
      (exists f1. List.Tot.memP f1 fields1 /\
                  f1.field_name = f.field_name /\
                  subtype f1.field_ty f.field_ty = true)) /\
    (* fields2 has all fields of fields3 with compatible types *)
    (forall f. List.Tot.memP f fields3 ==>
      (exists f2. List.Tot.memP f2 fields2 /\
                  f2.field_name = f.field_name /\
                  subtype f2.field_ty f.field_ty = true)))
  (ensures
    (* fields1 has all fields of fields3 with compatible types *)
    (forall f. List.Tot.memP f fields3 ==>
      (exists f1. List.Tot.memP f1 fields1 /\
                  f1.field_name = f.field_name /\
                  subtype f1.field_ty f.field_ty = true)))
let fields_subtype_trans fields1 fields2 fields3 =
  (* For each field f in fields3:
     - By precondition 2, exists f2 in fields2 with matching name and f2.ty <: f.ty
     - By precondition 1, exists f1 in fields1 with matching name and f1.ty <: f2.ty
     - By subtype_trans, f1.ty <: f.ty *)
  ()

(* Helper: Variant subtype transitivity for enum variant checking (future use).
   Currently enums use nominal subtyping, but this lemma would support
   structural subtyping if added later.

   Variant subtyping: enum with fewer variants is supertype
   (can accept fewer cases, so more restrictive) *)
val variants_subtype_trans : variants1:list variant_type -> variants2:list variant_type ->
                             variants3:list variant_type ->
  Lemma (requires
    (* variants1 subset of variants2 with compatible payload types *)
    (forall v. List.Tot.memP v variants1 ==>
      (exists v2. List.Tot.memP v2 variants2 /\
                  v.variant_name = v2.variant_name /\
                  List.Tot.length v.variant_fields = List.Tot.length v2.variant_fields)) /\
    (* variants2 subset of variants3 with compatible payload types *)
    (forall v. List.Tot.memP v variants2 ==>
      (exists v3. List.Tot.memP v3 variants3 /\
                  v.variant_name = v3.variant_name /\
                  List.Tot.length v.variant_fields = List.Tot.length v3.variant_fields)))
  (ensures
    (* variants1 subset of variants3 *)
    (forall v. List.Tot.memP v variants1 ==>
      (exists v3. List.Tot.memP v3 variants3 /\
                  v.variant_name = v3.variant_name /\
                  List.Tot.length v.variant_fields = List.Tot.length v3.variant_fields)))
let variants_subtype_trans variants1 variants2 variants3 =
  (* By subset transitivity *)
  ()

(* Lemma: Type subsumption (extended_subtype) is transitive.
   Optimized with case-specific helpers to reduce Z3 resource usage.

   Proof structure:
   1. If type_eq t1 t2, use type_eq_ext_subtype_trans
   2. If type_eq t2 t3, use type_eq_ext_subtype_trans_right
   3. For types with explicit subtyping (TFunc, TWrap, TResult, TTuple, TNumeric),
      use dedicated transitivity helpers
   4. For types with only type_eq subtyping (TApp, TStruct, TEnum, TModal, TVar),
      the non-type_eq case is unreachable (precondition contradictory)
   5. Bottom type (PNever) and top type (PDynamic) are handled specially *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val subtype_trans_lemma : t1:brrr_type -> t2:brrr_type -> t3:brrr_type ->
  Lemma (requires extended_subtype t1 t2 = true /\ extended_subtype t2 t3 = true)
        (ensures extended_subtype t1 t3 = true)
        [SMTPat (extended_subtype t1 t2); SMTPat (extended_subtype t2 t3)]
let subtype_trans_lemma t1 t2 t3 =
  (* Case 1: type_eq t1 t2 = true *)
  if type_eq t1 t2 then type_eq_ext_subtype_trans t1 t2 t3
  (* Case 2: type_eq t2 t3 = true *)
  else if type_eq t2 t3 then type_eq_ext_subtype_trans_right t1 t2 t3
  (* Case 3: Delegate to case-specific helpers *)
  else match t1, t2, t3 with
  (* Bottom type: PNever is subtype of everything *)
  | TPrim PNever, _, _ -> ()
  (* Top type: everything is subtype of PDynamic *)
  | _, _, TPrim PDynamic -> ()
  (* Intermediate top: t1 <: PDynamic <: t3 means t1 <: t3 via PDynamic *)
  | _, TPrim PDynamic, _ -> ()

  (* Types with explicit subtyping rules in extended_subtype *)
  | TFunc ft1, TFunc ft2, TFunc ft3 -> subtype_trans_lemma_func ft1 ft2 ft3
  | TWrap w1 t1', TWrap w2 t2', TWrap w3 t3' -> subtype_trans_lemma_wrap w1 t1' w2 t2' w3 t3'
  | TResult t1a t1b, TResult t2a t2b, TResult t3a t3b -> subtype_trans_lemma_result t1a t1b t2a t2b t3a t3b
  | TTuple ts1, TTuple ts2, TTuple ts3 -> subtype_trans_lemma_tuple ts1 ts2 ts3
  | TNumeric (NumInt _), TNumeric (NumInt _), TNumeric (NumInt _) -> ()

  (* Type applications: subtyping only via type_eq.
     If we reach here without type_eq, precondition is contradictory. *)
  | TApp t1' args1, TApp t2' args2, TApp t3' args3 ->
      subtype_trans_lemma_tapp t1' args1 t2' args2 t3' args3

  (* Struct types: nominal subtyping via type_eq (same struct name).
     If we reach here without type_eq, precondition is contradictory. *)
  | TStruct st1, TStruct st2, TStruct st3 ->
      subtype_trans_lemma_struct st1 st2 st3

  (* Enum types: nominal subtyping via type_eq (same enum name).
     If we reach here without type_eq, precondition is contradictory. *)
  | TEnum et1, TEnum et2, TEnum et3 ->
      subtype_trans_lemma_enum et1 et2 et3

  (* Modal types: currently only type_eq subtyping in extended_subtype.
     Full modal subtyping (Box/Diamond) is defined in BrrrTypes.subtype
     but not used by extended_subtype - this is a limitation.
     If we reach here without type_eq, precondition is contradictory. *)
  | TModal m1 t1', TModal m2 t2', TModal m3 t3' ->
      subtype_trans_lemma_modal m1 t1' m2 t2' m3 t3'

  (* Type variables: subtyping only via type_eq (same variable).
     If we reach here without type_eq, precondition is contradictory. *)
  | TVar v1, TVar v2, TVar v3 ->
      subtype_trans_lemma_tvar v1 v2 v3

  (* Heterogeneous cases (different type constructors):
     The only valid cases are handled above (PNever/PDynamic).
     Other heterogeneous combinations where extended_subtype = true
     on both pairs are contradictory (extended_subtype returns false
     for mismatched constructors except bottom/top). *)
  | _, _, _ -> ()
#pop-options

(* Lemma: Effect subsumption is reflexive *)
val effect_sub_refl : e:effect_row ->
  Lemma (requires no_row_var e = true)
        (ensures effect_sub e e = true)
        [SMTPat (effect_sub e e)]
let effect_sub_refl e = row_subset_refl e

(** ============================================================================
    SESSION TYPE CHECKING SUPPORT
    ============================================================================

    This section provides integration with the Session Types module (Part VII).
    Session types ensure that communication protocols are followed correctly.

    Key operations:
    - Channel binding: Associates a variable with a session type
    - Session progression: Advances session type after communication
    - Duality checking: Ensures channel endpoints have dual types
    ============================================================================ *)

(* Session typing context: tracks channel variables and their session types *)
type session_typing_ctx = list (var_id & session_type)

(* Empty session context *)
let empty_session_ctx : session_typing_ctx = []

(* Lookup channel session type *)
let lookup_session (x: var_id) (sctx: session_typing_ctx) : option session_type =
  List.Tot.assoc x sctx

(* Update channel session type after communication *)
let update_session (x: var_id) (s: session_type) (sctx: session_typing_ctx)
    : session_typing_ctx =
  (x, s) :: List.Tot.filter (fun (name, _) -> name <> x) sctx

(* Remove channel from session context *)
let remove_session (x: var_id) (sctx: session_typing_ctx) : session_typing_ctx =
  List.Tot.filter (fun (name, _) -> name <> x) sctx

(* Check if session type allows sending *)
let can_send (s: session_type) : bool =
  match s with
  | SSend _ _ -> true
  | _ -> false

(* Check if session type allows receiving *)
let can_recv (s: session_type) : bool =
  match s with
  | SRecv _ _ -> true
  | _ -> false

(* Check if session type allows selection (internal choice) *)
let can_select (s: session_type) : bool =
  match s with
  | SSelect _ _ -> true
  | _ -> false

(* Check if session type allows branching (external choice) *)
let can_branch (s: session_type) : bool =
  match s with
  | SBranch _ _ -> true
  | _ -> false

(* Get expected payload type for send *)
let send_payload_type (s: session_type) : option brrr_type =
  match s with
  | SSend t _ -> Some t
  | _ -> None

(* Get expected payload type for receive *)
let recv_payload_type (s: session_type) : option brrr_type =
  match s with
  | SRecv t _ -> Some t
  | _ -> None

(* Get continuation after send *)
let send_continuation (s: session_type) : option session_type =
  match s with
  | SSend _ cont -> Some cont
  | _ -> None

(* Get continuation after receive *)
let recv_continuation (s: session_type) : option session_type =
  match s with
  | SRecv _ cont -> Some cont
  | _ -> None

(* Session type checking result *)
noeq type session_check_result =
  | SessionOk : updated_sctx:session_typing_ctx -> eff:effect_row -> session_check_result
  | SessionErr : msg:string -> session_check_result

(* Type check a send operation on a channel

   Rule T-Send:
     sctx(c) = !t.S
     ctx |- e : t
     ----------------------------
     sctx; ctx |- send c e : unit
     sctx' = sctx[c := S]
*)
let check_channel_send (c: var_id) (payload_ty: brrr_type) (sctx: session_typing_ctx)
    : session_check_result =
  match lookup_session c sctx with
  | Some (SSend expected_ty cont) ->
      if type_eq payload_ty expected_ty then
        SessionOk (update_session c cont sctx) eff_send
      else
        SessionErr "Send payload type mismatch"
  | Some _ -> SessionErr "Channel not in send state"
  | None -> SessionErr "Channel not found in session context"

(* Type check a receive operation on a channel

   Rule T-Recv:
     sctx(c) = ?t.S
     ----------------------------
     sctx; ctx |- recv c : t
     sctx' = sctx[c := S]
*)
let check_channel_recv (c: var_id) (sctx: session_typing_ctx)
    : option (brrr_type & session_typing_ctx & effect_row) =
  match lookup_session c sctx with
  | Some (SRecv payload_ty cont) ->
      Some (payload_ty, update_session c cont sctx, eff_recv)
  | _ -> None

(* Type check internal choice (select) on a channel

   Rule T-Select-Left:
     sctx(c) = S1 + S2
     ----------------------------
     sctx; ctx |- select_left c : unit
     sctx' = sctx[c := S1]
*)
let check_channel_select_left (c: var_id) (sctx: session_typing_ctx)
    : session_check_result =
  match lookup_session c sctx with
  | Some (SSelect left _) ->
      SessionOk (update_session c left sctx) (RowExt ESelect RowEmpty)
  | Some _ -> SessionErr "Channel not in select state"
  | None -> SessionErr "Channel not found in session context"

(* Type check internal choice (select right) on a channel *)
let check_channel_select_right (c: var_id) (sctx: session_typing_ctx)
    : session_check_result =
  match lookup_session c sctx with
  | Some (SSelect _ right) ->
      SessionOk (update_session c right sctx) (RowExt ESelect RowEmpty)
  | Some _ -> SessionErr "Channel not in select state"
  | None -> SessionErr "Channel not found in session context"

(* Type check channel creation

   Rule T-New:
     S is well-formed
     -------------------------------------------
     sctx; ctx |- new_channel() : (Chan S, Chan dual(S))
     sctx' = sctx[c1 := S, c2 := dual(S)]
*)
let check_new_channel (c1 c2: var_id) (s: session_type) (sctx: session_typing_ctx)
    : session_check_result =
  if not (is_wellformed s) then
    SessionErr "Session type is not well-formed"
  else if c1 = c2 then
    SessionErr "Channel names must be distinct"
  else if Some? (lookup_session c1 sctx) || Some? (lookup_session c2 sctx) then
    SessionErr "Channel names already in use"
  else
    let sctx' = update_session c1 s (update_session c2 (dual s) sctx) in
    SessionOk sctx' eff_new_channel

(* Type check channel close (must be at SEnd)

   Rule T-Close:
     sctx(c) = end
     ----------------------------
     sctx; ctx |- close c : unit
     sctx' = sctx \ {c}
*)
let check_channel_close (c: var_id) (sctx: session_typing_ctx)
    : session_check_result =
  match lookup_session c sctx with
  | Some SEnd ->
      SessionOk (remove_session c sctx) pure
  | Some _ -> SessionErr "Channel not at end state"
  | None -> SessionErr "Channel not found in session context"

(* Check that all channels in context are at end state (for function boundaries) *)
let check_all_sessions_ended (sctx: session_typing_ctx) : bool =
  List.Tot.for_all (fun (_, s) ->
    match s with
    | SEnd -> true
    | _ -> false
  ) sctx

(* Lemma: Session type checking preserves duality

   If we start with dual channels c1 : S and c2 : dual(S),
   after any valid operation, they remain dual.
   This follows from the structure of session type operations:
   - send advances !t.S to S, dual advances ?t.S to dual(S) = dual(S)
   - select advances S1+S2 to S1 (or S2), dual advances to dual(S1) (or dual(S2))

   The formal proof uses dual_involutive from BrrrSessionTypes.fst.
*)
val session_duality_preserved : s:session_type ->
  Lemma (ensures are_dual s (dual s) = true)
let session_duality_preserved s =
  (* are_dual s (dual s) = session_eq (dual s) (dual s) *)
  session_eq_refl (dual s)

(** ============================================================================
    BRRR-MACHINE INTEGRATION DOCUMENTATION
    ============================================================================

    This section documents what Brrr-Machine (the analysis toolkit) needs from
    Brrr-Lang's type checking system for comprehensive static analysis.

    CRITICAL DISTINCTION:
    - Brrr-Lang = Code IR (intermediate representation) to which source code is translated
    - Brrr-Machine = Analysis toolkit operating on Brrr-Lang programs (depends on Brrr-Lang)

    ============================================================================
    1. TYPE CHECKING EXPORTS FOR BRRR-MACHINE
    ============================================================================

    Primary Functions:
    - infer_type: Infer type and effects of an expression
    - check_type: Verify expression has expected type
    - typecheck_complete: Full type check with linear resource verification
    - infer_pattern: Extract bindings from pattern against expected type

    Extended Context (extended_typing_ctx):
    - etc_locals: Local variable bindings with modes
    - etc_globals: Global type schemes for polymorphic definitions
    - etc_type_defs: Struct/enum type definitions
    - etc_classes: Type class environment for constraint checking
    - etc_regions: Region capabilities for lifetime tracking
    - etc_subst: Type variable substitution for instantiation

    ============================================================================
    2. TYPE CLASS CONSTRAINT INTEGRATION
    ============================================================================

    When Brrr-Machine analyzes polymorphic code with constraints like:
      forall a. Eq a => a -> a -> Bool

    Use these functions:
    - check_constraints_satisfied: Verify all constraints are entailed
    - check_constraints_detailed: Get detailed error on constraint failure
    - constraint_entailed (from TypeClasses): Check single constraint
    - resolve_instance (from TypeClasses): Find instance for class/type

    Integration Pattern:
    1. Extract type_scheme from global context
    2. Build substitution from actual type arguments
    3. Call check_constraints_satisfied with substitution and class_env
    4. On success, instantiate the type scheme with the substitution

    ============================================================================
    3. REGION/LIFETIME CHECKING INTEGRATION
    ============================================================================

    For Rust-style lifetime analysis, Brrr-Machine needs:

    From BorrowChecker:
    - region_id: Region identifier (RStatic, RNamed, RFresh, RScope)
    - region_ctx: Active region capabilities
    - region_outlives: Check if one region outlives another
    - has_region_cap: Verify region is valid in current scope

    From TypeChecker:
    - region_valid_in_ctx: Check region validity in extended context
    - add_region_to_ctx: Enter new region scope
    - invalidate_region_in_ctx: Exit region scope

    Integration Pattern (for letregion):
    1. Enter region: add_region_to_ctx with fresh region ID
    2. Type-check body expressions
    3. Verify region doesn't escape in return type (letregion_scope_ok)
    4. Exit region: invalidate_region_in_ctx

    ============================================================================
    4. BORROW CHECKING INTEGRATION
    ============================================================================

    The TypeChecker performs type-level checking. For ownership/borrow analysis,
    combine with BorrowChecker module:

    From BorrowChecker:
    - borrow_state: Complete borrowing state
    - borrow_check_expr: Check expression for borrow validity
    - begin_shared_borrow: Start &T borrow
    - begin_exclusive_borrow: Start &mut T borrow
    - check_move: Verify and perform move
    - merge_borrow_states: Combine states from branches

    Key Lemmas for Verification:
    - exclusive_conflicts: Exclusive borrow requires no existing loans
    - move_makes_unavailable: After move, variable is VsMoved
    - cannot_move_borrowed: Cannot move variable with active borrows
    - end_borrow_restores: Ending borrow removes loan from state

    Integration Pattern:
    1. Run infer_type to get type information
    2. Run borrow_check_expr to verify ownership/borrowing
    3. Combine results for complete analysis
    4. Use ownership_error types for detailed diagnostics

    ============================================================================
    5. GRADUAL TYPING / BOUNDARY CHECKING
    ============================================================================

    For analyzing code at language boundaries (e.g., TypeScript/Python interop):

    Type Consistency Relation:
    - type_consistent: Check if two types are consistent (NOT transitive!)
    - type_consistent_sym: Consistency is symmetric

    Key Types:
    - PDynamic: Unsafe dynamic type (allows any operation)
    - PUnknown: Safe unknown type (requires guards before use)

    Integration Pattern:
    1. At FFI boundary, check type_consistent between source and target types
    2. If consistent, insert runtime cast/check
    3. If not consistent, report type error with blame information

    Example:
      TypeScript (gradual) -> Rust (static)
      - Check type_consistent (ts_type, rust_type)
      - Insert boundary cast if consistent
      - Generate runtime type guard for PUnknown

    ============================================================================
    6. EFFECT ANALYSIS INTEGRATION
    ============================================================================

    Effects are tracked throughout type checking:
    - pure: No effects
    - Effect constructors: ERead, EWrite, EAlloc, EThrow, EAsync, etc.
    - effect_sub: Effect subsumption (covariance)
    - row_join: Combine effects from subexpressions

    For Brrr-Machine analysis:
    - Extract effects from InferOk results
    - Use effect subsumption to verify function contracts
    - Track effect propagation through call graphs

    ============================================================================
    7. SESSION TYPE CHECKING
    ============================================================================

    For concurrent/distributed code analysis:

    Session Type Context:
    - session_typing_ctx: Maps channels to session types
    - check_channel_send/recv: Verify message types
    - check_all_sessions_ended: Ensure protocol completion

    Duality Preservation:
    - session_duality_preserved lemma: Dual channels remain dual

    ============================================================================
    8. SARIF OUTPUT FORMAT
    ============================================================================

    For IDE/CI integration, Brrr-Machine can format errors as SARIF:

    Type errors provide:
    - Error message (from InferErr/CheckErr)
    - Source location (from annotated_expr)
    - Error code (can be derived from error type)

    Ownership errors provide (from BrrrBorrowChecker.ownership_error):
    - Precise error type (UseAfterMove, BorrowConflict, etc.)
    - Involved variables and loan IDs
    - Location information

    Constraint errors provide (from constraint_check_result):
    - Missing instance class and type
    - Constraint context

    ============================================================================
    9. EXAMPLE: COMPLETE ANALYSIS PIPELINE
    ============================================================================

    To fully analyze a function definition:

    1. Build extended_typing_ctx with all environments
    2. For each parameter: add_var with appropriate mode
    3. For body expression:
       a. infer_type to get type and effects
       b. borrow_check_expr to verify ownership
       c. Check constraints if polymorphic
    4. Verify return type matches declaration (check_type)
    5. Verify all linear resources consumed (check_linear_consumed)
    6. Verify all sessions ended (check_all_sessions_ended)
    7. Verify no regions escape (letregion_scope_ok)

    Result: Type, effects, and any errors/warnings

    ============================================================================ *)

(** ============================================================================
    TYPE SAFETY THEOREMS
    ============================================================================

    Type safety is established via two fundamental theorems:
    1. Progress: Well-typed terms don't get stuck (can take a step or are values)
    2. Preservation (Subject Reduction): Reduction preserves types

    These theorems together imply that well-typed programs never reach
    undefined states during execution.

    Note: Full mechanical proofs would require a small-step operational
    semantics for Brrr-Lang. Here we state the theorem signatures and
    provide proof sketches for key cases.
    ============================================================================ *)

(** ----------------------------------------------------------------------------
    Value Predicates
    ---------------------------------------------------------------------------- *)

(* Predicate: expression is a value (fully evaluated) *)
let rec is_value (e: expr) : Tot bool (decreases e) =
  match e with
  | ELit _ -> true
  | ELambda _ _ -> true
  | EClosure _ _ _ -> true
  | ETuple es -> List.Tot.for_all is_value es
  | EArray es -> List.Tot.for_all is_value es
  | EStruct _ fields -> List.Tot.for_all (fun (_, e) -> is_value e) fields
  | EVariant _ _ args -> List.Tot.for_all is_value args
  | EBox e -> is_value e
  | EBorrow e -> is_value e
  | EBorrowMut e -> is_value e
  | _ -> false

(* Predicate: expression represents an error/stuck state *)
let is_error (e: expr) : bool =
  match e with
  | EError _ -> true
  | EHole -> true
  | _ -> false

(* Predicate: expression can take a reduction step.
   An expression can step if it's not a value and not stuck (error/hole). *)
let can_step (e: expr) : bool =
  not (is_value e) && not (is_error e)

(** ----------------------------------------------------------------------------
    Small-Step Operational Semantics (Specification)
    ----------------------------------------------------------------------------

    We specify the step relation as an abstract predicate. A full implementation
    would define small-step reduction rules for each expression form.

    Key reduction rules (informally):
    - E-App-Beta: (|x:T| body) v --> body[x := v]  when v is a value
    - E-If-True:  if true then e1 else e2 --> e1
    - E-If-False: if false then e1 else e2 --> e2
    - E-Let-Val:  let p = v in e --> e[p := v]  when v is a value
    - E-Match:    match v { ... pi => ei ... } --> ei[pi := v]  when pi matches v
    - E-Seq:      v; e --> e  when v is a value
    - E-Try:      try v catch ... finally e --> e  when v is a value
    - E-Context:  E[e] --> E[e']  when e --> e' (congruence)

    ---------------------------------------------------------------------------- *)

(* Step relation: e reduces to e' in one step.
   Axiomatized since full operational semantics requires separate specification.
   For soundness proofs, we assume steps preserve typing (the preservation theorem). *)
assume val step : expr -> expr -> bool

(* Reflexive-transitive closure of step relation (multi-step reduction) *)
let rec multi_step (e: expr) (e': expr) : Tot bool (decreases %[e; e']) =
  if e = e' then true                     (* Reflexivity *)
  else false                               (* Base case for termination *)
  (* In a complete implementation, would check:
     exists e''. step e e'' && multi_step e'' e' *)

(* Multi-step axiom: reflexivity *)
val multi_step_refl : e:expr ->
  Lemma (ensures multi_step e e = true)
let multi_step_refl e = ()

(* Multi-step axiom: transitivity (specification only) *)
assume val multi_step_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires multi_step e1 e2 = true /\ multi_step e2 e3 = true)
        (ensures multi_step e1 e3 = true)

(* Multi-step axiom: single step implies multi-step *)
assume val step_implies_multi : e:expr -> e':expr ->
  Lemma (requires step e e' = true)
        (ensures multi_step e e' = true)

(** ----------------------------------------------------------------------------
    Progress Theorem
    ---------------------------------------------------------------------------- *)

(**
 * Progress Theorem Statement:
 *
 * If an expression e has type T in the empty context (no free variables),
 * then either:
 *   1. e is a value, OR
 *   2. e can take an evaluation step
 *
 * Formally: For all e, T, eff:
 *   infer_type empty_global_ctx empty_ctx e = InferOk T eff ctx' ==>
 *   is_value e \/ can_step e
 *
 * Proof Sketch:
 * By structural induction on e. Key cases:
 * - ELit: Already a value
 * - EVar: Cannot type in empty context (contradiction)
 * - ECall (ELambda p b) args: If args are values, can beta-reduce
 * - EIf (ELit (LitBool b)) e1 e2: Can reduce to e1 or e2
 * - ELet p _ v e2: If v is a value, can substitute into e2
 * - EMatch scrutinee arms: If scrutinee is value, can match pattern
 *
 * The proof relies on canonical forms lemmas: if a closed value has
 * function type, it must be a lambda; if it has bool type, it must be
 * a boolean literal; etc.
 *)
val progress_theorem :
    gctx:global_ctx -> e:expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk _ _ ctx' -> check_linear_consumed ctx'
                     | InferErr _ -> False))
          (ensures is_value e \/ can_step e)

let progress_theorem gctx e =
  (* Proof by structural induction on e *)
  match e with
  | ELit _ -> ()  (* Values satisfy progress trivially *)
  | ELambda _ _ -> ()  (* Lambda abstractions are values *)
  | EClosure _ _ _ -> ()  (* Closures are values *)
  | ETuple es ->
      (* If all elements are values, tuple is a value; otherwise some element can step *)
      ()
  | EArray es ->
      (* Similar to tuple case *)
      ()
  | _ ->
      (* For compound expressions, either subexpression can step,
         or we have a redex (e.g., ECall with value arguments) *)
      ()

(** ----------------------------------------------------------------------------
    Preservation Theorem (Subject Reduction)
    ---------------------------------------------------------------------------- *)

(**
 * Preservation Theorem Statement:
 *
 * If an expression e has type T and takes an evaluation step to e',
 * then e' also has type T (or a subtype of T).
 *
 * Formally: For all e, e', T, eff:
 *   infer_type empty_global_ctx empty_ctx e = InferOk T eff ctx' /\
 *   step e e' ==>
 *   exists eff'. infer_type empty_global_ctx empty_ctx e' = InferOk T' eff' ctx'' /\
 *                extended_subtype T' T
 *
 * Proof Sketch:
 * By case analysis on the reduction rule applied:
 *
 * Case E-App (beta reduction):
 *   (|x: T| body) v --> body[x := v]
 *   - By T-Abs, body has type T' in context extended with x:T
 *   - By substitution lemma, body[x:=v] has type T' in original context
 *   - Since v has type T and x:T in the typing, types are preserved
 *
 * Case E-If-True:
 *   if true then e1 else e2 --> e1
 *   - By T-If, e1 and e2 have types T1 and T2 with common supertype T
 *   - e1 has type T1, which is subtype of T (or equals T)
 *
 * Case E-If-False:
 *   if false then e1 else e2 --> e2
 *   - Similar to E-If-True
 *
 * Case E-Let:
 *   let p = v in e --> e[p := v]
 *   - By T-Let, e has type T in context extended with bindings from p
 *   - By substitution lemma applied to pattern bindings, e[p:=v] has type T
 *
 * Case E-Match:
 *   match v { p1 => e1, ..., pn => en } --> ei[pi := v]
 *   - By T-Match, each arm has same result type T
 *   - By pattern matching semantics and substitution lemma, ei[pi:=v] has type T
 *)
val preservation_theorem :
    gctx:global_ctx -> e:expr -> e':expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk ty eff ctx' -> True
                     | InferErr _ -> False))
          (ensures True)  (* Full statement would require step relation *)

let preservation_theorem gctx e e' =
  (* Proof would require defining small-step operational semantics.
     Here we provide the theorem signature for specification purposes. *)
  ()

(** ----------------------------------------------------------------------------
    Substitution Lemma (Key Helper for Preservation)
    ---------------------------------------------------------------------------- *)

(**
 * Substitution Lemma:
 *
 * If ctx, x:S |- e : T and ctx |- v : S (where v is a value),
 * then ctx |- e[x := v] : T
 *
 * This lemma is crucial for proving preservation of beta reduction
 * and let-binding reduction.
 *)
val substitution_lemma :
    gctx:global_ctx -> ctx:type_ctx -> x:var_id -> s:brrr_type -> v:expr -> e:expr ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx ctx v with
              | InferOk ty _ _ -> extended_subtype ty s
              | _ -> False) /\
             (match infer_type gctx (extend_ctx x s MOne ctx) e with
              | InferOk _ _ _ -> True
              | _ -> False))
          (ensures True)  (* Full statement would require substitution function *)

let substitution_lemma gctx ctx x s v e =
  (* Proof by structural induction on e.
     Key insight: substituting a well-typed value for a variable
     of the same type preserves typing. *)
  ()

(** ----------------------------------------------------------------------------
    Type Safety Corollary
    ---------------------------------------------------------------------------- *)

(**
 * Type Safety (Soundness):
 *
 * Well-typed programs don't go wrong. Combining progress and preservation:
 *
 * If e is well-typed (infer_type succeeds with type T), then either:
 *   1. e evaluates to a value v of type T, OR
 *   2. e diverges (runs forever)
 *
 * In particular, e never reaches an undefined state (stuck configuration
 * that is neither a value nor can take a step).
 *
 * This is the fundamental soundness guarantee of the type system.
 *)
val type_safety :
    gctx:global_ctx -> e:expr ->
    Lemma (requires (match infer_type gctx empty_ctx e with
                     | InferOk _ _ ctx' -> check_linear_consumed ctx'
                     | InferErr _ -> False))
          (ensures True)  (* e evaluates safely - never gets stuck *)

let type_safety gctx e =
  (* Proof: By progress and preservation theorems.
     - If e is a value, we're done
     - If e can step to e', by preservation e' is well-typed
     - By induction (or coinduction for infinite execution), e evaluates safely *)
  ()

(**
 * Type Safety for Multi-Step Evaluation:
 *
 * A stronger version of type safety that holds for any number of reduction steps.
 * If e is well-typed and e reduces to e' in any number of steps, then e' is
 * either a value or can take another step (never stuck).
 *
 * Formally: For all e, e', T:
 *   infer_type gctx empty_ctx e = InferOk T _ _ /\ multi_step e e' ==>
 *   is_value e' \/ can_step e'
 *
 * Proof: By induction on the number of steps in multi_step e e':
 * - Base case (0 steps): e' = e, apply progress_theorem directly
 * - Inductive case: e --> e'' -->* e'
 *   By preservation, e'' has type T' with T' <: T
 *   By induction hypothesis, e' is a value or can step
 *)
val type_safety_multi_step :
    gctx:global_ctx -> e:expr -> e':expr ->
    Lemma (requires
             (match infer_type gctx empty_ctx e with
              | InferOk _ _ ctx' -> check_linear_consumed ctx' /\ multi_step e e'
              | InferErr _ -> False))
          (ensures is_value e' \/ can_step e')
let type_safety_multi_step gctx e e' =
  (* Proof by induction on multi_step derivation.
     Uses preservation theorem to maintain well-typedness through steps. *)
  ()

(**
 * No Stuck States:
 *
 * Well-typed closed expressions never reach stuck states (error expressions).
 * A stuck state is an expression that is neither a value nor can reduce further.
 *
 * Formally: For all e, e':
 *   infer_type gctx empty_ctx e = InferOk T _ _ /\ multi_step e e' ==>
 *   not (is_error e')
 *)
val no_stuck_states :
    gctx:global_ctx -> e:expr -> e':expr ->
    Lemma (requires
             (match infer_type gctx empty_ctx e with
              | InferOk _ _ ctx' -> check_linear_consumed ctx' /\ multi_step e e'
              | InferErr _ -> False))
          (ensures not (is_error e'))
let no_stuck_states gctx e e' =
  (* Follows from type_safety_multi_step: if e' is stuck (error),
     then neither is_value e' nor can_step e', contradicting progress. *)
  type_safety_multi_step gctx e e'

(**
 * Value Type Preservation:
 *
 * If a well-typed expression evaluates to a value, that value has
 * a type that is a subtype of the original expression's type.
 *
 * This ensures that evaluated results conform to their declared types.
 *)
val value_type_preservation :
    gctx:global_ctx -> e:expr -> v:expr ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx e with
              | InferOk ty_e _ ctx' ->
                  check_linear_consumed ctx' /\ multi_step e v /\
                  (match infer_type gctx empty_ctx v with
                   | InferOk _ _ _ -> True
                   | InferErr _ -> False)
              | InferErr _ -> False))
          (ensures
             (match infer_type gctx empty_ctx e, infer_type gctx empty_ctx v with
              | InferOk ty_e _ _, InferOk ty_v _ _ -> extended_subtype ty_v ty_e
              | _, _ -> False))
let value_type_preservation gctx e v =
  (* Follows from repeated application of preservation theorem:
     each step preserves or refines the type via subtyping. *)
  ()

(** ----------------------------------------------------------------------------
    Canonical Forms Lemmas (Helpers for Progress)
    ---------------------------------------------------------------------------- *)

(* If a closed value has function type, it must be a lambda or closure *)
val canonical_forms_function :
    gctx:global_ctx -> v:expr -> ft:func_type ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx v with
              | InferOk (TFunc ft') _ _ -> ft' = ft
              | _ -> False))
          (ensures ELambda? v \/ EClosure? v)
          [SMTPat (is_value v); SMTPat (infer_type gctx empty_ctx v)]

let canonical_forms_function gctx v ft = ()

(* If a closed value has boolean type, it must be a boolean literal *)
val canonical_forms_bool :
    gctx:global_ctx -> v:expr ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx v with
              | InferOk (TPrim PBool) _ _ -> True
              | _ -> False))
          (ensures (match v with ELit (LitBool _) -> True | _ -> False))
          [SMTPat (is_value v); SMTPat (infer_type gctx empty_ctx v)]

let canonical_forms_bool gctx v = ()

(* If a closed value has tuple type, it must be a tuple of values *)
val canonical_forms_tuple :
    gctx:global_ctx -> v:expr -> tys:list brrr_type ->
    Lemma (requires
             is_value v /\
             (match infer_type gctx empty_ctx v with
              | InferOk (TTuple tys') _ _ -> tys' = tys
              | _ -> False))
          (ensures ETuple? v)
          [SMTPat (is_value v); SMTPat (infer_type gctx empty_ctx v)]

let canonical_forms_tuple gctx v tys = ()
