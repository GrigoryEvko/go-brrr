(**
 * Brrr-Lang Translation Layer Specification
 *
 * This module defines translation functors from source languages to Brrr-Lang IR.
 * Each translation is a compositional, sound mapping that preserves semantic properties.
 *
 * Based on brrr_lang_spec_v0.4.md Part VI (Source Language Mapping)
 *
 * Translation targets:
 *   1. Rust -> Brrr-Lang (ownership model, lifetimes, traits)
 *   2. TypeScript -> Brrr-Lang (union types, gradual typing, async)
 *   3. Python -> Brrr-Lang (dynamic types, duck typing, decorators)
 *   4. Go -> Brrr-Lang (interfaces, goroutines, channels)
 *
 * Categorical foundation:
 *   Each language L forms a category Cat_L with types as objects and functions as morphisms.
 *   Translation T : Cat_L -> Cat_Brrr is a functor preserving identity and composition.
 *)
module TranslationSpec

(** Z3 solver options - conservative settings for translation proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open PythonTypes  (* Canonical Python type definitions - single source of truth *)

(** ============================================================================
    TRANSLATION FUNCTOR INTERFACE
    ============================================================================ *)

(* Source language identifier *)
type source_language =
  | LangRust
  | LangTypeScript
  | LangPython
  | LangGo
  | LangSwift
  | LangJava
  | LangC
  | LangCpp

(* Language configuration parameters - from spec Definition 2.1 *)
type lang_config = {
  memory_model    : memory_mode;
  type_discipline : type_mode;
  null_handling   : null_mode;
  effect_tracking : effect_mode;
  concurrency     : concurrency_mode
}

and memory_mode =
  | MemOwnership   (* Affine types, move semantics - Rust *)
  | MemRC          (* Reference counting - Swift *)
  | MemGC          (* Garbage collection - Python, Go, TypeScript, Java *)
  | MemManual      (* Manual allocation - C/C++ *)

and type_mode =
  | TypeStatic     (* Fully static - Rust, Go, Java *)
  | TypeGradual    (* Gradual typing - TypeScript *)
  | TypeDynamic    (* Fully dynamic - Python *)

and null_mode =
  | NullNonNull    (* No null - Rust Option, Swift Optional *)
  | NullOptional   (* Explicit optional types - Kotlin *)
  | NullNullable   (* Implicit nullable - Python, Go, Java, TypeScript *)

and effect_mode =
  | EffPure        (* Effects tracked precisely *)
  | EffTracked     (* Effects tracked coarsely *)
  | EffUntracked   (* Effects not tracked *)

and concurrency_mode =
  | ConcNone       (* No concurrency primitives *)
  | ConcThreads    (* OS threads - C/C++, Java *)
  | ConcAsync      (* Async/await - TypeScript, Rust, Swift *)
  | ConcCSP        (* CSP channels - Go *)
  | ConcActors     (* Actor model - Swift actors *)

(* Get configuration for a language *)
let lang_config_of (lang: source_language) : lang_config =
  match lang with
  | LangRust -> {
      memory_model = MemOwnership;
      type_discipline = TypeStatic;
      null_handling = NullNonNull;
      effect_tracking = EffUntracked;
      concurrency = ConcAsync
    }
  | LangTypeScript -> {
      memory_model = MemGC;
      type_discipline = TypeGradual;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcAsync
    }
  | LangPython -> {
      memory_model = MemGC;
      type_discipline = TypeDynamic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcNone
    }
  | LangGo -> {
      memory_model = MemGC;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcCSP
    }
  | LangSwift -> {
      memory_model = MemRC;
      type_discipline = TypeStatic;
      null_handling = NullNonNull;
      effect_tracking = EffTracked;
      concurrency = ConcActors
    }
  | LangJava -> {
      memory_model = MemGC;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffTracked;
      concurrency = ConcThreads
    }
  | LangC -> {
      memory_model = MemManual;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcThreads
    }
  | LangCpp -> {
      memory_model = MemManual;
      type_discipline = TypeStatic;
      null_handling = NullNullable;
      effect_tracking = EffUntracked;
      concurrency = ConcThreads
    }

(** ============================================================================
    SOURCE LOCATION TYPES FOR TRANSLATION
    ============================================================================

    Following EverParse's with_meta_t pattern and matching PythonTypes.fst:
    - All translation results carry source_range for precise error reporting
    - Errors include source file:line:col for debugging
    - Warnings preserve original source location

    Reference: EverParse src/3d/Ast.fst lines 146-148:
      let error #a msg (r:range) : ML a =
        raise (Error (Printf.sprintf "%s: (Error) %s\n" (string_of_pos (fst r)) msg))
    ============================================================================ *)

(** Translation source range - reuses Expressions.fst types *)
let trans_range = range

(** Dummy range for synthetic translations *)
let dummy_trans_range : trans_range = dummy_range

(** Translation result - carries translated item plus source location and diagnostics.
    All variants carry source_range for precise error reporting.

    Following the same pattern as PythonTypes.py_trans_result. *)
noeq type trans_result (a: Type) =
  | TransOk    : value:a -> source_range:trans_range -> trans_result a
  | TransApprox: value:a -> reason:string -> source_range:trans_range -> trans_result a  (* Sound approximation *)
  | TransError : reason:string -> source_range:trans_range -> trans_result a

(** Check if translation succeeded (exact or approximate) *)
let trans_is_success (#a: Type) (r: trans_result a) : bool =
  match r with
  | TransOk _ _ -> true
  | TransApprox _ _ _ -> true
  | TransError _ _ -> false

(** Extract value from successful translation *)
let trans_get_value (#a: Type) (r: trans_result a{trans_is_success r}) : a =
  match r with
  | TransOk v _ -> v
  | TransApprox v _ _ -> v

(** Translation context - carries state during translation.

    Following EverParse's env pattern (Binding.fst):
    - Tracks current source location for error reporting
    - Maintains type/lifetime environments
    - Generates fresh node IDs *)
noeq type trans_ctx = {
  source_lang    : source_language;
  config         : lang_config;
  type_env       : list (string & brrr_type);   (* Type bindings *)
  lifetime_env   : list (string & region);       (* Lifetime -> region mapping *)
  effect_vars    : list string;                  (* Effect variable names *)
  next_node_id   : nat;                          (* Fresh node ID counter *)
  current_range  : trans_range                   (* Current source location for error reporting *)
}

(** Create initial translation context *)
let init_ctx (lang: source_language) : trans_ctx = {
  source_lang = lang;
  config = lang_config_of lang;
  type_env = [];
  lifetime_env = [];
  effect_vars = [];
  next_node_id = 0;
  current_range = dummy_trans_range
}

(** Create translation context at a specific source location *)
let init_ctx_at (lang: source_language) (r: trans_range) : trans_ctx = {
  source_lang = lang;
  config = lang_config_of lang;
  type_env = [];
  lifetime_env = [];
  effect_vars = [];
  next_node_id = 0;
  current_range = r
}

(** Update context to track current source location *)
let ctx_at_range (ctx: trans_ctx) (r: trans_range) : trans_ctx =
  { ctx with current_range = r }

(** Create error result using context's current range *)
let ctx_error (ctx: trans_ctx) (msg: string) : trans_result 'a =
  TransError msg ctx.current_range

(** Create success result using context's current range *)
let ctx_ok (ctx: trans_ctx) (v: 'a) : trans_result 'a =
  TransOk v ctx.current_range

(** Create approximation result using context's current range *)
let ctx_approx (ctx: trans_ctx) (v: 'a) (reason: string) : trans_result 'a =
  TransApprox v reason ctx.current_range

(** Extract source range from any translation result *)
let trans_get_range (#a: Type) (r: trans_result a) : trans_range =
  match r with
  | TransOk _ range -> range
  | TransApprox _ _ range -> range
  | TransError _ range -> range

(** Format error message with source location.
    Following EverParse's error function pattern (Ast.fst lines 146-148). *)
let trans_format_error (#a: Type) (r: trans_result a{TransError? r}) : string =
  match r with
  | TransError msg range ->
      string_of_range range ^ ": (Error) " ^ msg

(** Format approximation warning with source location *)
let trans_format_warning (#a: Type) (r: trans_result a{TransApprox? r _ _}) : string =
  match r with
  | TransApprox _ msg range ->
      string_of_range range ^ ": (Warning) " ^ msg

(** Map over translation result, preserving source location *)
let trans_map (#a #b: Type) (f: a -> b) (r: trans_result a) : trans_result b =
  match r with
  | TransOk v range -> TransOk (f v) range
  | TransApprox v reason range -> TransApprox (f v) reason range
  | TransError reason range -> TransError reason range

(** Bind/flatMap over translation results *)
let trans_bind (#a #b: Type) (r: trans_result a) (f: a -> trans_result b) : trans_result b =
  match r with
  | TransOk v _ -> f v
  | TransApprox v reason range ->
      (match f v with
       | TransOk v' _ -> TransApprox v' reason range
       | TransApprox v' reason' _ -> TransApprox v' (reason ^ "; " ^ reason') range
       | TransError reason' range' -> TransError reason' range')
  | TransError reason range -> TransError reason range

(** Combine two translation results with a binary operation.
    Uses the range from the first result for the combined result. *)
let trans_combine (#a #b #c: Type) (f: a -> b -> c)
                  (r1: trans_result a) (r2: trans_result b)
    : trans_result c =
  match r1, r2 with
  | TransOk v1 range1, TransOk v2 _ ->
      TransOk (f v1 v2) range1
  | TransError reason range, _ ->
      TransError reason range
  | _, TransError reason range ->
      TransError reason range
  | TransApprox v1 r1 range1, TransApprox v2 r2 _ ->
      TransApprox (f v1 v2) (r1 ^ "; " ^ r2) range1
  | TransApprox v1 r range1, TransOk v2 _ ->
      TransApprox (f v1 v2) r range1
  | TransOk v1 range1, TransApprox v2 r _ ->
      TransApprox (f v1 v2) r range1

(** Create a success result from an expression, extracting its range *)
let trans_ok_from (e: expr) (result: 'a) : trans_result 'a =
  TransOk result (loc_of e)

(** Create an approximation result from an expression, extracting its range *)
let trans_approx_from (e: expr) (result: 'a) (reason: string) : trans_result 'a =
  TransApprox result reason (loc_of e)

(** Create an error result from an expression, extracting its range *)
let trans_error_from (e: expr) (reason: string) : trans_result 'a =
  TransError reason (loc_of e)

(** Create an error result at a specific range *)
let trans_error_at (r: trans_range) (reason: string) : trans_result 'a =
  TransError reason r

(** Create a success result at a specific range *)
let trans_ok_at (r: trans_range) (result: 'a) : trans_result 'a =
  TransOk result r

(** Create an approximation result at a specific range *)
let trans_approx_at (r: trans_range) (result: 'a) (reason: string) : trans_result 'a =
  TransApprox result reason r

(* Default effect row for each language *)
let default_effects (lang: source_language) : effect_row =
  match lang with
  | LangRust -> pure  (* Rust tracks effects via return types *)
  | LangTypeScript -> RowExt (EThrow "Error") (RowExt EAsync (RowVar "epsilon"))
  | LangPython -> RowExt (EThrow "Exception") (RowExt EIO (RowVar "epsilon"))
  | LangGo -> RowExt EPanic (RowExt ESpawn (RowVar "epsilon"))
  | LangSwift -> RowExt (EThrow "Error") (RowExt EAsync (RowVar "epsilon"))
  | LangJava -> RowExt (EThrow "Throwable") (RowVar "epsilon")
  | LangC -> RowVar "epsilon"  (* C: unknown effects *)
  | LangCpp -> RowExt (EThrow "exception") (RowVar "epsilon")

(** ============================================================================
    PART 1: RUST -> BRRR-LANG TRANSLATION
    ============================================================================

    Key mappings:
      - Ownership: T -> own T, &T -> ref T, &mut T -> refmut T
      - Lifetimes: 'a -> region 'a with outlives constraints
      - Traits: trait Foo -> type class Foo
      - Move semantics: let y = x -> let y = move(x) for non-Copy types

    Soundness: If Rust borrow checker accepts P, then T_Rs(P) is ownership-safe.
    ============================================================================ *)

(* Rust ownership annotation *)
type rust_ownership =
  | RsOwned                           (* T - owned value *)
  | RsRef       : lifetime:string -> rust_ownership  (* &'a T - shared borrow *)
  | RsRefMut    : lifetime:string -> rust_ownership  (* &'a mut T - exclusive borrow *)
  | RsRc                              (* Rc<T> - reference counted *)
  | RsArc                             (* Arc<T> - atomic RC *)
  | RsBox                             (* Box<T> - owned heap *)

(* Rust base type *)
noeq type rust_type =
  | RsBool    : rust_type
  | RsI8      : rust_type
  | RsI16     : rust_type
  | RsI32     : rust_type
  | RsI64     : rust_type
  | RsI128    : rust_type
  | RsIsize   : rust_type
  | RsU8      : rust_type
  | RsU16     : rust_type
  | RsU32     : rust_type
  | RsU64     : rust_type
  | RsU128    : rust_type
  | RsUsize   : rust_type
  | RsF32     : rust_type
  | RsF64     : rust_type
  | RsChar    : rust_type
  | RsStr     : rust_type              (* String slice *)
  | RsString  : rust_type              (* Owned String *)
  | RsUnit    : rust_type
  | RsNever   : rust_type              (* ! type *)
  | RsTuple   : list rust_type -> rust_type
  | RsArray   : rust_type -> nat -> rust_type  (* [T; N] *)
  | RsSlice   : rust_type -> rust_type         (* [T] *)
  | RsOption  : rust_type -> rust_type
  | RsResult  : rust_type -> rust_type -> rust_type
  | RsVec     : rust_type -> rust_type
  | RsFn      : list rust_type -> rust_type -> rust_type
  | RsStruct  : string -> list (string & rust_type) -> rust_type
  | RsEnum    : string -> list (string & list rust_type) -> rust_type
  | RsRef_    : rust_ownership -> rust_type -> rust_type  (* Reference with ownership *)
  | RsNamed   : string -> rust_type
  | RsGeneric : string -> list rust_type -> rust_type

(* Translate Rust base type to Brrr-Lang type *)
let rec translate_rust_base (t: rust_type) : brrr_type =
  match t with
  | RsBool    -> t_bool
  | RsI8      -> t_i8
  | RsI16     -> t_i16
  | RsI32     -> t_i32
  | RsI64     -> t_i64
  | RsI128    -> TNumeric (NumInt { width = I128; sign = Signed })
  | RsIsize   -> t_i64  (* Platform-dependent, approximate as i64 *)
  | RsU8      -> t_u8
  | RsU16     -> t_u16
  | RsU32     -> t_u32
  | RsU64     -> t_u64
  | RsU128    -> TNumeric (NumInt { width = I128; sign = Unsigned })
  | RsUsize   -> t_u64
  | RsF32     -> t_f32
  | RsF64     -> t_f64
  | RsChar    -> t_char
  | RsStr     -> t_string  (* String slice -> String *)
  | RsString  -> t_string
  | RsUnit    -> t_unit
  | RsNever   -> t_never
  | RsTuple ts -> TTuple (List.Tot.map translate_rust_base ts)
  | RsArray t' _ -> t_array (translate_rust_base t')
  | RsSlice t' -> t_slice (translate_rust_base t')
  | RsOption t' -> t_option (translate_rust_base t')
  | RsResult t' e' -> TResult (translate_rust_base t') (translate_rust_base e')
  | RsVec t' -> t_array (translate_rust_base t')  (* Vec<T> -> Array<T> *)
  | RsFn params ret ->
      let params' = List.Tot.map translate_rust_base params in
      let ret' = translate_rust_base ret in
      t_func params' ret' pure  (* Rust closures: effects via return type *)
  | RsStruct name fields ->
      TStruct {
        struct_name = name;
        struct_fields = List.Tot.map (fun (n, t') ->
          { field_name = n; field_ty = translate_rust_base t'; field_vis = Public }
        ) fields;
        struct_repr = ReprRust
      }
  | RsEnum name variants ->
      TEnum {
        enum_name = name;
        enum_variants = List.Tot.map (fun (n, ts) ->
          { variant_name = n; variant_fields = List.Tot.map translate_rust_base ts }
        ) variants
      }
  | RsRef_ own inner ->
      let inner' = translate_rust_base inner in
      (match own with
       | RsOwned -> inner'  (* Owned: no wrapper *)
       | RsRef _ -> t_ref inner'
       | RsRefMut _ -> t_ref_mut inner'
       | RsRc -> t_rc inner'
       | RsArc -> t_arc inner'
       | RsBox -> t_box inner')
  | RsNamed name -> TNamed name
  | RsGeneric name args ->
      TApp (TNamed name) (List.Tot.map translate_rust_base args)

(* Translate Rust ownership to Brrr-Lang mode *)
let translate_rust_ownership (own: rust_ownership) : mode =
  match own with
  | RsOwned -> MOne      (* Owned: linear/affine *)
  | RsRef _ -> MOmega    (* Shared borrow: can be duplicated *)
  | RsRefMut _ -> MOne   (* Exclusive borrow: linear *)
  | RsRc -> MOmega       (* RC: shared ownership *)
  | RsArc -> MOmega      (* Arc: shared ownership *)
  | RsBox -> MOne        (* Box: owned heap, linear *)

(* Translate Rust lifetime to Brrr-Lang region *)
let translate_rust_lifetime (lt: string) (ctx: trans_ctx) : region =
  if lt = "'static" then RStatic
  else
    match List.Tot.assoc lt ctx.lifetime_env with
    | Some r -> r
    | None -> RNamed lt  (* Create new named region *)

(* Full Rust type translation with ownership and lifetime *)
let translate_rust_type (t: rust_type) (own: rust_ownership) (ctx: trans_ctx)
    : (brrr_type & mode & option region) =
  let base = translate_rust_base t in
  let m = translate_rust_ownership own in
  let region = match own with
    | RsRef lt -> Some (translate_rust_lifetime lt ctx)
    | RsRefMut lt -> Some (translate_rust_lifetime lt ctx)
    | _ -> None
  in
  (base, m, region)

(* Rust expression - simplified AST *)
noeq type rust_expr =
  | RsEVar     : string -> rust_expr
  | RsELit     : literal -> rust_expr
  | RsEBinOp   : binary_op -> rust_expr -> rust_expr -> rust_expr
  | RsEUnOp    : unary_op -> rust_expr -> rust_expr
  | RsECall    : rust_expr -> list rust_expr -> rust_expr
  | RsEMethod  : rust_expr -> string -> list rust_expr -> rust_expr
  | RsEField   : rust_expr -> string -> rust_expr
  | RsEIndex   : rust_expr -> rust_expr -> rust_expr
  | RsEBorrow  : rust_expr -> rust_expr            (* &e *)
  | RsEBorrowMut : rust_expr -> rust_expr          (* &mut e *)
  | RsEDeref   : rust_expr -> rust_expr            (* *e *)
  | RsEMove    : rust_expr -> rust_expr            (* move semantics *)
  | RsEClone   : rust_expr -> rust_expr            (* .clone() *)
  | RsELet     : string -> option rust_type -> rust_expr -> rust_expr -> rust_expr
  | RsELetMut  : string -> option rust_type -> rust_expr -> rust_expr -> rust_expr
  | RsEAssign  : rust_expr -> rust_expr -> rust_expr
  | RsEIf      : rust_expr -> rust_expr -> rust_expr -> rust_expr
  | RsEMatch   : rust_expr -> list (pattern & rust_expr) -> rust_expr
  | RsELoop    : option string -> rust_expr -> rust_expr
  | RsEWhile   : option string -> rust_expr -> rust_expr -> rust_expr
  | RsEFor     : string -> rust_expr -> rust_expr -> rust_expr
  | RsEBreak   : option string -> option rust_expr -> rust_expr
  | RsEContinue: option string -> rust_expr
  | RsEReturn  : option rust_expr -> rust_expr
  | RsEBlock   : list rust_expr -> rust_expr
  | RsEClosure : list (string & rust_type) -> rust_expr -> rust_expr
  | RsEStruct  : string -> list (string & rust_expr) -> rust_expr
  | RsETuple   : list rust_expr -> rust_expr
  | RsEArray   : list rust_expr -> rust_expr
  | RsERange   : rust_expr -> rust_expr -> rust_expr
  | RsEAwait   : rust_expr -> rust_expr
  | RsEAsync   : rust_expr -> rust_expr
  | RsETry     : rust_expr -> rust_expr            (* ? operator *)
  | RsEUnsafe  : rust_expr -> rust_expr

(* Borrow context tracks what's borrowed *)
noeq type borrow_ctx = {
  owned_vars   : list string;      (* Variables with owned values *)
  borrowed_vars: list (string & string);  (* (var, lifetime) pairs - shared borrows *)
  mutborrow_vars: list (string & string); (* (var, lifetime) - exclusive borrows *)
  moved_vars   : list string       (* Variables that have been moved *)
}

let empty_borrow_ctx : borrow_ctx = {
  owned_vars = [];
  borrowed_vars = [];
  mutborrow_vars = [];
  moved_vars = []
}

(* Check if variable is Copy type - simplified *)
let is_copy_type (t: rust_type) : bool =
  match t with
  | RsBool | RsI8 | RsI16 | RsI32 | RsI64 | RsI128 | RsIsize
  | RsU8 | RsU16 | RsU32 | RsU64 | RsU128 | RsUsize
  | RsF32 | RsF64 | RsChar | RsUnit -> true
  | RsRef_ (RsRef _) _ -> true  (* Shared references are Copy *)
  | _ -> false

(* Translate Rust expression to Brrr-Lang *)
let rec translate_rust_expr (e: rust_expr) (bctx: borrow_ctx) (ctx: trans_ctx)
    : trans_result expr =
  match e with
  | RsEVar x ->
      if List.Tot.mem x bctx.moved_vars then
        TransError ("use after move: " ^ x)
      else
        TransOk (EVar x)

  | RsELit lit -> TransOk (ELit lit)

  | RsEBinOp op e1 e2 ->
      (match translate_rust_expr e1 bctx ctx, translate_rust_expr e2 bctx ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | TransApprox e1' r1, TransApprox e2' r2 ->
           TransApprox (EBinary op e1' e2') (r1 ^ "; " ^ r2)
       | TransApprox e1' r, TransOk e2' -> TransApprox (EBinary op e1' e2') r
       | TransOk e1', TransApprox e2' r -> TransApprox (EBinary op e1' e2') r)

  | RsEBorrow e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EBorrow e'')
       | TransApprox e'' r -> TransApprox (EBorrow e'') r
       | TransError r -> TransError r)

  | RsEBorrowMut e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EBorrowMut e'')
       | TransApprox e'' r -> TransApprox (EBorrowMut e'') r
       | TransError r -> TransError r)

  | RsEDeref e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EDeref e'')
       | TransApprox e'' r -> TransApprox (EDeref e'') r
       | TransError r -> TransError r)

  | RsEMove e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EMove e'')
       | TransApprox e'' r -> TransApprox (EMove e'') r
       | TransError r -> TransError r)

  | RsELet x ty init body ->
      (match translate_rust_expr init bctx ctx with
       | TransOk init' ->
           let ty' = match ty with
             | Some t -> Some (translate_rust_base t)
             | None -> None
           in
           (match translate_rust_expr body bctx ctx with
            | TransOk body' -> TransOk (ELet (PatVar x) ty' init' body')
            | TransApprox body' r -> TransApprox (ELet (PatVar x) ty' init' body') r
            | TransError r -> TransError r)
       | TransApprox init' r ->
           let ty' = match ty with Some t -> Some (translate_rust_base t) | None -> None in
           (match translate_rust_expr body bctx ctx with
            | TransOk body' -> TransApprox (ELet (PatVar x) ty' init' body') r
            | TransApprox body' r2 -> TransApprox (ELet (PatVar x) ty' init' body') (r ^ "; " ^ r2)
            | TransError r2 -> TransError r2)
       | TransError r -> TransError r)

  | RsEIf cond then_ else_ ->
      (match translate_rust_expr cond bctx ctx,
             translate_rust_expr then_ bctx ctx,
             translate_rust_expr else_ bctx ctx with
       | TransOk c, TransOk t, TransOk e -> TransOk (EIf c t e)
       | TransError r, _, _ -> TransError r
       | _, TransError r, _ -> TransError r
       | _, _, TransError r -> TransError r
       | _, _, _ -> TransApprox (EIf EHole EHole EHole) "partial translation")

  | RsEBlock stmts ->
      let rec translate_stmts (ss: list rust_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_rust_expr s bctx ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block translation")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | RsEAwait e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EAwait e'')
       | TransApprox e'' r -> TransApprox (EAwait e'') r
       | TransError r -> TransError r)

  | RsEAsync e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EAsync e'')
       | TransApprox e'' r -> TransApprox (EAsync e'') r
       | TransError r -> TransError r)

  | RsEUnsafe e' ->
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' -> TransOk (EUnsafe e'')
       | TransApprox e'' r -> TransApprox (EUnsafe e'') r
       | TransError r -> TransError r)

  | RsETry e' ->
      (* ? operator: extract Ok or propagate Err *)
      (match translate_rust_expr e' bctx ctx with
       | TransOk e'' ->
           (* match e { Ok(v) => v, Err(e) => return Err(e) } *)
           TransOk (EMatch e'' [
             { arm_pattern = PatVariant "Result" "Ok" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Result" "Err" [PatVar "e"];
               arm_guard = None;
               arm_body = EReturn (Some (EVariant "Result" "Err" [EVar "e"])) }
           ])
       | TransApprox e'' r -> TransApprox e'' r
       | TransError r -> TransError r)

  | _ -> TransApprox EHole "unsupported Rust expression"

(** ============================================================================
    PART 2: TYPESCRIPT -> BRRR-LANG TRANSLATION
    ============================================================================

    Key mappings:
      - Union types: A | B -> TUnion A B (sum type)
      - Intersection: A & B -> TIntersection A B (product refinement)
      - Gradual typing: any -> Dynamic, unknown -> Unknown
      - Optional: T | undefined -> Option<T>
      - Async/Promise: Promise<T> -> Future<T, Hot>
      - Nullish: T | null | undefined -> Option<T>

    Soundness: Type guards and casts may require runtime checks.
    ============================================================================ *)

(* TypeScript type AST *)
noeq type ts_type =
  | TSUndefined  : ts_type
  | TSNull       : ts_type
  | TSBoolean    : ts_type
  | TSNumber     : ts_type
  | TSBigInt     : ts_type
  | TSString     : ts_type
  | TSSymbol     : ts_type
  | TSVoid       : ts_type
  | TSNever      : ts_type
  | TSAny        : ts_type
  | TSUnknown    : ts_type
  | TSArray      : ts_type -> ts_type
  | TSTuple      : list ts_type -> ts_type
  | TSObject     : list (string & ts_type & bool) -> ts_type  (* (name, type, optional) *)
  | TSFunction   : list ts_type -> ts_type -> bool -> ts_type (* params, ret, is_async *)
  | TSUnion      : ts_type -> ts_type -> ts_type
  | TSIntersection : ts_type -> ts_type -> ts_type
  | TSPromise    : ts_type -> ts_type
  | TSLiteral    : literal -> ts_type
  | TSNamed      : string -> ts_type
  | TSGeneric    : string -> list ts_type -> ts_type
  | TSMapped     : ts_type -> ts_type  (* Mapped types approximation *)
  | TSConditional : ts_type -> ts_type -> ts_type -> ts_type  (* T extends U ? X : Y *)
  | TSTemplateLiteral : ts_type  (* Template literal types -> String *)

(* Translate TypeScript type to Brrr-Lang *)
let rec translate_ts_type (t: ts_type) : brrr_type =
  match t with
  | TSUndefined -> t_unit
  | TSNull -> t_option t_dynamic  (* null -> Option<Dynamic> *)
  | TSBoolean -> t_bool
  | TSNumber -> t_f64  (* JavaScript number is f64 *)
  | TSBigInt -> TNumeric (NumInt ibig)
  | TSString -> t_string
  | TSSymbol -> t_string  (* Symbol approximated as String *)
  | TSVoid -> t_unit
  | TSNever -> t_never
  | TSAny -> t_dynamic   (* any -> Dynamic (unsafe top) *)
  | TSUnknown -> t_unknown  (* unknown -> Unknown (safe top) *)
  | TSArray elem -> t_array (translate_ts_type elem)
  | TSTuple elems -> TTuple (List.Tot.map translate_ts_type elems)
  | TSObject fields ->
      TStruct {
        struct_name = "_anonymous";
        struct_fields = List.Tot.map (fun (n, ty, opt) ->
          let field_ty = if opt then t_option (translate_ts_type ty)
                         else translate_ts_type ty in
          { field_name = n; field_ty = field_ty; field_vis = Public }
        ) fields;
        struct_repr = ReprRust
      }
  | TSFunction params ret is_async ->
      let params' = List.Tot.map translate_ts_type params in
      let ret' = translate_ts_type ret in
      let ret'' = if is_async then TWrap WOption ret' (* Future approx *)
                  else ret' in
      let eff = if is_async then RowExt EAsync (RowVar "epsilon")
                else RowVar "epsilon" in
      t_func params' ret'' eff
  | TSUnion a b ->
      (* Union types: need sum type or approximation *)
      (* A | B -> Option if one is undefined/null, else approximate *)
      (match a, b with
       | TSUndefined, t -> t_option (translate_ts_type t)
       | t, TSUndefined -> t_option (translate_ts_type t)
       | TSNull, t -> t_option (translate_ts_type t)
       | t, TSNull -> t_option (translate_ts_type t)
       | _, _ ->
           (* General union: create enum with variants *)
           TEnum {
             enum_name = "_Union";
             enum_variants = [
               { variant_name = "Left"; variant_fields = [translate_ts_type a] };
               { variant_name = "Right"; variant_fields = [translate_ts_type b] }
             ]
           })
  | TSIntersection a b ->
      (* Intersection: approximate as struct merge *)
      (* This is a simplification; full intersection requires type checking *)
      translate_ts_type a  (* Approximate with first type *)
  | TSPromise t' ->
      (* Promise<T> -> Future<T> *)
      TWrap WOption (translate_ts_type t')  (* Simplified Future *)
  | TSLiteral lit ->
      (* Literal type -> base type *)
      (match lit with
       | LitBool _ -> t_bool
       | LitInt _ _ -> t_f64
       | LitString _ -> t_string
       | _ -> t_dynamic)
  | TSNamed name -> TNamed name
  | TSGeneric name args ->
      TApp (TNamed name) (List.Tot.map translate_ts_type args)
  | TSMapped t' -> translate_ts_type t'  (* Approximate as underlying type *)
  | TSConditional _ t_true _ -> translate_ts_type t_true  (* Conservative approx *)
  | TSTemplateLiteral -> t_string

(* TypeScript expression AST *)
noeq type ts_expr =
  | TSEVar       : string -> ts_expr
  | TSELit       : literal -> ts_expr
  | TSEBinOp     : binary_op -> ts_expr -> ts_expr -> ts_expr
  | TSEUnOp      : unary_op -> ts_expr -> ts_expr
  | TSECall      : ts_expr -> list ts_expr -> ts_expr
  | TSENew       : ts_expr -> list ts_expr -> ts_expr
  | TSEProperty  : ts_expr -> string -> ts_expr
  | TSEIndex     : ts_expr -> ts_expr -> ts_expr
  | TSEArrow     : list (string & option ts_type) -> ts_expr -> ts_expr
  | TSEFunction  : option string -> list (string & option ts_type) -> ts_expr -> ts_expr
  | TSEObject    : list (string & ts_expr) -> ts_expr
  | TSEArray     : list ts_expr -> ts_expr
  | TSEAwait     : ts_expr -> ts_expr
  | TSEAsync     : ts_expr -> ts_expr
  | TSEYield     : ts_expr -> ts_expr
  | TSEOptChain  : ts_expr -> string -> ts_expr  (* a?.b *)
  | TSENullCoal  : ts_expr -> ts_expr -> ts_expr  (* a ?? b *)
  | TSETypeAssert: ts_expr -> ts_type -> ts_expr  (* e as T *)
  | TSENonNull   : ts_expr -> ts_expr  (* e! *)
  | TSETypeof    : ts_expr -> ts_expr
  | TSEInstanceof: ts_expr -> ts_type -> ts_expr
  | TSETernary   : ts_expr -> ts_expr -> ts_expr -> ts_expr
  | TSESpread    : ts_expr -> ts_expr
  | TSETemplate  : list ts_expr -> ts_expr  (* Template literal *)
  | TSELet       : string -> option ts_type -> ts_expr -> ts_expr -> ts_expr
  | TSEConst     : string -> option ts_type -> ts_expr -> ts_expr -> ts_expr
  | TSEIf        : ts_expr -> ts_expr -> option ts_expr -> ts_expr
  | TSESwitch    : ts_expr -> list (ts_expr & ts_expr) -> option ts_expr -> ts_expr
  | TSEFor       : string -> ts_expr -> ts_expr -> ts_expr
  | TSEForOf     : string -> ts_expr -> ts_expr -> ts_expr
  | TSEWhile     : ts_expr -> ts_expr -> ts_expr
  | TSETry       : ts_expr -> option (string & ts_expr) -> option ts_expr -> ts_expr
  | TSEThrow     : ts_expr -> ts_expr
  | TSEReturn    : option ts_expr -> ts_expr
  | TSEBreak     : option string -> ts_expr
  | TSEContinue  : option string -> ts_expr
  | TSEBlock     : list ts_expr -> ts_expr
  | TSEClass     : string -> list (string & ts_expr) -> ts_expr  (* Simplified class expr *)

(* Translate TypeScript expression to Brrr-Lang *)
let rec translate_ts_expr (e: ts_expr) (ctx: trans_ctx) : trans_result expr =
  match e with
  | TSEVar x -> TransOk (EVar x)
  | TSELit lit -> TransOk (ELit lit)

  | TSEBinOp op e1 e2 ->
      (match translate_ts_expr e1 ctx, translate_ts_expr e2 ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial binop")

  | TSECall f args ->
      (match translate_ts_expr f ctx with
       | TransOk f' ->
           let rec translate_args (as_: list ts_expr) : trans_result (list expr) =
             match as_ with
             | [] -> TransOk []
             | a :: rest ->
                 (match translate_ts_expr a ctx, translate_args rest with
                  | TransOk a', TransOk rest' -> TransOk (a' :: rest')
                  | TransError r, _ -> TransError r
                  | _, TransError r -> TransError r
                  | _, _ -> TransApprox [] "partial args")
           in
           (match translate_args args with
            | TransOk args' -> TransOk (ECall f' args')
            | TransApprox args' r -> TransApprox (ECall f' args') r
            | TransError r -> TransError r)
       | TransError r -> TransError r
       | TransApprox f' r -> TransApprox (ECall f' []) r)

  | TSEAwait e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EAwait e'')
       | TransApprox e'' r -> TransApprox (EAwait e'') r
       | TransError r -> TransError r)

  | TSEAsync e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EAsync e'')
       | TransApprox e'' r -> TransApprox (EAsync e'') r
       | TransError r -> TransError r)

  | TSEOptChain base prop ->
      (* a?.b -> match a { Some(v) => Some(v.prop), None => None } *)
      (match translate_ts_expr base ctx with
       | TransOk base' ->
           TransOk (EMatch base' [
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = EVariant "Option" "None" [] };
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVariant "Option" "Some" [EField (EVar "v") prop] }
           ])
       | TransError r -> TransError r
       | TransApprox e' r -> TransApprox e' r)

  | TSENullCoal e1 e2 ->
      (* a ?? b -> match a { Some(v) => v, None => b } *)
      (match translate_ts_expr e1 ctx, translate_ts_expr e2 ctx with
       | TransOk e1', TransOk e2' ->
           TransOk (EMatch e1' [
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = e2' }
           ])
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial nullish coalescing")

  | TSETypeAssert e' ty ->
      (* e as T -> cast with runtime type check *)
      (match translate_ts_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EAs e'' (translate_ts_type ty))
                       "type assertion requires runtime check"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox (EAs e'' (translate_ts_type ty)) r)

  | TSENonNull e' ->
      (* e! -> match e { Some(v) => v, None => panic } *)
      (match translate_ts_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EMatch e'' [
             { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
               arm_guard = None;
               arm_body = EVar "v" };
             { arm_pattern = PatVariant "Option" "None" [];
               arm_guard = None;
               arm_body = EThrow (ELit (LitString "non-null assertion failed")) }
           ]) "non-null assertion may panic"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox e'' r)

  | TSEArrow params body ->
      let params' = List.Tot.map (fun (n, ty) ->
        match ty with
        | Some t -> (n, translate_ts_type t)
        | None -> (n, t_dynamic)  (* Untyped param -> dynamic *)
      ) params in
      (match translate_ts_expr body ctx with
       | TransOk body' -> TransOk (ELambda params' body')
       | TransApprox body' r -> TransApprox (ELambda params' body') r
       | TransError r -> TransError r)

  | TSELet x ty init body ->
      let ty' = match ty with
        | Some t -> Some (translate_ts_type t)
        | None -> None
      in
      (match translate_ts_expr init ctx, translate_ts_expr body ctx with
       | TransOk init', TransOk body' -> TransOk (ELet (PatVar x) ty' init' body')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial let")

  | TSETernary cond then_ else_ ->
      (match translate_ts_expr cond ctx,
             translate_ts_expr then_ ctx,
             translate_ts_expr else_ ctx with
       | TransOk c, TransOk t, TransOk e -> TransOk (EIf c t e)
       | TransError r, _, _ -> TransError r
       | _, TransError r, _ -> TransError r
       | _, _, TransError r -> TransError r
       | _, _, _ -> TransApprox EHole "partial ternary")

  | TSEThrow e' ->
      (match translate_ts_expr e' ctx with
       | TransOk e'' -> TransOk (EThrow e'')
       | TransApprox e'' r -> TransApprox (EThrow e'') r
       | TransError r -> TransError r)

  | TSEBlock stmts ->
      let rec translate_stmts (ss: list ts_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_ts_expr s ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | _ -> TransApprox EHole "unsupported TypeScript expression"

(** ============================================================================
    PART 3: PYTHON -> BRRR-LANG TRANSLATION
    ============================================================================

    Python translation uses the canonical types from PythonTypes.fst:

    Types (py_type):
      - Primitive: PyNone, PyBool, PyInt, PyFloat, PyStr, PyBytes
      - Collection: PyList, PyDict, PySet, PyFrozenSet, PyTuple
      - Typing: PyOptional, PyUnion, PyCallable, PyAwaitable, PyGenerator,
                PyIterator, PyIterable
      - Special: PyAny, PyNever, PyType, PyClass, PyGeneric, PyTypeVar,
                 PyLiteral, PySelf

    Expressions (py_expr):
      - Atoms: PyEVar, PyELit, PyENone, PyETrue, PyEFalse
      - Operations: PyEBinOp, PyEUnOp, PyECompare, PyEBoolOp
      - Calls: PyECall, PyEAttr, PyEIndex, PyESlice
      - Functions: PyELambda
      - Collections: PyEList, PyEDict, PyETuple, PyESet
      - Comprehensions: PyEListComp, PyEDictComp, PyESetComp, PyEGenExpr
      - Control flow: PyEIfExp, PyEWalrus, PyEIf, PyEFor, PyEWhile,
                      PyETry, PyEWith, PyEMatch
      - Async: PyEAwait, PyEYield, PyEYieldFrom
      - Statements: PyEAssign, PyEAugAssign, PyEReturn, PyERaise, PyEAssert,
                    PyEPass, PyEBreak, PyEContinue
      - Block: PyEBlock

    Key mappings:
      - Dynamic types: Python type -> Dynamic (with type hints -> gradual)
      - None: None -> Unit
      - Collections: list -> gc Array, dict -> gc Dict
      - Duck typing: attribute access -> runtime lookup
      - Decorators: @decorator -> effect annotation (approximation)

    For complete Python translation with full typing module support,
    see PythonTranslation.fst which provides:
      - translate_py_type: py_type -> brrr_type
      - translate_py_expr: py_expr -> py_trans_result
      - python_functor: Translation functor with laws and soundness proofs

    Soundness: Requires runtime type guards for any static property.
    ============================================================================ *)

(** Python default effects: Throw + IO + epsilon

    Python functions have implicit effects:
    - Throw: Any function can raise exceptions
    - IO: Any function can perform I/O
    - epsilon: Open row for additional effects
*)
let py_default_effects : effect_row =
  RowExt (EThrow "Exception") (RowExt EIO (RowVar "epsilon"))

(** ============================================================================
    PART 4: GO -> BRRR-LANG TRANSLATION
    ============================================================================

    Key mappings:
      - Interfaces: interface{} -> type class
      - Goroutines: go f(x) -> spawn(f(x))
      - Channels: chan T -> Channel<T>
      - Error handling: error -> Result<T, Error>
      - Multiple returns: (T, error) -> Result<T, Error>
      - nil: nil -> None (for pointer/interface/chan/map/slice)

    Soundness: Race conditions in Go may not be detected.
    ============================================================================ *)

(* Go type AST *)
noeq type go_type =
  | GoBool     : go_type
  | GoInt      : go_type      (* Platform-dependent int *)
  | GoInt8     : go_type
  | GoInt16    : go_type
  | GoInt32    : go_type
  | GoInt64    : go_type
  | GoUint     : go_type
  | GoUint8    : go_type
  | GoUint16   : go_type
  | GoUint32   : go_type
  | GoUint64   : go_type
  | GoUintptr  : go_type
  | GoFloat32  : go_type
  | GoFloat64  : go_type
  | GoComplex64: go_type
  | GoComplex128: go_type
  | GoString   : go_type
  | GoByte     : go_type      (* alias for uint8 *)
  | GoRune     : go_type      (* alias for int32 *)
  | GoArray    : go_type -> nat -> go_type  (* [N]T *)
  | GoSlice    : go_type -> go_type          (* []T *)
  | GoMap      : go_type -> go_type -> go_type  (* map[K]V *)
  | GoChan     : go_type -> bool -> bool -> go_type  (* chan T, send-only, recv-only *)
  | GoPtr      : go_type -> go_type          (* *T *)
  | GoFunc     : list go_type -> list go_type -> go_type  (* func(params)(results) *)
  | GoStruct   : string -> list (string & go_type) -> go_type
  | GoInterface: string -> list (string & go_type) -> go_type
  | GoNamed    : string -> go_type
  | GoError    : go_type      (* error interface *)
  | GoAny      : go_type      (* interface{} / any *)

(* Translate Go type to Brrr-Lang *)
let rec translate_go_type (t: go_type) : brrr_type =
  match t with
  | GoBool -> t_bool
  | GoInt -> t_i64   (* Approximate as i64 *)
  | GoInt8 -> t_i8
  | GoInt16 -> t_i16
  | GoInt32 -> t_i32
  | GoInt64 -> t_i64
  | GoUint -> t_u64
  | GoUint8 -> t_u8
  | GoUint16 -> t_u16
  | GoUint32 -> t_u32
  | GoUint64 -> t_u64
  | GoUintptr -> t_u64
  | GoFloat32 -> t_f32
  | GoFloat64 -> t_f64
  | GoComplex64 ->
      TTuple [t_f32; t_f32]  (* Approximate complex as tuple *)
  | GoComplex128 ->
      TTuple [t_f64; t_f64]
  | GoString -> t_string
  | GoByte -> t_u8
  | GoRune -> t_i32
  | GoArray elem _ -> t_array (translate_go_type elem)
  | GoSlice elem -> t_slice (translate_go_type elem)
  | GoMap k v ->
      TStruct {
        struct_name = "Map";
        struct_fields = [
          { field_name = "key_type"; field_ty = translate_go_type k; field_vis = Public };
          { field_name = "val_type"; field_ty = translate_go_type v; field_vis = Public }
        ];
        struct_repr = ReprRust
      }
  | GoChan elem _ _ ->
      (* Channel<T> - direction ignored for now *)
      TWrap WOption (translate_go_type elem)  (* Simplified as Option for now *)
  | GoPtr elem -> t_option (translate_go_type elem)  (* Go pointer nullable *)
  | GoFunc params results ->
      let params' = List.Tot.map translate_go_type params in
      let ret' = match results with
        | [] -> t_unit
        | [r] -> translate_go_type r
        | rs -> TTuple (List.Tot.map translate_go_type rs)
      in
      let eff = RowExt EPanic (RowExt ESpawn (RowVar "epsilon")) in
      t_func params' ret' eff
  | GoStruct name fields ->
      TStruct {
        struct_name = name;
        struct_fields = List.Tot.map (fun (n, ty) ->
          { field_name = n; field_ty = translate_go_type ty; field_vis = Public }
        ) fields;
        struct_repr = ReprRust
      }
  | GoInterface name methods ->
      (* Interface -> type class (dynamic dispatch) *)
      TNamed name  (* Approximate as named type *)
  | GoNamed name -> TNamed name
  | GoError -> TNamed "Error"  (* Error interface *)
  | GoAny -> t_dynamic

(* Go expression AST *)
noeq type go_expr =
  | GoEVar      : string -> go_expr
  | GoELit      : literal -> go_expr
  | GoENil      : go_expr
  | GoEBinOp    : binary_op -> go_expr -> go_expr -> go_expr
  | GoEUnOp     : unary_op -> go_expr -> go_expr
  | GoECall     : go_expr -> list go_expr -> go_expr
  | GoEMethod   : go_expr -> string -> list go_expr -> go_expr
  | GoEField    : go_expr -> string -> go_expr
  | GoEIndex    : go_expr -> go_expr -> go_expr
  | GoESlice    : go_expr -> option go_expr -> option go_expr -> option go_expr -> go_expr
  | GoETypeAssert: go_expr -> go_type -> go_expr  (* e.(T) *)
  | GoEMake     : go_type -> list go_expr -> go_expr  (* make(T, args) *)
  | GoENew      : go_type -> go_expr               (* new(T) *)
  | GoEComposite: go_type -> list go_expr -> go_expr  (* T{elems} *)
  | GoEFunc     : list (string & go_type) -> list go_type -> go_expr -> go_expr
  | GoEGo       : go_expr -> go_expr               (* go f(x) *)
  | GoEDefer    : go_expr -> go_expr               (* defer f(x) *)
  | GoEChanSend : go_expr -> go_expr -> go_expr    (* ch <- v *)
  | GoEChanRecv : go_expr -> go_expr               (* <-ch *)
  | GoESelect   : list (go_expr & go_expr) -> option go_expr -> go_expr
  | GoEIf       : option go_expr -> go_expr -> go_expr -> option go_expr -> go_expr
  | GoEFor      : option go_expr -> option go_expr -> option go_expr -> go_expr -> go_expr
  | GoEForRange : string -> option string -> go_expr -> go_expr -> go_expr
  | GoESwitch   : option go_expr -> go_expr -> list (list go_expr & go_expr) -> option go_expr -> go_expr
  | GoETypeSwitch: string -> go_expr -> list (go_type & go_expr) -> option go_expr -> go_expr
  | GoEReturn   : list go_expr -> go_expr
  | GoEBreak    : option string -> go_expr
  | GoEContinue : option string -> go_expr
  | GoEGoto     : string -> go_expr
  | GoEFallthrough : go_expr
  | GoEPanic    : go_expr -> go_expr
  | GoERecover  : go_expr
  | GoEBlock    : list go_expr -> go_expr
  | GoEShortDecl: list string -> list go_expr -> go_expr -> go_expr  (* x := e *)
  | GoEAssign   : list go_expr -> list go_expr -> go_expr

(* Translate Go expression *)
let rec translate_go_expr (e: go_expr) (ctx: trans_ctx) : trans_result expr =
  match e with
  | GoEVar x -> TransOk (EVar x)
  | GoELit lit -> TransOk (ELit lit)
  | GoENil -> TransOk (EVariant "Option" "None" [])

  | GoEBinOp op e1 e2 ->
      (match translate_go_expr e1 ctx, translate_go_expr e2 ctx with
       | TransOk e1', TransOk e2' -> TransOk (EBinary op e1' e2')
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial binop")

  | GoECall f args ->
      (match translate_go_expr f ctx with
       | TransOk f' ->
           let rec translate_args (as_: list go_expr) : trans_result (list expr) =
             match as_ with
             | [] -> TransOk []
             | a :: rest ->
                 (match translate_go_expr a ctx, translate_args rest with
                  | TransOk a', TransOk rest' -> TransOk (a' :: rest')
                  | TransError r, _ -> TransError r
                  | _, TransError r -> TransError r
                  | _, _ -> TransApprox [] "partial args")
           in
           (match translate_args args with
            | TransOk args' -> TransOk (ECall f' args')
            | TransApprox args' r -> TransApprox (ECall f' args') r
            | TransError r -> TransError r)
       | TransError r -> TransError r
       | TransApprox f' r -> TransApprox (ECall f' []) r)

  | GoEGo e' ->
      (* go f(x) -> spawn(f(x)) *)
      (match translate_go_expr e' ctx with
       | TransOk e'' -> TransOk (ESpawn e'')
       | TransApprox e'' r -> TransApprox (ESpawn e'') r
       | TransError r -> TransError r)

  | GoEChanSend ch v ->
      (* ch <- v -> channel send operation *)
      (match translate_go_expr ch ctx, translate_go_expr v ctx with
       | TransOk ch', TransOk v' ->
           TransOk (EMethodCall ch' "send" [v'])
       | TransError r, _ -> TransError r
       | _, TransError r -> TransError r
       | _, _ -> TransApprox EHole "partial chan send")

  | GoEChanRecv ch ->
      (* <-ch -> channel receive operation *)
      (match translate_go_expr ch ctx with
       | TransOk ch' -> TransOk (EMethodCall ch' "recv" [])
       | TransApprox ch' r -> TransApprox (EMethodCall ch' "recv" []) r
       | TransError r -> TransError r)

  | GoEDefer e' ->
      (* defer f(x) -> special deferred execution *)
      (match translate_go_expr e' ctx with
       | TransOk e'' ->
           TransApprox e'' "defer semantics approximated"
       | TransApprox e'' r -> TransApprox e'' r
       | TransError r -> TransError r)

  | GoEPanic e' ->
      (match translate_go_expr e' ctx with
       | TransOk e'' -> TransOk (EThrow e'')
       | TransApprox e'' r -> TransApprox (EThrow e'') r
       | TransError r -> TransError r)

  | GoERecover ->
      (* recover() -> catch panic *)
      TransApprox (ELit LitUnit) "recover requires special handling"

  | GoETypeAssert e' ty ->
      (* e.(T) -> type assertion with runtime check *)
      (match translate_go_expr e' ctx with
       | TransOk e'' ->
           TransApprox (EAs e'' (translate_go_type ty))
                       "type assertion requires runtime check"
       | TransError r -> TransError r
       | TransApprox e'' r -> TransApprox (EAs e'' (translate_go_type ty)) r)

  | GoEIf init cond then_ else_ ->
      let translate_body b = translate_go_expr b ctx in
      (match init with
       | Some init' ->
           (match translate_go_expr init' ctx,
                  translate_go_expr cond ctx,
                  translate_body then_ with
            | TransOk init'', TransOk cond', TransOk then'' ->
                let else'' = match else_ with
                  | Some e -> (match translate_body e with
                              | TransOk e' -> e'
                              | _ -> ELit LitUnit)
                  | None -> ELit LitUnit
                in
                TransOk (ESeq init'' (EIf cond' then'' else''))
            | TransError r, _, _ -> TransError r
            | _, TransError r, _ -> TransError r
            | _, _, TransError r -> TransError r
            | _, _, _ -> TransApprox EHole "partial if")
       | None ->
           (match translate_go_expr cond ctx, translate_body then_ with
            | TransOk cond', TransOk then'' ->
                let else'' = match else_ with
                  | Some e -> (match translate_body e with
                              | TransOk e' -> e'
                              | _ -> ELit LitUnit)
                  | None -> ELit LitUnit
                in
                TransOk (EIf cond' then'' else'')
            | TransError r, _ -> TransError r
            | _, TransError r -> TransError r
            | _, _ -> TransApprox EHole "partial if"))

  | GoEReturn results ->
      (match results with
       | [] -> TransOk (EReturn None)
       | [r] ->
           (match translate_go_expr r ctx with
            | TransOk r' -> TransOk (EReturn (Some r'))
            | TransApprox r' re -> TransApprox (EReturn (Some r')) re
            | TransError re -> TransError re)
       | _ ->
           (* Multiple returns -> tuple *)
           let rec translate_results (rs: list go_expr) : trans_result (list expr) =
             match rs with
             | [] -> TransOk []
             | r :: rest ->
                 (match translate_go_expr r ctx, translate_results rest with
                  | TransOk r', TransOk rest' -> TransOk (r' :: rest')
                  | TransError re, _ -> TransError re
                  | _, TransError re -> TransError re
                  | _, _ -> TransApprox [] "partial results")
           in
           (match translate_results results with
            | TransOk rs' -> TransOk (EReturn (Some (ETuple rs')))
            | TransApprox rs' re -> TransApprox (EReturn (Some (ETuple rs'))) re
            | TransError re -> TransError re))

  | GoEBlock stmts ->
      let rec translate_stmts (ss: list go_expr) : trans_result (list expr) =
        match ss with
        | [] -> TransOk []
        | s :: rest ->
            (match translate_go_expr s ctx, translate_stmts rest with
             | TransOk s', TransOk rest' -> TransOk (s' :: rest')
             | TransError r, _ -> TransError r
             | _, TransError r -> TransError r
             | _, _ -> TransApprox [] "partial block")
      in
      (match translate_stmts stmts with
       | TransOk ss -> TransOk (EBlock ss)
       | TransApprox ss r -> TransApprox (EBlock ss) r
       | TransError r -> TransError r)

  | GoEBreak lbl -> TransOk (EBreak lbl None)
  | GoEContinue lbl -> TransOk (EContinue lbl)

  | _ -> TransApprox EHole "unsupported Go expression"

(** ============================================================================
    CROSS-LANGUAGE BOUNDARY HANDLING
    ============================================================================ *)

(* Language axioms - properties guaranteed by the language *)
type lang_axiom =
  | AxMemSafe    (* Memory safety - no use-after-free, buffer overflow *)
  | AxTypeSafe   (* Type safety - no type confusion *)
  | AxNullSafe   (* Null safety - no null pointer dereference *)
  | AxRaceFree   (* Race freedom - no data races *)
  | AxLeakFree   (* Leak freedom - no memory leaks *)
  | AxDetDrop    (* Deterministic destruction *)

(* Get axioms for a language *)
let language_axioms (lang: source_language) : list lang_axiom =
  match lang with
  | LangRust -> [AxMemSafe; AxTypeSafe; AxRaceFree; AxLeakFree]
  | LangTypeScript -> [AxMemSafe; AxTypeSafe]
  | LangPython -> [AxMemSafe; AxLeakFree]
  | LangGo -> [AxMemSafe; AxTypeSafe; AxLeakFree]
  | LangSwift -> [AxMemSafe; AxTypeSafe; AxNullSafe]
  | LangJava -> [AxMemSafe; AxTypeSafe; AxLeakFree]
  | LangC -> []  (* C provides no guarantees *)
  | LangCpp -> []  (* C++ provides no guarantees *)

(* Check if axiom is in list *)
let has_axiom (ax: lang_axiom) (axs: list lang_axiom) : bool =
  List.Tot.mem ax axs

(* Compute boundary risks when crossing from L1 to L2 *)
let boundary_risks (from_lang to_lang: source_language) : list lang_axiom =
  let from_axs = language_axioms from_lang in
  let to_axs = language_axioms to_lang in
  (* Risks are axioms from has but to doesn't *)
  List.Tot.filter (fun ax -> has_axiom ax from_axs && not (has_axiom ax to_axs))
    [AxMemSafe; AxTypeSafe; AxNullSafe; AxRaceFree; AxLeakFree; AxDetDrop]

(* Generate guard for boundary crossing *)
let generate_boundary_guard (from_lang to_lang: source_language)
                            (value: expr) (ty: brrr_type) : expr =
  let risks = boundary_risks from_lang to_lang in
  let guarded = value in

  (* Add type check if crossing into typed from untyped *)
  let guarded =
    if has_axiom AxTypeSafe (language_axioms to_lang) &&
       not (has_axiom AxTypeSafe (language_axioms from_lang))
    then EIs guarded ty  (* Runtime type check *)
    else guarded
  in

  (* Add null check if crossing into null-safe *)
  let guarded =
    if has_axiom AxNullSafe (language_axioms to_lang) &&
       not (has_axiom AxNullSafe (language_axioms from_lang))
    then EMatch guarded [
           { arm_pattern = PatVariant "Option" "None" [];
             arm_guard = None;
             arm_body = EThrow (ELit (LitString "null value at boundary")) };
           { arm_pattern = PatVariant "Option" "Some" [PatVar "v"];
             arm_guard = None;
             arm_body = EVar "v" }
         ]
    else guarded
  in

  guarded

(** ============================================================================
    SOUNDNESS PROPERTIES
    ============================================================================ *)

(* Translation soundness statement (informal):

   For each source language L with translation T_L:

   1. Type Preservation:
      If e : tau in L, then T_L(e) : T_L(tau) in Brrr-Lang

   2. Semantic Preservation:
      If [[e]]_L(rho) = v, then [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v)

   3. Effect Soundness:
      If e has effect epsilon in L, then T_L(e) has effect T_L(epsilon) in Brrr-Lang

   4. Approximation Safety:
      If TransApprox is returned, the translation is sound but may reject
      more programs than necessary (conservative approximation)
*)

(* Approximation annotations for unsound features *)
type approx_reason =
  | ApproxDynamic      (* Dynamic typing requires runtime checks *)
  | ApproxUnion        (* Union types require runtime dispatch *)
  | ApproxIntersection (* Intersection types simplified *)
  | ApproxDuckTyping   (* Duck typing requires runtime lookup *)
  | ApproxDecorator    (* Decorator effect approximated *)
  | ApproxAsync        (* Async semantics simplified *)
  | ApproxChannel      (* Channel semantics simplified *)
  | ApproxInterface    (* Interface dynamic dispatch *)
  | ApproxLifetime     (* Lifetime elision approximated *)
  | ApproxMacro        (* Macro expansion not supported *)
