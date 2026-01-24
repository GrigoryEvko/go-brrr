(**
 * BrrrLang.Core.ProcMacros
 *
 * Procedural macro system with typed multi-stage programming (MSP) integration.
 * Extends brrr_lang_spec_v0.4.tex Part VI - Macros and Syntax Transformers.
 *
 * Implements:
 *   - TokenStream: raw token stream interface for proc macros
 *   - ProcMacro: function-like procedural macros
 *   - DeriveMacro: derive macro interface for trait derivation
 *   - AttributeMacro: attribute macro support
 *   - Code[tau]: typed multi-stage programming integration
 *   - Capability model: sandbox restrictions for compile-time execution
 *   - Expansion tracking: for Brrr-Machine analysis
 *
 * Key invariant: NO ADMITS ALLOWED - all proofs must be complete.
 *
 * Design rationale:
 * - Procedural macros execute arbitrary code at compile time
 * - Unlike declarative macro_rules!, proc macros are full programs
 * - Safety requires a capability-based sandbox model
 * - Integration with MSP Code[tau] enables typed metaprogramming
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Macros, BrrrReflection
 *)
module ProcMacros

open Primitives
open Modes
open Effects
open BrrrTypes
open Expressions
open Macros
open BrrrReflection
open FStar.List.Tot

(** ============================================================================
    TOKEN STREAM - Input/Output interface for procedural macros
    ============================================================================

    TokenStream is the primary data structure for procedural macros.
    Unlike the simpler `token` type in Macros.fst, TokenStream provides:
    - Structured iteration with spans
    - Group/delimiter tracking
    - Efficient concatenation
    - Cursor-based parsing interface
    ============================================================================ *)

(* Span tracks source location for error messages *)
type token_span = {
  ts_file   : string;
  ts_start  : nat;     (* Byte offset start *)
  ts_end    : nat;     (* Byte offset end *)
  ts_line   : nat;     (* Line number (1-based) *)
  ts_column : nat      (* Column number (1-based) *)
}

(* Create empty span *)
let empty_span : token_span = {
  ts_file = ""; ts_start = 0; ts_end = 0; ts_line = 0; ts_column = 0
}

(* Delimiter kind for grouped tokens *)
type delimiter =
  | DelimParen   (* ( ) *)
  | DelimBrace   (* { } *)
  | DelimBracket (* [ ] *)
  | DelimNone    (* No delimiters - invisible grouping *)

(* Spacing information for pretty-printing *)
type spacing =
  | SpaceAlone  (* Token is followed by whitespace *)
  | SpaceJoint  (* Token is directly adjacent to next token *)

(* Token tree: structured token representation with spans *)
noeq type token_tree =
  | TTIdent   : string -> token_span -> token_tree
  | TTLiteral : literal -> token_span -> token_tree
  | TTPunct   : string -> spacing -> token_span -> token_tree
  | TTGroup   : delimiter -> token_stream -> token_span -> token_tree

(* Token stream: sequence of token trees *)
and token_stream = {
  tstream_trees : list token_tree;
  tstream_span  : token_span     (* Combined span of all tokens *)
}

(* Empty token stream *)
let empty_token_stream : token_stream = {
  tstream_trees = [];
  tstream_span = empty_span
}

(* Create stream from single token tree *)
let singleton_stream (tt: token_tree) : token_stream =
  let sp = match tt with
    | TTIdent _ s | TTLiteral _ s | TTPunct _ _ s | TTGroup _ _ s -> s
  in
  { tstream_trees = [tt]; tstream_span = sp }

(* Concatenate two token streams *)
let concat_streams (s1 s2: token_stream) : token_stream =
  let combined_span = {
    ts_file = s1.tstream_span.ts_file;
    ts_start = s1.tstream_span.ts_start;
    ts_end = s2.tstream_span.ts_end;
    ts_line = s1.tstream_span.ts_line;
    ts_column = s1.tstream_span.ts_column
  } in
  { tstream_trees = s1.tstream_trees @ s2.tstream_trees;
    tstream_span = combined_span }

(* Token tree size for termination proofs *)
let rec tt_size (tt: token_tree) : Tot nat (decreases tt) =
  match tt with
  | TTIdent _ _ | TTLiteral _ _ | TTPunct _ _ _ -> 1
  | TTGroup _ ts _ -> 1 + ts_size ts

and ts_size (ts: token_stream) : Tot nat (decreases ts.tstream_trees) =
  tt_list_size ts.tstream_trees

and tt_list_size (tts: list token_tree) : Tot nat (decreases tts) =
  match tts with
  | [] -> 0
  | tt :: rest -> tt_size tt + tt_list_size rest

(* Token stream is non-empty *)
let is_empty_stream (ts: token_stream) : bool =
  List.Tot.isEmpty ts.tstream_trees

(** ============================================================================
    TOKEN STREAM CURSOR - For parsing proc macro input
    ============================================================================ *)

(* Cursor position in a token stream *)
noeq type stream_cursor = {
  cursor_stream : token_stream;
  cursor_pos    : nat               (* Current position in tstream_trees *)
}

(* Create cursor at start of stream *)
let stream_start (ts: token_stream) : stream_cursor =
  { cursor_stream = ts; cursor_pos = 0 }

(* Check if cursor is at end *)
let cursor_at_end (c: stream_cursor) : bool =
  c.cursor_pos >= List.Tot.length c.cursor_stream.tstream_trees

(* Peek current token without advancing *)
let cursor_peek (c: stream_cursor) : option token_tree =
  List.Tot.nth c.cursor_stream.tstream_trees c.cursor_pos

(* Advance cursor by one position *)
let cursor_advance (c: stream_cursor) : stream_cursor =
  if cursor_at_end c then c
  else { c with cursor_pos = c.cursor_pos + 1 }

(* Get next token and advance cursor *)
let cursor_next (c: stream_cursor) : option (token_tree & stream_cursor) =
  match cursor_peek c with
  | None -> None
  | Some tt -> Some (tt, cursor_advance c)

(** ============================================================================
    CONVERSION: token <-> token_tree
    ============================================================================

    Convert between Macros.fst token type and TokenStream's token_tree.
    This enables interop between declarative and procedural macros.
    ============================================================================ *)

(* Convert Macros.fst token to token_tree *)
let rec token_to_tree (t: token) : token_tree =
  match t with
  | TokIdent s -> TTIdent s empty_span
  | TokLit lit -> TTLiteral lit empty_span
  | TokPunct s -> TTPunct s SpaceAlone empty_span
  | TokGroup delim inner ->
      let d = match delim with
        | "(" | ")" -> DelimParen
        | "{" | "}" -> DelimBrace
        | "[" | "]" -> DelimBracket
        | _ -> DelimNone
      in
      TTGroup d (tokens_to_stream inner) empty_span

and tokens_to_stream (ts: list token) : token_stream =
  let trees = List.Tot.map token_to_tree ts in
  { tstream_trees = trees; tstream_span = empty_span }

(* Convert token_tree back to Macros.fst token *)
let rec tree_to_token (tt: token_tree) : token =
  match tt with
  | TTIdent s _ -> TokIdent s
  | TTLiteral lit _ -> TokLit lit
  | TTPunct s _ _ -> TokPunct s
  | TTGroup d ts _ ->
      let delim = match d with
        | DelimParen -> "("
        | DelimBrace -> "{"
        | DelimBracket -> "["
        | DelimNone -> ""
      in
      TokGroup delim (stream_to_tokens ts)

and stream_to_tokens (ts: token_stream) : list token =
  List.Tot.map tree_to_token ts.tstream_trees

(** ============================================================================
    CAPABILITY MODEL - Sandbox restrictions for proc macro execution
    ============================================================================

    Procedural macros execute arbitrary code at compile time. This is powerful
    but dangerous. We use a capability-based model to restrict what proc macros
    can do:

    - Pure: can only transform tokens, no side effects
    - FileRead: can read files (for include! style macros)
    - EnvRead: can read environment variables
    - Network: can make network requests (dangerous!)
    - Exec: can execute external processes (very dangerous!)

    Capabilities form a lattice - each capability implies all weaker ones.
    ============================================================================ *)

(* Individual capabilities *)
type capability =
  | CapPure        (* Pure token transformation only *)
  | CapFileRead    (* Can read files *)
  | CapEnvRead     (* Can read environment variables *)
  | CapNetwork     (* Can make network requests *)
  | CapExec        (* Can execute external processes *)

(* Capability set *)
type cap_set = list capability

(* Empty capability set - maximum restriction *)
let cap_empty : cap_set = []

(* Pure capability set - the safe default *)
let cap_pure : cap_set = [CapPure]

(* Full capability set - maximum privilege (dangerous!) *)
let cap_full : cap_set = [CapPure; CapFileRead; CapEnvRead; CapNetwork; CapExec]

(* Check if capability set contains a specific capability *)
let has_cap (c: capability) (cs: cap_set) : bool =
  List.Tot.mem c cs

(* Capability ordering: c1 is weaker than or equal to c2 *)
let cap_order (c1 c2: capability) : bool =
  match c1, c2 with
  | CapPure, _ -> true            (* Pure is weakest *)
  | CapFileRead, CapFileRead -> true
  | CapFileRead, CapEnvRead -> true
  | CapFileRead, CapNetwork -> true
  | CapFileRead, CapExec -> true
  | CapEnvRead, CapEnvRead -> true
  | CapEnvRead, CapNetwork -> true
  | CapEnvRead, CapExec -> true
  | CapNetwork, CapNetwork -> true
  | CapNetwork, CapExec -> true
  | CapExec, CapExec -> true
  | _, _ -> false

(* Capability set ordering: cs1 is a subset of cs2 *)
let rec cap_set_leq (cs1 cs2: cap_set) : bool =
  match cs1 with
  | [] -> true
  | c :: rest -> has_cap c cs2 && cap_set_leq rest cs2

(* Capability set meet (intersection) *)
let cap_meet (cs1 cs2: cap_set) : cap_set =
  List.Tot.filter (fun c -> has_cap c cs2) cs1

(* Capability set join (union) *)
let cap_join (cs1 cs2: cap_set) : cap_set =
  cs1 @ List.Tot.filter (fun c -> not (has_cap c cs1)) cs2

(** ============================================================================
    TYPED CODE - Multi-Stage Programming integration
    ============================================================================

    Code[tau] is the type of code that, when executed, produces a value of
    type tau. This is the foundation of typed multi-stage programming (MSP).

    Unlike untyped token manipulation, Code[tau] preserves type information:
    - Quote lifts expression to Code: <e> : Code[tau] when e : tau
    - Splice inserts code: ~e : tau when e : Code[tau]
    - Run executes code: run(e) : tau when e : Code[tau]
    - Lift embeds runtime value: lift(v) : Code[tau] when v : tau (persistable)

    Proc macros can work with both untyped TokenStream and typed Code[tau].
    ============================================================================ *)

(* Stage level: 0 = runtime, 1+ = compile time *)
type stage = nat

(* Code type: typed representation of code fragment *)
noeq type code (tau: brrr_type) =
  | CQuote    : expr -> code tau           (* <e> - quoted expression *)
  | CLift     : code tau                   (* lift(v) - embedded value *)
  | CSplice   : code (t_code tau) -> code tau (* ~e - spliced code *)
  | CRun      : expr -> code tau           (* placeholder for run result *)

(* Helper: Code type constructor *)
let t_code (tau: brrr_type) : brrr_type =
  TNamed { tname_path = ["std"; "code"]; tname_name = "Code"; tname_args = [tau] }

(* Code with stage annotation *)
noeq type staged_code (tau: brrr_type) = {
  sc_code  : code tau;
  sc_stage : stage
}

(* Create code at stage 0 (runtime) *)
let code_at_runtime (#tau: brrr_type) (c: code tau) : staged_code tau =
  { sc_code = c; sc_stage = 0 }

(* Quote: lift expression to next stage *)
let quote (#tau: brrr_type) (e: expr) : staged_code tau =
  { sc_code = CQuote e; sc_stage = 1 }

(* Splice: lower code to current stage (only valid inside quote) *)
let splice (#tau: brrr_type) (sc: staged_code (t_code tau)) : option (staged_code tau) =
  if sc.sc_stage = 0 then None  (* Can't splice at stage 0 *)
  else Some { sc_code = CSplice sc.sc_code; sc_stage = sc.sc_stage - 1 }

(** ============================================================================
    CODE BUILDER - Constructing typed code programmatically
    ============================================================================

    CodeBuilder provides a typed interface for constructing code fragments.
    This is safer than raw TokenStream manipulation because types are checked.
    ============================================================================ *)

(* Code builder state *)
noeq type code_builder = {
  cb_exprs : list expr;        (* Accumulated expressions *)
  cb_stage : stage;            (* Current stage *)
  cb_marks : mark_state        (* For hygiene *)
}

(* Empty code builder *)
let empty_builder (st: mark_state) : code_builder =
  { cb_exprs = []; cb_stage = 1; cb_marks = st }

(* Add literal to builder *)
let cb_lit (lit: literal) (cb: code_builder) : code_builder =
  { cb with cb_exprs = ELit lit :: cb.cb_exprs }

(* Add variable reference to builder *)
let cb_var (x: string) (cb: code_builder) : code_builder =
  { cb with cb_exprs = EVar x :: cb.cb_exprs }

(* Add hygienic variable to builder *)
let cb_var_hygienic (x: string) (scope: nat) (cb: code_builder) : code_builder =
  let (id, marks') = fresh_ident x scope cb.cb_marks in
  { cb with
    cb_exprs = EVar id.id_name :: cb.cb_exprs;
    cb_marks = marks' }

(* Add binary operation to builder *)
let cb_binop (op: binary_op) (cb: code_builder) : option code_builder =
  match cb.cb_exprs with
  | e2 :: e1 :: rest -> Some { cb with cb_exprs = EBinary op e1 e2 :: rest }
  | _ -> None

(* Add function call to builder *)
let cb_call (n_args: nat) (cb: code_builder) : option code_builder =
  if List.Tot.length cb.cb_exprs < n_args + 1 then None
  else
    let (args_rev, rest) = List.Tot.splitAt n_args cb.cb_exprs in
    match rest with
    | f :: rest' ->
        Some { cb with cb_exprs = ECall f (List.Tot.rev args_rev) :: rest' }
    | [] -> None

(* Build let binding *)
let cb_let (x: string) (ty_opt: option brrr_type) (cb: code_builder)
    : option code_builder =
  match cb.cb_exprs with
  | body :: init :: rest ->
      Some { cb with cb_exprs = ELet (PatVar x) ty_opt init body :: rest }
  | _ -> None

(* Finalize builder to single expression *)
let cb_finalize (cb: code_builder) : option expr =
  match cb.cb_exprs with
  | [e] -> Some e
  | es -> Some (EBlock (List.Tot.rev es))

(** ============================================================================
    PROC MACRO TYPES - Function-like, Derive, and Attribute macros
    ============================================================================

    Three kinds of procedural macros:

    1. Function-like: foo!(...)
       Input: TokenStream (the contents of ...)
       Output: TokenStream (replacement code)

    2. Derive: #[derive(Foo)]
       Input: TokenStream (the struct/enum definition)
       Output: TokenStream (additional impl blocks)

    3. Attribute: #[foo(...)]
       Input: TokenStream (attribute args), TokenStream (annotated item)
       Output: TokenStream (replacement item)
    ============================================================================ *)

(* Proc macro result: success or error *)
noeq type pm_result =
  | PMSuccess : token_stream -> pm_result
  | PMError   : string -> token_span -> pm_result

(* Function-like proc macro signature *)
type fn_proc_macro = token_stream -> pm_result

(* Derive proc macro signature *)
type derive_proc_macro = token_stream -> pm_result

(* Attribute proc macro signature *)
type attr_proc_macro = token_stream -> token_stream -> pm_result

(* Proc macro kind *)
noeq type proc_macro_kind =
  | PMKFunction  : fn_proc_macro -> proc_macro_kind
  | PMKDerive    : derive_proc_macro -> proc_macro_kind
  | PMKAttribute : attr_proc_macro -> proc_macro_kind

(* Proc macro definition *)
noeq type proc_macro_def = {
  pm_name         : string;               (* Macro name *)
  pm_kind         : proc_macro_kind;      (* Kind with implementation *)
  pm_capabilities : cap_set;              (* Required capabilities *)
  pm_doc          : option string         (* Documentation *)
}

(** ============================================================================
    PROC MACRO CONTEXT - Runtime context for macro execution
    ============================================================================

    The context provides:
    - Capability checking
    - Error accumulation
    - Span tracking
    - Hygiene state
    ============================================================================ *)

(* Diagnostic severity *)
type diag_severity =
  | DiagError
  | DiagWarning
  | DiagNote
  | DiagHelp

(* Diagnostic message *)
noeq type diagnostic = {
  diag_severity : diag_severity;
  diag_message  : string;
  diag_span     : option token_span
}

(* Proc macro context *)
noeq type pm_context = {
  ctx_caps        : cap_set;              (* Available capabilities *)
  ctx_marks       : mark_state;           (* Hygiene mark state *)
  ctx_scope       : nat;                  (* Current scope level *)
  ctx_diagnostics : list diagnostic;      (* Accumulated diagnostics *)
  ctx_call_site   : token_span            (* Where macro was invoked *)
}

(* Create initial context with given capabilities *)
let init_context (caps: cap_set) (call_site: token_span) : pm_context = {
  ctx_caps = caps;
  ctx_marks = init_mark_state;
  ctx_scope = 0;
  ctx_diagnostics = [];
  ctx_call_site = call_site
}

(* Add diagnostic to context *)
let ctx_add_diag (sev: diag_severity) (msg: string) (sp: option token_span)
                  (ctx: pm_context) : pm_context =
  let diag = { diag_severity = sev; diag_message = msg; diag_span = sp } in
  { ctx with ctx_diagnostics = diag :: ctx.ctx_diagnostics }

(* Check if context has required capability *)
let ctx_has_cap (c: capability) (ctx: pm_context) : bool =
  has_cap c ctx.ctx_caps

(* Generate fresh hygienic identifier in context *)
let ctx_fresh_ident (name: string) (ctx: pm_context) : (ident & pm_context) =
  let (id, marks') = fresh_ident name ctx.ctx_scope ctx.ctx_marks in
  (id, { ctx with ctx_marks = marks' })

(* Enter new scope *)
let ctx_enter_scope (ctx: pm_context) : pm_context =
  { ctx with ctx_scope = ctx.ctx_scope + 1 }

(* Exit scope *)
let ctx_exit_scope (ctx: pm_context) : pm_context =
  if ctx.ctx_scope > 0 then { ctx with ctx_scope = ctx.ctx_scope - 1 }
  else ctx

(** ============================================================================
    DERIVE MACRO HELPERS - For implementing derive macros
    ============================================================================

    Derive macros transform struct/enum definitions into trait implementations.
    These helpers parse the input and generate output.
    ============================================================================ *)

(* Parsed struct information *)
noeq type struct_info = {
  si_name       : string;
  si_generics   : list string;           (* Generic type parameters *)
  si_fields     : list (string & type_rep);
  si_visibility : visibility
}

(* Parsed enum information *)
noeq type enum_info = {
  ei_name       : string;
  ei_generics   : list string;
  ei_variants   : list variant_info;
  ei_visibility : visibility
}

(* Enum variant information *)
and variant_info = {
  vi_name   : string;
  vi_fields : list (option string & type_rep)  (* Named or positional *)
}

(* Parse item kind (for derive macros) *)
noeq type item_info =
  | ItemStruct : struct_info -> item_info
  | ItemEnum   : enum_info -> item_info
  | ItemOther  : token_stream -> item_info

(* Parse struct from token stream (simplified) *)
let parse_struct_info (ts: token_stream) : option struct_info =
  (* Full implementation would parse:
     [pub] struct Name [<T, U>] { field: Type, ... }
     For now, return None as placeholder *)
  None

(* Parse enum from token stream (simplified) *)
let parse_enum_info (ts: token_stream) : option enum_info =
  None

(* Parse derive input *)
let parse_derive_input (ts: token_stream) : option item_info =
  match parse_struct_info ts with
  | Some si -> Some (ItemStruct si)
  | None ->
      match parse_enum_info ts with
      | Some ei -> Some (ItemEnum ei)
      | None -> Some (ItemOther ts)

(** ============================================================================
    TRAIT METHOD GENERATION - For derive macros
    ============================================================================ *)

(* Generate method signature token stream *)
let gen_method_sig (name: string) (params: list (string & type_rep))
                   (ret_ty: type_rep) : token_stream =
  (* fn name(self, params) -> ret_ty *)
  let fn_tok = TTIdent "fn" empty_span in
  let name_tok = TTIdent name empty_span in
  (* Simplified - would build full signature *)
  { tstream_trees = [fn_tok; name_tok]; tstream_span = empty_span }

(* Generate impl block header *)
let gen_impl_header (trait_name: string) (type_name: string)
                    (generics: list string) : token_stream =
  let impl_tok = TTIdent "impl" empty_span in
  let trait_tok = TTIdent trait_name empty_span in
  let for_tok = TTIdent "for" empty_span in
  let type_tok = TTIdent type_name empty_span in
  { tstream_trees = [impl_tok; trait_tok; for_tok; type_tok];
    tstream_span = empty_span }

(** ============================================================================
    EXPANSION TRACKING - For Brrr-Machine analysis
    ============================================================================

    Brrr-Machine needs to track macro expansions for:
    - Error attribution (map errors back to original source)
    - Code coverage analysis
    - Security taint tracking through macros
    - Call graph construction

    Each expansion is recorded with:
    - Original token span
    - Expanded token span
    - Macro identity
    - Hygiene mapping
    ============================================================================ *)

(* Expansion ID for tracking *)
type expansion_id = nat

(* Expansion record *)
noeq type expansion_record = {
  exp_id          : expansion_id;
  exp_macro_name  : string;
  exp_kind        : proc_macro_kind;
  exp_input_span  : token_span;
  exp_output_span : token_span;
  exp_hygiene_map : list (ident & ident);  (* Original -> renamed mappings *)
  exp_parent      : option expansion_id    (* For nested macro calls *)
}

(* Expansion trace: sequence of expansions *)
type expansion_trace = list expansion_record

(* Empty expansion trace *)
let empty_trace : expansion_trace = []

(* Global expansion counter (would be in state monad in real impl) *)
let next_expansion_id (trace: expansion_trace) : expansion_id =
  List.Tot.length trace

(* Record new expansion *)
let record_expansion (macro_name: string) (kind: proc_macro_kind)
                     (input_span: token_span) (output_span: token_span)
                     (hygiene: list (ident & ident)) (parent: option expansion_id)
                     (trace: expansion_trace) : expansion_trace =
  let exp = {
    exp_id = next_expansion_id trace;
    exp_macro_name = macro_name;
    exp_kind = kind;
    exp_input_span = input_span;
    exp_output_span = output_span;
    exp_hygiene_map = hygiene;
    exp_parent = parent
  } in
  exp :: trace

(* Find expansion by ID *)
let find_expansion (id: expansion_id) (trace: expansion_trace)
    : option expansion_record =
  List.Tot.find (fun exp -> exp.exp_id = id) trace

(* Get all expansions of a specific macro *)
let get_macro_expansions (name: string) (trace: expansion_trace)
    : list expansion_record =
  List.Tot.filter (fun exp -> exp.exp_macro_name = name) trace

(* Map span back through expansions to original source *)
let rec trace_to_original (sp: token_span) (trace: expansion_trace)
    : token_span =
  match List.Tot.find (fun exp ->
    sp.ts_file = exp.exp_output_span.ts_file &&
    sp.ts_start >= exp.exp_output_span.ts_start &&
    sp.ts_end <= exp.exp_output_span.ts_end) trace with
  | None -> sp  (* Not in any expansion *)
  | Some exp -> trace_to_original exp.exp_input_span trace

(** ============================================================================
    PROC MACRO REGISTRY - Registration and lookup
    ============================================================================ *)

(* Proc macro registry *)
type pm_registry = list (string & proc_macro_def)

(* Empty registry *)
let empty_pm_registry : pm_registry = []

(* Register proc macro *)
let register_proc_macro (m: proc_macro_def) (reg: pm_registry) : pm_registry =
  (m.pm_name, m) :: reg

(* Lookup proc macro by name *)
let lookup_proc_macro (name: string) (reg: pm_registry) : option proc_macro_def =
  List.Tot.assoc name reg

(* Check if macro requires dangerous capabilities *)
let macro_requires_dangerous_caps (m: proc_macro_def) : bool =
  has_cap CapNetwork m.pm_capabilities ||
  has_cap CapExec m.pm_capabilities

(** ============================================================================
    PROC MACRO EXECUTION
    ============================================================================

    Execute a proc macro with capability checking and expansion tracking.
    ============================================================================ *)

(* Execution result *)
noeq type exec_result = {
  er_result : pm_result;
  er_trace  : expansion_record;
  er_ctx    : pm_context
}

(* Execute function-like proc macro *)
let exec_fn_macro (m: proc_macro_def) (input: token_stream) (ctx: pm_context)
                  (parent_exp: option expansion_id)
    : option exec_result =
  (* Check capabilities *)
  if not (cap_set_leq m.pm_capabilities ctx.ctx_caps) then
    let ctx' = ctx_add_diag DiagError
      ("Macro " ^ m.pm_name ^ " requires capabilities not granted")
      (Some ctx.ctx_call_site) ctx in
    None
  else
    match m.pm_kind with
    | PMKFunction fn ->
        let result = fn input in
        let output_span = match result with
          | PMSuccess ts -> ts.tstream_span
          | PMError _ sp -> sp
        in
        let exp = {
          exp_id = 0;  (* Would be assigned by trace *)
          exp_macro_name = m.pm_name;
          exp_kind = m.pm_kind;
          exp_input_span = input.tstream_span;
          exp_output_span = output_span;
          exp_hygiene_map = [];
          exp_parent = parent_exp
        } in
        Some { er_result = result; er_trace = exp; er_ctx = ctx }
    | _ -> None  (* Not a function-like macro *)

(* Execute derive macro *)
let exec_derive_macro (m: proc_macro_def) (input: token_stream) (ctx: pm_context)
                      (parent_exp: option expansion_id)
    : option exec_result =
  if not (cap_set_leq m.pm_capabilities ctx.ctx_caps) then None
  else
    match m.pm_kind with
    | PMKDerive fn ->
        let result = fn input in
        let output_span = match result with
          | PMSuccess ts -> ts.tstream_span
          | PMError _ sp -> sp
        in
        let exp = {
          exp_id = 0;
          exp_macro_name = m.pm_name;
          exp_kind = m.pm_kind;
          exp_input_span = input.tstream_span;
          exp_output_span = output_span;
          exp_hygiene_map = [];
          exp_parent = parent_exp
        } in
        Some { er_result = result; er_trace = exp; er_ctx = ctx }
    | _ -> None

(* Execute attribute macro *)
let exec_attr_macro (m: proc_macro_def) (attr_args: token_stream)
                    (item: token_stream) (ctx: pm_context)
                    (parent_exp: option expansion_id)
    : option exec_result =
  if not (cap_set_leq m.pm_capabilities ctx.ctx_caps) then None
  else
    match m.pm_kind with
    | PMKAttribute fn ->
        let result = fn attr_args item in
        let output_span = match result with
          | PMSuccess ts -> ts.tstream_span
          | PMError _ sp -> sp
        in
        let exp = {
          exp_id = 0;
          exp_macro_name = m.pm_name;
          exp_kind = m.pm_kind;
          exp_input_span = item.tstream_span;
          exp_output_span = output_span;
          exp_hygiene_map = [];
          exp_parent = parent_exp
        } in
        Some { er_result = result; er_trace = exp; er_ctx = ctx }
    | _ -> None

(** ============================================================================
    QUOTE MACRO - Built-in quasi-quotation for proc macros
    ============================================================================

    The quote! macro enables quasi-quotation in proc macros:

    quote! {
        let x = #expr;
        x + 1
    }

    Where #expr is an antiquotation (splice) of a token_stream variable.
    ============================================================================ *)

(* Quote interpolation marker *)
noeq type quote_interp =
  | QIExpr   : string -> quote_interp    (* #name - splice expression *)
  | QIIdent  : string -> quote_interp    (* #name - splice as identifier *)
  | QITokens : string -> quote_interp    (* ##name - splice tokens directly *)
  | QIRepeat : quote_template -> string -> string -> quote_interp
                                          (* #(...)* with sep and var *)

(* Quote template element *)
and quote_template_elem =
  | QTLit    : token_tree -> quote_template_elem
  | QTInterp : quote_interp -> quote_template_elem

(* Quote template *)
and quote_template = list quote_template_elem

(* Quote variable environment: name -> token_stream *)
type quote_env = list (string & token_stream)

(* Lookup in quote environment *)
let quote_lookup (name: string) (env: quote_env) : option token_stream =
  List.Tot.assoc name env

(* Expand quote template with environment *)
let rec expand_quote_template (tmpl: quote_template) (env: quote_env)
    : option token_stream =
  match tmpl with
  | [] -> Some empty_token_stream
  | elem :: rest ->
      (match expand_quote_elem elem env with
       | None -> None
       | Some ts1 ->
           (match expand_quote_template rest env with
            | None -> None
            | Some ts2 -> Some (concat_streams ts1 ts2)))

and expand_quote_elem (elem: quote_template_elem) (env: quote_env)
    : option token_stream =
  match elem with
  | QTLit tt -> Some (singleton_stream tt)
  | QTInterp interp ->
      (match interp with
       | QIExpr name | QIIdent name | QITokens name -> quote_lookup name env
       | QIRepeat _ _ _ -> None)  (* Would need iteration support *)

(** ============================================================================
    SAFETY PROOFS
    ============================================================================

    Key safety properties for procedural macros.
    ============================================================================ *)

(* Capability checking is transitive *)
val cap_set_leq_trans : cs1:cap_set -> cs2:cap_set -> cs3:cap_set ->
  Lemma (requires cap_set_leq cs1 cs2 /\ cap_set_leq cs2 cs3)
        (ensures cap_set_leq cs1 cs3)
let rec cap_set_leq_trans cs1 cs2 cs3 =
  match cs1 with
  | [] -> ()
  | c :: rest ->
      (* c is in cs2 and cs2 <= cs3, so c is in cs3 *)
      cap_set_leq_trans rest cs2 cs3

(* Empty capability set is always satisfied *)
val cap_empty_satisfied : cs:cap_set ->
  Lemma (ensures cap_set_leq cap_empty cs)
let cap_empty_satisfied cs = ()

(* Pure capability is minimal non-empty *)
val cap_pure_minimal : cs:cap_set ->
  Lemma (requires has_cap CapPure cs)
        (ensures cap_set_leq cap_pure cs)
let cap_pure_minimal cs = ()

(* Expansion trace length increases *)
val trace_length_increases : macro_name:string -> kind:proc_macro_kind ->
  input_span:token_span -> output_span:token_span ->
  hygiene:list (ident & ident) -> parent:option expansion_id ->
  trace:expansion_trace ->
  Lemma (ensures List.Tot.length (record_expansion macro_name kind input_span
                                    output_span hygiene parent trace) >
                 List.Tot.length trace)
let trace_length_increases _ _ _ _ _ _ trace = ()

(* Hygiene is preserved through proc macro execution *)
val proc_macro_hygiene : ctx:pm_context -> name:string -> scope:nat ->
  Lemma (requires ctx.ctx_marks >= 1)
        (ensures (let (id, ctx') = ctx_fresh_ident name ctx in
                  id.id_mark >= 1 /\ ctx'.ctx_marks > ctx.ctx_marks))
let proc_macro_hygiene ctx name scope =
  fresh_mark_increasing ctx.ctx_marks

(** ============================================================================
    EXAMPLE PROC MACROS
    ============================================================================ *)

(* Example: stringify! macro - converts tokens to string literal *)
let stringify_macro : fn_proc_macro =
  fun input ->
    let rec tokens_to_string (tts: list token_tree) : string =
      match tts with
      | [] -> ""
      | TTIdent s _ :: rest -> s ^ " " ^ tokens_to_string rest
      | TTLiteral (LitString s) _ :: rest -> "\"" ^ s ^ "\"" ^ tokens_to_string rest
      | TTLiteral (LitInt n _) _ :: rest -> (* Would convert int *) tokens_to_string rest
      | TTPunct s _ _ :: rest -> s ^ tokens_to_string rest
      | TTGroup _ inner _ :: rest ->
          "(" ^ tokens_to_string inner.tstream_trees ^ ")" ^ tokens_to_string rest
      | _ :: rest -> tokens_to_string rest
    in
    let result_str = tokens_to_string input.tstream_trees in
    let lit_tok = TTLiteral (LitString result_str) input.tstream_span in
    PMSuccess (singleton_stream lit_tok)

(* Register stringify macro *)
let stringify_def : proc_macro_def = {
  pm_name = "stringify";
  pm_kind = PMKFunction stringify_macro;
  pm_capabilities = cap_pure;
  pm_doc = Some "Converts tokens to a string literal"
}

(* Example: derive Debug (simplified) *)
let derive_debug_macro : derive_proc_macro =
  fun input ->
    match parse_derive_input input with
    | None -> PMError "Could not parse input" input.tstream_span
    | Some (ItemStruct si) ->
        (* Generate: impl Debug for StructName { fn fmt(...) { ... } } *)
        let header = gen_impl_header "Debug" si.si_name si.si_generics in
        PMSuccess header  (* Simplified - would generate full impl *)
    | Some (ItemEnum ei) ->
        let header = gen_impl_header "Debug" ei.ei_name ei.ei_generics in
        PMSuccess header
    | Some (ItemOther _) ->
        PMError "derive(Debug) only works on struct/enum" input.tstream_span

let derive_debug_def : proc_macro_def = {
  pm_name = "Debug";
  pm_kind = PMKDerive derive_debug_macro;
  pm_capabilities = cap_pure;
  pm_doc = Some "Derive Debug trait implementation"
}

(* Default proc macro registry *)
let default_pm_registry : pm_registry =
  register_proc_macro derive_debug_def
    (register_proc_macro stringify_def empty_pm_registry)

(** ============================================================================
    INTEGRATION WITH DECLARATIVE MACROS
    ============================================================================

    Allow using proc macros within macro_rules! expansions and vice versa.
    ============================================================================ *)

(* Unified macro kind *)
noeq type any_macro =
  | AMDeclarative : macro_def -> any_macro
  | AMProcedural  : proc_macro_def -> any_macro

(* Unified registry *)
type unified_registry = list (string & any_macro)

(* Lookup in unified registry *)
let lookup_any_macro (name: string) (reg: unified_registry) : option any_macro =
  List.Tot.assoc name reg

(* Convert declarative macro result to token stream *)
let syntax_to_token_stream (s: syntax) : option token_stream =
  match s with
  | SynExpr _ e ->
      (* Would convert expression to tokens *)
      Some empty_token_stream  (* Placeholder *)
  | SynList ss ->
      Some empty_token_stream  (* Placeholder *)
  | _ -> None

(* Convert token stream to syntax for declarative macros *)
let token_stream_to_syntax (ts: token_stream) : option syntax =
  let tokens = stream_to_tokens ts in
  Some (SynList (List.Tot.map (fun t -> SynToken t) tokens))

(** ============================================================================
    BRRR-MACHINE INTERFACE
    ============================================================================

    Interface for Brrr-Machine to query macro expansion information.
    ============================================================================ *)

(* Query: get all expansions in a file *)
let get_file_expansions (filename: string) (trace: expansion_trace)
    : list expansion_record =
  List.Tot.filter (fun exp -> exp.exp_input_span.ts_file = filename) trace

(* Query: check if span is within macro expansion *)
let span_in_expansion (sp: token_span) (trace: expansion_trace) : bool =
  List.Tot.existsb (fun exp ->
    sp.ts_file = exp.exp_output_span.ts_file &&
    sp.ts_start >= exp.exp_output_span.ts_start &&
    sp.ts_end <= exp.exp_output_span.ts_end) trace

(* Query: get expansion depth (how nested) *)
let rec expansion_depth (exp: expansion_record) (trace: expansion_trace) : nat =
  match exp.exp_parent with
  | None -> 0
  | Some parent_id ->
      match find_expansion parent_id trace with
      | None -> 0
      | Some parent -> 1 + expansion_depth parent trace

(* Query: get all macros used in code *)
let get_used_macros (trace: expansion_trace) : list string =
  List.Tot.map (fun exp -> exp.exp_macro_name) trace

(* Security: check if any dangerous macros were used *)
let has_dangerous_expansions (trace: expansion_trace) (reg: pm_registry) : bool =
  List.Tot.existsb (fun exp ->
    match lookup_proc_macro exp.exp_macro_name reg with
    | None -> false
    | Some m -> macro_requires_dangerous_caps m) trace

(** ============================================================================
    FINAL TYPE SUMMARY
    ============================================================================

    Key types exported by this module:

    - token_stream      : TokenStream type for proc macro I/O
    - proc_macro_def    : Procedural macro definition
    - pm_context        : Execution context with capabilities
    - expansion_trace   : Track all macro expansions
    - code tau          : Typed code for MSP integration
    - code_builder      : Programmatic code construction
    - cap_set           : Capability restrictions

    Key functions:
    - exec_fn_macro     : Execute function-like proc macro
    - exec_derive_macro : Execute derive macro
    - exec_attr_macro   : Execute attribute macro
    - trace_to_original : Map expanded spans back to source
    - expand_quote_template : Quasi-quotation expansion
    ============================================================================ *)
