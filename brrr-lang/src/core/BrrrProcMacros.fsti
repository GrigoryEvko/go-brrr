(**
 * BrrrLang.Core.ProcMacros Interface
 * ===================================
 *
 * Procedural Macro System with Typed Multi-Stage Programming Integration
 *
 * This module implements the procedural macro subsystem for Brrr-Lang, extending
 * the declarative macro_rules! system (see BrrrMacros.fst) with full programmatic
 * control over syntax transformation. Based on brrr_lang_spec_v0.4.tex Part VI.
 *
 * ============================================================================
 * KEY FEATURES
 * ============================================================================
 *
 * 1. Three kinds of procedural macros:
 *    - Function-like: macro_name!(input_tokens)
 *    - Derive: #[derive(MacroName)] struct/enum
 *    - Attribute: #[macro_name(args)] item
 *
 * 2. Capability-based security model
 *    - Default: pure token transformation only
 *    - Optional: file read, env read, network, exec
 *
 * 3. Typed code generation via Code[tau]
 *    - Multi-stage programming integration
 *    - Quote, splice, run, lift operations
 *
 * 4. Expansion tracking for Brrr-Machine analysis
 *    - Error attribution
 *    - Taint analysis
 *    - Code coverage
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Macros, Reflection
 *)
module BrrrProcMacros

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrMacros
open BrrrReflection
open FStar.List.Tot


(** ============================================================================
    TOKEN STREAM - Input/Output interface for procedural macros
    ============================================================================ *)

(** Span tracks source location for error messages *)
type token_span = {
  ts_file   : string;
  ts_start  : nat;     (** Byte offset start *)
  ts_end    : nat;     (** Byte offset end *)
  ts_line   : nat;     (** Line number (1-based) *)
  ts_column : nat      (** Column number (1-based) *)
}

(** Create empty span *)
val empty_span : token_span

(** Delimiter kind for grouped tokens *)
type delimiter =
  | DelimParen   (** ( ) *)
  | DelimBrace   (** { } *)
  | DelimBracket (** [ ] *)
  | DelimNone    (** No delimiters - invisible grouping *)

(** Spacing information for pretty-printing *)
type spacing =
  | SpaceAlone  (** Token is followed by whitespace *)
  | SpaceJoint  (** Token is directly adjacent to next token *)

(** Token tree: structured token representation with spans *)
noeq type token_tree =
  | TTIdent   : string -> token_span -> token_tree
  | TTLiteral : literal -> token_span -> token_tree
  | TTPunct   : string -> spacing -> token_span -> token_tree
  | TTGroup   : delimiter -> token_stream -> token_span -> token_tree

(** Token stream: sequence of token trees *)
and token_stream = {
  tstream_trees : list token_tree;
  tstream_span  : token_span     (** Combined span of all tokens *)
}

(** Empty token stream *)
val empty_token_stream : token_stream

(** Create stream from single token tree *)
val singleton_stream : tt:token_tree -> token_stream

(** Concatenate two token streams *)
val concat_streams : s1:token_stream -> s2:token_stream -> token_stream

(** Token tree size for termination proofs *)
val tt_size : tt:token_tree -> Tot nat (decreases tt)

(** Token stream size for termination proofs *)
val ts_size : ts:token_stream -> Tot nat (decreases ts.tstream_trees)

(** Token tree list size for termination proofs *)
val tt_list_size : tts:list token_tree -> Tot nat (decreases tts)

(** Token stream is non-empty *)
val is_empty_stream : ts:token_stream -> bool


(** ============================================================================
    TOKEN STREAM CURSOR - For parsing proc macro input
    ============================================================================ *)

(** Cursor position in a token stream *)
noeq type stream_cursor = {
  cursor_stream : token_stream;
  cursor_pos    : nat               (** Current position in tstream_trees *)
}

(** Create cursor at start of stream *)
val stream_start : ts:token_stream -> stream_cursor

(** Check if cursor is at end *)
val cursor_at_end : c:stream_cursor -> bool

(** Peek current token without advancing *)
val cursor_peek : c:stream_cursor -> option token_tree

(** Advance cursor by one position *)
val cursor_advance : c:stream_cursor -> stream_cursor

(** Get next token and advance cursor *)
val cursor_next : c:stream_cursor -> option (token_tree & stream_cursor)


(** ============================================================================
    CONVERSION: token <-> token_tree
    ============================================================================ *)

(** Convert BrrrMacros.fst token to token_tree *)
val token_to_tree : t:token -> token_tree

(** Convert tokens to stream *)
val tokens_to_stream : ts:list token -> token_stream

(** Convert token_tree back to BrrrMacros.fst token *)
val tree_to_token : tt:token_tree -> token

(** Convert stream to tokens *)
val stream_to_tokens : ts:token_stream -> list token


(** ============================================================================
    CAPABILITY MODEL - Sandbox restrictions for proc macro execution
    ============================================================================

    Procedural macros execute ARBITRARY CODE at compile time.
    The capability model restricts what macros can do by default.
    ============================================================================ *)

(** Individual capabilities *)
type capability =
  | CapPure        (** Pure token transformation only *)
  | CapFileRead    (** Can read files *)
  | CapEnvRead     (** Can read environment variables *)
  | CapNetwork     (** Can make network requests - DANGEROUS *)
  | CapExec        (** Can execute external processes - VERY DANGEROUS *)

(** Capability set *)
type cap_set = list capability

(** Empty capability set - maximum restriction *)
val cap_empty : cap_set

(** Pure capability set - the safe default *)
val cap_pure : cap_set

(** Full capability set - maximum privilege (dangerous!) *)
val cap_full : cap_set

(** Check if capability set contains a specific capability *)
val has_cap : c:capability -> cs:cap_set -> bool

(** Capability ordering: c1 is weaker than or equal to c2 *)
val cap_order : c1:capability -> c2:capability -> bool

(** Capability set ordering: cs1 is a subset of cs2 *)
val cap_set_leq : cs1:cap_set -> cs2:cap_set -> bool

(** Capability set meet (intersection) *)
val cap_meet : cs1:cap_set -> cs2:cap_set -> cap_set

(** Capability set join (union) *)
val cap_join : cs1:cap_set -> cs2:cap_set -> cap_set


(** ============================================================================
    TYPED CODE - Multi-Stage Programming integration
    ============================================================================

    Code[tau] is a REPRESENTATION of code that computes a tau value.
    Operations: quote, splice, run, lift

    Stage 0 = Runtime
    Stage 1 = Compile time
    Stage n = Meta-level n
    ============================================================================ *)

(** Stage level: 0 = runtime, 1+ = compile time *)
type stage = nat

(** Code type: typed representation of code fragment *)
val t_code : tau:brrr_type -> brrr_type

(** Code with stage annotation *)
noeq type code (tau: brrr_type) =
  | CQuote    : expr -> code tau           (** <e> - quoted expression *)
  | CLift     : code tau                   (** lift(v) - embedded value *)
  | CSplice   : code (t_code tau) -> code tau (** ~e - spliced code *)
  | CRun      : expr -> code tau           (** placeholder for run result *)

(** Helper: Code type constructor *)
noeq type staged_code (tau: brrr_type) = {
  sc_code  : code tau;
  sc_stage : stage
}

(** Create code at stage 0 (runtime) *)
val code_at_runtime : #tau:brrr_type -> c:code tau -> staged_code tau

(** Quote: lift expression to next stage *)
val quote_expr : #tau:brrr_type -> e:expr -> staged_code tau

(** Splice: lower code to current stage (only valid inside quote) *)
val splice : #tau:brrr_type -> sc:staged_code (t_code tau) -> option (staged_code tau)


(** ============================================================================
    CODE BUILDER - Constructing typed code programmatically
    ============================================================================ *)

(** Code builder state *)
noeq type code_builder = {
  cb_exprs : list expr;        (** Accumulated expressions *)
  cb_stage : stage;            (** Current stage *)
  cb_marks : mark_state        (** For hygiene *)
}

(** Empty code builder *)
val empty_builder : st:mark_state -> code_builder

(** Add literal to builder *)
val cb_lit : lit:literal -> cb:code_builder -> code_builder

(** Add variable reference to builder *)
val cb_var : x:string -> cb:code_builder -> code_builder

(** Add hygienic variable to builder *)
val cb_var_hygienic : x:string -> scope:nat -> cb:code_builder -> code_builder

(** Add binary operation to builder *)
val cb_binop : op:binary_op -> cb:code_builder -> option code_builder

(** Add function call to builder *)
val cb_call : n_args:nat -> cb:code_builder -> option code_builder

(** Build let binding *)
val cb_let : x:string -> ty_opt:option brrr_type -> cb:code_builder -> option code_builder

(** Finalize builder to single expression *)
val cb_finalize : cb:code_builder -> option expr


(** ============================================================================
    PROC MACRO TYPES - Function-like, Derive, and Attribute macros
    ============================================================================ *)

(** Proc macro result: success or error *)
noeq type pm_result =
  | PMSuccess : token_stream -> pm_result
  | PMError   : string -> token_span -> pm_result

(** Function-like proc macro signature *)
type fn_proc_macro = token_stream -> pm_result

(** Derive proc macro signature *)
type derive_proc_macro = token_stream -> pm_result

(** Attribute proc macro signature *)
type attr_proc_macro = token_stream -> token_stream -> pm_result

(** Proc macro kind *)
noeq type proc_macro_kind =
  | PMKFunction  : fn_proc_macro -> proc_macro_kind
  | PMKDerive    : derive_proc_macro -> proc_macro_kind
  | PMKAttribute : attr_proc_macro -> proc_macro_kind

(** Proc macro definition *)
noeq type proc_macro_def = {
  pm_name         : string;               (** Macro name *)
  pm_kind         : proc_macro_kind;      (** Kind with implementation *)
  pm_capabilities : cap_set;              (** Required capabilities *)
  pm_doc          : option string         (** Documentation *)
}


(** ============================================================================
    PROC MACRO CONTEXT - Runtime context for macro execution
    ============================================================================ *)

(** Diagnostic severity *)
type diag_severity =
  | DiagError
  | DiagWarning
  | DiagNote
  | DiagHelp

(** Diagnostic message *)
noeq type diagnostic = {
  diag_severity : diag_severity;
  diag_message  : string;
  diag_span     : option token_span
}

(** Proc macro context *)
noeq type pm_context = {
  ctx_caps        : cap_set;              (** Available capabilities *)
  ctx_marks       : mark_state;           (** Hygiene mark state *)
  ctx_scope       : nat;                  (** Current scope level *)
  ctx_diagnostics : list diagnostic;      (** Accumulated diagnostics *)
  ctx_call_site   : token_span            (** Where macro was invoked *)
}

(** Create initial context with given capabilities *)
val init_context : caps:cap_set -> call_site:token_span -> pm_context

(** Add diagnostic to context *)
val ctx_add_diag : sev:diag_severity -> msg:string -> sp:option token_span ->
                   ctx:pm_context -> pm_context

(** Check if context has required capability *)
val ctx_has_cap : c:capability -> ctx:pm_context -> bool

(** Generate fresh hygienic identifier in context *)
val ctx_fresh_ident : name:string -> ctx:pm_context -> (ident & pm_context)

(** Enter new scope *)
val ctx_enter_scope : ctx:pm_context -> pm_context

(** Exit scope *)
val ctx_exit_scope : ctx:pm_context -> pm_context


(** ============================================================================
    DERIVE MACRO HELPERS - For implementing derive macros
    ============================================================================ *)

(** Parsed struct information *)
noeq type struct_info = {
  si_name       : string;
  si_generics   : list string;           (** Generic type parameters *)
  si_fields     : list (string & type_rep);
  si_visibility : visibility
}

(** Enum variant information *)
noeq type variant_info = {
  vi_name   : string;
  vi_fields : list (option string & type_rep)  (** Named or positional *)
}

(** Parsed enum information *)
noeq type enum_info = {
  ei_name       : string;
  ei_generics   : list string;
  ei_variants   : list variant_info;
  ei_visibility : visibility
}

(** Parse item kind (for derive macros) *)
noeq type item_info =
  | ItemStruct : struct_info -> item_info
  | ItemEnum   : enum_info -> item_info
  | ItemOther  : token_stream -> item_info

(** Parse struct from token stream (simplified) *)
val parse_struct_info : ts:token_stream -> option struct_info

(** Parse enum from token stream (simplified) *)
val parse_enum_info : ts:token_stream -> option enum_info

(** Parse derive input *)
val parse_derive_input : ts:token_stream -> option item_info

(** Generate method signature token stream *)
val gen_method_sig : name:string -> params:list (string & type_rep) ->
                     ret_ty:type_rep -> token_stream

(** Generate impl block header *)
val gen_impl_header : trait_name:string -> type_name:string ->
                      generics:list string -> token_stream


(** ============================================================================
    EXPANSION TRACKING - For Brrr-Machine analysis
    ============================================================================

    Macro expansion tracking enables:
    - Error attribution to original source
    - Taint analysis through expansions
    - Code coverage attribution
    - Security auditing
    ============================================================================ *)

(** Expansion ID for tracking *)
type expansion_id = nat

(** Expansion record *)
noeq type expansion_record = {
  exp_id          : expansion_id;
  exp_macro_name  : string;
  exp_kind        : proc_macro_kind;
  exp_input_span  : token_span;
  exp_output_span : token_span;
  exp_hygiene_map : list (ident & ident);  (** Original -> renamed mappings *)
  exp_parent      : option expansion_id    (** For nested macro calls *)
}

(** Expansion trace: sequence of expansions *)
type expansion_trace = list expansion_record

(** Empty expansion trace *)
val empty_trace : expansion_trace

(** Get next expansion ID *)
val next_expansion_id : trace:expansion_trace -> expansion_id

(** Record new expansion *)
val record_expansion : macro_name:string -> kind:proc_macro_kind ->
                       input_span:token_span -> output_span:token_span ->
                       hygiene:list (ident & ident) -> parent:option expansion_id ->
                       trace:expansion_trace -> expansion_trace

(** Find expansion by ID *)
val find_expansion : id:expansion_id -> trace:expansion_trace ->
  option expansion_record

(** Get all expansions of a specific macro *)
val get_macro_expansions : name:string -> trace:expansion_trace ->
  list expansion_record

(** Map span back through expansions to original source *)
val trace_to_original : sp:token_span -> trace:expansion_trace -> token_span


(** ============================================================================
    PROC MACRO REGISTRY - Registration and lookup
    ============================================================================ *)

(** Proc macro registry *)
type pm_registry = list (string & proc_macro_def)

(** Empty registry *)
val empty_pm_registry : pm_registry

(** Register proc macro *)
val register_proc_macro : m:proc_macro_def -> reg:pm_registry -> pm_registry

(** Lookup proc macro by name *)
val lookup_proc_macro : name:string -> reg:pm_registry -> option proc_macro_def

(** Check if macro requires dangerous capabilities *)
val macro_requires_dangerous_caps : m:proc_macro_def -> bool


(** ============================================================================
    PROC MACRO EXECUTION
    ============================================================================ *)

(** Execution result *)
noeq type exec_result = {
  er_result : pm_result;
  er_trace  : expansion_record;
  er_ctx    : pm_context
}

(** Execute function-like proc macro *)
val exec_fn_macro : m:proc_macro_def -> input:token_stream -> ctx:pm_context ->
                    parent_exp:option expansion_id ->
  option exec_result

(** Execute derive macro *)
val exec_derive_macro : m:proc_macro_def -> input:token_stream -> ctx:pm_context ->
                        parent_exp:option expansion_id ->
  option exec_result

(** Execute attribute macro *)
val exec_attr_macro : m:proc_macro_def -> attr_args:token_stream ->
                      item:token_stream -> ctx:pm_context ->
                      parent_exp:option expansion_id ->
  option exec_result


(** ============================================================================
    QUOTE MACRO - Built-in quasi-quotation for proc macros
    ============================================================================ *)

(** Quote interpolation marker *)
noeq type quote_interp =
  | QIExpr   : string -> quote_interp    (** #name - splice expression *)
  | QIIdent  : string -> quote_interp    (** #name - splice as identifier *)
  | QITokens : string -> quote_interp    (** ##name - splice tokens directly *)
  | QIRepeat : quote_template -> string -> string -> quote_interp
                                          (** #(...)* with sep and var *)

(** Quote template element *)
and quote_template_elem =
  | QTLit    : token_tree -> quote_template_elem
  | QTInterp : quote_interp -> quote_template_elem

(** Quote template *)
and quote_template = list quote_template_elem

(** Quote variable environment: name -> token_stream *)
type quote_env = list (string & token_stream)

(** Lookup in quote environment *)
val quote_lookup : name:string -> env:quote_env -> option token_stream

(** Expand quote template with environment *)
val expand_quote_template : tmpl:quote_template -> env:quote_env ->
  option token_stream

(** Expand single quote template element *)
val expand_quote_elem : elem:quote_template_elem -> env:quote_env ->
  option token_stream


(** ============================================================================
    SAFETY PROOFS
    ============================================================================ *)

(** Capability checking is transitive *)
val cap_set_leq_trans : cs1:cap_set -> cs2:cap_set -> cs3:cap_set ->
  Lemma (requires cap_set_leq cs1 cs2 /\ cap_set_leq cs2 cs3)
        (ensures cap_set_leq cs1 cs3)

(** Empty capability set is always satisfied *)
val cap_empty_satisfied : cs:cap_set ->
  Lemma (ensures cap_set_leq cap_empty cs)

(** Pure capability is minimal non-empty *)
val cap_pure_minimal : cs:cap_set ->
  Lemma (requires has_cap CapPure cs)
        (ensures cap_set_leq cap_pure cs)

(** Expansion trace length increases *)
val trace_length_increases : macro_name:string -> kind:proc_macro_kind ->
  input_span:token_span -> output_span:token_span ->
  hygiene:list (ident & ident) -> parent:option expansion_id ->
  trace:expansion_trace ->
  Lemma (ensures List.Tot.length (record_expansion macro_name kind input_span
                                    output_span hygiene parent trace) >
                 List.Tot.length trace)

(** Hygiene is preserved through proc macro execution *)
val proc_macro_hygiene : ctx:pm_context -> name:string -> scope:nat ->
  Lemma (requires ctx.ctx_marks >= 1)
        (ensures (let (id, ctx') = ctx_fresh_ident name ctx in
                  id.id_mark >= 1 /\ ctx'.ctx_marks > ctx.ctx_marks))


(** ============================================================================
    EXAMPLE PROC MACROS
    ============================================================================ *)

(** stringify! macro - converts tokens to string literal *)
val stringify_macro : fn_proc_macro

(** stringify macro definition *)
val stringify_def : proc_macro_def

(** derive Debug macro (simplified) *)
val derive_debug_macro : derive_proc_macro

(** derive Debug definition *)
val derive_debug_def : proc_macro_def

(** Default proc macro registry *)
val default_pm_registry : pm_registry


(** ============================================================================
    INTEGRATION WITH DECLARATIVE MACROS
    ============================================================================ *)

(** Unified macro kind *)
noeq type any_macro =
  | AMDeclarative : macro_def -> any_macro
  | AMProcedural  : proc_macro_def -> any_macro

(** Unified registry *)
type unified_registry = list (string & any_macro)

(** Lookup in unified registry *)
val lookup_any_macro : name:string -> reg:unified_registry -> option any_macro

(** Convert declarative macro result to token stream *)
val syntax_to_token_stream : s:syntax -> option token_stream

(** Convert token stream to syntax for declarative macros *)
val token_stream_to_syntax : ts:token_stream -> option syntax


(** ============================================================================
    BRRR-MACHINE INTERFACE
    ============================================================================

    Query API for static analysis integration.
    ============================================================================ *)

(** Query: get all expansions in a file *)
val get_file_expansions : filename:string -> trace:expansion_trace ->
  list expansion_record

(** Query: check if span is within macro expansion *)
val span_in_expansion : sp:token_span -> trace:expansion_trace -> bool

(** Query: get expansion depth (how nested) *)
val expansion_depth : exp:expansion_record -> trace:expansion_trace -> nat

(** Query: get all macros used in code *)
val get_used_macros : trace:expansion_trace -> list string

(** Security: check if any dangerous macros were used *)
val has_dangerous_expansions : trace:expansion_trace -> reg:pm_registry -> bool
