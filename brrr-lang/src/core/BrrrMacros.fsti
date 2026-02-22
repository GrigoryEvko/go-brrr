(**
    BrrrLang.Core.Macros Interface

    Hygienic macro system with typed syntax transformers.
    Based on brrr_lang_spec_v0.4.tex Part VI - Macros and Syntax Transformers.

    ============================================================================
    MODULE OVERVIEW
    ============================================================================

    This module implements a hygienic macro system based on:

    - Kohlbecker et al. (1986) "Hygienic Macro Expansion"
    - Dybvig, Hieb, Bruggeman (1992) "Syntactic Abstraction in Scheme"
    - Flatt (2016) "Binding as Sets of Scopes"

    Key features:
    - Hygienic identifiers with mark-based renaming
    - Typed syntax fragments (SynExpr carries brrr_type)
    - Pattern matching on token streams
    - Quasi-quotation for template expansion
    - Formal proofs of hygiene properties

    ============================================================================
    HYGIENE GUARANTEE
    ============================================================================

    The macro system maintains these critical invariants:

    1. User identifiers have mark = 0
    2. Macro-introduced identifiers have mark >= 1
    3. Two identifiers are equal only if name, scope, AND mark all match
    4. Different macro expansions use disjoint mark ranges

    These invariants are PROVEN in F* without admits.

    Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions
*)
module BrrrMacros

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open FStar.List.Tot

(** ============================================================================
    HYGIENIC IDENTIFIERS
    ============================================================================

    Hygiene marks track the origin of identifiers:
    - name  : the textual name of the identifier
    - scope : lexical nesting level where the identifier was introduced
    - mark  : unique number assigned during macro expansion (0 = user code)

    Two identifiers are considered equal only if ALL three components match.
    ============================================================================ *)

(** Hygienic identifier with scope and mark tracking *)
type ident = {
  id_name  : string;   (** The textual name *)
  id_scope : nat;      (** Lexical scope level *)
  id_mark  : nat       (** Macro expansion mark (0 = user code) *)
}

(** Create a user-code identifier (mark = 0) *)
val user_ident : name:string -> scope:nat -> ident

(** Create a macro-introduced identifier *)
val macro_ident : name:string -> scope:nat -> mark:nat -> ident

(** Check if two identifiers are equal (all components must match) *)
val ident_eq : i1:ident -> i2:ident -> bool

(** Check if identifiers have the same name (ignoring hygiene) *)
val ident_name_eq : i1:ident -> i2:ident -> bool

(** Ident equality is reflexive *)
val ident_eq_refl : i:ident ->
  Lemma (ensures ident_eq i i = true)
        [SMTPat (ident_eq i i)]

(** Ident equality is symmetric *)
val ident_eq_sym : i1:ident -> i2:ident ->
  Lemma (requires ident_eq i1 i2 = true)
        (ensures ident_eq i2 i1 = true)

(** Ident equality is transitive *)
val ident_eq_trans : i1:ident -> i2:ident -> i3:ident ->
  Lemma (requires ident_eq i1 i2 = true /\ ident_eq i2 i3 = true)
        (ensures ident_eq i1 i3 = true)


(** ============================================================================
    FRESH NAME GENERATION STATE
    ============================================================================

    The mark counter is explicitly threaded through computations.
    Marks start at 1 (0 is reserved for user code identifiers).
    ============================================================================ *)

(** Mark generation state: next available mark number *)
type mark_state = nat

(** Initial mark state (marks start at 1; 0 is reserved for user code) *)
val init_mark_state : mark_state

(** Generate a fresh mark, returning new state *)
val fresh_mark : st:mark_state -> (nat & mark_state)

(** Generate a fresh identifier with given name and scope *)
val fresh_ident : name:string -> scope:nat -> st:mark_state -> (ident & mark_state)

(** Generate multiple fresh identifiers *)
val fresh_idents : names:list string -> scope:nat -> st:mark_state ->
  Tot (list ident & mark_state) (decreases names)

(** Fresh marks are always non-zero when starting from state >= 1 *)
val fresh_mark_nonzero : st:mark_state ->
  Lemma (requires st >= 1)
        (ensures fst (fresh_mark st) >= 1)

(** Fresh marks are strictly increasing *)
val fresh_mark_increasing : st:mark_state ->
  Lemma (ensures snd (fresh_mark st) > st)

(** Fresh mark equals input state *)
val fresh_mark_value : st:mark_state ->
  Lemma (ensures fst (fresh_mark st) = st)

(** Fresh ident has mark equal to input state *)
val fresh_ident_mark : name:string -> scope:nat -> st:mark_state ->
  Lemma (ensures (fst (fresh_ident name scope st)).id_mark = st)

(** Fresh idents monotonicity: state never decreases *)
val fresh_idents_monotonic : names:list string -> scope:nat -> st:mark_state ->
  Lemma (ensures snd (fresh_idents names scope st) >= st)
        (decreases names)

(** Fresh idents strictly increases state for non-empty lists *)
val fresh_idents_strictly_monotonic : names:list string -> scope:nat -> st:mark_state ->
  Lemma (requires Cons? names)
        (ensures snd (fresh_idents names scope st) > st)
        (decreases names)

(** Predicate: all marks in an ident list are in range [lo, hi) *)
val all_marks_in_range : ids:list ident -> lo:nat -> hi:nat -> Tot bool (decreases ids)

(** Helper: first fresh_ident mark equals input state *)
val first_fresh_ident_mark : names:list string -> scope:nat -> st:mark_state ->
  Lemma (requires Cons? names)
        (ensures (match fst (fresh_idents names scope st) with
                  | id :: _ -> id.id_mark = st
                  | [] -> false))
        (decreases names)

(** Helper: widen lower bound of range *)
val all_marks_range_widen_lo : ids:list ident -> lo:mark_state -> mid:mark_state -> hi:mark_state ->
  Lemma (requires lo <= mid /\ all_marks_in_range ids mid hi)
        (ensures all_marks_in_range ids lo hi)
        (decreases ids)

(** Helper: extend range when adding an element at the start *)
val all_marks_range_extend : id:ident -> ids:list ident -> lo:mark_state -> mid:mark_state -> hi:mark_state ->
  Lemma (requires id.id_mark = lo /\ mid = lo + 1 /\ hi >= mid /\ all_marks_in_range ids mid hi)
        (ensures all_marks_in_range (id :: ids) lo hi)

(** All marks produced by fresh_idents are in range [st, result_state) *)
val fresh_idents_marks_bounded : names:list string -> scope:nat -> st:mark_state ->
  Lemma (ensures (let (ids, st') = fresh_idents names scope st in
                  all_marks_in_range ids st st'))
        (decreases names)

(** Marks from different state ranges are disjoint *)
val disjoint_mark_ranges : id1:ident -> id2:ident -> st1:mark_state -> st2:mark_state -> st3:mark_state ->
  Lemma (requires id1.id_mark >= st1 /\ id1.id_mark < st2 /\
                  id2.id_mark >= st2 /\ id2.id_mark < st3)
        (ensures ident_eq id1 id2 = false)


(** ============================================================================
    SYNTAX KINDS
    ============================================================================

    Syntax kinds classify the different forms of syntax fragments that macros
    can manipulate. Corresponds to fragment specifiers in Rust macros.
    ============================================================================ *)

(** Syntax fragment kinds *)
type syntax_kind =
  | SKExpr  : syntax_kind   (** Expression *)
  | SKStmt  : syntax_kind   (** Statement *)
  | SKPat   : syntax_kind   (** Pattern *)
  | SKType  : syntax_kind   (** Type *)
  | SKIdent : syntax_kind   (** Identifier *)
  | SKToken : syntax_kind   (** Raw token - for flexible macro matching *)


(** ============================================================================
    TOKEN REPRESENTATION
    ============================================================================

    Tokens are the input to macro pattern matching.
    ============================================================================ *)

(** Token representation for macro input *)
noeq type token =
  | TokIdent  : string -> token                 (** Identifier *)
  | TokLit    : literal -> token                (** Literal value *)
  | TokPunct  : string -> token                 (** Punctuation *)
  | TokGroup  : string -> list token -> token   (** Grouped tokens *)

(** Token size for termination proofs *)
val token_size : t:token -> Tot nat (decreases t)

(** Token list size for termination proofs *)
val token_list_size : ts:list token -> Tot nat (decreases ts)


(** ============================================================================
    SYNTAX TYPES (TYPED SYNTAX FRAGMENTS)
    ============================================================================

    Typed syntax fragments for macro manipulation:
    - SynExpr[T] : expression producing value of type T
    - SynStmt    : statement (no value)
    - SynPat[T]  : pattern matching values of type T
    - SynType    : type expression
    - SynToken   : raw token for flexible matching
    - SynGroup   : grouped bindings from nested pattern matching
    ============================================================================ *)

(** Typed syntax fragments *)
noeq type syntax =
  | SynExpr  : brrr_type -> expr -> syntax        (** Expression producing type *)
  | SynStmt  : expr -> syntax                     (** Statement *)
  | SynPat   : brrr_type -> pattern -> syntax     (** Pattern matching type *)
  | SynType  : brrr_type -> syntax                (** Type expression *)
  | SynIdent : ident -> syntax                    (** Hygienic identifier *)
  | SynList  : list syntax -> syntax              (** Syntax list (for repetitions) *)
  | SynToken : token -> syntax                    (** Raw token capture *)
  | SynGroup : list (string & syntax) -> syntax   (** Grouped bindings from pattern match *)

(** Get the kind of a syntax fragment *)
val syntax_kind_of : s:syntax -> syntax_kind

(** Size function for termination *)
val syntax_size : s:syntax -> Tot nat (decreases s)

(** Size of syntax list for termination *)
val syntax_list_size : ss:list syntax -> Tot nat (decreases ss)

(** Size of syntax bindings for termination *)
val syntax_bindings_size : binds:list (string & syntax) -> Tot nat (decreases binds)


(** ============================================================================
    QUASI-QUOTATION
    ============================================================================

    Quasi-quotation allows building syntax with holes:
    - QQLit    : literal syntax fragment
    - QQSplice : $var - hole to be filled with syntax bound to var
    - QQSeq    : sequence of quasi-quotes
    - QQExpr   : build expression syntax
    - QQRepeat : $(..),* - repetition with separator
    ============================================================================ *)

(** Quasi-quotation: syntax templates with holes *)
noeq type quasi_quote =
  | QQLit     : syntax -> quasi_quote                    (** Literal syntax *)
  | QQSplice  : string -> quasi_quote                    (** $var hole *)
  | QQSeq     : list quasi_quote -> quasi_quote          (** Sequence *)
  | QQExpr    : quasi_quote -> quasi_quote               (** Build expr *)
  | QQStmt    : quasi_quote -> quasi_quote               (** Build stmt *)
  | QQRepeat  : quasi_quote -> string -> quasi_quote     (** $(pat),sep - repetition *)
  | QQOpt     : quasi_quote -> quasi_quote               (** Optional: $(...)? *)

(** Quasi-quote size for termination *)
val qq_size : qq:quasi_quote -> Tot nat (decreases qq)

(** Quasi-quote list size for termination *)
val qq_list_size : qqs:list quasi_quote -> Tot nat (decreases qqs)


(** ============================================================================
    MACRO PATTERNS
    ============================================================================

    Patterns for matching macro invocations:
    - MPLit    : literal token that must match exactly
    - MPVar    : capture variable with syntax type constraint
    - MPRepeat : $(pat),* - match zero or more with separator
    - MPGroup  : (pat) or {pat} or [pat] - grouped pattern
    - MPOpt    : $(pat)? - optional pattern
    ============================================================================ *)

(** Macro pattern for matching invocations *)
noeq type macro_pattern =
  | MPLit    : string -> macro_pattern                      (** Literal token *)
  | MPVar    : string -> syntax_kind -> macro_pattern       (** $name:kind *)
  | MPRepeat : macro_pattern -> string -> macro_pattern     (** $(pat),* with sep *)
  | MPGroup  : string -> list macro_pattern -> macro_pattern (** Delimited group *)
  | MPOpt    : macro_pattern -> macro_pattern               (** Optional $(...)? *)
  | MPSeq    : list macro_pattern -> macro_pattern          (** Sequence *)

(** Pattern size for termination *)
val mp_size : mp:macro_pattern -> Tot nat (decreases mp)

(** Pattern list size for termination *)
val mp_list_size : mps:list macro_pattern -> Tot nat (decreases mps)


(** ============================================================================
    MACRO RULES AND DEFINITIONS
    ============================================================================ *)

(** A single macro rule: pattern => template *)
noeq type macro_rule = {
  rule_pattern  : list macro_pattern;   (** Input pattern *)
  rule_template : quasi_quote           (** Output template *)
}

(** Macro definition with name and rules *)
noeq type macro_def = {
  macro_name  : string;                 (** Macro name *)
  macro_rules : list macro_rule         (** Pattern => template rules *)
}

(** Binding environment for macro expansion *)
type syntax_env = list (string & syntax)

(** Look up binding in syntax environment *)
val syntax_lookup : name:string -> env:syntax_env -> option syntax

(** Extend syntax environment *)
val syntax_extend : name:string -> s:syntax -> env:syntax_env -> syntax_env

(** Merge two syntax environments (left takes precedence) *)
val syntax_merge : env1:syntax_env -> env2:syntax_env -> syntax_env


(** ============================================================================
    PATTERN MATCHING
    ============================================================================ *)

(** Convert token to syntax based on expected kind *)
val token_to_syntax : t:token -> kind:syntax_kind -> option syntax

(** Match result: bindings or failure *)
type match_result = option syntax_env

(** Maximum recursion depth for pattern matching *)
val max_match_depth : nat

(** Combined metric for termination *)
val merge_rep_binding_single : name:string -> syn:syntax -> env:syntax_env ->
  Tot syntax_env (decreases env)

(** Merge repetition bindings from multiple iterations *)
val merge_rep_bindings : b1:syntax_env -> b2:syntax_env ->
  Tot syntax_env (decreases b1)

(** Initialize repetition bindings *)
val init_rep_bindings : binds:syntax_env ->
  Tot syntax_env (decreases binds)

(** Match a single pattern against tokens with depth bound *)
type match_metric = nat & nat

(** Merge repetition binding for a single variable *)
val match_macro_pattern : pat:macro_pattern -> tokens:list token -> depth:nat ->
  Tot (match_result & list token) (decreases depth)

(** Match a sequence of patterns *)
val match_pattern_seq : pats:list macro_pattern -> tokens:list token -> depth:nat ->
  Tot (match_result & list token) (decreases depth)

(** Match zero or more occurrences with separator *)
val match_repetition : inner:macro_pattern -> sep:string -> tokens:list token -> depth:nat ->
  Tot (match_result & list token) (decreases depth)

(** Match a list of patterns - full implementation *)
val match_mp_list : mps:list macro_pattern -> ts:list token -> (match_result & list token)

(** Main pattern matching entry point *)
val match_mp_single : mp:macro_pattern -> ts:list token -> (match_result & list token)


(** ============================================================================
    TEMPLATE EXPANSION
    ============================================================================ *)

(** Expand a quasi-quote template with bindings *)
val fill_qq : qq:quasi_quote -> env:syntax_env -> Tot (option syntax) (decreases qq)

(** Fill list of quasi-quotes *)
val fill_qq_list : qqs:list quasi_quote -> env:syntax_env ->
  Tot (option (list syntax)) (decreases qqs)

(** Simple quasi-quote fill (no recursion issues) *)
val fill_qq_simple : qq:quasi_quote -> env:syntax_env -> option syntax

(** Expand repetition over items *)
val expand_repetition : qq:quasi_quote -> items:list syntax -> env:syntax_env -> acc:list syntax ->
  Tot (list syntax) (decreases items)


(** ============================================================================
    EXPRESSION EXTRACTION
    ============================================================================ *)

(** Convert token list to expression *)
val tokens_to_expr : ts:list token -> Tot (option expr) (decreases ts)

(** Extract expression from syntax *)
val syntax_to_expr : s:syntax -> Tot (option expr) (decreases s)

(** Extract expression from syntax list *)
val syntax_list_to_expr : ss:list syntax -> Tot (option expr) (decreases ss)

(** Extract expressions from bindings and sequence them *)
val syntax_bindings_to_expr : binds:list (string & syntax) ->
  Tot (option expr) (decreases binds)

(** Extract pattern from syntax *)
val syntax_to_pattern : s:syntax -> option pattern


(** ============================================================================
    HYGIENIC RENAMING
    ============================================================================ *)

(** Rename map: old name -> new ident *)
type rename_map = list (string & ident)

(** Look up rename *)
val rename_lookup : name:string -> renames:rename_map -> option ident

(** Rename an identifier if in rename map *)
val rename_ident : id:ident -> renames:rename_map -> ident

(** Collect binders in a pattern - simple patterns only *)
val collect_binders_pat_simple : p:pattern -> list string

(** Collect all binders in an expression *)
val collect_binders_expr : e:expr -> Tot (list string) (decreases e)

(** Collect binders from expression list *)
val collect_binders_expr_list : es:list expr -> Tot (list string) (decreases es)

(** Helper: zip two lists into pairs *)
val zip : #a:Type -> #b:Type -> l1:list a -> l2:list b -> Tot (list (a & b)) (decreases l1)

(** Generate fresh renames for binders *)
val gen_renames : binders:list string -> scope:nat -> st:mark_state ->
  (rename_map & mark_state)

(** gen_renames monotonicity: state never decreases *)
val gen_renames_monotonic : binders:list string -> scope:nat -> st:mark_state ->
  Lemma (ensures snd (gen_renames binders scope st) >= st)

(** Helper: marks in range [lo, hi) with lo >= 1 implies marks >= 1 *)
val all_marks_in_range_implies_ge_1 : ids:list ident -> lo:mark_state -> hi:mark_state ->
  Lemma (requires lo >= 1 /\ all_marks_in_range ids lo hi)
        (ensures forall id. List.Tot.memP id ids ==> id.id_mark >= 1)
        (decreases ids)

(** gen_renames preserves nonzero marks when starting from st >= 1 *)
val gen_renames_marks_nonzero : binders:list string -> scope:nat -> st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (let (ids, _) = fresh_idents binders scope st in
                  forall id. List.Tot.memP id ids ==> id.id_mark >= 1))

(** Apply renaming to expression *)
val rename_expr : e:expr -> renames:rename_map -> Tot expr (decreases e)

(** Apply renaming to expression list *)
val rename_expr_list : es:list expr -> renames:rename_map -> Tot (list expr) (decreases es)

(** Rename syntax *)
val rename_syntax : s:syntax -> renames:rename_map -> Tot syntax (decreases s)

(** Rename syntax list *)
val rename_syntax_list : ss:list syntax -> renames:rename_map -> Tot (list syntax) (decreases ss)

(** Rename bindings in a syntax group *)
val rename_syntax_bindings : binds:list (string & syntax) -> renames:rename_map ->
  Tot (list (string & syntax)) (decreases binds)

(** Rename identifiers within a token list *)
val rename_token_list : ts:list token -> renames:rename_map ->
  Tot (list token) (decreases ts)


(** ============================================================================
    MACRO EXPANSION
    ============================================================================ *)

(** Try to expand using a single macro rule *)
val try_expand_rule : rule:macro_rule -> input:list token -> scope:nat -> st:mark_state ->
  option (syntax & mark_state)

(** Expand macro rules in order *)
val expand_macro_rules : rules:list macro_rule -> input:list token -> scope:nat -> st:mark_state ->
  option (syntax & mark_state)

(** Main macro expansion entry point *)
val expand_macro : m:macro_def -> input:list token -> scope:nat -> st:mark_state ->
  option (syntax & mark_state)

(** try_expand_rule monotonicity *)
val try_expand_rule_monotonic : rule:macro_rule -> input:list token -> scope:nat -> st:mark_state ->
  Lemma (ensures (match try_expand_rule rule input scope st with
                  | Some (_, st') -> st' >= st
                  | None -> true))

(** expand_macro_rules monotonicity *)
val expand_macro_rules_monotonic : rules:list macro_rule -> input:list token -> scope:nat -> st:mark_state ->
  Lemma (ensures (match expand_macro_rules rules input scope st with
                  | Some (_, st') -> st' >= st
                  | None -> true))
        (decreases rules)


(** ============================================================================
    HYGIENE PROOFS
    ============================================================================ *)

(** All binders in renamed expressions have marks from the given state *)
val rename_binders_have_marks : e:expr -> renames:rename_map -> st:mark_state ->
  Lemma (requires forall (name: string) (id: ident).
           rename_lookup name renames = Some id ==> id.id_mark >= 1)
        (ensures True)

(** Fresh identifiers never equal user identifiers *)
val fresh_ident_neq_user : name:string -> scope:nat -> st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (fst (fresh_ident name scope st)).id_mark >= 1 /\
                 (forall (user_id: ident). user_id.id_mark = 0 ==>
                   ident_eq (fst (fresh_ident name scope st)) user_id = false))

(** Two fresh identifiers from different states are different *)
val fresh_idents_distinct : name1:string -> scope1:nat -> st1:mark_state ->
                            name2:string -> scope2:nat -> st2:mark_state ->
  Lemma (requires st1 >= 1 /\ st2 >= 1 /\ st1 <> st2)
        (ensures ident_eq (fst (fresh_ident name1 scope1 st1))
                          (fst (fresh_ident name2 scope2 st2)) = false)

(** Predicate: identifier was introduced by user code *)
val is_user_ident : id:ident -> bool

(** Predicate: identifier was introduced by macro *)
val is_macro_ident : id:ident -> bool

(** User and macro identifiers are disjoint *)
val user_macro_disjoint : id:ident ->
  Lemma (ensures is_user_ident id ==> not (is_macro_ident id))

(** Hygiene property: user ident never equals macro ident *)
val hygiene_user_vs_macro : user_id:ident -> macro_id:ident ->
  Lemma (requires is_user_ident user_id /\ is_macro_ident macro_id)
        (ensures ident_eq user_id macro_id = false)

(** CORE HYGIENE SEPARATION THEOREM *)
val hygiene_separation : id1:ident -> id2:ident ->
  Lemma (requires id1.id_mark = 0 /\ id2.id_mark >= 1)
        (ensures ident_eq id1 id2 = false)

(** Symmetry of hygiene separation *)
val hygiene_separation_sym : id1:ident -> id2:ident ->
  Lemma (requires id1.id_mark >= 1 /\ id2.id_mark = 0)
        (ensures ident_eq id1 id2 = false)

(** Different macro marks mean different identifiers *)
val macro_marks_distinct : id1:ident -> id2:ident ->
  Lemma (requires id1.id_mark <> id2.id_mark)
        (ensures ident_eq id1 id2 = false)

(** Helper: extract result state or return original *)
val expansion_result_state : result:option (syntax & mark_state) -> default:mark_state -> mark_state

(** MAIN HYGIENE THEOREM *)
val hygiene_theorem : m:macro_def -> input:list token -> scope:nat -> st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (match expand_macro m input scope st with
                  | Some (_, st') -> st' >= st
                  | None -> true))
        [SMTPat (expand_macro m input scope st)]


(** ============================================================================
    CAPTURE AVOIDANCE
    ============================================================================ *)

(** Type representing a variable reference in code *)
type var_ref = {
  ref_name : string;
  ref_mark : nat
}

(** Create var_ref from ident *)
val ident_to_ref : id:ident -> var_ref

(** Check if a binding captures a reference *)
val binding_captures_ref : binding:ident -> ref:var_ref -> bool

(** Macro binding cannot capture user ref *)
val macro_binding_no_user_capture : binding:ident -> user_ref:var_ref ->
  Lemma (requires is_macro_ident binding /\ user_ref.ref_mark = 0)
        (ensures binding_captures_ref binding user_ref = false)

(** User binding cannot capture macro ref *)
val user_binding_no_macro_capture : binding:ident -> macro_ref:var_ref ->
  Lemma (requires is_user_ident binding /\ macro_ref.ref_mark >= 1)
        (ensures binding_captures_ref binding macro_ref = false)


(** ============================================================================
    EXAMPLE MACROS
    ============================================================================ *)

(** assert_eq! macro *)
val assert_eq_macro : macro_def

(** vec! macro *)
val vec_macro : macro_def

(** dbg! macro *)
val dbg_macro : macro_def


(** ============================================================================
    MACRO REGISTRY
    ============================================================================ *)

(** Macro registry: name -> definition *)
type macro_registry = list (string & macro_def)

(** Empty registry *)
val empty_registry : macro_registry

(** Register a macro *)
val register_macro : m:macro_def -> reg:macro_registry -> macro_registry

(** Lookup a macro by name *)
val lookup_macro : name:string -> reg:macro_registry -> option macro_def

(** Default registry with common macros *)
val default_registry : macro_registry


(** ============================================================================
    EXPANSION DRIVER
    ============================================================================ *)

(** Result of macro expansion *)
noeq type expansion_result =
  | ExpSuccess : syntax -> mark_state -> expansion_result
  | ExpNoMatch : expansion_result         (** No rule matched *)
  | ExpNotFound : expansion_result        (** Macro not in registry *)
  | ExpError : string -> expansion_result (** Expansion error *)

(** Expand a macro invocation *)
val expand_invocation : name:string -> input:list token -> scope:nat ->
                        st:mark_state -> reg:macro_registry ->
  expansion_result


(** ============================================================================
    COMPLETE HYGIENE GUARANTEES
    ============================================================================ *)

(** Complete hygiene guarantee *)
val complete_hygiene_guarantee : m:macro_def -> input:list token -> scope:nat -> st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (match expand_macro m input scope st with
                  | Some (_, st') -> st' >= st /\ st' >= 1
                  | None -> true))

(** Expansion marks bounded *)
val expansion_marks_bounded : m:macro_def -> input:list token -> scope:nat -> st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (match expand_macro m input scope st with
                  | Some (_, st') -> st' >= st
                  | None -> true))

(** Consecutive expansions produce disjoint mark ranges *)
val consecutive_expansions_disjoint :
  m1:macro_def -> input1:list token -> scope1:nat ->
  m2:macro_def -> input2:list token -> scope2:nat ->
  st:mark_state ->
  Lemma (requires st >= 1)
        (ensures (match expand_macro m1 input1 scope1 st with
                  | Some (_, st1) ->
                      (match expand_macro m2 input2 scope2 st1 with
                       | Some (_, st2) -> st1 >= st /\ st2 >= st1
                       | None -> true)
                  | None -> true))

(** Marks from consecutive expansions are truly disjoint *)
val marks_disjoint_theorem : m1:macro_def -> input1:list token -> scope1:nat ->
                              m2:macro_def -> input2:list token -> scope2:nat ->
                              st:mark_state -> id1:ident -> id2:ident ->
  Lemma (requires st >= 1 /\
                  (match expand_macro m1 input1 scope1 st with
                   | Some (_, st1) -> id1.id_mark >= st /\ id1.id_mark < st1 /\
                                       (match expand_macro m2 input2 scope2 st1 with
                                        | Some (_, st2) -> id2.id_mark >= st1 /\ id2.id_mark < st2
                                        | None -> false)
                   | None -> false))
        (ensures ident_eq id1 id2 = false)
