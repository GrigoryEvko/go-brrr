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
module BrrrExpressions

(** Z3 solver options - conservative settings for expression proofs.
    Following HACL* pattern of --fuel 0 --ifuel 0 as baseline. *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
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

    DESIGN PATTERN: Following EverParse's with_meta_t (Ast.fst lines 107-111)
    =========================================================================
    EverParse defines:

      noeq type with_meta_t 'a = {
        v: 'a;              (* The underlying value *)
        range: range;       (* Source span *)
        comments: comments  (* Attached documentation *)
      }

    Our with_loc is a simplified version without comments:

      noeq type with_loc 'a = {
        loc_value: 'a;      (* The underlying value *)
        loc_range: range    (* Source span: (start_pos, end_pos) *)
      }

    WHY noeq?
    ---------
    The noeq attribute is needed because:
    1. Polymorphic type 'a may not have decidable equality
    2. We want custom equality (comparing loc_value, ignoring loc_range)
    3. expr' and pattern' (the main uses) have custom equality functions

    USAGE PATTERNS:
    ---------------
    Creating: locate value range, locate_dummy value
    Accessing: w.loc_value, w.loc_range, or unloc w, loc_of w
    Mapping: map_loc f w (applies f to value, preserves location)

    For pattern matching on located expressions/patterns:
      match e.loc_value with   (* Access the inner expr'/pattern' *)
      | EVar x -> ...

    REFERENCE IMPLEMENTATIONS:
    --------------------------
    - EverParse Ast.fst: with_meta_t, with_range, with_range_and_comments
    - EverParse Binding.fst: Uses with_meta_t for error reporting
    - HACL* Lib.Buffer.fsti: Similar pattern for annotated buffers *)
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

(** Check if a position equals another.
    Unfold allows Z3 to see the structure for automatic proofs. *)
[@(strict_on_arguments [0;1])]
unfold
let pos_eq (p1 p2: pos) : bool =
  p1.pos_filename = p2.pos_filename &&
  p1.pos_line = p2.pos_line &&
  p1.pos_col = p2.pos_col

(** Check if two ranges are equal.
    Unfold allows Z3 to see the structure for automatic proofs. *)
[@(strict_on_arguments [0;1])]
unfold
let range_eq (r1 r2: range) : bool =
  let (s1, e1) = r1 in
  let (s2, e2) = r2 in
  pos_eq s1 s2 && pos_eq e1 e2

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
  | LitImaginary : float_repr -> float_prec -> literal
      (** Imaginary literal: 3i, 1.5i, 0i
          Go spec (Imaginary literals):
            An imaginary literal represents the imaginary part of a complex constant.
            It consists of an integer or floating-point literal followed by the
            lower-case letter i.
          Runtime value: VTuple [VFloat 0 prec; VFloat f prec]
          (a complex number with zero real part and f as imaginary part) *)

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
  | OpBitAndNot : binary_op  (** &^ - bit clear (AND NOT): a &^ b = a & (~b) *)
  | OpShl    : binary_op
  | OpShr    : binary_op

(** Go operator precedence levels (5 = highest, 1 = lowest).

    Go spec (Operator precedence):
      "Unary operators have the highest precedence."
      "There are five precedence levels for binary operators.
       Multiplication operators bind strongest, followed by addition
       operators, comparison operators, && (logical AND), and finally
       || (logical OR)."

    Precedence 5: *  /  %  <<  >>  &  &^
    Precedence 4: +  -  |  ^
    Precedence 3: ==  !=  <  <=  >  >=
    Precedence 2: &&
    Precedence 1: ||

    Returns 0 for operators not in Go's precedence table. *)
[@(strict_on_arguments [0])]
unfold
let go_op_precedence (op: binary_op) : nat =
  match op with
  | OpMul | OpDiv | OpMod | OpShl | OpShr | OpBitAnd | OpBitAndNot -> 5
  | OpAdd | OpSub | OpBitOr | OpBitXor -> 4
  | OpEq | OpNe | OpLt | OpLe | OpGt | OpGe -> 3
  | OpAnd -> 2
  | OpOr -> 1

(** ============================================================================
    GRADUAL TYPING: BLAME LABELS AND CAST KINDS
    ============================================================================

    Cast insertion is the core mechanism for gradual typing safety.
    When types are not statically compatible but are consistent (via Dynamic/Unknown),
    casts are inserted to perform runtime checks.

    Based on: Siek & Taha 2006 "Gradual Typing for Functional Languages"
    See also: Wadler & Findler 2009 "Well-Typed Programs Can't Be Blamed"

    BLAME TRACKING:
    ---------------
    Blame labels identify the source of a cast failure for error reporting.
    When a cast fails at runtime, the blame label indicates:
    - Where the cast was inserted (source location)
    - Which party is "at fault" (positive = source, negative = target)
    - Context for meaningful error messages

    CAST KINDS:
    -----------
    - CKUp: Upcast to supertype (always safe, can be erased)
    - CKDown: Downcast to subtype (may fail at runtime)
    - CKDynamic: Cast involving Dynamic type (runtime type check)

    ============================================================================ *)

(** Blame label for tracking cast failure responsibility *)
noeq type blame_label = {
  bl_positive : bool;     (** True = cast source at fault, False = cast target at fault *)
  bl_location : range;    (** Source location where cast was inserted *)
  bl_context  : string;   (** Human-readable context for error message *)
}

(** Cast kind - determines runtime behavior *)
type cast_kind =
  | CKUp      : cast_kind   (** Upcast to supertype - always safe, zero cost *)
  | CKDown    : cast_kind   (** Downcast to subtype - runtime check, may fail *)
  | CKDynamic : cast_kind   (** Cast through Dynamic - runtime type tag check *)

(** Cast expression metadata *)
noeq type cast_info = {
  ci_from  : brrr_type;   (** Source type being cast from *)
  ci_to    : brrr_type;   (** Target type being cast to *)
  ci_kind  : cast_kind;   (** Kind of cast (determines runtime behavior) *)
  ci_blame : blame_label; (** Blame label for error reporting *)
}

(** Flip blame polarity - used for contravariant positions (function arguments).
    When casting a function (T1 -> T2) to (T3 -> T4), the argument cast
    has flipped blame because the caller provides the argument. *)
val flip_blame : blame_label -> blame_label

(** Create a blame label at a source location *)
val mk_blame : bool -> range -> string -> blame_label

(** ============================================================================
    PATTERNS AND EXPRESSIONS (mutually recursive with source location)
    ============================================================================

    DESIGN PATTERN: Separation of Structure and Metadata
    =====================================================
    Following EverParse Ast.fst with_meta_t pattern (lines 107-111):

      noeq type with_meta_t 'a = {
        v: 'a;            (* The actual value *)
        range: range;      (* Source location *)
        comments: comments (* Attached comments *)
      }

    We use a similar pattern:
      - pattern' : The underlying pattern ADT (no location)
      - pattern  : with_loc pattern' = { loc_value: pattern'; loc_range: range }
      - expr'    : The underlying expression ADT (no location)
      - expr     : with_loc expr' = { loc_value: expr'; loc_range: range }

    This separation provides:
    1. STRUCTURAL EQUALITY: Compare expr'/pattern' without location noise
    2. TRAVERSAL SIMPLICITY: Size functions work on inner types
    3. METADATA FLEXIBILITY: Source locations, types, effects can be attached
    4. PATTERN MATCHING: Use e.loc_value to access the underlying structure

    Reference: brrr_lang_spec_v0.4.tex Part V (Expression AST)
    See also: SPECIFICATION_ERRATA.md Chapter 7 (Pattern Type Mismatch)

    IMPORTANT: When pattern matching on expr or pattern, you MUST access
    .loc_value first to get the underlying structure:

      match e.loc_value with        (* CORRECT *)
      | EVar x -> ...

      match e with                  (* WRONG - e is with_loc expr', not expr' *)
      | EVar x -> ...

    ============================================================================ *)

(** Pattern underlying type.

    The pattern' type represents the STRUCTURE of a pattern without source
    location information. This is the "semantic" content of the pattern.

    Wrapped in with_loc to create the pattern type with location tracking.

    Following EverParse's expr/expr' separation pattern from Ast.fst.

    EVERPARSE COMPARISON (Ast.fst lines 309-390):
    ---------------------------------------------
    EverParse defines:
      and expr = with_meta_t expr'  (* Located expression *)
      and expr' = ...               (* Underlying structure *)

    We follow the same pattern:
      and pattern = with_loc pattern'  (* Located pattern *)
      and pattern' = ...               (* Underlying structure *)

    DEEP EMBEDDING (fstar_pop_book.md Part 2, lines 4939-4962):
    ----------------------------------------------------------
    pattern' is a deep embedding of Brrr-Lang pattern syntax as an F*
    inductive type. Each constructor corresponds to a syntactic form
    from brrr_lang_spec_v0.4.tex (lines 3526-3536).

    The noeq qualifier is required because pattern' contains:
    - Nested patterns (PatTuple, PatOr, etc.) via the pattern type
    - Expressions (PatGuard) which may contain functions *)
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
  | PatType    : brrr_type -> option var_id -> pattern'  (* Type pattern: matches if runtime type is T, optionally binds with narrowed type *)

(** Expression underlying type.

    The expr' type represents the STRUCTURE of an expression without source
    location information. This is the "semantic" content of the expression.

    Wrapped in with_loc to create the expr type with location tracking:
      expr = with_loc expr' = { loc_value: expr'; loc_range: range }

    DESIGN RATIONALE (from fstar_pop_book.md, Part 2 - Inductive Types):
    -------------------------------------------------------------------
    This is a deep embedding of Brrr-Lang expressions as an F* inductive type.
    Each constructor represents a syntactic form from brrr_lang_spec_v0.4.tex.

    The noeq attribute is used because:
    - expr' contains functions (ELambda, EClosure bodies conceptually)
    - expr' is recursive (children are expr, not expr')
    - We define custom structural equality (expr_eq) instead

    HIGHER-ORDER ABSTRACT SYNTAX (HOAS) NOTE:
    -----------------------------------------
    Unlike pure HOAS (see fstar_pop_book.md Part 2, section on PHOAS), we use
    named variables (var_id = string) rather than F* functions to represent
    binding. This is a FIRST-ORDER representation that requires:
    - Explicit free variable computation (free_vars)
    - Capture-avoiding substitution (subst_expr)
    - Alpha equivalence via normalization (expr_alpha_eq)

    The named variable approach is chosen for:
    1. Easier serialization/deserialization
    2. Better error messages with original names
    3. Compatibility with the source language syntax

    EVERPARSE COMPARISON (Ast.fst lines 285-390):
    ---------------------------------------------
    EverParse's expr' type includes:
    - Constant, Identifier, App, This for basic expressions
    - Record, Static_method_call, etc. for more complex forms

    Our expr' is more comprehensive, including:
    - Control flow (EIf, EMatch, ELoop, EWhile, EFor, EGoto, ELabeled)
    - Memory operations (EBox, EDeref, EBorrow, EMove, EDrop)
    - Async/effects (EAwait, EYield, EAsync, ESpawn, EHandle, EPerform)
    - Delimited continuations (EReset, EShift, EResume)

    STRICT POSITIVITY (fstar_pop_book.md lines 5454-5499):
    -----------------------------------------------------
    expr' is strictly positive: it never appears to the left of an arrow
    in its own definition. This is crucial for logical consistency.
    All recursive occurrences go through 'expr' (= with_loc expr').

    Reference: brrr_lang_spec_v0.4.tex Part V, Expression Grammar *)
and expr' =
  | ELit      : literal -> expr'
  | EVar      : var_id -> expr'
  | EGlobal   : string -> expr'
  | EUnary    : unary_op -> expr -> expr'
  | EBinary   : binary_op -> expr -> expr -> expr'
  | ECall     : expr -> list expr -> expr'
  | EMethodCall : expr -> string -> list expr -> expr'
  (* METHOD REFERENCES: First-class method values
     --------------------------------------------
     EMethodRef and ETypeMethod create first-class function values from methods.

     EMethodRef (obj, "method"):
       - Creates a BOUND method reference with captured receiver
       - Equivalent to: (args) => obj.method(args)
       - The object is evaluated once when the reference is created
       - Type: (arg_types) -> ret_type (receiver already captured)
       - Example: let f = obj.toString;  f()  (* calls obj.toString() *)

     ETypeMethod (T, "method"):
       - Creates an UNBOUND method reference (no receiver)
       - Type: (T, arg_types) -> ret_type (receiver is first argument)
       - Example: let f = String::length;  f("hello")  (* returns 5 *)

     This design follows Rust's method reference syntax and enables:
     - Passing methods as callbacks without allocating closures
     - Method chaining transformations (map, filter, etc.)
     - Reflection-like patterns for method dispatch

     Reference: brrr_lang_spec_v0.4.tex Section on Method Calls *)
  | EMethodRef : expr -> string -> expr'               (* Bound method reference: obj.method without calling *)
  | ETypeMethod : type_name -> string -> expr'         (* Unbound type method: T::method *)
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
  (* LOW-LEVEL CONTROL FLOW: goto and labeled statements
     -------------------------------------------------
     EGoto and ELabeled provide C-style labeled jump semantics for:
     - Breaking out of deeply nested loops (beyond break/continue)
     - State machine implementations
     - Cleanup code patterns (goto cleanup;)
     - Low-level code generation targets

     EGoto (label) jumps to the ELabeled (label, body) statement.
     The label must be unique within the enclosing function.

     WARNING: These bypass structured control flow and should be used sparingly.
     Type checking ensures jumps don't cross variable binding boundaries.

     Reference: brrr_lang_spec_v0.4.tex Section on Control Flow *)
  | EGoto     : label -> expr'                          (* goto label - jump to labeled statement *)
  | ELabeled  : label -> expr -> expr'                  (* label: stmt - labeled statement target *)
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
  | ERecover  : expr'
      (** recover() - Go built-in that stops a panicking sequence.
          Go spec (Handling panics):
            "The recover built-in function allows a program to manage behavior
             of a panicking goroutine. [...] If recover is called outside the
             deferred function it does not stop a panicking sequence."
          Semantics:
            - In normal (non-panicking) context: returns nil (VNone)
            - Inside a deferred function during panic unwinding:
              returns the panic value and stops the panic
          The actual panic interception is handled by the ETry/EThrow mechanism:
            GoEDefer + GoERecover patterns are translated to ETry/catch blocks
            by BrrrLangMapping. ERecover in isolation returns VNone (not panicking). *)
  | ETry      : expr -> list catch_arm -> option expr -> expr'
  | EAwait    : expr -> expr'
  | EYield    : expr -> expr'
  (* GENERATORS: Native generator expressions
     -----------------------------------------
     Generators are resumable computations that can yield values and be resumed.
     Following Python/JavaScript generator semantics with typed yield/resume.

     EGenerator wraps a body expression that may contain EYield expressions.
     When created, the generator is in Initial state (not yet started).

     EGenNext advances the generator:
       - Initial -> Evaluate body until first yield or return
       - Yielded -> Resume from yield point
       - Done -> Returns None

     EGenSend resumes a generator with a value (the yield expression evaluates
     to the sent value).

     Reference: brrr_lang_spec_v0.4.tex lines 2936-2972 *)
  | EGenerator : expr -> expr'                          (* gen { body } - create generator *)
  | EGenNext   : expr -> expr'                          (* gen.next() - advance generator *)
  | EGenSend   : expr -> expr -> expr'                  (* gen.send(value) - resume with value *)
  | EHandle   : expr -> effect_handler -> expr'
  | EPerform  : effect_op -> list expr -> expr'
  | EAsync    : expr -> expr'
  | ESpawn    : expr -> expr'
  | EResume   : var_id -> expr -> expr'
  | EReset    : label -> expr -> expr'
  | EShift    : label -> var_id -> expr -> expr'
  (* UNDELIMITED CONTINUATIONS: control/prompt (Felleisen 1988)
     -----------------------------------------------------------
     EControl and EAbort provide undelimited continuation capture, in contrast
     to EShift which captures delimited continuations.

     KEY DIFFERENCE from shift/reset:
     - shift k: When k(v) is called, the continuation INCLUDES the reset delimiter.
       Control returns to the shift body, then proceeds to reset.
     - control k: When k(v) is called, the continuation does NOT include reset.
       Control returns DIRECTLY to the outer context, bypassing reset.

     Operational semantics (Felleisen 1988):
       reset<p> E[control<p> (k. body)]  =>  body[k := x. E[x]]
       reset<p> E[abort<p> v]            =>  v

     Note that control's k does NOT wrap E[x] in reset, unlike shift.

     EControl captures the continuation WITHOUT the delimiter:
       - k(v) returns directly to outer context
       - More primitive than shift, harder to reason about
       - Useful for implementing non-local returns, exceptions

     EAbort discards the continuation entirely:
       - Equivalent to: control<p> (k. v) where k is unused
       - Jumps directly to the enclosing reset
       - Used for: return, break, continue, throw

     Reference: Felleisen 1988 "The Theory and Practice of First-Class Prompts" *)
  | EControl  : label -> var_id -> expr -> expr'       (* control<p> (k. body) - capture undelimited *)
  | EAbort    : label -> expr -> expr'                 (* abort<p> v - discard continuation *)
  | EAs       : expr -> brrr_type -> expr'
  | EIs       : expr -> brrr_type -> expr'
  | ESizeof   : brrr_type -> expr'
  | EAlignof  : brrr_type -> expr'
  | EOffsetof : brrr_type -> string -> expr'
      (** unsafe.Offsetof(s.f): returns the byte offset of field f within the struct
          type T, relative to the struct's starting address.
          Go spec (Package unsafe):
            "The function Offsetof takes a (possibly parenthesized) selector s.f,
             denoting a field f of the struct denoted by s or *s, and returns the
             field offset in bytes relative to the struct's address."
          Invariant: uintptr(&s) + Offsetof(s.f) == uintptr(&s.f)
          The brrr_type must be a TStruct. The string is the field name.
          This is a compile-time constant expression of type uintptr. *)
  | EPtrAdd   : expr -> expr -> expr'
      (** unsafe.Add(ptr, len): pointer arithmetic returning ptr + len bytes.
          Go spec (Package unsafe):
            "The function Add adds len to ptr and returns the updated pointer
             unsafe.Pointer(uintptr(ptr) + uintptr(len))."
          The first operand must be an unsafe.Pointer (Raw pointer).
          The second operand must be an integer type.
          The result is an unsafe.Pointer.
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | EConvert  : brrr_type -> expr -> expr'             (* explicit type conversion T(x) - Go spec "Conversions":
                                                           Changes representation for string/byte/rune/numeric conversions.
                                                           string([]byte{...})  -> byte slice to string
                                                           []byte("hello")     -> string to byte slice
                                                           string([]rune{...}) -> rune slice to string
                                                           []rune("hello")     -> string to rune slice
                                                           string(65)          -> integer to single-rune string
                                                           Numeric: truncates or extends as appropriate.
                                                           Other: changes type, not representation. *)
  | ENew      : brrr_type -> expr'                     (* new(T) - allocate zero-valued T, returns *T *)
  | ELen      : expr -> expr'                          (* len(e) - length of array/slice/string/map *)
  | ECap      : expr -> expr'                          (* cap(e) - capacity of slice/vector *)
  | EMin      : list expr -> expr'                     (* min(x, y...) - smallest of ordered args (Go 1.21) *)
  | EMax      : list expr -> expr'                     (* max(x, y...) - largest of ordered args (Go 1.21) *)
  | ECopy     : expr -> expr -> expr'                  (* copy(dst, src) - copies min(len(dst),len(src)) elements, returns count *)
  | EClear    : expr -> expr'                          (* clear(s) - zeroes slice elements or deletes map entries *)
  | EComplex  : expr -> expr -> expr'
      (** complex(real, imag) - construct complex number from real and imaginary parts.
          Go spec (Manipulating complex numbers):
            "The built-in function complex constructs a complex value from a
             floating-point real and imaginary part."
          Both arguments must be the same floating-point type:
            - float32 args -> complex64 result
            - float64 args -> complex128 result
          Runtime: VTuple [VFloat real prec; VFloat imag prec] *)
  | ERealPart : expr -> expr'
      (** real(c) - extract real part of a complex number.
          Go spec: "real and imag extract the real and imaginary parts of a complex value."
          Argument must be complex type:
            - complex64 arg  -> float32 result
            - complex128 arg -> float64 result
          Runtime: given VTuple [VFloat r _; VFloat _ _], returns VFloat r prec *)
  | EImagPart : expr -> expr'
      (** imag(c) - extract imaginary part of a complex number.
          Go spec: "real and imag extract the real and imaginary parts of a complex value."
          Argument must be complex type:
            - complex64 arg  -> float32 result
            - complex128 arg -> float64 result
          Runtime: given VTuple [VFloat _ _; VFloat i _], returns VFloat i prec *)
  | EDelete   : expr -> expr -> expr'                  (* delete(map, key) - removes key from map; no-op if nil or key absent *)
  | EAppend   : expr -> list expr -> expr'              (* append(slice, elems...) - Go append built-in:
                                                           append(s, x...)          -> appends elements x to slice s
                                                           append(s, other...)      -> appends all elements of other slice
                                                           Returns new slice, may allocate new backing array.
                                                           See Go spec: "Appending to and copying slices" *)
  | EMake     : brrr_type -> list expr -> expr'         (* make(T, args...) - Go built-in:
                                                           make([]T, len)       -> slice len=cap=len
                                                           make([]T, len, cap)  -> slice len, cap
                                                           make(map[K]V)        -> empty map
                                                           make(map[K]V, hint)  -> map with capacity hint
                                                           make(chan T)         -> unbuffered channel
                                                           make(chan T, size)   -> buffered channel *)
  | EBlock    : list expr -> expr'
  | ESeq      : expr -> expr -> expr'
  | EUnsafe   : expr -> expr'
  | EPtrToInt : expr -> expr'
      (** unsafe.Pointer -> uintptr: reinterpret a raw pointer as a pointer-sized
          unsigned integer. The GC does NOT treat the resulting integer as a reference,
          so the original object may be collected if no other pointer keeps it alive.
          Go spec (Package unsafe):
            "The effect of converting between Pointer and uintptr is
             implementation-defined."
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | EIntToPtr : expr -> brrr_type -> expr'
      (** uintptr -> unsafe.Pointer: reinterpret a pointer-sized unsigned integer
          as a raw pointer of the given type. The integer MUST have been derived from
          a valid, live pointer -- arbitrary integers produce undefined behavior.
          Go spec (Package unsafe):
            "Any pointer or value of underlying type uintptr can be converted to
             a type of underlying type Pointer and vice versa."
          The brrr_type parameter is the target pointer type (typically Raw[Unit]
          for Go's untyped unsafe.Pointer).
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | ESliceFromPtr : expr -> expr -> brrr_type -> expr'
      (** unsafe.Slice(ptr, len) - create a slice from a pointer and length.
          Go spec (Package unsafe, Go 1.17):
            "The function Slice returns a slice whose underlying array starts at ptr
             and whose length and capacity are len."
            Slice(ptr, len) is equivalent to:
              ( *[len]ArbitraryType)(unsafe.Pointer(ptr))[:]
          Special case: if ptr is nil and len is zero, returns nil.
          The len argument must be of integer type.
          At run time, if len is negative or ptr is nil and len is not zero,
          a run-time panic occurs.
          The brrr_type is the element type of the resulting slice.
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | ESliceData : expr -> expr'
      (** unsafe.SliceData(slice) - get pointer to underlying array of a slice.
          Go spec (Package unsafe, Go 1.20):
            "The function SliceData returns a pointer to the underlying array
             of the slice argument."
          If cap(slice) is not zero, the pointer is &slice[:1][0].
          If slice is nil, the result is nil.
          Otherwise it is a non-nil pointer to an unspecified memory address.
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | EStringFromPtr : expr -> expr -> expr'
      (** unsafe.String(ptr, len) - create a string from a byte pointer and length.
          Go spec (Package unsafe, Go 1.20):
            "The function String returns a string value whose underlying bytes
             start at ptr and whose length is len."
          The first operand must be a *byte pointer.
          The second operand must be an integer type.
          The result is a string.
          The same requirements apply to the ptr and len argument as in the
          function Slice. If len is zero, the result is the empty string "".
          Since Go strings are immutable, the bytes passed to String must not
          be modified afterwards.
          At run time, if len is negative or ptr is nil and len is not zero,
          a run-time panic occurs.
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | EStringData : expr -> expr'
      (** unsafe.StringData(str) - get pointer to underlying bytes of a string.
          Go spec (Package unsafe, Go 1.20):
            "The function StringData returns a pointer to the underlying bytes
             of the str argument."
          For an empty string the return value is unspecified, and may be nil.
          Since Go strings are immutable, the bytes returned by StringData
          must not be modified.
          The result is a *byte pointer.
          Must appear inside an EUnsafe block (requires EUnsafe effect). *)
  | EHole     : expr'
  | EError    : string -> expr'
  (* GRADUAL TYPING: Runtime cast expression
     ----------------------------------------
     ECast wraps an expression with a runtime type check for gradual typing.
     Inserted automatically by the type checker when:
     - An expression of type T1 flows to a context expecting T2
     - T1 and T2 are consistent (T1 ~ T2) but not subtypes

     Runtime semantics:
     - CKUp: No-op at runtime (can be erased by optimizer)
     - CKDown: Check that value is instance of target type, fail with blame on mismatch
     - CKDynamic: Extract value from Dynamic tag or wrap value in Dynamic tag

     Reference: Siek & Taha 2006 "Gradual Typing for Functional Languages" *)
  | ECast     : expr -> cast_info -> expr'

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

(** Pattern with source location - following EverParse pattern.

    pattern = with_loc pattern' = { loc_value: pattern'; loc_range: range }

    This is the "located" pattern type used throughout the codebase.
    The separation from pattern' allows:
    - Size computations on pattern' (for termination proofs)
    - Structural equality ignoring location
    - Consistent error reporting with source spans *)
and pattern = with_loc pattern'

(** Expression with source location - following EverParse pattern.

    expr = with_loc expr' = { loc_value: expr'; loc_range: range }

    This is the "located" expression type used throughout the codebase.

    KEY INVARIANT: For well-formed ASTs from parsing, the loc_range spans
    the entire syntactic extent of the expression in source code.

    For synthetic nodes (created during compilation), use dummy_range
    via locate_dummy or mk_expr_dummy.

    CRITICAL PATTERN MATCHING NOTE (SPECIFICATION_ERRATA.md Chapter 7):
    -------------------------------------------------------------------
    When pattern matching on expr, you MUST access .loc_value:

      let match_example (e: expr) =
        match e.loc_value with      (* CORRECT *)
        | EVar x -> ...
        | ELit l -> ...

      let match_WRONG (e: expr) =
        match e with                (* WRONG! e is with_loc expr', not expr' *)
        | EVar x -> ...             (* This won't type-check correctly *)

    This is a common source of bugs. The F* type checker may not always
    catch this error clearly, leading to confusing type mismatches. *)
and expr = with_loc expr'

(** ============================================================================
    ANNOTATED EXPRESSIONS (with additional metadata)
    ============================================================================ *)

(** Expression with full metadata (node ID, type, effects) *)
noeq type annotated_expr = {
  node         : node_id;
  source_range : range;
  ty           : option brrr_type;
  effects      : option effect_row;
  expr         : expr
}

(** Create annotated expression using the expression's range *)
val annotate : node_id -> expr -> annotated_expr

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
val p_type : brrr_type -> option var_id -> pattern  (* Type pattern *)
val p_wild_at : range -> pattern
val p_var_at : range -> var_id -> pattern
val p_type_at : range -> brrr_type -> option var_id -> pattern  (* Type pattern with location *)

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

(** expr_list_size for cons - crucial for termination proofs in other modules *)
val expr_list_size_cons : e:expr -> rest:list expr ->
  Lemma (ensures expr_list_size (e :: rest) = expr_size e + expr_list_size rest)
        [SMTPat (expr_list_size (e :: rest))]

(** expr_list_size for nil *)
val expr_list_size_nil : unit ->
  Lemma (ensures expr_list_size [] = 0)

(** expr_list_size decreases when removing head - for termination proofs *)
val expr_list_size_decreases : e:expr -> rest:list expr ->
  Lemma (ensures expr_list_size rest < expr_list_size (e :: rest))
        [SMTPat (expr_list_size (e :: rest))]

(** field_expr_list_size decreases when removing head *)
val field_expr_list_size_decreases : nm:string -> e:expr -> rest:list (string & expr) ->
  Lemma (ensures field_expr_list_size rest < field_expr_list_size ((nm, e) :: rest))
        [SMTPat (field_expr_list_size ((nm, e) :: rest))]

(** match_arm_list_size decreases when removing head *)
val match_arm_list_size_decreases : arm:match_arm -> rest:list match_arm ->
  Lemma (ensures match_arm_list_size rest < match_arm_list_size (arm :: rest))
        [SMTPat (match_arm_list_size (arm :: rest))]

(** catch_arm_list_size decreases when removing head *)
val catch_arm_list_size_decreases : c:catch_arm -> rest:list catch_arm ->
  Lemma (ensures catch_arm_list_size rest < catch_arm_list_size (c :: rest))
        [SMTPat (catch_arm_list_size (c :: rest))]

(** ============================================================================
    SUBEXPRESSION RELATIONSHIP (part 1: immediate_subexprs)
    ============================================================================ *)

(** Collect immediate subexpressions of an expression *)
val immediate_subexprs : expr -> list expr

(** Check if e2 is an immediate subexpression of e1 *)
val is_immediate_subexpr : sub:expr -> parent:expr -> Tot bool

(** ============================================================================
    EXPRESSION WELL-FORMEDNESS
    ============================================================================ *)

(** Well-formedness predicate for expressions.
    An expression is well-formed if:
    1. All variable references are valid identifiers
    2. Pattern bindings are consistent
    3. Type annotations (if present) are well-formed
    4. Control flow constructs are properly structured *)

(** Reserved prefix for generated identifiers *)
val reserved_prefix : string

(** Check if a variable identifier is valid (non-empty, no reserved prefix) *)
val is_valid_var_id : var_id -> bool

(** Collect all bound variables in a pattern *)
val pattern_bound_vars : pattern -> Tot (list var_id)

(** Check for duplicate bindings in pattern *)
val pattern_has_duplicate_bindings : pattern -> bool

(** Check if pattern is well-formed (no duplicate bindings in tuples, etc.) *)
val pattern_wf : pattern -> Tot bool

(** Check if expression is well-formed (structural validity) *)
val expr_wf : e:expr -> Tot bool (decreases expr_size e)

(** Check if match arms are exhaustive (requires external type info) *)
val match_arms_wf : list match_arm -> bool

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

(** Collect free variables in a list of expressions *)
val free_vars_list : list expr -> Tot (list var_id)

(** Collect free variables in field expressions *)
val free_vars_fields : list (string & expr) -> Tot (list var_id)

(** Check if variable is free in expression *)
val is_free_in : var_id -> expr -> Tot bool

(** Variables that may be bound by a parent expression *)
val parent_binds : expr -> list var_id

(** Free variables of subexpression are subset of parent free variables
    (modulo bindings in between) *)
val free_vars_subexpr : sub:expr -> parent:expr ->
  Lemma (requires is_immediate_subexpr sub parent = true)
        (ensures forall v. mem v (free_vars sub) ==>
                          mem v (free_vars parent) \/
                          mem v (parent_binds parent))

(** ============================================================================
    EXPRESSION EQUALITY
    ============================================================================ *)

(** Literal equality.
    Unfold allows Z3 to see the structure for automatic proofs.
    Uses IEEE 754 equality for floats (NaN != NaN). *)
[@(strict_on_arguments [0;1])]
unfold
let literal_eq (l1 l2: literal) : bool =
  match l1, l2 with
  | LitUnit, LitUnit -> true
  | LitBool b1, LitBool b2 -> b1 = b2
  | LitInt n1 t1, LitInt n2 t2 -> n1 = n2 && t1.width = t2.width && t1.sign = t2.sign
  | LitFloat r1 p1, LitFloat r2 p2 -> float_repr_eq_ieee754 r1 r2 && p1 = p2
  | LitString s1, LitString s2 -> s1 = s2
  | LitChar c1, LitChar c2 -> c1 = c2
  | LitImaginary r1 p1, LitImaginary r2 p2 -> float_repr_eq_ieee754 r1 r2 && p1 = p2
  | _, _ -> false

(** Unary operator equality.
    Unfold allows Z3 to see the structure for automatic proofs. *)
[@(strict_on_arguments [0;1])]
unfold
let unary_op_eq (op1 op2: unary_op) : bool = op1 = op2

(** Binary operator equality.
    Unfold allows Z3 to see the structure for automatic proofs. *)
[@(strict_on_arguments [0;1])]
unfold
let binary_op_eq (op1 op2: binary_op) : bool = op1 = op2

(** ============================================================================
    STRUCTURAL EQUALITY
    ============================================================================ *)

(** Pattern equality (ignores location, compares structure) *)
val pattern_eq : pattern -> pattern -> Tot bool

(** Pattern list equality *)
val pattern_list_eq : list pattern -> list pattern -> Tot bool

(** Pattern field list equality *)
val pattern_field_list_eq : list (string & pattern) -> list (string & pattern) -> Tot bool

(** Expression structural equality (ignores location, compares structure) *)
val expr_eq : e1:expr -> e2:expr -> Tot bool

(** Expression list structural equality *)
val expr_list_eq : list expr -> list expr -> Tot bool

(** Expression field list structural equality *)
val expr_field_list_eq : list (string & expr) -> list (string & expr) -> Tot bool

(** Optional expression structural equality *)
val option_expr_eq : option expr -> option expr -> Tot bool

(** Match arm list equality *)
val match_arm_list_eq : list match_arm -> list match_arm -> Tot bool

(** Catch arm list equality *)
val catch_arm_list_eq : list catch_arm -> list catch_arm -> Tot bool

(** ============================================================================
    EXPRESSION EQUALITY LEMMAS
    ============================================================================
    NOTE: pattern_eq_sym and pattern_eq_trans are internal to the implementation
    and not exposed in this interface to avoid ordering conflicts.
    ============================================================================ *)

(** expr_eq is reflexive *)
val expr_eq_refl : e:expr ->
  Lemma (ensures expr_eq e e = true)

(** pattern_eq is reflexive (defined with expr_eq_refl in mutual recursion) *)
val pattern_eq_refl : p:pattern ->
  Lemma (ensures pattern_eq p p = true)

(** expr_eq is symmetric *)
val expr_eq_sym : e1:expr -> e2:expr ->
  Lemma (requires expr_eq e1 e2 = true)
        (ensures expr_eq e2 e1 = true)

(** expr_eq is transitive *)
val expr_eq_trans : e1:expr -> e2:expr -> e3:expr ->
  Lemma (requires expr_eq e1 e2 = true /\ expr_eq e2 e3 = true)
        (ensures expr_eq e1 e3 = true)

(** ============================================================================
    SUBEXPRESSION RELATIONSHIP (is_subexpr and lemmas)
    ============================================================================ *)

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

(** Subexpression ranges are within parent range (when properly constructed) *)
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
    EXPRESSION NORMALIZATION
    ============================================================================

    Normalization transforms expressions to a canonical form. It must be
    declared BEFORE alpha equivalence because alpha equivalence is defined
    in terms of normalization.
    ============================================================================ *)

(** Normalize expression to a canonical form:
    - Unwrap singleton blocks: EBlock [e] -> e
    - Flatten nested blocks: EBlock [EBlock [a,b], c] -> EBlock [a,b,c]
    - Recursively normalize subexpressions

    The result is in "block-normal form" where:
    - No singleton blocks exist
    - No nested blocks exist
    - All subexpressions are recursively normalized *)
val normalize_expr : expr -> expr

(** Normalization is idempotent: applying it twice gives the same result *)
val normalize_expr_idempotent : e:expr ->
  Lemma (ensures expr_eq (normalize_expr e) (normalize_expr (normalize_expr e)) = true)

(** ============================================================================
    ALPHA EQUIVALENCE
    ============================================================================

    Two expressions are alpha-equivalent if they normalize to structurally
    equal expressions. This captures semantic equivalence up to:
    - Block structure (singleton blocks, nested blocks)
    - Source locations (ranges are not compared in expr_eq)

    This definition ensures that normalization trivially preserves alpha
    equivalence: normalize_expr e is always alpha-equivalent to e.
    ============================================================================ *)

(** Alpha equivalence for patterns (structural comparison) *)
val pattern_alpha_eq : pattern -> pattern -> bool

(** Alpha equivalence for expressions.

    Two expressions are alpha-equivalent iff they normalize to structurally
    equal expressions: expr_alpha_eq e1 e2 = expr_eq (normalize e1) (normalize e2)

    This is a decidable equivalence relation. *)
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

(** Normalization preserves semantics (alpha equivalence).

    This is theorem T-4.1. The proof is elegant:
    - expr_alpha_eq e (normalize e) = expr_eq (normalize e) (normalize (normalize e))
    - By idempotence: normalize (normalize e) = normalize e
    - So we need: expr_eq (normalize e) (normalize e) = true
    - This is trivially true by reflexivity *)
val normalize_expr_equiv : e:expr ->
  Lemma (ensures expr_alpha_eq e (normalize_expr e) = true)

(** ============================================================================
    EXPRESSION SERIALIZATION (for debugging/display)
    ============================================================================ *)

(** Pretty-print expression to string *)
val expr_to_string : expr -> string

(** Pretty-print pattern to string *)
val pattern_to_string : pattern -> string

(** Parse expression from string (may fail) *)
val expr_from_string : string -> option expr
