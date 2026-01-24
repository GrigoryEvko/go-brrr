(**
 * Brrr-Lang Python Types - Single Source of Truth
 *
 * Canonical Python type definitions for the translation layer.
 * All modules requiring Python type representations MUST import from here.
 *
 * Based on brrr_lang_spec_v0.4.md Part VI Section 2 (Python Translation).
 * Follows EverParse's single-source-of-truth pattern (see Ast.fst).
 *
 * Source Location Tracking:
 *   Following EverParse's with_meta_t pattern, all Python AST nodes
 *   carry source location information for precise error reporting.
 *   See EverParse src/3d/Ast.fst lines 107-111 for reference.
 *)
module PythonTypes

(** Z3 solver options - conservative settings *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open Primitives
open BrrrTypes
open Expressions  (* Imports pos, range, dummy_range, string_of_range *)

(** ============================================================================
    PYTHON SOURCE LOCATION TYPES
    ============================================================================

    Following EverParse's with_meta_t pattern for source location tracking.
    We reuse the core range/pos types from Expressions.fst and add
    Python-specific wrappers.

    Reference: EverParse src/3d/Ast.fst lines 107-111:
      noeq type with_meta_t 'a = { v:'a; range:range; comments: comments }
    ============================================================================ *)

(** Python source range - reuse from Expressions.fst *)
let py_range : Type = range

(** Dummy Python range for synthetic nodes *)
let dummy_py_range : py_range = dummy_range

(** Format Python range for error messages *)
let string_of_py_range (r: py_range) : string = string_of_range r

(** Format Python position for error messages *)
let string_of_py_pos (p: pos) : string = string_of_pos p

(** Location wrapper for Python AST nodes.
    Following EverParse's with_meta_t pattern.

    Unlike EverParse, we don't track comments in the Python AST wrapper
    since Python comments are handled separately by the parser. *)
noeq type with_py_loc 'a = {
  py_value : 'a;         (* The wrapped value *)
  py_range : py_range    (* Source span *)
}

(** Wrap a value with a source location *)
let py_loc (#a: Type) (r: py_range) (x: a) : with_py_loc a =
  { py_value = x; py_range = r }

(** Wrap a value with dummy location (for synthetic nodes) *)
let py_loc_dummy (#a: Type) (x: a) : with_py_loc a =
  py_loc dummy_py_range x

(** Extract the value from a located wrapper *)
let py_value_of (#a: Type) (w: with_py_loc a) : a = w.py_value

(** Extract the range from a located wrapper *)
let py_range_of (#a: Type) (w: with_py_loc a) : py_range = w.py_range

(** Map a function over a located value, preserving location *)
let py_loc_map (#a #b: Type) (f: a -> b) (w: with_py_loc a) : with_py_loc b =
  { py_value = f w.py_value; py_range = w.py_range }

(** ============================================================================
    PYTHON SOURCE TYPES
    ============================================================================

    Python type annotations from typing module.
    These represent the source language types before translation to Brrr-Lang.

    Complete coverage of Python's typing module:
    - Primitive types: None, bool, int, float, str, bytes
    - Collection types: list, dict, set, frozenset, tuple
    - Typing constructs: Optional, Union, Callable, Awaitable, Generator, etc.
    - Special types: Any, Never, Type, TypeVar, Literal, Self
    ============================================================================ *)

(** Python source types (from typing module annotations)

    This is the canonical definition used throughout the translation layer.
    Import this type via: open PythonTypes
*)
noeq type py_type =
  (* Primitive types *)
  | PyNone     : py_type                       (* None type (NoneType) *)
  | PyBool     : py_type                       (* bool *)
  | PyInt      : py_type                       (* int (arbitrary precision) *)
  | PyFloat    : py_type                       (* float (64-bit IEEE 754) *)
  | PyStr      : py_type                       (* str (Unicode string) *)
  | PyBytes    : py_type                       (* bytes *)

  (* Collection types *)
  | PyList     : elem:py_type -> py_type                   (* list[T] *)
  | PyDict     : key:py_type -> value:py_type -> py_type   (* dict[K, V] *)
  | PySet      : elem:py_type -> py_type                   (* set[T] *)
  | PyFrozenSet: elem:py_type -> py_type                   (* frozenset[T] *)
  | PyTuple    : elems:list py_type -> py_type             (* tuple[T1, T2, ...] *)

  (* Typing module constructs *)
  | PyOptional : inner:py_type -> py_type                  (* Optional[T] = T | None *)
  | PyUnion    : branches:list py_type -> py_type          (* Union[T1, T2, ...] *)
  | PyCallable : params:list py_type -> ret:py_type -> py_type  (* Callable[[Args], Ret] *)
  (* Enhanced callable with effect annotations and async flag.
     - effects: List of exception type names (e.g., ["ValueError", "TypeError"])
                None means conservative/unknown (any exception possible)
     - is_async: True for async def functions (coroutines) *)
  | PyCallableAnnotated : params:list py_type -> ret:py_type ->
                          effects:option (list string) -> is_async:bool -> py_type
  | PyAwaitable: inner:py_type -> py_type                  (* Awaitable[T] *)
  (* Async coroutine - explicitly tracks async effect unlike plain Awaitable *)
  | PyCoroutine: inner:py_type -> py_type                  (* Coroutine[T] - async result *)
  | PyGenerator: yield_ty:py_type -> send_ty:py_type -> return_ty:py_type -> py_type  (* Generator[Y, S, R] *)
  (* Async generator - produces values asynchronously *)
  | PyAsyncGenerator: yield_ty:py_type -> send_ty:py_type -> py_type  (* AsyncGenerator[Y, S] *)
  | PyIterator : elem:py_type -> py_type                   (* Iterator[T] *)
  | PyIterable : elem:py_type -> py_type                   (* Iterable[T] *)

  (* Special types *)
  | PyAny      : py_type                       (* Any (dynamic) *)
  | PyNever    : py_type                       (* NoReturn / Never *)
  | PyType     : inner:py_type -> py_type      (* Type[T] (metaclass) *)
  | PyClass    : name:string -> py_type        (* Named class *)
  | PyGeneric  : name:string -> args:list py_type -> py_type  (* Generic[T1, T2, ...] *)
  | PyTypeVar  : name:string -> py_type        (* TypeVar("T") *)
  | PyLiteral  : value:literal -> py_type      (* Literal[value] *)
  | PySelf     : py_type                       (* Self type *)

(** ============================================================================
    PYTHON SOURCE EXPRESSIONS
    ============================================================================

    Python expression AST representing source code constructs.
    Complete coverage of Python 3.10+ syntax including:
    - Atoms: variables, literals, None/True/False
    - Operations: binary, unary, chained comparisons
    - Calls and access: function calls, attribute access, indexing, slicing
    - Functions: lambda expressions
    - Collections: list, dict, tuple, set literals
    - Comprehensions: list, dict, set, generator expressions
    - Control flow: if/for/while/try/with/match
    - Async: await, yield, yield from

    Source Location Tracking:
      Following EverParse's with_meta_t pattern (Ast.fst lines 107-111):
      - py_expr' is the raw expression type (without location)
      - py_expr = with_py_loc py_expr' wraps expressions with source span
      - All AST constructors produce located expressions
    ============================================================================ *)

(** Python source expressions (raw, without location) *)
noeq type py_expr' =
  (* Atoms *)
  | PyEVar'      : name:string -> py_expr'                   (* Variable reference *)
  | PyELit'      : value:literal -> py_expr'                 (* Literal value *)
  | PyENone'     : py_expr'                                  (* None literal *)
  | PyETrue'     : py_expr'                                  (* True literal *)
  | PyEFalse'    : py_expr'                                  (* False literal *)

  (* Operations *)
  | PyEBinOp'    : op:binary_op -> left:py_expr -> right:py_expr -> py_expr'  (* e1 op e2 *)
  | PyEUnOp'     : op:unary_op -> operand:py_expr -> py_expr'                 (* op e *)
  | PyECompare'  : first:py_expr -> rest:list (binary_op & py_expr) -> py_expr'  (* Chained: a < b < c *)
  | PyEBoolOp'   : is_and:bool -> operands:list py_expr -> py_expr'  (* and/or with short-circuit *)

  (* Calls and access *)
  | PyECall'     : func:py_expr -> args:list py_expr -> kwargs:list (string & py_expr) -> py_expr'  (* f(args, **kwargs) *)
  | PyEAttr'     : obj:py_expr -> attr:string -> py_expr'    (* e.attr *)
  | PyEIndex'    : obj:py_expr -> index:py_expr -> py_expr'  (* e[i] *)
  | PyESlice'    : obj:py_expr -> start:option py_expr -> stop:option py_expr -> step:option py_expr -> py_expr'  (* e[a:b:c] *)

  (* Functions *)
  | PyELambda'   : params:list string -> body:py_expr -> py_expr'  (* lambda x: e *)

  (* Collections *)
  | PyEList'     : elems:list py_expr -> py_expr'            (* [e1, e2, ...] *)
  | PyEDict'     : pairs:list (py_expr & py_expr) -> py_expr'  (* {k1: v1, ...} *)
  | PyETuple'    : elems:list py_expr -> py_expr'            (* (e1, e2, ...) *)
  | PyESet'      : elems:list py_expr -> py_expr'            (* {e1, e2, ...} *)

  (* Comprehensions *)
  | PyEListComp' : body:py_expr -> clauses:list py_comp_clause -> py_expr'  (* [e for ...] *)
  | PyEDictComp' : key:py_expr -> value:py_expr -> clauses:list py_comp_clause -> py_expr'  (* {k: v for ...} *)
  | PyESetComp'  : body:py_expr -> clauses:list py_comp_clause -> py_expr'   (* {e for ...} *)
  | PyEGenExpr'  : body:py_expr -> clauses:list py_comp_clause -> py_expr'   (* (e for ...) *)

  (* Control flow expressions *)
  | PyEIfExp'    : cond:py_expr -> then_:py_expr -> else_:py_expr -> py_expr'    (* e1 if cond else e2 *)
  | PyEWalrus'   : var:string -> value:py_expr -> py_expr'                       (* x := e (assignment expr) *)

  (* Async *)
  | PyEAwait'    : inner:py_expr -> py_expr'                  (* await e *)

  (* Statements as expressions (for block translation) *)
  | PyEAssign'   : target:py_expr -> value:py_expr -> py_expr'    (* x = e *)
  | PyEAugAssign': op:binary_op -> target:py_expr -> value:py_expr -> py_expr'  (* x += e *)
  | PyEReturn'   : value:option py_expr -> py_expr'          (* return [e] *)
  | PyEYield'    : value:option py_expr -> py_expr'          (* yield [e] *)
  | PyEYieldFrom': iter:py_expr -> py_expr'                  (* yield from e *)
  | PyERaise'    : exc:option py_expr -> cause:option py_expr -> py_expr'  (* raise [e] [from e] *)
  | PyEAssert'   : test:py_expr -> msg:option py_expr -> py_expr'          (* assert e [, msg] *)
  | PyEPass'     : py_expr'                                  (* pass *)
  | PyEBreak'    : py_expr'                                  (* break *)
  | PyEContinue' : py_expr'                                  (* continue *)

  (* Control flow *)
  | PyEIf'       : cond:py_expr -> then_:py_expr -> elifs:list (py_expr & py_expr) -> else_:option py_expr -> py_expr'  (* if/elif/else *)
  | PyEFor'      : var:string -> iter:py_expr -> body:py_expr -> else_:option py_expr -> py_expr'  (* for x in e: body [else: ...] *)
  | PyEWhile'    : cond:py_expr -> body:py_expr -> else_:option py_expr -> py_expr'            (* while cond: body [else: ...] *)
  | PyETry'      : body:py_expr -> handlers:list py_except_handler -> else_:option py_expr -> finally:option py_expr -> py_expr'  (* try/except/else/finally *)
  | PyEWith'     : items:list (py_expr & option string) -> body:py_expr -> py_expr'       (* with e [as x]: body *)
  | PyEMatch'    : scrutinee:py_expr -> cases:list (py_match_pattern & option py_expr & py_expr) -> py_expr'  (* match e: case ... *)

  (* Block *)
  | PyEBlock'    : stmts:list py_expr -> py_expr'            (* Sequence of statements *)

(** Comprehension clause: for x in iter [if cond] *)
and py_comp_clause =
  | PyCompFor  : var:string -> iter:py_expr -> py_comp_clause          (* for x in iter *)
  | PyCompIf   : cond:py_expr -> py_comp_clause                        (* if cond *)

(** Exception handler with source location *)
and py_except_handler = {
  except_range : py_range;         (* Source location of handler *)
  except_type  : option py_type;   (* Exception type to catch *)
  except_name  : option string;    (* Variable name to bind *)
  except_body  : py_expr           (* Handler body *)
}

(** Match pattern (Python 3.10+) *)
and py_match_pattern =
  | PyPatWild    : py_match_pattern                                    (* _ *)
  | PyPatCapture : name:string -> py_match_pattern                     (* name *)
  | PyPatLiteral : value:literal -> py_match_pattern                   (* 42, "str" *)
  | PyPatSequence: elems:list py_match_pattern -> py_match_pattern     (* [p1, p2] *)
  | PyPatMapping : pairs:list (py_expr & py_match_pattern) -> py_match_pattern  (* {k1: p1} *)
  | PyPatClass   : name:string -> pos_args:list py_match_pattern -> kw_args:list (string & py_match_pattern) -> py_match_pattern  (* Cls(p1, k=p2) *)
  | PyPatOr      : alts:list py_match_pattern -> py_match_pattern      (* p1 | p2 *)
  | PyPatAs      : pat:py_match_pattern -> name:string -> py_match_pattern  (* p as name *)
  | PyPatGuard   : pat:py_match_pattern -> guard:py_expr -> py_match_pattern  (* p if guard (conceptual) *)

(** Located Python expression - the main type used throughout translation.
    Wraps py_expr' with source location following EverParse pattern. *)
and py_expr = with_py_loc py_expr'

(** ============================================================================
    PYTHON EXPRESSION CONSTRUCTORS WITH LOCATION
    ============================================================================

    Smart constructors that create located expressions.
    Use these instead of directly constructing py_expr values.
    ============================================================================ *)

(** Create a located expression at a given range *)
let mk_py_expr (r: py_range) (e: py_expr') : py_expr = py_loc r e

(** Create a located expression at dummy range (for synthetic nodes) *)
let mk_py_expr_dummy (e: py_expr') : py_expr = py_loc_dummy e

(** Extract the raw expression from a located expression *)
let py_expr_value (e: py_expr) : py_expr' = py_value_of e

(** Extract the source range from a located expression *)
let py_expr_range (e: py_expr) : py_range = py_range_of e

(** Convenience constructors for common expressions with location *)
let py_var (r: py_range) (name: string) : py_expr = mk_py_expr r (PyEVar' name)
let py_lit (r: py_range) (lit: literal) : py_expr = mk_py_expr r (PyELit' lit)
let py_none (r: py_range) : py_expr = mk_py_expr r PyENone'
let py_true (r: py_range) : py_expr = mk_py_expr r PyETrue'
let py_false (r: py_range) : py_expr = mk_py_expr r PyEFalse'
let py_binop (r: py_range) (op: binary_op) (l: py_expr) (rhs: py_expr) : py_expr =
  mk_py_expr r (PyEBinOp' op l rhs)
let py_unop (r: py_range) (op: unary_op) (e: py_expr) : py_expr =
  mk_py_expr r (PyEUnOp' op e)
let py_call (r: py_range) (f: py_expr) (args: list py_expr) (kwargs: list (string & py_expr)) : py_expr =
  mk_py_expr r (PyECall' f args kwargs)
let py_attr (r: py_range) (obj: py_expr) (attr: string) : py_expr =
  mk_py_expr r (PyEAttr' obj attr)
let py_index (r: py_range) (obj: py_expr) (idx: py_expr) : py_expr =
  mk_py_expr r (PyEIndex' obj idx)
let py_lambda (r: py_range) (params: list string) (body: py_expr) : py_expr =
  mk_py_expr r (PyELambda' params body)
let py_list (r: py_range) (elems: list py_expr) : py_expr =
  mk_py_expr r (PyEList' elems)
let py_dict (r: py_range) (pairs: list (py_expr & py_expr)) : py_expr =
  mk_py_expr r (PyEDict' pairs)
let py_tuple (r: py_range) (elems: list py_expr) : py_expr =
  mk_py_expr r (PyETuple' elems)
let py_set (r: py_range) (elems: list py_expr) : py_expr =
  mk_py_expr r (PyESet' elems)
let py_if_exp (r: py_range) (cond: py_expr) (then_: py_expr) (else_: py_expr) : py_expr =
  mk_py_expr r (PyEIfExp' cond then_ else_)
let py_await (r: py_range) (e: py_expr) : py_expr =
  mk_py_expr r (PyEAwait' e)
let py_return (r: py_range) (v: option py_expr) : py_expr =
  mk_py_expr r (PyEReturn' v)
let py_yield (r: py_range) (v: option py_expr) : py_expr =
  mk_py_expr r (PyEYield' v)
let py_raise (r: py_range) (exc: option py_expr) (cause: option py_expr) : py_expr =
  mk_py_expr r (PyERaise' exc cause)
let py_pass (r: py_range) : py_expr = mk_py_expr r PyEPass'
let py_break (r: py_range) : py_expr = mk_py_expr r PyEBreak'
let py_continue (r: py_range) : py_expr = mk_py_expr r PyEContinue'
let py_block (r: py_range) (stmts: list py_expr) : py_expr =
  mk_py_expr r (PyEBlock' stmts)

(** Backwards compatibility aliases - create expressions at dummy range.
    Use the located constructors above for proper source tracking. *)
let PyEVar (name: string) : py_expr = mk_py_expr_dummy (PyEVar' name)
let PyELit (value: literal) : py_expr = mk_py_expr_dummy (PyELit' value)
let PyENone : py_expr = mk_py_expr_dummy PyENone'
let PyETrue : py_expr = mk_py_expr_dummy PyETrue'
let PyEFalse : py_expr = mk_py_expr_dummy PyEFalse'
let PyEBinOp (op: binary_op) (left: py_expr) (right: py_expr) : py_expr =
  mk_py_expr_dummy (PyEBinOp' op left right)
let PyEUnOp (op: unary_op) (operand: py_expr) : py_expr =
  mk_py_expr_dummy (PyEUnOp' op operand)
let PyECompare (first: py_expr) (rest: list (binary_op & py_expr)) : py_expr =
  mk_py_expr_dummy (PyECompare' first rest)
let PyEBoolOp (is_and: bool) (operands: list py_expr) : py_expr =
  mk_py_expr_dummy (PyEBoolOp' is_and operands)
let PyECall (func: py_expr) (args: list py_expr) (kwargs: list (string & py_expr)) : py_expr =
  mk_py_expr_dummy (PyECall' func args kwargs)
let PyEAttr (obj: py_expr) (attr: string) : py_expr =
  mk_py_expr_dummy (PyEAttr' obj attr)
let PyEIndex (obj: py_expr) (index: py_expr) : py_expr =
  mk_py_expr_dummy (PyEIndex' obj index)
let PyESlice (obj: py_expr) (start: option py_expr) (stop: option py_expr) (step: option py_expr) : py_expr =
  mk_py_expr_dummy (PyESlice' obj start stop step)
let PyELambda (params: list string) (body: py_expr) : py_expr =
  mk_py_expr_dummy (PyELambda' params body)
let PyEList (elems: list py_expr) : py_expr =
  mk_py_expr_dummy (PyEList' elems)
let PyEDict (pairs: list (py_expr & py_expr)) : py_expr =
  mk_py_expr_dummy (PyEDict' pairs)
let PyETuple (elems: list py_expr) : py_expr =
  mk_py_expr_dummy (PyETuple' elems)
let PyESet (elems: list py_expr) : py_expr =
  mk_py_expr_dummy (PyESet' elems)
let PyEListComp (body: py_expr) (clauses: list py_comp_clause) : py_expr =
  mk_py_expr_dummy (PyEListComp' body clauses)
let PyEDictComp (key: py_expr) (value: py_expr) (clauses: list py_comp_clause) : py_expr =
  mk_py_expr_dummy (PyEDictComp' key value clauses)
let PyESetComp (body: py_expr) (clauses: list py_comp_clause) : py_expr =
  mk_py_expr_dummy (PyESetComp' body clauses)
let PyEGenExpr (body: py_expr) (clauses: list py_comp_clause) : py_expr =
  mk_py_expr_dummy (PyEGenExpr' body clauses)
let PyEIfExp (cond: py_expr) (then_: py_expr) (else_: py_expr) : py_expr =
  mk_py_expr_dummy (PyEIfExp' cond then_ else_)
let PyEWalrus (var: string) (value: py_expr) : py_expr =
  mk_py_expr_dummy (PyEWalrus' var value)
let PyEAwait (inner: py_expr) : py_expr =
  mk_py_expr_dummy (PyEAwait' inner)
let PyEAssign (target: py_expr) (value: py_expr) : py_expr =
  mk_py_expr_dummy (PyEAssign' target value)
let PyEAugAssign (op: binary_op) (target: py_expr) (value: py_expr) : py_expr =
  mk_py_expr_dummy (PyEAugAssign' op target value)
let PyEReturn (value: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEReturn' value)
let PyEYield (value: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEYield' value)
let PyEYieldFrom (iter: py_expr) : py_expr =
  mk_py_expr_dummy (PyEYieldFrom' iter)
let PyERaise (exc: option py_expr) (cause: option py_expr) : py_expr =
  mk_py_expr_dummy (PyERaise' exc cause)
let PyEAssert (test: py_expr) (msg: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEAssert' test msg)
let PyEPass : py_expr = mk_py_expr_dummy PyEPass'
let PyEBreak : py_expr = mk_py_expr_dummy PyEBreak'
let PyEContinue : py_expr = mk_py_expr_dummy PyEContinue'
let PyEIf (cond: py_expr) (then_: py_expr) (elifs: list (py_expr & py_expr)) (else_: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEIf' cond then_ elifs else_)
let PyEFor (var: string) (iter: py_expr) (body: py_expr) (else_: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEFor' var iter body else_)
let PyEWhile (cond: py_expr) (body: py_expr) (else_: option py_expr) : py_expr =
  mk_py_expr_dummy (PyEWhile' cond body else_)
let PyETry (body: py_expr) (handlers: list py_except_handler) (else_: option py_expr) (finally: option py_expr) : py_expr =
  mk_py_expr_dummy (PyETry' body handlers else_ finally)
let PyEWith (items: list (py_expr & option string)) (body: py_expr) : py_expr =
  mk_py_expr_dummy (PyEWith' items body)
let PyEMatch (scrutinee: py_expr) (cases: list (py_match_pattern & option py_expr & py_expr)) : py_expr =
  mk_py_expr_dummy (PyEMatch' scrutinee cases)
let PyEBlock (stmts: list py_expr) : py_expr =
  mk_py_expr_dummy (PyEBlock' stmts)

(** ============================================================================
    PYTHON TRANSLATION RESULT
    ============================================================================

    Result type for Python expression translation.
    Supports exact translation, sound approximation, or error.

    Source Location Tracking:
      All result variants carry source_range to preserve the original
      Python source location for error reporting and debugging.
      Following EverParse's error function pattern (Ast.fst lines 146-148).
    ============================================================================ *)

(** Translation result: success with possible approximation warning.
    All variants carry source_range for precise error reporting. *)
noeq type py_trans_result =
  | PyTransOk     : result:expr -> source_range:py_range -> py_trans_result
  | PyTransApprox : result:expr -> reason:string -> source_range:py_range -> py_trans_result
  | PyTransError  : reason:string -> source_range:py_range -> py_trans_result

(** ============================================================================
    HELPER FUNCTIONS
    ============================================================================ *)

(** Check if translation succeeded (exact or approximate) *)
let py_trans_is_success (r: py_trans_result) : bool =
  match r with
  | PyTransOk _ _ -> true
  | PyTransApprox _ _ _ -> true
  | PyTransError _ _ -> false

(** Extract expression from successful translation *)
let py_trans_get_expr (r: py_trans_result{py_trans_is_success r}) : expr =
  match r with
  | PyTransOk e _ -> e
  | PyTransApprox e _ _ -> e

(** Extract source range from any translation result *)
let py_trans_get_range (r: py_trans_result) : py_range =
  match r with
  | PyTransOk _ range -> range
  | PyTransApprox _ _ range -> range
  | PyTransError _ range -> range

(** Format error message with source location.
    Following EverParse's error function pattern (Ast.fst lines 146-148). *)
let py_trans_format_error (r: py_trans_result{PyTransError? r}) : string =
  match r with
  | PyTransError msg range ->
      string_of_py_range range ^ ": (Error) " ^ msg

(** Format approximation warning with source location *)
let py_trans_format_warning (r: py_trans_result{PyTransApprox? r _ _}) : string =
  match r with
  | PyTransApprox _ msg range ->
      string_of_py_range range ^ ": (Warning) " ^ msg

(** Map over translation result, preserving source location *)
let py_trans_map (f: expr -> expr) (r: py_trans_result) : py_trans_result =
  match r with
  | PyTransOk e range -> PyTransOk (f e) range
  | PyTransApprox e reason range -> PyTransApprox (f e) reason range
  | PyTransError reason range -> PyTransError reason range

(** Combine two translation results with a binary operation.
    Uses the range from the first result for the combined result. *)
let py_trans_combine (f: expr -> expr -> expr)
                     (r1: py_trans_result) (r2: py_trans_result)
    : py_trans_result =
  match r1, r2 with
  | PyTransOk e1 range1, PyTransOk e2 _ ->
      PyTransOk (f e1 e2) range1
  | PyTransError reason range, _ ->
      PyTransError reason range
  | _, PyTransError reason range ->
      PyTransError reason range
  | PyTransApprox e1 r1 range1, PyTransApprox e2 r2 _ ->
      PyTransApprox (f e1 e2) (r1 ^ "; " ^ r2) range1
  | PyTransApprox e1 r range1, PyTransOk e2 _ ->
      PyTransApprox (f e1 e2) r range1
  | PyTransOk e1 range1, PyTransApprox e2 r _ ->
      PyTransApprox (f e1 e2) r range1

(** Create a success result from a py_expr, extracting its range *)
let py_trans_ok_from (e: py_expr) (result: expr) : py_trans_result =
  PyTransOk result (py_expr_range e)

(** Create an approximation result from a py_expr, extracting its range *)
let py_trans_approx_from (e: py_expr) (result: expr) (reason: string) : py_trans_result =
  PyTransApprox result reason (py_expr_range e)

(** Create an error result from a py_expr, extracting its range *)
let py_trans_error_from (e: py_expr) (reason: string) : py_trans_result =
  PyTransError reason (py_expr_range e)

(** Create an error result at a specific range *)
let py_trans_error_at (range: py_range) (reason: string) : py_trans_result =
  PyTransError reason range
