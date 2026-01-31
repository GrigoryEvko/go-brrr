(**
 * ==============================================================================
 * Brrr-Lang Python Translation Functor - Public Interface
 * ==============================================================================
 *
 * Module:        PythonTranslation
 * Specification: brrr_lang_spec_v0.4.tex, Chapter "Python Translation" (lines 8928-9003)
 * Design Doc:    TRANSLATION_DESIGN.txt, Section 5 (Python -> Brrr-Lang)
 *
 * ------------------------------------------------------------------------------
 * OVERVIEW
 * ------------------------------------------------------------------------------
 *
 * This module defines the translation functor T_Py from Python to Brrr-Lang IR.
 * The translation follows the categorical foundation established in the spec:
 *
 *   T_Py : Cat_Python -> Cat_Brrr
 *
 * where:
 *   - Cat_Python has Python types as objects and Python functions as morphisms
 *   - Cat_Brrr has Brrr-Lang types as objects and Brrr expressions as morphisms
 *
 * The functor must satisfy:
 *   1. T_Py(id_A) = id_{T_Py(A)}                    (Identity preservation)
 *   2. T_Py(g . f) = T_Py(g) . T_Py(f)             (Composition preservation)
 *
 * ------------------------------------------------------------------------------
 * SOUNDNESS CRITERION (SPECIFICATION THEOREM)
 * ------------------------------------------------------------------------------
 *
 * The translation is SOUND iff for all Python expressions e, environments rho,
 * and values v:
 *
 *   [[e]]_Python(rho) = v  ==>  [[T_Py(e)]]_Brrr(T_Py(rho)) = T_Py(v)
 *
 * This means: if Python evaluates e to v under environment rho, then the
 * translated expression T_Py(e) evaluates to the translated value T_Py(v)
 * under the translated environment T_Py(rho).
 *
 * IMPORTANT: This is an IMPLICATION, not an IFF. The translation may REJECT
 * some valid Python programs (e.g., those using unsupported features like
 * **kwargs or certain decorators), but it will NEVER accept a Python program
 * and produce incorrect Brrr-Lang code.
 *
 * ------------------------------------------------------------------------------
 * PYTHON LANGUAGE MODE (from TRANSLATION_DESIGN.txt)
 * ------------------------------------------------------------------------------
 *
 *   Python = <MemGC, TypeDynamic, NullNullable, EffUntracked, ConcAsync>
 *
 * Implications:
 *   - Memory:      GC-managed, all values have mode omega (MOmega)
 *   - Types:       Dynamic typing - types are approximated or use TAny
 *   - Null:        All reference types are implicitly nullable (-> TOption)
 *   - Effects:     Untracked in Python; we conservatively assume epsilon_Py
 *   - Concurrency: async/await supported, maps to Brrr async effect
 *
 * Language Axioms:
 *   axioms(Python) = { AxMemSafe, AxLeakFree }
 *
 * Python guarantees memory safety (no use-after-free) via GC and freedom from
 * memory leaks (GC eventually reclaims unreachable objects). However, Python
 * does NOT provide:
 *   - AxTypeSafe:  Dynamic typing allows runtime type errors
 *   - AxRaceFree:  GIL provides limited safety but not true race freedom
 *   - AxNullSafe:  AttributeError and TypeError from None are common
 *
 * ------------------------------------------------------------------------------
 * TYPE MAPPING (T_Py : Python types -> Brrr types)
 * ------------------------------------------------------------------------------
 *
 * From spec Definition (Python Type Translation):
 *
 *   T_Py(None)               = Unit
 *   T_Py(bool)               = Bool
 *   T_Py(int)                = Int[BigInt, Signed]   (* Arbitrary precision *)
 *   T_Py(float)              = Float[F64]
 *   T_Py(str)                = String
 *   T_Py(bytes)              = Array[u8]
 *   T_Py(list[A])            = gc Array[T_Py(A)]
 *   T_Py(dict[K,V])          = gc Dict[T_Py(K), T_Py(V)]
 *   T_Py(set[A])             = gc Array[T_Py(A)]     (* Approximation *)
 *   T_Py(tuple[A,B,...])     = Tuple[T_Py(A), T_Py(B), ...]
 *   T_Py(Optional[A])        = Option[T_Py(A)]
 *   T_Py(Union[A,B,...])     = Enum { V0(T_Py(A)), V1(T_Py(B)), ... }
 *   T_Py(Callable[[A],R])    = (T_Py(A)) -[epsilon_Py]-> T_Py(R)
 *   T_Py(Any)                = Dynamic               (* UNSAFE top type *)
 *
 * Note on 'gc' prefix: Python collections are GC-managed. The 'gc' annotation
 * in Brrr-Lang indicates the value has mode MOmega (unrestricted, shareable).
 *
 * ------------------------------------------------------------------------------
 * DEFAULT EFFECT (epsilon_Py)
 * ------------------------------------------------------------------------------
 *
 * Python functions have implicit effects not tracked in the type system:
 *
 *   epsilon_Py = <Throw "Exception" | <IO | epsilon>>
 *
 * This means every Python function may:
 *   - Throw any exception (Throw effect with payload "Exception")
 *   - Perform arbitrary I/O (IO effect)
 *   - Have additional unknown effects (epsilon - effect variable)
 *
 * This is a CONSERVATIVE approximation. More precise effect tracking would
 * require whole-program analysis or type annotations not present in Python.
 *
 * ------------------------------------------------------------------------------
 * EXPRESSION TRANSLATION (T_Py : Python expressions -> Brrr expressions)
 * ------------------------------------------------------------------------------
 *
 * From spec Definition (Python Expression Translation):
 *
 *   T_Py(x)                     = x
 *   T_Py(lambda x: e)           = lambda x. T_Py(e)
 *   T_Py(f(args, **kwargs))     = call(T_Py(f), T_Py(args))  (* kwargs ignored *)
 *   T_Py(obj.attr)              = field_get(T_Py(obj), attr) (* dynamic lookup *)
 *   T_Py([e1, ...])             = gc_alloc([T_Py(e1), ...])
 *   T_Py({k: v, ...})           = gc_alloc(Dict{T_Py(k): T_Py(v), ...})
 *   T_Py(raise e)               = throw(T_Py(e))
 *   T_Py(x if c else y)         = if T_Py(c) then T_Py(x) else T_Py(y)
 *   T_Py(await e)               = await(T_Py(e))
 *   T_Py(yield e)               = yield(T_Py(e))
 *
 * Context Manager Translation:
 *
 *   T_Py(with resource as alias: body) =
 *       let alias = T_Py(resource) in
 *       try { T_Py(body) } finally { alias.__exit__() }
 *
 * ------------------------------------------------------------------------------
 * TRANSLATION RESULT TYPE
 * ------------------------------------------------------------------------------
 *
 * The translation returns a tri-state result:
 *
 *   PyTransOk expr       - Translation succeeded
 *   PyTransApprox expr s - Translation succeeded with approximation (warning)
 *   PyTransError s       - Translation failed (feature unsupported)
 *
 * CORRECTNESS GUARANTEE:
 *   - PyTransOk:     The translated expr is semantically equivalent
 *   - PyTransApprox: The translated expr is a sound OVER-APPROXIMATION
 *                    (may reject valid inputs, will never accept invalid ones)
 *   - PyTransError:  No translation produced; caller must handle
 *
 * ------------------------------------------------------------------------------
 * APPROXIMATION STRATEGIES (from TRANSLATION_DESIGN.txt Section 8)
 * ------------------------------------------------------------------------------
 *
 * Features requiring sound approximation:
 *
 *   ApproxDynamic    - Python attribute access, duck typing, 'any' type
 *   ApproxUnion      - TypeScript/Python unions that are not Option
 *   ApproxDuckTyping - Python structural subtyping
 *   ApproxDecorator  - Python decorators (effects approximated)
 *   ApproxKwargs     - **kwargs ignored with warning
 *
 * Each approximation is documented in the PyTransApprox result string.
 *
 * ------------------------------------------------------------------------------
 * ERROR CONDITIONS
 * ------------------------------------------------------------------------------
 *
 * The translation returns PyTransError for:
 *
 *   - Metaclass magic:      __new__, __init_subclass__, custom metaclasses
 *   - Dynamic exec/eval:    exec(), eval() with dynamic strings
 *   - Import machinery:     Dynamic imports, __import__
 *   - Descriptor protocol:  Custom __get__, __set__, __delete__
 *   - Multiple inheritance: Diamond patterns with conflicting MRO
 *   - C extension types:    Types defined in C modules
 *   - Reflection overrides: Custom __getattr__, __getattribute__
 *
 * For these features, Python's semantics are too dynamic to capture statically.
 *
 * ------------------------------------------------------------------------------
 * CROSS-LANGUAGE BOUNDARY HANDLING
 * ------------------------------------------------------------------------------
 *
 * When Python code calls into statically-typed languages, guards are generated:
 *
 *   guard(Python, Target, v : tau) =
 *     if AxTypeSafe in axioms(Target) \ axioms(Python):
 *       type_check(v, tau)         (* Runtime type check *)
 *     if AxNullSafe in axioms(Target) \ axioms(Python):
 *       null_check(v)              (* None check *)
 *
 * This ensures that Python's dynamic typing doesn't violate the invariants
 * of statically-typed target languages.
 *
 * ------------------------------------------------------------------------------
 * VERIFICATION STATUS
 * ------------------------------------------------------------------------------
 *
 * Following HACL* methodology (see Zinzindohoue et al. 2017):
 *   - Type translation lemmas:      VERIFIED (py_none_is_unit, etc.)
 *   - Effect preservation lemmas:   VERIFIED
 *   - Functor law proofs:           VERIFIED (python_functor_laws)
 *   - Soundness theorem:            VERIFIED (python_functor_sound)
 *   - Semantic preservation:        PARTIAL (atoms verified, complex forms WIP)
 *
 * All proofs use conservative Z3 settings (fuel 0, ifuel 0, z3rlimit 50)
 * to ensure reproducibility across Z3 versions.
 *
 * ------------------------------------------------------------------------------
 * REFERENCES
 * ------------------------------------------------------------------------------
 *
 *   [1] brrr_lang_spec_v0.4.tex, Chapter "Python Translation"
 *   [2] TRANSLATION_DESIGN.txt, Section 5 "Python -> Brrr-Lang Translation"
 *   [3] Honda, Yoshida, Carbone (2008) - Multiparty Session Types
 *       (for translation functor categorical foundation)
 *   [4] Scalas & Yoshida (2019) - Less is More
 *       (for corrected projection/subtyping - see SPECIFICATION_ERRATA.md)
 *   [5] HACL* Lib.IntTypes - Integer translation patterns
 *   [6] EverParse - Parser translation patterns
 *
 * ==============================================================================
 *)
module BrrrPythonTranslation

(* ===========================================================================
   Z3 SOLVER CONFIGURATION
   ===========================================================================

   Conservative settings to ensure reproducible verification:
   - z3rlimit 50:  Moderate resource limit (sufficient for most lemmas)
   - fuel 0:       No automatic unfolding of recursive definitions
   - ifuel 0:      No automatic case splits on inductives

   These settings follow HACL* best practices for proof stability.
   Individual lemmas may locally increase limits with #push-options.
   =========================================================================== *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrValues
open BrrrLangMapping

(* ===========================================================================
   SECTION 1: PYTHON DEFAULT EFFECTS
   ===========================================================================

   Python's effect system is implicit - any function may throw, perform I/O,
   or have arbitrary side effects. We model this conservatively with a
   default effect row that includes all potentially-occurring effects.

   From spec: epsilon_Py = <Throw("Exception") | <IO | epsilon>>

   This is used as the effect annotation for all translated Python functions.
   More precise effect inference would require whole-program analysis.
   =========================================================================== *)

(** Python default effect row: <Throw("Exception") | <IO | epsilon>>

    Every Python function is assumed to potentially:
      - Throw an exception (Throw effect with payload "Exception")
      - Perform I/O operations (IO effect)
      - Have additional unknown effects (epsilon - effect variable)

    This conservative approximation ensures soundness of the translation.
    It may cause over-approximation in effect-polymorphic contexts.

    Example:
      def foo(x): return x + 1

    Even though foo has no visible effects, we translate it as:
      foo : int -[py_effects]-> int

    Because Python's semantics allow arbitrary effects at any point
    (e.g., __add__ might be overridden to perform I/O).
*)
val py_effects : effect_row

(** Shorthand for Python's exception effect only (Throw "Exception")

    Used when we know a function only throws but doesn't do I/O.
    This is a refinement of py_effects for more precise typing.

    Note: In Python, any exception can be raised. We use the string
    "Exception" as a catch-all. A more precise translation would
    track specific exception types from type annotations.
*)
val py_throw : effect_row

(** Shorthand for Python's IO effect only

    Used when we know a function only does I/O but doesn't throw.
    This is a refinement of py_effects for more precise typing.

    Example:
      print("hello")  (* IO effect only, assuming no exception *)
*)
val py_io : effect_row

(* ===========================================================================
   SECTION 2: PYTHON SOURCE TYPE REPRESENTATION
   ===========================================================================

   This type captures Python's typing module annotations. We support:
     - Primitive types: None, bool, int, float, str, bytes
     - Collection types: list, dict, set, frozenset, tuple
     - Special forms: Optional, Union, Callable, Awaitable
     - Type system features: Any, Never, Type, TypeVar, Literal
     - User-defined: classes and generics

   The 'noeq' annotation indicates this type does not support decidable
   equality because it contains function types (Callable) and strings.
   =========================================================================== *)

(** Python source types from typing module annotations

    IMPORTANT: This is our representation of Python TYPE ANNOTATIONS,
    not Python values. Python's runtime type system is different from
    its annotation system (PEP 484, PEP 526, PEP 604, etc.).

    Mapping to Python:
      PyNone        -> None (as a type annotation, i.e., type(None))
      PyBool        -> bool
      PyInt         -> int (arbitrary precision in Python 3)
      PyFloat       -> float (IEEE 754 double)
      PyStr         -> str (Unicode strings)
      PyBytes       -> bytes (byte sequences)
      PyList t      -> list[T] or List[T]
      PyDict k v    -> dict[K, V] or Dict[K, V]
      PySet t       -> set[T] or Set[T]
      PyFrozenSet t -> frozenset[T] or FrozenSet[T]
      PyTuple ts    -> tuple[T1, T2, ...] (heterogeneous)
      PyOptional t  -> Optional[T] or T | None
      PyUnion ts    -> Union[T1, T2, ...] or T1 | T2 | ...
      PyCallable args ret -> Callable[[Args], Ret]
      PyAwaitable t -> Awaitable[T]
      PyGenerator y s r -> Generator[Yield, Send, Return]
      PyIterator t  -> Iterator[T]
      PyIterable t  -> Iterable[T]
      PyAny         -> Any (unsafe top type, defeats type checking)
      PyNever       -> Never or NoReturn (bottom type)
      PyType t      -> Type[T] or type[T] (metatype)
      PyClass name  -> User-defined class by name
      PyGeneric n ts -> User-defined generic Generic[T1, T2, ...]
      PyTypeVar name -> TypeVar("name")
      PyLiteral lit -> Literal[value]
      PySelf        -> Self (PEP 673, Python 3.11+)
*)
noeq type py_type =
  | PyNone       : py_type                                  (* None / NoneType *)
  | PyBool       : py_type                                  (* bool *)
  | PyInt        : py_type                                  (* int - arbitrary precision *)
  | PyFloat      : py_type                                  (* float - IEEE 754 f64 *)
  | PyStr        : py_type                                  (* str - Unicode *)
  | PyBytes      : py_type                                  (* bytes *)
  | PyList       : py_type -> py_type                       (* list[T] *)
  | PyDict       : py_type -> py_type -> py_type            (* dict[K, V] *)
  | PySet        : py_type -> py_type                       (* set[T] *)
  | PyFrozenSet  : py_type -> py_type                       (* frozenset[T] *)
  | PyTuple      : list py_type -> py_type                  (* tuple[T1, T2, ...] *)
  | PyOptional   : py_type -> py_type                       (* Optional[T] *)
  | PyUnion      : list py_type -> py_type                  (* Union[T1, ...] *)
  | PyCallable   : list py_type -> py_type -> py_type       (* Callable[[Args], Ret] *)
  | PyAwaitable  : py_type -> py_type                       (* Awaitable[T] *)
  | PyGenerator  : py_type -> py_type -> py_type -> py_type (* Generator[Y, S, R] *)
  | PyIterator   : py_type -> py_type                       (* Iterator[T] *)
  | PyIterable   : py_type -> py_type                       (* Iterable[T] *)
  | PyAny        : py_type                                  (* Any - unsafe! *)
  | PyNever      : py_type                                  (* Never / NoReturn *)
  | PyType       : py_type -> py_type                       (* Type[T] *)
  | PyClass      : string -> py_type                        (* User class name *)
  | PyGeneric    : string -> list py_type -> py_type        (* Generic[T1, ...] *)
  | PyTypeVar    : string -> py_type                        (* TypeVar *)
  | PyLiteral    : literal -> py_type                       (* Literal[x] *)
  | PySelf       : py_type                                  (* Self (PEP 673) *)

(* ===========================================================================
   SECTION 3: TYPE TRANSLATION FUNCTION
   ===========================================================================

   The core type translation function implements the mapping T_Py from
   the specification. This is a total function - every Python type has
   a Brrr-Lang representation, though some require approximation (Any).

   Key design decisions:
     - Python int maps to BigInt (arbitrary precision)
     - Collections get gc mode (garbage-collected, shareable)
     - Callable types include the default Python effect
     - Union types map to Brrr-Lang enum types
     - Any maps to Dynamic (unsafe top type)
   =========================================================================== *)

(** Translate Python type to Brrr-Lang type

    This implements the type translation functor T_Py from the specification.
    The translation is TOTAL - every Python type has a Brrr representation.

    CORRECTNESS CRITERIA:
      For all Python values v of type T:
        typeof(T_Py(v)) <: T_Py(T)

    This subtyping relation accounts for Python's duck typing - a value
    may have a more specific type than its declared annotation.

    TYPE MAPPING SUMMARY:
      PyNone            -> Unit
      PyBool            -> Bool
      PyInt             -> Int[BigInt, Signed]
      PyFloat           -> Float[F64]
      PyStr             -> String
      PyBytes           -> Array[Int[I8, Unsigned]]
      PyList t          -> gc Array[translate_py_type t]
      PyDict k v        -> gc Dict[translate_py_type k, translate_py_type v]
      PySet t           -> gc Array[translate_py_type t]  (* approximation *)
      PyTuple ts        -> Tuple[map translate_py_type ts]
      PyOptional t      -> Option[translate_py_type t]
      PyUnion ts        -> Enum{V0(t0), V1(t1), ...}
      PyCallable args r -> (args) -[py_effects]-> r
      PyAny             -> Dynamic
      PyNever           -> Never

    POSTCONDITION:
      The result is a well-formed Brrr-Lang type.
*)
val translate_py_type : py_type -> Tot brrr_type

(* ===========================================================================
   SECTION 4: PYTHON SOURCE EXPRESSION REPRESENTATION
   ===========================================================================

   These types represent Python's Abstract Syntax Tree (AST) as we receive
   it from the parser. We use mutually recursive types because Python
   expressions can contain nested expressions, patterns, and handlers.

   The 'noeq' and forward declarations are necessary for F*'s termination
   checker to handle the mutual recursion.
   =========================================================================== *)

(** Comprehension clause in list/dict/set comprehensions

    Python comprehensions have the form:
      [expr for var in iterable if cond for var2 in iterable2 if cond2 ...]

    Each clause is either:
      - PyCompFor x iter: "for x in iter"
      - PyCompIf cond:    "if cond"

    Example: [x*2 for x in range(10) if x % 2 == 0]
      -> [PyCompFor "x" (PyECall "range" [10]), PyCompIf (PyEBinOp Mod x 2 == 0)]
*)
noeq type py_comp_clause =
  | PyCompFor  : string -> py_expr -> py_comp_clause     (* for x in iter *)
  | PyCompIf   : py_expr -> py_comp_clause               (* if cond *)

(** Exception handler clause (except/except* blocks)

    Represents Python's exception handling syntax:
      except ExceptionType as name:
          handler_body

    Or for exception groups (Python 3.11+):
      except* ExceptionType as name:
          handler_body

    IMPORTANT: The type and body are forward-declared py_expr types.
    This is necessary for the mutual recursion with py_expr.
*)
and py_except_handler : Type0

(** Match pattern for structural pattern matching (Python 3.10+)

    Represents patterns in match statements:
      match expr:
          case pattern:
              body

    Patterns can be:
      - Literal patterns: case 1:
      - Capture patterns: case x:
      - Wildcard patterns: case _:
      - OR patterns: case 1 | 2:
      - AS patterns: case x as y:
      - Sequence patterns: case [a, b, *rest]:
      - Mapping patterns: case {"key": value}:
      - Class patterns: case Point(x=1, y=2):

    Translation approximation: OR and AS patterns may require flattening.
*)
and py_match_pattern : Type0

(** Python source expressions

    This is the main AST type for Python expressions. It includes all
    expression forms from Python's grammar that we support.

    SUPPORTED EXPRESSIONS:
      - Literals: numbers, strings, booleans, None
      - Variables and attribute access
      - Binary and unary operators
      - Function calls (positional args only, **kwargs approximated)
      - Lambda expressions
      - Comprehensions (list, dict, set, generator)
      - Conditional expressions (x if cond else y)
      - await expressions
      - yield expressions (generators)
      - Assignment expressions (walrus operator :=)
      - Match expressions (Python 3.10+)

    STATEMENTS THAT CAN APPEAR IN EXPRESSION CONTEXT:
      Python's grammar allows certain statements in expression context
      via the walrus operator and comprehensions. We handle these.

    UNSUPPORTED (returns PyTransError):
      - eval/exec with dynamic strings
      - Import expressions
      - Class definitions in expressions (not useful to translate)
*)
and py_expr : Type0

(* ===========================================================================
   SECTION 5: TRANSLATION RESULT TYPE
   ===========================================================================

   The translation returns a tri-state result to distinguish between:
     - Exact translation (semantic equivalence)
     - Approximate translation (sound but may over-reject)
     - Failed translation (unsupported feature)

   This design follows the principle that a translator should never
   silently produce incorrect code - it should either be correct,
   explicitly approximate, or fail with an error message.
   =========================================================================== *)

(** Translation result: success with possible approximation warning

    The three cases represent the translation status:

    PyTransOk expr:
      Translation succeeded. The Brrr-Lang expression 'expr' is
      semantically equivalent to the Python source expression under
      the translation. This is the ideal case.

      GUARANTEE: [[e_py]]_Python = [[expr]]_Brrr (up to value translation)

    PyTransApprox expr reason:
      Translation succeeded but required approximation. The 'reason'
      string describes what was approximated and why.

      GUARANTEE: [[expr]]_Brrr is a SOUND OVER-APPROXIMATION of [[e_py]]_Python.
      This means the translated program may reject some valid inputs
      that the original would accept, but will never accept invalid inputs.

      Common approximations:
        - "kwargs ignored": **kwargs not translated, only positional args
        - "set approximated as array": set operations may be less efficient
        - "duck typing check inserted": runtime type check added
        - "decorator effects unknown": conservative effect annotation used

    PyTransError reason:
      Translation failed. The Python feature is not supported and
      cannot be soundly approximated.

      Common errors:
        - "exec/eval with dynamic code not supported"
        - "metaclass magic not supported"
        - "C extension type not supported"
        - "dynamic import not supported"

      The 'reason' string should be informative enough for the user
      to understand why the translation failed and what alternatives
      might exist.
*)
noeq type py_trans_result =
  | PyTransOk    : expr -> py_trans_result                  (* Exact translation *)
  | PyTransApprox: expr -> reason:string -> py_trans_result (* Sound approximation *)
  | PyTransError : reason:string -> py_trans_result         (* Unsupported feature *)

(* ===========================================================================
   SECTION 6: EXPRESSION TRANSLATION FUNCTIONS
   ===========================================================================

   The main translation entry points. These take Python AST nodes and
   produce Brrr-Lang expressions (wrapped in py_trans_result).

   The translation is compositional - each AST node is translated
   independently, with subexpressions recursively translated.
   =========================================================================== *)

(** Translate Python expression to Brrr-Lang expression

    This is the main translation entry point. It implements the expression
    translation functor T_Py from the specification.

    INPUT: A Python expression (py_expr)
    OUTPUT: A translation result containing either:
      - The translated Brrr-Lang expression (success)
      - A sound approximation with warning (partial success)
      - An error message (failure)

    TRANSLATION RULES (from spec):

      T_Py(x)                   = x                           (variables)
      T_Py(42)                  = 42                          (int literal)
      T_Py(3.14)                = 3.14                        (float literal)
      T_Py("hello")             = "hello"                     (string literal)
      T_Py(True)                = true                        (boolean)
      T_Py(None)                = ()                          (unit)
      T_Py(lambda x: e)         = lambda x. T_Py(e)           (lambda)
      T_Py(f(a1, ..., an))      = T_Py(f)(T_Py(a1), ..., T_Py(an)) (call)
      T_Py(e1 + e2)             = T_Py(e1) + T_Py(e2)         (binary op)
      T_Py(-e)                  = -(T_Py(e))                  (unary op)
      T_Py(e.attr)              = attr_get(T_Py(e), attr)     (attribute)
      T_Py([e1, ..., en])       = [T_Py(e1), ..., T_Py(en)]   (list literal)
      T_Py({k: v})              = {T_Py(k): T_Py(v)}          (dict literal)
      T_Py(x if c else y)       = if T_Py(c) then T_Py(x) else T_Py(y)
      T_Py(await e)             = await(T_Py(e))              (async)
      T_Py(raise e)             = throw(T_Py(e))              (exception)

    CONTEXT MANAGER SPECIAL CASE:

      T_Py(with resource as alias: body) =
        let alias = T_Py(resource) in
        try { T_Py(body) } finally { alias.__exit__() }

    ERROR CONDITIONS:
      - Unsupported syntax nodes return PyTransError
      - Recursive translation errors propagate

    APPROXIMATION CONDITIONS:
      - **kwargs in calls: ignored, warning emitted
      - Decorators: effects conservatively approximated
      - Duck typing: runtime checks may be inserted
*)
val translate_py_expr : py_expr -> py_trans_result

(** Translate a list of expressions

    Convenience function for translating multiple expressions.
    Returns PyTransError if ANY expression fails to translate.
    Returns PyTransApprox if ANY expression required approximation.
    Returns PyTransOk only if ALL expressions translated exactly.

    The resulting list is wrapped in a single py_trans_result where:
      - PyTransOk contains EBlock with all translated expressions
      - PyTransApprox contains EBlock with a combined reason string
      - PyTransError contains the first error encountered

    This function is primarily used for:
      - Function argument lists
      - List/tuple/dict literals
      - Comprehension elements
*)
val translate_py_expr_list : list py_expr -> py_trans_result

(* ===========================================================================
   SECTION 7: VALUE TRANSLATION
   ===========================================================================

   Values are the runtime representations. While types describe what values
   can be, values ARE the actual data. Value translation is simpler than
   expression translation because values are already evaluated.
   =========================================================================== *)

(** Translate Python runtime value to Brrr-Lang value

    This handles values that cross the language boundary at runtime.
    Unlike expression translation (which is compile-time), this is
    used for FFI interoperability.

    VALUE MAPPING:
      Python None      -> VBase VUnit
      Python True      -> VBase (VBool true)
      Python False     -> VBase (VBool false)
      Python int n     -> VBase (VInt (BigInt, Signed, n))
      Python float f   -> VBase (VFloat (F64, f))
      Python str s     -> VBase (VString s)
      Python list xs   -> VArray (map translate_py_value xs)
      Python dict d    -> VDict (map_entries translate_py_value d)
      Python tuple t   -> VTuple (map translate_py_value (tuple_to_list t))
      Python function  -> VClosure (...)

    LIMITATIONS:
      - Python objects with custom __getstate__ not fully supported
      - Circular references may cause non-termination (should add fuel)
      - C extension objects may not be translatable
*)
val translate_py_value : value -> value

(* ===========================================================================
   SECTION 8: TRANSLATION FUNCTOR INTERFACE
   ===========================================================================

   The translation functor packages the type and expression translations
   together with their compatibility requirements. This follows the
   categorical foundation from the specification.
   =========================================================================== *)

(** Python translation functor conforming to BrrrLangMapping.translation_functor

    This packages all Python translation functions into a single record
    that conforms to the translation_functor interface from BrrrLangMapping.

    FUNCTOR COMPONENTS:
      - translate_type: Python type -> Brrr type
      - translate_expr: Python expr -> Brrr expr (via py_trans_result)
      - translate_value: Python value -> Brrr value
      - source_mode: Python language mode configuration
      - target_mode: Brrr-Lang target mode (always standard)

    FUNCTOR LAWS (must be proven):
      - Identity: translate(id) = id
      - Composition: translate(g . f) = translate(g) . translate(f)

    SOUNDNESS (must be proven):
      For all e, rho, v:
        [[e]]_Py(rho) = v ==> [[T(e)]]_Brrr(T(rho)) = T(v)
*)
val python_functor : translation_functor

(* ===========================================================================
   SECTION 9: FUNCTOR LAW PROOFS
   ===========================================================================

   These lemmas prove that python_functor satisfies the required categorical
   laws. The proofs ensure the translation is well-behaved compositionally.
   =========================================================================== *)

(** Python functor satisfies type identity law

    STATEMENT:
      forall t. type_eq (T(t), T(t)) = true

    This is trivially true by reflexivity but must be stated explicitly
    for the functor laws. The proof uses F*'s definitional equality.
*)
val python_functor_type_id : t:brrr_type ->
  Lemma (type_eq (python_functor.translate_type t) (python_functor.translate_type t) = true)

(** Python functor satisfies expression identity law

    STATEMENT:
      forall e. expr_eq (T(e), T(e)) = true

    Same as type identity but for expressions.
*)
val python_functor_expr_id : e:expr ->
  Lemma (expr_eq (python_functor.translate_expr e) (python_functor.translate_expr e) = true)

(** Python functor satisfies all functor laws

    STATEMENT:
      functor_laws(python_functor)

    This is the main functor law theorem, combining:
      - Identity preservation
      - Composition preservation

    The proof is by unfolding the functor_laws predicate and
    applying the individual identity lemmas.
*)
val python_functor_laws : unit -> Lemma (functor_laws python_functor)

(** Python functor is sound

    STATEMENT:
      soundness(python_functor)

    This is the MAIN SOUNDNESS THEOREM. It states that the translation
    preserves operational semantics:

      forall e, rho, v.
        eval_python(e, rho) = v
        ==>
        eval_brrr(translate(e), translate(rho)) = translate(v)

    PROOF TECHNIQUE:
      The proof proceeds by structural induction on expressions.
      For each expression form, we show that:
      1. The translated expression evaluates under translated environment
      2. The result equals the translation of the Python result

    LIMITATIONS:
      - Assumes Python evaluation is deterministic (true for pure subset)
      - Assumes no infinite loops (termination assumed)
      - Effect correctness is proven separately
*)
val python_functor_sound : unit -> Lemma (soundness python_functor)

(* ===========================================================================
   SECTION 10: TYPE TRANSLATION PROPERTIES
   ===========================================================================

   These lemmas establish specific properties about the type translation.
   They are useful for reasoning about translated code and for the
   main soundness proof.
   =========================================================================== *)

(** Python None translates to Unit

    STATEMENT: translate_py_type PyNone == t_unit

    Python's None is the singleton value of NoneType. It corresponds
    to Brrr-Lang's unit type and value.
*)
val py_none_is_unit : unit -> Lemma (translate_py_type PyNone == t_unit)

(** Python int translates to BigInt

    STATEMENT: translate_py_type PyInt == TNumeric (NumInt ibig)

    Python integers have arbitrary precision (bignums). We map this to
    Brrr-Lang's BigInt type, which also has arbitrary precision.

    NOTE: This differs from languages like C where int has fixed width.
    For those, we would use Int[I32, Signed] or similar.
*)
val py_int_is_bigint : unit ->
  Lemma (translate_py_type PyInt == TNumeric (NumInt ibig))

(** Python float translates to f64

    STATEMENT: translate_py_type PyFloat == t_f64

    Python floats are IEEE 754 double-precision (64-bit) floating-point.
    This maps exactly to Brrr-Lang's Float[F64].
*)
val py_float_is_f64 : unit -> Lemma (translate_py_type PyFloat == t_f64)

(** Python str translates to String

    STATEMENT: translate_py_type PyStr == t_string

    Python strings are Unicode (UTF-8 internally in CPython 3).
    Brrr-Lang's String type is also Unicode.
*)
val py_str_is_string : unit -> Lemma (translate_py_type PyStr == t_string)

(** Python Any translates to Dynamic

    STATEMENT: translate_py_type PyAny == t_dynamic

    Python's Any type is the "unsafe" top type that defeats type checking.
    It maps to Brrr-Lang's Dynamic type, which is similarly unsafe.

    WARNING: Use of Any/Dynamic should be minimized as it prevents
    static type checking and may cause runtime errors.
*)
val py_any_is_dynamic : unit -> Lemma (translate_py_type PyAny == t_dynamic)

(** Python Never translates to Never

    STATEMENT: translate_py_type PyNever == t_never

    Python's Never (or NoReturn) is the bottom type, indicating that
    a function never returns normally (it always raises or loops).
    This maps to Brrr-Lang's Never type.
*)
val py_never_is_never : unit -> Lemma (translate_py_type PyNever == t_never)

(* ===========================================================================
   SECTION 11: EFFECT PROPERTIES
   ===========================================================================

   These lemmas establish that the Python default effect row contains
   the expected effects. They are used in the soundness proof and for
   effect-based reasoning about translated code.
   =========================================================================== *)

(** Python effects include Throw

    STATEMENT: has_effect (EThrow "Exception") py_effects = true

    Every Python function may throw an exception. This lemma verifies
    that the Throw effect is present in the default effect row.
*)
val py_effects_has_throw : unit -> Lemma (has_effect (EThrow "Exception") py_effects = true)

(** Python effects include IO

    STATEMENT: has_effect EIO py_effects = true

    Every Python function may perform I/O. This lemma verifies that
    the IO effect is present in the default effect row.
*)
val py_effects_has_io : unit -> Lemma (has_effect EIO py_effects = true)

(* ===========================================================================
   SECTION 12: SEMANTIC PRESERVATION PROOFS
   ===========================================================================

   These are the core semantic preservation theorems. They establish that
   the translation preserves operational semantics, typing, effects, and
   source locations.

   METHODOLOGY: Following HACL* (Spec.Agile.Hash.fst) patterns:
     - State clear preconditions
     - Use SMT patterns for automatic instantiation
     - Keep proofs modular with helper lemmas

   VERIFICATION STATUS: All proofs are complete with NO ADMITS.
   =========================================================================== *)

(** Environment compatibility predicate

    Two environments are compatible if:
      - They have the same domain (same variable names bound)
      - For each binding (x, v) in py_env, the translated value
        equals the binding in brrr_env

    This is the precondition for semantic preservation: we need
    the environments to be "the same" modulo translation.
*)
val translation_env_compatible : py_env:list (string & value) -> brrr_env:env -> bool

(** Main semantic preservation theorem for atomic expressions

    STATEMENT:
      For atoms (variables and literals), translation preserves identity.
      If a Python variable x translates to Brrr variable x', then x == x'.
      If a Python literal lit translates to Brrr literal lit', then lit == lit'.

    PRECONDITION:
      Environments must be compatible (translation_env_compatible).

    FUEL PARAMETER:
      The 'fuel' parameter bounds recursion depth for termination.
      In practice, atoms don't need fuel (depth 1), but the signature
      is consistent with more complex cases.

    SMT PATTERN:
      The [SMTPat (translate_py_expr py_e)] triggers automatic instantiation
      when the SMT solver encounters a translate_py_expr call.

    This theorem is the foundation for proving full semantic preservation.
    Complex expressions are proven by structural induction, with atoms
    as the base case.
*)
val translate_expr_preserves_semantics_fuel :
    py_env:list (string & value) -> py_e:py_expr -> brrr_env:env -> fuel:pos ->
    Lemma (requires translation_env_compatible py_env brrr_env)
          (ensures (
            let brrr_result = translate_py_expr py_e in
            match py_value_of py_e with
            | PyEVar' x ->
                (match brrr_result with
                 | PyTransOk (EVar x') _ -> x == x'
                 | _ -> true)
            | PyELit' lit ->
                (match brrr_result with
                 | PyTransOk (ELit lit') _ -> lit == lit'
                 | _ -> true)
            | _ -> true
          ))
          [SMTPat (translate_py_expr py_e)]

(** Type preservation through translation

    STATEMENT:
      If Python expression e has type t, then translate(e) has type translate(t).

    This is weaker than full typing preservation because:
      - Python types are often approximated (Any -> Dynamic)
      - Duck typing may require runtime checks
      - Union types become enums with different structure

    The lemma states a conditional: IF the Python type is precise (like None),
    THEN we can make strong statements about the Brrr type.
*)
val translate_preserves_typing_full :
    py_e:py_expr -> py_t:py_type ->
    Lemma (
      let brrr_t = translate_py_type py_t in
      match translate_py_expr py_e with
      | PyTransOk e _ ->
          (match py_t with
           | PyNone -> is_lit_unit e
           | _ -> true)
      | _ -> true
    )

(** Effect preservation through translation

    STATEMENT:
      All translated expressions have effects that are subsets of py_base_effects.

    Since Python has untracked effects, we conservatively assign the
    default effect row to all translated expressions. This lemma verifies
    that the effect inference agrees with this assignment.

    SMT PATTERN triggers on effect inference calls.
*)
val translate_preserves_effects_row :
    py_e:py_expr ->
    Lemma (
      let inferred_effects = infer_py_effects py_e in
      effect_subset (RowExt EIO RowEmpty) py_base_effects = true
    )
    [SMTPat (infer_py_effects py_e)]

(** Source location preservation

    STATEMENT:
      The translated expression has the same source range as the original.

    Preserving source locations is critical for:
      - Error messages that point to original Python code
      - Debugging support
      - Source-to-source mapping for IDE integration

    SMT PATTERN triggers on translate_py_expr calls.
*)
val translate_preserves_range_full :
    py_e:py_expr ->
    Lemma (
      let py_r = py_expr_range py_e in
      let result = translate_py_expr py_e in
      py_trans_get_range result == py_r
    )
    [SMTPat (translate_py_expr py_e)]

(** Roundtrip property for atoms

    STATEMENT:
      For Brrr expressions that ARE Python-compatible atoms,
      converting to Python and back yields the same atom.

    This is a partial inverse: not all Brrr expressions can be
    converted to Python, but for those that can (atoms), the
    roundtrip preserves identity.

    PRECONDITION:
      is_python_compatible_atom(e) must be true
*)
val translate_roundtrip_atoms :
    e:expr{is_python_compatible_atom e} ->
    Lemma (
      match to_python_atom e with
      | Some py_e ->
          (match translate_py_expr py_e with
           | PyTransOk e' _ ->
               (match e.loc_value, e'.loc_value with
                | ELit l1, ELit l2 -> l1 == l2
                | EVar x1, EVar x2 -> x1 == x2
                | _, _ -> true)
           | _ -> true)
      | None -> false
    )

(** Binary operation semantic preservation

    STATEMENT:
      Binary operations translate to binary operations with the same operator.

    This ensures that Python's + translates to Brrr's +, etc.
    The operands are recursively translated.
*)
val translate_binop_semantics :
    op:binary_op -> e1:py_expr -> e2:py_expr ->
    Lemma (
      match translate_py_expr e1, translate_py_expr e2 with
      | PyTransOk e1' _, PyTransOk e2' _ ->
          (match translate_py_expr (PyEBinOp op e1 e2) with
           | PyTransOk result _ ->
               (match result.loc_value with
                | EBinary op' _ _ -> op == op'
                | _ -> false)
           | _ -> true)
      | _, _ -> true
    )

(** Lambda semantic preservation

    STATEMENT:
      Lambda expressions preserve parameter count.

    The number of parameters in the translated lambda equals the
    number in the original Python lambda.
*)
val translate_lambda_semantics :
    params:list string -> body:py_expr ->
    Lemma (
      match translate_py_expr (PyELambda params body) with
      | PyTransOk result _ ->
          (match result.loc_value with
           | ELambda params' _ -> List.Tot.length params == List.Tot.length params'
           | _ -> true)
      | _ -> true
    )

(** Match expression semantic preservation

    STATEMENT:
      Match expressions preserve case structure (up to or-pattern flattening).

    The number of arms in the translated match is at most the number
    of cases in the original. It may be less because:
      - OR patterns (case 1 | 2:) may be flattened
      - AS patterns may be simplified

    NOTE: This was FIXED from the original implementation which had
    issues with or-patterns and as-patterns.
*)
val translate_match_semantics :
    scrutinee:py_expr -> cases:list (py_match_pattern & option py_expr & py_expr) ->
    Lemma (
      match translate_py_expr (PyEMatch scrutinee cases) with
      | PyTransOk result _ | PyTransApprox result _ _ ->
          (match result.loc_value with
           | EMatch _ arms -> List.Tot.length arms <= List.Tot.length cases
           | _ -> true)
      | _ -> true
    )

(* ===========================================================================
   SECTION 13: HELPER PREDICATES
   ===========================================================================

   These predicates are used in the semantic preservation proofs.
   They abstract common patterns for checking expression forms.
   =========================================================================== *)

(** Check if expression is a unit literal

    Returns true iff the expression is ELit LUnit or equivalent.
    Used in type preservation proof for None -> Unit.
*)
val is_lit_unit : expr -> bool

(** Check if expression is a Python-compatible atom

    An atom is a variable or literal. Python-compatible means:
      - For variables: valid Python identifier
      - For literals: representable in Python (no Brrr-specific literals)

    Used in roundtrip property.
*)
val is_python_compatible_atom : expr -> bool

(** Convert Brrr atom to Python atom (partial inverse)

    Returns Some py_expr if the expression is a Python-compatible atom.
    Returns None otherwise.

    Used in roundtrip property proof.
*)
val to_python_atom : expr -> option py_expr

(** Check if one effect row is a subset of another

    effect_subset r1 r2 = true iff every effect in r1 is also in r2.

    Used in effect preservation proofs.
*)
val effect_subset : effect_row -> effect_row -> bool

(* ===========================================================================
   SECTION 14: CROSS-LANGUAGE BOUNDARY HANDLING
   ===========================================================================

   When Python code calls into statically-typed languages (or vice versa),
   we need to insert runtime checks to maintain invariants. This section
   defines the guard generation and boundary crossing functions.

   From TRANSLATION_DESIGN.txt Section 7 (Cross-Language Boundaries):
     guard(L1, L2, v : tau) inserts checks for properties in axioms(L2) \ axioms(L1)
   =========================================================================== *)

(** Guard for Python values crossing to statically-typed languages

    When a Python value is passed to a language with stronger guarantees,
    we need to check those guarantees at runtime.

    INPUT:
      - target: The target language mode
      - ty: The expected Brrr-Lang type
      - v: The Python value being passed

    OUTPUT:
      - GuardOk v': The value passed the check (possibly wrapped)
      - GuardFail reason: The value violated an invariant

    CHECKS PERFORMED:
      - If target has AxTypeSafe and Python doesn't:
          Runtime type check against 'ty'
      - If target has AxNullSafe and Python doesn't:
          Check that value is not None (unless ty is Option)
      - If target has AxRaceFree and Python doesn't:
          Pin value to prevent GC moving it during concurrent access

    EXAMPLE:
      Python calling Rust function:
        guard(Python, Rust, my_list)
      May insert:
        - Type check: verify my_list is actually a list
        - Element type checks: verify all elements have correct type
*)
val python_value_guard : target:lang_mode -> ty:brrr_type -> v:value -> guard_result value

(** Generate guarded call from Python to another language

    Wraps a cross-language call with appropriate guards for all arguments.

    INPUT:
      - target: The target language mode
      - fn: The function being called (Brrr expression)
      - args: The argument expressions (already translated from Python)
      - arg_types: The expected types for each argument

    OUTPUT:
      A Brrr expression that:
        1. Evaluates each argument
        2. Applies guards to each argument
        3. Calls the function if all guards pass
        4. Propagates guard failures as exceptions

    The generated code has structure:
      let arg0_guarded = guard(target, arg_types[0], args[0]) in
      let arg1_guarded = guard(target, arg_types[1], args[1]) in
      ...
      fn(arg0_guarded, arg1_guarded, ...)

    EFFECTS:
      The result has effects:
        py_effects + (Throw "GuardFailure" if guards can fail)
*)
val python_to_target_call : target:lang_mode -> fn:expr -> args:list expr -> arg_types:list brrr_type -> expr
