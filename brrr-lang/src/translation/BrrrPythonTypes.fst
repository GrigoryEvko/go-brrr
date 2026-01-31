(**
 * Brrr-Lang Python Types - Single Source of Truth
 *
 * =============================================================================
 * MODULE OVERVIEW
 * =============================================================================
 *
 * This module provides the canonical Python type definitions for the Brrr-Lang
 * translation layer. It serves as the single source of truth for all Python
 * type representations across the codebase.
 *
 * Design Principles:
 *   1. Single Source of Truth: All modules requiring Python type representations
 *      MUST import from here. No duplicate definitions allowed.
 *   2. Complete Coverage: Covers all Python typing module constructs including
 *      primitives, collections, generics, callables, and special types.
 *   3. Source Location Tracking: Every AST node carries source position for
 *      precise error reporting during translation and verification.
 *
 * =============================================================================
 * PYTHON TYPE SYSTEM BACKGROUND
 * =============================================================================
 *
 * Python's type system (as of Python 3.10+) is a gradual type system defined
 * by PEP 484 and implemented in the `typing` module. Key characteristics:
 *
 * 1. Nominal Typing: Types are identified by name, not structure.
 *    class Foo: pass
 *    class Bar: pass
 *    # Foo and Bar are distinct even if structurally identical
 *
 * 2. Gradual Typing: The `Any` type allows mixing typed and untyped code.
 *    x: Any  # Accepts any value, disables type checking for x
 *
 * 3. Structural Subtyping: Protocols (PEP 544) enable duck typing.
 *    class Sized(Protocol):
 *        def __len__(self) -> int: ...
 *    # Any class with __len__ is a Sized
 *
 * 4. Generic Types: Parametric polymorphism via TypeVar and Generic.
 *    T = TypeVar('T')
 *    class Box(Generic[T]):
 *        value: T
 *
 * =============================================================================
 * TRANSLATION TO BRRR-LANG
 * =============================================================================
 *
 * The type mapping T_Py: Python Type -> Brrr-Lang Type follows these rules
 * (from brrr_lang_spec_v0.4.tex Section VI.2 "Python Translation"):
 *
 *   T_Py(None)              = Unit
 *   T_Py(bool)              = Bool
 *   T_Py(int)               = Int[BigInt, Signed]   (* arbitrary precision *)
 *   T_Py(float)             = Float[F64]
 *   T_Py(str)               = String
 *   T_Py(bytes)             = Array[u8]
 *   T_Py(list[A])           = gc Array[T_Py(A)]
 *   T_Py(dict[K,V])         = gc Dict[T_Py(K), T_Py(V)]
 *   T_Py(set[A])            = gc Array[T_Py(A)]     (* approximation *)
 *   T_Py(tuple[A,B,...])    = Tuple[T_Py(A), T_Py(B), ...]
 *   T_Py(Optional[A])       = Option[T_Py(A)]
 *   T_Py(Union[A,B,...])    = Enum { V0(T_Py(A)), V1(T_Py(B)), ... }
 *   T_Py(Callable[[A],R])   = (T_Py(A)) -[epsilon_Py]-> T_Py(R)
 *   T_Py(Any)               = Dynamic
 *
 * Default Effect: epsilon_Py = <Throw "Exception" | <IO | epsilon>>
 *
 * Approximations (see TRANSLATION_DESIGN.txt Section 8):
 *   - kwargs: Keyword arguments are approximated (warning emitted)
 *   - Attribute access: Requires dynamic lookup
 *   - Lambda parameters: Dynamically typed
 *   - Duck typing: Requires runtime checks
 *   - Sets: Mapped to Arrays (ordering may differ)
 *
 * =============================================================================
 * RUNTIME TYPE CHECKING IMPLICATIONS
 * =============================================================================
 *
 * Python type annotations are NOT enforced at runtime by default. This module
 * represents the STATIC type information for verification purposes. Runtime
 * checking considerations:
 *
 * 1. Type Erasure: Generic type parameters are erased at runtime.
 *    list[int] and list[str] are both just `list` at runtime.
 *
 * 2. Runtime Checks: Optional runtime enforcement via:
 *    - beartype: Decorator-based runtime type checking
 *    - typeguard: Runtime type checking for function arguments/returns
 *    - pydantic: Data validation using type annotations
 *
 * 3. Translation Impact: When generating Brrr-Lang code, we may need to:
 *    - Insert runtime type checks for Dynamic types
 *    - Add bounds checks for collections
 *    - Generate error handling for type coercions
 *
 * =============================================================================
 * REFERENCES
 * =============================================================================
 *
 * - brrr_lang_spec_v0.4.tex Part VI Section 2 (Python Translation)
 * - EverParse src/3d/Ast.fst lines 107-111 (with_meta_t pattern)
 * - PEP 484: Type Hints (https://peps.python.org/pep-0484/)
 * - PEP 544: Protocols (https://peps.python.org/pep-0544/)
 * - Python typing module documentation
 * - TRANSLATION_DESIGN.txt Sections 5 and 8
 *
 *)
module BrrrPythonTypes

(** Z3 solver options - conservative settings *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrTypes
open BrrrExpressions  (* Imports pos, range, dummy_range, string_of_range *)

(** ============================================================================
    PYTHON SOURCE LOCATION TYPES
    ============================================================================

    Following EverParse's with_meta_t pattern for source location tracking.
    We reuse the core range/pos types from BrrrExpressions.fst and add
    Python-specific wrappers.

    Reference: EverParse src/3d/Ast.fst lines 107-111:
      noeq type with_meta_t 'a = { v:'a; range:range; comments: comments }
    ============================================================================ *)

(** Python source range - reuse from BrrrExpressions.fst *)
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

    Python type annotations from the typing module.
    These represent the source language types before translation to Brrr-Lang.

    Complete coverage of Python's typing module:
    - Primitive types: None, bool, int, float, str, bytes
    - Collection types: list, dict, set, frozenset, tuple
    - Typing constructs: Optional, Union, Callable, Awaitable, Generator, etc.
    - Special types: Any, Never, Type, TypeVar, Literal, Self

    ==========================================================================
    TYPE CATEGORY OVERVIEW
    ==========================================================================

    1. PRIMITIVE TYPES (PyNone, PyBool, PyInt, PyFloat, PyStr, PyBytes)
       These map directly to Brrr-Lang base types with minimal transformation.
       - PyInt uses arbitrary precision (BigInt) since Python ints are unbounded
       - PyFloat is IEEE 754 double precision (F64)

    2. COLLECTION TYPES (PyList, PyDict, PySet, PyFrozenSet, PyTuple)
       These require GC allocation in Brrr-Lang:
       - PyList -> gc Array[T]      (mutable, ordered)
       - PyDict -> gc Dict[K,V]     (mutable, ordered as of Python 3.7+)
       - PySet  -> gc Array[T]      (approximation: loses set semantics)
       - PyTuple -> Tuple[T1,...,Tn] (immutable, fixed length)

    3. TYPING MODULE CONSTRUCTS (PyOptional, PyUnion, PyCallable, etc.)
       Special types from the typing module:
       - PyOptional[T] = T | None (sugar for Union[T, None])
       - PyUnion[T1,T2,...] translated to Brrr-Lang enums
       - PyCallable[[Args], Ret] translated to arrow types with effects

    4. ASYNC TYPES (PyAwaitable, PyCoroutine, PyAsyncGenerator)
       Async/await constructs that translate to effect-annotated types:
       - PyAwaitable[T] -> Future[T]
       - PyCoroutine[T] -> computation with Async effect
       - PyAsyncGenerator -> streaming effect

    5. SPECIAL TYPES (PyAny, PyNever, PyType, PyTypeVar, PyLiteral, PySelf)
       Advanced typing constructs:
       - PyAny -> Dynamic (disables static checking)
       - PyNever -> NoReturn (function never returns normally)
       - PyTypeVar -> Generic type parameter
       - PyLiteral -> Singleton types (Literal["foo"], Literal[42])

    ==========================================================================
    PYTHON TYPING MODULE VERSION COMPATIBILITY
    ==========================================================================

    This module targets Python 3.10+ features:
    - Union syntax: X | Y (instead of Union[X, Y])
    - ParamSpec and TypeVarTuple (for callable types)
    - Pattern matching type guards (match statement)
    - Self type (PEP 673)

    For older Python versions, some constructs may need runtime imports:
      from typing import Union, Optional, List, Dict  # Python 3.9-
      from __future__ import annotations              # Python 3.7+

    ============================================================================ *)

(** Python source types (from typing module annotations)

    This is the canonical definition used throughout the translation layer.
    Import this type via: open BrrrPythonTypes

    ==========================================================================
    DESIGN RATIONALE: noeq Annotation
    ==========================================================================

    The 'noeq' annotation is required because:
    1. py_type contains recursive list fields (e.g., list py_type in PyTuple)
    2. F* cannot automatically derive decidable equality for recursive types
    3. We provide custom equality functions when needed for comparison

    See FSTAR_REFERENCE.md Section 15 "noeq Usage" for details.

    ==========================================================================
    TRANSLATION RULES BY CONSTRUCTOR
    ==========================================================================

    Each constructor documents:
    - Python syntax correspondence
    - Brrr-Lang translation target
    - Runtime behavior notes
    - Known limitations or approximations
*)
noeq type py_type =

  (* ==========================================================================
     PRIMITIVE TYPES - Direct mappings to base Brrr-Lang types
     ========================================================================== *)

  (** PyNone: Python's None singleton type (NoneType)

      Python syntax: None, type(None)
      Brrr-Lang: T_Py(None) = Unit

      Runtime: Python's None is a singleton; there is exactly one None object.
      Translation: Maps to Brrr-Lang's Unit type with single value ().

      Example usage:
        def returns_none() -> None:
            return None
  *)
  | PyNone     : py_type

  (** PyBool: Python's boolean type

      Python syntax: bool, True, False
      Brrr-Lang: T_Py(bool) = Bool

      Runtime: Python bools are a subtype of int (True=1, False=0).
      Translation: Direct mapping to Brrr-Lang Bool, losing int compatibility.

      Example:
        def is_valid(x: int) -> bool:
            return x > 0
  *)
  | PyBool     : py_type

  (** PyInt: Python's arbitrary precision integer type

      Python syntax: int
      Brrr-Lang: T_Py(int) = Int[BigInt, Signed]

      CRITICAL: Python integers have UNBOUNDED precision. They can represent
      any integer regardless of magnitude. This maps to Brrr-Lang's BigInt,
      not a fixed-width integer type.

      Runtime implications:
      - Memory allocation grows with integer size
      - Operations like factorial(10000) are valid
      - Division always rounds toward negative infinity (floor division)

      Example:
        x: int = 10 ** 1000  # Valid Python, requires BigInt representation

      Note: For interop with C/Rust fixed-width integers, explicit bounds
      checking or overflow handling may be needed during translation.
  *)
  | PyInt      : py_type

  (** PyFloat: Python's floating point type (IEEE 754 double precision)

      Python syntax: float
      Brrr-Lang: T_Py(float) = Float[F64]

      Python floats are always 64-bit IEEE 754 doubles. There is no single-
      precision float in standard Python (numpy.float32 is different).

      Special values: inf, -inf, nan are all valid Python floats.

      Example:
        x: float = 3.14159
        y: float = float('inf')
  *)
  | PyFloat    : py_type

  (** PyStr: Python's Unicode string type

      Python syntax: str
      Brrr-Lang: T_Py(str) = String

      Python 3 strings are sequences of Unicode code points. Internally,
      Python uses a flexible representation (Latin-1, UCS-2, or UCS-4)
      depending on the highest code point in the string.

      Important: Python strings are IMMUTABLE. All string operations
      create new strings.

      Example:
        s: str = "Hello, World!"
        emoji: str = "Hello "  # Unicode is native
  *)
  | PyStr      : py_type

  (** PyBytes: Python's byte sequence type

      Python syntax: bytes
      Brrr-Lang: T_Py(bytes) = Array[u8]

      Bytes is a sequence of integers in range [0, 255]. It is IMMUTABLE.
      For mutable byte sequences, Python uses bytearray (not represented here).

      Example:
        data: bytes = b"Hello"
        raw: bytes = bytes([0x48, 0x65, 0x6c, 0x6c, 0x6f])
  *)
  | PyBytes    : py_type

  (* ==========================================================================
     COLLECTION TYPES - GC-managed container types
     ========================================================================== *)

  (** PyList: Python's mutable, ordered sequence type

      Python syntax: list, list[T], List[T] (typing module)
      Brrr-Lang: T_Py(list[A]) = gc Array[T_Py(A)]

      Lists are:
      - Mutable: append, insert, remove, pop modify in place
      - Ordered: Iteration order matches insertion order
      - Heterogeneous: list[Any] can hold mixed types

      The 'gc' qualifier indicates garbage collection is required.

      Example:
        nums: list[int] = [1, 2, 3]
        mixed: list[int | str] = [1, "two", 3]
  *)
  | PyList     : elem:py_type -> py_type

  (** PyDict: Python's mutable mapping type

      Python syntax: dict, dict[K, V], Dict[K, V]
      Brrr-Lang: T_Py(dict[K,V]) = gc Dict[T_Py(K), T_Py(V)]

      Dicts are:
      - Mutable: Keys can be added, modified, removed
      - Ordered: As of Python 3.7+, iteration order = insertion order
      - Hash-based: Keys must be hashable (immutable)

      Key constraint: In Python, dict keys must be hashable. This includes
      primitives, tuples of hashables, and frozensets. Lists and dicts
      cannot be keys.

      Example:
        config: dict[str, int] = {"timeout": 30, "retries": 3}
  *)
  | PyDict     : key:py_type -> value:py_type -> py_type

  (** PySet: Python's mutable, unordered collection of unique elements

      Python syntax: set, set[T], Set[T]
      Brrr-Lang: T_Py(set[A]) = gc Array[T_Py(A)]  (* APPROXIMATION *)

      APPROXIMATION WARNING: Sets are translated to arrays, which:
      - Loses uniqueness guarantee (caller must deduplicate)
      - Loses O(1) membership testing (becomes O(n))
      - May have different iteration order

      A more precise translation would use a dedicated Set type with
      hash-based operations.

      Example:
        unique: set[int] = {1, 2, 3, 1}  # Results in {1, 2, 3}
  *)
  | PySet      : elem:py_type -> py_type

  (** PyFrozenSet: Python's immutable, unordered collection of unique elements

      Python syntax: frozenset, frozenset[T], FrozenSet[T]
      Brrr-Lang: Same approximation as PySet

      frozenset is hashable (can be a dict key or set element) because
      it is immutable. This property is lost in the Array approximation.

      Example:
        frozen: frozenset[int] = frozenset([1, 2, 3])
  *)
  | PyFrozenSet: elem:py_type -> py_type

  (** PyTuple: Python's immutable, fixed-length sequence

      Python syntax: tuple, tuple[T1, T2, ...], Tuple[T1, T2, ...]
      Brrr-Lang: T_Py(tuple[A,B,...]) = Tuple[T_Py(A), T_Py(B), ...]

      Tuples are:
      - Immutable: Cannot be modified after creation
      - Fixed-length: Length is part of the type (statically known)
      - Heterogeneous: Each position can have a different type

      Special case: tuple[int, ...] means variable-length tuple of ints.
      This is approximated as list[int] in translation.

      Example:
        point: tuple[int, int, int] = (1, 2, 3)
        result: tuple[str, int] = ("success", 200)
  *)
  | PyTuple    : elems:list py_type -> py_type

  (* ==========================================================================
     TYPING MODULE CONSTRUCTS - Generic and composite types
     ========================================================================== *)

  (** PyOptional: Nullable type (T or None)

      Python syntax: Optional[T], T | None
      Brrr-Lang: T_Py(Optional[A]) = Option[T_Py(A)]

      Optional[T] is sugar for Union[T, None]. It indicates a value may
      be absent. This maps directly to Brrr-Lang's Option type.

      Example:
        def find(key: str) -> Optional[int]:
            return None  # or return some_int
  *)
  | PyOptional : inner:py_type -> py_type

  (** PyUnion: Union of multiple types

      Python syntax: Union[T1, T2, ...], T1 | T2 | ...
      Brrr-Lang: T_Py(Union[A,B,...]) = Enum { V0(T_Py(A)), V1(T_Py(B)), ... }

      Unions represent values that can be one of several types. In Brrr-Lang,
      these are translated to tagged enums where each variant wraps one
      of the union member types.

      Runtime: Python uses isinstance() checks to discriminate union members.
      Translation: Generates match expressions on the enum tag.

      Example:
        def process(x: int | str | None) -> bool:
            if isinstance(x, int): return x > 0
            if isinstance(x, str): return len(x) > 0
            return False
  *)
  | PyUnion    : branches:list py_type -> py_type

  (** PyCallable: Function type annotation

      Python syntax: Callable[[Arg1, Arg2, ...], Return]
      Brrr-Lang: T_Py(Callable[[A],R]) = (T_Py(A)) -[epsilon_Py]-> T_Py(R)

      Callable represents any callable object: functions, lambdas, methods,
      classes with __call__, etc.

      Default effect epsilon_Py = <Throw "Exception" | <IO | epsilon>>
      This conservatively assumes any Python function may:
      - Raise an exception
      - Perform IO operations

      Example:
        handler: Callable[[str, int], bool]
        factory: Callable[[], MyClass]
  *)
  | PyCallable : params:list py_type -> ret:py_type -> py_type

  (** PyCallableAnnotated: Enhanced callable with effect annotations

      Extension of PyCallable that tracks:
      - effects: Specific exceptions that may be raised
                 None = conservative (any exception possible)
                 Some ["ValueError", "TypeError"] = only these exceptions
      - is_async: True for async def functions (coroutines)

      This enables more precise effect translation:
      - Known effects -> specific Throw effect in Brrr-Lang
      - async functions -> Async effect annotation

      Example:
        # @raises(ValueError, TypeError)
        async def validate(x: int) -> bool: ...
        # Would be: PyCallableAnnotated [PyInt] PyBool (Some ["ValueError", "TypeError"]) true
  *)
  | PyCallableAnnotated : params:list py_type -> ret:py_type ->
                          effects:option (list string) -> is_async:bool -> py_type

  (** PyAwaitable: Type that can be awaited

      Python syntax: Awaitable[T]
      Brrr-Lang: Translates to Future[T] or async effect

      Awaitable is a protocol that requires __await__ method. This includes:
      - Coroutines (async def functions)
      - Tasks
      - Futures
      - Objects with __await__

      Example:
        async def fetch() -> str: ...
        result: Awaitable[str] = fetch()  # Not yet awaited
  *)
  | PyAwaitable: inner:py_type -> py_type

  (** PyCoroutine: Explicit coroutine type (from async def)

      Python syntax: Coroutine[YieldType, SendType, ReturnType]
      Brrr-Lang: Computation with Async effect

      Unlike plain Awaitable, PyCoroutine explicitly represents the result
      of an async def function. The full signature includes yield/send types
      for advanced coroutine protocols, but commonly only ReturnType matters.

      Example:
        async def fetch_data() -> str:
            await asyncio.sleep(1)
            return "data"
        # Return type: Coroutine[Any, Any, str]
  *)
  | PyCoroutine: inner:py_type -> py_type

  (** PyGenerator: Generator type (yield-based iteration)

      Python syntax: Generator[YieldType, SendType, ReturnType]
      Brrr-Lang: Computation with Yield effect

      Generators are functions that use yield to produce values lazily.
      The three type parameters are:
      - yield_ty: Type of values yielded (yield x)
      - send_ty: Type of values sent in (x = yield)
      - return_ty: Type of final return value

      Example:
        def count_up(n: int) -> Generator[int, None, str]:
            for i in range(n):
                yield i
            return "done"
  *)
  | PyGenerator: yield_ty:py_type -> send_ty:py_type -> return_ty:py_type -> py_type

  (** PyAsyncGenerator: Asynchronous generator

      Python syntax: AsyncGenerator[YieldType, SendType]
      Brrr-Lang: Computation with both Async and Yield effects

      Async generators combine async/await with yield. They use:
      - async def + yield
      - async for to consume

      Note: Unlike Generator, AsyncGenerator has no return type parameter
      because async generators cannot return a value (only raise StopAsyncIteration).

      Example:
        async def fetch_pages() -> AsyncGenerator[str, None]:
            for page in range(10):
                data = await fetch(page)
                yield data
  *)
  | PyAsyncGenerator: yield_ty:py_type -> send_ty:py_type -> py_type

  (** PyIterator: Iterator protocol type

      Python syntax: Iterator[T]
      Brrr-Lang: Translated to array/sequence with lazy evaluation

      Iterator is a protocol requiring __iter__ and __next__ methods.
      It represents single-pass, forward-only iteration.

      Example:
        def get_items() -> Iterator[int]:
            return iter([1, 2, 3])
  *)
  | PyIterator : elem:py_type -> py_type

  (** PyIterable: Iterable protocol type

      Python syntax: Iterable[T]
      Brrr-Lang: Any type supporting iteration

      Iterable is a protocol requiring only __iter__ method.
      It can be iterated multiple times (unlike Iterator).

      Examples of Iterable: list, tuple, set, dict, str, range, generators

      Example:
        def process_all(items: Iterable[int]) -> int:
            return sum(items)
  *)
  | PyIterable : elem:py_type -> py_type

  (* ==========================================================================
     SPECIAL TYPES - Advanced typing constructs
     ========================================================================== *)

  (** PyAny: Dynamic/top type (disables type checking)

      Python syntax: Any
      Brrr-Lang: T_Py(Any) = Dynamic

      Any is compatible with every type. It acts as an escape hatch from
      the type system. Operations on Any values are not checked statically.

      WARNING: Using Any sacrifices type safety. Prefer Union types or
      TypeVar for generic code.

      Translation implications:
      - All operations on Dynamic require runtime type checks
      - May generate additional error handling code

      Example:
        def process(x: Any) -> Any:
            return x.some_method()  # No static checking
  *)
  | PyAny      : py_type

  (** PyNever: Bottom type (function never returns normally)

      Python syntax: Never, NoReturn (deprecated alias)
      Brrr-Lang: T_Py(Never) = Never (bottom type)

      Never indicates a function never returns:
      - Always raises an exception
      - Contains infinite loop
      - Calls sys.exit()

      Example:
        def fail(msg: str) -> Never:
            raise RuntimeError(msg)

        def loop_forever() -> Never:
            while True:
                pass
  *)
  | PyNever    : py_type

  (** PyType: Metaclass/type-of-type annotation

      Python syntax: Type[T], type[T]
      Brrr-Lang: Translated to type-level representation

      Type[T] represents the class object itself, not an instance.
      Type[Dog] means "the class Dog or a subclass of Dog".

      Example:
        def create_instance(cls: Type[Animal]) -> Animal:
            return cls()  # Calls cls's constructor
  *)
  | PyType     : inner:py_type -> py_type

  (** PyClass: Named class type (user-defined or stdlib)

      Python syntax: ClassName (direct reference)
      Brrr-Lang: Translated to struct or nominal type

      Represents a reference to a class by name. Used for:
      - User-defined classes
      - Standard library classes not in typing module
      - Forward references before class definition

      Example:
        class MyClass:
            pass

        def factory() -> MyClass:  # PyClass "MyClass"
            return MyClass()
  *)
  | PyClass    : name:string -> py_type

  (** PyGeneric: Generic type with type arguments

      Python syntax: GenericClass[T1, T2, ...]
      Brrr-Lang: Parametric type instantiation

      Represents a generic class instantiated with specific type arguments.
      Common generic classes: list[T], dict[K,V], Optional[T], etc.

      Used for user-defined generics:
        class Box(Generic[T]):
            value: T

        box: Box[int]  # PyGeneric "Box" [PyInt]

      Example:
        from typing import Generic, TypeVar
        T = TypeVar('T')
        class Container(Generic[T]):
            def __init__(self, value: T): self.value = value
  *)
  | PyGeneric  : name:string -> args:list py_type -> py_type

  (** PyTypeVar: Type variable for generic definitions

      Python syntax: TypeVar("T"), TypeVar("T", bound=SomeClass)
      Brrr-Lang: Generic type parameter

      TypeVar represents a placeholder type in generic definitions.
      It may have constraints:
      - Unbound: TypeVar("T") - can be any type
      - Bound: TypeVar("T", bound=Number) - subtype of Number
      - Constrained: TypeVar("T", int, str) - must be int or str

      Note: This representation only captures the name. Bounds and
      constraints would require additional fields if needed.

      Example:
        T = TypeVar("T")
        def identity(x: T) -> T:
            return x
  *)
  | PyTypeVar  : name:string -> py_type

  (** PyLiteral: Literal/singleton type

      Python syntax: Literal[value], Literal["foo"], Literal[42]
      Brrr-Lang: Singleton refinement type

      Literal types restrict a type to specific values. They are
      useful for discriminated unions and string enums.

      Example:
        Mode = Literal["read", "write", "append"]

        def open_file(path: str, mode: Mode) -> File:
            ...

        open_file("test.txt", "read")   # OK
        open_file("test.txt", "delete") # Type error
  *)
  | PyLiteral  : value:literal -> py_type

  (** PySelf: Self type for method return annotations (PEP 673)

      Python syntax: Self
      Brrr-Lang: Translates to "this" type in methods

      Self represents the type of the enclosing class, useful for
      fluent interfaces and factory methods in class hierarchies.

      Example:
        class Builder:
            def set_name(self, name: str) -> Self:
                self.name = name
                return self  # Returns same type as receiver
  *)

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

    ==========================================================================
    SOURCE LOCATION TRACKING PATTERN
    ==========================================================================

    Following EverParse's with_meta_t pattern (Ast.fst lines 107-111):
    - py_expr' is the raw expression type (without location)
    - py_expr = with_py_loc py_expr' wraps expressions with source span
    - All AST constructors produce located expressions

    This design enables:
    1. Precise error messages pointing to source locations
    2. Source maps for debugging translated code
    3. Incremental compilation by tracking modified ranges

    ==========================================================================
    EXPRESSION CATEGORY OVERVIEW
    ==========================================================================

    1. ATOMS (PyEVar', PyELit', PyENone', PyETrue', PyEFalse')
       Leaf nodes: variables, literals, constants
       Translation: Direct mapping to Brrr-Lang atoms

    2. OPERATIONS (PyEBinOp', PyEUnOp', PyECompare', PyEBoolOp')
       Arithmetic, comparison, and boolean operators
       Translation: Mapped to Brrr-Lang primitives with overflow checking

    3. CALLS AND ACCESS (PyECall', PyEAttr', PyEIndex', PyESlice')
       Function calls, attribute access, subscripting
       Translation: May require dynamic dispatch for duck typing

    4. COLLECTIONS (PyEList', PyEDict', PyETuple', PyESet')
       Literal syntax for container construction
       Translation: GC allocation with element translation

    5. COMPREHENSIONS (PyEListComp', PyEDictComp', PyESetComp', PyEGenExpr')
       Compact iteration syntax: [x*2 for x in range(10)]
       Translation: Desugared to loops with accumulator

    6. CONTROL FLOW (PyEIf', PyEFor', PyEWhile', PyETry', PyEWith', PyEMatch')
       Statements embedded as expressions for block translation
       Translation: Structured control flow with effect handling

    7. ASYNC (PyEAwait', PyEYield', PyEYieldFrom')
       Async/generator operations
       Translation: Effect-annotated computations

    ==========================================================================
    TRANSLATION SEMANTICS (from TRANSLATION_DESIGN.txt Section 5)
    ==========================================================================

    Expression translation T_Py(e):
      T_Py(x)                 = x                     [variable]
      T_Py(lambda x: e)       = lambda x. T_Py(e)    [lambda]
      T_Py(f(args, **kwargs)) = call(T_Py(f), T_Py(args))  [kwargs approximated]
      T_Py(obj.attr)          = field_get(T_Py(obj), attr) [dynamic lookup]
      T_Py([e1, ...])         = gc_alloc([T_Py(e1), ...])
      T_Py({k: v, ...})       = gc_alloc(Dict{T_Py(k): T_Py(v), ...})
      T_Py(raise e)           = throw(T_Py(e))
      T_Py(x if c else y)     = if T_Py(c) then T_Py(x) else T_Py(y)
      T_Py(await e)           = await(T_Py(e))
      T_Py(yield e)           = yield(T_Py(e))

    ============================================================================ *)

(** Python source expressions (raw, without location)

    This type represents Python expression syntax WITHOUT source location.
    For expressions with location tracking, use py_expr = with_py_loc py_expr'.

    ==========================================================================
    MUTUAL RECURSION NOTE
    ==========================================================================

    py_expr' is mutually recursive with:
    - py_comp_clause (for comprehensions)
    - py_except_handler (for try/except)
    - py_match_pattern (for match statements)
    - py_expr (located wrapper)

    The recursion is well-founded because:
    - Children are always smaller than parents
    - Lists are finite
    - No cycles in the AST structure
*)
noeq type py_expr' =

  (* ==========================================================================
     ATOMS - Leaf nodes with no sub-expressions
     ========================================================================== *)

  (** PyEVar': Variable reference

      Python: x, my_var, _private
      Translation: Direct variable lookup in environment

      Name binding: Variables are resolved using Python's LEGB rule:
        L(ocal) -> E(nclosing) -> G(lobal) -> B(uilt-in)
  *)
  | PyEVar'      : name:string -> py_expr'

  (** PyELit': Literal value (numbers, strings)

      Python: 42, 3.14, "hello", b"bytes"
      Translation: Direct constant embedding

      Note: The 'literal' type is imported from BrrrTypes/BrrrExpressions.
  *)
  | PyELit'      : value:literal -> py_expr'

  (** PyENone': None literal

      Python: None
      Translation: T_Py(None) = ()  (unit value)

      Separate from PyELit' for clarity and type-specific handling.
  *)
  | PyENone'     : py_expr'

  (** PyETrue': Boolean True literal

      Python: True
      Translation: T_Py(True) = true

      Note: In Python, True == 1 (boolean is subtype of int).
  *)
  | PyETrue'     : py_expr'

  (** PyEFalse': Boolean False literal

      Python: False
      Translation: T_Py(False) = false

      Note: In Python, False == 0 (boolean is subtype of int).
  *)
  | PyEFalse'    : py_expr'

  (* ==========================================================================
     OPERATIONS - Arithmetic, comparison, and boolean operators
     ========================================================================== *)

  (** PyEBinOp': Binary operation

      Python: e1 + e2, e1 * e2, e1 // e2, e1 ** e2, etc.
      Translation: Primitive operation with appropriate semantics

      Python-specific operators:
      - //  : Floor division (rounds toward -infinity)
      - **  : Exponentiation
      - @   : Matrix multiplication (numpy)
      - in  : Membership test
      - is  : Identity test (same object)

      Note: Operators like + may be overloaded via __add__ in Python.
      Translation assumes primitive types or generates dynamic dispatch.
  *)
  | PyEBinOp'    : op:binary_op -> left:py_expr -> right:py_expr -> py_expr'

  (** PyEUnOp': Unary operation

      Python: -x, +x, ~x, not x
      Translation: Primitive unary operation

      - Minus (-): Numeric negation
      - Plus (+): Numeric identity (rarely used)
      - Invert (~): Bitwise NOT
      - Not (not): Boolean negation
  *)
  | PyEUnOp'     : op:unary_op -> operand:py_expr -> py_expr'

  (** PyECompare': Chained comparison (Python-specific)

      Python: a < b < c  (equivalent to: a < b and b < c)
      Translation: Desugared to conjunction with single evaluation of middle terms

      IMPORTANT: In Python, b is evaluated only once:
        1 < x < 10  becomes  1 < x and x < 10 (but x computed once)

      The 'rest' field contains pairs of (operator, operand) for chaining.
  *)
  | PyECompare'  : first:py_expr -> rest:list (binary_op & py_expr) -> py_expr'

  (** PyEBoolOp': Boolean and/or with short-circuit evaluation

      Python: a and b and c, x or y or z
      Translation: Short-circuit evaluation (lazy conjunction/disjunction)

      - is_and = true:  a and b and c  (returns first falsy or last value)
      - is_and = false: a or b or c    (returns first truthy or last value)

      Python semantics: Returns actual value, not just True/False.
        [] or "default"  returns "default"
        [1] and "yes"    returns "yes"
  *)
  | PyEBoolOp'   : is_and:bool -> operands:list py_expr -> py_expr'

  (* ==========================================================================
     CALLS AND ACCESS - Function calls, attribute/item access
     ========================================================================== *)

  (** PyECall': Function/method call

      Python: f(a, b, c), obj.method(x, y=1, **kwargs)
      Translation: Function application with argument translation

      - func: The callable expression (function, method, class, etc.)
      - args: Positional arguments
      - kwargs: Keyword arguments as (name, value) pairs

      APPROXIMATION: **kwargs and *args unpacking are partially supported.
      A warning is emitted when kwargs cannot be fully translated.
  *)
  | PyECall'     : func:py_expr -> args:list py_expr -> kwargs:list (string & py_expr) -> py_expr'

  (** PyEAttr': Attribute access

      Python: obj.attr, self.value, module.function
      Translation: Field access or dynamic attribute lookup

      Python attribute access may involve:
      - Instance attributes: obj.__dict__["attr"]
      - Class attributes: type(obj).__dict__["attr"]
      - Descriptors: __get__, __set__
      - __getattr__: Fallback for missing attributes

      DYNAMIC: May require runtime lookup for duck typing.
  *)
  | PyEAttr'     : obj:py_expr -> attr:string -> py_expr'

  (** PyEIndex': Subscript/indexing operation

      Python: e[i], dict[key], arr[0]
      Translation: Array index or dictionary lookup

      Calls __getitem__ in Python, which may be overloaded.
      For negative indices: e[-1] accesses last element.
  *)
  | PyEIndex'    : obj:py_expr -> index:py_expr -> py_expr'

  (** PyESlice': Slice operation

      Python: e[a:b], e[a:b:c], e[::2], e[::-1]
      Translation: Subsequence extraction

      Parameters (all optional):
      - start: Beginning index (default 0)
      - stop: Ending index (exclusive, default len)
      - step: Step size (default 1)

      Negative step reverses direction: e[::-1] reverses sequence.
  *)
  | PyESlice'    : obj:py_expr -> start:option py_expr -> stop:option py_expr -> step:option py_expr -> py_expr'

  (* ==========================================================================
     FUNCTIONS - Lambda expressions
     ========================================================================== *)

  (** PyELambda': Anonymous function expression

      Python: lambda x, y: x + y
      Translation: lambda x. lambda y. T_Py(x + y)

      Lambdas are restricted to single expressions in Python.
      For multi-statement functions, use def (not representable here).

      Note: Lambda parameters are dynamically typed in untyped Python.
      Type annotations require def syntax: def f(x: int) -> int: ...
  *)
  | PyELambda'   : params:list string -> body:py_expr -> py_expr'

  (* ==========================================================================
     COLLECTIONS - Literal container construction
     ========================================================================== *)

  (** PyEList': List literal

      Python: [1, 2, 3], [], [a, b, c]
      Translation: gc_alloc(Array[T_Py(e1), T_Py(e2), ...])

      Creates a new mutable list with the given elements.
  *)
  | PyEList'     : elems:list py_expr -> py_expr'

  (** PyEDict': Dictionary literal

      Python: {"key": value}, {1: "a", 2: "b"}, {}
      Translation: gc_alloc(Dict{...})

      Creates a new mutable dictionary with key-value pairs.
      Keys are evaluated first, then values, left to right.
  *)
  | PyEDict'     : pairs:list (py_expr & py_expr) -> py_expr'

  (** PyETuple': Tuple literal

      Python: (1, 2, 3), (), (x,)  (note trailing comma for single element)
      Translation: Tuple[T_Py(e1), T_Py(e2), ...]

      Creates an immutable tuple. Unlike lists, tuples have fixed length.
  *)
  | PyETuple'    : elems:list py_expr -> py_expr'

  (** PyESet': Set literal

      Python: {1, 2, 3}, set()
      Translation: gc_alloc(Array[...]) with deduplication

      APPROXIMATION: Translated to array; loses O(1) membership testing.
      Note: Empty set must be set() not {} (which creates empty dict).
  *)
  | PyESet'      : elems:list py_expr -> py_expr'

  (* ==========================================================================
     COMPREHENSIONS - Compact iteration syntax
     ========================================================================== *)

  (** PyEListComp': List comprehension

      Python: [x*2 for x in range(10) if x > 5]
      Translation: Desugared to loop with accumulator

      Comprehension structure:
        [body for var1 in iter1 if cond1 for var2 in iter2 ...]
  *)
  | PyEListComp' : body:py_expr -> clauses:list py_comp_clause -> py_expr'

  (** PyEDictComp': Dictionary comprehension

      Python: {k: v*2 for k, v in items.items()}
      Translation: Desugared to loop building dictionary
  *)
  | PyEDictComp' : key:py_expr -> value:py_expr -> clauses:list py_comp_clause -> py_expr'

  (** PyESetComp': Set comprehension

      Python: {x*2 for x in range(10)}
      Translation: Desugared to loop with deduplication
  *)
  | PyESetComp'  : body:py_expr -> clauses:list py_comp_clause -> py_expr'

  (** PyEGenExpr': Generator expression (lazy)

      Python: (x*2 for x in range(10))
      Translation: Computation with Yield effect

      Unlike list comprehension, generator expressions are LAZY.
      Values are produced on demand during iteration.
  *)
  | PyEGenExpr'  : body:py_expr -> clauses:list py_comp_clause -> py_expr'

  (* ==========================================================================
     CONTROL FLOW EXPRESSIONS - Conditional and assignment expressions
     ========================================================================== *)

  (** PyEIfExp': Conditional expression (ternary)

      Python: x if condition else y
      Translation: if T_Py(condition) then T_Py(x) else T_Py(y)

      Note: Unlike C's ternary (?:), Python's reads "value if cond else other".
  *)
  | PyEIfExp'    : cond:py_expr -> then_:py_expr -> else_:py_expr -> py_expr'

  (** PyEWalrus': Assignment expression (Python 3.8+)

      Python: (x := expression)
      Translation: let x = T_Py(expression) in x

      The walrus operator := assigns and returns the value.
      Useful in comprehensions and while conditions:
        while (line := file.readline()):
            process(line)
  *)
  | PyEWalrus'   : var:string -> value:py_expr -> py_expr'

  (* ==========================================================================
     ASYNC - Asynchronous operations
     ========================================================================== *)

  (** PyEAwait': Await expression (async context only)

      Python: await coroutine
      Translation: await(T_Py(coroutine))

      Suspends execution until the awaitable completes.
      Only valid inside async def functions.
  *)
  | PyEAwait'    : inner:py_expr -> py_expr'

  (* ==========================================================================
     STATEMENTS AS EXPRESSIONS - For block translation
     ========================================================================== *)

  (** PyEAssign': Assignment statement

      Python: x = value, a, b = 1, 2
      Translation: Mutable binding update

      Note: Python assignment is a statement, not expression.
      We represent it here for block translation purposes.
  *)
  | PyEAssign'   : target:py_expr -> value:py_expr -> py_expr'

  (** PyEAugAssign': Augmented assignment

      Python: x += 1, y *= 2, z //= 3
      Translation: x = x op value (with single evaluation of x)

      Calls __iadd__, __imul__, etc. for in-place modification.
  *)
  | PyEAugAssign': op:binary_op -> target:py_expr -> value:py_expr -> py_expr'

  (** PyEReturn': Return statement

      Python: return value, return
      Translation: Effect return or function exit
  *)
  | PyEReturn'   : value:option py_expr -> py_expr'

  (** PyEYield': Yield expression (generators)

      Python: yield value, yield
      Translation: Yield effect operation

      Produces a value to the caller and suspends generator execution.
  *)
  | PyEYield'    : value:option py_expr -> py_expr'

  (** PyEYieldFrom': Delegating yield (generators)

      Python: yield from iterable
      Translation: Nested yield effect

      Delegates to another iterable/generator, forwarding yields.
  *)
  | PyEYieldFrom': iter:py_expr -> py_expr'

  (** PyERaise': Raise exception statement

      Python: raise Exception("msg"), raise, raise e from cause
      Translation: throw(T_Py(exception))

      - raise exc: Raise new exception
      - raise: Re-raise current exception (in except block)
      - raise exc from cause: Chain exceptions
  *)
  | PyERaise'    : exc:option py_expr -> cause:option py_expr -> py_expr'

  (** PyEAssert': Assertion statement

      Python: assert condition, assert condition, "message"
      Translation: if not T_Py(condition) then throw AssertionError

      Assertions can be disabled with python -O flag.
  *)
  | PyEAssert'   : test:py_expr -> msg:option py_expr -> py_expr'

  (** PyEPass': No-op statement

      Python: pass
      Translation: ()  (unit value)

      Placeholder for empty blocks: if cond: pass
  *)
  | PyEPass'     : py_expr'

  (** PyEBreak': Break loop statement

      Python: break
      Translation: Break control effect

      Exits the nearest enclosing for/while loop.
  *)
  | PyEBreak'    : py_expr'

  (** PyEContinue': Continue loop statement

      Python: continue
      Translation: Continue control effect

      Skips to next iteration of nearest enclosing loop.
  *)
  | PyEContinue' : py_expr'

  (* ==========================================================================
     CONTROL FLOW STATEMENTS - if/for/while/try/with/match
     ========================================================================== *)

  (** PyEIf': If statement with elif/else chains

      Python: if cond: body elif cond2: body2 else: body3
      Translation: Nested conditionals

      Structure:
      - cond: Primary condition
      - then_: Primary body
      - elifs: List of (condition, body) pairs for elif
      - else_: Optional else body
  *)
  | PyEIf'       : cond:py_expr -> then_:py_expr -> elifs:list (py_expr & py_expr) -> else_:option py_expr -> py_expr'

  (** PyEFor': For loop with optional else

      Python: for x in iterable: body else: no_break
      Translation: Iteration with optional completion handler

      The else clause executes if the loop completes WITHOUT break.
      This is a unique Python feature for search patterns.
  *)
  | PyEFor'      : var:string -> iter:py_expr -> body:py_expr -> else_:option py_expr -> py_expr'

  (** PyEWhile': While loop with optional else

      Python: while cond: body else: no_break
      Translation: Condition-based loop with completion handler

      Like for-else, the else runs if no break occurs.
  *)
  | PyEWhile'    : cond:py_expr -> body:py_expr -> else_:option py_expr -> py_expr'

  (** PyETry': Try/except/else/finally exception handling

      Python: try: body except E as e: handler else: ok finally: cleanup
      Translation: Effect handling with multiple clauses

      Structure:
      - body: Code that may raise exceptions
      - handlers: List of except clauses (type, name, handler_body)
      - else_: Runs if body completes without exception
      - finally: Always runs (for cleanup)
  *)
  | PyETry'      : body:py_expr -> handlers:list py_except_handler -> else_:option py_expr -> finally:option py_expr -> py_expr'

  (** PyEWith': Context manager statement

      Python: with expr as var: body
      Translation: try/finally with __enter__/__exit__

      Context manager protocol:
      1. __enter__() called, result bound to 'as' variable
      2. Body executed
      3. __exit__() called (handles exceptions too)

      Multiple items: with a as x, b as y: body
  *)
  | PyEWith'     : items:list (py_expr & option string) -> body:py_expr -> py_expr'

  (** PyEMatch': Pattern matching (Python 3.10+)

      Python: match expr: case pattern: body case pattern2 if guard: body2
      Translation: Multi-way branch with pattern destructuring

      Cases are (pattern, optional_guard, body).
      Patterns can bind variables, match structure, check types.
  *)
  | PyEMatch'    : scrutinee:py_expr -> cases:list (py_match_pattern & option py_expr & py_expr) -> py_expr'

  (* ==========================================================================
     BLOCK - Statement sequence
     ========================================================================== *)

  (** PyEBlock': Sequence of statements

      Python: stmt1; stmt2; stmt3 (or newline-separated)
      Translation: let _ = T_Py(stmt1) in let _ = T_Py(stmt2) in ...

      Represents the body of functions, loops, if branches, etc.
  *)
  | PyEBlock'    : stmts:list py_expr -> py_expr'

(** ============================================================================
    COMPREHENSION CLAUSES
    ============================================================================

    Comprehension clauses represent the 'for' and 'if' components within
    list, dict, set comprehensions, and generator expressions.

    Example: [x*2 for x in range(10) if x > 5]
    Clauses: [PyCompFor "x" (range 10), PyCompIf (x > 5)]

    Translation desugars comprehensions to explicit loops:
      result = []
      for x in range(10):
          if x > 5:
              result.append(x*2)
*)
and py_comp_clause =
  (** PyCompFor: For clause in comprehension

      Python: for var in iterable (within comprehension)
      Translation: Loop iteration
  *)
  | PyCompFor  : var:string -> iter:py_expr -> py_comp_clause

  (** PyCompIf: If clause in comprehension (filter)

      Python: if condition (within comprehension)
      Translation: Conditional filter
  *)
  | PyCompIf   : cond:py_expr -> py_comp_clause

(** ============================================================================
    EXCEPTION HANDLER
    ============================================================================

    Represents a single except clause in a try/except statement.

    Python: except ExceptionType as name: body
    Translation: Effect handler clause

    The handler structure:
    - except_range: Source location for error reporting
    - except_type: Exception type to catch (None = catch all)
    - except_name: Variable to bind exception (None = no binding)
    - except_body: Handler body to execute

    Example:
      try:
          risky()
      except ValueError as e:  # except_type=Some PyClass "ValueError"
          handle(e)            # except_name=Some "e"
      except:                  # except_type=None (catches all)
          fallback()
*)
and py_except_handler = {
  except_range : py_range;         (* Source location of handler *)
  except_type  : option py_type;   (* Exception type to catch; None = bare except *)
  except_name  : option string;    (* Variable name to bind exception instance *)
  except_body  : py_expr           (* Handler body *)
}

(** ============================================================================
    MATCH PATTERNS (Python 3.10+)
    ============================================================================

    Pattern matching patterns for the 'match' statement (PEP 634).

    Patterns can:
    - Match literal values (42, "hello")
    - Capture values into variables (x, y)
    - Destructure sequences ([a, b, *rest])
    - Destructure mappings ({key: value_pattern})
    - Match class instances (Point(x=0, y=y))
    - Combine with OR (a | b)
    - Add guards (pattern if condition)

    Example:
      match point:
          case Point(x=0, y=y):  # PyPatClass with keyword patterns
              print(f"On Y axis at {y}")
          case Point(x=x, y=0):
              print(f"On X axis at {x}")
          case Point() as p:    # PyPatAs
              print(f"Point at {p}")
          case _:               # PyPatWild
              print("Not a point")

    Translation: Desugared to nested if/isinstance checks and bindings.
*)
and py_match_pattern =
  (** PyPatWild: Wildcard pattern (matches anything)

      Python: case _:
      Translation: Default branch (always matches)
  *)
  | PyPatWild    : py_match_pattern

  (** PyPatCapture: Capture pattern (binds to variable)

      Python: case x:  (binds matched value to x)
      Translation: Binding introduction
  *)
  | PyPatCapture : name:string -> py_match_pattern

  (** PyPatLiteral: Literal pattern (exact value match)

      Python: case 42:, case "hello":
      Translation: Equality comparison
  *)
  | PyPatLiteral : value:literal -> py_match_pattern

  (** PyPatSequence: Sequence pattern (list/tuple destructuring)

      Python: case [a, b, c]:, case (x, y):
      Translation: Length check + element extraction

      Note: *rest patterns for variable-length not represented.
  *)
  | PyPatSequence: elems:list py_match_pattern -> py_match_pattern

  (** PyPatMapping: Mapping pattern (dict destructuring)

      Python: case {"name": n, "age": a}:
      Translation: Key existence check + value extraction

      Keys must be literal or simple expressions.
  *)
  | PyPatMapping : pairs:list (py_expr & py_match_pattern) -> py_match_pattern

  (** PyPatClass: Class pattern (instance destructuring)

      Python: case Point(x=0, y=y):
      Translation: isinstance check + attribute extraction

      - name: Class name to match against
      - pos_args: Positional attribute patterns
      - kw_args: Keyword attribute patterns
  *)
  | PyPatClass   : name:string -> pos_args:list py_match_pattern -> kw_args:list (string & py_match_pattern) -> py_match_pattern

  (** PyPatOr: OR pattern (alternative patterns)

      Python: case 1 | 2 | 3:
      Translation: Try each alternative in order

      All alternatives must bind the same variables.
  *)
  | PyPatOr      : alts:list py_match_pattern -> py_match_pattern

  (** PyPatAs: AS pattern (match and bind)

      Python: case [a, b] as pair:
      Translation: Match pattern + bind entire value

      Allows both destructuring and keeping the whole value.
  *)
  | PyPatAs      : pat:py_match_pattern -> name:string -> py_match_pattern

  (** PyPatGuard: Guarded pattern (conceptual representation)

      Python: case x if x > 0:
      Translation: Pattern match + guard condition check

      Note: In Python's actual AST, guards are attached to case clauses,
      not patterns. We include this for completeness.
  *)
  | PyPatGuard   : pat:py_match_pattern -> guard:py_expr -> py_match_pattern

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

    ==========================================================================
    DESIGN PHILOSOPHY
    ==========================================================================

    Translation can fail or be imprecise for several reasons:

    1. EXACT TRANSLATION (PyTransOk):
       The Python construct has a direct, semantics-preserving Brrr-Lang
       equivalent. Examples:
       - Arithmetic operations on primitives
       - Simple function calls
       - List literals
       - Boolean expressions

    2. SOUND APPROXIMATION (PyTransApprox):
       The translation is SOUND (preserves semantics) but MAY be overly
       conservative or lose precision. Examples:
       - kwargs approximation (preserves behavior, may lose efficiency)
       - Duck typing (adds runtime checks)
       - Union types (may use Dynamic)
       - Set translated to Array (loses uniqueness)

       The 'reason' field documents what approximation was made.
       Generated code is SAFE but may have different performance
       characteristics or error messages.

    3. TRANSLATION ERROR (PyTransError):
       The construct cannot be translated safely. Examples:
       - Metaclass manipulation (__new__, type())
       - exec/eval with dynamic code
       - Monkey patching at runtime
       - Untyped code requiring inference

    ==========================================================================
    SOURCE LOCATION TRACKING
    ==========================================================================

    All result variants carry source_range to preserve the original
    Python source location for error reporting and debugging.
    Following EverParse's error function pattern (Ast.fst lines 146-148).

    This enables:
    - Precise error messages pointing to problematic Python code
    - IDE integration showing translation issues inline
    - Source maps linking generated code to original source

    ==========================================================================
    TRANSLATION FUNCTOR CONTEXT
    ==========================================================================

    From TRANSLATION_DESIGN.txt Section 3 (Categorical Foundation):

    The translation forms a functor T_Py: Py_Cat -> Brrr_Cat where:
    - Py_Cat: Category of Python programs (objects=types, morphisms=functions)
    - Brrr_Cat: Category of Brrr-Lang programs

    py_trans_result represents the codomain of this functor, allowing us to:
    - Track partial morphisms (errors)
    - Annotate lossy morphisms (approximations)
    - Preserve source information for debugging

    ==========================================================================
    ERROR RECOVERY STRATEGY
    ==========================================================================

    When using translation results:

    1. Pattern match on the result type
    2. For PyTransOk: Use the result directly
    3. For PyTransApprox: Log the warning, use the result
    4. For PyTransError: Report error with source location

    Example:
      match translate_expr py_e with
      | PyTransOk e _ -> continue_with e
      | PyTransApprox e warning range ->
          log_warning range warning;
          continue_with e
      | PyTransError msg range ->
          report_error range msg;
          fail_translation ()

    ============================================================================ *)

(** Translation result: success with possible approximation warning.
    All variants carry source_range for precise error reporting.

    PyTransOk: Exact, semantics-preserving translation succeeded.
               The result expression is equivalent to the source.

    PyTransApprox: Sound but imprecise translation.
                   The result is safe but may be overly conservative.
                   'reason' documents what approximation was made.

    PyTransError: Translation failed.
                  'reason' documents why translation is impossible.
*)
noeq type py_trans_result =
  (** Exact translation - semantics fully preserved *)
  | PyTransOk     : result:expr -> source_range:py_range -> py_trans_result

  (** Approximate translation - sound but imprecise
      reason: Documentation of the approximation made (e.g., "kwargs ignored") *)
  | PyTransApprox : result:expr -> reason:string -> source_range:py_range -> py_trans_result

  (** Translation error - cannot safely translate
      reason: Documentation of why translation failed *)
  | PyTransError  : reason:string -> source_range:py_range -> py_trans_result

(** ============================================================================
    HELPER FUNCTIONS FOR TRANSLATION RESULTS
    ============================================================================

    These functions provide a monadic-style interface for working with
    translation results. They enable:

    1. Success checking: py_trans_is_success
    2. Result extraction: py_trans_get_expr, py_trans_get_range
    3. Error formatting: py_trans_format_error, py_trans_format_warning
    4. Functor operations: py_trans_map
    5. Applicative operations: py_trans_combine
    6. Smart constructors: py_trans_ok_from, py_trans_approx_from, etc.

    ==========================================================================
    DESIGN PATTERN: RAILWAY-ORIENTED PROGRAMMING
    ==========================================================================

    These helpers follow the "Railway-Oriented Programming" pattern:
    - Success track: PyTransOk flows through transformations
    - Warning track: PyTransApprox preserves warnings through composition
    - Error track: PyTransError short-circuits computation

    This enables clean composition of translation steps:

      translate_binary_op op e1 e2 =
        py_trans_combine mk_binop
          (translate_expr e1)
          (translate_expr e2)

    If either sub-translation fails or approximates, the combined result
    propagates that information appropriately.

    ============================================================================ *)

(** Check if translation succeeded (exact or approximate).

    Returns true for PyTransOk and PyTransApprox (usable results),
    false for PyTransError (translation failed).

    Usage:
      if py_trans_is_success result then
        use (py_trans_get_expr result)
      else
        report_error result
*)
let py_trans_is_success (r: py_trans_result) : bool =
  match r with
  | PyTransOk _ _ -> true
  | PyTransApprox _ _ _ -> true
  | PyTransError _ _ -> false

(** Extract expression from successful translation.

    PRECONDITION: py_trans_is_success r (verified by refinement type)

    This function is total on successful results. The refinement type
    ensures we cannot call it on error results.
*)
let py_trans_get_expr (r: py_trans_result{py_trans_is_success r}) : expr =
  match r with
  | PyTransOk e _ -> e
  | PyTransApprox e _ _ -> e

(** Extract source range from any translation result.

    All result variants carry source range, so this is total.
    Useful for error reporting regardless of success/failure.
*)
let py_trans_get_range (r: py_trans_result) : py_range =
  match r with
  | PyTransOk _ range -> range
  | PyTransApprox _ _ range -> range
  | PyTransError _ range -> range

(** Format error message with source location.

    Following EverParse's error function pattern (Ast.fst lines 146-148).

    PRECONDITION: PyTransError? r (verified by refinement type)

    Output format: "file.py:10:5-10:15: (Error) reason"
*)
let py_trans_format_error (r: py_trans_result{PyTransError? r}) : string =
  match r with
  | PyTransError msg range ->
      string_of_py_range range ^ ": (Error) " ^ msg

(** Format approximation warning with source location.

    PRECONDITION: PyTransApprox? r _ _ (verified by refinement type)

    Output format: "file.py:10:5-10:15: (Warning) reason"

    Note: Warnings should be collected and displayed to users so they
    understand where the translation may be imprecise.
*)
let py_trans_format_warning (r: py_trans_result{PyTransApprox? r _ _}) : string =
  match r with
  | PyTransApprox _ msg range ->
      string_of_py_range range ^ ": (Warning) " ^ msg

(** Map over translation result, preserving source location.

    Functor operation: applies f to the result expression if successful,
    leaving errors unchanged.

    Examples:
      (* Add type annotation to result *)
      py_trans_map (add_ascription ty) result

      (* Wrap in error handling *)
      py_trans_map wrap_in_try_catch result
*)
let py_trans_map (f: expr -> expr) (r: py_trans_result) : py_trans_result =
  match r with
  | PyTransOk e range -> PyTransOk (f e) range
  | PyTransApprox e reason range -> PyTransApprox (f e) reason range
  | PyTransError reason range -> PyTransError reason range

(** Combine two translation results with a binary operation.

    Applicative operation: combines two results using function f,
    propagating errors and warnings appropriately.

    Error propagation:
    - If either result is an error, the error is propagated
    - First error takes precedence if both are errors

    Warning accumulation:
    - If both are approximations, warnings are concatenated
    - If only one is approximation, that warning is kept
    - If both are exact, result is exact

    Uses the range from the first result for the combined result.

    Example:
      (* Combine left and right operands of binary expression *)
      let combine_binop op =
        py_trans_combine (fun l r -> mk_binop op l r)

      combine_binop Add left_result right_result
*)
let py_trans_combine (f: expr -> expr -> expr)
                     (r1: py_trans_result) (r2: py_trans_result)
    : py_trans_result =
  match r1, r2 with
  (* Both exact -> exact *)
  | PyTransOk e1 range1, PyTransOk e2 _ ->
      PyTransOk (f e1 e2) range1
  (* Error in first -> propagate first error *)
  | PyTransError reason range, _ ->
      PyTransError reason range
  (* Error in second -> propagate second error *)
  | _, PyTransError reason range ->
      PyTransError reason range
  (* Both approximate -> combine warnings *)
  | PyTransApprox e1 r1 range1, PyTransApprox e2 r2 _ ->
      PyTransApprox (f e1 e2) (r1 ^ "; " ^ r2) range1
  (* First approximate, second exact -> keep first warning *)
  | PyTransApprox e1 r range1, PyTransOk e2 _ ->
      PyTransApprox (f e1 e2) r range1
  (* First exact, second approximate -> keep second warning *)
  | PyTransOk e1 range1, PyTransApprox e2 r _ ->
      PyTransApprox (f e1 e2) r range1

(** ============================================================================
    SMART CONSTRUCTORS FOR TRANSLATION RESULTS
    ============================================================================

    These constructors automatically extract source ranges from Python
    expressions, reducing boilerplate in translation code.

    Instead of:
      PyTransOk (translate e) (py_expr_range py_e)

    Write:
      py_trans_ok_from py_e (translate e)
    ============================================================================ *)

(** Create a success result from a py_expr, extracting its range.

    Usage:
      let translate_var py_e name =
        let brrr_var = mk_var name in
        py_trans_ok_from py_e brrr_var
*)
let py_trans_ok_from (e: py_expr) (result: expr) : py_trans_result =
  PyTransOk result (py_expr_range e)

(** Create an approximation result from a py_expr, extracting its range.

    Usage:
      let translate_kwargs py_e kwargs =
        if List.length kwargs > 0 then
          py_trans_approx_from py_e
            (translate_without_kwargs py_e)
            "kwargs ignored in translation"
        else
          py_trans_ok_from py_e (translate py_e)
*)
let py_trans_approx_from (e: py_expr) (result: expr) (reason: string) : py_trans_result =
  PyTransApprox result reason (py_expr_range e)

(** Create an error result from a py_expr, extracting its range.

    Usage:
      let translate_eval py_e =
        py_trans_error_from py_e
          "eval() cannot be safely translated to Brrr-Lang"
*)
let py_trans_error_from (e: py_expr) (reason: string) : py_trans_result =
  PyTransError reason (py_expr_range e)

(** Create an error result at a specific range.

    Usage when source is not a py_expr:
      let translate_at_range range reason =
        py_trans_error_at range ("Unsupported: " ^ reason)
*)
let py_trans_error_at (range: py_range) (reason: string) : py_trans_result =
  PyTransError reason range
