(**
 * =============================================================================
 * Brrr-Lang Translation Layer Specification - Interface
 * =============================================================================
 *
 * This module provides the public interface for multi-language translation
 * to the Brrr-Lang intermediate representation. It implements translation
 * functors as described in brrr_lang_spec_v0.4.tex Part VI (Source Language
 * Mapping) and Chapter "Translation Functor Framework".
 *
 * -----------------------------------------------------------------------------
 * CATEGORICAL FOUNDATION
 * -----------------------------------------------------------------------------
 *
 * Each source language L forms a category Cat_L where:
 *   - Objects are types in L
 *   - Morphisms are functions f : A -> B in L
 *   - Identity is the identity function id_A
 *   - Composition is standard function composition
 *
 * A translation T : Cat_L -> Cat_Brrr is a FUNCTOR satisfying:
 *
 *   [FUNCTOR-IDENTITY]    T(id_A) = id_{T(A)}
 *   [FUNCTOR-COMPOSITION] T(g . f) = T(g) . T(f)
 *
 * -----------------------------------------------------------------------------
 * SOUNDNESS THEOREM (Informal)
 * -----------------------------------------------------------------------------
 *
 * A translation T_L is SOUND if and only if:
 *
 *   forall e, rho. [[e]]_L(rho) = v  ==>  [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v)
 *
 * Where [[e]]_L(rho) denotes the denotational semantics of expression e
 * in language L under environment rho.
 *
 * This means: if a source program evaluates to a value, its translation
 * evaluates to the translated value. The translation preserves semantics.
 *
 * -----------------------------------------------------------------------------
 * SUPPORTED LANGUAGES
 * -----------------------------------------------------------------------------
 *
 * This interface provides translation for:
 *
 *   - Rust:       Ownership model, lifetimes, traits, move semantics
 *   - TypeScript: Union types, gradual typing, async/await
 *   - Go:         Interfaces, goroutines, CSP channels
 *
 * For Python translation with comprehensive typing module support, see
 * the dedicated BrrrPythonTranslation.fsti module.
 *
 * Additional languages (Swift, Java, C/C++) are defined but translation
 * is partial or in development.
 *
 * -----------------------------------------------------------------------------
 * TRANSLATION RESULT TYPES
 * -----------------------------------------------------------------------------
 *
 * Translations return `trans_result a` which can be:
 *
 *   - TransOk value:         Translation succeeded with exact semantics
 *   - TransApprox value msg: Translation succeeded with approximation
 *   - TransError msg:        Translation failed
 *
 * The TransApprox case is critical for soundness: it indicates that the
 * translation is a SOUND OVER-APPROXIMATION. The translated code may
 * reject valid programs but will never accept invalid ones.
 *
 * See TRANSLATION_DESIGN.txt Section 8 for approximation strategies.
 *
 * -----------------------------------------------------------------------------
 * VERIFICATION STATUS (from SPECIFICATION_ERRATA.md)
 * -----------------------------------------------------------------------------
 *
 * The following properties are mechanized or planned:
 *
 *   - Type Preservation: If e : tau in L, then T_L(e) : T_L(tau) in Brrr
 *   - Semantic Preservation: Deferred to operational semantics module
 *   - Effect Soundness: Effects are over-approximated when uncertain
 *   - Approximation Safety: TransApprox never introduces unsoundness
 *
 * Known issues affecting translation:
 *   - Honda 2008 session type errors (see errata Chapter 5)
 *   - Alpha equivalence requires normalization-based definition
 *   - Some theorems blocked by infrastructure ordering issues
 *
 * -----------------------------------------------------------------------------
 * REFERENCES
 * -----------------------------------------------------------------------------
 *
 *   [1] brrr_lang_spec_v0.4.tex, Part VI "Source Language Mapping"
 *   [2] TRANSLATION_DESIGN.txt (co-located design document)
 *   [3] SPECIFICATION_ERRATA.md (known issues and corrections)
 *   [4] Pierce (2002), "Types and Programming Languages", Chapter 6
 *   [5] Barendregt (1984), "The Lambda Calculus", Section 2.1
 *
 * =============================================================================
 *)
module BrrrTranslationSpec

(**
 * Z3 solver options - conservative settings for translation proofs.
 *
 * Using minimal fuel to force explicit proofs rather than relying on
 * Z3's automated reasoning for recursive definitions. This follows
 * HACL* methodology for verification stability.
 *
 * --z3rlimit 50: Resource limit for SMT queries
 * --fuel 0:      No automatic unfolding of recursive definitions
 * --ifuel 0:     No automatic unfolding of inductive types
 *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions


(* =============================================================================
   PART I: SOURCE LANGUAGE IDENTIFICATION
   =============================================================================

   Each source language is identified by a unique tag. This determines which
   translation function to invoke and which default configuration to use.

   Language taxonomy based on brrr_lang_spec_v0.4.tex Section "Language Modes":

     Ownership-based: Rust (affine types, borrow checking)
     Reference-counted: Swift (ARC with COW semantics)
     Garbage-collected: Python, Go, TypeScript, Java
     Manual: C, C++ (no automatic memory management)

   ============================================================================= *)

(**
 * Source language identifier.
 *
 * Each variant corresponds to a source language with distinct semantics
 * that must be translated to Brrr-Lang's unified IR. The translation
 * functor implementation is selected based on this tag.
 *
 * IMPORTANT: Not all languages have complete implementations:
 *   - LangRust, LangTypeScript, LangGo: Full translation support
 *   - LangPython: Separate module (BrrrPythonTranslation.fsti)
 *   - LangSwift, LangJava: Partial support
 *   - LangC, LangCpp: Minimal support, FFI focus only
 *)
type source_language =
  | LangRust       (* Rust: ownership, lifetimes, traits, zero-cost abstractions *)
  | LangTypeScript (* TypeScript: gradual types, async/await, union types *)
  | LangPython     (* Python: dynamic typing, duck typing, generators *)
  | LangGo         (* Go: interfaces, goroutines, channels (CSP model) *)
  | LangSwift      (* Swift: ARC, optionals, actors, value/reference types *)
  | LangJava       (* Java: classes, GC, null, checked exceptions *)
  | LangC          (* C: manual memory, undefined behavior, FFI target *)
  | LangCpp        (* C++: manual memory, RAII, templates, FFI target *)


(* =============================================================================
   PART II: LANGUAGE CONFIGURATION PARAMETERS
   =============================================================================

   Each source language is characterized by a 5-tuple of configuration
   parameters that determine how translation proceeds:

     L = <Memory, Types, Null, Effects, Concurrency>

   This follows the categorical approach from brrr_lang_spec_v0.4.tex
   Section "Translation Functor Framework". Each parameter dimension
   determines specific translation rules.

   See TRANSLATION_DESIGN.txt Section 2 for detailed parameter values
   by language.

   ============================================================================= *)

(**
 * Memory management model.
 *
 * Determines how the source language manages heap memory, which affects:
 *   - Ownership mode mapping (MOne vs MOmega)
 *   - Resource lifetime tracking
 *   - Deallocation semantics
 *
 * Mapping to Brrr-Lang modes (from TRANSLATION_DESIGN.txt):
 *   MemOwnership -> MOne (linear/affine, explicit move)
 *   MemRC        -> MOmega with ref-counting annotations
 *   MemGC        -> MOmega (shared, GC-managed)
 *   MemManual    -> MOne with explicit free required
 *)
type memory_mode =
  | MemOwnership   (* Affine types, move semantics - Rust *)
  | MemRC          (* Reference counting - Swift ARC *)
  | MemGC          (* Garbage collection - Python, Go, TypeScript, Java *)
  | MemManual      (* Manual allocation/deallocation - C/C++ *)

(**
 * Type discipline.
 *
 * Determines how much type information is available at compile time:
 *   TypeStatic:  Full type information (Rust, Go, Java)
 *   TypeGradual: Mix of static and dynamic (TypeScript)
 *   TypeDynamic: Minimal static types (Python)
 *
 * For gradual/dynamic languages, translation may require runtime type
 * checks (guards) and may produce TransApprox results when types are
 * insufficiently constrained.
 *)
type type_mode =
  | TypeStatic     (* Fully static typing - Rust, Go, Java *)
  | TypeGradual    (* Gradual typing - TypeScript (any, unknown) *)
  | TypeDynamic    (* Fully dynamic typing - Python *)

(**
 * Null handling strategy.
 *
 * Determines how null/nil/None values are represented:
 *   NullNonNull:  No null; use Option type (Rust, Swift)
 *   NullOptional: Explicit optional types (Kotlin)
 *   NullNullable: Implicit nullable references (Python, Go, Java, TS)
 *
 * Translation to Brrr-Lang:
 *   - NullNonNull: Types are non-nullable by default
 *   - NullNullable: Reference types wrapped in TOption
 *
 * See brrr_lang_spec_v0.4.tex "Type Translation" for formal rules.
 *)
type null_mode =
  | NullNonNull    (* No null - Rust Option, Swift Optional *)
  | NullOptional   (* Explicit optional types - Kotlin-style *)
  | NullNullable   (* Implicit nullable - Python, Go, Java, TypeScript *)

(**
 * Effect tracking mode.
 *
 * Determines how side effects are represented in the source language:
 *   EffPure:      Effects tracked precisely (Haskell, pure F-star)
 *   EffTracked:   Effects tracked coarsely (async markers, throws)
 *   EffUntracked: Effects not tracked (most imperative languages)
 *
 * For EffUntracked languages, translation assigns conservative effect
 * rows based on the language's default effects (see default_effects).
 *)
type effect_mode =
  | EffPure        (* Effects tracked precisely in type system *)
  | EffTracked     (* Effects tracked coarsely (async, throws markers) *)
  | EffUntracked   (* Effects not tracked in source language *)

(**
 * Concurrency model.
 *
 * Determines how the language supports concurrent execution:
 *   ConcNone:    No built-in concurrency
 *   ConcThreads: OS threads with shared memory (C/C++, Java)
 *   ConcAsync:   Async/await pattern (TypeScript, Rust, Swift)
 *   ConcCSP:     Communicating Sequential Processes (Go channels)
 *   ConcActors:  Actor model with message passing (Swift actors)
 *
 * Affects translation of concurrent primitives to Brrr-Lang's
 * unified concurrency model (spawn, channels, futures).
 *)
type concurrency_mode =
  | ConcNone       (* No concurrency primitives *)
  | ConcThreads    (* OS threads with shared memory - C/C++, Java *)
  | ConcAsync      (* Async/await pattern - TypeScript, Rust, Swift *)
  | ConcCSP        (* CSP channels - Go goroutines and channels *)
  | ConcActors     (* Actor model - Swift actors *)

(**
 * Complete language configuration.
 *
 * Aggregates all configuration parameters for a source language.
 * This is an abstract type; use lang_config_of to obtain the
 * configuration for a specific language.
 *
 * Structure (from TRANSLATION_DESIGN.txt):
 *   { memory: memory_mode;
 *     types: type_mode;
 *     null_handling: null_mode;
 *     effects: effect_mode;
 *     concurrency: concurrency_mode }
 *)
type lang_config : Type0

(**
 * Retrieve configuration for a specific language.
 *
 * Returns the canonical configuration for the given source language.
 * This determines all translation rules for that language.
 *
 * Example configurations (from TRANSLATION_DESIGN.txt):
 *   Rust: { MemOwnership, TypeStatic, NullNonNull, EffTracked, ConcAsync }
 *   TypeScript: { MemGC, TypeGradual, NullNullable, EffUntracked, ConcAsync }
 *   Go: { MemGC, TypeStatic, NullNullable, EffUntracked, ConcCSP }
 *)
val lang_config_of : source_language -> lang_config


(* =============================================================================
   PART III: TRANSLATION CONTEXT
   =============================================================================

   Translation is stateful: we track information discovered during
   translation such as:

     - Fresh variable counters for avoiding capture
     - Borrow tracking for Rust translation
     - Type inference results for gradual typing
     - Accumulated diagnostics and warnings

   The context is threaded through translation functions and updated
   as translation proceeds.

   ============================================================================= *)

(**
 * Translation context - carries state during translation.
 *
 * This is an abstract type containing:
 *   - Source language identifier
 *   - Language configuration
 *   - Fresh name counter (for generating unique identifiers)
 *   - Accumulated diagnostics
 *   - Language-specific state (e.g., borrow context for Rust)
 *
 * The `noeq` attribute indicates this type does not have decidable
 * equality, as it contains mutable-like state.
 *)
noeq type trans_ctx : Type0

(**
 * Create initial translation context for a source language.
 *
 * Initializes all context state based on the language's configuration.
 * The context can then be threaded through translation functions.
 *
 * @param lang The source language to translate from
 * @return Fresh translation context with default initialization
 *)
val init_ctx : source_language -> trans_ctx


(* =============================================================================
   PART IV: TRANSLATION RESULT
   =============================================================================

   Translation functions return a tri-state result capturing:

     1. Exact translation (TransOk): Semantics preserved exactly
     2. Approximate translation (TransApprox): Sound over-approximation
     3. Failed translation (TransError): Cannot translate

   The TransApprox case is fundamental to the soundness guarantee.
   When source language features cannot be translated precisely,
   we produce a conservative approximation that may reject valid
   programs but never accepts invalid ones.

   From TRANSLATION_DESIGN.txt Section 8 "Approximation Strategies":

   Features requiring sound approximation include:
     - Dynamic typing (ApproxDynamic)
     - Union types that aren't Option (ApproxUnion)
     - Intersection types (ApproxIntersection)
     - Duck typing (ApproxDuckTyping)
     - Decorators (ApproxDecorator)
     - Complex async patterns (ApproxAsync)
     - Go select statements (ApproxChannel)
     - Interface dynamic dispatch (ApproxInterface)
     - Lifetime inference (ApproxLifetime)
     - Macro expansion (ApproxMacro)

   ============================================================================= *)

(**
 * Translation result with optional approximation notice.
 *
 * @param a The type of the translated value
 *
 * Variants:
 *   TransOk value:       Translation succeeded with exact semantics
 *   TransApprox value r: Translation succeeded but approximated
 *   TransError reason:   Translation failed completely
 *
 * SOUNDNESS INVARIANT:
 *   If TransApprox is returned, the translated code is a sound
 *   over-approximation. It may reject valid source programs but
 *   will never accept programs that would cause runtime errors
 *   beyond what the source program would cause.
 *)
noeq type trans_result (a: Type) =
  | TransOk    : value:a -> trans_result a
  | TransApprox: value:a -> reason:string -> trans_result a
  | TransError : reason:string -> trans_result a


(* =============================================================================
   PART V: DEFAULT EFFECTS
   =============================================================================

   Each language has a default effect row representing the effects that
   any expression in that language might produce. For EffUntracked
   languages, this is assigned to all translated expressions.

   From TRANSLATION_DESIGN.txt:

     epsilon_Py = <Throw "Exception" | <IO | epsilon>>
     epsilon_TS = <Throw | <Async | epsilon>>
     epsilon_Go = <Panic | <Spawn | epsilon>>

   These over-approximate the actual effects but ensure soundness.

   ============================================================================= *)

(**
 * Default effect row for each source language.
 *
 * Returns the conservative effect row that over-approximates all
 * possible effects an expression in this language might produce.
 *
 * Used when:
 *   - Translating from EffUntracked languages
 *   - Generating boundary guards for FFI
 *   - Computing composite effect rows
 *
 * @param lang The source language
 * @return Effect row over-approximating all effects in that language
 *
 * Typical values:
 *   LangPython:     Throw + IO + epsilon (exceptions and I/O)
 *   LangTypeScript: Throw + Async + epsilon (exceptions and async)
 *   LangGo:         Panic + Spawn + epsilon (panic and goroutines)
 *   LangRust:       epsilon or Panic (depends on panic=unwind/abort)
 *)
val default_effects : source_language -> effect_row


(* =============================================================================
   PART VI: RUST TRANSLATION
   =============================================================================

   Rust translation preserves ownership semantics through Brrr-Lang's
   mode system. The key mappings are:

   TYPE MAPPING (from TRANSLATION_DESIGN.txt Section 3):
     T_Rs(bool)         = Bool
     T_Rs(i8..i128)     = Int[I8..I128, Signed]
     T_Rs(u8..u128)     = Int[I8..I128, Unsigned]
     T_Rs(f32/f64)      = Float[F32/F64]
     T_Rs(&str/String)  = String
     T_Rs(T)            = own T_Rs^base(T)      [owned value]
     T_Rs(&'a T)        = ref T_Rs^base(T) ['a] [shared borrow]
     T_Rs(&'a mut T)    = refmut T_Rs^base(T) ['a] [mutable borrow]
     T_Rs(Box<T>)       = own Box[T_Rs^base(T)]
     T_Rs(Rc<T>)        = rc T_Rs^base(T)
     T_Rs(Arc<T>)       = arc T_Rs^base(T)
     T_Rs(Option<T>)    = Option[T_Rs(T)]
     T_Rs(Result<T,E>)  = Result[T_Rs(T), T_Rs(E)]
     T_Rs(Vec<T>)       = Array[T_Rs(T)]

   OWNERSHIP MAPPING:
     RsOwned      -> MOne   (linear/affine, must move)
     RsRef 'a     -> MOmega (shared, duplicable within lifetime)
     RsRefMut 'a  -> MOne   (exclusive, linear within lifetime)
     RsRc         -> MOmega (shared ownership via ref count)
     RsArc        -> MOmega (shared ownership, thread-safe)
     RsBox        -> MOne   (owned heap allocation, linear)

   SOUNDNESS THEOREM (from TRANSLATION_DESIGN.txt):
     If the Rust borrow checker accepts program P, then T_Rs(P)
     is ownership-safe in Brrr-Lang.

   ============================================================================= *)

(**
 * Rust ownership annotation.
 *
 * Captures how a Rust value is owned or borrowed. This determines
 * the mode and region in the Brrr-Lang translation.
 *
 * Variants:
 *   RsOwned:      Full ownership (T) - linear, must move
 *   RsRef lt:     Shared borrow (&'lt T) - duplicable within lifetime
 *   RsRefMut lt:  Mutable borrow (&'lt mut T) - exclusive, linear
 *   RsRc:         Reference counted (Rc<T>) - shared ownership
 *   RsArc:        Atomic ref counted (Arc<T>) - thread-safe shared
 *   RsBox:        Heap box (Box<T>) - owned heap allocation
 *)
type rust_ownership =
  | RsOwned                            (* T - owned value *)
  | RsRef       : lifetime:string -> rust_ownership  (* &'a T - shared borrow *)
  | RsRefMut    : lifetime:string -> rust_ownership  (* &'a mut T - mutable borrow *)
  | RsRc                               (* Rc<T> - reference counted *)
  | RsArc                              (* Arc<T> - atomic reference counted *)
  | RsBox                              (* Box<T> - heap allocation *)

(**
 * Rust type AST.
 *
 * Abstract representation of Rust types. Includes:
 *   - Primitive types (bool, integers, floats)
 *   - Compound types (tuples, arrays, structs, enums)
 *   - Reference types with lifetimes
 *   - Smart pointers (Box, Rc, Arc)
 *   - Generic types and trait bounds
 *
 * The `noeq` attribute indicates no decidable equality.
 *)
noeq type rust_type : Type0

(**
 * Rust expression AST.
 *
 * Abstract representation of Rust expressions. Includes:
 *   - Variables and literals
 *   - Borrow expressions (&e, &mut e)
 *   - Dereference ( *e)
 *   - Move and copy operations
 *   - Pattern matching
 *   - Async/await
 *   - Unsafe blocks
 *)
noeq type rust_expr : Type0

(**
 * Borrow context for tracking active borrows.
 *
 * During Rust translation, we track which variables are currently
 * borrowed and how, to ensure the translation respects Rust's
 * borrow checking invariants.
 *
 * Contains:
 *   - Active shared borrows (variable -> list of borrowers)
 *   - Active mutable borrows (variable -> exclusive borrower)
 *   - Lifetime relationships
 *)
noeq type borrow_ctx : Type0

(**
 * Empty borrow context with no active borrows.
 *
 * Starting point for translation; indicates no borrows are active.
 *)
val empty_borrow_ctx : borrow_ctx

(**
 * Translate Rust base type to Brrr-Lang type.
 *
 * Translates the "inner" type without ownership annotations.
 * Ownership is handled separately by translate_rust_ownership.
 *
 * @param t The Rust type to translate
 * @return Corresponding Brrr-Lang type
 *
 * Examples:
 *   bool       -> TBool
 *   i32        -> TInt { width = I32; sign = Signed }
 *   String     -> TString
 *   Vec<T>     -> TArray (translate_rust_base T)
 *)
val translate_rust_base : rust_type -> brrr_type

(**
 * Translate Rust ownership to Brrr-Lang mode.
 *
 * Maps Rust's ownership model to Brrr-Lang's mode semiring.
 *
 * @param own The Rust ownership annotation
 * @return Corresponding mode in {MZero, MOne, MOmega}
 *
 * Mapping:
 *   RsOwned    -> MOne   (linear, must use exactly once)
 *   RsRef _    -> MOmega (can duplicate within lifetime)
 *   RsRefMut _ -> MOne   (exclusive, can't duplicate)
 *   RsRc       -> MOmega (shared via ref counting)
 *   RsArc      -> MOmega (shared, thread-safe)
 *   RsBox      -> MOne   (linear heap ownership)
 *)
val translate_rust_ownership : rust_ownership -> mode

(**
 * Translate Rust lifetime to Brrr-Lang region.
 *
 * Maps Rust lifetime annotations to Brrr-Lang's region system.
 *
 * @param lt   The lifetime string ('a, 'static, etc.)
 * @param ctx  Translation context for fresh region generation
 * @return Corresponding Brrr-Lang region
 *
 * Mapping (from TRANSLATION_DESIGN.txt):
 *   'static -> RStatic
 *   'a      -> RNamed "a"
 *   fresh   -> RFresh n (from context counter)
 *)
val translate_rust_lifetime : string -> trans_ctx -> region

(**
 * Full Rust type translation with ownership and lifetime.
 *
 * Combines base type, ownership mode, and region into a complete
 * Brrr-Lang type representation.
 *
 * @param t   The Rust base type
 * @param own The ownership annotation
 * @param ctx Translation context
 * @return Triple of (brrr_type, mode, optional region)
 *
 * The region is present for borrowed types (Ref, RefMut) and
 * absent for owned types.
 *)
val translate_rust_type : rust_type -> rust_ownership -> trans_ctx ->
  (brrr_type & mode & option region)

(**
 * Translate Rust expression to Brrr-Lang.
 *
 * Main entry point for Rust expression translation. Handles all
 * Rust expression forms including borrows, moves, and async.
 *
 * @param e   The Rust expression to translate
 * @param bc  Current borrow context
 * @param ctx Translation context
 * @return Translation result with Brrr-Lang expression
 *
 * Key translations (from TRANSLATION_DESIGN.txt):
 *   T_Rs(x)           = x                [if not moved]
 *   T_Rs(&e)          = borrow(T_Rs(e))
 *   T_Rs(&mut e)      = borrow_mut(T_Rs(e))
 *   T_Rs( *e)         = deref(T_Rs(e))
 *   T_Rs(e?)          = match T_Rs(e) { Ok(v) => v, Err(e) => return Err(e) }
 *   T_Rs(async { e }) = async(T_Rs(e))
 *   T_Rs(e.await)     = await(T_Rs(e))
 *   T_Rs(unsafe { e }) = unsafe(T_Rs(e))
 *
 * May return TransApprox for:
 *   - Complex lifetime elision (ApproxLifetime)
 *   - Macro-generated code (ApproxMacro)
 *)
val translate_rust_expr : rust_expr -> borrow_ctx -> trans_ctx -> trans_result expr


(* =============================================================================
   PART VII: TYPESCRIPT TRANSLATION
   =============================================================================

   TypeScript translation handles gradual typing through a combination
   of static translation and runtime guards.

   TYPE MAPPING (from TRANSLATION_DESIGN.txt Section 4):
     T_TS(undefined)    = Unit
     T_TS(null)         = Option[Dynamic]
     T_TS(boolean)      = Bool
     T_TS(number)       = Float[F64]       [JS number is f64]
     T_TS(bigint)       = Int[BigInt, Signed]
     T_TS(string)       = String
     T_TS(symbol)       = String           [approximation]
     T_TS(void)         = Unit
     T_TS(never)        = Never
     T_TS(any)          = Dynamic          [UNSAFE top type]
     T_TS(unknown)      = Unknown          [SAFE top type]
     T_TS(A[])          = gc Array[T_TS(A)]
     T_TS((A,B,...))    = Tuple[T_TS(A), T_TS(B), ...]
     T_TS(Promise<A>)   = Future[T_TS(A), Hot]
     T_TS(A | B)        = Union or Option  [context-dependent]
     T_TS(A & B)        = A                [approximation]

   ASYNC/AWAIT:
     T_TS(async f)      = f : tau -[Async]-> Future[sigma]
     T_TS(await e)      = await(T_TS(e))

   OPTIONAL CHAINING:
     T_TS(a?.b)         = match T_TS(a) { None => None, Some(v) => Some(v.b) }

   DEFAULT EFFECTS: epsilon_TS = <Throw | <Async | epsilon>>

   ============================================================================= *)

(**
 * TypeScript type AST.
 *
 * Abstract representation of TypeScript types including:
 *   - Primitive types (boolean, number, string, symbol)
 *   - Special types (undefined, null, void, never, any, unknown)
 *   - Array and tuple types
 *   - Union and intersection types
 *   - Promise types
 *   - Object and interface types
 *   - Conditional types
 *)
noeq type ts_type : Type0

(**
 * TypeScript expression AST.
 *
 * Abstract representation of TypeScript expressions including:
 *   - Variables and literals
 *   - Optional chaining (a?.b)
 *   - Nullish coalescing (a ?? b)
 *   - Type assertions (e as T, e!)
 *   - Async/await
 *   - Arrow functions
 *   - Object and array literals
 *)
noeq type ts_expr : Type0

(**
 * Translate TypeScript type to Brrr-Lang.
 *
 * @param t The TypeScript type to translate
 * @return Corresponding Brrr-Lang type
 *
 * Note: Union types (A | B) are translated as:
 *   - Option[T] if one component is null/undefined
 *   - TUnion otherwise (may require TransApprox)
 *
 * Note: Intersection types (A & B) are approximated as just A.
 *)
val translate_ts_type : ts_type -> brrr_type

(**
 * Translate TypeScript expression to Brrr-Lang.
 *
 * @param e   The TypeScript expression to translate
 * @param ctx Translation context
 * @return Translation result
 *
 * May return TransApprox for:
 *   - 'any' type usage (ApproxDynamic)
 *   - Complex union types (ApproxUnion)
 *   - Intersection types (ApproxIntersection)
 *   - Complex async patterns (ApproxAsync)
 *)
val translate_ts_expr : ts_expr -> trans_ctx -> trans_result expr


(* =============================================================================
   PART VIII: GO TRANSLATION
   =============================================================================

   Go translation handles interfaces and CSP-style concurrency.

   TYPE MAPPING (from TRANSLATION_DESIGN.txt Section 6):
     T_Go(bool)          = Bool
     T_Go(int)           = Int[I64, Signed]      [platform-dependent]
     T_Go(int8..int64)   = Int[I8..I64, Signed]
     T_Go(uint8..uint64) = Int[I8..I64, Unsigned]
     T_Go(float32/64)    = Float[F32/F64]
     T_Go(complex64/128) = Tuple[Float, Float]   [approximation]
     T_Go(string)        = String
     T_Go(byte)          = Int[I8, Unsigned]
     T_Go(rune)          = Int[I32, Signed]
     T_Go([N]T)          = Array[T_Go(T)]
     T_Go([]T)           = gc Slice[T_Go(T)]
     T_Go(map[K]V)       = gc Dict[T_Go(K), T_Go(V)]
     T_Go(chan T)        = Channel[T_Go(T)]
     T_Go( *T)           = Option[T_Go(T)]       [nullable pointer]
     T_Go(interface{})   = Dynamic
     T_Go(error)         = Named "Error"

   GOROUTINE/CHANNEL:
     T_Go(go f(x))       = spawn(T_Go(f)(T_Go(x)))
     T_Go(ch <- v)       = chan_send(T_Go(ch), T_Go(v))
     T_Go(<-ch)          = chan_recv(T_Go(ch))
     T_Go(select {...})  = select([...cases...])  [may approximate]

   ERROR HANDLING:
     T_Go(func() (T, error)) = () -[epsilon_Go]-> Result[T_Go(T), Error]
     T_Go(panic(v))          = throw(T_Go(v))
     T_Go(recover())         = catch_panic()      [special handling]
     T_Go(defer f())         = defer(T_Go(f()))   [deferred execution]

   DEFAULT EFFECTS: epsilon_Go = <Panic | <Spawn | epsilon>>

   APPROXIMATIONS (from TRANSLATION_DESIGN.txt):
     - defer semantics require stack-based execution model
     - recover() needs special catch handling
     - Type assertions require runtime checks
     - nil interface differs from nil concrete type

   ============================================================================= *)

(**
 * Go type AST.
 *
 * Abstract representation of Go types including:
 *   - Primitive types (bool, int variants, float variants)
 *   - Special types (byte, rune, string, error)
 *   - Composite types (array, slice, map, struct)
 *   - Channel types (chan T, <-chan T, chan<- T)
 *   - Pointer types ( *T)
 *   - Interface types (including interface{})
 *   - Function types
 *)
noeq type go_type : Type0

(**
 * Go expression AST.
 *
 * Abstract representation of Go expressions including:
 *   - Variables and literals
 *   - Goroutine spawn (go f(x))
 *   - Channel operations (ch <- v, <-ch)
 *   - Select statement
 *   - Defer statement
 *   - Panic and recover
 *   - Type assertions (x.(T))
 *   - Type switches
 *)
noeq type go_expr : Type0

(**
 * Translate Go type to Brrr-Lang.
 *
 * @param t The Go type to translate
 * @return Corresponding Brrr-Lang type
 *
 * Note: Go's 'int' type is platform-dependent (32 or 64 bit).
 * Translation assumes 64-bit (I64) by default.
 *
 * Note: interface{} (empty interface) translates to Dynamic.
 *)
val translate_go_type : go_type -> brrr_type

(**
 * Translate Go expression to Brrr-Lang.
 *
 * @param e   The Go expression to translate
 * @param ctx Translation context
 * @return Translation result
 *
 * May return TransApprox for:
 *   - Complex select statements (ApproxChannel)
 *   - Interface dynamic dispatch (ApproxInterface)
 *   - defer with complex control flow
 *   - recover() in unusual contexts
 *)
val translate_go_expr : go_expr -> trans_ctx -> trans_result expr


(* =============================================================================
   PART IX: CROSS-LANGUAGE BOUNDARY HANDLING
   =============================================================================

   When code crosses language boundaries (FFI), properties that hold
   in one language may not hold in the other. We track which "axioms"
   each language guarantees and generate guards for boundary crossings.

   LANGUAGE AXIOMS (from TRANSLATION_DESIGN.txt Section 7):
     Rust:       { AxMemSafe, AxTypeSafe, AxRaceFree, AxLeakFree }
     TypeScript: { AxMemSafe, AxTypeSafe }
     Python:     { AxMemSafe, AxLeakFree }
     Go:         { AxMemSafe, AxTypeSafe, AxLeakFree }
     Swift:      { AxMemSafe, AxTypeSafe, AxNullSafe }
     Java:       { AxMemSafe, AxTypeSafe, AxLeakFree }
     C/C++:      { } (no guarantees)

   BOUNDARY RISKS:
     Risks(L1, L2) = axioms(L1) \ axioms(L2)
     When crossing from L1 to L2, properties in Risks are at risk.

   GUARD GENERATION:
     guard(L1, L2, v : tau) generates runtime checks for:
       - Type safety: type_check(v, tau)
       - Null safety: null_check(v)
       - Memory pinning: pin(v)  [prevent GC movement]

   ============================================================================= *)

(**
 * Language axioms - properties guaranteed by the language.
 *
 * Each axiom represents a safety property that the language's
 * type system and runtime enforce.
 *)
type lang_axiom =
  | AxMemSafe    (* Memory safety - no buffer overflows, use-after-free *)
  | AxTypeSafe   (* Type safety - no type confusion, valid casts only *)
  | AxNullSafe   (* Null safety - no null pointer dereferences *)
  | AxRaceFree   (* Data race freedom - no unsynchronized shared access *)
  | AxLeakFree   (* Leak freedom - resources deallocated (via GC or RAII) *)
  | AxDetDrop    (* Deterministic destruction - predictable cleanup order *)

(**
 * Get axioms guaranteed by a language.
 *
 * @param lang The source language
 * @return List of axioms that language enforces
 *
 * Examples:
 *   LangRust -> [AxMemSafe; AxTypeSafe; AxRaceFree; AxLeakFree; AxDetDrop]
 *   LangC    -> []  (C provides no safety guarantees)
 *)
val language_axioms : source_language -> list lang_axiom

(**
 * Compute boundary risks when crossing from L1 to L2.
 *
 * Returns axioms that hold in from_lang but not in to_lang.
 * These properties are "at risk" when crossing the boundary.
 *
 * @param from_lang Source language of the value
 * @param to_lang   Target language receiving the value
 * @return List of axioms that may be violated
 *
 * Example:
 *   boundary_risks LangRust LangC -> [AxMemSafe; AxTypeSafe; AxRaceFree; AxLeakFree]
 *   (Everything Rust guarantees is at risk in C)
 *)
val boundary_risks : from_lang:source_language -> to_lang:source_language ->
  list lang_axiom

(**
 * Generate guard expression for boundary crossing.
 *
 * Creates runtime checks to protect against boundary risks.
 * The returned expression wraps the value with necessary guards.
 *
 * @param from_lang Source language
 * @param to_lang   Target language
 * @param value     The expression being passed across boundary
 * @param ty        The type of the value
 * @return Guarded expression with runtime checks
 *
 * Generated guards may include:
 *   - type_check(v, tau): Runtime type verification
 *   - null_check(v): Null/None check before use
 *   - pin(v): Pin GC-managed memory to prevent movement
 *   - copy(v): Deep copy to prevent aliasing violations
 *)
val generate_boundary_guard : from_lang:source_language -> to_lang:source_language ->
                              value:expr -> ty:brrr_type -> expr


(* =============================================================================
   PART X: SOUNDNESS PROPERTIES (THEOREMS)
   =============================================================================

   This section documents the correctness criteria for translation.
   The theorems are stated informally here; mechanized proofs are in
   the corresponding .Theorems.fst modules where available.

   See SPECIFICATION_ERRATA.md for verification status and known issues.

   ============================================================================= *)

(**
 * Approximation annotations for features requiring sound over-approximation.
 *
 * When a source language feature cannot be translated exactly, we
 * return TransApprox with one of these reasons. Each reason indicates
 * a specific class of approximation.
 *
 * From TRANSLATION_DESIGN.txt Section 8 "Approximation Strategies":
 *
 *   ApproxDynamic:      Python/TypeScript dynamic attribute access
 *   ApproxUnion:        TypeScript unions that aren't Option
 *   ApproxIntersection: TypeScript A & B simplified to A
 *   ApproxDuckTyping:   Python structural subtyping
 *   ApproxDecorator:    Python decorators effect approximated
 *   ApproxAsync:        Complex async patterns simplified
 *   ApproxChannel:      Go select statement simplified
 *   ApproxInterface:    Go interface dynamic dispatch
 *   ApproxLifetime:     Rust lifetime inference approximated
 *   ApproxMacro:        Macro bodies not expanded
 *
 * INVARIANT: All approximations are SOUND over-approximations.
 * They may cause the type checker to reject valid programs but
 * will never allow invalid programs to type-check.
 *)
type approx_reason =
  | ApproxDynamic       (* Dynamic typing required runtime checks *)
  | ApproxUnion         (* Union type not representable as Option *)
  | ApproxIntersection  (* Intersection type simplified *)
  | ApproxDuckTyping    (* Structural subtyping approximated *)
  | ApproxDecorator     (* Decorator effect unknown *)
  | ApproxAsync         (* Complex async pattern simplified *)
  | ApproxChannel       (* Channel/select simplified *)
  | ApproxInterface     (* Interface dispatch approximated *)
  | ApproxLifetime      (* Lifetime inference incomplete *)
  | ApproxMacro         (* Macro not expanded *)


(* -----------------------------------------------------------------------------
   THEOREM: TYPE PRESERVATION
   -----------------------------------------------------------------------------

   If e : tau in source language L, then T_L(e) : T_L(tau) in Brrr-Lang.

   This states that translation preserves typing judgments: well-typed
   source programs translate to well-typed Brrr-Lang programs.

   FORMAL STATEMENT:

     forall L, Gamma, e, tau.
       Gamma |-_L e : tau  ==>
       T_L(Gamma) |-_Brrr T_L(e) : T_L(tau)

   PROOF STATUS (from SPECIFICATION_ERRATA.md):
     - Rust: Partially mechanized, blocked by lifetime infrastructure
     - TypeScript: Proof sketch exists, needs gradual typing model
     - Go: Proof sketch exists, needs interface semantics

   REFERENCE: Pierce (2002), "Types and Programming Languages", Chapter 8

   --------------------------------------------------------------------------- *)


(* -----------------------------------------------------------------------------
   THEOREM: SEMANTIC PRESERVATION
   -----------------------------------------------------------------------------

   If [[e]]_L(rho) = v in language L, then
   [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v).

   The translation preserves operational semantics: evaluating the
   translated program produces the translated result.

   FORMAL STATEMENT:

     forall L, e, rho, v.
       [[e]]_L(rho) = v  ==>
       [[T_L(e)]]_Brrr(T_L(rho)) = T_L(v)

   CAVEAT: For TransApprox results, this holds up to the approximation.
   The translated program may fail (conservatively) where the source
   would succeed.

   PROOF STATUS:
     Requires operational semantics infrastructure not yet implemented.
     See SPECIFICATION_ERRATA.md Chapter 11 for handler termination
     dependencies.

   REFERENCE: brrr_lang_spec_v0.4.tex, Theorem "Translation Soundness"

   --------------------------------------------------------------------------- *)


(* -----------------------------------------------------------------------------
   THEOREM: COMPOSITIONALITY
   -----------------------------------------------------------------------------

   For any context C and expression e:
     T_L(C[e]) = T_L(C)[T_L(e)]

   The translation is compositional - it can be applied to sub-expressions
   independently and the results compose correctly.

   FORMAL STATEMENT:

     forall L, C, e.
       T_L(C[e]) = T_L(C)[T_L(e)]

   where C[e] denotes plugging expression e into context C, and
   T_L(C) denotes the translation of the context itself.

   SIGNIFICANCE:
   This property enables:
     - Incremental translation (translate sub-expressions separately)
     - Caching of translation results
     - Modular reasoning about translation correctness

   PROOF STATUS:
     Follows from structural recursion of translation functions.
     Not separately mechanized; implicit in function definitions.

   REFERENCE: Barendregt (1984), "The Lambda Calculus", Section 2.1

   --------------------------------------------------------------------------- *)


(* -----------------------------------------------------------------------------
   THEOREM: EFFECT SOUNDNESS
   -----------------------------------------------------------------------------

   If e has effect epsilon in L, then T_L(e) has effect T_L(epsilon)
   which is an over-approximation of the actual effects.

   FORMAL STATEMENT:

     forall L, e, epsilon.
       e : T !{epsilon}  in L  ==>
       T_L(e) : T_L(T) !{epsilon'} where epsilon' >= T_L(epsilon)

   The >= relation means epsilon' is at least as permissive as T_L(epsilon).

   For EffUntracked languages, epsilon' = default_effects(L), which
   conservatively approximates all possible effects.

   PROOF STATUS:
     Implicit in translation design; effects are always over-approximated.

   --------------------------------------------------------------------------- *)


(* -----------------------------------------------------------------------------
   THEOREM: APPROXIMATION SAFETY
   -----------------------------------------------------------------------------

   TransApprox returns sound over-approximations: the translated code
   may reject valid programs but will never accept invalid ones.

   FORMAL STATEMENT:

     forall e, ctx.
       translate(e, ctx) = TransApprox(e', reason)  ==>
       (forall inputs. e' safe  ==>  e safe)

   That is: if the approximated translation is safe for some inputs,
   the original was safe for those inputs.

   CONTRAPOSITIVE: If the original program would fail, the approximation
   either also fails or conservatively rejects.

   PROOF STATUS:
     By design of approximation strategies. Each ApproxReason has a
     documented over-approximation property.

   --------------------------------------------------------------------------- *)
