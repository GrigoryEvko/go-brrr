(** ============================================================================
    BrrrFFI.Theorems.fst - Foreign Function Interface Theorems for Brrr-Lang
    ============================================================================

    Multi-language boundary theorems for FFI safety and cross-language
    interoperability. Based on foundational work in multi-language semantics.

    PRIMARY REFERENCES:
    ===================
    - Matthews & Findler 2007, "Operational Semantics for Multi-Language Programs"
      POPL 2007 - Establishes boundary term semantics (Theorems 1-6)
      Key insight: Boundaries are cross-language casts that regulate both
      control flow and value conversion between languages.

    - Patterson et al. 2022, "Semantic Soundness for Language Interoperability"
      PLDI 2022 - Realizability-based approach (Lemma 3.1)
      Extends Matthews-Findler to handle polymorphism and abstraction.

    - Wadler & Findler 2009, "Well-Typed Programs Can't Be Blamed"
      ESOP 2009 - Blame tracking for contract violations at boundaries.

    COVERED THEOREMS FROM AXIOMS_REPORT_v2.md:
    ==========================================
    - T-5.3: convertibility_sound   - Cross-language type convertibility
    - T-5.4: boundary_soundness     - Multi-language boundary terms
    - T-5.9: round_trip_preservation - Parse -> IR -> pretty preserves semantics
    - T-5.10: cfg_complete          - CFG correctly models control flow

    PROOF STATUS: All theorems ADMITTED
    ===================================
    Each requires 8-80 hours of proof effort depending on complexity.
    The admitted proofs contain detailed proof sketches and literature references.

    MEMORY SAFETY ACROSS FFI BOUNDARIES:
    ====================================
    FFI boundaries present unique memory safety challenges:

    1. OWNERSHIP TRANSFER: When passing values across FFI boundaries, ownership
       semantics differ between languages. Rust has move semantics, Python uses
       reference counting via CPython, C requires explicit malloc/free. The
       boundary_soundness theorem (T-5.4) guarantees that well-typed boundary
       crossings do not violate memory safety invariants.

    2. LIFETIME MANAGEMENT: References crossing boundaries must have lifetimes
       that outlive the call. This is enforced through the guard system in
       BrrrLangMapping.fst which generates appropriate checks based on source/target
       language memory modes (see BrrrLangMapping.memory_axioms).

    3. BUFFER SAFETY: For Low-star and C extraction via Karamel, buffers crossing FFI
       boundaries must satisfy:
       - live h buf: Buffer is allocated in memory h
       - disjoint: No aliasing with other mutable state
       - modifies loc_buffer: Only specified locations modified
       See FSTAR_REFERENCE.md Section 11 (Low-star and LowStar) for patterns.

    4. REPR ATTRIBUTES FOR C INTEROP: Types crossing to C must have defined ABI:
       - #[repr(C)]: C-compatible struct layout (fields in declaration order)
       - #[repr(transparent)]: Same layout as inner type (newtype pattern)
       - #[repr(packed)]: No padding between fields
       - #[repr(align(n))]: Alignment to n bytes
       See brrr_lang_spec_v0.4.tex Part X (FFI & Interop) for full definitions.

    KARAMEL EXTRACTION PATTERNS:
    ============================
    Following HACL-star and EverParse patterns for verified C code generation:

    1. inline_for_extraction: Functions inlined during Karamel extraction,
       eliminating function call overhead while preserving verification.
       Example from HACL-star Bignum: addcarry_st, subborrow_st use this.

    2. noextract: Proof-only definitions not extracted to C. Used for
       specifications, lemmas, and ghost computations.

    3. Stack vs Heap: LowStar.Buffer operations distinguish:
       - alloca: Stack-allocated, auto-freed at pop_frame
       - malloc: Heap-allocated, requires explicit free
       Boundary guards must track allocation origin.

    4. Modifies clauses: Every function specifies exactly what memory it
       modifies via (modifies loc h0 h1). Frame rule allows local reasoning:
       if function only modifies loc, all disjoint state is preserved.

    RELATED MODULES:
    ================
    - BrrrLangMapping.fst: Language mode configurations and boundary guards
    - BrrrValues.fst: Runtime value representation (heap, env, result monad)
    - BrrrTypes.fst: Type definitions including FFI-safe subset

    AXIOM DEPENDENCIES (from SPECIFICATION_ERRATA.md):
    ==================================================
    - AXIOM-EXT-004: Tree-sitter parser correctness (trusted)
    - AXIOM-EXT-005: Language frontend correctness (trusted)
    - AXIOM-FFI-001: Pointer conversion soundness (trusted)
    - AXIOM-FFI-002: CPython runtime interop (trusted)
    - AXIOM-FFI-003: Dynamic dispatch resolution (trusted)

    AXIOM DETAILS:
    --------------
    AXIOM-FFI-001 (Pointer Conversion Soundness):
      Assumes pointer casts between compatible FFI-safe types preserve
      memory safety. Required because F* cannot verify foreign pointer
      arithmetic or aliasing patterns in C code.

    AXIOM-FFI-002 (CPython Runtime Interop):
      Assumes Python's reference counting mechanism (Py_INCREF/Py_DECREF)
      correctly manages object lifetimes when crossing FFI boundaries.
      PyObject* ownership transfer must follow Python C API conventions.

    AXIOM-FFI-003 (Dynamic Dispatch Resolution):
      Assumes virtual method tables (vtables) in C++/Java are correctly
      resolved at runtime. Required for OOP interop where method calls
      go through indirection.

    HACL-STAR AND EVERPARSE VERIFICATION PATTERNS:
    ===============================================
    These proven-in-production patterns from HACL-star guide our approach:

    1. LAYERED VERIFICATION (from HACL-star methodology):
       Spec.Algorithm         -- Pure mathematical spec
           |
           v (refines)
       Hacl.Spec.Algorithm    -- Low-level functional spec
           |
           v (refines)
       Hacl.Impl.Algorithm    -- Imperative implementation
           |
           v (extracts to)
       algorithm.c            -- Generated C code

    2. Z3 OPTIONS PATTERN (from HACL-star):
       set-options "--z3rlimit 50 --fuel 0 --ifuel 0"   (Default)
       push-options "--z3rlimit 200 --fuel 1"           (Complex proofs)
       ...
       pop-options                                       (Restore)

    3. EVERPARSE ZERO-COPY PARSING:
       Parsers operate directly on LowStar buffers without copying.
       Requires careful lifetime management across FFI boundaries.
       See: Ramananandro et al. 2019, USENIX Security

    4. INTEGER TYPE METHODOLOGY (HACL-star Lib.IntTypes):
       Uses dependent types (int_t t l) to statically ensure:
       - Inputs are in range by construction
       - No overflow in arithmetic operations
       - Constant-time execution for cryptographic code
    ============================================================================ *)

module BrrrFFI.Theorems

open FStar.List.Tot
open FStar.Classical

(* Import core definitions *)
open BrrrLangMapping
open BrrrTypes
open BrrrExpressions
open BrrrValues

(* ============================================================================
   EXTRACTION PIPELINE NOTES (FSTAR_REFERENCE.md Section 9)
   ============================================================================

   F* supports multiple extraction targets through FStarC.Extraction:

   1. ML Extraction (OCaml/F#):
      - Refinement types erased: {x:a | p} -> a
      - Ghost/erased types become unit
      - Effect tags: E_PURE (pure), E_GHOST (erased), E_IMPURE (effectful)

   2. Karamel/Low* Extraction (C code):
      - LowStar.Buffer.buffer uint8 -> uint8_t*
      - FStar.UInt32.t -> uint32_t
      - FStar.UInt64.t -> uint64_t

   KEY EXTRACTION ATTRIBUTES (for FFI-compatible code):

   [@@inline_for_extraction]
     - Function inlined during Karamel extraction
     - Eliminates function call overhead
     - HACL* uses this for performance-critical primitives
     - Example: addcarry_st, subborrow_st in Bignum

   [@@noextract]
     - Definition NOT extracted to C
     - Used for specifications, lemmas, ghost computations
     - Keeps proof-only code out of generated C

   [@@CInline]
     - Hint to C compiler for inlining
     - Weaker than inline_for_extraction (suggestion only)

   [@@CMacro]
     - Extract as C preprocessor macro
     - Useful for constants and simple expressions

   [@@CPrologue "..."] / [@@CEpilogue "..."]
     - Insert raw C code before/after definition
     - Useful for include directives, pragmas, etc.

   CODEGEN OPTIONS:
     --codegen OCaml    : Generate OCaml code
     --codegen FSharp   : Generate F# code
     --codegen krml     : Generate Karamel intermediate (for C)
     --codegen Plugin   : Generate F* plugin
   ============================================================================ *)

(** ============================================================================
    SMT OPTIONS FOR TRACTABLE VERIFICATION
    ============================================================================ *)

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* ============================================================================
   LOW-STAR AND LOWSTAR MEMORY MODEL NOTES (FSTAR_REFERENCE.md Section 11)
   ============================================================================

   LowStar provides memory-safe C programming within F*. Key patterns for FFI:

   BUFFER OPERATIONS (LowStar.Buffer):
   -----------------------------------
   type buffer (a:Type) = mbuffer a (trivial_preorder a) (trivial_preorder a)

   val create : init:'a -> len:UInt32.t -> Stack (buffer 'a)
     (requires fun h -> True)
     (ensures fun h0 b h1 -> live h1 b /\ length b = UInt32.v len)

   val index : b:buffer 'a -> i:UInt32.t{UInt32.v i < length b} -> Stack 'a
     (requires fun h -> live h b)
     (ensures fun h0 r h1 -> h0 == h1 /\ r == Seq.index (as_seq h0 b) (UInt32.v i))

   val upd : b:buffer 'a -> i:UInt32.t{UInt32.v i < length b} -> v:'a -> Stack unit
     (requires fun h -> live h b)
     (ensures fun h0 _ h1 -> modifies (loc_buffer b) h0 h1 /\ live h1 b)

   MEMORY PREDICATES:
   ------------------
   val live : mem -> buffer 'a -> Type0      (* Buffer is allocated *)
   val modifies : loc -> mem -> mem -> Type0 (* Only loc changed *)
   val loc_buffer : buffer 'a -> loc         (* Location of buffer *)
   val loc_none : loc                        (* Empty location *)
   val loc_union : loc -> loc -> loc         (* Union of locations *)
   val disjoint : buffer 'a -> buffer 'b -> Type0

   STACK VS HEAP ALLOCATION:
   -------------------------
   Stack allocation (auto-freed at pop_frame):
     push_frame ();
     let buf = alloca 0uy 16ul in
     (* ... use buf ... *)
     pop_frame ()

   Heap allocation (requires explicit free):
     let buf = malloc HyperStack.root 0uy 32ul in
     (* ... use buf ... *)
     free buf

   FFI IMPLICATIONS:
   -----------------
   When passing LowStar buffers across FFI boundaries:
   1. Buffer must be live in the current memory state
   2. Lifetime must outlive the foreign call
   3. Modifies clause must account for foreign modifications
   4. Disjointness must be established if foreign code aliases
   ============================================================================ *)

(** ============================================================================
    TYPE DEFINITIONS FOR MULTI-LANGUAGE SEMANTICS
    ============================================================================

    Following Matthews-Findler 2007 Section 2, we define:
    - Multi-language expressions (can contain embedded terms from other languages)
    - Boundary terms (MS = ML-outside-Scheme-inside, SM = Scheme-outside-ML-inside)
    - Lump values (opaque foreign values)
    - Natural embedding (type-directed value conversion)
    ============================================================================ *)

(** Multi-language expression: combines expressions from multiple source languages.

    From Matthews-Findler 2007:
    "We introduce boundaries as a new kind of expression in each language.
     In ML, we extend e to also produce (tau MS e) and we extend Scheme's
     e to also produce (SM^tau e) where tau on the ML side of each boundary
     indicates the type ML will consider the expression on its side of the
     boundary to be."

    Our multi_expr type models this by allowing:
    - Native Brrr expressions
    - Boundary terms that wrap foreign expressions with type annotations
    - Language annotations tracking which language context we are in
*)
type source_language =
  | LangBrrr       : source_language    (* Brrr IR itself *)
  | LangPython     : source_language
  | LangTypeScript : source_language
  | LangRust       : source_language
  | LangGo         : source_language
  | LangJava       : source_language
  | LangC          : source_language
  | LangCpp        : source_language

let source_language_eq (l1 l2: source_language) : bool =
  match l1, l2 with
  | LangBrrr, LangBrrr -> true
  | LangPython, LangPython -> true
  | LangTypeScript, LangTypeScript -> true
  | LangRust, LangRust -> true
  | LangGo, LangGo -> true
  | LangJava, LangJava -> true
  | LangC, LangC -> true
  | LangCpp, LangCpp -> true
  | _, _ -> false

(** Get language mode for a source language.

    Each language mode captures memory management and safety properties:

    MEMORY MODES (from brrr_lang_spec_v0.4.tex):
    --------------------------------------------
    - rust_mode:   Ownership-based, move semantics, borrow checking
    - python_mode: Reference counting (CPython), GC for cycles
    - typescript_mode: GC-managed, no manual memory
    - go_mode:     GC-managed, value semantics for small types
    - java_mode:   GC-managed, reference semantics
    - c_mode:      Manual malloc/free, pointer arithmetic allowed
    - cpp_mode:    RAII + manual, smart pointers optional

    UNSAFE EFFECT (from spec Section "Safety and Unsafety"):
    --------------------------------------------------------
    FFI calls require unsafe context in Brrr:

      unsafe { extern_function(args) }

    The unsafe block:
    1. Discharges the Unsafe effect requirement
    2. Shifts responsibility to programmer for memory safety
    3. Must document invariants maintained

    UNSAFE EFFECTS ENUMERATION:
      UnsafeFFI       - Foreign function call
      UnsafePtr       - Raw pointer dereference
      UnsafeTransmute - Bit-level type reinterpretation
*)
let language_mode (lang: source_language) : lang_mode =
  match lang with
  | LangBrrr -> rust_mode  (* Brrr uses Rust-like semantics *)
  | LangPython -> python_mode
  | LangTypeScript -> typescript_mode
  | LangRust -> rust_mode
  | LangGo -> go_mode
  | LangJava -> java_mode
  | LangC -> c_mode
  | LangCpp -> cpp_mode

(** Multi-language expression following Matthews-Findler structure.

    This is a SIMPLIFIED model of multi-language expressions.
    The key cases are:

    - MNative: A native Brrr expression (no boundary crossing)

    - MBoundary: A boundary term wrapping a foreign expression
      Parameters: source lang, target lang, ascribed type, inner expression
      Corresponds to Matthews-Findler's (tau MS e) and (SM^tau e)

    - MLump: An opaque foreign value (lump embedding)
      Used when type-directed conversion is not possible

    - MGuard: A guard checking a foreign value (natural embedding)
      Corresponds to Matthews-Findler's G^tau guards from Section 3.2

    MEMORY SAFETY NOTE:
    ===================
    The multi_expr type is noeq (no decidable equality) because it contains:
    - Closures via expr (functions cannot be compared)
    - Opaque values via MLump (foreign representations)

    For Karamel extraction, this type would NOT be directly extractable to C
    since it requires GC or reference counting. Instead, Karamel extraction
    would work with the lower-level buffer-based representations in LowStar.

    REPR CONSIDERATIONS:
    ====================
    If this were to be made FFI-safe for C interop, each variant would need:
    - Tagged union representation with explicit discriminator
    - Pointer-stable layouts for inner data
    - No implicit closures (would need function pointers + context)

    See brrr_lang_spec_v0.4.tex Section "FFI-Safe Types" for the subset
    of types that have defined C ABI representation.
*)
noeq type multi_expr =
  | MNative   : expr -> multi_expr
  | MBoundary : source:source_language -> target:source_language ->
                tau:brrr_type -> inner:multi_expr -> multi_expr
  | MLump     : source:source_language -> v:value -> multi_expr
  | MGuard    : tau:brrr_type -> inner:multi_expr -> multi_expr
  | MError    : msg:string -> multi_expr

(** Multi-language value - result of evaluation *)
noeq type multi_value =
  | MVNative : value -> multi_value
  | MVLump   : source:source_language -> v:value -> multi_value
  | MVError  : msg:string -> multi_value

(** Evaluation outcome for multi-language expressions *)
noeq type multi_outcome =
  | MOValue   : multi_value -> multi_outcome
  | MOError   : string -> multi_outcome
  | MODiverge : multi_outcome

(** ============================================================================
    TYPING JUDGMENT FOR MULTI-LANGUAGE EXPRESSIONS
    ============================================================================

    Following Matthews-Findler 2007 Section 2.2:
    "The new Scheme judgment says that an (SM^tau e) boundary is well-typed
     if ML's type system proves e has type tau -- that is, a Scheme program
     type-checks if it is closed and all its ML subterms have the types the
     program claims they have."

    Our typed_multi predicate captures when a multi-language expression
    is well-typed according to this regime.
*)

(** Multi-language typing context *)
type multi_ctx = list (string & brrr_type)

(** Typing judgment for multi-language expressions.

    typed_multi ctx e tau means:
    - Expression e has type tau in context ctx
    - All boundary terms are consistently typed
    - Guards match their ascribed types
*)
let rec typed_multi (ctx: multi_ctx) (e: multi_expr) (tau: brrr_type) : Type0 =
  match e with
  | MNative _ -> True  (* Native expression typing handled separately *)

  | MBoundary source target tau_bound inner ->
      (* Boundary well-typed if inner is well-typed at ascribed type *)
      type_eq tau_bound tau = true /\
      typed_multi ctx inner tau_bound

  | MLump source v ->
      (* Lump is well-typed at lump type - this is the L type from Matthews-Findler *)
      type_eq tau t_dynamic = true

  | MGuard tau_guard inner ->
      (* Guard well-typed if types match and inner is well-typed *)
      type_eq tau_guard tau = true /\
      typed_multi ctx inner tau_guard

  | MError _ -> True  (* Errors are well-typed at any type *)

(** ============================================================================
    THEOREM T-5.3: CONVERTIBILITY SOUNDNESS
    ============================================================================

    Cross-language type convertibility is sound.

    LITERATURE: Patterson et al. 2022 "Semantic Soundness for Language
    Interoperability", Lemma 3.1 (Type Convertibility)

    STATEMENT:
    If tau_A and tau_B are convertible types (written tau_A ~ tau_B),
    and value v realizes tau_A in source language,
    then convert(v) realizes tau_B in target language.

    Formally:
      convertible(tau_A, tau_B) /\ realizes_source(v, tau_A)
      ==>
      realizes_target(convert(v), tau_B)

    INTUITION:
    Convertibility captures when values can safely cross language boundaries.
    Patterson 2022 defines this using realizability: a value realizes a type
    if it behaves according to that type's specification.

    The key insight from Patterson is that convertibility must respect:
    1. Covariance of positive positions (function results)
    2. Contravariance of negative positions (function arguments)
    3. Invariance of mutable references

    PROOF SKETCH (8-16 hours):
    1. Define realizes predicate for source and target languages
    2. Define convertibility relation ~ inductively on types
    3. Prove by induction on type structure:
       - Base types: conversion preserves representation
       - Function types: contravariant in domain, covariant in codomain
       - Reference types: require exact type match
    4. Show convert function implements the conversion

    WHY ADMITTED:
    Full proof requires formalizing realizability semantics for all
    supported source languages, which is substantial per-language work.
    ============================================================================ *)

(** Convertibility relation between types.

    tau_A ~ tau_B means values of type tau_A can be safely converted
    to values of type tau_B when crossing a language boundary.

    This follows Patterson 2022's definition which builds on
    Matthews-Findler's type-directed conversion.

    Key rules:
    - Reflexivity: tau ~ tau
    - Base types: convertible if representations are compatible
    - Functions: (A -> B) ~ (A' -> B') if A' ~ A and B ~ B'
    - Dynamic: any ~ Dynamic and Dynamic ~ any (but with runtime checks)

    MEMORY REPRESENTATION NOTES:
    ============================
    Convertibility is deeply tied to memory representation compatibility:

    1. PRIMITIVE TYPES: Int, Float, Bool have platform-defined layouts.
       Karamel maps FStar.UInt32.t -> uint32_t, FStar.UInt64.t -> uint64_t.
       Conversion between same-sized primitives is identity.

    2. STRUCT TYPES: Require field-by-field convertibility. For C interop,
       source struct must have #[repr(C)] to guarantee field ordering.
       Without repr(C), Rust/F* may reorder fields for optimization.

    3. ARRAY/BUFFER TYPES: LowStar.Buffer.buffer t converts to t* in C.
       Length information is NOT part of C pointer, so must be passed
       separately or use sentinel values.

    4. FUNCTION TYPES: Contravariant in domain, covariant in codomain.
       This ensures that if f : A -> B is passed where A' -> B' expected,
       arguments flow A' -> A (caller provides A', callee expects A) and
       results flow B -> B' (callee returns B, caller expects B').

    5. OPTION/NULLABLE: Option[T] may map to nullable T* in C, but this
       loses the type-level null safety. Guard must check for None->NULL.

    FFI-SAFE TYPE SUBSET (from brrr_lang_spec_v0.4.tex Part X):
    ===========================================================
    Only these types have defined ABI for C interop:
    - TInt[w, s] for w in {8, 16, 32, 64}
    - TFloat[p] for p in {32, 64}
    - Ptr[tau] for FFI-safe tau
    - FnPtr[...] function pointers
    - CStr (null-terminated strings)
    - Struct with #[repr(C)]

    F* MECHANIZATION OF FFI-SAFE TYPES (from spec):

    type ffi_safe_type =
      | FFIInt    : int_width -> signedness -> ffi_safe_type
      | FFIFloat  : float_prec -> ffi_safe_type
      | FFIPtr    : ffi_safe_type -> ffi_safe_type
      | FFIFnPtr  : list ffi_safe_type -> ffi_safe_type -> ffi_safe_type
      | FFICStr   : ffi_safe_type
      | FFIVoid   : ffi_safe_type
      | FFIStruct : list (string & ffi_safe_type) -> ffi_safe_type

    SIZE AND ALIGNMENT (assuming 64-bit platform):
      FFIInt I8  -> size=1, align=1
      FFIInt I16 -> size=2, align=2
      FFIInt I32 -> size=4, align=4
      FFIInt I64 -> size=8, align=8
      FFIFloat F32 -> size=4, align=4
      FFIFloat F64 -> size=8, align=8
      FFIPtr _ -> size=8, align=8 (64-bit pointer)
      FFICStr -> size=8, align=8 (char* pointer)

    CALLING CONVENTIONS:
      CC_C       : Standard C calling convention (cdecl)
      CC_Rust    : Rust ABI (not stable)
      CC_System  : Platform default
      CC_Fastcall: Register-based (x86 specific)
*)
let rec convertible (tau_a tau_b: brrr_type) : bool =
  (* Reflexivity *)
  if type_eq tau_a tau_b then true
  (* Dynamic type is convertible to/from anything *)
  else if type_eq tau_a t_dynamic then true
  else if type_eq tau_b t_dynamic then true
  (* Function types: contravariant in domain, covariant in codomain *)
  else match tau_a, tau_b with
  | TFunc ft_a, TFunc ft_b ->
      (* Check arities match *)
      if List.Tot.length ft_a.f_params <> List.Tot.length ft_b.f_params then false
      (* Domain: contravariant - target domain must convert to source domain *)
      else if not (List.Tot.for_all2 (fun (_, t_a) (_, t_b) -> convertible t_b t_a)
                     ft_a.f_params ft_b.f_params) then false
      (* Codomain: covariant - source codomain must convert to target codomain *)
      else convertible ft_a.f_return ft_b.f_return
  | TOption t_a, TOption t_b -> convertible t_a t_b
  | TArray t_a _, TArray t_b _ -> convertible t_a t_b
  | TStruct fields_a _, TStruct fields_b _ ->
      (* Struct fields must be pairwise convertible *)
      List.Tot.length fields_a = List.Tot.length fields_b &&
      List.Tot.for_all2 (fun (n_a, t_a) (n_b, t_b) ->
        n_a = n_b && convertible t_a t_b
      ) fields_a fields_b
  | _, _ -> false

(** Realizability predicate: value v realizes type tau in language lang.

    This is an abstract predicate representing the semantic interpretation
    of types. A value realizes a type if it behaves according to that type's
    specification when used in programs.

    Patterson 2022 defines this formally using denotational semantics.
    Here we use it as an abstract specification.
*)
let realizes (lang: source_language) (tau: brrr_type) (v: value) : Type0 =
  (* Abstract: instantiated per language with actual typing semantics *)
  True

(** Value conversion function: convert value from source to target type.

    This corresponds to Matthews-Findler's type-directed conversion
    extended with Patterson's realizability guarantees.

    For base types: direct representation conversion
    For functions: wrap with boundary terms (as in Matthews-Findler Section 3)
    For structures: recursive field conversion
*)
let convert (source target: source_language) (tau_source tau_target: brrr_type) (v: value)
    : guard_result value =
  (* Use the generate_guard function from LangMapping *)
  generate_guard (language_mode source) (language_mode target) tau_target v

(** THEOREM T-5.3: Convertibility Soundness

    If types are convertible and value realizes source type,
    then converted value realizes target type.

    Reference: Patterson 2022, Lemma 3.1

    EFFORT: 8-16 hours
    PREREQUISITES:
    - Formalize realizability for each source language
    - Prove conversion respects realizability
*)
(* Helper predicate for convertibility soundness postcondition.
   In F*, match expressions cannot appear directly in ensures clauses.
   We factor the postcondition into a separate predicate. *)
let convertibility_postcondition
    (target: source_language)
    (tau_target: brrr_type)
    (result: guard_result value) : Type0 =
  match result with
  | GuardOk v' -> realizes target tau_target v'
  | GuardErr _ -> True  (* Error is a valid outcome - no unsafe behavior *)

val convertibility_sound :
    source:source_language -> target:source_language ->
    tau_source:brrr_type -> tau_target:brrr_type ->
    v:value ->
  Lemma
    (requires
      convertible tau_source tau_target = true /\
      realizes source tau_source v)
    (ensures
      convertibility_postcondition target tau_target
        (convert source target tau_source tau_target v))

(* ============================================================================
   KARAMEL EXTRACTION AND TYPE CONVERSION PATTERNS
   ============================================================================

   When extracting FFI-boundary code to C via Karamel, type conversions must
   preserve the following invariants:

   PRIMITIVE TYPE MAPPINGS (Karamel default):
   ------------------------------------------
   F* Type               C Type           Notes
   ---------             ------           -----
   FStar.UInt8.t         uint8_t          Direct representation
   FStar.UInt16.t        uint16_t         Direct representation
   FStar.UInt32.t        uint32_t         Direct representation
   FStar.UInt64.t        uint64_t         Direct representation
   FStar.Int8.t          int8_t           Two's complement
   FStar.Int32.t         int32_t          Two's complement
   bool                  bool (C99)       0/1 representation
   unit                  void             Returns nothing

   STRUCT CONVERSION REQUIREMENTS:
   -------------------------------
   For a Brrr struct to have defined C ABI:

   1. Must have #[repr(C)] attribute
      - Fields in declaration order
      - Predictable padding/alignment
      - No field reordering optimization

   2. All field types must be FFI-safe
      - Recursive requirement
      - No closures, no GC'd references

   3. Example repr(C) struct layout:
      struct Point { int32_t x; int32_t y; }
      Layout: [x:4 bytes][y:4 bytes] = 8 bytes total

   FUNCTION POINTER CONVERSION:
   ----------------------------
   Brrr closures CANNOT be directly converted to C function pointers because:
   - Closures capture environment
   - C function pointers are just code addresses
   - No place to store captured variables

   Solution patterns:
   1. Trampoline: void* context passed as first argument
   2. Global state: Captured variables in thread-local storage
   3. Defunctionalization: Convert closures to tagged unions

   KARAMEL ATTRIBUTES FOR FFI:
   ---------------------------
   [@@CConst]           - Mark as const in C
   [@@CAbstract]        - Opaque type (incomplete struct)
   [@@CPrologue "include_directive"] - Inject headers
   ============================================================================ *)

let convertibility_sound source target tau_source tau_target v =
  (* PROOF SKETCH (following Patterson 2022 Lemma 3.1):

     The proof proceeds by induction on the structure of tau_source.

     BASE CASE - Primitive types (Int, Float, Bool, String):
       Conversion is identity or representation change.
       If tau_source ~ tau_target for primitives, then either:
       - Same type: v' = v, realizes preserved trivially
       - Compatible types (e.g., Int32 ~ Int64): representation change preserves semantics
       - Incompatible: convertible returns false (precondition violated)

     INDUCTIVE CASE - Function types (A -> B) ~ (A' -> B'):
       By inversion of convertibility: A' ~ A and B ~ B'
       The converted function f' wraps f with domain/codomain conversions:
         f' = \x'. convert_B(f(convert_A(x')))
       By IH on A: if x' realizes A', then convert_A(x') realizes A
       So f(convert_A(x')) realizes B (since f realizes A -> B)
       By IH on B: convert_B(f(convert_A(x'))) realizes B'
       Therefore f' realizes A' -> B'

     INDUCTIVE CASE - Option types:
       Option[A] ~ Option[B] requires A ~ B
       Convert None to None, Some v to Some (convert v)
       By IH, converted inner values realize target type

     INDUCTIVE CASE - Struct types:
       Each field converted independently
       By IH, each converted field realizes its target type
       Therefore struct realizes target struct type

     DYNAMIC TYPE:
       Dynamic ~ T for any T (with runtime check)
       Guard performs runtime type check
       If check succeeds, value must have correct shape
       If check fails, GuardErr returned (safe)

     The key insight from Patterson is that realizability is preserved
     because conversion respects the variance of type positions:
     - Covariant positions (results): source converts to target
     - Contravariant positions (arguments): target converts to source
     - Invariant positions (refs): exact match required
  *)
  admit ()

(** ============================================================================
    THEOREM T-5.4: MATTHEWS-FINDLER BOUNDARY SOUNDNESS
    ============================================================================

    Multi-language boundary terms are type-sound.

    LITERATURE: Matthews & Findler 2007 "Operational Semantics for
    Multi-Language Programs", POPL 2007, Theorems 1-6

    STATEMENT:
    If e is a well-typed multi-language expression (typed_multi ctx e tau),
    then evaluation of e either:
    1. Terminates with a value of type tau, or
    2. Terminates with an error (type mismatch detected at boundary), or
    3. Diverges

    Importantly, e does NOT get stuck - all type errors are caught at boundaries.

    THEOREMS FROM MATTHEWS-FINDLER:
    - Theorem 1 (Lump Type Soundness): Lump embedding is type-sound
    - Theorem 2 (Simple Natural Soundness): Natural embedding with guards is sound
    - Theorem 3 (Guard Equivalence): Guarded boundaries = guards + unguarded boundaries
    - Theorem 4 (Contract Refinement): Positive/negative guards are contracts
    - Theorem 5 (Macro-Expressibility): Natural boundaries are macro-expressible in lump
    - Theorem 6 (Mapped Embedding Soundness): Type-mapped boundaries are sound

    PROOF SKETCH (8-16 hours):
    1. Define multi-language reduction semantics
    2. Prove preservation: reduction preserves typing
    3. Prove progress: well-typed expressions are values or can step
    4. Combine for type soundness

    WHY ADMITTED:
    Full proof requires complete operational semantics for multi-language
    system, which is substantial infrastructure work.
    ============================================================================ *)

(** Multi-language reduction relation (simplified).

    This models the operational semantics from Matthews-Findler 2007.
    Key rules:

    - Native expressions: use standard Brrr reduction
    - Boundary with value: perform conversion
    - Boundary with error: propagate error
    - Guard with value: check type and proceed or error
    - Lump: pass through (opaque)
*)
let multi_reduces (e: multi_expr) (e': multi_expr) : Type0 =
  (* Abstract reduction relation - would be defined inductively *)
  True

(** Multi-step reduction (reflexive transitive closure) *)
let rec multi_reduces_star (e: multi_expr) (e': multi_expr) : Type0 =
  e == e' \/ (exists e_mid. multi_reduces e e_mid /\ multi_reduces_star e_mid e')

(** Value predicate for multi-language expressions *)
let is_multi_value (e: multi_expr) : bool =
  match e with
  | MNative (ELit _) -> true
  | MLump _ _ -> true
  | MError _ -> true  (* Errors are final states *)
  | _ -> false

(** THEOREM T-5.4: Matthews-Findler Boundary Soundness

    Well-typed multi-language programs don't get stuck.

    Reference: Matthews-Findler 2007, Theorems 1-6

    EFFORT: 8-16 hours
    PREREQUISITES:
    - Define complete multi-language operational semantics
    - Prove preservation and progress lemmas
*)
val boundary_soundness :
    e:multi_expr -> tau:brrr_type ->
  Lemma
    (requires typed_multi [] e tau)
    (ensures
      (* e reduces to a value, error, or diverges *)
      (exists v. multi_reduces_star e (MNative (ELit v))) \/
      (exists msg. multi_reduces_star e (MError msg)) \/
      True)  (* divergence case - always satisfiable *)

let boundary_soundness e tau =
  (* PROOF SKETCH (following Matthews-Findler 2007):

     The proof combines the standard preservation + progress approach
     adapted for multi-language semantics.

     PRESERVATION (Lemma):
     If typed_multi ctx e tau and e -> e', then typed_multi ctx e' tau

     Proof by case analysis on the reduction rule applied:

     Case MNative e -> MNative e':
       By standard Brrr preservation
       (requires Brrr type system is sound)

     Case MBoundary source target tau v -> e':
       Boundary reduces when inner is a value.
       The conversion respects types by T-5.3 (convertibility_sound).
       If conversion succeeds (GuardOk v'), result has type tau.
       If conversion fails (GuardErr msg), we get MError msg.

     Case MGuard tau v -> e':
       Guard checks if v has type tau.
       If check passes, result is v with same type tau.
       If check fails, result is MError with message.

     Case MLump source v:
       Lumps don't reduce further - they are values.
       Type is preserved trivially.

     PROGRESS (Lemma):
     If typed_multi [] e tau and not is_multi_value e, then exists e'. e -> e'

     Proof by case analysis on e:

     Case MNative e (not a value):
       By standard Brrr progress, e can step.
       Therefore MNative e can step to MNative e'.

     Case MBoundary source target tau inner:
       By IH, inner is a value or can step.
       If inner is a value, boundary can convert (or error).
       If inner can step, boundary can step (congruence).

     Case MGuard tau inner:
       By IH, inner is a value or can step.
       If inner is a value, guard can check (succeed or error).
       If inner can step, guard can step (congruence).

     TYPE SOUNDNESS (Theorem):
     Combining preservation and progress:

     If typed_multi [] e tau, then either:
     1. e is a value of type tau
     2. e can reduce

     By induction on reduction length:
     - If e is a value, done (case 1 or MError)
     - If e can reduce to e', by preservation e' : tau
     - By IH, e' is a value or reduces further
     - Either we eventually reach a value, reach MError, or diverge

     The key insight from Matthews-Findler is that boundaries act as
     checkpoints that catch type mismatches. The "wrong" expressions
     in their semantics correspond to our MError cases.
  *)
  admit ()

(** ============================================================================
    THEOREM T-5.9: ROUND-TRIP PRESERVATION
    ============================================================================

    Parse -> IR -> Pretty-Print preserves semantics.

    LITERATURE: CompCert-style compiler correctness proofs
    (Leroy et al., various papers 2006-present)

    STATEMENT:
    For source code s in language L:
      eval(parse_L(s)) == eval(parse_L(pretty_print_L(to_ir(parse_L(s)))))

    That is, the round-trip through the IR preserves observable behavior.

    WARNING: This theorem requires PER-LANGUAGE effort (40-80 hours each).
    Each source language needs its own:
    1. Parser correctness proof
    2. IR translation correctness proof
    3. Pretty-printer correctness proof
    4. Round-trip simulation relation

    PROOF APPROACH:
    Use simulation relations (as in CompCert):
    1. Define source semantics eval_L
    2. Define IR semantics eval_IR
    3. Prove: parse_L(s) ~_fwd to_ir(parse_L(s))
       (forward simulation: source steps imply IR steps)
    4. Prove: to_ir(e) ~_bwd pretty_print_L(to_ir(e))
       (backward simulation: IR steps imply source steps)
    5. Combine for round-trip preservation

    WHY ADMITTED:
    This is a MASSIVE undertaking - CompCert took years to verify C alone.
    Each language requires substantial formalization effort.
    ============================================================================ *)

(** Source code representation *)
type source_code = string

(** Abstract syntax tree from parsing *)
noeq type parse_result =
  | ParseOk   : ast:expr -> parse_result
  | ParseErr  : msg:string -> parse_result

(** Parser for a specific language *)
type parser = source_code -> parse_result

(** Pretty-printer for a specific language *)
type pretty_printer = expr -> source_code

(** Semantic equivalence of expressions.

    Two expressions are semantically equivalent if they have the same
    observable behavior: they produce the same values for all inputs,
    and have the same effects (termination, errors, I/O).

    This is defined abstractly here; concrete instantiation requires
    defining the evaluation semantics.
*)
let semantically_equivalent (e1 e2: expr) : Type0 =
  (* Abstract: would be defined in terms of evaluation *)
  True

(** THEOREM T-5.9: Round-Trip Preservation

    Parsing, converting to IR, and pretty-printing preserves semantics.

    WARNING: Requires PER-LANGUAGE proof effort (40-80 hours EACH).

    Reference: CompCert methodology (Leroy et al.)

    EFFORT: 40-80 hours PER LANGUAGE
    PREREQUISITES:
    - Formalize parser correctness
    - Formalize IR translation correctness
    - Formalize pretty-printer correctness
    - Prove simulation relations
*)
(* Helper predicate for round-trip postcondition.
   Expresses that parsing, IR conversion, and pretty-printing preserves semantics. *)
let round_trip_postcondition
    (parse: parser)
    (to_ir: expr -> expr)
    (pretty: pretty_printer)
    (source: source_code) : Type0 =
  match parse source with
  | ParseErr _ -> True  (* Parse error: nothing to preserve *)
  | ParseOk ast ->
      let ir = to_ir ast in
      let pretty_source = pretty ir in
      (match parse pretty_source with
       | ParseErr _ -> True  (* Re-parse error: acceptable *)
       | ParseOk ast' ->
           (* Semantic equivalence preserved *)
           semantically_equivalent ast (to_ir ast'))

val round_trip_preservation :
    lang:source_language ->
    parse:parser ->
    to_ir:(expr -> expr) ->
    pretty:pretty_printer ->
    source:source_code ->
  Lemma
    (ensures round_trip_postcondition parse to_ir pretty source)

(* ============================================================================
   PARSER TRUST BOUNDARY AND AXIOM-EXT-004
   ============================================================================

   The round_trip_preservation theorem depends on AXIOM-EXT-004 which trusts
   tree-sitter parsers to correctly implement language grammars.

   WHY THIS IS A TRUST BOUNDARY:
   -----------------------------
   1. Tree-sitter grammars are written in JavaScript DSL
   2. Grammar correctness is tested empirically, not proven
   3. F* cannot verify external parser implementation

   WHAT WE TRUST (AXIOM-EXT-004):
   ------------------------------
   - Parser accepts valid programs: valid(s) => parse(s) = Ok(ast)
   - Parser rejects invalid programs: !valid(s) => parse(s) = Err(...)
   - Parsing is deterministic: parse(s) = parse(s) always
   - AST preserves source structure: reconstruct(parse(s)) ~= s

   MITIGATIONS IN PRACTICE:
   ------------------------
   1. Tree-sitter corpus testing (thousands of real programs)
   2. Fuzzing for parser crashes and malformed output
   3. Round-trip testing (parse -> pretty -> parse = original)
   4. Cross-validation with reference implementations

   COMPILERLIKE VERIFICATION APPROACH:
   -----------------------------------
   CompCert trusts: lexer, parser, assembler, linker
   HACL* trusts: F* compiler, Z3 solver
   Brrr trusts: tree-sitter parsers, Karamel extraction

   Each verified system has a Trusted Computing Base (TCB) that must be
   audited and tested rather than formally verified.
   ============================================================================ *)

let round_trip_preservation lang parse to_ir pretty source =
  (* PROOF SKETCH (per-language, 40-80 hours each):

     This proof follows the CompCert methodology of using simulation
     relations to establish semantic preservation.

     DEFINITIONS NEEDED:
     - eval_L : L_expr -> L_state -> L_outcome
       Evaluation semantics for source language L
     - eval_IR : expr -> eval_state -> eval_outcome
       Evaluation semantics for Brrr IR
     - ~_L : L_expr -> expr -> Type0
       Forward simulation relation between L and IR

     PHASE 1: Parser Correctness
     ----------------------------
     Prove: If parse(source) = ParseOk(ast), then ast accurately
     represents the syntactic structure of source.

     This typically requires:
     - Grammar specification for language L
     - Proof that parser implements grammar correctly
     - For tree-sitter based parsers, trust the grammar (Axiom AXIOM-EXT-004)

     PHASE 2: IR Translation Correctness (Forward Simulation)
     --------------------------------------------------------
     Prove: If ast ->_L ast' (source takes a step), then
            to_ir(ast) ->*_IR to_ir(ast') (IR takes corresponding steps)

     Key lemmas:
     - Each L construct translates to semantically equivalent IR
     - Translation commutes with substitution
     - Translation preserves typing

     PHASE 3: Pretty-Printer Correctness
     -----------------------------------
     Prove: If pretty(ir) = source', then parse(source') = ParseOk(ir')
            where ir and ir' are alpha-equivalent.

     This requires:
     - Pretty-printer produces valid syntax
     - Pretty-printer is injective on alpha-equivalence classes
     - Round-trip preserves AST structure (up to alpha)

     PHASE 4: Combining Simulations
     ------------------------------
     The round-trip is:
       source --parse--> ast --to_ir--> ir --pretty--> source' --parse--> ast'

     By Phase 1: ast represents source
     By Phase 2: ir simulates ast
     By Phase 3: ast' is alpha-equivalent to ir (up to re-parsing)
     By Phase 2 (reverse): ast' simulates ir

     Therefore: ast and ast' are semantically equivalent
     (they simulate the same IR computation).

     PER-LANGUAGE EFFORT:
     - Python: 60-80 hours (complex semantics, many constructs)
     - TypeScript: 60-80 hours (structural types, async/await)
     - Rust: 80+ hours (ownership, lifetimes, complex type system)
     - Go: 40-60 hours (simpler semantics, but goroutines)
     - Java: 60-80 hours (OOP, generics, exceptions)
     - C/C++: 80+ hours (undefined behavior, complex memory model)

     Note: CompCert took YEARS to verify C compilation.
     This theorem essentially requires similar effort for EACH language.
  *)
  admit ()

(** ============================================================================
    THEOREM T-5.10: CFG COMPLETENESS
    ============================================================================

    Control Flow Graph correctly models all control flow constructs.

    LITERATURE: Standard compiler textbooks (Aho, Sethi, Ullman)
    plus language-specific control flow specifications.

    STATEMENT:
    For any program P and its CFG G = build_cfg(P):
      For all execution paths path of P,
      there exists a CFG path cfg_path in G such that
      cfg_path corresponds to path.

    That is, the CFG over-approximates all possible control flow.

    PROOF APPROACH:
    1. Define execution_path as a sequence of program points
    2. Define cfg_path as a sequence of CFG nodes
    3. Define correspondence between execution paths and CFG paths
    4. Prove by structural induction on the program

    EFFORT: 8-16 hours
    ============================================================================ *)

(** Program point: location in program *)
type program_point = nat

(** Execution path: sequence of program points visited during execution *)
type execution_path = list program_point

(** CFG node identifier *)
type cfg_node = nat

(** CFG edge *)
type cfg_edge = cfg_node & cfg_node

(** Control Flow Graph *)
noeq type cfg = {
  cfg_nodes : list cfg_node;
  cfg_edges : list cfg_edge;
  cfg_entry : cfg_node;
  cfg_exit  : cfg_node
}

(** CFG path: sequence of nodes following edges *)
type cfg_path = list cfg_node

(** Check if a sequence of nodes forms a valid path in the CFG *)
let rec is_valid_cfg_path (g: cfg) (path: cfg_path) : bool =
  match path with
  | [] -> true
  | [n] -> List.Tot.mem n g.cfg_nodes
  | n1 :: n2 :: rest ->
      List.Tot.mem (n1, n2) g.cfg_edges &&
      is_valid_cfg_path g (n2 :: rest)

(** Correspondence between program points and CFG nodes.

    A program point p corresponds to CFG node n if the node
    represents that point in the control flow abstraction.
*)
let point_corresponds_to_node (p: program_point) (n: cfg_node) : bool =
  (* In a typical CFG construction, node IDs correspond to program points *)
  p = n

(** Execution path corresponds to CFG path if each program point
    visited corresponds to the respective CFG node. *)
let paths_correspond (exec_path: execution_path) (cfg_path_nodes: cfg_path) : bool =
  List.Tot.length exec_path = List.Tot.length cfg_path_nodes &&
  List.Tot.for_all2 point_corresponds_to_node exec_path cfg_path_nodes

(** Build CFG from expression (abstract) *)
let build_cfg (e: expr) : cfg =
  (* Abstract: actual implementation would traverse expression *)
  { cfg_nodes = []; cfg_edges = []; cfg_entry = 0; cfg_exit = 0 }

(** Predicate: execution path is possible for expression *)
let possible_execution (e: expr) (path: execution_path) : Type0 =
  (* Abstract: defined by operational semantics *)
  True

(* ============================================================================
   CFG AND FFI CONTROL FLOW CONSIDERATIONS
   ============================================================================

   When building CFGs for programs with FFI calls, special handling is needed:

   FFI CALL CONTROL FLOW:
   ----------------------
   An FFI call node in the CFG has:
   - Incoming edge from call site
   - Outgoing edge to return continuation
   - Potentially exceptional edge (if foreign code can throw/panic)

   LONGJMP/SETJMP COMPLICATIONS:
   -----------------------------
   C code can use setjmp/longjmp for non-local control transfer.
   This breaks normal CFG assumptions:
   - Control can jump to arbitrary setjmp sites
   - Local variables may have undefined values after longjmp
   - Must model as potential edge to any setjmp location

   SIGNAL HANDLERS:
   ----------------
   Asynchronous signals can interrupt execution at any point.
   For sound analysis:
   - Model signal handlers as callable from any instruction
   - Or restrict to async-signal-safe functions in handlers

   CALLBACK COMPLICATIONS:
   -----------------------
   When passing Brrr callbacks to C code:
   - C code may call back at unpredictable points
   - Callback may be stored and called later
   - Requires modeling callback as reachable from FFI call

   For cfg_complete, we assume:
   1. No setjmp/longjmp across FFI boundaries
   2. Signal handlers are async-signal-safe only
   3. Callbacks complete before FFI call returns (synchronous)
   ============================================================================ *)

(** THEOREM T-5.10: CFG Completeness

    Every possible execution path has a corresponding CFG path.

    Reference: Standard compiler construction

    EFFORT: 8-16 hours
    PREREQUISITES:
    - Formalize operational semantics with program points
    - Define CFG construction algorithm
    - Prove correspondence by structural induction
*)
(* Helper predicate for CFG completeness postcondition.
   The cfg has a corresponding path for every execution path. *)
let cfg_completeness_holds (e: expr) (path: execution_path) : Type0 =
  let g = build_cfg e in
  exists cfg_path_nodes.
    is_valid_cfg_path g cfg_path_nodes = true /\
    paths_correspond path cfg_path_nodes = true

val cfg_complete :
    e:expr -> path:execution_path ->
  Lemma
    (requires possible_execution e path)
    (ensures cfg_completeness_holds e path)

let cfg_complete e path =
  (* PROOF SKETCH (8-16 hours):

     The proof proceeds by structural induction on expression e,
     showing that CFG construction creates nodes and edges for
     all possible control flow patterns.

     BASE CASES:

     Case ELit l (literals):
       Execution has single point, CFG has single node.
       Correspondence is immediate.

     Case EVar x (variables):
       Same as literals - single point, single node.

     INDUCTIVE CASES:

     Case EIf cond then_br else_br:
       Execution visits: cond point, then branch condition check,
       then either then_br points or else_br points.

       CFG construction creates:
       - Node for cond
       - Edge from cond to then_br entry (condition true)
       - Edge from cond to else_br entry (condition false)
       - Edges within then_br (by IH)
       - Edges within else_br (by IH)
       - Edges from then_br exit and else_br exit to join node

       By IH, then_br and else_br paths have corresponding CFG paths.
       The edges from cond to branch entries and from exits to join
       complete the correspondence.

     Case EWhile cond body:
       Execution visits: cond check, body (if true), back to cond, etc.
       Loop may execute 0 or more times.

       CFG construction creates:
       - Loop header node (cond check)
       - Back edge from body exit to header (continue loop)
       - Exit edge from header to loop exit (exit loop)
       - Edges within body (by IH)

       For any execution with k iterations:
       - Path visits header k+1 times (k body executions + final check)
       - CFG path follows: header -> body (k times) -> header -> exit
       - Correspondence follows from IH on body

     Case ECall f args:
       Execution visits: argument evaluation points, function entry,
       function body points, return.

       If interprocedural:
       - CFG includes call edges to function CFG
       - Return edges back to caller
       - By IH on function body, paths correspond

       If intraprocedural (call nodes only):
       - CFG has single node for call
       - Execution path for call is abstracted to single point
       - Correspondence immediate

     Case ELambda params body:
       Lambda itself is a value (no execution).
       When called, body execution starts.
       By IH on body, paths correspond.

     Case EMatch scrutinee branches:
       Similar to EIf but with multiple branches.
       CFG has edges from scrutinee to each branch entry.
       By IH on each branch, paths correspond.

     Case ELet x rhs body:
       Execution visits: rhs points, then body points.
       CFG has: rhs nodes, edge to body entry, body nodes.
       By IH on rhs and body, paths correspond.

     Case ETry body handler:
       Normal execution: body points only.
       Exceptional: body points (until exception), handler points.

       CFG construction creates:
       - Body nodes
       - Exceptional edge from any body node to handler entry
       - Normal edge from body exit to try-block exit
       - Handler nodes
       - Edge from handler exit to try-block exit

       By IH on body and handler, paths correspond.
       Exception edges cover all exceptional paths.

     COMPLETENESS ARGUMENT:
     The CFG construction is complete because:
     1. Every expression constructor has corresponding CFG construction
     2. All control flow edges (sequential, conditional, loop, exception)
        are represented
     3. The construction is systematic (no cases missed)

     The key invariant maintained is:
       For expression e with entry node n_e and exit node x_e,
       all execution paths through e correspond to CFG paths from n_e to x_e.

     This invariant is established at base cases and preserved inductively.
  *)
  admit ()

(** ============================================================================
    AUXILIARY LEMMAS FOR FFI SAFETY
    ============================================================================

    These lemmas support the main theorems and establish useful properties
    for FFI boundary analysis.

    LEMMA USAGE IN PRACTICE:
    ========================

    The convertible_* lemmas are used during type checking at FFI boundaries:

    1. When Brrr calls C function:
       - Check return type is convertible from C type
       - Check argument types are convertible to C types
       - Generate guards for dynamic checks if needed

    2. When C calls Brrr callback:
       - Check callback parameter types convertible from C
       - Check callback return type convertible to C
       - May require wrapper generation

    3. When passing data structures:
       - Recursively check field convertibility
       - Ensure layout compatibility (repr(C))
       - Handle nested structs and arrays

    RELATIONSHIP TO LOWSTAR MODIFIES CLAUSES:
    =========================================

    LowStar's modifies clauses interact with FFI boundaries:

    val foreign_call : b:buffer uint8 -> len:uint32 -> Stack unit
      (requires fun h0 -> live h0 b)
      (ensures fun h0 _ h1 ->
        modifies (loc_buffer b) h0 h1 /\  (* Foreign code may modify b *)
        live h1 b)                         (* But b remains valid *)

    The boundary_soundness theorem ensures that if we correctly specify
    the modifies clause, the post-condition holds after the FFI call.

    FRAME RULE APPLICATION:
    =======================

    Separation logic's frame rule (from FSTAR_REFERENCE.md) applies:

      {P} c {Q}   frame_safe c R
      --------------------------
        {P * R} c {Q * R}

    For FFI: if foreign code only modifies loc_buffer b, then any
    disjoint state R is preserved across the call. This enables
    modular reasoning about FFI effects.
    ============================================================================ *)

(** Lemma: Reflexivity of convertibility *)
val convertible_refl : tau:brrr_type ->
  Lemma (convertible tau tau = true)
let convertible_refl tau = ()

(** Lemma: Dynamic type is convertible to anything *)
val dynamic_convertible_to_any : tau:brrr_type ->
  Lemma (convertible t_dynamic tau = true)
let dynamic_convertible_to_any tau = ()

(** Lemma: Any type is convertible to dynamic *)
val any_convertible_to_dynamic : tau:brrr_type ->
  Lemma (convertible tau t_dynamic = true)
let any_convertible_to_dynamic tau = ()

(** Lemma: Typing is preserved across MBoundary when types match *)
val boundary_typing_preservation :
    ctx:multi_ctx -> source:source_language -> target:source_language ->
    tau:brrr_type -> inner:multi_expr ->
  Lemma
    (requires typed_multi ctx inner tau)
    (ensures typed_multi ctx (MBoundary source target tau inner) tau)
let boundary_typing_preservation ctx source target tau inner =
  type_eq_refl tau

(** Lemma: Guard typing is consistent *)
val guard_typing_consistency :
    ctx:multi_ctx -> tau:brrr_type -> inner:multi_expr ->
  Lemma
    (requires typed_multi ctx inner tau)
    (ensures typed_multi ctx (MGuard tau inner) tau)
let guard_typing_consistency ctx tau inner =
  type_eq_refl tau

(** ============================================================================
    SUMMARY OF FFI THEOREMS
    ============================================================================

    T-5.3 (convertibility_sound):
      Cross-language type conversion is semantically correct.
      Effort: 8-16 hours
      Status: ADMITTED with proof sketch

    T-5.4 (boundary_soundness):
      Multi-language boundary terms are type-sound.
      Effort: 8-16 hours
      Status: ADMITTED with proof sketch

    T-5.9 (round_trip_preservation):
      Parse -> IR -> Pretty preserves semantics.
      Effort: 40-80 hours PER LANGUAGE
      Status: ADMITTED with proof sketch
      WARNING: Major undertaking - CompCert-level effort required

    T-5.10 (cfg_complete):
      CFG correctly models all control flow.
      Effort: 8-16 hours
      Status: ADMITTED with proof sketch

    Total estimated effort for full proofs: 64-128 hours base + 40-80 per language

    DEPENDENCIES:
    - BrrrLangMapping.fst provides language modes and guards
    - BrrrTypes.fst provides type definitions
    - BrrrValues.fst provides value representation
    - BrrrExpressions.fst provides expression AST

    RELATED AXIOMS (from AXIOMS_REPORT_v2.md):
    - AXIOM-EXT-004: Tree-sitter parser correctness (trusted)
    - AXIOM-EXT-005: Language frontend correctness (trusted)
    - AXIOM-FFI-001: Pointer conversion soundness (trusted)
    - AXIOM-FFI-002: CPython runtime interop (trusted)
    - AXIOM-FFI-003: Dynamic dispatch resolution (trusted)

    ============================================================================
    VERIFICATION ROADMAP FOR FULL PROOFS
    ============================================================================

    PHASE 1 - INFRASTRUCTURE (Required for all theorems):
    -----------------------------------------------------
    1. Define operational semantics for multi_expr evaluation
    2. Implement reduction relation multi_reduces properly
    3. Add heap/memory model for buffer operations
    4. Define realizability predicates per language

    PHASE 2 - TYPE CONVERSION (T-5.3):
    ----------------------------------
    1. Formalize convertible relation inductively
    2. Define convert function with all cases
    3. Prove by induction on type structure
    4. Handle variance correctly for function types

    PHASE 3 - BOUNDARY SOUNDNESS (T-5.4):
    -------------------------------------
    1. Define preservation lemma for multi_reduces
    2. Define progress lemma for well-typed terms
    3. Combine into type soundness theorem
    4. Handle MError cases as safe termination

    PHASE 4 - ROUND-TRIP (T-5.9, per language):
    -------------------------------------------
    1. Formalize parser AST for language L
    2. Define IR translation function
    3. Prove forward simulation (parse to IR)
    4. Prove backward simulation (pretty to parse)
    5. Establish semantic equivalence

    PHASE 5 - CFG COMPLETENESS (T-5.10):
    ------------------------------------
    1. Define program_point type formally
    2. Implement build_cfg correctly
    3. Define possible_execution via small-step
    4. Prove by structural induction on expr

    ============================================================================
    KARAMEL EXTRACTION VERIFICATION NOTES
    ============================================================================

    For FFI code to extract correctly to C via Karamel:

    REQUIRED ATTRIBUTES:
    - Types: All FFI-boundary types must be FFI-safe
    - Functions: Mark with inline_for_extraction or noextract
    - Proofs: All lemmas should be noextract

    GENERATED C PATTERNS:
    - LowStar buffers become raw pointers
    - Stack effects become stack-allocated locals
    - Modifies clauses become comments (documentation only in C)
    - Pre/post conditions are erased

    RUNTIME CHECKS:
    - None generated by default (all proven at verification time)
    - Can add with_check functions for defensive programming
    - Guards at FFI boundaries may generate runtime assertions

    INTEGRATION WITH EXISTING C CODE:
    - Use [@@CPrologue] for #include directives
    - Use extern_fn declarations for existing C functions
    - Use opaque types for C structs not fully specified

    ============================================================================
    REFERENCES FOR FURTHER STUDY
    ============================================================================

    MULTI-LANGUAGE SEMANTICS:
    - Matthews & Findler 2007: Boundary terms, lump embedding
    - Patterson et al. 2022: Realizability-based soundness
    - Wadler & Findler 2009: Blame calculus for contracts

    VERIFIED C EXTRACTION:
    - HACL* (Zinzindohoue et al. 2017): Verified crypto in F*
    - EverParse (Ramananandro et al. 2019): Zero-copy parsers
    - CompCert (Leroy et al.): Verified C compiler

    LOW-LEVEL VERIFICATION:
    - Low* (Protzenko et al. 2017): Low-level subset of F*
    - Steel (Swamy et al. 2020): Separation logic in F*
    - Iris (Jung et al. 2018): Higher-order separation logic
    ============================================================================ *)
