
  ---
  REFERENCE F* CODEBASE ANALYSIS

  HACL (991 F files) - Verified Crypto Library**

  Architecture Pattern:
  specs/           # Pure functional specifications (Spec.*.fst)
    └── lemmas/    # Proofs connecting specs
  code/            # Low-level verified implementations (Hacl.*.fst)
    └── Hacl.Spec.* # Implementation-level specs
  lib/             # Shared library (Lib.*.fst/fsti)
  dist/            # Generated C code via Karamel extraction

  Key Patterns:

  1. Interface/Implementation Separation (.fsti/.fst):
    - .fsti declares val signatures with pre/post conditions
    - .fst provides implementations
    - Example: Lib.Sequence.fsti has 400 lines of spec, Lib.Sequence.fst has implementations
  2. Spec-to-Impl Layering:
  Spec.SHA2.fst        # Mathematical specification
    ↓ proves equiv to
  Hacl.Spec.SHA2.fst   # Implementation-level spec
    ↓ Low* refinement
  Hacl.Hash.SHA2.fst   # Imperative low-level code
    ↓ Karamel extraction
  Hacl_Hash_SHA2.c     # Generated C
  3. Z3 Tuning via Options:
  #set-options "--z3rlimit 25 --fuel 0 --ifuel 1"
  #push-options "--max_fuel 1 --z3rlimit 200"
  4. Admits Strategy: Only for SIMD intrinsics (Lib.IntVector.fst) where full verification isn't practical - ~20 admits total in 991 files.
  5. Lemma Structure:
  val lemma_foo: x:t -> y:t -> 
    Lemma (requires P x y) (ensures Q x y)
    [SMTPat (foo x y)]  (* SMT trigger pattern *)

  ---
  EverParse (576 F files) - Verified Parser Generator*

  Architecture Pattern:
  src/3d/          # Main compiler
    Ast.fst        # Source AST (like brrr-lang syntax)
    Binding.fst    # Name resolution & type checking
    Target.fst     # Target IR (like brrr-machine CPG)
    Desugar.fst    # AST transformations
    TranslateForInterpreter.fst  # Code generation

  Key Patterns:

  1. AST with Metadata (directly applicable to brrr-lang):
  noeq type with_meta_t 'a = {
    v: 'a;         (* The value *)
    range: range;  (* Source location *)
    comments: comments
  }
  2. Environment Threading:
  noeq type env = {
    this: option ident;
    generics: list generic_param;
    locals: H.t ident' (ident' & typ & bool);  (* bool = used? *)
    globals: global_env;
  }
  3. Error Handling Pattern:
  exception Error of string
  let error #a msg (r:range) : ML a =
    raise (Error (Printf.sprintf "%s: %s" (string_of_pos (fst r)) msg))
  4. Almost Zero Admits: Only 1 commented-out admit in test code.

  ---
  COMPARISON WITH BRRR-LANG/BRRR-MACHINE

  | Aspect               | HACL*/EverParse                   | brrr-lang/brrr-machine |
  |----------------------|-----------------------------------|------------------------|
  | .fsti interfaces     | Yes, for all public APIs          | Missing - need to add  |
  | Spec/Impl separation | 3-layer (Spec → Hacl.Spec → Hacl) | Flat structure         |
  | Z3 options tuning    | Explicit per-file                 | Not visible            |
  | Lemma files          | Dedicated lemmas/ dirs            | Inline only            |
  | Admits               | ~20 in HACL*, 1 in EverParse      | ~12 documented         |
  | Source locations     | with_meta_t pattern               | Not implemented        |
  | Generated code       | Karamel → C                       | Planned: → Rust        |

  ---
  RECOMMENDED IMPROVEMENTS FOR BRRR-LANG

  Based on HACL*/EverParse patterns:

  1. Add Interface Files (.fsti)

  Create interface files for core modules:
  brrr-lang/src/core/BrrrTypes.fsti     # Type signatures
  brrr-lang/src/core/Effects.fsti       # Effect row interface
  brrr-machine/src/analysis/IFDS.fsti   # IFDS problem interface

  2. Separate Spec Layer

  brrr-machine/src/spec/Spec.IFDS.fst        # Mathematical IFDS spec
  brrr-machine/src/spec/Spec.Taint.fst       # Taint analysis spec
  brrr-machine/src/impl/BrrrMachine.IFDS.fst # Implementation

  3. Add Source Location Tracking

  Following EverParse's with_meta_t:
  noeq type located 'a = {
    value: 'a;
    span: option span;  (* Source span in original language *)
  }

  4. Dedicate Lemma Files

  brrr-machine/src/analysis/lemmas/
    ├── IFDS.Lemmas.fst         # IFDS soundness proofs
    ├── GaloisConnection.Lemmas.fst  # Galois connection laws
    └── Taint.Lemmas.fst        # Taint propagation lemmas

  5. Z3 Options Strategy

  Add to top of each file:
  #set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

  6. Extraction Strategy

  Similar to HACL* → Karamel → C, design:
  brrr-lang F* → Karamel/custom → Rust
                   ↓
  brrr-machine F* types → Rust impl via FFI

  ---
  Do you want me to:
  1. Create .fsti interface files for core brrr-lang modules?
  2. Refactor into Spec/Impl separation pattern?
  3. Add source location tracking following EverParse?
  4. Create dedicated lemma files with proof structure?

> browse more maybe? launch 4 elite-bug-hunter agents to provide many details on organization of these reference quality 2 libs 

∴ Thinking…

  The user wants me to launch 4 elite-bug-hunter agents to deeply analyze the organization and patterns in HACL* and EverParse reference F* libraries. Let me design 4 focused exploration tasks that will provide comprehensive details on different 
  aspects of these codebases.

  I should focus each agent on a specific aspect:
  1. HACL* architecture and spec/impl patterns
  2. HACL* proof strategies and lemma organization
  3. EverParse AST/binding/type system patterns
  4. Cross-cutting patterns: error handling, extraction, testing

  Let me launch these in parallel.

● elite-bug-hunter(HACL* architecture analysis)
  ⎿  Prompt:                                                                                                                                                                                                                                        
       Analyze the HACL* F* codebase at /home/grigory/Downloads/hacl-star in EXTREME DETAIL.

       Focus on ARCHITECTURE AND ORGANIZATION:

       1. Directory Structure Deep Dive:
         - Map out the complete directory tree for specs/, code/, lib/
         - Document how modules are namespaced (Spec., Hacl., Lib.*)
         - Identify the layering: specs → Hacl.Spec → Hacl.Impl → generated
       2. Interface/Implementation Pattern:
         - Find examples of .fsti/.fst pairs
         - Document what goes in interface vs implementation
         - Note val declarations with pre/post conditions
         - Find friend declarations and understand their purpose
       3. Module Dependencies:
         - Trace import patterns (which modules import which)
         - Find circular dependency prevention strategies
         - Document how they structure mutual dependencies
       4. Inline Annotations:
         - Find all uses of inline_for_extraction
         - Document noextract usage
         - Find unfold patterns
       5. Type Abstraction Patterns:
         - How they define abstract types in .fsti
         - How they reveal implementations in .fst
         - Find abstract or opaque type patterns

       Read at least 10-15 representative files across different directories. Provide CONCRETE examples with file paths and line numbers. This is research only - do not modify any files.
  ⎿  Response:
       Now I have comprehensive data. Let me provide a detailed analysis of the HACL* F* codebase architecture:

       ---
       HACL* F* CODEBASE ARCHITECTURE ANALYSIS

       1. DIRECTORY STRUCTURE DEEP DIVE

       Top-Level Organization

       /home/grigory/Downloads/hacl-star/
       ├── specs/          # Pure mathematical specifications (991 .fst/.fsti files total)
       │   ├── drbg/       # DRBG specifications
       │   ├── frodo/      # Frodo KEM specifications
       │   ├── lemmas/     # Proof lemmas for specs
       │   └── tests/      # Test vectors
       ├── code/           # Low-level implementations (27 subdirectories)
       │   ├── bignum/     # Big number arithmetic (Hacl.Bignum.*, Hacl.Spec.Bignum.*, Hacl.Impl.*)
       │   ├── blake2/     # Blake2 hash implementations
       │   ├── chacha20/   # ChaCha20 stream cipher
       │   ├── curve25519/ # Curve25519 elliptic curve
       │   ├── hash/       # Hash algorithms (SHA2, SHA3, MD5, SHA1)
       │   ├── meta/       # Meta-programming modules
       │   ├── streaming/  # Streaming hash APIs
       │   └── ...
       ├── lib/            # Shared library code
       │   ├── c/          # C-specific helpers
       │   └── ml/         # OCaml-specific helpers
       ├── providers/      # EverCrypt abstraction layer
       │   └── evercrypt/  # Runtime algorithm selection
       ├── vale/           # Vale (assembly) specifications
       └── dist/           # Generated C code distributions

       Module Namespace Patterns

       Three distinct namespaces:

       1. Spec.* - Pure mathematical specifications (no side effects)
         - Location: /home/grigory/Downloads/hacl-star/specs/
         - Example: Spec.Agile.Hash, Spec.SHA2, Spec.Chacha20
       2. Lib.* - Reusable library primitives
         - Location: /home/grigory/Downloads/hacl-star/lib/
         - Example: Lib.Buffer, Lib.IntTypes, Lib.Sequence
       3. Hacl.* - Implementation code with multiple sub-namespaces:
         - Hacl.Spec.* - Low-level functional specifications
         - Hacl.Impl.* - Imperative implementations
         - Hacl.* - Top-level extracted APIs (e.g., Hacl.Bignum256)
         - Location: /home/grigory/Downloads/hacl-star/code/

       Layering Architecture

                    Spec.* (Pure specifications, mathematical correctness)
                        │
                        ▼
                 Hacl.Spec.* (Low-level functional specs with sequence operations)
                        │
                        ▼
                 Hacl.Impl.* (Imperative implementations using buffers)
                        │
                        ▼
                  Hacl.* (Top-level APIs, instantiated for specific sizes)
                        │
                        ▼
               EverCrypt.* (Agile/multiplexing layer with runtime dispatch)

       ---
       2. INTERFACE/IMPLEMENTATION PATTERN (.fsti/.fst PAIRS)

       Example: /home/grigory/Downloads/hacl-star/specs/Spec.Agile.Hash.fsti (lines 1-94)

       Interface file declares:
       - val declarations with pre/post conditions
       - Type definitions visible to clients
       - Documentation comments

       // From Spec.Agile.Hash.fsti lines 54-86:
       val init (a:hash_alg): init_t a

       val update (a:md_alg): update_t a

       val update_multi
         (a:hash_alg)
         (hash:words_state a)
         (prev:extra_state a)
         (blocks:bytes_blocks a):
         Pure (words_state a)
           (requires update_multi_pre a prev blocks)
           (ensures fun _ -> True)

       val finish (a:hash_alg): Spec.Hash.Definitions.finish_t a

       Example: /home/grigory/Downloads/hacl-star/specs/Spec.Agile.Hash.fst (lines 1-98)

       Implementation file provides:
       - Concrete implementations of declared vals
       - Internal helper functions
       - Private definitions

       // From Spec.Agile.Hash.fst lines 12-24:
       let init a =
         match a with
         | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
             Spec.SHA2.init a
         | MD5 ->
             Spec.MD5.init
         | SHA1 ->
             Spec.SHA1.init
         | Blake2S -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2S (Spec.Blake2.blake2_default_params _)
         | Blake2B -> Spec.Blake2.blake2_init_hash Spec.Blake2.Blake2B (Spec.Blake2.blake2_default_params _)
         | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 ->
             Lib.Sequence.create 25 (u64 0)

       Montgomery Example: /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Bignum.Montgomery.fsti (lines 19-30)

       Defining function types as aliases:

       // Type alias for function signature - Lines 20-27:
       inline_for_extraction noextract
       let bn_check_modulus_st (t:limb_t) (len:BN.meta_len t) =
         n:lbignum t len ->
         Stack (limb t)
         (requires fun h -> live h n)
         (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
           r == S.bn_check_modulus (as_seq h0 n))

       // Val declaration using the type alias - Lines 29-30:
       inline_for_extraction noextract
       val bn_check_modulus: #t:limb_t -> #len:BN.meta_len t -> bn_check_modulus_st t len

       ---
       3. FRIEND DECLARATIONS

       The friend keyword allows an implementation to access private definitions from another module's implementation.

       Patterns Found:

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fst (lines 8-9):
       friend Lib.Sequence
       friend Lib.LoopCombinators

       From /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Bignum.Montgomery.fst (line 21):
       friend Hacl.Spec.Bignum.Montgomery

       From /home/grigory/Downloads/hacl-star/code/hash/Hacl.Hash.SHA2.fst (lines 16-20):
       friend Spec.Agile.Hash
       friend Spec.Hash.Incremental
       friend Spec.SHA2

       Purpose of friend:

       1. Access to abstract types - Implementation can see the concrete definition
       2. Proof obligations - Implementation can use private lemmas
       3. Layered architecture - Hacl.Impl friends Hacl.Spec which friends Spec.*

       ---
       4. INLINE ANNOTATIONS

       inline_for_extraction

       Used extensively throughout the codebase. From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:

       // Line 26-31: Type definition that should be inlined during extraction
       inline_for_extraction
       let buffer_t (t:buftype) (a:Type0) =
         match t with
         | IMMUT -> IB.ibuffer a
         | MUT -> B.buffer a
         | CONST -> CB.const_buffer a

       // Lines 51-56: Function inlined during extraction
       inline_for_extraction
       let to_const #a #t (b:buffer_t t a) : r:cbuffer a {length r == length b}=
         match t with
         | MUT -> CB.of_buffer (b <: buffer a)
         | IMMUT -> CB.of_ibuffer (b <: ibuffer a)
         | CONST -> b <: cbuffer a

       noextract

       Combined with inline_for_extraction for proof-only definitions. From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti (lines 117-125):

       inline_for_extraction noextract
       let is_null (#t : buftype) (#a : Type0) (b : buffer_t t a) :
         Stack bool
         (requires (fun h -> live h b))
         (ensures  (fun h y h' -> h == h' /\ y == g_is_null b)) =
         match t with
         | IMMUT -> IB.is_null (b <: ibuffer a)
         | MUT -> B.is_null (b <: buffer a)
         | CONST -> CB.is_null (b <: cbuffer a)

       unfold

       Used to expand definitions during normalization. From /home/grigory/Downloads/hacl-star/specs/Spec.Agile.Hash.fsti (lines 91-93):

       unfold
       let hash (a:fixed_len_alg) (input:bytes{S.length input `less_than_max_input_length` a}) =
         hash' a input ()

       From /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fsti (lines 74-75):
       unfold
       let modulus (t:inttype) = pow2 (bits t)

       [@inline_let]

       For let-bindings that should be inlined. From /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Bignum.Montgomery.fst (lines 38-43):

       let bn_precomp_r2_mod_n #t k nBits n res =
         [@inline_let] let len = k.BN.len in
         memset res (uint #t 0) len;
         BN.bn_set_ith_bit len res nBits;
         [@inline_let]
         let spec h = S.bn_lshift1_mod_n (as_seq h n) in

       [@ inline_let] (with space)

       Alternate syntax. From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fst (lines 286-287):

         [@ inline_let]
         let spec_fh h0 = Seq.repeati_blocks_f (v bs) (as_seq h0 inp) spec_f (v nb) in

       ---
       5. TYPE ABSTRACTION PATTERNS

       Abstract Types in Interface

       From /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fsti (lines 136-139):

       // Abstract type declaration - concrete representation hidden
       inline_for_extraction
       val sec_int_t: inttype -> Type0

       val sec_int_v: #t:inttype -> sec_int_t t -> range_t t

       Concrete in Implementation

       From /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fst (the implementation would reveal):

       // The concrete definition is provided in the .fst file
       // Making it "friend" allows other modules to see the representation

       Type Classes Pattern

       From /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Bignum.Montgomery.fsti (lines 170-184):

       inline_for_extraction noextract
       class mont (t:limb_t) = {
         bn: BN.bn t;
         mont_check: bn_check_modulus_st t bn.BN.len;
         precomp: bn_precomp_r2_mod_n_st t bn.BN.len;
         reduction: bn_mont_reduction_st t bn.BN.len;
         to: bn_to_mont_st t bn.BN.len;
         from: bn_from_mont_st t bn.BN.len;
         mul: bn_mont_mul_st t bn.BN.len;
         sqr: bn_mont_sqr_st t bn.BN.len;
       }

       /// Encoding type-class hierarchies via a hook for type class resolution.
       inline_for_extraction noextract
       instance bn_of_mont (t:limb_t) (x:mont t) : BN.bn t = x.bn

       Refinement Types Pattern

       From /home/grigory/Downloads/hacl-star/specs/Spec.Hash.Definitions.fst (lines 77-82):

       let sha2_alg = a:hash_alg { is_sha2 a }
       let keccak_alg = a:hash_alg { is_keccak a }
       let blake_alg = a:hash_alg { is_blake a }
       let md_alg = a:hash_alg { is_md a }
       let fixed_len_alg = a:hash_alg { not (is_shake a) }

       ---
       6. MODULE DEPENDENCIES

       Import Patterns

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti (lines 1-18):

       module Lib.Buffer

       open FStar.HyperStack
       open FStar.HyperStack.ST

       open Lib.IntTypes
       open Lib.RawIntTypes

       module B = LowStar.Buffer
       module IB = LowStar.ImmutableBuffer
       module CB = LowStar.ConstBuffer
       module LMB = LowStar.Monotonic.Buffer

       module HS = FStar.HyperStack

       module Seq = Lib.Sequence
       module Loop = Lib.LoopCombinators

       Pattern:
       - open for bringing all names into scope
       - module X = ... for qualified access aliases
       - include for re-exporting (rare)

       Circular Dependency Prevention

       From /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Bignum.Montgomery.fsti (lines 12-16):

       module S = Hacl.Spec.Bignum.Montgomery  // Forward reference to spec
       module BN = Hacl.Bignum

       include Hacl.Bignum.ModInvLimb  // Re-export dependency

       The layering prevents cycles:
       Spec.* (no dependencies on Hacl.*)
         │
         ▼
       Hacl.Spec.* (depends on Spec.*, not Hacl.Impl.*)
         │
         ▼
       Hacl.Impl.* (depends on Hacl.Spec.*, Lib.*)
         │
         ▼
       Hacl.* (depends on Hacl.Impl.*)

       ---
       7. META-PROGRAMMING (SPLICE PATTERN)

       From /home/grigory/Downloads/hacl-star/code/curve25519/Hacl.Meta.Curve25519.fst (lines 34-50):

       %splice[
         addanddouble_point_add_and_double_higher;
         addanddouble_point_double_higher;
         generic_montgomery_ladder_higher;
         finv_fsquare_times_higher;
         finv_finv_higher;
         fields_store_felem_higher;
         generic_encode_point_higher;
         generic_scalarmult_higher;
         generic_secret_to_public_higher;
         generic_ecdh_higher
       ]
       (Meta.Interface.specialize (`Hacl.Impl.Curve25519.Fields.field_spec) [
         `Hacl.Impl.Curve25519.Generic.scalarmult;
         `Hacl.Impl.Curve25519.Generic.secret_to_public;
         `Hacl.Impl.Curve25519.Generic.ecdh
       ])

       This generates specialized implementations for different field representations at compile time.

       ---
       8. EVERCRYPT AGILITY LAYER

       From /home/grigory/Downloads/hacl-star/providers/evercrypt/fst/EverCrypt.Hash.fst (lines 102-123):

       noeq
       type state_s: alg -> Type0 =
       | MD5_s: p:Hacl.Hash.Definitions.state (|MD5, ()|) -> state_s MD5
       | SHA1_s: p:Hacl.Hash.Definitions.state (|SHA1, ()|) -> state_s SHA1
       | SHA2_224_s: p:Hacl.Hash.Definitions.state (|SHA2_224, ()|) -> state_s SHA2_224
       | SHA2_256_s: p:Hacl.Hash.Definitions.state (|SHA2_256, ()|) -> state_s SHA2_256
       | SHA2_384_s: p:Hacl.Hash.Definitions.state (|SHA2_384, ()|) -> state_s SHA2_384
       | SHA2_512_s: p:Hacl.Hash.Definitions.state (|SHA2_512, ()|) -> state_s SHA2_512
       // ... Blake2 with SIMD variants
       | Blake2S_128_s:
         _:squash (EverCrypt.TargetConfig.hacl_can_compile_vec128 /\
           EverCrypt.AutoConfig2.vec128_enabled) ->
         p:Hacl.Hash.Definitions.state (|Blake2S, Hacl.Impl.Blake2.Core.M128|) ->
         state_s Blake2S

       Pattern: Dependent pairs (| alg, impl |) plus squash types for compile-time/runtime capability checks.

       ---
       9. PROOF OPTIONS PATTERNS

       From various files:

       #set-options "--z3rlimit 50 --fuel 0 --ifuel 0"    // Default proving options
       #push-options "--fuel 1"                            // Temporarily increase fuel
       #pop-options                                        // Restore previous options
       #reset-options "--z3rlimit 100 --fuel 0 --ifuel 0" // Reset all options
       #restart-solver                                     // Reset Z3 state

       ---
       10. KEY ARCHITECTURAL INSIGHTS

       1. Separation of Concerns: Pure specs (Spec.) are completely separate from imperative implementations (Hacl.Impl.), connected via functional intermediate specs (Hacl.Spec.*).
       2. Type-Driven Specialization: Using type classes and inline_for_extraction to generate specialized code for different limb sizes (U32, U64) and vector widths.
       3. Friend Pattern: Controlled "escape hatch" for proof-level access to abstract types without breaking modularity for clients.
       4. Layered Proofs: Each layer proves refinement of the layer above:
         - Hacl.Impl.* refines Hacl.Spec.*
         - Hacl.Spec.* refines Spec.*
       5. Meta-Programming: F* splice/reflection for generating specialized implementations from generic code.
  ⎿  Done (24 tool uses · 135.8k tokens · 2m 39s)

● elite-bug-hunter(HACL* proofs and lemmas)
  ⎿  Prompt:                                                                                                                                                                                                                                        
       Analyze the HACL* F* codebase at /home/grigory/Downloads/hacl-star focusing on PROOFS AND LEMMAS.

       Investigate in EXTREME DETAIL:

       1. Lemma Organization:
         - Explore specs/lemmas/ directory completely
         - Find all *Lemmas.fst files and their patterns
         - Document the naming conventions for lemmas
         - How do they group related lemmas?
       2. Proof Techniques:
         - Find examples of Lemma with requires/ensures
         - Document SMTPat usage patterns
         - Find Classical.* imports and usage
         - Identify assert_norm vs assert usage
         - Find reveal_opaque patterns
       3. Z3 Tuning Strategies:
         - Collect ALL #set-options patterns across the codebase
         - Find --z3rlimit values (what ranges do they use?)
         - Document --fuel and --ifuel settings
         - Find #push-options/#pop-options scoping
       4. Proof Obligations:
         - Find refinement types with complex predicates
         - Document postcondition patterns in Lib.Buffer, Lib.Sequence
         - How do they prove memory safety?
       5. Admits Analysis:
         - Find ALL admits in the codebase (grep for "admit()")
         - Categorize WHY they're admitted
         - Document the ratio of proven vs admitted code

       Read 15+ files focusing on specs/lemmas/, lib/ directory lemmas, and Hacl.Spec.* files. Provide file paths and line numbers. Research only - no modifications.
  ⎿  Response:
       HACL* F* Codebase: Comprehensive Proofs and Lemmas Analysis

       1. LEMMA ORGANIZATION

       1.1 specs/lemmas/ Directory Structure

       The /home/grigory/Downloads/hacl-star/specs/lemmas/ directory contains lemma modules for specifications:

       | File                       | Size        | Description                             |
       |----------------------------|-------------|-----------------------------------------|
       | Spec.Ed25519.Lemmas.fst    | 43986 bytes | Ed25519 elliptic curve lemmas (largest) |
       | Spec.SHA2.Lemmas.fst       | 16735 bytes | SHA2 hash function lemmas               |
       | Spec.Hash.Lemmas.fst       | 8516 bytes  | Generic hash lemmas                     |
       | Spec.K256.Lemmas.fst       | 4271 bytes  | secp256k1 curve lemmas                  |
       | Spec.P256.Lemmas.fst       | 603 bytes   | P-256 curve lemmas (mostly admitted)    |
       | Spec.Curve25519.Lemmas.fst | 752 bytes   | Curve25519 lemmas                       |

       1.2 Lemma File Naming Conventions

       The codebase follows a consistent naming pattern:

       {Domain}.{SubDomain}.Lemmas.fst

       Examples across the codebase (50+ lemma files found):
       - Specs: Spec.Ed25519.Lemmas, Spec.Hash.Lemmas, Spec.K256.Lemmas
       - Implementations: Hacl.Spec.Montgomery.Lemmas, Hacl.Spec.K256.Field52.Lemmas
       - Libraries: Lib.Sequence.Lemmas, Lib.Vec.Lemmas, Lib.UpdateMulti.Lemmas

       1.3 Lemma Grouping Patterns

       Lemmas are grouped by:

       1. Mathematical Operation: Field operations (add, mul, div), modular arithmetic
       2. Data Structure: Points (affine, projective, extended), sequences, buffers
       3. Algorithm Phase: _loop, _step, _aux suffixes for iterative proofs

       Example from /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Ed25519.Lemmas.fst:59-122:
       /////////////////////////////////////
       //// Properties for finv and fdiv ///
       /////////////////////////////////////

       val fdiv_lemma: x:elem{x <> zero} -> Lemma (x /% x == one)
       val fdiv_one_lemma: x:elem -> Lemma (x /% one == x)
       val fdiv_cancel_lemma: x:elem -> y:elem -> z:elem{z <> zero} -> Lemma ((x *% z) /% (z *% y) == x /% y)

       ////////////////////////////////////////////
       //// Addition laws in affine coordinates ///
       ////////////////////////////////////////////

       val lemma_aff_double_aux: x:elem -> y:elem -> Lemma (...)

       ---
       2. PROOF TECHNIQUES

       2.1 Lemma with requires/ensures Pattern

       Standard lemma declaration pattern from /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Hash.Lemmas.fsti:16-21:

       val update_multi_zero (a: hash_alg { not (is_blake a)} ) (h: words_state a): Lemma
         (ensures (update_multi a h () S.empty == h))

       val update_multi_associative_blake (a: blake_alg)
         (h: words_state a)
         (prevlen1: nat)
         (prevlen2: nat)
         (input1: bytes)
         (input2: bytes):
         Lemma
         (requires (
           prevlen1 % block_length a = 0 /\
           S.length input1 % block_length a == 0 /\
           S.length input2 % block_length a == 0 /\
           prevlen2 = prevlen1 + S.length input1 /\
           update_multi_pre a prevlen1 (S.append input1 input2)))
         (ensures (
           let input = S.append input1 input2 in
           S.length input % block_length a == 0 /\
           update_multi a (update_multi a h prevlen1 input1) prevlen2 input2 == update_multi a h prevlen1 input))

       2.2 SMTPat Usage Patterns

       SMTPat triggers automatic lemma application. Found 15+ patterns in specs/lemmas/:

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.SHA2.Lemmas.fst:153:
       let rec ws_224_256 (b: block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}):
         Lemma
           (ensures (ws SHA2_224 b t == ws SHA2_256 b t))
         [ SMTPat (ws SHA2_256 b t) ]

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:155-157:
       let mut_immut_disjoint #t #t' (b: buffer_t MUT t) (ib: buffer_t IMMUT t') (h: HS.mem):
         Lemma
           (requires (B.live h b /\ B.live h ib))
           (ensures (disjoint b ib))
           [SMTPat (B.loc_disjoint (loc b) (loc ib)); SMTPat (B.live h b); SMTPat (B.live h ib)]

       Common SMTPat patterns:
       - Single pattern: [ SMTPat (f x) ]
       - Multiple patterns: [ SMTPat (f x); SMTPat (g y) ]
       - Disjoint pattern: [ SMTPat (f x y \/ g x y) ]

       2.3 Classical.* Usage Patterns

       From /home/grigory/Downloads/hacl-star/lib/Lib.Sequence.Lemmas.fst:289-298:
       calc (==) {
         repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0;
         == { }
         Loops.repeat_right mi (mi + n0) a repeat_bf_s0 acc0;
         == { Classical.forall_intro_2 (aux_repeat_bf_s0 #inp_t blocksize len0 mi hi n inp a f);
                repeat_right_extensionality n0 mi a a repeat_bf_s0 repeat_bf_t acc0 }
         Loops.repeat_right mi (mi + n0) a repeat_bf_t acc0;
       }

       Key Classical functions used:
       - Classical.forall_intro - Introduce universal quantifier
       - Classical.forall_intro_2, Classical.forall_intro_3 - Multi-argument variants
       - Classical.move_requires, Classical.move_requires_2, Classical.move_requires_3 - Move preconditions

       2.4 assert_norm vs assert Usage

       assert_norm - Forces normalization at compile time, used for constant computations:

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Ed25519.Lemmas.fst:1158:
       let aff_g_is_on_curve () =
         assert_norm (is_on_curve (g_x, g_y))

       From /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fst:7-10:
       let pow2_2 _   = assert_norm (pow2 2 = 4)
       let pow2_3 _   = assert_norm (pow2 3 = 8)
       let pow2_4 _   = assert_norm (pow2 4 = 16)
       let pow2_127 _ = assert_norm (pow2 127 = 0x80000000000000000000000000000000)

       Regular assert - Runtime assertion, used for intermediate proof steps:
       assert (x1 *% x1 == x2);
       assert (rx == pX /\ ry == pY);

       2.5 reveal_opaque Patterns

       Used to expose opaque definitions when needed for proofs:

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.SHA2.Lemmas.fst:102-119:
       let ws_is_ws_pre (i:nat{i <= size_k_w a}) : Lemma
         (ensures forall (j:nat{j < i}).
           ws a block j ==
           (Lib.LoopCombinators.repeati i (ws_pre_inner a block) (Seq.create (size_k_w a) (to_word a 0))).[j])
         = if i = 0 then ()
           else (
             ws_is_ws_pre (i - 1);
             Lib.LoopCombinators.unfold_repeati (size_k_w a) (ws_pre_inner a block)
               (Seq.create (size_k_w a) (to_word a 0)) (i - 1);
             reveal_opaque (`%ws) ws
           )

       Pattern: reveal_opaque (\%function_name) function_name`

       ---
       3. Z3 TUNING STRATEGIES

       3.1 #set-options Distribution

       | z3rlimit Value | Occurrences       |
       |----------------|-------------------|
       | 50             | 402 (most common) |
       | 100            | 159               |
       | 20             | 95                |
       | 200            | 75                |
       | 30             | 66                |
       | 300            | 32                |
       | 150            | 25                |
       | 400            | 23                |
       | 500            | 14                |
       | 600            | 12                |
       | 1000           | 3                 |
       | 3000           | 1 (maximum)       |

       3.2 Fuel and iFuel Settings

       | Setting     | Occurrences                 |
       |-------------|-----------------------------|
       | fuel 0      | 643 (overwhelming majority) |
       | ifuel 0     | 622                         |
       | ifuel 1     | 104                         |
       | max_fuel 1  | 58                          |
       | fuel 1      | 55                          |
       | max_ifuel 1 | 53                          |

       Pattern: Most proofs use --fuel 0 --ifuel 0 as baseline, with localized increases.

       3.3 #push-options/#pop-options Scoping

       From /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Spec.Montgomery.Lemmas.fst:31-95:
       #push-options "--z3rlimit 100"
       val eea_pow2_odd_k_lemma: a:pos -> n:pos -> k1:pos -> Lemma
         (requires n * k1 % pow2 (a - 1) == 1 /\ n % 2 = 1)
         (ensures (let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
           n * k % pow2 a == 1))
       let eea_pow2_odd_k_lemma a n k1 =
         // ... complex proof
       #pop-options

       Special Z3 options used:
       - --z3smtopt '(set-option :smt.arith.solver 2)' - Alternative arithmetic solver
       - --z3cliopt smt.QI.EAGER_THRESHOLD=5 - Quantifier instantiation tuning
       - --z3rlimit_factor 2 - Multiplier for existing limit
       - --retry 2 - Retry count
       - --query_stats - Debug statistics
       - #restart-solver - Fresh Z3 instance

       ---
       4. PROOF OBLIGATIONS

       4.1 Refinement Types with Complex Predicates

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:66-72:
       inline_for_extraction
       let lbuffer_t (t:buftype) (a:Type0) (len:size_t) =
         b:buffer_t t a{length #t #a b == v len}

       unfold let lbuffer (a:Type0) (len:size_t) = lbuffer_t MUT a len
       unfold let ilbuffer (a:Type0) (len:size_t) = lbuffer_t IMMUT a len
       unfold let glbuffer (a:Type0) (len:size_t) = c:clbuffer a len{CB.qual_of #a c == CB.IMMUTABLE}

       From /home/grigory/Downloads/hacl-star/lib/Lib.LoopCombinators.fsti:232-234:
       unfold
       type repeatable (#a:Type) (#n:nat) (pred:(i:nat{i <= n} -> a -> Tot Type)) =
         i:nat{i < n} -> x:a{pred i x} -> y:a{pred (i+1) y}

       4.2 Postcondition Patterns in Lib.Buffer

       From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:443-449:
       val copy:
           #t:buftype
         -> #a:Type
         -> #len:size_t
         -> o:lbuffer a len
         -> i:lbuffer_t t a len ->
         Stack unit
           (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint i o)
           (ensures  fun h0 _ h1 ->
             modifies1 o h0 h1 /\
             as_seq h1 o == as_seq h0 i)

       4.3 Memory Safety Proof Patterns

       Modification tracking:
       let modifies (s:B.loc) (h1 h2:HS.mem) = B.modifies s h1 h2
       let modifies0 (h1 h2:HS.mem) = modifies (B.loc_none) h1 h2
       let modifies1 (#a:Type0) (b:buffer_t MUT a) (h1 h2:HS.mem) = modifies (loc b) h1 h2

       Loop invariants: From /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti:621-633:
       let loop_inv
         (h0:mem)
         (n:size_t)
         (a_spec:(i:size_nat{i <= v n} -> Type))
         (refl:(mem -> i:size_nat{i <= v n} -> GTot (a_spec i)))
         (footprint:(i:size_nat{i <= v n} -> GTot B.loc))
         (spec:(mem -> GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1))))
         (i:size_nat{i <= v n})
         (h:mem):
         Type0
       =
         modifies (footprint i) h0 h /\
         refl h i == Loop.repeat_gen i a_spec (spec h0) (refl h0 0)

       ---
       5. ADMITS ANALYSIS

       5.1 Total Admits Found: 74

       5.2 Admits by File

       | File                                                                   | Count | Category                         |
       |------------------------------------------------------------------------|-------|----------------------------------|
       | /home/grigory/Downloads/hacl-star/lib/Lib.IntVector.fst                | 57    | Vector intrinsics axiomatization |
       | /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.P256.Lemmas.fst    | 6     | Elliptic curve algebra           |
       | /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.K256.Lemmas.fst    | 4     | Elliptic curve algebra           |
       | /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Ed25519.Lemmas.fst | 2     | Elliptic curve algebra           |
       | Other                                                                  | 5     | Various                          |

       5.3 Admit Categories

       Category 1: Vector Intrinsics (77% of admits)

       From /home/grigory/Downloads/hacl-star/lib/Lib.IntVector.fst:20-26:
       let vec #t #w =
         match t, w with
         | _,_ -> admit()  // Placeholder for platform-specific implementation

       let vec_v #t #w x = admit()
       let vecv_extensionality #t #w f1 f2 = admit()
       let reveal_vec_v_1 #t f = admit()

       These are intentional - they represent platform-specific SIMD operations that must be axiomatized.

       Category 2: Assumed Primes (assume val)

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Ed25519.Lemmas.fst:49:
       assume val prime_lemma: unit -> Lemma (Euclid.is_prime prime)

       Proving primality of large cryptographic primes is computationally expensive and typically done once externally.

       Category 3: Elliptic Curve Group Laws

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.P256.Lemmas.fst:19-29:
       let aff_point_at_inf_lemma p = admit()
       let aff_point_add_assoc_lemma p q s = admit ()
       let aff_point_add_comm_lemma p q = admit()
       let to_aff_point_at_infinity_lemma () = admit()
       let to_aff_point_add_lemma p q = admit()
       let to_aff_point_double_lemma p = admit()

       These represent complex algebraic properties that require specialized proofs (often done in external proof assistants).

       5.4 Ratio of Proven vs Admitted Code

       Proven: ~99% of the codebase has complete proofs
       Admitted: ~1% (74 admits total across 400+ .fst files with tens of thousands of lemmas)

       Most admits are:
       1. Intentional axiomatizations of platform primitives
       2. Well-known mathematical facts (primality of cryptographic constants)
       3. Complex elliptic curve group law properties

       ---
       6. KEY PROOF PATTERNS SUMMARY

       6.1 calc Blocks

       Extensively used for equational reasoning:

       calc (==) {
         (a * b % m) * c % m;
         == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c m }
         (a * b) * c % m;
         == { Math.Lemmas.paren_mul_right a b c }
         a * (b * c) % m;
         == { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) m }
         a * (b * c % m) % m;
       }

       6.2 Tactics Usage

       From /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Ed25519.Lemmas.fst:46:
       noextract
       let ed25519_semiring () : Tac unit = canon_semiring elem_cr; trefl()

       // Usage:
       assert (x *% y +% y *% x == 2 *% x *% y) by (ed25519_semiring ())

       6.3 Math.Lemmas Library

       Core lemmas used throughout:
       - Math.Lemmas.lemma_mod_mul_distr_l/r
       - Math.Lemmas.modulo_distributivity
       - Math.Lemmas.euclidean_division_definition
       - Math.Lemmas.pow2_plus/double_sum/lt_compat
       - Math.Lemmas.small_mod

       ---
       7. CRITICAL FINDINGS

       7.1 Strong Points

       1. Systematic organization - Lemmas grouped by mathematical domain
       2. Consistent naming - {Module}.Lemmas.fst pattern
       3. Conservative Z3 settings - fuel 0, ifuel 0 baseline prevents proof explosion
       4. Explicit scoping - #push-options/#pop-options for local changes
       5. Low admit ratio - <1% of proofs admitted

       7.2 Potential Concerns

       1. P256 lemmas nearly all admitted - 6 of 8 lemmas in Spec.P256.Lemmas.fst are admit()
       2. Vector intrinsics axiomatized - 57 admits in Lib.IntVector.fst
       3. Maximum z3rlimit of 3000 found - indicates some proofs require significant resources
       4. Assumed primality - prime_lemma for Ed25519, K256, P256 curves

       7.3 Verification Coverage

       Files with complete proofs (no admits):
       - /home/grigory/Downloads/hacl-star/lib/Lib.Sequence.Lemmas.fst
       - /home/grigory/Downloads/hacl-star/lib/Lib.NatMod.fst
       - /home/grigory/Downloads/hacl-star/lib/Lib.LoopCombinators.fst
       - /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Hash.Lemmas.fst
       - /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.SHA2.Lemmas.fst
       - /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Spec.Montgomery.Lemmas.fst
  ⎿  Done (39 tool uses · 153.5k tokens · 4m 24s)

● elite-bug-hunter(EverParse AST/types deep dive)
  ⎿  Prompt:                                                                                                                                                                                                                                        
       Analyze the EverParse F* codebase at /home/grigory/Downloads/everparse focusing on AST AND TYPE SYSTEM patterns.

       Investigate in EXTREME DETAIL:

       1. AST Design (src/3d/Ast.fst):
         - Read the ENTIRE Ast.fst file
         - Document all type definitions
         - Find the with_meta_t pattern and all its uses
         - Document range/pos tracking
         - Find how expressions, types, declarations are structured
       2. Binding and Name Resolution (src/3d/Binding.fst):
         - Read the ENTIRE Binding.fst file
         - Document the env type and how it's threaded
         - Find lookup functions and error handling
         - Document scope management (push/pop patterns)
         - How do they handle shadowing?
       3. Type System:
         - Find TypeSizes.fst and understand size computation
         - Document type checking patterns in Binding.fst
         - Find coercion handling
       4. Target IR (src/3d/Target.fst):
         - Read Target.fst to understand target language
         - Compare Target vs Ast - what's the difference?
         - Find translation patterns (Ast → Target)
       5. Error Handling Pattern:
         - Find the exception type
         - Document error message formatting
         - Find all uses of error function
         - How do they preserve source locations in errors?
       6. GlobalEnv Pattern:
         - Find GlobalEnv.fst
         - Document how global state is managed
         - Find hashtable usage patterns

       Read at least 10 files thoroughly. Provide file paths, line numbers, and concrete code snippets. Research only - no modifications.
  ⎿  Response:
       Now I have comprehensive understanding of the EverParse F* codebase. Let me provide a detailed analysis of all the patterns I've discovered:

       ---
       EverParse F* Codebase Analysis - AST and Type System Patterns

       1. AST Design (/home/grigory/Downloads/everparse/src/3d/Ast.fst)

       1.1 Core Metadata Pattern: with_meta_t

       The fundamental pattern for source location tracking is defined at lines 107-111:

       noeq
       type with_meta_t 'a = {
         v:'a;
         range:range;
         comments: comments
       }

       Usage Pattern: Every AST node that needs source location information wraps its content in with_meta_t. This pattern is used extensively:

       - ident = with_meta_t ident' (line 133)
       - expr = with_meta_t expr' (line 309)
       - typ = with_meta_t typ' (line 390)
       - action = with_meta_t action' (line 415)
       - field = with_meta_t field' (line 577)
       - atomic_field = with_meta_t atomic_field' (line 570)
       - decl uses d_decl : with_meta_t decl' (line 755)

       1.2 Source Position and Range (lines 34-98)

       [@@ PpxDerivingYoJson ]
       type pos = {
         filename: string;
         line:int;
         col:int
       }

       [@@ PpxDerivingYoJson ]
       let range = pos * pos  // start and end positions

       Utility functions:
       - string_of_pos (line 81): Formats position as "filename:(line,col)"
       - string_of_range (line 91): Formats range with start-end positions
       - dummy_pos (lines 100-104): Used for synthetic nodes

       1.3 Identifier Structure (lines 128-139)

       [@@ PpxDerivingYoJson ]
       type ident' = {
         modul_name : option string;
         name : string
       }
       [@@ PpxDerivingYoJson ]
       let ident = with_meta_t ident'

       Qualified names supported through modul_name. The reserved_prefix = "___" (line 25) prevents user identifiers from clashing with generated names.

       1.4 Expression AST (lines 300-309)

       [@@ PpxDerivingYoJson ]
       noeq
       type expr' =
         | Constant of constant
         | Identifier of ident
         | Static of expr        // compile-time constant guard
         | This                  // self-reference in refinements
         | App : op -> list expr -> expr'

       and expr = with_meta_t expr'

       Note: Expression AST is relatively simple - no binding structure within expressions. Names are concrete identifiers (no shadowing allowed).

       1.5 Type AST (lines 378-392)

       and typ' =
         | Type_app : ident -> t_kind -> list generic_inst -> list typ_param -> typ'
         | Pointer : typ -> pointer_qualifier -> typ'
         | Type_arrow : args:list typ { Cons? args } -> typ -> typ'

       and typ = with_meta_t typ'

       Three type kinds (t_kind, lines 317-321):
       - KindSpec - Specification types with 3D interpretation
       - KindOutput - Parse tree construction types
       - KindExtern - Abstract external types

       1.6 Declaration Structure (lines 672-757)

       [@@ PpxDerivingYoJson ]
       noeq
       type decl' =
         | ModuleAbbrev: ident -> ident -> decl'
         | Define: ident -> option typ -> constant -> decl'
         | TypeAbbrev: list attribute -> typ -> ident -> list generic_param -> list param -> decl'
         | Enum: typ -> ident -> list enum_case -> decl'
         | Record: names:typedef_names -> generics:list generic_param -> params:list param ->
                   where:option expr -> fields:record -> decl'
         | CaseType: names:typedef_names -> generics:list generic_param -> params:list param ->
                     switch_case -> decl'
         | ProbeFunction: ident -> list param -> probe_action -> probe_function_type -> decl'
         | OutputType: out_typ -> decl'
         | ExternType: typedef_names -> decl'
         | ExternFn: ident -> typ -> list param -> pure:bool -> decl'
         | ExternProbe: ident -> probe_qualifier -> decl'
         ...

       [@@ PpxDerivingYoJson ]
       noeq
       type decl = {
         d_decl : with_meta_t decl';
         d_exported : bool
       }

       ---
       2. Binding and Name Resolution (/home/grigory/Downloads/everparse/src/3d/Binding.fst)

       2.1 Environment Structure (lines 37-48)

       /// Maps locally bound names to their type and usage status
       let local_env = H.t ident' (ident' & typ & bool)

       noeq
       type env = {
         this: option ident;       // Current type being defined
         generics: list generic_param;  // Generic parameters in scope
         locals: local_env;        // Local bindings (fields, parameters)
         globals: global_env;      // Global definitions
       }

       2.2 Environment Threading Pattern

       Environments are threaded explicitly through ML functions:

       let mk_env (g:global_env) =
         { this = None;
           generics = [];
           locals = H.create 10;
           globals = g }

       let copy_env (e:env) =  // Deep copy for scoped changes
         let locals = H.create 10 in
         H.iter (fun k v -> H.insert locals k v) e.locals;
         { this = e.this; generics = e.generics; 
           globals = e.globals; locals = locals }

       2.3 Lookup Functions (lines 142-166)

       let try_lookup (e:env) (i:ident)
       : ML (option (either typ (decl & either decl_attributes macro_signature)))
       = match H.try_find e.locals i.v with
         | Some (_, t, true) -> Some (Inl t)
         | Some (j, t, false) ->  // Mark as used when first accessed
           H.remove e.locals i.v;
           H.insert e.locals i.v (j, t, true);
           Some (Inl t)
         | None ->
           match try_lookup_generic e i with
           | Some (GenericProbeFunction _ ty _) -> Some (Inl ty)
           | _ ->
             match H.try_find e.globals.ge_h i.v with
             | Some d -> Some (Inr d)
             | None -> ...

       let lookup (e:env) (i:ident) : ML (...) =
         match try_lookup e i with
         | None -> error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range
         | Some v -> v

       Key Pattern: The boolean in local_env tracks whether a local has been used. This is used to determine field dependencies (line 1848).

       2.4 Scope Management (lines 127-133)

       let add_local (e:env) (i:ident) (t:typ) : ML unit =
         check_shadow e.globals.ge_h i t.range;
         check_shadow e.locals i t.range;
         let i' = format_identifier e i in
         H.insert e.locals i.v (i'.v, t, false);
         H.insert e.locals i'.v (i'.v, t, false)

       let remove_local (e:env) (i:ident) : ML unit =
         match H.try_find e.locals i.v with
         | Some (j, _, _) ->
           H.remove e.locals i.v;
           H.remove e.locals j
         | _ -> ()

       2.5 Shadowing Check (lines 75-80)

       let check_shadow (e:H.t ident' 'a) (i:ident) (r:range) =
         match H.try_find e i.v with
         | Some j ->
           let msg = Printf.sprintf "Declaration %s clashes with previous declaration" (ident_to_string i) in
           error msg i.range
         | _ -> ()

       EverParse does NOT allow shadowing - all names must be unique within scope.

       2.6 Record Field Checking (lines 1816-1868)

       let rec check_record (check_field:check_field_t) (env:env) (fs:record) : ML record =
         let env = copy_env env in  // Locals don't escape the record
         
         let fields = List.map (fun f -> ... check_atomic_field env true af ...) fs in
         
         // Infer dependent fields by checking usage
         let fields = fields |> List.mapi (fun i f ->
           match f.v with
           | AtomicField af ->
             let used = is_used env sf.field_ident in
             let dependent = used || (Some? sf.field_constraint && not last_field) in
             ...

       ---
       3. Type System

       3.1 Type Size Computation (/home/grigory/Downloads/everparse/src/3d/TypeSizes.fst)

       Size ADT (referenced from Ast.fst, defined in TypeSizes):

       type size_env = H.t typename (size & alignment)

       let initial_senv () =
         let i = [
           ("unit",     (Fixed 0,  None));
           ("Bool",     (Fixed 1,  Some 1));
           ("UINT8",    (Fixed 1,  Some 1));
           ("UINT16",   (Fixed 2,  Some 2));
           ("UINT32",   (Fixed 4,  Some 4));
           ("UINT64",   (Fixed 8,  Some 8));
           ...
           ("all_bytes", (Variable, None));
           ("PUINT8",   (Variable, pointer_alignment))
         ]

       3.2 Field Size Calculation (TypeSizes.fst lines 165-200)

       let size_and_alignment_of_atomic_field (env:env_t) (f:atomic_field)
         : ML (size & alignment)
         = let base_size, align = size_and_alignment_of_typ env f.v.field_type in
           let size =
             match f.v.field_array_opt with
             | FieldScalar -> base_size
             | FieldArrayQualified (n, ByteArrayByteSize) ->
               if base_size <> Fixed 1 then error "Expected a byte array..." f.range;
               let n = value_of_const_expr env n in
               match n with | Some (Inr (_, k)) -> Fixed k | _ -> Variable
             | FieldString (Some n) | FieldArrayQualified (n, ArrayByteSize) ->
               match value_of_const_expr env n with
               | Some (Inr (_, k)) -> Fixed k
               | _ -> Variable
             | _ -> Variable
           in size, align

       3.3 Type Checking in Binding.fst

       Expression Type Checking (lines 813-1120):

       and check_expr (env:env) (e:expr) : ML (expr & typ) =
         match e.v with
         | Constant c -> e, type_of_constant e.range c
         | Identifier i ->
           let i, t = check_ident env i in
           { e with v = Identifier i }, t
         | App (Cast _ to) [n] ->
           let n, from = check_expr env n in
           if not (typ_is_integral env from)
           then error "Casts are only supported on integral types" e.range
           ...
         | App op es ->
           let ets = List.map (check_expr env) es in
           ... // Operator-specific type checking

       3.4 Integer Coercion (lines 486-498)

       let try_cast_integer env et to : ML (option expr) =
         let e, from = et in
         let i_to = typ_is_integral env to in
         let i_from = typ_is_integral env from in
         if i_from && i_to then
           let i_from = typ_as_integer_type (unfold_typ_abbrev_and_enum env from) in
           let i_to = typ_as_integer_type (unfold_typ_abbrev_and_enum env to) in
           if i_from = i_to then Some e
           else if integer_type_leq i_from i_to  // Only widening casts
           then Some (cast e i_from i_to)
           else None
         else None

       ---
       4. Target IR (/home/grigory/Downloads/everparse/src/3d/Target.fsti and Target.fst)

       4.1 Target vs AST Differences

       Target Operators (Target.fsti lines 24-51):
       - Same as AST operators BUT SizeOf is REMOVED
       - Arithmetic operators carry resolved integer types (not optional)

       noeq
       type op =
         | Plus of A.integer_type    // AST has: Plus of option integer_type
         | Minus of A.integer_type
         | Cast : from:A.integer_type -> to:A.integer_type -> op  // Both required!
         ...

       4.2 Target Expressions (Target.fsti lines 57-64)

       noeq
       type expr' =
         | Constant   : c:A.constant -> expr'
         | Identifier : i:A.ident -> expr'
         | App        : hd:op -> args:list expr -> expr'
         | Record     : type_name:A.ident -> list (A.ident * expr) -> expr'

       and expr = expr' & A.range  // Simpler than AST: no with_meta_t wrapper

       Note: This is REMOVED from Target - must be eliminated during translation.

       4.3 Target Types (Target.fsti lines 186-213)

       noeq
       type typ =
         | T_false    : typ
         | T_app      : hd:A.ident -> A.t_kind -> args:list index -> typ
         | T_nlist    : elt: typ -> bytesize: expr -> typ
         | T_pair     : fst: typ -> snd: typ -> typ
         | T_dep_pair : dfst:typ -> dsnd:(A.ident & typ) -> typ
         | T_refine   : base:typ -> refinement:lam expr -> typ
         | T_if_else  : e:expr -> t:typ -> f:typ -> typ
         | T_pointer  : typ -> pointer_size:A.integer_type -> typ
         | T_with_action: typ -> action -> typ
         | T_with_dep_action: typ -> a:lam action -> typ
         | T_with_comment: typ -> A.comments -> typ
         | T_with_probe: ...
         | T_arrow : list typ -> typ -> typ

       4.4 Parser Structure (Target.fsti lines 284-323)

       noeq
       type parser' =
         | Parse_return    : v:expr -> parser'
         | Parse_app       : hd:A.ident -> args:list index -> parser'
         | Parse_nlist     : t_size_constant:bool -> n:expr -> t:parser -> parser'
         | Parse_pair      : n1:A.ident -> p_is_const:bool -> p:parser ->
                             q_is_const:bool -> q:parser -> parser'
         | Parse_dep_pair  : n1:A.ident -> p:parser -> k:lam parser -> parser'
         | Parse_refinement: n:A.ident -> p:parser -> f:lam expr -> parser'
         ...

       and parser = {
         p_kind:parser_kind;
         p_typ:typ;
         p_parser:parser';
         p_typename: A.ident;
         p_fieldname: string;
       }

       ---
       5. Error Handling Pattern

       5.1 Exception Type (Ast.fst line 144)

       exception Error of string

       5.2 Error Function (Ast.fst lines 146-148)

       let error #a msg (r:range) : ML a =
         raise (Error (Printf.sprintf "%s: (Error) %s\n" (string_of_pos (fst r)) msg))

       Pattern: All error functions take a range parameter to preserve source locations.

       5.3 Error Message Examples (from Binding.fst)

       // Line 165: Variable not found
       error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range

       // Line 77-79: Shadow check
       error (Printf.sprintf "Declaration %s clashes with previous declaration"
              (ident_to_string i)) i.range

       // Lines 2176-2179: Type mismatch
       error (Printf.sprintf "Expected a boolean where clause; got %s"
              (print_typ t)) e.range

       // Line 1862-1866: Reader requirement
       error "The type of this field does not have a reader, \
              either because its values are too large \
              or because reading it may incur a double fetch; \
              subsequent fields cannot depend on it" af.range

       5.4 Warning Function (Ast.fst lines 149-150)

       let warning msg (r:range) : ML unit =
         FStar.IO.print_string (Printf.sprintf "%s: (Warning) %s\n" (string_of_pos (fst r)) msg)

       ---
       6. GlobalEnv Pattern (/home/grigory/Downloads/everparse/src/3d/GlobalEnv.fst)

       6.1 Global Environment Structure (lines 74-83)

       noeq
       type global_env = {
         mname: string;
         ge_h: global_hash_t;           // Main declarations
         ge_out_t: H.t ident' decl;     // Output types
         ge_extern_t: H.t ident' decl;  // Extern types
         ge_extern_fn: H.t ident' decl; // Extern functions
         ge_probe_fn: H.t ident' decl;  // Probe functions
         ge_cfg: option (Config.config & string)
       }

       6.2 Declaration Attributes (lines 36-44)

       type decl_attributes = {
         may_fail:bool;
         integral:option integer_type;
         bit_order: option bitfield_bit_order;
         has_reader:bool;
         parser_weak_kind:weak_kind;
         parser_kind_nz:option bool;
         primitive:bool;
       }

       6.3 Macro Signature (lines 47-51)

       noeq
       type macro_signature = {
         macro_arguments_t: list typ;
         macro_result_t: typ;
         macro_defn_t:option expr
       }

       6.4 Hash Table Usage Pattern

       All lookups use the ident' (underlying value without metadata) as key:

       // Insertion (Binding.fst lines 108-115)
       let add_global (e:global_env) (i:ident) (d:decl) (t:either decl_attributes macro_signature) =
         let insert k v = H.insert e.ge_h k.v v in
         check_shadow e.ge_h i d.d_decl.range;
         let i' = format_identifier env i in
         insert i (d, t);
         insert i' (d, t);  // Also insert formatted name

       // Lookup (Binding.fst lines 162-166)
       let lookup (e:env) (i:ident) =
         match try_lookup e i with
         | None -> error (Printf.sprintf "Variable %s not found" (ident_to_string i)) i.range
         | Some v -> v

       6.5 Separate Tables for Different Declaration Kinds

       // Adding output type (Binding.fst lines 545-549)
       let add_output_type (ge:global_env) (i:ident) (d:decl{OutputType? d.d_decl.v}) =
         let insert i = H.insert ge.ge_out_t i d in
         insert i.v;
         let td_abbrev = (OutputType?._0 d.d_decl.v).out_typ_names.typedef_abbrev in
         insert td_abbrev.v

       // Adding extern type (Binding.fst lines 556-560)
       let add_extern_type (ge:global_env) (i:ident) (d:decl{ExternType? d.d_decl.v}) =
         let insert i = H.insert ge.ge_extern_t i d in
         insert i.v;
         let td_abbrev = (ExternType?._0 d.d_decl.v).typedef_abbrev in
         insert td_abbrev.v

       ---
       7. Translation Pattern (Ast to Target)

       From /home/grigory/Downloads/everparse/src/3d/TranslateForInterpreter.fst:

       7.1 Expression Translation (lines 318-325)

       let rec translate_expr (e:A.expr) : ML T.expr =
         (match e.v with
          | Constant c -> T.Constant c
          | Identifier i -> T.Identifier i
          | App op exprs -> T.App (translate_op op) (List.map translate_expr exprs)
          | Static _ -> failwith "`static` should have been eliminated already"
          | This -> failwith "`this` should have been eliminated already"),
         e.A.range

       7.2 Operator Translation (lines 280-316)

       let translate_op : A.op -> ML T.op = 
         let force_topt (o:option A.integer_type) : ML integer_type =
           match o with
           | None -> failwith "Unelaborated integer operator"
           | Some t -> t
         in
         fun op ->
         match op with
         | Plus topt -> T.Plus (force_topt topt)
         | Cast (Some from) to -> T.Cast from to
         | Cast None _ | SizeOf -> failwith "Should have been eliminated already"
         ...

       Key insight: Translation assumes prior elaboration phases have:
       1. Resolved all integer operators to specific types
       2. Eliminated SizeOf expressions
       3. Eliminated This references
       4. Eliminated Static guards

       ---
       Summary of Key Design Patterns

       1. Metadata Wrapper: with_meta_t carries range and comments through the AST
       2. Explicit Environment Threading: Environments passed explicitly to all checker functions
       3. No Shadowing: All names unique within scope; check_shadow enforces this
       4. Usage Tracking: Boolean flag tracks field usage for dependency inference
       5. Separate Hash Tables: Different declaration kinds in separate tables for efficient lookup
       6. Two-Phase Types: AST types have optional type annotations; Target types fully resolved
       7. Exception-Based Errors: Single Error exception with source location formatting
       8. Elaboration Before Translation: Several passes eliminate syntactic sugar before Target translation
  ⎿  Done (15 tool uses · 169.6k tokens · 2m 48s)

● elite-bug-hunter(Cross-cutting F* patterns)
  ⎿  Prompt:                                                                                                                                                                                                                                        
       Analyze BOTH /home/grigory/Downloads/hacl-star AND /home/grigory/Downloads/everparse for CROSS-CUTTING PATTERNS.

       Investigate in EXTREME DETAIL:

       1. Build and Extraction:
         - Read Makefile patterns in both projects
         - Find how they configure F* compilation
         - Document Karamel extraction setup in HACL*
         - Find .fst.config.json files and understand their purpose
       2. Testing Patterns:
         - Explore tests/ directories in both
         - Find how they write F* tests
         - Document any property-based testing
       3. Effect Handling:
         - Find ML effect usage (FStar.All, FStar.ST)
         - Document Stack vs Heap effects in HACL*
         - Find Tot vs ML separation patterns
       4. Refinement Type Patterns:
         - Find complex refinement types
         - Document size_t patterns (size_nat, size_t)
         - Find bounded integer patterns
       5. Memory Management (HACL* focus):
         - Find LowStar.Buffer patterns
         - Document B.live, B.modifies usage
         - Find stack allocation patterns
         - Document how they ensure memory safety
       6. noeq Type Patterns:
         - Find all noeq type declarations
         - Understand WHY they use noeq
         - Document when noeq is appropriate
       7. Module System Patterns:
         - Find module X = Y aliases
         - Document include usage
         - Find open vs explicit qualification patterns
       8. Hint Files:
         - Explore hints/ directory in HACL*
         - Understand what hints are and how they're used

       Read 20+ files across both codebases. Provide comparative analysis with specific file paths and patterns. Research only - no modifications.
  ⎿  Response:
       Now let me provide the comprehensive comparative analysis based on my research:

       ---
       COMPARATIVE ANALYSIS: HACL* and EverParse F* Codebases

       1. BUILD AND EXTRACTION PATTERNS

       HACL* Build System (/home/grigory/Downloads/hacl-star/Makefile.common)

       F Compiler Configuration:*
       FSTAR_NO_FLAGS = $(FSTAR_EXE) $(FSTAR_HINTS) \
         --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES) --cmi \
         --already_cached 'Prims FStar LowStar C Spec.Loops TestLib WasmSupport' \
         --warn_error '@240+241@247-272-274@319@328@331@332@337' \
         --cache_dir $(OUTPUT_DIR) --trivial_pre_for_unannotated_effectful_fns false

       Key patterns:
       - --cmi (cross-module inlining) enabled
       - Explicit caching of standard library modules
       - Z3 version pinned to 4.8.5 for consistency
       - Vale-specific flags for assembly verification:
       VALE_FSTAR_FLAGS=--z3cliopt smt.arith.nl=false \
         --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 \
         --max_fuel 1 --max_ifuel 1 --initial_ifuel 0

       Karamel Extraction Setup:
       BASE_FLAGS = \
         -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] \
         -bundle Lib.*[rename=Hacl_Lib] \
         -drop Lib.IntVector.Intrinsics \
         -fparentheses -fno-shadow -fcurly-braces -fnoreturn-else \
         -funroll-loops 16

       The -bundle flags control how F* modules map to C files. The -drop removes modules that have hand-written C implementations.

       EverParse Build System (/home/grigory/Downloads/everparse/Makefile)

       EverParse uses a simpler Makefile structure focused on the 3d frontend and LowParse combinators. It relies heavily on F*'s cache system.

       ---
       2. TESTING PATTERNS

       HACL* Tests (/home/grigory/Downloads/hacl-star/code/tests/Hacl.Test.SHA2.fst)

       Pattern: Vector-based testing with global test data:
       let test1_plaintext: b:lbuffer uint8 3ul{ recallable b } =
         let l:list uint8 = normalize_term (List.Tot.map u8 [0x61; 0x62; 0x63]) in
         assert_norm (List.Tot.length l == 3);
         createL_mglobal l

       Key testing patterns:
       1. recallable buffers for persistent test data
       2. assert_norm for compile-time length verification
       3. createL_mglobal for managed global buffers
       4. push_frame()/pop_frame() for stack-based temporary allocations
       5. result_compare_display for verification with output

       EverParse Tests (/home/grigory/Downloads/everparse/tests/Test.fst)

       Pattern: Parser roundtrip testing:
       let test_open_enum () : St bool =
         let x = T7.Body_y [...] in
         let xb = T7.t7_serializer32 x in
         match T7.t7_parser32 xb with
         | Some (x',r) -> x = x' && r = len xb
         | _ -> false

       Key testing patterns:
       1. St effect for stateful test code
       2. Serializer/Parser roundtrip verification
       3. assume false for unverified paths during testing
       4. LPL.validate for validator testing

       ---
       3. EFFECT HANDLING PATTERNS

       Tot vs ML Separation

       Pure Specifications (Tot/Pure/GTot):
       - /home/grigory/Downloads/hacl-star/specs/ contains pure specifications
       - Example from Spec.GaloisField.fst:
       val fexp: #f:field -> a:felem f -> n:nat{n >= 1} -> Tot (felem f) (decreases n)
       let rec fexp #f a x =
         if x = 1 then a else ...

       Effectful Implementation Code:
       - /home/grigory/Downloads/hacl-star/code/ uses Stack, ST, StackInline
       - Example from Hacl.Impl.Curve25519.Field51.fst:
       inline_for_extraction noextract
       val create_felem: unit
         -> StackInline felem
           (requires fun _ -> True)
           (ensures  fun h0 f h1 ->
             stack_allocated f h0 h1 (LSeq.create 5 (u64 0)) /\
             as_nat h1 f == 0)

       FStar.All Usage (/home/grigory/Downloads/everparse/src/3d/Ast.fst)

       EverParse's 3d frontend uses FStar.All for ML-style effects:
       open FStar.All

       noeq
       type comments_buffer_t = {
         push: string & pos & pos -> ML unit;
         flush: unit -> ML (list string);
       }

       The ML effect is used for parsing/AST manipulation code that runs at compile time, not for verified runtime code.

       ---
       4. REFINEMENT TYPE PATTERNS

       size_t / size_nat Patterns (/home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fsti)

       Critical type definitions:
       unfold let max_size_t = maxint U32

       unfold type size_nat = n:nat{n <= max_size_t}

       unfold type size_pos = n:pos{n <= max_size_t}

       unfold type size_t = uint_t U32 PUB

       unfold let size (n:size_nat) : size_t = uint #U32 #PUB n

       Bounded integer pattern with secrecy levels:
       type secrecy_level = | SEC | PUB

       inline_for_extraction
       let int_t (t:inttype) (l:secrecy_level) =
         match l with
         | PUB -> pub_int_t t
         | SEC -> sec_int_t t

       Parser Kind Pattern (/home/grigory/Downloads/everparse/src/lowparse/LowParse.Spec.Base.fsti)

       Complex refinement for parser metadata:
       inline_for_extraction
       type parser_kind' = {
         parser_kind_low: nat;
         parser_kind_high: option nat;
         parser_kind_subkind: option parser_subkind;
         parser_kind_metadata: parser_kind_metadata_t;
       }

       let parser_kind = (x: parser_kind' {
         Some? x.parser_kind_high ==> x.parser_kind_low <= Some?.v x.parser_kind_high
       })

       ---
       5. MEMORY MANAGEMENT (HACL* Focus)

       LowStar.Buffer Patterns (/home/grigory/Downloads/hacl-star/code/curve25519/Hacl.Impl.Curve25519.Field51.fst)

       Standard memory management idioms:

       module B = LowStar.Buffer
       module ST = FStar.HyperStack.ST

       -- Stack allocation with specification
       inline_for_extraction noextract
       val set_zero:
         f:felem -> Stack unit
         (requires fun h -> live h f)
         (ensures  fun h0 _ h1 ->
           modifies (loc f) h0 h1 /\
           as_nat h1 f == 0)

       Key patterns:
       1. live h f - buffer validity predicate
       2. modifies (loc f) h0 h1 - frame condition specifying modified memory
       3. stack_allocated f h0 h1 init - stack allocation with initial value
       4. loc_none, loc_union - location algebra for framing

       Memory State Verification Pattern:

       let mk_alloca a () =
         let h0 = ST.get () in
         let st = Hacl.Impl.SHA2.Generic.alloc a Vec.M32 in
         Hacl.Impl.SHA2.Generic.init st;
         let h1 = ST.get () in
         LowStar.Buffer.(modifies_only_not_unused_in loc_none h0 h1);
         coerce_to_state a st

       ---
       6. NOEQ TYPE PATTERNS

       When noeq is Appropriate

       HACL Example (/home/grigory/Downloads/hacl-star/specs/Spec.GaloisField.fst):*
       noeq type field =
         | GF: t:inttype{unsigned t /\ t <> U1} -> irred: uint_t t SEC -> field

       EverParse Examples (/home/grigory/Downloads/everparse/src/3d/Ast.fst):
       noeq type comments_buffer_t = {
         push: string & pos & pos -> ML unit;
         flush: unit -> ML (list string);
         flush_until: pos -> ML (list string);
       }

       noeq type with_meta_t 'a = {
         v:'a;
         range:range;
         comments: comments
       }

       Why noeq is used:
       1. Contains functions/closures - equality cannot be decidable on function types
       2. Contains abstract types - like sec_int_t which hides implementation
       3. Performance optimization - avoids generating equality checking code when not needed
       4. Mutable state references - records containing ref types

       ---
       7. MODULE SYSTEM PATTERNS

       Module Aliases (/home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fst)

       Standard alias pattern:
       module B = LowStar.Buffer
       module IB = LowStar.ImmutableBuffer
       module ST = FStar.HyperStack.ST
       module Seq = Lib.Sequence

       Include Pattern (/home/grigory/Downloads/everparse/src/lowparse/LowParse.Spec.Combinators.fsti)

       EverParse uses include extensively for parser combinator layering:
       include LowParse.Spec.Base

       From multiple files:
       LowParse.Spec.Combinators.fsti:include LowParse.Spec.Base
       LowParse.Low.Base.Spec.fsti:include LowParse.Spec.Base
       LowParse.Low.Base.Spec.fsti:include LowParse.Slice
       LowParse.Low.Base.Spec.fsti:include LowParse.CLens

       Include vs Open:
       - include re-exports all names (used for building combinator hierarchies)
       - open only brings names into scope locally

       Friend Pattern (/home/grigory/Downloads/hacl-star/code/hash/Hacl.Hash.SHA2.fst)

       // To prove we are properly defining init
       friend Spec.Agile.Hash
       // To prove we are properly defining update_last
       friend Spec.Hash.Incremental
       // To know the definition of init
       friend Spec.SHA2

       The friend keyword grants access to abstract type implementations for verification purposes.

       ---
       8. HINT FILES (/home/grigory/Downloads/hacl-star/hints/)

       Structure (JSON format):
       [
         "01d94a7dbf1115efa1b2c3e4012b8c7e",  // file hash
         [
           ["Hacl.Hash.SHA2.coerce_to_state",   // function name
            1,                                   // query index
            0,                                   // fuel
            1,                                   // ifuel
            [                                    // Z3 hints (lemmas/tactics used)
              "@MaxFuel_assumption",
              "equation_Lib.IntTypes.bits",
              ...
            ]
           ]
         ]
       ]

       Purpose:
       - Cache Z3 proof state between builds
       - Dramatically speed up re-verification (hours -> minutes)
       - HACL* has 1100+ hint files (one per .fst file)

       Usage flags:
       FSTAR_HINTS ?= --use_hints --use_hint_hashes --record_hints

       ---
       9. CROSS-CUTTING DESIGN PATTERNS SUMMARY

       | Pattern           | HACL*                                  | EverParse                                    |
       |-------------------|----------------------------------------|----------------------------------------------|
       | Effect separation | specs/ (Tot) vs code/ (Stack)          | LowParse.Spec (GTot) vs LowParse.Low (Stack) |
       | Memory model      | LowStar.Buffer with explicit modifies  | Slice-based with validators                  |
       | noeq usage        | Crypto types with secret values        | AST types with functions                     |
       | Testing           | Vector comparison with createL_mglobal | Roundtrip parser testing                     |
       | Build             | Complex Karamel bundles                | Simpler 3d extraction                        |
       | Module layering   | Hierarchical Impl -> Spec -> Def       | Combinator include chains                    |
       | Z3 tuning         | Aggressive fuel/ifuel limits, hints    | Similar but less aggressive                  |

       ---
       10. CRITICAL FILES FOR REFERENCE

       HACL:*
       - /home/grigory/Downloads/hacl-star/lib/Lib.IntTypes.fsti - Integer type system
       - /home/grigory/Downloads/hacl-star/lib/Lib.Buffer.fsti - Memory management
       - /home/grigory/Downloads/hacl-star/Makefile.common - Build patterns
       - /home/grigory/Downloads/hacl-star/code/hash/Hacl.Hash.SHA2.fst - Implementation pattern

       EverParse:
       - /home/grigory/Downloads/everparse/src/lowparse/LowParse.Spec.Base.fsti - Parser foundations
       - /home/grigory/Downloads/everparse/src/3d/Ast.fst - AST with ML effects
       - /home/grigory/Downloads/everparse/tests/Test.fst - Testing pattern
  ⎿  Done (33 tool uses · 103.0k tokens · 2m 53s)

∴ Thinking…

  The 4 elite-bug-hunter agents have completed their analysis. Let me summarize the key findings from all 4 agents into a comprehensive overview for the user.

● Excellent! All 4 agents completed their deep analysis. Here's the consolidated findings:                                                                                                                     12:29 PM  claude-opus-4-5-20251101

  ---
  COMPREHENSIVE F* REFERENCE CODEBASE ANALYSIS

  HACL* (991 F* files) - Agent 1: Architecture

  Directory Layering Pattern

  specs/           → Pure mathematical specs (Spec.*)
    └── lemmas/    → Proof files
  code/            → Implementation code
    ├── Hacl.Spec.*   → Low-level functional specs
    ├── Hacl.Impl.*   → Imperative implementations (LowStar)
    └── Hacl.*        → Top-level APIs
  lib/             → Shared library (Lib.Buffer, Lib.Sequence, Lib.IntTypes)
  providers/       → EverCrypt agility layer (runtime dispatch)
  dist/            → Generated C code via Karamel

  Key Patterns Discovered

  1. Interface/Implementation Separation
  - .fsti declares val with pre/post conditions
  - .fst provides implementations
  - Example: Lib.Buffer.fsti (44KB) vs Lib.Buffer.fst (24KB)

  2. friend Declarations - Controlled proof access:
  friend Spec.SHA2           // Access abstract definitions for proofs
  friend Hacl.Spec.Bignum.Montgomery

  3. Inline Annotations:
  - inline_for_extraction - Inline during C extraction
  - noextract - Proof-only, don't extract
  - unfold - Expand during normalization
  - [@inline_let] - Inline let-bindings

  4. Type Abstraction:
  // In .fsti - abstract
  inline_for_extraction val sec_int_t: inttype -> Type0

  // In .fst - concrete (revealed to friends)
  let sec_int_t t = match t with U32 -> FStar.UInt32.t | ...

  ---
  HACL* - Agent 2: Proofs & Lemmas

  Lemma Organization

  specs/lemmas/
  ├── Spec.Ed25519.Lemmas.fst    (44KB - largest)
  ├── Spec.SHA2.Lemmas.fst       (17KB)
  ├── Spec.Hash.Lemmas.fst       (9KB)
  ├── Spec.K256.Lemmas.fst       (4KB)
  └── Spec.P256.Lemmas.fst       (admitted)

  Z3 Tuning Statistics

  | z3rlimit | Count   | --fuel | Count |
  |----------|---------|--------|-------|
  | 50       | 402     | 0      | 643   |
  | 100      | 159     | 1      | 55    |
  | 200      | 75      |        |       |
  | 3000     | 1 (max) |        |       |

  Default pattern: #set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

  Admits Analysis

  Total: 74 admits across 991 files (<1%)

  | Location                | Count | Reason                         |
  |-------------------------|-------|--------------------------------|
  | Lib.IntVector.fst       | 57    | SIMD intrinsics axiomatization |
  | Spec.P256.Lemmas.fst    | 6     | Elliptic curve group laws      |
  | Spec.K256.Lemmas.fst    | 4     | Elliptic curve group laws      |
  | Spec.Ed25519.Lemmas.fst | 2     | Assumed primality              |

  Key Proof Patterns

  // calc blocks for equational reasoning
  calc (==) {
    (a * b % m) * c % m;
    == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c m }
    (a * b) * c % m;
  }

  // SMTPat for automatic lemma application
  val lemma_foo: x:t -> Lemma (P x) [SMTPat (foo x)]

  // reveal_opaque for opaque function proofs
  reveal_opaque (`%ws) ws

  ---
  EverParse (576 F* files) - Agent 3: AST/Types

  Core with_meta_t Pattern

  noeq type with_meta_t 'a = {
    v: 'a;           // The value
    range: range;    // Source span (pos * pos)
    comments: comments
  }

  // Usage throughout AST:
  let ident = with_meta_t ident'
  let expr = with_meta_t expr'
  let typ = with_meta_t typ'

  Environment Threading

  noeq type env = {
    this: option ident;           // Current type context
    generics: list generic_param; // Generic params in scope
    locals: H.t ident' (ident' & typ & bool);  // bool = used?
    globals: global_env;
  }

  // Pattern: copy_env for scoped changes
  let check_record env fs =
    let env = copy_env env in  // Deep copy
    ...

  Error Handling

  exception Error of string

  let error #a msg (r:range) : ML a =
    raise (Error (Printf.sprintf "%s: (Error) %s\n"
                  (string_of_pos (fst r)) msg))

  Target vs AST Differences

  | AST                         | Target                          |
  |-----------------------------|---------------------------------|
  | Plus of option integer_type | Plus of integer_type (resolved) |
  | Has This, Static, SizeOf    | Eliminated before translation   |
  | with_meta_t wrapper         | Simple (expr' * range) pair     |

  ---
  Cross-Cutting Patterns - Agent 4

  Effect Separation

  | Layer       | Effect                 | Purpose                 |
  |-------------|------------------------|-------------------------|
  | specs/      | Tot, Pure, GTot        | Mathematical specs      |
  | code/       | Stack, ST, StackInline | Verified implementation |
  | 3d frontend | ML (FStar.All)         | Compile-time processing |

  Memory Management (LowStar)

  val copy:
    o:lbuffer a len -> i:lbuffer_t t a len ->
    Stack unit
      (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint i o)
      (ensures  fun h0 _ h1 ->
        modifies1 o h0 h1 /\
        as_seq h1 o == as_seq h0 i)

  noeq Usage Criteria

  - Contains functions/closures
  - Contains abstract types (e.g., sec_int_t)
  - Performance optimization (skip equality code generation)
  - Mutable state references

  Hint Files (.hints/)

  ["Hacl.Hash.SHA2.init", 1, 0, 1,
    ["@MaxFuel_assumption", "equation_Lib.IntTypes.bits", ...]]
  - Cache Z3 proof state
  - 1100+ hint files in HACL*
  - Flags: --use_hints --use_hint_hashes --record_hints

  ---
  RECOMMENDATIONS FOR BRRR-LANG/BRRR-MACHINE

  Based on reference patterns:

  | Pattern              | Current State  | Recommendation                                      |
  |----------------------|----------------|-----------------------------------------------------|
  | .fsti interfaces     | Missing        | Add for all public modules                          |
  | Lemma files          | Inline         | Create brrr-machine/src/analysis/lemmas/            |
  | with_meta_t          | Not used       | Add source location tracking                        |
  | Z3 options           | Not tuned      | Add #set-options "--z3rlimit 50 --fuel 0 --ifuel 0" |
  | Hint files           | Missing        | Configure --record_hints                            |
  | Spec/Impl separation | Flat           | Create spec/ vs impl/ layers                        |
  | Admits               | ~12 documented | Acceptable - document why                           |

