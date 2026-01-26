# F* Quick Reference Guide
# For full documentation see: brrr-lang/fstar_doc.md (12,530 lines)

## 1. COMPILER ARCHITECTURE

### Entry Points
```
FStarC.Main.main()           # CLI entry point
FStarC.Universal.batch_mode_tc()  # Batch compilation
FStarC.Interactive.Ide.interactive_mode()  # IDE mode (--ide)
```

### Compilation Pipeline
```
Source File (.fst/.fsti)
    ↓ FStarC.Parser.ParseIt.parse()
Parser AST (FStarC.Parser.AST.decl)
    ↓ FStarC.ToSyntax.ToSyntax.desugar_*
Internal Syntax (FStarC.Syntax.Syntax.term)
    ↓ FStarC.TypeChecker.Tc.tc_decl()
Type-checked Term + Guards
    ↓ FStarC.SMTEncoding.Encode.*
SMT Queries → Z3
    ↓ FStarC.Extraction.ML.* / FStarC.Extraction.Krml.*
OCaml/F#/C Code
```

### Key Source Locations (FStar repo)
```
src/parser/          # Parser, lexer, AST
src/tosyntax/        # Desugaring (name resolution)
src/syntax/          # Internal term representation
src/typechecker/     # Type checker, normalization
src/smtencoding/     # SMT encoding for Z3
src/tactics/         # Tactic engine
src/extraction/      # Code generation
ulib/                # Standard library
```

---
## 2. SYNTAX REPRESENTATION

### Parser AST (FStarC.Parser.AST)
```fstar
// Unstratified - terms and types unified
type term' =
  | Wild           // _
  | Const c        // Literal
  | Var lid        // Variable
  | Name lid       // Constructor/type name
  | App (t, args)  // Application
  | Abs (pats, t)  // Lambda: fun p -> t
  | Let (q, lbs, t)// Let binding
  | Ascribed (t, ty, tac, eq)  // t <: ty
  | ...

type decl' =
  | TopLevelModule lid
  | Val (lid, ty)           // val f : t
  | Let (q, lbs)            // let f = e
  | Tycon (is_effect, tcs)  // type/effect definition
  | Assume (lid, t)         // assume val
  | Pragma p
  | ...
```

### Internal Syntax (FStarC.Syntax.Syntax)
```fstar
// De Bruijn indexed terms
type term' =
  | Tm_bvar bv              // Bound variable (index)
  | Tm_name bv              // Free variable (name)
  | Tm_fvar fv              // Fully qualified name
  | Tm_uinst (fv, univs)    // Universe instantiation
  | Tm_constant c           // Literal
  | Tm_type u               // Type u#a
  | Tm_abs (bs, t, rc)      // Lambda
  | Tm_arrow (bs, c)        // Function type
  | Tm_refine (bv, phi)     // Refinement {x:t | phi}
  | Tm_app (t, args)        // Application
  | Tm_match (t, bs, rc)    // Pattern match
  | Tm_let (lbs, t)         // Let binding
  | Tm_ascribed (t, asc, eff)
  | Tm_meta (t, meta)       // Metadata wrapper
  | Tm_lazy li              // Lazy thunk
  | Tm_quoted (t, qi)       // Quotation
  | Tm_unknown              // Placeholder

type binder = {
  binder_bv: bv;
  binder_qual: option binder_qual;  // Implicit, Meta, Equality
  binder_positivity: option positivity_qualifier;
  binder_attrs: list attribute;
}

type comp' =
  | Total t                 // Tot t
  | GTotal t                // GTot t (ghost)
  | Comp ct                 // M t wp (effect)
```

### Delayed Substitution
```fstar
// Substitutions are delayed for efficiency
type subst_elt =
  | DB (int, bv)      // De Bruijn shift
  | NM (bv, int)      // Name to de Bruijn
  | NT (bv, term)     // Name to term
  | UN (int, universe)// Universe substitution
  | UD (univ_name, int)

// Apply with:
FStarC.Syntax.Subst.compress : term -> term  // Force substitution
FStarC.Syntax.Subst.subst : list subst_elt -> term -> term
```

---
## 3. TYPE CHECKER

### Core Functions (FStarC.TypeChecker.Tc)
```fstar
// Main entry points
val tc_decl : env -> sigelt -> list sigelt & list sigelt  // (checked, generalized)
val tc_term : env -> term -> term & lcomp & guard_t

// Environment operations
val Env.push_binder : env -> binder -> env
val Env.push_let_binding : env -> lbname -> tscheme -> env
val Env.lookup_lid : env -> lid -> (universes & typ) & range
```

### Bidirectional Type Checking
```fstar
// Inference mode: synthesize type from term
tc_term env e → (e', t, guard)

// Checking mode: check term against expected type
tc_check_tot_or_gtot_term env e t → (e', guard)

// With expected type hint
tc_term_with_type env e expected_typ → (e', lc, guard)
```

### Guards
```fstar
type guard_t = {
  guard_f: guard_formula;     // Proof obligation
  deferred_to_tac: list (...)// Deferred to tactics
  implicits: implicits_t;    // Unresolved implicits
}

// Discharge guards
Rel.force_trivial_guard : env -> guard_t -> unit
Rel.discharge_guard : env -> guard_t -> guard_t  // May leave residual
```

### Rel.fst - Unification (237KB, largest file)
```fstar
// Key types
type worklist = {
  attempting: list prob;      // Current problems
  wl_deferred: list (...)    // Deferred constraints
  ctr: int;                  // Counter for uvars
  ...
}

type prob =
  | TProb of tprob           // Type problem
  | CProb of cprob           // Computation problem

// Main solver
val solve : env -> worklist -> solution
val teq : env -> t1:typ -> t2:typ -> guard_t  // t1 = t2
val subtype : env -> t1:typ -> t2:typ -> guard_t  // t1 <: t2

// Flex-rigid patterns (uvar vs concrete)
// Flex-flex patterns (uvar vs uvar)
```

---
## 4. NORMALIZATION

### Reduction Strategies (FStarC.TypeChecker.Normalize)
```fstar
type step =
  | Beta              // (fun x -> e) v → e[v/x]
  | Iota              // match C v with C x -> e → e[v/x]
  | Zeta              // Unfold recursive definitions
  | ZetaFull          // Unfold all recursion
  | Delta             // Unfold definitions
  | Primops           // Evaluate primitive operations
  | Simplify          // Propositional simplification
  | EraseUniverses    // Remove universe annotations
  | AllowUnboundUniverses
  | Reify             // Reify effects
  | Unmeta            // Remove metadata
  | Unascribe         // Remove ascriptions
  | NBE               // Use NBE instead of interpreter
  | ...

val normalize : list step -> env -> term -> term
val normalize_comp : list step -> env -> comp -> comp
```

### Normalization By Evaluation (NBE)
```fstar
// Faster for large terms - compiles to OCaml closures
FStarC.TypeChecker.NBE.normalize : list step -> env -> term -> term

// Embeddings for primitive types
type embedding 'a = {
  em: 'a -> term;    // Embed value to term
  un: term -> option 'a;  // Unembed term to value
  typ: typ;
}
```

---
## 5. EFFECT SYSTEM

### Built-in Effects
```fstar
// Pure effects
effect PURE (a:Type) (pre:Type0) (post:a -> Type0) = ...
effect Pure (a:Type) (pre:Type0) (post:a -> Type0) = PURE a pre (fun r -> pre ==> post r)
effect Tot (a:Type) = PURE a True (fun _ -> True)

// Ghost (erased at extraction)
effect GHOST (a:Type) (pre:Type0) (post:a -> Type0) = ...
effect GTot (a:Type) = GHOST a True (fun _ -> True)

// Divergence
effect DIV (a:Type) (pre:Type0) (post:a -> Type0) = ...
effect Div (a:Type) (pre:Type0) (post:a -> Type0) = DIV a pre (fun r -> pre ==> post r)
effect Dv (a:Type) = DIV a True (fun _ -> True)

// State (HyperStack)
effect STATE_h (heap:Type) (a:Type) (pre:heap -> Type0) (post:heap -> a -> heap -> Type0)
effect ST (a:Type) (pre:...) (post:...) = STATE_h mem a pre post
effect Stack (a:Type) (pre:...) (post:...) = ...  // Stack discipline
```

### Lemma Effect
```fstar
// Desugared specially by the compiler
effect Lemma (a:Type) (pre:Type0) (post:squash pre -> Type0) (pats:list pattern) =
  Pure unit pre (fun _ -> post ())

// Usage forms:
val lemma1 : unit -> Lemma (ensures P)
val lemma2 : x:t -> Lemma (requires Q x) (ensures P x)
val lemma3 : x:t -> Lemma (requires Q x) (ensures P x) [SMTPat (f x)]
```

### Layered Effects (user-defined)
```fstar
// Define effect with:
layered_effect {
  M : a:Type -> wp:... -> Effect
  with repr = ...
       return = ...
       bind = ...
       subcomp = ...
       if_then_else = ...
}

// Lift between effects
sub_effect PURE ~> M = lift_pure_M
```

---
## 6. SMT ENCODING

### Term Encoding (FStarC.SMTEncoding.Term)
```fstar
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort        // Main F* term sort
  | Fuel_sort        // For termination
  | BitVec_sort of int
  | Array (s1, s2)
  | Arrow (s1, s2)
  | Sort of string

type term =
  | Integer of string
  | BoundV of int
  | FreeV of fv
  | App (op, terms)
  | Quant (qop, pats, wopt, sorts, term)  // forall/exists with patterns
  | Let (bindings, term)
  | Labeled (term, msg, range)
  | LblPos (term, string)
```

### Fuel Encoding (termination)
```fstar
// Recursive calls consume fuel
// Base case: fuel = 0 → undefined
// SMT patterns trigger fuel increment
```

### SMT Patterns (Triggers)
```fstar
// In F* lemmas:
val my_lemma : x:t -> Lemma (P x) [SMTPat (f x)]

// Encoded as:
(forall ((x Term))
  (! (=> (HasType x T) (P x))
     :pattern ((f x))))
```

---
## 7. TACTICS SYSTEM

### Tactic Monad
```fstar
// Core type (simplified)
type tac a = proofstate -> __result a

type proofstate = {
  main_context: env;
  all_implicits: implicits;
  goals: list goal;
  smt_goals: list goal;
  depth: int;
  ...
}

// Tactic effect
effect Tac (a:Type) = TAC a (fun _ p -> True) (fun _ r p -> True)
```

### Core Tactics (FStar.Tactics.V2.Builtins)
```fstar
// Goal manipulation
val intro : unit -> Tac binder          // Intro hypothesis
val exact : term -> Tac unit            // Provide exact proof term
val apply : term -> Tac unit            // Apply function/lemma
val apply_lemma : term -> Tac unit      // Apply lemma

// Inspection
val cur_env : unit -> Tac env
val cur_goal : unit -> Tac typ
val cur_witness : unit -> Tac term

// Control flow
val trivial : unit -> Tac unit          // Solve with True
val smt : unit -> Tac unit              // Discharge to SMT
val trefl : unit -> Tac unit            // Reflexivity
val norm : list norm_step -> Tac unit   // Normalize goal
val compute : unit -> Tac unit          // Full normalization

// Debugging
val print : string -> Tac unit
val dump : string -> Tac unit           // Dump goals
val fail : string -> Tac 'a

// Combinators
val or_else : (unit -> Tac 'a) -> (unit -> Tac 'a) -> Tac 'a
val try_with : (unit -> Tac 'a) -> (exn -> Tac 'a) -> Tac 'a
val repeat : (unit -> Tac unit) -> Tac unit
val first : list (unit -> Tac 'a) -> Tac 'a
```

### Using Tactics
```fstar
// Inline tactic call
let proof = assert P by (tactic ())

// As lemma proof
let lemma_proof () : Lemma P =
  _ by (apply_lemma (`other_lemma); trivial ())

// Synthesize witness
let witness : t = synth_by_tactic (fun () -> exact (`value))
```

---
## 8. REFLECTION API

### Term Inspection (FStar.Reflection.V2)
```fstar
// Inspect term structure
val inspect : term -> term_view
val pack : term_view -> term

type term_view =
  | Tv_Var of namedv
  | Tv_BVar of bv
  | Tv_FVar of fv
  | Tv_UInst of fv & list universe
  | Tv_App of term & argv
  | Tv_Abs of binder & term
  | Tv_Arrow of binder & comp
  | Tv_Type of universe
  | Tv_Refine of binder & term
  | Tv_Const of vconst
  | Tv_Let of bool & list term & binder & term & term
  | Tv_Match of term & option match_returns_ascription & list branch
  | Tv_AscribedT of term & term & option term & bool
  | Tv_AscribedC of term & comp & option term & bool
  | Tv_Unknown
  | Tv_Unsupp

// Quotation
val quote : 'a -> Tac term     // Quote value to term
val unquote : term -> Tac 'a   // Unquote term to value
```

### Environment Lookup
```fstar
val lookup_typ : env -> name -> option sigelt
val lookup_val : env -> name -> option typ
val binders_of_env : env -> binders
val fv_to_string : fv -> string
```

---
## 9. EXTRACTION

### ML Extraction (FStarC.Extraction.ML)
```fstar
// Type translation
F* Type          →  OCaml Type
─────────────────────────────────
int              →  Prims.int (Z.t)
nat              →  Prims.nat (Z.t with x >= 0)
bool             →  bool
unit             →  unit
list a           →  a list
option a         →  a option
a & b            →  a * b
a -> b           →  a -> b
{x:a | p}        →  a (refinement erased)
erased a         →  unit
squash p         →  unit

// Effect tags
E_PURE → pure (no side effects)
E_GHOST → erased (becomes unit)
E_IMPURE → effectful
```

### Karamel/Low* Extraction (FStarC.Extraction.Krml)
```fstar
// Low* types → C types
LowStar.Buffer.buffer uint8    →  uint8_t*
LowStar.Buffer.buffer uint32   →  uint32_t*
FStar.UInt32.t                 →  uint32_t
FStar.UInt64.t                 →  uint64_t

// Key annotations
inline_for_extraction  // Inline before extraction
noextract             // Don't extract (proof-only)
```

### Key Attributes
```fstar
[@@inline_for_extraction]    // Inline during extraction
[@@noextract]                // Don't extract
[@@CInline]                  // C inline hint
[@@CMacro]                   // Extract as C macro
[@@CPrologue "..."]          // C code before definition
[@@CEpilogue "..."]          // C code after definition
```

---
## 10. STANDARD LIBRARY (ulib/)

### Lists (FStar.List.Tot)
```fstar
val length : list 'a -> nat
val hd : l:list 'a{Cons? l} -> 'a
val tl : l:list 'a{Cons? l} -> list 'a
val nth : list 'a -> nat -> option 'a
val index : l:list 'a -> i:nat{i < length l} -> 'a
val append : list 'a -> list 'a -> list 'a  // infix @
val rev : list 'a -> list 'a
val map : ('a -> 'b) -> list 'a -> list 'b
val fold_left : ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
val fold_right : ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
val filter : ('a -> bool) -> list 'a -> list 'a
val find : f:('a -> bool) -> list 'a -> option (x:'a{f x})
val mem : #a:eqtype -> a -> list a -> bool
val memP : #a:Type -> a -> list a -> Type0  // Propositional
val for_all : ('a -> bool) -> list 'a -> bool
val existsb : ('a -> bool) -> list 'a -> bool
val assoc : #a:eqtype -> #b:Type -> a -> list (a & b) -> option b
val sortWith : ('a -> 'a -> int) -> list 'a -> list 'a
```

### Sequences (FStar.Seq)
```fstar
val length : seq 'a -> nat
val index : s:seq 'a -> i:nat{i < length s} -> 'a
val create : nat -> 'a -> seq 'a
val init : len:nat -> (i:nat{i < len} -> 'a) -> seq 'a
val empty : seq 'a
val upd : s:seq 'a -> n:nat{n < length s} -> 'a -> seq 'a
val append : seq 'a -> seq 'a -> seq 'a  // infix @|
val slice : s:seq 'a -> i:nat -> j:nat{i <= j /\ j <= length s} -> seq 'a
val equal : seq 'a -> seq 'a -> prop
val seq_to_list : seq 'a -> list 'a
val seq_of_list : list 'a -> seq 'a
```

### Sets and Maps
```fstar
// FStar.Set
val empty : set 'a
val singleton : 'a -> set 'a
val mem : 'a -> set 'a -> bool
val union : set 'a -> set 'a -> set 'a
val intersect : set 'a -> set 'a -> set 'a
val complement : set 'a -> set 'a

// FStar.Map
val sel : t key value -> key -> value
val upd : t key value -> key -> value -> t key value
val const : value -> t key value
val domain : t key value -> set key
val contains : t key value -> key -> bool
```

### Classical Logic (FStar.Classical)
```fstar
val forall_intro : (#a:Type) -> (#p:a -> Type) ->
                   (x:a -> Lemma (p x)) -> Lemma (forall x. p x)
val forall_intro_2 : ... -> Lemma (forall x y. p x y)
val exists_intro : (#a:Type) -> (p:a -> Type) -> (witness:a) ->
                   Lemma (requires p witness) (ensures exists x. p x)
val exists_elim : (goal:Type) -> (#a:Type) -> (#p:a -> Type) ->
                  squash (exists x. p x) -> (x:a{p x} -> squash goal) -> Lemma goal
val move_requires : (x:a -> Lemma (requires p x) (ensures q x)) ->
                    x:a -> Lemma (p x ==> q x)
val excluded_middle : p:Type -> Lemma (p \/ ~p)
```

### Math Lemmas (FStar.Math.Lemmas)
```fstar
// Modular arithmetic
val lemma_mod_plus : a:int -> k:int -> n:pos -> Lemma ((a + k * n) % n = a % n)
val lemma_mod_mul_distr_l : a:int -> b:int -> n:pos -> Lemma ((a * b) % n = ((a % n) * b) % n)
val cancel_mul_mod : a:int -> n:pos -> Lemma ((a * n) % n = 0)
val small_mod : a:nat -> n:pos -> Lemma (requires a < n) (ensures a % n = a)

// Powers of 2
val pow2_plus : n:nat -> m:nat -> Lemma (pow2 n * pow2 m = pow2 (n + m))
val pow2_lt_compat : n:nat -> m:nat -> Lemma (requires m < n) (ensures pow2 m < pow2 n)

// Division
val lemma_div_mod : a:int -> p:nonzero -> Lemma (a = p * (a / p) + a % p)
val small_div : a:nat -> n:pos -> Lemma (requires a < n) (ensures a / n = 0)
```

### Ghost/Erased (FStar.Ghost)
```fstar
[@@ erasable]
val erased : Type -> Type       // Computationally irrelevant wrapper

val reveal : erased 'a -> GTot 'a  // Unwrap (ghost only)
val hide : 'a -> erased 'a         // Wrap

// Lemmas with SMT patterns
val hide_reveal : x:erased 'a -> Lemma (hide (reveal x) == x) [SMTPat (reveal x)]
val reveal_hide : x:'a -> Lemma (reveal (hide x) == x) [SMTPat (hide x)]

// Monadic operations
let (let@) (x:erased 'a) (f:'a -> erased 'b) : erased 'b = ...
```

### Calculational Proofs (FStar.Calc)
```fstar
// Syntax:
calc (==) {
    expr1;
    == { lemma1 () }    // Justification
    expr2;
    == { lemma2 () }
    expr3;
}
// Proves: expr1 == expr3
```

---
## 11. LOW*/LOWSTAR (Memory-Safe C)

### Buffer Operations (LowStar.Buffer)
```fstar
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

val sub : b:buffer 'a -> i:UInt32.t -> len:UInt32.t -> Stack (buffer 'a)
  // Pointer arithmetic: returns b + i
```

### Memory Predicates
```fstar
val live : mem -> buffer 'a -> Type0      // Buffer is allocated
val modifies : loc -> mem -> mem -> Type0  // Only loc changed
val loc_buffer : buffer 'a -> loc          // Location of buffer
val loc_none : loc                         // Empty location
val loc_union : loc -> loc -> loc          // Union of locations
val disjoint : buffer 'a -> buffer 'b -> Type0
```

### Stack Effects
```fstar
effect Stack (a:Type) (pre:mem -> Type0) (post:mem -> a -> mem -> Type0) = ...
effect StackInline (a:Type) (...) = ...  // Inlined into caller's frame

val push_frame : unit -> Stack unit ...
val pop_frame : unit -> Stack unit ...

// Pattern:
let my_function () : Stack unit ... =
  push_frame ();
  let buf = create 0uy 16ul in  // Stack allocated
  // ... use buf ...
  pop_frame ()  // buf deallocated
```

---
## 12. COMMAND-LINE OPTIONS

### Verification
```
--admit_smt_queries    Admit all SMT (unsafe)
--lax                  Lax type checking only
--no_smt               Fail on SMT queries
```

### Fuel/Resources
```
--initial_fuel N       Initial recursive unrolling (default: 2)
--max_fuel N           Max recursive unrolling (default: 8)
--initial_ifuel N      Initial inductive unrolling (default: 1)
--max_ifuel N          Max inductive unrolling (default: 2)
--z3rlimit N           Z3 resource limit (default: 5)
--z3rlimit_factor N    Multiplier for z3rlimit
```

### Hints/Caching
```
--use_hints            Use hints database
--record_hints         Record hints
--use_hint_hashes      Admit on hash match
--cache_checked_modules Write .checked files
--cache_dir DIR        Cache directory
```

### Output
```
--codegen TARGET       OCaml|FSharp|krml|Plugin
--odir DIR             Output directory
--extract MODULES      Module extraction selectors
```

### Debugging
```
--debug TOGGLES        Debug toggles (comma-separated)
--trace_error          Stack traces on errors
--timing               Per-definition timing
--log_queries          Log all SMT queries
```

### IDE
```
--ide                  JSON-based IDE mode
--ide_id_info_off      Disable identifier info
```

---
## 13. PROOF PATTERNS

### SMT Patterns
```fstar
// Single pattern
val lemma1 : x:t -> Lemma (P x) [SMTPat (f x)]

// Multiple patterns
val lemma2 : x:t -> y:t -> Lemma (P x y)
  [SMTPat (f x); SMTPat (g y)]

// Disjunctive patterns
val lemma3 : x:t -> Lemma (P x)
  [SMTPatOr [[SMTPat (f x)]; [SMTPat (g x)]]]
```

### Fuel Control
```fstar
#set-options "--fuel 0 --ifuel 0"  // Minimal (fastest)
#set-options "--fuel 1 --ifuel 1"  // Low
#set-options "--fuel 2 --ifuel 2"  // Default
#push-options "--fuel 4"           // Temporarily increase
#pop-options                       // Restore
```

### Z3 Options
```fstar
#set-options "--z3rlimit 50"
#set-options "--z3seed 42"
#set-options "--z3cliopt smt.arith.nl=false"  // Disable nonlinear
#restart-solver  // Fresh Z3 instance
```

### Admit Patterns
```fstar
// Temporary placeholder
assume val todo_lemma : x:t -> Lemma (P x)

// In-proof admit
let proof x = admit ()  // UNSAFE - marks as unverified

// Magic for extraction
let extract_only x = FStar.Tactics.Effect.synth_by_tactic (fun () -> tadmit())
```

---
## 14. INTERFACE/IMPLEMENTATION (.fsti/.fst)

### Interface File (.fsti)
```fstar
module MyModule

// Public type (abstract)
val my_type : Type0

// Public function signature with spec
val my_function : x:nat -> y:nat{y > x} ->
  Pure nat (requires x > 0) (ensures fun r -> r > y)

// Public lemma
val my_lemma : x:nat -> Lemma (ensures x + 0 = x) [SMTPat (x + 0)]
```

### Implementation File (.fst)
```fstar
module MyModule

// Reveal abstract type
let my_type = int

// Implement function
let my_function x y = x + y + 1

// Prove lemma
let my_lemma x = ()  // Trivial by normalization
```

### Friend Declarations
```fstar
// In implementation, access abstract types from other modules
friend OtherModule  // Grants access to OtherModule's implementation details
```

---
## 15. ORGANIZATION PATTERNS (from HACL*/EverParse)

### Directory Structure
```
project/
├── specs/              # Pure specifications (Spec.*.fst)
│   └── lemmas/         # Proof lemmas (*.Lemmas.fst)
├── code/               # Implementations
│   ├── Impl.*.fst      # Low-level implementations
│   └── Hacl.*.fst      # Top-level APIs
├── lib/                # Shared library (Lib.*.fst)
└── hints/              # Z3 hints cache (*.hints)
```

### Layering Pattern
```
Spec.Algorithm          # Pure mathematical spec
    ↓ refines
Hacl.Spec.Algorithm     # Low-level functional spec
    ↓ refines
Hacl.Impl.Algorithm     # Imperative implementation
    ↓ extracts to
algorithm.c             # Generated C code
```

### Module Naming
```fstar
// Specs
module Spec.Hash.SHA256          // Mathematical specification

// Implementation specs
module Hacl.Spec.SHA2.Vec256     // Vectorized impl spec

// Implementations
module Hacl.Impl.SHA2.Core32     // 32-bit implementation
module Hacl.Hash.SHA2            // Top-level API

// Lemmas
module Hacl.Spec.SHA2.Lemmas     // Proofs about SHA2
```

### Z3 Options Pattern (from HACL*)
```fstar
// Default for most modules
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// For complex proofs
#push-options "--z3rlimit 200 --fuel 1"
let complex_lemma () = ...
#pop-options
```

### noeq Usage
```fstar
// Use noeq when type contains:
noeq type my_record = {
  callback: int -> int;    // Functions (can't compare)
  secret: sec_int_t U32;   // Abstract types
  mutable_ref: ref int;    // References
}

// Don't use noeq for simple data
type point = { x: int; y: int }  // Can derive equality
```

---
## 16. COMMON ERRORS & FIXES

### "Subtyping check failed"
```fstar
// Problem: refinement not provable
let f (x:nat{x > 0}) = x - 1  // Error: can't prove (x-1) >= 0

// Fix: add assertion or strengthen precondition
let f (x:nat{x > 0}) =
  assert (x - 1 >= 0);
  x - 1
```

### "Expected type X, got Y"
```fstar
// Problem: type mismatch
let f (x:uint32) : uint64 = x  // Error

// Fix: explicit cast
let f (x:uint32) : uint64 = FStar.Int.Cast.uint32_to_uint64 x
```

### "Proof obligation failed"
```fstar
// Problem: SMT can't prove
val lemma : x:nat -> Lemma (complex_property x)  // SMT timeout

// Fixes:
// 1. Increase limits
#push-options "--z3rlimit 100"

// 2. Add intermediate assertions
let lemma x =
  assert (intermediate_fact x);  // Hint to SMT
  ()

// 3. Use calc blocks for equational reasoning
let lemma x =
  calc (==) {
    lhs x; == { sub_lemma1 x } rhs x;
  }
```

### "Not an eqtype"
```fstar
// Problem: comparing non-eqtype
let check (x y : my_abstract_type) = x = y  // Error

// Fix: use propositional equality or add decidable equality
let check (x y : my_abstract_type) = x == y  // Propositional (returns Type)
```

---
## 17. DEBUGGING COMMANDS

### Command Line
```bash
# Trace errors
fstar.exe --trace_error MyModule.fst

# Debug specific phases
fstar.exe --debug "Rel,Tc,SMTEncoding" MyModule.fst

# Log SMT queries
fstar.exe --log_queries MyModule.fst

# Timing per definition
fstar.exe --timing MyModule.fst

# Full statistics
fstar.exe --stats true MyModule.fst
```

### In-File Debugging
```fstar
// Print during normalization
let _ = FStar.IO.print_string "reached here"

// In tactics
let _ = by (dump "current goals")

// Inspect types
#check (some_term)

// Show normalized form
#normalize (some_term) [delta; zeta; iota]
```

---
## QUICK LOOKUP TABLE

| Task | Module/Function |
|------|-----------------|
| Parse file | `FStarC.Parser.ParseIt.parse` |
| Desugar | `FStarC.ToSyntax.ToSyntax.desugar_*` |
| Type check | `FStarC.TypeChecker.Tc.tc_term` |
| Normalize | `FStarC.TypeChecker.Normalize.normalize` |
| Unify types | `FStarC.TypeChecker.Rel.teq` |
| Subtype check | `FStarC.TypeChecker.Rel.subtype` |
| SMT encode | `FStarC.SMTEncoding.Encode.encode_*` |
| Run tactic | `FStarC.Tactics.Interpreter.run` |
| Extract ML | `FStarC.Extraction.ML.Term.term_as_mlexpr` |
| Extract C | `FStarC.Extraction.Krml.translate_*` |

| ulib Module | Purpose |
|-------------|---------|
| `FStar.List.Tot` | Pure list operations |
| `FStar.Seq` | Sequences (arrays) |
| `FStar.Set` | Finite sets |
| `FStar.Map` | Partial maps |
| `FStar.Classical` | Classical logic |
| `FStar.Calc` | Calculational proofs |
| `FStar.Math.Lemmas` | Integer arithmetic |
| `FStar.Ghost` | Erased types |
| `FStar.Squash` | Proof irrelevance |
| `LowStar.Buffer` | Memory-safe buffers |

---
## 18. EFFECT ELABORATION EXAMPLES

### Defining Custom Effects
```fstar
// Step 1: Define the effect representation
let state_wp (a:Type) (s:Type) = s -> (a & s -> Type) -> Type

// Step 2: Define effect combinators
let return_state (#a:Type) (#s:Type) (x:a) : state_wp a s =
  fun s0 post -> post (x, s0)

let bind_state (#a #b:Type) (#s:Type)
               (f:state_wp a s) (g:a -> state_wp b s) : state_wp b s =
  fun s0 post -> f s0 (fun (x, s1) -> g x s1 post)

// Step 3: Declare the effect
new_effect {
  STATE_s (s:Type) : a:Type -> state_wp a s -> Effect
  with repr      = (s -> a & s)
     ; return    = return_state
     ; bind      = bind_state
}
```

### Effect Lifting
```fstar
// Lift PURE to STATE
sub_effect PURE ~> STATE_s = fun #a #s (wp: pure_wp a) ->
  fun s0 post -> wp (fun x -> post (x, s0))

// Usage: PURE code works in STATE context
let f () : STATE_s int int =
  let x = 1 + 1 in  // PURE, automatically lifted
  x
```

### Layered Effects (New Style)
```fstar
layered_effect {
  READER (r:Type) : a:Type -> (r -> a -> Type) -> Effect
  with
    repr = (r -> a)
  ; return = fun #a x -> fun _ -> x
  ; bind = fun #a #b f g -> fun r -> g (f r) r
  ; subcomp = fun #a f -> f
  ; if_then_else = fun #a f g b -> fun r -> if b then f r else g r
}
```

---
## 19. MEMORY MANAGEMENT PATTERNS (Low*)

### Stack Allocation Pattern
```fstar
open LowStar.Buffer
open FStar.HyperStack.ST

let stack_example () : Stack unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies loc_none h0 h1)
=
  push_frame ();

  // Stack-allocated buffer (deallocated at pop_frame)
  let buf = alloca 0uy 16ul in

  // Use buffer
  buf.(0ul) <- 42uy;
  let x = buf.(0ul) in

  pop_frame ()
```

### Heap Allocation Pattern
```fstar
let heap_example () : ST (buffer uint8)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    live h1 r /\
    length r = 32 /\
    fresh_loc (loc_buffer r) h0 h1)
=
  // Heap-allocated (must be freed manually)
  let buf = malloc HyperStack.root 0uy 32ul in
  buf

let use_and_free () : ST unit ... =
  let buf = heap_example () in
  // ... use buf ...
  free buf  // Must free to avoid leak
```

### Framing and Modifies
```fstar
// Specify exactly what memory is modified
val copy_buffer :
    src:buffer uint8
  -> dst:buffer uint8{length dst >= length src}
  -> len:UInt32.t{UInt32.v len <= length src}
  -> Stack unit
    (requires fun h0 ->
      live h0 src /\ live h0 dst /\ disjoint src dst)
    (ensures fun h0 _ h1 ->
      // Only dst modified
      modifies (loc_buffer dst) h0 h1 /\
      // src unchanged (framing)
      as_seq h1 src == as_seq h0 src /\
      // dst contains copy
      Seq.slice (as_seq h1 dst) 0 (UInt32.v len) ==
        Seq.slice (as_seq h0 src) 0 (UInt32.v len))
```

### Modifies Algebra
```fstar
// Location combinators
loc_none                     // Empty location
loc_buffer b                 // Single buffer
loc_union l1 l2              // Union
loc_addresses r addrs        // Addresses in region
loc_regions false regions    // All memory in regions

// Useful lemmas
val modifies_refl : l:loc -> h:mem ->
  Lemma (modifies l h h)

val modifies_trans : l1:loc -> h1:mem -> l2:loc -> h2:mem -> h3:mem ->
  Lemma (requires modifies l1 h1 h2 /\ modifies l2 h2 h3)
        (ensures modifies (loc_union l1 l2) h1 h3)

val modifies_only_not_unused_in : l:loc -> h0:mem -> h1:mem ->
  Lemma (requires modifies l h0 h1)
        (ensures forall b. loc_disjoint (loc_buffer b) l /\ live h0 b ==>
                           live h1 b /\ as_seq h1 b == as_seq h0 b)
```

---
## 20. TACTIC RECIPES

### Proving Equalities
```fstar
// Use trefl for syntactic equality
let eq1 () = assert (1 + 1 == 2) by trefl ()

// Use compute for normalized equality
let eq2 () = assert (List.length [1;2;3] == 3) by (compute (); trefl ())

// Use rewrite for substitution
let eq3 (x y : nat) =
  assert (x = y ==> x + 1 = y + 1) by (
    let h = implies_intro () in
    rewrite (binder_to_term h);
    trefl ()
  )
```

### Inspecting and Manipulating Goals
```fstar
let inspect_goal () = assert True by (
  let g = cur_goal () in
  let e = cur_env () in
  dump "Initial goal";        // Print goal state
  print (term_to_string g);   // Print goal type
  trivial ()                  // Solve
)
```

### Custom Tactic Combinators
```fstar
// Repeat until failure
let rec repeat_tac (t : unit -> Tac unit) : Tac unit =
  or_else (fun () -> t (); repeat_tac t) (fun () -> ())

// Try each tactic in order
let rec first_tac (ts : list (unit -> Tac unit)) : Tac unit =
  match ts with
  | [] -> fail "No tactic succeeded"
  | t::ts' -> or_else t (fun () -> first_tac ts')

// Solve all goals with same tactic
let all_goals (t : unit -> Tac unit) : Tac unit =
  let rec go () =
    match goals () with
    | [] -> ()
    | _::_ -> t (); go ()
  in go ()
```

### Automation with norm
```fstar
// Simplify propositional logic
let auto_prop () = assert ((True /\ True) ==> True) by (
  norm [delta; iota; zeta; primops];
  trivial ()
)

// Unfold specific definitions
let unfold_example () = assert (my_def 1 = 2) by (
  norm [delta_only [`%my_def]];
  trefl ()
)
```

---
## 21. REFLECTION RECIPES

### Term Construction
```fstar
// Build term programmatically
let make_app (f : term) (args : list term) : Tac term =
  List.fold_left (fun acc arg -> pack (Tv_App acc (arg, Q_Explicit))) f args

// Quote and unquote
let quoted_term : term = `(1 + 1)
let unquoted () : Tac int = unquote (`(1 + 1))
```

### Type Inspection
```fstar
let inspect_type (t : term) : Tac unit =
  let tc = tc (cur_env ()) t in
  match inspect tc with
  | Tv_Arrow bv c -> print "It's a function type"
  | Tv_Refine bv phi -> print "It's a refinement type"
  | Tv_FVar fv -> print ("It's " ^ fv_to_string fv)
  | _ -> print "Other type"
```

### Pattern Matching on Terms
```fstar
let is_application (t : term) : Tac bool =
  match inspect t with
  | Tv_App _ _ -> true
  | _ -> false

let get_head (t : term) : Tac term =
  match inspect t with
  | Tv_App hd _ -> get_head hd
  | _ -> t
```

---
## 22. ERROR CODE QUICK REFERENCE

### Fatal Errors (compilation stops)
```
12   Fatal_TypeError              Type mismatch
24   Fatal_AssertionFailure       Assert failed
128  Fatal_ModuleNotFound         Module not found
157  Fatal_ParseErrors            Parse error
168  Fatal_SyntaxError            Syntax error
170  Fatal_TacticGotStuck         Tactic stuck
```

### Recoverable Errors (can be suppressed)
```
9    Error_ProofObligationFailed  SMT proof failed
11   Error_TypeCheckerFailToProve TC couldn't prove
13   Error_UnconstrainedUnificationVar  Unresolved uvar
19   Error_Z3SolverError          Z3 error
```

### Warnings (--warn_error to control)
```
241  Warning_CachedFile           Cache issue
251  Warning_HintFailedToReplayProof  Hint failed
290  Warning_Defensive            Defensive check
305  Warning_QuantifierWithoutPattern  Missing SMTPat
328  Warning_UnusedLetRec         Unused recursive binding
```

### Controlling Error Levels
```bash
# Suppress warning
fstar.exe --warn_error -290 MyModule.fst

# Promote warning to error
fstar.exe --warn_error +305 MyModule.fst

# Demote error to warning
fstar.exe --warn_error @9 MyModule.fst
```

---
## 23. HINT SYSTEM

### Recording Hints
```bash
# Record hints during verification
fstar.exe --record_hints --hint_dir ./hints MyModule.fst

# Creates: hints/MyModule.fst.hints
```

### Using Hints
```bash
# Use recorded hints
fstar.exe --use_hints --hint_dir ./hints MyModule.fst

# Use with hash checking (strict)
fstar.exe --use_hints --use_hint_hashes --hint_dir ./hints MyModule.fst
```

### Hint File Format
```json
[
  "file_hash_abc123",
  [
    ["MyModule.lemma_name",
     1,      // query index
     0,      // fuel used
     1,      // ifuel used
     ["@MaxFuel_assumption", "equation_Prims.nat", ...]  // Z3 facts
    ]
  ]
]
```

---
## 24. CACHING SYSTEM

### Checked Files
```bash
# Enable caching
fstar.exe --cache_checked_modules --cache_dir .cache MyModule.fst

# Creates: .cache/MyModule.fst.checked
```

### Cache Verification
```fstar
// In-file cache control
#set-options "--cache_checked_modules"

// Skip dependency checking
#set-options "--already_cached 'Prims FStar LowStar'"
```

### Query Caching (IDE)
```bash
# Experimental: cache SMT queries
fstar.exe --query_cache --ide MyModule.fst
```

---
## 25. IDE PROTOCOL QUICK REFERENCE

### Query Types
```json
// Push code fragment
{"query-id":"1", "query":"push", "args":{"kind":"full","code":"let x = 1","line":1,"column":0}}

// Lookup symbol
{"query-id":"2", "query":"lookup", "args":{"symbol":"List.map","requested-info":["type","documentation"]}}

// Autocomplete
{"query-id":"3", "query":"autocomplete", "args":{"partial-symbol":"List.m","context":"code"}}

// Full buffer verification
{"query-id":"4", "query":"full-buffer", "args":{"code":"module M\nlet x = 1","kind":"full"}}

// Cancel pending
{"query-id":"5", "query":"cancel", "args":{}}
```

### Response Format
```json
{"kind":"response", "query-id":"1", "status":"success", "response":{...}}
{"kind":"response", "query-id":"1", "status":"failure", "response":"error message"}
{"kind":"message", "level":"progress", "contents":{"stage":"full-buffer-fragment-ok"}}
```

---
## 26. ENVIRONMENT VARIABLES

```bash
FSTAR_HOME=/path/to/fstar      # Installation directory
FSTAR_LIB=/path/to/ulib        # Standard library path
Z3_EXE=/path/to/z3             # Z3 executable path
GITHUB_ACTIONS=true            # Use github error format
```

---
## 27. INTERFACE PATTERNS

### Minimal Interface (.fsti)
```fstar
module MyModule

// Abstract type
val my_type : Type0

// Public API
val create : unit -> my_type
val process : my_type -> nat -> my_type
val extract : my_type -> nat

// Specification lemma
val lemma_create_extract : unit ->
  Lemma (extract (create ()) == 0)
```

### Rich Interface with Specs
```fstar
module MyBuffer

open FStar.HyperStack.ST
open LowStar.Buffer

// Abstract state predicate
val invariant : buffer uint8 -> mem -> Type0

// Create with invariant
val create : len:UInt32.t{UInt32.v len > 0} ->
  ST (buffer uint8)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 ->
      live h1 r /\
      length r = UInt32.v len /\
      invariant r h1 /\
      fresh_loc (loc_buffer r) h0 h1)

// Modify preserves invariant
val modify : b:buffer uint8 -> i:UInt32.t -> v:uint8 ->
  ST unit
    (requires fun h0 -> live h0 b /\ invariant b h0 /\ UInt32.v i < length b)
    (ensures fun h0 _ h1 ->
      modifies (loc_buffer b) h0 h1 /\
      invariant b h1)
```

---
## 28. PROOF DEBUGGING WORKFLOW

### Step 1: Minimize Fuel
```fstar
// Start with minimal fuel
#set-options "--fuel 0 --ifuel 0 --z3rlimit 5"

let my_lemma x =
  // If this fails, SMT needs help
  ()
```

### Step 2: Add Assertions
```fstar
let my_lemma x =
  // Add intermediate facts
  assert (fact1 x);      // Check if SMT knows this
  assert (fact2 x);      // And this
  // Now the final goal should follow
  ()
```

### Step 3: Use Calc
```fstar
let my_lemma x =
  calc (==) {
    lhs x;
    == { lemma1 x }  // Justify each step
    mid1 x;
    == { lemma2 x }
    rhs x;
  }
```

### Step 4: Inspect with Tactics
```fstar
let my_lemma x =
  _ by (
    dump "Before anything";
    // ... try tactics ...
    dump "After tactics";
    smt ()  // Send to SMT
  )
```

### Step 5: Log SMT
```bash
# See what's being sent to Z3
fstar.exe --log_queries --keep_query_captions true MyModule.fst

# Inspect the .smt2 files
```

---
## 29. PERFORMANCE OPTIMIZATION

### Proof Performance
```fstar
// 1. Minimize fuel (most impactful)
#set-options "--fuel 0 --ifuel 0"

// 2. Use SMT patterns on lemmas
val helper : x:nat -> Lemma (P x) [SMTPat (f x)]

// 3. Avoid quantifiers when possible
// Bad: forall x. P x
// Good: Lemma + SMTPat

// 4. Split large proofs
let big_proof x =
  part1 x;
  part2 x;
  part3 x
```

### Extraction Performance
```fstar
// 1. Use inline_for_extraction
[@@inline_for_extraction]
let fast_helper x = x + 1

// 2. Specialize generics
[@@specialize]
let generic_func #t (x:t) = ...

// 3. Mark proof-only code
[@@noextract]
let spec_only x = ...
```

### IDE Performance
```fstar
// 1. Use lax mode for editing
// Check with: VerifyToPosition

// 2. Minimize dependencies
// Avoid: open FStar.All
// Prefer: specific imports

// 3. Use interface files
// Hides implementation details
```

---
## 30. COMMON IDIOMS

### Refinement Coercion
```fstar
// Coerce nat to int
let nat_to_int (x:nat) : int = x

// Coerce with proof
let pos_to_nat (x:pos) : nat =
  assert (x >= 0);  // May be needed
  x
```

### Ghost Unwrapping
```fstar
// In ghost context
let ghost_use (x: erased nat) : GTot nat = reveal x

// In pure context (return erased)
let pure_use (x: erased nat) : nat =
  // Can't reveal in Pure!
  // Must return erased or use tactics
  admit ()
```

### Option Handling
```fstar
// Pattern match
let handle (x: option nat) : nat =
  match x with
  | Some v -> v
  | None -> 0

// With default
let with_default (x: option nat) (d: nat) : nat =
  match x with
  | Some v -> v
  | None -> d

// From FStar.Option
let safe = FStar.Option.dflt 0 x
```

### List Processing
```fstar
// Functional style
let process (xs: list nat) : list nat =
  xs
  |> List.Tot.filter (fun x -> x > 0)
  |> List.Tot.map (fun x -> x + 1)

// With fold
let sum (xs: list nat) : nat =
  List.Tot.fold_left (+) 0 xs
```

---
# END OF F* QUICK REFERENCE
# Full documentation: brrr-lang/fstar_doc.md
