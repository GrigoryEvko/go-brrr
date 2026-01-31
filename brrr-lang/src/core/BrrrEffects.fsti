(**
 * BrrrLang.Core.Effects - Interface
 *
 * Row-Polymorphic Algebraic Effect System for the Brrr-Lang Code IR.
 * Based on brrr_lang_spec_v0.4.tex Part II (Type System), Section 4 (Effects).
 *
 * THEORETICAL FOUNDATIONS:
 *
 *   This module implements a row-polymorphic effect system following
 *   Leijen's design from Koka [Leijen14, Leijen17], combined with
 *   algebraic effect semantics from Plotkin & Power [Plotkin03]
 *   and effect handlers from Plotkin & Pretnar [Plotkin09].
 *
 *   [Leijen14] Leijen. "Koka: Programming with Row Polymorphic Effect Types."
 *              MSFP 2014. Introduces row-polymorphic effects with scoped
 *              effect handlers and effect inference.
 *
 *   [Leijen17] Leijen. "Type Directed Compilation of Row-Typed Algebraic
 *              BrrrEffects." POPL 2017. Evidence-passing translation and
 *              efficient compilation of row-typed effects.
 *
 *   [Plotkin03] Plotkin & Power. "Algebraic Operations and Generic BrrrEffects."
 *               Applied Categorical Structures 2003. Foundational algebraic
 *               treatment of computational effects as operations + equations.
 *
 *   [Plotkin09] Plotkin & Pretnar. "Handlers of Algebraic BrrrEffects." ESOP 2009.
 *               Effect handlers as homomorphisms from free algebraic models.
 *               Establishes correctness criteria for handlers.
 *
 * EFFECT ROWS (Row Polymorphism):
 *
 *   Effect types are represented as ROWS - extensible records of effects.
 *   Following Leijen's design:
 *
 *     effect_row ::= RowEmpty                    -- empty row (pure)
 *                  | RowExt effect_op effect_row -- extend with effect
 *                  | RowVar string               -- row variable (polymorphism)
 *                  | RowVarUnify string string   -- unification constraint
 *
 *   Row variables (RowVar) enable EFFECT POLYMORPHISM without explicit
 *   effect annotations. For example, a map function:
 *
 *     map : forall a b epsilon. (a -> <epsilon> b) -> List a -> <epsilon> List b
 *
 *   The epsilon is a row variable that captures the effects of the function
 *   argument and propagates them to the result.
 *
 *   ROW UNIFICATION occurs during type inference when two row types must
 *   be equal. RowVarUnify tracks constraints between row variables that
 *   must be unified. See SPECIFICATION_ERRATA.md for known issues with
 *   row unification in the presence of recursive types.
 *
 * EFFECT ALGEBRA (Bounded Join-Semilattice):
 *
 *   Effect rows form a bounded join-semilattice with:
 *     - Bottom: RowEmpty (pure - no effects)
 *     - Join:   row_join (union of effect sets)
 *     - Order:  effect_subset (effect subtyping)
 *
 *   Key algebraic properties (proven in BrrrEffects.fst):
 *     - Associativity: row_join (row_join r1 r2) r3 ~ row_join r1 (row_join r2 r3)
 *     - Commutativity: row_join r1 r2 ~ row_join r2 r1  (semantic equality)
 *     - Idempotence:   row_join r r = r
 *     - Identity:      row_join RowEmpty r = r
 *
 *   These properties are CRITICAL for the graded monad structure:
 *     (m >>= f) >>= g = m >>= (fun x -> f x >>= g)
 *   requires associativity of effect combination.
 *
 * ALGEBRAIC EFFECTS:
 *
 *   Each effect_op represents an algebraic operation in the sense of
 *   Plotkin & Power - an operation with a signature (argument type,
 *   continuation type) that can be performed by computations and
 *   handled by effect handlers.
 *
 *   Effect handlers (effect_handler) are HOMOMORPHISMS from free algebraic
 *   models [Plotkin09]. A handler is correct if it preserves the equations
 *   of the effect theory. See handler_clause for operation clauses.
 *
 *   LIMITATIONS (from [Plotkin09], [Sivaramakrishnan21]):
 *     - call/cc is NOT an algebraic effect (not compositional)
 *     - Parallel composition requires BINARY handlers
 *     - C FFI boundaries BLOCK effect propagation
 *
 * EFFECT ABSENCE THEOREMS [Leijen14]:
 *
 *   If an effect is ABSENT from the inferred effect row, the computation
 *   CANNOT exhibit that behavior. This enables:
 *     - Exception-free code: EThrow not in row => no unhandled exceptions
 *     - Termination guarantee: EDiv not in row => computation terminates
 *     - State isolation: ERead/EWrite not in row => referentially transparent
 *
 * MODULE CONTENTS:
 *
 *   1. Location-parameterized effects (ERead(loc), EWrite(loc), EFree(loc))
 *   2. Algebraic effect handlers with perform/handle/resume
 *   3. Effect signatures for declaring effect operations
 *   4. Graded monad structure with return/bind
 *   5. Session channel effects (Honda 1998/2008 session types)
 *   6. Resource effects (acquire/release) with linearity checking
 *   7. Coeffect support (liveness, usage, capabilities per [Petricek14])
 *
 * Following HACL* patterns from Lib.LoopCombinators.fsti and
 * EverParse patterns from GlobalEnv.fst.
 *
 * See also: SPECIFICATION_ERRATA.md for known issues and deviations
 * from the specification.
 *)
module BrrrEffects

(* Z3 configuration for effect algebra proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

open BrrrPrimitives
open BrrrUtils

(** ============================================================================
    ABSTRACT LOCATIONS AND PARAMETERS
    ============================================================================ *)

(** Abstract location for parameterized memory effects.
    Supports both concrete allocation sites and symbolic/polymorphic locations. *)
type abstract_loc =
  | LocConcrete : nat -> abstract_loc              (* Concrete allocation site *)
  | LocAbstract : string -> abstract_loc           (* Abstract/symbolic location *)
  | LocParam    : nat -> abstract_loc              (* Parameter location for polymorphism *)
  | LocUnknown  : abstract_loc                     (* Unknown/any location - aliases all *)

(** Lock identifier for concurrency effects *)
type lock_id = nat

(** Channel identifier for session effects *)
type chan_id = nat

(** I/O source types for parameterized input effects *)
type io_source =
  | IOStdin      : io_source
  | IOEnvVar     : string -> io_source
  | IOFileInput  : string -> io_source
  | IONetworkIn  : io_source
  | IOUserInput  : io_source

(** I/O sink types for parameterized output effects *)
type io_sink =
  | IOStdout     : io_sink
  | IOStderr     : io_sink
  | IOFileOutput : string -> io_sink
  | IONetworkOut : io_sink
  | IODatabase   : string -> io_sink

(** Simple type representation for effect parameters.
    Forward reference to avoid circular dependency with Types.fst. *)
type effect_type =
  | ETUnit   : effect_type
  | ETBool   : effect_type
  | ETInt    : effect_type
  | ETString : effect_type
  | ETChan   : effect_type -> effect_type          (* Chan<T> *)
  | ETRef    : effect_type -> effect_type          (* Ref<T> *)
  | ETFn     : effect_type -> effect_type -> effect_type  (* A -> B *)
  | ETVar    : nat -> effect_type                  (* Type variable *)

(** Resource type for acquire/release effects *)
type resource_type = string

(** ============================================================================
    EFFECT OPERATIONS (Algebraic Effects)
    ============================================================================

    Each effect_op represents an ALGEBRAIC OPERATION in the sense of
    Plotkin & Power [Plotkin03]. An algebraic operation has:
      - An argument type (the value passed to the operation)
      - A return type (the value the operation yields to the continuation)

    Algebraic effects satisfy the key property that effect handlers are
    HOMOMORPHISMS - they preserve the algebraic structure. This is what
    distinguishes algebraic effects from general monads.

    The operations are organized by category:
      - Memory: ERead, EWrite, EAlloc, EFree (location-parameterized)
      - Control: EThrow, ECatch, EPanic, EDiv, EYield, EShift, EAbort
      - I/O: EInput, EOutput, EIO, ENet, EFS, EFileRead, EFileWrite
      - Concurrency: ESpawn, EJoin, ELock, EUnlock, EAtomic
      - Session: ESend, ERecv, ESelect, EBranch (Honda 1998/2008)
      - Resource: EAcquire, ERelease, EUse

    PARAMETERIZATION: Many effects are parameterized by locations, channels,
    or types. This enables precise effect tracking:
      - ERead(loc) reads from specific location loc
      - ESend(ch, T) sends value of type T on channel ch

    Based on synthesis_combined.md Section 6.1 (BrrrMachine.Effects).
*)
type effect_op =
  (* Memory effects - location-parameterized per spec *)
  | ERead      : loc:abstract_loc -> effect_op
  | EWrite     : loc:abstract_loc -> effect_op
  | EAlloc     : effect_op
  | EFree      : loc:abstract_loc -> effect_op

  (* Control effects *)
  | EThrow     : exn_type:string -> effect_op
  | ECatch     : exn_type:string -> effect_op
  | EPanic     : effect_op
  | EAsync     : effect_op
  | EYield     : yield_type:effect_type -> resume_type:effect_type -> effect_op
  | EDiv       : effect_op
  | EShift     : effect_op
  | EAbort     : effect_op

  (* I/O effects - parameterized per spec *)
  | EInput     : source:io_source -> effect_op
  | EOutput    : sink:io_sink -> effect_op
  | EIO        : effect_op
  | ENet       : effect_op
  | EFS        : effect_op
  | EFileRead  : path:string -> effect_op
  | EFileWrite : path:string -> effect_op
  | ERandom    : effect_op
  | EClock     : effect_op

  (* Concurrency effects - parameterized locks *)
  | ESpawn     : effect_op
  | EJoin      : effect_op
  | ELock      : lock_id:lock_id -> effect_op
  | EUnlock    : lock_id:lock_id -> effect_op
  | ERLock     : lock_id:lock_id -> effect_op                  (* sync.RWMutex.RLock() - acquire shared read lock.
                                                                   Go memory model (https://go.dev/ref/mem#locks):
                                                                   "For any call to l.RLock on a sync.RWMutex variable l,
                                                                    there is an n such that the n-th call to l.Unlock
                                                                    is synchronized before the return from l.RLock."
                                                                   Multiple concurrent RLock holders are permitted;
                                                                   only Lock() (exclusive write) blocks them. *)
  | ERUnlock   : lock_id:lock_id -> effect_op                  (* sync.RWMutex.RUnlock() - release shared read lock.
                                                                   Go memory model (https://go.dev/ref/mem#locks):
                                                                   "the matching call to l.RUnlock is synchronized
                                                                    before the return from call n+1 to l.Lock."
                                                                   RUnlock has release semantics: writes made under
                                                                   the read lock become visible to the next write locker. *)
  | ECondWait      : cond_id:nat -> effect_op                  (* sync.Cond.Wait() - atomically unlock mutex and suspend.
                                                                   Go sync package: "Wait atomically unlocks c.L and
                                                                   suspends execution of the calling goroutine. After
                                                                   later resuming execution, Wait locks c.L before
                                                                   returning." Has both release (unlock) and acquire
                                                                   (re-lock) semantics. *)
  | ECondSignal    : cond_id:nat -> effect_op                  (* sync.Cond.Signal() - wake one waiting goroutine.
                                                                   Go sync package: "Signal wakes one goroutine waiting
                                                                   on c, if there is any." The signal itself has release
                                                                   semantics: writes before Signal become visible to the
                                                                   goroutine that wakes from Wait. *)
  | ECondBroadcast : cond_id:nat -> effect_op                  (* sync.Cond.Broadcast() - wake all waiting goroutines.
                                                                   Go sync package: "Broadcast wakes all goroutines
                                                                   waiting on c." Same release semantics as Signal
                                                                   but wakes ALL waiters instead of just one. *)
  | EAtomic    : effect_op
  | EOnce      : once_id:nat -> effect_op                      (* sync.Once execution - Go memory model:
                                                                   completion of f() in once.Do(f) is
                                                                   synchronized-before return of any Do call.
                                                                   Has both acquire and release semantics. *)
  | EWaitGroupAdd  : wg_id:nat -> delta:int -> effect_op       (* sync.WaitGroup.Add(n) - increments internal
                                                                   counter by delta. If counter goes negative,
                                                                   panics per Go spec. delta > 0 typically called
                                                                   before spawning goroutines. *)
  | EWaitGroupDone : wg_id:nat -> effect_op                    (* sync.WaitGroup.Done() - equivalent to Add(-1).
                                                                   Has release semantics: writes in the goroutine
                                                                   are visible after the corresponding Wait returns.
                                                                   Per Go memory model: "a return from any Wait call
                                                                   is synchronized after the return from Add that
                                                                   caused the counter to become zero." *)
  | EWaitGroupWait : wg_id:nat -> effect_op                    (* sync.WaitGroup.Wait() - blocks until counter
                                                                   reaches 0. Has acquire semantics: observes all
                                                                   writes that happened-before each Done() call.
                                                                   Per Go memory model: the return from Wait()
                                                                   synchronizes-after the last Done() call. *)

  (* Session effects - Honda 1998/2008 with full parameters *)
  | ESend      : chan:chan_id -> payload:effect_type -> effect_op
  | ERecv      : chan:chan_id -> payload:effect_type -> effect_op
  | ESelect    : chan:chan_id -> label:string -> effect_op
  | EBranch    : chan:chan_id -> labels:list string -> effect_op
  | EChanCreate: chan:chan_id -> elem:effect_type -> buf_size:nat -> effect_op
  | EChanClose : chan:chan_id -> effect_op
  | EDelegate  : chan:chan_id -> target:chan_id -> effect_op

  (* Finalizer effects - Go runtime.SetFinalizer *)
  | ESetFinalizer : effect_op                                  (* runtime.SetFinalizer(obj, finalizer) - registers
                                                                   finalizer f to run when obj becomes unreachable.
                                                                   Go memory model (https://go.dev/ref/mem#finalizer):
                                                                   "A call to SetFinalizer(x, f) is synchronized before
                                                                    the finalization call f(x)."
                                                                   Has release semantics at registration and acquire
                                                                   semantics at finalization invocation. The finalizer
                                                                   runs in a single goroutine; order among finalizers
                                                                   is unspecified. *)

  (* Resource effects *)
  | EAcquire   : resource:resource_type -> effect_op
  | ERelease   : resource:resource_type -> effect_op
  | EUse       : resource:resource_type -> effect_op

  (* State effects (STRef-style) *)
  | EState     : effect_op
  | ESTRead    : ref_id:nat -> effect_op
  | ESTWrite   : ref_id:nat -> effect_op
  | ESTNew     : effect_op

  (* FFI effects *)
  | EUnsafe    : effect_op
  | EFFI       : effect_op

  (* Legacy unparameterized versions for backwards compatibility *)
  | EReadSimple  : effect_op
  | EWriteSimple : effect_op
  | ELockSimple  : effect_op
  | ENewCh       : effect_op

(** ============================================================================
    EFFECT ROWS (Row-Polymorphic Effect Types)
    ============================================================================

    Effect rows implement Leijen's row-polymorphic effect types [Leijen14].
    A row is an EXTENSIBLE collection of effects with optional tail variable.

    SYNTAX (following Definition 3.9 from brrr_lang_spec_v0.4.tex):

      effect_row ::= <>                    -- empty row (pure computation)
                   | <e | rho>             -- row extension: effect e with tail rho
                   | rho                   -- row variable (for polymorphism)

    EXAMPLES:

      RowEmpty                             -- Pure computation: <>
      RowExt ERead RowEmpty                -- Read effect: <read>
      RowExt EWrite (RowExt ERead RowEmpty)-- State: <write, read>
      RowVar "epsilon"                     -- Effect variable: epsilon
      RowExt EIO (RowVar "epsilon")        -- IO + unknown: <io | epsilon>

    ROW POLYMORPHISM enables functions to be POLYMORPHIC over effects:

      let map f xs = ...
      // Inferred type: forall a b epsilon.
      //   (a -> <epsilon> b) -> List a -> <epsilon> List b

    The row variable epsilon captures whatever effects f has and propagates
    them to the result. This is Leijen's key insight: effect inference
    without explicit annotations.

    ROW UNIFICATION: When type inference requires two rows to be equal,
    row unification generates constraints. RowVarUnify tracks cases where
    two DIFFERENT row variables must unify (they become aliases).

    SUBSUMPTION: Effect rows form a partial order under effect_subset.
    If r1 is a subset of r2, then a computation with effects r1 can be
    used where r2 is expected (effect weakening).

    NOTE: noeq because structural equality is not decidable for rows
    containing variables - semantic equality (row_equiv) must be used
    for rows with variables.
*)
noeq type effect_row =
  | RowEmpty : effect_row
      (** Empty row - represents a PURE computation with no effects.
          This is the BOTTOM element of the effect lattice. *)

  | RowExt   : effect_op -> effect_row -> effect_row
      (** Row extension - adds an effect to an existing row.
          RowExt e r represents <e | r> in row notation.
          Effects are accumulated via extension during composition. *)

  | RowVar   : string -> effect_row
      (** Row variable - enables EFFECT POLYMORPHISM.
          Represents an unknown set of effects to be determined by inference
          or instantiation. Named by string for debugging/pretty-printing. *)

  | RowVarUnify : string -> string -> effect_row
      (** Unification of two row variables - tracks the constraint that
          two variables must represent the same effects. Generated during
          row unification when two different variables meet.
          See SPECIFICATION_ERRATA.md for edge cases. *)

(** Row unification constraint: v1 must equal v2.

    During row unification, when two different row variables meet,
    we generate a constraint requiring them to be equal. This follows
    Leijen's approach to effect inference [Leijen14]:

      Gamma |- e1 : tau1 | rho1    Gamma |- e2 : tau2 | rho2
      ------------------------------------------------------
      Gamma |- (e1; e2) : tau2 | rho1 \/ rho2

    When rho1 and rho2 are different variables, we generate the constraint
    rho1 = rho2 and return their unification.
*)
type row_constraint = {
  rc_var1: string;   (** First row variable *)
  rc_var2: string    (** Second row variable - must equal rc_var1 *)
}

(** Result of row join with accumulated constraints.

    Row join may generate unification constraints when joining rows
    containing different variables. This type bundles the result row
    with any constraints that must be satisfied for the join to be valid.
*)
noeq type row_join_result = {
  rjr_row: effect_row;           (** Resulting joined row *)
  rjr_constraints: list row_constraint  (** Constraints that must hold *)
}

(** Pure effect (empty row) - identity element for join *)
unfold let pure : effect_row = RowEmpty

(** Unit effect type constant *)
unfold let et_unit : effect_type = ETUnit

(** ============================================================================
    EQUALITY PREDICATES
    ============================================================================

    Following HACL-star/EverParse patterns: simple pattern-matching equality functions
    are defined with `unfold let` to make their bodies visible to Z3 during
    normalization. This enables trivial reflexivity/symmetry/transitivity proofs.

    Recursive functions (effect_type_eq, string_list_eq) remain as `val` since
    `unfold` does not work well with recursion.
*)

(** Abstract location equality - unfold for proof automation *)
[@(strict_on_arguments [0; 1])]
unfold
let abstract_loc_eq (l1 l2: abstract_loc) : bool =
  match l1, l2 with
  | LocConcrete n1, LocConcrete n2 -> n1 = n2
  | LocAbstract s1, LocAbstract s2 -> s1 = s2
  | LocParam p1, LocParam p2 -> p1 = p2
  | LocUnknown, LocUnknown -> true
  | _, _ -> false

(** Effect type equality - recursive, kept as val *)
val effect_type_eq : effect_type -> effect_type -> bool

(** String list equality - recursive, kept as val *)
val string_list_eq : list string -> list string -> bool

(** Effect operation equality - unfold for proof automation.
    Handles all parameterized and unparameterized variants. *)
[@(strict_on_arguments [0; 1])]
unfold
let effect_op_eq (e1 e2: effect_op) : bool =
  match e1, e2 with
  (* Memory effects - location-parameterized *)
  | ERead loc1, ERead loc2 -> abstract_loc_eq loc1 loc2
  | EWrite loc1, EWrite loc2 -> abstract_loc_eq loc1 loc2
  | EAlloc, EAlloc -> true
  | EFree loc1, EFree loc2 -> abstract_loc_eq loc1 loc2

  (* Control effects *)
  | EThrow t1, EThrow t2 -> t1 = t2
  | ECatch t1, ECatch t2 -> t1 = t2
  | EPanic, EPanic -> true
  | EAsync, EAsync -> true
  | EYield y1 r1, EYield y2 r2 -> effect_type_eq y1 y2 && effect_type_eq r1 r2
  | EDiv, EDiv -> true
  | EShift, EShift -> true
  | EAbort, EAbort -> true

  (* I/O effects *)
  | EInput s1, EInput s2 -> s1 = s2
  | EOutput s1, EOutput s2 -> s1 = s2
  | EIO, EIO -> true
  | ENet, ENet -> true
  | EFS, EFS -> true
  | EFileRead p1, EFileRead p2 -> p1 = p2
  | EFileWrite p1, EFileWrite p2 -> p1 = p2
  | ERandom, ERandom -> true
  | EClock, EClock -> true

  (* Concurrency effects - lock-parameterized *)
  | ESpawn, ESpawn -> true
  | EJoin, EJoin -> true
  | ELock l1, ELock l2 -> l1 = l2
  | EUnlock l1, EUnlock l2 -> l1 = l2
  | ERLock l1, ERLock l2 -> l1 = l2
  | ERUnlock l1, ERUnlock l2 -> l1 = l2
  | ECondWait c1, ECondWait c2 -> c1 = c2
  | ECondSignal c1, ECondSignal c2 -> c1 = c2
  | ECondBroadcast c1, ECondBroadcast c2 -> c1 = c2
  | EAtomic, EAtomic -> true
  | EOnce o1, EOnce o2 -> o1 = o2
  | EWaitGroupAdd w1 d1, EWaitGroupAdd w2 d2 -> w1 = w2 && d1 = d2
  | EWaitGroupDone w1, EWaitGroupDone w2 -> w1 = w2
  | EWaitGroupWait w1, EWaitGroupWait w2 -> w1 = w2

  (* Session effects - fully parameterized *)
  | ESend c1 t1, ESend c2 t2 -> c1 = c2 && effect_type_eq t1 t2
  | ERecv c1 t1, ERecv c2 t2 -> c1 = c2 && effect_type_eq t1 t2
  | ESelect c1 l1, ESelect c2 l2 -> c1 = c2 && l1 = l2
  | EBranch c1 ls1, EBranch c2 ls2 -> c1 = c2 && string_list_eq ls1 ls2
  | EChanCreate c1 t1 b1, EChanCreate c2 t2 b2 -> c1 = c2 && effect_type_eq t1 t2 && b1 = b2
  | EChanClose c1, EChanClose c2 -> c1 = c2
  | EDelegate c1 t1, EDelegate c2 t2 -> c1 = c2 && t1 = t2

  (* Finalizer effects *)
  | ESetFinalizer, ESetFinalizer -> true

  (* Resource effects *)
  | EAcquire r1, EAcquire r2 -> r1 = r2
  | ERelease r1, ERelease r2 -> r1 = r2
  | EUse r1, EUse r2 -> r1 = r2

  (* State effects *)
  | EState, EState -> true
  | ESTRead r1, ESTRead r2 -> r1 = r2
  | ESTWrite r1, ESTWrite r2 -> r1 = r2
  | ESTNew, ESTNew -> true

  (* FFI effects *)
  | EUnsafe, EUnsafe -> true
  | EFFI, EFFI -> true

  (* Legacy unparameterized *)
  | EReadSimple, EReadSimple -> true
  | EWriteSimple, EWriteSimple -> true
  | ELockSimple, ELockSimple -> true
  | ENewCh, ENewCh -> true

  (* No match *)
  | _, _ -> false

(** Convert effect_type to effect_type (identity, for API consistency) *)
inline_for_extraction noextract
let effect_type_id (t: effect_type) : effect_type = t

(** ============================================================================
    EFFECT ROW OPERATIONS
    ============================================================================ *)

(** Check if effect is in row *)
val has_effect : effect_op -> effect_row -> bool

(** Add effect to row (if not present) *)
val add_effect : effect_op -> effect_row -> effect_row

(** Remove effect from row *)
val remove_effect : effect_op -> effect_row -> effect_row

(** Row join (union of effects) with proper row variable handling.

    Row variable semantics:
    - RowVar represents an unknown set of effects (polymorphism)
    - When joining RowVar v with concrete effects, extend RowVar with those effects
    - When joining two different RowVars, return RowVarUnify to track the constraint
    - When joining the same RowVar with itself, return that RowVar *)
val row_join : effect_row -> effect_row -> effect_row

(** Row join with explicit constraint collection.
    Use this when you need to track all unification constraints. *)
val row_join_constrained : effect_row -> effect_row -> row_join_result

(** Row subset check *)
val row_subset : effect_row -> effect_row -> bool

(** Row equality check: structural equality for effect rows *)
val row_eq : effect_row -> effect_row -> bool

(** Check if effect_row is free of RowVar at all levels *)
val no_row_var : effect_row -> bool

(** Semantic equality for effect rows: same set of effects *)
val row_equiv : effect_row -> effect_row -> prop

(** ============================================================================
    REFLEXIVITY LEMMAS
    ============================================================================ *)

(** abstract_loc_eq is reflexive *)
val abstract_loc_eq_refl : l:abstract_loc ->
  Lemma (abstract_loc_eq l l = true)
        [SMTPat (abstract_loc_eq l l)]

(** effect_type_eq is reflexive *)
val effect_type_eq_refl : t:effect_type ->
  Lemma (effect_type_eq t t = true)
        [SMTPat (effect_type_eq t t)]

(** string_list_eq is reflexive *)
val string_list_eq_refl : l:list string ->
  Lemma (string_list_eq l l = true)

(** effect_op_eq is reflexive *)
val effect_op_eq_refl : e:effect_op ->
  Lemma (effect_op_eq e e = true)
        [SMTPat (effect_op_eq e e)]

(** row_eq is reflexive *)
val row_eq_refl : r:effect_row ->
  Lemma (ensures row_eq r r = true)
        [SMTPat (row_eq r r)]

(** ============================================================================
    SYMMETRY LEMMAS

    Order matches implementation dependency order:
    1. abstract_loc_eq_sym (no deps)
    2. effect_type_eq_sym (recursive, no deps)
    3. string_list_eq_sym (recursive, no deps)
    4. effect_op_eq_sym (needs above three)
    5. row_eq_sym (needs effect_op_eq_sym)
    ============================================================================ *)

(** abstract_loc_eq is symmetric *)
val abstract_loc_eq_sym : l1:abstract_loc -> l2:abstract_loc ->
  Lemma (abstract_loc_eq l1 l2 = abstract_loc_eq l2 l1)

(** effect_type_eq is symmetric *)
val effect_type_eq_sym : t1:effect_type -> t2:effect_type ->
  Lemma (effect_type_eq t1 t2 = effect_type_eq t2 t1)

(** string_list_eq is symmetric *)
val string_list_eq_sym : l1:list string -> l2:list string ->
  Lemma (string_list_eq l1 l2 = string_list_eq l2 l1)

(** effect_op_eq is symmetric *)
val effect_op_eq_sym : e1:effect_op -> e2:effect_op ->
  Lemma (effect_op_eq e1 e2 = effect_op_eq e2 e1)

(** row_eq is symmetric *)
val row_eq_sym : r1:effect_row -> r2:effect_row ->
  Lemma (requires row_eq r1 r2 = true)
        (ensures row_eq r2 r1 = true)

(** ============================================================================
    TRANSITIVITY LEMMAS
    ============================================================================ *)

(** row_eq is transitive *)
val row_eq_trans : r1:effect_row -> r2:effect_row -> r3:effect_row ->
  Lemma (requires row_eq r1 r2 = true /\ row_eq r2 r3 = true)
        (ensures row_eq r1 r3 = true)

(** ============================================================================
    EFFECT SEMILATTICE HELPER LEMMAS
    ============================================================================ *)

(** If r has no RowVar, neither does any suffix *)
val no_row_var_ext : e:effect_op -> rest:effect_row ->
  Lemma (requires no_row_var (RowExt e rest) = true)
        (ensures no_row_var rest = true)

(** has_effect is preserved when extending a row *)
val has_effect_ext : e:effect_op -> e':effect_op -> row:effect_row ->
  Lemma (has_effect e row ==> has_effect e (RowExt e' row))

(** The head of a RowExt is always present *)
val has_effect_head : e:effect_op -> rest:effect_row ->
  Lemma (has_effect e (RowExt e rest) = true)
        [SMTPat (has_effect e (RowExt e rest))]

(** add_effect is no-op when effect already present *)
val add_effect_noop : e:effect_op -> row:effect_row ->
  Lemma (requires has_effect e row = true)
        (ensures add_effect e row == row)

(** has_effect is preserved by add_effect *)
val has_effect_add_effect : e:effect_op -> e':effect_op -> row:effect_row ->
  Lemma (has_effect e row = true ==> has_effect e (add_effect e' row) = true)

(** row_subset is preserved when extending the superset *)
val row_subset_weaken : r1:effect_row -> r2:effect_row -> e:effect_op ->
  Lemma (requires no_row_var r1 = true /\ row_subset r1 r2 = true)
        (ensures row_subset r1 (RowExt e r2) = true)

(** r is a subset of (RowExt e r) for any e *)
val row_subset_ext : r:effect_row -> e:effect_op ->
  Lemma (requires no_row_var r = true)
        (ensures row_subset r (RowExt e r) = true)
        (decreases r)

(** row_subset is reflexive for concrete rows *)
val row_subset_refl : r:effect_row ->
  Lemma (requires no_row_var r = true)
        (ensures row_subset r r = true)

(** row_eq implies row_subset for concrete rows.
    This bridges type_eq (using row_eq) with extended_subtype (using row_subset). *)
val row_eq_implies_subset : r1:effect_row -> r2:effect_row ->
  Lemma (requires row_eq r1 r2 = true /\ no_row_var r1 = true)
        (ensures row_subset r1 r2 = true)

(** row_eq on left composes with row_subset on right.
    Used for function effect transitivity. *)
val row_eq_subset_trans : r1:effect_row -> r2:effect_row -> r3:effect_row ->
  Lemma (requires row_eq r1 r2 = true /\ no_row_var r1 = true /\ row_subset r2 r3 = true)
        (ensures row_subset r1 r3 = true)

(** row_eq preserves no_row_var property *)
val row_eq_preserves_no_row_var : r1:effect_row -> r2:effect_row ->
  Lemma (requires row_eq r1 r2 = true)
        (ensures no_row_var r1 = no_row_var r2)

(** row_subset implies no_row_var on the left *)
val row_subset_implies_no_row_var_left : r1:effect_row -> r2:effect_row ->
  Lemma (requires row_subset r1 r2 = true)
        (ensures no_row_var r1 = true)

(** row_eq preserves has_effect *)
val row_eq_has_effect : e:effect_op -> r2:effect_row -> r3:effect_row ->
  Lemma (requires row_eq r2 r3 = true /\ has_effect e r2 = true)
        (ensures has_effect e r3 = true)

(** row_subset on left composes with row_eq on right *)
val row_subset_eq_trans : r1:effect_row -> r2:effect_row -> r3:effect_row ->
  Lemma (requires row_subset r1 r2 = true /\ row_eq r2 r3 = true)
        (ensures row_subset r1 r3 = true)

(** has_effect respects row_subset *)
val has_effect_subset : e:effect_op -> r2:effect_row -> r3:effect_row ->
  Lemma (requires has_effect e r2 = true /\ row_subset r2 r3 = true)
        (ensures has_effect e r3 = true)

(** row_subset is transitive *)
val row_subset_trans : r1:effect_row -> r2:effect_row -> r3:effect_row ->
  Lemma (requires row_subset r1 r2 = true /\ row_subset r2 r3 = true)
        (ensures row_subset r1 r3 = true)

(** effect_op_eq is a congruence for has_effect *)
val has_effect_op_eq_cong : e1:effect_op -> e2:effect_op -> r:effect_row ->
  Lemma (requires effect_op_eq e1 e2 = true)
        (ensures has_effect e1 r = has_effect e2 r)

(** row_subset respects row_eq on the left (congruence) *)
val row_subset_cong_left : r1:effect_row -> r2:effect_row -> r:effect_row ->
  Lemma (requires row_eq r1 r2 = true)
        (ensures row_subset r1 r = row_subset r2 r)

(** ============================================================================
    EFFECT SEMILATTICE LAWS
    ============================================================================ *)

(** row_join preserves effects from second argument *)
val has_effect_row_join_r : e:effect_op -> r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ has_effect e r2 = true)
        (ensures has_effect e (row_join r1 r2) = true)

(** add_effect e always ensures e is present *)
val has_effect_add_effect_same : e:effect_op -> row:effect_row ->
  Lemma (has_effect e (add_effect e row) = true)

(** row_join preserves effects from first argument *)
val has_effect_row_join_l : e:effect_op -> r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ has_effect e r1 = true)
        (ensures has_effect e (row_join r1 r2) = true)

(** row_join doesn't introduce new effects *)
val row_join_no_new_effects : e:effect_op -> r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ has_effect e r1 = false /\ has_effect e r2 = false)
        (ensures has_effect e (row_join r1 r2) = false)

(** Absorption: row_join r1 r2 == r2 when r1 is subset of r2 *)
val row_join_absorb : r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ row_subset r1 r2 = true)
        (ensures row_join r1 r2 == r2)

(** Join is commutative (semantic equality).
    Note: Structural equality (==) is NOT provable because row_join produces
    different structures depending on argument order. *)
val row_join_comm : r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ no_row_var r2 = true)
        (ensures row_equiv (row_join r1 r2) (row_join r2 r1))

(** Pure is identity for join *)
val row_join_pure : r:effect_row ->
  Lemma (row_join pure r == r)
        [SMTPat (row_join pure r)]

(** Join is idempotent *)
val row_join_idem : r:effect_row ->
  Lemma (requires no_row_var r = true)
        (ensures row_join r r == r)

(** has_effect distributes over row_join *)
val has_effect_row_join_distrib_l : e:effect_op -> r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ no_row_var r2 = true)
        (ensures has_effect e (row_join r1 r2) = (has_effect e r1 || has_effect e r2))

(** Row join is associative (semantic equality).
    CRITICAL for graded monad associativity:
      (m >>= f) >>= g = m >>= (fun x -> f x >>= g)
    requires that effect combination is associative. *)
val row_join_assoc : r1:effect_row -> r2:effect_row -> r3:effect_row ->
  Lemma (requires no_row_var r1 = true /\ no_row_var r2 = true /\ no_row_var r3 = true)
        (ensures row_equiv (row_join r1 (row_join r2 r3)) (row_join (row_join r1 r2) r3))

(** Effect subtyping respects row_join (covariance).
    Critical for effect polymorphism. *)
val effect_sub_join_compat : r1:effect_row -> r1':effect_row ->
                             r2:effect_row -> r2':effect_row ->
  Lemma (requires no_row_var r1 = true /\ no_row_var r1' = true /\
                  no_row_var r2 = true /\ no_row_var r2' = true /\
                  row_subset r1 r1' = true /\ row_subset r2 r2' = true)
        (ensures row_subset (row_join r1 r2) (row_join r1' r2') = true)

(** ============================================================================
    COMMON EFFECT COMBINATIONS
    ============================================================================ *)

(** Unparameterized read effect (any location) *)
unfold let eff_read_any : effect_row =
  RowExt (ERead LocUnknown) RowEmpty

(** Unparameterized write effect (any location) *)
unfold let eff_write_any : effect_row =
  RowExt (EWrite LocUnknown) RowEmpty

(** State effect: Read + Write (any location) *)
unfold let eff_state : effect_row =
  RowExt (ERead LocUnknown) (RowExt (EWrite LocUnknown) RowEmpty)

(** IO effect: all I/O *)
unfold let eff_io : effect_row =
  RowExt EIO (RowExt ENet (RowExt EFS RowEmpty))

(** Exception effect (generic) *)
unfold let eff_exn : effect_row =
  RowExt (EThrow "Exception") RowEmpty

(** Panic effect *)
unfold let eff_panic : effect_row = RowExt EPanic RowEmpty

(** Async effect *)
unfold let eff_async : effect_row = RowExt EAsync RowEmpty

(** Divergence effect *)
unfold let eff_div : effect_row = RowExt EDiv RowEmpty

(** Random effect *)
unfold let eff_random : effect_row = RowExt ERandom RowEmpty

(** Clock effect *)
unfold let eff_clock : effect_row = RowExt EClock RowEmpty

(** Atomic effect *)
unfold let eff_atomic : effect_row = RowExt EAtomic RowEmpty

(** Total effect (everything) - conservative approximation *)
unfold let eff_total : effect_row =
  RowExt EDiv (RowExt EUnsafe (RowExt EIO (RowExt EPanic eff_state)))

(** Spawn effect *)
unfold let eff_spawn : effect_row = RowExt ESpawn RowEmpty

(** Join effect *)
unfold let eff_join : effect_row = RowExt EJoin RowEmpty

(** Once effect (sync.Once - parameterized by once_id) *)
inline_for_extraction noextract
let eff_once (oid: nat) : effect_row = RowExt (EOnce oid) RowEmpty

(** WaitGroup Add effect (sync.WaitGroup.Add - parameterized by wg_id and delta) *)
inline_for_extraction noextract
let eff_wg_add (wid: nat) (delta: int) : effect_row = RowExt (EWaitGroupAdd wid delta) RowEmpty

(** WaitGroup Done effect (sync.WaitGroup.Done - parameterized by wg_id) *)
inline_for_extraction noextract
let eff_wg_done (wid: nat) : effect_row = RowExt (EWaitGroupDone wid) RowEmpty

(** WaitGroup Wait effect (sync.WaitGroup.Wait - parameterized by wg_id) *)
inline_for_extraction noextract
let eff_wg_wait (wid: nat) : effect_row = RowExt (EWaitGroupWait wid) RowEmpty

(** WaitGroup combined effect: Add + Done + Wait for a specific WaitGroup instance *)
inline_for_extraction noextract
let eff_wg (wid: nat) : effect_row =
  RowExt (EWaitGroupAdd wid 1) (RowExt (EWaitGroupDone wid) (RowExt (EWaitGroupWait wid) RowEmpty))

(** Legacy session effects for backwards compatibility *)
unfold let eff_session : effect_row =
  RowExt ENewCh (RowExt EReadSimple (RowExt EWriteSimple RowEmpty))

unfold let eff_send : effect_row = RowExt EReadSimple RowEmpty
unfold let eff_recv : effect_row = RowExt EWriteSimple RowEmpty
unfold let eff_new_channel : effect_row = RowExt ENewCh RowEmpty

(** State effect for a specific location *)
inline_for_extraction noextract
val eff_state_loc : abstract_loc -> effect_row

(** Exception effect for specific type *)
inline_for_extraction noextract
val eff_throw : string -> effect_row

(** Session effects for a specific channel *)
inline_for_extraction noextract
val eff_session_chan : chan_id -> effect_type -> effect_row

(** Send effect for specific channel *)
inline_for_extraction noextract
val eff_send_chan : chan_id -> effect_type -> effect_row

(** Receive effect for specific channel *)
inline_for_extraction noextract
val eff_recv_chan : chan_id -> effect_type -> effect_row

(** Channel creation effect *)
inline_for_extraction noextract
val eff_chan_create : chan_id -> effect_type -> nat -> effect_row

(** Channel close effect *)
inline_for_extraction noextract
val eff_chan_close : chan_id -> effect_row

(** Delegate effect *)
inline_for_extraction noextract
val eff_delegate : chan_id -> chan_id -> effect_row

(** Lock effect for specific lock *)
inline_for_extraction noextract
val eff_lock : lock_id -> effect_row

(** Unlock effect for specific lock *)
inline_for_extraction noextract
val eff_unlock : lock_id -> effect_row

(** Read-lock effect for specific RWMutex *)
inline_for_extraction noextract
val eff_rlock : lock_id -> effect_row

(** Read-unlock effect for specific RWMutex *)
inline_for_extraction noextract
val eff_runlock : lock_id -> effect_row

(** Condition variable wait effect *)
inline_for_extraction noextract
val eff_cond_wait : nat -> effect_row

(** Condition variable signal effect *)
inline_for_extraction noextract
val eff_cond_signal : nat -> effect_row

(** Condition variable broadcast effect *)
inline_for_extraction noextract
val eff_cond_broadcast : nat -> effect_row

(** Resource acquire/release effects *)
inline_for_extraction noextract
val eff_resource : resource_type -> effect_row

(** ============================================================================
    EFFECT SIGNATURES
    ============================================================================ *)

(** Continuation linearity - one-shot vs multi-shot *)
type linearity =
  | OneShot    : linearity    (* Continuation can be invoked exactly once *)
  | MultiShot  : linearity    (* Continuation can be invoked multiple times *)

(** Operation signature: declares a single effect operation *)
noeq type op_sig = {
  op_name    : string;            (* Operation name *)
  arg_type   : effect_type;       (* Argument type *)
  ret_type   : effect_type        (* Return type *)
}

(** Effect signature: declares a named effect with its operations.
    Example: effect State(S) { get : () -> S; put : S -> () } *)
noeq type effect_sig = {
  eff_name    : string;           (* Effect name *)
  eff_params  : list effect_type; (* Type parameters *)
  operations  : list op_sig       (* Operations this effect provides *)
}

(** ============================================================================
    EFFECT HANDLERS (Plotkin-Pretnar Style)
    ============================================================================

    Effect handlers provide a structured way to give semantics to algebraic
    effects. Following Plotkin & Pretnar [Plotkin09], a handler is a
    HOMOMORPHISM from the free algebra of effects to some target model.

    SYNTAX (informal):

      handle computation with {
        return x -> body_return
        op1(arg, k) -> body1    -- k is the continuation
        op2(arg, k) -> body2
        ...
      }

    SEMANTICS:
      - When computation returns normally, execute body_return
      - When computation performs op1(v), capture the continuation k
        and execute body1 with arg=v

    HANDLER CORRECTNESS [Plotkin09]:
    A handler is correct if it preserves the equations of the effect theory.
    For example, if the theory has equation `get; put x = put x; get`,
    the handler must preserve this equivalence.

    DEEP vs SHALLOW HANDLERS:
      - Deep: Handler recursively applies to the continuation
      - Shallow: Handler applies once; continuation runs unhandled

    CONTINUATION LINEARITY:
      - OneShot: Continuation can be invoked at most once (resource-safe)
      - MultiShot: Continuation can be invoked multiple times (backtracking)

    LIMITATIONS [Plotkin09, Sivaramakrishnan21]:
      - call/cc cannot be expressed as an algebraic effect
      - Parallel composition (par) requires binary handlers
      - C FFI boundaries block effect propagation
*)

(** Handler clause: how to handle one effect operation.

    When the handled computation performs op, we:
      1. Bind the argument to hc_params
      2. Bind the continuation to hc_kont
      3. Execute the body at hc_body_ref
*)
noeq type handler_clause = {
  hc_op          : effect_op;             (** Which operation this handles *)
  hc_params      : list string;           (** Parameter names for op arguments *)
  hc_kont        : string;                (** Name for the continuation variable *)
  hc_kont_linear : linearity;             (** Can continuation be used multiple times? *)
  hc_body_ref    : nat                    (** Reference to handler body in AST *)
}

(** Effect handler - handles a set of effects with clauses for each operation.

    The handler intercepts effects from eh_handled_effects.
    Each effect operation has a corresponding clause in eh_op_clauses.
    The return clause handles normal termination.
*)
noeq type effect_handler = {
  eh_handled_effects : effect_row;          (** Effects being handled (removed from result) *)
  eh_return_var      : string;              (** Variable name in return clause *)
  eh_return_body_ref : nat;                 (** Reference to return body *)
  eh_op_clauses      : list handler_clause; (** Operation handler clauses *)
  eh_finally_ref     : option nat           (** Optional finally clause *)
}

(** Shallow vs deep handlers.

    DEEP handlers (default): The handler recursively wraps the continuation.
    When the continuation performs an effect, it's also handled.

    SHALLOW handlers: The handler applies only once. When the continuation
    is invoked, it runs without the handler installed.
*)
type handler_depth =
  | ShallowHandler : handler_depth  (** Handler applies once *)
  | DeepHandler    : handler_depth  (** Handler wraps continuation recursively *)

(** Extended handler with depth information *)
noeq type extended_handler = {
  eh_handler : effect_handler;
  eh_depth   : handler_depth
}

(** ============================================================================
    FREE MONAD ENCODING
    ============================================================================ *)

(** Free monad over an effect signature.
    Uses List.Tot.memP (propositional membership) since op_sig is noeq
    and doesn't have decidable equality. *)
noeq type free (eff: effect_sig) (a: Type) =
  | FreePure   : value:a -> free eff a
  | FreeImpure : op:op_sig{List.Tot.memP op eff.operations}
               -> arg:effect_type
               -> cont:(effect_type -> free eff a)
               -> free eff a

(** Return for free monad *)
val free_return : #eff:effect_sig -> #a:Type -> a -> free eff a

(** Bind for free monad *)
val free_bind : #eff:effect_sig -> #a:Type -> #b:Type ->
  free eff a -> (a -> free eff b) -> free eff b

(** Perform an operation.
    Uses memP for propositional membership. *)
val free_perform : #eff:effect_sig -> #a:Type ->
  op:op_sig{List.Tot.memP op eff.operations} -> effect_type -> free eff effect_type

(** ============================================================================
    LEGACY EFFECT HANDLERS
    ============================================================================ *)

noeq type handler_clause_legacy = {
  op     : effect_op;
  params : list string;
  kont   : string;
  body   : unit
}

noeq type effect_handler_legacy = {
  handled_effects : effect_row;
  return_clause   : string & unit;
  op_clauses      : list handler_clause_legacy
}

(** ============================================================================
    EFFECT POLYMORPHISM
    ============================================================================ *)

(** Effect scheme: forall epsilon. tau[epsilon] *)
noeq type effect_scheme = {
  vars : list string;      (* Bound effect variables *)
  row  : effect_row        (* The effect row - may reference vars *)
}

(** Monomorphic effect *)
val mono_effect : effect_row -> effect_scheme

(** Substitute effect variable *)
val subst_effect_var : string -> effect_row -> effect_row -> effect_row

(** Instantiate effect scheme *)
val instantiate_effect : effect_scheme -> list effect_row -> option effect_row

(** ============================================================================
    GRADED MONAD STRUCTURE
    ============================================================================

    Effect rows form a GRADED MONAD (also called indexed or parametric monad).
    This is the computational interpretation of Moggi's monadic semantics
    [Moggi91] extended with effect indices.

    A graded monad is a family of types M(e, a) indexed by:
      - e : effect_row (the effect index, a monoid)
      - a : Type (the result type)

    With operations:
      - return : a -> M(pure, a)           -- pure values have no effects
      - bind : M(e1, a) -> (a -> M(e2, b)) -> M(e1 + e2, b)

    The effect indices combine via row_join (the monoid operation).
    This gives us the GRADED MONAD LAWS:

      LEFT IDENTITY:  return x >>= f  =  f x
                      (effects: pure + e = e)

      RIGHT IDENTITY: m >>= return  =  m
                      (effects: e + pure = e)

      ASSOCIATIVITY:  (m >>= f) >>= g  =  m >>= (x -> f x >>= g)
                      (effects: (e1 + e2) + e3 = e1 + (e2 + e3))

    The associativity law depends on row_join_assoc (proven in BrrrEffects.fst).

    REFERENCE: Definition 1.7 in brrr_lang_spec_v0.4.tex defines the
    graded monad structure for Brrr-Lang computations.
*)

(** Computation type indexed by effect row.

    comp a eff represents a computation that:
      - May perform effects in eff
      - Returns a value of type a (if it terminates)

    The run field is a thunk that, when forced, executes the computation.
    The eff index is a PHANTOM type - it exists only for type checking,
    not at runtime.
*)
noeq type comp (a: Type) (eff: effect_row) =
  | MkComp : run:(unit -> a) -> comp a eff

(** Return: lift a pure value into a computation with no effects.

    return x produces a computation that immediately yields x
    without performing any effects. This is the unit of the monad.
*)
val comp_return : #a:Type -> a -> comp a pure

(** Bind: sequence two computations, combining their effects.

    m >>= f first runs m (with effects e1), then passes its result
    to f, which produces another computation (with effects e2).
    The combined computation has effects (row_join e1 e2).

    This is the core of effect sequencing in the graded monad.
*)
val comp_bind : #a:Type -> #b:Type -> #e1:effect_row -> #e2:effect_row ->
  comp a e1 -> (a -> comp b e2) -> comp b (row_join e1 e2)

(** Map: apply a function to the result *)
val comp_map : #a:Type -> #b:Type -> #eff:effect_row ->
  (a -> b) -> comp a eff -> comp b eff

(** Lift: embed a computation with fewer effects into one with more *)
val comp_lift : #a:Type -> #e1:effect_row -> #e2:effect_row ->
  comp a e1 -> comp a (row_join e1 e2)

(** Left identity: return a >>= f = f a *)
val comp_left_identity : #a:Type -> #b:Type -> #e:effect_row -> x:a -> f:(a -> comp b e) ->
  Lemma (requires no_row_var e = true)
        (ensures (match comp_bind (comp_return x) f, f x with
                  | MkComp run1, MkComp run2 -> run1 () == run2 ()))

(** Right identity: m >>= return = m *)
val comp_right_identity : #a:Type -> #e:effect_row -> m:comp a e ->
  Lemma (requires no_row_var e = true)
        (ensures (match comp_bind m comp_return, m with
                  | MkComp run1, MkComp run2 -> run1 () == run2 ()))

(** ============================================================================
    EFFECT SIGNATURE FOR FUNCTION TYPES
    ============================================================================ *)

(** Complete effect signature for function analysis *)
noeq type func_effect_sig = {
  fes_effects     : effect_row;
  fes_may_read    : bool;
  fes_may_write   : bool;
  fes_may_alloc   : bool;
  fes_may_free    : bool;
  fes_may_throw   : bool;
  fes_may_panic   : bool;
  fes_may_diverge : bool;
  fes_may_io      : bool;
  fes_may_spawn   : bool;
  fes_may_send    : bool;
  fes_may_recv    : bool;
  fes_may_create_chan : bool;
  fes_may_close_chan  : bool;
  fes_may_select  : bool;
  fes_may_branch  : bool;
  fes_may_delegate: bool;
  fes_channel_types : list (nat & effect_type);
  fes_is_pure     : bool
}

(** Empty/pure effect signature *)
val empty_func_effect_sig : func_effect_sig

(** Derive flags from effect row *)
val derive_effect_flags : effect_row -> func_effect_sig

(** ============================================================================
    EFFECT EVENTS AND TRACES
    ============================================================================ *)

(** Effect event: a single effect occurrence at runtime *)
noeq type effect_event = {
  ee_kind      : effect_op;
  ee_location  : nat;
  ee_timestamp : nat;
  ee_thread    : option nat
}

(** Effect trace: sequence of effect events *)
type effect_trace = list effect_event

(** Effect violations detected from traces *)
noeq type effect_violation =
  | UseAfterFree   : loc:abstract_loc -> free_site:nat -> use_site:nat -> effect_violation
  | DoubleFree     : loc:abstract_loc -> first_free:nat -> second_free:nat -> effect_violation
  | DataRace       : loc:abstract_loc -> access1:effect_event -> access2:effect_event -> effect_violation
  | Deadlock       : locks:list nat -> threads:list nat -> effect_violation
  | ResourceLeak   : resource:resource_type -> acquire_site:nat -> effect_violation
  | UnhandledEffect: eff:effect_op -> site:nat -> effect_violation

(** ============================================================================
    EFFECT MASKING
    ============================================================================ *)

(** An effect mask hides certain effects from the caller's view *)
noeq type effect_mask = {
  visible : effect_row;
  hidden  : effect_row
}

(** Create mask that hides some effects *)
val mask_effects : effect_row -> effect_row -> effect_mask

(** ============================================================================
    COEFFECT INTERFACE
    ============================================================================ *)

(** Coeffect algebra operations - interface for Brrr-Machine *)
noeq type coeffect_ops (c: Type) = {
  co_zero  : c;
  co_one   : c;
  co_plus  : c -> c -> c;
  co_times : c -> c -> c;
  co_meet  : c -> c -> c
}

(** Liveness coeffect *)
type liveness = | LDead | LLive

val liveness_ops : coeffect_ops liveness

(** Usage coeffect *)
type usage_bound =
  | UZero    : usage_bound
  | UOne     : usage_bound
  | UBounded : n:nat -> usage_bound
  | UMany    : usage_bound

val usage_plus : usage_bound -> usage_bound -> usage_bound

val usage_ops : coeffect_ops usage_bound

(** Capability coeffect *)
type capability =
  | CapNetwork   : capability
  | CapFileRead  : capability
  | CapFileWrite : capability
  | CapGPS       : capability
  | CapCamera    : capability
  | CapMicrophone: capability
  | CapCustom    : string -> capability

type capability_set = list capability

val cap_set_empty : capability_set

val cap_set_union : capability_set -> capability_set -> capability_set

val capability_ops : coeffect_ops capability_set

(** Full type judgment with effects and coeffects *)
noeq type full_type_judgment = {
  ftj_context    : list (string & effect_type);
  ftj_coeffects  : capability_set;
  ftj_effects    : effect_row;
  ftj_result_type: effect_type
}

(** ============================================================================
    CHANNEL LINEARITY
    ============================================================================ *)

(** Channel state for linearity checking *)
type channel_state =
  | ChanOpen   : elem_type:effect_type -> buffer_size:nat -> channel_state
  | ChanClosed : channel_state

(** Channel context *)
type channel_context = list (chan_id & channel_state)

(** Check channel linearity *)
val check_channel_effect : channel_context -> effect_op -> option channel_context

(** ============================================================================
    WAITGROUP STATE MODEL
    ============================================================================

    Models Go's sync.WaitGroup synchronization primitive.

    INVARIANTS (from Go spec - pkg/sync/#WaitGroup):
      - Counter must never go negative (panic if it does)
      - Add with positive delta must happen before Wait
      - Done() is equivalent to Add(-1)
      - Wait blocks until counter reaches 0

    MEMORY MODEL (from Go memory model):
      - "For any call to wg.Add(n) with n > 0 that occurs when the counter
         is zero, if there is a concurrent wg.Wait, that Add is
         synchronized-before that Wait."
      - "The return from Wait is synchronized after the counter reaching
         zero, which happens after all Done calls complete."
      - Effectively: Done() has release semantics, Wait() has acquire semantics.
        All writes before Done() are visible after Wait() returns.
*)

(** WaitGroup identifier *)
type wg_id = nat

(** WaitGroup state - tracks the internal counter value *)
type wg_state =
  | WgActive  : counter:nat -> wg_state    (* Counter >= 0, active *)
  | WgPanicked : wg_state                  (* Counter went negative - panic *)

(** WaitGroup context: maps wg_id to state *)
type wg_context = list (wg_id & wg_state)

(** Apply WaitGroup Add operation to context.
    Returns None if WaitGroup not found or counter would go negative. *)
val wg_apply_add : wg_context -> wg_id -> int -> option wg_context

(** Apply WaitGroup Done operation to context (= Add(-1)).
    Returns None if WaitGroup not found or counter would go negative. *)
val wg_apply_done : wg_context -> wg_id -> option wg_context

(** Check if WaitGroup counter is zero (Wait would return immediately).
    Returns None if WaitGroup not found. *)
val wg_is_zero : wg_context -> wg_id -> option bool

(** Create a new WaitGroup in the context with counter = 0 *)
val wg_create : wg_context -> wg_id -> wg_context

(** Check WaitGroup effect validity against context *)
val check_wg_effect : wg_context -> effect_op -> option wg_context

(** ============================================================================
    HAPPENS-BEFORE RELATION
    ============================================================================ *)

(** Check if effect has release semantics *)
val is_release_effect : effect_event -> bool

(** Check if effect has acquire semantics *)
val is_acquire_effect : effect_event -> bool

(** Check if two events synchronize *)
val effects_synchronize : effect_event -> effect_event -> bool

(** Happens-before relation *)
val happens_before : effect_event -> effect_event -> bool

(** ============================================================================
    EFFECT COMMUTATIVITY
    ============================================================================ *)

(** Extract channel ID from effect operation *)
val get_effect_channel : effect_op -> option chan_id

(** Extract lock ID from effect operation *)
val get_effect_lock : effect_op -> option lock_id

(** Extract condition variable ID from effect operation *)
val get_effect_cond : effect_op -> option nat

(** Extract location from effect operation *)
val get_effect_location : effect_op -> option abstract_loc

(** Extract resource from effect operation *)
val get_effect_resource : effect_op -> option resource_type

(** Effect commutativity: two effects commute if on disjoint resources.
    Critical for program transformation and parallelization. *)
val effects_commute : effect_op -> effect_op -> bool

(** Effect commutativity is symmetric *)
val effects_commute_sym : e1:effect_op -> e2:effect_op ->
  Lemma (effects_commute e1 e2 = effects_commute e2 e1)

(** Row effects commutativity *)
val row_effects_commute : effect_row -> effect_row -> bool

(** Check if effect commutes with all in row *)
val row_effect_commutes_with_all : effect_op -> effect_row -> bool

(** ============================================================================
    SESSION TYPE INTEGRATION
    ============================================================================ *)

(** Convert effect_type to string *)
val effect_type_to_string : effect_type -> string

(** Session state for effect-level tracking.
    noeq because it contains recursive references. *)
noeq type session_state =
  | SendState   : payload:effect_type -> next:session_state -> session_state
  | RecvState   : payload:effect_type -> next:session_state -> session_state
  | SelectState : branches:list session_state -> session_state
  | BranchState : branches:list session_state -> session_state
  | EndState    : session_state
  | RecState    : var:nat -> body:session_state -> session_state
  | VarState    : var:nat -> session_state

(** Dual of session state *)
val dual_state : s:session_state -> Tot session_state (decreases s)

(** Session duality is involutive: dual(dual(s)) = s.
    Fundamental to session type theory (Honda 1998/2008). *)
val dual_state_involutive : s:session_state ->
  Lemma (dual_state (dual_state s) == s)
        [SMTPat (dual_state (dual_state s))]

(** Check if two session states are dual *)
val are_dual_states : s1:session_state -> s2:session_state -> Tot bool (decreases s1)

val are_dual_state_lists : l1:list session_state -> l2:list session_state -> Tot bool (decreases l1)

(** Session-aware channel context *)
noeq type session_channel_ctx = {
  scc_basic : channel_context;
  scc_sessions : list (chan_id & session_state)
}

(** Empty session channel context *)
val empty_session_ctx : session_channel_ctx

(** Lookup session state for a channel *)
val lookup_session_state : chan_id -> session_channel_ctx -> option session_state

(** Update session state for a channel *)
val update_session_state : chan_id -> session_state -> session_channel_ctx -> session_channel_ctx

(** Advance session state after send *)
val advance_session_send : chan_id -> effect_type -> session_channel_ctx -> option session_channel_ctx

(** Advance session state after receive *)
val advance_session_recv : chan_id -> effect_type -> session_channel_ctx -> option session_channel_ctx

(** Advance session state after select *)
val advance_session_select : chan_id -> nat -> session_channel_ctx -> option session_channel_ctx

(** Check session state after branch *)
val check_session_branch : chan_id -> session_channel_ctx -> option (list session_state)

(** Check if session effect is valid according to session context *)
val check_session_effect : session_channel_ctx -> effect_op -> option session_channel_ctx
