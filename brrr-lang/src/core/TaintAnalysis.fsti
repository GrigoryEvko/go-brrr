(**
 * BrrrLang.Core.TaintAnalysis Interface
 *
 * Public interface for the taint analysis lattice.
 * Exposes abstract types and operations for tracking untrusted data flow.
 *
 * This interface provides:
 *   - Taint kinds for vulnerability categorization
 *   - Taint status type with lattice operations (join, meet, leq)
 *   - Lattice law lemmas (commutativity, associativity, idempotence, absorption)
 *   - Source/Sink/Sanitizer primitives for taint tracking
 *
 * Soundness properties are proven in the implementation (TaintAnalysis.fst).
 *)
module TaintAnalysis

open FStar.List.Tot

(** ============================================================================
    TAINT KINDS
    ============================================================================

    Taint kinds categorize the type of security vulnerability.
    ============================================================================ *)

(** Taint kind for vulnerability categorization *)
type taint_kind =
  | TaintSQLi          : taint_kind
  | TaintXSS           : taint_kind
  | TaintCMDi          : taint_kind
  | TaintPathTraversal : taint_kind
  | TaintSSRF          : taint_kind

(** Taint kind equality *)
val taint_kind_eq : taint_kind -> taint_kind -> bool

(** taint_kind_eq is reflexive *)
val taint_kind_eq_refl : k:taint_kind ->
    Lemma (ensures taint_kind_eq k k = true)
          [SMTPat (taint_kind_eq k k)]

(** taint_kind_eq is symmetric *)
val taint_kind_eq_sym : k1:taint_kind -> k2:taint_kind ->
    Lemma (requires taint_kind_eq k1 k2 = true)
          (ensures taint_kind_eq k2 k1 = true)

(** taint_kind_eq implies Leibniz equality *)
val taint_kind_eq_implies_eq : k1:taint_kind -> k2:taint_kind ->
    Lemma (requires taint_kind_eq k1 k2 = true)
          (ensures k1 = k2)

(** ============================================================================
    TAINT STATUS
    ============================================================================

    The taint status of a value indicates whether it contains untrusted data.
    ============================================================================ *)

(** Taint status - tracks whether data is tainted and with what kinds *)
type taint_status =
  | Untainted : taint_status
  | Tainted   : list taint_kind -> taint_status

(** Check if taint status is untainted *)
val is_untainted : taint_status -> bool

(** Normalize taint status (empty Tainted becomes Untainted) *)
val normalize_taint : taint_status -> taint_status

(** Check if taint status contains a specific kind *)
val taint_contains : taint_status -> taint_kind -> bool

(** ============================================================================
    TAINT STATUS EQUALITY
    ============================================================================ *)

(** Taint status equality (semantic, compares taint kind sets) *)
val taint_status_eq : taint_status -> taint_status -> bool

(** taint_status_eq is reflexive *)
val taint_status_eq_refl : t:taint_status ->
    Lemma (ensures taint_status_eq t t = true)
          [SMTPat (taint_status_eq t t)]

(** ============================================================================
    TAINT LATTICE OPERATIONS
    ============================================================================

    The taint status forms a bounded lattice:
    - Bottom: Untainted
    - Top: Tainted [all kinds]
    - Join: union of taint kinds (least upper bound)
    - Meet: intersection of taint kinds (greatest lower bound)
    ============================================================================ *)

(**
 * Join two taint statuses (least upper bound).
 * Result is tainted with union of all taint kinds from both operands.
 *)
val taint_join : taint_status -> taint_status -> taint_status

(** ============================================================================
    TAINT JOIN PROPERTIES
    ============================================================================ *)

(** Untainted is the identity element for join (left) *)
val taint_join_untainted_left : t:taint_status ->
    Lemma (ensures taint_join Untainted t = t)
          [SMTPat (taint_join Untainted t)]

(** Untainted is the identity element for join (right) *)
val taint_join_untainted_right : t:taint_status ->
    Lemma (ensures taint_join t Untainted = t)
          [SMTPat (taint_join t Untainted)]

(** taint_join is commutative (in terms of taint_contains) *)
val taint_join_comm_contains : t1:taint_status -> t2:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t1 t2) k = taint_contains (taint_join t2 t1) k)
          [SMTPat (taint_contains (taint_join t1 t2) k); SMTPat (taint_contains (taint_join t2 t1) k)]

(** taint_join is associative (in terms of taint_contains) *)
val taint_join_assoc_contains : t1:taint_status -> t2:taint_status -> t3:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join (taint_join t1 t2) t3) k =
                   taint_contains (taint_join t1 (taint_join t2 t3)) k)

(** taint_join is idempotent (in terms of taint_contains) *)
val taint_join_idem_contains : t:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t t) k = taint_contains t k)
          [SMTPat (taint_contains (taint_join t t) k)]

(**
 * Meet of two taint statuses (greatest lower bound).
 * Result is tainted with intersection of taint kinds from both operands.
 *)
val taint_meet : taint_status -> taint_status -> taint_status

(** ============================================================================
    TAINT MEET PROPERTIES
    ============================================================================ *)

(** taint_meet is commutative (in terms of taint_contains) *)
val taint_meet_comm_contains : t1:taint_status -> t2:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t1 t2) k = taint_contains (taint_meet t2 t1) k)

(** taint_meet is idempotent (in terms of taint_contains) *)
val taint_meet_idem_contains : t:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t t) k = taint_contains t k)
          [SMTPat (taint_contains (taint_meet t t) k)]

(** ============================================================================
    LATTICE IDEMPOTENCE (Structural)
    ============================================================================ *)

(** taint_join is idempotent (structural) *)
val taint_join_idempotent : t:taint_status ->
    Lemma (ensures taint_status_eq (taint_join t t) t = true)
          [SMTPat (taint_join t t)]

(** taint_meet is idempotent (structural) *)
val taint_meet_idempotent : t:taint_status ->
    Lemma (ensures taint_status_eq (taint_meet t t) t = true)
          [SMTPat (taint_meet t t)]

(** ============================================================================
    ABSORPTION LAWS
    ============================================================================ *)

(** Absorption law 1: join(t, meet(t, s)) = t (in terms of taint_contains) *)
val taint_absorption1_contains : t:taint_status -> s:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t (taint_meet t s)) k = taint_contains t k)

(** Absorption law 2: meet(t, join(t, s)) = t (in terms of taint_contains) *)
val taint_absorption2_contains : t:taint_status -> s:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t (taint_join t s)) k = taint_contains t k)

(** Absorption law 1 (structural): join(t, meet(t, s)) = t *)
val taint_absorption1 : t:taint_status -> s:taint_status ->
    Lemma (ensures taint_status_eq (taint_join t (taint_meet t s)) t = true)

(** Absorption law 2 (structural): meet(t, join(t, s)) = t *)
val taint_absorption2 : t:taint_status -> s:taint_status ->
    Lemma (ensures taint_status_eq (taint_meet t (taint_join t s)) t = true)

(** ============================================================================
    TAINT ORDERING (PARTIAL ORDER)
    ============================================================================ *)

(**
 * Partial order on taint status.
 * t1 <= t2 iff all taints in t1 are also in t2.
 *)
val taint_leq : taint_status -> taint_status -> bool

(** taint_leq is reflexive *)
val taint_leq_refl : t:taint_status ->
    Lemma (ensures taint_leq t t = true)
          [SMTPat (taint_leq t t)]

(** Untainted is the bottom element *)
val taint_leq_bot : t:taint_status ->
    Lemma (ensures taint_leq Untainted t = true)
          [SMTPat (taint_leq Untainted t)]

(** taint_leq is transitive *)
val taint_leq_trans : t1:taint_status -> t2:taint_status -> t3:taint_status ->
    Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t3 = true)
          (ensures taint_leq t1 t3 = true)

(** taint_leq is antisymmetric (via taint_status_eq) *)
val taint_leq_antisym : t1:taint_status -> t2:taint_status ->
    Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t1 = true)
          (ensures taint_status_eq t1 t2 = true)

(** Join is least upper bound *)
val taint_join_lub : t1:taint_status -> t2:taint_status ->
    Lemma (ensures taint_leq t1 (taint_join t1 t2) = true /\
                   taint_leq t2 (taint_join t1 t2) = true)

(** ============================================================================
    TAINTED VALUES
    ============================================================================

    A tainted value pairs a value with its taint status.
    ============================================================================ *)

(** Tainted value record type *)
noeq type tainted (a: Type) = {
  value : a;
  taint : taint_status;
}

(** Create an untainted value *)
val untainted : #a:Type -> a -> tainted a

(** Create a tainted value with a single kind *)
val tainted_with : #a:Type -> a -> taint_kind -> tainted a

(** Get the underlying value *)
val get_value : #a:Type -> tainted a -> a

(** Get the taint status *)
val get_taint : #a:Type -> tainted a -> taint_status

(** Check if a tainted value is safe (untainted) *)
val is_safe : #a:Type -> tainted a -> bool

(** ============================================================================
    SOURCES, SINKS, AND SANITIZERS
    ============================================================================ *)

(** Mark a value as coming from a tainted source *)
val source : #a:Type -> taint_kind -> a -> tainted a

(** Attempt to use a tainted value at a sink (returns Some iff safe) *)
val sink : #a:Type -> taint_kind -> tainted a -> option a

(** Sanitize a tainted value, removing a specific taint kind *)
val sanitize : #a:Type -> taint_kind -> tainted a -> (a -> a) -> tainted a

(** ============================================================================
    SOUNDNESS THEOREMS
    ============================================================================ *)

(** After sanitization, the value does not contain the sanitized taint kind *)
val sanitize_removes_taint : #a:Type -> k:taint_kind -> t:tainted a -> f:(a -> a) ->
    Lemma (ensures taint_contains (sanitize k t f).taint k = false)

(** Sanitization preserves other taint kinds *)
val sanitize_preserves_other_taints : #a:Type -> k:taint_kind -> k':taint_kind ->
    t:tainted a -> f:(a -> a) ->
    Lemma (requires taint_kind_eq k k' = false /\ taint_contains t.taint k' = true)
          (ensures taint_contains (sanitize k t f).taint k' = true)

(** Sink soundness: returns Some iff not tainted with checked kind *)
val sink_soundness : #a:Type -> k:taint_kind -> t:tainted a ->
    Lemma (ensures Some? (sink k t) <==> taint_contains t.taint k = false)

(** Sanitized values pass the sink check *)
val sanitize_then_sink : #a:Type -> k:taint_kind -> t:tainted a -> f:(a -> a) ->
    Lemma (ensures Some? (sink k (sanitize k t f)))

(** ============================================================================
    TAINT PROPAGATION
    ============================================================================ *)

(** Apply a unary function, propagating taint *)
val taint_map : #a:Type -> #b:Type -> (a -> b) -> tainted a -> tainted b

(** Apply a binary function, joining taints *)
val taint_map2 : #a:Type -> #b:Type -> #c:Type -> (a -> b -> c) ->
    tainted a -> tainted b -> tainted c

(** ============================================================================
    PROPAGATION PROPERTIES
    ============================================================================ *)

(** taint_map preserves taint status *)
val taint_map_preserves_taint : #a:Type -> #b:Type -> f:(a -> b) -> t:tainted a ->
    Lemma (ensures (taint_map f t).taint = t.taint)

(** taint_map2 combines taints correctly *)
val taint_map2_combines_taints : #a:Type -> #b:Type -> #c:Type -> f:(a -> b -> c) ->
    t1:tainted a -> t2:tainted b -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_map2 f t1 t2).taint k =
                   (taint_contains t1.taint k || taint_contains t2.taint k))

(** ============================================================================
    MONADIC OPERATIONS
    ============================================================================ *)

(** Monadic pure: lift an untainted value *)
val taint_pure : #a:Type -> a -> tainted a

(** Monadic bind: sequence taint-tracking computations *)
val taint_bind : #a:Type -> #b:Type -> tainted a -> (a -> tainted b) -> tainted b
