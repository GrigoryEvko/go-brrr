(**
 * BrrrLang.Core.Modes - Interface
 *
 * Mode semiring for ownership and linearity tracking.
 * Based on brrr_lang_spec_v0.4.tex Part III (Ownership & Memory):
 *   - Chapter 7: Mode Semiring
 *   - Chapter 9: Borrowing as Fractional Permissions
 *
 * Modes form a semiring (M, +, *, 0, 1, omega) where:
 *   - 0 = absent (not available)
 *   - 1 = linear (use exactly once)
 *   - omega = unrestricted (use any number of times)
 *)
module Modes

open FStar.List.Tot

(* Z3 solver options for consistent proof behavior.
   Following HACL* patterns: conservative fuel settings with explicit rlimit.
   Using fuel 1/ifuel 1 for exhaustiveness proofs on small enum types. *)
#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** ============================================================================
    CORE MODE TYPES
    ============================================================================ *)

(* Core usage mode: how many times a value can be used *)
type mode =
  | MZero  : mode   (* 0 - absent/unavailable *)
  | MOne   : mode   (* 1 - exactly once (linear) *)
  | MOmega : mode   (* omega - any number of times (unrestricted) *)

(* Extended mode annotations - substructural variants *)
type extended_mode =
  | EMLinear      : extended_mode   (* Exactly once *)
  | EMAffine      : extended_mode   (* At most once *)
  | EMRelevant    : extended_mode   (* At least once *)
  | EMUnrestricted: extended_mode   (* Any number *)

(** ============================================================================
    MODE OPERATIONS
    ============================================================================ *)

(* Convert extended mode to base mode *)
val extended_to_mode : extended_mode -> mode

(* Structural rule checks *)
val allows_weakening : extended_mode -> bool
val allows_contraction : extended_mode -> bool

(* Can transition from extended mode to target mode?
   This checks if the extended mode allows reaching the target. *)
val can_transition : extended_mode -> mode -> bool

(* Mode semiring operations *)
val mode_add : mode -> mode -> mode
val mode_mul : mode -> mode -> mode

(* Mode lattice operations *)
val mode_leq : mode -> mode -> bool
val mode_join : mode -> mode -> mode
val mode_meet : mode -> mode -> mode

(** ============================================================================
    SEMIRING LAWS (Lemmas with SMTPat triggers)
    Following HACL* Lib.IntTypes patterns for automatic lemma application.
    ============================================================================ *)

(* Addition is commutative: m1 + m2 = m2 + m1 *)
val mode_add_comm : m1:mode -> m2:mode ->
  Lemma (ensures mode_add m1 m2 = mode_add m2 m1)
        [SMTPat (mode_add m1 m2)]

(* Addition is associative: (m1 + m2) + m3 = m1 + (m2 + m3) *)
val mode_add_assoc : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_add (mode_add m1 m2) m3 = mode_add m1 (mode_add m2 m3))
        [SMTPat (mode_add (mode_add m1 m2) m3)]

(* Zero is additive identity: 0 + m = m *)
val mode_add_zero : m:mode ->
  Lemma (ensures mode_add MZero m = m)
        [SMTPat (mode_add MZero m)]

(* Multiplication is associative: (m1 * m2) * m3 = m1 * (m2 * m3) *)
val mode_mul_assoc : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_mul (mode_mul m1 m2) m3 = mode_mul m1 (mode_mul m2 m3))
        [SMTPat (mode_mul (mode_mul m1 m2) m3)]

(* Multiplication is commutative: m1 * m2 = m2 * m1 *)
val mode_mul_comm : m1:mode -> m2:mode ->
  Lemma (ensures mode_mul m1 m2 = mode_mul m2 m1)
        [SMTPat (mode_mul m1 m2)]

(* One is multiplicative identity: 1 * m = m *)
val mode_mul_one : m:mode ->
  Lemma (ensures mode_mul MOne m = m)
        [SMTPat (mode_mul MOne m)]

(* Zero annihilates: 0 * m = 0 *)
val mode_mul_zero : m:mode ->
  Lemma (ensures mode_mul MZero m = MZero)
        [SMTPat (mode_mul MZero m)]

(* Distributivity: m1 * (m2 + m3) = m1*m2 + m1*m3 *)
val mode_distrib : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_mul m1 (mode_add m2 m3) = mode_add (mode_mul m1 m2) (mode_mul m1 m3))
        [SMTPat (mode_mul m1 (mode_add m2 m3))]

(* Ordering is reflexive: m <= m *)
val mode_leq_refl : m:mode ->
  Lemma (ensures mode_leq m m = true)
        [SMTPat (mode_leq m m)]

(* Ordering is transitive: m1 <= m2 /\ m2 <= m3 ==> m1 <= m3 *)
val mode_leq_trans : m1:mode -> m2:mode -> m3:mode ->
  Lemma (requires mode_leq m1 m2 = true /\ mode_leq m2 m3 = true)
        (ensures mode_leq m1 m3 = true)

(* Extended mode consistency: if the base mode is less than target,
   the extended mode can transition to that target. *)
val extended_mode_consistent : em:extended_mode -> m:mode ->
  Lemma (ensures mode_leq (extended_to_mode em) m = true ==>
                 can_transition em m = true)
        [SMTPat (extended_to_mode em); SMTPat (mode_leq (extended_to_mode em) m)]

(** ============================================================================
    MODE LATTICE LAWS (with SMTPat triggers)
    ============================================================================ *)

(* Join is commutative *)
val mode_join_comm : m1:mode -> m2:mode ->
  Lemma (ensures mode_join m1 m2 = mode_join m2 m1)
        [SMTPat (mode_join m1 m2)]

(* Join is associative *)
val mode_join_assoc : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_join (mode_join m1 m2) m3 = mode_join m1 (mode_join m2 m3))
        [SMTPat (mode_join (mode_join m1 m2) m3)]

(* Zero is identity for join *)
val mode_join_zero : m:mode ->
  Lemma (ensures mode_join MZero m = m /\ mode_join m MZero = m)
        [SMTPat (mode_join MZero m)]

(* Omega is absorbing for join *)
val mode_join_omega : m:mode ->
  Lemma (ensures mode_join MOmega m = MOmega /\ mode_join m MOmega = MOmega)
        [SMTPat (mode_join MOmega m)]

(* Join is idempotent *)
val mode_join_idemp : m:mode ->
  Lemma (ensures mode_join m m = m)
        [SMTPat (mode_join m m)]

(* Meet is commutative *)
val mode_meet_comm : m1:mode -> m2:mode ->
  Lemma (ensures mode_meet m1 m2 = mode_meet m2 m1)
        [SMTPat (mode_meet m1 m2)]

(* Meet is associative *)
val mode_meet_assoc : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_meet (mode_meet m1 m2) m3 = mode_meet m1 (mode_meet m2 m3))
        [SMTPat (mode_meet (mode_meet m1 m2) m3)]

(* Omega is identity for meet *)
val mode_meet_omega : m:mode ->
  Lemma (ensures mode_meet MOmega m = m /\ mode_meet m MOmega = m)
        [SMTPat (mode_meet MOmega m)]

(* Zero is absorbing for meet *)
val mode_meet_zero : m:mode ->
  Lemma (ensures mode_meet MZero m = MZero /\ mode_meet m MZero = MZero)
        [SMTPat (mode_meet MZero m)]

(* Meet is idempotent *)
val mode_meet_idemp : m:mode ->
  Lemma (ensures mode_meet m m = m)
        [SMTPat (mode_meet m m)]

(* Antisymmetry: m1 <= m2 /\ m2 <= m1 ==> m1 = m2 *)
val mode_leq_antisym : m1:mode -> m2:mode ->
  Lemma (requires mode_leq m1 m2 = true /\ mode_leq m2 m1 = true)
        (ensures m1 = m2)

(* Absorption laws *)
val mode_absorb_join_meet : m1:mode -> m2:mode ->
  Lemma (ensures mode_join m1 (mode_meet m1 m2) = m1)

val mode_absorb_meet_join : m1:mode -> m2:mode ->
  Lemma (ensures mode_meet m1 (mode_join m1 m2) = m1)

(* Connection between ordering and lattice operations *)
val mode_leq_join : m1:mode -> m2:mode ->
  Lemma (ensures mode_leq m1 m2 = true <==> mode_join m1 m2 = m2)

val mode_leq_meet : m1:mode -> m2:mode ->
  Lemma (ensures mode_leq m1 m2 = true <==> mode_meet m1 m2 = m1)

(** ============================================================================
    OWNERSHIP QUALIFIERS
    ============================================================================ *)

type ownership =
  | Owned     : ownership
  | Borrowed  : ownership
  | BorrowMut : ownership

val can_read : ownership -> bool
val can_write : ownership -> bool
val can_move : ownership -> bool

(* Ownership to mode conversion *)
val ownership_to_mode : ownership -> bool -> mode
val ownership_to_extended_mode : ownership -> bool -> extended_mode

(** ============================================================================
    MODE CONTEXT (CONSUMPTION TRACKING)
    ============================================================================ *)

(* Mode context entry: variable name, current mode, and extended mode annotation *)
type mode_ctx_entry = string & mode & extended_mode

(* A mode context tracks usage of each variable with full mode information *)
type mode_ctx = list mode_ctx_entry

val empty_mode_ctx : mode_ctx
val lookup_mode : string -> mode_ctx -> (mode & extended_mode)
val lookup_mode_only : string -> mode_ctx -> mode
val lookup_extended_mode : string -> mode_ctx -> extended_mode
val update_mode : string -> mode -> mode_ctx -> mode_ctx
val update_mode_full : string -> mode -> extended_mode -> mode_ctx -> mode_ctx
val extend_mode_ctx : string -> mode -> extended_mode -> mode_ctx -> mode_ctx
val consume : string -> mode_ctx -> option mode_ctx
val split_ctx : mode_ctx -> (mode_ctx & mode_ctx)
val join_ctx : mode_ctx -> mode_ctx -> mode_ctx
val can_weaken_var : string -> mode_ctx -> bool
val can_contract_var : string -> mode_ctx -> bool
val contract_mode_ctx : string -> mode_ctx -> option mode_ctx

(* Context validity predicate: all entries have consistent mode/extended_mode pairs *)
val valid_mode_ctx : mode_ctx -> bool

(* Consume preserves validity: if context is valid, consuming yields valid or None *)
val consume_preserves_valid : x:string -> ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true)
        (ensures Some? (consume x ctx) ==> valid_mode_ctx (Some?.v (consume x ctx)) = true)
        [SMTPat (consume x ctx)]

(* Split preserves validity: splitting valid context yields two valid contexts *)
val split_preserves_valid : ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true)
        (ensures valid_mode_ctx (fst (split_ctx ctx)) = true /\
                 valid_mode_ctx (snd (split_ctx ctx)) = true)
        [SMTPat (split_ctx ctx)]

(* Join preserves validity *)
val join_preserves_valid : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx1 = true /\ valid_mode_ctx ctx2 = true)
        (ensures valid_mode_ctx (join_ctx ctx1 ctx2) = true)
        [SMTPat (join_ctx ctx1 ctx2)]

(** ============================================================================
    FRACTIONAL PERMISSIONS
    ============================================================================ *)

type fraction_raw = {
  frac_num : nat;
  frac_den : nat
}

val valid_frac : fraction_raw -> bool

type fraction = f:fraction_raw{valid_frac f}

val frac_full : fraction
val frac_half : fraction

val is_full_perm : fraction -> bool
val is_shared_perm : fraction -> bool
val frac_leq : fraction -> fraction -> bool
val frac_eq : fraction -> fraction -> bool

(* Fraction operations - frac_simplify must come first as it's called by frac_split *)
val frac_simplify : fraction -> fraction
val frac_split : fraction -> (fraction & fraction)
val frac_join : fraction -> fraction -> option fraction

(* Fraction equality lemmas *)
val frac_eq_refl : f:fraction ->
  Lemma (ensures frac_eq f f = true)
        [SMTPat (frac_eq f f)]

val frac_eq_sym : f1:fraction -> f2:fraction ->
  Lemma (requires frac_eq f1 f2 = true)
        (ensures frac_eq f2 f1 = true)

val frac_eq_trans : f1:fraction -> f2:fraction -> f3:fraction ->
  Lemma (requires frac_eq f1 f2 = true /\ frac_eq f2 f3 = true)
        (ensures frac_eq f1 f3 = true)

val frac_leq_trans : f1:fraction -> f2:fraction -> f3:fraction ->
  Lemma (requires frac_leq f1 f2 = true /\ frac_leq f2 f3 = true)
        (ensures frac_leq f1 f3 = true)

(* Split/join inverse lemma: splitting and joining recovers original fraction.
   This is fundamental for fractional permission soundness. *)
val frac_split_join_inverse : f:fraction ->
  Lemma (ensures
    (let (h1, h2) = frac_split f in
     Some? (frac_join h1 h2) /\
     frac_eq (Some?.v (frac_join h1 h2)) f = true))
  [SMTPat (frac_split f)]

(* Fraction ordering is reflexive *)
val frac_leq_refl : f:fraction ->
  Lemma (ensures frac_leq f f = true)
        [SMTPat (frac_leq f f)]

(* Full permission is maximal *)
val frac_full_maximal : f:fraction ->
  Lemma (ensures frac_leq f frac_full = true)
        [SMTPat (frac_leq f frac_full)]

(* Half permission is less than full *)
val frac_half_lt_full : unit ->
  Lemma (ensures frac_leq frac_half frac_full = true /\
                 is_shared_perm frac_half = true)

(** ============================================================================
    PERMISSION-BASED REFERENCES
    ============================================================================ *)

type ref_kind =
  | RefBox     : fraction -> ref_kind
  | RefDiamond : ref_kind

val is_box_ref : ref_kind -> bool
val is_diamond_ref : ref_kind -> bool
val ref_permission : ref_kind -> fraction
val ref_can_read : ref_kind -> bool
val ref_can_write : ref_kind -> bool

val freeze : ref_kind -> option ref_kind
val thaw : ref_kind -> option ref_kind
val split_box : ref_kind -> option (ref_kind & ref_kind)
val join_box : ref_kind -> ref_kind -> option ref_kind

(** ============================================================================
    LINEAR CONTEXT
    ============================================================================ *)

type lin_entry = {
  le_var  : string;
  le_mode : mode;
  le_ext  : extended_mode;
  le_perm : option fraction;
  le_used : bool    (* Was this variable accessed at least once? *)
}

type lin_ctx = list lin_entry

val empty_lin_ctx : lin_ctx
val lookup_lin : string -> lin_ctx -> option lin_entry
val extend_lin : lin_entry -> lin_ctx -> lin_ctx

(* Mark a variable as used (for EMRelevant tracking) *)
val use_lin : string -> lin_ctx -> option lin_ctx

val split_lin_ctx : lin_ctx -> (lin_ctx & lin_ctx)
val join_lin_ctx : lin_ctx -> lin_ctx -> lin_ctx
val is_fully_consumed : lin_ctx -> bool
val weaken_lin : string -> mode -> extended_mode -> lin_ctx -> option lin_ctx
val contract_lin : string -> lin_ctx -> option lin_ctx

(** ============================================================================
    ADDITIONAL LEMMAS FOR LINEAR CONTEXT SOUNDNESS
    ============================================================================ *)

(* Validity predicate for linear context *)
val valid_lin_ctx : lin_ctx -> bool

(* Using a variable preserves validity *)
val use_lin_preserves_valid : x:string -> ctx:lin_ctx ->
  Lemma (requires valid_lin_ctx ctx = true)
        (ensures Some? (use_lin x ctx) ==> valid_lin_ctx (Some?.v (use_lin x ctx)) = true)
        [SMTPat (use_lin x ctx)]

(** ============================================================================
    MODE SUBTYPING AND COMPATIBILITY
    Following HACL* Lib.IntTypes secrecy_level pattern.
    ============================================================================ *)

(* Mode subtyping: m1 <: m2 means m1 can be used where m2 is expected.
   Based on the lattice ordering: 0 <: 1 <: omega.

   Intuition:
   - MZero (absent) can be used where anything is expected (vacuously)
   - MOne (linear) can be used where omega is expected (use once is a subset of use many)
   - MOmega requires omega *)
unfold
let mode_subtype (m1 m2: mode) : bool = mode_leq m1 m2

(* Convenience refinement types following Spec.Hash.Definitions pattern *)
let linear_mode = m:mode{ m = MOne }
let unrestricted_mode = m:mode{ m = MOmega }
let available_mode = m:mode{ m <> MZero }

(* Extended mode subtyping: em1 <: em2 means em1 is more restrictive.
   Ordering: EMLinear <: EMAffine, EMLinear <: EMRelevant, both <: EMUnrestricted *)
val extended_mode_subtype : extended_mode -> extended_mode -> bool

(* Mode compatibility for parallel composition.
   Two modes are compatible if they can be combined in split_ctx.
   - MOmega + anything = compatible (can share)
   - MOne + MZero = compatible (exclusive to one side)
   - MOne + MOne = incompatible (would require duplication) *)
val mode_compatible : mode -> mode -> bool

(* Extended mode compatibility: checks if structural rules allow combination.
   Accounts for contraction/weakening capabilities. *)
val extended_mode_compatible : extended_mode -> extended_mode -> bool

(** ============================================================================
    MODE CONTEXT SPLITTING SPECIFICATIONS
    split_ctx is DETERMINISTIC: linear resources go to LEFT side.
    ============================================================================ *)

(* Check if a mode context entry is present (has non-zero mode) *)
unfold
let mode_ctx_entry_present (entry: mode_ctx_entry) : bool =
  match entry with (_, m, _) -> m <> MZero

(* Get the mode for a variable from context, returning MZero if absent *)
val get_mode_in_ctx : x:string -> ctx:mode_ctx -> mode

(* Linear exclusivity: after split, linear resources are exclusive to left side.
   If a variable has MOne in ctx, it has MOne in left and MZero in right. *)
val split_ctx_linear_exclusive : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         get_mode_in_ctx x ctx = MOne ==>
         (get_mode_in_ctx x l = MOne /\ get_mode_in_ctx x r = MZero))
        [SMTPat (split_ctx ctx); SMTPat (get_mode_in_ctx x ctx)]

(* Omega sharing: after split, unrestricted resources are in both sides. *)
val split_ctx_omega_shared : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         get_mode_in_ctx x ctx = MOmega ==>
         (get_mode_in_ctx x l = MOmega /\ get_mode_in_ctx x r = MOmega))
        [SMTPat (split_ctx ctx); SMTPat (get_mode_in_ctx x ctx)]

(* Zero propagation: zero mode stays zero in both halves. *)
val split_ctx_zero_both : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         get_mode_in_ctx x ctx = MZero ==>
         (get_mode_in_ctx x l = MZero /\ get_mode_in_ctx x r = MZero))

(* Completeness: modes add up. For any variable, the modes in split halves
   combine via mode_add to give the original mode. *)
val split_ctx_mode_sum : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         mode_add (get_mode_in_ctx x l) (get_mode_in_ctx x r) =
         get_mode_in_ctx x ctx \/
         (get_mode_in_ctx x ctx = MOmega))

(* Extended mode preservation: split preserves extended_mode annotations. *)
val split_ctx_preserves_extended : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         lookup_extended_mode x l = lookup_extended_mode x ctx /\
         lookup_extended_mode x r = lookup_extended_mode x ctx)

(** ============================================================================
    MODE CONTEXT CONSUMPTION CHECKING
    ============================================================================ *)

(* Check if all linear resources in mode_ctx are fully consumed.
   This is the mode_ctx analog of is_fully_consumed for lin_ctx.

   Rules based on extended_mode:
   - EMLinear: must have mode MZero (used exactly once)
   - EMRelevant: must have been used at least once (mode can be MZero or MOmega after use)
   - EMAffine: can be MZero or MOne (unused is okay)
   - EMUnrestricted: any mode is valid *)
val is_mode_ctx_fully_consumed : mode_ctx -> bool

(* Well-formedness: a mode_ctx is well-formed if:
   1. No duplicate variable names
   2. All entries are valid (mode consistent with extended_mode) *)
val mode_ctx_wf : mode_ctx -> bool

(* Fully consumed context implies valid context *)
val fully_consumed_implies_valid : ctx:mode_ctx ->
  Lemma (requires is_mode_ctx_fully_consumed ctx = true)
        (ensures valid_mode_ctx ctx = true)

(** ============================================================================
    JOIN CONTEXT SPECIFICATIONS
    ============================================================================ *)

(* Join is symmetric for modes *)
val join_ctx_mode_comm : ctx1:mode_ctx -> ctx2:mode_ctx -> x:string ->
  Lemma (get_mode_in_ctx x (join_ctx ctx1 ctx2) =
         mode_join (get_mode_in_ctx x ctx1) (get_mode_in_ctx x ctx2))

(* Split then join recovers original (up to mode equivalence) *)
val split_join_roundtrip : ctx:mode_ctx -> x:string ->
  Lemma (let (l, r) = split_ctx ctx in
         get_mode_in_ctx x (join_ctx l r) = get_mode_in_ctx x ctx)
        [SMTPat (get_mode_in_ctx x (join_ctx (fst (split_ctx ctx)) (snd (split_ctx ctx))))]

(** ============================================================================
    LINEAR CONTEXT SPLITTING SPECIFICATIONS
    ============================================================================ *)

(* Split preserves validity for linear context *)
val split_lin_preserves_valid : ctx:lin_ctx ->
  Lemma (requires valid_lin_ctx ctx = true)
        (ensures valid_lin_ctx (fst (split_lin_ctx ctx)) = true /\
                 valid_lin_ctx (snd (split_lin_ctx ctx)) = true)
        [SMTPat (split_lin_ctx ctx)]

(* Join preserves validity for linear context *)
val join_lin_preserves_valid : ctx1:lin_ctx -> ctx2:lin_ctx ->
  Lemma (requires valid_lin_ctx ctx1 = true /\ valid_lin_ctx ctx2 = true)
        (ensures valid_lin_ctx (join_lin_ctx ctx1 ctx2) = true)
        [SMTPat (join_lin_ctx ctx1 ctx2)]

(* Contraction preserves validity *)
val contract_lin_preserves_valid : x:string -> ctx:lin_ctx ->
  Lemma (requires valid_lin_ctx ctx = true)
        (ensures Some? (contract_lin x ctx) ==>
                 valid_lin_ctx (Some?.v (contract_lin x ctx)) = true)
        [SMTPat (contract_lin x ctx)]

(* Weakening preserves validity *)
val weaken_lin_preserves_valid : x:string -> m:mode -> em:extended_mode -> ctx:lin_ctx ->
  Lemma (requires valid_lin_ctx ctx = true)
        (ensures Some? (weaken_lin x m em ctx) ==>
                 valid_lin_ctx (Some?.v (weaken_lin x m em ctx)) = true)

(** ============================================================================
    OWNERSHIP TO MODE LEMMAS
    ============================================================================ *)

(* Owned non-copy types are linear *)
val owned_noncopy_is_linear : unit ->
  Lemma (ensures ownership_to_mode Owned false = MOne /\
                 ownership_to_extended_mode Owned false = EMLinear)

(* Borrowed references are unrestricted *)
val borrowed_is_unrestricted : unit ->
  Lemma (ensures ownership_to_mode Borrowed true = MOmega /\
                 ownership_to_mode Borrowed false = MOmega /\
                 ownership_to_extended_mode Borrowed true = EMUnrestricted)

(* Mutable borrows are affine (can be dropped but not duplicated) *)
val borrow_mut_is_affine : unit ->
  Lemma (ensures ownership_to_mode BorrowMut true = MOne /\
                 ownership_to_extended_mode BorrowMut true = EMAffine)

(** ============================================================================
    MODE CHECKING JUDGMENTS
    Type aliases for mode checking specifications.
    ============================================================================ *)

(* A mode-checked expression: expression with its mode context delta *)
type mode_checked_result = {
  mcr_mode : mode;
  mcr_ext  : extended_mode;
  mcr_ctx  : mode_ctx         (* Resulting context after checking *)
}

(* Mode checking success: input context transforms to output context *)
type mode_check_ok (ctx_in: mode_ctx) (ctx_out: mode_ctx) =
  valid_mode_ctx ctx_in ==> valid_mode_ctx ctx_out

(* Linear resource accounting: resources consumed in ctx_out were available in ctx_in *)
val mode_check_linear_accounting : ctx_in:mode_ctx -> ctx_out:mode_ctx -> x:string ->
  Lemma (requires mode_check_ok ctx_in ctx_out)
        (ensures get_mode_in_ctx x ctx_out = MZero ==>
                 (get_mode_in_ctx x ctx_in = MOne \/ get_mode_in_ctx x ctx_in = MZero))

(** ============================================================================
    RESOURCE COUNTING - Following HACL* Lib.Sequence patterns
    Count resources by ownership type for linearity verification.
    ============================================================================ *)

(* Count variables with MOne (owned/linear) mode in context *)
val count_owned : mode_ctx -> nat

(* Count variables with MOmega (borrowed/shared) mode in context *)
val count_borrowed : mode_ctx -> nat

(* Count consumed (MZero) variables in context *)
val count_consumed : mode_ctx -> nat

(* Total variable count equals sum of all categories *)
val count_total_eq : ctx:mode_ctx ->
  Lemma (ensures length ctx = count_owned ctx + count_borrowed ctx + count_consumed ctx)
        [SMTPat (length ctx)]

(* Split preserves owned count: owned resources are exclusive to one side.
   After split, the sum of owned counts in both halves equals the original.
   Proof: MOne -> (MOne, MZero), so left gets the count, right gets zero for that var. *)
val split_preserves_owned_count : ctx:mode_ctx ->
  Lemma (ensures (let (l, r) = split_ctx ctx in
                  count_owned l = count_owned ctx /\
                  count_owned r = 0))
        [SMTPat (split_ctx ctx)]

(* Split duplicates borrowed count: borrowed resources go to both sides.
   Proof: MOmega -> (MOmega, MOmega), so both halves get the full count. *)
val split_preserves_borrowed_count : ctx:mode_ctx ->
  Lemma (ensures (let (l, r) = split_ctx ctx in
                  count_borrowed l = count_borrowed ctx /\
                  count_borrowed r = count_borrowed ctx))

(** ============================================================================
    MODE TRANSITION VALIDITY - Following HACL* state machine patterns
    Defines valid mode transitions for borrow checker semantics.
    ============================================================================ *)

(* Valid mode transitions following Rust borrow semantics:
   - MOne -> MZero: consumption (move or last use)
   - MOne -> MOmega: contraction (if extended_mode allows)
   - MOmega -> MOmega: unrestricted can stay unrestricted
   - MZero -> MZero: dead stays dead
   Invalid transitions:
   - MZero -> MOne/MOmega: cannot resurrect consumed resource
   - MOmega -> MOne: cannot un-share (need explicit ownership transfer) *)
val valid_mode_transition : m_before:mode -> m_after:mode -> bool

(* Mode transition is reflexive: m -> m is always valid for non-zero modes *)
val mode_transition_refl : m:mode ->
  Lemma (ensures m <> MZero ==> valid_mode_transition m m = true)
        [SMTPat (valid_mode_transition m m)]

(* Mode transition is transitive: if m1->m2 and m2->m3 are valid, so is m1->m3 *)
val mode_transition_trans : m1:mode -> m2:mode -> m3:mode ->
  Lemma (requires valid_mode_transition m1 m2 = true /\ valid_mode_transition m2 m3 = true)
        (ensures valid_mode_transition m1 m3 = true)

(* Consumption is terminal: after MZero, only MZero is reachable *)
val mode_zero_terminal : m:mode ->
  Lemma (ensures valid_mode_transition MZero m = true <==> m = MZero)
        [SMTPat (valid_mode_transition MZero m)]

(* Contraction preserves validity: MOne can transition to MOmega *)
val mode_contraction_valid : unit ->
  Lemma (ensures valid_mode_transition MOne MOmega = true)

(* Consumption from linear is valid *)
val mode_consume_valid : unit ->
  Lemma (ensures valid_mode_transition MOne MZero = true)

(** ============================================================================
    LINEARITY PRESERVATION - Following HACL* Lib.Buffer memory safety patterns
    Comprehensive proofs that operations preserve linearity invariants.
    ============================================================================ *)

(* Well-formedness predicate for linearity checking *)
let linearity_wf (ctx: mode_ctx) : bool =
  mode_ctx_wf ctx && valid_mode_ctx ctx

(* Split preserves linearity: if input is well-formed, both outputs are well-formed.
   This is the key lemma for the L-App rule soundness. *)
val split_preserves_linearity : ctx:mode_ctx ->
  Lemma (requires linearity_wf ctx = true)
        (ensures (let (c1, c2) = split_ctx ctx in
                  linearity_wf c1 = true /\ linearity_wf c2 = true))
        [SMTPat (split_ctx ctx)]

(* Join preserves linearity *)
val join_preserves_linearity : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires linearity_wf ctx1 = true /\ linearity_wf ctx2 = true)
        (ensures linearity_wf (join_ctx ctx1 ctx2) = true)
        [SMTPat (join_ctx ctx1 ctx2)]

(* Consumption preserves linearity *)
val consume_preserves_linearity : x:string -> ctx:mode_ctx ->
  Lemma (requires linearity_wf ctx = true)
        (ensures Some? (consume x ctx) ==> linearity_wf (Some?.v (consume x ctx)) = true)
        [SMTPat (consume x ctx)]

(* Contraction preserves linearity (when allowed by extended_mode) *)
val contract_preserves_linearity : x:string -> ctx:mode_ctx ->
  Lemma (requires linearity_wf ctx = true)
        (ensures Some? (contract_mode_ctx x ctx) ==>
                 linearity_wf (Some?.v (contract_mode_ctx x ctx)) = true)
        [SMTPat (contract_mode_ctx x ctx)]

(** ============================================================================
    MODE ALGEBRA LAWS - Complete lattice/semiring structure
    Following HACL* Lib.NatMod algebraic proof patterns.
    ============================================================================ *)

(* Lattice distributivity: join distributes over meet *)
val mode_join_distrib_meet : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_join m1 (mode_meet m2 m3) =
                 mode_meet (mode_join m1 m2) (mode_join m1 m3))

(* Lattice distributivity: meet distributes over join *)
val mode_meet_distrib_join : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_meet m1 (mode_join m2 m3) =
                 mode_join (mode_meet m1 m2) (mode_meet m1 m3))

(* Mode addition is monotonic w.r.t. lattice order *)
val mode_add_monotonic : m1:mode -> m2:mode -> m3:mode ->
  Lemma (requires mode_leq m1 m2 = true)
        (ensures mode_leq (mode_add m1 m3) (mode_add m2 m3) = true)

(* Mode multiplication is monotonic w.r.t. lattice order *)
val mode_mul_monotonic : m1:mode -> m2:mode -> m3:mode ->
  Lemma (requires mode_leq m1 m2 = true)
        (ensures mode_leq (mode_mul m1 m3) (mode_mul m2 m3) = true)

(* Semiring-lattice connection: multiplication distributes over join *)
val mode_mul_distrib_join : m1:mode -> m2:mode -> m3:mode ->
  Lemma (ensures mode_mul m1 (mode_join m2 m3) =
                 mode_join (mode_mul m1 m2) (mode_mul m1 m3))

(** ============================================================================
    EXTENDED MODE ALGEBRA - Substructural type system properties
    ============================================================================ *)

(* Extended mode lattice join *)
val extended_mode_join : extended_mode -> extended_mode -> extended_mode

(* Extended mode lattice meet *)
val extended_mode_meet : extended_mode -> extended_mode -> extended_mode

(* Extended mode join is commutative *)
val extended_mode_join_comm : em1:extended_mode -> em2:extended_mode ->
  Lemma (ensures extended_mode_join em1 em2 = extended_mode_join em2 em1)
        [SMTPat (extended_mode_join em1 em2)]

(* Extended mode meet is commutative *)
val extended_mode_meet_comm : em1:extended_mode -> em2:extended_mode ->
  Lemma (ensures extended_mode_meet em1 em2 = extended_mode_meet em2 em1)
        [SMTPat (extended_mode_meet em1 em2)]

(* Subtyping is reflexive *)
val extended_mode_subtype_refl : em:extended_mode ->
  Lemma (ensures extended_mode_subtype em em = true)
        [SMTPat (extended_mode_subtype em em)]

(* Subtyping is transitive *)
val extended_mode_subtype_trans : em1:extended_mode -> em2:extended_mode -> em3:extended_mode ->
  Lemma (requires extended_mode_subtype em1 em2 = true /\ extended_mode_subtype em2 em3 = true)
        (ensures extended_mode_subtype em1 em3 = true)

(* Subtyping is antisymmetric *)
val extended_mode_subtype_antisym : em1:extended_mode -> em2:extended_mode ->
  Lemma (requires extended_mode_subtype em1 em2 = true /\ extended_mode_subtype em2 em1 = true)
        (ensures em1 = em2)

(** ============================================================================
    BORROW CHECKER STYLE PROOFS - Following Rust semantics
    ============================================================================ *)

(* Exclusive borrow invariant: at most one mutable borrow at a time.
   Formalized as: if a variable has MOne mode, it cannot appear twice
   with MOne in any reachable context. *)
val exclusive_borrow_invariant : ctx:mode_ctx -> x:string -> y:string ->
  Lemma (requires mode_ctx_wf ctx = true /\
                  get_mode_in_ctx x ctx = MOne /\
                  lookup_extended_mode x ctx = EMAffine)
        (ensures x = y \/ get_mode_in_ctx y ctx <> MOne \/
                 lookup_extended_mode y ctx <> EMAffine)

(* Shared borrow coexistence: multiple shared borrows can coexist.
   MOmega resources can be duplicated freely. *)
val shared_borrow_coexist : ctx:mode_ctx -> x:string ->
  Lemma (requires get_mode_in_ctx x ctx = MOmega)
        (ensures (let (l, r) = split_ctx ctx in
                  get_mode_in_ctx x l = MOmega /\ get_mode_in_ctx x r = MOmega))
        [SMTPat (get_mode_in_ctx x ctx)]

(* Borrow expiration: after all borrows return, ownership is restored.
   This is modeled by the thaw operation on ref_kind. *)
val borrow_expiration : rk:ref_kind ->
  Lemma (requires RefBox? rk /\ is_full_perm (RefBox?._0 rk))
        (ensures Some? (thaw rk) /\ RefDiamond? (Some?.v (thaw rk)))

(* No use after move: consumed linear resource cannot be accessed.
   If mode is MZero, any access attempt should fail. *)
val no_use_after_move : ctx:mode_ctx -> x:string ->
  Lemma (requires get_mode_in_ctx x ctx = MZero /\
                  lookup_extended_mode x ctx = EMLinear)
        (ensures consume x ctx = None)
        [SMTPat (consume x ctx); SMTPat (get_mode_in_ctx x ctx)]

(* Linear context respects move semantics *)
val linear_move_semantics : ctx:mode_ctx -> x:string ->
  Lemma (requires get_mode_in_ctx x ctx = MOne /\
                  lookup_extended_mode x ctx = EMLinear)
        (ensures Some? (consume x ctx) /\
                 get_mode_in_ctx x (Some?.v (consume x ctx)) = MZero)

(** ============================================================================
    CONTEXT COMPOSITION - Following HACL* calc block patterns
    ============================================================================ *)

(* Sequential composition: ctx1 ; ctx2 where ctx2 consumes from ctx1's output *)
val ctx_seq_compose : ctx1:mode_ctx -> ctx2:mode_ctx -> mode_ctx

(* Sequential composition preserves well-formedness *)
val ctx_seq_compose_wf : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires mode_ctx_wf ctx1 = true /\ mode_ctx_wf ctx2 = true)
        (ensures mode_ctx_wf (ctx_seq_compose ctx1 ctx2) = true)

(* Parallel composition is commutative (for compatible contexts) *)
val ctx_par_compose_comm : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires mode_ctx_wf ctx1 = true /\ mode_ctx_wf ctx2 = true)
        (ensures join_ctx ctx1 ctx2 = join_ctx ctx2 ctx1 \/
                 (* Contexts may differ in variable ordering, but modes match *)
                 (forall x. get_mode_in_ctx x (join_ctx ctx1 ctx2) =
                           get_mode_in_ctx x (join_ctx ctx2 ctx1)))
