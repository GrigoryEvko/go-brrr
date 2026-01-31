(**
 * BrrrLang.Core.BorrowChecker - Interface
 *
 * Public interface for ownership and borrow checking in Brrr-Lang.
 * Based on brrr_lang_spec_v0.4.tex Part III (Ownership & Memory).
 *
 * This interface exposes:
 *   - Core types for borrow state tracking
 *   - Borrow checking functions
 *   - Region escape analysis
 *   - Soundness theorems
 *
 * THEORETICAL FOUNDATIONS
 * =======================
 *
 * The borrow checker implements a static analysis inspired by:
 *
 * 1. RustBelt (Jung et al. 2018, POPL)
 *    "RustBelt: Securing the Foundations of the Rust Programming Language"
 *    - Semantic foundation using Iris separation logic
 *    - Lifetime logic for modeling borrows
 *    - Proof that Rust's type system is sound
 *
 * 2. Iris Separation Logic (Jung et al. 2018, JFP)
 *    "Iris from the Ground Up: A Modular Foundation for Higher-Order
 *     Concurrent Separation Logic"
 *    - Points-to predicates: l |-> v, l |->^p v (fractional)
 *    - Separating conjunction for disjoint composition
 *    - Ghost state for shared ownership (Rc/Arc)
 *
 * 3. Pulse Ownership Model (F* ecosystem)
 *    - pts_to r #p v: permission-indexed points-to
 *    - share/gather: fractional permission splitting
 *    - Frame rule for local reasoning
 *
 * KEY CONCEPTS
 * ============
 *
 * var_state: Tracks ownership status of each variable
 *   - VsOwned: Full ownership, can move/borrow/drop
 *   - VsBorrowed: Has active shared borrows (read-only access)
 *   - VsBorrowedMut: Has exclusive borrow (no other access allowed)
 *   - VsMoved: Ownership transferred, use-after-move is error
 *   - VsShared: Reference-counted (Rc/Arc), shared ownership
 *   - VsDropped: Explicitly destroyed
 *
 * loan: Tracks active borrows with lifetime/scope information
 *   - loan_id: Unique identifier for the borrow
 *   - loan_var: Which variable is borrowed
 *   - loan_kind: Shared vs exclusive
 *   - loan_depth: Scope depth for automatic release
 *
 * SAFETY GUARANTEES
 * =================
 *
 * The borrow checker enforces:
 *   1. No use-after-move (VsMoved blocks further access)
 *   2. No use-after-free (VsDropped blocks further access)
 *   3. Exclusive access for mutation (&mut is unique)
 *   4. No data races (exclusive XOR shared, never both)
 *   5. Borrows don't outlive borrowed data (region analysis)
 *
 * SOUNDNESS THEOREMS
 * ==================
 *
 * This module proves several key safety properties:
 *   - exclusive_conflicts: &mut prevents other borrows
 *   - move_makes_unavailable: move invalidates the source
 *   - cannot_move_borrowed: borrowed data cannot be moved
 *   - borrow_exclusive: exclusive borrows are unique
 *   - borrow_live: borrowed data outlives borrows
 *)
module BrrrBorrowChecker

(* Z3 solver options for SMT tractability *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open BrrrModes
open BrrrTypes
open BrrrExpressions

(** ============================================================================
    REGION CAPABILITIES
    ============================================================================ *)

(* Region capability - tracks what regions are accessible *)
val region_cap : Type0

(* Region context - tracks available region capabilities *)
val region_ctx : Type0

(* Check if region has valid capability in context *)
val has_region_cap : region -> region_ctx -> bool

(* Add region capability to context *)
val add_region_cap : region -> region_ctx -> region_ctx

(* Invalidate region capability (when exiting letregion) *)
val invalidate_region : region -> region_ctx -> region_ctx

(* Generate fresh region *)
val fresh_region : nat -> region & nat

(* Check if region appears free in a type (region escape analysis) *)
val region_free_in_type : region -> brrr_type -> bool

(* Check if letregion scope is valid: region must not escape *)
val letregion_scope_ok : region -> brrr_type -> bool

(** ============================================================================
    LOAN IDENTIFIERS
    ============================================================================ *)

(* Unique identifier for each loan/borrow *)
val loan_id : Type0

(* Generate fresh loan ID *)
val fresh_loan_id : nat -> loan_id & nat

(** ============================================================================
    BORROW KIND
    ============================================================================ *)

(* Kind of borrow *)
type borrow_kind =
  | BorrowShared    : borrow_kind   (* &T - shared/immutable borrow *)
  | BorrowExclusive : borrow_kind   (* &mut T - exclusive/mutable borrow *)

(* Can read through this borrow? *)
val borrow_can_read : borrow_kind -> bool

(* Can write through this borrow? *)
val borrow_can_write : borrow_kind -> bool

(* Is borrow exclusive? *)
val is_exclusive : borrow_kind -> bool

(** ============================================================================
    ACTIVE LOAN - Borrow Tracking
    ============================================================================

    A loan represents an active borrow (reference) to a variable. Loans track
    the borrowing relationship and enforce the exclusivity invariants.

    THEORETICAL BASIS (RustBelt, Jung 2018)
    =======================================

    In RustBelt, borrows are modeled using the lifetime logic:

      &'a T  ~  bor(kappa, ty_shr(kappa, T, l))

    Where bor(kappa, P) is the "borrowed for lifetime kappa" modality.

    The loan record captures:
      - loan_id: unique witness for this borrow instance
      - loan_var: the borrowed location l
      - loan_kind: shared (ty_shr) vs mutable (&uniq)
      - loan_depth: approximates lifetime kappa via lexical scope depth

    LOAN INVARIANTS (enforced by well_formed predicate)
    ===================================================

    1. At most one BorrowExclusive loan per variable at any time
    2. BorrowExclusive conflicts with all other loans (shared or exclusive)
    3. Multiple BorrowShared loans can coexist (fractional permissions)
    4. loan_depth determines automatic release point (scope exit)

    SEPARATION LOGIC VIEW (Pulse/Steel)
    ====================================

    | loan_kind      | Permission held            |
    |----------------|----------------------------|
    | BorrowShared   | pts_to x #(1/n) v (frac)   |
    | BorrowExclusive| pts_to x #1.0R v (full)    |

    Creating a loan "borrows" permission from the owner.
    Ending a loan "returns" permission to the owner.

    ============================================================================ *)

(* An active loan (borrow) on a variable *)
val loan : Type0

(* Create a new loan *)
val make_loan : loan_id -> var_id -> borrow_kind -> nat -> loan

(** ============================================================================
    OWNERSHIP ERROR TYPES
    ============================================================================ *)

(* Ownership/borrow error types *)
type ownership_error =
  (* Move errors *)
  | ErrUseAfterMove      : var:var_id -> moved_at:nat -> ownership_error
  | ErrMoveWhileBorrowed : var:var_id -> loan:loan_id -> ownership_error
  | ErrDoubleMove        : var:var_id -> ownership_error

  (* Borrow errors *)
  | ErrBorrowWhileMoved  : var:var_id -> ownership_error
  | ErrMutBorrowWhileBorrowed : var:var_id -> existing:loan_id -> ownership_error
  | ErrBorrowWhileMutBorrowed : var:var_id -> existing:loan_id -> ownership_error
  | ErrMultipleMutBorrows : var:var_id -> first:loan_id -> ownership_error

  (* Lifetime errors *)
  | ErrBorrowOutlivesValue : loan:loan_id -> var:var_id -> ownership_error
  | ErrDanglingReference  : loan:loan_id -> ownership_error
  | ErrRegionEscapes      : r:region -> ownership_error

  (* Drop/free errors *)
  | ErrDropWhileBorrowed : var:var_id -> loans:list loan_id -> ownership_error
  | ErrDoubleFree        : var:var_id -> ownership_error

  (* Mode errors *)
  | ErrLinearNotConsumed : var:var_id -> ownership_error
  | ErrRelevantNotUsed   : var:var_id -> ownership_error
  | ErrAffineUsedMultiple : var:var_id -> count:nat -> ownership_error

  (* General errors *)
  | ErrVariableNotFound  : var:var_id -> ownership_error
  | ErrLoanNotFound      : loan:loan_id -> ownership_error
  | ErrInternalError     : msg:string -> ownership_error

(* Result type with explicit error *)
type borrow_result (a: Type) =
  | BrOk   : value:a -> borrow_result a
  | BrErr  : error:ownership_error -> borrow_result a

(** ============================================================================
    VARIABLE STATE - Ownership State Machine
    ============================================================================

    var_state models the ownership status of a variable at a given program point.
    This is the core abstraction enabling Rust-like memory safety guarantees.

    RUST/RUSTBELT CORRESPONDENCE (Jung 2018)
    ========================================

    | var_state     | Rust concept      | RustBelt semantic       |
    |---------------|-------------------|-------------------------|
    | VsOwned       | Owned value       | ty_own(tau, v)          |
    | VsMoved       | After move        | (empty - no assertion)  |
    | VsBorrowed    | &T references     | ty_shr(kappa, tau, l)   |
    | VsBorrowedMut | &mut T reference  | &uniq(kappa, l)         |
    | VsShared      | Rc<T> / Arc<T>    | shared ghost ownership  |
    | VsDropped     | After drop        | (empty - deallocated)   |

    SEPARATION LOGIC VIEW (Pulse/Steel)
    ====================================

    | var_state     | Separation logic predicate           |
    |---------------|--------------------------------------|
    | VsOwned       | pts_to x #1.0R v (full permission)   |
    | VsMoved       | emp (no permission remains)          |
    | VsBorrowed    | pts_to x #(1/n) v (fractional)       |
    | VsBorrowedMut | pts_to x #1.0R v (exclusive, scoped) |
    | VsShared      | shared_inv(x) * token(ref_count)     |
    | VsDropped     | emp (memory freed)                   |

    VsShared AND Rc/Arc
    ===================

    The VsShared state models reference-counted smart pointers:
      - ref_count tracks the number of Rc/Arc clones
      - Cloning increments ref_count (VsShared(n) -> VsShared(n+1))
      - Dropping decrements ref_count
      - When ref_count = 1 and dropped: VsShared(1) -> VsDropped
      - Cannot get &mut without interior mutability (RefCell)

    This follows the Iris pattern for shared ownership via ghost state,
    where a "token" represents one owner's stake in the shared resource.

    ============================================================================ *)

(* Ownership state of a variable *)
type var_state =
  | VsOwned       : var_state        (* Fully owned, can move/borrow *)
  | VsMoved       : var_state        (* Has been moved, unavailable *)
  | VsBorrowed    : list loan_id -> var_state  (* Has active shared borrows *)
  | VsBorrowedMut : loan_id -> var_state       (* Has active exclusive borrow *)
  | VsShared      : ref_count:nat -> var_state (* Reference-counted shared ownership *)
  | VsDropped     : var_state        (* Explicitly dropped, unavailable *)

(* Is variable available for use? *)
val is_available : var_state -> bool

(* Can variable be moved? *)
val can_move_state : var_state -> bool

(* Can variable be borrowed shared? *)
val can_borrow_shared : var_state -> bool

(* Can variable be borrowed exclusively? *)
val can_borrow_mut : var_state -> bool

(** ============================================================================
    VARIABLE ENTRY
    ============================================================================ *)

(* Variable entry type *)
val var_entry : Type0

(* Accessors for var_entry fields - renamed to avoid shadowing record field names *)
val get_ve_var : var_entry -> var_id
val get_ve_ty : var_entry -> brrr_type
val get_ve_mode : var_entry -> mode
val get_ve_state : var_entry -> var_state

(** ============================================================================
    BORROW STATE - Global Checker State
    ============================================================================

    The borrow_state maintains all information needed for ownership tracking
    during static analysis. It combines:
      - Per-variable ownership states (var_entry list)
      - Active borrows/loans (loan list)
      - Administrative state (counters, scope depth)

    CORRESPONDENCE TO RUSTBELT (Jung 2018)
    ======================================

    In RustBelt's semantic model:
      - Typing context Gamma maps variables to types
      - Lifetime context Delta tracks active lifetimes
      - The semantic interpretation [[Gamma; Delta |- e : tau]]
        requires all ownership assertions to be satisfied

    Our borrow_state is a STATIC APPROXIMATION of this semantic state,
    suitable for efficient analysis during type checking.

    WELL-FORMEDNESS INVARIANT
    =========================

    A borrow_state is well-formed (well_formed st = true) when:
      1. Each variable's ve_state is consistent with active loans:
         - VsOwned     => no loans for this variable
         - VsMoved     => no loans for this variable
         - VsDropped   => no loans for this variable
         - VsBorrowed  => all loans are BorrowShared
         - VsBorrowedMut => exactly one loan, BorrowExclusive
         - VsShared    => can have shared loans

      2. Loan IDs are unique (fresh_loan_id ensures this)

      3. Scope depths are properly nested

    This invariant is preserved by all operations (Lemma: borrow_op_preserves_wf).

    STATE MERGING (Control Flow Joins)
    ==================================

    When control flow merges (if/else, match), states must be merged.
    The merge computes the MEET in the var_state lattice:

                          VsOwned
                         /   |   \
              VsBorrowed  VsShared  VsBorrowedMut
                        \    |    /
                     VsMoved / VsDropped

    This ensures soundness: code after the merge cannot assume ownership
    that might not hold on some execution path.

    ============================================================================ *)

(* Borrow checker state *)
val borrow_state : Type0

(* Empty borrow state *)
val empty_borrow_state : borrow_state

(* Add new variable to state *)
val add_var : var_id -> brrr_type -> mode -> borrow_state -> borrow_state

(* Find variable entry *)
val find_var : var_id -> borrow_state -> option var_entry

(* Get variable state *)
val get_var_state : var_id -> borrow_state -> option var_state

(* Get variable mode *)
val get_var_mode : var_id -> borrow_state -> option mode

(** ============================================================================
    LOAN LOOKUP HELPERS
    ============================================================================ *)

(* Find loan by ID *)
val find_loan : loan_id -> borrow_state -> option loan

(* Get all loans for a variable *)
val loans_for_var : var_id -> borrow_state -> list loan

(** ============================================================================
    MOVE AND DROP
    ============================================================================ *)

(* Check if a move is valid and perform it *)
val check_move : var_id -> borrow_state -> option borrow_state

(* Check if a drop is valid and perform it *)
val check_drop : var_id -> borrow_state -> option borrow_state

(** ============================================================================
    BORROW OPERATIONS
    ============================================================================ *)

(* Begin a shared borrow *)
val begin_shared_borrow : var_id -> borrow_state -> option (loan_id & borrow_state)

(* Begin an exclusive borrow *)
val begin_exclusive_borrow : var_id -> borrow_state -> option (loan_id & borrow_state)

(* Begin borrow (shared or exclusive) *)
val begin_borrow : var_id -> bool -> borrow_state -> option (loan_id & borrow_state)

(* End a borrow *)
val end_borrow : loan_id -> borrow_state -> option borrow_state

(** ============================================================================
    SCOPE MANAGEMENT
    ============================================================================ *)

(* Enter a new scope *)
val enter_scope : borrow_state -> borrow_state

(* Exit scope - ends all borrows at current depth *)
val exit_scope : borrow_state -> option borrow_state

(** ============================================================================
    EXPRESSION BORROW CHECKING
    ============================================================================ *)

(* Borrow check result *)
val bc_result : Type0

(* Borrow check an expression *)
val borrow_check_expr : nat -> expr -> borrow_state -> bc_result

(* Borrow check with default fuel *)
val borrow_check : expr -> bc_result

(* Borrow check with initial state *)
val borrow_check_with_state : expr -> borrow_state -> bc_result

(** ============================================================================
    WELL-FORMEDNESS AND INVARIANTS
    ============================================================================ *)

(* Check if borrow state is well-formed *)
val well_formed : borrow_state -> bool

(** ============================================================================
    SOUNDNESS THEOREMS - Core Safety Properties
    ============================================================================

    These theorems establish the fundamental safety guarantees of the
    borrow checker. They correspond to key properties proven in RustBelt
    (Jung 2018) using Iris separation logic.

    THEORETICAL SIGNIFICANCE (RustBelt)
    ===================================

    In RustBelt, the soundness of Rust's type system is established through:

      1. Semantic typing: [[Gamma |- e : tau]] in Iris logic
      2. Fundamental theorem: syntactic typing implies semantic typing
      3. Adequacy: semantic typing implies memory safety

    Our theorems are STATIC APPROXIMATIONS of the semantic properties:

      exclusive_conflicts      ~ &uniq exclusivity (no aliasing)
      move_makes_unavailable   ~ ownership transfer is permanent
      cannot_move_borrowed     ~ borrowed data is pinned
      borrow_exclusive         ~ mutable references are unique
      borrow_live              ~ no dangling pointers

    SEPARATION LOGIC BASIS (Pulse/Steel)
    ====================================

    In separation logic terms, these theorems ensure:

      - Frame rule compatibility: operations don't affect unrelated state
      - Permission accounting: permissions are neither created nor destroyed
      - Lifetime soundness: borrows don't outlive their sources

    PROOF STRUCTURE
    ===============

    Most proofs rely on the well_formed invariant, which ensures:
      - var_state is consistent with loan list
      - Exclusive borrows have exactly one loan
      - Moved/dropped variables have no loans

    From well_formed, we can derive strong properties about what
    operations are permitted and their effects on state.

    ============================================================================ *)

(* Lemma: Exclusive borrow conflicts with any other borrow
   When begin_exclusive_borrow succeeds, no other loans exist for that variable.

   RUSTBELT CORRESPONDENCE: This captures the &uniq exclusivity property.
   In Iris: &uniq(kappa, l) * P(l) ==> False (contradiction) *)
val exclusive_conflicts : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (begin_exclusive_borrow x st) /\ well_formed st)
        (ensures length (loans_for_var x st) = 0)

(* Lemma: After move of linear variable, variable state is VsMoved *)
val move_makes_unavailable : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (check_move x st) /\
                  (match find_var x st with Some ve -> get_ve_mode ve = MOne | None -> false))
        (ensures (match check_move x st with
                  | Some st' ->
                      (match find_var x st' with
                       | Some ve' -> get_ve_state ve' = VsMoved
                       | None -> true)
                  | None -> true))

(* Lemma: Cannot move borrowed variable *)
val cannot_move_borrowed : x:var_id -> st:borrow_state ->
  Lemma (requires (match find_var x st with
                   | Some ve -> not (can_move_state (get_ve_state ve))
                   | None -> true))
        (ensures None? (check_move x st))

(* Lemma: Ending borrow removes the loan from the state *)
val end_borrow_restores : lid:loan_id -> st:borrow_state ->
  Lemma (requires Some? (find_loan lid st))
        (ensures (match end_borrow lid st with
                  | Some st' -> None? (find_loan lid st')
                  | None -> true))

(** ============================================================================
    EXTENDED BORROW STATE WITH REGIONS
    ============================================================================ *)

(* Extended borrow state with region tracking *)
val extended_borrow_state : Type0

(* Enter letregion scope: introduce fresh region *)
val enter_letregion : extended_borrow_state -> region & extended_borrow_state

(* Exit letregion scope: invalidate region, check no escaping references *)
val exit_letregion : region -> brrr_type -> extended_borrow_state -> borrow_result extended_borrow_state

(** ============================================================================
    NEW SOUNDNESS THEOREMS - Borrow Safety
    ============================================================================ *)

(* Lemma: Exclusive borrows are exclusive - no concurrent borrows allowed
   This is the core safety property of Rust-like borrowing *)
val borrow_exclusive : x:var_id -> st:borrow_state -> lid:loan_id ->
  Lemma (requires well_formed st /\
                  (match find_var x st with
                   | Some ve -> VsBorrowedMut? (get_ve_state ve)
                   | None -> false))
        (ensures length (loans_for_var x st) = 1)

(* Lemma: Borrowed data outlives the borrow
   A loan cannot exist for a moved or dropped variable *)
val borrow_live : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st)
        (ensures (match find_var x st with
                  | Some ve -> (VsMoved? (get_ve_state ve) \/ VsDropped? (get_ve_state ve)) ==>
                               length (loans_for_var x st) = 0
                  | None -> true))

(** ============================================================================
    LIFETIME TRACKING TYPES
    ============================================================================ *)

(* Lifetime constraint *)
type lifetime_constraint =
  | LCOutlives : r1:region -> r2:region -> lifetime_constraint  (* r1: r2 means r1 outlives r2 *)
  | LCEqual    : r1:region -> r2:region -> lifetime_constraint  (* r1 = r2 *)

(* Lifetime constraint set *)
val lifetime_constraints : Type0

(* Add a lifetime constraint *)
val add_lifetime_constraint : lifetime_constraint -> lifetime_constraints -> lifetime_constraints

(* Check if constraints are satisfiable *)
val constraints_satisfiable : lifetime_constraints -> bool

(* Infer minimal lifetimes from constraints *)
val solve_lifetime_constraints : lifetime_constraints -> option (list (region & region))
