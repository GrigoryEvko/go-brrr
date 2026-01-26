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
 *)
module BorrowChecker

(* Z3 solver options for SMT tractability *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open Modes
open BrrrTypes
open Expressions

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
    ACTIVE LOAN
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
    VARIABLE STATE
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

(* Accessors for var_entry fields - needed for interface *)
val ve_var : var_entry -> var_id
val ve_ty : var_entry -> brrr_type
val ve_mode : var_entry -> mode
val ve_state : var_entry -> var_state

(** ============================================================================
    BORROW STATE
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
    SOUNDNESS THEOREMS
    ============================================================================ *)

(* Lemma: Exclusive borrow conflicts with any other borrow
   When begin_exclusive_borrow succeeds, no other loans exist for that variable *)
val exclusive_conflicts : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (begin_exclusive_borrow x st) /\ well_formed st)
        (ensures length (loans_for_var x st) = 0)

(* Lemma: After move of linear variable, variable state is VsMoved *)
val move_makes_unavailable : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (check_move x st) /\
                  (match find_var x st with Some ve -> ve_mode ve = MOne | None -> false))
        (ensures (match check_move x st with
                  | Some st' ->
                      (match find_var x st' with
                       | Some ve' -> ve_state ve' = VsMoved
                       | None -> true)
                  | None -> true))

(* Lemma: Cannot move borrowed variable *)
val cannot_move_borrowed : x:var_id -> st:borrow_state ->
  Lemma (requires (match find_var x st with
                   | Some ve -> not (can_move_state (ve_state ve))
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
                   | Some ve -> VsBorrowedMut? (ve_state ve)
                   | None -> false))
        (ensures length (loans_for_var x st) = 1)

(* Lemma: Borrowed data outlives the borrow
   A loan cannot exist for a moved or dropped variable *)
val borrow_live : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st)
        (ensures (match find_var x st with
                  | Some ve -> (VsMoved? (ve_state ve) \/ VsDropped? (ve_state ve)) ==>
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
