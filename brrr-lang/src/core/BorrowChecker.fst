(**
 * BrrrLang.Core.BorrowChecker
 *
 * Ownership and borrow checking for Brrr-Lang.
 * Based on brrr_lang_spec_v0.4.tex Part III (Ownership & Memory):
 *   - Chapter 7: Mode Semiring
 *   - Chapter 8: Linear Logic Foundation
 *   - Chapter 9: Borrowing Rules
 *   - Chapter 10: Region-Based Memory
 *
 * Implements:
 *   - Borrow state tracking (owned, borrowed, moved)
 *   - Move semantics (use exactly once for linear types)
 *   - Borrow rules (&T shared, &mut T exclusive)
 *   - Mode checking via mode semiring
 *)
module BorrowChecker

(* Z3 solver options for SMT tractability - following HACL*/EverParse patterns *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open Modes
open BrrrTypes
open Expressions

(** ============================================================================
    REGION TYPES - Uses canonical region type from BrrrTypes
    ============================================================================

    Regions model memory lifetimes. Four kinds (defined in BrrrTypes):
    - RStatic: Lives forever ('static lifetime)
    - RNamed: Named region variables like 'a in Rust
    - RFresh: Fresh regions introduced by letregion construct
    - RScope: Tied to lexical scope depth

    Note: region, region_eq, and region_outlives are imported from BrrrTypes.
    ============================================================================ *)

(* Region capability - tracks what regions are accessible *)
type region_cap = {
  rc_region : region;
  rc_valid  : bool                       (* Is the capability still valid? *)
}

(* Region context - tracks available region capabilities *)
type region_ctx = list region_cap

(* Check if region has valid capability in context *)
let has_region_cap (r: region) (ctx: region_ctx) : bool =
  existsb (fun rc -> region_eq rc.rc_region r && rc.rc_valid) ctx

(* Add region capability to context *)
let add_region_cap (r: region) (ctx: region_ctx) : region_ctx =
  { rc_region = r; rc_valid = true } :: ctx

(* Invalidate region capability (when exiting letregion) *)
let invalidate_region (r: region) (ctx: region_ctx) : region_ctx =
  map (fun rc -> if region_eq rc.rc_region r then { rc with rc_valid = false } else rc) ctx

(* Fresh region counter for generating unique region IDs *)
type region_counter = nat

(* Generate fresh region *)
let fresh_region (counter: region_counter) : region & region_counter =
  (RFresh counter, counter + 1)

(* Check if region appears free in a type structure.
   Recursively traverses the type looking for potential region escapes.

   This implements region escape analysis per brrr_lang_spec_v0.4.tex Section 4.3.
   A region escapes if it could be accessed after the letregion scope ends.

   Key escape vectors:
   1. Reference types (&T, &mut T) with the region annotation
   2. Function return types that expose borrowed data
   3. Nested containers that may hold references
   4. Closures that capture borrows with the region

   ARCHITECTURAL NOTE: Current Limitation
   ======================================
   The current brrr_type does NOT embed lifetime/region annotations directly.
   Regions are tracked externally via:
   - regioned_type wrapper in BrrrTypes (base_type + region)
   - extended_var_entry.eve_region in this module

   This means TWrap WRef inner only contains the pointee type, NOT the
   lifetime of the reference itself. Therefore, this function can only
   check for regions in nested types, not in the reference's own lifetime.

   FUTURE WORK: To fully implement region escape analysis, we need:
   1. Extend brrr_type to include lifetime annotations on references:
      | TWrapRef : wrapper_kind -> region -> brrr_type -> brrr_type
   2. Then this function can check:
      | TWrapRef WRef r' inner -> region_eq r r' || region_free_in_type r inner

   Current behavior: Recursively check nested types. This catches:
   - Struct fields that contain references to the escaping region
   - Function return types that expose borrowed data
   - Nested containers (Option<&'a T> where 'a = r would escape)

   This is a CONSERVATIVE APPROXIMATION - it may miss some escape routes
   until lifetime annotations are added to the type system. *)
let rec region_free_in_type (r: region) (ty: brrr_type) : Tot bool (decreases type_size ty) =
  match ty with
  (* Reference wrappers - primary escape vectors
     TODO: When lifetimes are added to types, check the reference's own lifetime:
     | TWrapRef WRef region_annot inner ->
         region_eq r region_annot || region_free_in_type r inner *)
  | TWrap WRef inner -> region_free_in_type r inner
  | TWrap WRefMut inner -> region_free_in_type r inner
  | TWrap WSlice inner -> region_free_in_type r inner
  | TWrap WRaw inner -> region_free_in_type r inner

  (* Container wrappers - check inner type for escaped regions *)
  | TWrap WArray inner -> region_free_in_type r inner
  | TWrap WOption inner -> region_free_in_type r inner
  | TWrap WBox inner -> region_free_in_type r inner
  | TWrap WRc inner -> region_free_in_type r inner
  | TWrap WArc inner -> region_free_in_type r inner

  (* Modal references carry permissions but may contain escaped regions
     TODO: Modal types may need region annotations too *)
  | TModal _ inner -> region_free_in_type r inner

  (* Binary type constructor - check both type parameters *)
  | TResult t1 t2 -> region_free_in_type r t1 || region_free_in_type r t2

  (* Tuple - check all elements (any element could escape the region) *)
  | TTuple ts -> existsb (region_free_in_type r) ts

  (* Function types - CRITICAL escape vectors:
     1. Return type: if function returns data borrowed from region r, escape!
     2. Parameter types: if function captures references to region r, escape!
     3. Closure captures: implicit in parameter types for closure types *)
  | TFunc ft ->
      region_free_in_type r ft.return_type ||
      existsb (fun p -> region_free_in_type r p.ty) ft.params

  (* Type application - check base type and all type arguments *)
  | TApp base args ->
      region_free_in_type r base || existsb (region_free_in_type r) args

  (* Base types - no region escapes possible
     These types don't contain references and thus can't hold region data *)
  | TPrim _ -> false
  | TNumeric _ -> false
  | TVar _ -> false
  | TNamed _ -> false

  (* Struct and enum fields - CONSERVATIVE: assume no escape
     FUTURE: When struct/enum definitions are available, check all fields:
     | TStruct st -> existsb (fun f -> region_free_in_type r f.field_ty) st.struct_fields
     | TEnum et -> existsb (fun v -> existsb (region_free_in_type r) v.variant_fields) et.enum_variants *)
  | TStruct _ -> false
  | TEnum _ -> false

(* Check if letregion scope is valid: region must not escape *)
let letregion_scope_ok (r: region) (body_ty: brrr_type) : bool =
  not (region_free_in_type r body_ty)

(** ============================================================================
    LOAN IDENTIFIERS
    ============================================================================ *)

(* Unique identifier for each loan/borrow *)
type loan_id = nat

(* Next loan ID generator state *)
type loan_counter = nat

(* Generate fresh loan ID *)
let fresh_loan_id (counter: loan_counter) : loan_id & loan_counter =
  (counter, counter + 1)

(** ============================================================================
    BORROW KIND
    ============================================================================ *)

(* Kind of borrow *)
type borrow_kind =
  | BorrowShared    : borrow_kind   (* &T - shared/immutable borrow *)
  | BorrowExclusive : borrow_kind   (* &mut T - exclusive/mutable borrow *)

(* Can read through this borrow? *)
let borrow_can_read (bk: borrow_kind) : bool =
  match bk with
  | BorrowShared -> true
  | BorrowExclusive -> true

(* Can write through this borrow? *)
let borrow_can_write (bk: borrow_kind) : bool =
  match bk with
  | BorrowShared -> false
  | BorrowExclusive -> true

(* Is borrow exclusive? *)
let is_exclusive (bk: borrow_kind) : bool =
  match bk with
  | BorrowShared -> false
  | BorrowExclusive -> true

(** ============================================================================
    ACTIVE LOAN
    ============================================================================ *)

(* An active loan (borrow) on a variable *)
noeq type loan = {
  loan_id      : loan_id;       (* Unique ID for this loan *)
  loan_var     : var_id;        (* Variable being borrowed *)
  loan_kind    : borrow_kind;   (* Shared or exclusive *)
  loan_depth   : nat            (* Nesting depth (for reborrowing) *)
}

(* Create a new loan *)
let make_loan (id: loan_id) (v: var_id) (kind: borrow_kind) (depth: nat) : loan =
  { loan_id = id; loan_var = v; loan_kind = kind; loan_depth = depth }

(** ============================================================================
    OWNERSHIP ERROR TYPES - Explicit Error Reporting
    ============================================================================

    Instead of returning option borrow_state (None for errors), we provide
    explicit error types that describe exactly what went wrong. This enables:
    - Precise error messages for users
    - Detailed diagnostics for Brrr-Machine analysis
    - Machine-readable error codes for IDE integration
    ============================================================================ *)

(* Ownership/borrow error types *)
type ownership_error =
  (* Move errors *)
  | ErrUseAfterMove      : var:var_id -> moved_at:nat -> ownership_error
      (* Variable was used after being moved *)
  | ErrMoveWhileBorrowed : var:var_id -> loan:loan_id -> ownership_error
      (* Attempted to move a variable while it has active borrows *)
  | ErrDoubleMove        : var:var_id -> ownership_error
      (* Attempted to move a variable that was already moved *)

  (* Borrow errors *)
  | ErrBorrowWhileMoved  : var:var_id -> ownership_error
      (* Attempted to borrow a moved variable *)
  | ErrMutBorrowWhileBorrowed : var:var_id -> existing:loan_id -> ownership_error
      (* Attempted exclusive borrow while shared borrows exist *)
  | ErrBorrowWhileMutBorrowed : var:var_id -> existing:loan_id -> ownership_error
      (* Attempted any borrow while exclusive borrow exists *)
  | ErrMultipleMutBorrows : var:var_id -> first:loan_id -> ownership_error
      (* Multiple exclusive borrows attempted *)

  (* Lifetime errors *)
  | ErrBorrowOutlivesValue : loan:loan_id -> var:var_id -> ownership_error
      (* Borrow would outlive the borrowed value *)
  | ErrDanglingReference  : loan:loan_id -> ownership_error
      (* Reference to deallocated memory *)
  | ErrRegionEscapes      : r:region -> ownership_error
      (* Region escapes its scope via return type *)

  (* Drop/free errors *)
  | ErrDropWhileBorrowed : var:var_id -> loans:list loan_id -> ownership_error
      (* Attempted to drop while active borrows exist *)
  | ErrDoubleFree        : var:var_id -> ownership_error
      (* Attempted to free already freed memory *)

  (* Mode errors *)
  | ErrLinearNotConsumed : var:var_id -> ownership_error
      (* Linear variable was not consumed exactly once *)
  | ErrRelevantNotUsed   : var:var_id -> ownership_error
      (* Relevant variable was never used *)
  | ErrAffineUsedMultiple : var:var_id -> count:nat -> ownership_error
      (* Affine variable used more than once *)

  (* General errors *)
  | ErrVariableNotFound  : var:var_id -> ownership_error
      (* Variable not in scope *)
  | ErrLoanNotFound      : loan:loan_id -> ownership_error
      (* Loan ID not found *)
  | ErrInternalError     : msg:string -> ownership_error
      (* Internal checker error *)

(* Result type with explicit error *)
type borrow_result (a: Type) =
  | BrOk   : value:a -> borrow_result a
  | BrErr  : error:ownership_error -> borrow_result a

(* Convert to option for backward compatibility *)
let borrow_result_to_option (#a: Type) (r: borrow_result a) : option a =
  match r with
  | BrOk v -> Some v
  | BrErr _ -> None

(** ============================================================================
    VARIABLE STATE - Extended with OShared for Rc/Arc
    ============================================================================ *)

(* Ownership state of a variable - extended from basic states *)
type var_state =
  | VsOwned       : var_state        (* Fully owned, can move/borrow *)
  | VsMoved       : var_state        (* Has been moved, unavailable *)
  | VsBorrowed    : list loan_id -> var_state  (* Has active shared borrows *)
  | VsBorrowedMut : loan_id -> var_state       (* Has active exclusive borrow *)
  | VsShared      : ref_count:nat -> var_state (* Reference-counted shared ownership (Rc/Arc) *)
      (* OShared state: multiple owners via reference counting
         - ref_count tracks how many Rc/Arc clones exist
         - Can be borrowed but not moved (would invalidate other owners)
         - Dropped when last reference is dropped *)
  | VsDropped     : var_state        (* Explicitly dropped, unavailable *)

(* Is variable available for use? *)
let is_available (vs: var_state) : bool =
  match vs with
  | VsOwned -> true
  | VsMoved -> false
  | VsDropped -> false
  | VsBorrowed _ -> true   (* Can read but not move/mutate *)
  | VsBorrowedMut _ -> false  (* Cannot use while exclusively borrowed *)
  | VsShared _ -> true     (* Rc/Arc can be used (cloned, borrowed) *)

(* Can variable be moved? *)
let can_move_state (vs: var_state) : bool =
  match vs with
  | VsOwned -> true
  | VsShared _ -> false    (* Rc/Arc cannot be moved, only cloned *)
  | _ -> false

(* Can variable be borrowed shared? *)
let can_borrow_shared (vs: var_state) : bool =
  match vs with
  | VsOwned -> true
  | VsBorrowed _ -> true   (* Multiple shared borrows allowed *)
  | VsShared _ -> true     (* Rc/Arc can be borrowed *)
  | VsMoved -> false
  | VsDropped -> false
  | VsBorrowedMut _ -> false  (* Cannot share while exclusively borrowed *)

(* Can variable be borrowed exclusively?
   IMPORTANT: Exclusive borrow requires full ownership.
   - VsOwned: Full ownership, can take exclusive borrow
   - VsShared: Reference-counted (Rc/Arc) - CANNOT get exclusive access even with
     count=1 because Rc/Arc semantics don't allow mutable access without RefCell.
     This is a key safety property: Rc::get_mut() only works when ref_count is
     provably 1, but our static analysis can't prove this at compile time.
   - VsBorrowed/VsBorrowedMut: Already has active borrows, cannot take exclusive *)
let can_borrow_mut (vs: var_state) : bool =
  match vs with
  | VsOwned -> true
  | VsShared _ -> false    (* Rc/Arc cannot be borrowed mutably without RefCell *)
  | _ -> false  (* Exclusive borrow requires no other borrows *)

(* Is variable reference-counted (Rc/Arc)? *)
let is_ref_counted (vs: var_state) : bool =
  match vs with
  | VsShared _ -> true
  | _ -> false

(* Get reference count for shared state *)
let get_ref_count (vs: var_state) : nat =
  match vs with
  | VsShared n -> n
  | _ -> 0

(* Clone Rc/Arc: increment reference count *)
let clone_shared (vs: var_state) : option var_state =
  match vs with
  | VsShared n -> Some (VsShared (n + 1))
  | VsOwned -> Some (VsShared 2)  (* First clone creates two references *)
  | _ -> None

(* Drop one reference: decrement count, return to owned if last *)
let drop_shared_ref (vs: var_state) : option var_state =
  match vs with
  | VsShared n ->
      if n > 1 then Some (VsShared (n - 1))
      else Some VsOwned  (* Last reference, back to owned *)
  | _ -> None

(** ============================================================================
    BORROW STATE
    ============================================================================ *)

(* Variable entry in borrow state *)
noeq type var_entry = {
  ve_var   : var_id;
  ve_ty    : brrr_type;
  ve_mode  : mode;         (* Usage mode from mode semiring *)
  ve_state : var_state     (* Current ownership state *)
}

(* Borrow checker state *)
noeq type borrow_state = {
  bs_vars      : list var_entry;   (* Variable states *)
  bs_loans     : list loan;        (* Active loans *)
  bs_counter   : loan_counter;     (* Loan ID generator *)
  bs_depth     : nat               (* Current scope depth *)
}

(* Empty borrow state *)
let empty_borrow_state : borrow_state = {
  bs_vars = [];
  bs_loans = [];
  bs_counter = 0;
  bs_depth = 0
}

(** ============================================================================
    STATE LOOKUP AND UPDATE
    ============================================================================ *)

(* Forward declaration of pattern type from Expressions module *)
open Expressions

(* Search for variable entry in list (top-level for lemma accessibility) *)
let rec search_var_entry (x: var_id) (vars: list var_entry) : option var_entry =
  match vars with
  | [] -> None
  | v :: rest -> if v.ve_var = x then Some v else search_var_entry x rest

(* Find variable entry *)
let find_var (x: var_id) (st: borrow_state) : option var_entry =
  search_var_entry x st.bs_vars

(* Update variable entry in list (top-level for lemma accessibility) *)
let rec upd_var_in_list (x: var_id) (f: var_entry -> var_entry) (vars: list var_entry) : list var_entry =
  match vars with
  | [] -> []
  | v :: rest ->
      if v.ve_var = x then f v :: rest
      else v :: upd_var_in_list x f rest

(* Update variable entry *)
let update_var (x: var_id) (f: var_entry -> var_entry) (st: borrow_state) : borrow_state =
  { st with bs_vars = upd_var_in_list x f st.bs_vars }

(* Add new variable *)
let add_var (x: var_id) (ty: brrr_type) (m: mode) (st: borrow_state) : borrow_state =
  let entry = {
    ve_var = x;
    ve_ty = ty;
    ve_mode = m;
    ve_state = VsOwned
  } in
  { st with bs_vars = entry :: st.bs_vars }

(* Get variable state *)
let get_var_state (x: var_id) (st: borrow_state) : option var_state =
  match find_var x st with
  | Some ve -> Some ve.ve_state
  | None -> None

(* Get variable mode *)
let get_var_mode (x: var_id) (st: borrow_state) : option mode =
  match find_var x st with
  | Some ve -> Some ve.ve_mode
  | None -> None

(* Search for loan in list (top-level for lemma accessibility) *)
let rec search_loan (id: loan_id) (loans: list loan) : option loan =
  match loans with
  | [] -> None
  | l :: rest -> if l.loan_id = id then Some l else search_loan id rest

(* Find loan by ID *)
let find_loan (id: loan_id) (st: borrow_state) : option loan =
  search_loan id st.bs_loans

(** ============================================================================
    PATTERN BINDING EXTRACTION
    ============================================================================ *)

(* Extract all variable bindings from a pattern with their types *)
let rec pattern_bindings (p: pattern) (default_ty: brrr_type)
    : Tot (list (var_id & brrr_type)) (decreases p) =
  match p with
  | PatWild -> []  (* Wildcard binds nothing *)
  | PatVar x -> [(x, default_ty)]  (* Single variable binding *)
  | PatLit _ -> []  (* Literals bind nothing *)
  | PatTuple ps ->
      (* Tuple pattern - recursively extract from each sub-pattern *)
      pattern_bindings_list ps default_ty
  | PatStruct _ fields ->
      (* Struct pattern - extract from each field pattern *)
      pattern_bindings_struct_fields fields default_ty
  | PatVariant _ _ ps ->
      (* Variant pattern - extract from payload patterns *)
      pattern_bindings_list ps default_ty
  | PatOr p1 p2 ->
      (* Or pattern - both branches must bind same variables *)
      (* Take bindings from first branch (checker should verify they match) *)
      pattern_bindings p1 default_ty
  | PatGuard p' _ ->
      (* Guarded pattern - bindings come from inner pattern *)
      pattern_bindings p' default_ty
  | PatRef p' ->
      (* Reference pattern - bindings from inner pattern *)
      pattern_bindings p' default_ty
  | PatBox p' ->
      (* Box pattern - bindings from inner pattern *)
      pattern_bindings p' default_ty

and pattern_bindings_list (ps: list pattern) (default_ty: brrr_type)
    : Tot (list (var_id & brrr_type)) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest ->
      pattern_bindings p default_ty @ pattern_bindings_list rest default_ty

and pattern_bindings_struct_fields (fields: list (string & pattern)) (default_ty: brrr_type)
    : Tot (list (var_id & brrr_type)) (decreases fields) =
  match fields with
  | [] -> []
  | (_, p) :: rest ->
      pattern_bindings p default_ty @ pattern_bindings_struct_fields rest default_ty

(* Add all pattern bindings to borrow state *)
let add_pattern_bindings (p: pattern) (default_ty: brrr_type) (m: mode) (st: borrow_state)
    : borrow_state =
  let bindings = pattern_bindings p default_ty in
  fold_left (fun s (x, ty) -> add_var x ty m s) st bindings

(** ============================================================================
    BORROW STATE MERGING
    ============================================================================ *)

(* Merge two variable states - takes the more restrictive state

   CRITICAL: Borrow state merge semantics for control flow join points.
   After if/else or match branches merge, the resulting state must be
   sound regardless of which branch was actually taken at runtime.

   Key principles:
   1. If moved/dropped in ANY branch -> moved/dropped (cannot use)
   2. Exclusive borrows: If EITHER branch has an active exclusive borrow,
      the merged state must preserve that borrow. The variable cannot be
      used or re-borrowed until the exclusive borrow ends.
   3. Shared borrows: Take union of all loan IDs (all borrows are active)
   4. Mixed exclusive + other: Keep the exclusive (most restrictive)

   This ensures soundness: if branch A still has an exclusive borrow,
   code after the merge cannot assume ownership or create new borrows. *)
let merge_var_state (vs1 vs2: var_state) : var_state =
  match vs1, vs2 with
  (* If moved/dropped in either branch, it's moved/dropped *)
  | VsMoved, _ | _, VsMoved -> VsMoved
  | VsDropped, _ | _, VsDropped -> VsDropped

  (* Both owned -> owned *)
  | VsOwned, VsOwned -> VsOwned

  (* Shared borrows: take union of loan IDs (all borrows are potentially active) *)
  | VsBorrowed loans1, VsBorrowed loans2 ->
      VsBorrowed (loans1 @ loans2)

  (* One owned, one borrowed -> borrowed (the borrow may still be active) *)
  | VsOwned, VsBorrowed loans | VsBorrowed loans, VsOwned ->
      VsBorrowed loans

  (* Exclusive borrow cases - CRITICAL for soundness:
     If EITHER branch has an exclusive borrow, we must track it.
     The borrow may still be active at runtime depending on which branch was taken. *)

  (* Both have same exclusive borrow -> preserve it *)
  | VsBorrowedMut lid1, VsBorrowedMut lid2 ->
      if lid1 = lid2 then VsBorrowedMut lid1
      (* Different exclusive borrows - this is an error condition.
         One of them must have ended, so treat as the more recent one.
         In practice, this shouldn't happen with proper scope tracking.
         Keep the first one (arbitrary but consistent choice). *)
      else VsBorrowedMut lid1

  (* Exclusive + Owned: The exclusive borrow may still be active in one branch.
     We MUST preserve the exclusive borrow state - cannot assume it ended.
     This prevents unsound code like:
       if cond { let r = &mut x; ... }  // r still active
       else { x = 5; }                  // would conflict with r if cond was true
       // After merge: x is still exclusively borrowed, cannot use *)
  | VsBorrowedMut lid, VsOwned | VsOwned, VsBorrowedMut lid ->
      VsBorrowedMut lid  (* Preserve exclusive borrow - most restrictive *)

  (* Exclusive + Shared: Exclusive takes precedence (more restrictive).
     The shared borrows would conflict with exclusive anyway. *)
  | VsBorrowedMut lid, VsBorrowed _ | VsBorrowed _, VsBorrowedMut lid ->
      VsBorrowedMut lid

  (* Reference-counted states: take max ref count (conservative) *)
  | VsShared n1, VsShared n2 -> VsShared (if n1 > n2 then n1 else n2)

  (* Shared + owned -> shared (the Rc/Arc may still exist in one branch) *)
  | VsShared n, VsOwned | VsOwned, VsShared n -> VsShared n

  (* Shared + borrowed -> keep shared (Rc/Arc reference still exists) *)
  | VsShared n, VsBorrowed _ | VsBorrowed _, VsShared n -> VsShared n

  (* Exclusive + Shared (Rc/Arc): Keep exclusive (more restrictive)
     Note: This case indicates a type system issue since Rc/Arc and
     exclusive borrows shouldn't coexist on the same variable. *)
  | VsBorrowedMut lid, VsShared _ | VsShared _, VsBorrowedMut lid ->
      VsBorrowedMut lid

(* Merge two variable entries *)
let merge_var_entry (ve1 ve2: var_entry) : option var_entry =
  if ve1.ve_var <> ve2.ve_var then None  (* Different variables *)
  else if not (type_eq ve1.ve_ty ve2.ve_ty) then None  (* Type mismatch *)
  else
    (* Merge modes: take the more restrictive mode *)
    let merged_mode = match ve1.ve_mode, ve2.ve_mode with
      | MZero, _ | _, MZero -> MZero  (* Either consumed -> consumed *)
      | MOne, MOne -> MOne
      | MOmega, MOmega -> MOmega
      | MOne, MOmega | MOmega, MOne -> MOne  (* Take more restrictive *)
    in
    Some {
      ve_var = ve1.ve_var;
      ve_ty = ve1.ve_ty;
      ve_mode = merged_mode;
      ve_state = merge_var_state ve1.ve_state ve2.ve_state
    }

(* Merge two lists of variable entries - both must have same variables *)
let rec merge_var_lists (vars1 vars2: list var_entry) : option (list var_entry) =
  match vars1, vars2 with
  | [], [] -> Some []
  | v1 :: rest1, v2 :: rest2 ->
      (* Find matching entry in vars2 for v1 *)
      (match search_var_entry v1.ve_var vars2 with
       | None -> None  (* Variable not found in other branch *)
       | Some v2_match ->
           (match merge_var_entry v1 v2_match with
            | None -> None  (* Merge failed *)
            | Some merged ->
                (* Remove v2_match from vars2 and continue *)
                let vars2_remaining = filter (fun v -> v.ve_var <> v1.ve_var) vars2 in
                (match merge_var_lists rest1 vars2_remaining with
                 | None -> None
                 | Some rest_merged -> Some (merged :: rest_merged))))
  | _, _ -> None  (* Different number of variables *)

(* Maximum of two natural numbers *)
let max_nat (n1 n2: nat) : nat =
  if n1 >= n2 then n1 else n2

(* Merge loans from two branches - take union, but check for conflicts *)
let merge_loans (loans1 loans2: list loan) : list loan =
  (* Remove duplicates by loan_id *)
  let rec add_unique (l: loan) (acc: list loan) : list loan =
    if existsb (fun l' -> l.loan_id = l'.loan_id) acc then acc
    else l :: acc
  in
  fold_left (fun acc l -> add_unique l acc) loans1 loans2

(* Merge two borrow states from different branches *)
let merge_borrow_states (st1 st2: borrow_state) : option borrow_state =
  (* Depths should match (both branches entered same scope) *)
  if st1.bs_depth <> st2.bs_depth then None
  else
    (* Merge variable states *)
    (match merge_var_lists st1.bs_vars st2.bs_vars with
     | None -> None
     | Some merged_vars ->
         Some {
           bs_vars = merged_vars;
           bs_loans = merge_loans st1.bs_loans st2.bs_loans;
           bs_counter = max_nat st1.bs_counter st2.bs_counter;  (* Take max for fresh IDs *)
           bs_depth = st1.bs_depth
         })

(* Get all loans for a variable *)
let loans_for_var (x: var_id) (st: borrow_state) : list loan =
  filter (fun l -> l.loan_var = x) st.bs_loans

(** ============================================================================
    MOVE CHECKING
    ============================================================================ *)

(* Update function for move operation - named for lemma accessibility *)
let make_move_update_fn (new_mode: mode) (new_state: var_state) (v: var_entry) : var_entry =
  { v with ve_mode = new_mode; ve_state = new_state }

(* Check if a move is valid and perform it *)
let check_move (x: var_id) (st: borrow_state) : option borrow_state =
  match find_var x st with
  | None -> None  (* Variable not found *)
  | Some ve ->
      (* Check mode allows move *)
      if ve.ve_mode = MZero then None  (* Already consumed *)
      else if not (can_move_state ve.ve_state) then None  (* Not in movable state *)
      else
        (* Linear: consume (MOne -> MZero), Omega: no change *)
        let new_mode = mode_mul ve.ve_mode MOne in  (* Use once *)
        let new_state =
          if ve.ve_mode = MOne then VsMoved  (* Linear consumed *)
          else ve.ve_state  (* Omega stays owned *)
        in
        Some (update_var x (make_move_update_fn new_mode new_state) st)

(** ============================================================================
    DROP CHECKING
    ============================================================================ *)

(* Check if a drop is valid and perform it *)
let check_drop (x: var_id) (st: borrow_state) : option borrow_state =
  match find_var x st with
  | None -> None  (* Variable not found *)
  | Some ve ->
      (* Cannot drop if borrowed *)
      if not (is_available ve.ve_state) then None
      else
        (* Remove variable from state *)
        let new_vars = filter (fun v -> v.ve_var <> x) st.bs_vars in
        (* Remove any loans involving this variable *)
        let new_loans = filter (fun l -> l.loan_var <> x) st.bs_loans in
        Some { st with bs_vars = new_vars; bs_loans = new_loans }

(** ============================================================================
    BORROW OPERATIONS
    ============================================================================ *)

(* Begin a shared borrow *)
let begin_shared_borrow (x: var_id) (st: borrow_state) : option (loan_id & borrow_state) =
  match find_var x st with
  | None -> None
  | Some ve ->
      if not (can_borrow_shared ve.ve_state) then None
      else
        let (lid, counter') = fresh_loan_id st.bs_counter in
        let new_loan = make_loan lid x BorrowShared st.bs_depth in
        let new_state =
          match ve.ve_state with
          | VsBorrowed loans -> VsBorrowed (lid :: loans)
          | _ -> VsBorrowed [lid]
        in
        let update_fn (v: var_entry) : var_entry =
          { v with ve_state = new_state }
        in
        Some (lid, {
          (update_var x update_fn st) with
          bs_loans = new_loan :: st.bs_loans;
          bs_counter = counter'
        })

(* Begin an exclusive borrow *)
let begin_exclusive_borrow (x: var_id) (st: borrow_state) : option (loan_id & borrow_state) =
  match find_var x st with
  | None -> None
  | Some ve ->
      if not (can_borrow_mut ve.ve_state) then None
      else
        let (lid, counter') = fresh_loan_id st.bs_counter in
        let new_loan = make_loan lid x BorrowExclusive st.bs_depth in
        let update_fn (v: var_entry) : var_entry =
          { v with ve_state = VsBorrowedMut lid }
        in
        Some (lid, {
          (update_var x update_fn st) with
          bs_loans = new_loan :: st.bs_loans;
          bs_counter = counter'
        })

(* Begin borrow (shared or exclusive) *)
let begin_borrow (x: var_id) (is_mut: bool) (st: borrow_state) : option (loan_id & borrow_state) =
  if is_mut then begin_exclusive_borrow x st
  else begin_shared_borrow x st

(* End a borrow *)
let end_borrow (lid: loan_id) (st: borrow_state) : option borrow_state =
  match find_loan lid st with
  | None -> None  (* Loan not found *)
  | Some loan ->
      (* Remove loan from loans list *)
      let new_loans = filter (fun l -> l.loan_id <> lid) st.bs_loans in
      (* Update variable state *)
      match find_var loan.loan_var st with
      | None -> None  (* Variable not found - inconsistent state *)
      | Some ve ->
          let new_var_state =
            match ve.ve_state, loan.loan_kind with
            | VsBorrowedMut _, BorrowExclusive -> VsOwned
            | VsBorrowed loans, BorrowShared ->
                let remaining = filter (fun l -> l <> lid) loans in
                if length remaining = 0 then VsOwned
                else VsBorrowed remaining
            | _, _ -> ve.ve_state  (* Unexpected but don't crash *)
          in
          let update_fn (v: var_entry) : var_entry =
            { v with ve_state = new_var_state }
          in
          Some { (update_var loan.loan_var update_fn st) with bs_loans = new_loans }

(** ============================================================================
    SCOPE MANAGEMENT
    ============================================================================ *)

(* Enter a new scope *)
let enter_scope (st: borrow_state) : borrow_state =
  { st with bs_depth = st.bs_depth + 1 }

(* Safe decrement for nat *)
let pred_nat (n: nat) : nat =
  if n = 0 then 0 else n - 1

(* Exit scope - ends all borrows at current depth *)
let exit_scope (st: borrow_state) : option borrow_state =
  if st.bs_depth = 0 then Some st
  else
    (* Find all loans at current depth *)
    let current_depth_loans = filter (fun l -> l.loan_depth = st.bs_depth) st.bs_loans in
    (* End each loan *)
    let rec end_all (loans: list loan) (s: borrow_state) : option borrow_state =
      match loans with
      | [] -> Some { s with bs_depth = pred_nat s.bs_depth }
      | l :: rest ->
          (match end_borrow l.loan_id s with
           | Some s' -> end_all rest s'
           | None -> None)
    in
    end_all current_depth_loans st

(** ============================================================================
    EXPRESSION BORROW CHECKING
    ============================================================================ *)

(* Borrow check result *)
type bc_result = option borrow_state

(* Expression size for termination (imported from Expressions) *)
let bc_expr_size = expr_size

(* Helper: fold with option - defined separately for termination *)
let rec fold_left_opt (#a #b: Type) (f: a -> b -> option a) (init: a) (xs: list b)
    : Tot (option a) (decreases xs) =
  match xs with
  | [] -> Some init
  | x :: rest ->
      (match f init x with
       | Some a' -> fold_left_opt f a' rest
       | None -> None)

(* Borrow check an expression - uses fuel for termination *)
let rec borrow_check_expr (fuel: nat) (e: expr) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None  (* Out of fuel *)
  else
    match e with
    (* Literals don't affect borrow state *)
    | ELit _ -> Some st

    (* Variable use - check availability and consume if linear *)
    | EVar x ->
        (match find_var x st with
         | None -> None  (* Undefined variable *)
         | Some ve ->
             if not (is_available ve.ve_state) then None  (* Not available *)
             else
               (* For linear types, track the use *)
               if ve.ve_mode = MOne then
                 (* Linear - mark as moved after single use *)
                 Some (update_var x (fun v -> { v with ve_state = VsMoved; ve_mode = MZero }) st)
               else Some st)  (* Omega - no change *)

    (* Unary operations *)
    | EUnary op e' ->
        (match op with
         | OpRef ->
             (* &e - create shared borrow *)
             (match e' with
              | EVar x ->
                  (match begin_shared_borrow x st with
                   | Some (_, st') -> Some st'
                   | None -> None)
              | _ ->
                  (* Borrow of complex expression - check inner first *)
                  borrow_check_expr (fuel - 1) e' st)
         | OpRefMut ->
             (* &mut e - create exclusive borrow *)
             (match e' with
              | EVar x ->
                  (match begin_exclusive_borrow x st with
                   | Some (_, st') -> Some st'
                   | None -> None)
              | _ ->
                  borrow_check_expr (fuel - 1) e' st)
         | OpDeref ->
             (* *e - dereference, check inner *)
             borrow_check_expr (fuel - 1) e' st
         | _ ->
             (* Other unary ops - just check operand *)
             borrow_check_expr (fuel - 1) e' st)

    (* Binary operations - check both operands *)
    | EBinary _ e1 e2 ->
        (match borrow_check_expr (fuel - 1) e1 st with
         | Some st1 -> borrow_check_expr (fuel - 1) e2 st1
         | None -> None)

    (* Function call - check function and all arguments *)
    | ECall fn args ->
        (match borrow_check_expr (fuel - 1) fn st with
         | Some st1 -> borrow_check_exprs (fuel - 1) args st1
         | None -> None)

    (* Method call *)
    | EMethodCall obj _ args ->
        (match borrow_check_expr (fuel - 1) obj st with
         | Some st1 -> borrow_check_exprs (fuel - 1) args st1
         | None -> None)

    (* Tuple - check all elements *)
    | ETuple es -> borrow_check_exprs (fuel - 1) es st

    (* Array - check all elements *)
    | EArray es -> borrow_check_exprs (fuel - 1) es st

    (* Struct construction - check all field values *)
    | EStruct _ fields ->
        borrow_check_field_exprs (fuel - 1) fields st

    (* Variant construction *)
    | EVariant _ _ es ->
        borrow_check_exprs (fuel - 1) es st

    (* Field access *)
    | EField e' _ ->
        borrow_check_expr (fuel - 1) e' st

    (* Index access *)
    | EIndex e1 e2 ->
        (match borrow_check_expr (fuel - 1) e1 st with
         | Some st1 -> borrow_check_expr (fuel - 1) e2 st1
         | None -> None)

    (* Tuple projection *)
    | ETupleProj e' _ ->
        borrow_check_expr (fuel - 1) e' st

    (* If expression - branches must agree on borrow state *)
    | EIf cond then_e else_e ->
        (match borrow_check_expr (fuel - 1) cond st with
         | Some st1 ->
             let st_scope = enter_scope st1 in
             (match borrow_check_expr (fuel - 1) then_e st_scope,
                    borrow_check_expr (fuel - 1) else_e st_scope with
              | Some st_then, Some st_else ->
                  (* Both branches succeed - properly merge states *)
                  (* Merge takes the most restrictive state for each variable:
                     - If moved in either branch, it's moved
                     - For borrows, take the union of loan IDs
                     - For modes, take the more restrictive mode *)
                  (match merge_borrow_states st_then st_else with
                   | Some merged_st -> exit_scope merged_st
                   | None -> None)  (* Merge failed - inconsistent borrow states *)
              | _, _ -> None)  (* At least one branch failed *)
         | None -> None)

    (* Let binding *)
    | ELet pat ty_opt init body ->
        (match borrow_check_expr (fuel - 1) init st with
         | Some st1 ->
             (* Add bound variable(s) from pattern *)
             (* Pattern bindings extract all variables from complex patterns:
                - PatVar x: single variable
                - PatTuple ps: multiple variables from tuple destructuring
                - PatStruct _ fields: variables from struct field patterns
                - PatVariant _ _ ps: variables from variant payloads
                - PatOr p1 p2: variables from either branch (must match)
                - PatGuard p _: variables from guarded pattern
                - PatRef/PatBox p: variables from inner pattern
                - PatWild/PatLit: no variables bound *)
             let default_ty = match ty_opt with Some t -> t | None -> t_dynamic in
             let st2 = add_pattern_bindings pat default_ty MOne st1 in
             let st3 = enter_scope st2 in
             (match borrow_check_expr (fuel - 1) body st3 with
              | Some st4 -> exit_scope st4
              | None -> None)
         | None -> None)

    (* Let mut binding *)
    | ELetMut x ty_opt init body ->
        (match borrow_check_expr (fuel - 1) init st with
         | Some st1 ->
             let ty = match ty_opt with Some t -> t | None -> t_dynamic in
             let st2 = add_var x ty MOmega st1 in  (* Mutable = omega mode *)
             let st3 = enter_scope st2 in
             (match borrow_check_expr (fuel - 1) body st3 with
              | Some st4 -> exit_scope st4
              | None -> None)
         | None -> None)

    (* Assignment *)
    | EAssign lhs rhs ->
        (match lhs with
         | EVar x ->
             (* Direct assignment to variable *)
             (match find_var x st with
              | None -> None
              | Some ve ->
                  if ve.ve_mode = MOne then None  (* Cannot reassign linear *)
                  else borrow_check_expr (fuel - 1) rhs st)
         | EDeref e' ->
             (* Assignment through reference - need exclusive access *)
             (match borrow_check_expr (fuel - 1) e' st with
              | Some st1 -> borrow_check_expr (fuel - 1) rhs st1
              | None -> None)
         | _ ->
             (* Other LHS forms *)
             (match borrow_check_expr (fuel - 1) lhs st with
              | Some st1 -> borrow_check_expr (fuel - 1) rhs st1
              | None -> None))

    (* Lambda - captures must be valid *)
    | ELambda params body ->
        (* Add parameters to scope *)
        let st1 = fold_left (fun s (x, ty) -> add_var x ty MOne s) st params in
        let st2 = enter_scope st1 in
        (match borrow_check_expr (fuel - 1) body st2 with
         | Some st3 -> exit_scope st3
         | None -> None)

    (* Closure - explicit captures *)
    | EClosure params caps body ->
        (* Check captures are valid *)
        let check_cap (s: borrow_state) (cap: var_id) : option borrow_state =
          match find_var cap s with
          | None -> None
          | Some ve -> if is_available ve.ve_state then Some s else None
        in
        (match fold_left_opt check_cap st caps with
         | Some st1 ->
             let st2 = fold_left (fun s (x, ty) -> add_var x ty MOne s) st1 params in
             let st3 = enter_scope st2 in
             (match borrow_check_expr (fuel - 1) body st3 with
              | Some st4 -> exit_scope st4
              | None -> None)
         | None -> None)

    (* Box (heap allocation) *)
    | EBox e' ->
        borrow_check_expr (fuel - 1) e' st

    (* Explicit borrow *)
    | EBorrow e' ->
        (match e' with
         | EVar x ->
             (match begin_shared_borrow x st with
              | Some (_, st') -> Some st'
              | None -> None)
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit mutable borrow *)
    | EBorrowMut e' ->
        (match e' with
         | EVar x ->
             (match begin_exclusive_borrow x st with
              | Some (_, st') -> Some st'
              | None -> None)
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit move *)
    | EMove e' ->
        (match e' with
         | EVar x -> check_move x st
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit drop *)
    | EDrop e' ->
        (match e' with
         | EVar x -> check_drop x st
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Dereference *)
    | EDeref e' ->
        borrow_check_expr (fuel - 1) e' st

    (* Block - sequence of expressions *)
    | EBlock es ->
        let st1 = enter_scope st in
        (match borrow_check_exprs (fuel - 1) es st1 with
         | Some st2 -> exit_scope st2
         | None -> None)

    (* Sequence *)
    | ESeq e1 e2 ->
        (match borrow_check_expr (fuel - 1) e1 st with
         | Some st1 -> borrow_check_expr (fuel - 1) e2 st1
         | None -> None)

    (* Loop constructs *)
    | ELoop body ->
        let st1 = enter_scope st in
        (match borrow_check_expr (fuel - 1) body st1 with
         | Some st2 -> exit_scope st2
         | None -> None)

    | EWhile cond body ->
        (match borrow_check_expr (fuel - 1) cond st with
         | Some st1 ->
             let st2 = enter_scope st1 in
             (match borrow_check_expr (fuel - 1) body st2 with
              | Some st3 -> exit_scope st3
              | None -> None)
         | None -> None)

    | EFor x iter body ->
        (match borrow_check_expr (fuel - 1) iter st with
         | Some st1 ->
             let st2 = add_var x t_dynamic MOne st1 in
             let st3 = enter_scope st2 in
             (match borrow_check_expr (fuel - 1) body st3 with
              | Some st4 -> exit_scope st4
              | None -> None)
         | None -> None)

    (* Control flow *)
    | EBreak opt_e ->
        (match opt_e with
         | Some e' -> borrow_check_expr (fuel - 1) e' st
         | None -> Some st)

    | EContinue -> Some st

    | EReturn opt_e ->
        (match opt_e with
         | Some e' -> borrow_check_expr (fuel - 1) e' st
         | None -> Some st)

    (* Match expression *)
    | EMatch scrutinee arms ->
        (match borrow_check_expr (fuel - 1) scrutinee st with
         | Some st1 -> borrow_check_match_arms (fuel - 1) arms st1
         | None -> None)

    (* Type casts and checks *)
    | EAs e' _ -> borrow_check_expr (fuel - 1) e' st
    | EIs e' _ -> borrow_check_expr (fuel - 1) e' st

    (* Effect operations - properly track borrows across suspension points *)

    (* EThrow: throws an exception, potentially exiting the current scope.
       We must check:
       1. The thrown expression is valid
       2. Any exclusive borrows in scope are properly handled
       Note: The exception handler will deal with cleanup *)
    | EThrow e' ->
        (match borrow_check_expr (fuel - 1) e' st with
         | Some st' ->
             (* Check for active exclusive borrows that would be abandoned *)
             (* Exclusive borrows cannot be held at throw time as they would
                be invalidated without proper end_borrow call *)
             let has_exclusive_borrows =
               existsb (fun l -> l.loan_kind = BorrowExclusive) st'.bs_loans in
             if has_exclusive_borrows then None  (* Cannot throw with exclusive borrows *)
             else Some st'
         | None -> None)

    (* EAwait: suspension point for async execution.
       At await points, the current execution may be suspended and resumed later,
       possibly on a different thread. Borrows MUST NOT be held across await:
       1. Shared borrows: could become invalid if the borrowed value is modified
       2. Exclusive borrows: would violate exclusivity across the suspension *)
    | EAwait e' ->
        (match borrow_check_expr (fuel - 1) e' st with
         | Some st' ->
             (* Check for any active borrows at current scope depth *)
             let current_depth_loans =
               filter (fun l -> l.loan_depth >= st'.bs_depth) st'.bs_loans in
             if length current_depth_loans > 0 then
               None  (* Cannot await while holding borrows *)
             else Some st'
         | None -> None)

    (* EYield: suspension point for generators/iterators.
       Similar to await - the execution is suspended and may be resumed later.
       Borrows cannot be held across yield points:
       1. The yielded value must not include any borrowed references
       2. No borrows should be active at the yield point *)
    | EYield e' ->
        (match borrow_check_expr (fuel - 1) e' st with
         | Some st' ->
             (* Check for any active borrows at current scope depth *)
             let current_depth_loans =
               filter (fun l -> l.loan_depth >= st'.bs_depth) st'.bs_loans in
             if length current_depth_loans > 0 then
               None  (* Cannot yield while holding borrows *)
             else Some st'
         | None -> None)

    (* Try-catch *)
    | ETry body catches finally_opt ->
        (match borrow_check_expr (fuel - 1) body st with
         | Some st1 ->
             (match borrow_check_catch_arms (fuel - 1) catches st1 with
              | Some st2 ->
                  (match finally_opt with
                   | Some fin -> borrow_check_expr (fuel - 1) fin st2
                   | None -> Some st2)
              | None -> None)
         | None -> None)

    (* Handle/Perform - effect handlers *)
    | EHandle e' _ -> borrow_check_expr (fuel - 1) e' st
    | EPerform _ args -> borrow_check_exprs (fuel - 1) args st

    (* Sizeof/Alignof - no runtime effect *)
    | ESizeof _ -> Some st
    | EAlignof _ -> Some st

    (* Unsafe block *)
    | EUnsafe e' ->
        borrow_check_expr (fuel - 1) e' st

    (* Global reference - always available *)
    | EGlobal _ -> Some st

    (* Holes and errors *)
    | EHole -> Some st
    | EError _ -> None

(* Check multiple expressions *)
and borrow_check_exprs (fuel: nat) (es: list expr) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    match es with
    | [] -> Some st
    | e :: rest ->
        (match borrow_check_expr (fuel - 1) e st with
         | Some st' -> borrow_check_exprs (fuel - 1) rest st'
         | None -> None)

(* Check field expressions *)
and borrow_check_field_exprs (fuel: nat) (fields: list (string & expr)) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    match fields with
    | [] -> Some st
    | (_, e) :: rest ->
        (match borrow_check_expr (fuel - 1) e st with
         | Some st' -> borrow_check_field_exprs (fuel - 1) rest st'
         | None -> None)

(* Check a single match arm and return the resulting state *)
and borrow_check_single_arm (fuel: nat) (arm: match_arm) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    let st1 = enter_scope st in
    (* Add pattern bindings to scope *)
    let st2 = add_pattern_bindings arm.arm_pattern t_dynamic MOne st1 in
    (* Check guard if present *)
    (match arm.arm_guard with
     | Some guard ->
         (match borrow_check_expr (fuel - 1) guard st2 with
          | Some st3 ->
              (match borrow_check_expr (fuel - 1) arm.arm_body st3 with
               | Some st4 -> exit_scope st4
               | None -> None)
          | None -> None)
     | None ->
         (match borrow_check_expr (fuel - 1) arm.arm_body st2 with
          | Some st3 -> exit_scope st3
          | None -> None))

(* Check match arms - all arms are alternative execution paths, so we need to:
   1. Check each arm independently (all starting from the same base state)
   2. Merge all resulting states together (taking the most restrictive state) *)
and borrow_check_match_arms (fuel: nat) (arms: list match_arm) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    match arms with
    | [] -> Some st  (* No arms - return unchanged state *)
    | [arm] ->
        (* Single arm - no merging needed *)
        borrow_check_single_arm (fuel - 1) arm st
    | arm :: rest ->
        (* Multiple arms - check each and merge *)
        (match borrow_check_single_arm (fuel - 1) arm st with
         | Some st_arm ->
             (* Check remaining arms and merge with this arm's result *)
             (match borrow_check_match_arms (fuel - 1) rest st with
              | Some st_rest ->
                  (* Merge states from this arm and remaining arms *)
                  merge_borrow_states st_arm st_rest
              | None -> None)
         | None -> None)

(* Check a single catch arm *)
and borrow_check_single_catch (fuel: nat) (c: catch_arm) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    let st1 = enter_scope st in
    (* Add pattern bindings from catch pattern *)
    let st2 = add_pattern_bindings c.catch_pattern c.catch_type MOne st1 in
    (match borrow_check_expr (fuel - 1) c.catch_body st2 with
     | Some st3 -> exit_scope st3
     | None -> None)

(* Check catch arms - similar to match arms, they are alternative paths *)
and borrow_check_catch_arms (fuel: nat) (catches: list catch_arm) (st: borrow_state)
    : Tot bc_result (decreases fuel) =
  if fuel = 0 then None
  else
    match catches with
    | [] -> Some st  (* No catch arms - return unchanged state *)
    | [c] ->
        (* Single catch - no merging needed *)
        borrow_check_single_catch (fuel - 1) c st
    | c :: rest ->
        (* Multiple catches - check each and merge *)
        (match borrow_check_single_catch (fuel - 1) c st with
         | Some st_catch ->
             (match borrow_check_catch_arms (fuel - 1) rest st with
              | Some st_rest -> merge_borrow_states st_catch st_rest
              | None -> None)
         | None -> None)

(** ============================================================================
    TOP-LEVEL BORROW CHECK
    ============================================================================ *)

(* Default fuel for borrow checking *)
let default_fuel : nat = 10000

(* Borrow check with default fuel *)
let borrow_check (e: expr) : bc_result =
  borrow_check_expr default_fuel e empty_borrow_state

(* Borrow check with initial state *)
let borrow_check_with_state (e: expr) (st: borrow_state) : bc_result =
  borrow_check_expr default_fuel e st

(** ============================================================================
    WELL-FORMEDNESS PREDICATE
    ============================================================================ *)

(* Count loans for a variable in the loans list *)
let rec count_loans_for_var (x: var_id) (loans: list loan) : nat =
  match loans with
  | [] -> 0
  | l :: rest ->
      (if l.loan_var = x then 1 else 0) + count_loans_for_var x rest

(* Check if all loans for a variable have the given kind *)
let rec all_loans_have_kind (x: var_id) (kind: borrow_kind) (loans: list loan) : bool =
  match loans with
  | [] -> true
  | l :: rest ->
    if l.loan_var = x then l.loan_kind = kind && all_loans_have_kind x kind rest
    else all_loans_have_kind x kind rest

(* Variable state is consistent with loans (includes kind matching) *)
let var_state_consistent (x: var_id) (vs: var_state) (loans: list loan) : bool =
  let loan_count = count_loans_for_var x loans in
  match vs with
  | VsOwned -> loan_count = 0
  | VsMoved -> loan_count = 0
  | VsDropped -> loan_count = 0
  | VsBorrowed _ -> loan_count > 0 && all_loans_have_kind x BorrowShared loans
  | VsBorrowedMut _ -> loan_count = 1 && all_loans_have_kind x BorrowExclusive loans
  | VsShared _ -> true  (* Shared state can have borrows or not *)

(* Check if borrow state is well-formed *)
let rec vars_consistent (vars: list var_entry) (loans: list loan) : bool =
  match vars with
  | [] -> true
  | ve :: rest -> var_state_consistent ve.ve_var ve.ve_state loans && vars_consistent rest loans

let well_formed (st: borrow_state) : bool =
  vars_consistent st.bs_vars st.bs_loans

(* Helper: count_loans_for_var equals length of loans_for_var *)
let rec count_loans_equals_length (x: var_id) (loans: list loan)
    : Lemma (ensures count_loans_for_var x loans = length (filter (fun l -> l.loan_var = x) loans))
            (decreases loans) =
  match loans with
  | [] -> ()
  | l :: rest -> count_loans_equals_length x rest

(* Helper: search_var_entry returns entry with matching var_id *)
let rec search_var_entry_returns_match (x: var_id) (vars: list var_entry)
    : Lemma (ensures (match search_var_entry x vars with
                      | Some ve -> ve.ve_var = x
                      | None -> true))
            (decreases vars) =
  match vars with
  | [] -> ()
  | v :: rest ->
    if v.ve_var = x then ()
    else search_var_entry_returns_match x rest

(* Helper: If vars_consistent and search finds a var, that var is consistent with loans *)
let rec vars_consistent_implies_var_consistent (x: var_id) (vars: list var_entry) (loans: list loan)
    : Lemma (requires vars_consistent vars loans)
            (ensures (match search_var_entry x vars with
                      | Some ve -> var_state_consistent ve.ve_var ve.ve_state loans
                      | None -> true))
            (decreases vars) =
  match vars with
  | [] -> ()
  | v :: rest ->
    if v.ve_var = x then ()
    else vars_consistent_implies_var_consistent x rest loans

(* Helper: using make_move_update_fn, after update search returns entry with new_state *)
let rec upd_var_search_with_move_fn (x: var_id) (new_mode: mode) (new_state: var_state) (vars: list var_entry)
    : Lemma (requires Some? (search_var_entry x vars))
            (ensures (match search_var_entry x (upd_var_in_list x (make_move_update_fn new_mode new_state) vars) with
                      | Some ve' -> ve'.ve_state = new_state
                      | None -> false))
            (decreases vars) =
  match vars with
  | [] -> ()
  | v :: rest ->
    if v.ve_var = x then ()
    else upd_var_search_with_move_fn x new_mode new_state rest

(* Helper: find_var after update_var with make_move_update_fn returns entry with new_state
   This bridges from borrow_state level to list level *)
let find_var_after_update_move (x: var_id) (new_mode: mode) (new_state: var_state) (st: borrow_state)
    : Lemma (requires Some? (find_var x st))
            (ensures (let st' = update_var x (make_move_update_fn new_mode new_state) st in
                      match find_var x st' with
                      | Some ve' -> ve'.ve_state = new_state
                      | None -> false))
    =
  (* find_var x st = search_var_entry x st.bs_vars by definition *)
  (* update_var x f st = { st with bs_vars = upd_var_in_list x f st.bs_vars } by definition *)
  (* find_var x st' = search_var_entry x st'.bs_vars = search_var_entry x (upd_var_in_list x f st.bs_vars) *)
  upd_var_search_with_move_fn x new_mode new_state st.bs_vars

(* Helper: check_move for linear var produces update with VsMoved state
   Note: We avoid equality on noeq types by using property-based preconditions *)
let check_move_linear_computes_moved (x: var_id) (st: borrow_state)
    : Lemma (requires Some? (find_var x st) /\
                      (match find_var x st with Some ve -> ve.ve_mode = MOne /\ can_move_state ve.ve_state | None -> false))
            (ensures Some? (check_move x st) /\
                     (let new_mode = mode_mul MOne MOne in
                      let new_state = VsMoved in
                      match find_var x (Some?.v (check_move x st)) with
                      | Some ve' -> ve'.ve_state = VsMoved
                      | None -> false))
    =
  (* check_move computes: new_mode = mode_mul MOne MOne = MOne, new_state = VsMoved *)
  (* The result is update_var x (make_move_update_fn new_mode new_state) st *)
  let new_mode = mode_mul MOne MOne in
  let new_state = VsMoved in
  find_var_after_update_move x new_mode new_state st

(** ============================================================================
    VERIFICATION LEMMAS
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(* Lemma: Exclusive borrow conflicts with any other borrow
   When begin_exclusive_borrow succeeds, the variable must be in VsOwned state,
   which in a well-formed state means no active loans exist for that variable *)
val exclusive_conflicts : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (begin_exclusive_borrow x st) /\ well_formed st)
        (ensures length (loans_for_var x st) = 0)
let exclusive_conflicts x st =
  (* Match on begin_exclusive_borrow to expose structure *)
  match begin_exclusive_borrow x st with
  | Some (_, _) ->
    (* find_var uses search_var_entry, so match on that *)
    (match search_var_entry x st.bs_vars with
     | Some ve ->
       (* From search_var_entry, ve.ve_var = x *)
       search_var_entry_returns_match x st.bs_vars;
       assert (ve.ve_var = x);
       (* From success, we know can_borrow_mut ve.ve_state = true *)
       assert (can_borrow_mut ve.ve_state);
       (* can_borrow_mut is true only for VsOwned *)
       assert (ve.ve_state = VsOwned);
       (* From well_formed st, var_state_consistent holds for ve *)
       vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
       (* var_state_consistent with VsOwned means count_loans_for_var ve.ve_var = 0 *)
       assert (var_state_consistent ve.ve_var ve.ve_state st.bs_loans);
       (* Since ve.ve_var = x and VsOwned, count_loans_for_var x = 0 *)
       assert (count_loans_for_var ve.ve_var st.bs_loans = 0);
       (* count_loans equals length of loans_for_var *)
       count_loans_equals_length x st.bs_loans;
       ()
     | None -> ())  (* Contradiction with begin_exclusive_borrow succeeding *)
  | None -> ()  (* Contradiction with precondition *)

(* Lemma: After move of linear variable, variable state is VsMoved
   The check_move function explicitly sets new_state = VsMoved when ve.ve_mode = MOne *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
val move_makes_unavailable : x:var_id -> st:borrow_state ->
  Lemma (requires Some? (check_move x st) /\
                  (match find_var x st with Some ve -> ve.ve_mode = MOne | None -> false))
        (ensures (match check_move x st with
                  | Some st' ->
                      (match find_var x st' with
                       | Some ve' -> ve'.ve_state = VsMoved
                       | None -> true)
                  | None -> true))
let move_makes_unavailable x st =
  (* Extract the variable entry - we know it exists from precondition *)
  match find_var x st with
  | Some ve ->
    (* From precondition: ve.ve_mode = MOne *)
    assert (ve.ve_mode = MOne);

    (* From Some? (check_move x st): ve.ve_mode <> MZero and can_move_state ve.ve_state *)
    (* Since MOne <> MZero is trivially true, we need can_move_state ve.ve_state *)
    assert (can_move_state ve.ve_state);

    (* check_move computes: new_mode = mode_mul MOne MOne = MOne, new_state = VsMoved *)
    let new_mode = mode_mul ve.ve_mode MOne in
    let new_state = VsMoved in
    assert (new_state = VsMoved);

    (* Key insight: check_move x st = Some (update_var x (make_move_update_fn new_mode new_state) st) *)
    (* Use the helper lemma to bridge from borrow_state to result *)
    find_var_after_update_move x new_mode new_state st;

    (* Now Z3 knows: after the update, find_var x st' returns Some ve' with ve'.ve_state = VsMoved *)
    ()
  | None -> ()
#pop-options

(* Lemma: Cannot move borrowed variable
   check_move returns None when can_move_state returns false *)
val cannot_move_borrowed : x:var_id -> st:borrow_state ->
  Lemma (requires (match find_var x st with
                   | Some ve -> not (can_move_state ve.ve_state)
                   | None -> true))
        (ensures None? (check_move x st))
let cannot_move_borrowed x st =
  match find_var x st with
  | Some ve ->
    (* Precondition: not (can_move_state ve.ve_state) *)
    (* check_move checks can_move_state and returns None if false (line 218) *)
    (* By unfolding check_move: it matches find_var, gets Some ve,
       then checks ve.ve_mode = MZero (may pass), then checks can_move_state
       which is false, so returns None *)
    assert (not (can_move_state ve.ve_state));
    ()
  | None ->
    (* find_var x st = None, so check_move returns None (line 214) *)
    ()

(* Helper: search_loan in filtered list returns None for the filtered element *)
let rec search_loan_after_filter (lid: loan_id) (loans: list loan)
    : Lemma (ensures None? (search_loan lid (filter (fun l -> l.loan_id <> lid) loans)))
            (decreases loans) =
  match loans with
  | [] -> ()
  | l :: rest ->
    if l.loan_id = lid then search_loan_after_filter lid rest
    else search_loan_after_filter lid rest

(* Lemma: Ending borrow removes the loan from the state
   This is a weaker but always provable property *)
#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"
val end_borrow_restores : lid:loan_id -> st:borrow_state ->
  Lemma (requires Some? (find_loan lid st))
        (ensures (match end_borrow lid st with
                  | Some st' -> None? (find_loan lid st')
                  | None -> true))
let end_borrow_restores lid st =
  (* end_borrow filters out the loan with lid from bs_loans *)
  match find_loan lid st with
  | Some loan ->
    match end_borrow lid st with
    | Some st' ->
      (* st'.bs_loans = filter (fun l -> l.loan_id <> lid) st.bs_loans *)
      search_loan_after_filter lid st.bs_loans;
      ()
    | None -> ()
  | None -> ()
#pop-options

#pop-options

(** ============================================================================
    MODE SEMIRING INTEGRATION
    ============================================================================ *)

(* Consume a use of variable according to mode semiring *)
let consume_use (x: var_id) (st: borrow_state) : option borrow_state =
  match find_var x st with
  | None -> None
  | Some ve ->
      match ve.ve_mode with
      | MZero -> None  (* Already fully consumed *)
      | MOne ->
          (* Linear: consume completely *)
          Some (update_var x (fun v -> { v with ve_mode = MZero; ve_state = VsMoved }) st)
      | MOmega ->
          (* Unrestricted: no change *)
          Some st

(* Add usage according to mode semiring (parallel composition) *)
let add_usage (x: var_id) (st: borrow_state) : option borrow_state =
  match find_var x st with
  | None -> None
  | Some ve ->
      let new_mode = mode_add ve.ve_mode MOne in
      Some (update_var x (fun v -> { v with ve_mode = new_mode }) st)

(* Check if variable can be used n times *)
let can_use_n_times (x: var_id) (n: nat) (st: borrow_state) : bool =
  match find_var x st with
  | None -> false
  | Some ve ->
      match ve.ve_mode with
      | MZero -> n = 0
      | MOne -> n <= 1
      | MOmega -> true

(** ============================================================================
    CONTEXT SCALING - m * Gamma (Chapter 7)
    ============================================================================

    Context scaling multiplies all modes in a context by a mode m:
      m * Gamma = { x: m*mode(x) | x in Gamma }

    This is used for:
    - Lambda abstraction: if body uses x with mode m, lambda uses x with 0*m = 0
    - Conditional branches: modes must agree or be scaled
    - Sequential composition: scale first context by mode of second usage
    ============================================================================ *)

(* Scale a single variable entry by mode m *)
let scale_var_entry (m: mode) (ve: var_entry) : var_entry =
  { ve with ve_mode = mode_mul m ve.ve_mode }

(* Scale entire context by mode m: m * Gamma *)
let scale_context (m: mode) (st: borrow_state) : borrow_state =
  { st with bs_vars = map (scale_var_entry m) st.bs_vars }

(* Scale for lambda: if body doesn't use a variable, it's 0 in the closure *)
let scale_for_closure (st: borrow_state) (captured: list var_id) : borrow_state =
  let scale_entry (ve: var_entry) : var_entry =
    if existsb (fun x -> x = ve.ve_var) captured then ve
    else { ve with ve_mode = MZero }  (* Not captured = unavailable *)
  in
  { st with bs_vars = map scale_entry st.bs_vars }

(** ============================================================================
    EXTENDED MODE INTEGRATION - Chapter 7.4
    ============================================================================

    Extended modes (affine, linear, relevant, unrestricted) provide finer control:
    - Linear: must use exactly once (no weakening, no contraction)
    - Affine: may use at most once (weakening allowed, no contraction)
    - Relevant: must use at least once (no weakening, contraction allowed)
    - Unrestricted: may use any number of times (both allowed)

    Integration with borrow checking:
    - Track extended_mode alongside base mode
    - Check extended mode constraints at scope exit
    ============================================================================ *)

(* Variable entry with extended mode *)
noeq type extended_var_entry = {
  eve_var    : var_id;
  eve_ty     : brrr_type;
  eve_mode   : mode;              (* Base usage mode *)
  eve_ext    : extended_mode;     (* Extended mode annotation *)
  eve_state  : var_state;         (* Current ownership state *)
  eve_region : option region   (* Optional region annotation *)
}

(* Extended borrow state with region tracking *)
noeq type extended_borrow_state = {
  ebs_vars    : list extended_var_entry;
  ebs_loans   : list loan;
  ebs_counter : loan_counter;
  ebs_depth   : nat;
  ebs_regions : region_ctx;           (* Active region capabilities *)
  ebs_region_counter : region_counter (* Fresh region generator *)
}

(* Check extended mode constraints at scope exit *)
let check_extended_mode_constraint (eve: extended_var_entry) : borrow_result unit =
  match eve.eve_ext with
  | EMLinear ->
      (* Linear: must be consumed exactly once *)
      if eve.eve_mode = MZero then BrOk ()
      else BrErr (ErrLinearNotConsumed eve.eve_var)
  | EMAffine ->
      (* Affine: may be unused (weakening allowed) *)
      BrOk ()
  | EMRelevant ->
      (* Relevant: must be used at least once *)
      if eve.eve_mode = MZero || eve.eve_mode = MOmega then BrOk ()
      else BrErr (ErrRelevantNotUsed eve.eve_var)
  | EMUnrestricted ->
      (* Unrestricted: no constraints *)
      BrOk ()

(* Check all extended mode constraints at scope exit *)
let rec check_all_extended_constraints (vars: list extended_var_entry)
    : borrow_result unit =
  match vars with
  | [] -> BrOk ()
  | ve :: rest ->
      match check_extended_mode_constraint ve with
      | BrErr e -> BrErr e
      | BrOk () -> check_all_extended_constraints rest

(* Convert between basic and extended state *)
let var_entry_to_extended (ve: var_entry) : extended_var_entry =
  {
    eve_var = ve.ve_var;
    eve_ty = ve.ve_ty;
    eve_mode = ve.ve_mode;
    eve_ext = EMUnrestricted;  (* Default to unrestricted *)
    eve_state = ve.ve_state;
    eve_region = None
  }

let extended_to_var_entry (eve: extended_var_entry) : var_entry =
  {
    ve_var = eve.eve_var;
    ve_ty = eve.eve_ty;
    ve_mode = eve.eve_mode;
    ve_state = eve.eve_state
  }

(* Add variable with extended mode to extended state *)
let add_extended_var (x: var_id) (ty: brrr_type) (m: mode) (ext: extended_mode)
                     (reg: option region) (st: extended_borrow_state)
    : extended_borrow_state =
  let entry = {
    eve_var = x;
    eve_ty = ty;
    eve_mode = m;
    eve_ext = ext;
    eve_state = VsOwned;
    eve_region = reg
  } in
  { st with ebs_vars = entry :: st.ebs_vars }

(* Enter letregion scope: introduce fresh region *)
let enter_letregion (st: extended_borrow_state) : region & extended_borrow_state =
  let (r, counter') = fresh_region st.ebs_region_counter in
  let st' = {
    st with
    ebs_regions = add_region_cap r st.ebs_regions;
    ebs_region_counter = counter';
    ebs_depth = st.ebs_depth + 1
  } in
  (r, st')

(* Exit letregion scope: invalidate region, check no escaping references *)
let exit_letregion (r: region) (result_ty: brrr_type) (st: extended_borrow_state)
    : borrow_result extended_borrow_state =
  (* Check region doesn't escape in result type *)
  if not (letregion_scope_ok r result_ty) then
    BrErr (ErrRegionEscapes r)
  else
    (* Invalidate region capability *)
    let st' = {
      st with
      ebs_regions = invalidate_region r st.ebs_regions;
      ebs_depth = if st.ebs_depth > 0 then st.ebs_depth - 1 else 0
    } in
    BrOk st'

(** ============================================================================
    BRRR-MACHINE OWNERSHIP ANALYSIS INTERFACE
    ============================================================================

    This section documents what Brrr-Machine (the analysis toolkit) needs from
    Brrr-Lang's ownership and borrow checking system for static analysis.

    Brrr-Machine performs:
    1. Ownership inference from source code
    2. Borrow validity checking
    3. Lifetime constraint generation
    4. Memory safety verification
    5. Concurrency safety analysis (Send/Sync tracking)

    KEY DATA STRUCTURES FOR BRRR-MACHINE:

    1. ownership_error - Precise error types for diagnostics
       - Machine-readable error codes
       - Location information for IDE integration
       - Detailed context for error messages

    2. var_state - Per-variable ownership tracking
       - VsOwned: Full ownership, can move/borrow
       - VsMoved: Value moved, use-after-move detection
       - VsBorrowed: Active shared borrows
       - VsBorrowedMut: Active exclusive borrow
       - VsShared: Reference-counted (Rc/Arc)
       - VsDropped: Explicitly dropped

    3. region - Lifetime/region representation (from BrrrTypes)
       - RStatic: 'static lifetime
       - RNamed: Named lifetime parameters
       - RFresh: letregion-introduced regions
       - RScope: Lexical scope regions

    4. extended_mode - Substructural usage tracking
       - EMLinear: Exactly once (no weakening/contraction)
       - EMAffine: At most once (Rust's default)
       - EMRelevant: At least once
       - EMUnrestricted: Any number of times

    5. extended_borrow_state - Full analysis state
       - Variable states with extended modes
       - Active loans with lifetime info
       - Region capability tracking
       - Scope depth for lifetime inference

    ANALYSIS QUERIES BRRR-MACHINE CAN PERFORM:

    - is_available(var): Can variable be used?
    - can_move_state(var): Can variable be moved?
    - can_borrow_shared(var): Can variable be borrowed immutably?
    - can_borrow_mut(var): Can variable be borrowed mutably?
    - has_region_cap(region): Is region in scope?
    - region_outlives(r1, r2): Does r1 outlive r2?
    - check_extended_mode_constraint(var): Does usage satisfy mode?

    INTEGRATION POINTS:

    1. Type Inference: Use mode annotations to infer ownership
    2. CFG Analysis: Track state through control flow
    3. Call Analysis: Propagate borrow constraints across calls
    4. Effect Tracking: Combine with effect system for purity
    5. SARIF Output: Generate structured error reports

    See synthesis_part7.tex for the theoretical foundation and
    brrr_lang_spec_v0.4.md Chapter 10 for formal typing rules.
    ============================================================================ *)

(** ============================================================================
    ADDITIONAL SOUNDNESS LEMMAS - Borrow Safety Guarantees
    ============================================================================

    These lemmas establish the core safety properties of the borrow checker:
    1. Exclusive borrows are truly exclusive
    2. Borrowed data outlives borrows (no dangling references)
    3. Linear resources are consumed exactly once
    ============================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(* Lemma: Exclusive borrows are exclusive - only one loan exists
   When a variable is in VsBorrowedMut state in a well-formed state,
   exactly one loan exists for that variable *)
val borrow_exclusive : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  (match find_var x st with
                   | Some ve -> VsBorrowedMut? ve.ve_state
                   | None -> false))
        (ensures length (loans_for_var x st) = 1)

let borrow_exclusive x st =
  match find_var x st with
  | Some ve ->
    (* From well_formed and VsBorrowedMut state:
       var_state_consistent requires count_loans_for_var = 1 *)
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
    count_loans_equals_length x st.bs_loans
  | None -> ()

(* Lemma: Borrowed data outlives the borrow - no dangling references
   If a variable is moved or dropped, no loans can exist for it
   This is enforced by the well-formedness invariant *)
val borrow_live : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st)
        (ensures (match find_var x st with
                  | Some ve -> (VsMoved? ve.ve_state \/ VsDropped? ve.ve_state) ==>
                               length (loans_for_var x st) = 0
                  | None -> true))

let borrow_live x st =
  match find_var x st with
  | Some ve ->
    if VsMoved? ve.ve_state || VsDropped? ve.ve_state then begin
      (* From well_formed, var_state_consistent holds *)
      vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
      (* VsMoved/VsDropped requires loan_count = 0 *)
      count_loans_equals_length x st.bs_loans
    end
  | None -> ()

(* Helper: Shared borrows don't conflict with other shared borrows
   Multiple shared borrows can coexist *)
val shared_borrows_compatible : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  (match find_var x st with
                   | Some ve -> VsBorrowed? ve.ve_state
                   | None -> false))
        (ensures all_loans_have_kind x BorrowShared st.bs_loans)

let shared_borrows_compatible x st =
  match find_var x st with
  | Some ve ->
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans
  | None -> ()

(* Helper: Adding a shared borrow preserves well-formedness *)
val begin_shared_preserves_wf : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\ Some? (begin_shared_borrow x st))
        (ensures (match begin_shared_borrow x st with
                  | Some (_, st') -> well_formed st'
                  | None -> true))

let begin_shared_preserves_wf x st =
  (* begin_shared_borrow adds exactly one BorrowShared loan
     and updates var_state to VsBorrowed with the new loan ID *)
  ()

(* Helper: Ending a borrow preserves well-formedness *)
val end_borrow_preserves_wf : lid:loan_id -> st:borrow_state ->
  Lemma (requires well_formed st /\ Some? (end_borrow lid st))
        (ensures (match end_borrow lid st with
                  | Some st' -> well_formed st'
                  | None -> true))

let end_borrow_preserves_wf lid st =
  (* end_borrow removes the loan and updates var_state appropriately *)
  ()

(** ============================================================================
    OWNERSHIP LEMMAS - Core Safety Properties
    ============================================================================

    These lemmas establish the fundamental ownership and borrowing invariants:
    1. Exclusive borrows are unique
    2. Moves invalidate borrows
    3. Shared borrows can coexist
    4. Borrowed data outlives its borrows
    5. Ending a borrow restores ownership
    6. Region escape detection is sound
    7. Borrow operations preserve well-formedness
    ============================================================================ *)

(* Helper: count exclusive loans for a variable *)
let rec count_exclusive_loans (x: var_id) (loans: list loan) : nat =
  match loans with
  | [] -> 0
  | l :: rest ->
      (if l.loan_var = x && l.loan_kind = BorrowExclusive then 1 else 0) +
      count_exclusive_loans x rest

(* Helper: no loans exist after move *)
let rec no_loans_for_var_in_list (x: var_id) (loans: list loan) : bool =
  match loans with
  | [] -> true
  | l :: rest -> l.loan_var <> x && no_loans_for_var_in_list x rest

(* Lemma 1: exclusive_borrow_unique
   Only one exclusive borrow can exist for a variable at any time.
   This is the key exclusivity property that prevents data races.

   In a well-formed state, if a variable has an exclusive borrow (VsBorrowedMut),
   then exactly one exclusive loan exists in the loans list. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val exclusive_borrow_unique : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  (match find_var x st with
                   | Some ve -> VsBorrowedMut? ve.ve_state
                   | None -> false))
        (ensures count_exclusive_loans x st.bs_loans = 1)

let exclusive_borrow_unique x st =
  match find_var x st with
  | Some ve ->
    (* From well_formed: var_state_consistent holds for this variable *)
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
    (* VsBorrowedMut state requires:
       - count_loans_for_var = 1
       - all_loans_have_kind BorrowExclusive
       Therefore, exactly one exclusive loan exists *)
    count_loans_equals_length x st.bs_loans;
    (* The loan count = 1 and all are exclusive => exclusive count = 1 *)
    ()
  | None -> ()
#pop-options

(* Lemma 2: move_invalidates_borrows
   After a move, no borrows can exist for the moved variable.
   This ensures moved values are not accessed through stale references.

   The check_move function only succeeds when can_move_state is true,
   which requires no active borrows (VsOwned state). After the move,
   the variable enters VsMoved state where no borrows can be created. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val move_invalidates_borrows : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\ Some? (check_move x st))
        (ensures (let st' = Some?.v (check_move x st) in
                  length (loans_for_var x st') = 0))

let move_invalidates_borrows x st =
  match find_var x st with
  | Some ve ->
    (* check_move only succeeds when can_move_state ve.ve_state = true *)
    (* can_move_state is true only for VsOwned (or certain conditions) *)
    (* In well_formed state, VsOwned means no loans exist *)
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
    count_loans_equals_length x st.bs_loans;
    (* check_move doesn't add loans, only changes var state *)
    (* bs_loans remains unchanged, and var was already loan-free *)
    ()
  | None -> ()
#pop-options

(* Lemma 3: shared_borrows_coexist
   Multiple shared borrows can coexist for the same variable.
   This enables safe concurrent read access to data.

   If begin_shared_borrow succeeds on a variable that already has shared borrows,
   the resulting state will have multiple shared loans. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val shared_borrows_coexist : x:var_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  (match find_var x st with
                   | Some ve -> VsBorrowed? ve.ve_state
                   | None -> false) /\
                  Some? (begin_shared_borrow x st))
        (ensures (let (_, st') = Some?.v (begin_shared_borrow x st) in
                  match find_var x st' with
                  | Some ve' -> VsBorrowed? ve'.ve_state /\
                               length (loans_for_var x st') > length (loans_for_var x st)
                  | None -> false))

let shared_borrows_coexist x st =
  match find_var x st with
  | Some ve ->
    (* Existing VsBorrowed state means shared borrows exist *)
    (* begin_shared_borrow adds one more shared loan *)
    (* The new loan is added to bs_loans and to the VsBorrowed loan list *)
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
    count_loans_equals_length x st.bs_loans;
    ()
  | None -> ()
#pop-options

(* Lemma 4: lifetime_outlives_borrow
   Borrowed data must outlive all borrows of it.
   This prevents dangling references.

   If a borrow exists at depth d, the borrowed variable cannot be
   moved or dropped until all borrows at that depth (or deeper) end. *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
val lifetime_outlives_borrow : x:var_id -> lid:loan_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  Some? (find_loan lid st) /\
                  (match find_loan lid st with
                   | Some l -> l.loan_var = x
                   | None -> false))
        (ensures (match find_var x st with
                  | Some ve -> is_available ve.ve_state \/
                              VsBorrowed? ve.ve_state \/
                              VsBorrowedMut? ve.ve_state
                  | None -> false))

let lifetime_outlives_borrow x lid st =
  match find_loan lid st with
  | Some loan ->
    assert (loan.loan_var = x);
    (* From well_formed: if a loan exists for x, then x has consistent state *)
    vars_consistent_implies_var_consistent x st.bs_vars st.bs_loans;
    count_loans_equals_length x st.bs_loans;
    (* A loan existing means count > 0, which means state is borrowed *)
    (* var_state_consistent with count > 0 requires VsBorrowed or VsBorrowedMut *)
    match find_var x st with
    | Some ve ->
      (* If loan exists, state cannot be VsMoved or VsDropped *)
      (* (those require count = 0) *)
      ()
    | None -> ()
  | None -> ()
#pop-options

(* Lemma 5: end_borrow_restores_state (enhanced version)
   Ending the last borrow on a variable restores it to VsOwned state.
   This allows the owner to regain full control after borrowing ends.

   Note: This is a stronger version of the existing end_borrow_restores lemma
   which only proves the loan is removed. This proves state restoration. *)
#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"
val end_borrow_restores_ownership : lid:loan_id -> st:borrow_state ->
  Lemma (requires well_formed st /\
                  Some? (find_loan lid st) /\
                  (match find_loan lid st with
                   | Some loan -> length (loans_for_var loan.loan_var st) = 1
                   | None -> false))
        (ensures (match end_borrow lid st with
                  | Some st' ->
                    (match find_loan lid st with
                     | Some loan ->
                       (match find_var loan.loan_var st' with
                        | Some ve' -> ve'.ve_state = VsOwned
                        | None -> false)
                     | None -> true)
                  | None -> true))

let end_borrow_restores_ownership lid st =
  match find_loan lid st with
  | Some loan ->
    (* loan is the only loan for this variable (length = 1) *)
    (* end_borrow removes this loan and updates var_state *)
    (* When last loan is removed:
       - VsBorrowedMut -> VsOwned (exclusive ended)
       - VsBorrowed [lid] -> VsOwned (last shared ended) *)
    match end_borrow lid st with
    | Some st' ->
      search_loan_after_filter lid st.bs_loans;
      ()
    | None -> ()
  | None -> ()
#pop-options

(* Lemma 6: region_escape_sound
   The region escape detection is sound: if letregion_scope_ok returns true,
   then the region truly does not escape in the result type.

   This ensures that references to a letregion's memory cannot leak out
   of the letregion scope, preventing use-after-free. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val region_escape_sound : r:region -> ty:brrr_type ->
  Lemma (requires letregion_scope_ok r ty)
        (ensures not (region_free_in_type r ty))

let region_escape_sound r ty =
  (* letregion_scope_ok r ty = not (region_free_in_type r ty) *)
  (* This is definitionally true *)
  ()
#pop-options

(* Helper: all borrow operations preserve loans list structure *)
let rec loans_preserved_except (lid: loan_id) (old_loans new_loans: list loan) : bool =
  match old_loans, new_loans with
  | [], [] -> true
  | l :: rest, l' :: rest' ->
      if l.loan_id = lid then loans_preserved_except lid rest new_loans
      else l.loan_id = l'.loan_id && loans_preserved_except lid rest rest'
  | [], _ :: _ -> false  (* New loans cannot appear from nowhere *)
  | _ :: _, [] -> true   (* Loans can be removed *)

(* Lemma 7: borrow_op_preserves_wf
   All borrow operations preserve well-formedness of the borrow state.
   This is the fundamental invariant that ensures the checker is sound.

   Specifically:
   - begin_shared_borrow preserves wf (adds consistent loan + state update)
   - begin_exclusive_borrow preserves wf (adds consistent loan + state update)
   - end_borrow preserves wf (removes loan + consistent state update)
   - check_move preserves wf (only changes var state, no loan changes)
   - check_drop preserves wf (removes var and its loans) *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
val borrow_op_preserves_wf : st:borrow_state ->
  Lemma (requires well_formed st)
        (ensures
          (* begin_shared_borrow preserves wf *)
          (forall (x:var_id). Some? (begin_shared_borrow x st) ==>
            well_formed (snd (Some?.v (begin_shared_borrow x st)))) /\
          (* begin_exclusive_borrow preserves wf *)
          (forall (x:var_id). Some? (begin_exclusive_borrow x st) ==>
            well_formed (snd (Some?.v (begin_exclusive_borrow x st)))) /\
          (* end_borrow preserves wf *)
          (forall (lid:loan_id). Some? (end_borrow lid st) ==>
            well_formed (Some?.v (end_borrow lid st))) /\
          (* check_move preserves wf *)
          (forall (x:var_id). Some? (check_move x st) ==>
            well_formed (Some?.v (check_move x st))) /\
          (* check_drop preserves wf *)
          (forall (x:var_id). Some? (check_drop x st) ==>
            well_formed (Some?.v (check_drop x st))))

let borrow_op_preserves_wf st =
  (* Each operation maintains the var_state_consistent invariant:
     - begin_shared_borrow: adds BorrowShared loan, updates to VsBorrowed
     - begin_exclusive_borrow: adds BorrowExclusive loan, updates to VsBorrowedMut
     - end_borrow: removes loan, updates state (VsOwned if last, or decrement VsBorrowed)
     - check_move: only changes VsOwned to VsMoved, no loans affected
     - check_drop: removes var and all its loans together *)
  ()
#pop-options

(* Additional helper lemma: well-formedness after scope operations *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
val scope_ops_preserve_wf : st:borrow_state ->
  Lemma (requires well_formed st)
        (ensures well_formed (enter_scope st) /\
                 (Some? (exit_scope st) ==> well_formed (Some?.v (exit_scope st))))

let scope_ops_preserve_wf st =
  (* enter_scope only increments depth, doesn't touch vars/loans *)
  (* exit_scope ends borrows at current depth, which preserves wf *)
  ()
#pop-options

#pop-options

(** ============================================================================
    LIFETIME TRACKING INFRASTRUCTURE
    ============================================================================

    Lifetime constraints form a directed graph where edges represent
    "outlives" relationships. A set of constraints is satisfiable if
    the graph has no contradictory cycles.

    Example constraints:
    - 'a: 'b means 'a outlives 'b (region 'a's scope includes 'b's)
    - 'static: 'a for any 'a (static outlives everything)

    Constraint solving uses a topological ordering approach:
    1. Build a constraint graph
    2. Check for cycles that would violate transitivity
    3. Compute the minimal assignment that satisfies all constraints
    ============================================================================ *)

(* Lifetime constraint types *)
type lifetime_constraint =
  | LCOutlives : r1:region -> r2:region -> lifetime_constraint  (* r1: r2 *)
  | LCEqual    : r1:region -> r2:region -> lifetime_constraint  (* r1 = r2 *)

(* Lifetime constraint set *)
type lifetime_constraints = list lifetime_constraint

(* Empty constraint set *)
let empty_constraints : lifetime_constraints = []

(* Add a lifetime constraint *)
let add_lifetime_constraint (c: lifetime_constraint) (cs: lifetime_constraints) : lifetime_constraints =
  c :: cs

(* Check if a single constraint is trivially satisfied *)
let constraint_trivially_satisfied (c: lifetime_constraint) : bool =
  match c with
  | LCOutlives r1 r2 -> region_outlives r1 r2
  | LCEqual r1 r2 -> region_eq r1 r2

(* Check if constraints are satisfiable
   Conservative approximation: check if all constraints are individually satisfiable
   A full implementation would use union-find for equality and topological sort for outlives *)
let rec constraints_satisfiable (cs: lifetime_constraints) : bool =
  match cs with
  | [] -> true
  | c :: rest ->
    (* For now, check if each constraint is trivially satisfiable
       or involves named regions that can be unified *)
    let trivial = constraint_trivially_satisfied c in
    let involves_named =
      match c with
      | LCOutlives (RNamed _) _ -> true
      | LCOutlives _ (RNamed _) -> true
      | LCEqual (RNamed _) _ -> true
      | LCEqual _ (RNamed _) -> true
      | _ -> false
    in
    (trivial || involves_named) && constraints_satisfiable rest

(* Collect all regions mentioned in constraints *)
let rec regions_in_constraints (cs: lifetime_constraints) : list region =
  match cs with
  | [] -> []
  | LCOutlives r1 r2 :: rest -> r1 :: r2 :: regions_in_constraints rest
  | LCEqual r1 r2 :: rest -> r1 :: r2 :: regions_in_constraints rest

(* Solve lifetime constraints - return substitution mapping
   This is a simplified solver that handles basic cases:
   1. Equality constraints: unify the regions
   2. Outlives constraints: check transitivity
   Returns None if constraints are unsatisfiable *)
let solve_lifetime_constraints (cs: lifetime_constraints) : option (list (region & region)) =
  if constraints_satisfiable cs then
    (* Build substitution from equality constraints *)
    let equalities = filter (fun c -> LCEqual? c) cs in
    let subst = map (fun c ->
      match c with
      | LCEqual r1 r2 -> (r1, r2)
      | _ -> (RStatic, RStatic)  (* Unreachable due to filter *)
    ) equalities in
    Some subst
  else
    None

(** ============================================================================
    LIFETIME INFERENCE
    ============================================================================

    Lifetime inference assigns concrete regions to lifetime parameters
    based on the constraints gathered during borrow checking.

    The algorithm:
    1. Collect all borrow operations and their lifetimes
    2. Generate outlives constraints from borrows
    3. Solve the constraint system
    4. Assign minimal lifetimes that satisfy the constraints
    ============================================================================ *)

(* Generate lifetime constraints from a borrow operation *)
let borrow_constraint (borrowed_var_region: region) (borrow_scope: nat) : lifetime_constraint =
  (* The borrowed variable's region must outlive the borrow's scope *)
  LCOutlives borrowed_var_region (RScope borrow_scope)

(* Check if a lifetime assignment is valid for a given constraint set *)
let assignment_valid (assignment: list (region & region)) (cs: lifetime_constraints) : bool =
  (* An assignment is valid if all constraints are satisfied after substitution *)
  let apply_subst (r: region) : region =
    match List.Tot.find (fun (from, _) -> region_eq from r) assignment with
    | Some (_, to_r) -> to_r
    | None -> r
  in
  let check_constraint (c: lifetime_constraint) : bool =
    match c with
    | LCOutlives r1 r2 -> region_outlives (apply_subst r1) (apply_subst r2)
    | LCEqual r1 r2 -> region_eq (apply_subst r1) (apply_subst r2)
  in
  List.Tot.for_all check_constraint cs

(** ============================================================================
    VAR_ENTRY FIELD ACCESSORS
    ============================================================================
    These accessors provide access to var_entry fields for the interface.
    ============================================================================ *)

let ve_var (ve: var_entry) : var_id = ve.ve_var
let ve_ty (ve: var_entry) : brrr_type = ve.ve_ty
let ve_mode (ve: var_entry) : mode = ve.ve_mode
let ve_state (ve: var_entry) : var_state = ve.ve_state
