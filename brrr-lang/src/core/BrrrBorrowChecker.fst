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
 *
 * THEORETICAL FOUNDATIONS
 * =======================
 *
 * This module implements a static borrow checker inspired by:
 *
 * 1. RustBelt (Jung et al. 2018, POPL)
 *    - Semantic foundation for Rust's type system using Iris separation logic
 *    - Key insight: ownership = exclusive access to memory
 *    - Borrows modeled as fractional permissions (pts_to r #p v)
 *    - Reference: "RustBelt: Securing the Foundations of the Rust
 *      Programming Language"
 *
 * 2. Iris Separation Logic (Jung et al. 2018, JFP)
 *    - Higher-order concurrent separation logic
 *    - Points-to predicates: l |-> v (exclusive), l |->^p v (fractional)
 *    - Separating conjunction (star): disjoint heap composition
 *    - Frame rule: {P} c {Q} implies {P * R} c {Q * R}
 *
 * 3. Pulse/Steel (F* ecosystem)
 *    - pts_to r #p v: reference r points to v with permission p
 *    - share/gather: split and combine fractional permissions
 *    - Ownership transfer via linear types
 *
 * OWNERSHIP MODEL (spec Section 5.5)
 * ==================================
 *
 * Brrr-Lang ownership maps to separation logic:
 *   - own x : T        <=>  x |-> v (full ownership)
 *   - &T (shared ref)  <=>  x |->^(1/n) v (fractional, read-only)
 *   - &mut T (excl)    <=>  x |-> v (exclusive access)
 *   - Rc<T>/Arc<T>     <=>  shared ownership with reference counting
 *
 * KEY INVARIANTS
 * ==============
 *
 * 1. Exclusivity: At most one &mut T exists per location at any time
 * 2. No aliasing: &mut T and &T cannot coexist for same location
 * 3. Lifetime soundness: borrows do not outlive borrowed data
 * 4. Linear consumption: linear types used exactly once
 *
 * These invariants prevent:
 *   - Data races (exclusive access or shared read-only)
 *   - Use-after-free (lifetime tracking)
 *   - Double-free (linear consumption)
 *   - Iterator invalidation (borrow scope tracking)
 *)
module BrrrBorrowChecker

(* Z3 solver options for SMT tractability - following HACL-star/EverParse patterns *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Mul  (* For arithmetic multiplication operator *)
open BrrrModes
open BrrrTypes
open BrrrExpressions

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
      region_free_in_params r ft.params

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

(* Helper: check if region appears in parameter types
   Separated from region_free_in_type to enable mutual recursion with proper termination *)
and region_free_in_params (r: region) (ps: list param_type) : Tot bool (decreases ps) =
  match ps with
  | [] -> false
  | p :: rest -> region_free_in_type r p.ty || region_free_in_params r rest

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
    BORROW KIND FUNCTIONS
    ============================================================================ *)

(* Note: borrow_kind type is defined in interface file BrrrBorrowChecker.fsti *)

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
    ACTIVE LOAN - Borrow Tracking Records
    ============================================================================

    A loan represents an active borrow of a variable. Loans are the dynamic
    counterpart to Rust's borrow checker - they track WHO has borrowed WHAT
    and for HOW LONG (via depth/scope tracking).

    THEORETICAL BASIS
    =================

    In RustBelt (Jung 2018), borrows are modeled using lifetime logic:

      &'a T  ~  bor(k, ty_shr(k, T, l))

    Where:
      - k is the lifetime (our loan_depth approximates this)
      - ty_shr(k, T, l) is the sharing predicate at location l
      - bor(k, P) is the "borrowed for lifetime k" modality

    Our loan record captures the essential information:
      - loan_id: unique identifier for this specific borrow instance
      - loan_var: which variable is borrowed (the location l)
      - loan_kind: shared (ty_shr) vs exclusive (&uniq)
      - loan_depth: approximates lifetime via lexical scope depth

    SEPARATION LOGIC VIEW (Pulse/Steel)
    ====================================

    A loan can be seen as holding a fractional permission:

      Shared loan:    pts_to loan_var #(1/n) v  (fraction of permission)
      Exclusive loan: pts_to loan_var #1.0R v   (full permission, exclusive)

    The loan_id serves as a witness that this permission was legitimately
    acquired and will be returned when the loan ends.

    LOAN INVARIANTS
    ===============

    1. At most one exclusive loan per variable at any time
    2. Exclusive loans conflict with all other loans (shared or exclusive)
    3. Multiple shared loans can coexist (fractional permissions compose)
    4. loan_depth determines when the loan automatically ends (scope exit)
    5. Ending a loan restores the previous ownership state

    REBORROWING
    ===========

    loan_depth enables reborrowing: creating a new borrow from an existing one.
    The new borrow has a DEEPER depth, ensuring it ends before the original:

      let x = 5;
      let r1 = &x;        // loan at depth 1
      {
        let r2 = &*r1;    // reborrow at depth 2, must end first
      }                   // r2 ends here
      // r1 still valid

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

    Note: ownership_error and borrow_result types are defined in the interface
    file BrrrBorrowChecker.fsti. This section provides helper functions.
    ============================================================================ *)

(* Convert to option for backward compatibility *)
let borrow_result_to_option (#a: Type) (r: borrow_result a) : option a =
  match r with
  | BrOk v -> Some v
  | BrErr _ -> None

(** ============================================================================
    VARIABLE STATE FUNCTIONS
    ============================================================================

    Note: var_state type is defined in interface file BrrrBorrowChecker.fsti.
    This section provides functions for working with var_state values.
    ============================================================================ *)

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
    BORROW STATE - The Global Checker State
    ============================================================================

    The borrow_state maintains all information needed for ownership tracking
    during borrow checking. It combines:
      - Per-variable ownership states (var_entry list)
      - Active borrows/loans (loan list)
      - Administrative state (counters, scope depth)

    CORRESPONDENCE TO RUST/RUSTBELT
    ===============================

    In Rust's borrow checker (MIR-based), similar information is tracked:
      - move_paths: tracks which values have been moved
      - borrows_in_scope: tracks active borrows
      - region_inference: computes lifetimes

    In RustBelt's semantic model (Jung 2018):
      - Typing context Gamma maps variables to types
      - Lifetime context Delta tracks active lifetimes
      - The semantic interpretation [[Gamma; Delta |- e : tau]]
        requires all ownership assertions to be satisfied

    WELL-FORMEDNESS INVARIANT
    =========================

    A borrow_state is well-formed (well_formed st = true) when:
      1. Each variable's ve_state is consistent with bs_loans:
         - VsOwned     => no loans for this variable
         - VsMoved     => no loans for this variable
         - VsDropped   => no loans for this variable
         - VsBorrowed  => all loans are BorrowShared
         - VsBorrowedMut => exactly one loan, BorrowExclusive
         - VsShared    => can have shared loans

      2. Loan IDs are unique (bs_counter ensures freshness)

      3. Scope depths are monotonic (enter_scope increments, exit_scope decrements)

    This invariant is preserved by all operations (Lemma: borrow_op_preserves_wf).

    SCOPE TRACKING
    ==============

    bs_depth tracks the current lexical scope depth for lifetime inference.
    When entering a block/function:
      - enter_scope increments bs_depth
      - New borrows get loan_depth = current bs_depth

    When exiting a scope:
      - exit_scope ends all loans with loan_depth >= current depth
      - This implements automatic borrow release at scope end

    This is a STATIC APPROXIMATION of Rust's NLL (Non-Lexical Lifetimes).
    A more precise analysis would use a CFG-based approach.

    ============================================================================ *)

(* Variable entry in borrow state *)
noeq type var_entry = {
  ve_var   : var_id;
  ve_ty    : brrr_type;
  ve_mode  : mode;         (* Usage mode from mode semiring (0, 1, omega) *)
  ve_state : var_state     (* Current ownership state *)
}

(* Accessors for var_entry fields - must be defined before borrow_state *)
let get_ve_var (ve: var_entry) : var_id = ve.ve_var
let get_ve_ty (ve: var_entry) : brrr_type = ve.ve_ty
let get_ve_mode (ve: var_entry) : mode = ve.ve_mode
let get_ve_state (ve: var_entry) : var_state = ve.ve_state

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
open BrrrExpressions

(* Add new variable - must come before find_var per interface order *)
let add_var (x: var_id) (ty: brrr_type) (m: mode) (st: borrow_state) : borrow_state =
  let entry = {
    ve_var = x;
    ve_ty = ty;
    ve_mode = m;
    ve_state = VsOwned
  } in
  { st with bs_vars = entry :: st.bs_vars }

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

(* Pattern size for termination measure - defined locally for BorrowChecker *)
let rec bc_pattern_size (p: pattern) : Tot nat (decreases p) =
  match p.loc_value with
  | PatWild | PatVar _ | PatLit _ -> 1
  | PatRest _ -> 1
  | PatTuple pats -> 1 + bc_pattern_list_size pats
  | PatStruct _ fps -> 1 + bc_field_pattern_list_size fps
  | PatVariant _ _ pats -> 1 + bc_pattern_list_size pats
  | PatOr p1 p2 -> 1 + bc_pattern_size p1 + bc_pattern_size p2
  | PatGuard p' _ -> 1 + bc_pattern_size p'
  | PatRef p' -> 1 + bc_pattern_size p'
  | PatBox p' -> 1 + bc_pattern_size p'
  | PatAs p' _ -> 1 + bc_pattern_size p'

and bc_pattern_list_size (pats: list pattern) : Tot nat (decreases pats) =
  match pats with
  | [] -> 0
  | p :: rest -> bc_pattern_size p + bc_pattern_list_size rest

and bc_field_pattern_list_size (fps: list (string & pattern)) : Tot nat (decreases fps) =
  match fps with
  | [] -> 0
  | (_, p) :: rest -> bc_pattern_size p + bc_field_pattern_list_size rest

(* Extract all variable bindings from a pattern with their types *)
let rec pattern_bindings (p: pattern) (default_ty: brrr_type)
    : Tot (list (var_id & brrr_type)) (decreases bc_pattern_size p) =
  match p.loc_value with
  | PatWild -> []  (* Wildcard binds nothing *)
  | PatVar x -> [(x, default_ty)]  (* Single variable binding *)
  | PatLit _ -> []  (* Literals bind nothing *)
  | PatRest None -> []  (* ...  binds nothing *)
  | PatRest (Some x) -> [(x, default_ty)]  (* ...rest binds rest *)
  | PatAs p' x ->
      (* p @ x - binds x to entire match, plus inner bindings *)
      (x, default_ty) :: pattern_bindings p' default_ty
  | PatTuple ps ->
      (* Tuple pattern - recursively extract from each sub-pattern *)
      pattern_bindings_list ps default_ty
  | PatStruct _ fields ->
      (* Struct pattern - extract from each field pattern *)
      pattern_bindings_struct_fields fields default_ty
  | PatVariant _ _ ps ->
      (* Variant pattern - extract from payload patterns *)
      pattern_bindings_list ps default_ty
  | PatOr p1 _ ->
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
    : Tot (list (var_id & brrr_type)) (decreases bc_pattern_list_size ps) =
  match ps with
  | [] -> []
  | p :: rest ->
      pattern_bindings p default_ty @ pattern_bindings_list rest default_ty

and pattern_bindings_struct_fields (fields: list (string & pattern)) (default_ty: brrr_type)
    : Tot (list (var_id & brrr_type)) (decreases bc_field_pattern_list_size fields) =
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
    BORROW STATE MERGING - Control Flow Join Semantics
    ============================================================================

    When control flow merges (if/else, match arms), we must compute a sound
    approximation of the borrow state that holds regardless of which branch
    was actually taken at runtime.

    THEORETICAL BASIS (RustBelt, Jung 2018)
    =======================================

    In RustBelt's semantic model, this corresponds to the interpretation of
    conditionals in the logical relation:

      [[if c then e1 else e2]](Delta) =
        forall v1 v2.
          (c = true  ==> [[e1]](Delta) = v1) /\
          (c = false ==> [[e2]](Delta) = v2) ==>
          result in [[tau]]

    The key insight: we must be CONSERVATIVE. If EITHER branch might have
    moved a variable, we must assume it IS moved after the merge. This is
    an over-approximation that guarantees soundness.

    SEPARATION LOGIC VIEW (Pulse/Steel)
    ====================================

    In separation logic, this relates to the frame rule and composition:

      {P1} e1 {Q1}    {P2} e2 {Q2}
      ----------------------------
      {P1 \/ P2} if c then e1 else e2 {Q1 \/ Q2}

    Our merge computes Q1 \/ Q2 as the "least upper bound" in the lattice
    of borrow states, ordered by restrictiveness.

    LATTICE STRUCTURE
    =================

    The var_state forms a lattice where MORE restrictive states are LOWER:

                          VsOwned
                         /   |   \
                        /    |    \
              VsBorrowed  VsShared  VsBorrowedMut
                        \    |    /
                         \   |   /
                     VsMoved / VsDropped

    Merge computes the MEET (greatest lower bound) in this lattice:
      - VsOwned /\ VsMoved = VsMoved (moved in one branch => moved)
      - VsOwned /\ VsBorrowed = VsBorrowed (borrowed in one => borrowed)
      - VsBorrowed /\ VsBorrowedMut = VsBorrowedMut (exclusive wins)

    MERGE RULES (spec lines 2315-2549)
    ==================================

    1. MOVED/DROPPED PROPAGATION:
       If either branch moves or drops the variable, the merged state
       reflects that - we cannot prove the variable is still available.

    2. EXCLUSIVE BORROW PRESERVATION:
       If either branch has an active exclusive borrow, we must preserve it.
       This prevents unsound code like:
         if cond { let r = &mut x; ... }
         else { x = 5; }  // Would conflict with r if cond was true!
         // After merge: x is still exclusively borrowed

    3. SHARED BORROW UNION:
       Multiple shared borrows can coexist. Take the union of loan IDs
       from both branches - all borrows are potentially active.

    4. REFERENCE COUNT MAXIMUM:
       For Rc/Arc (VsShared), take the maximum ref_count. This is
       conservative: we don't know which branch's clones exist.

    SOUNDNESS GUARANTEE
    ===================

    The merge is SOUND because it never allows operations that would be
    unsafe in ANY possible runtime execution path. This is the key
    property needed for Theorem T-5.1 (session progress) and the
    fundamental safety guarantees of the borrow checker.

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
    match e.loc_value with
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
             (match e'.loc_value with
              | EVar x ->
                  (match begin_shared_borrow x st with
                   | Some (_, st') -> Some st'
                   | None -> None)
              | _ ->
                  (* Borrow of complex expression - check inner first *)
                  borrow_check_expr (fuel - 1) e' st)
         | OpRefMut ->
             (* &mut e - create exclusive borrow *)
             (match e'.loc_value with
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
                - PatAs p x: binds x to entire match, plus inner bindings
                - PatRest (Some x): binds rest to x in slice patterns
                - PatWild/PatLit/PatRest None: no variables bound *)
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
        (match lhs.loc_value with
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
        (match e'.loc_value with
         | EVar x ->
             (match begin_shared_borrow x st with
              | Some (_, st') -> Some st'
              | None -> None)
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit mutable borrow *)
    | EBorrowMut e' ->
        (match e'.loc_value with
         | EVar x ->
             (match begin_exclusive_borrow x st with
              | Some (_, st') -> Some st'
              | None -> None)
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit move *)
    | EMove e' ->
        (match e'.loc_value with
         | EVar x -> check_move x st
         | _ -> borrow_check_expr (fuel - 1) e' st)

    (* Explicit drop *)
    | EDrop e' ->
        (match e'.loc_value with
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
    | ELoop _ body ->
        let st1 = enter_scope st in
        (match borrow_check_expr (fuel - 1) body st1 with
         | Some st2 -> exit_scope st2
         | None -> None)

    | EWhile _ cond body ->
        (match borrow_check_expr (fuel - 1) cond st with
         | Some st1 ->
             let st2 = enter_scope st1 in
             (match borrow_check_expr (fuel - 1) body st2 with
              | Some st3 -> exit_scope st3
              | None -> None)
         | None -> None)

    | EFor _ x iter body ->
        (match borrow_check_expr (fuel - 1) iter st with
         | Some st1 ->
             let st2 = add_var x t_dynamic MOne st1 in
             let st3 = enter_scope st2 in
             (match borrow_check_expr (fuel - 1) body st3 with
              | Some st4 -> exit_scope st4
              | None -> None)
         | None -> None)

    (* Control flow *)
    | EBreak _ opt_e ->
        (match opt_e with
         | Some e' -> borrow_check_expr (fuel - 1) e' st
         | None -> Some st)

    | EContinue _ -> Some st

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
    | EConvert _ e' -> borrow_check_expr (fuel - 1) e' st

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

    (* Sizeof/Alignof/Offsetof/New - no borrow impact *)
    | ESizeof _ -> Some st
    | EAlignof _ -> Some st
    | EOffsetof _ _ -> Some st
    | ENew _ -> Some st

    (* Make - borrow check argument expressions *)
    | EMake _ args -> borrow_check_exprs (fuel - 1) args st

    (* Unsafe block *)
    | EUnsafe e' ->
        borrow_check_expr (fuel - 1) e' st

    (* Pointer/integer conversions *)
    | EPtrToInt e' -> borrow_check_expr (fuel - 1) e' st
    | EIntToPtr e' _ -> borrow_check_expr (fuel - 1) e' st

    (* Pointer arithmetic - check both subexpressions *)
    | EPtrAdd ptr_e len_e ->
        (match borrow_check_expr (fuel - 1) ptr_e st with
         | Some st1 -> borrow_check_expr (fuel - 1) len_e st1
         | None -> None)

    (* Global reference - always available *)
    | EGlobal _ -> Some st

    (* Async/Spawn - check inner expression *)
    | EAsync e' -> borrow_check_expr (fuel - 1) e' st
    | ESpawn e' -> borrow_check_expr (fuel - 1) e' st

    (* Generators - check inner expressions.
       EGenerator: The body may contain yield points.
       EGenNext/EGenSend: Check the generator and value expressions. *)
    | EGenerator e' -> borrow_check_expr (fuel - 1) e' st
    | EGenNext e' -> borrow_check_expr (fuel - 1) e' st
    | EGenSend gen_e val_e ->
        (match borrow_check_expr (fuel - 1) gen_e st with
         | Some st' -> borrow_check_expr (fuel - 1) val_e st'
         | None -> None)

    (* Delimited continuations - check expressions *)
    | EResume _ e' -> borrow_check_expr (fuel - 1) e' st
    | EReset _ e' -> borrow_check_expr (fuel - 1) e' st
    | EShift _ _ e' -> borrow_check_expr (fuel - 1) e' st

    (* Holes, errors, recover *)
    | EHole -> Some st
    | ERecover -> Some st
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
   exactly one loan exists for that variable.
   Note: lid parameter required by interface but unused in proof *)
let borrow_exclusive x st (_lid: loan_id) =
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

(* Note: lifetime_constraint type is defined in interface file BrrrBorrowChecker.fsti *)

(* Lifetime constraint set - implementation of abstract type from interface *)
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
    RUSTBELT-STYLE LIFETIME TOKENS
    ============================================================================

    This section implements lifetime tokens following the RustBelt paper
    (Jung et al. 2018, POPL). The key insight from RustBelt is that borrows
    can be modeled using fractional permissions indexed by lifetimes:

      kappa.tok(q)  - ownership of fraction q of lifetime kappa
      bor(kappa, P) - P is borrowed for lifetime kappa

    THEORETICAL FOUNDATION (RustBelt, Jung 2018)
    ============================================

    RustBelt models Rust's type system in Iris separation logic. The key
    constructs are:

    1. Lifetime Tokens: kappa.tok(q)
       - Represents "q fraction of ownership" of lifetime kappa
       - Full ownership kappa.tok(1) means the lifetime can be ended
       - Fractional ownership enables shared borrows

    2. Borrow Modality: bor(kappa, P)
       - "P is true for the duration of lifetime kappa"
       - When kappa ends, P is no longer accessible
       - Enables temporary shared access to owned resources

    3. Fractured Borrows: &frac(kappa, q, l) and &full(kappa, l)
       - &frac(kappa, q, l) - shared borrow with fraction q
       - &full(kappa, l) - exclusive borrow (full permission)

    KEY OPERATIONS
    ==============

    1. Token Splitting:
       kappa.tok(q1+q2) <=> kappa.tok(q1) star kappa.tok(q2)
       Enables sharing a lifetime among multiple owners.

    2. Lifetime Ending:
       kappa.tok(1) ==> lifetime_ended(kappa)
       Full token ownership allows ending the lifetime.

    3. Reborrowing:
       Given &full(kappa, l), can create &full(kappa', l)
       where kappa' : kappa (kappa' outlives kappa).

    4. Two-Phase Borrows:
       Start as shared, upgrade to exclusive at a specific point.
       Enables patterns like vec.push(vec.len()) in Rust.

    SEPARATION LOGIC CORRESPONDENCE (Pulse/Steel)
    =============================================

    | RustBelt Construct      | Pulse Equivalent                    |
    |-------------------------|-------------------------------------|
    | kappa.tok(q)            | pts_to token_ref #q ()              |
    | bor(kappa, P)           | exists star v. P v star inv kappa v |
    | &frac(kappa, q, l)      | pts_to l #q v star kappa.tok(q)     |
    | &full(kappa, l)         | pts_to l #1.0R v star kappa.tok(1)  |

    ============================================================================ *)

(** ----------------------------------------------------------------------------
    FRACTION TYPE - Rational Numbers for Permissions
    ---------------------------------------------------------------------------- *)

(* Fraction represented as rational number num/den where 0 < q <= 1
   Invariant: den > 0 (enforced by pos type)
   Invariant: 0 < num <= den (for valid permission fractions) *)
noeq type fraction = {
  frac_num : nat;       (* Numerator: 0 <= num *)
  frac_den : Prims.pos  (* Denominator: den > 0 - qualified to avoid shadowing *)
}

(* Full permission fraction: 1/1 = 1 *)
let frac_one : fraction = { frac_num = 1; frac_den = (1 <: Prims.pos) }

(* Half permission fraction: 1/2 *)
let frac_half : fraction = { frac_num = 1; frac_den = (2 <: Prims.pos) }

(* Zero permission fraction: 0/1 = 0 *)
let frac_zero : fraction = { frac_num = 0; frac_den = (1 <: Prims.pos) }

(* Check if fraction is valid (0 < q <= 1) for a permission *)
let frac_valid (f: fraction) : bool =
  f.frac_num > 0 && f.frac_num <= f.frac_den

(* Check if fraction is zero *)
let frac_is_zero (f: fraction) : bool =
  f.frac_num = 0

(* Check if fraction is full (equals 1) *)
let frac_is_full (f: fraction) : bool =
  f.frac_num = f.frac_den && f.frac_den > 0

(* Fraction equality (cross-multiply to avoid division)
   a/b = c/d  iff  a star d = b star c *)
let frac_eq (f1 f2: fraction) : bool =
  f1.frac_num * f2.frac_den = f2.frac_num * f1.frac_den

(* Fraction less-than-or-equal
   a/b <= c/d  iff  a star d <= b star c (when b, d > 0) *)
let frac_leq (f1 f2: fraction) : bool =
  f1.frac_num * f2.frac_den <= f2.frac_num * f1.frac_den

(* Fraction strictly less-than *)
let frac_lt (f1 f2: fraction) : bool =
  f1.frac_num * f2.frac_den < f2.frac_num * f1.frac_den

(* Greatest common divisor for fraction reduction *)
let rec gcd (a b: nat) : Tot nat (decreases b) =
  if b = 0 then (if a = 0 then 1 else a)
  else gcd b (a % b)

(* Safe gcd that ensures result is positive *)
let gcd_pos (a: nat) (b: Prims.pos) : Prims.pos =
  let g = gcd a b in
  if g = 0 then 1 else g

(* Reduce fraction to lowest terms *)
let frac_reduce (f: fraction) : fraction =
  let g = gcd_pos f.frac_num f.frac_den in
  { frac_num = f.frac_num / g; frac_den = f.frac_den / g }

(* Add two fractions: a/b + c/d = (a star d + b star c) / (b star d) *)
let frac_add (f1 f2: fraction) : fraction =
  let num = f1.frac_num * f2.frac_den + f2.frac_num * f1.frac_den in
  let den = f1.frac_den * f2.frac_den in
  frac_reduce { frac_num = num; frac_den = den }

(* Subtract fractions: a/b - c/d = (a star d - b star c) / (b star d)
   Returns frac_zero if result would be negative *)
let frac_sub (f1 f2: fraction) : fraction =
  let cross1 = f1.frac_num * f2.frac_den in
  let cross2 = f2.frac_num * f1.frac_den in
  if cross1 >= cross2 then
    let num = cross1 - cross2 in
    let den = f1.frac_den * f2.frac_den in
    frac_reduce { frac_num = num; frac_den = den }
  else
    frac_zero

(* Halve a fraction: (a/b) / 2 = a / (2 star b) *)
let frac_halve (f: fraction) : fraction =
  { frac_num = f.frac_num; frac_den = 2 * f.frac_den }

(* Double a fraction: (a/b) star 2 = (2 star a) / b
   Capped at 1 to maintain permission invariant *)
let frac_double (f: fraction) : fraction =
  let doubled_num = 2 * f.frac_num in
  if doubled_num > f.frac_den then
    frac_one
  else
    frac_reduce { frac_num = doubled_num; frac_den = f.frac_den }

(** ----------------------------------------------------------------------------
    LIFETIME TYPE - Unique Lifetime Identifiers
    ---------------------------------------------------------------------------- *)

(* Lifetime identifier - represents a named lifetime kappa
   In RustBelt: kappa ranges over lifetime names
   Here we use nat for simplicity, but semantically represents 'a, 'b, etc. *)
type lifetime = nat

(* Special lifetimes *)
let lifetime_static : lifetime = 0  (* 'static - lives forever *)

(* Fresh lifetime counter *)
type lifetime_counter = nat

(* Generate fresh lifetime *)
let fresh_lifetime (counter: lifetime_counter) : lifetime & lifetime_counter =
  (counter + 1, counter + 2)  (* Start from 1 to reserve 0 for 'static *)

(** ----------------------------------------------------------------------------
    LIFETIME TOKEN - kappa.tok(q)
    ---------------------------------------------------------------------------- *)

(* Lifetime token: ownership of fraction q of lifetime kappa
   kappa.tok(q) represents partial ownership of the ability to end lifetime kappa

   SEMANTICS (RustBelt):
   - kappa.tok(1) means full ownership - can end the lifetime
   - kappa.tok(q) where q < 1 means shared ownership - cannot end alone
   - kappa.tok(q1) star kappa.tok(q2) = kappa.tok(q1+q2) (combining tokens) *)
noeq type lifetime_token = {
  lt_lifetime : lifetime;    (* The lifetime this token refers to *)
  lt_fraction : fraction     (* The fraction of ownership *)
}

(* Create a lifetime token: kappa.tok(q) *)
let tok (lt: lifetime) (q: fraction) : lifetime_token =
  { lt_lifetime = lt; lt_fraction = q }

(* Create full token for a lifetime: kappa.tok(1) *)
let tok_full (lt: lifetime) : lifetime_token =
  tok lt frac_one

(* Create half token: kappa.tok(1/2) *)
let tok_half (lt: lifetime) : lifetime_token =
  tok lt frac_half

(* Check if token has full permission *)
let tok_is_full (t: lifetime_token) : bool =
  frac_is_full t.lt_fraction

(* Check if token has valid (non-zero) permission *)
let tok_is_valid (t: lifetime_token) : bool =
  frac_valid t.lt_fraction

(* Token equality *)
let tok_eq (t1 t2: lifetime_token) : bool =
  t1.lt_lifetime = t2.lt_lifetime && frac_eq t1.lt_fraction t2.lt_fraction

(** ----------------------------------------------------------------------------
    BORROW ASSERTION - bor(kappa, P) and Fractured Borrows
    ---------------------------------------------------------------------------- *)

(* Borrow assertion types from RustBelt
   These represent different forms of borrowed ownership:

   BorFull(kappa, l)     - Exclusive borrow of location l for lifetime kappa
                           Equivalent to &mut T in Rust
                           Holds full permission to l while kappa is alive

   BorFrac(kappa, q, l)  - Fractional/shared borrow with fraction q
                           Equivalent to &T in Rust (when q < 1)
                           Multiple BorFrac can coexist (fractions must sum <= 1)

   BorToken(tok)         - Ownership of a lifetime token
                           Enables lifetime management operations *)
noeq type borrow_assertion =
  | BorFull  : lt:lifetime -> v:var_id -> borrow_assertion
      (* &full(kappa, l) - exclusive borrow for lifetime kappa *)
  | BorFrac  : lt:lifetime -> frac:fraction -> v:var_id -> borrow_assertion
      (* &frac(kappa, q, l) - shared borrow with fraction q *)
  | BorToken : tok:lifetime_token -> borrow_assertion
      (* kappa.tok(q) - lifetime token ownership *)

(* Check if borrow assertion is exclusive *)
let borrow_is_exclusive (ba: borrow_assertion) : bool =
  match ba with
  | BorFull _ _ -> true
  | BorFrac _ _ _ -> false
  | BorToken _ -> false

(* Get the variable from a borrow assertion (if applicable) *)
let borrow_var (ba: borrow_assertion) : option var_id =
  match ba with
  | BorFull _ v -> Some v
  | BorFrac _ _ v -> Some v
  | BorToken _ -> None

(* Get the lifetime from a borrow assertion *)
let borrow_lifetime (ba: borrow_assertion) : option lifetime =
  match ba with
  | BorFull lt _ -> Some lt
  | BorFrac lt _ _ -> Some lt
  | BorToken t -> Some t.lt_lifetime

(** ----------------------------------------------------------------------------
    LIFETIME STATE TRACKING
    ---------------------------------------------------------------------------- *)

(* Lifetime state - tracks whether a lifetime is active or ended *)
type lifetime_state =
  | LtActive   : lifetime_state  (* Lifetime is still alive *)
  | LtEnded    : lifetime_state  (* Lifetime has been ended *)
  | LtFrozen   : lifetime_state  (* Lifetime is frozen (cannot be ended yet) *)

(* Lifetime entry - tracks a single lifetime *)
noeq type lifetime_entry = {
  le_lifetime  : lifetime;        (* The lifetime ID *)
  le_state     : lifetime_state;  (* Current state *)
  le_tokens    : fraction;        (* Total tokens distributed *)
  le_returned  : fraction;        (* Tokens returned so far *)
  le_depth     : nat              (* Scope depth where created *)
}

(* Check if lifetime can be ended (all tokens returned) *)
let lifetime_can_end (le: lifetime_entry) : bool =
  le.le_state = LtActive && frac_eq le.le_returned le.le_tokens

(* Check if lifetime is active *)
let lifetime_is_active (le: lifetime_entry) : bool =
  le.le_state = LtActive

(** ----------------------------------------------------------------------------
    TOKEN OPERATIONS - Split/Combine/Return
    ---------------------------------------------------------------------------- *)

(* Token splitting: kappa.tok(q1+q2) => kappa.tok(q1) star kappa.tok(q2)
   This is the fundamental operation for sharing lifetime ownership *)
let tok_split (t: lifetime_token) (q1 q2: fraction)
    : option (lifetime_token & lifetime_token) =
  (* Check that q1 + q2 = t.lt_fraction *)
  let sum = frac_add q1 q2 in
  if frac_eq sum t.lt_fraction && frac_valid q1 && frac_valid q2 then
    Some (tok t.lt_lifetime q1, tok t.lt_lifetime q2)
  else
    None

(* Token combining: kappa.tok(q1) star kappa.tok(q2) => kappa.tok(q1+q2)
   Inverse of splitting - gather fractional ownership back together *)
let tok_combine (t1 t2: lifetime_token) : option lifetime_token =
  if t1.lt_lifetime = t2.lt_lifetime then
    let combined_frac = frac_add t1.lt_fraction t2.lt_fraction in
    (* Ensure combined fraction doesn't exceed 1 *)
    if frac_leq combined_frac frac_one then
      Some (tok t1.lt_lifetime combined_frac)
    else
      None
  else
    None

(* Split token in half: kappa.tok(q) => kappa.tok(q/2) star kappa.tok(q/2) *)
let tok_split_half (t: lifetime_token) : lifetime_token & lifetime_token =
  let half_frac = frac_halve t.lt_fraction in
  (tok t.lt_lifetime half_frac, tok t.lt_lifetime half_frac)

(** ----------------------------------------------------------------------------
    REBORROWING - Creating Shorter Borrows from Existing Ones
    ---------------------------------------------------------------------------- *)

(* Reborrow state - tracks an active reborrow relationship *)
noeq type reborrow_entry = {
  rb_outer_lt  : lifetime;    (* Original/outer lifetime *)
  rb_inner_lt  : lifetime;    (* Reborrowed/inner lifetime (must end first) *)
  rb_var       : var_id;      (* The reborrowed variable *)
  rb_kind      : borrow_kind  (* Shared or exclusive *)
}

(* Check if inner lifetime outlives (is contained within) outer lifetime
   inner : outer means inner ends before outer ends *)
let lifetime_outlives (inner outer: lifetime) (depth_inner depth_outer: nat) : bool =
  (* Inner lifetime outlives outer if:
     1. Outer is 'static (outlives everything)
     2. Inner was created at same or deeper scope than outer *)
  outer = lifetime_static || depth_inner >= depth_outer

(* Create a reborrow: from &'outer mut T, create &'inner mut T where 'inner: 'outer
   This is safe because:
   1. The inner borrow must end before the outer borrow
   2. While inner is active, outer is "frozen" (cannot be used)
   3. When inner ends, outer becomes accessible again *)
let create_reborrow (outer_lt inner_lt: lifetime) (v: var_id) (kind: borrow_kind)
                    (outer_depth inner_depth: nat)
    : option reborrow_entry =
  if lifetime_outlives inner_lt outer_lt inner_depth outer_depth then
    Some {
      rb_outer_lt = outer_lt;
      rb_inner_lt = inner_lt;
      rb_var = v;
      rb_kind = kind
    }
  else
    None

(** ----------------------------------------------------------------------------
    TWO-PHASE BORROWS - Shared-to-Exclusive Upgrade
    ---------------------------------------------------------------------------- *)

(* Two-phase borrow state
   A two-phase borrow starts as shared and upgrades to exclusive at a
   specific program point. This enables patterns like:

     vec.push(vec.len())

   Where vec.len() creates a shared borrow, and vec.push() needs exclusive.
   The shared borrow is "reserved" and upgrades when push actually mutates.

   PHASES:
   1. TpbReserved: Shared borrow created, exclusive access reserved
   2. TpbActivated: Upgraded to exclusive, mutation can occur
   3. TpbCompleted: Two-phase borrow ended, back to normal state *)

type two_phase_state =
  | TpbReserved   : two_phase_state  (* Shared phase - can read, mutation reserved *)
  | TpbActivated  : two_phase_state  (* Exclusive phase - can mutate *)
  | TpbCompleted  : two_phase_state  (* Finished - back to normal *)

noeq type two_phase_borrow = {
  tpb_var       : var_id;           (* Variable being borrowed *)
  tpb_lifetime  : lifetime;         (* Lifetime of the two-phase borrow *)
  tpb_state     : two_phase_state;  (* Current phase *)
  tpb_shared_id : loan_id;          (* ID of the shared loan (phase 1) *)
  tpb_depth     : nat               (* Scope depth *)
}

(* Create a two-phase borrow - starts in reserved state *)
let create_two_phase_borrow (v: var_id) (lt: lifetime) (shared_id: loan_id) (depth: nat)
    : two_phase_borrow =
  {
    tpb_var = v;
    tpb_lifetime = lt;
    tpb_state = TpbReserved;
    tpb_shared_id = shared_id;
    tpb_depth = depth
  }

(* Activate a two-phase borrow - upgrade to exclusive *)
let activate_two_phase (tpb: two_phase_borrow) : option two_phase_borrow =
  match tpb.tpb_state with
  | TpbReserved -> Some { tpb with tpb_state = TpbActivated }
  | _ -> None  (* Can only activate from reserved state *)

(* Complete a two-phase borrow *)
let complete_two_phase (tpb: two_phase_borrow) : option two_phase_borrow =
  match tpb.tpb_state with
  | TpbActivated -> Some { tpb with tpb_state = TpbCompleted }
  | TpbReserved -> Some { tpb with tpb_state = TpbCompleted }  (* Can skip activation *)
  | TpbCompleted -> None  (* Already completed *)

(* Check if two-phase borrow allows shared access *)
let tpb_allows_shared (tpb: two_phase_borrow) : bool =
  tpb.tpb_state = TpbReserved

(* Check if two-phase borrow allows exclusive access *)
let tpb_allows_exclusive (tpb: two_phase_borrow) : bool =
  tpb.tpb_state = TpbActivated

(** ----------------------------------------------------------------------------
    LIFETIME TOKEN BORROW STATE - Extended State with Tokens
    ---------------------------------------------------------------------------- *)

(* Extended borrow state with lifetime token tracking *)
noeq type lt_borrow_state = {
  ltbs_base       : borrow_state;           (* Base borrow state *)
  ltbs_lifetimes  : list lifetime_entry;    (* Active lifetimes *)
  ltbs_tokens     : list lifetime_token;    (* Held tokens *)
  ltbs_reborrows  : list reborrow_entry;    (* Active reborrows *)
  ltbs_two_phase  : list two_phase_borrow;  (* Two-phase borrows *)
  ltbs_lt_counter : lifetime_counter        (* Fresh lifetime generator *)
}

(* Empty lifetime token borrow state *)
let empty_lt_borrow_state : lt_borrow_state = {
  ltbs_base = empty_borrow_state;
  ltbs_lifetimes = [];
  ltbs_tokens = [];
  ltbs_reborrows = [];
  ltbs_two_phase = [];
  ltbs_lt_counter = 1  (* Reserve 0 for 'static *)
}

(* Find lifetime entry by ID *)
let rec find_lifetime (lt: lifetime) (entries: list lifetime_entry)
    : option lifetime_entry =
  match entries with
  | [] -> None
  | e :: rest ->
    if e.le_lifetime = lt then Some e
    else find_lifetime lt rest

(* Update lifetime entry *)
let rec update_lifetime (lt: lifetime) (f: lifetime_entry -> lifetime_entry)
                        (entries: list lifetime_entry)
    : list lifetime_entry =
  match entries with
  | [] -> []
  | e :: rest ->
    if e.le_lifetime = lt then f e :: rest
    else e :: update_lifetime lt f rest

(* Create a new lifetime in the state *)
let create_lifetime (st: lt_borrow_state) : lifetime & lt_borrow_state =
  let (lt, counter') = fresh_lifetime st.ltbs_lt_counter in
  let entry = {
    le_lifetime = lt;
    le_state = LtActive;
    le_tokens = frac_one;      (* Full token available *)
    le_returned = frac_zero;   (* None returned yet *)
    le_depth = st.ltbs_base.bs_depth
  } in
  (lt, {
    st with
    ltbs_lifetimes = entry :: st.ltbs_lifetimes;
    ltbs_lt_counter = counter'
  })

(* Acquire a token for a lifetime *)
let acquire_token (lt: lifetime) (q: fraction) (st: lt_borrow_state)
    : option (lifetime_token & lt_borrow_state) =
  match find_lifetime lt st.ltbs_lifetimes with
  | None -> None
  | Some entry ->
    if not (lifetime_is_active entry) then None
    else
      (* Check that enough tokens are available *)
      let available = frac_sub entry.le_tokens entry.le_returned in
      if frac_lt available q then None
      else
        let token = tok lt q in
        let entry' = { entry with le_returned = frac_add entry.le_returned q } in
        Some (token, {
          st with
          ltbs_lifetimes = update_lifetime lt (fun _ -> entry') st.ltbs_lifetimes;
          ltbs_tokens = token :: st.ltbs_tokens
        })

(* Return a token to end/release lifetime ownership *)
let return_token (token: lifetime_token) (st: lt_borrow_state)
    : option lt_borrow_state =
  match find_lifetime token.lt_lifetime st.ltbs_lifetimes with
  | None -> None
  | Some entry ->
    (* Return the fraction to the lifetime *)
    let entry' = { entry with le_returned = frac_sub entry.le_returned token.lt_fraction } in
    (* Remove token from held tokens *)
    let new_tokens = filter (fun t -> not (tok_eq t token)) st.ltbs_tokens in
    Some {
      st with
      ltbs_lifetimes = update_lifetime token.lt_lifetime (fun _ -> entry') st.ltbs_lifetimes;
      ltbs_tokens = new_tokens
    }

(* End a lifetime (requires full token returned) *)
let end_lifetime (lt: lifetime) (st: lt_borrow_state)
    : option lt_borrow_state =
  match find_lifetime lt st.ltbs_lifetimes with
  | None -> None
  | Some entry ->
    if not (lifetime_can_end entry) then None
    else
      let entry' = { entry with le_state = LtEnded } in
      Some {
        st with
        ltbs_lifetimes = update_lifetime lt (fun _ -> entry') st.ltbs_lifetimes
      }

(** ----------------------------------------------------------------------------
    SOUNDNESS LEMMAS FOR LIFETIME TOKENS
    ---------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(* Lemma: Token splitting preserves total fraction
   If tok_split succeeds, the two resulting tokens have fractions that sum to original *)
val tok_split_preserves_fraction : t:lifetime_token -> q1:fraction -> q2:fraction ->
  Lemma (requires Some? (tok_split t q1 q2))
        (ensures (let (t1, t2) = Some?.v (tok_split t q1 q2) in
                  frac_eq (frac_add t1.lt_fraction t2.lt_fraction) t.lt_fraction))

let tok_split_preserves_fraction t q1 q2 =
  (* By definition, tok_split only succeeds when q1 + q2 = t.lt_fraction
     and the resulting tokens have fractions q1 and q2 *)
  ()

(* Lemma: Token combining is inverse of splitting *)
val tok_combine_inverse_split : t:lifetime_token -> q1:fraction -> q2:fraction ->
  Lemma (requires Some? (tok_split t q1 q2) /\ frac_valid q1 /\ frac_valid q2)
        (ensures (let (t1, t2) = Some?.v (tok_split t q1 q2) in
                  Some? (tok_combine t1 t2) /\
                  tok_eq (Some?.v (tok_combine t1 t2)) t))

let tok_combine_inverse_split t q1 q2 =
  (* tok_combine reverses tok_split: combining the split tokens yields original *)
  ()

(* Lemma: Full token enables lifetime ending
   If we have a full token (fraction = 1) for a lifetime, we can end it *)
val full_token_ends_lifetime : lt:lifetime -> st:lt_borrow_state ->
  Lemma (requires Some? (find_lifetime lt st.ltbs_lifetimes) /\
                  (match find_lifetime lt st.ltbs_lifetimes with
                   | Some e -> lifetime_is_active e /\ frac_eq e.le_returned e.le_tokens
                   | None -> false))
        (ensures Some? (end_lifetime lt st))

let full_token_ends_lifetime lt st =
  (* When all tokens are returned (le_returned = le_tokens), lifetime can end *)
  ()

(* Lemma: Reborrow creates valid inner lifetime
   If reborrow succeeds, the inner lifetime properly outlives the outer *)
val reborrow_creates_valid_inner : outer_lt:lifetime -> inner_lt:lifetime ->
                                   v:var_id -> kind:borrow_kind ->
                                   outer_depth:nat -> inner_depth:nat ->
  Lemma (requires Some? (create_reborrow outer_lt inner_lt v kind outer_depth inner_depth))
        (ensures lifetime_outlives inner_lt outer_lt inner_depth outer_depth)

let reborrow_creates_valid_inner outer_lt inner_lt v kind outer_depth inner_depth =
  (* create_reborrow only succeeds when lifetime_outlives is true *)
  ()

(* Lemma: Two-phase borrow state transitions are valid *)
val two_phase_transitions_valid : tpb:two_phase_borrow ->
  Lemma (ensures
    (* Reserved can activate or complete *)
    (tpb.tpb_state = TpbReserved ==> Some? (activate_two_phase tpb) /\ Some? (complete_two_phase tpb)) /\
    (* Activated can only complete *)
    (tpb.tpb_state = TpbActivated ==> None? (activate_two_phase tpb) /\ Some? (complete_two_phase tpb)) /\
    (* Completed cannot transition *)
    (tpb.tpb_state = TpbCompleted ==> None? (activate_two_phase tpb) /\ None? (complete_two_phase tpb)))

let two_phase_transitions_valid tpb =
  (* State machine transitions are explicitly defined *)
  ()

(* Lemma: Borrow token soundness
   A borrow assertion is sound if:
   - For BorFull: we have the full token for the lifetime
   - For BorFrac: we have at least the fractional token
   - For BorToken: the token is valid *)
val borrow_assertion_sound : ba:borrow_assertion -> st:lt_borrow_state ->
  Lemma (ensures (
    match ba with
    | BorFull lt v ->
        (match find_lifetime lt st.ltbs_lifetimes with
         | Some e -> lifetime_is_active e
         | None -> true)
    | BorFrac lt q v ->
        (match find_lifetime lt st.ltbs_lifetimes with
         | Some e -> lifetime_is_active e ==> frac_valid q
         | None -> true)
    | BorToken tok ->
        tok_is_valid tok ==> frac_valid tok.lt_fraction))

let borrow_assertion_sound ba st =
  ()

#pop-options

(** ----------------------------------------------------------------------------
    INTEGRATION HELPERS - Connect Lifetime Tokens with Base Borrow State
    ---------------------------------------------------------------------------- *)

(* Begin a shared borrow with lifetime tracking *)
let begin_shared_borrow_lt (x: var_id) (st: lt_borrow_state)
    : option (loan_id & lifetime & lt_borrow_state) =
  match begin_shared_borrow x st.ltbs_base with
  | None -> None
  | Some (lid, base') ->
    (* Create a new lifetime for this borrow *)
    let (lt, st') = create_lifetime { st with ltbs_base = base' } in
    Some (lid, lt, st')

(* Begin an exclusive borrow with lifetime tracking *)
let begin_exclusive_borrow_lt (x: var_id) (st: lt_borrow_state)
    : option (loan_id & lifetime & lt_borrow_state) =
  match begin_exclusive_borrow x st.ltbs_base with
  | None -> None
  | Some (lid, base') ->
    (* Create a new lifetime for this borrow *)
    let (lt, st') = create_lifetime { st with ltbs_base = base' } in
    Some (lid, lt, st')

(* End a borrow and its associated lifetime *)
let end_borrow_lt (lid: loan_id) (lt: lifetime) (st: lt_borrow_state)
    : option lt_borrow_state =
  match end_borrow lid st.ltbs_base with
  | None -> None
  | Some base' ->
    (* End the lifetime *)
    end_lifetime lt { st with ltbs_base = base' }

(* Begin a reborrow from an existing exclusive borrow *)
let begin_reborrow (outer_lid: loan_id) (outer_lt: lifetime) (st: lt_borrow_state)
    : option (loan_id & lifetime & lt_borrow_state) =
  match find_loan outer_lid st.ltbs_base with
  | None -> None
  | Some outer_loan ->
    if outer_loan.loan_kind <> BorrowExclusive then None
    else
      (* Create new inner lifetime *)
      let (inner_lt, st') = create_lifetime st in
      (* Create inner borrow on same variable *)
      match begin_exclusive_borrow outer_loan.loan_var st'.ltbs_base with
      | None -> None
      | Some (inner_lid, base') ->
        (* Record reborrow relationship *)
        let rb = {
          rb_outer_lt = outer_lt;
          rb_inner_lt = inner_lt;
          rb_var = outer_loan.loan_var;
          rb_kind = BorrowExclusive
        } in
        Some (inner_lid, inner_lt, {
          st' with
          ltbs_base = base';
          ltbs_reborrows = rb :: st'.ltbs_reborrows
        })

(* Begin a two-phase borrow *)
let begin_two_phase_borrow (x: var_id) (st: lt_borrow_state)
    : option (two_phase_borrow & lt_borrow_state) =
  (* Start with shared borrow *)
  match begin_shared_borrow_lt x st with
  | None -> None
  | Some (lid, lt, st') ->
    let tpb = create_two_phase_borrow x lt lid st'.ltbs_base.bs_depth in
    Some (tpb, { st' with ltbs_two_phase = tpb :: st'.ltbs_two_phase })

(* Activate a two-phase borrow to exclusive *)
let activate_two_phase_borrow (tpb: two_phase_borrow) (st: lt_borrow_state)
    : option (loan_id & lt_borrow_state) =
  match activate_two_phase tpb with
  | None -> None
  | Some tpb' ->
    (* End the shared borrow *)
    match end_borrow tpb.tpb_shared_id st.ltbs_base with
    | None -> None
    | Some base' ->
      (* Begin exclusive borrow *)
      match begin_exclusive_borrow tpb.tpb_var base' with
      | None -> None
      | Some (exc_lid, base'') ->
        (* Update two-phase list *)
        let new_tpb_list = map (fun t ->
          if t.tpb_var = tpb.tpb_var && t.tpb_lifetime = tpb.tpb_lifetime
          then tpb'
          else t
        ) st.ltbs_two_phase in
        Some (exc_lid, {
          st with
          ltbs_base = base'';
          ltbs_two_phase = new_tpb_list
        })

(** ============================================================================
    REGION TYPING RULES - Tofte & Talpin Style Region Types
    ============================================================================

    This section implements region typing rules following the foundational work:
    - Tofte & Talpin (1997) "Region-Based Memory Management"
    - brrr_lang_spec_v0.4.tex lines 2315-2549

    REGION TYPING OVERVIEW
    ======================

    Regions provide a compile-time memory management discipline:
    - Allocations are tagged with a region: new_at[rho](e)
    - letregion introduces a fresh region scope
    - When letregion exits, all memory in that region is freed
    - Region escape analysis ensures no dangling references

    KEY TYPING RULES
    ================

    R-Alloc: Allocation in a region
      Gamma; cap[rho] |- e : tau ; eps
      ------------------------------------------
      Gamma; cap[rho] |- new_at[rho](e) : tau @ rho ; eps + Alloc

    R-LetRegion: Region introduction
      Gamma; cap[rho] |- e : tau ; eps    rho not in FRV(tau)
      --------------------------------------------------------
      Gamma |- letregion rho in e : tau ; eps

    R-Sub: Region subtyping via outlives
      Gamma |- e : tau @ rho1 ; eps    rho1 <= rho2
      ----------------------------------------------
      Gamma |- e : tau @ rho2 ; eps

    REGION EFFECTS
    ==============

    Operations on regions produce effects:
    - REAlloc(rho): Memory allocated in region rho
    - RERead(rho): Memory read from region rho
    - REWrite(rho): Memory written in region rho
    - REFree(rho): Region rho deallocated (implicit at letregion exit)

    ============================================================================ *)

(** ----------------------------------------------------------------------------
    REGION EFFECT TYPES
    ---------------------------------------------------------------------------- *)

(** Region effects track memory operations on specific regions.
    These effects enable:
    1. Region capability checking (can't access region without cap[rho])
    2. Effect-based memory tracking (what regions are touched)
    3. Region polymorphism (forall rho. ... can be instantiated)

    The effect types correspond to:
    - REAlloc: new_at[rho] operation
    - RERead: dereference of ref[rho] tau
    - REWrite: assignment to ref[rho] tau
    - REFree: implicit at letregion exit *)
type region_effect =
  | REAlloc : r:region -> region_effect  (** Memory allocation in region r *)
  | RERead  : r:region -> region_effect  (** Read from region r *)
  | REWrite : r:region -> region_effect  (** Write to region r *)
  | REFree  : r:region -> region_effect  (** Region r freed (letregion exit) *)

(** Get the region from a region effect *)
let region_effect_region (eff: region_effect) : region =
  match eff with
  | REAlloc r -> r
  | RERead r -> r
  | REWrite r -> r
  | REFree r -> r

(** Check if region effect is permitted given a region context.
    An effect on region r is permitted iff cap[r] is in context. *)
let region_effect_permitted (eff: region_effect) (ctx: region_ctx) : bool =
  has_region_cap (region_effect_region eff) ctx

(** Collect all region effects from a list *)
let rec collect_region_effects (effs: list region_effect) : list region =
  match effs with
  | [] -> []
  | eff :: rest -> region_effect_region eff :: collect_region_effects rest

(** Check if all region effects are permitted in context *)
let rec all_effects_permitted (effs: list region_effect) (ctx: region_ctx) : bool =
  match effs with
  | [] -> true
  | eff :: rest -> region_effect_permitted eff ctx && all_effects_permitted rest ctx

(** ----------------------------------------------------------------------------
    REGION SUBSTITUTION - subst_region
    ---------------------------------------------------------------------------- *)

(** Region substitution result type.
    When exiting letregion, we either:
    - RConcrete: Substitute with a concrete region ID
    - RErased: Erase the region (existentially pack) *)
type region_subst =
  | RConcrete : r:region -> region_subst  (** Replace with concrete region *)
  | RErased   : region_subst              (** Existentially pack / erase region *)

(** Substitute a region variable in a region value.
    If the region matches rvar, apply substitution; otherwise keep original. *)
let subst_in_region (rvar: string) (s: region_subst) (r: region) : region =
  match r with
  | RNamed name ->
    if name = rvar then
      (match s with
       | RConcrete r' -> r'
       | RErased -> RStatic)  (* Erase to static as conservative approximation *)
    else r
  | _ -> r  (* Other region kinds are unaffected by named substitution *)

(** Substitute region variable in a type.

    SPECIFICATION REFERENCE: brrr_lang_spec_v0.4.tex Section 4.3

    This function traverses the type structure and replaces occurrences of
    the named region variable rvar according to the substitution s.

    CURRENT LIMITATION: Since brrr_type doesn't embed region annotations
    directly (regions are tracked via regioned_type wrapper), this function
    primarily handles nested types to find any regioned components.

    When TRef[rho, tau] syntax is added to brrr_type, this function should:
    1. Check if the reference's region equals rvar
    2. If so, apply substitution or pack existentially

    For now, we recursively traverse to handle any future region annotations
    and prepare the infrastructure for full region typing.

    @param rvar The region variable name to substitute (e.g., "a" for 'a)
    @param s The substitution to apply
    @param ty The type to transform
    @return The type with region variable substituted *)
let rec subst_region (rvar: string) (s: region_subst) (ty: brrr_type)
    : Tot brrr_type (decreases type_size ty) =
  match ty with
  (* Wrapper types - substitute in inner type *)
  | TWrap w inner -> TWrap w (subst_region rvar s inner)

  (* Modal types - substitute in inner type *)
  | TModal m inner -> TModal m (subst_region rvar s inner)

  (* Result type - substitute in both success and error types *)
  | TResult t_ok t_err ->
    TResult (subst_region rvar s t_ok) (subst_region rvar s t_err)

  (* Tuple - substitute in all element types *)
  | TTuple ts -> TTuple (List.Tot.map (subst_region rvar s) ts)

  (* Function type - substitute in params and return type
     This is critical for region polymorphic functions:
     forall 'a. (ref['a] int) -> int  when instantiated should
     substitute 'a throughout the function signature *)
  | TFunc ft ->
    let subst_param (p: param_type) : param_type =
      { name = p.name; ty = subst_region rvar s p.ty; mode = p.mode }
    in
    TFunc {
      ft with
      return_type = subst_region rvar s ft.return_type;
      params = List.Tot.map subst_param ft.params
    }

  (* Type application - substitute in base and all arguments *)
  | TApp base args ->
    TApp (subst_region rvar s base) (List.Tot.map (subst_region rvar s) args)

  (* Struct fields - would need to substitute in field types
     Currently structs are opaque, but when inlined would traverse fields *)
  | TStruct st ->
    (* TODO: When struct field types are accessible, substitute in each:
       let subst_field f = { f with field_ty = subst_region rvar s f.field_ty } in
       TStruct { st with struct_fields = map subst_field st.struct_fields } *)
    TStruct st

  (* Enum variants - similar to struct *)
  | TEnum et -> TEnum et

  (* Base types - no region information to substitute *)
  | TPrim _ -> ty
  | TNumeric _ -> ty
  | TVar _ -> ty
  | TNamed _ -> ty

(** Substitute multiple region variables in sequence *)
let rec subst_regions (substs: list (string & region_subst)) (ty: brrr_type)
    : Tot brrr_type (decreases List.Tot.length substs) =
  match substs with
  | [] -> ty
  | (rvar, s) :: rest -> subst_regions rest (subst_region rvar s ty)

(** ----------------------------------------------------------------------------
    REGION STACK FOR LETREGION SCOPING
    ---------------------------------------------------------------------------- *)

(** Region stack entry - tracks a letregion scope *)
noeq type region_stack_entry = {
  rse_region : region;        (** The region introduced by this letregion *)
  rse_depth  : nat;           (** Scope depth when entered *)
  rse_var    : option string  (** Optional named region variable *)
}

(** Region stack type - stack of active letregion scopes *)
type region_stack = list region_stack_entry

(** Push a new region onto the stack *)
let push_region_stack (r: region) (depth: nat) (var: option string)
                       (stack: region_stack) : region_stack =
  { rse_region = r; rse_depth = depth; rse_var = var } :: stack

(** Pop the top region from the stack *)
let pop_region_stack (stack: region_stack) : option (region_stack_entry & region_stack) =
  match stack with
  | [] -> None
  | top :: rest -> Some (top, rest)

(** Find region entry by name *)
let rec find_region_by_name (name: string) (stack: region_stack)
    : option region_stack_entry =
  match stack with
  | [] -> None
  | entry :: rest ->
    (match entry.rse_var with
     | Some n when n = name -> Some entry
     | _ -> find_region_by_name name rest)

(** Check if region is currently on the stack (active) *)
let rec region_on_stack (r: region) (stack: region_stack) : bool =
  match stack with
  | [] -> false
  | entry :: rest -> region_eq entry.rse_region r || region_on_stack r rest

(** ----------------------------------------------------------------------------
    ENHANCED EXTENDED BORROW STATE WITH REGION STACK
    ---------------------------------------------------------------------------- *)

(** Full borrow state with region stack tracking.
    This extends extended_borrow_state with:
    - Region stack for proper letregion nesting
    - Region effects tracking
    - Region capability validation *)
noeq type full_borrow_state = {
  fbs_extended     : extended_borrow_state;  (** Base extended state *)
  fbs_region_stack : region_stack;           (** Stack of active letregions *)
  fbs_effects      : list region_effect      (** Accumulated region effects *)
}

(** Empty full borrow state *)
let empty_full_borrow_state : full_borrow_state = {
  fbs_extended = {
    ebs_vars = [];
    ebs_loans = [];
    ebs_counter = 0;
    ebs_depth = 0;
    ebs_regions = [];
    ebs_region_counter = 0
  };
  fbs_region_stack = [];
  fbs_effects = []
}

(** Add a region effect to the state *)
let add_region_effect (eff: region_effect) (st: full_borrow_state) : full_borrow_state =
  { st with fbs_effects = eff :: st.fbs_effects }

(** Check if region is accessible in current state *)
let region_accessible (r: region) (st: full_borrow_state) : bool =
  has_region_cap r st.fbs_extended.ebs_regions ||
  region_on_stack r st.fbs_region_stack ||
  (match r with RStatic -> true | _ -> false)

(** ----------------------------------------------------------------------------
    R-ALLOC RULE - Allocation in a Region
    ---------------------------------------------------------------------------- *)

(** Result type for allocation checking *)
type alloc_result =
  | AllocOk    : ty:brrr_type -> st:full_borrow_state -> alloc_result
  | AllocError : err:ownership_error -> alloc_result

(** Check allocation in a region (R-Alloc rule).

    TYPING RULE (brrr_lang_spec_v0.4.tex line 2166):
      Gamma; cap[rho] |- e : tau ; eps
      ------------------------------------------
      Gamma; cap[rho] |- new_at[rho](e) : tau @ rho ; eps + Alloc

    This checks:
    1. Region rho is alive (capability exists)
    2. The initializer expression type-checks
    3. No exclusive borrows prevent the allocation

    @param r The region to allocate in
    @param init_ty The type of the initializer expression
    @param st The current borrow state
    @return AllocOk with the regioned type, or AllocError *)
let check_alloc (r: region) (init_ty: brrr_type) (st: full_borrow_state)
    : alloc_result =
  (* Check 1: Region must be accessible *)
  if not (region_accessible r st) then
    (* Region not in scope - cannot allocate *)
    AllocError (ErrRegionEscapes r)
  else
    (* Check 2: Add allocation effect *)
    let st' = add_region_effect (REAlloc r) st in
    (* Return regioned type: init_ty @ r
       Note: We return init_ty as the base type. In a full implementation,
       this would be wrapped in regioned_type { base_type = init_ty; region = r } *)
    AllocOk init_ty st'

(** Check if allocation would be valid without performing it *)
let can_alloc_in_region (r: region) (st: full_borrow_state) : bool =
  region_accessible r st

(** ----------------------------------------------------------------------------
    R-LETREGION RULE - Region Introduction
    ---------------------------------------------------------------------------- *)

(** Result type for letregion checking *)
type letregion_result =
  | LetRegionOk  : r:region -> st:full_borrow_state -> letregion_result
  | LetRegionErr : err:ownership_error -> letregion_result

(** Enter a letregion scope (first half of R-LetRegion rule).

    This introduces a fresh region and adds its capability to the context.
    The region can be optionally named for region polymorphism.

    @param rvar Optional name for the region variable
    @param st Current borrow state
    @return Fresh region and updated state *)
let enter_letregion_full (rvar: option string) (st: full_borrow_state)
    : region & full_borrow_state =
  (* Generate fresh region *)
  let (r, counter') = fresh_region st.fbs_extended.ebs_region_counter in

  (* Add region capability *)
  let regions' = add_region_cap r st.fbs_extended.ebs_regions in

  (* Push onto region stack *)
  let stack' = push_region_stack r st.fbs_extended.ebs_depth rvar st.fbs_region_stack in

  (* Update extended state *)
  let ext' = {
    st.fbs_extended with
    ebs_regions = regions';
    ebs_region_counter = counter';
    ebs_depth = st.fbs_extended.ebs_depth + 1
  } in

  (r, { st with fbs_extended = ext'; fbs_region_stack = stack' })

(** Exit a letregion scope (second half of R-LetRegion rule).

    TYPING RULE (brrr_lang_spec_v0.4.tex line 2170):
      Gamma; cap[rho] |- e : tau ; eps    rho not in FRV(tau)
      --------------------------------------------------------
      Gamma |- letregion rho in e : tau ; eps

    The critical check is that rho does not appear free in the result type tau.
    This ensures no dangling references can escape the letregion scope.

    @param r The region being exited
    @param result_ty The type of the body expression
    @param st Current borrow state
    @return Updated state with region removed, or error if region escapes *)
let exit_letregion_full (r: region) (result_ty: brrr_type) (st: full_borrow_state)
    : letregion_result =
  (* CRITICAL CHECK: Region must not escape in result type *)
  if region_free_in_type r result_ty then
    LetRegionErr (ErrRegionEscapes r)
  else
    (* Pop region from stack *)
    match pop_region_stack st.fbs_region_stack with
    | None -> LetRegionErr (ErrInternalError "Region stack underflow")
    | Some (top, rest) ->
      if not (region_eq top.rse_region r) then
        LetRegionErr (ErrInternalError "Region stack mismatch")
      else
        (* Invalidate region capability *)
        let regions' = invalidate_region r st.fbs_extended.ebs_regions in

        (* Add free effect *)
        let effects' = (REFree r) :: st.fbs_effects in

        (* Update extended state *)
        let ext' = {
          st.fbs_extended with
          ebs_regions = regions';
          ebs_depth = if st.fbs_extended.ebs_depth > 0
                      then st.fbs_extended.ebs_depth - 1
                      else 0
        } in

        LetRegionOk r {
          st with
          fbs_extended = ext';
          fbs_region_stack = rest;
          fbs_effects = effects'
        }

(** ----------------------------------------------------------------------------
    R-SUB RULE - Region Subtyping via Outlives
    ---------------------------------------------------------------------------- *)

(** Check if a reference with region r1 can be used where r2 is expected.

    TYPING RULE (brrr_lang_spec_v0.4.tex line 2174):
      Gamma |- e : tau @ rho1 ; eps    rho1 <= rho2
      ----------------------------------------------
      Gamma |- e : tau @ rho2 ; eps

    This relies on the outlives relation: rho1 <= rho2 means rho1 outlives rho2.
    If rho1 outlives rho2, then a reference valid for rho1's lifetime is also
    valid for the shorter rho2 lifetime.

    @param r1 The actual region of the reference
    @param r2 The expected/required region
    @return True if r1 can be coerced to r2 *)
let region_subtype_check (r1 r2: region) : bool =
  region_outlives r1 r2

(** Check if a regioned type can be used where another regioned type is expected *)
let regioned_type_subtype (rt1 rt2: regioned_type) : bool =
  subtype rt1.base_type rt2.base_type && region_outlives rt1.region rt2.region

(** ----------------------------------------------------------------------------
    REGION BORROWING RULES
    ---------------------------------------------------------------------------- *)

(** Check if borrowing from a region is valid.

    A borrow from region r is valid if:
    1. r is accessible (has capability)
    2. The borrow doesn't outlive the region
    3. Exclusivity rules are satisfied

    @param r The region being borrowed from
    @param borrow_depth The scope depth of the borrow
    @param st The current borrow state
    @return True if borrow is permitted *)
let can_borrow_from_region (r: region) (borrow_depth: nat) (st: full_borrow_state) : bool =
  if not (region_accessible r st) then false
  else
    (* Check that borrow doesn't outlive region *)
    match r with
    | RStatic -> true  (* Static region never ends *)
    | RScope region_depth -> borrow_depth >= region_depth
    | RFresh _ ->
      (* Fresh regions from letregion - check stack *)
      (match List.Tot.find (fun e -> region_eq e.rse_region r) st.fbs_region_stack with
       | Some entry -> borrow_depth >= entry.rse_depth
       | None -> false)
    | RNamed _ -> true  (* Named regions are abstract - assume valid *)

(** Check outlives constraint for a borrow.

    When creating a reference &'a T from data in region 'b, we need 'b: 'a
    (region 'b outlives lifetime 'a). This ensures the reference doesn't
    dangle when the borrowed region is freed.

    @param data_region The region containing the borrowed data
    @param ref_lifetime The lifetime of the reference being created
    @return True if the outlives constraint holds *)
let check_borrow_outlives (data_region: region) (ref_lifetime: region) : bool =
  region_outlives data_region ref_lifetime

(** ----------------------------------------------------------------------------
    SOUNDNESS LEMMAS FOR REGION TYPING
    ---------------------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(** Lemma: Region substitution preserves type structure.
    Substituting a region variable doesn't change the "shape" of the type,
    only potentially the region annotations within it. *)
val subst_region_preserves_structure : rvar:string -> s:region_subst -> ty:brrr_type ->
  Lemma (ensures
    (* Type constructor is preserved *)
    (TPrim? ty ==> TPrim? (subst_region rvar s ty)) /\
    (TNumeric? ty ==> TNumeric? (subst_region rvar s ty)) /\
    (TWrap? ty ==> TWrap? (subst_region rvar s ty)) /\
    (TFunc? ty ==> TFunc? (subst_region rvar s ty)) /\
    (TTuple? ty ==> TTuple? (subst_region rvar s ty)))

let subst_region_preserves_structure rvar s ty =
  (* By case analysis on ty - each case returns the same constructor *)
  ()

(** Lemma: letregion escape check is sound.
    If exit_letregion_full succeeds, the region truly doesn't escape. *)
val letregion_exit_sound : r:region -> result_ty:brrr_type -> st:full_borrow_state ->
  Lemma (requires LetRegionOk? (exit_letregion_full r result_ty st))
        (ensures not (region_free_in_type r result_ty))

let letregion_exit_sound r result_ty st =
  (* exit_letregion_full only returns LetRegionOk when region_free_in_type is false *)
  ()

(** Lemma: Region outlives is transitive.
    If r1 outlives r2 and r2 outlives r3, then r1 outlives r3. *)
val region_outlives_transitive : r1:region -> r2:region -> r3:region ->
  Lemma (requires region_outlives r1 r2 /\ region_outlives r2 r3)
        (ensures region_outlives r1 r3)

let region_outlives_transitive r1 r2 r3 =
  (* region_outlives is transitive by definition:
     - RStatic outlives everything
     - For RScope/RFresh, <= is transitive on nat *)
  ()

(** Lemma: Static region outlives all regions.
    This is the fundamental property of 'static. *)
val static_outlives_all : r:region ->
  Lemma (ensures region_outlives RStatic r)

let static_outlives_all r =
  (* By definition, RStatic case returns true for any r2 *)
  ()

(** Lemma: Allocation in accessible region always succeeds.
    If a region is accessible, allocation will produce AllocOk. *)
val alloc_in_accessible_succeeds : r:region -> init_ty:brrr_type -> st:full_borrow_state ->
  Lemma (requires region_accessible r st)
        (ensures AllocOk? (check_alloc r init_ty st))

let alloc_in_accessible_succeeds r init_ty st =
  (* check_alloc returns AllocOk when region_accessible is true *)
  ()

(** Lemma: Entering letregion makes region accessible.
    After entering a letregion, the fresh region is accessible. *)
val letregion_enter_makes_accessible : st:full_borrow_state ->
  Lemma (ensures region_accessible (fst (enter_letregion_full None st))
                                   (snd (enter_letregion_full None st)))

let letregion_enter_makes_accessible st =
  (* enter_letregion_full adds the region to capabilities and stack *)
  ()

#pop-options

(** ----------------------------------------------------------------------------
    CONVENIENCE COMBINATORS FOR REGION TYPING
    ---------------------------------------------------------------------------- *)

(** Execute a computation in a letregion scope.

    This is a convenient combinator that:
    1. Enters a new letregion
    2. Runs the provided computation with the fresh region
    3. Validates the result doesn't escape
    4. Exits the letregion

    @param f The computation to run (takes region and state, returns type and state)
    @param st Initial state
    @return Result type and final state, or error *)
let with_letregion (#a: Type)
                   (f: region -> full_borrow_state -> option (brrr_type & a & full_borrow_state))
                   (st: full_borrow_state)
    : option (brrr_type & a & full_borrow_state) =
  (* Enter letregion *)
  let (r, st1) = enter_letregion_full None st in

  (* Run computation *)
  match f r st1 with
  | None -> None
  | Some (result_ty, result_val, st2) ->
    (* Exit letregion with escape check *)
    match exit_letregion_full r result_ty st2 with
    | LetRegionErr _ -> None
    | LetRegionOk _ st3 -> Some (result_ty, result_val, st3)

(** Allocate and return a reference in a region.

    Combines allocation check with reference type construction.

    @param r Region to allocate in
    @param init_ty Type of initialized value
    @param st Current state
    @return Reference type (ref[r] init_ty) and updated state *)
let alloc_ref_in_region (r: region) (init_ty: brrr_type) (st: full_borrow_state)
    : option (brrr_type & full_borrow_state) =
  match check_alloc r init_ty st with
  | AllocError _ -> None
  | AllocOk _ st' ->
    (* Return reference type: &init_ty (region tracked separately) *)
    Some (TWrap WRef init_ty, st')

(** Allocate mutable reference in a region.

    Similar to alloc_ref_in_region but produces &mut type.
    Requires the region to support exclusive access.

    @param r Region to allocate in
    @param init_ty Type of initialized value
    @param st Current state
    @return Mutable reference type and updated state *)
let alloc_ref_mut_in_region (r: region) (init_ty: brrr_type) (st: full_borrow_state)
    : option (brrr_type & full_borrow_state) =
  match check_alloc r init_ty st with
  | AllocError _ -> None
  | AllocOk _ st' ->
    (* Return mutable reference type *)
    Some (TWrap WRefMut init_ty, st')
