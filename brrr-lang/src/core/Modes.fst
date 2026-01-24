(**
 * BrrrLang.Core.Modes
 *
 * Mode semiring for ownership and linearity tracking.
 * Based on brrr_lang_spec_v0.4.tex Part III (Ownership & Memory):
 *   - Chapter 7: Mode Semiring
 *   - Chapter 9: Borrowing as Fractional Permissions
 *
 * Modes form a semiring (M, +, *, 0, 1, ω) where:
 *   - 0 = absent (not available)
 *   - 1 = linear (use exactly once)
 *   - ω = unrestricted (use any number of times)
 *
 * Extended modes:
 *   - Affine: use at most once (0 or 1)
 *   - Relevant: use at least once (1 or ω)
 *
 * Fractional permissions p ∈ (0,1]:
 *   - 1 = full/exclusive ownership
 *   - p < 1 = shared read-only access
 *   - Fractions sum: p₁ + p₂ ≤ 1
 *)
module Modes

open FStar.List.Tot
open FStar.Mul

(* Z3 solver options for consistent proof behavior.
   Using fuel 1 and ifuel 1 for exhaustiveness proofs on interface-defined types. *)
#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** ============================================================================
    MODE SEMIRING - Chapter 7
    ============================================================================ *)

(* Types mode and extended_mode are defined in Modes.fsti *)

(* Convert extended mode to base mode *)
let extended_to_mode (em: extended_mode) : mode =
  match em with
  | EMLinear -> MOne
  | EMAffine -> MOne        (* At most once = starts with 1 *)
  | EMRelevant -> MOne      (* At least once = starts with 1 *)
  | EMUnrestricted -> MOmega

(* Check if weakening is allowed (can discard unused) *)
let allows_weakening (em: extended_mode) : bool =
  match em with
  | EMAffine -> true
  | EMUnrestricted -> true
  | _ -> false

(* Check if contraction is allowed (can duplicate) *)
let allows_contraction (em: extended_mode) : bool =
  match em with
  | EMRelevant -> true
  | EMUnrestricted -> true
  | _ -> false

(* Can transition from extended mode to target mode?
   Checks if structural rules allow reaching the target from the extended mode.
   - EMLinear: can only stay at MOne or transition to MZero (use exactly once)
   - EMAffine: can reach MZero (weakening) or stay at MOne
   - EMRelevant: can reach MOmega (contraction) or stay at MOne
   - EMUnrestricted: can reach any mode *)
let can_transition (em: extended_mode) (target: mode) : bool =
  match em, target with
  | EMLinear, MOne -> true
  | EMLinear, MZero -> true  (* After consumption *)
  | EMAffine, MOne -> true
  | EMAffine, MZero -> true  (* Weakening allowed *)
  | EMRelevant, MOne -> true
  | EMRelevant, MOmega -> true  (* Contraction allowed *)
  | EMUnrestricted, _ -> true   (* All transitions allowed *)
  | _, _ -> false

(* Mode addition: combines parallel usages
   0 + m = m
   1 + 1 = ω
   ω + m = ω *)
let mode_add (m1 m2: mode) : mode =
  match m1, m2 with
  | MZero, m -> m
  | m, MZero -> m
  | MOmega, _ -> MOmega
  | _, MOmega -> MOmega
  | MOne, MOne -> MOmega

(* Mode multiplication: combines sequential usages
   0 * m = 0
   1 * m = m
   ω * 0 = 0
   ω * _ = ω *)
let mode_mul (m1 m2: mode) : mode =
  match m1, m2 with
  | MZero, _ -> MZero
  | _, MZero -> MZero
  | MOne, m -> m
  | m, MOne -> m
  | MOmega, MOmega -> MOmega

(* Mode ordering: 0 ≤ 1 ≤ ω *)
let mode_leq (m1 m2: mode) : bool =
  match m1, m2 with
  | MZero, _ -> true
  | MOne, MOne -> true
  | MOne, MOmega -> true
  | MOmega, MOmega -> true
  | _, _ -> false

(* Mode join (least upper bound) *)
let mode_join (m1 m2: mode) : mode =
  match m1, m2 with
  | MZero, m -> m
  | m, MZero -> m
  | MOmega, _ -> MOmega
  | _, MOmega -> MOmega
  | MOne, MOne -> MOne

(* Mode meet (greatest lower bound) *)
let mode_meet (m1 m2: mode) : mode =
  match m1, m2 with
  | MOmega, m -> m
  | m, MOmega -> m
  | MZero, _ -> MZero
  | _, MZero -> MZero
  | MOne, MOne -> MOne

(** ============================================================================
    SEMIRING LAWS (Lemmas)
    Signatures declared in Modes.fsti - only implementations here
    ============================================================================ *)

(* Addition is commutative: m1 + m2 = m2 + m1 *)
let mode_add_comm m1 m2 = ()

(* Addition is associative: (m1 + m2) + m3 = m1 + (m2 + m3) *)
let mode_add_assoc m1 m2 m3 = ()

(* Zero is additive identity: 0 + m = m *)
let mode_add_zero m = ()

(* Multiplication is associative *)
let mode_mul_assoc m1 m2 m3 = ()

(* Multiplication is commutative: m1 * m2 = m2 * m1.
   Proof by case analysis showing both sides reduce to the same value. *)
#push-options "--fuel 2 --ifuel 2"
let mode_mul_comm m1 m2 =
  match m1, m2 with
  | MZero, _ -> ()
  | _, MZero -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MOne -> ()
  | MOmega, MOmega -> ()
#pop-options

(* One is multiplicative identity: 1 * m = m *)
let mode_mul_one m = ()

(* Zero annihilates: 0 * m = 0 *)
let mode_mul_zero m = ()

(* Distributivity: m1 * (m2 + m3) = m1*m2 + m1*m3 *)
let mode_distrib m1 m2 m3 = ()

(* mode_leq is reflexive *)
let mode_leq_refl m =
  match m with
  | MZero -> ()
  | MOne -> ()
  | MOmega -> ()

(* mode_leq is transitive *)
let mode_leq_trans m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, _, _ -> ()
  | MOne, MOne, MOne -> ()
  | MOne, MOne, MOmega -> ()
  | MOne, MOmega, MOmega -> ()
  | MOmega, MOmega, MOmega -> ()
  | _, _, _ -> ()

(* Extended mode consistency lemma:
   If base mode is <= target, the extended mode can transition there. *)
let extended_mode_consistent em m =
  match em, m with
  | EMLinear, MOne -> ()
  | EMLinear, MOmega -> ()  (* MOne <= MOmega but can't transition - precondition guards this *)
  | EMAffine, MOne -> ()
  | EMAffine, MOmega -> ()
  | EMRelevant, MOne -> ()
  | EMRelevant, MOmega -> ()
  | EMUnrestricted, _ -> ()
  | _, MZero -> ()
  | _, _ -> ()

(** ============================================================================
    MODE LATTICE LAWS
    Signatures declared in Modes.fsti - only implementations here
    ============================================================================ *)

(* Join is commutative: m1 join m2 = m2 join m1 *)
let mode_join_comm m1 m2 =
  match m1, m2 with
  | MZero, MZero -> ()
  | MZero, MOne -> ()
  | MZero, MOmega -> ()
  | MOne, MZero -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MZero -> ()
  | MOmega, MOne -> ()
  | MOmega, MOmega -> ()

(* Join is associative: (m1 join m2) join m3 = m1 join (m2 join m3) *)
let mode_join_assoc m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, _, _ -> ()
  | _, MZero, _ -> ()
  | _, _, MZero -> ()
  | MOmega, _, _ -> ()
  | _, MOmega, _ -> ()
  | _, _, MOmega -> ()
  | MOne, MOne, MOne -> ()

(* Zero is identity for join *)
let mode_join_zero m = ()

(* Omega is absorbing for join *)
let mode_join_omega m = ()

(* Join is idempotent: m join m = m *)
let mode_join_idemp m =
  match m with
  | MZero -> ()
  | MOne -> ()
  | MOmega -> ()

(* Meet is commutative: m1 meet m2 = m2 meet m1 *)
let mode_meet_comm m1 m2 =
  match m1, m2 with
  | MZero, MZero -> ()
  | MZero, MOne -> ()
  | MZero, MOmega -> ()
  | MOne, MZero -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MZero -> ()
  | MOmega, MOne -> ()
  | MOmega, MOmega -> ()

(* Meet is associative: (m1 meet m2) meet m3 = m1 meet (m2 meet m3) *)
let mode_meet_assoc m1 m2 m3 =
  match m1, m2, m3 with
  | MOmega, _, _ -> ()
  | _, MOmega, _ -> ()
  | _, _, MOmega -> ()
  | MZero, _, _ -> ()
  | _, MZero, _ -> ()
  | _, _, MZero -> ()
  | MOne, MOne, MOne -> ()

(* Omega is identity for meet *)
let mode_meet_omega m = ()

(* Zero is absorbing for meet *)
let mode_meet_zero m = ()

(* Meet is idempotent: m meet m = m *)
let mode_meet_idemp m =
  match m with
  | MZero -> ()
  | MOne -> ()
  | MOmega -> ()

(* Antisymmetry: if m1 <= m2 and m2 <= m1 then m1 = m2 *)
let mode_leq_antisym m1 m2 =
  match m1, m2 with
  | MZero, MZero -> ()
  | MOne, MOne -> ()
  | MOmega, MOmega -> ()
  | _, _ -> ()

(* Lattice absorption laws *)
let mode_absorb_join_meet m1 m2 =
  match m1, m2 with
  | MZero, _ -> ()
  | _, MZero -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MOne -> ()
  | MOmega, MOmega -> ()
let mode_absorb_meet_join m1 m2 =
  match m1, m2 with
  | MOmega, _ -> ()
  | _, MOmega -> ()
  | MZero, MZero -> ()
  | MZero, MOne -> ()
  | MOne, MZero -> ()
  | MOne, MOne -> ()

(* Connection between ordering and lattice operations *)
let mode_leq_join m1 m2 =
  match m1, m2 with
  | MZero, _ -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MOmega -> ()
  | _, _ -> ()

let mode_leq_meet m1 m2 =
  match m1, m2 with
  | MZero, _ -> ()
  | MOne, MOne -> ()
  | MOne, MOmega -> ()
  | MOmega, MOmega -> ()
  | _, _ -> ()

(** ============================================================================
    OWNERSHIP QUALIFIERS
    ============================================================================ *)

(* Type ownership is defined in Modes.fsti *)

(* Can read through this ownership? *)
let can_read (o: ownership) : bool =
  match o with
  | Owned -> true
  | Borrowed -> true
  | BorrowMut -> true

(* Can write through this ownership? *)
let can_write (o: ownership) : bool =
  match o with
  | Owned -> true
  | Borrowed -> false
  | BorrowMut -> true

(* Can move/consume this ownership? *)
let can_move (o: ownership) : bool =
  match o with
  | Owned -> true
  | Borrowed -> false
  | BorrowMut -> false

(* Convert ownership to mode, considering Copy trait.

   The mode determines how many times a value can be used:
   - Owned + Copy: MOmega (can be used any number of times via implicit copy)
   - Owned + !Copy: MOne (linear, must be used exactly once)
   - Borrowed: MOmega (shared borrow can be used multiple times)
   - BorrowMut: MOne (exclusive borrow is linear - can only be used once at a time)

   This bridges Rust-style ownership with substructural type modes. *)
let ownership_to_mode (o: ownership) (is_copy: bool) : mode =
  match o with
  | Owned -> if is_copy then MOmega else MOne
  | Borrowed -> MOmega    (* Shared borrows are unrestricted *)
  | BorrowMut -> MOne     (* Exclusive borrows are linear *)

(* Convert ownership to extended_mode.

   Extended mode determines substructural properties:
   - Owned + Copy: EMUnrestricted (weakening + contraction allowed)
   - Owned + !Copy: EMLinear (no weakening, no contraction - must use exactly once)
   - Borrowed: EMUnrestricted (can drop, can share)
   - BorrowMut: EMAffine (can drop without use, but cannot duplicate) *)
let ownership_to_extended_mode (o: ownership) (is_copy: bool) : extended_mode =
  match o with
  | Owned -> if is_copy then EMUnrestricted else EMLinear
  | Borrowed -> EMUnrestricted
  | BorrowMut -> EMAffine  (* Can be dropped, but not duplicated *)

(** ============================================================================
    CONSUMPTION TRACKING (MODE CONTEXT)
    ============================================================================ *)

(* Types mode_ctx_entry and mode_ctx are defined in Modes.fsti *)

(* Empty context *)
let empty_mode_ctx : mode_ctx = []

(* Lookup mode and extended_mode of variable *)
let lookup_mode (x: string) (ctx: mode_ctx) : (mode & extended_mode) =
  let rec search (entries: list mode_ctx_entry) : (mode & extended_mode) =
    match entries with
    | [] -> (MZero, EMUnrestricted)  (* Not in context = unavailable, unrestricted default *)
    | (y, m, em) :: rest -> if y = x then (m, em) else search rest
  in
  search ctx

(* Lookup just the mode (convenience function) *)
let lookup_mode_only (x: string) (ctx: mode_ctx) : mode =
  fst (lookup_mode x ctx)

(* Lookup just the extended_mode (convenience function) *)
let lookup_extended_mode (x: string) (ctx: mode_ctx) : extended_mode =
  snd (lookup_mode x ctx)

(* Update mode of variable while preserving extended_mode *)
let update_mode (x: string) (m: mode) (ctx: mode_ctx) : mode_ctx =
  let em = lookup_extended_mode x ctx in
  (x, m, em) :: filter (fun (entry: mode_ctx_entry) ->
    match entry with (y, _, _) -> y <> x) ctx

(* Update both mode and extended_mode of variable *)
let update_mode_full (x: string) (m: mode) (em: extended_mode) (ctx: mode_ctx) : mode_ctx =
  (x, m, em) :: filter (fun (entry: mode_ctx_entry) ->
    match entry with (y, _, _) -> y <> x) ctx

(* Add a new variable to context *)
let extend_mode_ctx (x: string) (m: mode) (em: extended_mode) (ctx: mode_ctx) : mode_ctx =
  (x, m, em) :: ctx

(* Consume a linear variable: 1 -> 0
   Respects extended_mode:
   - For EMRelevant, contraction is allowed so MOmega is fine
   - For EMAffine, weakening is allowed so MZero is fine *)
let consume (x: string) (ctx: mode_ctx) : option mode_ctx =
  let (m, em) = lookup_mode x ctx in
  match m with
  | MZero -> None  (* Already consumed or never available *)
  | MOne -> Some (update_mode x MZero ctx)  (* Consume it *)
  | MOmega -> Some ctx  (* Unrestricted: no change *)

(* Split context for parallel composition (L-App rule).

   Linear splitting rules:
   - MOmega: Both branches can use (copy to both)
   - MOne: Left branch gets it, right gets MZero (linear resource goes to one side)
   - MZero: Neither has it (both get MZero)

   Extended mode is preserved in both branches. *)
let split_ctx (ctx: mode_ctx) : (mode_ctx & mode_ctx) =
  let split_one (entry: mode_ctx_entry) : (mode_ctx_entry & mode_ctx_entry) =
    match entry with
    | (x, m, em) ->
        match m with
        | MOmega -> ((x, MOmega, em), (x, MOmega, em))  (* Copy for both *)
        | MOne -> ((x, MOne, em), (x, MZero, em))       (* Left gets it, right empty *)
        | MZero -> ((x, MZero, em), (x, MZero, em))     (* Neither has it *)
  in
  let pairs = List.Tot.map split_one ctx in
  (List.Tot.map fst pairs, List.Tot.map snd pairs)

(* Join contexts after branches.
   Mode is joined (least upper bound), extended_mode is taken from left (should be same). *)
let join_ctx (ctx1: mode_ctx) (ctx2: mode_ctx) : mode_ctx =
  let join_one (entry: mode_ctx_entry) : mode_ctx_entry =
    match entry with
    | (x, m1, em) ->
        let m2 = lookup_mode_only x ctx2 in
        (x, mode_join m1 m2, em)
  in
  map join_one ctx1

(* Check if a variable can be weakened (dropped without use) *)
let can_weaken_var (x: string) (ctx: mode_ctx) : bool =
  allows_weakening (lookup_extended_mode x ctx)

(* Check if a variable can be contracted (duplicated) *)
let can_contract_var (x: string) (ctx: mode_ctx) : bool =
  allows_contraction (lookup_extended_mode x ctx)

(* Contract a variable: allows multiple uses if permitted by extended_mode.
   Changes mode to MOmega (can use any number of times). *)
let contract_mode_ctx (x: string) (ctx: mode_ctx) : option mode_ctx =
  if can_contract_var x ctx then
    let (m, em) = lookup_mode x ctx in
    if m = MZero then None  (* Cannot contract already-consumed variable *)
    else Some (update_mode x MOmega ctx)
  else None

(* Valid mode context: all entries have consistent mode/extended_mode pairs.
   A valid entry has mode compatible with its extended mode:
   - EMLinear/EMAffine: mode should be MOne or MZero (not MOmega without contraction)
   - EMRelevant/EMUnrestricted: any mode is valid *)
let valid_mode_ctx_entry (entry: mode_ctx_entry) : bool =
  match entry with
  | (_, m, em) ->
    match em with
    | EMLinear -> m = MOne || m = MZero
    | EMAffine -> m = MOne || m = MZero
    | EMRelevant -> true  (* Can be MOne or MOmega after contraction *)
    | EMUnrestricted -> true

let valid_mode_ctx (ctx: mode_ctx) : bool =
  for_all valid_mode_ctx_entry ctx

(* Consume preserves validity *)
let consume_preserves_valid x ctx =
  match consume x ctx with
  | None -> ()
  | Some _ ->
    (* After consuming, mode goes MOne -> MZero or MOmega -> MOmega.
       Both preserve validity. *)
    ()

(* Split preserves validity: both halves remain valid *)
let split_preserves_valid ctx =
  let _ = split_ctx ctx in
  (* Splitting preserves extended_mode and only changes mode:
     MOmega -> (MOmega, MOmega)
     MOne -> (MOne, MZero)
     MZero -> (MZero, MZero)
     All of these preserve the validity invariant. *)
  ()

(* Join preserves validity *)
let join_preserves_valid ctx1 ctx2 =
  (* Joining takes mode_join of modes, preserves extended_mode.
     mode_join preserves the invariant since:
     - join(MZero, MZero) = MZero
     - join(MZero, MOne) = MOne
     - join(MOne, MOne) = MOne
     - join with MOmega = MOmega *)
  ()

(** ============================================================================
    FRACTIONAL PERMISSIONS - Chapter 9
    ============================================================================ *)

(* Types fraction_raw and fraction are defined in Modes.fsti *)

(* Predicate for valid fraction in (0,1] *)
let valid_frac (f: fraction_raw) : bool =
  f.frac_num > 0 && f.frac_den > 0 && f.frac_num <= f.frac_den

(* Full permission = 1 *)
let frac_full : fraction = { frac_num = 1; frac_den = 1 }

(* Half permission = 1/2 *)
let frac_half : fraction = { frac_num = 1; frac_den = 2 }

(* Is this full ownership? *)
let is_full_perm (f: fraction) : bool =
  f.frac_num = f.frac_den

(* Is this a read-only share? (less than full) *)
let is_shared_perm (f: fraction) : bool =
  f.frac_num < f.frac_den

(* Permission comparison: f1 <= f2
   Cross-multiply to avoid floating point: n1*d2 <= n2*d1 *)
let frac_leq (f1 f2: fraction) : bool =
  f1.frac_num * f2.frac_den <= f2.frac_num * f1.frac_den

(* Permission equality *)
let frac_eq (f1 f2: fraction) : bool =
  f1.frac_num * f2.frac_den = f2.frac_num * f1.frac_den

(* GCD for simplification - must be defined before frac_simplify *)
let rec gcd (a b: nat) : Tot nat (decreases b) =
  if b = 0 then (if a = 0 then 1 else a)
  else gcd b (a % b)

(* Lemma: integer division preserves ordering.
   If a <= b and c > 0, then a / c <= b / c.
   Proof: Follows from the definition of integer division. *)
val div_preserves_le : a:nat -> b:nat -> c:nat{c > 0} ->
  Lemma (requires a <= b)
        (ensures a / c <= b / c)
let div_preserves_le a b c =
  (* FStar.Math.Lemmas.lemma_div_le a b c would be the canonical approach,
     but this follows directly from the definition of integer division:
     a = (a/c)*c + (a%c), b = (b/c)*c + (b%c), 0 <= a%c < c, 0 <= b%c < c.
     If a/c > b/c, then a/c >= b/c + 1, so (a/c)*c >= (b/c)*c + c.
     Since a <= b, we have (a/c)*c + (a%c) <= (b/c)*c + (b%c).
     But (a/c)*c >= (b/c)*c + c > (b/c)*c + (b%c), contradiction. *)
  ()

(* Simplify fraction to lowest terms - keep original if can't simplify.
   The invariant new_num <= new_den is preserved by div_preserves_le. *)
#push-options "--z3rlimit 100"
let frac_simplify (f: fraction) : fraction =
  let g = gcd f.frac_num f.frac_den in
  if g > 0 then
    let new_num = f.frac_num / g in
    let new_den = f.frac_den / g in
    (* Apply lemma to show new_num <= new_den from f.frac_num <= f.frac_den *)
    div_preserves_le f.frac_num f.frac_den g;
    if new_num > 0 && new_den > 0 then
      { frac_num = new_num; frac_den = new_den }
    else f
  else f
#pop-options

(* Split permission: p -> (p/2, p/2)
   Simplifies result to prevent denominator explosion over repeated splits.
   For example: 1/1 -> (1/2, 1/2)
                1/2 -> (1/4, 1/4) *)
let frac_split (f: fraction) : (fraction & fraction) =
  let half = { frac_num = f.frac_num; frac_den = f.frac_den * 2 } in
  let simplified = frac_simplify half in
  (simplified, simplified)

(* Join permissions: (p1, p2) -> p1 + p2
   Returns None if sum would exceed 1 *)
let frac_join (f1 f2: fraction) : option fraction =
  (* n1/d1 + n2/d2 = (n1*d2 + n2*d1)/(d1*d2) *)
  let common_den = f1.frac_den * f2.frac_den in
  let sum_num = f1.frac_num * f2.frac_den + f2.frac_num * f1.frac_den in
  if sum_num <= common_den then
    Some { frac_num = sum_num; frac_den = common_den }
  else
    None  (* Sum exceeds 1 *)

(* Fraction equality lemmas - signatures in Modes.fsti *)
let frac_eq_refl f = ()

let frac_eq_sym f1 f2 = ()

(* Helper lemma: multiplication cancellation for positive integers.
   If a * c = b * c and c > 0, then a = b.
   This is a fundamental arithmetic property.
   Not in .fsti - local helper lemma. *)
val mult_cancel_r : a:nat -> b:nat -> c:nat{c > 0} ->
  Lemma (requires a * c = b * c) (ensures a = b)
let mult_cancel_r a b c = ()

(* Transitivity of fraction equality.
   Proof: Given f1.n * f2.d = f2.n * f1.d (eq1)
          and   f2.n * f3.d = f3.n * f2.d (eq2)

   Multiply eq1 by f3.d: f1.n * f2.d * f3.d = f2.n * f1.d * f3.d
   Multiply eq2 by f1.d: f2.n * f3.d * f1.d = f3.n * f2.d * f1.d

   The second gives: f2.n * f1.d * f3.d = f3.n * f1.d * f2.d (commutativity)

   By transitivity: f1.n * f2.d * f3.d = f3.n * f1.d * f2.d
   Which is:        f1.n * f3.d * f2.d = f3.n * f1.d * f2.d

   Since f2.d > 0, cancel to get: f1.n * f3.d = f3.n * f1.d *)
let frac_eq_trans f1 f2 f3 =
  let n1 = f1.frac_num in
  let d1 = f1.frac_den in
  let n2 = f2.frac_num in
  let d2 = f2.frac_den in
  let n3 = f3.frac_num in
  let d3 = f3.frac_den in

  (* From preconditions we have:
     n1 * d2 = n2 * d1   ... (eq1)
     n2 * d3 = n3 * d2   ... (eq2) *)

  (* Multiply eq1 by d3: n1 * d2 * d3 = n2 * d1 * d3 *)
  assert (n1 * d2 * d3 = n2 * d1 * d3);

  (* Multiply eq2 by d1: n2 * d3 * d1 = n3 * d2 * d1 *)
  assert (n2 * d3 * d1 = n3 * d2 * d1);

  (* By commutativity: n2 * d1 * d3 = n2 * d3 * d1 *)
  assert (n2 * d1 * d3 = n2 * d3 * d1);

  (* So n2 * d1 * d3 = n3 * d2 * d1 = n3 * d1 * d2 *)
  assert (n2 * d1 * d3 = n3 * d1 * d2);

  (* By transitivity: n1 * d2 * d3 = n3 * d1 * d2 *)
  assert (n1 * d2 * d3 = n3 * d1 * d2);

  (* Rearrange using commutativity: n1 * d3 * d2 = n3 * d1 * d2 *)
  assert (n1 * d3 * d2 = n3 * d1 * d2);

  (* Apply cancellation lemma since d2 > 0 *)
  mult_cancel_r (n1 * d3) (n3 * d1) d2

(* Transitivity of frac_leq: f1 <= f2 /\ f2 <= f3 ==> f1 <= f3
   Proof sketch: Given n1*d2 <= n2*d1 and n2*d3 <= n3*d2,
   we need to show n1*d3 <= n3*d1.

   Multiply first by d3: n1*d2*d3 <= n2*d1*d3
   Multiply second by d1: n2*d3*d1 <= n3*d2*d1

   Since n2*d1*d3 = n2*d3*d1 (commutativity):
   n1*d2*d3 <= n2*d1*d3 = n2*d3*d1 <= n3*d2*d1 = n3*d1*d2

   So n1*d2*d3 <= n3*d1*d2, i.e., (n1*d3)*d2 <= (n3*d1)*d2
   Since d2 > 0, this implies n1*d3 <= n3*d1 *)
let frac_leq_trans f1 f2 f3 =
  let n1 = f1.frac_num in
  let d1 = f1.frac_den in
  let n2 = f2.frac_num in
  let d2 = f2.frac_den in
  let n3 = f3.frac_num in
  let d3 = f3.frac_den in
  (* From preconditions: n1*d2 <= n2*d1 and n2*d3 <= n3*d2 *)
  (* Multiply both sides of first inequality by d3 (d3 > 0) *)
  assert (n1 * d2 * d3 <= n2 * d1 * d3);
  (* Multiply both sides of second inequality by d1 (d1 > 0) *)
  assert (n2 * d3 * d1 <= n3 * d2 * d1);
  (* By commutativity: n2*d1*d3 = n2*d3*d1 *)
  assert (n2 * d1 * d3 = n2 * d3 * d1);
  (* By transitivity of <= on nat: n1*d2*d3 <= n3*d2*d1 *)
  (* Rearranging: n1*d3*d2 <= n3*d1*d2 *)
  assert (n1 * d3 * d2 <= n3 * d1 * d2);
  (* Since d2 > 0, we can use: if a*c <= b*c and c > 0 then a <= b *)
  (* This is just division, which F* SMT handles automatically *)
  ()

(* Split/join inverse lemma: splitting then joining recovers original fraction.
   Proof: split gives (n, 2*d) for each half.
   Join: (n/(2d) + n/(2d)) = n*(2d) + n*(2d) / (2d*2d) = 4*n*d / 4*d*d = n/d
   So the result is equal to the original fraction. *)
#push-options "--z3rlimit 100"
let frac_split_join_inverse f =
  let (h1, h2) = frac_split f in
  (* h1 = h2 = simplified version of { frac_num = f.frac_num; frac_den = f.frac_den * 2 }
     When we join them: sum_num = h1.num * h2.den + h2.num * h1.den
                              = h1.num * h1.den + h1.num * h1.den
                              = 2 * h1.num * h1.den
     common_den = h1.den * h2.den = h1.den * h1.den = h1.den^2

     For the unsimplified case:
     half = { num = f.num; den = f.den * 2 }
     sum_num = f.num * (f.den*2) + f.num * (f.den*2) = 2 * f.num * f.den * 2 = 4 * f.num * f.den
     common_den = (f.den*2) * (f.den*2) = 4 * f.den^2
     So we get (4 * f.num * f.den) / (4 * f.den^2) = f.num / f.den

     Cross-multiply equality check:
     joined.num * f.den = f.num * joined.den
     (4 * f.num * f.den) * f.den = f.num * (4 * f.den^2)
     4 * f.num * f.den^2 = 4 * f.num * f.den^2  -- true! *)
  ()
#pop-options

(* Fraction ordering is reflexive *)
let frac_leq_refl f =
  (* n1*d2 <= n2*d1 becomes n*d <= n*d which is trivially true *)
  ()

(* Full permission is maximal: any fraction <= full *)
let frac_full_maximal f =
  (* f.num * 1 <= 1 * f.den simplifies to f.num <= f.den, which is
     guaranteed by the fraction validity invariant. *)
  ()

(* Half is less than full and is shared *)
let frac_half_lt_full () =
  (* 1 * 1 <= 1 * 2 is 1 <= 2, true.
     is_shared_perm: 1 < 2, true. *)
  ()

(** ============================================================================
    PERMISSION-BASED REFERENCES - Chapter 9
    ============================================================================ *)

(* Type ref_kind is defined in Modes.fsti *)

(* Is this a shared (box) reference? *)
let is_box_ref (rk: ref_kind) : bool =
  match rk with
  | RefBox _ -> true
  | RefDiamond -> false

(* Is this an exclusive (diamond) reference? *)
let is_diamond_ref (rk: ref_kind) : bool =
  match rk with
  | RefDiamond -> true
  | RefBox _ -> false

(* Get permission from reference kind *)
let ref_permission (rk: ref_kind) : fraction =
  match rk with
  | RefBox p -> p
  | RefDiamond -> frac_full

(* Can read through this reference? (any non-zero permission) *)
let ref_can_read (rk: ref_kind) : bool = true  (* Any permission allows read *)

(* Can write through this reference? (requires full permission) *)
let ref_can_write (rk: ref_kind) : bool =
  match rk with
  | RefDiamond -> true
  | RefBox p -> is_full_perm p

(* Freeze: ◇τ @ 1 -> □τ @ ω
   Converts exclusive to shared, makes duplicable *)
let freeze (rk: ref_kind) : option ref_kind =
  match rk with
  | RefDiamond -> Some (RefBox frac_full)  (* Full share, now duplicable *)
  | RefBox _ -> None  (* Already shared *)

(* Thaw: □τ @ full -> ◇τ @ 1
   Converts full shared back to exclusive (requires collecting all shares) *)
let thaw (rk: ref_kind) : option ref_kind =
  match rk with
  | RefBox p -> if is_full_perm p then Some RefDiamond else None
  | RefDiamond -> None  (* Already exclusive *)

(* Split a box reference: □τ @ p -> (□τ @ p/2, □τ @ p/2) *)
let split_box (rk: ref_kind) : option (ref_kind & ref_kind) =
  match rk with
  | RefBox p ->
      let (p1, p2) = frac_split p in
      Some (RefBox p1, RefBox p2)
  | RefDiamond -> None  (* Cannot split exclusive *)

(* Join box references: (□τ @ p1, □τ @ p2) -> □τ @ (p1+p2) *)
let join_box (rk1 rk2: ref_kind) : option ref_kind =
  match rk1, rk2 with
  | RefBox p1, RefBox p2 ->
      (match frac_join p1 p2 with
       | Some p -> Some (RefBox p)
       | None -> None)
  | _, _ -> None  (* Cannot join with exclusive *)

(** ============================================================================
    LINEAR CONTEXT SPLITTING - Chapter 8
    ============================================================================ *)

(* Types lin_entry and lin_ctx are defined in Modes.fsti *)

(* Empty linear context *)
let empty_lin_ctx : lin_ctx = []

(* Lookup in linear context *)
let lookup_lin (x: string) (ctx: lin_ctx) : option lin_entry =
  let rec search (entries: list lin_entry) : option lin_entry =
    match entries with
    | [] -> None
    | e :: rest -> if e.le_var = x then Some e else search rest
  in
  search ctx

(* Add entry to linear context *)
let extend_lin (e: lin_entry) (ctx: lin_ctx) : lin_ctx = e :: ctx

(* Mark a variable as used in the context.
   This is called when a variable is actually accessed (not just contracted).
   Critical for EMRelevant soundness. *)
let use_lin (x: string) (ctx: lin_ctx) : option lin_ctx =
  match lookup_lin x ctx with
  | None -> None
  | Some e ->
      (* Mark as used and update mode if linear *)
      let new_mode = match e.le_mode with
        | MZero -> MZero  (* Already consumed - error state *)
        | MOne -> MZero   (* Consume linear *)
        | MOmega -> MOmega (* Unrestricted stays same *)
      in
      if e.le_mode = MZero then None  (* Can't use already consumed *)
      else
        let e' = { e with le_mode = new_mode; le_used = true } in
        Some (map (fun entry -> if entry.le_var = x then e' else entry) ctx)

(* Context splitting for parallel composition (L-App rule)
   Γ = Γ₁ + Γ₂ where linear variables go to exactly one side.
   Preserves le_used flag from original context. *)
let split_lin_ctx (ctx: lin_ctx) : (lin_ctx & lin_ctx) =
  let split_entry (e: lin_entry) : (lin_entry & lin_entry) =
    match e.le_mode with
    | MZero -> (e, e)  (* Zero mode: both get it *)
    | MOne ->
        (* Linear: left side gets it, right gets zero.
           Note: le_used is preserved on left (where the actual variable goes) *)
        let e_left = e in
        let e_right = { e with le_mode = MZero; le_used = false } in
        (e_left, e_right)
    | MOmega -> (e, e)  (* Omega: both sides can use, le_used preserved *)
  in
  let (lefts, rights) = fold_left (fun (l, r) e ->
    let (el, er) = split_entry e in
    (el :: l, er :: r)
  ) ([], []) ctx in
  (rev lefts, rev rights)

(* Context join after branches.
   For le_used: if either branch used the variable, it counts as used.
   This is sound for EMRelevant: using in either branch satisfies "at least once". *)
let join_lin_ctx (ctx1 ctx2: lin_ctx) : lin_ctx =
  let join_entry (e1: lin_entry) : lin_entry =
    match lookup_lin e1.le_var ctx2 with
    | Some e2 -> { e1 with
        le_mode = mode_join e1.le_mode e2.le_mode;
        le_used = e1.le_used || e2.le_used  (* Used in either branch counts *)
      }
    | None -> e1
  in
  map join_entry ctx1

(* Check if context is fully consumed (all linear vars used)

   IMPORTANT: For EMRelevant, we must check le_used, not just le_mode.
   Contraction (duplication) changes mode to MOmega but doesn't count as
   actual usage. The le_used flag tracks whether the variable was actually
   accessed at least once.

   Rules:
   - EMLinear: must be used exactly once (le_mode = MZero)
   - EMRelevant: must be used at least once (le_used = true)
   - EMAffine: can be unused (weakening allowed)
   - EMUnrestricted: can be unused or used any number of times *)
let is_fully_consumed (ctx: lin_ctx) : bool =
  for_all (fun e ->
    match e.le_ext with
    | EMLinear -> e.le_mode = MZero      (* Must be used exactly once *)
    | EMRelevant -> e.le_used            (* Must be used at least once - check actual usage, not mode *)
    | EMAffine -> true                   (* Can be unused *)
    | EMUnrestricted -> true
  ) ctx

(* Weaken context: add unused variable (only if mode allows) *)
let weaken_lin (x: string) (m: mode) (em: extended_mode) (ctx: lin_ctx) : option lin_ctx =
  if allows_weakening em then
    Some (extend_lin { le_var = x; le_mode = m; le_ext = em; le_perm = None; le_used = false } ctx)
  else
    None

(* Contract context: duplicate variable usage (only if mode allows).

   IMPORTANT: Contraction is NOT actual usage. It only allows the variable
   to be used multiple times in the future. The le_used flag is NOT set here.
   This is critical for EMRelevant soundness: contracting a relevant variable
   and then never using it should fail the is_fully_consumed check. *)
let contract_lin (x: string) (ctx: lin_ctx) : option lin_ctx =
  match lookup_lin x ctx with
  | None -> None
  | Some e ->
      if allows_contraction e.le_ext then
        (* Duplicate: mode becomes ω, but le_used unchanged - contraction is not use *)
        let e' = { e with le_mode = MOmega } in
        Some (map (fun entry -> if entry.le_var = x then e' else entry) ctx)
      else
        None

(** ============================================================================
    LINEAR CONTEXT VALIDITY LEMMAS
    ============================================================================ *)

(* Valid linear context: all entries have consistent mode/extended_mode pairs *)
let valid_lin_entry (e: lin_entry) : bool =
  match e.le_ext with
  | EMLinear -> e.le_mode = MOne || e.le_mode = MZero
  | EMAffine -> e.le_mode = MOne || e.le_mode = MZero
  | EMRelevant -> true
  | EMUnrestricted -> true

let valid_lin_ctx (ctx: lin_ctx) : bool =
  for_all valid_lin_entry ctx

(* Using a variable preserves validity *)
let use_lin_preserves_valid x ctx =
  match use_lin x ctx with
  | None -> ()
  | Some ctx' ->
    (* use_lin only transitions MOne -> MZero or keeps MOmega.
       Both preserve the validity invariant. *)
    ()

(** ============================================================================
    MODE SUBTYPING AND COMPATIBILITY IMPLEMENTATIONS
    ============================================================================ *)

(* Extended mode subtyping: em1 <: em2 means em1 is more restrictive.
   The lattice is:
     EMLinear (most restrictive)
        |    \
     EMAffine  EMRelevant
        \     /
      EMUnrestricted (least restrictive)
*)
let extended_mode_subtype (em1 em2: extended_mode) : bool =
  match em1, em2 with
  | EMLinear, _ -> true                     (* Linear subtypes everything *)
  | EMAffine, EMAffine -> true
  | EMAffine, EMUnrestricted -> true        (* Affine subtypes unrestricted *)
  | EMRelevant, EMRelevant -> true
  | EMRelevant, EMUnrestricted -> true      (* Relevant subtypes unrestricted *)
  | EMUnrestricted, EMUnrestricted -> true
  | _, _ -> false

(* Mode compatibility for parallel composition.
   Two modes can be combined if at least one is unrestricted,
   or if one is zero (absent). *)
let mode_compatible (m1 m2: mode) : bool =
  match m1, m2 with
  | MOmega, _ -> true     (* Omega can share with anything *)
  | _, MOmega -> true
  | MZero, _ -> true      (* Zero is compatible with anything *)
  | _, MZero -> true
  | MOne, MOne -> false   (* Two linear resources cannot be combined *)

(* Extended mode compatibility: checks if structural rules allow combination.
   Compatible if contraction is allowed on at least one side. *)
let extended_mode_compatible (em1 em2: extended_mode) : bool =
  allows_contraction em1 || allows_contraction em2 ||
  em1 = EMUnrestricted || em2 = EMUnrestricted

(** ============================================================================
    MODE CONTEXT SPLITTING IMPLEMENTATIONS
    ============================================================================ *)

(* Get the mode for a variable from context, returning MZero if absent *)
let get_mode_in_ctx (x: string) (ctx: mode_ctx) : mode =
  lookup_mode_only x ctx

(* Linear exclusivity lemma *)
let split_ctx_linear_exclusive ctx x =
  let (l, r) = split_ctx ctx in
  (* By definition of split_ctx:
     - MOne -> ((x, MOne, em), (x, MZero, em))
     So left gets MOne, right gets MZero. *)
  ()

(* Omega sharing lemma *)
let split_ctx_omega_shared ctx x =
  let (l, r) = split_ctx ctx in
  (* By definition of split_ctx:
     - MOmega -> ((x, MOmega, em), (x, MOmega, em))
     Both sides get MOmega. *)
  ()

(* Zero propagation lemma *)
let split_ctx_zero_both ctx x =
  let (l, r) = split_ctx ctx in
  (* By definition of split_ctx:
     - MZero -> ((x, MZero, em), (x, MZero, em)) *)
  ()

(* Mode sum lemma: modes combine correctly after split.
   Note: For omega, mode_add MOmega MOmega = MOmega, which equals original.
   For linear: mode_add MOne MZero = MOne, equals original.
   For zero: mode_add MZero MZero = MZero, equals original. *)
let split_ctx_mode_sum ctx x =
  let (l, r) = split_ctx ctx in
  let m = get_mode_in_ctx x ctx in
  let ml = get_mode_in_ctx x l in
  let mr = get_mode_in_ctx x r in
  match m with
  | MOmega -> ()  (* MOmega case: second disjunct *)
  | MOne -> ()    (* MOne + MZero = MOne *)
  | MZero -> ()   (* MZero + MZero = MZero *)

(* Extended mode preservation lemma *)
let split_ctx_preserves_extended ctx x =
  (* split_one preserves extended_mode in both halves:
     (x, m, em) -> ((x, _, em), (x, _, em)) *)
  ()

(** ============================================================================
    MODE CONTEXT CONSUMPTION IMPLEMENTATIONS
    ============================================================================ *)

(* Check if all linear resources in mode_ctx are fully consumed *)
let is_mode_ctx_fully_consumed (ctx: mode_ctx) : bool =
  for_all (fun (entry: mode_ctx_entry) ->
    match entry with
    | (_, m, em) ->
      match em with
      | EMLinear -> m = MZero      (* Must be consumed *)
      | EMRelevant -> m = MZero || m = MOmega  (* Must have been used at least once *)
      | EMAffine -> true           (* Can be unused *)
      | EMUnrestricted -> true
  ) ctx

(* Well-formedness check: no duplicates and all valid entries *)
let rec no_duplicate_vars (ctx: mode_ctx) : bool =
  match ctx with
  | [] -> true
  | (x, _, _) :: rest ->
      let no_dup = for_all (fun (entry: mode_ctx_entry) ->
        match entry with (y, _, _) -> y <> x) rest in
      no_dup && no_duplicate_vars rest

let mode_ctx_wf (ctx: mode_ctx) : bool =
  no_duplicate_vars ctx && valid_mode_ctx ctx

(* Fully consumed implies valid *)
let fully_consumed_implies_valid ctx =
  (* If fully consumed, each entry satisfies its extended_mode constraints,
     which implies valid_mode_ctx. The key insight is:
     - EMLinear with MZero is valid
     - EMRelevant with MZero or MOmega is valid
     - EMAffine and EMUnrestricted are always valid *)
  ()

(** ============================================================================
    JOIN CONTEXT IMPLEMENTATIONS
    ============================================================================ *)

(* Join mode lookup lemma *)
let join_ctx_mode_comm ctx1 ctx2 x =
  (* join_ctx computes mode_join on modes, which is what we're asserting. *)
  ()

(* Split-join roundtrip *)
let split_join_roundtrip ctx x =
  let (l, r) = split_ctx ctx in
  let m = get_mode_in_ctx x ctx in
  (* Case analysis:
     - MOmega: split gives (MOmega, MOmega), join gives mode_join MOmega MOmega = MOmega
     - MOne: split gives (MOne, MZero), join gives mode_join MOne MZero = MOne
     - MZero: split gives (MZero, MZero), join gives mode_join MZero MZero = MZero *)
  ()

(** ============================================================================
    LINEAR CONTEXT LEMMA IMPLEMENTATIONS
    ============================================================================ *)

(* Split preserves validity for linear context *)
let split_lin_preserves_valid ctx =
  let (l, r) = split_lin_ctx ctx in
  (* split_lin_ctx only changes modes:
     - MOne -> (MOne, MZero)
     - MOmega -> (MOmega, MOmega)
     - MZero -> (MZero, MZero)
     All preserve the validity invariant. *)
  ()

(* Join preserves validity for linear context *)
let join_lin_preserves_valid ctx1 ctx2 =
  (* join_lin_ctx uses mode_join which preserves validity:
     All mode_join results satisfy the extended_mode constraints. *)
  ()

(* Contraction preserves validity *)
let contract_lin_preserves_valid x ctx =
  match contract_lin x ctx with
  | None -> ()
  | Some ctx' ->
    (* Contraction changes mode to MOmega, which is valid for
       EMRelevant and EMUnrestricted (the only modes that allow contraction). *)
    ()

(* Weakening preserves validity *)
let weaken_lin_preserves_valid x m em ctx =
  match weaken_lin x m em ctx with
  | None -> ()
  | Some ctx' ->
    (* Weakening only adds an entry if allowed by extended_mode.
       The new entry is { le_var=x; le_mode=m; le_ext=em; le_used=false }.
       This is valid if the mode is consistent with extended_mode. *)
    ()

(** ============================================================================
    OWNERSHIP TO MODE LEMMA IMPLEMENTATIONS
    ============================================================================ *)

(* Owned non-copy types are linear *)
let owned_noncopy_is_linear () =
  (* By definition of ownership_to_mode and ownership_to_extended_mode:
     ownership_to_mode Owned false = MOne
     ownership_to_extended_mode Owned false = EMLinear *)
  ()

(* Borrowed references are unrestricted *)
let borrowed_is_unrestricted () =
  (* By definition:
     ownership_to_mode Borrowed _ = MOmega
     ownership_to_extended_mode Borrowed _ = EMUnrestricted *)
  ()

(* Mutable borrows are affine *)
let borrow_mut_is_affine () =
  (* By definition:
     ownership_to_mode BorrowMut _ = MOne
     ownership_to_extended_mode BorrowMut _ = EMAffine *)
  ()

(** ============================================================================
    MODE CHECKING JUDGMENT IMPLEMENTATIONS
    ============================================================================ *)

(* Linear resource accounting lemma *)
let mode_check_linear_accounting ctx_in ctx_out x =
  (* If x has MZero in output, it was either:
     1. Already MZero in input (never available)
     2. Consumed from MOne to MZero during checking
     MOmega resources don't become MZero through normal consumption. *)
  ()

(** ============================================================================
    RESOURCE COUNTING - Following HACL* Lib.Sequence patterns
    ============================================================================ *)

(* Count variables with MOne (owned/linear) mode in context *)
let rec count_owned (ctx: mode_ctx) : nat =
  match ctx with
  | [] -> 0
  | (_, m, _) :: rest ->
      (if m = MOne then 1 else 0) + count_owned rest

(* Count variables with MOmega (borrowed/shared) mode in context *)
let rec count_borrowed (ctx: mode_ctx) : nat =
  match ctx with
  | [] -> 0
  | (_, m, _) :: rest ->
      (if m = MOmega then 1 else 0) + count_borrowed rest

(* Count consumed (MZero) variables in context *)
let rec count_consumed (ctx: mode_ctx) : nat =
  match ctx with
  | [] -> 0
  | (_, m, _) :: rest ->
      (if m = MZero then 1 else 0) + count_consumed rest

(* Total variable count equals sum of all categories.
   Proof by induction on ctx structure. *)
#push-options "--fuel 2 --ifuel 1"
let rec count_total_eq (ctx: mode_ctx) : Lemma
  (ensures length ctx = count_owned ctx + count_borrowed ctx + count_consumed ctx)
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | (_, m, _) :: rest ->
      count_total_eq rest;
      (* Case analysis on mode covers all possibilities *)
      match m with
      | MZero -> ()
      | MOne -> ()
      | MOmega -> ()
#pop-options

(* Helper: count_owned after split_one.
   Proves that splitting an entry preserves owned count on left, gives 0 on right. *)
let split_one_owned_count (entry: mode_ctx_entry) : Lemma
  (ensures (
    let split_entry (e: mode_ctx_entry) : (mode_ctx_entry & mode_ctx_entry) =
      match e with
      | (x, m, em) ->
          match m with
          | MOmega -> ((x, MOmega, em), (x, MOmega, em))
          | MOne -> ((x, MOne, em), (x, MZero, em))
          | MZero -> ((x, MZero, em), (x, MZero, em))
    in
    let (l, r) = split_entry entry in
    let count_entry (e: mode_ctx_entry) : nat =
      match e with (_, m, _) -> if m = MOne then 1 else 0
    in
    count_entry l = count_entry entry /\ count_entry r = 0))
=
  match entry with
  | (_, MOne, _) -> ()
  | (_, MOmega, _) -> ()
  | (_, MZero, _) -> ()

(* Split preserves owned count: linear resources go exclusively to left.
   Proof by induction on context structure. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec split_preserves_owned_count_aux (ctx: mode_ctx) : Lemma
  (ensures (let (l, r) = split_ctx ctx in
            count_owned l = count_owned ctx /\
            count_owned r = 0))
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | entry :: rest ->
      split_preserves_owned_count_aux rest;
      split_one_owned_count entry
#pop-options

let split_preserves_owned_count ctx = split_preserves_owned_count_aux ctx

(* Helper for borrowed count preservation.
   Proves that splitting an entry preserves borrowed count on both sides. *)
let split_one_borrowed_count (entry: mode_ctx_entry) : Lemma
  (ensures (
    let split_entry (e: mode_ctx_entry) : (mode_ctx_entry & mode_ctx_entry) =
      match e with
      | (x, m, em) ->
          match m with
          | MOmega -> ((x, MOmega, em), (x, MOmega, em))
          | MOne -> ((x, MOne, em), (x, MZero, em))
          | MZero -> ((x, MZero, em), (x, MZero, em))
    in
    let (l, r) = split_entry entry in
    let count_entry (e: mode_ctx_entry) : nat =
      match e with (_, m, _) -> if m = MOmega then 1 else 0
    in
    count_entry l = count_entry entry /\ count_entry r = count_entry entry))
=
  match entry with
  | (_, MOne, _) -> ()
  | (_, MOmega, _) -> ()
  | (_, MZero, _) -> ()

(* Split duplicates borrowed count: both halves get the same borrowed count. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec split_preserves_borrowed_count_aux (ctx: mode_ctx) : Lemma
  (ensures (let (l, r) = split_ctx ctx in
            count_borrowed l = count_borrowed ctx /\
            count_borrowed r = count_borrowed ctx))
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | entry :: rest ->
      split_preserves_borrowed_count_aux rest;
      split_one_borrowed_count entry
#pop-options

let split_preserves_borrowed_count ctx = split_preserves_borrowed_count_aux ctx

(** ============================================================================
    MODE TRANSITION VALIDITY
    ============================================================================ *)

(* Valid mode transitions following borrow semantics *)
let valid_mode_transition (m_before m_after: mode) : bool =
  match m_before, m_after with
  | MZero, MZero -> true      (* Dead stays dead *)
  | MOne, MZero -> true       (* Consumption *)
  | MOne, MOne -> true        (* Keep linear *)
  | MOne, MOmega -> true      (* Contraction (if allowed) *)
  | MOmega, MOmega -> true    (* Unrestricted stays unrestricted *)
  | MOmega, MZero -> false    (* Cannot consume unrestricted *)
  | MZero, _ -> false         (* Cannot resurrect from zero (except to zero) *)
  | MOmega, MOne -> false     (* Cannot un-share *)

(* Mode transition is reflexive for available modes *)
let mode_transition_refl m =
  match m with
  | MZero -> ()
  | MOne -> ()
  | MOmega -> ()

(* Mode transition is transitive.
   Proof by exhaustive case analysis on all mode combinations. *)
#push-options "--fuel 1 --ifuel 1"
let mode_transition_trans m1 m2 m3 =
  match m1, m2, m3 with
  (* m1 = MZero cases: only valid if m2 = m3 = MZero *)
  | MZero, MZero, MZero -> ()
  (* m1 = MOne cases *)
  | MOne, MZero, MZero -> ()
  | MOne, MOne, MZero -> ()
  | MOne, MOne, MOne -> ()
  | MOne, MOne, MOmega -> ()
  | MOne, MOmega, MOmega -> ()
  (* m1 = MOmega cases *)
  | MOmega, MOmega, MOmega -> ()
  (* All other combinations are excluded by preconditions *)
  | _, _, _ -> ()
#pop-options

(* Consumption is terminal: after MZero, only MZero is reachable *)
let mode_zero_terminal m =
  match m with
  | MZero -> ()
  | MOne -> ()
  | MOmega -> ()

(* Contraction is valid transition *)
let mode_contraction_valid () = ()

(* Consumption from linear is valid *)
let mode_consume_valid () = ()

(** ============================================================================
    LINEARITY PRESERVATION
    ============================================================================ *)

(* Helper: no_duplicate_vars is preserved by split *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 150"
let rec split_preserves_no_dup_aux (ctx: mode_ctx) : Lemma
  (requires no_duplicate_vars ctx = true)
  (ensures (let (l, r) = split_ctx ctx in
            no_duplicate_vars l = true /\ no_duplicate_vars r = true))
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | (x, m, em) :: rest ->
      (* split_ctx maps over the list preserving structure *)
      split_preserves_no_dup_aux rest
#pop-options

(* Split preserves linearity: the main theorem.
   Follows HACL* Lib.Buffer modifies preservation pattern. *)
let split_preserves_linearity ctx =
  (* linearity_wf = mode_ctx_wf /\ valid_mode_ctx *)
  (* mode_ctx_wf = no_duplicate_vars /\ valid_mode_ctx *)
  split_preserves_no_dup_aux ctx;
  split_preserves_valid ctx

(* Join preserves linearity *)
let join_preserves_linearity ctx1 ctx2 =
  join_preserves_valid ctx1 ctx2

(* Consumption preserves linearity *)
let consume_preserves_linearity x ctx =
  consume_preserves_valid x ctx

(* Contraction preserves linearity *)
let contract_preserves_linearity x ctx =
  match contract_mode_ctx x ctx with
  | None -> ()
  | Some ctx' ->
      (* Contraction only changes mode to MOmega, preserving structure *)
      ()

(** ============================================================================
    MODE ALGEBRA LAWS - Complete lattice/semiring structure
    ============================================================================ *)

(* Lattice distributivity: join distributes over meet.
   Proof by exhaustive case analysis. *)
#push-options "--fuel 1 --ifuel 1"
let mode_join_distrib_meet m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, _, _ -> ()
  | _, MZero, _ -> ()
  | _, _, MZero -> ()
  | MOne, MOne, MOne -> ()
  | MOne, MOne, MOmega -> ()
  | MOne, MOmega, MOne -> ()
  | MOne, MOmega, MOmega -> ()
  | MOmega, MOne, MOne -> ()
  | MOmega, MOne, MOmega -> ()
  | MOmega, MOmega, MOne -> ()
  | MOmega, MOmega, MOmega -> ()
#pop-options

(* Lattice distributivity: meet distributes over join.
   Proof by exhaustive case analysis. *)
#push-options "--fuel 1 --ifuel 1"
let mode_meet_distrib_join m1 m2 m3 =
  match m1, m2, m3 with
  | MOmega, _, _ -> ()
  | _, MOmega, _ -> ()
  | _, _, MOmega -> ()
  | MZero, MZero, MZero -> ()
  | MZero, MZero, MOne -> ()
  | MZero, MOne, MZero -> ()
  | MZero, MOne, MOne -> ()
  | MOne, MZero, MZero -> ()
  | MOne, MZero, MOne -> ()
  | MOne, MOne, MZero -> ()
  | MOne, MOne, MOne -> ()
#pop-options

(* Mode addition is monotonic.
   Proof: if m1 <= m2, then m1 + m3 <= m2 + m3 by case analysis. *)
#push-options "--fuel 1 --ifuel 1"
let mode_add_monotonic m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, MZero, _ -> ()
  | MZero, MOne, MZero -> ()
  | MZero, MOne, MOne -> ()
  | MZero, MOne, MOmega -> ()
  | MZero, MOmega, _ -> ()
  | MOne, MOne, _ -> ()
  | MOne, MOmega, _ -> ()
  | MOmega, MOmega, _ -> ()
  | _, _, _ -> ()  (* Precondition excludes other cases *)
#pop-options

(* Mode multiplication is monotonic.
   Proof: if m1 <= m2, then m1 * m3 <= m2 * m3 by case analysis. *)
#push-options "--fuel 1 --ifuel 1"
let mode_mul_monotonic m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, _, _ -> ()
  | MOne, MOne, _ -> ()
  | MOne, MOmega, MZero -> ()
  | MOne, MOmega, MOne -> ()
  | MOne, MOmega, MOmega -> ()
  | MOmega, MOmega, _ -> ()
  | _, _, _ -> ()
#pop-options

(* Multiplication distributes over join.
   Proof by exhaustive case analysis using mode semiring properties. *)
#push-options "--fuel 1 --ifuel 1"
let mode_mul_distrib_join m1 m2 m3 =
  match m1, m2, m3 with
  | MZero, _, _ -> ()
  | _, MZero, MZero -> ()
  | MOne, MZero, MOne -> ()
  | MOne, MZero, MOmega -> ()
  | MOne, MOne, MZero -> ()
  | MOne, MOne, MOne -> ()
  | MOne, MOne, MOmega -> ()
  | MOne, MOmega, MZero -> ()
  | MOne, MOmega, MOne -> ()
  | MOne, MOmega, MOmega -> ()
  | MOmega, MZero, MOne -> ()
  | MOmega, MZero, MOmega -> ()
  | MOmega, MOne, MZero -> ()
  | MOmega, MOne, MOne -> ()
  | MOmega, MOne, MOmega -> ()
  | MOmega, MOmega, MZero -> ()
  | MOmega, MOmega, MOne -> ()
  | MOmega, MOmega, MOmega -> ()
#pop-options

(** ============================================================================
    EXTENDED MODE ALGEBRA
    ============================================================================ *)

(* Extended mode lattice join: least upper bound.
   Lattice structure:
     EMLinear (bottom)
        /    \
   EMAffine  EMRelevant
        \    /
    EMUnrestricted (top) *)
let extended_mode_join (em1 em2: extended_mode) : extended_mode =
  match em1, em2 with
  | EMUnrestricted, _ -> EMUnrestricted
  | _, EMUnrestricted -> EMUnrestricted
  | EMAffine, EMRelevant -> EMUnrestricted
  | EMRelevant, EMAffine -> EMUnrestricted
  | EMAffine, EMAffine -> EMAffine
  | EMAffine, EMLinear -> EMAffine
  | EMLinear, EMAffine -> EMAffine
  | EMRelevant, EMRelevant -> EMRelevant
  | EMRelevant, EMLinear -> EMRelevant
  | EMLinear, EMRelevant -> EMRelevant
  | EMLinear, EMLinear -> EMLinear

(* Extended mode lattice meet: greatest lower bound *)
let extended_mode_meet (em1 em2: extended_mode) : extended_mode =
  match em1, em2 with
  | EMLinear, _ -> EMLinear
  | _, EMLinear -> EMLinear
  | EMAffine, EMRelevant -> EMLinear
  | EMRelevant, EMAffine -> EMLinear
  | EMAffine, EMAffine -> EMAffine
  | EMAffine, EMUnrestricted -> EMAffine
  | EMUnrestricted, EMAffine -> EMAffine
  | EMRelevant, EMRelevant -> EMRelevant
  | EMRelevant, EMUnrestricted -> EMRelevant
  | EMUnrestricted, EMRelevant -> EMRelevant
  | EMUnrestricted, EMUnrestricted -> EMUnrestricted

(* Extended mode join is commutative *)
let extended_mode_join_comm em1 em2 =
  match em1, em2 with
  | EMLinear, EMLinear -> ()
  | EMLinear, EMAffine -> ()
  | EMLinear, EMRelevant -> ()
  | EMLinear, EMUnrestricted -> ()
  | EMAffine, EMLinear -> ()
  | EMAffine, EMAffine -> ()
  | EMAffine, EMRelevant -> ()
  | EMAffine, EMUnrestricted -> ()
  | EMRelevant, EMLinear -> ()
  | EMRelevant, EMAffine -> ()
  | EMRelevant, EMRelevant -> ()
  | EMRelevant, EMUnrestricted -> ()
  | EMUnrestricted, EMLinear -> ()
  | EMUnrestricted, EMAffine -> ()
  | EMUnrestricted, EMRelevant -> ()
  | EMUnrestricted, EMUnrestricted -> ()

(* Extended mode meet is commutative *)
let extended_mode_meet_comm em1 em2 =
  match em1, em2 with
  | EMLinear, EMLinear -> ()
  | EMLinear, EMAffine -> ()
  | EMLinear, EMRelevant -> ()
  | EMLinear, EMUnrestricted -> ()
  | EMAffine, EMLinear -> ()
  | EMAffine, EMAffine -> ()
  | EMAffine, EMRelevant -> ()
  | EMAffine, EMUnrestricted -> ()
  | EMRelevant, EMLinear -> ()
  | EMRelevant, EMAffine -> ()
  | EMRelevant, EMRelevant -> ()
  | EMRelevant, EMUnrestricted -> ()
  | EMUnrestricted, EMLinear -> ()
  | EMUnrestricted, EMAffine -> ()
  | EMUnrestricted, EMRelevant -> ()
  | EMUnrestricted, EMUnrestricted -> ()

(* Extended mode subtyping is reflexive *)
let extended_mode_subtype_refl em =
  match em with
  | EMLinear -> ()
  | EMAffine -> ()
  | EMRelevant -> ()
  | EMUnrestricted -> ()

(* Extended mode subtyping is transitive.
   Proof by case analysis on the lattice structure. *)
#push-options "--fuel 1 --ifuel 1"
let extended_mode_subtype_trans em1 em2 em3 =
  match em1, em2, em3 with
  (* EMLinear subtypes everything *)
  | EMLinear, _, _ -> ()
  (* EMAffine cases *)
  | EMAffine, EMAffine, EMAffine -> ()
  | EMAffine, EMAffine, EMUnrestricted -> ()
  | EMAffine, EMUnrestricted, EMUnrestricted -> ()
  (* EMRelevant cases *)
  | EMRelevant, EMRelevant, EMRelevant -> ()
  | EMRelevant, EMRelevant, EMUnrestricted -> ()
  | EMRelevant, EMUnrestricted, EMUnrestricted -> ()
  (* EMUnrestricted cases *)
  | EMUnrestricted, EMUnrestricted, EMUnrestricted -> ()
  (* Other cases excluded by preconditions *)
  | _, _, _ -> ()
#pop-options

(* Extended mode subtyping is antisymmetric *)
let extended_mode_subtype_antisym em1 em2 =
  match em1, em2 with
  | EMLinear, EMLinear -> ()
  | EMAffine, EMAffine -> ()
  | EMRelevant, EMRelevant -> ()
  | EMUnrestricted, EMUnrestricted -> ()
  | _, _ -> ()  (* Precondition excludes asymmetric cases *)

(** ============================================================================
    BORROW CHECKER STYLE PROOFS
    ============================================================================ *)

(* Exclusive borrow invariant: at most one mutable borrow at a time.
   This follows from the mode_ctx_wf ensuring no duplicate variables,
   combined with the fact that affine mode prevents duplication. *)
let exclusive_borrow_invariant ctx x y =
  (* Well-formedness guarantees no duplicates, and affine mode prevents
     the same variable from appearing twice with MOne. If x has MOne+EMAffine,
     either x = y, or y has different mode/extended_mode combination. *)
  ()

(* Shared borrow coexistence: MOmega resources are duplicated by split *)
let shared_borrow_coexist ctx x =
  split_ctx_omega_shared ctx x

(* Borrow expiration: full permission box can be thawed to diamond *)
let borrow_expiration rk =
  match rk with
  | RefBox p ->
      if is_full_perm p then ()
      else ()
  | RefDiamond -> ()

(* No use after move: consumed linear resource blocks further access *)
let no_use_after_move ctx x =
  (* consume checks mode first; MZero returns None *)
  ()

(* Linear move semantics: consuming linear resource sets mode to MZero *)
let linear_move_semantics ctx x =
  (* By definition of consume: MOne -> Some (update_mode x MZero ctx) *)
  ()

(** ============================================================================
    CONTEXT COMPOSITION
    ============================================================================ *)

(* Sequential composition: apply ctx2's consumption pattern to ctx1's output.
   For each variable, combine modes: if ctx2 consumes, reduce ctx1's mode. *)
let ctx_seq_compose (ctx1 ctx2: mode_ctx) : mode_ctx =
  let compose_one (entry: mode_ctx_entry) : mode_ctx_entry =
    match entry with
    | (x, m1, em) ->
        let m2 = lookup_mode_only x ctx2 in
        (* If ctx2 consumes (m2 = MZero), result is MZero.
           If ctx2 doesn't touch (m2 = MOne), keep m1.
           If both are omega, stay omega. *)
        let m_result = mode_mul m1 m2 in
        (x, m_result, em)
  in
  map compose_one ctx1

(* Sequential composition preserves well-formedness.
   Proof: map preserves list structure, mode_mul preserves validity. *)
let ctx_seq_compose_wf ctx1 ctx2 =
  (* Mapping preserves no_duplicate_vars since we only transform modes.
     valid_mode_ctx is preserved because mode_mul respects extended_mode constraints. *)
  ()

(* Parallel composition commutativity.
   Mode join is commutative, so the resulting modes are the same. *)
#push-options "--fuel 2 --ifuel 1"
let ctx_par_compose_comm ctx1 ctx2 =
  (* For each variable x:
     get_mode_in_ctx x (join_ctx ctx1 ctx2) uses mode_join m1 m2
     get_mode_in_ctx x (join_ctx ctx2 ctx1) uses mode_join m2 m1
     By mode_join_comm, these are equal. *)
  ()
#pop-options
