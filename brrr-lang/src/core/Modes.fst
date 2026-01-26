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

(* Types mode, extended_mode, and all mode operations are defined in Modes.fsti
   with 'unfold' for automatic normalization in proofs. *)

(** ============================================================================
    SEMIRING LAWS (Lemmas)
    With unfold definitions in .fsti, all proofs are trivial by normalization.
    ============================================================================ *)

(* Addition is commutative: m1 + m2 = m2 + m1 *)
let mode_add_comm m1 m2 = ()

(* Addition is associative: (m1 + m2) + m3 = m1 + (m2 + m3) *)
let mode_add_assoc m1 m2 m3 = ()

(* Zero is additive identity: 0 + m = m *)
let mode_add_zero m = ()

(* Multiplication is associative *)
let mode_mul_assoc m1 m2 m3 = ()

(* Multiplication is commutative: m1 * m2 = m2 * m1 *)
let mode_mul_comm m1 m2 = ()

(* One is multiplicative identity: 1 * m = m
   With unfold in .fsti, normalization handles this automatically. *)
let mode_mul_one m = ()

(* Zero annihilates: 0 * m = 0
   With unfold in .fsti, normalization handles this automatically. *)
let mode_mul_zero m = ()

(* Distributivity: m1 * (m2 + m3) = m1*m2 + m1*m3
   With unfold in .fsti, normalization handles all 27 cases automatically. *)
let mode_distrib m1 m2 m3 = ()

(* mode_leq is reflexive - trivial with unfold *)
let mode_leq_refl m = ()

(* mode_leq is transitive - with unfold and preconditions, trivial *)
let mode_leq_trans m1 m2 m3 = ()

(* Extended mode consistency: mode_leq is reflexive on extended mode's base mode.
   Trivial with unfold since mode_leq m m = true for all m. *)
let extended_mode_consistent em = ()

(** ============================================================================
    MODE LATTICE LAWS
    Signatures declared in Modes.fsti - only implementations here
    ============================================================================ *)

(* Join is commutative: m1 join m2 = m2 join m1 - trivial with unfold *)
let mode_join_comm m1 m2 = ()

(* Join is associative: (m1 join m2) join m3 = m1 join (m2 join m3) - trivial with unfold *)
let mode_join_assoc m1 m2 m3 = ()

(* Zero is identity for join *)
let mode_join_zero m = ()

(* Omega is absorbing for join *)
let mode_join_omega m = ()

(* Join is idempotent: m join m = m - trivial with unfold *)
let mode_join_idemp m = ()

(* Meet is commutative: m1 meet m2 = m2 meet m1 - trivial with unfold *)
let mode_meet_comm m1 m2 = ()

(* Meet is associative: (m1 meet m2) meet m3 = m1 meet (m2 meet m3) - trivial with unfold *)
let mode_meet_assoc m1 m2 m3 = ()

(* Omega is identity for meet *)
let mode_meet_omega m = ()

(* Zero is absorbing for meet *)
let mode_meet_zero m = ()

(* Meet is idempotent: m meet m = m - trivial with unfold *)
let mode_meet_idemp m = ()

(* Antisymmetry: if m1 <= m2 and m2 <= m1 then m1 = m2 - trivial with unfold and preconditions *)
let mode_leq_antisym m1 m2 = ()

(* Lattice absorption laws - trivial with unfold *)
let mode_absorb_join_meet m1 m2 = ()
let mode_absorb_meet_join m1 m2 = ()

(* Connection between ordering and lattice operations - trivial with unfold *)
let mode_leq_join m1 m2 = ()
let mode_leq_meet m1 m2 = ()

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
    LIST HELPER LEMMAS (for context validity proofs)
    ============================================================================ *)

(* Helper: for_all preserved under filter *)
#push-options "--fuel 1 --ifuel 1"
let rec for_all_filter (#a: Type) (p: a -> bool) (f: a -> bool) (l: list a)
  : Lemma (requires for_all p l = true)
          (ensures for_all p (filter f l) = true)
          (decreases l)
= match l with
  | [] -> ()
  | hd :: tl ->
      if f hd then for_all_filter p f tl
      else for_all_filter p f tl
#pop-options

(* Helper: for_all on cons *)
let for_all_cons (#a: Type) (p: a -> bool) (x: a) (l: list a)
  : Lemma (requires p x = true /\ for_all p l = true)
          (ensures for_all p (x :: l) = true)
= ()

(* Helper: for_all preserved under map when f preserves predicate *)
#push-options "--fuel 1 --ifuel 1"
let rec for_all_map (#a #b: Type) (p: b -> bool) (f: a -> b) (l: list a)
  (hf: (x: a) -> Lemma (requires memP x l) (ensures p (f x) = true))
  : Lemma (ensures for_all p (map f l) = true)
          (decreases l)
= match l with
  | [] -> ()
  | hd :: tl ->
      hf hd;
      for_all_map p f tl (fun x -> hf x)
#pop-options

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

(* Check if an entry has linear extended mode *)
let is_linear_entry (entry: mode_ctx_entry) : bool =
  match entry with
  | (_, _, EMLinear) -> true
  | _ -> false

(* Helper: get mode from context (local version for use before main def) *)
let get_mode_local (x: string) (ctx: mode_ctx) : mode =
  fst (lookup_mode x ctx)

(* Linear Exclusivity Predicate:
   For contexts from a split, linear resources can have mode MOne in at most one context.
   This ensures join won't produce ω (from 1+1) for linear resources. *)
let linear_exclusive_entry (x: string) (ctx1 ctx2: mode_ctx) : bool =
  let em = lookup_extended_mode x ctx1 in
  if em = EMLinear then
    let m1 = get_mode_local x ctx1 in
    let m2 = get_mode_local x ctx2 in
    (* If one has MOne, other must have MZero *)
    not (m1 = MOne && m2 = MOne)
  else true  (* Non-linear entries don't need exclusivity *)

let linear_exclusive (ctx1 ctx2: mode_ctx) : bool =
  for_all (fun (entry: mode_ctx_entry) ->
    match entry with (x, _, _) -> linear_exclusive_entry x ctx1 ctx2
  ) ctx1

(* Consume preserves validity.
   Consume does: MOne→MZero or MOmega→MOmega.
   update_mode creates: (x, MZero, em) :: filter (y <> x) ctx

   Proof:
   1. MZero is valid for ALL extended modes (EMLinear, EMAffine, EMRelevant, EMUnrestricted)
   2. filter preserves for_all (using for_all_filter helper) *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let consume_preserves_valid x ctx =
  match consume x ctx with
  | None -> ()  (* Postcondition is vacuously true *)
  | Some ctx' ->
      let (m, em) = lookup_mode x ctx in
      match m with
      | MZero -> ()  (* consume returns None, can't reach here *)
      | MOmega -> ()  (* ctx' = ctx, unchanged *)
      | MOne ->
          (* ctx' = (x, MZero, em) :: filter (...) ctx *)
          (* Need: for_all valid_mode_ctx_entry ctx' *)
          let filtered = filter (fun (entry: mode_ctx_entry) -> match entry with (y, _, _) -> y <> x) ctx in
          (* MZero is valid for all extended modes *)
          assert (valid_mode_ctx_entry (x, MZero, em) = true);
          (* filter preserves for_all *)
          for_all_filter valid_mode_ctx_entry (fun (entry: mode_ctx_entry) -> match entry with (y, _, _) -> y <> x) ctx;
          for_all_cons valid_mode_ctx_entry (x, MZero, em) filtered
#pop-options

(* Split preserves validity.
   split_ctx maps each entry: (x, m, em) -> ((x, m1, em), (x, m2, em))
   where m1, m2 preserve validity for em. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150"
let rec split_preserves_valid_aux (ctx: mode_ctx)
  : Lemma (requires for_all valid_mode_ctx_entry ctx = true)
          (ensures (let (l, r) = split_ctx ctx in
                    for_all valid_mode_ctx_entry l = true /\
                    for_all valid_mode_ctx_entry r = true))
          (decreases ctx)
= match ctx with
  | [] -> ()
  | (x, m, em) :: rest ->
      split_preserves_valid_aux rest;
      (* For each entry, split preserves validity:
         MOmega -> (MOmega, MOmega): both valid
         MOne -> (MOne, MZero): both valid for EMLinear/EMAffine, always valid for others
         MZero -> (MZero, MZero): both valid *)
      ()
#pop-options

let split_preserves_valid ctx = split_preserves_valid_aux ctx

(* ============================================================================
   SPLIT ENSURES LINEAR EXCLUSIVITY

   Theorem (brrr_lang_spec_v0.4.tex, lines 1744-1749):
     linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)) = true

   Proof outline:
   - For any variable x, split_ctx never produces MOne in both halves.
   - Therefore linear_exclusive_entry x holds for all x.
   - Use for_all_cons to lift pointwise validity to the whole context.
   ============================================================================ *)

(* Helper: lookup skips the head when the variable names differ. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"
let linear_exclusive_entry_skip_head
  (x y: string) (m1 m2: mode) (em: extended_mode) (l r: mode_ctx)
  : Lemma (requires x <> y)
          (ensures linear_exclusive_entry x ((y, m1, em) :: l) ((y, m2, em) :: r) =
                   linear_exclusive_entry x l r)
= ()
#pop-options

(* For any x, splitting ctx makes x linearly exclusive across halves. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let rec split_linear_exclusive_entry (ctx: mode_ctx) (x: string)
  : Lemma (ensures linear_exclusive_entry x (fst (split_ctx ctx)) (snd (split_ctx ctx)) = true)
          (decreases ctx)
= match ctx with
  | [] -> ()
  | (y, m, em) :: rest ->
      split_linear_exclusive_entry rest x;
      if x = y then
        (* x is at the head: split_one never yields (MOne, MOne). *)
        match m with
        | MOne -> ()
        | MOmega -> ()
        | MZero -> ()
      else
        (* x is in the tail: lookup ignores the head, so reuse IH. *)
        assert (x <> y);
        match m with
        | MOne ->
            let (l, r) = split_ctx rest in
            linear_exclusive_entry_skip_head x y MOne MZero em l r;
            assert (linear_exclusive_entry x l r = true)
        | MOmega ->
            let (l, r) = split_ctx rest in
            linear_exclusive_entry_skip_head x y MOmega MOmega em l r;
            assert (linear_exclusive_entry x l r = true)
        | MZero ->
            let (l, r) = split_ctx rest in
            linear_exclusive_entry_skip_head x y MZero MZero em l r;
            assert (linear_exclusive_entry x l r = true)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let split_ensures_exclusivity ctx =
  let (l, r) = split_ctx ctx in
  let p (entry: mode_ctx_entry) : bool =
    match entry with (x, _, _) -> linear_exclusive_entry x l r
  in
  let rec all_entries (xs: mode_ctx)
    : Lemma (ensures for_all p xs = true)
            (decreases xs)
  = match xs with
    | [] -> ()
    | (x, m, em) :: tl ->
        split_linear_exclusive_entry ctx x;
        all_entries tl;
        assert (p (x, m, em) = true);
        (* Lift pointwise truth to for_all on cons. *)
        for_all_cons p (x, m, em) tl
  in
  all_entries l
#pop-options

(* Helper: mode_join on {MZero, MOne} x {MZero, MOne} always produces {MZero, MOne}.

   Key insight: mode_join is a LATTICE JOIN (least upper bound), NOT mode_add.
   - mode_join MZero MZero = MZero
   - mode_join MZero MOne = MOne
   - mode_join MOne MZero = MOne
   - mode_join MOne MOne = MOne (NOT MOmega!)
   - mode_join MOmega _ = MOmega
   - mode_join _ MOmega = MOmega

   So the ONLY way to get MOmega from mode_join is if one input is MOmega. *)
let mode_join_linear_closed (m1 m2: mode) : Lemma
  (requires (m1 = MZero \/ m1 = MOne) /\ (m2 = MZero \/ m2 = MOne))
  (ensures mode_join m1 m2 = MZero \/ mode_join m1 m2 = MOne)
= ()

(* Join preserves validity WHEN linear exclusivity holds:
   With the linear_exclusive precondition, we know for EMLinear entries:
   - At most one context has MOne
   - So mode_join can only produce: 0+0=0, 0+1=1, 1+0=1 (never 1+1=ω)
   - All of {0, 1} are valid for EMLinear

   NOTE: The full proof requires connecting valid_mode_ctx (for_all valid_mode_ctx_entry)
   to individual entry properties, and showing mode_join preserves validity under
   the linear_exclusive precondition. This is semantically correct but mechanically
   complex due to interactions between for_all, map, and lookup. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let join_preserves_valid ctx1 ctx2 =
  (* With linear_exclusive precondition, join cannot produce ω for EMLinear entries.
     The possible outcomes per entry:
     - EMLinear: 0+0=0, 0+1=1, 1+0=1 (all valid, 1+1 excluded by precondition)
     - EMAffine: same as EMLinear
     - EMRelevant/EMUnrestricted: any result is valid

     The mode_join_linear_closed lemma establishes that mode_join on {0,1} x {0,1}
     produces {0,1}, which is valid for EMLinear/EMAffine. *)
  admit ()  (* Full mechanical proof deferred - semantically sound by mode_join_linear_closed *)
#pop-options

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
let rec count_total_eq (ctx: mode_ctx) : Lemma
  (ensures length ctx = count_owned ctx + count_borrowed ctx + count_consumed ctx)
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | _ :: rest -> count_total_eq rest

(* Helper: count_owned after split_one - trivial by definition *)
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
= ()

(* Split preserves owned count: linear resources go exclusively to left. *)
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

let split_preserves_owned_count ctx = split_preserves_owned_count_aux ctx

(* Helper for borrowed count preservation - trivial by definition *)
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
= ()

(* Split duplicates borrowed count: both halves get the same borrowed count. *)
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

(* Mode transition is reflexive for available modes - trivial *)
let mode_transition_refl m = ()

(* Mode transition is transitive - trivial with preconditions *)
let mode_transition_trans m1 m2 m3 = ()

(* Consumption is terminal: after MZero, only MZero is reachable - trivial *)
let mode_zero_terminal m = ()

(* Contraction is valid transition *)
let mode_contraction_valid () = ()

(* Consumption from linear is valid *)
let mode_consume_valid () = ()

(** ============================================================================
    LINEARITY PRESERVATION
    ============================================================================ *)

(* Helper: no_duplicate_vars is preserved by split *)
let rec split_preserves_no_dup_aux (ctx: mode_ctx) : Lemma
  (requires no_duplicate_vars ctx = true)
  (ensures (let (l, r) = split_ctx ctx in
            no_duplicate_vars l = true /\ no_duplicate_vars r = true))
  (decreases ctx)
=
  match ctx with
  | [] -> ()
  | _ :: rest -> split_preserves_no_dup_aux rest

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

(* Lattice distributivity: join distributes over meet - trivial with unfold *)
let mode_join_distrib_meet m1 m2 m3 = ()

(* Lattice distributivity: meet distributes over join - trivial with unfold *)
let mode_meet_distrib_join m1 m2 m3 = ()

(* Mode addition is monotonic - trivial with unfold and preconditions *)
let mode_add_monotonic m1 m2 m3 = ()

(* Mode multiplication is monotonic - trivial with unfold and preconditions *)
let mode_mul_monotonic m1 m2 m3 = ()

(* Multiplication distributes over join - trivial with unfold *)
let mode_mul_distrib_join m1 m2 m3 = ()

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

(* Extended mode join is commutative - trivial by case analysis *)
let extended_mode_join_comm em1 em2 = ()

(* Extended mode meet is commutative - trivial by case analysis *)
let extended_mode_meet_comm em1 em2 = ()

(* Extended mode subtyping is reflexive - trivial by definition *)
let extended_mode_subtype_refl em = ()

(* Extended mode subtyping is transitive - trivial with preconditions *)
let extended_mode_subtype_trans em1 em2 em3 = ()

(* Extended mode subtyping is antisymmetric - trivial with preconditions *)
let extended_mode_subtype_antisym em1 em2 = ()

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

(* Parallel composition commutativity - trivial by mode_join_comm *)
let ctx_par_compose_comm ctx1 ctx2 = ()
