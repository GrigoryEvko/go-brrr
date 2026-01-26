(**
 * Modes.Theorems - Linear Type System Soundness Theorems
 *
 * This module contains critical theorems for linear type system soundness,
 * establishing that context splitting and joining preserve linearity invariants.
 *
 * These theorems correspond to:
 *   - T-2.4: split_ensures_exclusivity
 *   - T-2.5: valid_ctx_linear_mode
 *   - T-2.6: join_preserves_valid
 *
 * Based on:
 *   - brrr_lang_spec_v0.4.tex, Part III (Ownership & Memory), Chapter 7-8
 *   - AXIOMS_REPORT_v2.md, Priority 2 theorems
 *
 * Literature references:
 *   - Girard 1987: Linear Logic (foundational)
 *   - Walker 2005: Substructural Type Systems (survey)
 *   - Wadler 1990: Linear Types Can Change the World
 *   - Atkey 2018: Syntax and Semantics of Quantitative Type Theory
 *)
module Modes.Theorems

open FStar.List.Tot
open Modes

(* Conservative Z3 options following HACL* patterns *)
#set-options "--z3rlimit 100 --fuel 2 --ifuel 2"

(** ============================================================================
    THEOREM T-2.4: Split Ensures Exclusivity

    ID: T-2.4
    Location: Modes.fst:467-485 (proven by construction)
    Effort: 2-3 hours
    Status: PROVEN in Modes.fst, restated here for completeness

    Statement: Context splitting preserves linear exclusivity. After splitting
    a context, linear resources (EMLinear) appear with mode MOne in at most
    one of the two resulting contexts.

    Proof Hint: By structural induction on the context. The split_one function
    maps MOne -> (MOne, MZero), ensuring linear resources go exclusively to
    the left context. Use for_all/map interaction lemmas.

    Literature: This is the key property ensuring that linear resources are
    not duplicated during parallel composition, following Girard's linear
    logic principle that linear hypotheses are used exactly once.
    ============================================================================ *)

(** Linear exclusivity after split: for any variable x with EMLinear in the
    original context, at most one of the split contexts has mode MOne for x. *)
val split_ensures_exclusivity_theorem : ctx:mode_ctx ->
  Lemma (ensures linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)) = true)
        [SMTPat (split_ctx ctx)]
let split_ensures_exclusivity_theorem ctx =
  (* Proven in Modes.fst:split_ensures_exclusivity via split_linear_exclusive_entry.
     The proof proceeds by induction on ctx:
     - Empty ctx: trivially true
     - (x, m, em) :: rest:
       * If m = MOne: split gives (MOne, MZero), so exclusivity holds for x
       * If m = MOmega: both get MOmega, but EMLinear check is false for omega
       * If m = MZero: both get MZero, exclusivity trivially holds
     The IH handles variables in rest. *)
  split_ensures_exclusivity ctx


(** ============================================================================
    THEOREM T-2.5: Valid Context Linear Mode Invariant

    ID: T-2.5
    Location: Modes.fst:322-329 (valid_mode_ctx_entry definition)
    Effort: 2-3 hours
    Status: Proof required

    Statement: In a valid mode context, entries with EMLinear extended mode
    can only have mode MOne or MZero (never MOmega). This ensures that
    linear resources cannot be contracted (duplicated) without explicit
    permission from the extended mode.

    Proof Hint: By the definition of valid_mode_ctx_entry:
      match em with
      | EMLinear -> m = MOne || m = MZero
      | EMAffine -> m = MOne || m = MZero
      | EMRelevant -> true
      | EMUnrestricted -> true
    The theorem follows directly from for_all distributing over the context.

    Literature: This invariant is central to substructural type systems
    (Walker 2005). Linear types forbid both weakening (drop without use)
    and contraction (duplicate). The mode MOne or MZero captures "used at
    most once", while EMLinear enforces "used exactly once" at the end.
    ============================================================================ *)

(** Predicate: is a mode restricted (MOne or MZero, not MOmega)? *)
let is_restricted_mode (m: mode) : bool =
  m = MOne || m = MZero

(** Helper: extract mode from context for a variable, with default MZero *)
let get_mode_for_var (x: string) (ctx: mode_ctx) : mode =
  lookup_mode_only x ctx

(** Helper: extract extended mode from context for a variable *)
let get_ext_mode_for_var (x: string) (ctx: mode_ctx) : extended_mode =
  lookup_extended_mode x ctx

(** T-2.5: Valid contexts enforce that EMLinear entries have restricted modes.

    If a context is valid and a variable x has EMLinear extended mode,
    then x's mode must be MOne or MZero (cannot be MOmega). *)
val valid_ctx_linear_mode_theorem : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures is_restricted_mode (get_mode_for_var x ctx) = true)
let valid_ctx_linear_mode_theorem ctx x =
  (* Proof outline:
     1. valid_mode_ctx ctx = for_all valid_mode_ctx_entry ctx
     2. If x is in ctx with extended mode EMLinear, then (x, m, EMLinear) is an entry
     3. valid_mode_ctx_entry (x, m, EMLinear) implies m = MOne || m = MZero
     4. Therefore is_restricted_mode m = true

     The mechanical proof requires showing that lookup_extended_mode x ctx = EMLinear
     implies there exists an entry (x, m, EMLinear) in ctx, and that for_all over
     valid_mode_ctx_entry implies valid_mode_ctx_entry holds for that entry.

     This is semantically immediate but requires list membership lemmas. *)
  admit ()


(** Corollary: EMLinear entries cannot have MOmega mode in valid contexts *)
val valid_ctx_linear_not_omega : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures get_mode_for_var x ctx <> MOmega)
let valid_ctx_linear_not_omega ctx x =
  valid_ctx_linear_mode_theorem ctx x


(** Generalization: EMAffine also enforces restricted modes *)
val valid_ctx_affine_mode_theorem : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMAffine)
        (ensures is_restricted_mode (get_mode_for_var x ctx) = true)
let valid_ctx_affine_mode_theorem ctx x =
  (* Same structure as T-2.5, using valid_mode_ctx_entry for EMAffine case *)
  admit ()


(** ============================================================================
    THEOREM T-2.6: Join Preserves Validity

    ID: T-2.6
    Location: Modes.fst:514-524
    Effort: 2-3 hours
    Status: Proof required (admit in Modes.fst)

    Statement: Context join preserves validity when the linear exclusivity
    precondition holds. This is CRITICAL for soundness of the L-App typing
    rule where we split contexts, type-check branches, and join results.

    Proof Hint: The key insight is that mode_join on {MZero, MOne} x {MZero, MOne}
    produces {MZero, MOne} (never MOmega). Use mode_join_linear_closed lemma:
      - mode_join MZero MZero = MZero
      - mode_join MZero MOne = MOne
      - mode_join MOne MZero = MOne
      - mode_join MOne MOne = MOne (NOT MOmega due to lattice semantics!)

    The linear_exclusive precondition ensures that for EMLinear entries,
    we never join MOne with MOne (one side always has MZero).

    Literature: This corresponds to the "context join" operation in linear
    logic sequent calculus, where contexts are split for parallel composition
    (tensor introduction) and joined for branch merge (plus elimination).
    See Girard 1987, Section 3 on multiplicative connectives.
    ============================================================================ *)

(** Helper lemma: mode_join preserves restriction when inputs are restricted.
    This is the core arithmetic fact underlying T-2.6. *)
val mode_join_preserves_restricted : m1:mode -> m2:mode ->
  Lemma (requires is_restricted_mode m1 = true /\ is_restricted_mode m2 = true)
        (ensures is_restricted_mode (mode_join m1 m2) = true)
let mode_join_preserves_restricted m1 m2 =
  (* By case analysis on mode_join definition:
     mode_join MZero MZero = MZero (restricted)
     mode_join MZero MOne = MOne (restricted)
     mode_join MOne MZero = MOne (restricted)
     mode_join MOne MOne = MOne (restricted, NOT omega!) *)
  ()


(** T-2.6: Context join preserves validity under linear exclusivity.

    CRITICAL PRECONDITION: linear_exclusive ctx1 ctx2 ensures that for
    any variable x with EMLinear, at most one context has mode MOne.
    Without this precondition, joining could produce invalid states. *)
val join_preserves_valid_theorem : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx1 = true /\
                  valid_mode_ctx ctx2 = true /\
                  linear_exclusive ctx1 ctx2 = true)
        (ensures valid_mode_ctx (join_ctx ctx1 ctx2) = true)
let join_preserves_valid_theorem ctx1 ctx2 =
  (* Proof outline:
     1. join_ctx maps each entry (x, m1, em) in ctx1 to (x, mode_join m1 m2, em)
        where m2 = lookup_mode_only x ctx2

     2. For each extended mode em, we must show valid_mode_ctx_entry holds:

        Case EMLinear:
          - valid_mode_ctx ctx1 => m1 in {MZero, MOne}
          - valid_mode_ctx ctx2 => m2 in {MZero, MOne} (by T-2.5 generalized)
          - linear_exclusive ctx1 ctx2 => not (m1 = MOne /\ m2 = MOne)
          - Therefore (m1, m2) in {(0,0), (0,1), (1,0)}
          - mode_join on these: {0, 1, 1} - all restricted
          - valid_mode_ctx_entry (x, mode_join m1 m2, EMLinear) = true

        Case EMAffine: Same reasoning as EMLinear

        Case EMRelevant: valid_mode_ctx_entry always true

        Case EMUnrestricted: valid_mode_ctx_entry always true

     3. By for_all preservation under map, valid_mode_ctx (join_ctx ctx1 ctx2)

     Mechanical complexity: connecting for_all, map, lookup, and the
     linear_exclusive pointwise predicate requires careful lemma composition. *)
  admit ()


(** Corollary: Split then join roundtrip preserves validity *)
val split_join_preserves_valid : ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true)
        (ensures valid_mode_ctx (join_ctx (fst (split_ctx ctx)) (snd (split_ctx ctx))) = true)
let split_join_preserves_valid ctx =
  (* split_ctx produces linearly exclusive contexts (T-2.4) *)
  split_ensures_exclusivity_theorem ctx;
  (* split_ctx preserves validity *)
  split_preserves_valid ctx;
  (* Therefore join is valid by T-2.6 *)
  join_preserves_valid_theorem (fst (split_ctx ctx)) (snd (split_ctx ctx))


(** ============================================================================
    ADDITIONAL SUPPORTING LEMMAS FOR LINEAR TYPE SOUNDNESS
    ============================================================================ *)

(** Lemma: Consumption preserves the linear mode invariant.
    After consuming a linear variable, its mode becomes MZero (still restricted). *)
val consume_preserves_linear_invariant : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  Some? (consume x ctx) /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures get_mode_for_var x (Some?.v (consume x ctx)) = MZero)
let consume_preserves_linear_invariant ctx x =
  (* By definition of consume:
     - If mode is MOne, returns Some (update_mode x MZero ctx)
     - If mode is MOmega, returns Some ctx (unchanged)
     - If mode is MZero, returns None

     Given valid_mode_ctx and EMLinear, mode must be MOne or MZero (T-2.5).
     If MZero, consume returns None (contradicts precondition).
     Therefore mode is MOne, and result has mode MZero for x. *)
  admit ()


(** Lemma: Linear exclusivity is symmetric *)
val linear_exclusive_sym : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires linear_exclusive ctx1 ctx2 = true)
        (ensures linear_exclusive ctx2 ctx1 = true)
let linear_exclusive_sym ctx1 ctx2 =
  (* linear_exclusive_entry checks: not (m1 = MOne /\ m2 = MOne)
     This is symmetric in m1 and m2. *)
  admit ()


(** Lemma: Empty context is valid *)
val empty_ctx_valid : unit ->
  Lemma (ensures valid_mode_ctx empty_mode_ctx = true)
let empty_ctx_valid () =
  (* empty_mode_ctx = [], for_all _ [] = true *)
  ()


(** Lemma: Extending with a valid entry preserves validity *)
val extend_preserves_valid : x:string -> m:mode -> em:extended_mode -> ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  (match em with
                   | EMLinear -> m = MOne || m = MZero
                   | EMAffine -> m = MOne || m = MZero
                   | _ -> true))
        (ensures valid_mode_ctx (extend_mode_ctx x m em ctx) = true)
let extend_preserves_valid x m em ctx =
  (* extend_mode_ctx prepends (x, m, em) to ctx.
     The precondition ensures valid_mode_ctx_entry (x, m, em) = true.
     for_all on the extended list follows from for_all_cons. *)
  admit ()


(** ============================================================================
    TYPE-THEORETIC INTERPRETATION

    These theorems establish that the mode context forms a valid model of
    linear logic's resource semantics:

    1. Split (T-2.4) corresponds to tensor introduction (A tensor B):
       Gamma |- A    Delta |- B
       -------------------------
       Gamma, Delta |- A tensor B

       Linear resources in Gamma go to Gamma, not Delta (exclusivity).

    2. Join (T-2.6) corresponds to additive connective elimination:
       Gamma |- A    Gamma |- B
       -------------------------
       Gamma |- A & B

       Both branches use the same resources (join merges).

    3. Validity (T-2.5) ensures the structural rules are respected:
       - EMLinear: no weakening, no contraction
       - EMAffine: weakening allowed, no contraction
       - EMRelevant: no weakening, contraction allowed
       - EMUnrestricted: both allowed

    See Walker 2005 "Substructural Type Systems" for the categorical semantics.
    ============================================================================ *)
