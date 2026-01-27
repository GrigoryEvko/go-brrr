(**
 * Modes.Theorems - Interface for Linear Type System Soundness Theorems
 *
 * This interface exposes the critical theorems for linear type system soundness:
 *   - T-2.4: split_ensures_exclusivity
 *   - T-2.5: valid_ctx_linear_mode
 *   - T-2.6: join_preserves_valid
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

(** ============================================================================
    HELPER PREDICATES
    ============================================================================ *)

(** Predicate: is a mode restricted (MOne or MZero, not MOmega)? *)
val is_restricted_mode : mode -> bool

(** Helper: extract mode from context for a variable *)
val get_mode_for_var : string -> mode_ctx -> mode

(** Helper: extract extended mode from context for a variable *)
val get_ext_mode_for_var : string -> mode_ctx -> extended_mode

(** ============================================================================
    THEOREM T-2.4: Split Ensures Exclusivity
    ============================================================================ *)

(** Linear exclusivity after split: for any variable x with EMLinear in the
    original context, at most one of the split contexts has mode MOne for x. *)
val split_ensures_exclusivity_theorem : ctx:mode_ctx ->
  Lemma (ensures linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)) = true)
        [SMTPat (split_ctx ctx)]

(** ============================================================================
    THEOREM T-2.5: Valid Context Linear Mode Invariant
    ============================================================================ *)

(** T-2.5: Valid contexts enforce that EMLinear entries have restricted modes.

    If a context is valid and a variable x has EMLinear extended mode,
    then x's mode must be MOne or MZero (cannot be MOmega).

    This is the fundamental invariant from Girard 1987 Linear Logic:
    linear hypotheses cannot have unrestricted multiplicity. *)
val valid_ctx_linear_mode_theorem : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures is_restricted_mode (get_mode_for_var x ctx) = true)

(** Corollary: EMLinear entries cannot have MOmega mode in valid contexts *)
val valid_ctx_linear_not_omega : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures get_mode_for_var x ctx <> MOmega)

(** Generalization: EMAffine also enforces restricted modes *)
val valid_ctx_affine_mode_theorem : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  get_ext_mode_for_var x ctx = EMAffine)
        (ensures is_restricted_mode (get_mode_for_var x ctx) = true)

(** ============================================================================
    THEOREM T-2.6: Join Preserves Validity
    ============================================================================ *)

(** Helper lemma: mode_join preserves restriction when inputs are restricted *)
val mode_join_preserves_restricted : m1:mode -> m2:mode ->
  Lemma (requires is_restricted_mode m1 = true /\ is_restricted_mode m2 = true)
        (ensures is_restricted_mode (mode_join m1 m2) = true)

(** T-2.6: Context join preserves validity under linear exclusivity.

    CRITICAL PRECONDITION: linear_exclusive ctx1 ctx2 ensures that for
    any variable x with EMLinear, at most one context has mode MOne. *)
val join_preserves_valid_theorem : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx1 = true /\
                  valid_mode_ctx ctx2 = true /\
                  linear_exclusive ctx1 ctx2 = true)
        (ensures valid_mode_ctx (join_ctx ctx1 ctx2) = true)

(** Corollary: Split then join roundtrip preserves validity *)
val split_join_preserves_valid : ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true)
        (ensures valid_mode_ctx (join_ctx (fst (split_ctx ctx)) (snd (split_ctx ctx))) = true)

(** ============================================================================
    ADDITIONAL SUPPORTING LEMMAS
    ============================================================================ *)

(** Consumption preserves the linear mode invariant *)
val consume_preserves_linear_invariant : ctx:mode_ctx -> x:string ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  Some? (consume x ctx) /\
                  get_ext_mode_for_var x ctx = EMLinear)
        (ensures get_mode_for_var x (Some?.v (consume x ctx)) = MZero)

(** Linear exclusivity is symmetric *)
val linear_exclusive_sym : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires linear_exclusive ctx1 ctx2 = true)
        (ensures linear_exclusive ctx2 ctx1 = true)

(** Empty context is valid *)
val empty_ctx_valid : unit ->
  Lemma (ensures valid_mode_ctx empty_mode_ctx = true)

(** Extending with a valid entry preserves validity *)
val extend_preserves_valid : x:string -> m:mode -> em:extended_mode -> ctx:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx = true /\
                  (match em with
                   | EMLinear -> m = MOne || m = MZero
                   | EMAffine -> m = MOne || m = MZero
                   | _ -> true))
        (ensures valid_mode_ctx (extend_mode_ctx x m em ctx) = true)
