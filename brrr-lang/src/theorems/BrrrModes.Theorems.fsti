(**
 * BrrrModes.Theorems - Interface for Linear Type System Soundness Theorems
 *
 * This interface exposes the critical theorems for linear type system soundness:
 *   - T-2.4: split_ensures_exclusivity
 *   - T-2.5: valid_ctx_linear_mode
 *   - T-2.6: join_preserves_valid
 *
 * ============================================================================
 * THEORETICAL FOUNDATION
 * ============================================================================
 *
 * The mode semiring M = {0, 1, omega} models resource usage multiplicities:
 *   - 0 (MZero): absent/consumed - resource unavailable
 *   - 1 (MOne): linear - must use exactly once
 *   - omega (MOmega): unrestricted - use any number of times
 *
 * Extended modes refine the structural rules (Walker 2005, Section 1.1):
 *   - EMLinear: forbids weakening AND contraction (Girard 1987 linear logic)
 *   - EMAffine: allows weakening, forbids contraction
 *   - EMRelevant: forbids weakening, allows contraction
 *   - EMUnrestricted: allows both (standard intuitionistic logic)
 *
 * The key insight from Girard's linear logic (1987) is that linear hypotheses
 * represent resources that must be used exactly once. The mode semiring
 * generalizes this: MOne captures "used at most once" while EMLinear enforces
 * "used exactly once" via the validity predicate.
 *
 * See: brrr_lang_spec_v0.4.tex, Chapter 7 (Mode Semiring), lines 1503-1705
 *
 * ============================================================================
 * LITERATURE REFERENCES
 * ============================================================================
 *
 * [Girard 1987] Girard, J-Y. "Linear Logic." Theoretical Computer Science,
 *               50(1):1-101, 1987.
 *               - Foundation: Linear hypotheses used exactly once
 *               - Exponentials: !A allows contraction, ?A allows weakening
 *               - Multiplicatives vs Additives: tensor vs plus
 *
 * [Walker 2005] Walker, D. "Substructural Type Systems." In Advanced Topics
 *               in Types and Programming Languages, B. Pierce (ed.), MIT Press.
 *               - Survey: Linear, affine, relevant, ordered type systems
 *               - Section 1.1: Structural rules (weakening, contraction, exchange)
 *               - Section 1.4: Context splitting for multiplicative connectives
 *
 * [Wadler 1990] Wadler, P. "Linear Types Can Change the World." In IFIP TC 2
 *               Working Conference on Programming Concepts and Methods, 1990.
 *               - Practical applications: Single-threaded arrays, I/O
 *
 * [Atkey 2018] Atkey, R. "Syntax and Semantics of Quantitative Type Theory."
 *               LICS 2018.
 *               - Semiring annotations: Generalizes linear/affine/relevant
 *               - Graded modal types
 *
 * ============================================================================
 * PROOF METHODOLOGY
 * ============================================================================
 *
 * The proofs use structural induction on mode contexts (lists of entries).
 * Key patterns from fstar_pop_book.md, lines 9265-9373:
 *
 * 1. Existential elimination (exists_elim):
 *    eliminate exists (x:t). p x
 *    returns q
 *    with pf_p. k x pf_p
 *
 * 2. Universal introduction (forall_intro):
 *    introduce forall (x:t). q x
 *    with f x
 *
 * 3. For proofs requiring witness extraction from for_all predicates,
 *    we use the for_all_mem lemma pattern to connect list membership
 *    with pointwise properties.
 *
 * See: FStar.Classical.forall_intro, FStar.Classical.exists_elim
 *)
module BrrrModes.Theorems

open FStar.List.Tot
open BrrrModes

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
    ============================================================================

    THEOREM STATEMENT (brrr_lang_spec_v0.4.tex, lines 1744-1749):

      forall ctx. linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx))

    where linear_exclusive ctx1 ctx2 := forall x.
      is_linear x ctx1 ==>
        (get_mode x ctx1 = MOne ==> get_mode x ctx2 = MZero) /\
        (get_mode x ctx2 = MOne ==> get_mode x ctx1 = MZero)

    INDUCTION STRATEGY:
    ------------------
    Proof by structural induction on the mode context (list of entries).

    Base case: ctx = []
      split_ctx [] = ([], [])
      linear_exclusive [] [] = true (vacuously, no entries to check)

    Inductive case: ctx = (y, m, em) :: rest
      IH: linear_exclusive (fst (split_ctx rest)) (snd (split_ctx rest)) = true

      By case analysis on m:
      - m = MOmega: split produces (MOmega, MOmega) in both halves
        Not EMLinear relevant since MOmega indicates unrestricted usage

      - m = MOne: split produces (MOne, MZero) - LEFT gets resource
        If em = EMLinear, then:
          get_mode y left = MOne, get_mode y right = MZero
          So linear_exclusive_entry y left right = not(MOne && MZero) = true

      - m = MZero: split produces (MZero, MZero) in both halves
        If em = EMLinear, both have MZero, so not(MZero && MZero) = true

    The induction is well-founded because lists are inductively defined.
    See: Walker 2005, Section 1.4 for context splitting in multiplicative rules.

    PROOF PATTERN (fstar_pop_book.md, lines 9265-9300):
    The for_all property is lifted using for_all_cons to connect pointwise
    truth to the entire list.
    ============================================================================ *)

(** Linear exclusivity after split: for any variable x with EMLinear in the
    original context, at most one of the split contexts has mode MOne for x. *)
val split_ensures_exclusivity_theorem : ctx:mode_ctx ->
  Lemma (ensures linear_exclusive (fst (split_ctx ctx)) (snd (split_ctx ctx)) = true)
        [SMTPat (split_ctx ctx)]

(** ============================================================================
    THEOREM T-2.5: Valid Context Linear Mode Invariant
    ============================================================================

    THEOREM STATEMENT (brrr_lang_spec_v0.4.tex, lines 1690-1705):

      forall ctx x. valid_mode_ctx ctx /\ get_ext_mode_for_var x ctx = EMLinear
                    ==> is_restricted_mode (get_mode_for_var x ctx)

    This captures Girard's (1987) key insight: linear hypotheses have
    restricted multiplicity. The valid_mode_ctx predicate enforces this
    constraint at the type level.

    INDUCTION STRATEGY:
    ------------------
    Proof by structural induction on ctx combined with direct search.

    The key helper lemma for_all_direct_search_restricted shows:
      for_all valid_mode_ctx_entry ctx /\ (x, m, EMLinear) in ctx
      ==> m = MOne \/ m = MZero

    Base case: ctx = []
      get_ext_mode_for_var x [] returns EMUnrestricted (default)
      Precondition get_ext_mode_for_var x ctx = EMLinear fails
      Lemma holds vacuously

    Inductive case: ctx = (y, m, em) :: rest
      Case y = x:
        valid_mode_ctx ctx = true implies valid_mode_ctx_entry (y, m, em) = true
        If em = EMLinear, then by valid_mode_ctx_entry definition:
          m = MOne \/ m = MZero (both are restricted)

      Case y <> x:
        By IH on rest with for_all preserved through tail

    CONNECTION TO GIRARD 1987:
    The exponential modality !A in linear logic allows contraction/weakening.
    EMLinear corresponds to bare A (no exponential), which must be used exactly
    once. The validity predicate enforces this by restricting the mode to
    {MZero, MOne} and excluding MOmega.

    PROOF PATTERN (fstar_pop_book.md, lines 9500-9700):
    Uses the exists_elim pattern to extract a witness from for_all:

      exists_elim (goal:Type) (p:a -> Type0) (witness_proof:squash (exists x. p x))
                  (continuation:(x:a{p x} -> squash goal)) : Lemma goal

    Here we extract the entry (x, m, em) from ctx to show m is restricted.
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
    ============================================================================

    THEOREM STATEMENT (brrr_lang_spec_v0.4.tex, lines 1770-1795):

      forall ctx1 ctx2.
        valid_mode_ctx ctx1 /\ valid_mode_ctx ctx2 /\ linear_exclusive ctx1 ctx2
        ==> valid_mode_ctx (join_ctx ctx1 ctx2)

    This theorem is critical for the L-App (application) typing rule where:
      Gamma |- e1 : A -> B    Delta |- e2 : A
      ----------------------------------------
             Gamma + Delta |- e1 e2 : B

    The context join (Gamma + Delta) must remain valid.

    CRITICAL INSIGHT - Why linear_exclusive is required:
    Without exclusivity, joining two contexts where both have MOne for an
    EMLinear variable x would produce:
      mode_join MOne MOne = MOne (NOT MOmega, since mode_join is lattice join)
    But the extended mode tracking would be lost. The linear_exclusive
    precondition ensures at most one context has MOne.

    KEY ARITHMETIC FACT:
    mode_join is a LATTICE JOIN (least upper bound), NOT mode_add:
      mode_join MZero MZero = MZero
      mode_join MZero MOne  = MOne
      mode_join MOne  MZero = MOne
      mode_join MOne  MOne  = MOne (NOT MOmega!)
      mode_join MOmega _    = MOmega

    INDUCTION STRATEGY:
    ------------------
    Proof by structural induction on ctx1 (the list being mapped over in join_ctx).

    Base case: ctx1 = []
      join_ctx [] ctx2 = []
      valid_mode_ctx [] = true (for_all on empty list)

    Inductive case: ctx1 = (x, m1, em) :: rest
      IH: valid_mode_ctx (join_ctx rest ctx2) = true (given linear_exclusive rest ctx2)

      Let m2 = get_mode_for_var x ctx2
      join produces (x, mode_join m1 m2, em) :: join_ctx rest ctx2

      By case analysis on em:

      Case em = EMLinear or em = EMAffine:
        Need: mode_join m1 m2 = MOne \/ mode_join m1 m2 = MZero

        From T-2.5 (valid_ctx_linear_mode_theorem):
          m1 in {MZero, MOne} (from valid_mode_ctx ctx1)
          m2 in {MZero, MOne} (from valid_mode_ctx ctx2, if em matches)

        From mode_join_preserves_restricted:
          mode_join on {MZero, MOne} x {MZero, MOne} produces {MZero, MOne}

      Case em = EMRelevant or em = EMUnrestricted:
        Any mode is valid, so mode_join m1 m2 is valid

    DEPENDENCY CHAIN:
    T-2.4 (split_ensures_exclusivity) --> provides linear_exclusive
    T-2.5 (valid_ctx_linear_mode)     --> shows m1, m2 are restricted
    mode_join_preserves_restricted    --> shows result is restricted
    T-2.6 (join_preserves_valid)      --> combines the above

    See: Walker 2005, Section 1.4 for the additive vs multiplicative treatment
    of context combination in substructural type systems.
    ============================================================================ *)

(** Helper lemma: mode_join preserves restriction when inputs are restricted.

    PROOF: By case analysis on m1 and m2, each in {MZero, MOne}.
    mode_join MZero MZero = MZero (restricted)
    mode_join MZero MOne  = MOne  (restricted)
    mode_join MOne  MZero = MOne  (restricted)
    mode_join MOne  MOne  = MOne  (restricted) -- KEY: NOT MOmega! *)
val mode_join_preserves_restricted : m1:mode -> m2:mode ->
  Lemma (requires is_restricted_mode m1 = true /\ is_restricted_mode m2 = true)
        (ensures is_restricted_mode (mode_join m1 m2) = true)

(** T-2.6: Context join preserves validity under linear exclusivity.

    CRITICAL PRECONDITION: linear_exclusive ctx1 ctx2 ensures that for
    any variable x with EMLinear, at most one context has mode MOne.

    This precondition is automatically satisfied when ctx1, ctx2 come from
    split_ctx (see T-2.4). For general contexts, it must be explicitly verified. *)
val join_preserves_valid_theorem : ctx1:mode_ctx -> ctx2:mode_ctx ->
  Lemma (requires valid_mode_ctx ctx1 = true /\
                  valid_mode_ctx ctx2 = true /\
                  linear_exclusive ctx1 ctx2 = true)
        (ensures valid_mode_ctx (join_ctx ctx1 ctx2) = true)

(** Corollary: Split then join roundtrip preserves validity.

    This is the composition of T-2.4 and T-2.6:
    1. split_ctx produces linearly exclusive contexts (T-2.4)
    2. split_preserves_valid ensures both halves are valid
    3. join_preserves_valid_theorem applies with linear_exclusive guaranteed

    This validates the L-App rule's context management. *)
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
