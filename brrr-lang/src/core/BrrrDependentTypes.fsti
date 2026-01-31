(**
 * BrrrDependentTypes.fsti - Interface for Dependent Type System
 *
 * Based on brrr_lang_spec_v0.4.tex Part IV - Dependent Types (Section 3.4).
 * Interface design follows HACL* patterns (Lib.IntTypes.fsti, Lib.Sequence.fsti).
 *
 * =============================================================================
 * THEORETICAL FOUNDATIONS
 * =============================================================================
 *
 * This module implements a dependent type system rooted in Martin-Lof Type
 * Theory (MLTT), the foundational framework for modern proof assistants like
 * Coq, Agda, and F*. Key references:
 *
 *   - Per Martin-Lof, "Intuitionistic Type Theory" (1984)
 *   - Bengt Nordstrom et al., "Programming in Martin-Lof's Type Theory" (1990)
 *   - Benjamin Pierce, "Types and Programming Languages" (2002), Ch. 29-30
 *   - F* Book, "Proof-oriented Programming in F*" - Part 2 (Inductive Types)
 *
 * The type constructors map to MLTT as follows:
 *
 *   Brrr-Lang         MLTT                Category Theory
 *   ---------         ----                ---------------
 *   DPi x:A.B         Pi(x:A).B           Dependent product (right adjoint)
 *   DSigma x:A.B      Sigma(x:A).B        Dependent sum (left adjoint)
 *   DRefinement       {x:A | P(x)}        Subobject classifier pullback
 *
 * =============================================================================
 * IMPLEMENTS
 * =============================================================================
 *
 *   - Pi-types:       Pi(x:t1).t2    (dependent function types)
 *   - Sigma-types:    Sigma(x:t1).t2 (dependent pair types)
 *   - Refinement:     {x: t | phi(x)} (types refined by predicates)
 *
 * =============================================================================
 * KEY OPERATIONS
 * =============================================================================
 *
 *   - Type substitution: [e/x]t (replace x with e in t)
 *   - Alpha-equivalence: types equal up to bound variable renaming
 *   - Refinement subtyping: {x:t|phi} <: {x:t|psi} iff forall x. phi => psi
 *
 * =============================================================================
 * SMT ENCODING NOTES (See FSTAR_REFERENCE.md Section 6)
 * =============================================================================
 *
 * When dependent types are encoded for SMT solving:
 *
 * 1. REFINEMENT TYPES are encoded as guarded assertions:
 *      {x:T | phi(x)} --> T with assertion phi(x)
 *    The refinement predicate becomes an SMT assumption or proof obligation.
 *
 * 2. PI-TYPES are encoded with function symbols and axioms:
 *      Pi(x:A).B --> forall (x:A). f(x) : B[x]
 *    The dependency is captured via SMT quantifiers with triggers.
 *
 * 3. SIGMA-TYPES are encoded as uninterpreted pairs with projection axioms:
 *      Sigma(x:A).B --> (a:A, b:B[a]) with fst/snd accessors
 *
 * 4. FORMULA IMPLICATION (for subtyping) uses Z3's quantifier reasoning:
 *      {x:T|phi} <: {x:T|psi} --> (assert (forall x. phi(x) ==> psi(x)))
 *
 * Key SMT patterns for efficient instantiation:
 *   - Use [SMTPat (f x)] on lemmas about substitution
 *   - Fuel control: --fuel 0 --ifuel 0 for decidable checks
 *   - Z3rlimit: typically 50-100 for dependent type proofs
 *
 * =============================================================================
 * SPECIFICATION ERRATA (See SPECIFICATION_ERRATA.md)
 * =============================================================================
 *
 * Chapter 3 notes that alpha-equivalence requires normalization-based
 * comparison rather than structural equality. The `dep_type_alpha_eq` function
 * implements the corrected definition: e1 ~= e2 iff normalize(e1) = normalize(e2).
 *)
module BrrrDependentTypes

open FStar.List.Tot
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions

(** Z3 solver options - conservative baseline for dependent type proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* =========================================================================
   SECTION 1: DEPENDENT TYPE VARIABLES AND FRESH NAMES
   ========================================================================= *)

(** Variable identifier for dependent types *)
type dep_var = string

(** Fresh variable counter for alpha-renaming *)
type fresh_counter = nat

(** Generate fresh variable name with prefix and counter *)
val fresh_var : prefix:string -> counter:fresh_counter -> dep_var

(* =========================================================================
   SECTION 2: COMPARISON OPERATORS
   ========================================================================= *)

(** Comparison operator for formulas *)
type cmp_op =
  | CmpEq  : cmp_op   (* = *)
  | CmpNe  : cmp_op   (* != *)
  | CmpLt  : cmp_op   (* < *)
  | CmpLe  : cmp_op   (* <= *)
  | CmpGt  : cmp_op   (* > *)
  | CmpGe  : cmp_op   (* >= *)

(* =========================================================================
   SECTION 3: FORMULAS (REFINEMENT PREDICATES)
   =========================================================================

   Formulas represent logical assertions over terms. They are used in:
   - Refinement types: {x: t | phi(x)}
   - Pre/postconditions: requires P, ensures Q
   - Loop invariants: while c invariant I { ... }

   Grammar:
     phi ::= true | false
          | e1 = e2 | e1 < e2 | e1 <= e2
          | phi1 /\ phi2 | phi1 \/ phi2 | ~phi
          | forall x:t. phi | exists x:t. phi
          | phi(e)          (formula application)

   THEORETICAL BACKGROUND (Refinement Types):

   Refinement types were introduced by Freeman and Pfenning (1991) and
   independently by Xi and Pfenning (1999). The key insight is that types
   can be refined with logical predicates to express more precise properties.

   Example from F* book (fstar_pop_book.md, lines 393-404):
     let rec get #a #n (i:nat{i < n}) (v:vec a n) : a = ...

   Here {i : nat | i < n} is a refinement type constraining i to be a valid
   index for a vector of length n.

   SMT ENCODING:

   When type checking:
     x : {v:T | phi(v)} and e has type T

   The SMT solver checks:
     (assert (forall v. (has_type v T) ==> (phi(v) ==> phi(e))))

   This uses Z3's E-matching with triggers [SMTPat (has_type v T)].
   See FSTAR_REFERENCE.md Section 6 for the full encoding scheme.
   ========================================================================= *)

(** Logical formula - assertions over terms *)
noeq type formula =
  (* Boolean constants *)
  | FTrue    : formula
  | FFalse   : formula

  (* Comparisons on expressions *)
  | FCmp     : cmp_op -> expr -> expr -> formula

  (* Propositional connectives *)
  | FAnd     : formula -> formula -> formula
  | FOr      : formula -> formula -> formula
  | FNot     : formula -> formula
  | FImpl    : formula -> formula -> formula   (* phi => psi *)
  | FIff     : formula -> formula -> formula   (* phi <=> psi *)

  (* Quantifiers - bind variable with type *)
  | FForall  : dep_var -> brrr_type -> formula -> formula
  | FExists  : dep_var -> brrr_type -> formula -> formula

  (* Predicate variable with argument *)
  | FPred    : string -> expr -> formula

  (* Expression coerced to formula (for boolean expressions) *)
  | FExpr    : expr -> formula

(* =========================================================================
   SECTION 4: DEPENDENT TYPE CONSTRUCTORS
   =========================================================================

   dep_type extends the core brrr_type with dependent types:

   1. DPi(x:t1).t2 - Dependent function type (generalized arrow type)
      When x does not occur in t2, this is equivalent to t1 -> t2

   2. DSigma(x:t1).t2 - Dependent pair type (generalized product type)
      When x does not occur in t2, this is equivalent to t1 * t2

   3. DRefinement{x:t | phi} - Refinement type
      Values of type t that satisfy predicate phi

   ---------------------------------------------------------------------------
   MARTIN-LOF TYPE THEORY CORRESPONDENCE
   ---------------------------------------------------------------------------

   DPi corresponds to MLTT's Pi-type (dependent product):

     Pi-FORMATION:
       Gamma |- A : Type    Gamma, x:A |- B : Type
       -------------------------------------------
               Gamma |- Pi(x:A).B : Type

     Pi-INTRO:
       Gamma, x:A |- e : B
       ---------------------
       Gamma |- \x.e : Pi(x:A).B

     Pi-ELIM:
       Gamma |- f : Pi(x:A).B    Gamma |- a : A
       ----------------------------------------
              Gamma |- f(a) : B[a/x]

   DSigma corresponds to MLTT's Sigma-type (dependent sum):

     Sigma-FORMATION:
       Gamma |- A : Type    Gamma, x:A |- B : Type
       -------------------------------------------
              Gamma |- Sigma(x:A).B : Type

     Sigma-INTRO:
       Gamma |- a : A    Gamma |- b : B[a/x]
       -------------------------------------
          Gamma |- (a, b) : Sigma(x:A).B

     Sigma-ELIM (fst/snd):
       Gamma |- p : Sigma(x:A).B
       -------------------------
       Gamma |- fst(p) : A

       Gamma |- p : Sigma(x:A).B
       -------------------------
       Gamma |- snd(p) : B[fst(p)/x]

   Reference: "Intuitionistic Type Theory" (Martin-Lof, 1984), pp. 35-50

   ---------------------------------------------------------------------------
   BRRR-LANG SPEC REFERENCE (brrr_lang_spec_v0.4.tex Section 3.4)
   ---------------------------------------------------------------------------

   The specification defines dependent types via the judgment:
     Delta; Gamma |- T : Kind

   Where Delta is a kind context and Gamma is a type context. Our dep_type
   corresponds to types with Kind = Type_0 (the base universe).

   The spec notes that type equality (Section 3.4.2) must account for
   substitution and alpha-equivalence - hence our normalize/alpha_eq machinery.
   ========================================================================= *)

(** Dependent type - extends base types with Pi, Sigma, Refinement *)
noeq type dep_type =
  (* Lift base types *)
  | DBase      : brrr_type -> dep_type

  (* Pi-type: dependent function *)
  | DPi        : dep_var -> dep_type -> dep_type -> dep_type

  (* Sigma-type: dependent pair *)
  | DSigma     : dep_var -> dep_type -> dep_type -> dep_type

  (* Refinement type: {x:t | phi} *)
  | DRefinement : dep_var -> dep_type -> formula -> dep_type

  (* Type application (for higher-kinded dependent types) *)
  | DApp       : dep_type -> expr -> dep_type

(* =========================================================================
   SECTION 5: SIZE METRICS (For Termination Proofs)
   ========================================================================= *)

(** Compute size of a formula (for termination proofs) *)
val formula_size : phi:formula -> Tot nat (decreases phi)

(** Compute size of a dependent type (for termination proofs) *)
val dep_type_size : t:dep_type -> Tot nat (decreases t)

(* =========================================================================
   SECTION 6: FREE AND BOUND VARIABLES
   ========================================================================= *)

(** Free variables in a formula *)
val formula_free_vars : phi:formula -> Tot (list dep_var) (decreases phi)

(** Free variables in a dependent type *)
val dep_type_free_vars : t:dep_type -> Tot (list dep_var) (decreases t)

(** Bound variables in a formula *)
val formula_bound_vars : phi:formula -> Tot (list dep_var) (decreases phi)

(** Bound variables in a dependent type *)
val dep_type_bound_vars : t:dep_type -> Tot (list dep_var) (decreases t)

(** Check if variable is free in dependent type *)
val is_free_in_dep_type : x:dep_var -> t:dep_type -> bool

(** Check if variable is free in formula *)
val is_free_in_formula : x:dep_var -> phi:formula -> bool

(** Check if variable is free in expression *)
val is_free_in_expr : x:dep_var -> e:expr -> bool

(* =========================================================================
   SECTION 7: CAPTURE-AVOIDING SUBSTITUTION
   =========================================================================

   Variable capture occurs when substituting [e/x] under a binder that binds
   a variable y that is free in e. For example:

     [y/x](forall y. x + y)  -- WRONG: gives (forall y. y + y) capturing y

   To avoid this, we alpha-rename the bound variable before substitution:

     [y/x](forall z. x + z)  -- CORRECT after renaming y to z
   ========================================================================= *)

(** Generate fresh variable avoiding capture *)
val generate_capture_fresh : base:string -> counter:nat -> avoid:list dep_var ->
    Tot dep_var (decreases 1000 - counter)

(** Collect variables to avoid during substitution *)
val capture_avoid_vars : replacement:expr -> body_fvs:list dep_var -> list dep_var

(** Substitute expression for variable in expression (capture-avoiding) *)
val subst_expr : x:dep_var -> replacement:expr -> e:expr ->
    Tot expr (decreases %[expr_size e; 0])

(** Substitute expression for variable in expression list *)
val subst_expr_list : x:dep_var -> replacement:expr -> es:list expr ->
    Tot (list expr) (decreases %[expr_list_size es; 1])

(** Substitute expression for variable in field list *)
val subst_expr_fields : x:dep_var -> replacement:expr -> fields:list (string & expr) ->
    Tot (list (string & expr)) (decreases %[field_expr_list_size fields; 2])

(** Substitute expression for variable in formula (capture-avoiding) *)
val subst_formula : x:dep_var -> replacement:expr -> phi:formula ->
    Tot formula (decreases phi)

(** Substitute expression for variable in dependent type (capture-avoiding)
    [e/x]T - replace all free occurrences of x in T with e *)
val subst_dep_type : x:dep_var -> replacement:expr -> t:dep_type ->
    Tot dep_type (decreases t)

(* =========================================================================
   SECTION 8: ALPHA-RENAMING
   ========================================================================= *)

(** Rename bound variable in formula *)
val alpha_rename_formula : old_var:dep_var -> new_var:dep_var -> phi:formula ->
    Tot formula (decreases phi)

(** Rename bound variable in dependent type *)
val alpha_rename_dep_type : old_var:dep_var -> new_var:dep_var -> t:dep_type ->
    Tot dep_type (decreases t)

(** Find fresh variable not in avoid list *)
val find_fresh_var : prefix:string -> counter:nat -> avoid:list dep_var ->
    Tot dep_var (decreases 1000 - counter)

(** Normalize formula with fresh bound variable names *)
val normalize_formula : phi:formula -> counter:fresh_counter -> avoid:list dep_var ->
    (formula & fresh_counter)

(** Normalize dependent type with fresh bound variable names *)
val normalize_dep_type : t:dep_type -> counter:fresh_counter -> avoid:list dep_var ->
    (dep_type & fresh_counter)

(* =========================================================================
   SECTION 9: EQUALITY PREDICATES
   ========================================================================= *)

(** Structural equality for formulas *)
val formula_eq : phi1:formula -> phi2:formula -> Tot bool (decreases phi1)

(** Structural equality for dependent types (not alpha-equivalence) *)
val dep_type_eq_structural : t1:dep_type -> t2:dep_type -> Tot bool (decreases t1)

(** Alpha-equivalence for dependent types (equality up to bound variable renaming) *)
val dep_type_alpha_eq : t1:dep_type -> t2:dep_type -> bool

(* =========================================================================
   SECTION 10: FORMULA IMPLICATION AND SUBTYPING
   =========================================================================

   Subtyping rules:

   1. DBase: delegate to base type subtyping

   2. DPi: contravariant in domain, covariant in codomain
      Pi(x:S1).T1 <: Pi(x:S2).T2  iff  S2 <: S1 and T1 <: T2

   3. DSigma: covariant in both components
      Sigma(x:S1).T1 <: Sigma(x:S2).T2  iff  S1 <: S2 and T1 <: T2

   4. DRefinement: phi1 => phi2 (logically)
      {x:T | phi1} <: {x:T | phi2}  iff  forall x:T. phi1(x) => phi2(x)
   ========================================================================= *)

(** Conservative formula implication check.
    Returns true only when syntactically phi1 => phi2.
    Returns false conservatively when unsure.

    SYNTACTIC ONLY - Does NOT handle:
    - Arithmetic: (x > 0) does NOT imply (x >= 0) syntactically
    - Quantifiers: (forall x. P(x)) does NOT imply P(y) syntactically
    - Transitive: (x < y /\ y < z) does NOT imply (x < z) syntactically

    For semantic checking, use SMT module's formula_implies_hybrid which
    first tries syntactic (fast) then falls back to Z3.

    Reference: fstar_pop_book.md, lines 500-530 (SMT solving overview)
    Reference: FSTAR_REFERENCE.md Section 6 (SMT Encoding) *)
val formula_implies : phi1:formula -> phi2:formula ->
    Tot bool (decreases (formula_size phi1 + formula_size phi2))

(** Dependent type subtyping with proper substitution handling

    SUBTYPING RULES (TAPL Chapter 15, 30):

    DBase:       delegate to BrrrTypes.subtype
    DPi:         CONTRAVARIANT domain, COVARIANT codomain
                 Pi(x:S1).T1 <: Pi(x:S2).T2  iff  S2 <: S1 and T1 <: T2
    DSigma:      COVARIANT in both components
                 Sigma(x:S1).T1 <: Sigma(x:S2).T2  iff  S1 <: S2 and T1 <: T2
    DRefinement: FORMULA IMPLICATION
                 {x:T|phi1} <: {x:T|phi2}  iff  (forall x. phi1 ==> phi2)

    The substitution [x2/x1] aligns bound variables for proper comparison.

    SMT ENCODING: Subtyping becomes validity query:
      t1 <: t2  iff  SMT proves (forall x. HasType(x,t1) ==> HasType(x,t2))

    Reference: hacl-star/lib/ uses refinement subtyping extensively *)
val dep_type_subtype : t1:dep_type -> t2:dep_type ->
    Tot bool (decreases (dep_type_size t1 + dep_type_size t2))

(* =========================================================================
   SECTION 11: SIZE PRESERVATION LEMMAS
   ========================================================================= *)

(** Substitution preserves formula size *)
val subst_formula_preserves_size : x:dep_var -> e:expr -> phi:formula ->
    Lemma (ensures formula_size (subst_formula x e phi) = formula_size phi)
          (decreases phi)

(** Substitution preserves dependent type size *)
val subst_dep_type_preserves_size : x:dep_var -> e:expr -> t:dep_type ->
    Lemma (ensures dep_type_size (subst_dep_type x e t) = dep_type_size t)
          (decreases t)
    [SMTPat (subst_dep_type x e t)]

(** Variable substitution preserves formula size *)
val subst_formula_var_size : x:dep_var -> y:dep_var -> phi:formula ->
    Lemma (ensures formula_size (subst_formula x (EVar y) phi) = formula_size phi)
          (decreases phi)

(* =========================================================================
   SECTION 12: STRUCTURAL EQUALITY LEMMAS
   ========================================================================= *)

(** Structural equality is reflexive for formulas *)
val formula_eq_refl : phi:formula ->
    Lemma (ensures formula_eq phi phi = true) (decreases phi)
    [SMTPat (formula_eq phi phi)]

(** Structural equality is reflexive for dependent types *)
val dep_type_eq_structural_refl : t:dep_type ->
    Lemma (ensures dep_type_eq_structural t t = true) (decreases t)
    [SMTPat (dep_type_eq_structural t t)]

(** Structural equality is symmetric for formulas *)
val formula_eq_sym : phi1:formula -> phi2:formula ->
    Lemma (requires formula_eq phi1 phi2 = true)
          (ensures formula_eq phi2 phi1 = true)
          (decreases phi1)

(** Structural equality is symmetric for dependent types *)
val dep_type_eq_structural_sym : t1:dep_type -> t2:dep_type ->
    Lemma (requires dep_type_eq_structural t1 t2 = true)
          (ensures dep_type_eq_structural t2 t1 = true)
          (decreases t1)

(** Structural equality is transitive for formulas *)
val formula_eq_trans : phi1:formula -> phi2:formula -> phi3:formula ->
    Lemma (requires formula_eq phi1 phi2 = true /\ formula_eq phi2 phi3 = true)
          (ensures formula_eq phi1 phi3 = true)
          (decreases phi1)

(** Structural equality is transitive for dependent types *)
val dep_type_eq_structural_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
    Lemma (requires dep_type_eq_structural t1 t2 = true /\ dep_type_eq_structural t2 t3 = true)
          (ensures dep_type_eq_structural t1 t3 = true)
          (decreases t1)

(* =========================================================================
   SECTION 13: ALPHA-EQUIVALENCE LEMMAS
   ========================================================================= *)

(** Alpha-equivalence is reflexive *)
val dep_type_alpha_eq_refl : t:dep_type ->
    Lemma (ensures dep_type_alpha_eq t t = true)
    [SMTPat (dep_type_alpha_eq t t)]

(** Alpha-equivalence is symmetric *)
val dep_type_alpha_eq_sym : t1:dep_type -> t2:dep_type ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true)
          (ensures dep_type_alpha_eq t2 t1 = true)
    [SMTPat (dep_type_alpha_eq t1 t2)]

(** Alpha-equivalence is transitive *)
val dep_type_alpha_eq_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true /\ dep_type_alpha_eq t2 t3 = true)
          (ensures dep_type_alpha_eq t1 t3 = true)

(** Alpha-equivalence respects substitution *)
val alpha_eq_subst_compat : t1:dep_type -> t2:dep_type -> x:dep_var -> e:expr ->
    Lemma (requires dep_type_alpha_eq t1 t2 = true)
          (ensures dep_type_alpha_eq (subst_dep_type x e t1) (subst_dep_type x e t2) = true)
    [SMTPat (subst_dep_type x e t1); SMTPat (subst_dep_type x e t2)]

(* =========================================================================
   SECTION 14: SUBTYPING LEMMAS
   ========================================================================= *)

(** Formula implication is reflexive *)
val formula_implies_refl : phi:formula ->
    Lemma (ensures formula_implies phi phi = true)
    [SMTPat (formula_implies phi phi)]

(** Subtyping is reflexive *)
val dep_type_subtype_refl : t:dep_type ->
    Lemma (ensures dep_type_subtype t t = true) (decreases t)
    [SMTPat (dep_type_subtype t t)]

(** Subtyping is transitive *)
val dep_type_subtype_trans : t1:dep_type -> t2:dep_type -> t3:dep_type ->
    Lemma (requires dep_type_subtype t1 t2 = true /\ dep_type_subtype t2 t3 = true)
          (ensures dep_type_subtype t1 t3 = true)
          (decreases (dep_type_size t1 + dep_type_size t2 + dep_type_size t3))
    [SMTPat (dep_type_subtype t1 t3)]

(* =========================================================================
   SECTION 15: SUBSTITUTION COMMUTATION LEMMAS
   ========================================================================= *)

(** Substitution with non-free variable preserves formula *)
val subst_var_free_vars : x:dep_var -> y:dep_var -> phi:formula ->
    Lemma (ensures
      (not (is_free_in_formula x phi)) ==>
      formula_eq (subst_formula x (EVar y) phi) phi = true)
          (decreases phi)

(** Substitutions commute when variables don't interfere *)
val subst_commutes_formula : x:dep_var -> y:dep_var -> e1:expr -> e2:expr -> phi:formula ->
    Lemma
      (requires x <> y /\ not (is_free_in_expr y e1) /\ not (is_free_in_expr x e2))
      (ensures
        formula_eq
          (subst_formula y e2 (subst_formula x e1 phi))
          (subst_formula x e1 (subst_formula y e2 phi)) = true)
      (decreases phi)

(** Substitution composition for formulas:
    [e2/y][e1/x]phi = [[e2/y]e1/x][e2/y]phi when x <> y and x not free in e2 *)
val subst_composition_formula : x:dep_var -> y:dep_var{x <> y} ->
    e1:expr -> e2:expr -> phi:formula ->
    Lemma (requires not (is_free_in_expr x e2))
          (ensures formula_eq
            (subst_formula y e2 (subst_formula x e1 phi))
            (subst_formula x (subst_expr y e2 e1) (subst_formula y e2 phi)) = true)
          (decreases phi)

(** Substitution composition for dependent types:
    [e2/y][e1/x]t = [[e2/y]e1/x][e2/y]t when x <> y and x not free in e2 *)
val subst_composition : x:dep_var -> y:dep_var{x <> y} ->
    e1:expr -> e2:expr -> t:dep_type ->
    Lemma (requires not (is_free_in_expr x e2))
          (ensures dep_type_eq_structural
            (subst_dep_type y e2 (subst_dep_type x e1 t))
            (subst_dep_type x (subst_expr y e2 e1) (subst_dep_type y e2 t)) = true)
          (decreases t)
    [SMTPat (subst_dep_type y e2 (subst_dep_type x e1 t))]

(** Substituting variable for itself is identity *)
val subst_identity : x:dep_var -> t:dep_type ->
    Lemma (ensures dep_type_eq_structural (subst_dep_type x (EVar x) t) t = true)
          (decreases t)
    [SMTPat (subst_dep_type x (EVar x) t)]

(** Free variable preservation under substitution *)
val subst_preserves_non_free : x:dep_var -> e:expr -> y:dep_var -> t:dep_type ->
    Lemma (requires y <> x /\ not (is_free_in_expr y e))
          (ensures is_free_in_dep_type y (subst_dep_type x e t) = is_free_in_dep_type y t)
          (decreases t)

(* =========================================================================
   SECTION 16: NORMALIZATION LEMMAS
   ========================================================================= *)

(** Normalization produces an alpha-equivalent type *)
val normalize_sound : t:dep_type -> counter:fresh_counter -> avoid:list dep_var ->
    Lemma (let (t', _) = normalize_dep_type t counter avoid in
           dep_type_alpha_eq t t' = true)

(** Normalization is idempotent *)
val normalize_idempotent : t:dep_type -> counter:fresh_counter -> avoid:list dep_var ->
    Lemma (let (t1, c1) = normalize_dep_type t counter avoid in
           let (t2, _) = normalize_dep_type t1 c1 avoid in
           dep_type_eq_structural t1 t2 = true)

(* =========================================================================
   SECTION 17: TYPE CONTEXT AND WELL-FORMEDNESS
   ========================================================================= *)

(** Type context: maps term variables to their dependent types *)
type dep_type_ctx = list (dep_var & dep_type)

(** Look up a variable in the context *)
val ctx_lookup : x:dep_var -> ctx:dep_type_ctx -> option dep_type

(** Check if a variable is bound in the context *)
val ctx_contains : x:dep_var -> ctx:dep_type_ctx -> bool

(** Extend context with a new binding *)
val ctx_extend : x:dep_var -> t:dep_type -> ctx:dep_type_ctx -> dep_type_ctx

(** Check if all free variables in expression are bound in context *)
val expr_vars_in_ctx : e:expr -> ctx:dep_type_ctx -> Tot bool (decreases %[expr_size e; 0])

(** Check if formula is well-formed in context *)
val formula_well_formed_in_ctx : phi:formula -> ctx:dep_type_ctx -> Tot bool (decreases phi)

(** Check if dependent type is well-formed in context *)
val well_formed_in_ctx : t:dep_type -> ctx:dep_type_ctx -> Tot bool (decreases t)

(** Substitution preserves well-formedness *)
val subst_preserves_well_formed : x:dep_var -> e:expr -> t:dep_type -> ctx:dep_type_ctx ->
    Lemma
      (requires
        well_formed_in_ctx t (ctx_extend x (DBase t_dynamic) ctx) /\
        expr_vars_in_ctx e ctx)
      (ensures well_formed_in_ctx (subst_dep_type x e t) ctx)
      (decreases t)

(* =========================================================================
   SECTION 18: TYPE CONSTRUCTORS (Convenience Functions)
   ========================================================================= *)

(** Create a simple (non-dependent) function type: t1 -> t2 *)
val d_arrow : t1:dep_type -> t2:dep_type -> dep_type

(** Create a simple (non-dependent) pair type: t1 * t2 *)
val d_pair : t1:dep_type -> t2:dep_type -> dep_type

(** Lift a base type to dependent type *)
val d_base : bt:brrr_type -> dep_type

(** Natural numbers: {n: Int | n >= 0}
    Corresponds to F*'s Prims.nat = x:int{x >= 0}
    Reference: fstar_pop_book.md, lines 3330-3340 *)
val d_nat : dep_type

(** Positive integers: {n: Int | n > 0}
    Corresponds to F*'s Prims.pos = x:int{x > 0}
    Used for array indices, divisors, loop bounds *)
val d_pos : dep_type

(** Bounded integers: {n: Int | lo <= n < hi}
    Encodes machine integer types with overflow checking:
      u8  = d_bounded 0 256
      i8  = d_bounded (-128) 128
      u16 = d_bounded 0 65536
    Reference: hacl-star/lib/Lib.IntTypes.fsti *)
val d_bounded : lo:int -> hi:int -> dep_type

(** Array with length refinement
    Corresponds to HACL* Lib.Sequence.lseq:
      let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}
    Reference: hacl-star/lib/Lib.Sequence.fsti, lines 24-27

    Enables compile-time bounds checking:
      index : s:lseq a len -> i:nat{i < len} -> a
    No runtime bounds check needed - SMT proves i < len statically *)
val d_array_len : elem_ty:brrr_type -> len_var:dep_var -> dep_type

(** Vector type: dependent array with length as type parameter
    Classic indexed type from type theory - see fstar_pop_book.md lines 360-404

    Example usage:
      append : vec a n -> vec a m -> vec a (n + m)
      reverse : vec a n -> vec a n
      get : i:nat{i < n} -> vec a n -> a

    SMT encodes length constraints as guards on HasType predicates *)
val d_vec : elem_ty:brrr_type -> len:expr -> dep_type

(* =========================================================================
   SECTION 19: DEPENDENT TYPE OPERATIONS
   ========================================================================= *)

(** Application result type for Pi-types:
    For f : Pi(x:A).B and argument a : A, f(a) has type [a/x]B

    MLTT Pi-ELIMINATION RULE (Martin-Lof 1984, p. 38):
      Gamma |- f : Pi(x:A).B    Gamma |- a : A
      ----------------------------------------
             Gamma |- f(a) : B[a/x]

    This is the defining characteristic of dependent types: the output type
    depends on the input VALUE, not just the input TYPE.

    EXAMPLE (fstar_pop_book.md, lines 370-378):
      If append : #n:nat -> #m:nat -> vec a n -> vec a m -> vec a (n+m)
      Then append v1 v2 where v1:vec a 3, v2:vec a 5 has type vec a 8

    SMT: Triggers quantifier instantiation - see FSTAR_REFERENCE.md Section 6
*)
val app_result_type : fn_type:dep_type -> arg:expr -> option dep_type

(** First projection type for Sigma-types *)
val fst_type : pair_type:dep_type -> option dep_type

(** Second projection type for Sigma-types:
    For p : Sigma(x:A).B, snd(p) has type [fst(p)/x]B *)
val snd_type : pair_type:dep_type -> pair_expr:expr -> option dep_type

(** Extract base type from refinement *)
val refinement_base : t:dep_type -> option dep_type

(** Extract predicate from refinement *)
val refinement_pred : t:dep_type -> option formula

(** Strengthen a refinement: {x:T|phi} -> {x:T|phi /\ psi} *)
val strengthen_refinement : t:dep_type -> extra:formula -> dep_type

(** Weaken a refinement: replace predicate with weaker one *)
val weaken_refinement : t:dep_type -> weaker:formula -> dep_type

(* =========================================================================
   SECTION 20: FORMULA SIMPLIFICATION
   ========================================================================= *)

(** Basic formula simplification (boolean algebra) *)
val simplify_formula : phi:formula -> Tot formula (decreases phi)

(* =========================================================================
   SECTION 21: PRETTY PRINTING
   ========================================================================= *)

(** Convert formula to string representation *)
val formula_to_string : phi:formula -> Tot string

(** Convert dependent type to string representation *)
val dep_type_to_string : t:dep_type -> Tot string
