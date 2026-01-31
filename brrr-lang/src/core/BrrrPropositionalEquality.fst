(**
 * BrrrLang.Core.PropositionalEquality
 *
 * =============================================================================
 * IMPLEMENTATION OF PROPOSITIONAL EQUALITY (IDENTITY TYPES)
 * =============================================================================
 *
 * This module implements the foundational theory of propositional equality
 * for Brrr-Lang. It directly addresses specification gaps:
 *
 *   Gap #4: Equality types MISSING - no propositional equality
 *   Gap #5: Universe levels MISSING - no stratification
 *
 * THEORETICAL BACKGROUND
 * ----------------------
 * The identity type, introduced by Per Martin-Lof (1973), is the canonical
 * way to express equality in dependent type theory. Unlike boolean equality,
 * which merely tests if two values are the same, the identity type produces
 * PROOF OBJECTS that witness the equality.
 *
 * In F*, we have three notions of equality:
 *
 *   1. DEFINITIONAL EQUALITY (implicit)
 *      Two terms that reduce to the same normal form.
 *      Example: (fun x -> x) 5 is definitionally equal to 5.
 *      This happens automatically in the type checker.
 *
 *   2. BOOLEAN EQUALITY (=)
 *      A decidable test returning true/false.
 *      Only available for eqtype (types with decidable equality).
 *      Example: (5 = 5) returns true : bool
 *
 *   3. PROPOSITIONAL EQUALITY (==) / eq_type
 *      A type whose inhabitants are equality proofs.
 *      Available for ALL types.
 *      Example: Refl : eq_type int 5 5
 *
 * F* EXTENSIONALITY
 * -----------------
 * F* is an EXTENSIONAL type theory, meaning:
 *   - Propositional equality implies definitional equality
 *   - All equality proofs are equal (UIP - Uniqueness of Identity Proofs)
 *   - Axiom K holds: every p : x = x is equal to Refl
 *
 * This contrasts with INTENSIONAL type theories (Coq, Agda, Lean) where
 * propositional and definitional equality are kept separate.
 *
 * The extensional approach simplifies proofs but makes type checking
 * potentially undecidable in edge cases.
 *
 * FUNCTIONAL EXTENSIONALITY WARNING
 * ---------------------------------
 * Full functional extensionality is NOT valid in F*:
 *
 *   INVALID: (forall x. f x == g x) ==> f == g
 *
 * This is because f and g might have different domains. For example:
 *   f : nat -> int  and  g : nat -> int
 *   might be equal on positive numbers but differ at 0.
 *
 * VALID (for eta-expanded functions):
 *   (fun x -> f x) == (fun x -> g x)  when pointwise equal
 *
 * Use FStar.FunctionalExtensionality for safe extensionality.
 *
 * MODULE STRUCTURE
 * ----------------
 * 1. Universe levels - proper transfinite ordinal representation
 * 2. Identity type (eq_type) - the core equality type
 * 3. Core operations - refl, subst, transport
 * 4. Derived operations - sym, trans, cong
 * 5. Equality lemmas - SMT-friendly formulations
 * 6. J-eliminator - general induction on equality proofs
 * 7. Heterogeneous equality - across different types
 * 8. UIP proofs - demonstrating F*'s extensional nature
 * 9. Decidable equality - typeclass for computational equality
 * 10. Leibniz equality - alternative characterization
 * 11. Path types - HoTT-style vocabulary
 * 12. Axiom K - enabling pattern matching on equality
 *
 * REFERENCES
 * ----------
 * [1] Martin-Lof, P. (1984). "Intuitionistic Type Theory"
 * [2] Streicher, T. (1993). "Investigations into Intensional Type Theory"
 * [3] HoTT Book (2013). "Homotopy Type Theory: Univalent Foundations"
 * [4] F* Tutorial and Reference Manual
 *
 * Depends on: Primitives, BrrrTypes
 *)
module BrrrPropositionalEquality

(** Z3 solver options - conservative baseline for equality proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes

(** ============================================================================
    UNIVERSE LEVELS
    ============================================================================

    To avoid Russell's paradox, types must be stratified into universes:
      Type0 : Type1 : Type2 : ...

    In F*, Type0 is the type of small types (not containing Type itself).
    For Brrr-Lang, we define explicit universe levels for user-facing types.

    We use a proper sum type to distinguish between:
    - Finite levels (0, 1, 2, ...) - concrete universe indices
    - Omega (w) - the limit ordinal, used for universe polymorphism
    - Omega+n - levels above omega (rarely needed)

    This avoids the hack of using a large finite number for omega.
    ============================================================================ *)

(** Universe level representation - properly handles omega *)
type universe_level =
  | UFinite : nat -> universe_level           (* Finite level: 0, 1, 2, ... *)
  | UOmega  : universe_level                  (* Limit ordinal omega *)
  | UOmegaPlus : nat -> universe_level        (* omega + n for n > 0 *)

(* Universe stratification constants *)
let level_zero : universe_level = UFinite 0       (* Type0 - small types *)
let level_one : universe_level = UFinite 1        (* Type1 - types of Type0 *)
let level_omega : universe_level = UOmega         (* Proper omega, not a hack! *)

(** Maximum of two levels - properly handles omega *)
let level_max (l1 l2: universe_level) : universe_level =
  match l1, l2 with
  | UFinite n1, UFinite n2 -> UFinite (if n1 >= n2 then n1 else n2)
  | UFinite _, UOmega -> UOmega
  | UOmega, UFinite _ -> UOmega
  | UOmega, UOmega -> UOmega
  | UFinite _, UOmegaPlus n -> UOmegaPlus n
  | UOmegaPlus n, UFinite _ -> UOmegaPlus n
  | UOmega, UOmegaPlus n -> UOmegaPlus n
  | UOmegaPlus n, UOmega -> UOmegaPlus n
  | UOmegaPlus n1, UOmegaPlus n2 -> UOmegaPlus (if n1 >= n2 then n1 else n2)

(** Successor level - properly handles omega *)
let level_succ (l: universe_level) : universe_level =
  match l with
  | UFinite n -> UFinite (n + 1)
  | UOmega -> UOmegaPlus 1           (* succ(omega) = omega + 1 *)
  | UOmegaPlus n -> UOmegaPlus (n + 1)

(** Universe level ordering - l1 <= l2 *)
let level_leq (l1 l2: universe_level) : bool =
  match l1, l2 with
  | UFinite n1, UFinite n2 -> n1 <= n2
  | UFinite _, UOmega -> true        (* n < omega for all finite n *)
  | UFinite _, UOmegaPlus _ -> true
  | UOmega, UFinite _ -> false       (* omega > n for all finite n *)
  | UOmega, UOmega -> true
  | UOmega, UOmegaPlus _ -> true     (* omega < omega + n *)
  | UOmegaPlus _, UFinite _ -> false
  | UOmegaPlus _, UOmega -> false    (* omega + n > omega *)
  | UOmegaPlus n1, UOmegaPlus n2 -> n1 <= n2

(** Universe level strict ordering - l1 < l2 *)
let level_lt (l1 l2: universe_level) : bool =
  level_leq l1 l2 && not (l1 = l2)

(** Maximum over a list of universe levels *)
let rec level_max_list (ls: list universe_level) : universe_level =
  match ls with
  | [] -> level_zero
  | [l] -> l
  | l :: rest -> level_max l (level_max_list rest)

(** Universe of a type - complete pattern match for all brrr_type constructors.
    Base types are in Type0, compound types are at the max of their components,
    and type-level types (Dynamic/Unknown) are at Type1.

    Note: This function is structurally recursive on brrr_type, matching the
    12 constructors defined in BrrrTypes.fst. *)
let rec type_universe (t: brrr_type) : Tot universe_level (decreases t) =
  match t with
  (* Primitives: mostly at level 0, except Dynamic/Unknown at level 1 *)
  | TPrim pk ->
      (match pk with
       | PUnit | PNever | PBool | PString | PChar -> level_zero
       | PDynamic | PUnknown -> level_one)  (* Type-level types at higher level *)

  (* Numerics: all base types at level 0 *)
  | TNumeric _ -> level_zero

  (* Wrappers: universe of inner type *)
  | TWrap _ inner -> type_universe inner

  (* Modal references: universe of inner type *)
  | TModal _ inner -> type_universe inner

  (* Result: max of both type parameters *)
  | TResult ok_ty err_ty -> level_max (type_universe ok_ty) (type_universe err_ty)

  (* Tuple: max of all element types *)
  | TTuple elems -> type_universe_list elems

  (* Function: max of params and return type *)
  | TFunc ft ->
      level_max (type_universe_params ft.params) (type_universe ft.return_type)

  (* Type variables: at level 1 (they range over types, so one level up) *)
  | TVar _ -> level_one

  (* Type application: max of (level 1 for the constructor) and all args *)
  | TApp base args ->
      level_max (level_max level_one (type_universe base)) (type_universe_list args)

  (* Named type references: at level 1 (refers to a type definition) *)
  | TNamed _ -> level_one

  (* Structs and Enums: at level 1 (they are type definitions) *)
  | TStruct _ -> level_one
  | TEnum _ -> level_one

(** Helper: universe level of a list of types *)
and type_universe_list (ts: list brrr_type) : Tot universe_level (decreases ts) =
  match ts with
  | [] -> level_zero
  | t :: rest -> level_max (type_universe t) (type_universe_list rest)

(** Helper: universe level of function parameters *)
and type_universe_params (ps: list param_type) : Tot universe_level (decreases ps) =
  match ps with
  | [] -> level_zero
  | p :: rest -> level_max (type_universe p.ty) (type_universe_params rest)

(** ============================================================================
    PROPOSITIONAL EQUALITY TYPE
    ============================================================================

    The identity type Eq(A, x, y) represents propositional equality.
    A value of this type is a PROOF that x and y are equal.

    Unlike judgmental equality (definitional), propositional equality
    requires explicit proofs and can be reasoned about.

    Formation:  A : Type, x : A, y : A
                ─────────────────────────
                   Eq(A, x, y) : Type

    Introduction:  x : A
                   ────────────────────
                   refl(x) : Eq(A, x, x)

    Elimination:  p : Eq(A, x, y), C : A -> Type, c : C(x)
                  ──────────────────────────────────────────
                      subst(p, C, c) : C(y)
    ============================================================================ *)

(* ============================================================================
   IDENTITY TYPE DEFINITION
   ============================================================================

   The eq_type inductive has exactly ONE constructor: Refl.
   This means:
     - The ONLY way to create an equality proof is via reflexivity
     - To have p : eq_type a x y, we MUST have x definitionally equal to y
     - Pattern matching on p : eq_type a x y REFINES x to equal y

   INDUCTION PRINCIPLE (auto-generated by F-star)
   ------------------------------------------
   F* automatically generates an induction principle for eq_type:

     eq_type_ind : (P : (x:a) -> (y:a) -> eq_type a x y -> Type) ->
                   ((x:a) -> P x x Refl) ->
                   (x:a) -> (y:a) -> (p:eq_type a x y) -> P x y p

   This is essentially the Martin-Lof J-eliminator.

   WHY ONE CONSTRUCTOR?
   --------------------
   Having only Refl means:
   1. x = y implies x and y are the same "point"
   2. Equality is the tightest possible relation
   3. In F*, matching on Refl COLLAPSES x and y

   In HoTT without UIP, one could imagine more constructors or
   higher-dimensional structure. F*'s Axiom K rules this out.

   ============================================================================ *)

(* Identity type - a proof that two values are equal.
   The only constructor Refl can only be applied when x equals y. *)
type eq_type (a: Type) (x y: a) : Type =
  | Refl : eq_type a x x

(* The canonical proof: reflexivity.
   This is the ONLY way to construct an equality proof. *)
let refl (#a: Type) (x: a) : eq_type a x x = Refl

(** ============================================================================
    EQUALITY ELIMINATION (SUBSTITUTION / LEIBNIZ)
    ============================================================================

    The core eliminator for equality: if x = y, then any property
    holding for x also holds for y.

    This is the computational content of equality.
    ============================================================================ *)

(* ============================================================================
   SUBSTITUTION (LEIBNIZ'S PRINCIPLE)
   ============================================================================

   The substitution principle embodies Leibniz's "indiscernibility of
   identicals": if x = y, then x and y are indistinguishable by any
   property.

   Type: p : eq_type a x y -> prop : (a -> Type) -> px : prop x -> prop y

   This is THE fundamental eliminator for equality. All other operations
   (sym, trans, cong) can be derived from subst.

   COMPUTATION
   -----------
   When p is Refl (which is always the case, by F*'s semantics):
     subst Refl prop px  -->  px

   This works because:
   1. p : eq_type a x y with constructor Refl means x = y definitionally
   2. Therefore prop x = prop y definitionally
   3. So px : prop x is also of type prop y

   LEIBNIZ'S ORIGINAL FORMULATION
   ------------------------------
   Leibniz (1686): "Eadem sunt quorum unum potest substitui alteri
                   salva veritate"
   ("Things are the same if one can be substituted for the other
    without loss of truth")

   ============================================================================ *)

(* Substitution principle: P(x) and x = y implies P(y).
   This is the core eliminator from which all others derive. *)
let subst (#a: Type) (#x #y: a) (p: eq_type a x y) (prop: a -> Type) (px: prop x) : prop y =
  match p with
  | Refl -> px  (* When p is Refl, x = y definitionally, so px : prop y *)

(* Transport along equality - alternative name emphasizing the "moving" intuition.
   In HoTT, this is thought of as "transporting" data along a path. *)
let transport (#a: Type) (prop: a -> Type) (#x #y: a) (p: eq_type a x y) (px: prop x) : prop y =
  subst p prop px

(** ============================================================================
    DERIVED PROPERTIES: SYMMETRY AND TRANSITIVITY
    ============================================================================

    These are derivable from substitution, demonstrating the
    power of the identity type.
    ============================================================================ *)

(* ============================================================================
   DERIVED PROPERTIES: SYMMETRY AND TRANSITIVITY
   ============================================================================

   These fundamental properties are DERIVABLE from substitution alone,
   demonstrating the power of the identity type's eliminator.

   DERIVATION STRATEGY
   -------------------
   To derive sym and trans, we use subst with cleverly chosen properties:

   For SYMMETRY (from p : x = y, produce q : y = x):
     Choose property P(z) = eq_type a z x
     We have: refl x : P(x) = eq_type a x x
     By subst: P(y) = eq_type a y x  (what we want!)

   For TRANSITIVITY (from p : x = y and q : y = z, produce r : x = z):
     Choose property P(w) = eq_type a x w
     We have: p : P(y) = eq_type a x y
     By subst along q: P(z) = eq_type a x z  (what we want!)

   PATH ALGEBRA INTERPRETATION
   ---------------------------
   In HoTT terms:
     sym corresponds to "path reversal" or "inverse path"
     trans corresponds to "path concatenation"

   These satisfy familiar algebraic laws (associativity, unit, inverse).

   ============================================================================ *)

(* Symmetry: x = y implies y = x.
   Derivation: Use subst with P(z) = eq_type a z x.
   Starting from refl x : eq_type a x x, we get eq_type a y x. *)
let sym (#a: Type) (#x #y: a) (p: eq_type a x y) : eq_type a y x =
  subst p (fun z -> eq_type a z x) (refl x)

(* Transitivity: x = y and y = z implies x = z.
   Derivation: Use subst with P(w) = eq_type a x w.
   Starting from p : eq_type a x y, we get eq_type a x z. *)
let trans (#a: Type) (#x #y #z: a) (p: eq_type a x y) (q: eq_type a y z) : eq_type a x z =
  subst q (fun w -> eq_type a x w) p

(** ============================================================================
    EQUALITY LEMMAS
    ============================================================================

    These lemmas express the fundamental properties of propositional equality
    in the Lemma form expected by F*'s SMT encoding. They are equivalent to
    the functions above but in a form suitable for SMT automation.
    ============================================================================ *)

(* Reflexivity lemma: for any x, there exists a proof that x = x *)
let equality_refl_lemma (#a: Type) (x: a) : Lemma (ensures exists (p: eq_type a x x). True) =
  let _ = Refl #a #x in ()

(* Symmetry lemma: from x = y, we can derive y = x *)
let equality_sym_lemma (#a: Type) (#x #y: a) (p: eq_type a x y)
    : Lemma (ensures exists (q: eq_type a y x). True) =
  let _ = sym p in ()

(* Transitivity lemma: from x = y and y = z, we can derive x = z *)
let equality_trans_lemma (#a: Type) (#x #y #z: a) (p: eq_type a x y) (q: eq_type a y z)
    : Lemma (ensures exists (r: eq_type a x z). True) =
  let _ = trans p q in ()

(* Leibniz's law lemma: equal values satisfy the same predicates *)
let equality_subst_lemma (#a: Type) (#x #y: a) (p: eq_type a x y) (prop: a -> Type) (px: prop x)
    : Lemma (ensures exists (py: prop y). True) =
  let _ = subst p prop px in ()

(** ============================================================================
    J-ELIMINATOR (PAULIN-MOHRING FORM)
    ============================================================================

    The most general form of equality elimination.
    Given a dependent type C(y, p) over all y equal to x with proof p,
    and a base case C(x, refl), derive C(y, p) for any p : x = y.
    ============================================================================ *)

(* J eliminator - Paulin-Mohring formulation *)
let j_elim
    (#a: Type)
    (#x: a)
    (c: (y: a) -> eq_type a x y -> Type)
    (base: c x (refl x))
    (#y: a)
    (p: eq_type a x y)
    : c y p =
  match p with
  | Refl -> base

(* Based J eliminator - Martin-Loef formulation *)
let j_elim_ml
    (#a: Type)
    (c: (x: a) -> (y: a) -> eq_type a x y -> Type)
    (base: (x: a) -> c x x (refl x))
    (#x #y: a)
    (p: eq_type a x y)
    : c x y p =
  match p with
  | Refl -> base x

(** ============================================================================
    CONGRUENCE (APPLICATION TO EQUAL ARGUMENTS)
    ============================================================================

    If x = y, then f(x) = f(y) for any function f.
    This is the "ap" (application) operation.
    ============================================================================ *)

(* Congruence: functions respect equality *)
let cong (#a #b: Type) (f: a -> b) (#x #y: a) (p: eq_type a x y) : eq_type b (f x) (f y) =
  match p with
  | Refl -> refl (f x)

(* Binary congruence *)
let cong2
    (#a #b #c: Type)
    (f: a -> b -> c)
    (#x1 #y1: a)
    (#x2 #y2: b)
    (p1: eq_type a x1 y1)
    (p2: eq_type b x2 y2)
    : eq_type c (f x1 x2) (f y1 y2) =
  match p1, p2 with
  | Refl, Refl -> refl (f x1 x2)

(** ============================================================================
    HETEROGENEOUS EQUALITY (JOHN MAJOR EQUALITY / JMeq)
    ============================================================================

    MOTIVATION
    ----------
    Sometimes we need to state that values of DIFFERENT types are equal.
    Standard equality (eq_type a x y) requires x and y to have the SAME type.

    Example: Consider indexed vectors
      vec a 0 and vec a 0 are the same type
      vec a 0 and vec a 1 are DIFFERENT types

    If we have n = m (as nats), we'd like to say:
      v : vec a n  is "equal" to  w : vec a m

    But eq_type (vec a n) v w doesn't typecheck if n != m syntactically!

    HETEROGENEOUS EQUALITY
    ----------------------
    heq_type A B x y says "x : A equals y : B" where A and B may differ.

    The only constructor HRefl : heq_type A A x x requires:
    1. A = B (same type)
    2. x = y (same value)

    So heq_type A B x y implies BOTH A = B and x = y.

    JOHN MAJOR EQUALITY
    -------------------
    Named after a joke by Conor McBride: "John Major is provably equal
    to any other British Prime Minister, but only under the assumption
    that all Prime Ministers are equal."

    The mathematical name is "heterogeneous" or "large" equality.

    USE CASES
    ---------
    1. GADT pattern matching with type-level indices
    2. Relating values across type-level computation
    3. Dependent elimination with type refinement
    4. Equating values whose types depend on proofs

    RELATION TO HOMOGENEOUS EQUALITY
    --------------------------------
    - eq_to_heq: eq_type a x y -> heq_type a a x y (trivial)
    - heq_to_eq: heq_type a a x y -> eq_type a x y (by matching HRefl)

    These conversions are valid because:
    - Any homogeneous equality is trivially heterogeneous
    - Heterogeneous equality between same types is just homogeneous

    ============================================================================ *)

(* Heterogeneous equality - values of potentially different types *)
type heq_type (a b: Type) (x: a) (y: b) : Type =
  | HRefl : heq_type a a x x

(* Heterogeneous reflexivity *)
let hrefl (#a: Type) (x: a) : heq_type a a x x = HRefl

(* Convert homogeneous to heterogeneous equality *)
let eq_to_heq (#a: Type) (#x #y: a) (p: eq_type a x y) : heq_type a a x y =
  match p with
  | Refl -> hrefl x

(* Convert heterogeneous to homogeneous (when types are equal) *)
let heq_to_eq (#a: Type) (#x #y: a) (p: heq_type a a x y) : eq_type a x y =
  match p with
  | HRefl -> refl x

(** ============================================================================
    EQUALITY PROOFS FOR BRRR TYPES
    ============================================================================

    Proof terms for type equality in the Brrr IR.
    ============================================================================ *)

(* Type equality proof *)
type type_eq_proof (t1 t2: brrr_type) : Type =
  eq_type brrr_type t1 t2

(* Proof that same types are equal *)
let type_refl (t: brrr_type) : type_eq_proof t t = refl t

(* Type equality is decidable for brrr_type (using existing type_eq) *)
let decide_type_eq (t1 t2: brrr_type) : option (type_eq_proof t1 t2) =
  if type_eq t1 t2 then
    (* We know t1 = t2 syntactically, but need propositional proof *)
    (* This requires trusted coercion since type_eq is boolean *)
    None  (* Cannot construct proof without axiom *)
  else
    None

(** ============================================================================
    UNIQUENESS OF IDENTITY PROOFS (UIP)
    ============================================================================

    UIP STATEMENT
    -------------
    For any two proofs p, q : eq_type a x y, we have:
      eq_type (eq_type a x y) p q

    In plain English: "All equality proofs are equal."

    HISTORICAL CONTEXT
    ------------------
    Whether UIP is provable was a major question in type theory:

    - Martin-Lof's original theory (1973): UIP status unclear
    - Hofmann & Streicher (1998): Showed UIP is INDEPENDENT of MLTT
      (neither provable nor refutable)
    - HoTT (2013): UIP is FALSE for higher types (groupoid model)
    - F* (and similar): UIP is TRUE by design (Axiom K)

    WHY UIP HOLDS IN F*
    -------------------
    F* includes Axiom K, which says every p : x = x is equal to Refl.
    From K, UIP follows by this argument:

    Given p, q : eq_type a x y
    1. Match on p with | Refl -> (now we know x = y definitionally)
    2. Match on q with | Refl -> (now q = Refl definitionally)
    3. Both p and q are Refl
    4. Therefore eq_type (eq_type a x y) p q via Refl

    The key insight: F*'s pattern matching REFINES the context with
    definitional equality information from the constructor.

    PROOF TECHNIQUE
    ---------------
    Each proof below works by nested pattern matching:

    1. Match p : eq_type a x y with | Refl -> ...
       This refines the goal to: eq_type (eq_type a x x) Refl q

    2. Match q : eq_type a x x with | Refl -> ...
       This refines the goal to: eq_type (eq_type a x x) Refl Refl

    3. Return Refl, which has this type

    CONSEQUENCES OF UIP
    -------------------
    - Proof irrelevance: equality proofs can be erased
    - Simpler reasoning: don't need coherence conditions
    - Easy extraction: proofs compile to unit
    - No higher groupoid structure

    H-SETS
    ------
    In HoTT terminology, types satisfying UIP are called "h-sets" or
    "sets" or "0-truncated types." All types in F* are h-sets.

    ============================================================================ *)

(** UIP for booleans - proven by pattern matching.

    When p : eq_type bool b1 b2, matching on Refl tells us b1 == b2.
    Then q : eq_type bool b1 b1, and matching on q gives q == Refl.
    Both p and q are Refl, so they are equal (via Refl). *)
let uip_bool (b1 b2: bool) (p q: eq_type bool b1 b2) : eq_type (eq_type bool b1 b2) p q =
  match p with
  | Refl ->
      (* p == Refl : eq_type bool b1 b1, so b1 == b2 definitionally *)
      match q with
      | Refl ->
          (* q == Refl : eq_type bool b1 b1, so q == p definitionally *)
          Refl  (* : eq_type (eq_type bool b1 b1) Refl Refl *)

(** UIP for integers - proven by pattern matching.

    Same reasoning as uip_bool: both proofs must be Refl. *)
let uip_int (n1 n2: int) (p q: eq_type int n1 n2) : eq_type (eq_type int n1 n2) p q =
  match p with
  | Refl ->
      match q with
      | Refl -> Refl

(** UIP for natural numbers - also decidable *)
let uip_nat (n1 n2: nat) (p q: eq_type nat n1 n2) : eq_type (eq_type nat n1 n2) p q =
  match p with
  | Refl ->
      match q with
      | Refl -> Refl

(** UIP for strings - decidable equality *)
let uip_string (s1 s2: string) (p q: eq_type string s1 s2) : eq_type (eq_type string s1 s2) p q =
  match p with
  | Refl ->
      match q with
      | Refl -> Refl

(** Generic UIP for any type - this pattern works because eq_type has only one constructor.

    Note: This relies on F*'s intensional equality and pattern matching semantics.
    In HoTT without K, this would not be valid, but F* has Axiom K built in. *)
let uip (#a: Type) (#x #y: a) (p q: eq_type a x y) : eq_type (eq_type a x y) p q =
  match p with
  | Refl ->
      match q with
      | Refl -> Refl

(** ============================================================================
    SINGLETON TYPES (REFINEMENT WITH EQUALITY)
    ============================================================================

    A singleton type {x : A | y = x} contains exactly one value.
    This is useful for GADT-like constructions.
    ============================================================================ *)

(* Singleton type: type containing exactly one value *)
noeq type singleton (a: Type) (x: a) =
  | MkSingleton : (y: a) -> eq_type a y x -> singleton a x

(* The unique inhabitant of singleton *)
let singleton_value (#a: Type) (#x: a) (s: singleton a x) : a =
  match s with
  | MkSingleton y _ -> y

(* Proof that singleton value equals x *)
let singleton_proof (#a: Type) (#x: a) (s: singleton a x)
    : eq_type a (singleton_value s) x =
  match s with
  | MkSingleton _ p -> p

(** ============================================================================
    EQUATIONAL REASONING COMBINATORS
    ============================================================================

    Convenient syntax for chains of equalities:
      x == y   by p1
        == z   by p2
        == w   by p3
    ============================================================================ *)

(* Begin equational chain *)
let eq_begin (#a: Type) (x: a) : eq_type a x x = refl x

(* Continue chain with step *)
let eq_step
    (#a: Type)
    (#x #y #z: a)
    (pxy: eq_type a x y)
    (pyz: eq_type a y z)
    : eq_type a x z =
  trans pxy pyz

(* End chain (identity) *)
let eq_end (#a: Type) (#x #y: a) (p: eq_type a x y) : eq_type a x y = p

(** ============================================================================
    DECIDABLE EQUALITY CLASS
    ============================================================================

    DECIDABLE vs UNDECIDABLE EQUALITY
    ---------------------------------
    For some types, we can COMPUTE whether two values are equal:
      int, bool, nat, string, finite types, ...

    For other types, equality is UNDECIDABLE:
      (int -> int)  -- requires checking infinitely many inputs
      arbitrary Type  -- Turing-complete computations possible

    DECIDABLE EQUALITY TYPE
    -----------------------
    dec_eq_result a x y is a DISJOINT SUM:
      - Yes (p : eq_type a x y)        -- x equals y, with proof
      - No  (f : eq_type a x y -> False)  -- x doesn't equal y, with refutation

    This is STRONGER than boolean equality:
      - bool_eq returns true/false with no proof
      - dec_eq returns proof of equality OR proof of inequality

    TYPECLASS PATTERN
    -----------------
    has_dec_eq a bundles:
      - The type a
      - A decision procedure dec_eq : (x y : a) -> dec_eq_result a x y

    This is similar to Haskell's Eq class but with proofs.

    F*'S EQTYPE
    -----------
    F* has built-in support for types with decidable equality:

      eqtype = a:Type{hasEq a}

    where hasEq is a predicate that F* derives automatically for
    inductive types whose constructors only contain eqtypes.

    For eqtype, the (=) operator returns bool and is sound:
      (x = y) = true  implies  x == y

    SOUNDNESS AND COMPLETENESS
    --------------------------
    To convert boolean equality to decidable equality, we need BOTH:

    1. SOUNDNESS: eq_fn x y = true  ==>  x == y
       "If the test returns true, the values are really equal"

    2. COMPLETENESS: x == y  ==>  eq_fn x y = true
       "If the values are really equal, the test returns true"

    Without completeness, we can't prove the No case (inequality).
    Completeness ensures the boolean test captures all equalities.

    ============================================================================ *)

(* Decidable equality result *)
noeq type dec_eq_result (a: Type) (x y: a) =
  | Yes : eq_type a x y -> dec_eq_result a x y
  | No  : (eq_type a x y -> False) -> dec_eq_result a x y

(* Decidable equality typeclass *)
noeq type has_dec_eq (a: Type) = {
  dec_eq : (x: a) -> (y: a) -> dec_eq_result a x y;
}

(** Boolean equality implies decidable equality.

    This function requires BOTH soundness and completeness:
    - Soundness: eq x y = true implies x == y (definitionally equal)
    - Completeness: x == y implies eq x y = true

    Without completeness, we cannot prove the No case (that inequality holds).

    NOTE: The completeness requirement is necessary because we need to prove
    that when eq x y = false, there is no proof of x = y. This is only possible
    if the boolean equality is COMPLETE (i.e., reflects all definitional equalities).
*)

(* For decidable equality, we need both soundness and completeness *)
let bool_eq_to_dec_eq
    (#a: Type)
    (eq_fn: a -> a -> bool)
    (eq_sound: (x: a) -> (y: a) -> Lemma (requires eq_fn x y = true) (ensures x == y))
    (eq_complete: (x: a) -> (y: a) -> Lemma (requires x == y) (ensures eq_fn x y = true))
    : has_dec_eq a =
  { dec_eq = fun x y ->
      if eq_fn x y then begin
        (* Use soundness to establish x == y definitionally *)
        eq_sound x y;
        (* Now x == y, so eq_type a x y is definitionally eq_type a x x *)
        Yes (Refl #a #x)
      end
      else begin
        (* When eq_fn x y = false, prove that eq_type a x y -> False *)
        No (fun (p: eq_type a x y) ->
          (* From p : eq_type a x y, we know x == y by matching on Refl *)
          match p with
          | Refl ->
              (* Now x == y definitionally, so by completeness eq_fn x y = true *)
              eq_complete x y
              (* But we have eq_fn x y = false, contradiction with true = false *)
              (* F* detects this contradiction automatically *)
        )
      end
  }

(** ============================================================================
    CONNECTION TO REFINEMENT TYPES
    ============================================================================

    Propositional equality connects to refinement types:
      {x : A | x = v} is equivalent to Singleton(A, v)

    This enables:
    1. GADT-like pattern matching with type refinement
    2. Dependent pattern matching
    3. Type-safe coercions
    ============================================================================ *)

(* Equality refinement: values equal to a specific value *)
type eq_refinement (a: Type) (v: a) = x:a{x == v}

(* Convert singleton to refinement *)
let singleton_to_refinement (#a: Type) (#v: a) (s: singleton a v) : eq_refinement a v =
  match s with
  | MkSingleton y p ->
      (* p : y = v, so y satisfies refinement x == v *)
      match p with
      | Refl -> y

(* Convert refinement to singleton *)
let refinement_to_singleton (#a: Type) (#v: a) (x: eq_refinement a v) : singleton a v =
  MkSingleton x (refl x)

(** ============================================================================
    COERCION ALONG EQUALITY
    ============================================================================

    When we have a proof that types A and B are equal,
    we can coerce values from A to B.
    ============================================================================ *)

(* Coerce value along type equality *)
let coerce (#a #b: Type) (p: eq_type Type a b) (x: a) : b =
  match p with
  | Refl -> x

(* Safe cast when types are propositionally equal *)
let cast_eq (#a #b: Type) (p: eq_type Type a b) : a -> b =
  coerce p

(** ============================================================================
    LEIBNIZ EQUALITY (ALTERNATIVE FORMULATION)
    ============================================================================

    LEIBNIZ'S PRINCIPLE (1686)
    --------------------------
    "Eadem sunt quorum unum potest substitui alteri salva veritate"
    ("Things are the same if one can be substituted for the other
     without loss of truth")

    This gives an alternative definition of equality:
      x = y  iff  forall P. P(x) -> P(y)

    LEIBNIZ EQUALITY TYPE
    ---------------------
      leibniz_eq a x y = (p: a -> Type) -> p x -> p y

    A proof of Leibniz equality is a FUNCTION that transforms ANY
    property of x into that same property of y.

    EQUIVALENCE WITH IDENTITY TYPE
    ------------------------------
    For types with J-elimination (like F*'s eq_type):

      eq_to_leibniz : eq_type a x y -> leibniz_eq a x y
        Proof: Use subst with the given property P

      leibniz_to_eq : leibniz_eq a x y -> eq_type a x y
        Proof: Apply Leibniz eq to P(z) = eq_type a x z,
               starting from refl x : P(x)

    These establish a bijection (isomorphism) between the two definitions.

    HISTORICAL NOTE
    ---------------
    Leibniz's formulation predates Martin-Lof's by 300 years!
    The identity type can be seen as an INTERNALIZATION of Leibniz's
    principle as a datatype.

    In System F (impredicative polymorphism), Leibniz equality is
    the natural definition since there's no identity type primitive.

    ============================================================================ *)

(* Leibniz equality *)
type leibniz_eq (a: Type) (x y: a) =
  (p: a -> Type) -> p x -> p y

(* Identity type implies Leibniz *)
let eq_to_leibniz (#a: Type) (#x #y: a) (eq: eq_type a x y) : leibniz_eq a x y =
  fun p px -> subst eq p px

(* Leibniz implies identity (for types with J-elimination) *)
let leibniz_to_eq (#a: Type) (#x #y: a) (leib: leibniz_eq a x y) : eq_type a x y =
  leib (fun z -> eq_type a x z) (refl x)

(** ============================================================================
    PATH TYPES (HOMOTOPY TYPE THEORY PERSPECTIVE)
    ============================================================================

    HOMOTOPY INTERPRETATION OF EQUALITY
    -----------------------------------
    In Homotopy Type Theory (HoTT), we interpret:

      - Types as SPACES
      - Values x : A as POINTS in space A
      - Equalities p : eq_type A x y as PATHS from x to y

    This geometric interpretation is remarkably powerful and leads to
    new insights about equality and type structure.

    PATH OPERATIONS
    ---------------
      OPERATION           TYPE THEORY        GEOMETRY
      -------------------------------------------------
      Reflexivity         Refl : x = x       Identity path (point)
      Symmetry            sym p : y = x      Path reversal
      Transitivity        trans p q : x = z  Path concatenation
      Congruence          cong f p : f x = f y  Applying map to path

    PATH ALGEBRA
    ------------
    Paths satisfy algebraic laws reminiscent of GROUP theory:

      concat (idpath x) p = p           (left unit)
      concat p (idpath y) = p           (right unit)
      concat (inverse p) p = idpath y   (left inverse)
      concat p (inverse p) = idpath x   (right inverse)
      concat (concat p q) r = concat p (concat q r)  (associativity)

    In full HoTT, these laws hold UP TO HIGHER PATHS (2-paths).
    In F* with UIP, they hold strictly (definitionally).

    HIGHER STRUCTURE (Not present in F-star with UIP)
    ----------------------------
    In HoTT without UIP:
      - Paths between paths (2-paths) form a groupoid
      - 2-paths between 2-paths (3-paths) form a 2-groupoid
      - And so on, forming an infinity-groupoid structure

    This rich structure is COLLAPSED in F* by Axiom K.

    WHY PROVIDE PATH VOCABULARY?
    ----------------------------
    1. INTUITION: Geometric language is often clearer
    2. LITERATURE: Many papers use HoTT terminology
    3. COMPATIBILITY: Easy to port proofs from HoTT systems
    4. FUTURE: If F* ever supports HoTT modes

    Note: In F*, path types are just ALIASES for eq_type.
    The higher structure of HoTT is not present.

    ============================================================================ *)

(* Path type - alias for equality *)
type path (a: Type) (x y: a) = eq_type a x y

(* Identity path - reflexivity *)
let idpath (#a: Type) (x: a) : path a x x = refl x

(* Path inverse - symmetry *)
let inverse (#a: Type) (#x #y: a) (p: path a x y) : path a y x = sym p

(* Path concatenation - transitivity *)
let concat (#a: Type) (#x #y #z: a) (p: path a x y) (q: path a y z) : path a x z = trans p q

(* Apply function to path *)
let ap (#a #b: Type) (f: a -> b) (#x #y: a) (p: path a x y) : path b (f x) (f y) = cong f p

(** ============================================================================
    AXIOM K (STREICHER'S AXIOM)
    ============================================================================

    STATEMENT OF AXIOM K
    --------------------
    For any type A, any x : A, and any proof p : eq_type A x x:

      eq_type (eq_type A x x) p (Refl #A #x)

    In words: "Every proof that x equals itself is equal to reflexivity."

    ORIGINS AND NAME
    ----------------
    Axiom K was introduced by Thomas Streicher in his 1993 PhD thesis
    "Investigations into Intensional Type Theory." The letter K was
    chosen arbitrarily (no deep meaning).

    It's also known as:
    - "Uniqueness of Reflexivity"
    - "The K axiom"
    - "Streicher's Axiom"

    CONSEQUENCES OF AXIOM K
    -----------------------
    1. UIP (Uniqueness of Identity Proofs) follows from K
    2. Pattern matching on equality proofs is valid
    3. Proof irrelevance for equality proofs
    4. The type theory becomes extensional

    INCOMPATIBILITY WITH HOTT
    -------------------------
    In Homotopy Type Theory, the UNIVALENCE AXIOM states:

      (A = B) <=> (A <-> B)   (type equality = type equivalence)

    This means there can be MANY distinct proofs that bool = bool
    (e.g., identity, negation). Axiom K would collapse these.

    F* CHOOSES K OVER UNIVALENCE because:
    - Simpler metatheory
    - Decidable type checking (usually)
    - Familiar programming model
    - Proof irrelevance for extraction

    WHY AXIOM K HERE?
    -----------------
    Although F* has Axiom K built in, we make it EXPLICIT here for:
    1. Clarity about our assumptions
    2. Compatibility with other proof assistants
    3. Documentation of the extensional nature of F*
    4. Potential future changes to F*'s foundations

    The `assume val` declares K as an axiom that F* must accept.
    In practice, F* proves this internally via pattern matching.

    ============================================================================ *)

(* Axiom K: all self-equalities are refl *)
assume val axiom_k :
  (#a: Type) ->
  (x: a) ->
  (p: eq_type a x x) ->
  eq_type (eq_type a x x) p (refl x)

(* Using K to pattern match on equality *)
let match_refl
    (#a: Type)
    (#x: a)
    (p: eq_type a x x)
    (result: Type)
    (on_refl: result)
    : result =
  (* By K, p = refl, so we can just return on_refl *)
  on_refl
