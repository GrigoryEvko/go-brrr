(**
 * BrrrLang.Core.PropositionalEquality
 *
 * Propositional Equality (Identity) Types for Brrr-Lang.
 *
 * Gap Resolution:
 *   4. Equality types MISSING - no propositional equality
 *   5. Universe levels MISSING - no stratification
 *
 * This module defines:
 *   - Identity type: Eq(a, x, y) - proof that x and y are equal
 *   - Reflexivity: refl(x) - proof that x = x
 *   - Substitution (Leibniz): if x = y, can substitute x for y
 *   - Symmetry and transitivity derived from subst
 *   - J-eliminator for general equality reasoning
 *   - Heterogeneous equality for type-level proofs
 *
 * This is the foundation for:
 *   - GADTs (Generalized Algebraic Data Types)
 *   - Type-level computation
 *   - Proof-carrying code
 *
 * Depends on: Primitives, BrrrTypes
 *)
module PropositionalEquality

(** Z3 solver options - conservative baseline for equality proofs *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open Primitives
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

(* We represent equality types as an abstract type in F* *)

(* Identity type - a proof that two values are equal *)
type eq_type (a: Type) (x y: a) : Type =
  | Refl : eq_type a x x

(* The canonical proof: reflexivity *)
let refl (#a: Type) (x: a) : eq_type a x x = Refl

(** ============================================================================
    EQUALITY ELIMINATION (SUBSTITUTION / LEIBNIZ)
    ============================================================================

    The core eliminator for equality: if x = y, then any property
    holding for x also holds for y.

    This is the computational content of equality.
    ============================================================================ *)

(* Substitution principle: P(x) and x = y implies P(y) *)
let subst (#a: Type) (#x #y: a) (p: eq_type a x y) (prop: a -> Type) (px: prop x) : prop y =
  match p with
  | Refl -> px  (* When p is refl, x = y definitionally *)

(* Alternative form: transport along equality *)
let transport (#a: Type) (prop: a -> Type) (#x #y: a) (p: eq_type a x y) (px: prop x) : prop y =
  subst p prop px

(** ============================================================================
    DERIVED PROPERTIES: SYMMETRY AND TRANSITIVITY
    ============================================================================

    These are derivable from substitution, demonstrating the
    power of the identity type.
    ============================================================================ *)

(* Symmetry: x = y implies y = x *)
let sym (#a: Type) (#x #y: a) (p: eq_type a x y) : eq_type a y x =
  (* Use subst with property P(z) = Eq(A, z, x) *)
  subst p (fun z -> eq_type a z x) (refl x)

(* Transitivity: x = y and y = z implies x = z *)
let trans (#a: Type) (#x #y #z: a) (p: eq_type a x y) (q: eq_type a y z) : eq_type a x z =
  (* Use subst with property P(w) = Eq(A, x, w) *)
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
    HETEROGENEOUS EQUALITY (JOHN MAJOR EQUALITY)
    ============================================================================

    For type families, we sometimes need equality between values
    of DIFFERENT types. This is "heterogeneous equality" or "JMeq".

    HeqType(A, x, B, y) - x:A and y:B are equal (implies A = B)
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

    For some types, all equality proofs are equal (UIP).
    This is NOT provable in general intensional type theory,
    but holds for "h-sets" (types with decidable equality).

    For types with decidable equality (like bool, int, nat), we can PROVE UIP
    by pattern matching on both equality proofs. Since both must be Refl
    (the only constructor of eq_type), they are definitionally equal.

    The key insight: when we match on p : eq_type a x y with | Refl -> ...,
    we learn that x == y definitionally. Then matching on q : eq_type a x x
    with | Refl -> ... gives us q == Refl definitionally. Similarly for p.
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

    Types with decidable equality can compute equality proofs.
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

    Leibniz equality: x = y iff for all P, P(x) implies P(y).
    This is equivalent to the identity type for well-behaved types.
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

    In HoTT, equality is interpreted as paths in a space.
    Path composition corresponds to transitivity.
    Path inversion corresponds to symmetry.

    We provide a thin layer for HoTT-style reasoning.
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
    AXIOM K (OPTIONAL - ENABLES PATTERN MATCHING ON REFL)
    ============================================================================

    Axiom K states that all proofs of x = x are refl.
    This enables pattern matching on equality proofs.
    It is incompatible with Univalence in HoTT.

    For practical verification, K is often assumed.
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
