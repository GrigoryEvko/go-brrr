(**
 * BrrrLang.Core.PropositionalEquality - Interface
 *
 * Propositional Equality (Identity) Types for Brrr-Lang.
 *
 * This module provides:
 *   - Identity type: eq_type a x y - proof that x and y are equal
 *   - Reflexivity: refl(x) - proof that x = x
 *   - Substitution (Leibniz): if x = y, can substitute x for y
 *   - Symmetry and transitivity derived from subst
 *   - J-eliminator for general equality reasoning
 *   - Heterogeneous equality for type-level proofs
 *   - UIP (Uniqueness of Identity Proofs)
 *   - Proper universe level stratification (no omega hack!)
 *
 * This is the foundation for:
 *   - GADTs (Generalized Algebraic Data Types)
 *   - Type-level computation
 *   - Proof-carrying code
 *
 * Follows HACL* interface patterns from Lib.IntTypes.fsti
 *)
module PropositionalEquality

(** Z3 solver options - conservative baseline following HACL* patterns *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open Primitives
open BrrrTypes

(* =========================================================================
   SECTION 1: UNIVERSE LEVELS
   =========================================================================

   Proper universe stratification to avoid Russell's paradox:
     Type0 : Type1 : Type2 : ... : omega : omega+1 : ...

   Unlike a naive implementation using nat, this properly handles omega
   as a distinct value, not a finite approximation.
   ========================================================================= *)

(** Universe level representation - properly handles omega *)
type universe_level =
  | UFinite : nat -> universe_level           (* Finite level: 0, 1, 2, ... *)
  | UOmega  : universe_level                  (* Limit ordinal omega *)
  | UOmegaPlus : nat -> universe_level        (* omega + n for n > 0 *)

(** Universe level constants *)
val level_zero : universe_level   (* Type0 *)
val level_one : universe_level    (* Type1 *)
val level_omega : universe_level  (* Proper omega, not a hack *)

(** Universe level operations *)
val level_max : universe_level -> universe_level -> universe_level
val level_succ : universe_level -> universe_level
val level_leq : universe_level -> universe_level -> bool
val level_lt : universe_level -> universe_level -> bool
val level_max_list : list universe_level -> universe_level

(** Universe of a brrr_type - structurally recursive *)
val type_universe : t:brrr_type -> Tot universe_level (decreases t)

(* =========================================================================
   SECTION 2: PROPOSITIONAL EQUALITY TYPE (Identity Type)
   =========================================================================

   The identity type eq_type a x y represents propositional equality.
   A value of this type is a PROOF that x and y are equal.

   Formation:  A : Type, x : A, y : A
               -----------------------
                  eq_type A x y : Type

   Introduction:  x : A
                  --------------------
                  Refl : eq_type A x x

   Elimination:  p : eq_type A x y, P : A -> Type, px : P x
                 ------------------------------------------
                      subst p P px : P y
   ========================================================================= *)

(** Martin-Lof identity type with single constructor *)
type eq_type (a: Type) (x y: a) : Type =
  | Refl : eq_type a x x

(* =========================================================================
   SECTION 3: CORE OPERATIONS
   ========================================================================= *)

(** Reflexivity: proof that x = x *)
val refl : #a:Type -> x:a -> eq_type a x x

(** Substitution (Leibniz): P(x) and x = y implies P(y) *)
val subst : #a:Type -> #x:a -> #y:a ->
    p:eq_type a x y ->
    prop:(a -> Type) ->
    px:prop x ->
    prop y

(** Transport along equality - alternative name for subst *)
val transport : #a:Type ->
    prop:(a -> Type) ->
    #x:a -> #y:a ->
    p:eq_type a x y ->
    px:prop x ->
    prop y

(* =========================================================================
   SECTION 4: DERIVED PROPERTIES
   ========================================================================= *)

(** Symmetry: x = y implies y = x *)
val sym : #a:Type -> #x:a -> #y:a -> eq_type a x y -> eq_type a y x

(** Transitivity: x = y and y = z implies x = z *)
val trans : #a:Type -> #x:a -> #y:a -> #z:a ->
    eq_type a x y -> eq_type a y z -> eq_type a x z

(* =========================================================================
   SECTION 5: EQUALITY LEMMAS

   These lemmas express the fundamental properties of propositional equality
   in the Lemma form expected by F*'s SMT encoding.
   ========================================================================= *)

(** Reflexivity as a lemma *)
val equality_refl_lemma : #a:Type -> x:a ->
    Lemma (ensures exists (p: eq_type a x x). True)

(** Symmetry as a lemma *)
val equality_sym_lemma : #a:Type -> #x:a -> #y:a -> p:eq_type a x y ->
    Lemma (ensures exists (q: eq_type a y x). True)

(** Transitivity as a lemma *)
val equality_trans_lemma : #a:Type -> #x:a -> #y:a -> #z:a ->
    p:eq_type a x y -> q:eq_type a y z ->
    Lemma (ensures exists (r: eq_type a x z). True)

(** Leibniz's law as a lemma: equal values satisfy the same predicates *)
val equality_subst_lemma : #a:Type -> #x:a -> #y:a ->
    p:eq_type a x y -> prop:(a -> Type) -> px:prop x ->
    Lemma (ensures exists (py: prop y). True)

(* =========================================================================
   SECTION 6: J-ELIMINATOR (Path Induction)
   ========================================================================= *)

(** Paulin-Mohring formulation of J *)
val j_elim : #a:Type -> #x:a ->
    c:((y:a) -> eq_type a x y -> Type) ->
    base:c x (refl x) ->
    #y:a -> p:eq_type a x y ->
    c y p

(** Martin-Lof formulation of J *)
val j_elim_ml : #a:Type ->
    c:((x:a) -> (y:a) -> eq_type a x y -> Type) ->
    base:((x:a) -> c x x (refl x)) ->
    #x:a -> #y:a -> p:eq_type a x y ->
    c x y p

(* =========================================================================
   SECTION 7: CONGRUENCE (Functions Respect Equality)
   ========================================================================= *)

(** Congruence: if x = y then f(x) = f(y) *)
val cong : #a:Type -> #b:Type ->
    f:(a -> b) ->
    #x:a -> #y:a ->
    eq_type a x y ->
    eq_type b (f x) (f y)

(** Binary congruence *)
val cong2 : #a:Type -> #b:Type -> #c:Type ->
    f:(a -> b -> c) ->
    #x1:a -> #y1:a -> #x2:b -> #y2:b ->
    eq_type a x1 y1 -> eq_type b x2 y2 ->
    eq_type c (f x1 x2) (f y1 y2)

(* =========================================================================
   SECTION 8: HETEROGENEOUS EQUALITY (John Major Equality)

   For type families, we sometimes need equality between values
   of DIFFERENT types. heq_type A B x y means x:A and y:B are equal
   (which implies A = B).
   ========================================================================= *)

(** Heterogeneous equality type *)
type heq_type (a b: Type) (x: a) (y: b) : Type =
  | HRefl : heq_type a a x x

(** Heterogeneous reflexivity *)
val hrefl : #a:Type -> x:a -> heq_type a a x x

(** Convert homogeneous to heterogeneous equality *)
val eq_to_heq : #a:Type -> #x:a -> #y:a -> eq_type a x y -> heq_type a a x y

(** Convert heterogeneous to homogeneous (when types are equal) *)
val heq_to_eq : #a:Type -> #x:a -> #y:a -> heq_type a a x y -> eq_type a x y

(* =========================================================================
   SECTION 9: BRRR TYPE EQUALITY
   ========================================================================= *)

(** Type equality proof for brrr_type *)
unfold
let type_eq_proof (t1 t2: brrr_type) : Type = eq_type brrr_type t1 t2

(** Proof that same types are equal *)
val type_refl : t:brrr_type -> type_eq_proof t t

(** Attempt to decide type equality (limited - see implementation) *)
val decide_type_eq : t1:brrr_type -> t2:brrr_type -> option (type_eq_proof t1 t2)

(* =========================================================================
   SECTION 10: UNIQUENESS OF IDENTITY PROOFS (UIP)

   For types with decidable equality (h-sets), all equality proofs are equal.
   This is proven by pattern matching on both proofs - both must be Refl.
   ========================================================================= *)

(** UIP for booleans - proven by pattern matching *)
val uip_bool : b1:bool -> b2:bool -> p:eq_type bool b1 b2 -> q:eq_type bool b1 b2 ->
    eq_type (eq_type bool b1 b2) p q

(** UIP for integers - proven by pattern matching *)
val uip_int : n1:int -> n2:int -> p:eq_type int n1 n2 -> q:eq_type int n1 n2 ->
    eq_type (eq_type int n1 n2) p q

(** UIP for natural numbers - proven by pattern matching *)
val uip_nat : n1:nat -> n2:nat -> p:eq_type nat n1 n2 -> q:eq_type nat n1 n2 ->
    eq_type (eq_type nat n1 n2) p q

(** UIP for strings - proven by pattern matching *)
val uip_string : s1:string -> s2:string -> p:eq_type string s1 s2 -> q:eq_type string s1 s2 ->
    eq_type (eq_type string s1 s2) p q

(** Generic UIP for any type - relies on F*'s Axiom K *)
val uip : #a:Type -> #x:a -> #y:a -> p:eq_type a x y -> q:eq_type a x y ->
    eq_type (eq_type a x y) p q

(* =========================================================================
   SECTION 11: SINGLETON TYPES

   A singleton type {x : A | y = x} contains exactly one value.
   This is useful for GADT-like constructions.
   ========================================================================= *)

(** Singleton type: contains exactly one value equal to x *)
noeq type singleton (a: Type) (x: a) =
  | MkSingleton : (y: a) -> eq_type a y x -> singleton a x

(** Extract the value from a singleton *)
val singleton_value : #a:Type -> #x:a -> singleton a x -> a

(** Proof that singleton value equals x *)
val singleton_proof : #a:Type -> #x:a -> s:singleton a x ->
    eq_type a (singleton_value s) x

(* =========================================================================
   SECTION 12: EQUATIONAL REASONING COMBINATORS

   Convenient syntax for chains of equalities:
     x == y   by p1
       == z   by p2
       == w   by p3
   ========================================================================= *)

(** Begin equational chain *)
val eq_begin : #a:Type -> x:a -> eq_type a x x

(** Continue chain with step *)
val eq_step : #a:Type -> #x:a -> #y:a -> #z:a ->
    eq_type a x y -> eq_type a y z -> eq_type a x z

(** End chain (identity) *)
val eq_end : #a:Type -> #x:a -> #y:a -> eq_type a x y -> eq_type a x y

(* =========================================================================
   SECTION 13: DECIDABLE EQUALITY
   ========================================================================= *)

(** Decidable equality result *)
noeq type dec_eq_result (a: Type) (x y: a) =
  | Yes : eq_type a x y -> dec_eq_result a x y
  | No  : (eq_type a x y -> False) -> dec_eq_result a x y

(** Decidable equality typeclass *)
noeq type has_dec_eq (a: Type) = {
  dec_eq : (x:a) -> (y:a) -> dec_eq_result a x y;
}

(**
 * Boolean equality implies decidable equality.
 * Requires BOTH soundness AND completeness:
 *   - Soundness: eq x y = true implies x == y
 *   - Completeness: x == y implies eq x y = true
 *)
val bool_eq_to_dec_eq : #a:Type ->
    eq_fn:(a -> a -> bool) ->
    eq_sound:((x:a) -> (y:a) -> Lemma (requires eq_fn x y = true) (ensures x == y)) ->
    eq_complete:((x:a) -> (y:a) -> Lemma (requires x == y) (ensures eq_fn x y = true)) ->
    has_dec_eq a

(* =========================================================================
   SECTION 14: REFINEMENT TYPES CONNECTION

   Propositional equality connects to refinement types:
     {x : A | x = v} is equivalent to Singleton(A, v)
   ========================================================================= *)

(** Equality refinement: values equal to a specific value *)
unfold
let eq_refinement (a: Type) (v: a) = x:a{x == v}

(** Convert singleton to refinement *)
val singleton_to_refinement : #a:Type -> #v:a -> singleton a v -> eq_refinement a v

(** Convert refinement to singleton *)
val refinement_to_singleton : #a:Type -> #v:a -> eq_refinement a v -> singleton a v

(* =========================================================================
   SECTION 15: COERCION ALONG EQUALITY

   When we have a proof that types A and B are equal,
   we can coerce values from A to B.
   ========================================================================= *)

(** Coerce value along type equality *)
val coerce : #a:Type -> #b:Type -> eq_type Type a b -> a -> b

(** Safe cast when types are propositionally equal *)
val cast_eq : #a:Type -> #b:Type -> eq_type Type a b -> (a -> b)

(* =========================================================================
   SECTION 16: LEIBNIZ EQUALITY

   Leibniz equality: x = y iff for all P, P(x) implies P(y).
   This is equivalent to the identity type for well-behaved types.
   ========================================================================= *)

(** Leibniz equality *)
unfold
let leibniz_eq (a: Type) (x y: a) = (p: a -> Type) -> p x -> p y

(** Identity type implies Leibniz *)
val eq_to_leibniz : #a:Type -> #x:a -> #y:a -> eq_type a x y -> leibniz_eq a x y

(** Leibniz implies identity (for types with J-elimination) *)
val leibniz_to_eq : #a:Type -> #x:a -> #y:a -> leibniz_eq a x y -> eq_type a x y

(* =========================================================================
   SECTION 17: PATH TYPES (HoTT Perspective)

   In HoTT, equality is interpreted as paths in a space.
   Path composition corresponds to transitivity.
   Path inversion corresponds to symmetry.
   ========================================================================= *)

(** Path type - alias for equality *)
unfold
let path (a: Type) (x y: a) = eq_type a x y

(** Identity path - reflexivity *)
val idpath : #a:Type -> x:a -> path a x x

(** Path inverse - symmetry *)
val inverse : #a:Type -> #x:a -> #y:a -> path a x y -> path a y x

(** Path concatenation - transitivity *)
val concat : #a:Type -> #x:a -> #y:a -> #z:a ->
    path a x y -> path a y z -> path a x z

(** Apply function to path *)
val ap : #a:Type -> #b:Type ->
    f:(a -> b) ->
    #x:a -> #y:a ->
    path a x y ->
    path b (f x) (f y)

(* =========================================================================
   SECTION 18: AXIOM K

   Axiom K states that all proofs of x = x are refl.
   This enables pattern matching on equality proofs.
   It is incompatible with Univalence in HoTT, but F* has K built in.
   ========================================================================= *)

(** Axiom K: all self-equalities are refl *)
assume val axiom_k : #a:Type -> x:a -> p:eq_type a x x ->
    eq_type (eq_type a x x) p (refl x)

(** Using K to pattern match on equality *)
val match_refl : #a:Type -> #x:a -> eq_type a x x -> result:Type -> result -> result
