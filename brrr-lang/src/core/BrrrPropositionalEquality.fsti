(**
 * BrrrLang.Core.PropositionalEquality - Interface
 *
 * =============================================================================
 * PROPOSITIONAL EQUALITY (IDENTITY TYPES) FOR BRRR-LANG
 * =============================================================================
 *
 * This module provides the foundational theory of propositional equality,
 * also known as the Martin-Lof Identity Type from dependent type theory.
 *
 * OVERVIEW
 * --------
 * Propositional equality (==) is DISTINCT from:
 *
 *   1. Definitional/Judgmental Equality: Terms that reduce to the same normal
 *      form. This is implicit in the type checker and cannot be stated as a
 *      proposition. Example: (fun x -> x) 5 is definitionally equal to 5.
 *
 *   2. Boolean Equality (=): A decidable function returning true/false.
 *      Only available for `eqtype` (types with decidable equality).
 *      Example: (5 = 5) returns the boolean `true`.
 *
 *   3. Propositional Equality (==): A TYPE whose inhabitants are PROOFS
 *      that two values are equal. Example: Refl : eq_type int 5 5
 *
 * In F*, the (==) operator is defined as: squash (equals x y)
 * where `equals` is the identity type and `squash` erases the proof witness.
 *
 * MARTIN-LOF IDENTITY TYPE
 * ------------------------
 * The identity type was introduced by Per Martin-Lof in his 1973 paper
 * "An Intuitionistic Theory of Types: Predicative Part" and forms the
 * basis for equality reasoning in type theory.
 *
 * Formation rule:
 *     A : Type    x : A    y : A
 *     --------------------------
 *         eq_type A x y : Type
 *
 * Introduction rule (Reflexivity):
 *             x : A
 *     ---------------------
 *     Refl : eq_type A x x
 *
 * Elimination rule (J-eliminator / Path Induction):
 *     C : (y:A) -> eq_type A x y -> Type
 *     c : C x Refl
 *     p : eq_type A x y
 *     ---------------------------------
 *           J C c p : C y p
 *
 * KEY CONCEPTS
 * ------------
 *
 * UIP (Uniqueness of Identity Proofs):
 *   In F*, ALL equality proofs are equal. Given p, q : eq_type A x y,
 *   we can prove eq_type (eq_type A x y) p q. This is a consequence of
 *   F*'s Axiom K: all proofs of x = x are definitionally equal to Refl.
 *
 *   UIP is what makes F* an EXTENSIONAL type theory, unlike:
 *   - Coq (intensional, without UIP by default)
 *   - Agda (intensional, UIP via --without-K)
 *   - Lean (intensional, proof irrelevance is separate)
 *   - HoTT (no UIP - equality proofs form higher groupoids)
 *
 * Equality Reflection:
 *   F* reflects provable equalities into definitional equalities.
 *   If (x == y) is derivable in context, then x and y are interchangeable.
 *   This enables implicit type conversions based on equality proofs:
 *
 *     let f (#a #b:Type) (pf: a == b) (x:a) : b = x  (* valid in F* *)
 *
 * FUNCTIONAL EXTENSIONALITY CAVEAT
 * --------------------------------
 * Functional extensionality (funext) states:
 *   (forall x. f x == g x) ==> f == g
 *
 * This is ONLY partially valid in F*:
 *
 *   - Valid for eta-expanded functions: (fun x -> f x) == (fun x -> g x)
 *   - INVALID in general due to domain issues!
 *
 * Counterexample (from F* book):
 *   let f (x:nat) : int = 0
 *   let g (x:nat) : int = if x = 0 then 1 else 0
 *   (* f and g are pointwise equal on positive nats, but f 0 != g 0 *)
 *   (* Full funext would derive f == g from (forall x:pos. f x == g x) *)
 *   (* But then f 0 == g 0 which is false! *)
 *
 * Use FStar.FunctionalExtensionality for safe extensionality reasoning.
 *
 * MODULE CONTENTS
 * ---------------
 *   - Universe levels: Proper stratification (Type0 : Type1 : ... : omega)
 *   - Identity type: eq_type a x y with constructor Refl
 *   - Core operations: refl, subst, transport
 *   - Derived properties: sym, trans, cong
 *   - J-eliminator: Both Paulin-Mohring and Martin-Lof formulations
 *   - Heterogeneous equality: For type families (John Major equality)
 *   - UIP proofs: Demonstrating F*'s extensional nature
 *   - Leibniz equality: Alternative characterization
 *   - Path types: HoTT-style interface (alias for identity type)
 *   - Decidable equality: Typeclass for computational equality
 *
 * REFERENCES
 * ----------
 * [1] Martin-Lof, P. (1984). "Intuitionistic Type Theory"
 * [2] Hofmann, M., Streicher, T. (1998). "The Groupoid Interpretation of
 *     Type Theory" - Shows UIP is independent of MLTT
 * [3] HoTT Book (2013). "Homotopy Type Theory: Univalent Foundations"
 *     Chapters 1-2 cover identity types without UIP
 * [4] F* Book, Chapter "Equality" - F*'s extensional approach
 * [5] Barendregt, H. (1984). "The Lambda Calculus" - Alpha equivalence
 *
 * BRRR-LANG SPECIFICATION
 * -----------------------
 * This module addresses Gap #4 from brrr_lang_spec_v0.4.tex:
 * "Equality types MISSING - no propositional equality"
 *
 * Propositional equality enables:
 *   - GADTs with type refinement on pattern match
 *   - Type-safe coercions along equality proofs
 *   - Proof-carrying code with verified type transformations
 *   - Dependent pattern matching in the Brrr IR
 *
 * Follows HACL* interface patterns from Lib.IntTypes.fsti
 *)
module BrrrPropositionalEquality

(** Z3 solver options - conservative baseline following HACL* patterns *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes

(* =========================================================================
   SECTION 1: UNIVERSE LEVELS
   =========================================================================

   RUSSELL'S PARADOX AND UNIVERSE STRATIFICATION
   ---------------------------------------------
   Without universe stratification, we could define:
     R = { x | x not_in x }
   And ask: is R in R? This leads to contradiction.

   The solution is UNIVERSE STRATIFICATION:
     Type0 : Type1 : Type2 : ... : omega : omega+1 : ...

   Each Type_n contains types whose elements are "smaller" types.
   Type0 contains "small" types like int, bool, list nat.
   Type1 contains Type0 and types formed from Type0.
   And so on.

   F*'s UNIVERSE POLYMORPHISM
   --------------------------
   F* supports universe-polymorphic definitions:
     val id : #u:universe -> #a:Type u -> a -> a

   This allows the same definition to work at all universe levels.

   OUR REPRESENTATION
   ------------------
   We use a proper sum type rather than encoding omega as a large nat:

     type universe_level =
       | UFinite : nat -> universe_level       (* 0, 1, 2, ... *)
       | UOmega  : universe_level              (* omega *)
       | UOmegaPlus : nat -> universe_level    (* omega + n *)

   This avoids overflow issues and correctly represents transfinite ordinals.

   RELATION TO BRRR-LANG
   ---------------------
   Universe levels are needed for:
   - Ensuring type-of-type consistency
   - Proper polymorphism over types
   - Avoiding circularity in type definitions
   - Metatheoretic proofs about the type system

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

   THE IDENTITY TYPE: eq_type a x y
   --------------------------------
   A value of type (eq_type a x y) is a PROOF that x and y are equal.
   This is fundamentally different from a boolean test!

   COMPARISON WITH BOOLEAN EQUALITY
   --------------------------------
   Boolean equality (=):
     - Returns true or false
     - Only works on eqtype (types with decidable equality)
     - Computational: actually compares values at runtime
     - Example: (5 = 5) evaluates to `true : bool`

   Propositional equality (==) / eq_type:
     - Returns a TYPE whose inhabitants are proofs
     - Works on ANY type
     - Logical: proofs may not be computable
     - Example: Refl : eq_type int 5 5 (a proof term)

   WHY TWO NOTIONS?
   ----------------
   Consider a type like (int -> int). We cannot decide if two functions
   are equal (halting problem!), so no boolean equality exists. But we
   CAN prove specific functions equal using propositional equality:

     let f = fun x -> x + 0
     let g = fun x -> x
     (* Cannot compute: f = g  (no decidable equality) *)
     (* But CAN prove: eq_type (int -> int) f g using funext *)

   TYPING RULES
   ------------
   Formation:  A : Type    x : A    y : A
               ---------------------------
                  eq_type A x y : Type

   Introduction (Reflexivity):
                   x : A
               -----------------
               Refl : eq_type A x x

   Elimination (Substitution/Leibniz):
               p : eq_type A x y
               P : A -> Type
               px : P x
               -------------------
               subst p P px : P y

   The elimination rule says: if x equals y, then any property P
   that holds for x also holds for y. This is Leibniz's principle
   of "indiscernibility of identicals."

   COMPUTATION RULE (beta for identity)
   ------------------------------------
   When p is Refl, subst reduces:
     subst Refl P px  -->  px

   This is because when x = y by Refl, we have x definitionally equal
   to y, so P x is the same type as P y.

   F*'S SPECIAL TREATMENT
   ----------------------
   In F*, due to Axiom K and equality reflection:
   1. Any p : eq_type A x y forces x and y to be definitionally equal
   2. Any p : eq_type A x x is definitionally equal to Refl
   3. This makes F* an EXTENSIONAL type theory

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
   SECTION 5: EQUALITY LEMMAS (SMT-FRIENDLY FORM)
   =========================================================================

   WHY LEMMA FORM?
   ---------------
   F*'s SMT solver (Z3) works best with universally quantified implications.
   The Lemma effect wraps our proofs in the form SMT expects:

     Lemma (requires P) (ensures Q)  ~  forall. P ==> Q

   These lemmas provide the SAME theorems as the functions above, but
   in a form that F* can automatically use when discharging proof
   obligations to Z3.

   SMT PATTERNS
   ------------
   F* allows SMTPat annotations to control when lemmas are instantiated:

     val lemma : x:t -> Lemma (P x) [SMTPat (f x)]

   This tells Z3: "when you see (f x), try instantiating this lemma."
   We don't use patterns here to avoid excessive instantiation.

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
   SECTION 6: J-ELIMINATOR (Path Induction / Identity Elimination)
   =========================================================================

   THE J-ELIMINATOR
   ----------------
   The J-eliminator is the MOST GENERAL elimination principle for identity
   types. It says: to prove something about ALL equality proofs p : x = y,
   it suffices to prove it for Refl : x = x.

   There are two equivalent formulations:

   PAULIN-MOHRING FORMULATION (based at x)
   ---------------------------------------
     J : (C : (y:A) -> x = y -> Type) ->
         C x Refl ->
         (y:A) -> (p: x = y) -> C y p

   "Given a family C indexed by endpoints and proofs, and a base case
   at C x Refl, produce C y p for any y and any proof p : x = y."

   MARTIN-LOF FORMULATION (symmetric)
   ----------------------------------
     J_ML : (C : (x:A) -> (y:A) -> x = y -> Type) ->
            ((x:A) -> C x x Refl) ->
            (x y:A) -> (p: x = y) -> C x y p

   "Given a family C over all pairs and proofs, and a method to produce
   C x x Refl for any x, produce C x y p for any proof p."

   These are INTERDERIVABLE - having one gives you the other.

   WHY "PATH INDUCTION"?
   ---------------------
   In HoTT (Homotopy Type Theory), equality proofs are interpreted as
   PATHS in a space. The J-eliminator corresponds to the fact that
   any path can be continuously shrunk to a point (the reflexivity path).

   This is also called the "based path induction principle."

   EXAMPLE USES
   ------------
   - Proving symmetry: Use C(y, p) = eq_type A y x
   - Proving transitivity: Use C(y, p) = (eq_type A y z -> eq_type A x z)
   - Proving congruence: Use C(y, p) = eq_type B (f x) (f y)

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
   =========================================================================

   THE UIP PRINCIPLE
   -----------------
   UIP (Uniqueness of Identity Proofs) states that any two proofs of
   the same equality are themselves equal:

     forall (p q : eq_type A x y). eq_type (eq_type A x y) p q

   In plain language: there is at most one way to prove x equals y.

   INTENSIONAL vs EXTENSIONAL TYPE THEORIES
   ----------------------------------------
   This is a MAJOR dividing line in type theory:

   EXTENSIONAL (F*, some Coq modes):
     - UIP holds
     - Equality proofs don't matter computationally
     - Type checking may be undecidable
     - Equality reflection: provable equality implies definitional equality

   INTENSIONAL (Agda, Lean, standard Coq):
     - UIP is NOT provable (but can be assumed as axiom)
     - Equality proofs may carry computational content
     - Type checking is decidable
     - Proofs can be distinguished

   HOTT (Homotopy Type Theory):
     - UIP is FALSE for higher types!
     - Equality proofs form groupoids (or higher groupoids)
     - Leads to univalence axiom: equivalent types are equal
     - Much richer structure, but more complex

   F*'S AXIOM K
   ------------
   F* includes Axiom K (Streicher's axiom), which states:

     forall (p : eq_type A x x). eq_type (eq_type A x x) p Refl

   "All proofs of x = x are equal to Refl."

   From Axiom K, UIP follows (shown by Streicher, 1993).

   WHY UIP MATTERS
   ---------------
   1. SIMPLIFIES PROOFS: Don't need to track which equality proof was used
   2. ENABLES PROOF IRRELEVANCE: Proofs can be erased at extraction
   3. TRANSPORT IS TRIVIAL: subst p P px equals px when p is Refl
   4. NO COHERENCE HELL: Don't need to prove proofs are equal

   H-SETS AND DECIDABLE EQUALITY
   -----------------------------
   In HoTT terminology, types satisfying UIP are called "h-sets" or
   "0-truncated types." Notably:

   - Any type with DECIDABLE equality (eqtype) is an h-set
   - This includes: bool, int, nat, string, finite types
   - Functions are NOT h-sets in general (in HoTT)
   - In F* with UIP, ALL types are h-sets

   The proofs below demonstrate UIP for specific types and generically.

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
   SECTION 16: LEIBNIZ EQUALITY (Alternative Characterization)
   =========================================================================

   LEIBNIZ'S PRINCIPLE OF INDISCERNIBILITY OF IDENTICALS
   ------------------------------------------------------
   Gottfried Wilhelm Leibniz (1686) formulated:

     "If x = y, then every property of x is also a property of y"

   Formally: x = y  <=>  forall P. P(x) -> P(y)

   This gives an alternative definition of equality in terms of
   universal quantification over predicates.

   LEIBNIZ EQUALITY TYPE
   ---------------------
     leibniz_eq A x y = (P : A -> Type) -> P x -> P y

   A value of this type is a FUNCTION that transforms evidence of
   any property of x into evidence of that property for y.

   EQUIVALENCE WITH IDENTITY TYPE
   ------------------------------
   For "well-behaved" types, Leibniz equality is equivalent to the
   identity type:

     eq_to_leibniz : eq_type A x y -> leibniz_eq A x y
     leibniz_to_eq : leibniz_eq A x y -> eq_type A x y

   The first direction is immediate (use subst).
   The second uses leibniz_eq with P(z) = eq_type A x z.

   WHY TWO FORMULATIONS?
   ---------------------
   1. Identity type (Martin-Lof): Inductive definition, clear computation
   2. Leibniz equality: Impredicative, useful in System F and polymorphic settings

   In predicative type theories such as F-star, these are equivalent.
   In impredicative settings, Leibniz can sometimes be more flexible.

   ========================================================================= *)

(** Leibniz equality *)
unfold
let leibniz_eq (a: Type) (x y: a) = (p: a -> Type) -> p x -> p y

(** Identity type implies Leibniz *)
val eq_to_leibniz : #a:Type -> #x:a -> #y:a -> eq_type a x y -> leibniz_eq a x y

(** Leibniz implies identity (for types with J-elimination) *)
val leibniz_to_eq : #a:Type -> #x:a -> #y:a -> leibniz_eq a x y -> eq_type a x y

(* =========================================================================
   SECTION 17: PATH TYPES (Homotopy Type Theory Perspective)
   =========================================================================

   PATHS AS EQUALITY
   -----------------
   In Homotopy Type Theory (HoTT), equality proofs are interpreted as
   PATHS in a topological space:

     x ====p====> y     means    p : eq_type A x y

   The reflexivity proof Refl corresponds to the "identity path" (staying
   at a point), and the operations on equality correspond to path operations:

     Reflexivity  <->  Identity path (idpath)
     Symmetry     <->  Path reversal (inverse)
     Transitivity <->  Path concatenation (concat)
     Congruence   <->  Applying a map to a path (ap)

   PATH ALGEBRA
   ------------
   Paths satisfy algebraic laws that are familiar from group theory:

     concat (idpath x) p = p             (left unit)
     concat p (idpath y) = p             (right unit)
     concat (inverse p) p = idpath y     (left inverse)
     concat p (inverse p) = idpath x     (right inverse)
     concat (concat p q) r = concat p (concat q r)  (associativity)

   HIGHER STRUCTURE (Not present in F-star with UIP)
   ----------------------------
   In full HoTT (without UIP), equality proofs between equality proofs
   form a GROUPOID structure. This leads to:

     - 2-paths: proofs that two equality proofs are equal
     - 3-paths: proofs about 2-paths
     - And so on, forming infinity-groupoids

   This is NOT present in F* due to UIP - all equality proofs collapse.

   WHY PROVIDE PATH VOCABULARY?
   ----------------------------
   1. Familiar to HoTT practitioners
   2. Intuitive geometric interpretation
   3. Consistent with research literature
   4. Useful for equational reasoning patterns

   Note: In F* with UIP, path types are just aliases for identity types.
   The higher structure of HoTT is flattened.

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
   SECTION 18: AXIOM K (Streicher's Axiom)
   =========================================================================

   AXIOM K STATEMENT
   -----------------
   Axiom K (due to Thomas Streicher, 1993) states:

     forall A x (p : eq_type A x x). eq_type (eq_type A x x) p Refl

   In words: "Every proof that x equals itself is equal to reflexivity."

   This is a REFLECTION PRINCIPLE that collapses identity proofs.

   WHY "K"?
   --------
   The letter K was chosen arbitrarily by Streicher in his thesis.
   It's also called the "uniqueness of reflexivity" principle.

   RELATION TO UIP
   ---------------
   Axiom K implies UIP (but not vice versa in all systems):

     From K: p : x = x  implies p = Refl
     UIP follows: if p, q : x = y, then both equal Refl when viewed
                  as proofs of x = x (after substitution along p or q)

   INCOMPATIBILITY WITH UNIVALENCE
   -------------------------------
   In HoTT, the UNIVALENCE AXIOM states:

     (A = B)  <=>  (A <-> B)  (isomorphism of types)

   This makes equality much richer - there can be many distinct
   proofs that bool = bool (identity, negation, etc.).

   Axiom K is INCOMPATIBLE with univalence because it would force
   all type isomorphisms to be equal to the identity.

   F* CHOOSES AXIOM K
   ------------------
   F* includes Axiom K because:
   1. Simpler metatheory
   2. Decidable type equivalence (in most cases)
   3. Proof irrelevance for extraction
   4. Familiar programming model

   The tradeoff is losing the rich structure of HoTT.

   PATTERN MATCHING ON EQUALITY
   ----------------------------
   Axiom K enables pattern matching on equality proofs:

     match p with
     | Refl -> ...

   Without K, this pattern match might not be valid because p might
   not definitionally be Refl.

   ========================================================================= *)

(** Axiom K: all self-equalities are refl *)
assume val axiom_k : #a:Type -> x:a -> p:eq_type a x x ->
    eq_type (eq_type a x x) p (refl x)

(** Using K to pattern match on equality *)
val match_refl : #a:Type -> #x:a -> eq_type a x x -> result:Type -> result -> result
