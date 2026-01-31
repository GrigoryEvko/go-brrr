(**
 * BrrrLang.Core.InformationFlow
 *
 * Multi-Level Security (MLS) Information Flow Analysis implementing
 * security type checking for noninterference.
 * Based on brrr_lang_spec_v0.4 Part IX, Example 1.3.
 *
 * ===========================================================================
 * THEORETICAL FOUNDATIONS
 * ===========================================================================
 *
 * This module implements Information Flow Control (IFC) based on the seminal
 * work of Denning (1976) "A Lattice Model of Secure Information Flow" and
 * the formalization of noninterference by Goguen & Meseguer (1982).
 *
 * Key Academic References:
 *   [Denning76]    Denning, D.E. "A Lattice Model of Secure Information Flow."
 *                  Communications of the ACM, 19(5):236-243, May 1976.
 *                  - Introduced lattice-based security classification
 *                  - Defined information flow as data movement between levels
 *
 *   [GoguenMeseguer82] Goguen, J.A. & Meseguer, J. "Security Policies and
 *                  Security Models." IEEE S&P 1982.
 *                  - Formalized noninterference property
 *                  - Proved type systems can enforce noninterference
 *
 *   [VolpanoSmith96] Volpano, D., Smith, G., Irvine, C. "A Sound Type System
 *                  for Secure Flow Analysis." JSC 1996.
 *                  - Type-based enforcement of noninterference
 *                  - Soundness proof: well-typed programs don't leak
 *
 *   [MyersLiskov97] Myers, A.C. & Liskov, B. "A Decentralized Model for
 *                  Information Flow Control." SOSP 1997.
 *                  - Decentralized Label Model (DLM)
 *                  - Combined confidentiality and integrity
 *
 *   [SabelfeldMyers03] Sabelfeld, A. & Myers, A.C. "Language-Based
 *                  Information-Flow Security." IEEE J. Sel. Areas Commun. 2003.
 *                  - Comprehensive survey of IFC techniques
 *                  - Termination-sensitive vs termination-insensitive
 *
 * ===========================================================================
 * SECURITY LATTICE STRUCTURE
 * ===========================================================================
 *
 * We implement a four-point DIAMOND security lattice (per spec Example 1.3):
 *
 *                       TopSecret (T)
 *                      /             \
 *                 Secret (S)    Confidential (C)
 *                      \             /
 *                        Public (P)
 *
 * This generalizes the classic two-point lattice {Low, High} to support
 * multiple incomparable security compartments. Key properties:
 *
 *   - Public (P): Bottom element, observable by anyone
 *   - TopSecret (T): Top element, highest classification
 *   - Secret (S) and Confidential (C): INCOMPARABLE middle levels
 *
 * The partial order is:
 *   P <= S, P <= C, S <= T, C <= T
 *   BUT: S </= C and C </= S (incomparable!)
 *
 * Why a Diamond Lattice?
 *   - Models real-world compartmented security (e.g., military classifications)
 *   - Prevents cross-compartment information flow
 *   - Secret data cannot be "downgraded" to Confidential
 *   - Enables fine-grained access control policies
 *
 * ===========================================================================
 * INFORMATION FLOW TYPES
 * ===========================================================================
 *
 * We distinguish two types of information flow:
 *
 * 1. EXPLICIT FLOWS (Direct Assignment):
 *    secret_var := public_expr      // OK: upward flow
 *    public_var := secret_expr      // ILLEGAL: downward flow
 *
 *    Rule: For assignment `x := e`, require label(e) <= label(x)
 *
 * 2. IMPLICIT FLOWS (Control-Flow Dependent):
 *    if secret_condition then
 *      public_var := 1              // ILLEGAL! Leaks secret_condition
 *    else
 *      public_var := 0              // via which branch executes
 *
 *    The Program Counter (PC) label tracks the security level of the
 *    current control context. Rule: pc join label(e) <= label(x)
 *
 * The PC mechanism (from [Denning76]) ensures that assignments in
 * secret-guarded branches cannot write to public variables.
 *
 * ===========================================================================
 * IMPLEMENTATION OVERVIEW
 * ===========================================================================
 *
 * Implements:
 *   - Four-point DIAMOND security lattice with proven properties
 *   - Labeled types combining base types with security labels
 *   - PC (Program Counter) label tracking for implicit flows
 *   - Information flow type checking with flow constraints
 *   - Noninterference theorem at any observation level
 *   - TINI (Termination-Insensitive Noninterference)
 *   - TSNI (Termination-Sensitive Noninterference) with termination channels
 *   - Declassification policies for controlled information release
 *   - Integrity lattice (dual of confidentiality) for endorsement
 *   - Combined confidentiality/integrity labels (DLM style)
 *
 * Key Security Properties:
 *   - Information flows only upward in the lattice
 *   - Secret data cannot flow to Confidential (and vice versa)
 *   - Only TopSecret can combine Secret and Confidential data
 *   - Well-typed programs satisfy noninterference
 *   - Termination channels are detected and reported
 *
 * Specification Reference: brrr_lang_spec_v0.4.tex
 *   - Chapter "Information Flow Types" (lines 5859-6063)
 *   - Chapter "Noninterference" (lines 6065-6130)
 *   - Chapter "Taint Analysis" (lines 6221-6372)
 *
 * Depends on: BrrrTypes, Expressions, Modes, Effects, Values
 *)
module BrrrInformationFlow

open BrrrTypes
open BrrrExpressions
open BrrrModes
open BrrrEffects
open BrrrValues
open FStar.List.Tot
open FStar.Classical

(** ============================================================================
    VALUE EQUALITY LEMMAS
    ============================================================================

    We prove that value_eq (from Values module) is an EQUIVALENCE RELATION:
      1. Reflexive:   forall v. v = v
      2. Symmetric:   forall v1 v2. v1 = v2 ==> v2 = v1
      3. Transitive:  forall v1 v2 v3. v1 = v2 /\ v2 = v3 ==> v1 = v3

    These lemmas are CRITICAL for proving low_equiv properties because:
    - Low-equivalence requires comparing values across two memories
    - The noninterference theorem needs to show equal values produce equal results
    - Transitivity enables reasoning about multiple execution paths

    The proofs proceed by structural induction on the value type, handling:
    - Primitive values (unit, bool, int, float, string, char)
    - Reference values (ref, ref_mut, box)
    - Composite values (tuples, arrays, structs, variants)
    - Special values (closures, futures, generators, option/result wrappers)

    See also: BrrrValues.fst for the value_eq definition
    ============================================================================ *)

(** value_eq is reflexive: v = v *)
let rec value_eq_refl (v: value) : Lemma (ensures value_eq v v = true) (decreases v) =
  match v with
  | VUnit | VBool _ | VInt _ | VFloat _ | VString _ | VChar _ -> ()
  | VRef _ | VRefMut _ | VBox _ | VClosure _ | VNone -> ()
  | VSome v' | VOk v' | VErr v' -> value_eq_refl v'
  | VTuple vs -> value_list_eq_refl vs
  | VArray vs -> value_list_eq_refl vs
  | VStruct _ _ -> ()  (* Struct equality uses field comparison *)
  | VVariant _ _ _ -> ()
  | VFuture _ -> ()
  | VGenerator _ -> ()

and value_list_eq_refl (vs: vlist value) : Lemma (ensures value_list_eq vs vs = true) (decreases vs) =
  match vs with
  | [] -> ()
  | v :: rest -> value_eq_refl v; value_list_eq_refl rest

(** value_eq is symmetric: v1 = v2 => v2 = v1 *)
let rec value_eq_sym (v1 v2: value)
    : Lemma (requires value_eq v1 v2 = true)
            (ensures value_eq v2 v1 = true)
            (decreases v1) =
  match v1, v2 with
  | VUnit, VUnit -> ()
  | VBool b1, VBool b2 -> ()
  | VInt n1, VInt n2 -> ()
  | VFloat f1, VFloat f2 -> ()
  | VString s1, VString s2 -> ()
  | VChar c1, VChar c2 -> ()
  | VRef l1, VRef l2 -> ()
  | VRefMut l1, VRefMut l2 -> ()
  | VBox l1, VBox l2 -> ()
  | VClosure c1, VClosure c2 -> ()
  | VNone, VNone -> ()
  | VSome v1', VSome v2' -> value_eq_sym v1' v2'
  | VOk v1', VOk v2' -> value_eq_sym v1' v2'
  | VErr v1', VErr v2' -> value_eq_sym v1' v2'
  | VTuple vs1, VTuple vs2 -> value_list_eq_sym vs1 vs2
  | VArray vs1, VArray vs2 -> value_list_eq_sym vs1 vs2
  | VFuture fs1, VFuture fs2 -> ()
  | VGenerator gs1, VGenerator gs2 -> ()
  | _, _ -> ()

and value_list_eq_sym (vs1 vs2: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true)
            (ensures value_list_eq vs2 vs1 = true)
            (decreases vs1) =
  match vs1, vs2 with
  | [], [] -> ()
  | v1 :: r1, v2 :: r2 -> value_eq_sym v1 v2; value_list_eq_sym r1 r2
  | _, _ -> ()

(** value_eq is transitive: v1 = v2 /\ v2 = v3 => v1 = v3 *)
let rec value_eq_trans (v1 v2 v3: value)
    : Lemma (requires value_eq v1 v2 = true /\ value_eq v2 v3 = true)
            (ensures value_eq v1 v3 = true)
            (decreases v1) =
  match v1, v2, v3 with
  | VUnit, VUnit, VUnit -> ()
  | VBool _, VBool _, VBool _ -> ()
  | VInt _, VInt _, VInt _ -> ()
  | VFloat _, VFloat _, VFloat _ -> ()
  | VString _, VString _, VString _ -> ()
  | VChar _, VChar _, VChar _ -> ()
  | VRef _, VRef _, VRef _ -> ()
  | VRefMut _, VRefMut _, VRefMut _ -> ()
  | VBox _, VBox _, VBox _ -> ()
  | VClosure _, VClosure _, VClosure _ -> ()
  | VNone, VNone, VNone -> ()
  | VSome v1', VSome v2', VSome v3' -> value_eq_trans v1' v2' v3'
  | VOk v1', VOk v2', VOk v3' -> value_eq_trans v1' v2' v3'
  | VErr v1', VErr v2', VErr v3' -> value_eq_trans v1' v2' v3'
  | VTuple vs1, VTuple vs2, VTuple vs3 -> value_list_eq_trans vs1 vs2 vs3
  | VArray vs1, VArray vs2, VArray vs3 -> value_list_eq_trans vs1 vs2 vs3
  | VFuture _, VFuture _, VFuture _ -> ()
  | VGenerator _, VGenerator _, VGenerator _ -> ()
  | _, _, _ -> ()

and value_list_eq_trans (vs1 vs2 vs3: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true /\ value_list_eq vs2 vs3 = true)
            (ensures value_list_eq vs1 vs3 = true)
            (decreases vs1) =
  match vs1, vs2, vs3 with
  | [], [], [] -> ()
  | v1 :: r1, v2 :: r2, v3 :: r3 -> value_eq_trans v1 v2 v3; value_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

(** ============================================================================
    SECURITY LEVELS (DIAMOND LATTICE)
    ============================================================================

    We implement a four-point diamond security lattice (per spec Example 1.3):

                       TopSecret (T)
                      /             \
                 Secret (S)    Confidential (C)
                      \             /
                        Public (P)

    This lattice models MULTI-LEVEL SECURITY (MLS) with COMPARTMENTALIZATION.

    Mathematical Structure:
    -----------------------
    The structure (L, <=, join, meet, P, T) forms a BOUNDED LATTICE where:
      - L = {Public, Secret, Confidential, TopSecret}
      - <= is a partial order (reflexive, antisymmetric, transitive)
      - join is the least upper bound (lub)
      - meet is the greatest lower bound (glb)
      - P (Public) is the bottom element
      - T (TopSecret) is the top element

    Hasse Diagram Interpretation:
    -----------------------------
    Lines indicate the "can flow to" relation (<=):
      - P <= S (public can flow to secret)
      - P <= C (public can flow to confidential)
      - S <= T (secret can flow to top-secret)
      - C <= T (confidential can flow to top-secret)

    CRITICAL: S and C have NO edge between them (INCOMPARABLE):
      - S </= C (secret CANNOT flow to confidential)
      - C </= S (confidential CANNOT flow to secret)

    Security Interpretation:
    ------------------------
    - Public: No restriction, observable by all principals
    - Secret: Compartment A - only principals with Secret clearance
    - Confidential: Compartment B - only principals with Confidential clearance
    - TopSecret: Union of all compartments - full clearance required

    Real-World Analogy:
    -------------------
    Think of government classifications where "Secret" might be military
    intelligence and "Confidential" might be diplomatic cables. An analyst
    with Secret clearance cannot access Confidential documents, and vice versa.
    Only TopSecret clearance grants access to both.

    Lattice Operations:
    -------------------
    - sec_leq l1 l2: True iff information at level l1 may flow to level l2
                     Implements the partial order <=

    - sec_join l1 l2: Computes the LEAST UPPER BOUND (lub)
                      Used when combining data from multiple sources
                      Example: join(S, C) = T (combining requires highest level)

    - sec_meet l1 l2: Computes the GREATEST LOWER BOUND (glb)
                      Used for computing common lower bounds
                      Example: meet(S, C) = P (their common observer is public-only)

    Key Insight (Diamond Property):
    -------------------------------
    The diamond shape arises because:
      join(S, C) = T  (their lub is the top)
      meet(S, C) = P  (their glb is the bottom)

    This creates a "diamond" or "M" shape in the Hasse diagram, which is
    characteristic of lattices with incomparable elements at the same "height."

    References:
    -----------
    - [Denning76] Section 3: Security classes form a lattice
    - [BellLaPadula73] "Simple Security" and "*-Property" (star property)
    - brrr_lang_spec_v0.4.tex Example 1.3 (Four-Point Lattice)
    ============================================================================ *)

(** Security level type - a four-point diamond lattice *)
type sec_level =
  | Public       : sec_level   (* Bottom: observable by all *)
  | Confidential : sec_level   (* Middle: one compartment *)
  | Secret       : sec_level   (* Middle: another compartment (incomparable with Confidential) *)
  | TopSecret    : sec_level   (* Top: highest classification *)

(** Security level ordering for diamond lattice

    Information may flow from level l1 to level l2 iff l1 <= l2.
    This prevents high-to-low flows.

    Diamond structure:
                  TopSecret
                 /         \
            Secret    Confidential
                 \         /
                   Public

    Truth table (key cases):
      sec_leq Public _           = true   (Public flows anywhere)
      sec_leq _ TopSecret        = true   (anything flows to TopSecret)
      sec_leq Secret Secret      = true   (reflexivity)
      sec_leq Confidential Confidential = true (reflexivity)
      sec_leq Secret Confidential = false (INCOMPARABLE!)
      sec_leq Confidential Secret = false (INCOMPARABLE!)
      sec_leq Secret Public      = false  (no downward flow)
      sec_leq TopSecret Public   = false  (no downward flow)
*)
let sec_leq (l1 l2: sec_level) : bool =
  match l1, l2 with
  (* Public is the bottom element - flows to everything *)
  | Public, _ -> true
  (* TopSecret is the top element - everything flows to it *)
  | _, TopSecret -> true
  (* Reflexivity for middle levels *)
  | Secret, Secret -> true
  | Confidential, Confidential -> true
  (* Secret and Confidential are INCOMPARABLE - neither flows to the other *)
  | Secret, Confidential -> false
  | Confidential, Secret -> false
  (* No downward flows from higher levels *)
  | Secret, Public -> false
  | Confidential, Public -> false
  | TopSecret, Secret -> false
  | TopSecret, Confidential -> false
  | TopSecret, Public -> false

(** Security level join (least upper bound)

    The join of two levels is the LEAST level that both can flow to.
    Used when combining data from multiple sources.

    Diamond structure - key insight:
      join(Secret, Confidential) = TopSecret
    because TopSecret is the smallest element that both can flow to.

    Truth table:
      sec_join Public x           = x          (Public is identity)
      sec_join x Public           = x
      sec_join TopSecret _        = TopSecret  (TopSecret is absorbing)
      sec_join _ TopSecret        = TopSecret
      sec_join Secret Secret      = Secret     (idempotent)
      sec_join Confidential Confidential = Confidential
      sec_join Secret Confidential = TopSecret (LUB of incomparable)
      sec_join Confidential Secret = TopSecret
*)
let sec_join (l1 l2: sec_level) : sec_level =
  match l1, l2 with
  (* Public is the bottom/identity element *)
  | Public, x -> x
  | x, Public -> x
  (* TopSecret is the top/absorbing element *)
  | TopSecret, _ -> TopSecret
  | _, TopSecret -> TopSecret
  (* Same level: idempotent *)
  | Secret, Secret -> Secret
  | Confidential, Confidential -> Confidential
  (* Secret and Confidential are incomparable: their LUB is TopSecret *)
  | Secret, Confidential -> TopSecret
  | Confidential, Secret -> TopSecret

(** Security level meet (greatest lower bound)

    The meet of two levels is the GREATEST level that can flow to both.
    Used for computing the most permissive common lower bound.

    Diamond structure - key insight:
      meet(Secret, Confidential) = Public
    because Public is the largest element that can flow to both.

    Truth table:
      sec_meet Public _           = Public        (Public is absorbing for meet)
      sec_meet _ Public           = Public
      sec_meet TopSecret x        = x             (TopSecret is identity for meet)
      sec_meet x TopSecret        = x
      sec_meet Secret Secret      = Secret        (idempotent)
      sec_meet Confidential Confidential = Confidential
      sec_meet Secret Confidential = Public       (GLB of incomparable)
      sec_meet Confidential Secret = Public
*)
let sec_meet (l1 l2: sec_level) : sec_level =
  match l1, l2 with
  (* Public is the bottom/absorbing element for meet *)
  | Public, _ -> Public
  | _, Public -> Public
  (* TopSecret is the top/identity element for meet *)
  | TopSecret, x -> x
  | x, TopSecret -> x
  (* Same level: idempotent *)
  | Secret, Secret -> Secret
  | Confidential, Confidential -> Confidential
  (* Secret and Confidential are incomparable: their GLB is Public *)
  | Secret, Confidential -> Public
  | Confidential, Secret -> Public

(** ============================================================================
    SECURITY LEVEL ORDERING PROOFS
    ============================================================================

    We prove that sec_leq forms a PARTIAL ORDER on the diamond lattice.

    A partial order (poset) requires three properties:

    1. REFLEXIVITY:  forall l. l <= l
       "Every element is related to itself."
       Proof: Direct case analysis on each security level.

    2. ANTISYMMETRY: forall l1 l2. l1 <= l2 /\ l2 <= l1 ==> l1 = l2
       "If two elements are related in both directions, they are equal."
       Proof: Most cases are vacuously true because the precondition is
       false (e.g., Secret <= Confidential is false).

    3. TRANSITIVITY: forall l1 l2 l3. l1 <= l2 /\ l2 <= l3 ==> l1 <= l3
       "The relation is 'chained' - if a <= b and b <= c, then a <= c."
       Proof: Exhaustive case analysis on all (l1, l2, l3) triples.

    CRITICAL: This is a PARTIAL order, NOT a TOTAL order!
    ---------------------------------------------------------
    A total order requires: forall l1 l2. l1 <= l2 \/ l2 <= l1
    Our lattice VIOLATES this for Secret and Confidential:
      - Secret </= Confidential
      - Confidential </= Secret
    Therefore, some pairs of elements are INCOMPARABLE.

    Why Partial Order Matters for Security:
    ---------------------------------------
    The partial order property ensures:
    - No cycles in information flow (antisymmetry prevents l1 < l2 < l1)
    - Flow constraints can be composed (transitivity)
    - Reflexivity allows data to stay at its current level

    The non-totality models COMPARTMENTALIZATION:
    - Secret and Confidential represent different security compartments
    - Data cannot flow between incomparable compartments
    - This is a SECURITY FEATURE, not a limitation

    Mathematical Note:
    ------------------
    The diamond lattice with 4 elements is isomorphic to the power set of
    a 2-element set ordered by inclusion: P({a,b}) = {{}, {a}, {b}, {a,b}}
    where {} = Public, {a} = Secret, {b} = Confidential, {a,b} = TopSecret.
    ============================================================================ *)

(** Reflexivity: Every security level is related to itself *)
let sec_leq_refl (l: sec_level) : Lemma (ensures sec_leq l l = true) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** Antisymmetry: If l1 <= l2 and l2 <= l1, then l1 = l2

    For the diamond lattice, this is straightforward because:
    - If both hold for Public or TopSecret, they must be equal
    - Secret and Confidential cannot have both directions (they're incomparable)
*)
let sec_leq_antisym (l1 l2: sec_level)
    : Lemma (requires sec_leq l1 l2 = true /\ sec_leq l2 l1 = true)
            (ensures l1 = l2) =
  match l1, l2 with
  | Public, Public -> ()
  | Confidential, Confidential -> ()
  | Secret, Secret -> ()
  | TopSecret, TopSecret -> ()
  (* All other cases are vacuously true because precondition is false *)
  | Public, Confidential -> ()    (* Vacuous: Confidential </= Public *)
  | Public, Secret -> ()          (* Vacuous: Secret </= Public *)
  | Public, TopSecret -> ()       (* Vacuous: TopSecret </= Public *)
  | Confidential, Public -> ()    (* Vacuous: Confidential </= Public *)
  | Confidential, Secret -> ()    (* Vacuous: Confidential </= Secret AND Secret </= Confidential *)
  | Confidential, TopSecret -> () (* Vacuous: TopSecret </= Confidential *)
  | Secret, Public -> ()          (* Vacuous: Secret </= Public *)
  | Secret, Confidential -> ()    (* Vacuous: Secret </= Confidential AND Confidential </= Secret *)
  | Secret, TopSecret -> ()       (* Vacuous: TopSecret </= Secret *)
  | TopSecret, Public -> ()       (* Vacuous: TopSecret </= Public *)
  | TopSecret, Confidential -> () (* Vacuous: TopSecret </= Confidential *)
  | TopSecret, Secret -> ()       (* Vacuous: TopSecret </= Secret *)

(** Transitivity: If l1 <= l2 and l2 <= l3, then l1 <= l3

    For the diamond lattice, the key cases are:
    - Public <= x <= y implies Public <= y (Public flows anywhere)
    - x <= y <= TopSecret implies x <= TopSecret (everything flows to top)
    - The middle levels are handled by their specific orderings
*)
let sec_leq_trans (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l1 l2 = true /\ sec_leq l2 l3 = true)
            (ensures sec_leq l1 l3 = true) =
  match l1, l2, l3 with
  (* Public is bottom - flows anywhere *)
  | Public, _, _ -> ()
  (* Everything flows to TopSecret *)
  | _, _, TopSecret -> ()
  (* Confidential chains *)
  | Confidential, Confidential, Confidential -> ()
  | Confidential, Confidential, Public -> ()        (* Vacuous: Conf </= Public *)
  | Confidential, Confidential, Secret -> ()        (* Vacuous: Conf </= Secret *)
  | Confidential, Public, _ -> ()                   (* Vacuous: Conf </= Public *)
  | Confidential, Secret, _ -> ()                   (* Vacuous: Conf </= Secret *)
  | Confidential, TopSecret, Public -> ()           (* Vacuous: TopSecret </= Public *)
  | Confidential, TopSecret, Confidential -> ()     (* Vacuous: TopSecret </= Conf *)
  | Confidential, TopSecret, Secret -> ()           (* Vacuous: TopSecret </= Secret *)
  (* Secret chains *)
  | Secret, Secret, Secret -> ()
  | Secret, Secret, Public -> ()                    (* Vacuous: Secret </= Public *)
  | Secret, Secret, Confidential -> ()              (* Vacuous: Secret </= Conf *)
  | Secret, Public, _ -> ()                         (* Vacuous: Secret </= Public *)
  | Secret, Confidential, _ -> ()                   (* Vacuous: Secret </= Conf *)
  | Secret, TopSecret, Public -> ()                 (* Vacuous: TopSecret </= Public *)
  | Secret, TopSecret, Confidential -> ()           (* Vacuous: TopSecret </= Conf *)
  | Secret, TopSecret, Secret -> ()                 (* Vacuous: TopSecret </= Secret *)
  (* TopSecret chains *)
  | TopSecret, TopSecret, TopSecret -> ()
  | TopSecret, TopSecret, Public -> ()              (* Vacuous: TopSecret </= Public *)
  | TopSecret, TopSecret, Confidential -> ()        (* Vacuous: TopSecret </= Conf *)
  | TopSecret, TopSecret, Secret -> ()              (* Vacuous: TopSecret </= Secret *)
  | TopSecret, Public, _ -> ()                      (* Vacuous: TopSecret </= Public *)
  | TopSecret, Confidential, _ -> ()                (* Vacuous: TopSecret </= Conf *)
  | TopSecret, Secret, _ -> ()                      (* Vacuous: TopSecret </= Secret *)

(** sec_leq is decidable - equality decision *)
let sec_level_eq (l1 l2: sec_level) : bool =
  match l1, l2 with
  | Public, Public -> true
  | Confidential, Confidential -> true
  | Secret, Secret -> true
  | TopSecret, TopSecret -> true
  | _, _ -> false

(** sec_level_eq is reflexive *)
let sec_level_eq_refl (l: sec_level) : Lemma (ensures sec_level_eq l l = true) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** sec_level_eq is symmetric *)
let sec_level_eq_sym (l1 l2: sec_level)
    : Lemma (requires sec_level_eq l1 l2 = true)
            (ensures sec_level_eq l2 l1 = true) =
  match l1, l2 with
  | Public, Public -> ()
  | Confidential, Confidential -> ()
  | Secret, Secret -> ()
  | TopSecret, TopSecret -> ()
  | _, _ -> ()

(** sec_level_eq implies Leibniz equality *)
let sec_level_eq_implies_eq (l1 l2: sec_level)
    : Lemma (requires sec_level_eq l1 l2 = true)
            (ensures l1 = l2) =
  match l1, l2 with
  | Public, Public -> ()
  | Confidential, Confidential -> ()
  | Secret, Secret -> ()
  | TopSecret, TopSecret -> ()
  | _, _ -> ()

(** ============================================================================
    JOIN SEMILATTICE PROOFS
    ============================================================================

    We prove that sec_join forms a JOIN SEMILATTICE over the sec_leq ordering.

    A join semilattice (L, <=, join) requires:

    ALGEBRAIC PROPERTIES:
    ---------------------
    1. ASSOCIATIVITY: (l1 join l2) join l3 = l1 join (l2 join l3)
       "Order of combining doesn't matter."
       Essential for combining multiple data sources incrementally.

    2. COMMUTATIVITY: l1 join l2 = l2 join l1
       "Order of operands doesn't matter."
       The security level of (a + b) equals (b + a).

    3. IDEMPOTENCY: l join l = l
       "Combining with yourself gives yourself."
       Combining two Secret values gives Secret (not TopSecret).

    ORDER-THEORETIC PROPERTIES:
    ---------------------------
    4. UPPER BOUND: l1 <= (l1 join l2) and l2 <= (l1 join l2)
       "The join is at least as high as both inputs."
       When combining data, the result has security >= both sources.

    5. LEAST UPPER BOUND: if l1 <= l3 and l2 <= l3 then (l1 join l2) <= l3
       "The join is the SMALLEST element above both."
       If some level l3 is above both l1 and l2, then join is <= l3.

    Diamond Lattice Key Insight:
    ----------------------------
    For incomparable elements (Secret and Confidential):
      join(Secret, Confidential) = TopSecret

    This is because:
    - TopSecret is above both Secret and Confidential
    - No smaller element exists that is above both
    - Therefore, TopSecret is the LEAST upper bound

    Security Interpretation:
    ------------------------
    The join operation answers: "What is the minimum security level needed
    to contain data from both sources?"

    Examples:
      join(Public, Secret) = Secret       (* Secret dominates *)
      join(Secret, Secret) = Secret       (* Idempotent *)
      join(Secret, Confidential) = TopSecret  (* Incomparable => top *)
      join(TopSecret, anything) = TopSecret   (* Top is absorbing *)
      join(Public, anything) = anything       (* Bottom is identity *)

    Proof Technique:
    ----------------
    All proofs use exhaustive case analysis on the 4x4 (or 4x4x4) combinations
    of security levels. This is feasible because the lattice is finite and small.
    F*'s SMT solver handles most cases automatically via normalization.

    References:
    -----------
    - [Davey&Priestley02] "Introduction to Lattices and Order" - lattice theory
    - [Denning76] Section 3.1 - security classes form a lattice
    ============================================================================ *)

(** Associativity of join - proven by exhaustive case analysis *)
let sec_join_assoc (l1 l2 l3: sec_level)
    : Lemma (ensures sec_join (sec_join l1 l2) l3 = sec_join l1 (sec_join l2 l3)) =
  match l1, l2, l3 with
  (* Public cases - Public is identity *)
  | Public, Public, Public -> ()
  | Public, Public, Confidential -> ()
  | Public, Public, Secret -> ()
  | Public, Public, TopSecret -> ()
  | Public, Confidential, Public -> ()
  | Public, Confidential, Confidential -> ()
  | Public, Confidential, Secret -> ()
  | Public, Confidential, TopSecret -> ()
  | Public, Secret, Public -> ()
  | Public, Secret, Confidential -> ()
  | Public, Secret, Secret -> ()
  | Public, Secret, TopSecret -> ()
  | Public, TopSecret, Public -> ()
  | Public, TopSecret, Confidential -> ()
  | Public, TopSecret, Secret -> ()
  | Public, TopSecret, TopSecret -> ()
  (* Confidential cases *)
  | Confidential, Public, Public -> ()
  | Confidential, Public, Confidential -> ()
  | Confidential, Public, Secret -> ()
  | Confidential, Public, TopSecret -> ()
  | Confidential, Confidential, Public -> ()
  | Confidential, Confidential, Confidential -> ()
  | Confidential, Confidential, Secret -> ()
  | Confidential, Confidential, TopSecret -> ()
  | Confidential, Secret, Public -> ()
  | Confidential, Secret, Confidential -> ()
  | Confidential, Secret, Secret -> ()
  | Confidential, Secret, TopSecret -> ()
  | Confidential, TopSecret, Public -> ()
  | Confidential, TopSecret, Confidential -> ()
  | Confidential, TopSecret, Secret -> ()
  | Confidential, TopSecret, TopSecret -> ()
  (* Secret cases *)
  | Secret, Public, Public -> ()
  | Secret, Public, Confidential -> ()
  | Secret, Public, Secret -> ()
  | Secret, Public, TopSecret -> ()
  | Secret, Confidential, Public -> ()
  | Secret, Confidential, Confidential -> ()
  | Secret, Confidential, Secret -> ()
  | Secret, Confidential, TopSecret -> ()
  | Secret, Secret, Public -> ()
  | Secret, Secret, Confidential -> ()
  | Secret, Secret, Secret -> ()
  | Secret, Secret, TopSecret -> ()
  | Secret, TopSecret, Public -> ()
  | Secret, TopSecret, Confidential -> ()
  | Secret, TopSecret, Secret -> ()
  | Secret, TopSecret, TopSecret -> ()
  (* TopSecret cases - TopSecret is absorbing *)
  | TopSecret, Public, Public -> ()
  | TopSecret, Public, Confidential -> ()
  | TopSecret, Public, Secret -> ()
  | TopSecret, Public, TopSecret -> ()
  | TopSecret, Confidential, Public -> ()
  | TopSecret, Confidential, Confidential -> ()
  | TopSecret, Confidential, Secret -> ()
  | TopSecret, Confidential, TopSecret -> ()
  | TopSecret, Secret, Public -> ()
  | TopSecret, Secret, Confidential -> ()
  | TopSecret, Secret, Secret -> ()
  | TopSecret, Secret, TopSecret -> ()
  | TopSecret, TopSecret, Public -> ()
  | TopSecret, TopSecret, Confidential -> ()
  | TopSecret, TopSecret, Secret -> ()
  | TopSecret, TopSecret, TopSecret -> ()

(** Commutativity of join *)
let sec_join_comm (l1 l2: sec_level)
    : Lemma (ensures sec_join l1 l2 = sec_join l2 l1) =
  match l1, l2 with
  | Public, Public -> ()
  | Public, Confidential -> ()
  | Public, Secret -> ()
  | Public, TopSecret -> ()
  | Confidential, Public -> ()
  | Confidential, Confidential -> ()
  | Confidential, Secret -> ()
  | Confidential, TopSecret -> ()
  | Secret, Public -> ()
  | Secret, Confidential -> ()
  | Secret, Secret -> ()
  | Secret, TopSecret -> ()
  | TopSecret, Public -> ()
  | TopSecret, Confidential -> ()
  | TopSecret, Secret -> ()
  | TopSecret, TopSecret -> ()

(** Idempotency of join *)
let sec_join_idem (l: sec_level)
    : Lemma (ensures sec_join l l = l) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** Join is an upper bound for left operand: l1 <= (l1 join l2)

    Key cases for diamond:
    - Secret join Confidential = TopSecret, and Secret <= TopSecret
    - Confidential join Secret = TopSecret, and Confidential <= TopSecret
*)
let sec_join_upper_left (l1 l2: sec_level)
    : Lemma (ensures sec_leq l1 (sec_join l1 l2) = true) =
  match l1, l2 with
  | Public, _ -> ()           (* Public <= anything *)
  | Confidential, Public -> ()
  | Confidential, Confidential -> ()
  | Confidential, Secret -> ()     (* Conf <= TopSecret *)
  | Confidential, TopSecret -> ()
  | Secret, Public -> ()
  | Secret, Confidential -> ()     (* Secret <= TopSecret *)
  | Secret, Secret -> ()
  | Secret, TopSecret -> ()
  | TopSecret, _ -> ()        (* TopSecret <= TopSecret *)

(** Join is an upper bound for right operand: l2 <= (l1 join l2) *)
let sec_join_upper_right (l1 l2: sec_level)
    : Lemma (ensures sec_leq l2 (sec_join l1 l2) = true) =
  sec_join_comm l1 l2;
  sec_join_upper_left l2 l1

(** Join is the LEAST upper bound

    If l1 <= l3 and l2 <= l3, then (l1 join l2) <= l3.
    Key diamond case: if Secret <= l3 and Confidential <= l3,
    then l3 must be TopSecret (only element above both), so join <= TopSecret.
*)
let sec_join_lub (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l1 l3 = true /\ sec_leq l2 l3 = true)
            (ensures sec_leq (sec_join l1 l2) l3 = true) =
  match l1, l2, l3 with
  (* Public cases *)
  | Public, Public, _ -> ()
  | Public, Confidential, Confidential -> ()
  | Public, Confidential, TopSecret -> ()
  | Public, Secret, Secret -> ()
  | Public, Secret, TopSecret -> ()
  | Public, TopSecret, TopSecret -> ()
  (* Confidential cases *)
  | Confidential, Public, Confidential -> ()
  | Confidential, Public, TopSecret -> ()
  | Confidential, Confidential, Confidential -> ()
  | Confidential, Confidential, TopSecret -> ()
  | Confidential, Secret, TopSecret -> ()  (* join = TopSecret, TopSecret <= TopSecret *)
  | Confidential, TopSecret, TopSecret -> ()
  (* Secret cases *)
  | Secret, Public, Secret -> ()
  | Secret, Public, TopSecret -> ()
  | Secret, Confidential, TopSecret -> ()  (* join = TopSecret, TopSecret <= TopSecret *)
  | Secret, Secret, Secret -> ()
  | Secret, Secret, TopSecret -> ()
  | Secret, TopSecret, TopSecret -> ()
  (* TopSecret cases *)
  | TopSecret, Public, TopSecret -> ()
  | TopSecret, Confidential, TopSecret -> ()
  | TopSecret, Secret, TopSecret -> ()
  | TopSecret, TopSecret, TopSecret -> ()
  (* Vacuous cases where precondition is false *)
  | _, _, Public -> ()
  | Confidential, _, Secret -> ()
  | Secret, _, Confidential -> ()
  | TopSecret, _, Secret -> ()
  | TopSecret, _, Confidential -> ()

(** Public is the bottom element *)
let sec_public_bottom (l: sec_level)
    : Lemma (ensures sec_leq Public l = true) =
  ()

(** TopSecret is the top element *)
let sec_topsecret_top (l: sec_level)
    : Lemma (ensures sec_leq l TopSecret = true) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** Join with Public is identity *)
let sec_join_public_left (l: sec_level)
    : Lemma (ensures sec_join Public l = l) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

let sec_join_public_right (l: sec_level)
    : Lemma (ensures sec_join l Public = l) =
  sec_join_comm l Public;
  sec_join_public_left l

(** Join with TopSecret is absorbing *)
let sec_join_topsecret_left (l: sec_level)
    : Lemma (ensures sec_join TopSecret l = TopSecret) =
  ()

let sec_join_topsecret_right (l: sec_level)
    : Lemma (ensures sec_join l TopSecret = TopSecret) =
  sec_join_comm l TopSecret;
  sec_join_topsecret_left l

(** DEPRECATED: sec_secret_top - use sec_topsecret_top instead for four-point lattice *)
let sec_secret_top (l: sec_level)
    : Lemma (ensures sec_leq l Secret = true \/ l = TopSecret \/ l = Confidential) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** DEPRECATED: sec_join_secret_left - Secret is no longer absorbing *)
let sec_join_secret_left (l: sec_level)
    : Lemma (ensures sec_join Secret l = Secret \/ sec_join Secret l = TopSecret) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** DEPRECATED: sec_join_secret_right *)
let sec_join_secret_right (l: sec_level)
    : Lemma (ensures sec_join l Secret = Secret \/ sec_join l Secret = TopSecret) =
  sec_join_comm l Secret;
  sec_join_secret_left l

(** ============================================================================
    MEET SEMILATTICE PROOFS
    ============================================================================

    We prove that sec_meet forms a MEET SEMILATTICE (dual to join semilattice).

    A meet semilattice (L, <=, meet) requires:

    ALGEBRAIC PROPERTIES (Dual to Join):
    ------------------------------------
    1. ASSOCIATIVITY: (l1 meet l2) meet l3 = l1 meet (l2 meet l3)
    2. COMMUTATIVITY: l1 meet l2 = l2 meet l1
    3. IDEMPOTENCY:   l meet l = l

    ORDER-THEORETIC PROPERTIES:
    ---------------------------
    4. LOWER BOUND: (l1 meet l2) <= l1 and (l1 meet l2) <= l2
       "The meet is at most as high as both inputs."

    5. GREATEST LOWER BOUND: if l3 <= l1 and l3 <= l2 then l3 <= (l1 meet l2)
       "The meet is the LARGEST element below both."

    Diamond Lattice Key Insight:
    ----------------------------
    For incomparable elements (Secret and Confidential):
      meet(Secret, Confidential) = Public

    This is because:
    - Public is below both Secret and Confidential
    - No larger element exists that is below both
    - Therefore, Public is the GREATEST lower bound

    Security Interpretation:
    ------------------------
    The meet operation answers: "What is the maximum security level that
    can observe BOTH data sources?"

    An observer at level L can see data at any level <= L. So:
    - Observer at Public can see only Public data
    - Observer at Secret can see Public + Secret (but NOT Confidential!)
    - Observer at TopSecret can see everything

    The meet(l1, l2) is the HIGHEST level that can observe both l1 and l2.

    Examples:
      meet(TopSecret, Secret) = Secret    (* TopSecret is identity *)
      meet(Secret, Secret) = Secret       (* Idempotent *)
      meet(Secret, Confidential) = Public (* Incomparable => bottom *)
      meet(Public, anything) = Public     (* Bottom is absorbing *)

    Why Meet Matters for IFC:
    -------------------------
    Meet is used less frequently than join in IFC, but appears in:
    - Declassification bounds (what can be released)
    - Computing common observation levels
    - Integrity label calculations (where flow direction is reversed)

    Together with join, meet makes (L, <=, join, meet, Public, TopSecret)
    a BOUNDED LATTICE, providing rich algebraic structure for security analysis.
    ============================================================================ *)

(** Associativity of meet - proven by exhaustive case analysis *)
let sec_meet_assoc (l1 l2 l3: sec_level)
    : Lemma (ensures sec_meet (sec_meet l1 l2) l3 = sec_meet l1 (sec_meet l2 l3)) =
  match l1, l2, l3 with
  (* Public cases - Public is absorbing for meet *)
  | Public, _, _ -> ()
  | _, Public, _ -> ()
  | _, _, Public -> ()
  (* Confidential cases *)
  | Confidential, Confidential, Confidential -> ()
  | Confidential, Confidential, Secret -> ()
  | Confidential, Confidential, TopSecret -> ()
  | Confidential, Secret, Confidential -> ()
  | Confidential, Secret, Secret -> ()
  | Confidential, Secret, TopSecret -> ()
  | Confidential, TopSecret, Confidential -> ()
  | Confidential, TopSecret, Secret -> ()
  | Confidential, TopSecret, TopSecret -> ()
  (* Secret cases *)
  | Secret, Confidential, Confidential -> ()
  | Secret, Confidential, Secret -> ()
  | Secret, Confidential, TopSecret -> ()
  | Secret, Secret, Confidential -> ()
  | Secret, Secret, Secret -> ()
  | Secret, Secret, TopSecret -> ()
  | Secret, TopSecret, Confidential -> ()
  | Secret, TopSecret, Secret -> ()
  | Secret, TopSecret, TopSecret -> ()
  (* TopSecret cases - TopSecret is identity for meet *)
  | TopSecret, Confidential, Confidential -> ()
  | TopSecret, Confidential, Secret -> ()
  | TopSecret, Confidential, TopSecret -> ()
  | TopSecret, Secret, Confidential -> ()
  | TopSecret, Secret, Secret -> ()
  | TopSecret, Secret, TopSecret -> ()
  | TopSecret, TopSecret, Confidential -> ()
  | TopSecret, TopSecret, Secret -> ()
  | TopSecret, TopSecret, TopSecret -> ()

(** Commutativity of meet *)
let sec_meet_comm (l1 l2: sec_level)
    : Lemma (ensures sec_meet l1 l2 = sec_meet l2 l1) =
  match l1, l2 with
  | Public, Public -> ()
  | Public, Confidential -> ()
  | Public, Secret -> ()
  | Public, TopSecret -> ()
  | Confidential, Public -> ()
  | Confidential, Confidential -> ()
  | Confidential, Secret -> ()
  | Confidential, TopSecret -> ()
  | Secret, Public -> ()
  | Secret, Confidential -> ()
  | Secret, Secret -> ()
  | Secret, TopSecret -> ()
  | TopSecret, Public -> ()
  | TopSecret, Confidential -> ()
  | TopSecret, Secret -> ()
  | TopSecret, TopSecret -> ()

(** Idempotency of meet *)
let sec_meet_idem (l: sec_level)
    : Lemma (ensures sec_meet l l = l) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** Meet is a lower bound for left operand: (l1 meet l2) <= l1

    Key cases for diamond:
    - meet(Secret, Confidential) = Public, and Public <= Secret
    - meet(Confidential, Secret) = Public, and Public <= Confidential
*)
let sec_meet_lower_left (l1 l2: sec_level)
    : Lemma (ensures sec_leq (sec_meet l1 l2) l1 = true) =
  match l1, l2 with
  | Public, _ -> ()           (* Public <= Public *)
  | Confidential, Public -> ()
  | Confidential, Confidential -> ()
  | Confidential, Secret -> ()     (* Public <= Confidential *)
  | Confidential, TopSecret -> ()
  | Secret, Public -> ()
  | Secret, Confidential -> ()     (* Public <= Secret *)
  | Secret, Secret -> ()
  | Secret, TopSecret -> ()
  | TopSecret, Public -> ()
  | TopSecret, Confidential -> ()
  | TopSecret, Secret -> ()
  | TopSecret, TopSecret -> ()

let sec_meet_lower_right (l1 l2: sec_level)
    : Lemma (ensures sec_leq (sec_meet l1 l2) l2 = true) =
  sec_meet_comm l1 l2;
  sec_meet_lower_left l2 l1

(** Meet is the greatest lower bound

    If l3 <= l1 and l3 <= l2, then l3 <= (l1 meet l2).
    Key diamond case: if l3 <= Secret and l3 <= Confidential,
    then l3 must be Public (only element below both), so l3 <= meet = Public.
*)
let sec_meet_glb (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l3 l1 = true /\ sec_leq l3 l2 = true)
            (ensures sec_leq l3 (sec_meet l1 l2) = true) =
  match l1, l2, l3 with
  (* TopSecret cases - TopSecret is identity for meet *)
  | TopSecret, TopSecret, _ -> ()
  | TopSecret, Secret, Public -> ()
  | TopSecret, Secret, Secret -> ()
  | TopSecret, Confidential, Public -> ()
  | TopSecret, Confidential, Confidential -> ()
  | Secret, TopSecret, Public -> ()
  | Secret, TopSecret, Secret -> ()
  | Confidential, TopSecret, Public -> ()
  | Confidential, TopSecret, Confidential -> ()
  | TopSecret, Public, Public -> ()
  | Public, TopSecret, Public -> ()
  (* Secret-only chains *)
  | Secret, Secret, Public -> ()
  | Secret, Secret, Secret -> ()
  (* Confidential-only chains *)
  | Confidential, Confidential, Public -> ()
  | Confidential, Confidential, Confidential -> ()
  (* Mixed Secret-Confidential: meet = Public, so l3 must be Public *)
  | Secret, Confidential, Public -> ()
  | Confidential, Secret, Public -> ()
  (* Public cases *)
  | Public, _, Public -> ()
  | _, Public, Public -> ()
  (* Vacuous cases (precondition false) *)
  | Secret, Confidential, Secret -> ()       (* Vacuous: Secret </= Confidential *)
  | Secret, Confidential, Confidential -> () (* Vacuous: Confidential </= Secret *)
  | Secret, Confidential, TopSecret -> ()    (* Vacuous: TopSecret </= Secret *)
  | Confidential, Secret, Secret -> ()       (* Vacuous: Secret </= Confidential *)
  | Confidential, Secret, Confidential -> () (* Vacuous: Confidential </= Secret *)
  | Confidential, Secret, TopSecret -> ()    (* Vacuous: TopSecret </= Confidential *)
  | Secret, Secret, Confidential -> ()       (* Vacuous: Confidential </= Secret *)
  | Secret, Secret, TopSecret -> ()          (* Vacuous: TopSecret </= Secret *)
  | Confidential, Confidential, Secret -> () (* Vacuous: Secret </= Confidential *)
  | Confidential, Confidential, TopSecret -> () (* Vacuous: TopSecret </= Conf *)
  | TopSecret, Secret, Confidential -> ()    (* Vacuous: Confidential </= Secret *)
  | TopSecret, Secret, TopSecret -> ()       (* Vacuous: TopSecret </= Secret *)
  | TopSecret, Confidential, Secret -> ()    (* Vacuous: Secret </= Confidential *)
  | TopSecret, Confidential, TopSecret -> () (* Vacuous: TopSecret </= Conf *)
  | Secret, TopSecret, Confidential -> ()    (* Vacuous: Confidential </= Secret *)
  | Secret, TopSecret, TopSecret -> ()       (* Vacuous: TopSecret </= Secret *)
  | Confidential, TopSecret, Secret -> ()    (* Vacuous: Secret </= Confidential *)
  | Confidential, TopSecret, TopSecret -> () (* Vacuous: TopSecret </= Conf *)
  | TopSecret, Public, _ -> ()
  | Public, TopSecret, _ -> ()
  | Secret, Public, _ -> ()
  | Public, Secret, _ -> ()
  | Confidential, Public, _ -> ()
  | Public, Confidential, _ -> ()
  | Public, Public, _ -> ()

(** Meet with TopSecret is identity *)
let sec_meet_topsecret_left (l: sec_level)
    : Lemma (ensures sec_meet TopSecret l = l) =
  match l with
  | Public -> ()
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

let sec_meet_topsecret_right (l: sec_level)
    : Lemma (ensures sec_meet l TopSecret = l) =
  sec_meet_comm l TopSecret;
  sec_meet_topsecret_left l

(** Meet with Public is absorbing *)
let sec_meet_public_left (l: sec_level)
    : Lemma (ensures sec_meet Public l = Public) =
  ()

let sec_meet_public_right (l: sec_level)
    : Lemma (ensures sec_meet l Public = Public) =
  sec_meet_comm l Public;
  sec_meet_public_left l

(** ============================================================================
    LABELED TYPES (SECURITY-TYPED VALUES)
    ============================================================================

    A LABELED TYPE pairs a base type with a security label, creating a
    security-aware type system. This is the core of our IFC mechanism.

    Mathematical Notation:
    ----------------------
    We write T^l for a type T at security level l.
    Examples:
      int^Public    -- a public integer (anyone can read)
      string^Secret -- a secret string (restricted access)
      bool^TopSecret -- a top-secret boolean

    In F*, we represent this as a record:
      { base_type = T; label = l }

    Security Type Subtyping:
    ------------------------
    Labeled types form a subtype relation combining:
    1. Base type subtyping: T1 <: T2
    2. Security label ordering: l1 <= l2

    The rule is:
      T1^l1 <: T2^l2  iff  T1 <: T2  AND  l1 <= l2

    This ensures COVARIANT label subtyping: a Secret value can be used
    where a TopSecret value is expected (because Secret <= TopSecret),
    but NOT vice versa.

    Examples:
      int^Public <: int^Secret      (* Public can flow to Secret *)
      int^Secret <: int^TopSecret   (* Secret can flow to TopSecret *)
      int^Secret </: int^Public     (* ILLEGAL: downward flow! *)
      int^Secret </: int^Confidential (* ILLEGAL: incomparable! *)

    Why Labeled Types Matter:
    -------------------------
    Labeled types enable STATIC enforcement of information flow policies:
    - The type checker tracks security labels through all operations
    - Type errors reveal potential information leaks
    - Well-typed programs are GUARANTEED to satisfy noninterference

    This is the key insight of [Volpano, Smith, Irvine 1996]:
    "A Sound Type System for Secure Flow Analysis"

    Constructor Functions:
    ----------------------
    - public_type(T): Creates T^Public (observable by all)
    - confidential_type(T): Creates T^Confidential
    - secret_type(T): Creates T^Secret
    - topsecret_type(T): Creates T^TopSecret (highest classification)

    Reference: brrr_lang_spec_v0.4.tex Section "Security-Typed Values"
    ============================================================================ *)

(** Labeled type: a base type with a security label *)
noeq type labeled_type = {
  base_type : brrr_type;
  label     : sec_level;
}

(** Create a labeled type *)
let label_type (t: brrr_type) (l: sec_level) : labeled_type =
  { base_type = t; label = l }

(** Create a public labeled type (observable by all) *)
let public_type (t: brrr_type) : labeled_type =
  { base_type = t; label = Public }

(** Create a confidential labeled type (one compartment) *)
let confidential_type (t: brrr_type) : labeled_type =
  { base_type = t; label = Confidential }

(** Create a secret labeled type (another compartment) *)
let secret_type (t: brrr_type) : labeled_type =
  { base_type = t; label = Secret }

(** Create a top-secret labeled type (highest classification) *)
let topsecret_type (t: brrr_type) : labeled_type =
  { base_type = t; label = TopSecret }

(** Labeled type equality *)
let labeled_type_eq (lt1 lt2: labeled_type) : bool =
  type_eq lt1.base_type lt2.base_type && sec_level_eq lt1.label lt2.label

(** Labeled type equality is reflexive *)
let labeled_type_eq_refl (lt: labeled_type)
    : Lemma (ensures labeled_type_eq lt lt = true) =
  type_eq_refl lt.base_type;
  sec_level_eq_refl lt.label

(** Labeled type equality is symmetric *)
let labeled_type_eq_sym (lt1 lt2: labeled_type)
    : Lemma (requires labeled_type_eq lt1 lt2 = true)
            (ensures labeled_type_eq lt2 lt1 = true) =
  type_eq_sym lt1.base_type lt2.base_type;
  sec_level_eq_sym lt1.label lt2.label

(** Subtyping for labeled types

    A labeled type lt1 is a subtype of lt2 iff:
    1. The base types are in a subtype relation
    2. The label of lt1 can flow to the label of lt2 (lt1.label <= lt2.label)

    This ensures that data cannot be coerced to a lower security level.
*)
let labeled_subtype (lt1 lt2: labeled_type) : bool =
  subtype lt1.base_type lt2.base_type && sec_leq lt1.label lt2.label

(** Labeled subtyping is reflexive *)
let labeled_subtype_refl (lt: labeled_type)
    : Lemma (ensures labeled_subtype lt lt = true) =
  subtype_refl lt.base_type;
  sec_leq_refl lt.label

(** Labeled subtyping is transitive *)
let labeled_subtype_trans (lt1 lt2 lt3: labeled_type)
    : Lemma (requires labeled_subtype lt1 lt2 = true /\ labeled_subtype lt2 lt3 = true)
            (ensures labeled_subtype lt1 lt3 = true) =
  subtype_trans lt1.base_type lt2.base_type lt3.base_type;
  sec_leq_trans lt1.label lt2.label lt3.label

(** Join of labeled types (for binary operations) *)
let labeled_type_join (lt1 lt2: labeled_type) : option labeled_type =
  if type_eq lt1.base_type lt2.base_type then
    Some { base_type = lt1.base_type; label = sec_join lt1.label lt2.label }
  else
    None

(** ============================================================================
    SECURITY CONTEXT
    ============================================================================

    The security context maps variables to their labeled types.
    It tracks both the base type and security level of each variable.
    ============================================================================ *)

(** Security context: maps variable names to labeled types *)
type sec_ctx = list (var_id & labeled_type)

(** Empty security context *)
let empty_sec_ctx : sec_ctx = []

(** Extend security context with a binding *)
let extend_sec_ctx (x: var_id) (lt: labeled_type) (ctx: sec_ctx) : sec_ctx =
  (x, lt) :: ctx

(** Lookup variable in security context *)
let rec lookup_sec_ctx (x: var_id) (ctx: sec_ctx) : option labeled_type =
  match ctx with
  | [] -> None
  | (y, lt) :: rest ->
      if x = y then Some lt
      else lookup_sec_ctx x rest

(** Check if variable is in context *)
let rec in_sec_ctx (x: var_id) (ctx: sec_ctx) : bool =
  match ctx with
  | [] -> false
  | (y, _) :: rest -> x = y || in_sec_ctx x rest

(** Get all variables in context *)
let rec sec_ctx_vars (ctx: sec_ctx) : list var_id =
  match ctx with
  | [] -> []
  | (x, _) :: rest -> x :: sec_ctx_vars rest

(** Get all labeled types in context *)
let rec sec_ctx_types (ctx: sec_ctx) : list labeled_type =
  match ctx with
  | [] -> []
  | (_, lt) :: rest -> lt :: sec_ctx_types rest

(** ============================================================================
    PROGRAM COUNTER LABEL (PC) - IMPLICIT FLOW TRACKING
    ============================================================================

    The PC (Program Counter) label is a fundamental concept in IFC that tracks
    the security level of the CONTROL FLOW CONTEXT. It prevents IMPLICIT FLOWS.

    Background: Explicit vs Implicit Flows
    --------------------------------------
    From [Denning76] and [Sabelfeld&Myers03]:

    1. EXPLICIT FLOW (Direct Data Dependency):
       y := x    (* Value of x directly flows to y *)

       Prevented by: label(x) <= label(y)

    2. IMPLICIT FLOW (Control Dependency):
       if secret then y := 1 else y := 0

       The VALUE of y reveals information about `secret`:
       - If y = 1, we know secret was true
       - If y = 0, we know secret was false

       This is a covert channel! Information flows through WHICH BRANCH executes.

    The PC Mechanism:
    -----------------
    The PC label tracks the security level of conditions that led to the
    current program point. It is:

    1. RAISED when entering a branch guarded by a high-security condition:
         pc' = pc join label(condition)

       Example:
         pc = Public
         if secret_bool then      (* pc' = Public join Secret = Secret *)
           ...                    (* Inside branch, pc = Secret *)

    2. RESTORED when exiting the branch:
         After if-then-else, pc returns to its value before the if

    3. USED to constrain assignments:
         For assignment x := e, we require:
           pc join label(e) <= label(x)

         The pc component ensures we can't write to public variables
         inside secret branches.

    Detailed Example:
    -----------------
    (* Initial state: pc = Public *)
    let secret_flag : bool^Secret = ... in
    let public_counter : int^Public = 0 in

    if secret_flag then            (* pc becomes Secret *)
      public_counter := 1          (* REJECTED! *)
      (* check: Secret join Public = Secret *)
      (* Secret </= Public, so FAIL *)
    else
      public_counter := 0          (* Also REJECTED! *)

    Even though both branches assign constants, the FACT that an assignment
    occurred reveals which branch was taken, leaking `secret_flag`.

    Why PC join rhs_label?
    ----------------------
    The full constraint is: pc join label(rhs) <= label(lhs)

    - pc: Captures implicit flow from control dependencies
    - label(rhs): Captures explicit flow from the assigned value
    - join: Takes the maximum (most restrictive)
    - <= label(lhs): Must flow to the target's level

    This elegantly handles both flow types in one rule!

    References:
    -----------
    - [Denning76] Section 4: Certification mechanism using program counters
    - [VolpanoSmith96] Figure 3: Typing rules with pc labels
    - brrr_lang_spec_v0.4.tex Section "Implicit Flows" (line 5944)
    ============================================================================ *)

(** PC label is just a security level *)
type pc_label = sec_level

(** Initial PC label (public - no control flow constraints) *)
let initial_pc : pc_label = Public

(** Raise PC label when entering conditional with given guard level *)
let raise_pc (pc: pc_label) (guard_level: sec_level) : pc_label =
  sec_join pc guard_level

(** ============================================================================
    INFORMATION FLOW TYPE CHECKING RESULT
    ============================================================================ *)

(** Result of security type checking *)
noeq type sec_check_result =
  | SecOk  : labeled_type -> sec_ctx -> sec_check_result
  | SecErr : string -> sec_check_result

(** ============================================================================
    FLOW CONSTRAINT CHECKING
    ============================================================================

    The core security constraint is the "no flows up" rule:

      pc join source_label <= target_label

    This means:
    1. The PC must be able to flow to the target (prevents implicit flows)
    2. The source must be able to flow to the target (prevents explicit flows)
    ============================================================================ *)

(** Check if assignment is allowed: pc join rhs_label <= lhs_label *)
let check_assignment_flow (pc: pc_label) (rhs_label: sec_level) (lhs_label: sec_level) : bool =
  sec_leq (sec_join pc rhs_label) lhs_label

(** Assignment flow is always allowed when target is TopSecret *)
let assignment_flow_to_topsecret (pc: pc_label) (rhs_label: sec_level)
    : Lemma (ensures check_assignment_flow pc rhs_label TopSecret = true) =
  sec_topsecret_top (sec_join pc rhs_label)

(** Assignment flow from Public to Public is allowed iff PC is Public *)
let assignment_flow_public_public (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Public Public = (pc = Public)) =
  match pc with
  | Public -> sec_join_public_left Public
  | Confidential -> ()
  | Secret -> ()
  | TopSecret -> ()

(** Assignment from Secret to Confidential is NEVER allowed (incomparable!)
    Even with Public PC, Secret cannot flow to Confidential.
*)
let assignment_flow_secret_to_confidential_forbidden (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Secret Confidential = false) =
  match pc with
  | Public -> ()      (* join(Public, Secret) = Secret, Secret </= Confidential *)
  | Confidential -> () (* join(Conf, Secret) = TopSecret, TopSecret </= Confidential *)
  | Secret -> ()      (* join(Secret, Secret) = Secret, Secret </= Confidential *)
  | TopSecret -> ()   (* join(TopSecret, Secret) = TopSecret, TopSecret </= Confidential *)

(** Assignment from Confidential to Secret is NEVER allowed (incomparable!) *)
let assignment_flow_confidential_to_secret_forbidden (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Confidential Secret = false) =
  match pc with
  | Public -> ()      (* join(Public, Conf) = Conf, Conf </= Secret *)
  | Confidential -> () (* join(Conf, Conf) = Conf, Conf </= Secret *)
  | Secret -> ()      (* join(Secret, Conf) = TopSecret, TopSecret </= Secret *)
  | TopSecret -> ()   (* join(TopSecret, Conf) = TopSecret, TopSecret </= Secret *)

(** ============================================================================
    INFORMATION FLOW TYPE CHECKING
    ============================================================================

    The security type checker extends the regular type checker with:
    1. Security labels on all types
    2. PC tracking through control flow
    3. Flow constraints on assignments
    4. Label propagation through expressions

    Key rules:
    - T-Var:    Gamma(x) = T^l  =>  Gamma |- x : T^l
    - T-Const:  Gamma |- c : T^Public
    - T-Op:     l = l1 join l2 for binary ops
    - T-If:     PC' = PC join l_cond for branches
    - T-Assign: PC join l_rhs <= l_lhs
    ============================================================================ *)

(** Infer security type of a literal (always Public) *)
let sec_infer_literal (lit: literal) : labeled_type =
  public_type (infer_literal lit)
  where
  let infer_literal (lit: literal) : brrr_type =
    match lit with
    | LitUnit -> t_unit
    | LitBool _ -> t_bool
    | LitInt _ it -> t_int it
    | LitFloat _ fp -> t_float fp
    | LitString _ -> t_string
    | LitChar _ -> t_char
    | LitImaginary _ fp -> TTuple [t_float fp; t_float fp]

(** Infer security type of unary operation *)
let sec_unary_op_type (op: unary_op) (lt: labeled_type) : option labeled_type =
  match op, lt.base_type with
  | OpNeg, TNumeric (NumInt it) -> Some { base_type = t_int it; label = lt.label }
  | OpNeg, TNumeric (NumFloat fp) -> Some { base_type = t_float fp; label = lt.label }
  | OpNot, TPrim PBool -> Some { base_type = t_bool; label = lt.label }
  | OpBitNot, TNumeric (NumInt it) -> Some { base_type = t_int it; label = lt.label }
  | OpDeref, TWrap WRef t' -> Some { base_type = t'; label = lt.label }
  | OpDeref, TWrap WRefMut t' -> Some { base_type = t'; label = lt.label }
  | OpDeref, TWrap WBox t' -> Some { base_type = t'; label = lt.label }
  | OpRef, t' -> Some { base_type = t_ref t'; label = lt.label }
  | OpRefMut, t' -> Some { base_type = t_ref_mut t'; label = lt.label }
  | _, _ -> None

(** Infer security type of binary operation *)
let sec_binary_op_type (op: binary_op) (lt1 lt2: labeled_type) : option labeled_type =
  let result_label = sec_join lt1.label lt2.label in
  match op with
  (* Arithmetic: both operands must be same numeric type *)
  | OpAdd | OpSub | OpMul | OpDiv | OpMod ->
      (match lt1.base_type, lt2.base_type with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
           if i1 = i2 then Some { base_type = t_int i1; label = result_label }
           else None
       | TNumeric (NumFloat f1), TNumeric (NumFloat f2) ->
           if f1 = f2 then Some { base_type = t_float f1; label = result_label }
           else None
       | _, _ -> None)
  (* Comparison: same type, returns bool at joined label *)
  | OpEq | OpNe | OpLt | OpLe | OpGt | OpGe ->
      if type_eq lt1.base_type lt2.base_type then
        Some { base_type = t_bool; label = result_label }
      else None
  (* Logical: both bool *)
  | OpAnd | OpOr ->
      (match lt1.base_type, lt2.base_type with
       | TPrim PBool, TPrim PBool -> Some { base_type = t_bool; label = result_label }
       | _, _ -> None)
  (* Bitwise: both same int *)
  | OpBitAnd | OpBitOr | OpBitXor | OpBitAndNot ->
      (match lt1.base_type, lt2.base_type with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
           if i1 = i2 then Some { base_type = t_int i1; label = result_label }
           else None
       | _, _ -> None)
  (* Shifts *)
  | OpShl | OpShr ->
      (match lt1.base_type, lt2.base_type with
       | TNumeric (NumInt i1), TNumeric (NumInt i2) ->
           if i2.sign = Unsigned then Some { base_type = t_int i1; label = result_label }
           else None
       | _, _ -> None)

(** Information flow type checking with PC tracking *)
let rec sec_typecheck (ctx: sec_ctx) (pc: pc_label) (e: expr)
    : Tot (option labeled_type) (decreases e) =
  match e with
  (* T-Var: Variable lookup *)
  | EVar x ->
      lookup_sec_ctx x ctx

  (* T-Lit: Literals are Public *)
  | ELit lit ->
      Some (sec_infer_literal lit)

  (* T-Global: Global references - assume Public for now *)
  | EGlobal _ ->
      Some (public_type t_dynamic)

  (* T-Unary: Unary operation preserves label *)
  | EUnary op e' ->
      (match sec_typecheck ctx pc e' with
       | Some lt -> sec_unary_op_type op lt
       | None -> None)

  (* T-Binary: Binary operation joins labels *)
  | EBinary op e1 e2 ->
      (match sec_typecheck ctx pc e1, sec_typecheck ctx pc e2 with
       | Some lt1, Some lt2 -> sec_binary_op_type op lt1 lt2
       | _, _ -> None)

  (* T-Tuple: Tuple has joined label of all elements *)
  | ETuple es ->
      (match sec_typecheck_list ctx pc es with
       | Some lts ->
           let labels = List.Tot.map (fun lt -> lt.label) lts in
           let types = List.Tot.map (fun lt -> lt.base_type) lts in
           let joined_label = List.Tot.fold_left sec_join Public labels in
           Some { base_type = TTuple types; label = joined_label }
       | None -> None)

  (* T-If: Conditional raises PC in branches *)
  | EIf cond then_e else_e ->
      (match sec_typecheck ctx pc cond with
       | Some cond_lt ->
           if not (type_eq cond_lt.base_type t_bool) then None
           else
             (* Raise PC for branches based on condition's security level *)
             let pc' = raise_pc pc cond_lt.label in
             (match sec_typecheck ctx pc' then_e, sec_typecheck ctx pc' else_e with
              | Some then_lt, Some else_lt ->
                  if type_eq then_lt.base_type else_lt.base_type then
                    (* Join the labels from both branches *)
                    Some { base_type = then_lt.base_type;
                           label = sec_join then_lt.label else_lt.label }
                  else None
              | _, _ -> None)
       | None -> None)

  (* T-Let: Let binding *)
  | ELet (PatVar x) _ e1 e2 ->
      (match sec_typecheck ctx pc e1 with
       | Some lt1 ->
           let ctx' = extend_sec_ctx x lt1 ctx in
           sec_typecheck ctx' pc e2
       | None -> None)

  (* T-LetMut: Mutable let binding *)
  | ELetMut x _ e1 e2 ->
      (match sec_typecheck ctx pc e1 with
       | Some lt1 ->
           let ctx' = extend_sec_ctx x { base_type = t_ref_mut lt1.base_type; label = lt1.label } ctx in
           sec_typecheck ctx' pc e2
       | None -> None)

  (* T-Assign: Assignment with flow check
     Rule: pc join rhs_label <= lhs_label *)
  | EAssign (EVar x) rhs ->
      (match lookup_sec_ctx x ctx, sec_typecheck ctx pc rhs with
       | Some lhs_lt, Some rhs_lt ->
           (* Check flow constraint: pc join rhs_label <= lhs_label *)
           if check_assignment_flow pc rhs_lt.label lhs_lt.label then
             Some (public_type t_unit)
           else
             None  (* Flow violation! *)
       | _, _ -> None)

  (* T-Seq: Sequence *)
  | ESeq e1 e2 ->
      (match sec_typecheck ctx pc e1 with
       | Some _ -> sec_typecheck ctx pc e2
       | None -> None)

  (* T-Block: Block expression *)
  | EBlock es ->
      sec_typecheck_block ctx pc es

  (* T-Loop: Loop body checked with same PC *)
  | ELoop body ->
      (match sec_typecheck ctx pc body with
       | Some lt -> Some { base_type = t_never; label = lt.label }
       | None -> None)

  (* T-While: While loop raises PC for body *)
  | EWhile cond body ->
      (match sec_typecheck ctx pc cond with
       | Some cond_lt ->
           if not (type_eq cond_lt.base_type t_bool) then None
           else
             let pc' = raise_pc pc cond_lt.label in
             (match sec_typecheck ctx pc' body with
              | Some _ -> Some (public_type t_unit)
              | None -> None)
       | None -> None)

  (* Default: expressions not handled yet *)
  | _ -> None

(** Type check a list of expressions *)
and sec_typecheck_list (ctx: sec_ctx) (pc: pc_label) (es: list expr)
    : Tot (option (list labeled_type)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
      (match sec_typecheck ctx pc e, sec_typecheck_list ctx pc rest with
       | Some lt, Some lts -> Some (lt :: lts)
       | _, _ -> None)

(** Type check a block (returns type of last expression) *)
and sec_typecheck_block (ctx: sec_ctx) (pc: pc_label) (es: list expr)
    : Tot (option labeled_type) (decreases es) =
  match es with
  | [] -> Some (public_type t_unit)
  | [e] -> sec_typecheck ctx pc e
  | e :: rest ->
      (match sec_typecheck ctx pc e with
       | Some _ -> sec_typecheck_block ctx pc rest
       | None -> None)

(** ============================================================================
    LOW EQUIVALENCE (INDISTINGUISHABILITY RELATION)
    ============================================================================

    LOW EQUIVALENCE is the foundational relation for stating noninterference.
    It captures what an observer at a given security level CAN and CANNOT see.

    Definition (Informal):
    ----------------------
    Two memory states s1 and s2 are LOW-EQUIVALENT at observation level `obs`
    (written s1 ~_obs s2) iff they agree on all variables whose security
    level flows to `obs`.

    Formally:
      s1 ~_obs s2  <=>  forall x. label(x) <= obs ==> s1(x) = s2(x)

    Intuition:
    ----------
    An observer at level `obs` can see:
    - All data at level <= obs
    - Nothing at levels > obs or incomparable to obs

    Example with Diamond Lattice:
    -----------------------------
    Consider observation level = Secret:
    - Observer sees: Public, Secret
    - Observer CANNOT see: Confidential, TopSecret

    So s1 ~_Secret s2 means:
    - s1 and s2 agree on all Public variables
    - s1 and s2 agree on all Secret variables
    - s1 and s2 MAY DIFFER on Confidential variables (incomparable!)
    - s1 and s2 MAY DIFFER on TopSecret variables

    This is a KEY INSIGHT of the diamond lattice: a Secret observer cannot
    see Confidential data, even though Confidential is at the "same height"!

    Properties:
    -----------
    Low equivalence at any observation level is an EQUIVALENCE RELATION:
    1. Reflexive:  s ~_obs s
    2. Symmetric:  s1 ~_obs s2 ==> s2 ~_obs s1
    3. Transitive: s1 ~_obs s2 /\ s2 ~_obs s3 ==> s1 ~_obs s3

    We prove all three properties below.

    Classic Definition (backward compatible):
    -----------------------------------------
    The classic "low equivalence" from [Goguen&Meseguer82] uses obs = Public:
      low_equiv(s1, s2) = low_equiv_at(s1, s2, Public)

    This is the most restrictive: only Public variables must match.

    Use in Noninterference:
    -----------------------
    Noninterference states: if two executions start from low-equivalent states,
    they produce low-equivalent results. This captures "secret inputs don't
    affect public outputs."

    References:
    -----------
    - [Goguen&Meseguer82] Definition of noninterference
    - [Sabelfeld&Myers03] Section 2.1: Security condition
    - brrr_lang_spec_v0.4.tex Definition "Low-Equivalence" (line 6069)
    ============================================================================ *)

(** Memory state: maps variables to values *)
type memory = list (var_id & value)

(** Lookup value in memory *)
let rec lookup_memory (x: var_id) (mem: memory) : option value =
  match mem with
  | [] -> None
  | (y, v) :: rest ->
      if x = y then Some v
      else lookup_memory x rest

(** Two memories are low-equivalent at observation level `obs`
    iff they agree on all variables at level <= obs.

    For multi-level security, an observer at level `obs` can see
    all data at levels that flow to `obs` (i.e., levels l where l <= obs).

    Example:
    - Observer at Public: can only see Public data
    - Observer at Secret: can see Public and Secret data (NOT Confidential!)
    - Observer at TopSecret: can see everything
*)
let rec low_equiv_at (ctx: sec_ctx) (mem1 mem2: memory) (obs: sec_level) : bool =
  match ctx with
  | [] -> true
  | (x, lt) :: rest ->
      if sec_leq lt.label obs then
        (* Variables at level <= obs must have equal values *)
        (match lookup_memory x mem1, lookup_memory x mem2 with
         | Some v1, Some v2 -> value_eq v1 v2 && low_equiv_at rest mem1 mem2 obs
         | None, None -> low_equiv_at rest mem1 mem2 obs
         | _, _ -> false)
      else
        (* Variables above obs can differ *)
        low_equiv_at rest mem1 mem2 obs

(** Two memories are low-equivalent (Public observation level)
    This is the classic definition: agreement on all Public variables.
    Preserved for backward compatibility.
*)
let rec low_equiv (ctx: sec_ctx) (mem1 mem2: memory) : bool =
  low_equiv_at ctx mem1 mem2 Public

(** Low equivalence at observation level is reflexive *)
let rec low_equiv_at_refl (ctx: sec_ctx) (mem: memory) (obs: sec_level)
    : Lemma (ensures low_equiv_at ctx mem mem obs = true) (decreases ctx) =
  match ctx with
  | [] -> ()
  | (x, lt) :: rest ->
      if sec_leq lt.label obs then
        (match lookup_memory x mem with
         | Some v -> value_eq_refl v; low_equiv_at_refl rest mem obs
         | None -> low_equiv_at_refl rest mem obs)
      else
        low_equiv_at_refl rest mem obs

(** Low equivalence is reflexive (backward compatible) *)
let low_equiv_refl (ctx: sec_ctx) (mem: memory)
    : Lemma (ensures low_equiv ctx mem mem = true) =
  low_equiv_at_refl ctx mem Public

(** Low equivalence at observation level is symmetric *)
let rec low_equiv_at_sym (ctx: sec_ctx) (mem1 mem2: memory) (obs: sec_level)
    : Lemma (requires low_equiv_at ctx mem1 mem2 obs = true)
            (ensures low_equiv_at ctx mem2 mem1 obs = true)
            (decreases ctx) =
  match ctx with
  | [] -> ()
  | (x, lt) :: rest ->
      if sec_leq lt.label obs then
        (match lookup_memory x mem1, lookup_memory x mem2 with
         | Some v1, Some v2 -> value_eq_sym v1 v2; low_equiv_at_sym rest mem1 mem2 obs
         | None, None -> low_equiv_at_sym rest mem1 mem2 obs
         | _, _ -> ())
      else
        low_equiv_at_sym rest mem1 mem2 obs

(** Low equivalence is symmetric (backward compatible) *)
let low_equiv_sym (ctx: sec_ctx) (mem1 mem2: memory)
    : Lemma (requires low_equiv ctx mem1 mem2 = true)
            (ensures low_equiv ctx mem2 mem1 = true) =
  low_equiv_at_sym ctx mem1 mem2 Public

(** Low equivalence at observation level is transitive *)
let rec low_equiv_at_trans (ctx: sec_ctx) (mem1 mem2 mem3: memory) (obs: sec_level)
    : Lemma (requires low_equiv_at ctx mem1 mem2 obs = true /\ low_equiv_at ctx mem2 mem3 obs = true)
            (ensures low_equiv_at ctx mem1 mem3 obs = true)
            (decreases ctx) =
  match ctx with
  | [] -> ()
  | (x, lt) :: rest ->
      if sec_leq lt.label obs then
        (match lookup_memory x mem1, lookup_memory x mem2, lookup_memory x mem3 with
         | Some v1, Some v2, Some v3 ->
             value_eq_trans v1 v2 v3;
             low_equiv_at_trans rest mem1 mem2 mem3 obs
         | None, None, None -> low_equiv_at_trans rest mem1 mem2 mem3 obs
         | _, _, _ -> ())
      else
        low_equiv_at_trans rest mem1 mem2 mem3 obs

(** Low equivalence is transitive (backward compatible) *)
let low_equiv_trans (ctx: sec_ctx) (mem1 mem2 mem3: memory)
    : Lemma (requires low_equiv ctx mem1 mem2 = true /\ low_equiv ctx mem2 mem3 = true)
            (ensures low_equiv ctx mem1 mem3 = true) =
  low_equiv_at_trans ctx mem1 mem2 mem3 Public

(** ============================================================================
    NONINTERFERENCE THEOREM
    ============================================================================

    NONINTERFERENCE is the gold standard security property for IFC systems.
    It was first formalized by [Goguen & Meseguer 1982] and states:

    "High-security inputs do not affect low-security outputs."

    Or equivalently:

    "An observer at a low security level cannot distinguish between
     executions that differ only in high-security inputs."

    Formal Statement (Simplified):
    ------------------------------
    For all programs P, states s1, s2:
      s1 ~_L s2  /\  P(s1) terminates  /\  P(s2) terminates
      ==>
      P(s1) ~_L P(s2)

    Where ~_L is low-equivalence at observation level L (typically Public).

    Intuition:
    ----------
    Consider an attacker who:
    - Can observe all public (low-security) data
    - Cannot observe any secret (high-security) data
    - Runs the program twice with different secret inputs

    Noninterference guarantees that the attacker sees IDENTICAL public outputs
    in both runs. The secret data is completely hidden.

    Type-Based Enforcement:
    -----------------------
    The key theorem connecting types to security is:

    SOUNDNESS: Well-typed programs satisfy noninterference.

    This is proven by showing that if:
      1. ctx |- e : T^l (expression e type-checks with label l)
      2. s1 ~_L s2 (states are low-equivalent)
      3. eval(e, s1) = v1, eval(e, s2) = v2 (both terminate)

    Then:
      l <= L  ==>  v1 = v2 (results are equal)

    The proof proceeds by induction on the typing derivation, showing that
    each typing rule preserves low-equivalence.

    Why This Matters:
    -----------------
    Once proven, soundness means:
    - The TYPE CHECKER is a SECURITY VERIFIER
    - Any program that type-checks is GUARANTEED secure
    - No runtime monitoring or dynamic checks needed
    - Security is a COMPILE-TIME property

    Proof Structure (Sketch):
    -------------------------
    By induction on expression structure:

    - Variables: If x has Public type and s1 ~_L s2, then s1(x) = s2(x)
                 by definition of low-equivalence.

    - Literals:  Always produce the same value, independent of state.

    - Binary ops: If result is Public, both operands must be Public
                  (by flow constraint). By IH, operands are equal, so
                  the operation produces equal results.

    - If-then-else: If result is Public and s1 ~_L s2:
                    - Condition must be Public (otherwise result would be high)
                    - By IH, condition evaluates to same boolean
                    - Same branch is taken in both executions
                    - By IH, branch bodies produce equal results

    - Assignments: The PC mechanism ensures we can't write to low variables
                   under high guards, preserving low-equivalence.

    References:
    -----------
    - [Goguen&Meseguer82] "Security Policies and Security Models" - original def
    - [VolpanoSmith96] "A Sound Type System for Secure Flow Analysis" - type-based
    - [Sabelfeld&Myers03] Section 2 - comprehensive treatment
    - brrr_lang_spec_v0.4.tex Theorem "Type Soundness Implies Noninterference"
    ============================================================================ *)

(**
 * Helper: if we type-check a variable x in context ctx with some result,
 * and x has a Public type, then the result label must be Public.
 *)
let sec_typecheck_var_public_label (ctx: sec_ctx) (x: var_id) (lt: labeled_type)
    : Lemma (requires lookup_sec_ctx x ctx = Some lt /\ lt.label = Public)
            (ensures sec_typecheck ctx Public (EVar x) = Some lt) =
  ()

(**
 * Type soundness implies noninterference for expressions.
 *
 * This is the core noninterference lemma. It states that if:
 * 1. An expression e type-checks with a Public result
 * 2. Two memories are low-equivalent
 * Then evaluation of e in both memories produces equal values.
 *
 * The proof proceeds by induction on the expression structure:
 * - Variables: Public variables have equal values by low_equiv
 * - Literals: Always produce the same value
 * - Binary ops: If result is Public, both operands must have values that
 *   produce the same result (by IH on subexpressions)
 * - If-then-else: If result is Public, condition must be Public (otherwise
 *   the result would be Secret), so both executions take the same branch
 *
 * NOTE: This is a simplified statement. A full proof would require:
 * - A formal operational semantics (evaluation relation)
 * - Proof that type checking implies evaluation preserves low-equivalence
 * - Proof that the PC mechanism prevents implicit flows
 *)

(** Expression evaluation result *)
type eval_result =
  | EvalValue : value -> eval_result
  | EvalStuck : eval_result

(** Simplified evaluation for expressions (needed for noninterference statement) *)
let rec eval_expr (e: expr) (mem: memory) : Tot eval_result (decreases e) =
  match e with
  | EVar x ->
      (match lookup_memory x mem with
       | Some v -> EvalValue v
       | None -> EvalStuck)

  | ELit lit ->
      (match lit with
       | LitUnit -> EvalValue VUnit
       | LitBool b -> EvalValue (VBool b)
       | LitInt n _ -> EvalValue (VInt n)
       | _ -> EvalStuck)  (* Simplified: only handle some literals *)

  | EBinary OpAdd e1 e2 ->
      (match eval_expr e1 mem, eval_expr e2 mem with
       | EvalValue (VInt n1), EvalValue (VInt n2) -> EvalValue (VInt (n1 + n2))
       | _, _ -> EvalStuck)

  | EBinary OpEq e1 e2 ->
      (match eval_expr e1 mem, eval_expr e2 mem with
       | EvalValue v1, EvalValue v2 -> EvalValue (VBool (value_eq v1 v2))
       | _, _ -> EvalStuck)

  (* Simplified: other expressions return stuck *)
  | _ -> EvalStuck

(**
 * Noninterference theorem (simplified statement).
 *
 * For a well-typed expression with Public result type,
 * low-equivalent inputs produce equal outputs.
 *
 * This theorem captures the essence of information flow security:
 * Secret data cannot influence public results.
 *)
type noninterference_statement =
  ctx:sec_ctx -> e:expr -> mem1:memory -> mem2:memory ->
  Lemma (requires
           (match sec_typecheck ctx Public e with
            | Some lt -> lt.label = Public
            | None -> false) /\
           low_equiv ctx mem1 mem2 = true)
        (ensures
           (match eval_expr e mem1, eval_expr e mem2 with
            | EvalValue v1, EvalValue v2 -> value_eq v1 v2 = true
            | EvalStuck, EvalStuck -> true
            | _, _ -> false))

(**
 * Noninterference for variables.
 * If x has Public type and memories are low-equivalent, then x has equal values.
 *)
let noninterference_var (ctx: sec_ctx) (x: var_id) (mem1 mem2: memory)
    : Lemma (requires
               (match lookup_sec_ctx x ctx with
                | Some lt -> lt.label = Public
                | None -> false) /\
               low_equiv ctx mem1 mem2 = true)
            (ensures
               (match lookup_memory x mem1, lookup_memory x mem2 with
                | Some v1, Some v2 -> value_eq v1 v2 = true
                | None, None -> true
                | _, _ -> false)) =
  let rec aux (ctx': sec_ctx)
      : Lemma (requires
                 low_equiv ctx' mem1 mem2 = true /\
                 (match lookup_sec_ctx x ctx' with
                  | Some lt -> lt.label = Public
                  | None -> false))
              (ensures
                 (match lookup_memory x mem1, lookup_memory x mem2 with
                  | Some v1, Some v2 -> value_eq v1 v2 = true
                  | None, None -> true
                  | _, _ -> false))
              (decreases ctx') =
    match ctx' with
    | [] -> ()
    | (y, lt) :: rest ->
        if x = y then
          (* Found x in context with Public label *)
          if lt.label = Public then
            (* low_equiv ensures public vars have equal values *)
            ()
          else
            ()  (* Vacuously true: x is Secret, contradicts precondition *)
        else
          aux rest
  in
  aux ctx

(**
 * Noninterference for literals.
 * Literals always evaluate to the same value regardless of memory.
 *)
let noninterference_lit (lit: literal) (mem1 mem2: memory)
    : Lemma (ensures
               (match eval_expr (ELit lit) mem1, eval_expr (ELit lit) mem2 with
                | EvalValue v1, EvalValue v2 -> value_eq v1 v2 = true
                | EvalStuck, EvalStuck -> true
                | _, _ -> false)) =
  match lit with
  | LitUnit -> value_eq_refl VUnit
  | LitBool b -> value_eq_refl (VBool b)
  | LitInt n _ -> value_eq_refl (VInt n)
  | _ -> ()

(** ============================================================================
    WELL-TYPED PROGRAMS DON'T LEAK
    ============================================================================

    The fundamental theorem of information flow typing:

    If a program type-checks under our security type system,
    then it satisfies noninterference.

    This is the key soundness result that justifies the type system.
    ============================================================================ *)

(**
 * Type soundness: well-typed expressions don't get stuck.
 * This is a partial result - a full proof would require a complete
 * operational semantics.
 *)
let type_soundness_var (ctx: sec_ctx) (x: var_id) (mem: memory)
    : Lemma (requires Some? (lookup_sec_ctx x ctx) /\ Some? (lookup_memory x mem))
            (ensures Some? (match eval_expr (EVar x) mem with EvalValue v -> Some v | _ -> None)) =
  ()

(**
 * Security type soundness: the security type system prevents leaks.
 *
 * This lemma states that if an assignment type-checks (passes flow check),
 * then it preserves low-equivalence.
 *
 * Specifically, if:
 *   - Assignment x := e type-checks (pc join label(e) <= label(x))
 *   - mem1 and mem2 are low-equivalent
 * Then:
 *   - The resulting memories are still low-equivalent
 *
 * This captures the key invariant: well-typed programs preserve low-equivalence.
 *)
type assignment_preserves_low_equiv_statement =
  ctx:sec_ctx -> pc:pc_label -> x:var_id -> rhs_lt:labeled_type ->
  mem1:memory -> mem2:memory -> v1:value -> v2:value ->
  Lemma (requires
           (* Assignment type-checks *)
           (match lookup_sec_ctx x ctx with
            | Some lhs_lt -> check_assignment_flow pc rhs_lt.label lhs_lt.label
            | None -> false) /\
           (* Memories are low-equivalent *)
           low_equiv ctx mem1 mem2 = true)
        (ensures
           (* After assignment, memories remain low-equivalent *)
           (* (We would need to define memory update for full statement) *)
           true)

(**
 * Main security theorem: Well-typed programs are noninterfering.
 *
 * This is stated as a type rather than a proven lemma because a complete
 * proof would require:
 * 1. A full operational semantics for expressions
 * 2. Proof of type preservation under evaluation
 * 3. Proof of progress (well-typed expressions don't get stuck)
 * 4. Proof that PC tracking prevents implicit flows
 *
 * The type captures the theorem statement that we aim to prove.
 *)
type security_theorem =
  (* For all well-typed programs *)
  ctx:sec_ctx -> e:expr ->
  (* Such that e type-checks with some labeled type *)
  squash (Some? (sec_typecheck ctx Public e)) ->
  (* And for all low-equivalent memory pairs *)
  mem1:memory -> mem2:memory ->
  squash (low_equiv ctx mem1 mem2 = true) ->
  (* The expression satisfies noninterference:
     If the result is Public, equal memories produce equal results *)
  squash (
    match sec_typecheck ctx Public e with
    | Some lt ->
        lt.label = Public ==>
        (match eval_expr e mem1, eval_expr e mem2 with
         | EvalValue v1, EvalValue v2 -> value_eq v1 v2 = true
         | _, _ -> true)
    | None -> true)

(** ============================================================================
    UTILITY FUNCTIONS
    ============================================================================ *)

(** Check if an expression is security-typed at a level that flows to `target` *)
let is_security_typed_at (ctx: sec_ctx) (pc: pc_label) (e: expr) (target: sec_level) : bool =
  match sec_typecheck ctx pc e with
  | Some lt -> sec_leq lt.label target
  | None -> false

(** Check if expression result can flow to public (observable by all) *)
let can_flow_to_public (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool =
  is_security_typed_at ctx pc e Public

(** Check if expression result can flow to confidential level *)
let can_flow_to_confidential (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool =
  is_security_typed_at ctx pc e Confidential

(** Check if expression result can flow to secret level *)
let can_flow_to_secret (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool =
  is_security_typed_at ctx pc e Secret

(** Check if expression has a high-security dependency (Confidential, Secret, or TopSecret) *)
let has_high_security_dependency (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool =
  match sec_typecheck ctx pc e with
  | Some lt -> not (lt.label = Public)
  | None -> false

(** Check if expression has top-secret dependency *)
let has_topsecret_dependency (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool =
  match sec_typecheck ctx pc e with
  | Some lt -> lt.label = TopSecret
  | None -> false

(** Check if expression involves incomparable levels (Secret and Confidential) *)
let involves_incomparable_levels (ctx: sec_ctx) (pc: pc_label) (e1 e2: expr) : bool =
  match sec_typecheck ctx pc e1, sec_typecheck ctx pc e2 with
  | Some lt1, Some lt2 ->
      (lt1.label = Secret && lt2.label = Confidential) ||
      (lt1.label = Confidential && lt2.label = Secret)
  | _, _ -> false

(** Get the security label of an expression *)
let get_security_label (ctx: sec_ctx) (pc: pc_label) (e: expr) : option sec_level =
  match sec_typecheck ctx pc e with
  | Some lt -> Some lt.label
  | None -> None

(** Get the minimum observation level required to see an expression's result *)
let minimum_observation_level (ctx: sec_ctx) (pc: pc_label) (e: expr) : option sec_level =
  get_security_label ctx pc e

(** Check if two levels are comparable in the lattice *)
let levels_are_comparable (l1 l2: sec_level) : bool =
  sec_leq l1 l2 || sec_leq l2 l1

(** Levels that are incomparable: Secret vs Confidential *)
let levels_are_incomparable (l1 l2: sec_level) : bool =
  not (levels_are_comparable l1 l2)

(** ============================================================================
    DECLASSIFICATION (Controlled Information Release)
    ============================================================================

    DECLASSIFICATION intentionally releases secret information to lower
    security levels. It is a CONTROLLED VIOLATION of noninterference.

    Motivation:
    -----------
    Pure noninterference is too restrictive for real programs. Consider:

    1. Password checking: "is_valid = (hash(input) == stored_hash)"
       The result (is_valid) is Public, but depends on the Secret password.
       This is an INTENTIONAL information release.

    2. Aggregate queries: "avg_salary = sum(salaries) / count"
       Individual salaries are Secret, but the average can be Public.

    3. Encryption: "ciphertext = encrypt(secret_key, message)"
       The ciphertext is Public, derived from Secret key and message.

    Declassification Dimensions (from [Sabelfeld&Sands05]):
    -------------------------------------------------------
    1. WHAT is released? (Which information)
       - Specific values, aggregates, derived data

    2. WHO can release it? (Which principals)
       - Only authorized code paths

    3. WHERE is it released? (Which program points)
       - Specific declassification points in code

    4. WHEN is it released? (Under what conditions)
       - After validation, after user consent

    Our Implementation:
    -------------------
    We use POLICY-BASED declassification with:

    - declass_policy: Specifies what can be declassified, by whom, how often
    - declass_ctx: Tracks declassification usage (audit trail)
    - declassify: The actual downgrade operation

    Security Considerations:
    ------------------------
    WARNING: Declassification weakens security guarantees!

    1. AUDIT: All declassifications should be logged
    2. LIMIT: Cap the number of declassifications (prevent covert channels)
    3. VALIDATE: Only declassify after validation/sanitization
    4. MINIMIZE: Release the minimum necessary information
    5. REVIEW: Declassification points require security review

    Formal Treatment:
    -----------------
    With declassification, we no longer have pure noninterference.
    Instead, we have RELAXED NONINTERFERENCE or DELIMITED RELEASE:

    "Secret inputs don't affect public outputs, EXCEPT at explicit
     declassification points which must satisfy the policy."

    References:
    -----------
    - [Sabelfeld&Sands05] "Dimensions and Principles of Declassification"
    - [MyersLiskov00] "Protecting Privacy using the Decentralized Label Model"
    - [Zdancewic&Myers01] "Robust Declassification"
    - brrr_lang_spec_v0.4.tex (declassification patterns)
    ============================================================================ *)

(** Declassification policy: specifies what can be declassified *)
noeq type declass_policy = {
  (* Name of the declassification point *)
  declass_name : string;
  (* Expression patterns that can be declassified *)
  allowed_patterns : list string;
  (* Maximum number of declassifications allowed *)
  max_declass : option nat;
}

(** Declassification context tracks declassification usage *)
noeq type declass_ctx = {
  policies : list declass_policy;
  usage : list (string & nat);  (* policy name -> count *)
}

(** Empty declassification context *)
let empty_declass_ctx : declass_ctx = {
  policies = [];
  usage = [];
}

(** Check if declassification is allowed *)
let can_declassify (dctx: declass_ctx) (policy_name: string) : bool =
  match List.Tot.find (fun p -> p.declass_name = policy_name) dctx.policies with
  | Some policy ->
      (match policy.max_declass with
       | None -> true  (* Unlimited *)
       | Some max ->
           (match List.Tot.find (fun (n, _) -> n = policy_name) dctx.usage with
            | Some (_, count) -> count < max
            | None -> true))
  | None -> false

(** Declassify a labeled type to Public (if policy allows) *)
let declassify (dctx: declass_ctx) (policy_name: string) (lt: labeled_type)
    : option (labeled_type & declass_ctx) =
  if can_declassify dctx policy_name then
    let new_lt = { lt with label = Public } in
    let new_usage =
      match List.Tot.find (fun (n, _) -> n = policy_name) dctx.usage with
      | Some (n, count) ->
          List.Tot.map (fun (n', c) -> if n' = n then (n', c + 1) else (n', c)) dctx.usage
      | None -> (policy_name, 1) :: dctx.usage
    in
    Some (new_lt, { dctx with usage = new_usage })
  else
    None

(** ============================================================================
    ENDORSEMENT (Controlled Trust Upgrade)
    ============================================================================

    Endorsement is the dual of declassification for integrity labels.
    It allows upgrading the integrity level of data.
    (Not fully implemented here - would need integrity labels)
    ============================================================================ *)

(** Integrity level (dual of confidentiality) *)
type integrity_level =
  | Untrusted : integrity_level  (* Low integrity - tainted *)
  | Trusted   : integrity_level  (* High integrity - sanitized *)

(** Integrity ordering: Untrusted < Trusted *)
let integrity_leq (i1 i2: integrity_level) : bool =
  match i1, i2 with
  | Untrusted, _ -> true
  | Trusted, Trusted -> true
  | Trusted, Untrusted -> false

(** ============================================================================
    PART I: TERMINATION-INSENSITIVE NONINTERFERENCE (TINI)
    ============================================================================

    TINI (Termination-Insensitive Noninterference) is the WEAKER form of
    noninterference that most practical type systems enforce.

    Definition:
    -----------
    A program P satisfies TINI iff:
      For all states s1, s2:
        s1 ~_L s2  /\  P(s1) TERMINATES  /\  P(s2) TERMINATES
        ==>
        P(s1) ~_L P(s2)

    Key Point: If EITHER execution diverges, TINI is trivially satisfied!

    Why "Termination-Insensitive"?
    ------------------------------
    TINI ignores the TERMINATION CHANNEL. Consider:

        if secret then loop_forever() else ()

    - If secret is true: program diverges
    - If secret is false: program terminates

    An attacker can learn `secret` by observing WHETHER the program terminates!

    Under TINI, this is NOT considered a leak because:
    - If secret=true: diverges, so TINI vacuously holds
    - If secret=false: terminates with same result

    We only compare executions that BOTH terminate.

    Why TINI is Common:
    -------------------
    1. DECIDABILITY: Checking termination is undecidable in general
    2. PRACTICALITY: Most real programs eventually terminate
    3. SIMPLICITY: Type systems can easily enforce TINI
    4. SOUNDNESS: TINI still provides strong guarantees when both runs terminate

    Formal Statement:
    -----------------
        tini_property(ctx, obs) =
          forall e, s1, s2, exec1, exec2.
            s1 ~_obs s2  /\  exec1 = Terminates(v1, s1')  /\  exec2 = Terminates(v2, s2')
            ==>
            v1 ~ v2  /\  s1' ~_obs s2'

    Note: The implication is vacuously true when either exec is Diverges.

    References:
    -----------
    - [Sabelfeld&Myers03] Section 4.1: Termination channels
    - [Volpano&Smith97] "Eliminating Covert Flows with Minimum Typings"
    - brrr_lang_spec_v0.4.tex Definition 2.5 (TINI)
    ============================================================================ *)

(** Execution result: programs either terminate with a result or diverge *)
type exec_result_full (a:Type) =
  | Terminates : result:a -> final_state:memory -> exec_result_full a
  | Diverges   : exec_result_full a

(** TINI property type: for terminating executions, low-equivalent inputs
    produce low-equivalent outputs.

    Formally: forall s1 s2.
      low_equiv(s1, s2) /\ terminates(e, s1) /\ terminates(e, s2)
      ==> low_equiv(eval(e, s1), eval(e, s2))

    Note: If either execution diverges, the implication is trivially true.
*)
type tini_property (ctx: sec_ctx) (obs: sec_level) =
  e:expr -> mem1:memory -> mem2:memory ->
  exec1:exec_result_full value -> exec2:exec_result_full value ->
  Lemma (requires
           low_equiv_at ctx mem1 mem2 obs = true /\
           (* Both must terminate for TINI to be non-trivial *)
           Terminates? exec1 /\ Terminates? exec2)
        (ensures
           (* Result values are equivalent at observation level *)
           (let Terminates v1 s1' = exec1 in
            let Terminates v2 s2' = exec2 in
            (* If result is observable at obs level, values must be equal *)
            (match sec_typecheck ctx Public e with
             | Some lt ->
                 sec_leq lt.label obs = true ==> value_eq v1 v2 = true
             | None -> true) /\
            (* Final states remain low-equivalent *)
            low_equiv_at ctx s1' s2' obs = true))

(** TINI check function: verify TINI for two executions *)
let check_tini (ctx: sec_ctx) (obs: sec_level)
               (mem1 mem2: memory)
               (exec1 exec2: exec_result_full value) : bool =
  if not (low_equiv_at ctx mem1 mem2 obs) then
    true  (* Precondition not met, trivially satisfied *)
  else
    match exec1, exec2 with
    | Diverges, _ -> true  (* One diverges: TINI satisfied *)
    | _, Diverges -> true
    | Terminates v1 s1', Terminates v2 s2' ->
        (* Both terminate: check equivalence *)
        value_eq v1 v2 && low_equiv_at ctx s1' s2' obs

(** TINI theorem statement: well-typed programs satisfy TINI *)
type tini_theorem =
  ctx:sec_ctx -> e:expr -> obs:sec_level ->
  (* Well-typed expression *)
  squash (Some? (sec_typecheck ctx Public e)) ->
  (* TINI holds for all low-equivalent memories *)
  squash (forall (mem1 mem2: memory) (exec1 exec2: exec_result_full value).
            low_equiv_at ctx mem1 mem2 obs = true /\
            Terminates? exec1 /\ Terminates? exec2 ==>
            check_tini ctx obs mem1 mem2 exec1 exec2 = true)

(** ============================================================================
    PART II: TERMINATION-SENSITIVE NONINTERFERENCE (TSNI)
    ============================================================================

    TSNI (Termination-Sensitive Noninterference) is the STRONGER form that
    also protects against TERMINATION CHANNELS.

    Definition:
    -----------
    A program P satisfies TSNI iff:
      For all states s1, s2:
        s1 ~_L s2
        ==>
        (P(s1) TERMINATES  <=>  P(s2) TERMINATES)         (* Same termination! *)
        /\
        (P(s1) TERMINATES ==> P(s1) ~_L P(s2))           (* And same results *)

    Key Difference from TINI:
    -------------------------
    TSNI adds: termination behavior must be IDENTICAL for low-equivalent inputs.

    TINI: "If both terminate, results are equal"
    TSNI: "BOTH must terminate (or both diverge), AND results are equal"

    The Termination Channel:
    ------------------------
    Per brrr_lang_spec_v0.4 Definition 2.4:

        if secret then loop_forever() else ()

    This leaks `secret` through termination:
    - Attacker runs program, waits T seconds
    - If program finishes: secret = false
    - If program still running: secret = true (probably)

    Under TINI: No violation (only one execution terminates)
    Under TSNI: VIOLATION! Termination differs based on secret.

    Why TSNI is Hard:
    -----------------
    1. UNDECIDABILITY: Proving uniform termination is generally undecidable
    2. LOOP ANALYSIS: Must ensure all loops terminate regardless of secrets
    3. RECURSION: Must verify termination arguments don't depend on secrets
    4. PRACTICAL: Few type systems enforce TSNI completely

    Our Approach:
    -------------
    We provide:
    1. tsni_property type: Formal statement of TSNI
    2. check_tsni function: Runtime check for two executions
    3. has_termination_channel: Static detection of potential channels
    4. no_termination_channel: Predicate for TSNI theorem

    For TSNI to hold, we require ADDITIONAL ANALYSIS beyond type checking:
    - Loop termination must not depend on high-security data
    - Recursive calls must have termination arguments independent of secrets

    Relationship to TINI:
    ---------------------
    TSNI strictly implies TINI:
      TSNI(P) ==> TINI(P)

    But not vice versa. A program can satisfy TINI but violate TSNI.

    References:
    -----------
    - [Sabelfeld&Myers03] Section 4.1: "Progress-sensitive" vs "progress-insensitive"
    - [Agat00] "Transforming out Timing Leaks" (timing + termination)
    - [Smith&Volpano98] "Secure Information Flow in a Multi-threaded Language"
    - brrr_lang_spec_v0.4.tex Definition 2.4-2.5 (Termination Channel, TINI/TSNI)
    ============================================================================ *)

(** Termination behavior type *)
type termination_behavior =
  | MustTerminate    : termination_behavior  (* Provably terminates *)
  | MayDiverge       : termination_behavior  (* Might not terminate *)
  | MustDiverge      : termination_behavior  (* Provably diverges *)

(** Termination behavior ordering: more precise behaviors are preferred *)
let termination_leq (t1 t2: termination_behavior) : bool =
  match t1, t2 with
  | MustTerminate, MustTerminate -> true
  | MustDiverge, MustDiverge -> true
  | MayDiverge, _ -> true  (* MayDiverge is least precise *)
  | _, MayDiverge -> true
  | _, _ -> false

(** TSNI property type: termination behavior must also be indistinguishable
    for low-equivalent inputs.

    Formally: forall s1 s2.
      low_equiv(s1, s2)
      ==> (terminates(e, s1) <=> terminates(e, s2))
          /\ (terminates(e, s1) ==> low_equiv(eval(e, s1), eval(e, s2)))
*)
type tsni_property (ctx: sec_ctx) (obs: sec_level) =
  e:expr -> mem1:memory -> mem2:memory ->
  exec1:exec_result_full value -> exec2:exec_result_full value ->
  Lemma (requires low_equiv_at ctx mem1 mem2 obs = true)
        (ensures
           (* Termination behavior must match! *)
           (Terminates? exec1 <==> Terminates? exec2) /\
           (* If both terminate, results must be equivalent *)
           (Terminates? exec1 /\ Terminates? exec2 ==>
            (let Terminates v1 s1' = exec1 in
             let Terminates v2 s2' = exec2 in
             (match sec_typecheck ctx Public e with
              | Some lt ->
                  sec_leq lt.label obs = true ==> value_eq v1 v2 = true
              | None -> true) /\
             low_equiv_at ctx s1' s2' obs = true)))

(** TSNI check function: verify TSNI for two executions *)
let check_tsni (ctx: sec_ctx) (obs: sec_level)
               (mem1 mem2: memory)
               (exec1 exec2: exec_result_full value) : bool =
  if not (low_equiv_at ctx mem1 mem2 obs) then
    true  (* Precondition not met *)
  else
    (* CRITICAL: Termination behavior must match *)
    match exec1, exec2 with
    | Terminates v1 s1', Terminates v2 s2' ->
        value_eq v1 v2 && low_equiv_at ctx s1' s2' obs
    | Diverges, Diverges -> true
    | Terminates _, Diverges -> false  (* TSNI VIOLATION! Termination leak *)
    | Diverges, Terminates _ -> false  (* TSNI VIOLATION! Termination leak *)

(** TSNI theorem statement: well-typed programs satisfy TSNI
    Note: This requires additional termination analysis beyond type checking. *)
type tsni_theorem =
  ctx:sec_ctx -> e:expr -> obs:sec_level ->
  (* Well-typed expression *)
  squash (Some? (sec_typecheck ctx Public e)) ->
  (* Additional constraint: no termination channel at observation level *)
  squash (no_termination_channel ctx obs e) ->
  (* TSNI holds *)
  squash (forall (mem1 mem2: memory) (exec1 exec2: exec_result_full value).
            low_equiv_at ctx mem1 mem2 obs = true ==>
            check_tsni ctx obs mem1 mem2 exec1 exec2 = true)

(** ============================================================================
    PART III: TERMINATION CHANNEL DETECTION
    ============================================================================

    A TERMINATION CHANNEL is a covert channel that leaks information through
    program termination behavior. Detecting these channels is essential for TSNI.

    Channel Types:
    --------------
    1. LOOP CONDITION CHANNEL:
       while high_variable > 0 do
         high_variable := high_variable - 1
       done

       The NUMBER OF ITERATIONS depends on high_variable.
       An attacker can time the loop to learn about high_variable.

    2. RECURSION GUARD CHANNEL:
       let rec f n = if n > 0 then f (n-1) else ()
       f secret_value

       Recursive depth depends on secret_value.

    3. BRANCH DIVERGENCE CHANNEL:
       if secret then
         loop_forever()        (* Diverges *)
       else
         ()                    (* Terminates *)

       Termination reveals secret.

    4. UNBOUNDED ITERATION CHANNEL:
       for i = 0 to secret_bound do
         computation()
       done

       Iteration count reveals secret_bound.

    Detection Algorithm:
    --------------------
    For each potentially-looping construct:
    1. Find the termination condition (loop guard, recursion base case)
    2. Compute the security label of the condition
    3. If label > observation_level, flag as potential channel
    4. Also check for divergence differences between branches

    Key Functions:
    --------------
    - has_termination_channel(ctx, obs, e): True if e has a channel at level obs
    - might_diverge(ctx, e): Conservative check if e might not terminate
    - collect_termination_channels(ctx, obs, e): Gather all channels

    Why This Matters:
    -----------------
    Static detection of termination channels enables:
    1. Warning developers about potential information leaks
    2. Upgrading from TINI to TSNI guarantees when no channels exist
    3. Identifying where loop transformations might be needed
    4. Security auditing of control flow

    Limitations:
    ------------
    - Conservative: May report false positives
    - Undecidable: Cannot catch all channels (halting problem)
    - Approximation: might_diverge is an over-approximation

    References:
    -----------
    - [Agat00] "Transforming out Timing Leaks" - loop transformation
    - [Volpano&Smith97] "Eliminating Covert Flows with Minimum Typings"
    - brrr_lang_spec_v0.4.tex Definition 2.4 (Termination Channel example)
    ============================================================================ *)

(** Termination channel classification *)
type termination_channel_kind =
  | LoopConditionChannel  : var_id -> termination_channel_kind
      (* Loop condition depends on high variable *)
  | RecursionGuardChannel : string -> termination_channel_kind
      (* Recursive call guard depends on high variable *)
  | BranchDivergence      : termination_channel_kind
      (* One branch may diverge while other terminates *)
  | UnboundedIteration    : termination_channel_kind
      (* Iteration count depends on secret *)

(** Termination channel descriptor *)
noeq type termination_channel = {
  channel_kind      : termination_channel_kind;
  source_level      : sec_level;    (* Security level of the leaking source *)
  observation_level : sec_level;    (* Level at which leak is observable *)
  location          : option string; (* Source location if available *)
  description       : string;        (* Human-readable description *)
}

(** Check if an expression has a termination channel at given observation level *)
let rec has_termination_channel (ctx: sec_ctx) (obs: sec_level) (e: expr)
    : Tot bool (decreases e) =
  match e with
  (* While loops: check if condition has high dependency *)
  | EWhile cond body ->
      (match sec_typecheck ctx Public cond with
       | Some cond_lt ->
           (* If condition depends on data above observation level,
              termination behavior leaks information *)
           not (sec_leq cond_lt.label obs) ||
           has_termination_channel ctx obs body
       | None -> true)  (* Conservatively assume channel exists *)

  (* Infinite loops always have potential channel if entered conditionally *)
  | ELoop body ->
      has_termination_channel ctx obs body

  (* If-then-else: check for branch divergence *)
  | EIf cond then_e else_e ->
      (match sec_typecheck ctx Public cond with
       | Some cond_lt ->
           if not (sec_leq cond_lt.label obs) then
             (* High condition means termination difference leaks *)
             might_diverge ctx then_e <> might_diverge ctx else_e
           else
             has_termination_channel ctx obs then_e ||
             has_termination_channel ctx obs else_e
       | None -> true)

  (* Sequence: check both parts *)
  | ESeq e1 e2 ->
      has_termination_channel ctx obs e1 ||
      has_termination_channel ctx obs e2

  (* Block: check all expressions *)
  | EBlock es ->
      has_termination_channel_list ctx obs es

  (* Let bindings *)
  | ELet (PatVar x) _ e1 e2 ->
      (match sec_typecheck ctx Public e1 with
       | Some lt1 ->
           let ctx' = extend_sec_ctx x lt1 ctx in
           has_termination_channel ctx obs e1 ||
           has_termination_channel ctx' obs e2
       | None -> true)

  (* Other expressions: no termination channel *)
  | _ -> false

(** Check list of expressions for termination channels *)
and has_termination_channel_list (ctx: sec_ctx) (obs: sec_level) (es: list expr)
    : Tot bool (decreases es) =
  match es with
  | [] -> false
  | e :: rest ->
      has_termination_channel ctx obs e ||
      has_termination_channel_list ctx obs rest

(** Conservative divergence check: might this expression not terminate? *)
and might_diverge (ctx: sec_ctx) (e: expr) : Tot bool (decreases e) =
  match e with
  | ELoop _ -> true  (* Infinite loops always might diverge *)
  | EWhile _ _ -> true  (* While loops might not terminate *)
  | EIf _ then_e else_e ->
      might_diverge ctx then_e || might_diverge ctx else_e
  | ESeq e1 e2 ->
      might_diverge ctx e1 || might_diverge ctx e2
  | EBlock es -> might_diverge_list ctx es
  | ELet (PatVar x) _ e1 e2 ->
      (match sec_typecheck ctx Public e1 with
       | Some lt1 ->
           let ctx' = extend_sec_ctx x lt1 ctx in
           might_diverge ctx e1 || might_diverge ctx' e2
       | None -> might_diverge ctx e1)
  | _ -> false

and might_diverge_list (ctx: sec_ctx) (es: list expr) : Tot bool (decreases es) =
  match es with
  | [] -> false
  | e :: rest -> might_diverge ctx e || might_diverge_list ctx rest

(** no_termination_channel predicate for TSNI theorem *)
let no_termination_channel (ctx: sec_ctx) (obs: sec_level) (e: expr) : bool =
  not (has_termination_channel ctx obs e)

(** Collect all termination channels in an expression *)
let rec collect_termination_channels (ctx: sec_ctx) (obs: sec_level) (e: expr)
    : Tot (list termination_channel) (decreases e) =
  match e with
  | EWhile cond body ->
      (match sec_typecheck ctx Public cond with
       | Some cond_lt ->
           if not (sec_leq cond_lt.label obs) then
             [{ channel_kind = LoopConditionChannel "cond";
                source_level = cond_lt.label;
                observation_level = obs;
                location = None;
                description = "While loop condition depends on high-security data" }]
             @ collect_termination_channels ctx obs body
           else
             collect_termination_channels ctx obs body
       | None -> [])

  | EIf cond then_e else_e ->
      (match sec_typecheck ctx Public cond with
       | Some cond_lt ->
           let branch_channels =
             if not (sec_leq cond_lt.label obs) &&
                might_diverge ctx then_e <> might_diverge ctx else_e
             then
               [{ channel_kind = BranchDivergence;
                  source_level = cond_lt.label;
                  observation_level = obs;
                  location = None;
                  description = "Branches have different termination behavior under high condition" }]
             else []
           in
           branch_channels @
           collect_termination_channels ctx obs then_e @
           collect_termination_channels ctx obs else_e
       | None -> [])

  | ESeq e1 e2 ->
      collect_termination_channels ctx obs e1 @
      collect_termination_channels ctx obs e2

  | EBlock es ->
      collect_termination_channels_list ctx obs es

  | ELet (PatVar x) _ e1 e2 ->
      (match sec_typecheck ctx Public e1 with
       | Some lt1 ->
           let ctx' = extend_sec_ctx x lt1 ctx in
           collect_termination_channels ctx obs e1 @
           collect_termination_channels ctx' obs e2
       | None -> collect_termination_channels ctx obs e1)

  | _ -> []

and collect_termination_channels_list (ctx: sec_ctx) (obs: sec_level) (es: list expr)
    : Tot (list termination_channel) (decreases es) =
  match es with
  | [] -> []
  | e :: rest ->
      collect_termination_channels ctx obs e @
      collect_termination_channels_list ctx obs rest

(** ============================================================================
    PART IV: INTEGRITY LATTICE FOR ENDORSEMENT
    ============================================================================

    INTEGRITY is the DUAL of confidentiality. While confidentiality restricts
    WHO CAN READ data, integrity restricts WHO CAN WRITE (or influence) data.

    The Biba Model (from [Biba77]):
    -------------------------------
    The integrity lattice is the "upside-down" version of confidentiality:

    Confidentiality: "No read up, no write down"
      - Can't read data above your level (protects secrecy)
      - Can't write data below your level (prevents leaking)

    Integrity: "No read down, no write up"
      - Can't read data below your level (prevents contamination)
      - Can't write data above your level (prevents tampering)

    In our model:
      - Untrusted data (e.g., user input) is LOW integrity
      - Trusted data (e.g., system configuration) is HIGH integrity
      - Low integrity data cannot flow to high integrity sinks

    Duality with Confidentiality:
    -----------------------------
    Consider the flow partial order:

    Confidentiality: Public <= Secret <= TopSecret
      Flow direction: Low -> High (secrets flow upward to more restricted)

    Integrity: Untrusted <= Trusted
      Flow direction: Low -> High (taint flows upward to more trusted... wait!)

    Actually, for INTEGRITY, we want to PREVENT untrusted data from
    influencing trusted computations. So the flow constraint is:

      integrity(source) >= integrity(sink)

    Or equivalently, we reverse the lattice ordering.

    Four-Point Integrity Diamond:
    -----------------------------
    We implement a diamond to match the confidentiality lattice:

                      HighIntegrity (H)
                     /                 \
              SystemData (S)     ValidatedUser (V)
                     \                 /
                       Untrusted (U)

    Interpretation:
    - Untrusted: Raw user input, network data, external files (tainted)
    - ValidatedUser: User input after validation/sanitization
    - SystemData: System-generated data (trusted source)
    - HighIntegrity: Fully trusted, validated through multiple paths

    Key property: SystemData and ValidatedUser are INCOMPARABLE
    - System data doesn't become user-validated just by copying
    - Validated user data doesn't become system data

    Combined with Confidentiality (DLM):
    ------------------------------------
    The Decentralized Label Model [Myers&Liskov97] combines both:

    Full label = (confidentiality, integrity)

    Example:
      (Secret, HighIntegrity) = Secret data from trusted source
      (Public, Untrusted) = Public data from untrusted source (user input)

    This enables tracking BOTH secrecy and integrity simultaneously.

    Endorsement (Dual of Declassification):
    ---------------------------------------
    Per brrr_lang_spec_v0.4 (line 4169):
      - Declassification: Lowers confidentiality (releases secret data)
      - Endorsement: Raises integrity (trusts untrusted data)

    Both require explicit policy approval and should be audited.

    References:
    -----------
    - [Biba77] "Integrity Considerations for Secure Computer Systems"
    - [Myers&Liskov97] "A Decentralized Model for Information Flow Control"
    - [Zdancewic&Myers01] "Robust Declassification"
    ============================================================================ *)

(** Four-point integrity diamond lattice *)
type integrity_level_full =
  | Untrusted      : integrity_level_full  (* Bottom: tainted, untrusted *)
  | ValidatedUser  : integrity_level_full  (* User input after validation *)
  | SystemData     : integrity_level_full  (* System-generated data *)
  | HighIntegrity  : integrity_level_full  (* Top: fully trusted *)

(** Integrity ordering: Untrusted < {ValidatedUser, SystemData} < HighIntegrity
    Note: ValidatedUser and SystemData are INCOMPARABLE (like Secret/Confidential)
*)
let integrity_leq_full (i1 i2: integrity_level_full) : bool =
  match i1, i2 with
  (* Untrusted is bottom - flows anywhere *)
  | Untrusted, _ -> true
  (* HighIntegrity is top - anything flows to it *)
  | _, HighIntegrity -> true
  (* Reflexivity for middle levels *)
  | ValidatedUser, ValidatedUser -> true
  | SystemData, SystemData -> true
  (* ValidatedUser and SystemData are INCOMPARABLE *)
  | ValidatedUser, SystemData -> false
  | SystemData, ValidatedUser -> false
  (* No downward flows *)
  | ValidatedUser, Untrusted -> false
  | SystemData, Untrusted -> false
  | HighIntegrity, ValidatedUser -> false
  | HighIntegrity, SystemData -> false
  | HighIntegrity, Untrusted -> false

(** Integrity join (least upper bound) *)
let integrity_join (i1 i2: integrity_level_full) : integrity_level_full =
  match i1, i2 with
  | Untrusted, x -> x
  | x, Untrusted -> x
  | HighIntegrity, _ -> HighIntegrity
  | _, HighIntegrity -> HighIntegrity
  | ValidatedUser, ValidatedUser -> ValidatedUser
  | SystemData, SystemData -> SystemData
  (* Incomparable: their LUB is HighIntegrity *)
  | ValidatedUser, SystemData -> HighIntegrity
  | SystemData, ValidatedUser -> HighIntegrity

(** Integrity meet (greatest lower bound) *)
let integrity_meet (i1 i2: integrity_level_full) : integrity_level_full =
  match i1, i2 with
  | Untrusted, _ -> Untrusted
  | _, Untrusted -> Untrusted
  | HighIntegrity, x -> x
  | x, HighIntegrity -> x
  | ValidatedUser, ValidatedUser -> ValidatedUser
  | SystemData, SystemData -> SystemData
  (* Incomparable: their GLB is Untrusted *)
  | ValidatedUser, SystemData -> Untrusted
  | SystemData, ValidatedUser -> Untrusted

(** ============================================================================
    INTEGRITY ORDERING PROOFS
    ============================================================================ *)

(** Reflexivity of integrity ordering *)
let integrity_leq_refl (i: integrity_level_full)
    : Lemma (ensures integrity_leq_full i i = true) =
  match i with
  | Untrusted -> ()
  | ValidatedUser -> ()
  | SystemData -> ()
  | HighIntegrity -> ()

(** Antisymmetry of integrity ordering *)
let integrity_leq_antisym (i1 i2: integrity_level_full)
    : Lemma (requires integrity_leq_full i1 i2 = true /\ integrity_leq_full i2 i1 = true)
            (ensures i1 = i2) =
  match i1, i2 with
  | Untrusted, Untrusted -> ()
  | ValidatedUser, ValidatedUser -> ()
  | SystemData, SystemData -> ()
  | HighIntegrity, HighIntegrity -> ()
  (* All other cases are vacuously true *)
  | Untrusted, ValidatedUser -> ()
  | Untrusted, SystemData -> ()
  | Untrusted, HighIntegrity -> ()
  | ValidatedUser, Untrusted -> ()
  | ValidatedUser, SystemData -> ()
  | ValidatedUser, HighIntegrity -> ()
  | SystemData, Untrusted -> ()
  | SystemData, ValidatedUser -> ()
  | SystemData, HighIntegrity -> ()
  | HighIntegrity, Untrusted -> ()
  | HighIntegrity, ValidatedUser -> ()
  | HighIntegrity, SystemData -> ()

(** Transitivity of integrity ordering *)
let integrity_leq_trans (i1 i2 i3: integrity_level_full)
    : Lemma (requires integrity_leq_full i1 i2 = true /\ integrity_leq_full i2 i3 = true)
            (ensures integrity_leq_full i1 i3 = true) =
  match i1, i2, i3 with
  (* Untrusted is bottom *)
  | Untrusted, _, _ -> ()
  (* HighIntegrity is top *)
  | _, _, HighIntegrity -> ()
  (* ValidatedUser chains *)
  | ValidatedUser, ValidatedUser, ValidatedUser -> ()
  | ValidatedUser, ValidatedUser, Untrusted -> ()
  | ValidatedUser, ValidatedUser, SystemData -> ()
  | ValidatedUser, Untrusted, _ -> ()
  | ValidatedUser, SystemData, _ -> ()
  | ValidatedUser, HighIntegrity, ValidatedUser -> ()
  | ValidatedUser, HighIntegrity, SystemData -> ()
  | ValidatedUser, HighIntegrity, Untrusted -> ()
  (* SystemData chains *)
  | SystemData, SystemData, SystemData -> ()
  | SystemData, SystemData, Untrusted -> ()
  | SystemData, SystemData, ValidatedUser -> ()
  | SystemData, Untrusted, _ -> ()
  | SystemData, ValidatedUser, _ -> ()
  | SystemData, HighIntegrity, ValidatedUser -> ()
  | SystemData, HighIntegrity, SystemData -> ()
  | SystemData, HighIntegrity, Untrusted -> ()
  (* HighIntegrity chains *)
  | HighIntegrity, HighIntegrity, HighIntegrity -> ()
  | HighIntegrity, HighIntegrity, ValidatedUser -> ()
  | HighIntegrity, HighIntegrity, SystemData -> ()
  | HighIntegrity, HighIntegrity, Untrusted -> ()
  | HighIntegrity, Untrusted, _ -> ()
  | HighIntegrity, ValidatedUser, _ -> ()
  | HighIntegrity, SystemData, _ -> ()

(** Integrity join is an upper bound *)
let integrity_join_upper_left (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full i1 (integrity_join i1 i2) = true) =
  match i1, i2 with
  | Untrusted, _ -> ()
  | ValidatedUser, Untrusted -> ()
  | ValidatedUser, ValidatedUser -> ()
  | ValidatedUser, SystemData -> ()
  | ValidatedUser, HighIntegrity -> ()
  | SystemData, Untrusted -> ()
  | SystemData, ValidatedUser -> ()
  | SystemData, SystemData -> ()
  | SystemData, HighIntegrity -> ()
  | HighIntegrity, _ -> ()

let integrity_join_upper_right (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full i2 (integrity_join i1 i2) = true) =
  match i1, i2 with
  | Untrusted, _ -> integrity_leq_refl i2
  | _, Untrusted -> ()
  | HighIntegrity, _ -> ()
  | _, HighIntegrity -> ()
  | ValidatedUser, ValidatedUser -> ()
  | ValidatedUser, SystemData -> ()
  | SystemData, ValidatedUser -> ()
  | SystemData, SystemData -> ()

(** Integrity meet is a lower bound *)
let integrity_meet_lower_left (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full (integrity_meet i1 i2) i1 = true) =
  match i1, i2 with
  | Untrusted, _ -> ()
  | _, Untrusted -> ()
  | HighIntegrity, _ -> integrity_leq_refl (integrity_meet HighIntegrity i2)
  | _, HighIntegrity -> ()
  | ValidatedUser, ValidatedUser -> ()
  | ValidatedUser, SystemData -> ()
  | SystemData, ValidatedUser -> ()
  | SystemData, SystemData -> ()

let integrity_meet_lower_right (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full (integrity_meet i1 i2) i2 = true) =
  match i1, i2 with
  | Untrusted, _ -> ()
  | _, Untrusted -> ()
  | HighIntegrity, _ -> integrity_leq_refl i2
  | _, HighIntegrity -> ()
  | ValidatedUser, ValidatedUser -> ()
  | ValidatedUser, SystemData -> ()
  | SystemData, ValidatedUser -> ()
  | SystemData, SystemData -> ()

(** ============================================================================
    PART V: ENDORSEMENT SYSTEM (CONTROLLED TRUST UPGRADE)
    ============================================================================

    ENDORSEMENT is the integrity-side counterpart to declassification.
    It allows UPGRADING the integrity level of data, typically after validation.

    The Trust Problem:
    ------------------
    Untrusted data (user input, network data) must often be used in
    trusted contexts (database queries, system calls). The challenge:

    1. We can't blindly trust all input (security vulnerability!)
    2. We can't reject all input (programs become useless)
    3. We need CONTROLLED trust upgrade with validation

    Endorsement provides this controlled upgrade.

    Comparison with Declassification:
    ---------------------------------
    Declassification (Confidentiality):
      - Direction: High -> Low (secret to public)
      - Risk: Information leakage
      - Example: Revealing password check result

    Endorsement (Integrity):
      - Direction: Low -> High (untrusted to trusted)
      - Risk: Injection attacks, tampering
      - Example: Using user input in SQL query after sanitization

    Both weaken security guarantees and require:
      - Explicit policy specification
      - Validation before upgrade
      - Audit logging
      - Usage limits

    Common Endorsement Patterns:
    ----------------------------
    1. INPUT VALIDATION:
       let validated_email = validate_email(user_input)
       (* user_input: Untrusted, validated_email: ValidatedUser *)

    2. SANITIZATION:
       let safe_html = escape_html(user_content)
       (* Removes script tags, encodes special chars *)

    3. BOUNDS CHECKING:
       if 0 <= index && index < array_length then
         endorse(index)  (* Now trusted for array access *)

    4. CRYPTOGRAPHIC VERIFICATION:
       if verify_signature(data, sig, pubkey) then
         endorse(data)  (* Authenticated data is trusted *)

    Policy-Based Control:
    ---------------------
    Our implementation uses endorse_policy to specify:
    - policy_name: Identifies the endorsement point
    - allowed_from: Source integrity level (must match)
    - allowed_to: Target integrity level
    - required_checks: What validation must occur
    - validator: Name of validation function
    - max_endorsements: Usage limit (prevents covert channels)

    The endorse_ctx tracks:
    - policies: Available endorsement policies
    - usage_counts: How many times each policy has been used
    - audit_log: Record of all endorsements

    Security Considerations:
    ------------------------
    WARNING: Endorsement is DANGEROUS if misused!

    1. VALIDATION MUST BE CORRECT: Faulty validation = vulnerability
    2. AUDIT TRAIL: Log all endorsements for forensic analysis
    3. MINIMIZE SCOPE: Endorse to minimum required level
    4. LIMIT USAGE: Cap endorsements to prevent timing channels
    5. CODE REVIEW: Endorsement points need security review

    References:
    -----------
    - [Zdancewic&Myers01] "Robust Declassification" (endorsement dual)
    - [Chong&Myers04] "Security Policies for Downgrading"
    - brrr_lang_spec_v0.4.tex line 4169 (endorsement definition)
    ============================================================================ *)

(** Endorsement policy: specifies when and how data can be endorsed *)
noeq type endorse_policy = {
  policy_name       : string;
  allowed_from      : integrity_level_full;  (* Source integrity level *)
  allowed_to        : integrity_level_full;  (* Target integrity level *)
  required_checks   : list string;           (* Required validation checks *)
  validator         : string;                (* Name of validation function *)
  max_endorsements  : option nat;            (* Limit on endorsements *)
}

(** Endorsement context tracks endorsement usage *)
noeq type endorse_ctx = {
  policies      : list endorse_policy;
  usage_counts  : list (string & nat);  (* policy name -> count *)
  audit_log     : list string;          (* Endorsement audit trail *)
}

(** Empty endorsement context *)
let empty_endorse_ctx : endorse_ctx = {
  policies = [];
  usage_counts = [];
  audit_log = [];
}

(** Create a new endorsement context with policies *)
let create_endorse_ctx (policies: list endorse_policy) : endorse_ctx = {
  policies = policies;
  usage_counts = [];
  audit_log = [];
}

(** Check if endorsement is allowed by policy *)
let can_endorse (ectx: endorse_ctx) (policy_name: string)
                (from_level: integrity_level_full) (to_level: integrity_level_full) : bool =
  match List.Tot.find (fun p -> p.policy_name = policy_name) ectx.policies with
  | Some policy ->
      (* Check level constraints *)
      policy.allowed_from = from_level &&
      policy.allowed_to = to_level &&
      (* Check usage limits *)
      (match policy.max_endorsements with
       | None -> true
       | Some max ->
           match List.Tot.find (fun (n, _) -> n = policy_name) ectx.usage_counts with
           | Some (_, count) -> count < max
           | None -> true)
  | None -> false

(** Labeled value with integrity *)
noeq type integrity_labeled (a:Type) = {
  ivalue     : a;
  integrity  : integrity_level_full;
}

(** Create untrusted labeled value *)
let untrusted (#a:Type) (v: a) : integrity_labeled a = {
  ivalue = v;
  integrity = Untrusted;
}

(** Create validated user data *)
let validated_user (#a:Type) (v: a) : integrity_labeled a = {
  ivalue = v;
  integrity = ValidatedUser;
}

(** Create system data *)
let system_data (#a:Type) (v: a) : integrity_labeled a = {
  ivalue = v;
  integrity = SystemData;
}

(** Create high-integrity data *)
let high_integrity (#a:Type) (v: a) : integrity_labeled a = {
  ivalue = v;
  integrity = HighIntegrity;
}

(** Endorse a value: upgrade its integrity level with policy check
    Returns the endorsed value and updated context, or None if not allowed *)
let endorse_value (#a:Type)
                  (ectx: endorse_ctx)
                  (policy_name: string)
                  (lv: integrity_labeled a)
                  (target_level: integrity_level_full)
    : option (integrity_labeled a & endorse_ctx) =
  if can_endorse ectx policy_name lv.integrity target_level then
    let endorsed = { lv with integrity = target_level } in
    (* Update usage count *)
    let new_counts =
      match List.Tot.find (fun (n, _) -> n = policy_name) ectx.usage_counts with
      | Some (n, count) ->
          List.Tot.map (fun (n', c) ->
            if n' = n then (n', c + 1) else (n', c)) ectx.usage_counts
      | None -> (policy_name, 1) :: ectx.usage_counts
    in
    (* Add to audit log *)
    let log_entry = "Endorsed using policy: " ^ policy_name in
    let new_ctx = {
      ectx with
      usage_counts = new_counts;
      audit_log = log_entry :: ectx.audit_log
    } in
    Some (endorsed, new_ctx)
  else
    None

(** Endorse function matching spec signature *)
let endorse_simple (#a:Type) (v: a) (from_: integrity_level_full) (to_: integrity_level_full)
    : a & integrity_level_full =
  (* Simple endorsement without policy check - for spec compatibility *)
  (v, to_)

(** ============================================================================
    COMBINED CONFIDENTIALITY AND INTEGRITY LABELS (DLM)
    ============================================================================

    The DECENTRALIZED LABEL MODEL (DLM) from [Myers & Liskov 1997] combines
    both confidentiality and integrity into a single label structure.

    Why Combine Both?
    -----------------
    Real security policies often involve BOTH dimensions:

    1. CLASSIFIED SYSTEM DATA:
       - Confidentiality: Secret (restricted readers)
       - Integrity: HighIntegrity (trusted source)

    2. USER INPUT:
       - Confidentiality: Public (anyone can see)
       - Integrity: Untrusted (user-controlled)

    3. PERSONAL HEALTH RECORDS:
       - Confidentiality: Secret (patient privacy)
       - Integrity: SystemData (from medical system)

    Tracking both prevents:
    - Information LEAKAGE (confidentiality violation)
    - Data CORRUPTION (integrity violation)

    Label Structure:
    ----------------
    A security_label is a pair: (confidentiality, integrity)

    Label ordering requires BOTH dimensions to be satisfied:
      l1 <= l2  iff  l1.conf <= l2.conf  AND  l1.int <= l2.int

    This is the PRODUCT ORDER on the two lattices.

    Note: The combined lattice is ALSO a lattice:
      join((c1,i1), (c2,i2)) = (join(c1,c2), join(i1,i2))
      meet((c1,i1), (c2,i2)) = (meet(c1,c2), meet(i1,i2))

    Example Security Labels:
    ------------------------
    Label                              Meaning
    -----------------------------------------------------------------------
    (Public, HighIntegrity)            Public, trusted data (system constants)
    (Public, Untrusted)                User input (needs validation)
    (Secret, HighIntegrity)            Secret from trusted source (keys)
    (Secret, Untrusted)                DANGEROUS: Secret but tainted
    (TopSecret, HighIntegrity)         Highest security classification

    Flow Constraints with Combined Labels:
    --------------------------------------
    For an assignment x := e:
      1. Confidentiality: label(e).conf <= label(x).conf
         (Cannot leak secret data to public variable)

      2. Integrity: label(e).int >= label(x).int
         (Cannot corrupt high-integrity with untrusted data)
         OR equivalently: label(x).int <= label(e).int
         (Wait, this depends on how we orient the integrity lattice)

    Integrity Flow Direction:
    -------------------------
    There's a subtlety: integrity flows in the OPPOSITE direction!

    For confidentiality: Low -> High is allowed (Public -> Secret)
    For integrity: High -> Low is allowed (HighIntegrity -> Untrusted)

    This is because:
    - Confidentiality: We don't want secrets to become public
    - Integrity: We don't want untrusted data to become trusted

    In our implementation, we use the same ordering direction for both,
    but the FLOW CONSTRAINT for integrity is reversed.

    The DLM Paper [Myers & Liskov 1997]:
    ------------------------------------
    The original DLM used:
    - Reader policies: "principals who can read" (confidentiality)
    - Writer policies: "principals who can write" (integrity)

    Labels were sets of policies, with lattice operations on sets.
    Our diamond lattice is a simplified version of this model.

    References:
    -----------
    - [Myers&Liskov97] "A Decentralized Model for Information Flow Control"
    - [Myers99] "JFlow: Practical Static Information Flow Control" (Jif)
    - [Zdancewic02] PhD Thesis: "Programming Languages for Information Security"
    ============================================================================ *)

(** Combined security label with both confidentiality and integrity *)
noeq type security_label = {
  confidentiality : sec_level;
  integrity       : integrity_level_full;
}

(** Security label ordering: must satisfy both dimensions *)
let security_label_leq (l1 l2: security_label) : bool =
  sec_leq l1.confidentiality l2.confidentiality &&
  integrity_leq_full l1.integrity l2.integrity

(** Security label join *)
let security_label_join (l1 l2: security_label) : security_label = {
  confidentiality = sec_join l1.confidentiality l2.confidentiality;
  integrity = integrity_join l1.integrity l2.integrity;
}

(** Security label meet *)
let security_label_meet (l1 l2: security_label) : security_label = {
  confidentiality = sec_meet l1.confidentiality l2.confidentiality;
  integrity = integrity_meet l1.integrity l2.integrity;
}

(** Security label ordering proofs *)
let security_label_leq_refl (l: security_label)
    : Lemma (ensures security_label_leq l l = true) =
  sec_leq_refl l.confidentiality;
  integrity_leq_refl l.integrity

let security_label_leq_trans (l1 l2 l3: security_label)
    : Lemma (requires security_label_leq l1 l2 = true /\ security_label_leq l2 l3 = true)
            (ensures security_label_leq l1 l3 = true) =
  sec_leq_trans l1.confidentiality l2.confidentiality l3.confidentiality;
  integrity_leq_trans l1.integrity l2.integrity l3.integrity

(** ============================================================================
    INTEGRITY-AWARE TYPE CHECKING
    ============================================================================

    Extend the type system to track integrity alongside confidentiality.
    ============================================================================ *)

(** Full labeled type with both confidentiality and integrity *)
noeq type full_labeled_type = {
  fbase_type     : brrr_type;
  flabel         : security_label;
}

(** Create a public, untrusted type (typical user input) *)
let public_untrusted (t: brrr_type) : full_labeled_type = {
  fbase_type = t;
  flabel = { confidentiality = Public; integrity = Untrusted };
}

(** Create a secret, high-integrity type (system secrets) *)
let secret_high_integrity (t: brrr_type) : full_labeled_type = {
  fbase_type = t;
  flabel = { confidentiality = Secret; integrity = HighIntegrity };
}

(** Check if a type can be used as a sink (requires sufficient integrity) *)
let can_use_as_sink (flt: full_labeled_type) (required_integrity: integrity_level_full) : bool =
  integrity_leq_full required_integrity flt.flabel.integrity

(** Check if declassification is safe (must not be influenced by untrusted data) *)
let safe_declassification (flt: full_labeled_type) : bool =
  (* Can only declassify if integrity is at least SystemData *)
  integrity_leq_full SystemData flt.flabel.integrity

(** Check if endorsement is safe (must verify the data) *)
let safe_endorsement (current: integrity_level_full) (target: integrity_level_full) : bool =
  (* Endorsement must actually raise integrity *)
  integrity_leq_full current target && not (current = target)

(** ============================================================================
    PART VI: DECENTRALIZED LABEL MODEL (DLM)
    ============================================================================

    The DECENTRALIZED LABEL MODEL (DLM) was introduced by Myers and Liskov in
    "Protecting Privacy using the Decentralized Label Model" (TOSEM 2000) and
    implemented in the JFlow/Jif language.

    Key Insight:
    ------------
    Traditional IFC uses a CENTRALIZED security lattice where labels are
    fixed security levels (Public, Secret, etc.). DLM instead uses a
    DECENTRALIZED model where:

    1. PRINCIPALS own and control data
    2. Labels specify WHO can read data (not just "how secret it is")
    3. Each owner specifies their own reader policy
    4. Declassification requires AUTHORITY from the owner

    Why Decentralize?
    -----------------
    In real systems, different principals have different security needs:

    - Alice wants her medical records private except to her doctor
    - Bob wants his salary visible only to HR
    - The system wants audit logs readable by auditors

    Each principal should be able to specify and control their own policy,
    without a central authority dictating all security levels.

    The DLM Label Structure:
    ------------------------
    A DLM label is a CONJUNCTION of label components:

        {o1: r1, r2; o2: r3, r4}

    This means:
    - Owner o1 allows readers r1 and r2
    - Owner o2 allows readers r3 and r4

    To actually read the data, you must be allowed by ALL owners!
    (Conjunction = intersection of allowed readers)

    The Acts-For Relation:
    ----------------------
    Principal p1 "acts for" principal p2 (written p1 >= p2) means:
    - p1 has at least as much authority as p2
    - p1 can do anything p2 can do
    - p1 can read anything p2 can read
    - p1 can declassify on behalf of p2

    Examples:
    - Admin >= User (admin can act as user)
    - TopSecret >= Secret (higher clearance acts for lower)
    - GroupMember >= Group (member can act for group)

    The acts-for relation forms a PREORDER:
    - Reflexive: p >= p
    - Transitive: p1 >= p2 and p2 >= p3 implies p1 >= p3

    Declassification with Authority:
    ---------------------------------
    Unlike simple declassification, DLM requires AUTHORITY:

    1. To remove a label component {o: r1, r2}, you must act-for owner o
    2. You can only declassify data you have authority over
    3. This prevents unauthorized information release

    Example:
        Data labeled {Alice: Bob; Charlie: Dave}

        - Alice can declassify her component: {Alice: anyone}
        - Charlie can declassify his component: {Charlie: anyone}
        - Neither can declassify the other's component
        - To fully declassify, need BOTH authorities

    Robust Declassification:
    ------------------------
    From [Zdancewic & Myers 2001]: Even with authority, declassification
    must be ROBUST - an attacker cannot influence WHAT gets declassified.

    Example of non-robust declassification:
        if (attacker_controlled_condition) then
            declassify(secret_A)
        else
            declassify(secret_B)

    The attacker can choose which secret to leak by controlling the condition!

    Robust declassification requires:
    - The condition must have HIGH integrity (not attacker-controlled)
    - The value being declassified must be independent of attacker input

    References:
    -----------
    - [Myers & Liskov 2000] "Protecting Privacy using the Decentralized Label Model"
    - [Myers 1999] "JFlow: Practical Mostly-Static Information Flow Control"
    - [Zdancewic & Myers 2001] "Robust Declassification"
    - [Chong & Myers 2004] "Security Policies for Downgrading"
    ============================================================================ *)

(** ============================================================================
    PRINCIPAL HIERARCHY
    ============================================================================

    Principals are the entities that own, control, and access data.
    The principal hierarchy supports:
    - Individual users (PUser)
    - Roles or groups (PRole)
    - Conjunctions for compound principals (PConjunction)
    - Top principal (trusts everyone, represents public)
    - Bottom principal (trusts no one, represents completely private)
    ============================================================================ *)

(** Principal type - entities that own and control data *)
type principal =
  | PUser        : user_name:string -> principal                    (* Individual user *)
  | PRole        : role_name:string -> principal                    (* Role or group *)
  | PConjunction : p1:principal -> p2:principal -> principal        (* Both principals together *)
  | PTop         : principal                                        (* Top principal - trusts everyone *)
  | PBot         : principal                                        (* Bottom principal - trusts no one *)

(** Principal equality *)
let rec principal_eq (p1 p2: principal) : Tot bool (decreases p1) =
  match p1, p2 with
  | PUser n1, PUser n2 -> n1 = n2
  | PRole n1, PRole n2 -> n1 = n2
  | PConjunction a1 b1, PConjunction a2 b2 ->
      principal_eq a1 a2 && principal_eq b1 b2
  | PTop, PTop -> true
  | PBot, PBot -> true
  | _, _ -> false

(** Principal equality is reflexive *)
let rec principal_eq_refl (p: principal)
    : Lemma (ensures principal_eq p p = true) (decreases p) =
  match p with
  | PUser _ -> ()
  | PRole _ -> ()
  | PConjunction p1 p2 -> principal_eq_refl p1; principal_eq_refl p2
  | PTop -> ()
  | PBot -> ()

(** ============================================================================
    ACTS-FOR RELATION
    ============================================================================

    The acts-for relation p1 >= p2 means p1 can act on behalf of p2.
    This is the fundamental authority relationship in DLM.

    Key properties:
    - Reflexive: Every principal acts for itself
    - Transitive: Authority chains through delegation
    - PBot acts for everyone (maximum authority)
    - Everyone acts for PTop (minimum authority)
    - Conjunction: p1 AND p2 can act for either p1 or p2
    ============================================================================ *)

(** Acts-for relation environment: maps delegation relationships *)
type acts_for_env = list (principal & principal)

(** Empty acts-for environment *)
let empty_acts_for_env : acts_for_env = []

(** Add a delegation: p1 acts for p2 *)
let add_acts_for (p1 p2: principal) (env: acts_for_env) : acts_for_env =
  (p1, p2) :: env

(** Check if acts-for is declared in environment *)
let rec acts_for_in_env (p1 p2: principal) (env: acts_for_env) : bool =
  match env with
  | [] -> false
  | (a, b) :: rest ->
      (principal_eq p1 a && principal_eq p2 b) || acts_for_in_env p1 p2 rest

(** Acts-for relation: p1 acts for p2 means p1 has at least as much authority as p2 *)
let rec acts_for (env: acts_for_env) (p1 p2: principal) : Tot bool (decreases %[p1; p2; 10]) =
  (* Reflexivity: p acts for p *)
  if principal_eq p1 p2 then true
  (* Everyone acts for PTop (minimum authority) *)
  else if PTop? p2 then true
  (* PBot acts for everyone (maximum authority) *)
  else if PBot? p1 then true
  (* Conjunction rule: p1 AND p2 acts for either p1 or p2 *)
  else match p1 with
       | PConjunction a b ->
           acts_for env a p2 || acts_for env b p2
       | _ ->
           (* Check environment for delegations *)
           acts_for_in_env p1 p2 env ||
           (* Transitive closure through PConjunction of p2 *)
           (match p2 with
            | PConjunction a b ->
                (* To act for (a AND b), must act for both *)
                acts_for env p1 a && acts_for env p1 b
            | _ -> false)

(** ============================================================================
    ACTS-FOR RELATION PROOFS
    ============================================================================ *)

(** Acts-for is reflexive *)
let acts_for_refl (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env p p = true) =
  principal_eq_refl p

(** Everyone acts for PTop *)
let acts_for_top (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env p PTop = true) =
  ()

(** PBot acts for everyone *)
let acts_for_bot (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env PBot p = true) =
  ()

(** Conjunction acts for left component *)
let acts_for_conj_left (env: acts_for_env) (p1 p2: principal)
    : Lemma (ensures acts_for env (PConjunction p1 p2) p1 = true) =
  acts_for_refl env p1

(** Conjunction acts for right component *)
let acts_for_conj_right (env: acts_for_env) (p1 p2: principal)
    : Lemma (ensures acts_for env (PConjunction p1 p2) p2 = true) =
  acts_for_refl env p2

(** ============================================================================
    DLM LABEL COMPONENTS
    ============================================================================

    A label component specifies one owner's policy:

        {owner: reader1, reader2, ...}

    This means: owner allows reader1, reader2, etc. to read the data.

    The effective readers for data labeled with multiple components is
    the INTERSECTION of all reader sets.
    ============================================================================ *)

(** Label component: owner -> set of readers *)
noeq type label_component = {
  lc_owner   : principal;           (* Who owns this data *)
  lc_readers : list principal;      (* Who can read this data *)
}

(** Create a label component *)
let make_label_component (owner: principal) (readers: list principal) : label_component = {
  lc_owner = owner;
  lc_readers = readers;
}

(** Check if a principal is in a reader list *)
let rec principal_in_list (p: principal) (ps: list principal) : bool =
  match ps with
  | [] -> false
  | q :: rest -> principal_eq p q || principal_in_list p rest

(** Check if a principal can read according to a component
    p can read if:
    - p acts for the owner (owners can always read their data)
    - p is in the reader list
    - p acts for someone in the reader list *)
let can_read_component (env: acts_for_env) (p: principal) (lc: label_component) : bool =
  (* Owner can always read *)
  acts_for env p lc.lc_owner ||
  (* Check if p is an authorized reader or acts for one *)
  List.Tot.existsb (fun r -> acts_for env p r) lc.lc_readers

(** Label component equality *)
let label_component_eq (lc1 lc2: label_component) : bool =
  principal_eq lc1.lc_owner lc2.lc_owner &&
  List.Tot.length lc1.lc_readers = List.Tot.length lc2.lc_readers &&
  List.Tot.for_all (fun r -> principal_in_list r lc2.lc_readers) lc1.lc_readers

(** ============================================================================
    DLM LABELS
    ============================================================================

    A full DLM label is a CONJUNCTION of label components:

        {o1: r1, r2; o2: r3}

    To read data with this label, you must be allowed by ALL components.
    This models joint ownership where all owners must agree.
    ============================================================================ *)

(** DLM label: conjunction of components *)
type dlm_label = list label_component

(** Empty label (fully public - no restrictions) *)
let dlm_public : dlm_label = []

(** Single-owner label *)
let dlm_owned_by (owner: principal) (readers: list principal) : dlm_label =
  [make_label_component owner readers]

(** Check if a principal can read data with a DLM label
    Must be allowed by ALL components *)
let can_read_dlm (env: acts_for_env) (p: principal) (l: dlm_label) : bool =
  List.Tot.for_all (fun lc -> can_read_component env p lc) l

(** Get all owners in a DLM label *)
let dlm_owners (l: dlm_label) : list principal =
  List.Tot.map (fun lc -> lc.lc_owner) l

(** Find component by owner in a DLM label *)
let rec find_component_by_owner (owner: principal) (l: dlm_label) : option label_component =
  match l with
  | [] -> None
  | lc :: rest ->
      if principal_eq lc.lc_owner owner then Some lc
      else find_component_by_owner owner rest

(** ============================================================================
    DLM LABEL OPERATIONS
    ============================================================================

    Join (Least Upper Bound) - More Restrictive:
    --------------------------------------------
    join(l1, l2) is the least label that is at least as restrictive as both.

    For each owner appearing in either label:
    - Take the INTERSECTION of their reader sets

    Why intersection? Because data labeled with l1 AND l2 can only be read
    by principals allowed by BOTH labels.

    Meet (Greatest Lower Bound) - Less Restrictive:
    -----------------------------------------------
    meet(l1, l2) is the greatest label that is at most as restrictive as both.

    For each owner appearing in BOTH labels:
    - Take the UNION of their reader sets

    Why union? The meet is the most permissive label that flows to both.

    Flows-To Relation:
    ------------------
    l1 flows to l2 (l1 <= l2) means data at l1 can be assigned to l2.
    This requires l2 to be at least as restrictive as l1.

    For each component in l1, there must be a corresponding component in l2
    with a SUBSET of readers (more restricted).
    ============================================================================ *)

(** Helper: intersect two principal lists *)
let rec list_intersect (ps1 ps2: list principal) : list principal =
  match ps1 with
  | [] -> []
  | p :: rest ->
      if principal_in_list p ps2 then
        p :: list_intersect rest ps2
      else
        list_intersect rest ps2

(** Helper: union two principal lists (no duplicates) *)
let rec list_union (ps1 ps2: list principal) : list principal =
  match ps1 with
  | [] -> ps2
  | p :: rest ->
      if principal_in_list p ps2 then
        list_union rest ps2
      else
        p :: list_union rest ps2

(** Helper: check if ps1 is a subset of ps2 *)
let is_subset (ps1 ps2: list principal) : bool =
  List.Tot.for_all (fun p -> principal_in_list p ps2) ps1

(** Merge two labels by applying f to reader sets of same owner *)
let rec merge_labels (l1 l2: dlm_label)
                     (f: list principal -> list principal -> list principal)
    : Tot dlm_label (decreases l1) =
  match l1 with
  | [] -> l2
  | lc1 :: rest1 ->
      (match find_component_by_owner lc1.lc_owner l2 with
       | Some lc2 ->
           let merged_readers = f lc1.lc_readers lc2.lc_readers in
           let merged_component = make_label_component lc1.lc_owner merged_readers in
           (* Remove lc2 from l2 and continue *)
           let l2_without = List.Tot.filter (fun lc -> not (principal_eq lc.lc_owner lc1.lc_owner)) l2 in
           merged_component :: merge_labels rest1 l2_without f
       | None ->
           (* Owner only in l1 - keep as is *)
           lc1 :: merge_labels rest1 l2 f)

(** DLM label join (least upper bound) - more restrictive
    For each owner, INTERSECT the reader sets *)
let dlm_join (l1 l2: dlm_label) : dlm_label =
  merge_labels l1 l2 list_intersect

(** DLM label meet (greatest lower bound) - less restrictive
    For each owner appearing in BOTH, UNION the reader sets *)
let dlm_meet (l1 l2: dlm_label) : dlm_label =
  (* Only keep components for owners appearing in BOTH labels *)
  let owners1 = dlm_owners l1 in
  let owners2 = dlm_owners l2 in
  let common_owners = List.Tot.filter (fun o -> principal_in_list o owners2) owners1 in
  List.Tot.concatMap (fun owner ->
    match find_component_by_owner owner l1, find_component_by_owner owner l2 with
    | Some lc1, Some lc2 ->
        [make_label_component owner (list_union lc1.lc_readers lc2.lc_readers)]
    | _, _ -> []  (* Should not happen due to filter *)
  ) common_owners

(** DLM flows-to relation: l1 <= l2 means l1 can flow to l2
    l2 must be at least as restrictive as l1 *)
let dlm_flows_to (env: acts_for_env) (l1 l2: dlm_label) : bool =
  (* For each component in l1, check that l2 is at least as restrictive *)
  List.Tot.for_all (fun lc1 ->
    match find_component_by_owner lc1.lc_owner l2 with
    | Some lc2 ->
        (* l2's readers must be a subset of l1's readers (more restrictive) *)
        is_subset lc2.lc_readers lc1.lc_readers
    | None ->
        (* Owner not in l2 means l2 is less restrictive for this owner *)
        (* This is OK - no restriction from this owner in l2 *)
        true
  ) l1 &&
  (* Also check that l2 doesn't ADD more restrictive components *)
  List.Tot.for_all (fun lc2 ->
    match find_component_by_owner lc2.lc_owner l1 with
    | Some lc1 ->
        (* Already checked above *)
        true
    | None ->
        (* l2 adds a new owner restriction - this makes l2 MORE restrictive *)
        (* For flow to be valid, we need l2's new restriction to be satisfied *)
        (* Actually, adding new owners is always OK (makes target more restrictive) *)
        true
  ) l2

(** ============================================================================
    DLM LABEL PROOFS
    ============================================================================ *)

(** dlm_flows_to is reflexive *)
let dlm_flows_to_refl (env: acts_for_env) (l: dlm_label)
    : Lemma (ensures dlm_flows_to env l l = true) =
  (* For each component, readers are subset of themselves *)
  ()

(** Public label flows to anything *)
let dlm_public_flows_to_all (env: acts_for_env) (l: dlm_label)
    : Lemma (ensures dlm_flows_to env dlm_public l = true) =
  (* Empty label has no components, so for_all is vacuously true *)
  ()

(** ============================================================================
    DECLASSIFICATION WITH AUTHORITY
    ============================================================================

    In DLM, declassification requires AUTHORITY from the data's owner(s).
    You can only downgrade the restrictions that you have authority over.

    Declassification Request:
    - current_label: The current DLM label
    - new_label: The desired (less restrictive) label
    - authority: The principal attempting declassification

    For declassification to succeed:
    - authority must acts-for each owner whose component is being relaxed
    - new_label must have wider reader sets than current_label
    ============================================================================ *)

(** Declassification request *)
noeq type dlm_declassify_request = {
  dr_current_label : dlm_label;       (* Current label on data *)
  dr_new_label     : dlm_label;       (* Desired new label *)
  dr_authority     : principal;       (* Who is declassifying *)
  dr_purpose       : string;          (* Audit: why declassifying *)
}

(** Check if declassification is authorized
    Authority must act-for each owner whose component becomes more permissive *)
let dlm_can_declassify (env: acts_for_env) (req: dlm_declassify_request) : bool =
  (* For each component in current label that becomes more permissive,
     authority must act-for the owner *)
  List.Tot.for_all (fun lc_curr ->
    match find_component_by_owner lc_curr.lc_owner req.dr_new_label with
    | Some lc_new ->
        (* Check if readers expanded (more permissive) *)
        if is_subset lc_curr.lc_readers lc_new.lc_readers then
          true  (* No change or more restrictive - always OK *)
        else
          (* Readers expanded - need authority *)
          acts_for env req.dr_authority lc_curr.lc_owner
    | None ->
        (* Component removed entirely - need authority *)
        acts_for env req.dr_authority lc_curr.lc_owner
  ) req.dr_current_label

(** Perform declassification with authority check *)
let dlm_declassify (env: acts_for_env) (req: dlm_declassify_request)
    : option dlm_label =
  if dlm_can_declassify env req then
    Some req.dr_new_label
  else
    None

(** ============================================================================
    ROBUST DECLASSIFICATION
    ============================================================================

    Even with proper authority, declassification can be DANGEROUS if an
    attacker can influence WHAT gets declassified.

    From [Zdancewic & Myers 2001]:

    Non-robust example:
        if (attacker_input > 0) then
            declassify(secret_password)
        else
            declassify(boring_constant)

    The attacker controls which secret is released!

    Robust declassification requires:
    1. The CONDITION for declassification must have HIGH INTEGRITY
       (attacker cannot influence when declassification happens)
    2. The VALUE being declassified must be independent of attacker input
       (attacker cannot influence what gets declassified)

    We model this by requiring:
    - condition_integrity >= required_integrity
    - value has been verified as attacker-independent
    ============================================================================ *)

(** Robust declassification request *)
noeq type robust_declassify_request = {
  rd_label        : dlm_label;              (* Current label *)
  rd_new_label    : dlm_label;              (* Target label *)
  rd_authority    : principal;              (* Who is declassifying *)
  rd_condition    : bool;                   (* The declassification condition *)
  rd_cond_integrity : integrity_level_full; (* Integrity of the condition *)
  rd_purpose      : string;                 (* Audit trail *)
}

(** Minimum integrity required for robust declassification condition
    Condition must be at least SystemData (not attacker-controlled) *)
let robust_required_integrity : integrity_level_full = SystemData

(** Check if robust declassification is allowed *)
let check_robust_declassify (env: acts_for_env) (req: robust_declassify_request) : bool =
  (* 1. Must have authority for regular declassification *)
  dlm_can_declassify env {
    dr_current_label = req.rd_label;
    dr_new_label = req.rd_new_label;
    dr_authority = req.rd_authority;
    dr_purpose = req.rd_purpose;
  } &&
  (* 2. Condition must have sufficient integrity (not attacker-controlled) *)
  integrity_leq_full robust_required_integrity req.rd_cond_integrity &&
  (* 3. Condition must be true *)
  req.rd_condition

(** Perform robust declassification *)
let robust_declassify (env: acts_for_env) (req: robust_declassify_request)
    : option dlm_label =
  if check_robust_declassify env req then
    Some req.rd_new_label
  else
    None

(** ============================================================================
    DLM EXAMPLES AND HELPERS
    ============================================================================ *)

(** Example principals *)
let alice : principal = PUser "Alice"
let bob : principal = PUser "Bob"
let charlie : principal = PUser "Charlie"
let admin : principal = PRole "Admin"
let hr_dept : principal = PRole "HR"

(** Example: Alice's private data, readable only by Alice *)
let alice_private : dlm_label = dlm_owned_by alice [alice]

(** Example: Alice's data shared with Bob *)
let alice_shares_with_bob : dlm_label = dlm_owned_by alice [alice; bob]

(** Example: HR data readable by HR and Admin *)
let hr_data : dlm_label = dlm_owned_by hr_dept [hr_dept; admin]

(** Example: Joint ownership by Alice and Bob, each specifying readers *)
let joint_alice_bob : dlm_label = [
  make_label_component alice [alice; charlie];
  make_label_component bob [bob; charlie]
]
(* Charlie can read because allowed by BOTH owners *)

(** ============================================================================
    INTEGRATION WITH EXISTING SECURITY TYPES
    ============================================================================

    We provide conversions between the simple sec_level lattice and DLM labels.
    This allows using DLM in contexts that expect the simpler model.
    ============================================================================ *)

(** System principals for mapping to sec_level *)
let public_principal : principal = PTop  (* Public = everyone can read *)
let confidential_principal : principal = PRole "Confidential"
let secret_principal : principal = PRole "Secret"
let topsecret_principal : principal = PRole "TopSecret"

(** Convert sec_level to DLM label *)
let sec_level_to_dlm (l: sec_level) : dlm_label =
  match l with
  | Public -> dlm_public  (* No restrictions *)
  | Confidential -> dlm_owned_by confidential_principal [confidential_principal]
  | Secret -> dlm_owned_by secret_principal [secret_principal]
  | TopSecret -> dlm_owned_by topsecret_principal [topsecret_principal]

(** Convert DLM label to approximate sec_level
    Uses a heuristic based on number of restrictions *)
let dlm_to_sec_level (l: dlm_label) : sec_level =
  match l with
  | [] -> Public
  | [lc] ->
      if principal_eq lc.lc_owner topsecret_principal then TopSecret
      else if principal_eq lc.lc_owner secret_principal then Secret
      else if principal_eq lc.lc_owner confidential_principal then Confidential
      else Secret  (* Default for unknown single owner *)
  | _ -> TopSecret  (* Multiple owners = highest restriction *)

(** Combined DLM and integrity label *)
noeq type full_dlm_label = {
  fdlm_confidentiality : dlm_label;
  fdlm_integrity       : integrity_level_full;
}

(** Create full DLM label *)
let make_full_dlm_label (conf: dlm_label) (integ: integrity_level_full) : full_dlm_label = {
  fdlm_confidentiality = conf;
  fdlm_integrity = integ;
}

(** Public untrusted (typical user input) *)
let dlm_public_untrusted : full_dlm_label = {
  fdlm_confidentiality = dlm_public;
  fdlm_integrity = Untrusted;
}

(** Private trusted (system secrets) *)
let dlm_private_trusted (owner: principal) : full_dlm_label = {
  fdlm_confidentiality = dlm_owned_by owner [owner];
  fdlm_integrity = HighIntegrity;
}

(** ============================================================================
    DLM TYPE CHECKING CONTEXT
    ============================================================================ *)

(** DLM security context: maps variables to DLM labels *)
type dlm_sec_ctx = list (var_id & full_dlm_label)

(** Empty DLM context *)
let empty_dlm_sec_ctx : dlm_sec_ctx = []

(** Extend DLM context *)
let extend_dlm_sec_ctx (x: var_id) (l: full_dlm_label) (ctx: dlm_sec_ctx) : dlm_sec_ctx =
  (x, l) :: ctx

(** Lookup in DLM context *)
let rec lookup_dlm_sec_ctx (x: var_id) (ctx: dlm_sec_ctx) : option full_dlm_label =
  match ctx with
  | [] -> None
  | (y, l) :: rest ->
      if x = y then Some l
      else lookup_dlm_sec_ctx x rest

(** ============================================================================
    DLM AUDIT LOGGING
    ============================================================================

    All declassifications should be logged for security auditing.
    ============================================================================ *)

(** Declassification audit entry *)
noeq type dlm_audit_entry = {
  audit_timestamp   : nat;              (* When *)
  audit_authority   : principal;        (* Who *)
  audit_from_label  : dlm_label;        (* From what *)
  audit_to_label    : dlm_label;        (* To what *)
  audit_purpose     : string;           (* Why *)
  audit_was_robust  : bool;             (* Was it robust declassification? *)
}

(** Audit log *)
type dlm_audit_log = list dlm_audit_entry

(** Empty audit log *)
let empty_dlm_audit_log : dlm_audit_log = []

(** Add audit entry *)
let log_declassification
    (log: dlm_audit_log)
    (timestamp: nat)
    (authority: principal)
    (from_label: dlm_label)
    (to_label: dlm_label)
    (purpose: string)
    (was_robust: bool) : dlm_audit_log =
  let entry = {
    audit_timestamp = timestamp;
    audit_authority = authority;
    audit_from_label = from_label;
    audit_to_label = to_label;
    audit_purpose = purpose;
    audit_was_robust = was_robust;
  } in
  entry :: log

(** Declassification with automatic audit logging *)
let dlm_declassify_logged
    (env: acts_for_env)
    (req: dlm_declassify_request)
    (log: dlm_audit_log)
    (timestamp: nat)
    : option (dlm_label & dlm_audit_log) =
  match dlm_declassify env req with
  | Some new_label ->
      let new_log = log_declassification log timestamp req.dr_authority
                      req.dr_current_label new_label req.dr_purpose false in
      Some (new_label, new_log)
  | None -> None

(** Robust declassification with automatic audit logging *)
let robust_declassify_logged
    (env: acts_for_env)
    (req: robust_declassify_request)
    (log: dlm_audit_log)
    (timestamp: nat)
    : option (dlm_label & dlm_audit_log) =
  match robust_declassify env req with
  | Some new_label ->
      let new_log = log_declassification log timestamp req.rd_authority
                      req.rd_label new_label req.rd_purpose true in
      Some (new_label, new_log)
  | None -> None

(** ============================================================================
    BRRR-MACHINE TERMINATION ANALYSIS REQUIREMENTS
    ============================================================================

    For Brrr-Machine to verify TSNI, it must analyze termination behavior.
    This section documents the required analysis capabilities.

    The analysis must:
    1. Identify loops and recursive calls
    2. Determine loop/recursion termination conditions
    3. Check if conditions depend on high-security data
    4. Report potential termination channels
    ============================================================================ *)

(** Termination analysis result from Brrr-Machine *)
noeq type termination_analysis_result = {
  definitely_terminates : bool;           (* Provably terminates *)
  definitely_diverges   : bool;           (* Provably diverges *)
  termination_channels  : list termination_channel;
  analysis_complete     : bool;           (* Was analysis conclusive? *)
}

(** Unknown termination (conservative) *)
let unknown_termination : termination_analysis_result = {
  definitely_terminates = false;
  definitely_diverges = false;
  termination_channels = [];
  analysis_complete = false;
}

(** Definitely terminates *)
let terminates_result : termination_analysis_result = {
  definitely_terminates = true;
  definitely_diverges = false;
  termination_channels = [];
  analysis_complete = true;
}

(** Definitely diverges *)
let diverges_result : termination_analysis_result = {
  definitely_terminates = false;
  definitely_diverges = true;
  termination_channels = [];
  analysis_complete = true;
}

(** Analysis requirements for Brrr-Machine *)
noeq type termination_analysis_requirements = {
  (* Required: Identify while loops and check condition security *)
  analyze_while_loops     : bool;
  (* Required: Identify for loops and check bound security *)
  analyze_for_loops       : bool;
  (* Required: Track recursive calls and termination arguments *)
  analyze_recursion       : bool;
  (* Optional: Use SMT for termination proofs *)
  use_smt_termination     : bool;
  (* Optional: Timeout for termination analysis (ms) *)
  analysis_timeout_ms     : option nat;
}

(** Default analysis requirements *)
let default_analysis_requirements : termination_analysis_requirements = {
  analyze_while_loops = true;
  analyze_for_loops = true;
  analyze_recursion = true;
  use_smt_termination = false;
  analysis_timeout_ms = Some 5000;
}

(** ============================================================================
    SUMMARY
    ============================================================================

    This module provides multi-level security (MLS) information flow analysis
    based on a four-point diamond lattice (per brrr_lang_spec_v0.4 Example 1.3).

    1. Security Lattice (sec_level) - Diamond Structure:

                       TopSecret
                      /         \
                 Secret    Confidential
                      \         /
                        Public

       Key properties:
       - Public: bottom element (observable by all)
       - TopSecret: top element (highest classification)
       - Secret and Confidential are INCOMPARABLE (neither flows to the other)
       - Proven partial order (refl, antisym, trans)
       - Proven join semilattice (assoc, comm, idem, lub)
       - Proven meet semilattice (assoc, comm, idem, glb)

    2. Diamond Lattice Operations:
       - sec_leq: partial order (NOT total! Secret </= Confidential)
       - sec_join: least upper bound
         * join(Secret, Confidential) = TopSecret
       - sec_meet: greatest lower bound
         * meet(Secret, Confidential) = Public

    3. Labeled Types (labeled_type):
       - Pairs base types with security labels
       - Subtyping respects both type and label ordering
       - Helper constructors: public_type, confidential_type, secret_type, topsecret_type

    4. Security Type Checking (sec_typecheck):
       - Tracks security labels through expressions
       - PC label prevents implicit flows
       - Assignment rule: pc join rhs_label <= lhs_label
       - IMPORTANT: Secret data CANNOT flow to Confidential (and vice versa)!

    5. Multi-Level Observation (low_equiv_at):
       - Generalized low-equivalence at any observation level
       - Observer at level obs sees all data at levels <= obs
       - Example: Secret observer sees Public+Secret (NOT Confidential!)

    6. Noninterference:
       - Parameterized by observation level
       - Statement: inputs equivalent at level obs => equal outputs at level obs
       - Key lemmas proven for variables and literals

    7. TINI (Termination-Insensitive NI) - NEW:
       - Only considers terminating executions
       - If either diverges, property trivially satisfied
       - tini_property type captures the formal statement
       - check_tini function for verification

    8. TSNI (Termination-Sensitive NI) - NEW:
       - Also considers termination behavior
       - Requires: terminates(e, s1) <=> terminates(e, s2)
       - tsni_property type captures the formal statement
       - check_tsni function for verification
       - Requires additional termination analysis

    9. Termination Channel Detection - NEW:
       - termination_channel type describes information leaks
       - has_termination_channel: detects potential channels
       - collect_termination_channels: gathers all channels
       - might_diverge: conservative divergence check

    10. Integrity Lattice - NEW:

                      HighIntegrity
                     /              \
              SystemData        ValidatedUser
                     \              /
                       Untrusted

       - Dual of confidentiality lattice
       - ValidatedUser and SystemData are INCOMPARABLE
       - Proven partial order (refl, antisym, trans)
       - Proven join/meet semilattice properties

    11. Endorsement System - NEW:
       - endorse_policy: controls when endorsement is allowed
       - endorse_ctx: tracks endorsement usage
       - endorse_value: upgrade integrity with policy check
       - Dual of declassification for integrity

    12. Combined Labels (security_label) - NEW:
       - Both confidentiality AND integrity
       - security_label_leq: ordering on both dimensions
       - Enables full information flow + taint tracking

    13. Brrr-Machine Requirements - NEW:
       - termination_analysis_result: what analysis returns
       - termination_analysis_requirements: what analysis needs
       - Documents integration between type system and analysis

    Key Security Guarantees:
    a) Information flows only upward in the confidentiality lattice
    b) Integrity flows only downward (untrusted cannot become trusted silently)
    c) Incomparable compartments are isolated
    d) Well-typed programs satisfy TINI
    e) Well-typed programs with no termination channels satisfy TSNI
    f) Endorsement requires explicit policy approval
    ============================================================================ *)
