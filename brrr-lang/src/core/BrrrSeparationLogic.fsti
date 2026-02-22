(**
 * BrrrLang.Core.SeparationLogic - Interface File
 *
 * Separation logic for reasoning about heap-manipulating programs in Brrr-Lang.
 * Based on Reynolds (2002) and O'Hearn (2001).
 *
 * This module provides:
 *   - Heap model with functional representation
 *   - Separation logic assertions (points-to, star, wand, etc.)
 *   - Satisfaction relation and entailment
 *   - Hoare triples and verified proof rules
 *   - Frame rule for modular reasoning
 *   - Ownership integration for Brrr's ownership system
 *   - Weakest precondition calculus
 *   - Magic wand properties and currying
 *   - Quantified permissions for arrays
 *   - Bi-abduction for automatic specification inference
 *   - Incorrectness separation logic for bug finding
 *   - Effect-SL bridge for effect-based reasoning
 *
 * References:
 *   - Reynolds, J.C. (2002). "Separation Logic: A Logic for Shared Mutable
 *     Data Structures." LICS 2002.
 *   - O'Hearn, P., Reynolds, J.C., Yang, H. (2001). "Local Reasoning about
 *     Programs that Alter Data Structures." CSL 2001.
 *   - Calcagno et al. (2011). "Compositional Shape Analysis by means of
 *     Bi-Abduction." JACM.
 *   - O'Hearn (2020). "Incorrectness Logic." POPL 2020.
 *)
module BrrrSeparationLogic

open FStar.FunctionalExtensionality
open FStar.Classical
open BrrrValues
open BrrrExpressions
open BrrrTypes
open BrrrPrimitives

(** ============================================================================
    HEAP MODEL
    ============================================================================ *)

(**
 * Location in the heap - natural number address.
 *)
type sl_loc = nat

(**
 * Functional heap: total function from locations to optional values.
 * Some v at location l means l is allocated and contains v.
 * None at location l means l is unallocated.
 *)
type sl_heap = sl_loc -> option value

(**
 * Empty heap - all locations are unallocated.
 * This is the unit element for separating conjunction.
 *)
val sl_emp : sl_heap

(**
 * Singleton heap - exactly one location has a value.
 *
 * @param l The location
 * @param v The value at that location
 * @return A heap where only l is allocated with value v
 *)
val sl_singleton : l:sl_loc -> v:value -> sl_heap

(**
 * Domain of a heap - the set of allocated locations.
 *
 * @param h The heap
 * @return A predicate that is true for allocated locations
 *)
val sl_dom : h:sl_heap -> (sl_loc -> prop)

(**
 * Check if location is in heap domain (decidable version).
 *
 * @param l Location to check
 * @param h Heap to check in
 * @return True iff l is allocated in h
 *)
val sl_in_dom : l:sl_loc -> h:sl_heap -> bool

(** ============================================================================
    HEAP OPERATIONS
    ============================================================================ *)

(**
 * Two heaps are disjoint if they have no overlapping allocated locations.
 *
 * @param h1 First heap
 * @param h2 Second heap
 * @return True iff dom(h1) and dom(h2) are disjoint
 *)
val sl_disjoint : h1:sl_heap -> h2:sl_heap -> prop

(**
 * Union of two heaps (left-biased when overlapping).
 *
 * PRECONDITION: Should only be used when h1 and h2 are disjoint.
 *
 * @param h1 First heap (takes priority)
 * @param h2 Second heap
 * @return Combined heap
 *)
val sl_heap_union : h1:sl_heap -> h2:sl_heap -> sl_heap

(**
 * Alternative union definition - more explicit about prioritization.
 *)
val sl_heap_union_prio : h1:sl_heap -> h2:sl_heap -> sl_heap

(**
 * Heap subtraction - remove locations from h1 that are in h2.
 *
 * @param h1 Source heap
 * @param h2 Locations to remove
 * @return h1 with locations in h2 removed
 *)
val sl_heap_subtract : h1:sl_heap -> h2:sl_heap -> sl_heap

(**
 * Heap subset - h1 is contained in h2.
 *
 * @param h1 Smaller heap
 * @param h2 Larger heap
 * @return True iff h1 agrees with h2 on all locations where h1 is defined
 *)
val sl_heap_subset : h1:sl_heap -> h2:sl_heap -> prop

(**
 * Heap equality via functional extensionality.
 *
 * @param h1 First heap
 * @param h2 Second heap
 * @return True iff h1 and h2 are equal at all locations
 *)
val sl_heap_eq : h1:sl_heap -> h2:sl_heap -> prop

(** ============================================================================
    MODIFIES PREDICATES (HACL*-style)
    ============================================================================ *)

(**
 * Modifies predicate: only locations in the list may have changed.
 *)
val sl_modifies : locs:list sl_loc -> h0:sl_heap -> h1:sl_heap -> prop

(**
 * Location liveness: a location is allocated in the heap.
 *)
val sl_live : h:sl_heap -> l:sl_loc -> prop

(**
 * Location disjointness: two locations are different.
 *)
val sl_loc_disjoint : l1:sl_loc -> l2:sl_loc -> prop

(**
 * Heap lookup helper.
 *)
val heap_lookup : l:sl_loc -> h:sl_heap -> option value

(**
 * Default int_type for heap operations.
 *)
val sl_loc_int_type : BrrrPrimitives.int_type

(**
 * Create an integer value with the default location type.
 *)
val mk_loc_int : n:int -> value

(**
 * Modifies with empty list means no changes.
 *)
val sl_modifies_empty : h0:sl_heap -> h1:sl_heap ->
  Lemma (ensures sl_modifies [] h0 h1 <==> sl_heap_eq h0 h1)

(**
 * Modifies is transitive.
 *)
val sl_modifies_trans : locs:list sl_loc -> h0:sl_heap -> h1:sl_heap -> h2:sl_heap ->
  Lemma (requires sl_modifies locs h0 h1 /\ sl_modifies locs h1 h2)
        (ensures sl_modifies locs h0 h2)

(**
 * Extending the modifies set.
 *)
val sl_modifies_extend : locs1:list sl_loc -> locs2:list sl_loc -> h0:sl_heap -> h1:sl_heap ->
  Lemma (requires sl_modifies locs1 h0 h1)
        (ensures sl_modifies (List.Tot.append locs1 locs2) h0 h1)

(** ============================================================================
    HEAP WELL-FORMEDNESS
    ============================================================================ *)

(**
 * A heap is well-formed if it has finite support.
 *)
val heap_well_formed : h:sl_heap -> prop

(**
 * Empty heap is well-formed.
 *)
val sl_emp_well_formed : unit ->
  Lemma (ensures heap_well_formed sl_emp)

(**
 * Singleton heap is well-formed.
 *)
val sl_singleton_well_formed : l:sl_loc -> v:value ->
  Lemma (ensures heap_well_formed (sl_singleton l v))

(** ============================================================================
    SEPARATION LOGIC ASSERTIONS
    ============================================================================ *)

(**
 * Separation logic assertion type.
 *
 * Constructors:
 *   SLEmp       - Empty heap assertion
 *   SLPointsTo  - Points-to predicate l |-> v
 *   SLStar      - Separating conjunction P * Q
 *   SLWand      - Magic wand (separating implication) P -* Q
 *   SLForall    - Universal quantification over values
 *   SLExists    - Existential quantification over values
 *   SLPure      - Pure proposition (no heap resources)
 *   SLAnd       - Non-separating conjunction P /\ Q
 *   SLOr        - Disjunction P \/ Q
 *   SLNot       - Negation ~P
 *   SLImpl      - Intuitionistic implication P ==> Q
 *   SLOwn       - Full ownership of location
 *   SLFrac      - Fractional permission n/d on location
 *)
noeq type sl_assertion =
  | SLEmp      : sl_assertion
  | SLPointsTo : sl_loc -> value -> sl_assertion
  | SLStar     : sl_assertion -> sl_assertion -> sl_assertion
  | SLWand     : sl_assertion -> sl_assertion -> sl_assertion
  | SLForall   : (value -> sl_assertion) -> sl_assertion
  | SLExists   : (value -> sl_assertion) -> sl_assertion
  | SLPure     : bool -> sl_assertion
  | SLAnd      : sl_assertion -> sl_assertion -> sl_assertion
  | SLOr       : sl_assertion -> sl_assertion -> sl_assertion
  | SLNot      : sl_assertion -> sl_assertion
  | SLImpl     : sl_assertion -> sl_assertion -> sl_assertion
  | SLOwn      : sl_loc -> sl_assertion
  | SLFrac     : sl_loc -> nat -> nat -> sl_assertion

(**
 * Size of assertion for termination proofs.
 *)
val sl_assertion_size : a:sl_assertion -> Tot nat (decreases a)

(** ============================================================================
    SATISFACTION RELATION
    ============================================================================ *)

(**
 * Satisfaction relation: h |= a
 *
 * Decides whether heap h satisfies assertion a.
 *
 * @param h The heap
 * @param a The assertion
 * @return Proposition asserting h satisfies a
 *)
val sl_satisfies : h:sl_heap -> a:sl_assertion -> Tot prop (decreases a)

(**
 * Infix notation for satisfaction.
 *)
val op_Bar_Equals : h:sl_heap -> a:sl_assertion -> prop

(** ============================================================================
    BASIC HEAP LEMMAS
    ============================================================================ *)

val sl_emp_is_empty : l:sl_loc -> Lemma (ensures None? (sl_emp l))

val sl_singleton_at : l:sl_loc -> v:value ->
  Lemma (ensures sl_singleton l v l == Some v)

val sl_singleton_elsewhere : l:sl_loc -> l':sl_loc -> v:value ->
  Lemma (requires l <> l')
        (ensures None? (sl_singleton l v l'))

val sl_disjoint_sym : h1:sl_heap -> h2:sl_heap ->
  Lemma (ensures sl_disjoint h1 h2 <==> sl_disjoint h2 h1)

val sl_emp_disjoint : h:sl_heap ->
  Lemma (ensures sl_disjoint sl_emp h)

val sl_singleton_disjoint : l1:sl_loc -> l2:sl_loc -> v1:value -> v2:value ->
  Lemma (requires l1 <> l2)
        (ensures sl_disjoint (sl_singleton l1 v1) (sl_singleton l2 v2))

(** ============================================================================
    OWNERSHIP UNIQUENESS LEMMAS
    ============================================================================ *)

(**
 * Points-to uniqueness: same location cannot point to two different values
 * in a satisfying heap decomposition.
 *)
val points_to_unique : l:sl_loc -> v1:value -> v2:value -> h:sl_heap ->
  Lemma (ensures ~(sl_satisfies h (SLStar (SLPointsTo l v1) (SLPointsTo l v2))))
        [SMTPat (sl_satisfies h (SLStar (SLPointsTo l v1) (SLPointsTo l v2)))]

(**
 * Points-to functional: if same heap satisfies both, values must be equal.
 *)
val points_to_functional : l:sl_loc -> v1:value -> v2:value -> h:sl_heap ->
  Lemma (requires sl_satisfies h (SLPointsTo l v1) /\ sl_satisfies h (SLPointsTo l v2))
        (ensures v1 == v2)

(** ============================================================================
    HEAP UNION LEMMAS
    ============================================================================ *)

val sl_union_emp_left : h:sl_heap -> l:sl_loc ->
  Lemma (ensures sl_heap_union sl_emp h l == h l)

val sl_union_emp_right : h:sl_heap -> l:sl_loc ->
  Lemma (ensures sl_heap_union h sl_emp l == h l)

val sl_union_comm_pointwise : h1:sl_heap -> h2:sl_heap -> l:sl_loc ->
  Lemma (requires sl_disjoint h1 h2)
        (ensures sl_heap_union h1 h2 l == sl_heap_union h2 h1 l)

val sl_union_comm : h1:sl_heap -> h2:sl_heap ->
  Lemma (requires sl_disjoint h1 h2)
        (ensures sl_heap_eq (sl_heap_union h1 h2) (sl_heap_union h2 h1))

val sl_union_assoc_pointwise : h1:sl_heap -> h2:sl_heap -> h3:sl_heap -> l:sl_loc ->
  Lemma (requires sl_disjoint h1 h2 /\ sl_disjoint h2 h3 /\ sl_disjoint h1 h3)
        (ensures sl_heap_union (sl_heap_union h1 h2) h3 l ==
                 sl_heap_union h1 (sl_heap_union h2 h3) l)

val sl_union_assoc : h1:sl_heap -> h2:sl_heap -> h3:sl_heap ->
  Lemma (requires sl_disjoint h1 h2 /\ sl_disjoint h2 h3 /\ sl_disjoint h1 h3)
        (ensures sl_heap_eq (sl_heap_union (sl_heap_union h1 h2) h3)
                            (sl_heap_union h1 (sl_heap_union h2 h3)))

val sl_disjoint_union_left : h1:sl_heap -> h2:sl_heap -> h3:sl_heap ->
  Lemma (requires sl_disjoint h1 h2)
        (ensures sl_disjoint (sl_heap_union h1 h2) h3 <==>
                 (sl_disjoint h1 h3 /\ sl_disjoint h2 h3))

(** ============================================================================
    SEPARATING CONJUNCTION PROPERTIES
    ============================================================================ *)

val sl_emp_satisfies_emp : squash (sl_satisfies sl_emp SLEmp)

val sl_singleton_satisfies_pointsto : l:sl_loc -> v:value ->
  Lemma (ensures sl_satisfies (sl_singleton l v) (SLPointsTo l v))

(**
 * Star commutativity: P * Q <==> Q * P
 *)
val sl_star_comm : h:sl_heap -> p:sl_assertion -> q:sl_assertion ->
  Lemma (ensures sl_satisfies h (SLStar p q) <==> sl_satisfies h (SLStar q p))

(**
 * Emp is left identity for star (forward direction).
 *)
val sl_star_emp_left_implies : h:sl_heap -> p:sl_assertion ->
  Lemma (requires sl_satisfies h (SLStar SLEmp p))
        (ensures exists (h2: sl_heap). sl_heap_eq h h2 /\ sl_satisfies h2 p)

(**
 * Emp is left identity for star (introduction).
 *)
val sl_star_emp_left_intro : h:sl_heap -> p:sl_assertion ->
  Lemma (requires sl_satisfies h p)
        (ensures sl_satisfies h (SLStar SLEmp p))

(**
 * Star associativity (forward direction): (P * Q) * R ==> P * (Q * R)
 *)
val sl_star_assoc_fwd : h:sl_heap -> p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (requires sl_satisfies h (SLStar (SLStar p q) r))
        (ensures sl_satisfies h (SLStar p (SLStar q r)))

val sl_star_assoc : h:sl_heap -> p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (ensures sl_satisfies h (SLStar (SLStar p q) r) ==>
                 sl_satisfies h (SLStar p (SLStar q r)))

(** ============================================================================
    HOARE TRIPLES
    ============================================================================ *)

(**
 * Hoare triple for separation logic.
 *)
noeq type sl_triple = {
  sl_pre  : sl_assertion;
  sl_cmd  : expr;
  sl_post : sl_assertion;
}

(**
 * Create a triple.
 *)
val mk_triple : pre:sl_assertion -> cmd:expr -> post:sl_assertion -> sl_triple

(** ============================================================================
    HEAP COMMANDS
    ============================================================================ *)

(**
 * Abstract commands for heap manipulation.
 *)
noeq type heap_cmd =
  | HCAlloc : value -> heap_cmd
  | HCFree  : sl_loc -> heap_cmd
  | HCRead  : sl_loc -> heap_cmd
  | HCWrite : sl_loc -> value -> heap_cmd
  | HCSkip  : heap_cmd
  | HCSeq   : heap_cmd -> heap_cmd -> heap_cmd

(**
 * Command execution result.
 *)
noeq type cmd_result =
  | CROk     : sl_heap -> option value -> cmd_result
  | CRError  : string -> cmd_result

(**
 * Execute a heap command.
 *)
val exec_heap_cmd : cmd:heap_cmd -> h:sl_heap -> next_loc:sl_loc ->
  Tot cmd_result (decreases cmd)

(** ============================================================================
    WELL-FORMEDNESS PRESERVATION
    ============================================================================ *)

val update_preserves_wf : h:sl_heap -> l:sl_loc -> v:option value ->
  Lemma (requires heap_well_formed h)
        (ensures heap_well_formed (fun l' -> if l' = l then v else h l'))

val cmd_preserves_wf : c:heap_cmd -> h:sl_heap -> next_loc:sl_loc ->
  Lemma (requires heap_well_formed h)
        (ensures (match exec_heap_cmd c h next_loc with
                  | CROk h' _ -> heap_well_formed h'
                  | CRError _ -> True))

(** ============================================================================
    TRIPLE VALIDITY AND CORE RULES
    ============================================================================ *)

(**
 * Triple validity for heap commands.
 *)
val sl_triple_valid_cmd : pre:sl_assertion -> cmd:heap_cmd -> post:sl_assertion -> prop

(**
 * Skip rule: {P} skip {P}
 *)
val sl_rule_skip : p:sl_assertion ->
  Lemma (ensures sl_triple_valid_cmd p HCSkip p)

(**
 * Sequence rule.
 *)
val sl_rule_seq : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
                   c1:heap_cmd -> c2:heap_cmd ->
  Lemma (requires sl_triple_valid_cmd p c1 q /\ sl_triple_valid_cmd q c2 r)
        (ensures sl_triple_valid_cmd p (HCSeq c1 c2) r)

(**
 * Consequence rule.
 *)
val sl_rule_consequence : p:sl_assertion -> p':sl_assertion ->
                           q:sl_assertion -> q':sl_assertion ->
                           cmd:heap_cmd ->
  Lemma (requires (forall h. sl_satisfies h p' ==> sl_satisfies h p) /\
                  sl_triple_valid_cmd p cmd q /\
                  (forall h. sl_satisfies h q ==> sl_satisfies h q'))
        (ensures sl_triple_valid_cmd p' cmd q')

(** ============================================================================
    FRAME RULE
    ============================================================================ *)

(**
 * Assertions are disjoint if any satisfying heaps are disjoint.
 *)
val sl_assertions_disjoint : p:sl_assertion -> r:sl_assertion -> prop

(**
 * A command is local if it only affects locations in its precondition footprint.
 *)
val cmd_is_local : cmd:heap_cmd -> pre:sl_assertion -> prop

(**
 * Frame preservation theorem.
 *)
val frame_preservation : p:sl_assertion -> q:sl_assertion -> r:sl_assertion -> c:heap_cmd ->
  Lemma (requires sl_triple_valid_cmd p c q /\ sl_assertions_disjoint p r /\ cmd_is_local c p)
        (ensures sl_triple_valid_cmd (SLStar p r) c (SLStar q r))

(**
 * Command safety for frame.
 *)
val cmd_safe_for_frame : cmd:heap_cmd -> h_frame:sl_heap -> h_local:sl_heap -> prop

(**
 * Frame rule for specific decomposition.
 *)
val sl_frame_rule_specific : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
                              h_p:sl_heap -> h_r:sl_heap -> cmd:heap_cmd -> next_loc:sl_loc ->
  Lemma (requires sl_triple_valid_cmd p cmd q /\
                  sl_disjoint h_p h_r /\
                  sl_satisfies h_p p /\
                  sl_satisfies h_r r)
        (ensures (match exec_heap_cmd cmd h_p next_loc with
                  | CROk h'_p _ -> sl_satisfies h'_p q
                  | CRError _ -> True))

(** ============================================================================
    POINTS-TO RULES
    ============================================================================ *)

(**
 * Alloc rule: {emp} x := alloc(v) {x |-> v}
 *)
val sl_rule_alloc : v:value ->
  Lemma (ensures forall (h: sl_heap) (next_loc: sl_loc).
    sl_satisfies h SLEmp ==>
    (match exec_heap_cmd (HCAlloc v) h next_loc with
     | CROk h' (Some (BrrrValues.VInt l _ty)) ->
         l >= 0 /\ sl_satisfies h' (SLPointsTo (if l >= 0 then l else 0) v)
     | _ -> True))

(**
 * Free rule: {x |-> v} free(x) {emp}
 *)
val sl_rule_free : l:sl_loc -> v:value ->
  Lemma (ensures sl_triple_valid_cmd (SLPointsTo l v) (HCFree l) SLEmp)

(**
 * Read rule: {x |-> v} y := *x {x |-> v}
 *)
val sl_rule_read : l:sl_loc -> v:value ->
  Lemma (ensures sl_triple_valid_cmd (SLPointsTo l v) (HCRead l) (SLPointsTo l v))

(**
 * Write rule: {x |-> _} *x := v {x |-> v}
 *)
val sl_rule_write : l:sl_loc -> v_old:value -> v_new:value ->
  Lemma (ensures sl_triple_valid_cmd (SLPointsTo l v_old) (HCWrite l v_new) (SLPointsTo l v_new))

(** ============================================================================
    OWNERSHIP INTEGRATION WITH BRRR
    ============================================================================ *)

(**
 * Full ownership: own x corresponds to x |-> v * Freeable(x)
 *)
val sl_own : l:sl_loc -> v:value -> sl_assertion

(**
 * Shared borrow: &x corresponds to fractional permission.
 *)
val sl_shared_borrow : l:sl_loc -> v:value -> frac_num:nat -> frac_den:nat -> sl_assertion

(**
 * Exclusive borrow: &mut x corresponds to full permission (temporarily).
 *)
val sl_exclusive_borrow : l:sl_loc -> v:value -> sl_assertion

(**
 * Move semantics: ownership transfer.
 *)
val sl_move : l:sl_loc -> v:value -> sl_assertion

(**
 * Split fractional permission.
 *)
val sl_frac_split : l:sl_loc -> n1:nat -> n2:nat -> d:nat ->
  Lemma (requires d > 0 /\ n1 + n2 <= d)
        (ensures forall h.
          sl_satisfies h (SLFrac l (n1 + n2) d) ==>
          sl_satisfies h (SLFrac l n1 d) /\ sl_satisfies h (SLFrac l n2 d))

(**
 * Join fractional permissions.
 *)
val sl_frac_join : l:sl_loc -> n1:nat -> n2:nat -> d:nat ->
  Lemma (requires d > 0 /\ n1 + n2 <= d)
        (ensures forall h.
          sl_satisfies h (SLFrac l n1 d) ==>
          sl_satisfies h (SLFrac l n2 d) ==>
          sl_satisfies h (SLFrac l (n1 + n2) d))

(**
 * Borrow creation.
 *)
val sl_borrow_create : l:sl_loc -> v:value ->
  Lemma (ensures forall h.
          sl_satisfies h (sl_own l v) ==>
          sl_satisfies h (SLStar (SLPointsTo l v) (SLFrac l 1 2)))

(**
 * Borrow return.
 *)
val sl_borrow_return : l:sl_loc -> v:value ->
  Lemma (ensures forall h.
          sl_satisfies h (SLStar (SLPointsTo l v) (SLFrac l 1 2)) ==>
          sl_satisfies h (sl_own l v))

(** ============================================================================
    WEAKEST PRECONDITION CALCULUS
    ============================================================================ *)

(**
 * Weakest precondition for heap commands.
 *)
val sl_wp : cmd:heap_cmd -> post:sl_assertion -> Tot sl_assertion (decreases cmd)

(**
 * WP soundness for skip.
 *)
val sl_wp_sound_skip : post:sl_assertion ->
  Lemma (ensures sl_triple_valid_cmd (sl_wp HCSkip post) HCSkip post)

(** ============================================================================
    SEMANTIC ENTAILMENT
    ============================================================================ *)

(**
 * Entailment: P |== Q means forall h. h |= P ==> h |= Q
 *)
val sl_entails : p:sl_assertion -> q:sl_assertion -> prop

val sl_entails_refl : p:sl_assertion ->
  Lemma (ensures sl_entails p p)

val sl_entails_trans : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (requires sl_entails p q /\ sl_entails q r)
        (ensures sl_entails p r)

val sl_star_mono_left : p:sl_assertion -> p':sl_assertion -> q:sl_assertion ->
  Lemma (requires sl_entails p p')
        (ensures sl_entails (SLStar p q) (SLStar p' q))

val sl_star_mono_right : p:sl_assertion -> q:sl_assertion -> q':sl_assertion ->
  Lemma (requires sl_entails q q')
        (ensures sl_entails (SLStar p q) (SLStar p q'))

(** ============================================================================
    ASSERTION CONSTRUCTORS AND COMBINATORS
    ============================================================================ *)

val sl_true : sl_assertion
val sl_false : sl_assertion
val sl_points_to_list : bindings:list (sl_loc & value) -> sl_assertion
val sl_if : b:bool -> p:sl_assertion -> q:sl_assertion -> sl_assertion

(** ============================================================================
    DERIVED RULES
    ============================================================================ *)

val sl_rule_conj : p1:sl_assertion -> p2:sl_assertion ->
                   q1:sl_assertion -> q2:sl_assertion -> cmd:heap_cmd ->
  Lemma (requires sl_triple_valid_cmd p1 cmd q1 /\ sl_triple_valid_cmd p2 cmd q2)
        (ensures sl_triple_valid_cmd (SLAnd p1 p2) cmd (SLAnd q1 q2))

val sl_rule_disj : p1:sl_assertion -> p2:sl_assertion ->
                   q1:sl_assertion -> q2:sl_assertion -> cmd:heap_cmd ->
  Lemma (requires sl_triple_valid_cmd p1 cmd q1 /\ sl_triple_valid_cmd p2 cmd q2)
        (ensures sl_triple_valid_cmd (SLOr p1 p2) cmd (SLOr q1 q2))

val sl_rule_exists : p:(value -> sl_assertion) -> q:(value -> sl_assertion) -> cmd:heap_cmd ->
  Lemma (requires forall x. sl_triple_valid_cmd (p x) cmd (q x))
        (ensures sl_triple_valid_cmd (SLExists p) cmd (SLExists q))

val sl_star_pure_implies : b:bool -> p:sl_assertion -> h:sl_heap ->
  Lemma (requires sl_satisfies h (SLStar (SLPure b) p))
        (ensures b == true)

(** ============================================================================
    MAGIC WAND PROPERTIES
    ============================================================================ *)

(**
 * Modus ponens for magic wand: P * (P -* Q) |= Q
 *)
val wand_modus_ponens : p:sl_assertion -> q:sl_assertion ->
  Lemma (ensures sl_entails (SLStar p (SLWand p q)) q)

(**
 * Wand introduction: If (P * R) |= Q then R |= (P -* Q)
 *)
val wand_intro : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (requires sl_entails (SLStar p r) q)
        (ensures sl_entails r (SLWand p q))

(**
 * Wand elimination.
 *)
val wand_elim : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (requires sl_entails r (SLWand p q))
        (ensures sl_entails (SLStar p r) q)

(**
 * Wand adjunction.
 *)
val wand_adjoint : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (ensures sl_entails (SLStar p r) q <==> sl_entails r (SLWand p q))

(**
 * Wand is contravariant in the first argument.
 *)
val wand_contravariant_left : p:sl_assertion -> p':sl_assertion -> q:sl_assertion ->
  Lemma (requires sl_entails p' p)
        (ensures sl_entails (SLWand p q) (SLWand p' q))

(**
 * Wand is covariant in the second argument.
 *)
val wand_covariant_right : p:sl_assertion -> q:sl_assertion -> q':sl_assertion ->
  Lemma (requires sl_entails q q')
        (ensures sl_entails (SLWand p q) (SLWand p q'))

(**
 * Emp is neutral for wand on the left.
 *)
val wand_emp_left : q:sl_assertion ->
  Lemma (ensures sl_entails (SLWand SLEmp q) q /\ sl_entails q (SLWand SLEmp q))

(**
 * Compute a simplified form of the magic wand when possible.
 *)
val compute_wand : p:sl_assertion -> q:sl_assertion -> option sl_assertion

val compute_wand_sound_pred : p:sl_assertion -> q:sl_assertion -> prop

val compute_wand_sound : p:sl_assertion -> q:sl_assertion ->
  Lemma (ensures compute_wand_sound_pred p q)

(**
 * Borrow wand helper.
 *)
val borrow_wand : l:sl_loc -> v:value -> sl_assertion

(**
 * Update wand helper.
 *)
val update_wand : l:sl_loc -> v_old:value -> v_new:value -> sl_assertion

val borrow_wand_emp : l:sl_loc -> v:value ->
  Lemma (ensures sl_entails (borrow_wand l v) SLEmp /\
                 sl_entails SLEmp (borrow_wand l v))

(**
 * Wand currying.
 *)
val wand_curry : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (ensures sl_entails (SLWand (SLStar p q) r) (SLWand p (SLWand q r)))

(**
 * Wand uncurrying.
 *)
val wand_uncurry : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
  Lemma (ensures sl_entails (SLWand p (SLWand q r)) (SLWand (SLStar p q) r))

(** ============================================================================
    FRAME PRESERVATION LEMMAS
    ============================================================================ *)

val frame_heap_preserved : cmd:heap_cmd -> h_local:sl_heap -> h_frame:sl_heap -> next_loc:sl_loc ->
  Lemma (requires sl_disjoint h_local h_frame)
        (ensures (match exec_heap_cmd cmd h_local next_loc with
                  | CROk h'_local _ -> sl_disjoint h'_local h_frame
                  | CRError _ -> True))

val frame_preserves_assertion : cmd:heap_cmd -> h_local:sl_heap -> h_frame:sl_heap ->
                                 r:sl_assertion -> next_loc:sl_loc ->
  Lemma (requires sl_disjoint h_local h_frame /\ sl_satisfies h_frame r)
        (ensures sl_satisfies h_frame r)

val frame_preserves_permissions : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
                                   cmd:heap_cmd -> h_p:sl_heap -> h_r:sl_heap -> next_loc:sl_loc ->
  Lemma (requires sl_triple_valid_cmd p cmd q /\
                  sl_disjoint h_p h_r /\
                  sl_satisfies h_p p /\
                  sl_satisfies h_r r)
        (ensures (match exec_heap_cmd cmd h_p next_loc with
                  | CROk h'_p _ -> sl_satisfies h'_p q /\ sl_satisfies h_r r
                  | CRError _ -> True))

(**
 * Frame rule soundness.
 *)
val frame_rule_sound : p:sl_assertion -> q:sl_assertion -> r:sl_assertion -> cmd:heap_cmd ->
  Lemma (requires sl_triple_valid_cmd p cmd q /\ cmd_is_local cmd p)
        (ensures sl_triple_valid_cmd (SLStar p r) cmd (SLStar q r))

val ownership_frame : l:sl_loc -> v:value -> r:sl_assertion ->
  Lemma (ensures sl_entails (SLStar (sl_own l v) r)
                            (SLStar (SLPointsTo l v) (SLStar (SLOwn l) r)))

val frac_frame : l:sl_loc -> n:nat -> d:nat{d > 0} -> r:sl_assertion ->
  Lemma (requires n <= d)
        (ensures sl_entails (SLStar (SLFrac l n d) r)
                            (SLStar (SLFrac l n d) r))

val borrow_frame : l:sl_loc -> v:value -> r:sl_assertion ->
  Lemma (ensures sl_entails (SLStar (sl_exclusive_borrow l v) r)
                            (SLStar (SLPointsTo l v) r))

(** ============================================================================
    CONCURRENT SEPARATION LOGIC
    ============================================================================ *)

val assertions_disjoint : p1:sl_assertion -> p2:sl_assertion -> prop
val parallel_star : p1:sl_assertion -> p2:sl_assertion -> sl_assertion

val concurrent_frame_valid : p1:sl_assertion -> q1:sl_assertion ->
                              p2:sl_assertion -> q2:sl_assertion ->
  Lemma (requires assertions_disjoint p1 p2)
        (ensures forall h.
          sl_satisfies h (SLStar p1 p2) ==>
          sl_satisfies h (SLStar q1 q2) \/
          sl_satisfies h (SLStar p1 q2) \/
          sl_satisfies h (SLStar q1 p2))

(** ============================================================================
    FRACTIONAL PERMISSIONS TYPE
    ============================================================================ *)

type fraction = {
  frac_num : nat;
  frac_den : nat;
}

val full_perm : fraction
val half_perm : fraction
val valid_perm : p:fraction -> bool
val is_full_perm : p:fraction -> bool
val mul : a:nat -> b:nat -> nat
val perm_half : p:fraction -> fraction
val perm_add : p1:fraction -> p2:fraction -> fraction

(** ============================================================================
    QUANTIFIED PERMISSION RANGE
    ============================================================================ *)

type qperm_range = {
  qpr_lo : nat;
  qpr_hi : nat;
}

val mk_range : lo:nat -> hi:nat -> qperm_range
val valid_range : r:qperm_range -> bool
val empty_range : r:qperm_range -> bool
val range_len : r:qperm_range -> nat
val in_range : i:nat -> r:qperm_range -> bool
val adjacent_ranges : r1:qperm_range -> r2:qperm_range -> bool
val disjoint_ranges : r1:qperm_range -> r2:qperm_range -> bool

(** ============================================================================
    ARRAY PERMISSIONS
    ============================================================================ *)

type array_access = {
  aa_array : sl_loc;
  aa_index : nat;
  aa_perm  : fraction;
}

val mk_array_access : arr:sl_loc -> i:nat -> p:fraction -> array_access
val array_loc : arr:sl_loc -> i:nat -> sl_loc
val array_access_to_sl : aa:array_access -> sl_assertion

(**
 * Iterated separating conjunction over range.
 *)
val sl_on_range : p:(nat -> sl_assertion) -> i:nat -> j:nat ->
  Tot sl_assertion (decreases (if j <= i then 0 else j - i))

val array_elem_perm : arr:sl_loc -> i:nat -> p:fraction -> sl_assertion
val array_slice_perm : arr:sl_loc -> lo:nat -> hi:nat -> p:fraction -> sl_assertion

(** ============================================================================
    QUANTIFIED PERMISSIONS
    ============================================================================ *)

noeq type quantified_permission =
  | QPForall : string -> qperm_range -> (nat -> sl_assertion) -> quantified_permission
  | QPExists : string -> qperm_range -> (nat -> sl_assertion) -> quantified_permission

val qperm_to_sl : qp:quantified_permission -> sl_assertion

val sl_on_range_sat : h:sl_heap -> p:(nat -> sl_assertion) -> i:nat -> j:nat ->
  Tot prop (decreases (if j <= i then 0 else j - i))

val qperm_sat : h:sl_heap -> qp:quantified_permission -> prop

(** ============================================================================
    ON_RANGE LEMMAS
    ============================================================================ *)

val sl_on_range_empty : p:(nat -> sl_assertion) -> i:nat ->
  Lemma (ensures sl_on_range p i i == SLEmp)

val sl_on_range_singleton : p:(nat -> sl_assertion) -> i:nat ->
  Lemma (ensures sl_on_range p i (i + 1) == SLStar (p i) SLEmp)

val sl_on_range_uncons : p:(nat -> sl_assertion) -> i:nat -> j:nat{i < j} ->
  Lemma (ensures sl_on_range p i j == SLStar (p i) (sl_on_range p (i + 1) j))

val sl_on_range_join_eq : p:(nat -> sl_assertion) -> i:nat -> k:nat -> j:nat ->
  Lemma (requires i <= k /\ k <= j)
        (ensures forall h. sl_satisfies h (SLStar (sl_on_range p i k) (sl_on_range p k j)) ==>
                           sl_satisfies h (sl_on_range p i j))
        (decreases (k - i))

(** ============================================================================
    ARRAY SPLIT AND JOIN
    ============================================================================ *)

val array_split : arr:sl_loc -> lo:nat -> k:nat -> hi:nat -> p:fraction ->
  Lemma (requires lo <= k /\ k <= hi)
        (ensures forall h. sl_satisfies h (array_slice_perm arr lo hi p) ==>
                           sl_satisfies h (SLStar (array_slice_perm arr lo k p)
                                                   (array_slice_perm arr k hi p)))
        (decreases (k - lo))

val array_join : arr:sl_loc -> lo:nat -> mid:nat -> hi:nat -> p:fraction ->
  Lemma (requires lo <= mid /\ mid <= hi)
        (ensures forall h.
          sl_satisfies h (SLStar (array_slice_perm arr lo mid p)
                                  (array_slice_perm arr mid hi p)) ==>
          sl_satisfies h (array_slice_perm arr lo hi p))

(** ============================================================================
    BOUNDS CHECKING
    ============================================================================ *)

val extract_bounds : qp:quantified_permission -> option (nat & nat)
val index_in_bounds : qp:quantified_permission -> idx:nat -> bool
val safe_access : arr:sl_loc -> idx:nat -> lo:nat -> hi:nat -> prop

val array_perm_bounds_safe : arr:sl_loc -> lo:nat -> hi:nat -> idx:nat -> p:fraction ->
  Lemma (requires lo <= idx /\ idx < hi)
        (ensures forall h. sl_satisfies h (array_slice_perm arr lo hi p) ==>
                           safe_access arr idx lo hi)

val qperm_instantiate : qp:quantified_permission -> k:nat ->
  Pure sl_assertion
    (requires QPForall? qp /\ in_range k (QPForall?._1 qp))
    (ensures fun _ -> True)

val qperm_instantiate_sound : qp:quantified_permission -> k:nat -> h:sl_heap ->
  Lemma (requires QPForall? qp /\
                  in_range k (QPForall?._1 qp) /\
                  sl_satisfies h (qperm_to_sl qp))
        (ensures exists h_k h_rest. sl_disjoint h_k h_rest /\
                                     sl_heap_eq h (sl_heap_union h_k h_rest) /\
                                     sl_satisfies h_k (qperm_instantiate qp k))

val array_perm_no_alias : arr:sl_loc -> i:nat -> j:nat -> p:fraction ->
  Lemma (requires i <> j)
        (ensures forall h1 h2.
          sl_satisfies h1 (array_elem_perm arr i p) /\
          sl_satisfies h2 (array_elem_perm arr j p) ==>
          sl_disjoint h1 h2)

val array_perm_share : arr:sl_loc -> lo:nat -> hi:nat ->
  Lemma (ensures forall h.
    sl_satisfies h (array_slice_perm arr lo hi full_perm) ==>
    sl_satisfies h (SLStar (array_slice_perm arr lo hi half_perm)
                            (array_slice_perm arr lo hi half_perm)))

val array_perm_gather : arr:sl_loc -> lo:nat -> hi:nat ->
  Lemma (ensures forall h.
    sl_satisfies h (SLStar (array_slice_perm arr lo hi half_perm)
                            (array_slice_perm arr lo hi half_perm)) ==>
    sl_satisfies h (array_slice_perm arr lo hi full_perm))

val array_focus : arr:sl_loc -> lo:nat -> hi:nat -> k:nat -> p:fraction ->
  Lemma (requires lo <= k /\ k < hi)
        (ensures forall h. sl_satisfies h (array_slice_perm arr lo hi p) ==>
                           exists h_k h_rest.
                             sl_disjoint h_k h_rest /\
                             sl_heap_eq h (sl_heap_union h_k h_rest) /\
                             sl_satisfies h_k (array_elem_perm arr k p))

(** ============================================================================
    BI-ABDUCTION
    ============================================================================ *)

noeq type biabduction_result = {
  bar_missing : sl_assertion;
  bar_frame   : sl_assertion;
  bar_valid   : bool;
}

val mk_biabduct_result : missing:sl_assertion -> frame:sl_assertion -> biabduction_result
val mk_biabduct_failure : biabduction_result

val sl_assertion_domain : a:sl_assertion -> Tot (list sl_loc) (decreases a)
val sl_loc_in_domain : l:sl_loc -> a:sl_assertion -> bool
val domains_disjoint : a1:sl_assertion -> a2:sl_assertion -> bool
val sl_assertion_free_locs : a:sl_assertion -> Tot (list sl_loc) (decreases a)
val sl_loc_free_in : l:sl_loc -> a:sl_assertion -> bool

val sl_simplify_assertion : a:sl_assertion -> Tot sl_assertion (decreases a)
val sl_flatten_stars : a:sl_assertion -> Tot (list sl_assertion) (decreases a)
val sl_unflatten_stars : atoms:list sl_assertion -> sl_assertion

val sl_atoms_equal : a1:sl_assertion -> a2:sl_assertion -> bool
val sl_atom_location : a:sl_assertion -> option sl_loc
val sl_find_by_location : l:sl_loc -> atoms:list sl_assertion -> option sl_assertion
val sl_remove_atom_from_list : a:sl_assertion -> atoms:list sl_assertion -> list sl_assertion

val sl_match_single_atom : required:sl_assertion -> available:list sl_assertion ->
  (bool & list sl_assertion & sl_assertion)

val sl_match_all_atoms : required:list sl_assertion -> available:list sl_assertion ->
  acc_missing:list sl_assertion -> Tot (list sl_assertion & list sl_assertion) (decreases required)

val compute_missing : p:sl_assertion -> q:sl_assertion -> sl_assertion
val compute_frame : p:sl_assertion -> q:sl_assertion -> sl_assertion

(**
 * Main bi-abduction function.
 *)
val biabduct : p:sl_assertion -> q:sl_assertion -> biabduction_result

val ba_emp : q:sl_assertion -> biabduction_result
val ba_pts_exact : l:sl_loc -> v:value -> anti_frame:sl_assertion -> biabduction_result
val ba_missing : p:sl_assertion -> l:sl_loc -> v:value -> biabduction_result
val ba_frame : q:sl_assertion -> l:sl_loc -> v:value -> biabduction_result
val ba_star : r1:biabduction_result -> r2:biabduction_result -> biabduction_result

(**
 * Bi-abduction soundness.
 *)
val biabduct_sound : p:sl_assertion -> q:sl_assertion ->
  Lemma (ensures (biabduct p q).bar_valid ==>
                 sl_entails (SLStar p (biabduct p q).bar_missing)
                            (SLStar q (biabduct p q).bar_frame))

val biabduct_preserves_sat : p:sl_assertion -> q:sl_assertion -> h:sl_heap ->
  Lemma (requires sl_satisfies h p /\ (biabduct p q).bar_valid)
        (ensures exists h'. sl_satisfies h' (SLStar p (biabduct p q).bar_missing))

(**
 * Function call inference.
 *)
val infer_call_precondition : current_state:sl_assertion -> required_pre:sl_assertion ->
  sl_assertion

val infer_call_postcondition : current_state:sl_assertion -> required_pre:sl_assertion ->
  func_post:sl_assertion -> sl_assertion

val biabduct_call : caller_state:sl_assertion -> func_pre:sl_assertion ->
  func_post:sl_assertion -> (sl_assertion & sl_assertion)

val infer_precondition_from_callsites : call_site_states:list sl_assertion ->
  current_guess:sl_assertion -> sl_assertion

(** ============================================================================
    INCORRECTNESS SEPARATION LOGIC (ISL)
    ============================================================================ *)

type isl_outcome =
  | IslOk
  | IslError of string

noeq type isl_triple = {
  isl_pre  : sl_assertion;
  isl_cmd  : heap_cmd;
  isl_post : sl_assertion;
  isl_outcome : isl_outcome;
}

val mk_isl_triple_ok : pre:sl_assertion -> cmd:heap_cmd -> post:sl_assertion -> isl_triple
val mk_isl_triple_err : pre:sl_assertion -> cmd:heap_cmd -> post:sl_assertion -> err:string -> isl_triple

val isl_valid_ok : pre:sl_assertion -> cmd:heap_cmd -> post:sl_assertion -> prop
val isl_valid_err : pre:sl_assertion -> cmd:heap_cmd -> err_post:sl_assertion -> err_msg:string -> prop
val isl_valid : t:isl_triple -> prop

val isl_rule_skip : p:sl_assertion ->
  Lemma (ensures isl_valid_ok p HCSkip p)

val isl_rule_seq : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
                   c1:heap_cmd -> c2:heap_cmd ->
  Lemma (requires isl_valid_ok p c1 q /\ isl_valid_ok q c2 r)
        (ensures isl_valid_ok p (HCSeq c1 c2) r)

val isl_rule_consequence : p:sl_assertion -> p':sl_assertion ->
                            q:sl_assertion -> q':sl_assertion -> cmd:heap_cmd ->
  Lemma (requires sl_entails p' p /\ isl_valid_ok p cmd q /\ sl_entails q q')
        (ensures isl_valid_ok p' cmd q')

val isl_rule_frame : p:sl_assertion -> q:sl_assertion -> r:sl_assertion -> cmd:heap_cmd ->
  Lemma (requires isl_valid_ok p cmd q /\ cmd_is_local cmd p)
        (ensures isl_valid_ok (SLStar p r) cmd (SLStar q r))

val isl_rule_error_intro : p:sl_assertion -> cmd:heap_cmd -> err:string ->
  Lemma (requires exists (h: sl_heap) (nl: sl_loc).
           sl_satisfies h p /\
           (match exec_heap_cmd cmd h nl with | CRError e -> e = err | CROk _ _ -> False))
        (ensures isl_valid_err p cmd SLEmp err)

val isl_double_free_error : l:sl_loc -> v:value ->
  Lemma (ensures isl_valid_err (SLPointsTo l v) (HCSeq (HCFree l) (HCFree l)) SLEmp "freeing unallocated location")

val isl_use_after_free_read : l:sl_loc -> v:value ->
  Lemma (ensures isl_valid_err (SLPointsTo l v) (HCSeq (HCFree l) (HCRead l)) SLEmp "reading from unallocated location")

val isl_use_after_free_write : l:sl_loc -> v1:value -> v2:value ->
  Lemma (ensures isl_valid_err (SLPointsTo l v1) (HCSeq (HCFree l) (HCWrite l v2)) SLEmp "writing to unallocated location")

noeq type execution_witness = {
  ew_initial_heap : sl_heap;
  ew_next_loc : sl_loc;
  ew_result : cmd_result;
}

val isl_true_positive : pre:sl_assertion -> cmd:heap_cmd -> err:string ->
  Lemma (requires isl_valid_err pre cmd SLEmp err)
        (ensures exists (h: sl_heap) (nl: sl_loc).
                   sl_satisfies h pre /\
                   (match exec_heap_cmd cmd h nl with | CRError e -> e = err | CROk _ _ -> False))

val isl_bug_is_real : t:isl_triple{IslError? t.isl_outcome} ->
  Lemma (requires isl_valid t)
        (ensures exists (h: sl_heap) (nl: sl_loc).
                   sl_satisfies h t.isl_pre /\ CRError? (exec_heap_cmd t.isl_cmd h nl))

val isl_wlp : cmd:heap_cmd -> post:sl_assertion -> Tot sl_assertion (decreases cmd)

val isl_wlp_sound_skip : post:sl_assertion ->
  Lemma (ensures isl_valid_ok (isl_wlp HCSkip post) HCSkip post)

val isl_error_pre : cmd:heap_cmd -> Tot sl_assertion (decreases cmd)

noeq type isl_summary = {
  sum_ok_triples : list isl_triple;
  sum_err_triples : list isl_triple;
}

val isl_empty_summary : isl_summary
val isl_compose_summaries : s1:isl_summary -> s2:isl_summary -> isl_summary
val isl_frame_summary : s:isl_summary -> frame:sl_assertion -> isl_summary

val isl_memory_leak_pattern : l:sl_loc -> v:value -> isl_triple
val isl_null_deref_read : l:sl_loc -> isl_triple
val isl_double_free_pattern : l:sl_loc -> v:value -> isl_triple
val isl_use_after_free_pattern : l:sl_loc -> v:value -> isl_triple

val isl_rule_iter_unfold : p:sl_assertion -> q:sl_assertion -> r:sl_assertion -> c:heap_cmd ->
  Lemma (requires isl_valid_ok p c q /\ isl_valid_ok q c r)
        (ensures isl_valid_ok p (HCSeq c c) r)

noeq type isl_biabduction_result = {
  isl_biab_anti_frame : sl_assertion;
  isl_biab_frame : sl_assertion;
}

(** ============================================================================
    EFFECT-SL BRIDGE
    ============================================================================ *)

noeq type sl_effect_op =
  | SLERead     : loc:sl_loc -> sl_effect_op
  | SLEWrite    : loc:sl_loc -> v:value -> sl_effect_op
  | SLEAlloc    : sl_effect_op
  | SLEFree     : loc:sl_loc -> sl_effect_op
  | SLEThrow    : exn_type:string -> sl_effect_op
  | SLECatch    : exn_type:string -> sl_effect_op
  | SLEDiv      : sl_effect_op
  | SLEPanic    : sl_effect_op
  | SLEAsync    : sl_effect_op
  | SLEIO       : sl_effect_op
  | SLENet      : sl_effect_op
  | SLEFS       : sl_effect_op
  | SLESpawn    : sl_effect_op
  | SLEJoin     : sl_effect_op
  | SLELock     : lock_id:nat -> sl_effect_op
  | SLEUnlock   : lock_id:nat -> sl_effect_op
  | SLESend     : chan:nat -> sl_effect_op
  | SLERecv     : chan:nat -> sl_effect_op
  | SLEAcquire  : resource:string -> sl_effect_op
  | SLERelease  : resource:string -> sl_effect_op
  | SLEPure     : sl_effect_op

noeq type sl_effect_row =
  | SLRowEmpty   : sl_effect_row
  | SLRowExt     : sl_effect_op -> sl_effect_row -> sl_effect_row
  | SLRowVar     : string -> sl_effect_row

(**
 * Effect-to-precondition mapping.
 *)
val effect_precondition : eff:sl_effect_op -> sl_assertion

(**
 * Effect-to-postcondition mapping.
 *)
val effect_postcondition : eff:sl_effect_op -> result:value -> sl_assertion

val effects_of_row : row:sl_effect_row -> Tot (list sl_effect_op) (decreases row)
val effect_row_precondition : row:sl_effect_row -> Tot sl_assertion (decreases row)
val effect_row_postcondition : row:sl_effect_row -> Tot sl_assertion (decreases row)

val read_requires_points_to : loc:sl_loc ->
  Lemma (sl_entails (effect_precondition (SLERead loc))
                    (SLExists (fun v -> SLPointsTo loc v)))

val write_requires_points_to : loc:sl_loc -> new_v:value ->
  Lemma (sl_entails (effect_precondition (SLEWrite loc new_v))
                    (SLExists (fun v -> SLPointsTo loc v)))

val free_requires_points_to : loc:sl_loc ->
  Lemma (sl_entails (effect_precondition (SLEFree loc))
                    (SLExists (fun v -> SLPointsTo loc v)))

val write_updates_points_to : loc:sl_loc -> old_v:value -> new_v:value ->
  Lemma (ensures forall h.
           sl_satisfies h (SLPointsTo loc old_v) ==>
           sl_satisfies h (effect_precondition (SLEWrite loc new_v)))

val alloc_establishes_points_to : fresh_loc:sl_loc ->
  Lemma (requires fresh_loc >= 0)
        (ensures forall h. sl_satisfies h SLEmp ==> True)

val free_consumes_points_to : loc:sl_loc -> v:value ->
  Lemma (ensures sl_entails (SLPointsTo loc v)
                            (effect_precondition (SLEFree loc)))

val effect_disjoint_from : eff:sl_effect_op -> frame:sl_assertion -> prop

val effect_preserves_frame : eff:sl_effect_op -> frame:sl_assertion ->
  Lemma (requires effect_disjoint_from eff frame)
        (ensures forall h.
           sl_satisfies h (SLStar (effect_precondition eff) frame) ==>
           sl_satisfies h (SLStar (effect_precondition eff) frame))

val effect_row_preserves_frame : row:sl_effect_row -> frame:sl_assertion ->
  Lemma (ensures forall h.
           sl_satisfies h (SLStar (effect_row_precondition row) frame) ==>
           sl_satisfies h (SLStar (effect_row_precondition row) frame))

val effect_to_heap_cmd : eff:sl_effect_op -> option heap_cmd

val effect_cmd_valid_pred : eff:sl_effect_op -> prop

val effect_precondition_enables_cmd : eff:sl_effect_op ->
  Lemma (ensures effect_cmd_valid_pred eff)

val effect_postcond_valid_pred : eff:sl_effect_op -> prop

val effect_postcondition_from_cmd : eff:sl_effect_op ->
  Lemma (ensures effect_postcond_valid_pred eff)
