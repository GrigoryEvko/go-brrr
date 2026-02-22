(**
 * BrrrLang.Core.SymbolicHeaps - Interface for Symbolic Heaps Shape Analysis
 *
 * Symbolic heaps are a restricted form of separation logic assertions designed
 * for efficient automated reasoning. They were introduced by Berdine, Calcagno,
 * and O'Hearn (2005) for compositional shape analysis.
 *
 * From brrr_lang_spec_v0.4.tex lines 7156-7199 (Symbolic Heap Grammar):
 *
 * A symbolic heap is a pair (Pi, Sigma) where:
 *   - Pi (pure part): conjunction of pure constraints (equalities, disequalities)
 *   - Sigma (spatial part): separating conjunction of heap predicates
 *
 * Grammar:
 *   Pi    ::= true | E1 = E2 | E1 != E2 | Pi /\ Pi
 *   Sigma ::= emp | E |-> E' | ls(E1, E2) | Sigma star Sigma
 *   Heap  ::= Pi | Sigma | exists x. Heap
 *
 * Key constructs from spec:
 *   - emp: empty heap
 *   - points-to (x |-> E): x points to value E
 *   - list segment (ls(E1, E2)): linked list from E1 to E2
 *   - junk predicate: resource leak detection
 *   - inductive definitions for data structures
 *
 * References:
 *   - brrr_lang_spec_v0.4.tex Section on Separation Logic
 *   - Pulse/fstar_pop_book.md: Recursive predicates (is_list pattern)
 *   - Berdine et al. "Symbolic Execution with Separation Logic" (CAV 2005)
 *   - Calcagno et al. "Compositional Shape Analysis" (POPL 2007)
 *
 * Depends on: BrrrTypes, Values
 *)
module BrrrSymbolicHeaps

open FStar.List.Tot
open BrrrTypes
open BrrrValues

(** ============================================================================
    HEAP MODEL FOR SYMBOLIC HEAPS
    ============================================================================

    We define a minimal heap model here to be self-contained and avoid
    dependency on potentially broken modules.
    ============================================================================ *)

(** Location is a natural number *)
type sh_loc = nat

(** Heap is a partial function from locations to values *)
type sh_heap = sh_loc -> option value

(** Empty heap - maps all locations to None *)
val sh_emp_heap : sh_heap

(** Singleton heap - maps only location l to value v *)
val sh_singleton : sh_loc -> value -> sh_heap

(** Domain membership - true if location is allocated in heap *)
val sh_in_dom : sh_loc -> sh_heap -> bool

(** Disjoint heaps - no location in both
    Two heaps are disjoint iff no location is allocated in both *)
val sh_disjoint : sh_heap -> sh_heap -> prop

(** Union of disjoint heaps
    Combines two heaps; first heap takes precedence *)
val sh_union : sh_heap -> sh_heap -> sh_heap

(** Heap equality - pointwise equality of mappings *)
val sh_heap_eq : sh_heap -> sh_heap -> prop

(** ============================================================================
    SYMBOLIC HEAP EXPRESSIONS
    ============================================================================

    Expressions in symbolic heaps are a restricted language for locations
    and values. These correspond to the "E" in the grammar.
    ============================================================================ *)

(** Expression in symbolic heap context - represents locations and values *)
noeq type sh_expr =
  | SHEVar    : string -> sh_expr                     (* Variable: x *)
  | SHELoc    : sh_loc -> sh_expr                     (* Concrete location *)
  | SHENull   : sh_expr                               (* Null pointer *)
  | SHEVal    : value -> sh_expr                      (* Concrete value *)
  | SHEDeref  : sh_expr -> sh_expr                    (* Dereference: star e *)
  | SHEField  : sh_expr -> string -> sh_expr          (* Field access: e.f *)
  | SHENext   : sh_expr -> sh_expr                    (* Next pointer: e.next *)

(** Expression equality (decidable for concrete values) *)
val sh_expr_eq : sh_expr -> sh_expr -> bool

(** ============================================================================
    PURE CONSTRAINTS (Pi)
    ============================================================================

    Pure constraints in symbolic heaps are equalities and disequalities
    between expressions. These correspond to the "Pi" part of the symbolic heap.
    ============================================================================ *)

(** Pure formula - constraints between symbolic expressions *)
noeq type sh_pure =
  | SHPTrue   : sh_pure                               (* true *)
  | SHPFalse  : sh_pure                               (* false *)
  | SHPEq     : sh_expr -> sh_expr -> sh_pure         (* E1 = E2 *)
  | SHPNeq    : sh_expr -> sh_expr -> sh_pure         (* E1 != E2 *)
  | SHPAnd    : sh_pure -> sh_pure -> sh_pure         (* Pi1 /\ Pi2 *)
  | SHPNot    : sh_pure -> sh_pure                    (* not Pi *)

(** Simplify pure formula - applies basic simplification rules *)
val sh_pure_simplify : sh_pure -> sh_pure

(** ============================================================================
    SYMBOLIC HEAP TYPE
    ============================================================================

    The core symbolic heap type, following the grammar from
    brrr_lang_spec_v0.4.tex lines 7156-7199.

    Constructor documentation:

      SHEmp: Empty spatial heap (Sigma = emp)
        Satisfied by the empty heap.

      SHPointsTo e v: Points-to predicate (e |-> v)
        Asserts that expression e evaluates to a location containing v.
        This is the fundamental heap predicate.

      SHListSeg e1 e2: List segment predicate (ls(e1, e2))
        Asserts a linked list from e1 to e2.
        Inductively defined:
          ls(E, E) = emp  (when E = E)
          ls(E1, E2) = exists v,n. E1 |-> (v,n) star ls(n, E2)  (when E1 != E2)

      SHTree e: Binary tree rooted at e (tree(e))
        Inductively defined:
          tree(null) = emp
          tree(x) = exists l,r,v. x |-> (v,l,r) star tree(l) star tree(r)

      SHStar s1 s2: Separating conjunction (Sigma1 star Sigma2)
        Combines two spatial predicates on disjoint heap regions.

      SHPure p: Pure constraint (Pi)
        Embeds a pure formula. Requires empty heap portion.
        Used for equalities and disequalities.

      SHJunk: Garbage predicate (junk)
        Represents memory that has been leaked - still allocated but
        no longer accessible. Used in resource leak detection.
        From spec: "junk predicate for resource leak detection"

      SHExists x t body: Existential quantification (exists x:t. Sigma)
        Introduces a fresh variable x of type t in body.
        Used for abstracting over unknown values.
    ============================================================================ *)

(** Symbolic heap - restricted separation logic for automated analysis *)
noeq type symbolic_heap =
  | SHEmp                                             (* Empty heap: emp *)
  | SHPointsTo   : sh_expr -> sh_expr -> symbolic_heap (* Points-to: E |-> V *)
  | SHListSeg    : sh_expr -> sh_expr -> symbolic_heap (* List segment: ls(E1, E2) *)
  | SHTree       : sh_expr -> symbolic_heap           (* Binary tree: tree(E) *)
  | SHStar       : symbolic_heap -> symbolic_heap -> symbolic_heap
                                                      (* Separating conj: Sigma1 star Sigma2 *)
  | SHPure       : sh_pure -> symbolic_heap           (* Pure constraint: Pi *)
  | SHJunk       : symbolic_heap                      (* Leaked memory: junk *)
  | SHExists     : string -> brrr_type -> symbolic_heap -> symbolic_heap
                                                      (* Existential: exists x:tau. Sigma *)

(** Symbolic heap size for termination proofs *)
val symbolic_heap_size : sh:symbolic_heap -> Tot nat (decreases sh)

(** ============================================================================
    SYMBOLIC HEAP COMBINATORS
    ============================================================================ *)

(** Flatten nested stars into a list of symbolic heaps *)
val sh_flatten_star : symbolic_heap -> list symbolic_heap

(** Rebuild symbolic heap from flat list using star *)
val sh_from_list : list symbolic_heap -> symbolic_heap

(** Normalize: flatten and remove emp *)
val sh_normalize : symbolic_heap -> symbolic_heap

(** Extract pure constraints from symbolic heap *)
val sh_extract_pure : symbolic_heap -> list sh_pure

(** Extract spatial predicates (non-pure) from symbolic heap *)
val sh_extract_spatial : symbolic_heap -> list symbolic_heap

(** ============================================================================
    VARIABLE ENVIRONMENT FOR SYMBOLIC HEAP INTERPRETATION
    ============================================================================ *)

(** Environment mapping symbolic variables to locations/values *)
type sh_env = list (string & sh_loc)

(** Lookup a variable in the environment *)
val sh_env_lookup : string -> sh_env -> option sh_loc

(** Extend environment with a new binding *)
val sh_env_extend : string -> sh_loc -> sh_env -> sh_env

(** ============================================================================
    SYMBOLIC EXPRESSION INTERPRETATION
    ============================================================================ *)

(** Interpret a symbolic expression to a location (when possible) *)
val sh_expr_to_loc : sh_expr -> sh_env -> sh_heap -> option sh_loc

(** Check if expression is null *)
val sh_expr_is_null : sh_expr -> sh_env -> bool

(** ============================================================================
    SATISFACTION RELATION FOR SYMBOLIC HEAPS
    ============================================================================

    The satisfaction relation defines when a concrete heap satisfies a
    symbolic heap. This is the semantic foundation for symbolic execution.

    Semantics:

      h |= emp           iff dom(h) = {}
      h |= E |-> V       iff h = {loc(E) |-> val(V)}
      h |= ls(E1, E2)    iff (E1 = E2 /\ dom(h) = {}) \/
                             (E1 != E2 /\ exists v,n.
                               h = {E1 |-> (v,n)} U h' /\ h' |= ls(n, E2))
      h |= tree(E)       iff (E = null /\ dom(h) = {}) \/
                             (exists l,r,v,hl,hr.
                               h = {E |-> (v,l,r)} U hl U hr /\
                               hl |= tree(l) /\ hr |= tree(r))
      h |= S1 star S2    iff exists h1,h2. h1 # h2 /\ h = h1 U h2 /\
                             h1 |= S1 /\ h2 |= S2
      h |= Pi            iff dom(h) = {} /\ [[Pi]] = true
      h |= junk          iff true (any heap satisfies junk)
      h |= exists x. S   iff exists v. h |= S[v/x]
    ============================================================================ *)

(** Pure constraint satisfaction *)
val sh_pure_sat : sh_pure -> sh_env -> prop

(** List segment satisfaction (co-inductive definition)

    From brrr_lang_spec_v0.4.tex:
      ls(E, E) = emp /\ E = E
      ls(E1, E2) = exists v,n. E1 |-> (v,n) star ls(n, E2) where E1 != E2

    We model this as:
    - If e1 and e2 evaluate to the same location, require empty heap
    - Otherwise, require e1 points to a cell, and the rest forms ls(next, e2)
*)
val list_seg_sat : sh_heap -> sh_env -> sh_expr -> sh_expr -> prop

(** Tree satisfaction (co-inductive definition)

    tree(null) = emp
    tree(x) = exists l,r,v. x |-> (v,l,r) star tree(l) star tree(r)
*)
val tree_sat : sh_heap -> sh_env -> sh_expr -> prop

(** Main satisfaction relation

    Defines when a concrete heap h satisfies a symbolic heap sh
    under environment env.
*)
val symbolic_heap_sat : h:sh_heap -> env:sh_env -> sh:symbolic_heap ->
  Tot prop (decreases %[symbolic_heap_size sh; 0])

(** ============================================================================
    LIST SEGMENT LEMMAS
    ============================================================================

    These lemmas establish the key properties of list segments from the spec.

    From brrr_lang_spec_v0.4.tex:
      ls_nil: ls(nil, nil) <==> emp
      ls_cons: ls(x::xs, nil) <==> x |-> _ star ls(xs, nil)
      ls_append: ls(x, y) star ls(y, z) ==> ls(x, z)
    ============================================================================ *)

(** ls_nil: Empty list segment at same location equals emp *)
val sh_ls_nil : e:sh_expr ->
  Lemma (ensures forall h env.
    symbolic_heap_sat h env (SHListSeg e e) <==>
    symbolic_heap_sat h env SHEmp)

(** ls_cons: Non-empty list segment unfolds to points-to plus tail *)
val sh_ls_cons : e1:sh_expr -> e2:sh_expr ->
  Lemma (requires not (sh_expr_eq e1 e2))
        (ensures forall h env.
          symbolic_heap_sat h env (SHListSeg e1 e2) ==>
          (exists (v: sh_expr) (next: sh_expr).
            symbolic_heap_sat h env (SHStar (SHPointsTo e1 v) (SHListSeg next e2))))

(** ls_append: List segment concatenation *)
val sh_ls_append : e1:sh_expr -> e2:sh_expr -> e3:sh_expr ->
  Lemma (ensures forall h env.
    symbolic_heap_sat h env (SHStar (SHListSeg e1 e2) (SHListSeg e2 e3)) ==>
    symbolic_heap_sat h env (SHListSeg e1 e3))

(** ============================================================================
    TREE LEMMAS
    ============================================================================ *)

(** tree_nil: Empty tree at null equals emp *)
val sh_tree_nil : unit ->
  Lemma (ensures forall h env.
    symbolic_heap_sat h env (SHTree SHENull) <==>
    symbolic_heap_sat h env SHEmp)

(** ============================================================================
    JUNK PREDICATE FOR RESOURCE LEAK DETECTION
    ============================================================================

    The junk predicate represents memory that has been leaked - memory that
    is still allocated but no longer accessible through any program variable.

    Properties:
    1. junk is satisfied by any heap (including empty)
    2. junk star P ==> junk  (junk absorbs resources)
    3. Memory that transitions to junk represents a resource leak

    In shape analysis, junk detection is crucial for:
    - Finding memory leaks (allocated but unreachable memory)
    - Identifying dangling pointer sources
    - Analyzing resource consumption
    ============================================================================ *)

(** Junk is satisfied by any heap *)
val sh_junk_any : h:sh_heap -> env:sh_env ->
  Lemma (ensures symbolic_heap_sat h env SHJunk)

(** Junk absorbs resources: junk star P implies junk *)
val sh_junk_absorbs : p:symbolic_heap -> h:sh_heap -> env:sh_env ->
  Lemma (ensures symbolic_heap_sat h env (SHStar SHJunk p) ==>
                 symbolic_heap_sat h env SHJunk)

(** Detecting potential leaks: if P contains junk, some memory may be leaked *)
val sh_potential_leak : symbolic_heap -> bool

(** ============================================================================
    SYMBOLIC HEAP ENTAILMENT
    ============================================================================

    Entailment between symbolic heaps: sh1 |= sh2 means any heap satisfying
    sh1 also satisfies sh2.
    ============================================================================ *)

(** Semantic entailment - sh1 entails sh2 *)
val sh_entails : symbolic_heap -> symbolic_heap -> prop

(** Reflexivity: every symbolic heap entails itself *)
val sh_entails_refl : sh:symbolic_heap ->
  Lemma (ensures sh_entails sh sh)

(** Transitivity: entailment composes *)
val sh_entails_trans : sh1:symbolic_heap -> sh2:symbolic_heap -> sh3:symbolic_heap ->
  Lemma (requires sh_entails sh1 sh2 /\ sh_entails sh2 sh3)
        (ensures sh_entails sh1 sh3)

(** emp is left identity for star (both directions) *)
val sh_emp_star_left : sh:symbolic_heap ->
  Lemma (ensures sh_entails (SHStar SHEmp sh) sh /\ sh_entails sh (SHStar SHEmp sh))

(** Star is commutative *)
val sh_star_comm : sh1:symbolic_heap -> sh2:symbolic_heap ->
  Lemma (ensures sh_entails (SHStar sh1 sh2) (SHStar sh2 sh1))

(** ============================================================================
    SYMBOLIC HEAP FRAME INFERENCE
    ============================================================================

    Frame inference finds the "leftover" resources after matching a precondition.
    Given a current heap description H and a required precondition P, find F such
    that H = P star F.

    This is the "abduction" part of bi-abduction.
    ============================================================================ *)

(** Simple frame inference (subtracts exact matches)

    Given what we have and what we need, returns the frame (leftover resources).
    Returns None if no simple frame can be inferred.
*)
val sh_infer_frame : have:symbolic_heap -> need:symbolic_heap -> option symbolic_heap

(** ============================================================================
    SYMBOLIC HEAP ANTI-FRAME INFERENCE
    ============================================================================

    Anti-frame inference finds what's "missing" to satisfy a precondition.
    Given a current heap description H and a required precondition P, find M such
    that H star M |= P.

    This is the "anti-abduction" part of bi-abduction.
    ============================================================================ *)

(** Simple anti-frame inference

    Given what we have and what we need, returns the anti-frame (missing resources).
    Returns None if no simple anti-frame can be inferred.
*)
val sh_infer_anti_frame : have:symbolic_heap -> need:symbolic_heap -> option symbolic_heap

(** ============================================================================
    DOUBLY-LINKED LIST SEGMENT PREDICATE
    ============================================================================

    Doubly-linked lists require tracking both forward and backward pointers.

    dls(head, prev, tail, next) represents a doubly-linked list segment where:
    - head: first node
    - prev: predecessor of head (null for start)
    - tail: last node
    - next: successor of tail (null for end)

    Inductive definition:
      dls(x, p, x, n) = x |-> (v, p, n)  (singleton)
      dls(x, p, z, n) = exists y,v. x |-> (v, p, y) star dls(y, x, z, n) where x != z
    ============================================================================ *)

(** Doubly-linked list segment - expressed as symbolic heap with extra structure *)
val sh_dls : head:sh_expr -> prev:sh_expr -> tail:sh_expr -> next:sh_expr -> symbolic_heap

(** ============================================================================
    SUMMARY: SYMBOLIC HEAPS MODULE
    ============================================================================

    This module provides symbolic heaps for shape analysis and bi-abduction:

    1. SYMBOLIC HEAP TYPE (symbolic_heap):
       - SHEmp: empty heap
       - SHPointsTo: points-to predicate (E |-> V)
       - SHListSeg: list segment (ls(E1, E2))
       - SHTree: binary tree (tree(E))
       - SHStar: separating conjunction
       - SHPure: pure constraints (Pi)
       - SHJunk: leaked memory for resource leak detection
       - SHExists: existential quantification

    2. SATISFACTION RELATION (symbolic_heap_sat):
       - Defines when a concrete heap satisfies a symbolic heap
       - Handles all symbolic heap constructors
       - Supports variable environments

    3. LIST SEGMENT LEMMAS:
       - sh_ls_nil: ls(e, e) <==> emp
       - sh_ls_cons: ls(e1, e2) ==> e1 |-> _ star ls(next, e2) when e1 != e2
       - sh_ls_append: ls(e1, e2) star ls(e2, e3) ==> ls(e1, e3)

    4. JUNK PREDICATE:
       - sh_junk_any: junk is satisfied by any heap
       - sh_junk_absorbs: junk star P ==> junk
       - sh_potential_leak: detect potential memory leaks

    5. ENTAILMENT:
       - sh_entails: semantic entailment
       - Reflexivity and transitivity lemmas
       - Star commutativity and emp identity

    6. FRAME INFERENCE (foundation for bi-abduction):
       - sh_infer_frame: find leftover resources
       - sh_infer_anti_frame: find missing resources

    This module provides the foundation for:
    - Compositional shape analysis (Calcagno et al. 2011)
    - Bi-abduction for automatic frame inference
    - Resource leak detection
    - Memory safety verification
    ============================================================================ *)
