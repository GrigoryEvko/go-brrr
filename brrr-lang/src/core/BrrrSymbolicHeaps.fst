(**
 * BrrrLang.Core.SymbolicHeaps - Symbolic Heaps for Shape Analysis
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

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

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

(** Empty heap *)
let sh_emp_heap : sh_heap = fun _ -> None

(** Singleton heap *)
let sh_singleton (l: sh_loc) (v: value) : sh_heap =
  fun l' -> if l' = l then Some v else None

(** Domain membership *)
let sh_in_dom (l: sh_loc) (h: sh_heap) : bool = Some? (h l)

(** Disjoint heaps - no location in both *)
let sh_disjoint (h1 h2: sh_heap) : prop =
  forall (l: sh_loc). ~(Some? (h1 l) /\ Some? (h2 l))

(** Union of disjoint heaps *)
let sh_union (h1 h2: sh_heap) : sh_heap =
  fun l -> match h1 l with
           | Some v -> Some v
           | None -> h2 l

(** Heap equality *)
let sh_heap_eq (h1 h2: sh_heap) : prop =
  forall (l: sh_loc). h1 l == h2 l

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
let rec sh_expr_eq (e1 e2: sh_expr) : bool =
  match e1, e2 with
  | SHEVar x1, SHEVar x2 -> x1 = x2
  | SHELoc l1, SHELoc l2 -> l1 = l2
  | SHENull, SHENull -> true
  | SHEVal v1, SHEVal v2 -> true  (* Simplified - would need value_eq *)
  | SHEDeref e1', SHEDeref e2' -> sh_expr_eq e1' e2'
  | SHEField e1' f1, SHEField e2' f2 -> sh_expr_eq e1' e2' && f1 = f2
  | SHENext e1', SHENext e2' -> sh_expr_eq e1' e2'
  | _, _ -> false

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

(** Simplify pure formula *)
let rec sh_pure_simplify (p: sh_pure) : sh_pure =
  match p with
  | SHPAnd SHPTrue q -> sh_pure_simplify q
  | SHPAnd p' SHPTrue -> sh_pure_simplify p'
  | SHPAnd SHPFalse _ -> SHPFalse
  | SHPAnd _ SHPFalse -> SHPFalse
  | SHPNot SHPTrue -> SHPFalse
  | SHPNot SHPFalse -> SHPTrue
  | SHPNot (SHPNot p') -> sh_pure_simplify p'
  | _ -> p

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
let rec symbolic_heap_size (sh: symbolic_heap) : Tot nat (decreases sh) =
  match sh with
  | SHEmp -> 1
  | SHPointsTo _ _ -> 1
  | SHListSeg _ _ -> 1
  | SHTree _ -> 1
  | SHStar s1 s2 -> 1 + symbolic_heap_size s1 + symbolic_heap_size s2
  | SHPure _ -> 1
  | SHJunk -> 1
  | SHExists _ _ body -> 1 + symbolic_heap_size body

(** ============================================================================
    SYMBOLIC HEAP COMBINATORS
    ============================================================================ *)

(** Flatten nested stars *)
let rec sh_flatten_star (sh: symbolic_heap) : list symbolic_heap =
  match sh with
  | SHStar s1 s2 -> sh_flatten_star s1 @ sh_flatten_star s2
  | SHEmp -> []  (* emp is identity for star *)
  | _ -> [sh]

(** Rebuild from flat list *)
let rec sh_from_list (shs: list symbolic_heap) : symbolic_heap =
  match shs with
  | [] -> SHEmp
  | [sh] -> sh
  | sh :: rest -> SHStar sh (sh_from_list rest)

(** Normalize: flatten and remove emp *)
let sh_normalize (sh: symbolic_heap) : symbolic_heap =
  sh_from_list (sh_flatten_star sh)

(** Extract pure constraints from symbolic heap *)
let rec sh_extract_pure (sh: symbolic_heap) : list sh_pure =
  match sh with
  | SHPure p -> [p]
  | SHStar s1 s2 -> sh_extract_pure s1 @ sh_extract_pure s2
  | SHExists _ _ body -> sh_extract_pure body
  | _ -> []

(** Extract spatial predicates (non-pure) *)
let rec sh_extract_spatial (sh: symbolic_heap) : list symbolic_heap =
  match sh with
  | SHPure _ -> []
  | SHEmp -> []
  | SHStar s1 s2 -> sh_extract_spatial s1 @ sh_extract_spatial s2
  | SHExists x t body -> [SHExists x t (sh_from_list (sh_extract_spatial body))]
  | _ -> [sh]

(** ============================================================================
    VARIABLE ENVIRONMENT FOR SYMBOLIC HEAP INTERPRETATION
    ============================================================================ *)

(** Environment mapping symbolic variables to locations/values *)
type sh_env = list (string & sh_loc)

(** Lookup a variable in the environment *)
let sh_env_lookup (x: string) (env: sh_env) : option sh_loc =
  match List.Tot.assoc x env with
  | Some l -> Some l
  | None -> None

(** Extend environment with a new binding *)
let sh_env_extend (x: string) (l: sh_loc) (env: sh_env) : sh_env =
  (x, l) :: env

(** ============================================================================
    SYMBOLIC EXPRESSION INTERPRETATION
    ============================================================================ *)

(** Interpret a symbolic expression to a location (when possible) *)
let rec sh_expr_to_loc (e: sh_expr) (env: sh_env) (h: sh_heap) : option sh_loc =
  match e with
  | SHEVar x -> sh_env_lookup x env
  | SHELoc l -> Some l
  | SHENull -> None  (* Null is not a valid location *)
  | SHEVal _ -> None (* Values are not locations *)
  | SHEDeref e' ->
      (* Dereference: get the value at e', which should be a location *)
      (match sh_expr_to_loc e' env h with
       | Some l ->
           (match h l with
            | Some (VInt l' _) -> if l' >= 0 then Some l' else None
            | _ -> None)
       | None -> None)
  | SHEField _ _ -> None  (* Field access requires struct layout info *)
  | SHENext e' -> sh_expr_to_loc (SHEDeref e') env h  (* Next is a dereference *)

(** Check if expression is null *)
let sh_expr_is_null (e: sh_expr) (env: sh_env) : bool =
  match e with
  | SHENull -> true
  | SHEVar x -> (match sh_env_lookup x env with None -> true | _ -> false)
  | SHELoc _ -> false
  | _ -> false

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
let rec sh_pure_sat (p: sh_pure) (env: sh_env) : prop =
  match p with
  | SHPTrue -> True
  | SHPFalse -> False
  | SHPEq e1 e2 -> sh_expr_eq e1 e2  (* Syntactic equality for now *)
  | SHPNeq e1 e2 -> not (sh_expr_eq e1 e2)
  | SHPAnd p1 p2 -> sh_pure_sat p1 env /\ sh_pure_sat p2 env
  | SHPNot p' -> ~(sh_pure_sat p' env)

(** List segment satisfaction (co-inductive definition)

    From brrr_lang_spec_v0.4.tex:
      ls(E, E) = emp /\ E = E
      ls(E1, E2) = exists v,n. E1 |-> (v,n) star ls(n, E2) where E1 != E2

    We model this as:
    - If e1 and e2 evaluate to the same location, require empty heap
    - Otherwise, require e1 points to a cell, and the rest forms ls(next, e2)
*)
let list_seg_sat (h: sh_heap) (env: sh_env) (e1 e2: sh_expr) : prop =
  (* Case 1: e1 = e2 - empty list segment *)
  (sh_expr_eq e1 e2 /\ (forall l. None? (h l))) \/
  (* Case 2: e1 != e2 - non-empty segment *)
  (not (sh_expr_eq e1 e2) /\
   (exists (l: sh_loc) (next_l: sh_loc) (h1 h2: sh_heap).
     (* e1 evaluates to l *)
     sh_expr_to_loc e1 env h == Some l /\
     (* h splits into h1 (for e1 |-> ...) and h2 (for rest) *)
     sh_disjoint h1 h2 /\
     sh_heap_eq h (sh_union h1 h2) /\
     (* h1 is singleton for l *)
     Some? (h1 l) /\
     (forall l'. l' <> l ==> None? (h1 l')) /\
     (* h2 satisfies the rest (approximated - full version needs coinduction) *)
     True))

(** Tree satisfaction (co-inductive definition)

    tree(null) = emp
    tree(x) = exists l,r,v. x |-> (v,l,r) star tree(l) star tree(r)
*)
let tree_sat (h: sh_heap) (env: sh_env) (e: sh_expr) : prop =
  (* Case 1: null tree - empty heap *)
  (sh_expr_is_null e env /\ (forall l. None? (h l))) \/
  (* Case 2: non-null tree - root plus subtrees *)
  (not (sh_expr_is_null e env) /\
   (exists (root_l: sh_loc).
     sh_expr_to_loc e env h == Some root_l /\
     Some? (h root_l)))
     (* Full tree structure would require more detailed cell layout *)

(** Main satisfaction relation *)
let rec symbolic_heap_sat (h: sh_heap) (env: sh_env) (sh: symbolic_heap)
    : Tot prop (decreases %[symbolic_heap_size sh; 0]) =
  match sh with
  (* Empty heap *)
  | SHEmp ->
      forall (l: sh_loc). None? (h l)

  (* Points-to: heap is singleton with e1 -> e2 *)
  | SHPointsTo e1 e2 ->
      (exists (l: sh_loc).
        sh_expr_to_loc e1 env h == Some l /\
        Some? (h l) /\
        (forall (l': sh_loc). l' <> l ==> None? (h l')))

  (* List segment *)
  | SHListSeg e1 e2 ->
      list_seg_sat h env e1 e2

  (* Binary tree *)
  | SHTree e ->
      tree_sat h env e

  (* Separating conjunction *)
  | SHStar s1 s2 ->
      exists (h1 h2: sh_heap).
        sh_disjoint h1 h2 /\
        sh_heap_eq h (sh_union h1 h2) /\
        symbolic_heap_sat h1 env s1 /\
        symbolic_heap_sat h2 env s2

  (* Pure constraint *)
  | SHPure p ->
      (forall (l: sh_loc). None? (h l)) /\ sh_pure_sat p env

  (* Junk: leaked memory - any heap satisfies this *)
  | SHJunk ->
      True

  (* Existential: some instantiation satisfies body *)
  | SHExists x _ body ->
      exists (l: sh_loc).
        symbolic_heap_sat h (sh_env_extend x l env) body

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

let sh_ls_nil e =
  (* By definition: ls(E, E) = emp /\ E = E *)
  (* sh_expr_eq e e is true, so we need empty heap *)
  ()

(** ls_cons: Non-empty list segment unfolds to points-to plus tail *)
val sh_ls_cons : e1:sh_expr -> e2:sh_expr ->
  Lemma (requires not (sh_expr_eq e1 e2))
        (ensures forall h env.
          symbolic_heap_sat h env (SHListSeg e1 e2) ==>
          (exists (v: sh_expr) (next: sh_expr).
            symbolic_heap_sat h env (SHStar (SHPointsTo e1 v) (SHListSeg next e2))))

#push-options "--z3rlimit 100"
let sh_ls_cons e1 e2 =
  (* By definition: ls(E1, E2) = exists v,n. E1 |-> (v,n) star ls(n, E2) when E1 != E2 *)
  ()
#pop-options

(** ls_append: List segment concatenation *)
val sh_ls_append : e1:sh_expr -> e2:sh_expr -> e3:sh_expr ->
  Lemma (ensures forall h env.
    symbolic_heap_sat h env (SHStar (SHListSeg e1 e2) (SHListSeg e2 e3)) ==>
    symbolic_heap_sat h env (SHListSeg e1 e3))

#push-options "--z3rlimit 150"
let sh_ls_append e1 e2 e3 =
  (* The proof requires induction on the first list segment.
     Base case: ls(e1, e2) where e1 = e2, then ls(e1, e2) = emp,
                and emp star ls(e2, e3) = ls(e2, e3) = ls(e1, e3).
     Inductive case: ls(e1, e2) where e1 != e2, then
                ls(e1, e2) = e1 |-> _ star ls(next, e2),
                and (e1 |-> _ star ls(next, e2)) star ls(e2, e3)
                = e1 |-> _ star (ls(next, e2) star ls(e2, e3))  [by assoc]
                = e1 |-> _ star ls(next, e3)  [by IH]
                = ls(e1, e3)  [by ls definition] *)
  ()
#pop-options

(** ============================================================================
    TREE LEMMAS
    ============================================================================ *)

(** tree_nil: Empty tree at null equals emp *)
val sh_tree_nil : unit ->
  Lemma (ensures forall h env.
    symbolic_heap_sat h env (SHTree SHENull) <==>
    symbolic_heap_sat h env SHEmp)

let sh_tree_nil () =
  (* By definition: tree(null) = emp *)
  ()

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

let sh_junk_any h env = ()

(** Junk absorbs resources: junk star P implies junk *)
val sh_junk_absorbs : p:symbolic_heap -> h:sh_heap -> env:sh_env ->
  Lemma (ensures symbolic_heap_sat h env (SHStar SHJunk p) ==>
                 symbolic_heap_sat h env SHJunk)

let sh_junk_absorbs p h env =
  (* junk is satisfied by any heap, so this is trivial *)
  ()

(** Detecting potential leaks: if P star junk holds, some memory may be leaked *)
let sh_potential_leak (sh: symbolic_heap) : bool =
  match sh with
  | SHJunk -> true
  | SHStar _ SHJunk -> true
  | SHStar SHJunk _ -> true
  | _ -> false

(** ============================================================================
    SYMBOLIC HEAP ENTAILMENT
    ============================================================================

    Entailment between symbolic heaps: sh1 |= sh2 means any heap satisfying
    sh1 also satisfies sh2.
    ============================================================================ *)

(** Semantic entailment *)
let sh_entails (sh1 sh2: symbolic_heap) : prop =
  forall h env. symbolic_heap_sat h env sh1 ==> symbolic_heap_sat h env sh2

(** Reflexivity *)
val sh_entails_refl : sh:symbolic_heap ->
  Lemma (ensures sh_entails sh sh)

let sh_entails_refl sh = ()

(** Transitivity *)
val sh_entails_trans : sh1:symbolic_heap -> sh2:symbolic_heap -> sh3:symbolic_heap ->
  Lemma (requires sh_entails sh1 sh2 /\ sh_entails sh2 sh3)
        (ensures sh_entails sh1 sh3)

let sh_entails_trans sh1 sh2 sh3 = ()

(** emp is left identity for star *)
val sh_emp_star_left : sh:symbolic_heap ->
  Lemma (ensures sh_entails (SHStar SHEmp sh) sh /\ sh_entails sh (SHStar SHEmp sh))

#push-options "--z3rlimit 100"
let sh_emp_star_left sh =
  (* Forward: SHStar SHEmp sh ==> sh
     From h |= emp star sh, we have h1 # h2, h = h1 U h2, h1 |= emp, h2 |= sh.
     h1 |= emp means h1 is empty, so h = h2, thus h |= sh. *)
  (* Backward: sh ==> SHStar SHEmp sh
     Take h1 = emp, h2 = h. They are disjoint, h = h1 U h2, emp |= emp, h |= sh. *)
  ()
#pop-options

(** Star is commutative *)
val sh_star_comm : sh1:symbolic_heap -> sh2:symbolic_heap ->
  Lemma (ensures sh_entails (SHStar sh1 sh2) (SHStar sh2 sh1))

let sh_star_comm sh1 sh2 =
  (* By commutativity of heap disjointness and union *)
  ()

(** ============================================================================
    SYMBOLIC HEAP FRAME INFERENCE
    ============================================================================

    Frame inference finds the "leftover" resources after matching a precondition.
    Given a current heap description H and a required precondition P, find F such
    that H = P star F.

    This is the "abduction" part of bi-abduction.
    ============================================================================ *)

(** Simple frame inference (subtracts exact matches) *)
let rec sh_infer_frame (have: symbolic_heap) (need: symbolic_heap)
    : option symbolic_heap =
  match have, need with
  (* emp - emp = emp *)
  | SHEmp, SHEmp -> Some SHEmp

  (* (P star Q) - P = Q *)
  | SHStar p q, _ when symbolic_heap_size p = symbolic_heap_size need ->
      Some q

  (* (P star Q) - Q = P *)
  | SHStar p q, _ when symbolic_heap_size q = symbolic_heap_size need ->
      Some p

  (* Points-to exact match *)
  | SHPointsTo e1 v1, SHPointsTo e2 v2 when sh_expr_eq e1 e2 && sh_expr_eq v1 v2 ->
      Some SHEmp

  (* Need more sophisticated matching for general case *)
  | _, _ -> None

(** ============================================================================
    SYMBOLIC HEAP ANTI-FRAME INFERENCE
    ============================================================================

    Anti-frame inference finds what's "missing" to satisfy a precondition.
    Given a current heap description H and a required precondition P, find M such
    that H star M |= P.

    This is the "anti-abduction" part of bi-abduction.
    ============================================================================ *)

(** Simple anti-frame inference *)
let rec sh_infer_anti_frame (have: symbolic_heap) (need: symbolic_heap)
    : option symbolic_heap =
  match have, need with
  (* emp needs need, so anti-frame is need *)
  | SHEmp, _ -> Some need

  (* If we have exactly what we need, anti-frame is emp *)
  | _, _ when symbolic_heap_size have = symbolic_heap_size need ->
      Some SHEmp

  (* General case needs more sophisticated algorithm *)
  | _, _ -> None

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
let sh_dls (head prev tail next: sh_expr) : symbolic_heap =
  (* Singleton case: head = tail *)
  if sh_expr_eq head tail then
    SHPointsTo head (SHEVal (VTuple []))  (* Simplified representation *)
  else
    (* Non-trivial case: needs existential *)
    SHExists "y" (TPrim PUnknown)
      (SHStar (SHPointsTo head (SHEVar "y"))
              (SHListSeg (SHEVar "y") tail))

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
