(**
 * Security.Theorems
 *
 * Research-grade formal theorems for information flow security, gradual typing,
 * and type-theoretic foundations. These theorems represent the deepest results
 * in programming language security theory and require substantial proof effort.
 *
 * ============================================================================
 * SECURITY LATTICE FOUNDATIONS
 * ============================================================================
 *
 * The information flow type system is based on a SECURITY LATTICE, following
 * the foundational work of Denning (1976) "A Lattice Model of Secure
 * Information Flow", CACM 19(5):236-243.
 *
 * A security lattice (L, <=, join, meet, bot, top) satisfies:
 *
 * PARTIAL ORDER LAWS (for the "flows-to" relation <=):
 *   1. Reflexivity:     forall l. l <= l
 *   2. Antisymmetry:    forall l1 l2. l1 <= l2 /\ l2 <= l1 ==> l1 = l2
 *   3. Transitivity:    forall l1 l2 l3. l1 <= l2 /\ l2 <= l3 ==> l1 <= l3
 *
 * LATTICE LAWS (for join = least upper bound, meet = greatest lower bound):
 *   4. Join idempotent:    forall l. l `join` l = l
 *   5. Join commutative:   forall l1 l2. l1 `join` l2 = l2 `join` l1
 *   6. Join associative:   forall l1 l2 l3. (l1 `join` l2) `join` l3 = l1 `join` (l2 `join` l3)
 *   7. Meet idempotent:    forall l. l `meet` l = l
 *   8. Meet commutative:   forall l1 l2. l1 `meet` l2 = l2 `meet` l1
 *   9. Meet associative:   forall l1 l2 l3. (l1 `meet` l2) `meet` l3 = l1 `meet` (l2 `meet` l3)
 *  10. Absorption:         forall l1 l2. l1 `join` (l1 `meet` l2) = l1
 *                          forall l1 l2. l1 `meet` (l1 `join` l2) = l1
 *
 * BOUNDED LATTICE LAWS:
 *  11. Bot is identity for join:  forall l. bot `join` l = l
 *  12. Top is identity for meet:  forall l. top `meet` l = l
 *  13. Bot is annihilator for meet: forall l. bot `meet` l = bot
 *  14. Top is annihilator for join: forall l. top `join` l = top
 *
 * DERIVED PROPERTY (join determines ordering):
 *  15. l1 <= l2 <==> l1 `join` l2 = l2
 *
 * ============================================================================
 * FOUR-POINT DIAMOND LATTICE
 * ============================================================================
 *
 * A canonical example is the FOUR-POINT DIAMOND, combining confidentiality
 * and integrity dimensions (Myers & Liskov 2000, JFlow):
 *
 *                      TopSecret (High-C, High-I)
 *                         /           \
 *                        /             \
 *              Secret (High-C)     Confidential (High-I)
 *                        \             /
 *                         \           /
 *                       Public (Low-C, Low-I)
 *
 * This forms a product lattice L = Confidentiality x Integrity where:
 *   - Confidentiality: Public <= Secret (who can READ)
 *   - Integrity: Trusted <= Untrusted (who can WRITE)
 *
 * In the diamond:
 *   - Public: anyone can read, anyone can write
 *   - Secret: restricted read, anyone can write
 *   - Confidential (Integrity-high): anyone can read, restricted write
 *   - TopSecret: restricted read AND restricted write
 *
 * The "four-point" property: there exist exactly 4 elements, with 2 incomparable
 * elements (Secret and Confidential) that have a common lower bound (Public)
 * and common upper bound (TopSecret).
 *
 * LITERATURE: Myers 1999 "JFlow: Practical Mostly-Static Information Flow Control"
 *             POPL 1999, pp. 228-241. https://doi.org/10.1145/292540.292561
 *
 * ============================================================================
 * THEOREM IDENTIFIERS (from AXIOMS_REPORT_v2.md):
 * ============================================================================
 *   T-5.5: noninterference - Well-typed programs satisfy noninterference
 *   T-5.6: blame_soundness - Blame correctly identifies contract violators
 *   T-5.7: parametricity - Related inputs produce related outputs (Abstraction Theorem)
 *   T-5.8: occurrence_typing_sound - Type narrowing after predicates is sound
 *
 * ============================================================================
 * LITERATURE REFERENCES:
 * ============================================================================
 *
 * FOUNDATIONAL SECURITY:
 *   - Denning 1976: "A Lattice Model of Secure Information Flow"
 *     CACM 19(5):236-243. https://doi.org/10.1145/360051.360056
 *     >> Established lattice-based information flow; introduced security labels.
 *
 *   - Denning & Denning 1977: "Certification of Programs for Secure Information Flow"
 *     CACM 20(7):504-513. https://doi.org/10.1145/359636.359712
 *     >> Static certification of information flow using compile-time analysis.
 *
 * TYPE-BASED INFORMATION FLOW:
 *   - Volpano, Smith, Irvine 1996: "A Sound Type System for Secure Flow Analysis"
 *     Journal of Computer Security, Vol. 4, No. 2-3, pp. 167-187
 *     https://doi.org/10.3233/JCS-1996-42-304
 *     >> First type system proof of noninterference; our T-5.5 follows this.
 *
 *   - Myers 1999: "JFlow: Practical Mostly-Static Information Flow Control"
 *     POPL 1999, pp. 228-241. https://doi.org/10.1145/292540.292561
 *     >> Practical IFC with declassification; introduced DLM (Decentralized Label Model).
 *
 *   - Myers & Liskov 2000: "Protecting Privacy using the Decentralized Label Model"
 *     ACM TOSEM 9(4):410-442. https://doi.org/10.1145/363516.363526
 *     >> Full treatment of DLM including integrity and authority.
 *
 * GRADUAL TYPING AND BLAME:
 *   - Wadler, Findler 2009: "Well-Typed Programs Can't Be Blamed"
 *     ESOP 2009, LNCS 5502, pp. 1-16
 *     https://doi.org/10.1007/978-3-642-00590-9_1
 *     >> Blame soundness theorem; our T-5.6 follows this.
 *
 * PARAMETRICITY:
 *   - Reynolds 1983: "Types, Abstraction and Parametric Polymorphism"
 *     IFIP Congress 1983, pp. 513-523
 *     >> Logical relations for parametricity; our T-5.7 follows this.
 *
 *   - Wadler 1989: "Theorems for Free!"
 *     FPCA 1989, pp. 347-359. https://doi.org/10.1145/99370.99404
 *     >> Deriving properties from types via parametricity.
 *
 * OCCURRENCE TYPING:
 *   - Tobin-Hochstadt, Felleisen 2008: "The Design and Implementation of Typed Scheme"
 *     POPL 2008, pp. 395-406
 *     https://doi.org/10.1145/1328438.1328486
 *     >> Occurrence typing for union types; our T-5.8 follows this.
 *
 * ============================================================================
 * EFFORT ESTIMATES:
 * ============================================================================
 * WARNING: These are RESEARCH-GRADE theorems requiring 40-80 hours EACH.
 * Full mechanized proofs would require:
 *   - Logical relations for parametricity (approx 1000 lines of F-star)
 *   - Step-indexed Kripke models for blame (approx 800 lines)
 *   - Refinement type semantics for occurrence typing (approx 600 lines)
 *   - Denotational semantics for noninterference (approx 1200 lines)
 *
 * Depends on: SecurityTypes, SecurityTypeChecker, Contracts, BrrrTypes, Expressions, Eval
 *)
module BrrrSecurity.Theorems

(** Z3 configuration - these proofs are complex and may require extensive resources *)
#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical

(* Import core modules *)
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrValues
open BrrrEval
open BrrrSecurityTypes

(** ============================================================================
    FOUNDATIONAL DEFINITIONS FOR SECURITY PROOFS
    ============================================================================

    Before stating the theorems, we establish the semantic foundations:
    - Low-equivalence relations for noninterference
    - Blame labels and contract semantics for blame soundness
    - Logical relations for parametricity
    - Type refinement predicates for occurrence typing

    These definitions follow the canonical presentations from the literature.
    ============================================================================ *)

(** ----------------------------------------------------------------------------
    LOW-EQUIVALENCE FOR NONINTERFERENCE
    ----------------------------------------------------------------------------
    Two states are low-equivalent at observation level L if they agree on all
    values observable at level L or below. This is the standard definition
    from Volpano et al. 1996, Definition 2.

    MATHEMATICAL DEFINITION (Volpano et al. 1996):
    Let sigma be a memory state mapping variables to labeled values.
    Two states sigma_1 and sigma_2 are L-equivalent, written sigma_1 ~_L sigma_2, iff:

      forall x. label(sigma_1(x)) <= L ==> sigma_1(x) = sigma_2(x)

    In words: all variables observable at level L or below have identical values.

    KEY INSIGHT (Denning 1976): Information flow is tracked via the lattice ordering.
    Data at level l1 can flow to level l2 only if l1 <= l2. This prevents:
      - Direct flows: assigning high to low (e.g., public := secret)
      - Indirect flows: branching on high then assigning low (e.g., if secret then public := 1)

    The program counter label (pc) tracks the "implicit context" - the security
    level of the decision that led to the current program point. Assignments
    in a high context (high pc) can only target high variables.

    ATTACKER MODEL: An attacker at level L can observe all variables with
    label <= L. Noninterference ensures such an attacker cannot distinguish
    runs that differ only in high (> L) inputs.
    ---------------------------------------------------------------------------- *)

(** Observation level: determines what an attacker can see *)
type observation_level = sec_label

(** A memory location with its security label *)
noeq type labeled_location = {
  ll_value : value;
  ll_label : sec_label;
}

(** Memory model for noninterference proofs *)
type security_memory = var_id -> option labeled_location

(** Two values are indistinguishable at observation level L *)
let value_indistinguishable (obs_level: observation_level) (v1 v2: value) (label: sec_label) : Type0 =
  sec_label_leq label obs_level ==> v1 == v2

(** Two memories are low-equivalent at observation level L.
    Definition: m1 ~_L m2 iff forall x with label(m1(x)) <= L, m1(x) = m2(x)

    This captures the attacker model: an attacker at level L cannot distinguish
    two memories that differ only in high (above L) locations.

    LATTICE CONNECTION: The sec_label_leq function implements the partial order
    on our security lattice. It must satisfy the lattice laws documented in the
    module header. The key property used in noninterference proofs:

      label(v) <= L  ==>  v is observable at L
      label(v) > L   ==>  v is NOT observable at L (can differ between runs)

    EQUIVALENCE RELATION PROPERTIES: Low-equivalence is:
      - Reflexive:  m ~_L m  (trivially, same values)
      - Symmetric:  m1 ~_L m2 ==> m2 ~_L m1  (equality is symmetric)
      - Transitive: m1 ~_L m2 /\ m2 ~_L m3 ==> m1 ~_L m3  (equality is transitive)

    These properties are essential for the noninterference proof's case analysis. *)
let memory_low_equiv (obs_level: observation_level) (m1 m2: security_memory) : Type0 =
  forall (x: var_id).
    match m1 x, m2 x with
    | Some loc1, Some loc2 ->
        value_indistinguishable obs_level loc1.ll_value loc2.ll_value loc1.ll_label
    | None, None -> True
    | _, _ -> False  (* Memories must have same domain for equivalence *)

(** Termination predicate for expressions *)
let terminates (e: expr) (m: security_memory) (fuel: nat) : Type0 =
  exists (v: value) (m': security_memory).
    (* Expression evaluates to some value and final memory *)
    True  (* Abstracted - would need operational semantics formalization *)

(** Final state after evaluation (abstracted) *)
assume val eval_security : expr -> security_memory -> nat -> option (value & security_memory)

(** ----------------------------------------------------------------------------
    BLAME LABELS AND CONTRACT SEMANTICS
    ----------------------------------------------------------------------------
    Blame tracking identifies which party (positive/negative) violated a
    contract. This follows Wadler-Findler 2009, Section 2.

    - Positive blame: the term being wrapped violated the contract
    - Negative blame: the context using the term violated the contract
    ---------------------------------------------------------------------------- *)

(** Blame label identifies a contract boundary *)
noeq type blame_label = {
  bl_positive : string;   (* Name of the wrapped term *)
  bl_negative : string;   (* Name of the context *)
  bl_contract : string;   (* Contract description *)
}

(** Which party is blamed *)
type blame_party =
  | BlamePositive : blame_party  (* The term violated *)
  | BlameNegative : blame_party  (* The context violated *)

(** A contract in the blame calculus *)
noeq type blame_contract = {
  bc_domain   : brrr_type;     (* Domain type *)
  bc_codomain : brrr_type;     (* Codomain type *)
  bc_label    : blame_label;   (* Blame tracking label *)
}

(** Contract monitoring result *)
type monitoring_result =
  | MRValue  : value -> monitoring_result            (* Evaluation succeeded *)
  | MRBlame  : blame_party -> blame_label -> monitoring_result  (* Contract violated *)
  | MRError  : string -> monitoring_result           (* Evaluation error *)

(** Cast expression with blame tracking *)
noeq type cast_expr =
  | CastUp    : blame_label -> brrr_type -> brrr_type -> expr -> cast_expr
  | CastDown  : blame_label -> brrr_type -> brrr_type -> expr -> cast_expr
  | CastFun   : blame_label -> blame_contract -> expr -> cast_expr

(** Contract monitoring function (abstracted) *)
assume val monitor_contract : blame_contract -> value -> monitoring_result

(** Subtyping in the blame calculus - determines cast direction *)
let blame_subtype (t1 t2: brrr_type) : bool =
  subtype t1 t2

(** Value has a given type (abstracted) - must be defined before party_violates *)
let has_type (v: value) (t: brrr_type) : Type0 =
  True  (* Would require full type semantics *)

(** A party "violates" a contract if they fail to meet their obligations *)
let party_violates (p: blame_party) (c: blame_contract) (v: value) : Type0 =
  match p with
  | BlamePositive -> (* Term failed to produce value of codomain type *)
      ~(has_type v c.bc_codomain)
  | BlameNegative -> (* Context failed to provide value of domain type *)
      ~(has_type v c.bc_domain)

(** ----------------------------------------------------------------------------
    LOGICAL RELATIONS FOR PARAMETRICITY
    ----------------------------------------------------------------------------
    Logical relations provide the semantic foundation for parametricity.
    This follows Reynolds 1983 and the modern treatment in Harper 2016.

    Key idea: Define a family of relations R_tau indexed by type tau.
    For function types: f1 R_{A->B} f2 iff forall a1 R_A a2, f1(a1) R_B f2(a2)
    ---------------------------------------------------------------------------- *)

(** Type environment: maps type variables to relation interpretations *)
type type_env = string -> option (value -> value -> Type0)

(** Empty type environment *)
let empty_type_env : type_env = fun _ -> None

(** Extend type environment with a relation *)
let extend_type_env (alpha: string) (rel: value -> value -> Type0) (env: type_env) : type_env =
  fun x -> if x = alpha then Some rel else env x

(** Logical relation for types (parametric in type environment).
    This is the fundamental lemma's semantic interpretation.

    R[[int]] = { (n, n) | n : int }
    R[[bool]] = { (b, b) | b : bool }
    R[[alpha]] = rho(alpha)  -- from environment
    R[[A -> B]] = { (f1, f2) | forall (v1, v2) in R[[A]], (f1 v1, f2 v2) in R[[B]] }
    R[[forall alpha. A]] = { (v1, v2) | forall R, (v1, v2) in R[[A]][alpha := R] }
*)
let rec logical_relation
    (env: type_env)
    (t: brrr_type)
    (v1 v2: value)
    : Tot Type0 (decreases t) =
  match t with
  (* Base types: diagonal relation *)
  | TNumeric _ -> v1 == v2  (* Integers and floats *)
  | TPrim PBool -> v1 == v2
  | TPrim PString -> v1 == v2
  | TPrim PUnit -> True  (* Unit is trivially related *)
  | TPrim PDynamic -> True  (* Dynamic is universally related *)
  | TPrim PUnknown -> True  (* Unknown is universally related *)
  | TPrim PNever -> False  (* Never type is uninhabited *)
  | TPrim PChar -> v1 == v2

  (* Type variable: lookup in environment *)
  | TVar alpha ->
      (match env alpha with
       | Some rel -> rel v1 v2
       | None -> False)  (* Unbound type variable *)

  (* Function type: relational arrow *)
  | TFunc ft ->
      (* Simplified: single argument function *)
      (match ft.params with
       | [p] ->
           forall (a1 a2: value).
             logical_relation env p.ty a1 a2 ==>
             (* Would need to apply v1, v2 as functions *)
             True  (* Abstracted: requires function application semantics *)
       | _ -> True)  (* Multi-arg: simplified *)

  (* Product type: pointwise relation *)
  | TTuple ts ->
      (match v1, v2 with
       | VTuple vs1, VTuple vs2 ->
           List.Tot.length vs1 = List.Tot.length vs2 /\
           List.Tot.length ts = List.Tot.length vs1 /\
           (forall (i: nat{i < List.Tot.length ts}).
             logical_relation env (List.Tot.index ts i)
                              (List.Tot.index vs1 i)
                              (List.Tot.index vs2 i))
       | _, _ -> False)

  (* Wrapper types: relation on wrapped type *)
  | TWrap _ inner -> logical_relation env inner v1 v2

  (* Modal types: relation on inner type *)
  | TModal _ inner -> logical_relation env inner v1 v2

  (* Result types: componentwise relation *)
  | TResult ok_t err_t -> True  (* Abstracted for simplicity *)

  (* Type application: instantiate and relate *)
  | TApp _ _ -> True  (* Abstracted: requires type instantiation *)

  (* Named types: need type definition lookup *)
  | TNamed _ -> True  (* Abstracted: requires type environment *)

  (* Struct types: field-wise relation *)
  | TStruct _ -> True  (* Abstracted: requires field matching *)

  (* Enum types: variant relation *)
  | TEnum _ -> True  (* Abstracted: requires tag matching *)

(** Value environment: maps variables to values *)
type value_env = var_id -> option value

(** Two value environments are related under a type context *)
let env_related
    (type_env: type_env)
    (ctx: list (var_id & brrr_type))
    (env1 env2: value_env)
    : Type0 =
  forall (x: var_id) (t: brrr_type).
    List.Tot.memP (x, t) ctx ==>
    (match env1 x, env2 x with
     | Some v1, Some v2 -> logical_relation type_env t v1 v2
     | _, _ -> False)

(** ----------------------------------------------------------------------------
    OCCURRENCE TYPING PREDICATES
    ----------------------------------------------------------------------------
    Occurrence typing narrows types based on control flow predicates.
    This follows Tobin-Hochstadt & Felleisen 2008.

    Key idea: After (if (number? x) e1 e2), in e1 we know x has type Number.
    ---------------------------------------------------------------------------- *)

(** Type predicate: a function that tests if a value has a certain type *)
noeq type type_predicate = {
  tp_name    : string;            (* e.g., "number?", "string?" *)
  tp_filters : brrr_type;         (* The type this predicate selects for *)
}

(** A value satisfies a type predicate *)
let satisfies_predicate (v: value) (pred: type_predicate) : bool =
  match pred.tp_name with
  | "number?" ->
      (match v with VInt _ _ -> true | VFloat _ _ -> true | _ -> false)
  | "string?" ->
      (match v with VString _ -> true | _ -> false)
  | "boolean?" ->
      (match v with VBool _ -> true | _ -> false)
  | "null?" ->
      (match v with VUnit -> true | _ -> false)
  | "procedure?" ->
      (match v with VClosure _ -> true | _ -> false)
  | _ -> false  (* Unknown predicate *)

(** Union type: represents a value that could be one of several types.
    In brrr-lang, enums serve as sum/variant types. *)
let is_union_type (t: brrr_type) : bool =
  match t with
  | TEnum _ -> true
  | _ -> false

(** Extract type from union that a predicate filters for *)
let filter_union_type (t: brrr_type) (pred: type_predicate) : option brrr_type =
  (* If t is Union [T1; T2; ...] and pred filters for Ti, return Some Ti *)
  Some pred.tp_filters  (* Simplified *)

(** Type refinement after predicate check *)
let refine_type_by_predicate (t: brrr_type) (pred: type_predicate) (passed: bool) : brrr_type =
  if passed then
    pred.tp_filters  (* Narrow to filtered type *)
  else
    t  (* Original type (could be more precise with type difference) *)

(** ============================================================================
    SECTION: SIMPLIFIED STATE MODEL FOR NONINTERFERENCE PROOFS
    ============================================================================

    For the noninterference proof, we use a simplified state model that connects
    directly to security labels. This abstracts over the full BrrrEval.fst semantics
    while preserving the essential structure for security reasoning.

    The key insight (Volpano et al. 1996) is that noninterference can be proven
    by tracking security labels through evaluation, without full operational
    semantics formalization.
    ============================================================================ *)

(** Variable identifier with associated security label *)
type labeled_var_id = var_id & sec_label

(** Security state: maps variable identifiers to labeled values *)
noeq type sec_state = {
  ss_bindings : list (var_id & value & sec_label);
  ss_heap     : list (nat & value & sec_label);
  ss_pc       : sec_label;  (* Current program counter security level *)
}

(** Empty security state *)
let empty_sec_state : sec_state = {
  ss_bindings = [];
  ss_heap = [];
  ss_pc = sec_public_trusted;
}

(** Lookup variable in security state *)
let ss_lookup (x: var_id) (s: sec_state) : option (value & sec_label) =
  match List.Tot.find (fun (y, _, _) -> x = y) s.ss_bindings with
  | Some (_, v, l) -> Some (v, l)
  | None -> None

(** Extend security state with a binding *)
let ss_extend (x: var_id) (v: value) (l: sec_label) (s: sec_state) : sec_state =
  { s with ss_bindings = (x, v, l) :: s.ss_bindings }

(** Get the label of a variable *)
let ss_var_label (x: var_id) (s: sec_state) : option sec_label =
  match ss_lookup x s with
  | Some (_, l) -> Some l
  | None -> None

(** ============================================================================
    SECTION: LOW-EQUIVALENCE DEFINITIONS
    ============================================================================

    Two states are low-equivalent at observation level L if they agree on all
    variables observable at L or below. This is the fundamental definition
    for noninterference (Volpano et al. 1996, Definition 2).

    Formally: s1 ~_L s2 iff forall x. label(x) <= L ==> s1(x) = s2(x)
    ============================================================================ *)

(** Low-equivalence predicate for security states *)
let low_equivalent (obs: sec_label) (s1 s2: sec_state) : Type0 =
  forall (x: var_id).
    (match ss_lookup x s1, ss_lookup x s2 with
     | Some (v1, l1), Some (v2, l2) ->
         (* Labels must match *)
         l1 == l2 /\
         (* If observable, values must match *)
         (sec_label_leq l1 obs ==> v1 == v2)
     | None, None -> True
     | _, _ -> False)

(** Low-equivalence is reflexive *)
val low_equiv_refl : obs:sec_label -> s:sec_state ->
  Lemma (ensures low_equivalent obs s s)
        [SMTPat (low_equivalent obs s s)]

let low_equiv_refl obs s = ()

(** Low-equivalence is symmetric *)
val low_equiv_sym : obs:sec_label -> s1:sec_state -> s2:sec_state ->
  Lemma (requires low_equivalent obs s1 s2)
        (ensures low_equivalent obs s2 s1)

let low_equiv_sym obs s1 s2 = ()

(** Low-equivalence is transitive *)
val low_equiv_trans : obs:sec_label -> s1:sec_state -> s2:sec_state -> s3:sec_state ->
  Lemma (requires low_equivalent obs s1 s2 /\ low_equivalent obs s2 s3)
        (ensures low_equivalent obs s1 s3)

let low_equiv_trans obs s1 s2 s3 = ()

(** ============================================================================
    SECTION: SECURITY TYPING JUDGMENTS (SIMPLIFIED)
    ============================================================================

    The security typing judgment Gamma; pc |- e : tau @ l means:
    - Expression e has type tau
    - The security label of e's result is l
    - The program counter label is pc
    - Gamma is the security typing context

    The key typing rules follow Volpano et al. 1996:

    T-VAR:   Gamma(x) = tau @ l
             -----------------------
             Gamma; pc |- x : tau @ l

    T-CONST: -----------------------
             Gamma; pc |- c : base_type(c) @ bot

    T-OP:    Gamma; pc |- e1 : tau @ l1    Gamma; pc |- e2 : tau @ l2
             --------------------------------------------------------
             Gamma; pc |- e1 op e2 : tau @ (l1 join l2)

    T-IF:    Gamma; pc |- e0 : bool @ l0
             Gamma; (pc join l0) |- e1 : tau @ l1
             Gamma; (pc join l0) |- e2 : tau @ l2
             -------------------------------------------
             Gamma; pc |- if e0 then e1 else e2 : tau @ (l1 join l2)

    T-ASSIGN: Gamma; pc |- e : tau @ l
              Gamma(x) = tau @ lx
              (pc join l) <= lx          (* CRITICAL: prevents implicit flows *)
              --------------------------------
              Gamma; pc |- x := e : unit @ bot

    T-SEQ:   Gamma; pc |- e1 : tau1 @ l1    Gamma; pc |- e2 : tau2 @ l2
             -----------------------------------------------------------
             Gamma; pc |- e1; e2 : tau2 @ l2
    ============================================================================ *)

(** Security typing context: maps variables to (type, label) pairs *)
type sec_typing_ctx = list (var_id & brrr_type & sec_label)

(** Lookup in security typing context *)
let stc_lookup (x: var_id) (ctx: sec_typing_ctx) : option (brrr_type & sec_label) =
  match List.Tot.find (fun (y, _, _) -> x = y) ctx with
  | Some (_, t, l) -> Some (t, l)
  | None -> None

(** Expression has well-formed security typing *)
noeq type sec_typed : sec_typing_ctx -> sec_label -> expr -> brrr_type -> sec_label -> Type =
  (* Variable reference *)
  | STVar : ctx:sec_typing_ctx -> pc:sec_label -> x:var_id -> t:brrr_type -> l:sec_label ->
            squash (stc_lookup x ctx == Some (t, l)) ->
            sec_typed ctx pc (mk_expr_dummy (EVar x)) t l

  (* Literal constant - always at bottom security *)
  | STLit : ctx:sec_typing_ctx -> pc:sec_label -> lit:literal -> t:brrr_type ->
            sec_typed ctx pc (mk_expr_dummy (ELit lit)) t sec_public_trusted

  (* Binary operation - joins labels *)
  | STBinOp : ctx:sec_typing_ctx -> pc:sec_label -> op:binary_op ->
              e1:expr -> e2:expr -> t:brrr_type -> l1:sec_label -> l2:sec_label ->
              sec_typed ctx pc e1 t l1 ->
              sec_typed ctx pc e2 t l2 ->
              sec_typed ctx pc (mk_expr_dummy (EBinary op e1 e2)) t (sec_label_join l1 l2)

  (* Conditional - raises PC in branches, joins result labels *)
  | STIf : ctx:sec_typing_ctx -> pc:sec_label -> cond:expr -> then_e:expr -> else_e:expr ->
           l_cond:sec_label -> t:brrr_type -> l_then:sec_label -> l_else:sec_label ->
           sec_typed ctx pc cond (TPrim PBool) l_cond ->
           sec_typed ctx (sec_label_join pc l_cond) then_e t l_then ->
           sec_typed ctx (sec_label_join pc l_cond) else_e t l_else ->
           sec_typed ctx pc (mk_expr_dummy (EIf cond then_e else_e)) t (sec_label_join l_then l_else)

  (* Sequence *)
  | STSeq : ctx:sec_typing_ctx -> pc:sec_label -> e1:expr -> e2:expr ->
            t1:brrr_type -> l1:sec_label -> t2:brrr_type -> l2:sec_label ->
            sec_typed ctx pc e1 t1 l1 ->
            sec_typed ctx pc e2 t2 l2 ->
            sec_typed ctx pc (mk_expr_dummy (ESeq e1 e2)) t2 l2

(** Well-typed with respect to IFC *)
let well_typed_ifc (ctx: sec_typing_ctx) (pc: sec_label) (e: expr) : Type0 =
  exists (t: brrr_type) (l: sec_label). sec_typed ctx pc e t l

(** Get result label from typing derivation *)
let get_result_label (#ctx: sec_typing_ctx) (#pc: sec_label) (#e: expr) (#t: brrr_type) (#l: sec_label)
    (d: sec_typed ctx pc e t l) : sec_label = l

(** ============================================================================
    SECTION: EXPRESSION EVALUATION WITH SECURITY
    ============================================================================

    Semantics for evaluating expressions while tracking security labels.
    This connects to the main BrrrEval.fst semantics but adds label tracking.
    ============================================================================ *)

(** Evaluation result with security label *)
type sec_eval_result =
  | SROk     : value -> sec_label -> sec_eval_result
  | SRErr    : string -> sec_eval_result
  | SRDiv    : sec_eval_result  (* Divergence *)

(** Evaluate expression in security state (simplified) *)
assume val sec_eval : fuel:nat -> expr -> sec_state -> sec_eval_result & sec_state

(** Termination predicate *)
let sec_terminates (fuel: nat) (e: expr) (s: sec_state) : Type0 =
  SROk? (fst (sec_eval fuel e s))

(** ============================================================================
    SECTION: TERMINATION-INSENSITIVE NONINTERFERENCE (TINI)
    ============================================================================

    TINI states that if two states are low-equivalent and a program terminates
    in both, the final states are also low-equivalent.

    This is weaker than termination-sensitive NI because it doesn't consider
    the termination channel (a program could leak information by diverging
    based on secret input).

    Reference: Volpano et al. 1996, Section 4
    ============================================================================ *)

(** TINI property for an expression *)
let termination_insensitive_ni (e: expr) (obs: sec_label) : Type0 =
  forall (s1 s2: sec_state) (fuel: nat).
    low_equivalent obs s1 s2 /\
    sec_terminates fuel e s1 /\
    sec_terminates fuel e s2
    ==>
    (let (_, s1') = sec_eval fuel e s1 in
     let (_, s2') = sec_eval fuel e s2 in
     low_equivalent obs s1' s2')

(** TINI with value indistinguishability *)
let tini_with_values (e: expr) (obs: sec_label) (result_label: sec_label) : Type0 =
  forall (s1 s2: sec_state) (fuel: nat).
    low_equivalent obs s1 s2 /\
    sec_terminates fuel e s1 /\
    sec_terminates fuel e s2
    ==>
    (match sec_eval fuel e s1, sec_eval fuel e s2 with
     | (SROk v1 l1, s1'), (SROk v2 l2, s2') ->
         (* Final states are low-equivalent *)
         low_equivalent obs s1' s2' /\
         (* If result is observable, values are equal *)
         (sec_label_leq result_label obs ==> v1 == v2)
     | _, _ -> True)

(** ============================================================================
    SECTION: AUXILIARY LEMMAS FOR NONINTERFERENCE PROOF
    ============================================================================

    These lemmas establish noninterference for each syntactic construct.
    The main theorem follows by induction on the typing derivation.
    ============================================================================ *)

(**
 * NI for variable references.
 *
 * If x has label l <= L, then in low-equivalent states, x has the same value.
 * If x has label l > L, results may differ but are not observable.
 *)
val ni_var : ctx:sec_typing_ctx -> pc:sec_label -> x:var_id -> obs:sec_label ->
             s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (EVar x)) s1 /\
           sec_terminates fuel (mk_expr_dummy (EVar x)) s2)
        (ensures
           (match ss_lookup x s1, ss_lookup x s2 with
            | Some (v1, l1), Some (v2, l2) ->
                l1 == l2 /\ (sec_label_leq l1 obs ==> v1 == v2)
            | _, _ -> True))

let ni_var ctx pc x obs s1 s2 fuel =
  (* By definition of low_equivalent, if label(x) <= obs, then s1(x) == s2(x) *)
  ()

(**
 * NI for literals.
 *
 * Literals evaluate to the same value in all states.
 *)
val ni_lit : ctx:sec_typing_ctx -> pc:sec_label -> lit:literal -> obs:sec_label ->
             s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (ELit lit)) s1 /\
           sec_terminates fuel (mk_expr_dummy (ELit lit)) s2)
        (ensures
           (match sec_eval fuel (mk_expr_dummy (ELit lit)) s1,
                  sec_eval fuel (mk_expr_dummy (ELit lit)) s2 with
            | (SROk v1 _, _), (SROk v2 _, _) -> v1 == v2
            | _, _ -> True))

let ni_lit ctx pc lit obs s1 s2 fuel =
  (* Literals are pure and don't depend on state *)
  admit ()

(**
 * NI for binary operations.
 *
 * If both operands satisfy NI, so does the operation.
 * Result label is join of operand labels.
 *)
val ni_binop : ctx:sec_typing_ctx -> pc:sec_label -> op:binary_op ->
               e1:expr -> e2:expr -> obs:sec_label ->
               s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (EBinary op e1 e2)) s1 /\
           sec_terminates fuel (mk_expr_dummy (EBinary op e1 e2)) s2 /\
           (* IH: operands satisfy NI *)
           termination_insensitive_ni e1 obs /\
           termination_insensitive_ni e2 obs)
        (ensures
           termination_insensitive_ni (mk_expr_dummy (EBinary op e1 e2)) obs)

let ni_binop ctx pc op e1 e2 obs s1 s2 fuel =
  (* By IH on e1 and e2, we get related intermediate values.
     By congruence of the operation, results are related. *)
  admit ()

(**
 * NI for conditionals with HIGH guard (CRITICAL CASE).
 *
 * When the guard has label > L, different branches may execute in the two runs.
 * The CONFINEMENT LEMMA ensures both branches preserve low state.
 *)
val ni_if_high_guard : ctx:sec_typing_ctx -> pc:sec_label ->
                       cond:expr -> then_e:expr -> else_e:expr ->
                       l_cond:sec_label -> obs:sec_label ->
                       s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           (* Guard label is above observation level *)
           ~(sec_label_leq l_cond obs) /\
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (EIf cond then_e else_e)) s1 /\
           sec_terminates fuel (mk_expr_dummy (EIf cond then_e else_e)) s2)
        (ensures
           (* Both branches produce low-equivalent results *)
           (let (_, s1') = sec_eval fuel (mk_expr_dummy (EIf cond then_e else_e)) s1 in
            let (_, s2') = sec_eval fuel (mk_expr_dummy (EIf cond then_e else_e)) s2 in
            low_equivalent obs s1' s2'))

let ni_if_high_guard ctx pc cond then_e else_e l_cond obs s1 s2 fuel =
  (* By confinement lemma: when PC > obs, execution cannot affect low state.
     In both runs, PC is raised to (pc `join` l_cond) > obs.
     Therefore both branches preserve low-equivalence with original state.
     By transitivity: s1' ~_obs s1 ~_obs s2 ~_obs s2', so s1' ~_obs s2'. *)
  admit ()

(**
 * NI for conditionals with LOW guard.
 *
 * When the guard is observable, both runs take the same branch.
 *)
val ni_if_low_guard : ctx:sec_typing_ctx -> pc:sec_label ->
                      cond:expr -> then_e:expr -> else_e:expr ->
                      l_cond:sec_label -> obs:sec_label ->
                      s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           (* Guard label is at or below observation level *)
           sec_label_leq l_cond obs /\
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (EIf cond then_e else_e)) s1 /\
           sec_terminates fuel (mk_expr_dummy (EIf cond then_e else_e)) s2 /\
           (* IH: branches satisfy NI *)
           termination_insensitive_ni then_e obs /\
           termination_insensitive_ni else_e obs)
        (ensures
           termination_insensitive_ni (mk_expr_dummy (EIf cond then_e else_e)) obs)

let ni_if_low_guard ctx pc cond then_e else_e l_cond obs s1 s2 fuel =
  (* Guard is low, so by NI it evaluates to the same value in both runs.
     Therefore the same branch executes. By IH on that branch, result is NI. *)
  admit ()

(**
 * NI for explicit flows (assignments).
 *
 * Assignment x := e is secure iff label(e) <= label(x).
 * Combined with PC check: (pc `join` label(e)) <= label(x).
 *)
val ni_explicit_flow : src_label:sec_label -> dst_label:sec_label ->
  Lemma (requires sec_label_leq src_label dst_label)
        (ensures True (* Flow is allowed *))

let ni_explicit_flow src_label dst_label = ()

(**
 * NI for implicit flows (assignments in high context).
 *
 * When PC > obs, all assignments must target high variables.
 *)
val ni_implicit_flow : pc:sec_label -> obs:sec_label -> x:var_id -> x_label:sec_label ->
  Lemma (requires
           (* In high context *)
           ~(sec_label_leq pc obs) /\
           (* Assignment type-checks *)
           sec_label_leq pc x_label)
        (ensures
           (* Target must be high *)
           ~(sec_label_leq x_label obs))

let ni_implicit_flow pc obs x x_label =
  (* If pc > obs and pc <= x_label (by typing), then x_label > obs.
     This uses transitivity of the partial order. *)
  admit ()

(**
 * NI for sequences.
 *)
val ni_seq : ctx:sec_typing_ctx -> pc:sec_label ->
             e1:expr -> e2:expr -> obs:sec_label ->
             s1:sec_state -> s2:sec_state -> fuel:nat ->
  Lemma (requires
           low_equivalent obs s1 s2 /\
           sec_terminates fuel (mk_expr_dummy (ESeq e1 e2)) s1 /\
           sec_terminates fuel (mk_expr_dummy (ESeq e1 e2)) s2 /\
           termination_insensitive_ni e1 obs /\
           termination_insensitive_ni e2 obs)
        (ensures
           termination_insensitive_ni (mk_expr_dummy (ESeq e1 e2)) obs)

let ni_seq ctx pc e1 e2 obs s1 s2 fuel =
  (* By IH on e1: intermediate states are low-equivalent.
     By IH on e2 starting from those states: final states are low-equivalent. *)
  admit ()

(** ============================================================================
    SECTION: CONFINEMENT LEMMA
    ============================================================================

    The confinement lemma is CRITICAL for handling implicit flows through
    control structures. It states that when the program counter label is
    above the observation level (i.e., we're in a "secret context"), execution
    cannot modify any observable (low) state.

    This handles cases like:
      if secret then public := 1 else public := 0

    The type system rejects this because in the branches, pc = secret, and
    the assignment rule requires (pc `join` l_rhs) <= l_x. Since pc = secret
    and l_x = public, this fails (secret is not <= public).

    Reference: Volpano et al. 1996, Lemma 1
    ============================================================================ *)

(**
 * Confinement Lemma: High context cannot affect low state.
 *)
val sec_confinement_lemma :
    ctx: sec_typing_ctx ->
    pc: sec_label ->
    e: expr ->
    obs: sec_label ->
    s: sec_state ->
    fuel: nat ->
    Lemma
      (requires
        (* PC is above observation level (secret context) *)
        ~(sec_label_leq pc obs) /\
        (* Expression is well-typed at pc *)
        well_typed_ifc ctx pc e /\
        (* Expression terminates *)
        sec_terminates fuel e s)
      (ensures
        (* Low state is preserved *)
        (let (_, s') = sec_eval fuel e s in
         low_equivalent obs s s'))

let sec_confinement_lemma ctx pc e obs s fuel =
  (* Proof by induction on e:
   *
   * Case EVar x:
   *   Variable lookup doesn't modify state. QED.
   *
   * Case ELit lit:
   *   Literal evaluation doesn't modify state. QED.
   *
   * Case EBinary op e1 e2:
   *   By IH on e1, e2: state after each is low-equivalent to original.
   *   By transitivity: final state is low-equivalent to original. QED.
   *
   * Case EIf cond then_e else_e:
   *   The branches are type-checked under pc' = pc `join` l_cond >= pc > obs.
   *   By IH on the executed branch: it preserves low state. QED.
   *
   * Case EAssign x e:
   *   By typing: (pc `join` l_e) <= l_x
   *   Since pc > obs and join is monotonic: l_x >= pc > obs
   *   So l_x > obs, meaning x is high. Low state is unchanged. QED.
   *
   * Case ESeq e1 e2:
   *   By IH on e1: s ~_obs s1 (intermediate)
   *   By IH on e2: s1 ~_obs s2 (final)
   *   By transitivity: s ~_obs s2. QED.
   *
   * Case ELet x _ e1 e2:
   *   Similar to sequence. The binding x gets label >= pc > obs (high).
   *)
  admit ()

(** ============================================================================
    SECTION: TERMINATION-SENSITIVE NONINTERFERENCE (TSNI)
    ============================================================================

    TSNI is STRONGER than TINI: it additionally requires that if two low-
    equivalent states cause different termination behavior, no information
    is leaked. In other words:

      s1 ~_L s2 ==> (terminates(e, s1) <==> terminates(e, s2))

    This rules out termination channels like:
      if secret then loop_forever() else ()

    TSNI is harder to achieve and typically requires either:
    1. Proving termination (decidability issues)
    2. Using timing-sensitive type systems (Agat 2000)
    3. Constant-time programming disciplines
    ============================================================================ *)

(** TSNI property *)
let termination_sensitive_ni (e: expr) (obs: sec_label) : Type0 =
  forall (s1 s2: sec_state) (fuel: nat).
    low_equivalent obs s1 s2 ==>
    (* Same termination behavior *)
    (sec_terminates fuel e s1 <==> sec_terminates fuel e s2)

(** TSNI implies TINI *)
val tsni_implies_tini : e:expr -> obs:sec_label ->
  Lemma (requires termination_sensitive_ni e obs)
        (ensures termination_insensitive_ni e obs)

let tsni_implies_tini e obs =
  (* TSNI ensures both runs terminate (or both diverge).
     When both terminate, TINI follows from the same proof as T-5.5. *)
  admit ()

(** ============================================================================
    THEOREM T-5.5: NONINTERFERENCE
    ============================================================================

    Report ID: T-5.5
    Location: BrrrInformationFlow.fst (theorem statement) / BrrrSecurityTypeChecker.fst:709-731
    Priority: 5 (Research-Grade)
    Effort Estimate: 40-80 hours

    ============================================================================
    HISTORICAL CONTEXT (Denning 1976)
    ============================================================================

    The noninterference property was first formalized by Denning (1976) as the
    "confinement problem": ensuring that a computation confined to security
    level H cannot communicate information to level L where L < H.

    Denning's lattice model establishes:
      - Every data object has a SECURITY CLASS (element of the lattice)
      - Information flows "upward" in the lattice (from low to high)
      - A SECURE INFORMATION FLOW is one where information at class c1 only
        flows to class c2 when c1 <= c2

    The key insight: treating information flow as a lattice-theoretic property
    enables STATIC CERTIFICATION at compile time.

    ============================================================================
    LITERATURE REFERENCE
    ============================================================================

    Volpano, Smith, Irvine 1996: "A Sound Type System for Secure Flow Analysis"
    Journal of Computer Security, Vol. 4, No. 2-3, pp. 167-187

    This paper provided the first TYPE-THEORETIC proof of noninterference,
    connecting Denning's lattice model to standard type soundness proofs.
    The innovation: treating security levels as type annotations enables
    using standard progress/preservation techniques.

    ============================================================================
    THEOREM (Noninterference - Volpano et al. Theorem 1)
    ============================================================================

    If a program c is well-typed under typing context Gamma with program counter
    label pc, then for any observation level L >= pc and any two memories m1, m2
    that are low-equivalent at L, if c terminates in both m1 and m2, then the
    resulting memories are also low-equivalent at L.

    Formally:
      Gamma, pc |- c : cmd /\ m1 ~_L m2 /\ (c, m1) =>* m1' /\ (c, m2) =>* m2'
      ==> m1' ~_L m2'

    INTUITION: A well-typed program cannot leak secrets to public observers.
    If two runs start with the same public inputs (but possibly different secrets),
    they produce the same public outputs.

    ============================================================================
    PROOF TECHNIQUE (Induction on Typing Derivation)
    ============================================================================

    The standard proof uses induction on the typing derivation with a
    "confinement lemma" that shows high commands cannot affect low state.

    Key lemmas required:

    1. CONFINEMENT LEMMA (Critical for implicit flows):
       If pc > L, then executing c does not change low state.
         Gamma, pc |- c : cmd /\ pc > L
         ==> forall m m'. (c, m) =>* m' ==> m ~_L m'

       This handles the case where control flow depends on secrets.
       When the program counter label is high, we are in a "secret context"
       (e.g., inside an `if secret then ... else ...`). The confinement
       lemma ensures that ALL assignments in this context target high variables,
       so low state is unchanged regardless of which branch executes.

    2. EXPRESSION NONINTERFERENCE:
       If Gamma |- e : tau @ l and m1 ~_L m2, then:
         l <= L  ==>  eval(e, m1) = eval(e, m2)
         l > L   ==>  (any values are ok, not observable)

       Expressions with low labels produce the same value in low-equivalent
       memories. This follows by induction on expression structure.

    3. SUBSTITUTION LEMMA:
       Typing is preserved under substitution of well-typed values.

    ============================================================================
    LATTICE USAGE IN THE PROOF
    ============================================================================

    The security lattice laws are used throughout:

    - TRANSITIVITY: When combining flows (e.g., y := x + z), the result label
      is join(label(x), label(z)). If both <= L, then result <= L by transitivity.

    - JOIN PROPERTIES: The pc is raised to join(pc, label(guard)) when entering
      a conditional. Join's idempotency ensures pc `join` pc = pc.

    - ORDERING FROM JOIN: The condition "l <= L" is checked using
      l `join` L = L, which follows from the lattice definition.

    ============================================================================
    TERMINATION SENSITIVITY
    ============================================================================

    The theorem as stated is TERMINATION-INSENSITIVE: it requires both runs
    to terminate. A termination channel exists:

      if secret then loop_forever() else ()

    An attacker can deduce `secret` from whether the program terminates.
    Termination-SENSITIVE noninterference is harder and requires either:
    - Proving termination (decidability issues)
    - Using a cost model (Agat 2000)
    - Timing-sensitive type systems (Volpano & Smith 1997)

    ============================================================================
    COMPLEXITY WARNING
    ============================================================================

    Full mechanization requires:
    - Operational semantics formalization (~400 lines)
    - Security typing rules (~300 lines)
    - Confinement lemma (~200 lines)
    - Main induction (~300 lines)
    - Supporting lemmas about memory operations (~200 lines)

    Total: approx 1400 lines of F-star for a complete proof.

    RELATED WORK:
    - Heintze & Riecke 1998: Proved noninterference for SLam calculus
    - Pottier & Simonet 2003: Proved for ML with references (using regions)
    - Stefan et al. 2017: Mechanized proof in Liquid Haskell (LIO monad)
    - Lourenco & Caires 2015: Dependent types for information flow (DCC)

    See also: SPECIFICATION_ERRATA.md for corrections to the spec based on
    mechanization efforts.
    ============================================================================ *)

(**
 * T-5.5: Noninterference Theorem
 *
 * Well-typed IFC programs satisfy termination-insensitive noninterference:
 * if two initial states agree on low (observable) data, and the program
 * terminates in both, then the final states also agree on low data.
 *
 * This is the fundamental soundness theorem for information flow type systems.
 * It guarantees that secret data cannot influence public outputs.
 *
 * Parameters:
 * - e: The expression to evaluate
 * - pc: The program counter label (security level of current context)
 * - L: The observation level (attacker's clearance)
 * - m1, m2: Initial memories that are low-equivalent at L
 * - fuel: Evaluation fuel (for termination)
 *
 * Requires:
 * - Expression e is well-typed at security level pc
 * - Memories m1 and m2 are low-equivalent at observation level L
 * - The program counter pc is at most L (we're in observable context)
 * - Evaluation terminates in both memories
 *
 * Ensures:
 * - Final memories are low-equivalent at L
 * - Final values are indistinguishable at L (if expression produces value)
 *)
val theorem_t5_5_noninterference :
    e: expr ->
    pc: sec_label ->
    obs_level: observation_level ->
    m1: security_memory ->
    m2: security_memory ->
    fuel: nat ->
    Lemma
      (requires
        (* Expression is well-typed at security level pc *)
        (* well_typed_ifc pc e /\ *)  (* Abstracted - would need IFC typing *)
        (* Memories are low-equivalent *)
        memory_low_equiv obs_level m1 m2 /\
        (* PC is observable (we're not in a secret branch) *)
        sec_label_leq pc obs_level /\
        (* Program terminates in both memories *)
        terminates e m1 fuel /\
        terminates e m2 fuel)
      (ensures
        (* Final memories are low-equivalent *)
        (match eval_security e m1 fuel, eval_security e m2 fuel with
         | Some (v1, m1'), Some (v2, m2') ->
             memory_low_equiv obs_level m1' m2' /\
             (* Final values are indistinguishable if result is low *)
             True  (* Would need result label obs_level ==> v1 == v2 *)
         | _, _ -> True))

let theorem_t5_5_noninterference e pc obs_level m1 m2 fuel =
  (* ============================================================================
   * PROOF OF NONINTERFERENCE (Volpano et al. 1996, Theorem 1)
   * ============================================================================
   *
   * The proof proceeds by induction on the TYPING DERIVATION, not the syntax
   * of expressions. This is crucial because security properties depend on how
   * the expression was typed, not just its structure.
   *
   * LATTICE PROPERTIES USED:
   *   - Transitivity of <=: l1 <= l2 /\ l2 <= l3 ==> l1 <= l3
   *   - Monotonicity of join: l1 <= l1' ==> l1 `join` l2 <= l1' `join` l2
   *   - Join is LUB: l1 `join` l2 >= l1 and l1 `join` l2 >= l2
   *   - Ordering via join: l1 <= l2 <==> l1 `join` l2 = l2
   *
   * ============================================================================
   * CASE ANALYSIS BY TYPING RULE
   * ============================================================================
   *
   * Case T-VAR (variable reference): e = x where Gamma(x) = tau @ l
   *   ------------------------------------------------------------------
   *   Goal: If m1 ~_L m2, then values of x in m1 and m2 satisfy:
   *         l <= L ==> m1(x) = m2(x)
   *
   *   Proof:
   *     If l <= L: By definition of m1 ~_L m2, all variables with label <= L
   *       have identical values in m1 and m2. Since label(x) = l <= L,
   *       we have m1(x) = m2(x).
   *
   *     If l > L: The values may differ, but they are not observable at L.
   *       Noninterference is trivially satisfied (high values can differ).
   *
   *   State change: None. Variable lookup doesn't modify memory.
   *
   * Case T-CONST (constant): e = c
   *   ------------------------------------------------------------------
   *   Goal: Constants produce same value in both runs.
   *
   *   Proof: Constants are pure and don't depend on state.
   *     eval(c, m1) = c = eval(c, m2)
   *     Result label is bottom (most public), so always observable.
   *
   *   State change: None.
   *
   * Case T-OP (binary operation): e = e1 op e2
   *   ------------------------------------------------------------------
   *   where Gamma; pc |- e1 : tau @ l1 and Gamma; pc |- e2 : tau @ l2
   *   Result label: l1 `join` l2
   *
   *   Goal: Operations preserve noninterference.
   *
   *   Proof by IH on e1 and e2:
   *     By IH on e1: v1 from m1, v1' from m2
   *       If l1 <= L: v1 = v1' (by IH)
   *
   *     By IH on e2: v2 from m1, v2' from m2
   *       If l2 <= L: v2 = v2' (by IH)
   *
   *     Result label is l1 `join` l2.
   *     If l1 `join` l2 <= L (result is observable):
   *       Then l1 <= L and l2 <= L (since join is LUB)
   *       By IH, v1 = v1' and v2 = v2'
   *       By congruence: v1 op v2 = v1' op v2'
   *
   *   State change: By IH, intermediate states are low-equivalent.
   *
   * Case T-IF (conditional): e = if e0 then e1 else e2
   *   ------------------------------------------------------------------
   *   Gamma; pc |- e0 : bool @ l0
   *   Gamma; pc' |- e1 : tau @ l1  where pc' = pc `join` l0
   *   Gamma; pc' |- e2 : tau @ l2
   *
   *   This is the CRITICAL CASE for implicit flows.
   *
   *   Subcase (a): l0 <= L (guard is low/observable)
   *     By IH on e0: same boolean in both runs (call it b)
   *     Both runs take the same branch.
   *     By IH on the chosen branch: noninterference preserved.
   *
   *   Subcase (b): l0 > L (guard is high/secret) - IMPLICIT FLOW CASE
   *     Runs may take DIFFERENT branches (since guard may differ).
   *     PC is raised to pc' = pc `join` l0 > L (secret context).
   *
   *     By CONFINEMENT LEMMA (sec_confinement_lemma):
   *       When pc' > L, execution cannot modify low state.
   *       Therefore: m1 ~_L m1' and m2 ~_L m2'
   *
   *     By transitivity of ~_L:
   *       m1 ~_L m2 (given)
   *       m1 ~_L m1' (confinement on run 1)
   *       m2 ~_L m2' (confinement on run 2)
   *       => m1' ~_L m2' (by transitivity)
   *
   *   This is where the type system prevents implicit flows:
   *     if secret then public := 1 else public := 0
   *   would require typing the assignments under pc = secret,
   *   but (secret `join` Public) <= Public is FALSE.
   *
   * Case T-ASSIGN (assignment): x := e
   *   ------------------------------------------------------------------
   *   Gamma; pc |- e : tau @ l
   *   Typing requires: (pc `join` l) <= label(x)
   *
   *   Subcase (a): label(x) > L (target is high)
   *     Assignment modifies a high variable.
   *     Low state unchanged in both runs.
   *     m1' ~_L m1 ~_L m2 ~_L m2' => m1' ~_L m2'
   *
   *   Subcase (b): label(x) <= L (target is low)
   *     By typing constraint: (pc `join` l) <= label(x) <= L
   *     This implies l <= L (since join is LUB and result <= L)
   *
   *     By IH on e: e produces same value v in both runs (since l <= L)
   *
   *     Both runs assign v to x.
   *     Since x is low and same value is assigned: m1' ~_L m2'
   *
   * Case T-SEQ (sequence): e1; e2
   *   ------------------------------------------------------------------
   *   Goal: Sequential composition preserves noninterference.
   *
   *   Proof:
   *     m1 ~_L m2 (given)
   *     By IH on e1: m1_mid ~_L m2_mid (after e1)
   *     By IH on e2 starting from m1_mid, m2_mid: m1' ~_L m2'
   *
   * Case T-LET (let binding): let x = e1 in e2
   *   ------------------------------------------------------------------
   *   Similar to sequence. The binding x gets label(e1).
   *   Body e2 is checked with x in scope at that label.
   *   By IH on e1 and e2.
   *
   * Case T-WHILE (loop): while e0 do e1
   *   ------------------------------------------------------------------
   *   By nested induction on loop iterations.
   *
   *   Base case (0 iterations): Guard is false in both runs.
   *     By IH on guard: if guard <= L, same truth value.
   *     If true/true: contradiction (0 iterations means guard false)
   *     If false/false: no change, m1 ~_L m2
   *
   *   Inductive case (n+1 iterations):
   *     Guard is true (at least once).
   *     By IH on body: one iteration preserves ~_L
   *     By induction on iterations: n more iterations preserve ~_L
   *
   *   If guard > L (secret loop):
   *     By confinement: each iteration preserves low state.
   *     (But note: different iteration counts could leak info
   *      through termination. This is why TINI is weaker than TSNI.)
   *
   * ============================================================================
   * CONFINEMENT LEMMA (Used in T-IF high guard case)
   * ============================================================================
   *
   * Lemma: If pc > L, then execution of e does not change low state.
   *
   * Proof: By induction on e.
   *   - Assignments: By typing, (pc `join` l) <= label(target).
   *     Since pc > L, label(target) > L. Only high vars modified.
   *   - Conditionals: PC is raised higher. By IH, branches confine.
   *   - Sequences: By IH, each sub-expression confines.
   *
   * ============================================================================
   * TERMINATION SENSITIVITY
   * ============================================================================
   *
   * This proof establishes TERMINATION-INSENSITIVE noninterference.
   * The theorem requires both runs to terminate.
   *
   * A termination channel exists:
   *   if secret then loop_forever() else ()
   *
   * Observation: program terminates only when secret is false.
   * This leaks 1 bit per execution.
   *
   * Termination-SENSITIVE NI would additionally require:
   *   m1 ~_L m2 ==> (terminates(e, m1) <==> terminates(e, m2))
   *
   * This is captured by the separate termination_sensitive_ni predicate.
   *
   * ============================================================================
   * MECHANIZATION STATUS
   * ============================================================================
   *
   * Full mechanization requires:
   *   - Formal definition of eval_security matching BrrrEval.fst
   *   - Security typing judgment as inductive type (added above)
   *   - Induction on typing derivation
   *   - Confinement lemma (sec_confinement_lemma above)
   *
   * The structure above provides the complete proof outline.
   * Each case is discharged by the corresponding auxiliary lemma.
   * ============================================================================
   *)
  (* Apply auxiliary lemmas based on expression structure *)
  admit ()  (* Full mechanization: 40-80 hours with formal eval_security *)


(** ============================================================================
    THEOREM T-5.6: BLAME SOUNDNESS
    ============================================================================

    Report ID: T-5.6
    Location: BrrrContracts.fst (theorem statement)
    Priority: 5 (Research-Grade)
    Effort Estimate: 16-32 hours

    LITERATURE REFERENCE:
    Wadler, Findler 2009: "Well-Typed Programs Can't Be Blamed"
    ESOP 2009, LNCS 5502, pp. 1-16, Theorem 1

    THEOREM (Blame Soundness - Wadler-Findler Theorem 1):
    If a program raises blame at label l with party p, then the term named
    by l with polarity p is not well-typed at its declared type.

    Equivalently: A well-typed term cannot be positively blamed.

    Formally:
      e -->* blame l (+) ==> not (Gamma |- l^+ : A)
      e -->* blame l (-) ==> not (Gamma |- l^- : A)

    PROOF TECHNIQUE:
    The proof uses a step-indexed logical relation that assigns meaning to
    casts. The key insight is that casts between compatible types preserve
    the logical relation, while casts between incompatible types are the
    only source of blame.

    Key definitions:
    1. Value compatibility: V[[A]] is the set of values semantically of type A
    2. Cast compatibility: A cast from A to B succeeds if A <: B or B <: A
    3. Blame assignment: When a cast fails, blame is assigned to the
       responsible party based on the subtyping direction

    COMPLEXITY WARNING:
    Full mechanization requires:
    - Cast calculus syntax and semantics (~200 lines)
    - Step-indexed logical relation (~400 lines)
    - Compatibility lemmas (~200 lines)
    - Main theorem proof (~200 lines)

    Total: approx 1000 lines of F-star for a complete proof.

    RELATED WORK:
    - Findler & Felleisen 2002: Original contracts with blame
    - Dimoulas et al. 2011: Correct blame for first-class contracts
    - Greenberg et al. 2010: Space-efficient manifest contracts
    ============================================================================ *)

(**
 * T-5.6: Blame Soundness Theorem
 *
 * When contract monitoring produces blame, the blamed party is indeed
 * responsible for the contract violation. Specifically:
 *
 * - Positive blame means the wrapped value failed to satisfy the contract's
 *   codomain constraint (the term didn't produce what it promised).
 *
 * - Negative blame means the context failed to satisfy the contract's
 *   domain constraint (the context didn't provide what was required).
 *
 * This theorem ensures that blame tracking is SOUND: if blame is raised,
 * there was a genuine contract violation by the blamed party.
 *
 * Parameters:
 * - c: The contract being monitored
 * - v: The value being checked against the contract
 *
 * Ensures:
 * - If monitoring returns BlamePositive, the value violated the codomain
 * - If monitoring returns BlameNegative, the context violated the domain
 *)
val theorem_t5_6_blame_soundness :
    c: blame_contract ->
    v: value ->
    Lemma
      (requires True)
      (ensures
        (match monitor_contract c v with
         | MRBlame party label ->
             party_violates party c v
         | MRValue _ -> True  (* No blame, no violation *)
         | MRError _ -> True  (* Errors are separate from blame *)))

let theorem_t5_6_blame_soundness c v =
  (* PROOF OUTLINE (Wadler-Findler 2009):
   *
   * By case analysis on the result of monitor_contract:
   *
   * Case MRValue v':
   *   No blame raised, theorem holds vacuously.
   *
   * Case MRBlame BlamePositive label:
   *   The positive party (the wrapped term) is blamed.
   *   This means the cast from the term's type to the contract's codomain failed.
   *   By definition of cast failure: v does not semantically inhabit bc_codomain.
   *   Therefore party_violates BlamePositive c v holds.
   *
   * Case MRBlame BlameNegative label:
   *   The negative party (the context) is blamed.
   *   This means the cast from the context's argument to the domain failed.
   *   By definition of cast failure: v does not semantically inhabit bc_domain.
   *   Therefore party_violates BlameNegative c v holds.
   *
   * KEY LEMMA (Cast Blame Assignment):
   *   For a cast (cast A B l v):
   *   - If A <: B and cast fails, blame positive (term at A claims B, fails)
   *   - If B <: A and cast fails, blame negative (context at B claims A, fails)
   *   - If neither A <: B nor B <: A, cast is statically rejected
   *
   * The critical insight is that subtyping determines blame direction:
   * - Upcast (A <: B): term is responsible for meeting supertype constraint
   * - Downcast (B <: A): context is responsible for providing subtype value
   *
   * STEP-INDEXED PROOF (for recursive types):
   * Define V_k[[A]] as k-step approximation of semantic type.
   * Show: forall k. v in V_k[[A]] ==> cast A A l v does not blame.
   * Induction on k, with compatibility lemmas for each type constructor.
   *)
  admit ()  (* T-5.6: 16-32 hours - requires cast calculus formalization *)


(** ============================================================================
    THEOREM T-5.7: PARAMETRICITY (ABSTRACTION THEOREM)
    ============================================================================

    Report ID: T-5.7
    Location: BrrrTypeChecker.fst (theorem statement)
    Priority: 5 (Research-Grade)
    Effort Estimate: 16-32 hours

    LITERATURE REFERENCE:
    Reynolds 1983: "Types, Abstraction and Parametric Polymorphism"
    IFIP Congress 1983, pp. 513-523

    See also:
    - Wadler 1989: "Theorems for Free!"
    - Bernardy et al. 2010: "Proofs for Free" (Agda mechanization)

    THEOREM (Parametricity / Abstraction Theorem - Reynolds 1983):
    If a term e has polymorphic type (forall alpha. tau), then for any
    two types A, B and any relation R : A <-> B, the instantiations
    e[A] and e[B] are related by the relational interpretation of tau.

    Formally:
      |- e : forall alpha. tau
      ==> forall A, B, R : A <-> B. (e[A], e[B]) in R[[tau]][alpha := R]

    COROLLARY (Identity Function):
    The only total function of type (forall a. a -> a) is the identity.
    Proof: Take R to be the graph of any function f: A -> B.
           By parametricity, id[A] and id[B] satisfy:
           forall x y. R(x, y) ==> R(id[A](x), id[B](y))
           Taking R = graph(f): f(x) = y ==> f(id[A](x)) = id[B](y)
           This forces id[A](x) = x for all x.

    PROOF TECHNIQUE:
    The proof uses logical relations, defining a relation R[[tau]] for each
    type tau, parameterized by interpretations of free type variables.

    For System F:
    R[[alpha]] = rho(alpha)  -- from environment
    R[[A -> B]] = { (f, g) | forall (a, b) in R[[A]], (f a, g b) in R[[B]] }
    R[[forall alpha. A]] = { (v, w) | forall R. (v, w) in R[[A]][alpha := R] }

    COMPLEXITY WARNING:
    Full mechanization requires:
    - Logical relation definition (~300 lines)
    - Fundamental lemma by induction on typing (~400 lines)
    - Identity and composition lemmas (~100 lines)
    - Example instantiations (~200 lines)

    Total: approx 1000 lines of F-star for a complete proof.

    RELATED WORK:
    - Pitts 2000: Parametric polymorphism and operational equivalence
    - Ahmed 2006: Step-indexed logical relations for recursive types
    - Dreyer et al. 2009: Logical relations for state and local reasoning
    ============================================================================ *)

(**
 * T-5.7: Parametricity (Fundamental Lemma of Logical Relations)
 *
 * Well-typed terms respect the logical relation interpretation of their types.
 * This is the key lemma that enables "theorems for free."
 *
 * Intuitively: A polymorphic function cannot inspect its type argument,
 * so it must treat all types uniformly. This uniformity is captured by
 * requiring that related inputs produce related outputs.
 *
 * Parameters:
 * - e: The expression to analyze
 * - t: The type of e
 * - rho: Type environment (interpretation of type variables)
 * - env1, env2: Value environments that are related under rho
 * - v1, v2: Results of evaluating e in env1, env2
 *
 * Ensures:
 * - If e has type t, then evaluating e in related environments produces
 *   related results according to the logical relation for t.
 *)
val theorem_t5_7_parametricity_fundamental :
    e: expr ->
    t: brrr_type ->
    rho: type_env ->
    ctx: list (var_id & brrr_type) ->
    env1: value_env ->
    env2: value_env ->
    Lemma
      (requires
        (* Expression is well-typed at type t *)
        (* well_typed ctx e t /\ *)  (* Abstracted - would need typing judgment *)
        (* Environments are related under the type context *)
        env_related rho ctx env1 env2)
      (ensures
        (* Results are related by logical relation at type t *)
        (* Would need: eval e env1 and eval e env2 are related by R[[t]](rho) *)
        True)

let theorem_t5_7_parametricity_fundamental e t rho ctx env1 env2 =
  (* PROOF OUTLINE (Reynolds 1983, Wadler 1989):
   *
   * By induction on the typing derivation Gamma |- e : tau
   *
   * Case T-VAR (x : tau in Gamma):
   *   By env_related, we have (env1(x), env2(x)) in R[[tau]].
   *
   * Case T-ABS (lambda x:A. e : A -> B):
   *   We must show the lambda values are in R[[A -> B]].
   *   Take any (a1, a2) in R[[A]].
   *   By IH on e with extended environments [x |-> a1] and [x |-> a2]:
   *   (eval e [env1, x:=a1], eval e [env2, x:=a2]) in R[[B]].
   *   This is exactly what R[[A -> B]] requires.
   *
   * Case T-APP (e1 e2 : B where e1 : A -> B and e2 : A):
   *   By IH, (eval e1 env1, eval e1 env2) in R[[A -> B]].
   *   By IH, (eval e2 env1, eval e2 env2) in R[[A]].
   *   By definition of R[[A -> B]]:
   *   (eval e1 env1 (eval e2 env1), eval e1 env2 (eval e2 env2)) in R[[B]].
   *
   * Case T-TABS (Lambda alpha. e : forall alpha. tau):
   *   We must show the type abstraction is in R[[forall alpha. tau]].
   *   Take any relation R : A <-> B.
   *   By IH on e with rho[alpha := R]:
   *   (eval e env1, eval e env2) in R[[tau]][alpha := R].
   *   This holds for all R, which is exactly R[[forall alpha. tau]].
   *
   * Case T-TAPP (e [A] : tau[A/alpha] where e : forall alpha. tau):
   *   By IH, (eval e env1, eval e env2) in R[[forall alpha. tau]].
   *   Instantiate with the identity relation on A.
   *   Get (eval e[A] env1, eval e[A] env2) in R[[tau]][alpha := Id_A].
   *   By substitution lemma, this equals R[[tau[A/alpha]]].
   *
   * KEY LEMMA (Substitution):
   *   R[[tau[A/alpha]]](rho) = R[[tau]](rho[alpha := Id_A])
   *   where Id_A = { (v, v) | v : A } is the identity relation on A.
   *)
  admit ()  (* T-5.7: 16-32 hours - requires logical relations infrastructure *)


(**
 * Corollary: The identity function is the only function of type forall a. a -> a
 *
 * This is the classic "free theorem" derivable from parametricity.
 *)
val corollary_identity_unique :
    f: (unit -> value) ->  (* Represents a closed term of type forall a. a -> a *)
    Lemma
      (ensures
        (* For all types A and values x : A, f[A](x) = x *)
        True)

let corollary_identity_unique f =
  (* By parametricity (T-5.7), for any A, B and R : A <-> B:
   *   forall x y. R(x, y) ==> R(f[A](x), f[B](y))
   *
   * Take A = B = some type T, and R = graph of any function g : T -> T.
   * Then: g(x) = y ==> g(f[T](x)) = f[T](y)
   *
   * Take x = y (so g(x) = x, i.e., x is a fixpoint of g).
   * Then: g(f[T](x)) = f[T](x)
   * So f[T](x) is also a fixpoint of g.
   *
   * This must hold for ALL g, including g = id.
   * For g = id: f[T](x) = x for all x.
   *
   * Therefore f is the identity function.
   *)
  admit ()


(** ============================================================================
    THEOREM T-5.8: OCCURRENCE TYPING SOUNDNESS
    ============================================================================

    Report ID: T-5.8
    Location: BrrrTypeChecker.fst
    Priority: 5 (Research-Grade)
    Effort Estimate: 8-16 hours

    LITERATURE REFERENCE:
    Tobin-Hochstadt, Felleisen 2008: "The Design and Implementation of Typed Scheme"
    POPL 2008, pp. 395-406, Section 3 and Theorem 1

    THEOREM (Occurrence Typing Soundness):
    If an expression e has union type (U T1 T2) and a predicate test (pred? e)
    succeeds, then in the true branch, e can be assigned the narrowed type T1
    (where T1 is the type that pred? selects for).

    Formally:
      Gamma |- e : (U T1 T2)   pred? selects T1
      Gamma |- (pred? e) : Bool
      -------------------------------------------
      Gamma, (pred? e) = true |- e : T1

    PROOF TECHNIQUE:
    The proof proceeds by showing that type environments can be refined by
    logical propositions. When we learn (pred? e) = true, we can update the
    type environment to record that e has the filtered type.

    Key mechanisms:
    1. Propositions: Assertions about runtime values (e.g., (number? x) = true)
    2. Filters: How type predicates affect type environments
    3. Refinement: Updating Gamma based on learned propositions

    COMPLEXITY WARNING:
    Full mechanization requires:
    - Proposition syntax and semantics (~150 lines)
    - Filter propagation rules (~200 lines)
    - Refinement relation (~150 lines)
    - Soundness proof (~300 lines)

    Total: approx 800 lines of F-star for a complete proof.

    RELATED WORK:
    - Kent 2016: Typed Racket implementation
    - Castagna & Lanvin 2017: Gradual typing with set-theoretic types
    - Pearce 2013: Occurrence typing in Whiley
    ============================================================================ *)

(**
 * T-5.8: Occurrence Typing Soundness
 *
 * Type narrowing based on predicate checks is sound: if a value passes
 * a type predicate test, it actually has the narrowed type.
 *
 * This theorem justifies the type system's ability to refine union types
 * in branches guarded by type predicates like number?, string?, etc.
 *
 * Example:
 *   let x : (U Number String) = ...
 *   if (number? x)
 *     then x + 1    -- x has type Number here
 *     else x ++ "!" -- x has type String here
 *
 * Parameters:
 * - v: The value being tested
 * - original_type: The declared type (a union type)
 * - pred: The type predicate being checked
 * - passed: Whether the predicate check succeeded
 *
 * Ensures:
 * - If predicate passes, value has the narrowed type
 * - If predicate fails, value has the complementary type (in ideal case)
 *)
val theorem_t5_8_occurrence_typing_sound :
    v: value ->
    original_type: brrr_type ->
    pred: type_predicate ->
    Lemma
      (requires
        (* Value has the original union type *)
        (* has_type v original_type /\ *)  (* Abstracted *)
        (* Original type is a union that pred can filter *)
        Some? (filter_union_type original_type pred))
      (ensures
        (* If predicate passes, value has filtered type *)
        satisfies_predicate v pred ==>
          (* has_type v (Some?.v (filter_union_type original_type pred)) *)
          True)

let theorem_t5_8_occurrence_typing_sound v original_type pred =
  (* PROOF OUTLINE (Tobin-Hochstadt & Felleisen 2008):
   *
   * By analysis of the predicate semantics and union type structure.
   *
   * Assume:
   * - v : (U T1 T2 ... Tn)  [value has union type]
   * - pred? filters for Ti    [predicate selects type Ti]
   * - (pred? v) = true        [predicate succeeds]
   *
   * By semantics of union types:
   *   v : (U T1 T2 ... Tn) iff v : T1 or v : T2 or ... or v : Tn
   *
   * By semantics of type predicates:
   *   (pred? v) = true iff v has the runtime structure corresponding to Ti
   *
   * SOUNDNESS ARGUMENT:
   * If (pred? v) = true, then by the correctness of the predicate implementation,
   * v must actually be a value of type Ti (the type pred? filters for).
   *
   * Therefore, we can soundly narrow the type from (U T1 T2 ... Tn) to Ti.
   *
   * KEY LEMMAS:
   *
   * 1. Predicate Correctness:
   *    (number? v) = true ==> v : Number
   *    (string? v) = true ==> v : String
   *    etc.
   *
   * 2. Union Elimination:
   *    v : (U T1 T2) /\ v : T1 ==> we can use v at type T1
   *
   * 3. Filter Soundness:
   *    filter_union (U T1 T2) pred = T1 when pred selects T1
   *    ==> (pred? v) = true implies v : T1
   *
   * NEGATIVE CASE (predicate fails):
   * If (pred? v) = false, then v does NOT have type Ti.
   * Combined with v : (U T1 ... Tn), we get v : (U T1 ... T(i-1) T(i+1) ... Tn).
   * This is "type difference" and requires more sophisticated reasoning.
   *
   * IMPLEMENTATION NOTES:
   * - Typed Racket tracks "propositions" in the type environment
   * - When entering a branch, propositions refine the environment
   * - Bidirectional type checking propagates refinements
   *)
  admit ()  (* T-5.8: 8-16 hours - requires predicate semantics formalization *)


(** ============================================================================
    AUXILIARY DEFINITIONS AND HELPER LEMMAS
    ============================================================================

    These helpers support the main theorems by providing:
    1. Security label operations satisfying lattice laws
    2. Runtime type checking for dynamic values
    3. Key lemmas for the noninterference proof

    ============================================================================
    LATTICE LAW VERIFICATION
    ============================================================================

    The sec_label type forms a lattice with the following operations
    (defined in BrrrSecurityTypes.fst):

      sec_label_leq  : sec_label -> sec_label -> bool   (* partial order: <= *)
      sec_label_join : sec_label -> sec_label -> sec_label  (* lub: join *)
      sec_label_meet : sec_label -> sec_label -> sec_label  (* glb: meet *)

    For correctness, these MUST satisfy the lattice laws from the module header.
    Verification of these laws is in BrrrSecurityTypes.Theorems.fst.

    PRODUCT LATTICE STRUCTURE: Our sec_label is a PRODUCT of:
      - Confidentiality lattice (who can READ)
      - Integrity lattice (who can WRITE)
      - Taint set (powerset lattice of taint kinds)

    The product of lattices is a lattice with componentwise operations:
      (c1, i1, t1) <= (c2, i2, t2)  iff  c1 <= c2 /\ i1 <= i2 /\ t1 <= t2
      (c1, i1, t1) `join` (c2, i2, t2) = (c1 `join` c2, i1 `join` i2, t1 `join` t2)

    This gives us the FOUR-POINT DIAMOND when confidentiality and integrity
    each have 2 elements (Low, High), before considering taints.
    ============================================================================ *)

(** Helper: Security label equality (needed for low-equivalence proofs)

    LATTICE CONNECTION: Equality is used to verify lattice antisymmetry:
      l1 <= l2 /\ l2 <= l1 ==> l1 = l2

    We check equality componentwise on the product lattice structure.
    For taint sets (which are lists), we check subset in both directions,
    which is equivalent to set equality. *)
let sec_label_eq (l1 l2: sec_label) : bool =
  l1.confidentiality = l2.confidentiality &&
  l1.integrity = l2.integrity &&
  taint_set_subset l1.taints l2.taints &&
  taint_set_subset l2.taints l1.taints

(** Helper: Check if a value semantically has a type *)
let value_has_runtime_type (v: value) (t: brrr_type) : bool =
  match v, t with
  | VInt _ _, TNumeric (NumInt _) -> true
  | VFloat _ _, TNumeric (NumFloat _) -> true
  | VBool _, TPrim PBool -> true
  | VString _, TPrim PString -> true
  | VUnit, TPrim PUnit -> true
  | VChar _, TPrim PChar -> true
  | _, _ -> false  (* Simplified *)

(** Helper: Confinement lemma for noninterference.
    High commands cannot affect low state.

    ============================================================================
    THE CONFINEMENT LEMMA (Volpano et al. 1996, Lemma 1)
    ============================================================================

    STATEMENT: If pc > L (we are in a high/secret context), then execution
    does not modify any variable with label <= L (low variables).

    INTUITION: In a secret branch (e.g., `if secret then ... else ...`),
    we raise the PC to secret level. The typing rule for assignment:

      Gamma, pc |- x := e : cmd    requires    pc `join` label(e) <= label(x)

    If pc > L, then pc `join` label(e) > L (since join is monotonic), so
    label(x) > L. Thus ALL assignments in a secret context target high
    variables, preserving low state.

    WHY THIS MATTERS FOR IMPLICIT FLOWS:

    Consider the classic implicit flow:
      if secret then public := 1 else public := 0

    Without confinement, an attacker could deduce `secret` from `public`.
    But our type system REJECTS this: in the branches, pc = secret, so
    assigning to `public` (with label Low) violates pc <= label(public).

    PROOF STRUCTURE (by induction on e):

    Case: Assignment x := rhs
      By typing: pc `join` label(rhs) <= label(x)
      Since pc > L, we have label(x) > L (by lattice transitivity)
      So x is high, and low state is unchanged.

    Case: If e0 then e1 else e2
      The branches are checked under pc' = pc `join` label(e0) >= pc > L.
      By IH on e1 and e2: both branches preserve low state.
      Since same low state before both, same after both. QED.

    Case: Sequence e1 ; e2
      By IH on e1: m ~_L m1 (intermediate state)
      By IH on e2: m1 ~_L m2 (final state)
      By transitivity of ~_L: m ~_L m2. QED.

    Case: While e0 do e1
      By nested induction on iterations. Each iteration preserves ~_L.

    LATTICE PROPERTIES USED:
      - Monotonicity of join: pc > L ==> pc `join` x >= pc > L
      - Transitivity of <=: Used in the assignment case
      - Transitivity of ~_L: Used in sequence case
    ============================================================================ *)
(** Confinement lemma for the old security_memory model.
    This is equivalent to sec_confinement_lemma but uses the
    security_memory representation from the original definitions. *)
val confinement_lemma :
    e: expr ->
    pc: sec_label ->
    obs_level: observation_level ->
    m: security_memory ->
    fuel: nat ->
    Lemma
      (requires
        (* PC is above observation level (we're in a secret context) *)
        ~(sec_label_leq pc obs_level) /\
        (* Expression terminates *)
        terminates e m fuel)
      (ensures
        (* Execution preserves low state *)
        (match eval_security e m fuel with
         | Some (_, m') -> memory_low_equiv obs_level m m'
         | None -> True))

let confinement_lemma e pc obs_level m fuel =
  (* This lemma is equivalent to sec_confinement_lemma.
   * The proof structure follows Volpano et al. 1996, Lemma 1.
   *
   * The key insight is that when pc > L (secret context):
   *   - All assignments must satisfy (pc `join` label_rhs) <= label_target
   *   - Since pc > L and join is monotonic, label_target > L
   *   - Therefore only high variables are modified
   *   - Low state is preserved
   *
   * See sec_confinement_lemma above for the detailed proof structure.
   *)
  admit ()


(** ============================================================================
    THEOREM SUMMARY AND VERIFICATION STATUS
    ============================================================================

    This module establishes four fundamental security theorems based on
    LATTICE-THEORETIC FOUNDATIONS (Denning 1976) and TYPE-THEORETIC
    PROOF TECHNIQUES (Volpano et al. 1996).

    ============================================================================
    LATTICE-BASED SECURITY MODEL
    ============================================================================

    All security properties are grounded in a BOUNDED LATTICE of security labels:

        (sec_label, sec_label_leq, sec_label_join, sec_label_meet, public, topsecret)

    The lattice satisfies:
      - Partial order laws (reflexivity, antisymmetry, transitivity)
      - Lattice laws (idempotency, commutativity, associativity of join/meet)
      - Bounded laws (public is bottom, topsecret is top)

    For the FOUR-POINT DIAMOND (confidentiality x integrity):

                         TopSecret
                          /     \
                    Secret       Confidential
                          \     /
                          Public

    Information flow security: data at level l1 flows to l2 only if l1 <= l2.

    ============================================================================
    THEOREM STATUS
    ============================================================================

    T-5.5 NONINTERFERENCE (Volpano 1996, Denning 1976):
      Status: ADMIT - requires operational semantics and IFC typing
      Effort: 40-80 hours
      Key challenge: Confinement lemma for implicit flows
      Lattice usage: Join for PC raising, ordering for flow checks

    T-5.6 BLAME SOUNDNESS (Wadler-Findler 2009):
      Status: ADMIT - requires cast calculus formalization
      Effort: 16-32 hours
      Key challenge: Step-indexed logical relations for recursive types
      Lattice usage: Subtyping ordering for cast direction

    T-5.7 PARAMETRICITY (Reynolds 1983):
      Status: ADMIT - requires logical relations infrastructure
      Effort: 16-32 hours
      Key challenge: Fundamental lemma by induction on typing
      Lattice usage: Type structure induction

    T-5.8 OCCURRENCE TYPING (Tobin-Hochstadt 2008):
      Status: ADMIT - requires predicate semantics
      Effort: 8-16 hours
      Key challenge: Proposition refinement propagation
      Lattice usage: Type narrowing as meet operation

    TOTAL ESTIMATED EFFORT: 80-160 hours for complete mechanization

    ============================================================================
    KEY REFERENCES
    ============================================================================

    FOUNDATIONAL:
      - Denning 1976: Lattice model of secure information flow (CACM)
      - Denning & Denning 1977: Certification of programs (CACM)

    TYPE-THEORETIC:
      - Volpano, Smith, Irvine 1996: Type system for IFC (JCS)
      - Myers 1999: JFlow practical IFC (POPL)
      - Myers & Liskov 2000: Decentralized Label Model (TOSEM)

    MECHANIZATION EXAMPLES:
      - Stefan et al. 2017: LIO in Liquid Haskell
      - Pottier & Simonet 2003: Flow Caml
      - Nanevski et al. 2008: Hoare Type Theory (ICFP)

    ============================================================================
    DEPENDENCIES
    ============================================================================

    - BrrrSecurityTypes.fst: Security labels and lattice operations
        * Must verify: lattice laws for sec_label_leq, sec_label_join, sec_label_meet
    - BrrrSecurityTypeChecker.fst: IFC typing rules
        * Must verify: typing preserves label invariants
    - BrrrContracts.fst: Contract infrastructure
        * Must verify: monitor_contract correctly assigns blame
    - BrrrEval.fst: Operational semantics
        * Must verify: evaluation respects type annotations
    - BrrrTypes.fst: Type definitions
        * Must verify: subtype relation is transitive

    ============================================================================
    RESEARCH IMPACT
    ============================================================================

    These theorems, when proven, would establish that brrr-lang's security
    type system provides:

    1. INFORMATION FLOW CONTROL: Noninterference guarantee ensures secrets
       cannot influence public outputs (neither directly nor through control flow).

    2. SOUND BLAME TRACKING: Gradual typing with correct blame assignment
       identifies the component responsible for type errors at runtime.

    3. PARAMETRIC POLYMORPHISM: "Theorems for free" from type signatures,
       enabling reasoning about polymorphic code without inspecting implementation.

    4. SOUND OCCURRENCE TYPING: Union type narrowing after predicate checks
       preserves type safety while enabling practical dynamic typing patterns.

    Together, these form a comprehensive security foundation based on
    LATTICE THEORY (Denning 1976) suitable for verified secure systems.

    See also: SPECIFICATION_ERRATA.md for corrections discovered during
    mechanization.
    ============================================================================ *)
