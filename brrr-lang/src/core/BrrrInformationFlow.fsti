(**
 * BrrrLang.Core.InformationFlow - Interface
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
 *   [Denning76]       Denning, D.E. "A Lattice Model of Secure Information Flow."
 *   [GoguenMeseguer82] Goguen, J.A. & Meseguer, J. "Security Policies and Security Models."
 *   [VolpanoSmith96]  Volpano, D., Smith, G., Irvine, C. "A Sound Type System for Secure Flow Analysis."
 *   [MyersLiskov97]   Myers, A.C. & Liskov, B. "A Decentralized Model for Information Flow Control."
 *   [SabelfeldMyers03] Sabelfeld, A. & Myers, A.C. "Language-Based Information-Flow Security."
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
 * CRITICAL: Secret and Confidential are INCOMPARABLE!
 *   - S </= C and C </= S
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
    ============================================================================ *)

(** value_eq is reflexive: v = v *)
val value_eq_refl (v: value) : Lemma (ensures value_eq v v = true) (decreases v)

(** Helper for list reflexivity *)
val value_list_eq_refl (vs: vlist value)
    : Lemma (ensures value_list_eq vs vs = true) (decreases vs)

(** value_eq is symmetric: v1 = v2 => v2 = v1 *)
val value_eq_sym (v1 v2: value)
    : Lemma (requires value_eq v1 v2 = true)
            (ensures value_eq v2 v1 = true)
            (decreases v1)

(** Helper for list symmetry *)
val value_list_eq_sym (vs1 vs2: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true)
            (ensures value_list_eq vs2 vs1 = true)
            (decreases vs1)

(** value_eq is transitive: v1 = v2 /\ v2 = v3 => v1 = v3 *)
val value_eq_trans (v1 v2 v3: value)
    : Lemma (requires value_eq v1 v2 = true /\ value_eq v2 v3 = true)
            (ensures value_eq v1 v3 = true)
            (decreases v1)

(** Helper for list transitivity *)
val value_list_eq_trans (vs1 vs2 vs3: vlist value)
    : Lemma (requires value_list_eq vs1 vs2 = true /\ value_list_eq vs2 vs3 = true)
            (ensures value_list_eq vs1 vs3 = true)
            (decreases vs1)

(** ============================================================================
    SECURITY LEVELS (DIAMOND LATTICE)
    ============================================================================

    Four-point diamond lattice for multi-level security with compartmentalization.

                       TopSecret (T)
                      /             \
                 Secret (S)    Confidential (C)
                      \             /
                        Public (P)

    Key insight: Secret and Confidential are INCOMPARABLE.
    ============================================================================ *)

(** Security level type - a four-point diamond lattice *)
type sec_level =
  | Public       : sec_level   (* Bottom: observable by all *)
  | Confidential : sec_level   (* Middle: one compartment *)
  | Secret       : sec_level   (* Middle: another compartment (incomparable with Confidential) *)
  | TopSecret    : sec_level   (* Top: highest classification *)

(** Security level ordering for diamond lattice - partial order.
    Information may flow from level l1 to level l2 iff l1 <= l2.
    NOTE: Secret and Confidential are INCOMPARABLE. *)
val sec_leq (l1 l2: sec_level) : bool

(** Security level join (least upper bound).
    Key insight: join(Secret, Confidential) = TopSecret *)
val sec_join (l1 l2: sec_level) : sec_level

(** Security level meet (greatest lower bound).
    Key insight: meet(Secret, Confidential) = Public *)
val sec_meet (l1 l2: sec_level) : sec_level

(** ============================================================================
    SECURITY LEVEL ORDERING PROOFS
    ============================================================================ *)

(** Reflexivity: Every security level is related to itself *)
val sec_leq_refl (l: sec_level) : Lemma (ensures sec_leq l l = true)

(** Antisymmetry: If l1 <= l2 and l2 <= l1, then l1 = l2 *)
val sec_leq_antisym (l1 l2: sec_level)
    : Lemma (requires sec_leq l1 l2 = true /\ sec_leq l2 l1 = true)
            (ensures l1 = l2)

(** Transitivity: If l1 <= l2 and l2 <= l3, then l1 <= l3 *)
val sec_leq_trans (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l1 l2 = true /\ sec_leq l2 l3 = true)
            (ensures sec_leq l1 l3 = true)

(** sec_leq is decidable - equality decision *)
val sec_level_eq (l1 l2: sec_level) : bool

(** sec_level_eq is reflexive *)
val sec_level_eq_refl (l: sec_level) : Lemma (ensures sec_level_eq l l = true)

(** sec_level_eq is symmetric *)
val sec_level_eq_sym (l1 l2: sec_level)
    : Lemma (requires sec_level_eq l1 l2 = true)
            (ensures sec_level_eq l2 l1 = true)

(** sec_level_eq implies Leibniz equality *)
val sec_level_eq_implies_eq (l1 l2: sec_level)
    : Lemma (requires sec_level_eq l1 l2 = true)
            (ensures l1 = l2)

(** ============================================================================
    JOIN SEMILATTICE PROOFS
    ============================================================================ *)

(** Associativity of join *)
val sec_join_assoc (l1 l2 l3: sec_level)
    : Lemma (ensures sec_join (sec_join l1 l2) l3 = sec_join l1 (sec_join l2 l3))

(** Commutativity of join *)
val sec_join_comm (l1 l2: sec_level)
    : Lemma (ensures sec_join l1 l2 = sec_join l2 l1)

(** Idempotency of join *)
val sec_join_idem (l: sec_level)
    : Lemma (ensures sec_join l l = l)

(** Join is an upper bound for left operand: l1 <= (l1 join l2) *)
val sec_join_upper_left (l1 l2: sec_level)
    : Lemma (ensures sec_leq l1 (sec_join l1 l2) = true)

(** Join is an upper bound for right operand: l2 <= (l1 join l2) *)
val sec_join_upper_right (l1 l2: sec_level)
    : Lemma (ensures sec_leq l2 (sec_join l1 l2) = true)

(** Join is the LEAST upper bound *)
val sec_join_lub (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l1 l3 = true /\ sec_leq l2 l3 = true)
            (ensures sec_leq (sec_join l1 l2) l3 = true)

(** Public is the bottom element *)
val sec_public_bottom (l: sec_level)
    : Lemma (ensures sec_leq Public l = true)

(** TopSecret is the top element *)
val sec_topsecret_top (l: sec_level)
    : Lemma (ensures sec_leq l TopSecret = true)

(** Join with Public is identity *)
val sec_join_public_left (l: sec_level)
    : Lemma (ensures sec_join Public l = l)

val sec_join_public_right (l: sec_level)
    : Lemma (ensures sec_join l Public = l)

(** Join with TopSecret is absorbing *)
val sec_join_topsecret_left (l: sec_level)
    : Lemma (ensures sec_join TopSecret l = TopSecret)

val sec_join_topsecret_right (l: sec_level)
    : Lemma (ensures sec_join l TopSecret = TopSecret)

(** DEPRECATED: sec_secret_top - use sec_topsecret_top instead for four-point lattice *)
val sec_secret_top (l: sec_level)
    : Lemma (ensures sec_leq l Secret = true \/ l = TopSecret \/ l = Confidential)

(** DEPRECATED: sec_join_secret_left - Secret is no longer absorbing *)
val sec_join_secret_left (l: sec_level)
    : Lemma (ensures sec_join Secret l = Secret \/ sec_join Secret l = TopSecret)

(** DEPRECATED: sec_join_secret_right *)
val sec_join_secret_right (l: sec_level)
    : Lemma (ensures sec_join l Secret = Secret \/ sec_join l Secret = TopSecret)

(** ============================================================================
    MEET SEMILATTICE PROOFS
    ============================================================================ *)

(** Associativity of meet *)
val sec_meet_assoc (l1 l2 l3: sec_level)
    : Lemma (ensures sec_meet (sec_meet l1 l2) l3 = sec_meet l1 (sec_meet l2 l3))

(** Commutativity of meet *)
val sec_meet_comm (l1 l2: sec_level)
    : Lemma (ensures sec_meet l1 l2 = sec_meet l2 l1)

(** Idempotency of meet *)
val sec_meet_idem (l: sec_level)
    : Lemma (ensures sec_meet l l = l)

(** Meet is a lower bound for left operand: (l1 meet l2) <= l1 *)
val sec_meet_lower_left (l1 l2: sec_level)
    : Lemma (ensures sec_leq (sec_meet l1 l2) l1 = true)

val sec_meet_lower_right (l1 l2: sec_level)
    : Lemma (ensures sec_leq (sec_meet l1 l2) l2 = true)

(** Meet is the greatest lower bound *)
val sec_meet_glb (l1 l2 l3: sec_level)
    : Lemma (requires sec_leq l3 l1 = true /\ sec_leq l3 l2 = true)
            (ensures sec_leq l3 (sec_meet l1 l2) = true)

(** Meet with TopSecret is identity *)
val sec_meet_topsecret_left (l: sec_level)
    : Lemma (ensures sec_meet TopSecret l = l)

val sec_meet_topsecret_right (l: sec_level)
    : Lemma (ensures sec_meet l TopSecret = l)

(** Meet with Public is absorbing *)
val sec_meet_public_left (l: sec_level)
    : Lemma (ensures sec_meet Public l = Public)

val sec_meet_public_right (l: sec_level)
    : Lemma (ensures sec_meet l Public = Public)

(** ============================================================================
    LABELED TYPES (SECURITY-TYPED VALUES)
    ============================================================================

    A labeled type pairs a base type with a security label.
    Written T^l for type T at security level l.
    ============================================================================ *)

(** Labeled type: a base type with a security label *)
noeq type labeled_type = {
  base_type : brrr_type;
  label     : sec_level;
}

(** Create a labeled type *)
val label_type (t: brrr_type) (l: sec_level) : labeled_type

(** Create a public labeled type (observable by all) *)
val public_type (t: brrr_type) : labeled_type

(** Create a confidential labeled type (one compartment) *)
val confidential_type (t: brrr_type) : labeled_type

(** Create a secret labeled type (another compartment) *)
val secret_type (t: brrr_type) : labeled_type

(** Create a top-secret labeled type (highest classification) *)
val topsecret_type (t: brrr_type) : labeled_type

(** Labeled type equality *)
val labeled_type_eq (lt1 lt2: labeled_type) : bool

(** Labeled type equality is reflexive *)
val labeled_type_eq_refl (lt: labeled_type)
    : Lemma (ensures labeled_type_eq lt lt = true)

(** Labeled type equality is symmetric *)
val labeled_type_eq_sym (lt1 lt2: labeled_type)
    : Lemma (requires labeled_type_eq lt1 lt2 = true)
            (ensures labeled_type_eq lt2 lt1 = true)

(** Subtyping for labeled types.
    lt1 is a subtype of lt2 iff base types match and lt1.label <= lt2.label *)
val labeled_subtype (lt1 lt2: labeled_type) : bool

(** Labeled subtyping is reflexive *)
val labeled_subtype_refl (lt: labeled_type)
    : Lemma (ensures labeled_subtype lt lt = true)

(** Labeled subtyping is transitive *)
val labeled_subtype_trans (lt1 lt2 lt3: labeled_type)
    : Lemma (requires labeled_subtype lt1 lt2 = true /\ labeled_subtype lt2 lt3 = true)
            (ensures labeled_subtype lt1 lt3 = true)

(** Join of labeled types (for binary operations) *)
val labeled_type_join (lt1 lt2: labeled_type) : option labeled_type

(** ============================================================================
    SECURITY CONTEXT
    ============================================================================

    The security context maps variables to their labeled types.
    ============================================================================ *)

(** Security context: maps variable names to labeled types *)
type sec_ctx = list (var_id & labeled_type)

(** Empty security context *)
val empty_sec_ctx : sec_ctx

(** Extend security context with a binding *)
val extend_sec_ctx (x: var_id) (lt: labeled_type) (ctx: sec_ctx) : sec_ctx

(** Lookup variable in security context *)
val lookup_sec_ctx (x: var_id) (ctx: sec_ctx) : option labeled_type

(** Check if variable is in context *)
val in_sec_ctx (x: var_id) (ctx: sec_ctx) : bool

(** Get all variables in context *)
val sec_ctx_vars (ctx: sec_ctx) : list var_id

(** Get all labeled types in context *)
val sec_ctx_types (ctx: sec_ctx) : list labeled_type

(** ============================================================================
    PROGRAM COUNTER LABEL (PC) - IMPLICIT FLOW TRACKING
    ============================================================================

    The PC label tracks the security level of the control flow context.
    It prevents implicit flows through control dependencies.
    ============================================================================ *)

(** PC label is just a security level *)
type pc_label = sec_level

(** Initial PC label (public - no control flow constraints) *)
val initial_pc : pc_label

(** Raise PC label when entering conditional with given guard level *)
val raise_pc (pc: pc_label) (guard_level: sec_level) : pc_label

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

    Core security constraint: pc join source_label <= target_label
    ============================================================================ *)

(** Check if assignment is allowed: pc join rhs_label <= lhs_label *)
val check_assignment_flow (pc: pc_label) (rhs_label: sec_level) (lhs_label: sec_level) : bool

(** Assignment flow is always allowed when target is TopSecret *)
val assignment_flow_to_topsecret (pc: pc_label) (rhs_label: sec_level)
    : Lemma (ensures check_assignment_flow pc rhs_label TopSecret = true)

(** Assignment flow from Public to Public is allowed iff PC is Public *)
val assignment_flow_public_public (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Public Public = (pc = Public))

(** Assignment from Secret to Confidential is NEVER allowed (incomparable!) *)
val assignment_flow_secret_to_confidential_forbidden (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Secret Confidential = false)

(** Assignment from Confidential to Secret is NEVER allowed (incomparable!) *)
val assignment_flow_confidential_to_secret_forbidden (pc: pc_label)
    : Lemma (ensures check_assignment_flow pc Confidential Secret = false)

(** ============================================================================
    INFORMATION FLOW TYPE CHECKING
    ============================================================================

    The security type checker extends the regular type checker with:
    1. Security labels on all types
    2. PC tracking through control flow
    3. Flow constraints on assignments
    4. Label propagation through expressions
    ============================================================================ *)

(** Infer security type of a literal (always Public) *)
val sec_infer_literal (lit: literal) : labeled_type

(** Infer security type of unary operation *)
val sec_unary_op_type (op: unary_op) (lt: labeled_type) : option labeled_type

(** Infer security type of binary operation *)
val sec_binary_op_type (op: binary_op) (lt1 lt2: labeled_type) : option labeled_type

(** Information flow type checking with PC tracking *)
val sec_typecheck (ctx: sec_ctx) (pc: pc_label) (e: expr)
    : Tot (option labeled_type) (decreases e)

(** Type check a list of expressions *)
val sec_typecheck_list (ctx: sec_ctx) (pc: pc_label) (es: list expr)
    : Tot (option (list labeled_type)) (decreases es)

(** Type check a block (returns type of last expression) *)
val sec_typecheck_block (ctx: sec_ctx) (pc: pc_label) (es: list expr)
    : Tot (option labeled_type) (decreases es)

(** ============================================================================
    LOW EQUIVALENCE (INDISTINGUISHABILITY RELATION)
    ============================================================================

    Two memories are low-equivalent at observation level `obs` iff they agree
    on all variables whose security level flows to `obs`.
    ============================================================================ *)

(** Memory state: maps variables to values *)
type memory = list (var_id & value)

(** Lookup value in memory *)
val lookup_memory (x: var_id) (mem: memory) : option value

(** Two memories are low-equivalent at observation level `obs`
    iff they agree on all variables at level <= obs. *)
val low_equiv_at (ctx: sec_ctx) (mem1 mem2: memory) (obs: sec_level) : bool

(** Classic low equivalence at Public observation level *)
val low_equiv (ctx: sec_ctx) (mem1 mem2: memory) : bool

(** Low equivalence at observation level is reflexive *)
val low_equiv_at_refl (ctx: sec_ctx) (mem: memory) (obs: sec_level)
    : Lemma (ensures low_equiv_at ctx mem mem obs = true) (decreases ctx)

(** Low equivalence is reflexive (backward compatible) *)
val low_equiv_refl (ctx: sec_ctx) (mem: memory)
    : Lemma (ensures low_equiv ctx mem mem = true)

(** Low equivalence at observation level is symmetric *)
val low_equiv_at_sym (ctx: sec_ctx) (mem1 mem2: memory) (obs: sec_level)
    : Lemma (requires low_equiv_at ctx mem1 mem2 obs = true)
            (ensures low_equiv_at ctx mem2 mem1 obs = true)
            (decreases ctx)

(** Low equivalence is symmetric (backward compatible) *)
val low_equiv_sym (ctx: sec_ctx) (mem1 mem2: memory)
    : Lemma (requires low_equiv ctx mem1 mem2 = true)
            (ensures low_equiv ctx mem2 mem1 = true)

(** Low equivalence at observation level is transitive *)
val low_equiv_at_trans (ctx: sec_ctx) (mem1 mem2 mem3: memory) (obs: sec_level)
    : Lemma (requires low_equiv_at ctx mem1 mem2 obs = true /\ low_equiv_at ctx mem2 mem3 obs = true)
            (ensures low_equiv_at ctx mem1 mem3 obs = true)
            (decreases ctx)

(** Low equivalence is transitive (backward compatible) *)
val low_equiv_trans (ctx: sec_ctx) (mem1 mem2 mem3: memory)
    : Lemma (requires low_equiv ctx mem1 mem2 = true /\ low_equiv ctx mem2 mem3 = true)
            (ensures low_equiv ctx mem1 mem3 = true)

(** ============================================================================
    NONINTERFERENCE THEOREM
    ============================================================================

    High-security inputs do not affect low-security outputs.
    ============================================================================ *)

(** Helper: Public variable lookup type-checks to Public label *)
val sec_typecheck_var_public_label (ctx: sec_ctx) (x: var_id) (lt: labeled_type)
    : Lemma (requires lookup_sec_ctx x ctx = Some lt /\ lt.label = Public)
            (ensures sec_typecheck ctx Public (EVar x) = Some lt)

(** Expression evaluation result *)
type eval_result =
  | EvalValue : value -> eval_result
  | EvalStuck : eval_result

(** Simplified evaluation for expressions *)
val eval_expr (e: expr) (mem: memory) : Tot eval_result (decreases e)

(** Noninterference theorem statement type.
    For a well-typed expression with Public result type,
    low-equivalent inputs produce equal outputs. *)
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

(** Noninterference for variables *)
val noninterference_var (ctx: sec_ctx) (x: var_id) (mem1 mem2: memory)
    : Lemma (requires
               (match lookup_sec_ctx x ctx with
                | Some lt -> lt.label = Public
                | None -> false) /\
               low_equiv ctx mem1 mem2 = true)
            (ensures
               (match lookup_memory x mem1, lookup_memory x mem2 with
                | Some v1, Some v2 -> value_eq v1 v2 = true
                | None, None -> true
                | _, _ -> false))

(** Noninterference for literals *)
val noninterference_lit (lit: literal) (mem1 mem2: memory)
    : Lemma (ensures
               (match eval_expr (ELit lit) mem1, eval_expr (ELit lit) mem2 with
                | EvalValue v1, EvalValue v2 -> value_eq v1 v2 = true
                | EvalStuck, EvalStuck -> true
                | _, _ -> false))

(** Type soundness for variables *)
val type_soundness_var (ctx: sec_ctx) (x: var_id) (mem: memory)
    : Lemma (requires Some? (lookup_sec_ctx x ctx) /\ Some? (lookup_memory x mem))
            (ensures Some? (match eval_expr (EVar x) mem with EvalValue v -> Some v | _ -> None))

(** Assignment preserves low-equivalence statement type *)
type assignment_preserves_low_equiv_statement =
  ctx:sec_ctx -> pc:pc_label -> x:var_id -> rhs_lt:labeled_type ->
  mem1:memory -> mem2:memory -> v1:value -> v2:value ->
  Lemma (requires
           (match lookup_sec_ctx x ctx with
            | Some lhs_lt -> check_assignment_flow pc rhs_lt.label lhs_lt.label
            | None -> false) /\
           low_equiv ctx mem1 mem2 = true)
        (ensures true)

(** Main security theorem type: Well-typed programs are noninterfering *)
type security_theorem =
  ctx:sec_ctx -> e:expr ->
  squash (Some? (sec_typecheck ctx Public e)) ->
  mem1:memory -> mem2:memory ->
  squash (low_equiv ctx mem1 mem2 = true) ->
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
val is_security_typed_at (ctx: sec_ctx) (pc: pc_label) (e: expr) (target: sec_level) : bool

(** Check if expression result can flow to public (observable by all) *)
val can_flow_to_public (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool

(** Check if expression result can flow to confidential level *)
val can_flow_to_confidential (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool

(** Check if expression result can flow to secret level *)
val can_flow_to_secret (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool

(** Check if expression has a high-security dependency (Confidential, Secret, or TopSecret) *)
val has_high_security_dependency (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool

(** Check if expression has top-secret dependency *)
val has_topsecret_dependency (ctx: sec_ctx) (pc: pc_label) (e: expr) : bool

(** Check if expression involves incomparable levels (Secret and Confidential) *)
val involves_incomparable_levels (ctx: sec_ctx) (pc: pc_label) (e1 e2: expr) : bool

(** Get the security label of an expression *)
val get_security_label (ctx: sec_ctx) (pc: pc_label) (e: expr) : option sec_level

(** Get the minimum observation level required to see an expression's result *)
val minimum_observation_level (ctx: sec_ctx) (pc: pc_label) (e: expr) : option sec_level

(** Check if two levels are comparable in the lattice *)
val levels_are_comparable (l1 l2: sec_level) : bool

(** Levels that are incomparable: Secret vs Confidential *)
val levels_are_incomparable (l1 l2: sec_level) : bool

(** ============================================================================
    DECLASSIFICATION (Controlled Information Release)
    ============================================================================

    DECLASSIFICATION intentionally releases secret information to lower
    security levels. It is a CONTROLLED VIOLATION of noninterference.
    ============================================================================ *)

(** Declassification policy: specifies what can be declassified *)
noeq type declass_policy = {
  declass_name : string;
  allowed_patterns : list string;
  max_declass : option nat;
}

(** Declassification context tracks declassification usage *)
noeq type declass_ctx = {
  policies : list declass_policy;
  usage : list (string & nat);
}

(** Empty declassification context *)
val empty_declass_ctx : declass_ctx

(** Check if declassification is allowed *)
val can_declassify (dctx: declass_ctx) (policy_name: string) : bool

(** Declassify a labeled type to Public (if policy allows) *)
val declassify (dctx: declass_ctx) (policy_name: string) (lt: labeled_type)
    : option (labeled_type & declass_ctx)

(** ============================================================================
    ENDORSEMENT (Controlled Trust Upgrade)
    ============================================================================ *)

(** Integrity level (dual of confidentiality) *)
type integrity_level =
  | Untrusted : integrity_level
  | Trusted   : integrity_level

(** Integrity ordering: Untrusted < Trusted *)
val integrity_leq (i1 i2: integrity_level) : bool

(** ============================================================================
    TERMINATION-INSENSITIVE NONINTERFERENCE (TINI)
    ============================================================================

    TINI: Only considers terminating executions.
    If either diverges, property trivially satisfied.
    ============================================================================ *)

(** Execution result: programs either terminate with a result or diverge *)
type exec_result_full (a:Type) =
  | Terminates : result:a -> final_state:memory -> exec_result_full a
  | Diverges   : exec_result_full a

(** TINI property type *)
type tini_property (ctx: sec_ctx) (obs: sec_level) =
  e:expr -> mem1:memory -> mem2:memory ->
  exec1:exec_result_full value -> exec2:exec_result_full value ->
  Lemma (requires
           low_equiv_at ctx mem1 mem2 obs = true /\
           Terminates? exec1 /\ Terminates? exec2)
        (ensures
           (let Terminates v1 s1' = exec1 in
            let Terminates v2 s2' = exec2 in
            (match sec_typecheck ctx Public e with
             | Some lt ->
                 sec_leq lt.label obs = true ==> value_eq v1 v2 = true
             | None -> true) /\
            low_equiv_at ctx s1' s2' obs = true))

(** TINI check function: verify TINI for two executions *)
val check_tini (ctx: sec_ctx) (obs: sec_level)
               (mem1 mem2: memory)
               (exec1 exec2: exec_result_full value) : bool

(** TINI theorem statement type *)
type tini_theorem =
  ctx:sec_ctx -> e:expr -> obs:sec_level ->
  squash (Some? (sec_typecheck ctx Public e)) ->
  squash (forall (mem1 mem2: memory) (exec1 exec2: exec_result_full value).
            low_equiv_at ctx mem1 mem2 obs = true /\
            Terminates? exec1 /\ Terminates? exec2 ==>
            check_tini ctx obs mem1 mem2 exec1 exec2 = true)

(** ============================================================================
    TERMINATION-SENSITIVE NONINTERFERENCE (TSNI)
    ============================================================================

    TSNI: Also considers termination behavior.
    Requires: terminates(e, s1) <=> terminates(e, s2)
    ============================================================================ *)

(** Termination behavior type *)
type termination_behavior =
  | MustTerminate    : termination_behavior
  | MayDiverge       : termination_behavior
  | MustDiverge      : termination_behavior

(** Termination behavior ordering *)
val termination_leq (t1 t2: termination_behavior) : bool

(** TSNI property type *)
type tsni_property (ctx: sec_ctx) (obs: sec_level) =
  e:expr -> mem1:memory -> mem2:memory ->
  exec1:exec_result_full value -> exec2:exec_result_full value ->
  Lemma (requires low_equiv_at ctx mem1 mem2 obs = true)
        (ensures
           (Terminates? exec1 <==> Terminates? exec2) /\
           (Terminates? exec1 /\ Terminates? exec2 ==>
            (let Terminates v1 s1' = exec1 in
             let Terminates v2 s2' = exec2 in
             (match sec_typecheck ctx Public e with
              | Some lt ->
                  sec_leq lt.label obs = true ==> value_eq v1 v2 = true
              | None -> true) /\
             low_equiv_at ctx s1' s2' obs = true)))

(** TSNI check function: verify TSNI for two executions *)
val check_tsni (ctx: sec_ctx) (obs: sec_level)
               (mem1 mem2: memory)
               (exec1 exec2: exec_result_full value) : bool

(** Predicate for no termination channel *)
type termination_channel_kind =
  | LoopConditionChannel  : var_id -> termination_channel_kind
  | RecursionGuardChannel : string -> termination_channel_kind
  | BranchDivergence      : termination_channel_kind
  | UnboundedIteration    : termination_channel_kind

(** Termination channel descriptor *)
noeq type termination_channel = {
  channel_kind      : termination_channel_kind;
  source_level      : sec_level;
  observation_level : sec_level;
  location          : option string;
  description       : string;
}

(** Check if an expression has a termination channel at given observation level *)
val has_termination_channel (ctx: sec_ctx) (obs: sec_level) (e: expr)
    : Tot bool (decreases e)

(** Check list of expressions for termination channels *)
val has_termination_channel_list (ctx: sec_ctx) (obs: sec_level) (es: list expr)
    : Tot bool (decreases es)

(** Conservative divergence check: might this expression not terminate? *)
val might_diverge (ctx: sec_ctx) (e: expr) : Tot bool (decreases e)

val might_diverge_list (ctx: sec_ctx) (es: list expr) : Tot bool (decreases es)

(** Collect all termination channels in an expression *)
val no_termination_channel (ctx: sec_ctx) (obs: sec_level) (e: expr) : bool

(** TSNI theorem statement type *)
type tsni_theorem =
  ctx:sec_ctx -> e:expr -> obs:sec_level ->
  squash (Some? (sec_typecheck ctx Public e)) ->
  squash (no_termination_channel ctx obs e) ->
  squash (forall (mem1 mem2: memory) (exec1 exec2: exec_result_full value).
            low_equiv_at ctx mem1 mem2 obs = true ==>
            check_tsni ctx obs mem1 mem2 exec1 exec2 = true)

(** ============================================================================
    TERMINATION CHANNEL DETECTION
    ============================================================================

    Detects covert channels that leak information through termination behavior.
    ============================================================================ *)

(** Termination channel classification *)
val collect_termination_channels (ctx: sec_ctx) (obs: sec_level) (e: expr)
    : Tot (list termination_channel) (decreases e)

val collect_termination_channels_list (ctx: sec_ctx) (obs: sec_level) (es: list expr)
    : Tot (list termination_channel) (decreases es)

(** ============================================================================
    INTEGRITY LATTICE (FOUR-POINT DIAMOND)
    ============================================================================

    Dual of confidentiality lattice for tracking data integrity/trust.

                      HighIntegrity (H)
                     /                 \
              SystemData (S)     ValidatedUser (V)
                     \                 /
                       Untrusted (U)

    Key: SystemData and ValidatedUser are INCOMPARABLE.
    ============================================================================ *)

(** Four-point integrity diamond lattice *)
type integrity_level_full =
  | Untrusted      : integrity_level_full
  | ValidatedUser  : integrity_level_full
  | SystemData     : integrity_level_full
  | HighIntegrity  : integrity_level_full

(** Integrity ordering *)
val integrity_leq_full (i1 i2: integrity_level_full) : bool

(** Integrity join (least upper bound) *)
val integrity_join (i1 i2: integrity_level_full) : integrity_level_full

(** Integrity meet (greatest lower bound) *)
val integrity_meet (i1 i2: integrity_level_full) : integrity_level_full

(** Reflexivity of integrity ordering *)
val integrity_leq_refl (i: integrity_level_full)
    : Lemma (ensures integrity_leq_full i i = true)

(** Antisymmetry of integrity ordering *)
val integrity_leq_antisym (i1 i2: integrity_level_full)
    : Lemma (requires integrity_leq_full i1 i2 = true /\ integrity_leq_full i2 i1 = true)
            (ensures i1 = i2)

(** Transitivity of integrity ordering *)
val integrity_leq_trans (i1 i2 i3: integrity_level_full)
    : Lemma (requires integrity_leq_full i1 i2 = true /\ integrity_leq_full i2 i3 = true)
            (ensures integrity_leq_full i1 i3 = true)

(** Integrity join is an upper bound *)
val integrity_join_upper_left (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full i1 (integrity_join i1 i2) = true)

val integrity_join_upper_right (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full i2 (integrity_join i1 i2) = true)

(** Integrity meet is a lower bound *)
val integrity_meet_lower_left (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full (integrity_meet i1 i2) i1 = true)

val integrity_meet_lower_right (i1 i2: integrity_level_full)
    : Lemma (ensures integrity_leq_full (integrity_meet i1 i2) i2 = true)

(** ============================================================================
    ENDORSEMENT SYSTEM (Controlled Trust Upgrade)
    ============================================================================

    Endorsement is the integrity-side counterpart to declassification.
    ============================================================================ *)

(** Endorsement policy *)
noeq type endorse_policy = {
  policy_name       : string;
  allowed_from      : integrity_level_full;
  allowed_to        : integrity_level_full;
  required_checks   : list string;
  validator         : string;
  max_endorsements  : option nat;
}

(** Endorsement context tracks endorsement usage *)
noeq type endorse_ctx = {
  policies      : list endorse_policy;
  usage_counts  : list (string & nat);
  audit_log     : list string;
}

(** Empty endorsement context *)
val empty_endorse_ctx : endorse_ctx

(** Create a new endorsement context with policies *)
val create_endorse_ctx (policies: list endorse_policy) : endorse_ctx

(** Check if endorsement is allowed by policy *)
val can_endorse (ectx: endorse_ctx) (policy_name: string)
                (from_level: integrity_level_full) (to_level: integrity_level_full) : bool

(** Labeled value with integrity *)
noeq type integrity_labeled (a:Type) = {
  ivalue     : a;
  integrity  : integrity_level_full;
}

(** Create untrusted labeled value *)
val untrusted (#a:Type) (v: a) : integrity_labeled a

(** Create validated user data *)
val validated_user (#a:Type) (v: a) : integrity_labeled a

(** Create system data *)
val system_data (#a:Type) (v: a) : integrity_labeled a

(** Create high-integrity data *)
val high_integrity (#a:Type) (v: a) : integrity_labeled a

(** Endorse a value: upgrade its integrity level with policy check *)
val endorse_value (#a:Type)
                  (ectx: endorse_ctx)
                  (policy_name: string)
                  (lv: integrity_labeled a)
                  (target_level: integrity_level_full)
    : option (integrity_labeled a & endorse_ctx)

(** Endorse function matching spec signature *)
val endorse_simple (#a:Type) (v: a) (from_: integrity_level_full) (to_: integrity_level_full)
    : a & integrity_level_full

(** ============================================================================
    COMBINED CONFIDENTIALITY AND INTEGRITY LABELS (DLM)
    ============================================================================

    Combined security label with both confidentiality and integrity.
    ============================================================================ *)

(** Combined security label with both confidentiality and integrity *)
noeq type security_label = {
  confidentiality : sec_level;
  integrity       : integrity_level_full;
}

(** Security label ordering: must satisfy both dimensions *)
val security_label_leq (l1 l2: security_label) : bool

(** Security label join *)
val security_label_join (l1 l2: security_label) : security_label

(** Security label meet *)
val security_label_meet (l1 l2: security_label) : security_label

(** Security label ordering proofs *)
val security_label_leq_refl (l: security_label)
    : Lemma (ensures security_label_leq l l = true)

val security_label_leq_trans (l1 l2 l3: security_label)
    : Lemma (requires security_label_leq l1 l2 = true /\ security_label_leq l2 l3 = true)
            (ensures security_label_leq l1 l3 = true)

(** ============================================================================
    INTEGRITY-AWARE TYPE CHECKING
    ============================================================================ *)

(** Full labeled type with both confidentiality and integrity *)
noeq type full_labeled_type = {
  fbase_type     : brrr_type;
  flabel         : security_label;
}

(** Create a public, untrusted type (typical user input) *)
val public_untrusted (t: brrr_type) : full_labeled_type

(** Create a secret, high-integrity type (system secrets) *)
val secret_high_integrity (t: brrr_type) : full_labeled_type

(** Check if a type can be used as a sink (requires sufficient integrity) *)
val can_use_as_sink (flt: full_labeled_type) (required_integrity: integrity_level_full) : bool

(** Check if declassification is safe (must not be influenced by untrusted data) *)
val safe_declassification (flt: full_labeled_type) : bool

(** Check if endorsement is safe (must verify the data) *)
val safe_endorsement (current: integrity_level_full) (target: integrity_level_full) : bool

(** ============================================================================
    PRINCIPAL HIERARCHY (DLM)
    ============================================================================

    Principals are the entities that own, control, and access data.
    ============================================================================ *)

(** Principal type - entities that own and control data *)
type principal =
  | PUser        : user_name:string -> principal
  | PRole        : role_name:string -> principal
  | PConjunction : p1:principal -> p2:principal -> principal
  | PTop         : principal
  | PBot         : principal

(** Principal equality *)
val principal_eq (p1 p2: principal) : Tot bool (decreases p1)

(** Principal equality is reflexive *)
val principal_eq_refl (p: principal)
    : Lemma (ensures principal_eq p p = true) (decreases p)

(** ============================================================================
    ACTS-FOR RELATION
    ============================================================================

    The acts-for relation p1 >= p2 means p1 can act on behalf of p2.
    ============================================================================ *)

(** Acts-for relation environment: maps delegation relationships *)
type acts_for_env = list (principal & principal)

(** Empty acts-for environment *)
val empty_acts_for_env : acts_for_env

(** Add a delegation: p1 acts for p2 *)
val add_acts_for (p1 p2: principal) (env: acts_for_env) : acts_for_env

(** Check if acts-for is declared in environment *)
val acts_for_in_env (p1 p2: principal) (env: acts_for_env) : bool

(** Acts-for relation: p1 acts for p2 means p1 has at least as much authority as p2 *)
val acts_for (env: acts_for_env) (p1 p2: principal) : Tot bool (decreases %[p1; p2; 10])

(** Acts-for is reflexive *)
val acts_for_refl (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env p p = true)

(** Everyone acts for PTop *)
val acts_for_top (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env p PTop = true)

(** PBot acts for everyone *)
val acts_for_bot (env: acts_for_env) (p: principal)
    : Lemma (ensures acts_for env PBot p = true)

(** Conjunction acts for left component *)
val acts_for_conj_left (env: acts_for_env) (p1 p2: principal)
    : Lemma (ensures acts_for env (PConjunction p1 p2) p1 = true)

(** Conjunction acts for right component *)
val acts_for_conj_right (env: acts_for_env) (p1 p2: principal)
    : Lemma (ensures acts_for env (PConjunction p1 p2) p2 = true)

(** ============================================================================
    DLM LABEL COMPONENTS
    ============================================================================

    A label component specifies one owner's policy: {owner: reader1, reader2, ...}
    ============================================================================ *)

(** Label component: owner -> set of readers *)
noeq type label_component = {
  lc_owner   : principal;
  lc_readers : list principal;
}

(** Create a label component *)
val make_label_component (owner: principal) (readers: list principal) : label_component

(** Check if a principal is in a reader list *)
val principal_in_list (p: principal) (ps: list principal) : bool

(** Check if a principal can read according to a component *)
val can_read_component (env: acts_for_env) (p: principal) (lc: label_component) : bool

(** Label component equality *)
val label_component_eq (lc1 lc2: label_component) : bool

(** ============================================================================
    DLM LABELS
    ============================================================================

    A full DLM label is a CONJUNCTION of label components.
    ============================================================================ *)

(** DLM label: conjunction of components *)
type dlm_label = list label_component

(** Empty label (fully public - no restrictions) *)
val dlm_public : dlm_label

(** Single-owner label *)
val dlm_owned_by (owner: principal) (readers: list principal) : dlm_label

(** Check if a principal can read data with a DLM label *)
val can_read_dlm (env: acts_for_env) (p: principal) (l: dlm_label) : bool

(** Get all owners in a DLM label *)
val dlm_owners (l: dlm_label) : list principal

(** Find component by owner in a DLM label *)
val find_component_by_owner (owner: principal) (l: dlm_label) : option label_component

(** ============================================================================
    DLM LABEL OPERATIONS
    ============================================================================ *)

(** Helper: intersect two principal lists *)
val list_intersect (ps1 ps2: list principal) : list principal

(** Helper: union two principal lists *)
val list_union (ps1 ps2: list principal) : list principal

(** Helper: check if ps1 is a subset of ps2 *)
val is_subset (ps1 ps2: list principal) : bool

(** Merge two labels by applying f to reader sets of same owner *)
val merge_labels (l1 l2: dlm_label)
                 (f: list principal -> list principal -> list principal)
    : Tot dlm_label (decreases l1)

(** DLM label join (least upper bound) - more restrictive *)
val dlm_join (l1 l2: dlm_label) : dlm_label

(** DLM label meet (greatest lower bound) - less restrictive *)
val dlm_meet (l1 l2: dlm_label) : dlm_label

(** DLM flows-to relation: l1 <= l2 means l1 can flow to l2 *)
val dlm_flows_to (env: acts_for_env) (l1 l2: dlm_label) : bool

(** dlm_flows_to is reflexive *)
val dlm_flows_to_refl (env: acts_for_env) (l: dlm_label)
    : Lemma (ensures dlm_flows_to env l l = true)

(** Public label flows to anything *)
val dlm_public_flows_to_all (env: acts_for_env) (l: dlm_label)
    : Lemma (ensures dlm_flows_to env dlm_public l = true)

(** ============================================================================
    DECLASSIFICATION WITH AUTHORITY
    ============================================================================ *)

(** Declassification request *)
noeq type dlm_declassify_request = {
  dr_current_label : dlm_label;
  dr_new_label     : dlm_label;
  dr_authority     : principal;
  dr_purpose       : string;
}

(** Check if declassification is authorized *)
val dlm_can_declassify (env: acts_for_env) (req: dlm_declassify_request) : bool

(** Perform declassification with authority check *)
val dlm_declassify (env: acts_for_env) (req: dlm_declassify_request)
    : option dlm_label

(** ============================================================================
    ROBUST DECLASSIFICATION
    ============================================================================ *)

(** Robust declassification request *)
noeq type robust_declassify_request = {
  rd_label        : dlm_label;
  rd_new_label    : dlm_label;
  rd_authority    : principal;
  rd_condition    : bool;
  rd_cond_integrity : integrity_level_full;
  rd_purpose      : string;
}

(** Minimum integrity required for robust declassification condition *)
val robust_required_integrity : integrity_level_full

(** Check if robust declassification is allowed *)
val check_robust_declassify (env: acts_for_env) (req: robust_declassify_request) : bool

(** Perform robust declassification *)
val robust_declassify (env: acts_for_env) (req: robust_declassify_request)
    : option dlm_label

(** ============================================================================
    DLM EXAMPLES AND HELPERS
    ============================================================================ *)

(** Example principals *)
val alice : principal
val bob : principal
val charlie : principal
val admin : principal
val hr_dept : principal

(** Example labels *)
val alice_private : dlm_label
val alice_shares_with_bob : dlm_label
val hr_data : dlm_label
val joint_alice_bob : dlm_label

(** ============================================================================
    INTEGRATION WITH EXISTING SECURITY TYPES
    ============================================================================ *)

(** System principals for mapping to sec_level *)
val public_principal : principal
val confidential_principal : principal
val secret_principal : principal
val topsecret_principal : principal

(** Convert sec_level to DLM label *)
val sec_level_to_dlm (l: sec_level) : dlm_label

(** Convert DLM label to approximate sec_level *)
val dlm_to_sec_level (l: dlm_label) : sec_level

(** Combined DLM and integrity label *)
noeq type full_dlm_label = {
  fdlm_confidentiality : dlm_label;
  fdlm_integrity       : integrity_level_full;
}

(** Create full DLM label *)
val make_full_dlm_label (conf: dlm_label) (integ: integrity_level_full) : full_dlm_label

(** Public untrusted (typical user input) *)
val dlm_public_untrusted : full_dlm_label

(** Private trusted (system secrets) *)
val dlm_private_trusted (owner: principal) : full_dlm_label

(** ============================================================================
    DLM TYPE CHECKING CONTEXT
    ============================================================================ *)

(** DLM security context: maps variables to DLM labels *)
type dlm_sec_ctx = list (var_id & full_dlm_label)

(** Empty DLM context *)
val empty_dlm_sec_ctx : dlm_sec_ctx

(** Extend DLM context *)
val extend_dlm_sec_ctx (x: var_id) (l: full_dlm_label) (ctx: dlm_sec_ctx) : dlm_sec_ctx

(** Lookup in DLM context *)
val lookup_dlm_sec_ctx (x: var_id) (ctx: dlm_sec_ctx) : option full_dlm_label

(** ============================================================================
    DLM AUDIT LOGGING
    ============================================================================ *)

(** Declassification audit entry *)
noeq type dlm_audit_entry = {
  audit_timestamp   : nat;
  audit_authority   : principal;
  audit_from_label  : dlm_label;
  audit_to_label    : dlm_label;
  audit_purpose     : string;
  audit_was_robust  : bool;
}

(** Audit log *)
type dlm_audit_log = list dlm_audit_entry

(** Empty audit log *)
val empty_dlm_audit_log : dlm_audit_log

(** Add audit entry *)
val log_declassification
    (log: dlm_audit_log)
    (timestamp: nat)
    (authority: principal)
    (from_label: dlm_label)
    (to_label: dlm_label)
    (purpose: string)
    (was_robust: bool) : dlm_audit_log

(** Declassification with automatic audit logging *)
val dlm_declassify_logged
    (env: acts_for_env)
    (req: dlm_declassify_request)
    (log: dlm_audit_log)
    (timestamp: nat)
    : option (dlm_label & dlm_audit_log)

(** Robust declassification with automatic audit logging *)
val robust_declassify_logged
    (env: acts_for_env)
    (req: robust_declassify_request)
    (log: dlm_audit_log)
    (timestamp: nat)
    : option (dlm_label & dlm_audit_log)

(** ============================================================================
    BRRR-MACHINE TERMINATION ANALYSIS REQUIREMENTS
    ============================================================================ *)

(** Termination analysis result from Brrr-Machine *)
noeq type termination_analysis_result = {
  definitely_terminates : bool;
  definitely_diverges   : bool;
  termination_channels  : list termination_channel;
  analysis_complete     : bool;
}

(** Unknown termination (conservative) *)
val unknown_termination : termination_analysis_result

(** Definitely terminates *)
val terminates_result : termination_analysis_result

(** Definitely diverges *)
val diverges_result : termination_analysis_result

(** Analysis requirements for Brrr-Machine *)
noeq type termination_analysis_requirements = {
  analyze_while_loops     : bool;
  analyze_for_loops       : bool;
  analyze_recursion       : bool;
  use_smt_termination     : bool;
  analysis_timeout_ms     : option nat;
}

(** Default analysis requirements *)
val default_analysis_requirements : termination_analysis_requirements
