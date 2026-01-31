(**
 * BrrrLang.Core.Effects - Implementation
 *
 * Row-Polymorphic Algebraic Effect System for the Brrr-Lang Code IR.
 * Based on brrr_lang_spec_v0.4.tex Part II (Type System), Section 4 (Effects).
 *
 * This file provides implementations for the signatures in BrrrEffects.fsti.
 * See BrrrEffects.fsti for full theoretical documentation on:
 *   - Row polymorphism (Leijen 2014 - Koka)
 *   - Algebraic effects (Plotkin & Power 2003)
 *   - Effect handlers (Plotkin & Pretnar 2009)
 *
 * EFFECT ALGEBRA IMPLEMENTATION:
 *
 *   Effect rows form a bounded join-semilattice. This file proves the
 *   algebraic laws required for soundness:
 *
 *   SEMILATTICE LAWS:
 *     - Associativity:  (r1 + r2) + r3 ~ r1 + (r2 + r3)  [row_join_assoc]
 *     - Commutativity:  r1 + r2 ~ r2 + r1                [row_join_comm]
 *     - Idempotence:    r + r = r                        [row_join_idem]
 *     - Identity:       pure + r = r                     [row_join_pure]
 *
 *   SUBSET LAWS (partial order):
 *     - Reflexivity:    r <= r                           [effect_subset_refl]
 *     - Transitivity:   r1 <= r2 /\ r2 <= r3 => r1 <= r3 [effect_subset_trans]
 *     - Antisymmetry:   r1 <= r2 /\ r2 <= r1 => r1 ~ r2  [effect_subset_antisym]
 *
 *   LATTICE STRUCTURE:
 *     - Bottom:         pure <= r for all r              [effect_empty_is_bottom]
 *     - LUB:            row_join is least upper bound    [effect_join_lub]
 *
 *   Note: Structural equality (==) differs from semantic equality (~).
 *   row_join may produce different structures for equivalent effect sets.
 *   Use row_equiv for semantic comparisons.
 *
 * ROW UNIFICATION:
 *
 *   During effect inference, row variables may need to unify:
 *     - row_join (RowVar v1) (RowVar v2) when v1 <> v2
 *       produces RowVarUnify v1 v2 (or a constraint)
 *     - row_join_constrained tracks all constraints explicitly
 *
 *   See SPECIFICATION_ERRATA.md for known edge cases in row unification.
 *
 * GRADED MONAD LAWS:
 *
 *   The graded monad structure requires effect algebra properties:
 *     - comp_left_identity:  return x >>= f = f x
 *     - comp_right_identity: m >>= return = m
 *     - Associativity depends on row_join_assoc
 *
 * PROOF PATTERNS (following HACL*/EverParse):
 *
 *   - SMT patterns [SMTPat ...] for automatic lemma application
 *   - calc blocks for equational reasoning
 *   - #push-options/#pop-options for local Z3 configuration
 *   - FStar.Classical.forall_intro for semantic equality proofs
 *)
module BrrrEffects

(* Z3 configuration for effect algebra proofs *)
#set-options "--z3rlimit 100 --fuel 2 --ifuel 2"

open BrrrPrimitives
open BrrrUtils  (* Shared utilities - zip_lists, option combinators, etc. *)

(** ============================================================================
    IMPLEMENTATIONS FOR VAL DECLARATIONS FROM EFFECTS.FSTI

    Types (abstract_loc, effect_type, effect_op, effect_row, etc.) are
    DEFINED in BrrrEffects.fsti and should NOT be redefined here.
    ============================================================================ *)

(* Effect type equality - recursive, implementation required *)
let rec effect_type_eq (t1 t2: effect_type) : bool =
  match t1, t2 with
  | ETUnit, ETUnit -> true
  | ETBool, ETBool -> true
  | ETInt, ETInt -> true
  | ETString, ETString -> true
  | ETChan t1', ETChan t2' -> effect_type_eq t1' t2'
  | ETRef t1', ETRef t2' -> effect_type_eq t1' t2'
  | ETFn a1 r1, ETFn a2 r2 -> effect_type_eq a1 a2 && effect_type_eq r1 r2
  | ETVar v1, ETVar v2 -> v1 = v2
  | _, _ -> false

(* et_unit is defined in BrrrEffects.fsti *)

(* String list equality - per .fsti order: before effect_op_eq *)
let rec string_list_eq (l1 l2: list string) : bool =
  match l1, l2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 -> h1 = h2 && string_list_eq t1 t2
  | _, _ -> false

(* effect_op_eq, effect_type_id, effect_row, row_constraint, row_join_result, pure
   are all defined in BrrrEffects.fsti *)

(** ============================================================================
    EFFECT ROW OPERATIONS - Implementations
    ============================================================================ *)

(* Check if effect is in row *)
let rec has_effect (e: effect_op) (row: effect_row) : bool =
  match row with
  | RowEmpty -> false
  | RowExt e' rest -> effect_op_eq e e' || has_effect e rest
  | RowVar _ -> false  (* Conservative: unknown *)
  | RowVarUnify _ _ -> false  (* Conservative: unknown for unified variables *)

(* Add effect to row (if not present) *)
let add_effect (e: effect_op) (row: effect_row) : effect_row =
  if has_effect e row then row
  else RowExt e row

(* Remove effect from row *)
let rec remove_effect (e: effect_op) (row: effect_row) : effect_row =
  match row with
  | RowEmpty -> RowEmpty
  | RowExt e' rest ->
      if effect_op_eq e e' then remove_effect e rest
      else RowExt e' (remove_effect e rest)
  | RowVar v -> RowVar v  (* Can't remove from variable *)
  | RowVarUnify v1 v2 -> RowVarUnify v1 v2  (* Can't remove from unified variables *)

(** Row join (union of effects) - the JOIN operation of the effect semilattice.

    This is the core operation for combining effects in sequential composition.
    Following Leijen [Leijen14], row_join implements the row union operation:

      <e1, e2, ..., en> + <f1, f2, ..., fm> = <e1, e2, ..., en, f1, f2, ..., fm>
                                              (with duplicates removed)

    ROW VARIABLE HANDLING (for effect polymorphism):
      - RowVar v represents an unknown set of effects
      - RowVar v + concrete effects: extend v with those effects
      - RowVar v1 + RowVar v2 (v1 <> v2): produces RowVarUnify v1 v2
      - RowVar v + RowVar v: identity, returns RowVar v

    RowVarUnify tracks that two row variables must be equal. This constraint
    is resolved during effect inference/unification.

    ALGEBRAIC PROPERTIES (proven below):
      - Associativity (semantic): row_join_assoc
      - Commutativity (semantic): row_join_comm
      - Idempotence: row_join_idem
      - Identity: row_join_pure (pure is left identity)

    For explicit constraint tracking, use row_join_constrained instead.

    Reference: Definition 3.9 in brrr_lang_spec_v0.4.tex (Effect Row).
*)
let rec row_join (r1 r2: effect_row) : effect_row =
  match r1 with
  | RowEmpty -> r2
  | RowExt e rest -> add_effect e (row_join rest r2)
  | RowVar v ->
      (* Row variable unification - return the concrete effects plus variable *)
      (match r2 with
      | RowEmpty -> RowVar v
      | RowExt e rest ->
          (* Extend the row variable with concrete effects from r2 *)
          RowExt e (row_join (RowVar v) rest)
      | RowVar v' ->
          (* Two row variables: if same, return one; if different, create unification *)
          if v = v' then RowVar v else RowVarUnify v v'
      | RowVarUnify v1 v2 ->
          (* Joining with already-unified variable: chain the unification *)
          if v = v1 || v = v2 then RowVarUnify v1 v2
          else RowVarUnify v v1)  (* Would need full constraint solving for v = v1 = v2 *)
  | RowVarUnify v1 v2 ->
      (* Join unified variable with another row *)
      (match r2 with
      | RowEmpty -> RowVarUnify v1 v2
      | RowExt e rest -> RowExt e (row_join (RowVarUnify v1 v2) rest)
      | RowVar v' ->
          if v' = v1 || v' = v2 then RowVarUnify v1 v2
          else RowVarUnify v1 v2  (* Would need constraint v' = v1 = v2 *)
      | RowVarUnify v1' v2' ->
          (* Two unified vars: if any overlap, merge; otherwise keep first *)
          if v1 = v1' || v1 = v2' || v2 = v1' || v2 = v2'
          then RowVarUnify v1 v2
          else RowVarUnify v1 v2)  (* Would need v1=v2=v1'=v2' *)

(* Row join with explicit constraint collection.
   Use this when you need to track all unification constraints. *)
let rec row_join_constrained (r1 r2: effect_row) : row_join_result =
  match r1 with
  | RowEmpty -> { rjr_row = r2; rjr_constraints = [] }
  | RowExt e rest ->
      let inner = row_join_constrained rest r2 in
      { rjr_row = add_effect e inner.rjr_row; rjr_constraints = inner.rjr_constraints }
  | RowVar v ->
      (match r2 with
      | RowEmpty -> { rjr_row = RowVar v; rjr_constraints = [] }
      | RowExt e rest ->
          let inner = row_join_constrained (RowVar v) rest in
          { rjr_row = RowExt e inner.rjr_row; rjr_constraints = inner.rjr_constraints }
      | RowVar v' ->
          if v = v' then { rjr_row = RowVar v; rjr_constraints = [] }
          else { rjr_row = RowVar v;
                 rjr_constraints = [{ rc_var1 = v; rc_var2 = v' }] }
      | RowVarUnify v1 v2 ->
          if v = v1 || v = v2 then { rjr_row = RowVarUnify v1 v2; rjr_constraints = [] }
          else { rjr_row = RowVar v;
                 rjr_constraints = [{ rc_var1 = v; rc_var2 = v1 }] })
  | RowVarUnify v1 v2 ->
      (match r2 with
      | RowEmpty -> { rjr_row = RowVarUnify v1 v2; rjr_constraints = [] }
      | RowExt e rest ->
          let inner = row_join_constrained (RowVarUnify v1 v2) rest in
          { rjr_row = RowExt e inner.rjr_row; rjr_constraints = inner.rjr_constraints }
      | RowVar v' ->
          if v' = v1 || v' = v2 then { rjr_row = RowVarUnify v1 v2; rjr_constraints = [] }
          else { rjr_row = RowVarUnify v1 v2;
                 rjr_constraints = [{ rc_var1 = v'; rc_var2 = v1 }] }
      | RowVarUnify v1' v2' ->
          if v1 = v1' || v1 = v2' || v2 = v1' || v2 = v2'
          then { rjr_row = RowVarUnify v1 v2; rjr_constraints = [] }
          else { rjr_row = RowVarUnify v1 v2;
                 rjr_constraints = [{ rc_var1 = v1; rc_var2 = v1' }] })

(* Row subset check *)
let rec row_subset (r1 r2: effect_row) : bool =
  match r1 with
  | RowEmpty -> true
  | RowExt e rest -> has_effect e r2 && row_subset rest r2
  | RowVar _ -> false  (* Can't know for variables *)
  | RowVarUnify _ _ -> false  (* Can't know for unified variables *)

(* Row equality check: structural equality for effect rows
 * Handles row variables and concrete effect lists
 * Per .fsti order: must come before reflexivity lemmas *)
let rec row_eq (r1 r2: effect_row) : bool =
  match r1, r2 with
  | RowEmpty, RowEmpty -> true
  | RowVar v1, RowVar v2 -> v1 = v2
  | RowVarUnify v1a v1b, RowVarUnify v2a v2b -> v1a = v2a && v1b = v2b
  | RowExt e1 rest1, RowExt e2 rest2 ->
      effect_op_eq e1 e2 && row_eq rest1 rest2
  | _, _ -> false

(* Check if effect_row is free of RowVar at all levels
 * Per .fsti order: must come before reflexivity lemmas *)
let rec no_row_var (r: effect_row) : bool =
  match r with
  | RowEmpty -> true
  | RowExt _ rest -> no_row_var rest
  | RowVar _ -> false
  | RowVarUnify _ _ -> false

(** Semantic equality for effect rows: same set of effects.

    Two rows are semantically equal (row_equiv) iff they contain exactly
    the same effects. This is WEAKER than structural equality (==):

      row_equiv (RowExt A (RowExt B RowEmpty)) (RowExt B (RowExt A RowEmpty))

    but NOT:

      (RowExt A (RowExt B RowEmpty)) == (RowExt B (RowExt A RowEmpty))

    Semantic equality is what matters for effect soundness - a computation
    with effects r1 can substitute for one with effects r2 when row_equiv r1 r2.

    This definition follows the extensional equality on sets:
      r1 ~ r2  iff  forall e. e in r1 <=> e in r2

    Reference: Leijen [Leijen14] uses scoped rows where order doesn't matter.
*)
let row_equiv (r1 r2: effect_row) : prop =
  forall (e:effect_op). has_effect e r1 = has_effect e r2

(* abstract_loc_eq is reflexive - trivial with unfold *)
(* val abstract_loc_eq_refl declared in BrrrEffects.fsti *)
let abstract_loc_eq_refl l = ()  (* Z3 sees unfold body directly *)

(* effect_type_eq is reflexive *)
(* val effect_type_eq_refl declared in BrrrEffects.fsti *)
let rec effect_type_eq_refl t =
  match t with
  | ETUnit -> () | ETBool -> () | ETInt -> () | ETString -> ()
  | ETChan t' -> effect_type_eq_refl t'
  | ETRef t' -> effect_type_eq_refl t'
  | ETFn a r -> effect_type_eq_refl a; effect_type_eq_refl r
  | ETVar _ -> ()

(* string_list_eq is reflexive *)
(* val string_list_eq_refl declared in BrrrEffects.fsti *)
let rec string_list_eq_refl l =
  match l with
  | [] -> ()
  | _ :: t -> string_list_eq_refl t

(* effect_op_eq is reflexive - needed for row_eq_refl below *)
(* val effect_op_eq_refl declared in BrrrEffects.fsti *)
let effect_op_eq_refl e =
  match e with
  (* Memory effects *)
  | ERead loc -> abstract_loc_eq_refl loc
  | EWrite loc -> abstract_loc_eq_refl loc
  | EAlloc -> ()
  | EFree loc -> abstract_loc_eq_refl loc

  (* Control effects *)
  | EThrow _ -> () | ECatch _ -> () | EPanic -> ()
  | EAsync -> ()
  (* Parameterized yield: prove reflexivity for both type parameters *)
  | EYield y_ty r_ty -> effect_type_eq_refl y_ty; effect_type_eq_refl r_ty
  | EDiv -> ()
  | EShift -> () | EAbort -> ()

  (* I/O effects *)
  | EInput _ -> () | EOutput _ -> ()
  | EIO -> () | ENet -> () | EFS -> ()
  | EFileRead _ -> () | EFileWrite _ -> ()
  | ERandom -> () | EClock -> ()

  (* Concurrency effects *)
  | ESpawn -> () | EJoin -> ()
  | ELock _ -> () | EUnlock _ -> () | EAtomic -> ()
  | ERLock _ -> () | ERUnlock _ -> ()
  | ECondWait _ -> () | ECondSignal _ -> () | ECondBroadcast _ -> ()
  | EOnce _ -> ()
  | EWaitGroupAdd _ _ -> () | EWaitGroupDone _ -> () | EWaitGroupWait _ -> ()

  (* Finalizer effects *)
  | ESetFinalizer -> ()

  (* Session effects *)
  | ESend _ t -> effect_type_eq_refl t
  | ERecv _ t -> effect_type_eq_refl t
  | ESelect _ _ -> ()
  | EBranch _ ls -> string_list_eq_refl ls
  | EChanCreate _ t _ -> effect_type_eq_refl t
  | EChanClose _ -> ()
  | EDelegate _ _ -> ()

  (* Resource effects *)
  | EAcquire _ -> () | ERelease _ -> () | EUse _ -> ()

  (* State effects *)
  | EState -> () | ESTRead _ -> () | ESTWrite _ -> () | ESTNew -> ()

  (* FFI effects *)
  | EUnsafe -> () | EFFI -> ()

  (* Legacy *)
  | EReadSimple -> () | EWriteSimple -> () | ELockSimple -> () | ENewCh -> ()

(* Row equality is reflexive *)
(* val row_eq_refl declared in BrrrEffects.fsti *)
let rec row_eq_refl r =
  match r with
  | RowEmpty -> ()
  | RowVar _ -> ()
  | RowVarUnify _ _ -> ()
  | RowExt e rest -> effect_op_eq_refl e; row_eq_refl rest

(** ============================================================================
    SYMMETRY LEMMAS - ordered by dependency

    Order matches .fsti declaration order:
    1. abstract_loc_eq_sym (no deps)
    2. effect_type_eq_sym (recursive, no deps)
    3. string_list_eq_sym (recursive, no deps)
    4. effect_op_eq_sym (needs above three)
    5. row_eq_sym (needs effect_op_eq_sym)
    ============================================================================ *)

(* abstract_loc_eq is symmetric - trivial with unfold *)
(* val abstract_loc_eq_sym declared in BrrrEffects.fsti *)
let abstract_loc_eq_sym l1 l2 = ()  (* Z3 sees unfold body directly *)

(* effect_type_eq is symmetric *)
(* val effect_type_eq_sym declared in BrrrEffects.fsti *)
let rec effect_type_eq_sym t1 t2 =
  match t1, t2 with
  | ETUnit, ETUnit -> () | ETBool, ETBool -> ()
  | ETInt, ETInt -> () | ETString, ETString -> ()
  | ETChan t1', ETChan t2' -> effect_type_eq_sym t1' t2'
  | ETRef t1', ETRef t2' -> effect_type_eq_sym t1' t2'
  | ETFn a1 r1, ETFn a2 r2 -> effect_type_eq_sym a1 a2; effect_type_eq_sym r1 r2
  | ETVar _, ETVar _ -> ()
  | _, _ -> ()

(* string_list_eq is symmetric *)
(* val string_list_eq_sym declared in BrrrEffects.fsti *)
let rec string_list_eq_sym l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | h1 :: t1, h2 :: t2 -> string_list_eq_sym t1 t2
  | _, _ -> ()

(* effect_op_eq is symmetric *)
(* val effect_op_eq_sym declared in BrrrEffects.fsti *)
let effect_op_eq_sym e1 e2 =
  match e1, e2 with
  (* Memory effects *)
  | ERead l1, ERead l2 -> abstract_loc_eq_sym l1 l2
  | EWrite l1, EWrite l2 -> abstract_loc_eq_sym l1 l2
  | EAlloc, EAlloc -> ()
  | EFree l1, EFree l2 -> abstract_loc_eq_sym l1 l2
  (* Control effects *)
  | EThrow _, EThrow _ -> () | ECatch _, ECatch _ -> () | EPanic, EPanic -> ()
  | EAsync, EAsync -> ()
  | EYield y1 r1, EYield y2 r2 -> effect_type_eq_sym y1 y2; effect_type_eq_sym r1 r2
  | EDiv, EDiv -> ()
  | EShift, EShift -> () | EAbort, EAbort -> ()
  (* I/O effects *)
  | EInput _, EInput _ -> () | EOutput _, EOutput _ -> ()
  | EIO, EIO -> () | ENet, ENet -> () | EFS, EFS -> ()
  | EFileRead _, EFileRead _ -> () | EFileWrite _, EFileWrite _ -> ()
  | ERandom, ERandom -> () | EClock, EClock -> ()
  (* Concurrency effects *)
  | ESpawn, ESpawn -> () | EJoin, EJoin -> ()
  | ELock _, ELock _ -> () | EUnlock _, EUnlock _ -> () | EAtomic, EAtomic -> ()
  | ERLock _, ERLock _ -> () | ERUnlock _, ERUnlock _ -> ()
  | ECondWait _, ECondWait _ -> () | ECondSignal _, ECondSignal _ -> ()
  | ECondBroadcast _, ECondBroadcast _ -> ()
  | EOnce _, EOnce _ -> ()
  | EWaitGroupAdd _ _, EWaitGroupAdd _ _ -> ()
  | EWaitGroupDone _, EWaitGroupDone _ -> ()
  | EWaitGroupWait _, EWaitGroupWait _ -> ()
  (* Finalizer effects *)
  | ESetFinalizer, ESetFinalizer -> ()
  (* Session effects *)
  | ESend c1 t1, ESend c2 t2 -> effect_type_eq_sym t1 t2
  | ERecv c1 t1, ERecv c2 t2 -> effect_type_eq_sym t1 t2
  | ESelect _ _, ESelect _ _ -> ()
  | EBranch c1 ls1, EBranch c2 ls2 -> string_list_eq_sym ls1 ls2
  | EChanCreate c1 t1 _, EChanCreate c2 t2 _ -> effect_type_eq_sym t1 t2
  | EChanClose _, EChanClose _ -> ()
  | EDelegate _ _, EDelegate _ _ -> ()
  (* Resource effects *)
  | EAcquire _, EAcquire _ -> () | ERelease _, ERelease _ -> () | EUse _, EUse _ -> ()
  (* State effects *)
  | EState, EState -> () | ESTRead _, ESTRead _ -> ()
  | ESTWrite _, ESTWrite _ -> () | ESTNew, ESTNew -> ()
  (* FFI effects *)
  | EUnsafe, EUnsafe -> () | EFFI, EFFI -> ()
  (* Legacy *)
  | EReadSimple, EReadSimple -> () | EWriteSimple, EWriteSimple -> ()
  | ELockSimple, ELockSimple -> () | ENewCh, ENewCh -> ()
  | _, _ -> ()

(* Row equality is symmetric - NOW comes after effect_op_eq_sym *)
(* val row_eq_sym declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rec row_eq_sym r1 r2 =
  match r1, r2 with
  | RowEmpty, RowEmpty -> ()
  | RowVar _, RowVar _ -> ()
  | RowVarUnify _ _, RowVarUnify _ _ -> ()
  | RowExt e1 rest1, RowExt e2 rest2 ->
      (* From precondition row_eq r1 r2 = true:
         effect_op_eq e1 e2 = true AND row_eq rest1 rest2 = true *)
      (* Need: effect_op_eq e2 e1 = true AND row_eq rest2 rest1 = true *)
      effect_op_eq_sym e1 e2;  (* Proves effect_op_eq e2 e1 = effect_op_eq e1 e2 = true *)
      row_eq_sym rest1 rest2   (* Proves row_eq rest2 rest1 = true by IH *)
  | _, _ -> ()
#pop-options

(* Helper: effect_type_eq is transitive - private lemma for row_eq_trans *)
private let rec effect_type_eq_trans (t1 t2 t3: effect_type) : Lemma
    (requires effect_type_eq t1 t2 = true /\ effect_type_eq t2 t3 = true)
    (ensures effect_type_eq t1 t3 = true) =
  match t1, t2, t3 with
  | ETUnit, ETUnit, ETUnit -> ()
  | ETBool, ETBool, ETBool -> ()
  | ETInt, ETInt, ETInt -> ()
  | ETString, ETString, ETString -> ()
  | ETChan t1', ETChan t2', ETChan t3' -> effect_type_eq_trans t1' t2' t3'
  | ETRef t1', ETRef t2', ETRef t3' -> effect_type_eq_trans t1' t2' t3'
  | ETFn a1 r1, ETFn a2 r2, ETFn a3 r3 ->
      effect_type_eq_trans a1 a2 a3; effect_type_eq_trans r1 r2 r3
  | ETVar v1, ETVar v2, ETVar v3 -> ()
  | _, _, _ -> ()

(* Helper: string_list_eq is transitive - private lemma for row_eq_trans *)
private let rec string_list_eq_trans (l1 l2 l3: list string) : Lemma
    (requires string_list_eq l1 l2 = true /\ string_list_eq l2 l3 = true)
    (ensures string_list_eq l1 l3 = true) =
  match l1, l2, l3 with
  | [], [], [] -> ()
  | h1 :: t1, h2 :: t2, h3 :: t3 -> string_list_eq_trans t1 t2 t3
  | _, _, _ -> ()

(* Helper: effect_op_eq is transitive - private lemma for row_eq_trans *)
#push-options "--z3rlimit 200 --fuel 1"
private let effect_op_eq_trans (e1 e2 e3: effect_op) : Lemma
    (requires effect_op_eq e1 e2 = true /\ effect_op_eq e2 e3 = true)
    (ensures effect_op_eq e1 e3 = true) =
  match e1, e2, e3 with
  (* Memory effects - loc params use nat/string equality which is transitive *)
  | ERead _, ERead _, ERead _ -> ()
  | EWrite _, EWrite _, EWrite _ -> ()
  | EAlloc, EAlloc, EAlloc -> ()
  | EFree _, EFree _, EFree _ -> ()
  (* Control effects *)
  | EThrow _, EThrow _, EThrow _ -> ()
  | ECatch _, ECatch _, ECatch _ -> ()
  | EPanic, EPanic, EPanic -> ()
  | EAsync, EAsync, EAsync -> ()
  | EYield y1 r1, EYield y2 r2, EYield y3 r3 ->
      effect_type_eq_trans y1 y2 y3; effect_type_eq_trans r1 r2 r3
  | EDiv, EDiv, EDiv -> ()
  | EShift, EShift, EShift -> ()
  | EAbort, EAbort, EAbort -> ()
  (* I/O effects *)
  | EInput _, EInput _, EInput _ -> ()
  | EOutput _, EOutput _, EOutput _ -> ()
  | EIO, EIO, EIO -> ()
  | ENet, ENet, ENet -> ()
  | EFS, EFS, EFS -> ()
  | EFileRead _, EFileRead _, EFileRead _ -> ()
  | EFileWrite _, EFileWrite _, EFileWrite _ -> ()
  | ERandom, ERandom, ERandom -> ()
  | EClock, EClock, EClock -> ()
  (* Concurrency effects *)
  | ESpawn, ESpawn, ESpawn -> ()
  | EJoin, EJoin, EJoin -> ()
  | ELock _, ELock _, ELock _ -> ()
  | EUnlock _, EUnlock _, EUnlock _ -> ()
  | ERLock _, ERLock _, ERLock _ -> ()
  | ERUnlock _, ERUnlock _, ERUnlock _ -> ()
  | ECondWait _, ECondWait _, ECondWait _ -> ()
  | ECondSignal _, ECondSignal _, ECondSignal _ -> ()
  | ECondBroadcast _, ECondBroadcast _, ECondBroadcast _ -> ()
  | EAtomic, EAtomic, EAtomic -> ()
  | EOnce _, EOnce _, EOnce _ -> ()
  | EWaitGroupAdd _ _, EWaitGroupAdd _ _, EWaitGroupAdd _ _ -> ()
  | EWaitGroupDone _, EWaitGroupDone _, EWaitGroupDone _ -> ()
  | EWaitGroupWait _, EWaitGroupWait _, EWaitGroupWait _ -> ()
  (* Finalizer effects *)
  | ESetFinalizer, ESetFinalizer, ESetFinalizer -> ()
  (* Session effects *)
  | ESend c1 t1, ESend c2 t2, ESend c3 t3 -> effect_type_eq_trans t1 t2 t3
  | ERecv c1 t1, ERecv c2 t2, ERecv c3 t3 -> effect_type_eq_trans t1 t2 t3
  | ESelect _ _, ESelect _ _, ESelect _ _ -> ()
  | EBranch c1 ls1, EBranch c2 ls2, EBranch c3 ls3 -> string_list_eq_trans ls1 ls2 ls3
  | EChanCreate c1 t1 _, EChanCreate c2 t2 _, EChanCreate c3 t3 _ -> effect_type_eq_trans t1 t2 t3
  | EChanClose _, EChanClose _, EChanClose _ -> ()
  | EDelegate _ _, EDelegate _ _, EDelegate _ _ -> ()
  (* Resource effects *)
  | EAcquire _, EAcquire _, EAcquire _ -> ()
  | ERelease _, ERelease _, ERelease _ -> ()
  | EUse _, EUse _, EUse _ -> ()
  (* State effects *)
  | EState, EState, EState -> ()
  | ESTRead _, ESTRead _, ESTRead _ -> ()
  | ESTWrite _, ESTWrite _, ESTWrite _ -> ()
  | ESTNew, ESTNew, ESTNew -> ()
  (* FFI effects *)
  | EUnsafe, EUnsafe, EUnsafe -> ()
  | EFFI, EFFI, EFFI -> ()
  (* Legacy *)
  | EReadSimple, EReadSimple, EReadSimple -> ()
  | EWriteSimple, EWriteSimple, EWriteSimple -> ()
  | ELockSimple, ELockSimple, ELockSimple -> ()
  | ENewCh, ENewCh, ENewCh -> ()
  | _, _, _ -> ()
#pop-options

(* Row equality is transitive *)
(* val row_eq_trans declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rec row_eq_trans r1 r2 r3 =
  match r1, r2, r3 with
  | RowEmpty, RowEmpty, RowEmpty -> ()
  | RowVar v1, RowVar v2, RowVar v3 -> ()  (* nat equality is transitive *)
  | RowVarUnify v1a v1b, RowVarUnify v2a v2b, RowVarUnify v3a v3b -> ()
  | RowExt e1 rest1, RowExt e2 rest2, RowExt e3 rest3 ->
      effect_op_eq_trans e1 e2 e3;
      row_eq_trans rest1 rest2 rest3
  | _, _, _ -> ()
#pop-options

(** ============================================================================
    EFFECT SEMILATTICE LAWS - HELPER LEMMAS
    ============================================================================ *)

(* If r has no RowVar, neither does any suffix *)
(* val no_row_var_ext declared in BrrrEffects.fsti *)
let no_row_var_ext e rest = ()

(* has_effect is preserved when extending a row *)
(* val has_effect_ext declared in BrrrEffects.fsti *)
let has_effect_ext e e' row = ()

(* The head of a RowExt is always present *)
(* val has_effect_head declared in BrrrEffects.fsti *)
let has_effect_head e rest = effect_op_eq_refl e

(* add_effect is no-op when effect already present *)
(* val add_effect_noop declared in BrrrEffects.fsti *)
let add_effect_noop e row = ()

(* has_effect is preserved by add_effect *)
(* val has_effect_add_effect declared in BrrrEffects.fsti *)
let has_effect_add_effect e e' row =
  if has_effect e' row then ()
  else has_effect_ext e e' row

(* row_subset is preserved when extending the superset *)
(* val row_subset_weaken declared in BrrrEffects.fsti *)
let rec row_subset_weaken r1 r2 e =
  match r1 with
  | RowEmpty -> ()
  | RowExt e' rest ->
      (* From precondition: has_effect e' r2 = true AND row_subset rest r2 = true *)
      has_effect_ext e' e r2;
      row_subset_weaken rest r2 e

(* Key lemma: r is a subset of (RowExt e r) for any e *)
(* val row_subset_ext declared in BrrrEffects.fsti *)
let rec row_subset_ext r e =
  match r with
  | RowEmpty -> ()
  | RowExt e' rest' ->
      (* Prove has_effect e' (RowExt e (RowExt e' rest')) = true *)
      has_effect_head e' rest';
      has_effect_ext e' e (RowExt e' rest');
      (* Prove row_subset rest' (RowExt e (RowExt e' rest')) = true *)
      (* By IH: row_subset rest' (RowExt e' rest') = true *)
      row_subset_ext rest' e';
      (* By weaken: row_subset rest' (RowExt e (RowExt e' rest')) = true *)
      row_subset_weaken rest' (RowExt e' rest') e

(* row_subset is reflexive for concrete rows *)
(* val row_subset_refl declared in BrrrEffects.fsti *)
let row_subset_refl r =
  match r with
  | RowEmpty -> ()
  | RowExt e rest ->
      has_effect_head e rest;
      row_subset_ext rest e  (* row_subset rest (RowExt e rest) = true *)

(* Key lemma: row_eq implies row_subset for concrete rows.
   This bridges type_eq (using row_eq) with extended_subtype (using row_subset).
   Note: row_subset (RowVar _) _ = false always, so we need no_row_var precondition. *)
(* val row_eq_implies_subset declared in BrrrEffects.fsti *)
let rec row_eq_implies_subset r1 r2 =
  match r1, r2 with
  | RowEmpty, RowEmpty -> ()
  | RowExt e1 rest1, RowExt e2 rest2 ->
      (* row_eq implies effect_op_eq e1 e2 = true *)
      (* has_effect e1 (RowExt e2 rest2) = effect_op_eq e1 e2 || ... = true *)
      (* For row_subset rest1 r2, recurse on inner rows *)
      row_eq_implies_subset rest1 rest2;
      (* Now: row_subset rest1 rest2 = true, need row_subset rest1 (RowExt e2 rest2) *)
      row_subset_weaken rest1 rest2 e2
  | _, _ -> ()  (* RowVar case: precondition no_row_var rules this out *)

(* Private helper: effect_op_eq e1 e = effect_op_eq e2 e when effect_op_eq e1 e2 = true
   Uses symmetry and transitivity of effect_op_eq *)
#push-options "--z3rlimit 200 --fuel 1"
private let effect_op_eq_cong_element (e1 e2 e: effect_op) : Lemma
    (requires effect_op_eq e1 e2 = true)
    (ensures effect_op_eq e1 e = effect_op_eq e2 e) =
  (* Case: effect_op_eq e1 e = true
     By sym: effect_op_eq e e1 = true
     By trans with e1 e2: effect_op_eq e e2 = true
     By sym: effect_op_eq e2 e = true *)
  if effect_op_eq e1 e then begin
    effect_op_eq_sym e1 e;  (* effect_op_eq e e1 = true *)
    effect_op_eq_trans e e1 e2;  (* effect_op_eq e e2 = true *)
    effect_op_eq_sym e e2  (* effect_op_eq e2 e = true *)
  end
  (* Case: effect_op_eq e1 e = false
     Suppose effect_op_eq e2 e = true
     By sym: effect_op_eq e e2 = true
     By trans with sym(e1 e2): would need effect_op_eq e e1 = true
     By sym: effect_op_eq e1 e = true - contradiction!
     So effect_op_eq e2 e = false *)
  else if effect_op_eq e2 e then begin
    effect_op_eq_sym e1 e2;  (* effect_op_eq e2 e1 = true *)
    effect_op_eq_sym e2 e;   (* effect_op_eq e e2 = true *)
    effect_op_eq_trans e e2 e1;  (* effect_op_eq e e1 = true *)
    effect_op_eq_sym e e1   (* effect_op_eq e1 e = true - contradicts our assumption *)
    (* This branch should be unreachable, but F* needs to see the proof *)
  end
  else ()  (* Both false - trivially equal *)
#pop-options

(* Private helper: effect_op_eq implies has_effect equality (inline version)
   Needed for row_eq_subset_trans since has_effect_op_eq_cong is declared later in .fsti *)
#push-options "--z3rlimit 200 --fuel 2"
private let rec has_effect_op_eq_cong_inline (e1 e2: effect_op) (r: effect_row) : Lemma
    (requires effect_op_eq e1 e2 = true)
    (ensures has_effect e1 r = has_effect e2 r) =
  match r with
  | RowEmpty -> ()
  | RowVar _ -> ()
  | RowVarUnify _ _ -> ()
  | RowExt e rest ->
      (* has_effect e1 (RowExt e rest) = effect_op_eq e1 e || has_effect e1 rest
         has_effect e2 (RowExt e rest) = effect_op_eq e2 e || has_effect e2 rest *)
      effect_op_eq_cong_element e1 e2 e;  (* effect_op_eq e1 e = effect_op_eq e2 e *)
      has_effect_op_eq_cong_inline e1 e2 rest  (* IH: has_effect e1 rest = has_effect e2 rest *)
      (* Since both parts are equal, the || results are equal *)
#pop-options

(* Key lemma: row_eq on left composes with row_subset on right.
   If r1 and r2 are equal (row_eq), and r2 is subset of r3,
   then r1 is also subset of r3. Used for function effect transitivity. *)
(* val row_eq_subset_trans declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1"
let rec row_eq_subset_trans r1 r2 r3 =
  match r1, r2 with
  | RowEmpty, RowEmpty -> ()
  | RowExt e1 rest1, RowExt e2 rest2 ->
      (* row_eq r1 r2 = true means effect_op_eq e1 e2 = true, row_eq rest1 rest2 = true
         row_subset r2 r3 = true means has_effect e2 r3 = true, row_subset rest2 r3 = true
         Need: has_effect e1 r3 = true AND row_subset rest1 r3 = true *)
      has_effect_op_eq_cong_inline e1 e2 r3;  (* has_effect e1 r3 = has_effect e2 r3 = true *)
      row_eq_subset_trans rest1 rest2 r3      (* row_subset rest1 r3 = true by IH *)
  | _, _ -> ()
#pop-options

(* Helper: row_eq preserves no_row_var property.
   If r1 and r2 are structurally equal, they have the same RowVar locations. *)
(* val row_eq_preserves_no_row_var declared in BrrrEffects.fsti *)
let rec row_eq_preserves_no_row_var r1 r2 =
  match r1, r2 with
  | RowEmpty, RowEmpty -> ()
  | RowVar _, RowVar _ -> ()
  | RowVarUnify _ _, RowVarUnify _ _ -> ()
  | RowExt _ rest1, RowExt _ rest2 -> row_eq_preserves_no_row_var rest1 rest2
  | _, _ -> ()

(* Helper: row_subset implies no_row_var on the left.
   row_subset r1 _ = false when r1 has RowVar, so if row_subset r1 r2 = true,
   then r1 has no RowVar. *)
(* val row_subset_implies_no_row_var_left declared in BrrrEffects.fsti *)
let rec row_subset_implies_no_row_var_left r1 r2 =
  match r1 with
  | RowEmpty -> ()
  | RowExt _ rest -> row_subset_implies_no_row_var_left rest r2
  | RowVar _ -> ()  (* Contradiction: row_subset (RowVar _) _ = false *)
  | RowVarUnify _ _ -> ()  (* Contradiction: row_subset (RowVarUnify _ _) _ = false *)

(* Key lemma: row_eq preserves has_effect.
   If r2 and r3 are structurally equal (row_eq), and an effect is in r2,
   then it's also in r3. *)
(* val row_eq_has_effect declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1"
let rec row_eq_has_effect e r2 r3 =
  match r2, r3 with
  | RowEmpty, RowEmpty -> ()  (* Contradiction: has_effect e RowEmpty = false *)
  | RowVar _, RowVar _ -> ()  (* Contradiction: has_effect e (RowVar _) = false *)
  | RowVarUnify _ _, RowVarUnify _ _ -> ()  (* Contradiction: has_effect e (RowVarUnify _ _) = false *)
  | RowExt e2 rest2, RowExt e3 rest3 ->
      (* row_eq implies effect_op_eq e2 e3 = true
         has_effect e r2 = effect_op_eq e e2 || has_effect e rest2 = true *)
      if effect_op_eq e e2 then begin
        (* Case: effect_op_eq e e2 = true
           Need: has_effect e (RowExt e3 rest3) = effect_op_eq e e3 || ... = true
           By transitivity: effect_op_eq e e2 = true, effect_op_eq e2 e3 = true
           => effect_op_eq e e3 = true *)
        effect_op_eq_trans e e2 e3
      end
      else
        (* Case: effect_op_eq e e2 = false, so has_effect e rest2 = true
           By IH: has_effect e rest3 = true *)
        row_eq_has_effect e rest2 rest3
  | _, _ -> ()
#pop-options

(* Key lemma: row_subset on left composes with row_eq on right.
   If r1 is subset of r2, and r2 equals r3, then r1 is subset of r3.
   Proof: all effects in r1 are in r2 (from row_subset), and all effects
   in r2 are in r3 (from row_eq), so all effects in r1 are in r3. *)
(* val row_subset_eq_trans declared in BrrrEffects.fsti *)
let rec row_subset_eq_trans r1 r2 r3 =
  match r1 with
  | RowEmpty -> ()
  | RowExt e rest ->
      (* From row_subset r1 r2: has_effect e r2 = true AND row_subset rest r2 = true *)
      (* Use row_eq_has_effect to show has_effect e r3 = true *)
      row_eq_has_effect e r2 r3;
      (* Recurse for row_subset rest r3 *)
      row_subset_eq_trans rest r2 r3
  | RowVar _ -> ()  (* Contradiction: row_subset (RowVar _) _ = false *)
  | RowVarUnify _ _ -> ()  (* Contradiction: row_subset (RowVarUnify _ _) _ = false *)

(* Helper: if has_effect e r2 and row_subset r2 r3, then has_effect e r3.
   Since row_subset r2 r3 means all effects in r2 are in r3. *)
(* val has_effect_subset declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1"
let rec has_effect_subset e r2 r3 =
  match r2 with
  | RowEmpty -> ()  (* Contradiction: has_effect e RowEmpty = false *)
  | RowExt e2 rest2 ->
      (* row_subset (RowExt e2 rest2) r3 = has_effect e2 r3 && row_subset rest2 r3
         has_effect e r2 = effect_op_eq e e2 || has_effect e rest2 = true *)
      if effect_op_eq e e2 then begin
        (* Case: effect_op_eq e e2 = true
           From row_subset: has_effect e2 r3 = true
           By congruence: has_effect e r3 = has_effect e2 r3 = true *)
        has_effect_op_eq_cong_inline e e2 r3
      end
      else
        (* Case: effect_op_eq e e2 = false, so has_effect e rest2 = true
           Also row_subset rest2 r3 = true from row_subset premise
           By IH: has_effect e r3 = true *)
        has_effect_subset e rest2 r3
  | RowVar _ -> ()  (* Contradiction: row_subset (RowVar _) _ = false *)
  | RowVarUnify _ _ -> ()  (* Contradiction: row_subset (RowVarUnify _ _) _ = false *)
#pop-options

(* Key lemma: row_subset is transitive for concrete rows.
   If r1 is subset of r2, and r2 is subset of r3, then r1 is subset of r3.
   Note: row_subset r _ = false when r has RowVar, so the preconditions
   imply that r1 and r2 have no RowVar. *)
(* val row_subset_trans declared in BrrrEffects.fsti *)
let rec row_subset_trans r1 r2 r3 =
  match r1 with
  | RowEmpty -> ()
  | RowExt e rest ->
      (* From row_subset r1 r2: has_effect e r2 = true AND row_subset rest r2 = true *)
      (* Use has_effect_subset to show has_effect e r3 = true *)
      has_effect_subset e r2 r3;
      (* Recurse on rest *)
      row_subset_trans rest r2 r3
  | RowVar _ -> ()  (* Contradiction: row_subset (RowVar _) _ = false *)
  | RowVarUnify _ _ -> ()  (* Contradiction: row_subset (RowVarUnify _ _) _ = false *)

(* Helper: if effect_op_eq e1 e2, then has_effect e1 r = has_effect e2 r for any r.
   This is because effect_op_eq is a partial equality: if e1 and e2 are equal
   as effect operations, they are found in the same rows. *)
(* val has_effect_op_eq_cong declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 2"
let rec has_effect_op_eq_cong e1 e2 r =
  match r with
  | RowEmpty -> ()
  | RowVar _ -> ()
  | RowVarUnify _ _ -> ()
  | RowExt e rest ->
      (* has_effect e1 (RowExt e rest) = effect_op_eq e1 e || has_effect e1 rest
         has_effect e2 (RowExt e rest) = effect_op_eq e2 e || has_effect e2 rest
         Need to show both parts are equal *)
      effect_op_eq_cong_element e1 e2 e;  (* effect_op_eq e1 e = effect_op_eq e2 e *)
      has_effect_op_eq_cong e1 e2 rest    (* IH: has_effect e1 rest = has_effect e2 rest *)
#pop-options

(* Key lemma: row_subset respects row_eq on the left (congruence).
   If row_eq r1 r2, then row_subset r1 r = row_subset r2 r.
   This follows from row_eq being structural equality: r1 and r2 have
   exactly the same effects in the same structure. *)
(* val row_subset_cong_left declared in BrrrEffects.fsti *)
let rec row_subset_cong_left r1 r2 r =
  row_eq_preserves_no_row_var r1 r2;
  match r1, r2 with
  | RowEmpty, RowEmpty -> ()  (* Both row_subset RowEmpty r = true *)
  | RowVar _, RowVar _ -> ()  (* Both row_subset (RowVar _) r = false *)
  | RowVarUnify _ _, RowVarUnify _ _ -> ()  (* Both row_subset (RowVarUnify _ _) r = false *)
  | RowExt e1 rest1, RowExt e2 rest2 ->
      (* row_eq gives: effect_op_eq e1 e2 = true, row_eq rest1 rest2 = true *)
      (* row_subset (RowExt e1 rest1) r = has_effect e1 r && row_subset rest1 r *)
      (* row_subset (RowExt e2 rest2) r = has_effect e2 r && row_subset rest2 r *)
      (* Since effect_op_eq e1 e2 = true, has_effect e1 r = has_effect e2 r *)
      has_effect_op_eq_cong e1 e2 r;
      (* By IH: row_subset rest1 r = row_subset rest2 r *)
      row_subset_cong_left rest1 rest2 r
  | _, _ -> ()  (* Impossible: row_eq requires same structure *)

(* Key lemma: row_join preserves effects from second argument *)
(* val has_effect_row_join_r declared in BrrrEffects.fsti *)
let rec has_effect_row_join_r e r1 r2 =
  match r1 with
  | RowEmpty -> ()
  | RowExt e' rest ->
      has_effect_row_join_r e rest r2;
      has_effect_add_effect e e' (row_join rest r2)

(* Helper: add_effect e always ensures e is present *)
(* val has_effect_add_effect_same declared in BrrrEffects.fsti *)
let has_effect_add_effect_same e row =
  if has_effect e row then ()
  else effect_op_eq_refl e

(* Key lemma: row_join preserves effects from first argument *)
(* val has_effect_row_join_l declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 1"
let rec has_effect_row_join_l e r1 r2 =
  match r1 with
  | RowEmpty -> ()  (* Contradiction: has_effect e RowEmpty = false *)
  | RowExt e' rest ->
      (* row_join (RowExt e' rest) r2 = add_effect e' (row_join rest r2) *)
      if effect_op_eq e e' then begin
        (* e = e', so we need has_effect e (add_effect e' (row_join rest r2)) = true
           First: has_effect e' (add_effect e' (row_join rest r2)) = true *)
        has_effect_add_effect_same e' (row_join rest r2);
        (* Now use congruence: effect_op_eq e e' = true implies
           has_effect e X = has_effect e' X for any X *)
        has_effect_op_eq_cong e e' (add_effect e' (row_join rest r2))
      end else begin
        (* e is in rest (since has_effect e r1 = true and e <> e') *)
        has_effect_row_join_l e rest r2;  (* IH: has_effect e (row_join rest r2) = true *)
        has_effect_add_effect e e' (row_join rest r2)  (* has_effect preserved by add_effect *)
      end
#pop-options

(* Lemma: row_join doesn't introduce new effects - if e is not in r1 or r2, it's not in row_join *)
(* val row_join_no_new_effects declared in BrrrEffects.fsti *)
let rec row_join_no_new_effects e r1 r2 =
  match r1 with
  | RowEmpty -> ()  (* row_join RowEmpty r2 = r2, and has_effect e r2 = false *)
  | RowExt e' rest ->
      (* row_join (RowExt e' rest) r2 = add_effect e' (row_join rest r2) *)
      (* Since has_effect e r1 = false and r1 = RowExt e' rest:
         has_effect e (RowExt e' rest) = effect_op_eq e e' || has_effect e rest = false
         So: effect_op_eq e e' = false AND has_effect e rest = false *)
      row_join_no_new_effects e rest r2;  (* IH: has_effect e (row_join rest r2) = false *)
      (* Now: add_effect e' (row_join rest r2) *)
      (* Since effect_op_eq e e', and has_effect e (row_join rest r2) = false:
         has_effect e (add_effect e' (row_join rest r2)) = false *)
      ()

(* Absorption lemma: row_join r1 r2 == r2 when r1's effects are subset of r2's *)
(* val row_join_absorb declared in BrrrEffects.fsti *)
let rec row_join_absorb r1 r2 =
  match r1 with
  | RowEmpty -> ()
  | RowExt e rest ->
      (* From row_subset: has_effect e r2 = true AND row_subset rest r2 = true *)
      row_join_absorb rest r2;
      (* Now: row_join rest r2 == r2 *)
      add_effect_noop e r2
      (* add_effect e r2 == r2 since has_effect e r2 = true *)

(** ============================================================================
    EFFECT SEMILATTICE LAWS - MAIN LEMMAS
    ============================================================================ *)

(* Join is commutative (semantic equality).
   Note: Structural equality (==) is NOT provable because row_join produces
   different structures depending on argument order. For example:
     row_join (RowExt A RowEmpty) (RowExt B RowEmpty) = RowExt A (RowExt B RowEmpty)
     row_join (RowExt B RowEmpty) (RowExt A RowEmpty) = RowExt B (RowExt A RowEmpty)
   These have the same effects but different structure. *)
(* val row_join_comm declared in BrrrEffects.fsti *)
let row_join_comm r1 r2 =
  let aux (e:effect_op) : Lemma (has_effect e (row_join r1 r2) = has_effect e (row_join r2 r1)) =
    (* If e is in r1: it's in row_join r1 r2 and row_join r2 r1 *)
    (* If e is in r2: it's in row_join r1 r2 and row_join r2 r1 *)
    (* If e is in neither: it's in neither result *)
    if has_effect e r1 then begin
      has_effect_row_join_l e r1 r2;
      has_effect_row_join_r e r2 r1
    end else if has_effect e r2 then begin
      has_effect_row_join_r e r1 r2;
      has_effect_row_join_l e r2 r1
    end else begin
      (* e is in neither r1 nor r2, so not in either join *)
      row_join_no_new_effects e r1 r2;
      row_join_no_new_effects e r2 r1
    end
  in
  FStar.Classical.forall_intro aux

(* Pure is identity for join *)
(* val row_join_pure declared in BrrrEffects.fsti *)
let row_join_pure r = ()

(* Join is idempotent (structural equality) *)
(* val row_join_idem declared in BrrrEffects.fsti *)
let row_join_idem r =
  row_subset_refl r;
  row_join_absorb r r

(** ============================================================================
    EFFECT ALGEBRA - COMPREHENSIVE PROOFS WITH SMTPAT TRIGGERS
    ============================================================================

    Following HACL* lemma patterns from:
    - /home/grigory/Downloads/hacl-star/specs/lemmas/Spec.Hash.Lemmas.fsti
    - /home/grigory/Downloads/hacl-star/lib/Lib.NatMod.fst
    - /home/grigory/Downloads/hacl-star/code/bignum/Hacl.Spec.Montgomery.Lemmas.fst

    These lemmas establish that effect rows form a bounded join-semilattice:
    - Pure (empty_effect) is the bottom element
    - effect_union is the join operation (commutative, associative, idempotent)
    - effect_subset defines the partial order

    SMTPat triggers enable automatic proof discovery by Z3.
    ============================================================================ *)

(** --------------------------------------------------------------------------
    ALIASES FOR EFFECT ALGEBRA API
    -------------------------------------------------------------------------- *)

(* Effect union: combines two effect rows (alias for row_join) *)
unfold let effect_union : effect_row -> effect_row -> effect_row = row_join

(* Empty effect: the pure effect row with no effects *)
unfold let empty_effect : effect_row = RowEmpty

(* Effect subset check: returns true if e1's effects are contained in e2 *)
unfold let effect_subset : effect_row -> effect_row -> bool = row_subset

(** --------------------------------------------------------------------------
    MONOID LAWS FOR EFFECT_UNION - WITH SMTPAT TRIGGERS

    Effect rows with effect_union form a commutative monoid:
    - Identity: effect_union e empty_effect == e
    - Associativity: effect_union (effect_union e1 e2) e3 = effect_union e1 (effect_union e2 e3)
    - Commutativity: effect_union e1 e2 ~ effect_union e2 e1 (semantic equality)
    - Idempotence: effect_union e e == e
    -------------------------------------------------------------------------- *)

(* Note: Structural equality effect_union e empty_effect == e does NOT hold
   because add_effect may deduplicate. For semantic equivalence, we use
   row_join_idem and related lemmas defined later in this file. *)

(* Left identity for effect_union: effect_union empty_effect e == e

   Proof: row_join RowEmpty r = r by the first match case.
*)
val effect_union_identity : e:effect_row ->
  Lemma (effect_union empty_effect e == e)
        [SMTPat (effect_union empty_effect e)]
let effect_union_identity e = ()

(* Idempotence: effect_union e e == e for concrete rows

   Proof: Uses row_subset_refl and row_join_absorb.
   If r is a subset of itself (trivially true), then row_join r r == r.
*)
val effect_union_idem : e:effect_row ->
  Lemma (requires no_row_var e = true)
        (ensures effect_union e e == e)
        [SMTPat (effect_union e e)]
let effect_union_idem e = row_join_idem e

(** --------------------------------------------------------------------------
    ASSOCIATIVITY PROOFS - USING CALC BLOCKS (HACL* PATTERN)
    -------------------------------------------------------------------------- *)

(* Helper: no_row_var is preserved by row_join *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec no_row_var_row_join (r1 r2: effect_row) : Lemma
    (requires no_row_var r1 = true /\ no_row_var r2 = true)
    (ensures no_row_var (row_join r1 r2) = true)
    (decreases r1) =
  match r1 with
  | RowEmpty -> ()
  | RowExt e rest ->
      no_row_var_row_join rest r2;
      (* add_effect preserves no_row_var: it either returns the row unchanged
         or wraps with RowExt, neither introduces RowVar *)
      ()
  | RowVar _ -> ()  (* Precondition violation *)
  | RowVarUnify _ _ -> ()  (* Precondition violation *)
#pop-options

(* Helper: has_effect is decidable for any effect and row *)
val has_effect_decidable : e:effect_op -> r:effect_row ->
  Lemma (has_effect e r = true \/ has_effect e r = false)
let has_effect_decidable e r = ()

(* Helper: has_effect distributes over row_join from left *)
(* val has_effect_row_join_distrib_l declared in BrrrEffects.fsti *)
let has_effect_row_join_distrib_l e r1 r2 =
  if has_effect e r1 then begin
    has_effect_row_join_l e r1 r2;
    ()
  end else if has_effect e r2 then begin
    has_effect_row_join_r e r1 r2;
    ()
  end else begin
    row_join_no_new_effects e r1 r2;
    ()
  end

(* Semantic associativity for effect_union with SMTPat.

   Note: Structural associativity (==) does NOT hold because row_join
   produces different orderings. For example:
     row_join (RowExt A empty) (row_join (RowExt B empty) (RowExt C empty))
       = RowExt A (RowExt B (RowExt C empty))
     row_join (row_join (RowExt A empty) (RowExt B empty)) (RowExt C empty)
       = RowExt A (RowExt B (RowExt C empty))  -- same in this case!

   Actually, for THIS direction they can be equal. Let me prove structural equality
   where possible using calc blocks.
*)

(* First, prove that has_effect distributes over effect_union *)
val has_effect_effect_union : e:effect_op -> r1:effect_row -> r2:effect_row ->
  Lemma (requires no_row_var r1 = true /\ no_row_var r2 = true)
        (ensures has_effect e (effect_union r1 r2) = (has_effect e r1 || has_effect e r2))
        [SMTPat (has_effect e (effect_union r1 r2))]
let has_effect_effect_union e r1 r2 = has_effect_row_join_distrib_l e r1 r2

(* Semantic associativity: both sides contain exactly the same effects *)
val effect_union_assoc_equiv : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true /\ no_row_var e3 = true)
        (ensures row_equiv (effect_union (effect_union e1 e2) e3)
                           (effect_union e1 (effect_union e2 e3)))
        [SMTPat (effect_union (effect_union e1 e2) e3)]
let effect_union_assoc_equiv e1 e2 e3 =
  no_row_var_row_join e1 e2;
  no_row_var_row_join e2 e3;
  let aux (e:effect_op) : Lemma
      (has_effect e (effect_union (effect_union e1 e2) e3) =
       has_effect e (effect_union e1 (effect_union e2 e3))) =
    (* LHS: has_effect e (effect_union (effect_union e1 e2) e3)
           = has_effect e (effect_union e1 e2) || has_effect e e3
           = (has_effect e e1 || has_effect e e2) || has_effect e e3 *)
    has_effect_effect_union e (effect_union e1 e2) e3;
    has_effect_effect_union e e1 e2;
    (* RHS: has_effect e (effect_union e1 (effect_union e2 e3))
           = has_effect e e1 || has_effect e (effect_union e2 e3)
           = has_effect e e1 || (has_effect e e2 || has_effect e e3) *)
    has_effect_effect_union e e1 (effect_union e2 e3);
    has_effect_effect_union e e2 e3
    (* Boolean associativity: (a || b) || c = a || (b || c) *)
  in
  FStar.Classical.forall_intro aux

(* Semantic commutativity: both sides contain exactly the same effects *)
val effect_union_comm_equiv : e1:effect_row -> e2:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true)
        (ensures row_equiv (effect_union e1 e2) (effect_union e2 e1))
        [SMTPat (effect_union e1 e2); SMTPat (effect_union e2 e1)]
let effect_union_comm_equiv e1 e2 = row_join_comm e1 e2

(** --------------------------------------------------------------------------
    SUBSET LAWS - PARTIAL ORDER PROPERTIES

    effect_subset defines a partial order on effect rows:
    - Reflexivity: effect_subset e e = true (for concrete rows)
    - Transitivity: effect_subset e1 e2 /\ effect_subset e2 e3 ==> effect_subset e1 e3
    - Antisymmetry: effect_subset e1 e2 /\ effect_subset e2 e1 ==> row_equiv e1 e2
    -------------------------------------------------------------------------- *)

(* Reflexivity of effect_subset *)
val effect_subset_refl : e:effect_row ->
  Lemma (requires no_row_var e = true)
        (ensures effect_subset e e = true)
        [SMTPat (effect_subset e e)]
let effect_subset_refl e = row_subset_refl e

(* Transitivity of effect_subset - CRITICAL for subtyping transitivity

   Proof using calc block (HACL* pattern):

   If effect_subset e1 e2 and effect_subset e2 e3, then for any effect e:
   - has_effect e e1 ==> has_effect e e2 (from effect_subset e1 e2)
   - has_effect e e2 ==> has_effect e e3 (from effect_subset e2 e3)
   - Therefore: has_effect e e1 ==> has_effect e e3
   - So: effect_subset e1 e3
*)
val effect_subset_trans : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires effect_subset e1 e2 = true /\ effect_subset e2 e3 = true)
        (ensures effect_subset e1 e3 = true)
let effect_subset_trans e1 e2 e3 = row_subset_trans e1 e2 e3

(* Antisymmetry: mutual subsets implies semantic equivalence *)
#push-options "--fuel 1 --ifuel 0"
val effect_subset_antisym : e1:effect_row -> e2:effect_row ->
  Lemma (requires effect_subset e1 e2 = true /\ effect_subset e2 e1 = true)
        (ensures row_equiv e1 e2)
let effect_subset_antisym e1 e2 =
  let aux (e:effect_op) : Lemma (has_effect e e1 = has_effect e e2) =
    (* If has_effect e e1 = true, then by e1 <= e2, has_effect e e2 = true *)
    (* If has_effect e e2 = true, then by e2 <= e1, has_effect e e1 = true *)
    if has_effect e e1 then has_effect_subset e e1 e2
    else if has_effect e e2 then has_effect_subset e e2 e1
    else ()
  in
  FStar.Classical.forall_intro aux
#pop-options

(** --------------------------------------------------------------------------
    LATTICE STRUCTURE - BOUNDED JOIN-SEMILATTICE

    Effect rows form a bounded join-semilattice with:
    - Bottom: empty_effect (Pure)
    - Join: effect_union
    - Order: effect_subset

    Key lattice properties:
    - empty_effect is the least element
    - effect_union e1 e2 is the least upper bound of e1 and e2
    -------------------------------------------------------------------------- *)

(* empty_effect is the bottom element *)
val effect_empty_is_bottom : e:effect_row ->
  Lemma (effect_subset empty_effect e = true)
        [SMTPat (effect_subset empty_effect e)]
let effect_empty_is_bottom e = ()

(* effect_union produces an upper bound of its arguments *)
val effect_union_upper_bound_l : e1:effect_row -> e2:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true)
        (ensures effect_subset e1 (effect_union e1 e2) = true)
let rec effect_union_upper_bound_l e1 e2 =
  match e1 with
  | RowEmpty -> ()
  | RowExt e rest ->
      (* Need: has_effect e (effect_union e1 e2) = true *)
      has_effect_row_join_l e e1 e2;
      (* Need: effect_subset rest (effect_union e1 e2) = true *)
      effect_union_upper_bound_l rest e2;
      (* By transitivity, since rest is in e1 and e1's effects are in union *)
      (* Actually we need a different approach - use has_effect_row_join_l *)
      let rec prove_rest (r: effect_row) : Lemma
          (requires no_row_var r = true /\ effect_subset r e1 = true)
          (ensures effect_subset r (effect_union e1 e2) = true) =
        match r with
        | RowEmpty -> ()
        | RowExt e' rest' ->
            has_effect_row_join_l e' e1 e2;
            prove_rest rest'
        | RowVar _ -> ()
        | RowVarUnify _ _ -> ()
      in
      row_subset_ext rest e;
      prove_rest rest

val effect_union_upper_bound_r : e1:effect_row -> e2:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true)
        (ensures effect_subset e2 (effect_union e1 e2) = true)
let rec effect_union_upper_bound_r e1 e2 =
  match e2 with
  | RowEmpty -> ()
  | RowExt e rest ->
      has_effect_row_join_r e e1 e2;
      effect_union_upper_bound_r e1 rest;
      let rec prove_rest (r: effect_row) : Lemma
          (requires no_row_var r = true /\ effect_subset r e2 = true)
          (ensures effect_subset r (effect_union e1 e2) = true) =
        match r with
        | RowEmpty -> ()
        | RowExt e' rest' ->
            has_effect_row_join_r e' e1 e2;
            prove_rest rest'
        | RowVar _ -> ()
        | RowVarUnify _ _ -> ()
      in
      row_subset_ext rest e;
      prove_rest rest

(* effect_union is the LEAST upper bound (LUB) - CRITICAL for lattice structure

   Proof: If e3 is an upper bound of both e1 and e2, then effect_union e1 e2 <= e3.

   Reasoning: effect_union e1 e2 contains exactly the effects in e1 or e2.
   Since e1 <= e3 and e2 <= e3, all effects in e1 are in e3 and all effects
   in e2 are in e3. Therefore all effects in (e1 union e2) are in e3.
*)
val effect_join_lub : e1:effect_row -> e2:effect_row -> e3:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true /\
                  effect_subset e1 e3 = true /\ effect_subset e2 e3 = true)
        (ensures effect_subset (effect_union e1 e2) e3 = true)
let rec effect_join_lub e1 e2 e3 =
  match e1 with
  | RowEmpty ->
      (* effect_union RowEmpty e2 = e2, and effect_subset e2 e3 = true *)
      ()
  | RowExt e rest ->
      (* effect_union (RowExt e rest) e2 = add_effect e (effect_union rest e2) *)
      (* From e1 <= e3: has_effect e e3 = true, and effect_subset rest e3 *)
      (* We need: effect_subset (add_effect e (effect_union rest e2)) e3 = true *)
      effect_join_lub rest e2 e3;
      (* Now: effect_subset (effect_union rest e2) e3 = true *)
      (* add_effect e (effect_union rest e2):
         - if e is in (effect_union rest e2), returns unchanged: already subset of e3
         - if e is not in (effect_union rest e2), returns RowExt e (effect_union rest e2):
           need has_effect e e3 (from e1 <= e3) AND effect_subset inner e3 (just proved) *)
      ()
  | RowVar _ -> ()  (* Precondition violation *)
  | RowVarUnify _ _ -> ()  (* Precondition violation *)

(** --------------------------------------------------------------------------
    ADDITIONAL ALGEBRAIC LAWS - DISTRIBUTIVITY AND ABSORPTION
    -------------------------------------------------------------------------- *)

(* effect_union distributes over itself (idempotent semilattice) *)
val effect_union_absorb_l : e1:effect_row -> e2:effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e2 = true /\
                  effect_subset e1 e2 = true)
        (ensures effect_union e1 e2 == e2)
        [SMTPat (effect_union e1 e2)]
let effect_union_absorb_l e1 e2 = row_join_absorb e1 e2

(* Row join is associative (semantic equality).
   This is CRITICAL for the graded monad associativity law:
   (m >>= f) >>= g = m >>= (fun x -> f x >>= g)
   requires that effect combination is associative.

   Note: Structural associativity (row_join r1 (row_join r2 r3) == row_join (row_join r1 r2) r3)
   does NOT hold because row order matters structurally. However, semantic associativity
   (row_equiv) DOES hold: the same effects are present in both results. *)
(* val row_join_assoc declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 200 --fuel 2"
let row_join_assoc r1 r2 r3 =
  (* First establish no_row_var for intermediate results *)
  no_row_var_row_join r2 r3;
  no_row_var_row_join r1 r2;
  let aux (e:effect_op) : Lemma
      (has_effect e (row_join r1 (row_join r2 r3)) =
       has_effect e (row_join (row_join r1 r2) r3)) =
    has_effect_row_join_distrib_l e r1 (row_join r2 r3);
    has_effect_row_join_distrib_l e r2 r3;
    has_effect_row_join_distrib_l e (row_join r1 r2) r3;
    has_effect_row_join_distrib_l e r1 r2
  in
  FStar.Classical.forall_intro aux
#pop-options

(* Effect subtyping respects row_join.
   If r1 is a subset of r1' and r2 is a subset of r2',
   then row_join r1 r2 is a subset of row_join r1' r2'.
   This is critical for effect polymorphism and subtyping covariance. *)
(* val effect_sub_join_compat declared in BrrrEffects.fsti *)
let rec effect_sub_join_compat r1 r1' r2 r2' =
  match r1 with
  | RowEmpty ->
      let rec aux (r: effect_row) : Lemma
          (requires no_row_var r = true /\ row_subset r r2' = true)
          (ensures row_subset r (row_join r1' r2') = true) =
        match r with
        | RowEmpty -> ()
        | RowExt e rest ->
            has_effect_row_join_r e r1' r2';
            aux rest
      in aux r2
  | RowExt e rest ->
      has_effect_row_join_l e r1' r2';
      effect_sub_join_compat rest r1' r2 r2'

(* Congruence: effect_subset is compatible with effect_union *)
val effect_subset_union_compat : e1:effect_row -> e1':effect_row ->
                                  e2:effect_row -> e2':effect_row ->
  Lemma (requires no_row_var e1 = true /\ no_row_var e1' = true /\
                  no_row_var e2 = true /\ no_row_var e2' = true /\
                  effect_subset e1 e1' = true /\ effect_subset e2 e2' = true)
        (ensures effect_subset (effect_union e1 e2) (effect_union e1' e2') = true)
let effect_subset_union_compat e1 e1' e2 e2' =
  effect_sub_join_compat e1 e1' e2 e2'

(** --------------------------------------------------------------------------
    DECIDABILITY AND COMPUTATIONAL LEMMAS
    -------------------------------------------------------------------------- *)

(* Effect row equality is decidable for concrete rows *)
#push-options "--fuel 1 --ifuel 0"
val row_eq_decidable : r1:effect_row -> r2:effect_row ->
  Lemma (row_eq r1 r2 = true \/ row_eq r1 r2 = false)
let row_eq_decidable r1 r2 = ()
#pop-options

(* no_row_var is decidable *)
val no_row_var_decidable : r:effect_row ->
  Lemma (no_row_var r = true \/ no_row_var r = false)
let no_row_var_decidable r = ()

(* Note: row_join_assoc and has_effect_row_join_distrib_l moved earlier in file
   to satisfy .fsti declaration order requirements *)

(** ============================================================================
    COMMON EFFECT COMBINATIONS - Implementations for val declarations
    (unfold let eff_* are defined in BrrrEffects.fsti)
    ============================================================================ *)

(* State effect for a specific location *)
inline_for_extraction noextract
let eff_state_loc (loc: abstract_loc) : effect_row =
  RowExt (ERead loc) (RowExt (EWrite loc) RowEmpty)

(* Exception effect for specific type *)
inline_for_extraction noextract
let eff_throw (exn_type: string) : effect_row =
  RowExt (EThrow exn_type) RowEmpty

(* Session effects for a specific channel *)
inline_for_extraction noextract
let eff_session_chan (ch: chan_id) (payload: effect_type) : effect_row =
  RowExt (ESend ch payload)
    (RowExt (ERecv ch payload)
      (RowExt (ESelect ch "")
        (RowExt (EBranch ch [])
          (RowExt (EChanClose ch) RowEmpty))))

(* Send effect for specific channel *)
inline_for_extraction noextract
let eff_send_chan (ch: chan_id) (payload: effect_type) : effect_row =
  RowExt (ESend ch payload) RowEmpty

(* Receive effect for specific channel *)
inline_for_extraction noextract
let eff_recv_chan (ch: chan_id) (payload: effect_type) : effect_row =
  RowExt (ERecv ch payload) RowEmpty

(* Channel creation effect *)
inline_for_extraction noextract
let eff_chan_create (ch: chan_id) (elem: effect_type) (buf: nat) : effect_row =
  RowExt (EChanCreate ch elem buf) RowEmpty

(* Channel close effect *)
inline_for_extraction noextract
let eff_chan_close (ch: chan_id) : effect_row =
  RowExt (EChanClose ch) RowEmpty

(* Delegate effect *)
inline_for_extraction noextract
let eff_delegate (ch: chan_id) (target: chan_id) : effect_row =
  RowExt (EDelegate ch target) RowEmpty

(* Lock effect for specific lock *)
inline_for_extraction noextract
let eff_lock (lid: lock_id) : effect_row =
  RowExt (ELock lid) RowEmpty

(* Unlock effect for specific lock *)
inline_for_extraction noextract
let eff_unlock (lid: lock_id) : effect_row =
  RowExt (EUnlock lid) RowEmpty

(* Read-lock effect for specific RWMutex *)
inline_for_extraction noextract
let eff_rlock (lid: lock_id) : effect_row =
  RowExt (ERLock lid) RowEmpty

(* Read-unlock effect for specific RWMutex *)
inline_for_extraction noextract
let eff_runlock (lid: lock_id) : effect_row =
  RowExt (ERUnlock lid) RowEmpty

(* Condition variable wait effect *)
inline_for_extraction noextract
let eff_cond_wait (cid: nat) : effect_row =
  RowExt (ECondWait cid) RowEmpty

(* Condition variable signal effect *)
inline_for_extraction noextract
let eff_cond_signal (cid: nat) : effect_row =
  RowExt (ECondSignal cid) RowEmpty

(* Condition variable broadcast effect *)
inline_for_extraction noextract
let eff_cond_broadcast (cid: nat) : effect_row =
  RowExt (ECondBroadcast cid) RowEmpty

(* eff_spawn, eff_join, eff_session, eff_send, eff_recv, eff_new_channel are defined in .fsti *)

(* Resource acquire/release *)
inline_for_extraction noextract
let eff_resource (res: resource_type) : effect_row =
  RowExt (EAcquire res) (RowExt (ERelease res) (RowExt (EUse res) RowEmpty))

(* linearity, op_sig, effect_sig, handler_clause, effect_handler, handler_depth,
   extended_handler, free types are all defined in BrrrEffects.fsti *)

(** ============================================================================
    FREE MONAD OPERATIONS - Implementations for val declarations
    ============================================================================ *)

(* Return for free monad (pure embedding) *)
let free_return (#eff: effect_sig) (#a: Type) (x: a) : free eff a =
  FreePure x

(* Bind for free monad (sequencing) *)
let rec free_bind (#eff: effect_sig) (#a #b: Type)
    (m: free eff a) (f: a -> free eff b) : free eff b =
  match m with
  | FreePure x -> f x
  | FreeImpure op arg cont ->
      FreeImpure op arg (fun ret -> free_bind (cont ret) f)

(* Perform an operation - injects an operation into the free monad.
   Uses memP for propositional membership since op_sig is noeq. *)
let free_perform (#eff: effect_sig) (#a: Type)
    (op: op_sig{List.Tot.memP op eff.operations})
    (arg: effect_type) : free eff effect_type =
  FreeImpure op arg (fun ret -> FreePure ret)

(* handler_clause_legacy, effect_handler_legacy, effect_scheme are defined in .fsti *)

(** ============================================================================
    EFFECT POLYMORPHISM - Implementations
    ============================================================================ *)

(* Monomorphic effect *)
let mono_effect (row: effect_row) : effect_scheme =
  { vars = []; row = row }

(* Substitute effect variable *)
let rec subst_effect_var (v: string) (replacement: effect_row) (row: effect_row)
    : effect_row =
  match row with
  | RowEmpty -> RowEmpty
  | RowExt e rest -> RowExt e (subst_effect_var v replacement rest)
  | RowVar v' -> if v = v' then replacement else RowVar v'
  | RowVarUnify v1 v2 ->
      (* Substitute in both unified variables *)
      if v = v1 && v = v2 then replacement
      else if v = v1 then row_join replacement (RowVar v2)
      else if v = v2 then row_join (RowVar v1) replacement
      else RowVarUnify v1 v2

(* Instantiate effect scheme - uses zip_lists from Utils *)
let instantiate_effect (scheme: effect_scheme) (args: list effect_row)
    : option effect_row =
  if List.Tot.length scheme.vars <> List.Tot.length args then None
  else
    let bindings = zip_lists scheme.vars args in
    let folder row binding =
      match binding with
      | (v, r) -> subst_effect_var v r row
    in
    Some (List.Tot.fold_left folder scheme.row bindings)

(** ============================================================================
    GRADED MONAD STRUCTURE - Based on brrr_lang_spec_v0.4.md Definition 1.7
    ============================================================================ *)

(* comp type is defined in BrrrEffects.fsti *)

(* Return: lift a pure value into a computation with no effects *)
let comp_return (#a: Type) (x: a) : comp a pure =
  MkComp (fun () -> x)

(* Bind: sequence two computations, combining their effects *)
let comp_bind (#a #b: Type) (#e1 #e2: effect_row)
    (m: comp a e1) (f: a -> comp b e2) : comp b (row_join e1 e2) =
  match m with
  | MkComp run_m ->
      MkComp (fun () ->
        let x = run_m () in
        match f x with
        | MkComp run_f -> run_f ())

(* Map: apply a function to the result (preserves effects) *)
let comp_map (#a #b: Type) (#eff: effect_row)
    (f: a -> b) (m: comp a eff) : comp b eff =
  match m with
  | MkComp run -> MkComp (fun () -> f (run ()))

(* Lift: embed a computation with fewer effects into one with more *)
let comp_lift (#a: Type) (#e1 #e2: effect_row)
    (m: comp a e1) : comp a (row_join e1 e2) =
  match m with
  | MkComp run -> MkComp run

(** ============================================================================
    GRADED MONAD LAWS - Proofs
    ============================================================================ *)

(* Left identity: return a >>= f = f a (up to effect equivalence) *)
(* val comp_left_identity declared in BrrrEffects.fsti *)
let comp_left_identity #a #b #e x f =
  row_join_pure e

(* Right identity: m >>= return = m (up to effect equivalence) *)
(* val comp_right_identity declared in BrrrEffects.fsti *)
let comp_right_identity #a #e m =
  match m with
  | MkComp _ -> ()

(* Associativity is guaranteed by row_join_assoc for the effects.
   The computation structure itself is trivially associative since
   we're just composing functions. *)

(* func_effect_sig type is defined in BrrrEffects.fsti *)

(* Empty/pure effect signature *)
let empty_func_effect_sig : func_effect_sig = {
  fes_effects = RowEmpty;
  fes_may_read = false;
  fes_may_write = false;
  fes_may_alloc = false;
  fes_may_free = false;
  fes_may_throw = false;
  fes_may_panic = false;
  fes_may_diverge = false;
  fes_may_io = false;
  fes_may_spawn = false;
  fes_may_send = false;
  fes_may_recv = false;
  fes_may_create_chan = false;
  fes_may_close_chan = false;
  fes_may_select = false;
  fes_may_branch = false;
  fes_may_delegate = false;
  fes_channel_types = [];
  fes_is_pure = true
}

(* Derive flags from effect row *)
let derive_effect_flags (row: effect_row) : func_effect_sig =
  let rec check row = {
    fes_effects = row;
    fes_may_read = has_effect (ERead LocUnknown) row || has_effect EReadSimple row;
    fes_may_write = has_effect (EWrite LocUnknown) row || has_effect EWriteSimple row;
    fes_may_alloc = has_effect EAlloc row;
    fes_may_free = has_effect (EFree LocUnknown) row;
    fes_may_throw = has_effect (EThrow "Exception") row;
    fes_may_panic = has_effect EPanic row;
    fes_may_diverge = has_effect EDiv row;
    fes_may_io = has_effect EIO row || has_effect ENet row || has_effect EFS row;
    fes_may_spawn = has_effect ESpawn row;
    fes_may_send = has_effect EReadSimple row;  (* Legacy send *)
    fes_may_recv = has_effect EWriteSimple row; (* Legacy recv *)
    fes_may_create_chan = has_effect ENewCh row;
    fes_may_close_chan = false;  (* Would need to check specific EChanClose *)
    fes_may_select = false;      (* Would need to check specific ESelect *)
    fes_may_branch = false;      (* Would need to check specific EBranch *)
    fes_may_delegate = false;    (* Would need to check specific EDelegate *)
    fes_channel_types = [];
    fes_is_pure = (match row with RowEmpty -> true | _ -> false)
  }
  in check row

(** ============================================================================
    EFFECT EVENTS AND TRACES - For runtime effect tracking
    Based on synthesis_combined.md effect_event type
    ============================================================================ *)

(* Effect event: a single effect occurrence at runtime *)
(* effect_event type is defined in BrrrEffects.fsti *)

(* Effect trace: sequence of effect events *)
(* effect_trace type is defined in BrrrEffects.fsti *)

(* Effect violations detected from traces *)
(* effect_violation type is defined in BrrrEffects.fsti *)

(** ============================================================================
    EFFECT MASKING
    ============================================================================ *)

(* An effect mask hides certain effects from the caller's view *)
(* effect_mask type is defined in BrrrEffects.fsti *)

(* Create mask that hides some effects *)
let mask_effects (to_hide: effect_row) (actual: effect_row) : effect_mask =
  let rec remove_all hide_row from_row =
    match hide_row with
    | RowEmpty -> from_row
    | RowExt e rest -> remove_all rest (remove_effect e from_row)
    | RowVar _ -> from_row  (* Conservative: can't remove unknown effects *)
    | RowVarUnify _ _ -> from_row  (* Conservative: can't remove unknown effects *)
  in
  { visible = remove_all to_hide actual; hidden = to_hide }

(** ============================================================================
    COEFFECT INTERFACE REQUIREMENTS FOR BRRR-MACHINE
    Based on Petricek 2014 and synthesis_combined.md Section 6.6

    IMPORTANT: Coeffects are the DUAL of effects.
    - Effects: what a computation PRODUCES (side effects)
    - Coeffects: what a computation REQUIRES (context requirements)

    The coeffect system is implemented in Brrr-Machine (the analysis toolkit),
    not in Brrr-Lang (the IR). However, Brrr-Lang must provide the interface
    for coeffect annotations to be attached to types and expressions.
    ============================================================================ *)

(* Coeffect algebra operations - interface for Brrr-Machine
   Based on Petricek 2014: coeffects form a semiring *)
(* coeffect_ops type is defined in BrrrEffects.fsti *)

(* Liveness coeffect - tracks which variables are live
   Based on synthesis_combined.md liveness_coeffect *)
(* liveness type is defined in BrrrEffects.fsti *)

let liveness_ops : coeffect_ops liveness = {
  co_zero = LDead;
  co_one = LLive;
  co_plus = (fun l1 l2 -> if l1 = LDead && l2 = LDead then LDead else LLive);
  co_times = (fun l1 l2 -> if l1 = LDead then LDead else l2);
  co_meet = (fun l1 l2 -> if l1 = LDead && l2 = LDead then LDead else LLive)
}

(* Usage coeffect - tracks how many times a variable is used
   Based on synthesis_combined.md usage_coeffect
   Maps to Rust ownership: UOne = owned/moved, UMany = borrowed *)
(* usage_bound type is defined in BrrrEffects.fsti *)

let usage_plus (u1 u2: usage_bound) : usage_bound =
  match u1, u2 with
  | UZero, u | u, UZero -> u
  | UOne, UOne -> UBounded 2
  | UOne, UBounded n | UBounded n, UOne -> UBounded (n + 1)
  | UBounded n, UBounded m -> UBounded (n + m)
  | UMany, _ | _, UMany -> UMany

let usage_ops : coeffect_ops usage_bound = {
  co_zero = UZero;
  co_one = UOne;
  co_plus = usage_plus;
  co_times = usage_plus;  (* Nesting also accumulates usage *)
  co_meet = (fun u1 u2 ->
    match u1, u2 with
    | UZero, _ -> UZero  (* If either branch doesn't use, might not use *)
    | _, UZero -> UZero
    | UOne, UOne -> UOne
    | UOne, UBounded _ -> UOne  (* min(1, n) = 1 for n >= 1 *)
    | UBounded _, UOne -> UOne
    | UBounded n, UBounded m -> UBounded (if n < m then n else m)
    | UMany, u -> u
    | u, UMany -> u)
}

(* Capability coeffect - flat coeffects for platform/resource requirements
   Based on synthesis_combined.md capability_algebra *)
(* capability type is defined in BrrrEffects.fsti *)

(* Capability set - union semantics *)
(* capability_set type is defined in BrrrEffects.fsti *)

let cap_set_empty : capability_set = []

let cap_set_union (s1 s2: capability_set) : capability_set =
  List.Tot.append s1 s2  (* Simple append; dedup in Brrr-Machine *)

let capability_ops : coeffect_ops capability_set = {
  co_zero = cap_set_empty;
  co_one = cap_set_empty;
  co_plus = cap_set_union;
  co_times = cap_set_union;
  co_meet = cap_set_union  (* Either branch might run, need both *)
}

(* Full type judgment with both effects AND coeffects
   Judgment form: Gamma @ r |- e : tau & epsilon
   - Gamma: typing context
   - r: coeffect annotation (what context variables are required)
   - e: expression
   - tau: result type
   - epsilon: effect row (what side effects are produced) *)
(* full_type_judgment type is defined in BrrrEffects.fsti *)

(** ============================================================================
    CHANNEL LINEARITY CHECK - Session type resource tracking
    Based on synthesis_combined.md check_channel_linearity
    ============================================================================ *)

(* Channel state for linearity checking *)
(* channel_state type is defined in BrrrEffects.fsti *)

(* Channel context: maps channel IDs to their states *)
(* channel_context type is defined in BrrrEffects.fsti *)

(* Check channel linearity: ensures channels are used correctly
   - Cannot use a closed channel
   - Closing consumes the channel (linear resource)
   - Delegation transfers ownership *)
let check_channel_effect (ctx: channel_context) (eff: effect_op)
    : option channel_context =
  match eff with
  | EChanCreate ch elem_ty buf_sz ->
      (* Channel must not already exist *)
      if List.Tot.assoc ch ctx = None
      then Some ((ch, ChanOpen elem_ty buf_sz) :: ctx)
      else None

  | ESend ch _ | ERecv ch _ | ESelect ch _ | EBranch ch _ ->
      (* Channel must be open *)
      (match List.Tot.assoc ch ctx with
       | Some (ChanOpen _ _) -> Some ctx
       | _ -> None)

  | EChanClose ch ->
      (* Channel must be open, becomes closed *)
      (match List.Tot.assoc ch ctx with
       | Some (ChanOpen _ _) ->
           Some (List.Tot.map (fun (k, s) ->
             if k = ch then (k, ChanClosed) else (k, s)) ctx)
       | _ -> None)

  | EDelegate ch target ->
      (* Both channels must be open; target is transferred out *)
      (match List.Tot.assoc ch ctx, List.Tot.assoc target ctx with
       | Some (ChanOpen _ _), Some (ChanOpen _ _) ->
           Some (List.Tot.filter (fun (k, _) -> k <> target) ctx)
       | _, _ -> None)

  | _ -> Some ctx  (* Non-channel effects don't affect channel context *)

(** ============================================================================
    WAITGROUP STATE MODEL - Go sync.WaitGroup semantics
    Models the internal counter and panics-on-negative invariant.

    Per Go spec (pkg/sync/#WaitGroup):
      "A WaitGroup waits for a collection of goroutines to finish.
       The main goroutine calls Add to set the number of goroutines to
       wait for. Then each of the goroutines runs and calls Done when
       finished. At the same time, Wait can be used to block until all
       goroutines have finished."

    Per Go memory model:
      "For any call to wg.Add(n) with n > 0, if there are m calls to
       wg.Done that happen after the Add, the return from the Wait call
       that follows those m calls to Done is synchronized after those
       Done calls."
    ============================================================================ *)

(* wg_state and wg_context types are defined in BrrrEffects.fsti *)

(* Helper: update WaitGroup state in context list *)
private let rec wg_update_ctx (ctx: wg_context) (wid: wg_id) (new_state: wg_state)
    : wg_context =
  match ctx with
  | [] -> []
  | (k, s) :: rest ->
      if k = wid then (k, new_state) :: rest
      else (k, s) :: wg_update_ctx rest wid new_state

(* Apply WaitGroup.Add(delta) - increment counter by delta.
   If counter + delta < 0, the WaitGroup panics (Go spec behavior).
   Returns None if wg_id not found or counter would go negative. *)
let wg_apply_add (ctx: wg_context) (wid: wg_id) (delta: int) : option wg_context =
  match List.Tot.assoc wid ctx with
  | Some (WgActive counter) ->
      let new_val = counter + delta in
      if new_val >= 0
      then Some (wg_update_ctx ctx wid (WgActive new_val))
      else Some (wg_update_ctx ctx wid WgPanicked)  (* Counter went negative - panic *)
  | Some WgPanicked -> None  (* Already panicked *)
  | None -> None             (* WaitGroup not found *)

(* Apply WaitGroup.Done() = Add(-1).
   Returns None if wg_id not found or counter would go negative. *)
let wg_apply_done (ctx: wg_context) (wid: wg_id) : option wg_context =
  wg_apply_add ctx wid (-1)

(* Check if WaitGroup counter is zero (Wait would return immediately).
   Returns None if wg_id not found. *)
let wg_is_zero (ctx: wg_context) (wid: wg_id) : option bool =
  match List.Tot.assoc wid ctx with
  | Some (WgActive counter) -> Some (counter = 0)
  | Some WgPanicked -> None  (* Panicked state *)
  | None -> None

(* Create a new WaitGroup in the context with counter = 0.
   Per Go: "A WaitGroup must not be copied after first use" -
   each wg_id represents a unique instance. *)
let wg_create (ctx: wg_context) (wid: wg_id) : wg_context =
  (wid, WgActive 0) :: ctx

(* Check WaitGroup effect validity against WaitGroup context.
   Applies the effect to update state, returning the new context. *)
let check_wg_effect (ctx: wg_context) (eff: effect_op) : option wg_context =
  match eff with
  | EWaitGroupAdd wid delta ->
      wg_apply_add ctx wid delta
  | EWaitGroupDone wid ->
      wg_apply_done ctx wid
  | EWaitGroupWait wid ->
      (* Wait is valid only when WaitGroup exists and is not panicked *)
      (match List.Tot.assoc wid ctx with
       | Some (WgActive _) -> Some ctx  (* Wait blocks, context unchanged *)
       | _ -> None)
  | _ -> Some ctx  (* Non-WaitGroup effects don't affect WaitGroup context *)

(** ============================================================================
    HAPPENS-BEFORE RELATION - For concurrency analysis
    Based on Lamport 1978, extended per Batty 2011 (C11 memory model)
    ============================================================================ *)

(* Check if effect has release semantics.
   Per Go memory model (https://go.dev/ref/mem#chan):
   "The closing of a channel is synchronized before a receive that returns
    a zero value because the channel is closed."
   This means EChanClose has release semantics. *)
let is_release_effect (e: effect_event) : bool =
  match e.ee_kind with
  | EUnlock _ -> true      (* Mutex unlock has release semantics *)
  | EAtomic -> true        (* Conservative: treat atomics as release *)
  | ESend _ _ -> true      (* Channel send has release semantics *)
  | EChanClose _ -> true   (* Channel close has release semantics - Go memory model *)
  | ERelease _ -> true     (* Explicit release *)
  | EOnce _ -> true        (* sync.Once has release semantics - Go memory model:
                              completion of f() in once.Do(f) synchronizes-before
                              return of any once.Do(f) call *)
  | EWaitGroupDone _ -> true  (* WaitGroup.Done has release semantics - Go memory model:
                                  writes before Done() are visible after Wait() returns *)
  | ERUnlock _ -> true       (* RWMutex.RUnlock has release semantics - Go memory model:
                                  "the matching call to l.RUnlock is synchronized before
                                   the return from call n+1 to l.Lock" *)
  | ECondSignal _ -> true    (* Cond.Signal has release semantics: writes before Signal
                                  become visible to the goroutine woken from Wait *)
  | ECondBroadcast _ -> true (* Cond.Broadcast has release semantics: same as Signal
                                  but wakes all waiters *)
  | ECondWait _ -> true      (* Cond.Wait has release semantics (unlock phase):
                                  atomically unlocks c.L, releasing writes to the mutex *)
  | ESetFinalizer -> true    (* SetFinalizer registration has release semantics - Go memory model:
                                  "A call to SetFinalizer(x, f) is synchronized before
                                   the finalization call f(x)." Registration publishes the
                                   object state for the finalizer goroutine to observe. *)
  | _ -> false

(* Check if effect has acquire semantics *)
let is_acquire_effect (e: effect_event) : bool =
  match e.ee_kind with
  | ELock _ -> true        (* Mutex lock has acquire semantics *)
  | EAtomic -> true        (* Conservative: treat atomics as acquire *)
  | ERecv _ _ -> true      (* Channel receive has acquire semantics *)
  | EAcquire _ -> true     (* Explicit acquire *)
  | EOnce _ -> true        (* sync.Once has acquire semantics - Go memory model:
                              all once.Do(f) callers observe f()'s writes upon return *)
  | EWaitGroupWait _ -> true  (* WaitGroup.Wait has acquire semantics - Go memory model:
                                  Wait() return synchronizes-after last Done() call *)
  | ERLock _ -> true        (* RWMutex.RLock has acquire semantics - Go memory model:
                                "the n-th call to l.Unlock is synchronized before the
                                 return from l.RLock" *)
  | ECondWait _ -> true     (* Cond.Wait has acquire semantics (re-lock phase):
                                after resuming, Wait locks c.L before returning,
                                acquiring writes from Signal/Broadcast sender *)
  | ESetFinalizer -> true  (* Finalizer invocation has acquire semantics - Go memory model:
                                the finalization call f(x) observes all writes that happened
                                before SetFinalizer(x, f). Ideally this would be a separate
                                EFinalizerInvoke effect op; for now ESetFinalizer doubles as
                                both the registration (release) and invocation (acquire) side. *)
  | _ -> false

(* Check if two events synchronize.
   Per Go memory model: close(ch) synchronizes-before recv that returns zero. *)
let effects_synchronize (e1 e2: effect_event) : bool =
  match e1.ee_kind, e2.ee_kind with
  | EUnlock l1, ELock l2 -> l1 = l2       (* Unlock/Lock on same mutex *)
  | ESend c1 _, ERecv c2 _ -> c1 = c2     (* Send/Recv on same channel *)
  | EChanClose c1, ERecv c2 _ -> c1 = c2  (* Close/Recv on same channel - Go memory model *)
  | _, EJoin -> true                       (* Thread join synchronizes *)
  | EAtomic, EAtomic -> true               (* Atomic operations may synchronize *)
  | ERelease r1, EAcquire r2 -> r1 = r2   (* Release/Acquire on same resource *)
  | EOnce o1, EOnce o2 -> o1 = o2         (* sync.Once: completion of f() in once.Do(f)
                                              synchronizes-before return of any once.Do(f).
                                              Same once_id means same Once instance. *)
  | EWaitGroupDone w1, EWaitGroupWait w2 -> w1 = w2  (* Done/Wait on same WaitGroup *)
  | EUnlock l1, ERLock l2 -> l1 = l2    (* RWMutex: n-th Unlock synchronizes-before RLock.
                                            Go memory model: "there is an n such that the n-th
                                            call to l.Unlock is synchronized before the return
                                            from l.RLock" *)
  | ERUnlock l1, ELock l2 -> l1 = l2    (* RWMutex: RUnlock synchronizes-before (n+1)-th Lock.
                                            Go memory model: "the matching call to l.RUnlock is
                                            synchronized before the return from call n+1 to
                                            l.Lock" *)
  | ECondSignal c1, ECondWait c2 -> c1 = c2      (* Signal wakes one waiter on same Cond *)
  | ECondBroadcast c1, ECondWait c2 -> c1 = c2   (* Broadcast wakes all waiters on same Cond *)
  | ESetFinalizer, ESetFinalizer -> true         (* SetFinalizer synchronizes with finalization -
                                                      Go memory model: "A call to SetFinalizer(x, f)
                                                      is synchronized before the finalization call f(x)."
                                                      Ideally this would be ESetFinalizer/EFinalizerInvoke
                                                      on the same object; using self-pairing until a
                                                      dedicated EFinalizerInvoke effect op is introduced. *)
  | _ -> false

(* Happens-before relation (simplified) *)
let happens_before (e1 e2: effect_event) : bool =
  (* Case 1: Sequenced-before (same thread program order) *)
  (e1.ee_thread = e2.ee_thread && e1.ee_timestamp < e2.ee_timestamp)
  ||
  (* Case 2: Synchronizes-with (cross-thread via release/acquire) *)
  (is_release_effect e1 && is_acquire_effect e2 && effects_synchronize e1 e2)

(** ============================================================================
    EFFECT COMMUTATIVITY - Operations on different resources commute
    Based on Honda 2008 Section 3.2 and synthesis_combined.md
    ============================================================================ *)

(* Extract channel ID from an effect operation, if applicable *)
let get_effect_channel (e: effect_op) : option chan_id =
  match e with
  | ESend ch _ -> Some ch
  | ERecv ch _ -> Some ch
  | ESelect ch _ -> Some ch
  | EBranch ch _ -> Some ch
  | EChanCreate ch _ _ -> Some ch
  | EChanClose ch -> Some ch
  | EDelegate ch _ -> Some ch
  | _ -> None

(* Extract lock ID from an effect operation, if applicable.
   Includes both exclusive (Mutex) and shared (RWMutex) lock operations. *)
let get_effect_lock (e: effect_op) : option lock_id =
  match e with
  | ELock lid -> Some lid
  | EUnlock lid -> Some lid
  | ERLock lid -> Some lid
  | ERUnlock lid -> Some lid
  | _ -> None

(* Extract condition variable ID from an effect operation, if applicable.
   sync.Cond operations on the same cond_id must not be reordered. *)
let get_effect_cond (e: effect_op) : option nat =
  match e with
  | ECondWait cid -> Some cid
  | ECondSignal cid -> Some cid
  | ECondBroadcast cid -> Some cid
  | _ -> None

(* Extract once_id from an effect operation, if applicable.
   sync.Once operations on the same once_id must not be reordered. *)
let get_effect_once (e: effect_op) : option nat =
  match e with
  | EOnce oid -> Some oid
  | _ -> None

(* Extract wg_id from an effect operation, if applicable.
   sync.WaitGroup operations on the same wg_id must not be reordered.
   Add/Done/Wait on the same WaitGroup establish happens-before edges. *)
let get_effect_wg (e: effect_op) : option nat =
  match e with
  | EWaitGroupAdd wid _ -> Some wid
  | EWaitGroupDone wid -> Some wid
  | EWaitGroupWait wid -> Some wid
  | _ -> None

(* Extract location from an effect operation, if applicable *)
let get_effect_location (e: effect_op) : option abstract_loc =
  match e with
  | ERead loc -> Some loc
  | EWrite loc -> Some loc
  | EFree loc -> Some loc
  | _ -> None

(* Extract resource from an effect operation, if applicable *)
let get_effect_resource (e: effect_op) : option resource_type =
  match e with
  | EAcquire res -> Some res
  | ERelease res -> Some res
  | EUse res -> Some res
  | _ -> None

(* Effect commutativity: two effects commute if they operate on disjoint resources.
   This is critical for program transformation and parallelization.

   Commutativity rules:
   1. Operations on different channels commute
   2. Operations on different locks commute
   3. Operations on different memory locations commute
   4. Operations on different resources commute
   5. Pure operations commute with everything

   Non-commutativity (ordering matters):
   1. Operations on the SAME channel (session type sequencing)
   2. Operations on the SAME lock (mutex semantics)
   3. Read/Write to the SAME location (memory ordering)
   4. Operations on the SAME resource (linear resource semantics)
   5. Operations that synchronize (happens-before edges)

   This function returns true if e1 and e2 can be safely reordered.
*)
let effects_commute (e1 e2: effect_op) : bool =
  (* Fast path: same effect never commutes with itself in general *)
  if effect_op_eq e1 e2 then false
  else
    (* Check channel operations *)
    match get_effect_channel e1, get_effect_channel e2 with
    | Some ch1, Some ch2 ->
        (* Different channels commute; same channel does not *)
        ch1 <> ch2
    | Some _, None | None, Some _ ->
        (* One is channel, other is not - commute if other is pure/disjoint *)
        true
    | None, None ->
        (* Neither is a channel operation - check other resources *)
        match get_effect_lock e1, get_effect_lock e2 with
        | Some l1, Some l2 -> l1 <> l2
        | Some _, None | None, Some _ -> true
        | None, None ->
            (* Check sync.Cond operations - same cond_id must not commute *)
            match get_effect_cond e1, get_effect_cond e2 with
            | Some c1, Some c2 -> c1 <> c2
            | Some _, None | None, Some _ -> true
            | None, None ->
            (* Check sync.Once operations - same once_id must not commute *)
            match get_effect_once e1, get_effect_once e2 with
            | Some o1, Some o2 -> o1 <> o2
            | Some _, None | None, Some _ -> true
            | None, None ->
            (* Check sync.WaitGroup operations - same wg_id must not commute *)
            match get_effect_wg e1, get_effect_wg e2 with
            | Some w1, Some w2 -> w1 <> w2
            | Some _, None | None, Some _ -> true
            | None, None ->
            match get_effect_location e1, get_effect_location e2 with
            | Some loc1, Some loc2 ->
                (* Different locations commute *)
                not (abstract_loc_eq loc1 loc2) &&
                (* Unless one is LocUnknown which aliases everything *)
                not (match loc1, loc2 with
                     | LocUnknown, _ | _, LocUnknown -> true
                     | _, _ -> false)
            | Some _, None | None, Some _ -> true
            | None, None ->
                match get_effect_resource e1, get_effect_resource e2 with
                | Some r1, Some r2 -> r1 <> r2
                | _, _ -> true  (* Pure/unrelated operations commute *)

(* Effect commutativity is symmetric *)
(* val effects_commute_sym declared in BrrrEffects.fsti *)
#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"
let effects_commute_sym e1 e2 =
  (* First, effect_op_eq is symmetric *)
  effect_op_eq_sym e1 e2;
  (* For abstract_loc_eq in the location comparison *)
  (match get_effect_location e1, get_effect_location e2 with
   | Some loc1, Some loc2 -> abstract_loc_eq_sym loc1 loc2
   | _, _ -> ())
  (* The rest follows from symmetry of <> and || *)
#pop-options

(* Effect row commutativity: all effects in row1 commute with all in row2 *)
let rec row_effects_commute (r1 r2: effect_row) : bool =
  match r1 with
  | RowEmpty -> true
  | RowVar _ -> false  (* Conservative: unknown effects might not commute *)
  | RowVarUnify _ _ -> false  (* Conservative: unknown effects might not commute *)
  | RowExt e1 rest1 ->
      row_effect_commutes_with_all e1 r2 && row_effects_commute rest1 r2

(* Check if a single effect commutes with all effects in a row *)
and row_effect_commutes_with_all (e: effect_op) (r: effect_row) : bool =
  match r with
  | RowEmpty -> true
  | RowVar _ -> false  (* Conservative *)
  | RowVarUnify _ _ -> false  (* Conservative *)
  | RowExt e' rest -> effects_commute e e' && row_effect_commutes_with_all e rest

(** ============================================================================
    SESSION TYPE INTEGRATION WITH EFFECT OPERATIONS
    Bridges BrrrSessionTypes.fst session_type with BrrrEffects.fst effect operations
    ============================================================================ *)

(* Convert effect_type to a simplified representation string for comparison *)
let rec effect_type_to_string (t: effect_type) : string =
  match t with
  | ETUnit -> "unit"
  | ETBool -> "bool"
  | ETInt -> "int"
  | ETString -> "string"
  | ETChan inner -> "chan<" ^ effect_type_to_string inner ^ ">"
  | ETRef inner -> "ref<" ^ effect_type_to_string inner ^ ">"
  | ETFn arg ret -> "fn(" ^ effect_type_to_string arg ^ ")->" ^ effect_type_to_string ret
  | ETVar n -> "T" ^ string_of_int n

(* Session type state for tracking protocol progress.
   This is a simplified representation for effect-level tracking.
   The full session types are in BrrrSessionTypes.fst.

   Relationship to BrrrSessionTypes.fst:
   - SSend t S  corresponds to  SendState (effect_type_of t) (session_state_of S)
   - SRecv t S  corresponds to  RecvState (effect_type_of t) (session_state_of S)
   - SSelect S1 S2 corresponds to SelectState [...states...]
   - SBranch S1 S2 corresponds to BranchState [...states...]
   - SEnd corresponds to EndState
   - SRec/SVar handled via unfolding

   This simplified representation is used for:
   1. Quick effect-level checks without full session type machinery
   2. Integration with effect_op parameters
   3. Brrr-Machine analysis that needs effect-level session info
*)
(* session_state type is defined in BrrrEffects.fsti *)

(* Dual of session state (simplified duality for effect-level).
   Uses mutual recursion with dual_state_list for proper termination. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec dual_state (s: session_state) : Tot session_state (decreases s) =
  match s with
  | SendState t next -> RecvState t (dual_state next)
  | RecvState t next -> SendState t (dual_state next)
  | SelectState branches -> BranchState (dual_state_list branches)
  | BranchState branches -> SelectState (dual_state_list branches)
  | RecState v body -> RecState v (dual_state body)
  | VarState v -> VarState v
  | EndState -> EndState

and dual_state_list (branches: list session_state) : Tot (list session_state) (decreases branches) =
  match branches with
  | [] -> []
  | h :: t -> dual_state h :: dual_state_list t
#pop-options

(* Helper: dual_state_list is involutive *)
let rec dual_state_list_involutive (bs: list session_state) : Lemma
    (ensures dual_state_list (dual_state_list bs) == bs)
    (decreases bs) =
  match bs with
  | [] -> ()
  | h :: t ->
      dual_state_involutive h;
      dual_state_list_involutive t

(* Session duality is involutive: dual(dual(s)) = s
   This is fundamental to session type theory (Honda 1998/2008).
   Proof by structural induction on session state. *)
(* val dual_state_involutive declared in BrrrEffects.fsti *)
and dual_state_involutive s =
  match s with
  | SendState t next ->
      (* dual(dual(SendState t next)) = dual(RecvState t (dual next))
                                      = SendState t (dual(dual next))
                                      = SendState t next  (by IH) *)
      dual_state_involutive next
  | RecvState t next ->
      dual_state_involutive next
  | SelectState branches ->
      (* Need: dual_state_list (dual_state_list branches) == branches *)
      dual_state_list_involutive branches
  | BranchState branches ->
      dual_state_list_involutive branches
  | RecState v body ->
      dual_state_involutive body
  | VarState _ -> ()
  | EndState -> ()

(* Check if two session states are dual *)
let rec are_dual_states (s1 s2: session_state) : Tot bool (decreases s1) =
  match s1, s2 with
  | SendState t1 next1, RecvState t2 next2 ->
      effect_type_eq t1 t2 && are_dual_states next1 next2
  | RecvState t1 next1, SendState t2 next2 ->
      effect_type_eq t1 t2 && are_dual_states next1 next2
  | SelectState bs1, BranchState bs2 ->
      List.Tot.length bs1 = List.Tot.length bs2 &&
      are_dual_state_lists bs1 bs2
  | BranchState bs1, SelectState bs2 ->
      List.Tot.length bs1 = List.Tot.length bs2 &&
      are_dual_state_lists bs1 bs2
  | VarState v1, VarState v2 -> v1 = v2
  | EndState, EndState -> true
  | RecState v1 body1, RecState v2 body2 ->
      v1 = v2 && are_dual_states body1 body2
  | _, _ -> false

and are_dual_state_lists (l1 l2: list session_state) : Tot bool (decreases l1) =
  match l1, l2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 -> are_dual_states h1 h2 && are_dual_state_lists t1 t2
  | _, _ -> false

(* Session-aware channel context: maps channel IDs to their current session states.
   This extends the basic channel_context with full session type tracking. *)
(* session_channel_ctx type is defined in BrrrEffects.fsti *)

(* Empty session channel context *)
let empty_session_ctx : session_channel_ctx = {
  scc_basic = [];
  scc_sessions = []
}

(* Lookup session state for a channel *)
let lookup_session_state (ch: chan_id) (ctx: session_channel_ctx)
    : option session_state =
  List.Tot.assoc ch ctx.scc_sessions

(* Update session state for a channel *)
let update_session_state (ch: chan_id) (s: session_state) (ctx: session_channel_ctx)
    : session_channel_ctx =
  { ctx with
    scc_sessions = (ch, s) :: List.Tot.filter (fun (c, _) -> c <> ch) ctx.scc_sessions }

(* Advance session state after a send operation.
   Returns None if the operation is not valid according to the session type. *)
let advance_session_send (ch: chan_id) (payload: effect_type) (ctx: session_channel_ctx)
    : option session_channel_ctx =
  match lookup_session_state ch ctx with
  | Some (SendState expected_t next) ->
      if effect_type_eq payload expected_t
      then Some (update_session_state ch next ctx)
      else None  (* Type mismatch *)
  | _ -> None  (* Not in send state *)

(* Advance session state after a receive operation *)
let advance_session_recv (ch: chan_id) (payload: effect_type) (ctx: session_channel_ctx)
    : option session_channel_ctx =
  match lookup_session_state ch ctx with
  | Some (RecvState expected_t next) ->
      if effect_type_eq payload expected_t
      then Some (update_session_state ch next ctx)
      else None
  | _ -> None

(* Advance session state after a select operation (internal choice) *)
let advance_session_select (ch: chan_id) (branch_idx: nat) (ctx: session_channel_ctx)
    : option session_channel_ctx =
  match lookup_session_state ch ctx with
  | Some (SelectState branches) ->
      if branch_idx < List.Tot.length branches
      then Some (update_session_state ch (List.Tot.index branches branch_idx) ctx)
      else None
  | _ -> None

(* Check session state after a branch operation (external choice).
   Returns the list of possible next states (caller chooses which applies). *)
let check_session_branch (ch: chan_id) (ctx: session_channel_ctx)
    : option (list session_state) =
  match lookup_session_state ch ctx with
  | Some (BranchState branches) -> Some branches
  | _ -> None

(* Check if a session channel effect is valid according to the session context.
   This integrates channel linearity checking with session type checking. *)
let check_session_effect (ctx: session_channel_ctx) (eff: effect_op)
    : option session_channel_ctx =
  (* First check basic channel linearity *)
  match check_channel_effect ctx.scc_basic eff with
  | None -> None  (* Linearity violation *)
  | Some new_basic ->
      let ctx' = { ctx with scc_basic = new_basic } in
      (* Now check session type progression *)
      match eff with
      | ESend ch payload ->
          advance_session_send ch payload ctx'

      | ERecv ch payload ->
          advance_session_recv ch payload ctx'

      | ESelect ch _ ->
          (* Select requires knowing which branch - simplified to branch 0 for now *)
          advance_session_select ch 0 ctx'

      | EBranch ch _ ->
          (* Branch is valid if we're in a branch state *)
          (match check_session_branch ch ctx' with
           | Some _ -> Some ctx'  (* Valid branch point *)
           | None -> None)

      | EChanCreate ch elem_ty buf_sz ->
          (* Create a new channel with an initial session type *)
          (* The initial session is EndState; actual session set by type system *)
          Some (update_session_state ch EndState ctx')

      | EChanClose ch ->
          (* Close is only valid if session is at EndState *)
          (match lookup_session_state ch ctx' with
           | Some EndState -> Some { ctx' with scc_sessions =
               List.Tot.filter (fun (c, _) -> c <> ch) ctx'.scc_sessions }
           | _ -> None)  (* Cannot close mid-session *)

      | EDelegate ch target ->
          (* Delegation transfers the session of target through ch.
             ch must be able to send a channel, target is removed. *)
          (match lookup_session_state target ctx' with
           | Some _ ->
               Some { ctx' with scc_sessions =
                   List.Tot.filter (fun (c, _) -> c <> target) ctx'.scc_sessions }
           | None -> None)

      | _ -> Some ctx'  (* Non-session effects don't affect session context *)

(** ============================================================================
    BRRR-MACHINE CONCURRENCY ANALYSIS REQUIREMENTS
    Documents what the analysis toolkit needs from Brrr-Lang for concurrency.
    ============================================================================

    Brrr-Machine (the analysis toolkit) needs the following from Brrr-Lang
    (the IR) for comprehensive concurrency analysis:

    1. EFFECT TRACKING:
       - effect_op: Individual effect operations with full parameters
       - effect_row: Sets of effects for tracking what code may do
       - effect_event: Runtime effect occurrences with timestamps/threads

    2. SESSION TYPES:
       - session_type (from BrrrSessionTypes.fst): Full binary session types
       - session_state (this file): Simplified state for effect tracking
       - dual/are_dual: Duality checking for protocol compatibility

    3. CHANNEL OPERATIONS:
       - ESend/ERecv: Message passing with type info
       - ESelect/EBranch: Choice/branching operations
       - EChanCreate/EChanClose: Channel lifecycle
       - EDelegate: Session delegation (higher-order channels)

    4. SYNCHRONIZATION PRIMITIVES:
       - ELock/EUnlock: Mutex operations
       - EAtomic: Atomic memory operations
       - ESpawn/EJoin: Thread lifecycle

    5. ORDERING RELATIONS:
       - happens_before: Partial order on effects
       - effects_synchronize: Cross-thread synchronization points
       - effects_commute: Reordering safety

    6. CONTEXT TRACKING:
       - channel_context: Basic channel state (open/closed)
       - session_channel_ctx: Full session type tracking
       - check_session_effect: Protocol conformance checking

    7. VIOLATION DETECTION:
       - effect_violation: Types of concurrency bugs
       - UseAfterFree, DoubleFree: Memory safety
       - DataRace, Deadlock: Concurrency bugs
       - ResourceLeak, UnhandledEffect: Resource management

    BRRR-MACHINE ANALYSIS PASSES (implemented in Brrr-Machine, uses this IR):

    1. Data Race Detection:
       - Build happens-before graph from effect traces
       - Find concurrent accesses to same location
       - Check if both are writes or one is write

    2. Deadlock Detection:
       - Build wait-for graph from lock/channel effects
       - Detect cycles indicating deadlock potential

    3. Session Type Conformance:
       - Track session state through channel operations
       - Verify operations match expected session type
       - Check duality of endpoint pairs

    4. Channel Linearity:
       - Ensure channels are used exactly once
       - Detect use-after-close
       - Verify proper delegation

    5. Effect Commutativity Analysis:
       - Identify parallelizable code regions
       - Verify safe reordering for optimization
       - Detect potential atomicity violations
    ============================================================================ *)
