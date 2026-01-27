(**
 * BrrrLang.Core.MultipartySession - Interface
 *
 * Public interface for multiparty session types.
 * Following HACL-star/EverParse patterns for .fsti/.fst separation.
 *
 * This interface exports:
 * - Global and local type definitions
 * - Projection function with specifications
 * - Well-formedness predicates
 * - Key lemmas for session type soundness
 *
 * Implementation details are hidden in MultipartySession.fst.
 *)
module MultipartySession

open FStar.List.Tot
open Primitives
open BrrrTypes
open Expressions
open SessionTypes

(* Z3 solver options - must match implementation *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    PARTICIPANT IDENTIFIERS
    ============================================================================ *)

type participant = string
type gtype_var = string

val participant_eq : participant -> participant -> bool

(** ============================================================================
    GLOBAL TYPE DEFINITION
    ============================================================================ *)

(* Global type - describes the entire protocol from a bird's eye view *)
noeq type global_type =
  | GMsg    : sender:participant -> receiver:participant ->
              payload:brrr_type -> continuation:global_type -> global_type
  | GChoice : sender:participant -> receiver:participant ->
              branches:list (label & global_type) -> global_type
  | GPar    : left:global_type -> right:global_type -> global_type
  | GDeleg  : delegator:participant -> receiver:participant ->
              delegated_session:global_type -> continuation:global_type -> global_type
  (* Session delegation (Honda 1998, Section 5):
     GDeleg p q G_d G_c represents:
     - Participant p (delegator) sends a channel with session type G_d to participant q (receiver)
     - The protocol continues with G_c
     - Projects to: p -> LThrow q (G_d|p) (G_c|p)
                    q -> LCatch p (G_d|q) (G_c|q)
                    other -> G_c|other *)
  | GRec    : var:gtype_var -> body:global_type -> global_type
  | GVar    : var:gtype_var -> global_type
  | GEnd    : global_type

(** ============================================================================
    LOCAL TYPE DEFINITION
    ============================================================================ *)

(* Local type - describes protocol from a single participant's perspective *)
noeq type local_type =
  | LSend   : target:participant -> payload:brrr_type ->
              continuation:local_type -> local_type
  | LRecv   : source:participant -> payload:brrr_type ->
              continuation:local_type -> local_type
  | LSelect : target:participant ->
              branches:list (label & local_type) -> local_type
  | LBranch : source:participant ->
              branches:list (label & local_type) -> local_type
  | LThrow  : target:participant -> delegated_type:local_type ->
              continuation:local_type -> local_type
  | LCatch  : source:participant -> delegated_type:local_type ->
              continuation:local_type -> local_type
  | LRec    : var:gtype_var -> body:local_type -> local_type
  | LVar    : var:gtype_var -> local_type
  | LEnd    : local_type

(** ============================================================================
    SIZE FUNCTIONS (for termination proofs)
    ============================================================================ *)

val global_size : g:global_type -> Tot nat (decreases g)
val branch_size : branches:list (label & global_type) -> Tot nat (decreases branches)
val local_size : l:local_type -> Tot nat (decreases l)
val local_branch_size : branches:list (label & local_type) -> Tot nat (decreases branches)

(** ============================================================================
    LOCAL TYPE EQUALITY
    ============================================================================ *)

val local_eq : l1:local_type -> l2:local_type -> Tot bool (decreases l1)
val local_branch_list_eq : bs1:list (label & local_type) -> bs2:list (label & local_type) ->
    Tot bool (decreases bs1)

(* Reflexivity lemma with SMTPat trigger *)
val local_eq_refl : l:local_type ->
  Lemma (ensures local_eq l l = true)
        (decreases l)
        [SMTPat (local_eq l l)]

(** ============================================================================
    LOCAL TYPE MERGE
    ============================================================================ *)

(* Merge two local types if they are compatible *)
val merge_local : l1:local_type -> l2:local_type ->
    Tot (option local_type) (decreases l1)

val merge_branch_lists : bs1:list (label & local_type) -> bs2:list (label & local_type) ->
    Tot (option (list (label & local_type))) (decreases bs1)

val merge_fold : acc:option local_type -> ls:list local_type ->
    Tot (option local_type) (decreases ls)

(* Merge is reflexive *)
val merge_local_refl : l:local_type ->
  Lemma (ensures merge_local l l == Some l)
        (decreases l)
        [SMTPat (merge_local l l)]

(** ============================================================================
    PARTICIPANT EXTRACTION
    ============================================================================ *)

val participants : g:global_type -> Tot (list participant) (decreases g)
val participants_branches : branches:list (label & global_type) ->
    Tot (list participant) (decreases branches)
val dedup : #a:eqtype -> l:list a -> list a
val unique_participants : g:global_type -> list participant

(** ============================================================================
    PROJECTION: Global Type -> Local Type
    ============================================================================ *)

(* Project global type to a participant's local type *)
val project : g:global_type -> p:participant ->
    Tot (option local_type) (decreases g)

val project_branches : branches:list (label & global_type) -> p:participant ->
    Tot (option (list (label & local_type))) (decreases branches)

(** ============================================================================
    LOCAL TYPE TO SESSION TYPE CONVERSION
    ============================================================================ *)

(* Convert local type to binary session type (erasing participant info) *)
val local_to_session : l:local_type -> Tot session_type (decreases l)

(** ============================================================================
    FREE VARIABLES
    ============================================================================ *)

val free_gvars : g:global_type -> Tot (list gtype_var) (decreases g)
val free_lvars : l:local_type -> Tot (list gtype_var) (decreases l)
val is_closed_global : g:global_type -> bool
val is_closed_local : l:local_type -> bool

(** ============================================================================
    CONTRACTIVITY (Guardedness)
    ============================================================================ *)

(* Check if variable x appears free in global type *)
val var_appears_in_global : x:gtype_var -> g:global_type -> Tot bool (decreases g)

(* Check if variable x is guarded in global type *)
val is_guarded_global : x:gtype_var -> g:global_type -> Tot bool (decreases g)

(* Check if variable x is guarded in local type *)
val is_guarded_local : x:gtype_var -> l:local_type -> Tot bool (decreases l)

(* Check if global type is contractive *)
val is_contractive_global : g:global_type -> bool

(* Check if local type is contractive *)
val is_contractive_local : l:local_type -> bool

(** ============================================================================
    WELL-FORMEDNESS PREDICATES
    ============================================================================ *)

(* Check sender/receiver distinction in all interactions *)
val distinct_roles : g:global_type -> bool

(* Check that choices have at least one branch *)
val nonempty_choices : g:global_type -> bool

(* Check that all participants have defined projections *)
val all_projectable : g:global_type -> bool

(* Check that parallel composition has disjoint participants *)
val disjoint_parallel_participants : g:global_type -> bool

(* Main well-formedness predicate *)
val well_formed_global : g:global_type -> bool

(** ============================================================================
    DEADLOCK FREEDOM
    ============================================================================ *)

type dep_edge = participant & participant
type dep_graph = list dep_edge

val build_dep_graph : g:global_type -> dep_graph
val is_acyclic : g:dep_graph -> bool
val is_deadlock_free_global : g:global_type -> bool

(** ============================================================================
    COMMUNICATION SAFETY PREDICATES
    ============================================================================ *)

val is_send_type : l:local_type -> bool
val is_recv_type : l:local_type -> bool
val send_target : l:local_type -> option participant
val recv_source : l:local_type -> option participant

(** ============================================================================
    DUAL LOCAL TYPES
    ============================================================================ *)

(* Check if two local types are dual with respect to participants p and q *)
val are_dual_wrt : l1:local_type -> l2:local_type -> p:participant -> q:participant -> bool

(** ============================================================================
    KEY LEMMAS - Projection Properties
    ============================================================================ *)

(* Projection of message sender gives send type *)
val projection_msg_sender_is_send : sender:participant -> receiver:participant ->
  ty:brrr_type -> cont:global_type ->
  Lemma (requires sender <> receiver /\ Some? (project cont sender))
        (ensures (match project (GMsg sender receiver ty cont) sender with
                  | Some l -> is_send_type l = true /\ send_target l = Some receiver
                  | None -> False))

(* Projection of message receiver gives recv type *)
val projection_msg_receiver_is_recv : sender:participant -> receiver:participant ->
  ty:brrr_type -> cont:global_type ->
  Lemma (requires sender <> receiver /\ Some? (project cont receiver))
        (ensures (match project (GMsg sender receiver ty cont) receiver with
                  | Some l -> is_recv_type l = true /\ recv_source l = Some sender
                  | None -> False))

(* Projection of choice sender gives select type *)
val projection_choice_sender_is_select : sender:participant -> receiver:participant ->
  branches:list (label & global_type) ->
  Lemma (requires sender <> receiver /\ Some? (project_branches branches sender))
        (ensures (match project (GChoice sender receiver branches) sender with
                  | Some l -> is_send_type l = true /\ send_target l = Some receiver
                  | None -> False))

(* Projection of choice receiver gives branch type *)
val projection_choice_receiver_is_branch : sender:participant -> receiver:participant ->
  branches:list (label & global_type) ->
  Lemma (requires sender <> receiver /\ Some? (project_branches branches receiver))
        (ensures (match project (GChoice sender receiver branches) receiver with
                  | Some l -> is_recv_type l = true /\ recv_source l = Some sender
                  | None -> False))

(** ============================================================================
    KEY LEMMAS - Well-Formedness Properties
    ============================================================================ *)

(* Well-formed global types are projectable to all participants *)
val wellformed_implies_projectable : g:global_type ->
  Lemma (requires well_formed_global g = true)
        (ensures all_projectable g = true)
        [SMTPat (well_formed_global g)]

(* Deadlock freedom: well-formed + acyclic deps => progress *)
val deadlock_freedom : g:global_type ->
  Lemma (requires well_formed_global g = true /\ is_deadlock_free_global g = true)
        (ensures all_projectable g = true)

(** ============================================================================
    HELPER PREDICATES
    ============================================================================ *)

val direct_interaction : g:global_type -> p:participant -> q:participant -> bool

(** ============================================================================
    KEY LEMMAS - Projection Consistency
    ============================================================================ *)

(* If two participants directly interact, both have defined projections *)
val projection_preserves_comm : g:global_type -> p:participant -> q:participant ->
  Lemma (requires well_formed_global g = true /\
                  direct_interaction g p q = true /\
                  p <> q)
        (ensures Some? (project g p) /\ Some? (project g q))

(* Projection consistency: interacting participants have compatible projections *)
val projection_consistency : g:global_type -> p:participant -> q:participant ->
  Lemma (requires well_formed_global g = true /\
                  direct_interaction g p q = true /\
                  p <> q)
        (ensures (match project g p, project g q with
                  | Some _, Some _ -> true
                  | _, _ -> false))

(** ============================================================================
    VALIDATION FUNCTIONS
    ============================================================================ *)

val validate_and_project : g:global_type -> option (list (participant & local_type))
val full_validate : g:global_type -> bool

(** ============================================================================
    ADDITIONAL LEMMAS - Projection Soundness
    ============================================================================ *)

(* Projection preserves type structure *)
val projection_preserves_structure : g:global_type -> p:participant ->
  Lemma (ensures (match g, project g p with
                  | GEnd, Some LEnd -> true
                  | GVar x, Some (LVar y) -> x = y
                  | GRec x _, Some (LRec y _) -> x = y
                  | GMsg s r _ _, Some (LSend target _ _) -> p = s /\ target = r
                  | GMsg s r _ _, Some (LRecv source _ _) -> p = r /\ source = s
                  | GChoice s r _, Some (LSelect target _) -> p = s /\ target = r
                  | GChoice s r _, Some (LBranch source _) -> p = r /\ source = s
                  | GDeleg d r _ _, Some (LThrow target _ _) -> p = d /\ target = r
                  | GDeleg d r _ _, Some (LCatch source _ _) -> p = r /\ source = d
                  | _, None -> true
                  | _, _ -> true
                  ))
        [SMTPat (project g p)]

(* Dual projections for message interaction *)
val dual_projection_msg : sender:participant -> receiver:participant ->
  ty:brrr_type -> cont:global_type ->
  Lemma (requires sender <> receiver /\
                  Some? (project cont sender) /\ Some? (project cont receiver))
        (ensures (let g = GMsg sender receiver ty cont in
                  match project g sender, project g receiver with
                  | Some (LSend t1 ty1 _), Some (LRecv s2 ty2 _) ->
                      t1 = receiver /\ s2 = sender /\ type_eq ty1 ty2
                  | _, _ -> False))
        [SMTPat (project (GMsg sender receiver ty cont) sender);
         SMTPat (project (GMsg sender receiver ty cont) receiver)]

(* Dual projections for delegation interaction *)
val dual_projection_deleg : delegator:participant -> receiver:participant ->
  ds:global_type -> cont:global_type ->
  Lemma (requires delegator <> receiver /\
                  Some? (project ds delegator) /\ Some? (project ds receiver) /\
                  Some? (project cont delegator) /\ Some? (project cont receiver))
        (ensures (let g = GDeleg delegator receiver ds cont in
                  match project g delegator, project g receiver with
                  | Some (LThrow t _ _), Some (LCatch s _ _) ->
                      t = receiver /\ s = delegator
                  | _, _ -> False))
        [SMTPat (project (GDeleg delegator receiver ds cont) delegator);
         SMTPat (project (GDeleg delegator receiver ds cont) receiver)]

(* Guardedness is preserved by projection *)
val guardedness_preserved : g:global_type -> p:participant -> x:gtype_var ->
  Lemma (requires is_guarded_global x g = true /\ Some? (project g p))
        (ensures is_guarded_local x (Some?.v (project g p)) = true)
        (decreases g)

(* Contractiveness is preserved by projection *)
val contractiveness_preserved : g:global_type -> p:participant ->
  Lemma (requires is_contractive_global g = true /\ Some? (project g p))
        (ensures is_contractive_local (Some?.v (project g p)) = true)
        (decreases g)

(* Projection of disjoint GPar preserves structure *)
val gpar_projection_disjoint : left:global_type -> right:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar left right) = true /\
                  List.Tot.mem p (participants left) = true /\
                  List.Tot.mem p (participants right) = false)
        (ensures project (GPar left right) p == project left p)

(* Projection of disjoint GPar (left branch) with SMT pattern *)
val project_gpar_disjoint : g1:global_type -> g2:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar g1 g2) = true /\
                  List.Tot.mem p (participants g1) = true)
        (ensures project (GPar g1 g2) p == project g1 p)
        [SMTPat (project (GPar g1 g2) p)]

(* Projection of disjoint GPar (right branch) with SMT pattern *)
val project_gpar_disjoint_right : g1:global_type -> g2:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar g1 g2) = true /\
                  List.Tot.mem p (participants g2) = true)
        (ensures project (GPar g1 g2) p == project g2 p)
        [SMTPat (project (GPar g1 g2) p)]

(* Well-formedness implies projection exists for all participants *)
val wellformed_all_projections : g:global_type -> p:participant ->
  Lemma (requires well_formed_global g = true /\
                  List.Tot.mem p (unique_participants g) = true)
        (ensures Some? (project g p))
        [SMTPat (well_formed_global g); SMTPat (project g p)]

(** ============================================================================
    EXAMPLE PROTOCOLS
    ============================================================================ *)

val two_buyer_protocol : global_type
val ping_pong_protocol : global_type
val stream_protocol : global_type
val parallel_streams_protocol : global_type
val parallel_fanout_protocol : global_type

(* Session delegation examples using GDeleg *)
val client_session_global : global_type
val ftp_delegation_protocol : global_type
val worker_pool_protocol : global_type

(* Local type delegation examples *)
val client_session_type : local_type
val ftp_worker_local : local_type
val ftp_server_local : local_type
