(**
 * BrrrLang.Core.MultipartySession - Public Interface
 *
 * ============================================================================
 * MULTIPARTY SESSION TYPES (MPST) FOR DISTRIBUTED COMMUNICATION PROTOCOLS
 * ============================================================================
 *
 * This module implements multiparty session types following the foundational
 * work of Honda, Yoshida, and Carbone (POPL 2008), with corrections from
 * Scalas & Yoshida (2019) "Less is More" and Yoshida & Hou (2024).
 *
 * THEORETICAL FOUNDATION:
 * ------------------------
 * Multiparty session types provide a type discipline for distributed protocols
 * involving multiple participants. The key insight is to describe protocols
 * from two perspectives:
 *
 *   1. GLOBAL TYPES (G): A bird's-eye view of the entire protocol, describing
 *      all interactions between all participants. This is the "choreography".
 *
 *   2. LOCAL TYPES (L): Each participant's view of the protocol, describing
 *      what that participant sends, receives, and chooses. This is the
 *      "endpoint behavior".
 *
 * The PROJECTION operation (G |_p) extracts participant p's local type from
 * a global type, ensuring that local implementations correctly follow the
 * global protocol.
 *
 * SAFETY GUARANTEES:
 * ------------------
 * Well-formed global types guarantee several safety properties:
 *
 *   - SESSION FIDELITY: Local implementations conform to the global protocol.
 *     Formally: if G |_p = L and process P has type L, then P follows G.
 *
 *   - COMMUNICATION SAFETY: No message type mismatches. If participant p
 *     sends type T, the receiver expects type T.
 *
 *   - PROGRESS (with caveats): Well-typed sessions can make progress.
 *     NOTE: Full deadlock freedom requires additional constraints (see below).
 *
 * IMPORTANT CORRECTIONS TO HONDA 2008:
 * ------------------------------------
 * The original Honda et al. formulation contained errors identified by
 * Scalas & Yoshida (2019):
 *
 *   1. PROJECTION USES SUBTYPING, NOT EQUALITY:
 *      Original: G |_p = Gamma(s[p])   (equality)
 *      Corrected: G |_p <= Gamma(s[p]) (subtyping)
 *
 *      This allows processes to implement MORE SPECIFIC protocols than
 *      what the global type specifies.
 *
 *   2. ASSOCIATION RELATION REPLACES COHERENCE:
 *      We use G ~ Gamma (G is associated with Gamma) defined as:
 *        forall p in participants(G). G |_p <= Gamma(s[p])
 *
 *   3. DEADLOCK FREEDOM REQUIRES EXTRA CONDITIONS:
 *      Well-typedness alone does NOT guarantee deadlock freedom in
 *      asynchronous settings. Additional requirements:
 *        - Priority-based typing (Kobayashi, Padovani), OR
 *        - Synchronous semantics, OR
 *        - Acyclic communication topology
 *
 * MERGE OPERATION:
 * ----------------
 * For participants not directly involved in a choice (GChoice), we must
 * MERGE the local types from different branches. Merge is defined only
 * when branches are COMPATIBLE:
 *
 *   - Same communication structure (sends match sends, receives match receives)
 *   - Same target/source participants
 *   - Same payload types
 *
 * If merge is undefined, projection fails, indicating the protocol is
 * ambiguous for that participant.
 *
 * SESSION DELEGATION (GDeleg):
 * ----------------------------
 * Following Honda (1998, Section 5), session delegation allows a participant
 * to transfer an active session channel to another participant:
 *
 *   GDeleg delegator receiver G_delegated G_continuation
 *
 * This projects to:
 *   - delegator: LThrow receiver (G_delegated|delegator) (G_cont|delegator)
 *   - receiver:  LCatch delegator (G_delegated|receiver) (G_cont|receiver)
 *   - others:    (G_cont|other)
 *
 * Delegation enables higher-order session programming where session channels
 * themselves can be communicated.
 *
 * PARALLEL COMPOSITION (GPar):
 * ----------------------------
 * GPar left right represents two independent sub-protocols running in parallel.
 * Well-formedness requires DISJOINT participants between left and right to
 * avoid interference. Projection simply projects from the relevant branch.
 *
 * REFERENCES:
 * -----------
 * [1] Honda, Yoshida, Carbone. "Multiparty Asynchronous Session Types."
 *     POPL 2008. (Foundational paper - contains some errors)
 *
 * [2] Scalas, Yoshida. "Less is More: Multiparty Session Types Revisited."
 *     POPL 2019. (Introduces association relation, fixes subtyping)
 *
 * [3] Yoshida, Hou. "Less is More, Revisited." ECOOP 2024.
 *     (Formalizes safety property correctly)
 *
 * [4] Honda. "Types for Dyadic Interaction." CONCUR 1993.
 *     (Original binary session types)
 *
 * [5] Honda. "Language Primitives and Type Discipline for Structured
 *     Communication-Based Programming." ESOP 1998. (Session delegation)
 *
 * [6] Kobayashi. "A New Type System for Deadlock-Free Processes."
 *     CONCUR 2006. (Priority-based deadlock freedom)
 *
 * INTERFACE DESIGN:
 * -----------------
 * Following HACL-star/EverParse patterns, this .fsti file exports:
 *   - Type definitions for global and local types
 *   - Projection function with specification
 *   - Well-formedness predicates
 *   - Key lemmas establishing soundness properties
 *
 * Implementation details are hidden in BrrrMultipartySession.fst.
 *)
module BrrrMultipartySession

open FStar.List.Tot
open BrrrPrimitives
open BrrrTypes
open BrrrExpressions
open BrrrSessionTypes

(* ============================================================================
   Z3 SOLVER CONFIGURATION
   ============================================================================

   These options must match the implementation file for consistent verification.

   --z3rlimit 50: Resource limit for SMT queries (prevents timeouts)
   --fuel 0: Minimal recursive unfolding (faster proofs)
   --ifuel 0: Minimal inductive unfolding (faster proofs)

   Increase fuel locally with #push-options if needed for specific lemmas.
*)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    PARTICIPANT IDENTIFIERS
    ============================================================================

    Participants are identified by strings (e.g., "Buyer1", "Seller", "Server").
    In a distributed system, these map to actual network endpoints.

    Type variables for recursive global types use the same representation
    for simplicity, though they inhabit a different namespace conceptually.
*)

(** Participant identifier type - represents a role in the protocol *)
type participant = string

(** Type variable identifier for recursive global types (mu X. G) *)
type gtype_var = string

(**
 * Decidable equality for participants.
 * Required for pattern matching on participant identity in projection.
 *)
val participant_eq : participant -> participant -> bool

(** ============================================================================
    GLOBAL TYPE DEFINITION
    ============================================================================

    Global types describe the protocol from a bird's-eye view, specifying
    ALL interactions between ALL participants.

    SYNTAX (from brrr_lang_spec_v0.4.tex, Section "Multiparty Session Types"):

      G ::= p -> q : T.G           (message from p to q with payload T)
          | p -> q : {l_i: G_i}    (labeled choice: p selects, q branches)
          | G1 || G2               (parallel composition)
          | throw p q G_d.G_c      (session delegation)
          | mu X. G                (recursion)
          | X                      (type variable)
          | end                    (termination)

    WELL-FORMEDNESS CONDITIONS:
    - sender <> receiver in all message/choice/delegation constructors
    - All recursive variables are bound (closed type)
    - Recursion is guarded (contractive) - no mu X. X
    - Parallel branches have disjoint participant sets
    - Choice branches have at least one option

    The 'noeq' annotation indicates that structural equality is not derivable
    (due to function-like components and abstract types in payloads).
*)
noeq type global_type =
  (**
   * GMsg sender receiver payload continuation
   *
   * Represents a message passing interaction:
   *   "sender sends payload to receiver, then continue with continuation"
   *
   * PROJECTION:
   *   - sender:   LSend receiver payload (project continuation)
   *   - receiver: LRecv sender payload (project continuation)
   *   - other:    project continuation (skip this interaction)
   *
   * WELL-FORMEDNESS: sender <> receiver
   *)
  | GMsg    : sender:participant -> receiver:participant ->
              payload:brrr_type -> continuation:global_type -> global_type

  (**
   * GChoice sender receiver branches
   *
   * Represents a labeled choice/branching:
   *   "sender selects a label, receiver branches on that label"
   *
   * The branches list contains (label, continuation) pairs.
   * At least one branch must be present.
   *
   * PROJECTION:
   *   - sender:   LSelect receiver [(l_i, project G_i)]  (internal choice)
   *   - receiver: LBranch sender [(l_i, project G_i)]   (external choice)
   *   - other:    MERGE all (project G_i)  (may fail if incompatible)
   *
   * MERGE REQUIREMENT:
   * For participants not directly involved, all branch projections must
   * be MERGEABLE (same communication structure). This ensures the
   * uninvolved participant can't distinguish which branch was taken.
   *
   * WELL-FORMEDNESS: sender <> receiver, branches non-empty
   *)
  | GChoice : sender:participant -> receiver:participant ->
              branches:list (label & global_type) -> global_type

  (**
   * GPar left right
   *
   * Parallel composition of two independent sub-protocols.
   *
   * PROJECTION:
   *   - If p in participants(left) and p not in participants(right): project left
   *   - If p in participants(right) and p not in participants(left): project right
   *   - If p in neither: LEnd
   *   - If p in both: UNDEFINED (violates disjointness)
   *
   * WELL-FORMEDNESS: participants(left) and participants(right) must be disjoint.
   * This prevents interference between parallel threads.
   *)
  | GPar    : left:global_type -> right:global_type -> global_type

  (**
   * GDeleg delegator receiver delegated_session continuation
   *
   * Session delegation (higher-order session types):
   *   "delegator transfers the channel for delegated_session to receiver"
   *
   * This enables passing session channels as first-class values.
   * The transferred channel has type (delegated_session|receiver).
   *
   * PROJECTION (following Honda 1998, Section 5):
   *   - delegator: LThrow receiver (delegated_session|delegator) (continuation|delegator)
   *   - receiver:  LCatch delegator (delegated_session|receiver) (continuation|receiver)
   *   - other:     continuation|other (unaffected)
   *
   * INTUITION:
   * Delegator "throws" (sends) a channel, receiver "catches" (receives) it.
   * The delegated session's projection differs for each participant because
   * they may play different roles in that sub-session.
   *
   * EXAMPLE - FTP with worker delegation:
   *   Client connects to Server, Server delegates to Worker:
   *   GDeleg "Server" "Worker" (client_session) (acknowledgment)
   *)
  | GDeleg  : delegator:participant -> receiver:participant ->
              delegated_session:global_type -> continuation:global_type -> global_type

  (**
   * GRec var body
   *
   * Recursive global type: mu var. body
   *
   * Enables protocols with loops, like streaming or keep-alive patterns.
   *
   * PROJECTION: LRec var (project body)
   *
   * CONTRACTIVITY REQUIREMENT:
   * The variable 'var' must be GUARDED in 'body'. This means 'var' must
   * appear under at least one communication action (GMsg, GChoice, GDeleg).
   * Invalid: mu X. X  (infinite unfolding, not contractive)
   * Valid:   mu X. p->q:int.X  (communication guards the recursion)
   *)
  | GRec    : var:gtype_var -> body:global_type -> global_type

  (**
   * GVar var
   *
   * Reference to a recursively bound type variable.
   *
   * PROJECTION: LVar var (preserves variable)
   *
   * WELL-FORMEDNESS: var must be bound by an enclosing GRec
   *)
  | GVar    : var:gtype_var -> global_type

  (**
   * GEnd
   *
   * Protocol termination - no more interactions.
   *
   * PROJECTION: LEnd
   *)
  | GEnd    : global_type

(** ============================================================================
    LOCAL TYPE DEFINITION
    ============================================================================

    Local types describe the protocol from a SINGLE participant's perspective.
    They are obtained by PROJECTING a global type onto a participant.

    SYNTAX:
      L ::= !<q, T>.L    (send to q)
          | ?<p, T>.L    (receive from p)
          | +{l_i: L_i}  (internal choice - select)
          | &{l_i: L_i}  (external choice - branch)
          | throw<q, L'>.L  (delegate session L' to q)
          | catch<p, L'>.L  (receive delegated session L' from p)
          | mu X. L      (recursion)
          | X            (variable)
          | end          (termination)

    DUALITY:
    For binary sessions, send is dual to receive, internal choice is dual
    to external choice. In multiparty settings, duality is more nuanced -
    we check that projections are COMPATIBLE rather than strictly dual.

    TYPE SAFETY:
    A process P with local type L is guaranteed to:
    - Send when the protocol expects a send
    - Receive when the protocol expects a receive
    - Handle all branches when branching
    - Not deadlock (with additional priority constraints)
*)
noeq type local_type =
  (**
   * LSend target payload continuation
   *
   * Send action: transmit 'payload' to 'target', then continue.
   *
   * RUNTIME: Corresponds to an asynchronous send operation.
   * The continuation can proceed immediately (non-blocking).
   *
   * From projection of GMsg where this participant is the sender.
   *)
  | LSend   : target:participant -> payload:brrr_type ->
              continuation:local_type -> local_type

  (**
   * LRecv source payload continuation
   *
   * Receive action: wait for 'payload' from 'source', then continue.
   *
   * RUNTIME: May block until a message arrives.
   *
   * From projection of GMsg where this participant is the receiver.
   *)
  | LRecv   : source:participant -> payload:brrr_type ->
              continuation:local_type -> local_type

  (**
   * LSelect target branches
   *
   * Internal choice (selection): choose one label from branches and
   * send it to target.
   *
   * SUBTYPING: Can select FEWER options than specified (contravariant).
   * If type says {ok, err}, implementation can always just send 'ok'.
   *
   * From projection of GChoice where this participant is the sender.
   *)
  | LSelect : target:participant ->
              branches:list (label & local_type) -> local_type

  (**
   * LBranch source branches
   *
   * External choice (branching): wait for source to send a label,
   * then continue with the corresponding branch.
   *
   * MUST handle ALL labels specified. Cannot ignore any branch.
   * SUBTYPING: Must handle ALL options (covariant in branches).
   *
   * From projection of GChoice where this participant is the receiver.
   *)
  | LBranch : source:participant ->
              branches:list (label & local_type) -> local_type

  (**
   * LThrow target delegated_type continuation
   *
   * Session delegation - throw (send) a session channel to target.
   * The channel has type 'delegated_type' from this participant's view.
   *
   * From projection of GDeleg where this participant is the delegator.
   *
   * HIGHER-ORDER: The delegated_type is itself a session type,
   * enabling session channels to be passed as values.
   *)
  | LThrow  : target:participant -> delegated_type:local_type ->
              continuation:local_type -> local_type

  (**
   * LCatch source delegated_type continuation
   *
   * Session delegation - catch (receive) a session channel from source.
   * The received channel has type 'delegated_type'.
   *
   * From projection of GDeleg where this participant is the receiver.
   *)
  | LCatch  : source:participant -> delegated_type:local_type ->
              continuation:local_type -> local_type

  (**
   * LRec var body
   *
   * Recursive local type: mu var. body
   *
   * CONTRACTIVITY: Same requirement as GRec - var must be guarded.
   *)
  | LRec    : var:gtype_var -> body:local_type -> local_type

  (**
   * LVar var
   *
   * Reference to recursively bound variable.
   *)
  | LVar    : var:gtype_var -> local_type

  (**
   * LEnd
   *
   * Protocol termination from this participant's view.
   *)
  | LEnd    : local_type

(** ============================================================================
    SIZE FUNCTIONS (for termination proofs)
    ============================================================================

    These functions compute structural sizes for use in termination arguments.
    F* requires explicit termination metrics for recursive functions.

    The size of a type is always > 0 and > size of any subterm.
    This establishes a well-founded ordering for structural recursion.
*)

(**
 * Compute the structural size of a global type.
 * Used as termination metric in recursive functions over global types.
 * Guarantee: global_size g > 0 for all g
 *)
val global_size : g:global_type -> Tot nat (decreases g)

(**
 * Compute the structural size of a list of labeled global type branches.
 * Helper for global_size on GChoice.
 *)
val branch_size : branches:list (label & global_type) -> Tot nat (decreases branches)

(**
 * Compute the structural size of a local type.
 * Used as termination metric in recursive functions over local types.
 *)
val local_size : l:local_type -> Tot nat (decreases l)

(**
 * Compute the structural size of a list of labeled local type branches.
 * Helper for local_size on LSelect/LBranch.
 *)
val local_branch_size : branches:list (label & local_type) -> Tot nat (decreases branches)

(** ============================================================================
    LOCAL TYPE EQUALITY
    ============================================================================

    Decidable structural equality for local types.

    This is more complex than mere structural equality because we need to
    handle recursive types correctly. Two recursive types are equal if their
    bodies are equal under the same variable bindings.

    Note: This is SYNTACTIC equality, not semantic equality. Two types that
    unfold to the same infinite tree may not be syntactically equal.
*)

(**
 * Decidable equality for local types.
 * Returns true iff l1 and l2 have identical structure.
 *)
val local_eq : l1:local_type -> l2:local_type -> Tot bool (decreases l1)

(**
 * Decidable equality for branch lists.
 * Two branch lists are equal if they have the same labels in the same
 * order with equal continuations.
 *)
val local_branch_list_eq : bs1:list (label & local_type) -> bs2:list (label & local_type) ->
    Tot bool (decreases bs1)

(**
 * LEMMA: local_eq is reflexive.
 *
 * For any local type l, local_eq l l = true.
 *
 * The SMTPat annotation allows Z3 to automatically apply this lemma
 * when it sees expressions of the form (local_eq l l).
 *)
val local_eq_refl : l:local_type ->
  Lemma (ensures local_eq l l = true)
        (decreases l)
        [SMTPat (local_eq l l)]

(** ============================================================================
    LOCAL TYPE MERGE
    ============================================================================

    MERGE OPERATION (from Honda et al. 2008, corrected in Scalas & Yoshida 2019)

    When projecting GChoice to a participant who is NOT the sender or receiver,
    we must MERGE the projections of all branches. This is necessary because
    the uninvolved participant cannot observe which branch was chosen.

    DEFINITION (merge is the least upper bound under subtyping):

      !<q,T>.L1 merge !<q,T>.L2 = !<q,T>.(L1 merge L2)   (same send)
      ?<q,T>.L1 merge ?<q,T>.L2 = ?<q,T>.(L1 merge L2)   (same receive)
      &{...} merge &{...} = & (union of branches with merged continuations)
      end merge end = end
      X merge X = X

    MERGE IS UNDEFINED (returns None) when:
      - Different action types (send vs receive)
      - Different targets/sources
      - Different payload types
      - Incompatible recursive structure

    INTUITION: Merge succeeds only when the participant's behavior is
    INDISTINGUISHABLE across branches. If merge fails, the protocol is
    AMBIGUOUS for that participant.

    EXAMPLE:
      Branch A: Alice sends to Bob, then Carol sends to Bob
      Branch B: Alice sends to Bob, then Carol sends to Bob (same)
      => Merge succeeds for Carol (same behavior in both branches)

      Branch A: Alice sends to Bob, then Carol sends to Dave
      Branch B: Alice sends to Bob, then Carol receives from Eve
      => Merge FAILS for Carol (different behaviors)
*)

(**
 * Attempt to merge two local types.
 * Returns Some merged_type if compatible, None if incompatible.
 *
 * PROPERTIES:
 *   - Reflexive: merge_local l l = Some l
 *   - Symmetric: merge_local l1 l2 = merge_local l2 l1
 *   - Associative: merge is associative when defined
 *)
val merge_local : l1:local_type -> l2:local_type ->
    Tot (option local_type) (decreases l1)

(**
 * Merge two lists of labeled branches.
 * Used for merging LBranch types.
 *
 * The result contains all labels from both lists, with continuations
 * merged where labels overlap.
 *)
val merge_branch_lists : bs1:list (label & local_type) -> bs2:list (label & local_type) ->
    Tot (option (list (label & local_type))) (decreases bs1)

(**
 * Fold merge over a list of local types.
 * Used when merging multiple branch projections in GChoice.
 *
 * merge_fold (Some l) [l1, l2, l3] = l merge l1 merge l2 merge l3
 *)
val merge_fold : acc:option local_type -> ls:list local_type ->
    Tot (option local_type) (decreases ls)

(**
 * LEMMA: Merge is reflexive.
 *
 * Merging a type with itself always succeeds and returns the same type.
 * This is crucial for the base case of merge_fold.
 *)
val merge_local_refl : l:local_type ->
  Lemma (ensures merge_local l l == Some l)
        (decreases l)
        [SMTPat (merge_local l l)]

(** ============================================================================
    PARTICIPANT EXTRACTION
    ============================================================================

    Functions to extract the set of participants from a global type.
    Used for:
    - Checking well-formedness (all participants have defined projections)
    - Checking disjointness in GPar
    - Iterating over participants for batch projection
*)

(**
 * Extract all participants mentioned in a global type.
 * May contain duplicates (use unique_participants for deduplication).
 *
 * Includes both senders and receivers from all interactions.
 *)
val participants : g:global_type -> Tot (list participant) (decreases g)

(**
 * Extract participants from a list of branches.
 * Helper for participants on GChoice.
 *)
val participants_branches : branches:list (label & global_type) ->
    Tot (list participant) (decreases branches)

(**
 * Remove duplicates from a list while preserving first occurrence order.
 * Generic over any eqtype (type with decidable equality).
 *)
val dedup : #a:eqtype -> l:list a -> list a

(**
 * Get unique participants from a global type.
 * Equivalent to dedup (participants g).
 *)
val unique_participants : g:global_type -> list participant

(** ============================================================================
    PROJECTION: Global Type -> Local Type
    ============================================================================

    PROJECTION is the key operation of MPST. It extracts a participant's
    local view from the global protocol specification.

    DEFINITION (from brrr_lang_spec_v0.4.tex):

      (p -> q : T.G) |_r =
        if r = p then !<q,T>.(G|_r)
        else if r = q then ?<p,T>.(G|_r)
        else G|_r

      (p -> q : {l_i: G_i}) |_r =
        if r = p then +{l_i: G_i|_r}
        else if r = q then &{l_i: G_i|_r}
        else MERGE_i (G_i|_r)

      (mu X. G) |_r = mu X. (G|_r)
      X |_r = X
      end |_r = end

    PROJECTION MAY FAIL (returns None) when:
      - Merge fails for an uninvolved participant in GChoice
      - Recursive projection fails in a subterm

    CORRECTNESS PROPERTY (Session Fidelity):
    If project g p = Some l and process P has type l, then P correctly
    implements participant p's role in protocol g.

    ASSOCIATION RELATION (Scalas & Yoshida 2019):
    Instead of requiring G|_p = Gamma(s[p]) (equality), we use:
      G ~ Gamma iff forall p. G|_p <= Gamma(s[p]) (subtyping)
    This allows implementations to be MORE SPECIFIC than the global type.
*)

(**
 * Project a global type to a participant's local type.
 *
 * Returns Some local_type if projection succeeds.
 * Returns None if projection fails (incompatible branches for merge).
 *
 * GUARANTEE: If project g p = Some l, then l correctly represents p's
 * required behavior to participate in protocol g.
 *)
val project : g:global_type -> p:participant ->
    Tot (option local_type) (decreases g)

(**
 * Project a list of branches to a participant.
 * Returns the projected branches if all succeed, None if any fails.
 *)
val project_branches : branches:list (label & global_type) -> p:participant ->
    Tot (option (list (label & local_type))) (decreases branches)

(** ============================================================================
    LOCAL TYPE TO SESSION TYPE CONVERSION
    ============================================================================

    Convert a local type to a binary session type by erasing participant
    information. This is useful for interfacing with binary session type
    systems or when only two participants are involved.

    The conversion loses information about WHO the communication partner is,
    keeping only WHAT is communicated.
*)

(**
 * Convert a local type to a binary session type.
 * Erases participant annotations, keeping only the communication structure.
 *
 * LSend p T L   -> STSend T (convert L)
 * LRecv p T L   -> STRecv T (convert L)
 * LSelect p bs  -> STSelect (convert each branch)
 * LBranch p bs  -> STBranch (convert each branch)
 * etc.
 *)
val local_to_session : l:local_type -> Tot session_type (decreases l)

(** ============================================================================
    FREE VARIABLES
    ============================================================================

    Functions to compute free type variables. A variable is FREE if it is
    not bound by an enclosing GRec/LRec.

    A type is CLOSED if it has no free variables.
    Closed types can be instantiated without additional context.
*)

(**
 * Compute free type variables in a global type.
 * Returns the list of variable names not bound by enclosing GRec.
 *)
val free_gvars : g:global_type -> Tot (list gtype_var) (decreases g)

(**
 * Compute free type variables in a local type.
 * Returns the list of variable names not bound by enclosing LRec.
 *)
val free_lvars : l:local_type -> Tot (list gtype_var) (decreases l)

(**
 * Check if a global type is closed (no free variables).
 *)
val is_closed_global : g:global_type -> bool

(**
 * Check if a local type is closed (no free variables).
 *)
val is_closed_local : l:local_type -> bool

(** ============================================================================
    CONTRACTIVITY (Guardedness)
    ============================================================================

    CONTRACTIVITY ensures recursive types are well-founded. A recursive type
    mu X. G is contractive if X is GUARDED in G, meaning every occurrence
    of X appears under at least one communication action.

    VALID (contractive):
      mu X. p->q:int.X         (X guarded by message)
      mu X. p->q:{ok:X, err:end}  (X guarded by choice)

    INVALID (not contractive):
      mu X. X                  (unguarded, infinite loop)
      mu X. mu Y. X            (X not guarded by any action)

    GUARDEDNESS is stronger than just "appears under binder":
      mu X. (mu Y. X)          (X appears but NOT guarded)

    The guardedness check ensures that unfolding a recursive type always
    makes progress - we can't infinitely unfold without doing communication.
*)

(**
 * Check if variable x appears free in global type g.
 * Does not count bound occurrences under GRec with the same variable.
 *)
val var_appears_in_global : x:gtype_var -> g:global_type -> Tot bool (decreases g)

(**
 * Check if variable x is GUARDED in global type g.
 * x is guarded if every free occurrence appears under a communication action
 * (GMsg, GChoice, or GDeleg).
 *
 * FORMAL DEFINITION:
 *   guarded(x, GMsg _ _ _ G) = true AND guarded(x, G)
 *   guarded(x, GChoice _ _ bs) = true AND all branches guarded
 *   guarded(x, GDeleg _ _ G1 G2) = guarded(x, G1) AND guarded(x, G2)
 *   guarded(x, GRec y G) = if x = y then true else guarded(x, G)
 *   guarded(x, GVar y) = if x = y then FALSE else true
 *   guarded(x, GEnd) = true
 *   guarded(x, GPar G1 G2) = guarded(x, G1) AND guarded(x, G2)
 *)
val is_guarded_global : x:gtype_var -> g:global_type -> Tot bool (decreases g)

(**
 * Check if variable x is guarded in local type l.
 * Analogous to is_guarded_global but for local types.
 *)
val is_guarded_local : x:gtype_var -> l:local_type -> Tot bool (decreases l)

(**
 * Check if a global type is contractive.
 * A type is contractive if all recursively bound variables are guarded.
 *
 * contractive(mu X. G) = is_guarded_global X G AND contractive(G)
 *)
val is_contractive_global : g:global_type -> bool

(**
 * Check if a local type is contractive.
 * Analogous to is_contractive_global.
 *)
val is_contractive_local : l:local_type -> bool

(** ============================================================================
    WELL-FORMEDNESS PREDICATES
    ============================================================================

    A global type is WELL-FORMED if it satisfies all structural requirements
    for a valid protocol. Well-formedness is a prerequisite for the safety
    guarantees of MPST.

    WELL-FORMEDNESS CONDITIONS (from brrr_lang_spec_v0.4.tex):

    1. DISTINCT ROLES: sender <> receiver in all interactions
    2. NON-EMPTY CHOICES: GChoice must have at least one branch
    3. ALL PROJECTABLE: projection must succeed for all participants
    4. DISJOINT PARALLEL: GPar branches must have disjoint participant sets
    5. CONTRACTIVE: all recursive types must be contractive
    6. CLOSED: no free type variables (optional - some systems allow open types)
*)

(**
 * Check that sender and receiver are distinct in all interactions.
 * Returns false if any GMsg, GChoice, or GDeleg has sender = receiver.
 *
 * RATIONALE: Self-communication is meaningless in a distributed protocol.
 *)
val distinct_roles : g:global_type -> bool

(**
 * Check that all GChoice constructors have at least one branch.
 * Empty choices are ill-formed (nothing to choose).
 *)
val nonempty_choices : g:global_type -> bool

(**
 * Check that projection succeeds for all participants.
 * This is the key "projectability" condition from Honda et al.
 *
 * If this fails, the protocol is ambiguous for some participant.
 *)
val all_projectable : g:global_type -> bool

(**
 * Check that parallel composition has disjoint participant sets.
 * In GPar G1 G2, participants(G1) and participants(G2) must not overlap.
 *
 * RATIONALE: Overlapping participants would have ambiguous behavior
 * (which branch to follow?).
 *)
val disjoint_parallel_participants : g:global_type -> bool

(**
 * MAIN WELL-FORMEDNESS PREDICATE.
 *
 * Combines all well-formedness checks:
 *   - distinct_roles
 *   - nonempty_choices
 *   - all_projectable
 *   - disjoint_parallel_participants
 *   - is_contractive_global
 *
 * A well-formed global type guarantees:
 *   - Projection succeeds for all participants
 *   - No structural anomalies
 *   - Communication safety (with appropriate process typing)
 *)
val well_formed_global : g:global_type -> bool

(** ============================================================================
    DEADLOCK FREEDOM
    ============================================================================

    IMPORTANT: Well-formedness alone does NOT guarantee deadlock freedom
    in asynchronous settings. This is a key correction to Honda 2008.

    Example of well-formed but potentially deadlocking protocol:
      A -> B : int. B -> C : int. C -> A : int. end

    Under asynchronous semantics with message reordering, this can deadlock.

    DEADLOCK FREEDOM APPROACHES:

    1. DEPENDENCY GRAPH ANALYSIS (implemented here):
       Build a graph of communication dependencies. If acyclic, no deadlock.

    2. PRIORITY-BASED TYPING (Kobayashi, Padovani):
       Assign priorities to actions. Require consistent ordering.

    3. SYNCHRONOUS SEMANTICS:
       If all communications are synchronous (blocking), deadlock is detectable.

    We implement a simple acyclicity check on the dependency graph.
*)

(** An edge in the dependency graph: (sender, receiver) *)
type dep_edge = participant & participant

(** The dependency graph: list of directed edges *)
type dep_graph = list dep_edge

(**
 * Build the dependency graph from a global type.
 * Each message/choice/delegation creates an edge from sender to receiver.
 *)
val build_dep_graph : g:global_type -> dep_graph

(**
 * Check if a dependency graph is acyclic.
 * Uses standard cycle detection (e.g., topological sort).
 *)
val is_acyclic : g:dep_graph -> bool

(**
 * Check if a global type is deadlock-free.
 * Currently: well-formed AND acyclic dependency graph.
 *
 * NOTE: This is a SUFFICIENT but not NECESSARY condition.
 * Some protocols with cycles may still be deadlock-free due to
 * message ordering constraints not captured here.
 *)
val is_deadlock_free_global : g:global_type -> bool

(** ============================================================================
    COMMUNICATION SAFETY PREDICATES
    ============================================================================

    Helper predicates for analyzing local types.
    Used in proofs about dual projections and communication compatibility.
*)

(** Check if a local type starts with a send action. *)
val is_send_type : l:local_type -> bool

(** Check if a local type starts with a receive action. *)
val is_recv_type : l:local_type -> bool

(** Extract the target participant from a send type. Returns None if not a send. *)
val send_target : l:local_type -> option participant

(** Extract the source participant from a receive type. Returns None if not a receive. *)
val recv_source : l:local_type -> option participant

(** ============================================================================
    DUAL LOCAL TYPES
    ============================================================================

    In binary session types, duality is simple: send is dual to receive.
    In multiparty session types, we check that two participants' projections
    are COMPATIBLE for their direct communication.

    For participants p and q who communicate directly:
      - When p sends to q, p's type has LSend q and q's type has LRecv p
      - Payload types must match
      - Continuations must be compatible
*)

(**
 * Check if two local types are dual with respect to participants p and q.
 *
 * l1 is p's local type, l2 is q's local type.
 * They are dual if:
 *   - When l1 = LSend q T L1', l2 = LRecv p T L2' (and continuations compatible)
 *   - When l1 = LRecv q T L1', l2 = LSend p T L2' (and continuations compatible)
 *   - Similar for select/branch
 *)
val are_dual_wrt : l1:local_type -> l2:local_type -> p:participant -> q:participant -> bool

(** ============================================================================
    KEY LEMMAS - Projection Properties
    ============================================================================

    These lemmas establish fundamental properties of the projection operation.
    They are essential for proving communication safety and session fidelity.

    PROOF METHODOLOGY:
    Most lemmas proceed by structural induction on the global type,
    with case analysis on the participant's role (sender, receiver, other).
*)

(**
 * LEMMA: Projection of message sender yields a send type.
 *
 * When projecting GMsg sender receiver ty cont to the sender,
 * the result is LSend receiver ty (projected continuation).
 *
 * PRECONDITIONS:
 *   - sender <> receiver (distinct roles)
 *   - continuation projects successfully
 *
 * POSTCONDITIONS:
 *   - Projection succeeds (Some)
 *   - Result is a send type (is_send_type = true)
 *   - Send target is the receiver (send_target = Some receiver)
 *)
val projection_msg_sender_is_send : sender:participant -> receiver:participant ->
  ty:brrr_type -> cont:global_type ->
  Lemma (requires sender <> receiver /\ Some? (project cont sender))
        (ensures (match project (GMsg sender receiver ty cont) sender with
                  | Some l -> is_send_type l = true /\ send_target l = Some receiver
                  | None -> False))

(**
 * LEMMA: Projection of message receiver yields a receive type.
 *
 * Dual to projection_msg_sender_is_send.
 *)
val projection_msg_receiver_is_recv : sender:participant -> receiver:participant ->
  ty:brrr_type -> cont:global_type ->
  Lemma (requires sender <> receiver /\ Some? (project cont receiver))
        (ensures (match project (GMsg sender receiver ty cont) receiver with
                  | Some l -> is_recv_type l = true /\ recv_source l = Some sender
                  | None -> False))

(**
 * LEMMA: Projection of choice sender yields a select type.
 *
 * When projecting GChoice sender receiver branches to the sender,
 * the result is LSelect receiver (projected branches).
 *)
val projection_choice_sender_is_select : sender:participant -> receiver:participant ->
  branches:list (label & global_type) ->
  Lemma (requires sender <> receiver /\ Some? (project_branches branches sender))
        (ensures (match project (GChoice sender receiver branches) sender with
                  | Some l -> is_send_type l = true /\ send_target l = Some receiver
                  | None -> False))

(**
 * LEMMA: Projection of choice receiver yields a branch type.
 *
 * Dual to projection_choice_sender_is_select.
 *)
val projection_choice_receiver_is_branch : sender:participant -> receiver:participant ->
  branches:list (label & global_type) ->
  Lemma (requires sender <> receiver /\ Some? (project_branches branches receiver))
        (ensures (match project (GChoice sender receiver branches) receiver with
                  | Some l -> is_recv_type l = true /\ recv_source l = Some sender
                  | None -> False))

(** ============================================================================
    KEY LEMMAS - Well-Formedness Properties
    ============================================================================

    These lemmas establish that well-formed global types have nice properties.
*)

(**
 * LEMMA: Well-formed global types are projectable to all participants.
 *
 * This is a key soundness property: if a protocol is well-formed,
 * every participant has a well-defined local type.
 *
 * The SMTPat allows Z3 to use this fact automatically.
 *)
val wellformed_implies_projectable : g:global_type ->
  Lemma (requires well_formed_global g = true)
        (ensures all_projectable g = true)
        [SMTPat (well_formed_global g)]

(**
 * LEMMA: Deadlock freedom implies projectability.
 *
 * A stronger property: if a protocol is both well-formed and has an
 * acyclic dependency graph, it is guaranteed to be projectable.
 *
 * NOTE: This lemma combines the safety properties but does NOT
 * prove absence of deadlocks (that requires runtime semantics).
 *)
val deadlock_freedom : g:global_type ->
  Lemma (requires well_formed_global g = true /\ is_deadlock_free_global g = true)
        (ensures all_projectable g = true)

(** ============================================================================
    HELPER PREDICATES
    ============================================================================
*)

(**
 * Check if two participants directly interact in a global type.
 * "Directly interact" means one sends a message to the other or
 * one makes a choice that the other branches on.
 *)
val direct_interaction : g:global_type -> p:participant -> q:participant -> bool

(** ============================================================================
    KEY LEMMAS - Projection Consistency
    ============================================================================

    PROJECTION CONSISTENCY (Honda et al. 2008, Theorem 1):
    If a global type is well-formed and two participants directly interact,
    their projections are compatible (dual at the interaction points).

    This is the key lemma for COMMUNICATION SAFETY:
    - What p sends is what q expects to receive
    - Payload types match
    - Continuations are compatible
*)

(**
 * LEMMA: Direct interaction implies both projections exist.
 *
 * If p and q directly interact in a well-formed global type,
 * both project(g, p) and project(g, q) are defined (Some).
 *)
val projection_preserves_comm : g:global_type -> p:participant -> q:participant ->
  Lemma (requires well_formed_global g = true /\
                  direct_interaction g p q = true /\
                  p <> q)
        (ensures Some? (project g p) /\ Some? (project g q))

(**
 * LEMMA: Projection consistency for interacting participants.
 *
 * A corollary of projection_preserves_comm: if p and q interact,
 * both have defined projections.
 *)
val projection_consistency : g:global_type -> p:participant -> q:participant ->
  Lemma (requires well_formed_global g = true /\
                  direct_interaction g p q = true /\
                  p <> q)
        (ensures (match project g p, project g q with
                  | Some _, Some _ -> true
                  | _, _ -> false))

(** ============================================================================
    VALIDATION FUNCTIONS
    ============================================================================

    Convenience functions for validating global types and extracting
    all projections at once.
*)

(**
 * Validate a global type and return all projections.
 *
 * If the type is well-formed and all projections succeed, returns
 * Some [(p1, L1), (p2, L2), ...] for all participants.
 *
 * Returns None if validation or any projection fails.
 *)
val validate_and_project : g:global_type -> option (list (participant & local_type))

(**
 * Full validation of a global type.
 *
 * Checks:
 *   - well_formed_global
 *   - is_contractive_global
 *   - is_closed_global
 *
 * Returns true iff all checks pass.
 *)
val full_validate : g:global_type -> bool

(** ============================================================================
    ADDITIONAL LEMMAS - Projection Soundness
    ============================================================================

    These lemmas establish deeper properties of projection, forming the
    foundation for the SESSION FIDELITY theorem.
*)

(**
 * LEMMA: Projection preserves structural correspondence.
 *
 * The structure of the projected local type reflects the participant's
 * role in the global type:
 *   - GMsg sender -> LSend (if participant is sender)
 *   - GMsg receiver -> LRecv (if participant is receiver)
 *   - GChoice sender -> LSelect
 *   - GChoice receiver -> LBranch
 *   - GDeleg delegator -> LThrow
 *   - GDeleg receiver -> LCatch
 *   - GRec/GVar/GEnd -> corresponding local constructors
 *
 * The SMTPat allows Z3 to reason about projection results automatically.
 *)
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

(**
 * LEMMA: Dual projections for message interaction.
 *
 * When sender sends to receiver, their projections are dual:
 *   - sender has LSend receiver ty (...)
 *   - receiver has LRecv sender ty (...)
 *   - Payload types are EQUAL (not just compatible)
 *
 * This establishes TYPE SAFETY for message passing.
 *
 * The SMTPat triggers on both projections simultaneously.
 *)
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

(**
 * LEMMA: Dual projections for delegation interaction.
 *
 * Similar to dual_projection_msg but for session delegation.
 * Establishes that delegator throws what receiver catches.
 *)
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

(**
 * LEMMA: Guardedness is preserved by projection.
 *
 * If variable x is guarded in global type g, and projection to p succeeds,
 * then x is guarded in the projected local type.
 *
 * This ensures contractivity is preserved through projection.
 *)
val guardedness_preserved : g:global_type -> p:participant -> x:gtype_var ->
  Lemma (requires is_guarded_global x g = true /\ Some? (project g p))
        (ensures is_guarded_local x (Some?.v (project g p)) = true)
        (decreases g)

(**
 * LEMMA: Contractiveness is preserved by projection.
 *
 * If g is contractive and projection to p succeeds, the result is contractive.
 *
 * Corollary of guardedness_preserved for all bound variables.
 *)
val contractiveness_preserved : g:global_type -> p:participant ->
  Lemma (requires is_contractive_global g = true /\ Some? (project g p))
        (ensures is_contractive_local (Some?.v (project g p)) = true)
        (decreases g)

(**
 * LEMMA: Projection of disjoint GPar follows the correct branch.
 *
 * If p participates in 'left' but not 'right' (disjoint parallel),
 * then projecting GPar to p is the same as projecting 'left' to p.
 *)
val gpar_projection_disjoint : left:global_type -> right:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar left right) = true /\
                  List.Tot.mem p (participants left) = true /\
                  List.Tot.mem p (participants right) = false)
        (ensures project (GPar left right) p == project left p)

(**
 * LEMMA: GPar projection (left branch) with SMT pattern.
 *
 * Variant of gpar_projection_disjoint with SMTPat for automatic application.
 *)
val project_gpar_disjoint : g1:global_type -> g2:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar g1 g2) = true /\
                  List.Tot.mem p (participants g1) = true)
        (ensures project (GPar g1 g2) p == project g1 p)
        [SMTPat (project (GPar g1 g2) p)]

(**
 * LEMMA: GPar projection (right branch) with SMT pattern.
 *
 * Dual of project_gpar_disjoint for when p is in the right branch.
 *)
val project_gpar_disjoint_right : g1:global_type -> g2:global_type -> p:participant ->
  Lemma (requires disjoint_parallel_participants (GPar g1 g2) = true /\
                  List.Tot.mem p (participants g2) = true)
        (ensures project (GPar g1 g2) p == project g2 p)
        [SMTPat (project (GPar g1 g2) p)]

(**
 * LEMMA: Well-formedness implies projection exists for all participants.
 *
 * KEY SOUNDNESS PROPERTY: Every participant in a well-formed protocol
 * has a well-defined local type.
 *
 * Dual SMTPat triggers ensure Z3 can use this in both directions.
 *)
val wellformed_all_projections : g:global_type -> p:participant ->
  Lemma (requires well_formed_global g = true /\
                  List.Tot.mem p (unique_participants g) = true)
        (ensures Some? (project g p))
        [SMTPat (well_formed_global g); SMTPat (project g p)]

(** ============================================================================
    EXAMPLE PROTOCOLS
    ============================================================================

    Canonical example protocols demonstrating MPST features.
    These serve as both documentation and test cases.
*)

(**
 * TWO-BUYER PROTOCOL (classic MPST example from Honda et al. 2008)
 *
 * Scenario: Two buyers (Buyer1, Buyer2) purchase an item from Seller.
 *
 * Protocol:
 *   1. Buyer1 -> Seller: book title (string)
 *   2. Seller -> Buyer1: price (int)
 *   3. Seller -> Buyer2: price (int)
 *   4. Buyer1 -> Buyer2: proposed share (int)
 *   5. Buyer2 -> Seller: {
 *        ok: Buyer2 -> Seller: address (string). end
 *        quit: end
 *      }
 *
 * This protocol demonstrates:
 *   - Multi-party communication (3 participants)
 *   - Sequential message passing
 *   - Labeled choice (Buyer2 decides)
 *   - Merge requirement (Buyer1 not involved in final choice)
 *)
val two_buyer_protocol : global_type

(**
 * PING-PONG PROTOCOL (simple recursive protocol)
 *
 * Scenario: Client and Server exchange ping/pong messages forever.
 *
 * Protocol:
 *   mu X. Client -> Server: ping. Server -> Client: pong. X
 *
 * Demonstrates recursive protocols.
 *)
val ping_pong_protocol : global_type

(**
 * STREAM PROTOCOL (data streaming)
 *
 * Scenario: Producer streams data to Consumer until done.
 *
 * Protocol:
 *   mu X. Producer -> Consumer: {
 *     data: Producer -> Consumer: value. X
 *     end: end
 *   }
 *
 * Demonstrates choice within recursion.
 *)
val stream_protocol : global_type

(**
 * PARALLEL STREAMS PROTOCOL
 *
 * Scenario: Two independent producer-consumer pairs running in parallel.
 *
 * Protocol:
 *   (Producer1 -> Consumer1: ...) || (Producer2 -> Consumer2: ...)
 *
 * Demonstrates GPar with disjoint participants.
 *)
val parallel_streams_protocol : global_type

(**
 * PARALLEL FANOUT PROTOCOL
 *
 * Scenario: Dispatcher sends to multiple workers in parallel branches.
 *
 * Demonstrates more complex parallel structure.
 *)
val parallel_fanout_protocol : global_type

(** ============================================================================
    SESSION DELEGATION EXAMPLES
    ============================================================================

    Examples demonstrating the GDeleg constructor for higher-order sessions.
*)

(**
 * CLIENT SESSION GLOBAL (used in delegation examples)
 *
 * A simple request-response session between Client and Handler.
 *)
val client_session_global : global_type

(**
 * FTP DELEGATION PROTOCOL
 *
 * Scenario: FTP server delegates file transfer to worker process.
 *
 * Protocol:
 *   1. Client -> Server: filename
 *   2. Server delegates client session to Worker
 *   3. Worker -> Client: file data
 *   4. Worker -> Server: completion status
 *
 * Demonstrates session delegation with GDeleg.
 *)
val ftp_delegation_protocol : global_type

(**
 * WORKER POOL PROTOCOL
 *
 * Scenario: Load balancer delegates client sessions to available workers.
 *
 * More complex delegation example with multiple potential recipients.
 *)
val worker_pool_protocol : global_type

(**
 * CLIENT SESSION LOCAL TYPE (for Client participant)
 *
 * The local type that a Client process should implement.
 *)
val client_session_type : local_type

(**
 * FTP WORKER LOCAL TYPE
 *
 * Local type for the Worker in ftp_delegation_protocol.
 * Includes LCatch to receive the delegated session.
 *)
val ftp_worker_local : local_type

(**
 * FTP SERVER LOCAL TYPE
 *
 * Local type for the Server in ftp_delegation_protocol.
 * Includes LThrow to delegate the session to Worker.
 *)
val ftp_server_local : local_type
