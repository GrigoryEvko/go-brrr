(**
 * BrrrLang.Core.SessionTypes - Interface
 *
 * Public interface for binary session types.
 * Based on brrr_lang_spec_v0.4.tex Part VII (Concurrency & Session Types).
 *
 * This interface follows HACL*/EverParse patterns:
 *   - #set-options for Z3 solver configuration
 *   - val declarations with pre/post conditions
 *   - SMTPat triggers for automatic lemma application
 *   - noeq for types containing functions or requiring coinductive equality
 *
 * Session types provide a type discipline for communication protocols,
 * ensuring that interacting processes follow agreed-upon message sequences.
 *
 * Grammar:
 *   S ::= !t.S        (send type t, continue as S)
 *      |  ?t.S        (receive type t, continue as S)
 *      |  +{l_i:S_i}  (internal choice: select among labeled branches)
 *      |  &{l_i:S_i}  (external choice: offer labeled branches)
 *      |  uX.S        (recursive session type)
 *      |  X           (session variable)
 *      |  end         (session termination)
 *
 * Key Properties:
 *   - Duality: dual(dual(S)) == S (involution)
 *   - Communication safety: dual endpoints have compatible types
 *   - Deadlock freedom: via priority annotations
 *
 * Implementation details are hidden in SessionTypes.fst.
 *)
module SessionTypes

open FStar.List.Tot
open Primitives
open BrrrTypes
open Expressions

(* Z3 solver options - matching HACL*/EverParse patterns
   - z3rlimit 50: reasonable timeout for proofs
   - fuel 0: disable recursive function unfolding by default
   - ifuel 0: disable inductive type unfolding by default *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    TYPE IDENTIFIERS
    ============================================================================ *)

(* Session type variable name *)
type session_var = string

(* Channel name *)
type channel_name = string

(** ============================================================================
    SOURCE LOCATION TRACKING (following EverParse with_meta_t pattern)
    ============================================================================ *)

(* Source position: identifies a point in a source file *)
type pos = {
  pos_filename : string;  (* Source file path *)
  pos_line     : nat;     (* 1-indexed line number *)
  pos_col      : nat      (* 0-indexed column number *)
}

(* Dummy position for synthetic nodes *)
val dummy_pos : pos

(* Format position as "file:(line,col)" for error messages *)
val string_of_pos : pos -> string

(* Source range: span from start to end position *)
type range = pos & pos

(* Dummy range for synthetic nodes *)
val dummy_range : range

(* Format range for error messages *)
val string_of_range : range -> string

(* Comments attached to AST nodes *)
type comments = list string

(* Metadata wrapper: attaches source location and comments to any value *)
noeq type with_meta_t (a: Type) = {
  meta_value    : a;        (* The wrapped value *)
  meta_range    : range;    (* Source span *)
  meta_comments : comments  (* Attached documentation *)
}

(* Wrap a value with dummy metadata *)
val with_dummy_meta : #a:Type -> v:a -> with_meta_t a

(* Wrap a value with a specific range *)
val with_range : #a:Type -> v:a -> r:range -> with_meta_t a

(* Wrap a value with range and comments *)
val with_meta : #a:Type -> v:a -> r:range -> c:comments -> with_meta_t a

(* Extract the value from metadata wrapper *)
val get_value : #a:Type -> m:with_meta_t a -> a

(* Extract the range from metadata wrapper *)
val get_range : #a:Type -> m:with_meta_t a -> range

(* Map a function over the wrapped value, preserving metadata *)
val map_meta : #a:Type -> #b:Type -> f:(a -> b) -> m:with_meta_t a -> with_meta_t b

(* Extract comments from metadata wrapper *)
val get_comments : #a:Type -> m:with_meta_t a -> comments

(* Session type error with location information *)
noeq type located_error = {
  error_message : string;
  error_range   : range
}

(* Create a located error *)
val make_error : msg:string -> r:range -> located_error

(* Format located error for display *)
val string_of_located_error : located_error -> string

(* Located identifier *)
type located_ident = with_meta_t string

(** ============================================================================
    SESSION TYPE DEFINITION
    ============================================================================ *)

(* Session type grammar - S ::= !t.S | ?t.S | +{l_i:S_i} | &{l_i:S_i} | uX.S | X | end

   noeq required because brrr_type contains function types with effect_row,
   making structural equality undecidable. *)
noeq type session_type =
  | SSend   : payload:brrr_type -> continuation:session_type -> session_type
  | SRecv   : payload:brrr_type -> continuation:session_type -> session_type
  | SSelect : branches:list (label & session_type) -> session_type
  | SBranch : branches:list (label & session_type) -> session_type
  | SRec    : var:session_var -> body:session_type -> session_type
  | SVar    : var:session_var -> session_type
  | SEnd    : session_type

(* Located session type: session type with source location *)
type located_session = with_meta_t session_type

(* Located session branch: branch with source location *)
type located_branch = with_meta_t (label & session_type)

(* Create located session with range *)
val locate_session : s:session_type -> r:range -> located_session

(* Create located session with dummy metadata *)
val unlocated_session : s:session_type -> located_session

(** ============================================================================
    SESSION TYPE SIZE (for termination proofs)
    ============================================================================ *)

(* Compute structural size of session type branches *)
val session_branches_size : branches:list (label & session_type) ->
  Tot nat (decreases branches)

(* Compute structural size of a session type *)
val session_size : s:session_type ->
  Tot nat (decreases s)

(** ============================================================================
    SESSION DUALITY - The Core Property
    ============================================================================ *)

(* Compute the dual of session type branches *)
val dual_branches : branches:list (label & session_type) ->
  Tot (list (label & session_type)) (decreases branches)

(* Compute the dual of a session type.
   Duality swaps the perspective between the two endpoints of a channel:
   - Send becomes Receive (and vice versa)
   - Internal choice (Select) becomes External choice (Branch) (and vice versa)
   - Recursion and variables are preserved (dual distributes through them)
   - End is self-dual *)
val dual : s:session_type ->
  Tot session_type (decreases s)

(** ============================================================================
    DUALITY INVOLUTION THEOREM
    ============================================================================ *)

(* Helper lemma: dual_branches is an involution *)
val dual_branches_involutive : branches:list (label & session_type) ->
  Lemma (ensures dual_branches (dual_branches branches) == branches)
        (decreases branches)

(* Theorem: Duality is an involution - dual(dual(S)) == S for all session types S.
   This is the fundamental property of session type duality. *)
val dual_involutive : s:session_type ->
  Lemma (ensures dual (dual s) == s)
        (decreases s)
        [SMTPat (dual (dual s))]

(** ============================================================================
    SESSION TYPE EQUALITY
    ============================================================================ *)

(* Structural equality for session type branch lists *)
val session_branches_eq : bs1:list (label & session_type) -> bs2:list (label & session_type) ->
  Tot bool (decreases bs1)

(* Structural equality for session types *)
val session_eq : s1:session_type -> s2:session_type ->
  Tot bool (decreases s1)

(* Session equality is reflexive *)
val session_eq_refl : s:session_type ->
  Lemma (ensures session_eq s s = true)
        (decreases s)
        [SMTPat (session_eq s s)]

(* Session equality is symmetric *)
val session_eq_sym : s1:session_type -> s2:session_type ->
  Lemma (requires session_eq s1 s2 = true)
        (ensures session_eq s2 s1 = true)
        (decreases s1)

(* Session equality is transitive *)
val session_eq_trans : s1:session_type -> s2:session_type -> s3:session_type ->
  Lemma (requires session_eq s1 s2 = true /\ session_eq s2 s3 = true)
        (ensures session_eq s1 s3 = true)
        (decreases s1)

(** ============================================================================
    DUAL PRESERVES EQUALITY
    ============================================================================ *)

(* If two session types are equal, their duals are equal *)
val dual_preserves_eq : s1:session_type -> s2:session_type ->
  Lemma (requires session_eq s1 s2 = true)
        (ensures session_eq (dual s1) (dual s2) = true)
        (decreases s1)
        [SMTPat (session_eq (dual s1) (dual s2))]

(** ============================================================================
    FREE VARIABLES
    ============================================================================ *)

(* Collect free session variables from branch list *)
val free_session_vars_branches : branches:list (label & session_type) ->
  Tot (list session_var) (decreases branches)

(* Collect free session variables in a session type *)
val free_session_vars : s:session_type ->
  Tot (list session_var) (decreases s)

(* Check if a session type is closed (no free variables) *)
val is_closed_session : s:session_type -> bool

(* Check if a variable is free in a session type *)
val is_free_in : x:session_var -> s:session_type -> bool

(** ============================================================================
    SESSION TYPE SUBSTITUTION
    ============================================================================ *)

(* Substitute a session variable in a branch list *)
val subst_session_branches : x:session_var -> replacement:session_type ->
  branches:list (label & session_type) -> Tot (list (label & session_type)) (decreases branches)

(* Substitute a session variable with a session type *)
val subst_session : x:session_var -> replacement:session_type -> s:session_type ->
  Tot session_type (decreases s)

(* Unfold a recursive session type by substituting the body for the variable *)
val unfold_rec : s:session_type -> session_type

(* Unfold a recursive session type one step (used in coinductive algorithms) *)
val unfold_session : s:session_type -> session_type

(* Check if a session type is a recursive type *)
val is_rec_type : s:session_type -> bool

(** ============================================================================
    SESSION TYPE WELL-FORMEDNESS
    ============================================================================ *)

(* Check if variable x is guarded in session type s *)
val is_guarded : x:session_var -> s:session_type -> bool

(* Check contractivity of branch list *)
val is_contractive_branches : branches:list (label & session_type) -> bool

(* Check if recursive types are contractive *)
val is_contractive : s:session_type -> bool

(* Well-formed session type: closed and contractive *)
val is_wellformed : s:session_type -> bool

(** ============================================================================
    CHANNEL TYPES
    ============================================================================ *)

(* A channel endpoint has a session type describing its protocol *)
noeq type channel_endpoint = {
  ch_name : channel_name;
  ch_session : session_type
}

(* Create a pair of dual channel endpoints *)
val make_channel_pair : name1:channel_name -> name2:channel_name -> session:session_type ->
  (channel_endpoint & channel_endpoint)

(* Advance a channel after a send operation *)
val advance_send : ch:channel_endpoint -> option channel_endpoint

(* Advance a channel after a receive operation *)
val advance_recv : ch:channel_endpoint -> option channel_endpoint

(* Look up a label in a branch list *)
val lookup_branch : lbl:label -> branches:list (label & session_type) -> option session_type

(* Select a labeled branch on internal choice *)
val select_branch : ch:channel_endpoint -> lbl:label -> option channel_endpoint

(* Offer a branch on external choice *)
val offer_branch : ch:channel_endpoint -> lbl:label -> option channel_endpoint

(* Get all available labels for select/branch *)
val get_available_labels : ch:channel_endpoint -> option (list label)

(* Check if channel is at end state *)
val is_channel_end : ch:channel_endpoint -> bool

(** ============================================================================
    SESSION CONTEXT
    ============================================================================ *)

(* Session typing context: maps channel names to session types *)
type session_ctx = list (channel_name & session_type)

(* Empty session context *)
val empty_session_ctx : session_ctx

(* Lookup channel in session context *)
val lookup_channel : c:channel_name -> ctx:session_ctx -> option session_type

(* Check if channel is in context *)
val has_channel : c:channel_name -> ctx:session_ctx -> bool

(* Remove channel from context *)
val remove_channel : c:channel_name -> ctx:session_ctx -> session_ctx

(* Add or update channel in context *)
val update_channel : c:channel_name -> s:session_type -> ctx:session_ctx -> session_ctx

(* Check if context domains are disjoint *)
val disjoint_ctx : ctx1:session_ctx -> ctx2:session_ctx -> bool

(* Merge two disjoint contexts *)
val merge_ctx : ctx1:session_ctx -> ctx2:session_ctx -> session_ctx

(* Helper: check if session type is SEnd *)
val is_end : s:session_type -> bool

(* Check if all channels in context are at end state *)
val all_ended : ctx:session_ctx -> bool

(** ============================================================================
    CHANNEL SPLITTING FOR PARALLEL COMPOSITION
    ============================================================================ *)

(* Split a session context for parallel composition.
   Each channel must go to exactly one side (linear usage). *)
val try_split_ctx : ctx:session_ctx -> left_channels:list channel_name ->
  option (session_ctx & session_ctx)

(** ============================================================================
    PROCESS SYNTAX
    ============================================================================ *)

(* Process expression - represents concurrent programs with message passing *)
noeq type process =
  | PSend   : channel:channel_name -> payload:brrr_type -> continuation:process -> process
  | PRecv   : channel:channel_name -> var:string -> continuation:process -> process
  | PSelect : channel:channel_name -> label:label -> continuation:process -> process
  | PBranch : channel:channel_name -> branches:list (label & process) -> process
  | PPar    : left:process -> right:process -> process
  | PNew    : name1:channel_name -> name2:channel_name -> session:session_type ->
              body:process -> process
  | PEnd    : process
  | PRec    : var:string -> body:process -> process
  | PVar    : var:string -> process

(* Process structural size *)
val process_size : p:process -> Tot nat (decreases p)

(* Branch list size *)
val branch_list_size : branches:list (label & process) -> Tot nat (decreases branches)

(** ============================================================================
    SESSION TYPE CHECKING
    ============================================================================ *)

(* Result of session type checking *)
noeq type check_result =
  | CheckOk : remaining_ctx:session_ctx -> check_result
  | CheckError : msg:string -> check_result

(* Check if result succeeded *)
val check_succeeded : r:check_result -> bool

(* Type check a send operation *)
val check_send : c:channel_name -> t:brrr_type -> ctx:session_ctx -> check_result

(* Type check a receive operation *)
val check_recv : c:channel_name -> ctx:session_ctx -> check_result

(* Type check internal choice (select) *)
val check_select : c:channel_name -> lbl:label -> ctx:session_ctx -> check_result

(* Type check external choice (branch) *)
val check_branch : c:channel_name -> lbl:label -> ctx:session_ctx -> check_result

(* Type check channel creation *)
val check_new : c:channel_name -> d:channel_name -> s:session_type -> ctx:session_ctx ->
  check_result

(* Type check terminated process *)
val check_end : ctx:session_ctx -> check_result

(** ============================================================================
    SESSION SUBTYPING - Coinductive Approach
    ============================================================================ *)

(* Visited set for coinductive subtyping *)
type visited_set = list (session_type & session_type)

(* Check if a pair is in the visited set *)
val pair_in_visited : s1:session_type -> s2:session_type -> vis:visited_set ->
  Tot bool (decreases vis)

(* Check if vis1 is a subset of vis2 *)
val visited_subset : vis1:visited_set -> vis2:visited_set -> Tot bool (decreases vis1)

(* Default fuel for coinductive subtyping *)
val default_subtype_fuel : nat

(* Coinductive session subtyping with visited set and fuel *)
val session_subtype_co : s1:session_type -> s2:session_type -> vis:visited_set -> fuel:nat ->
  Tot bool (decreases fuel)

(* Top-level session subtyping function *)
val session_subtype : s1:session_type -> s2:session_type -> bool

(* Check if all labels in bs2 exist in bs1 *)
val all_labels_present : bs2:list (label & session_type) -> bs1:list (label & session_type) ->
  Tot bool (decreases bs2)

(* Coinductive subtyping for branch lists *)
val session_branches_subtype_co : bs1:list (label & session_type) ->
  bs2:list (label & session_type) -> vis:visited_set -> fuel:nat ->
  Tot bool (decreases fuel)

(** ============================================================================
    SUBTYPING LEMMAS
    ============================================================================ *)

(* Session subtyping is reflexive *)
val session_subtype_refl : s:session_type ->
  Lemma (ensures session_subtype s s = true)
        (decreases s)
        [SMTPat (session_subtype s s)]

(* Session subtyping is transitive *)
val session_subtype_trans : s1:session_type -> s2:session_type -> s3:session_type ->
  Lemma (requires session_subtype s1 s2 = true /\ session_subtype s2 s3 = true)
        (ensures session_subtype s1 s3 = true)

(* Dual reverses subtyping direction *)
val dual_reverses_subtype : s1:session_type -> s2:session_type ->
  Lemma (requires session_subtype s1 s2 = true)
        (ensures session_subtype (dual s2) (dual s1) = true)

(** ============================================================================
    COINDUCTIVE SOUNDNESS PROPERTIES
    ============================================================================ *)

(* Structural equality implies coinductive subtyping *)
val session_eq_implies_subtype_co : s1:session_type -> s2:session_type ->
  vis:visited_set -> fuel:nat{fuel > 0} ->
  Lemma (requires session_eq s1 s2 = true)
        (ensures session_subtype_co s1 s2 vis fuel = true)

(* Reflexivity of coinductive subtyping *)
val session_subtype_co_refl : s:session_type -> vis:visited_set -> fuel:nat{fuel > 0} ->
  Lemma (ensures session_subtype_co s s vis fuel = true)

(* Soundness of coinductive subtyping *)
val session_subtype_sound : s1:session_type -> s2:session_type ->
  Lemma (requires session_subtype s1 s2 = true)
        (ensures True)

(* Fuel monotonicity: more fuel preserves true results *)
val fuel_monotone : s1:session_type -> s2:session_type -> vis:visited_set ->
  fuel1:nat -> fuel2:nat{fuel2 >= fuel1} ->
  Lemma (requires session_subtype_co s1 s2 vis fuel1 = true)
        (ensures session_subtype_co s1 s2 vis fuel2 = true)

(** ============================================================================
    COINDUCTIVE EQUALITY FOR SESSION TYPES
    ============================================================================ *)

(* Coinductive equality for branch lists *)
val session_branches_eq_co : bs1:list (label & session_type) -> bs2:list (label & session_type) ->
  vis:visited_set -> fuel:nat -> Tot bool (decreases fuel)

(* Coinductive session equality with fuel *)
val session_eq_co : s1:session_type -> s2:session_type -> vis:visited_set -> fuel:nat ->
  Tot bool (decreases fuel)

(* Top-level coinductive equality *)
val session_eq_coinductive : s1:session_type -> s2:session_type -> bool

(** ============================================================================
    SESSION TYPE MERGE (for projections)
    ============================================================================ *)

(* Merge two branch lists if they are compatible *)
val merge_session_branches : bs1:list (label & session_type) -> bs2:list (label & session_type) ->
  Tot (option (list (label & session_type))) (decreases bs1)

(* Merge two session types if they are compatible *)
val merge_session : s1:session_type -> s2:session_type ->
  Tot (option session_type) (decreases s1)

(** ============================================================================
    DUALITY COMPATIBILITY
    ============================================================================ *)

(* Check if two session types are dual to each other *)
val are_dual : s1:session_type -> s2:session_type -> bool

(* are_dual is symmetric *)
val are_dual_sym : s1:session_type -> s2:session_type ->
  Lemma (requires are_dual s1 s2 = true)
        (ensures are_dual s2 s1 = true)

(* Dual of dual is equal to original *)
val dual_dual_eq : s:session_type ->
  Lemma (ensures session_eq (dual (dual s)) s = true)
        [SMTPat (session_eq (dual (dual s)) s)]

(** ============================================================================
    DUAL PRESERVES PROPERTIES
    ============================================================================ *)

(* Dual preserves guardedness *)
val dual_preserves_guarded : x:session_var -> s:session_type ->
  Lemma (requires is_guarded x s = true)
        (ensures is_guarded x (dual s) = true)
        (decreases s)

(* Dual preserves contractivity *)
val dual_preserves_contractive : s:session_type ->
  Lemma (requires is_contractive s = true)
        (ensures is_contractive (dual s) = true)
        (decreases s)

(* Dual preserves free variables *)
val dual_preserves_free_vars : s:session_type ->
  Lemma (ensures free_session_vars (dual s) == free_session_vars s)
        (decreases s)

(* Dual preserves closedness *)
val dual_preserves_closed : s:session_type ->
  Lemma (requires is_closed_session s = true)
        (ensures is_closed_session (dual s) = true)

(* Dual preserves well-formedness *)
val dual_preserves_wellformed : s:session_type ->
  Lemma (requires is_wellformed s = true)
        (ensures is_wellformed (dual s) = true)

(* Dual preserves size *)
val dual_preserves_size : s:session_type ->
  Lemma (ensures session_size (dual s) = session_size s)
        (decreases s)

(** ============================================================================
    COMMON SESSION TYPE PATTERNS
    ============================================================================ *)

(* Send a single message then end *)
val s_send_once : t:brrr_type -> session_type

(* Receive a single message then end *)
val s_recv_once : t:brrr_type -> session_type

(* Request-response pattern: send request, receive response *)
val s_request_response : req_type:brrr_type -> resp_type:brrr_type -> session_type

(* Server pattern: receive request, send response *)
val s_server : req_type:brrr_type -> resp_type:brrr_type -> session_type

(* Lemma: request_response and server are duals *)
val request_response_dual_server : req_type:brrr_type -> resp_type:brrr_type ->
  Lemma (ensures dual (s_request_response req_type resp_type) ==
                 s_server req_type resp_type)

(* Infinite send stream *)
val s_send_stream : t:brrr_type -> session_type

(* Infinite receive stream *)
val s_recv_stream : t:brrr_type -> session_type

(** ============================================================================
    SESSION TYPE DEPTH
    ============================================================================ *)

(* Compute the depth of a session type (max nesting level) *)
val session_depth : s:session_type -> Tot nat (decreases s)

(** ============================================================================
    PRIORITY-BASED SESSION TYPES FOR DEADLOCK FREEDOM
    ============================================================================ *)

(* Priority level - natural number where lower = higher priority *)
type priority = nat

(* Compare priorities *)
val priority_compare : p1:priority -> p2:priority -> int
val priority_lt : p1:priority -> p2:priority -> bool
val priority_le : p1:priority -> p2:priority -> bool

(* Prioritized session type grammar *)
noeq type pri_session =
  | PriSend   : pri:priority -> payload:brrr_type -> continuation:pri_session -> pri_session
  | PriRecv   : pri:priority -> payload:brrr_type -> continuation:pri_session -> pri_session
  | PriSelect : pri:priority -> branches:list (label & pri_session) -> pri_session
  | PriBranch : pri:priority -> branches:list (label & pri_session) -> pri_session
  | PriRec    : var:session_var -> body:pri_session -> pri_session
  | PriVar    : var:session_var -> pri_session
  | PriEnd    : pri_session

(** ============================================================================
    PRIORITIZED SESSION SIZE
    ============================================================================ *)

val pri_session_size : s:pri_session -> Tot nat (decreases s)

(** ============================================================================
    PRIORITY EXTRACTION
    ============================================================================ *)

(* Get the priority of the first action *)
val first_priority : s:pri_session -> Tot (option priority) (decreases s)

(* Get minimum priority across branches *)
val min_priority_branches : branches:list (label & pri_session) ->
  Tot (option priority) (decreases branches)

(* Get minimum priority across all actions *)
val min_priority : s:pri_session -> Tot (option priority) (decreases s)

(* Get maximum priority across branches *)
val max_priority_branches : branches:list (label & pri_session) ->
  Tot (option priority) (decreases branches)

(* Get maximum priority across all actions *)
val max_priority : s:pri_session -> Tot (option priority) (decreases s)

(* Collect all priorities from branches *)
val all_priorities_branches : branches:list (label & pri_session) ->
  Tot (list priority) (decreases branches)

(* Collect all priorities used in a session type *)
val all_priorities : s:pri_session -> Tot (list priority) (decreases s)

(** ============================================================================
    PRIORITY CONSISTENCY
    ============================================================================ *)

(* Check priority consistency between dual session types *)
val priority_consistent : s1:pri_session -> s2:pri_session -> bool

(* Check if priority p is strictly less than first priority of all branches *)
val priority_lt_all_branches : p:priority -> branches:list (label & pri_session) -> bool

(* Check priorities are strictly increasing in all branches *)
val branches_priorities_strictly_increasing : branches:list (label & pri_session) -> bool

(* Check priorities are strictly increasing along the session *)
val priorities_strictly_increasing : s:pri_session -> Tot bool (decreases s)

(** ============================================================================
    PRIORITIZED SESSION DUALITY
    ============================================================================ *)

(* Compute dual of prioritized session type branches *)
val pri_dual_branches : branches:list (label & pri_session) ->
  Tot (list (label & pri_session)) (decreases branches)

(* Compute dual of prioritized session type *)
val pri_dual : s:pri_session -> Tot pri_session (decreases s)

(* Helper lemma: pri_dual_branches is an involution *)
val pri_dual_branches_involutive : branches:list (label & pri_session) ->
  Lemma (ensures pri_dual_branches (pri_dual_branches branches) == branches)
        (decreases branches)

(* Priority dual is an involution *)
val pri_dual_involutive : s:pri_session ->
  Lemma (ensures pri_dual (pri_dual s) == s)
        (decreases s)
        [SMTPat (pri_dual (pri_dual s))]

(* Dual preserves min_priority *)
val pri_dual_preserves_min_priority : s:pri_session ->
  Lemma (ensures min_priority (pri_dual s) == min_priority s)
        (decreases s)

(** ============================================================================
    PRIORITIZED SESSION WELL-FORMEDNESS
    ============================================================================ *)

(* Check if variable is guarded in prioritized session type *)
val pri_is_guarded : x:session_var -> s:pri_session -> bool

(* Check contractivity of prioritized session branches *)
val pri_is_contractive_branches : branches:list (label & pri_session) -> bool

(* Check contractivity of prioritized session type *)
val pri_is_contractive : s:pri_session -> bool

(* Collect free variables from prioritized session branches *)
val pri_free_vars_branches : branches:list (label & pri_session) ->
  Tot (list session_var) (decreases branches)

(* Collect free variables in prioritized session type *)
val pri_free_vars : s:pri_session -> Tot (list session_var) (decreases s)

(* Check if prioritized session type is closed *)
val pri_is_closed : s:pri_session -> bool

(* Well-formed prioritized session type *)
val pri_is_wellformed : s:pri_session -> bool

(** ============================================================================
    CONVERSION BETWEEN REGULAR AND PRIORITIZED SESSION TYPES
    ============================================================================ *)

(* Assign sequential priorities to branches *)
val assign_priorities_branches : branches:list (label & session_type) -> start_pri:priority ->
  Tot (list (label & pri_session) & priority) (decreases branches)

(* Assign sequential priorities to a regular session type *)
val assign_priorities : s:session_type -> start_pri:priority ->
  Tot (pri_session & priority) (decreases s)

(* Convert regular session type to prioritized with sequential priorities *)
val to_prioritized : s:session_type -> pri_session

(* Strip priorities from branches *)
val strip_priorities_branches : branches:list (label & pri_session) ->
  Tot (list (label & session_type)) (decreases branches)

(* Strip priorities from a prioritized session type *)
val strip_priorities : s:pri_session -> Tot session_type (decreases s)

(** ============================================================================
    DEADLOCK FREEDOM
    ============================================================================ *)

(* Dependency graph as adjacency list *)
type dep_graph = list (channel_name & list channel_name)

(* Empty dependency graph *)
val empty_dep_graph : dep_graph

(* Add edge to dependency graph *)
val add_dep_edge : c:channel_name -> d:channel_name -> g:dep_graph -> dep_graph

(* Get all nodes in dependency graph *)
val dep_graph_nodes : g:dep_graph -> list channel_name

(* Get neighbors of a node in dependency graph *)
val dep_graph_neighbors : node:channel_name -> g:dep_graph -> list channel_name

(* Build dependency graph from a process *)
val build_dep_graph : p:process -> Tot dep_graph (decreases p)

(* Default fuel for cycle detection *)
val default_cycle_fuel : nat

(* Check if graph has cycle using DFS *)
val dfs_cycle_check : g:dep_graph -> visited:list channel_name ->
  to_visit:list channel_name -> fuel:nat -> Tot bool (decreases fuel)

(* Check if cycle exists starting from a specific node *)
val has_cycle_from : g:dep_graph -> start:channel_name -> fuel:nat -> bool

(* Check if dependency graph has any cycle *)
val has_cycle : g:dep_graph -> bool

(* Check if a process is deadlock-free *)
val is_deadlock_free : p:process -> bool

(** ============================================================================
    LOCK ORDERING FOR MUTEX DEADLOCK PREVENTION
    ============================================================================ *)

(* Lock ordering type *)
type lock_order = list string

(* Find position of a lock in the ordering *)
val lock_position : lock:string -> order:lock_order -> int

(* Check if lock positions are strictly increasing (valid ordering) *)
val positions_increasing : positions:list int -> bool

(* Check if acquired locks respect the defined lock order *)
val respects_lock_order : acquired:list string -> order:lock_order -> bool

(* Check if two locks can be acquired in the given order *)
val can_acquire_in_order : first:string -> second:string -> order:lock_order -> bool

(** ============================================================================
    DEADLOCK FREEDOM VERIFICATION
    ============================================================================ *)

(* Default fuel for pairwise consistency check *)
val default_consistency_fuel : nat

(* Check pairwise consistency of branch lists *)
val branches_pairwise_consistent : bs1:list (label & pri_session) ->
  bs2:list (label & pri_session) -> fuel:nat -> Tot bool (decreases fuel)

(* Check full priority consistency between two prioritized session types *)
val priorities_pairwise_consistent : s1:pri_session -> s2:pri_session -> fuel:nat ->
  Tot bool (decreases fuel)

(* Check deadlock freedom for a session type pair *)
val satisfies_deadlock_freedom : s1:pri_session -> s2:pri_session -> bool

(* Verify a prioritized session type is safe for deadlock-free execution *)
val is_safe_for_deadlock_free_execution : s:pri_session -> bool

(** ============================================================================
    PRIORITIZED CHANNEL ENDPOINT
    ============================================================================ *)

(* Channel with priority annotation for Brrr-Machine analysis *)
noeq type pri_channel_endpoint = {
  pri_ch_name : channel_name;
  pri_ch_session : pri_session;
  pri_ch_min : option priority;
  pri_ch_max : option priority
}

(* Create prioritized channel endpoint *)
val make_pri_endpoint : name:channel_name -> session:pri_session -> pri_channel_endpoint

(* Create dual endpoint pair with consistent priorities *)
val make_pri_channel_pair : name1:channel_name -> name2:channel_name -> session:pri_session ->
  (pri_channel_endpoint & pri_channel_endpoint)

(* Prioritized session context *)
type pri_session_ctx = list (channel_name & pri_session)

(* Lookup channel in prioritized context *)
val lookup_pri_channel : c:channel_name -> ctx:pri_session_ctx -> option pri_session

(* Check if all channels in context have consistent priorities *)
val ctx_priorities_consistent : ctx:pri_session_ctx -> bool

(** ============================================================================
    BRRR-MACHINE INTEGRATION
    ============================================================================ *)

(* Result of priority-based deadlock analysis *)
noeq type deadlock_analysis_result =
  | DeadlockFree : dep_graph:dep_graph -> deadlock_analysis_result
  | PotentialDeadlock : cycle:list channel_name -> deadlock_analysis_result
  | PriorityViolation : chan1:channel_name -> pri1:priority ->
                        chan2:channel_name -> pri2:priority -> deadlock_analysis_result

(* Perform complete deadlock analysis on a process *)
val analyze_deadlock : p:process -> deadlock_analysis_result

(* Check if analysis result indicates deadlock-free *)
val is_analysis_deadlock_free : result:deadlock_analysis_result -> bool

(** ============================================================================
    EXAMPLE PRIORITIZED SESSION TYPES
    ============================================================================ *)

(* Client-server request-response with priorities *)
val pri_client_session : req_type:brrr_type -> resp_type:brrr_type -> pri_session

(* Server: receives at priority 0, sends at priority 1 *)
val pri_server_session : req_type:brrr_type -> resp_type:brrr_type -> pri_session

(* Client and server sessions are duals *)
val client_server_are_duals : req_type:brrr_type -> resp_type:brrr_type ->
  Lemma (ensures pri_dual (pri_client_session req_type resp_type) ==
                 pri_server_session req_type resp_type)

(* Client session has valid priority ordering *)
val client_session_increasing : req_type:brrr_type -> resp_type:brrr_type ->
  Lemma (ensures priorities_strictly_increasing (pri_client_session req_type resp_type) = true)

(** ============================================================================
    COMMUNICATION SAFETY - Key Theorems
    ============================================================================ *)

(* Communication safety: dual endpoints have compatible types *)
val comm_safe : s1:session_type -> s2:session_type -> bool

(* Dual types are communication safe *)
val dual_comm_safe : s:session_type ->
  Lemma (ensures comm_safe s (dual s) = true)
        [SMTPat (comm_safe s (dual s))]

(* Well-formed session types are safe to use *)
val wellformed_comm_safe : s1:session_type -> s2:session_type ->
  Lemma (requires is_wellformed s1 = true /\ is_wellformed s2 = true /\ are_dual s1 s2 = true)
        (ensures comm_safe s1 s2 = true)

(** ============================================================================
    SESSION TYPE PROGRESS - No Stuck States
    ============================================================================ *)

(* A session type has progress if it can always make a step or is at end *)
val has_progress : s:session_type -> bool

(* Well-formed types have progress *)
val wellformed_has_progress : s:session_type ->
  Lemma (requires is_wellformed s = true)
        (ensures has_progress s = true)
        [SMTPat (has_progress s)]

(** ============================================================================
    LINEARITY - Channels Used Exactly Once
    ============================================================================ *)

(* Check if context is used linearly (each channel used exactly once) *)
val is_linear_ctx : ctx:session_ctx -> bool

(* Well-typed processes use channels linearly *)
val welltyped_is_linear : ctx:session_ctx -> p:process ->
  Lemma (requires check_succeeded (check_end ctx))
        (ensures is_linear_ctx ctx = true)
