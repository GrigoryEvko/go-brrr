(**
 * BrrrLang.Core.SecurityTypes - Interface
 *
 * Public interface for the Unified Security Type System.
 * Following HACL-star/EverParse patterns for .fsti/.fst separation.
 *
 * This interface exports:
 *   - Security label types (sec_label, taint_kind, confidentiality, integrity)
 *   - Label ordering and lattice operations
 *   - Lattice law lemmas with SMT triggers
 *   - Security-typed types and subtyping
 *   - Taint effect integration
 *   - Source/Sink/Sanitizer annotations
 *
 * Based on:
 *   - Denning 1977 (Information Flow Lattices)
 *   - Livshits 2005 (Taint Analysis)
 *   - Myers 1999 (Decentralized Information Flow Control)
 *   - brrr_lang_spec_v0.4.tex Part IX
 *
 * Implementation details are hidden in SecurityTypes.fst.
 *)
module SecurityTypes

open FStar.List.Tot
open Primitives
open Modes
open Effects
open BrrrTypes

(** Z3 solver options - must match implementation *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** ============================================================================
    TAINT KINDS
    ============================================================================ *)

(** Taint kind for vulnerability categorization *)
type taint_kind =
  | TkSQLi          : taint_kind
  | TkXSS           : taint_kind
  | TkCMDi          : taint_kind
  | TkPathTraversal : taint_kind
  | TkSSRF          : taint_kind
  | TkLDAPi         : taint_kind
  | TkXMLi          : taint_kind
  | TkHeaderi       : taint_kind
  | TkLogi          : taint_kind
  | TkTemplatei     : taint_kind
  | TkDeserial      : taint_kind
  | TkRedirect      : taint_kind
  | TkCustom        : string -> taint_kind

(** Taint kind equality *)
val taint_kind_eq : k1:taint_kind -> k2:taint_kind -> bool

(** Taint set type *)
type taint_set = list taint_kind

(** ============================================================================
    CONFIDENTIALITY AND INTEGRITY DIMENSIONS
    ============================================================================ *)

(** Confidentiality dimension - prevents data leaks *)
type confidentiality =
  | CPublic : confidentiality
  | CSecret : confidentiality

(** Integrity dimension - tracks trust level *)
type integrity =
  | IUntrusted : integrity
  | ITrusted   : integrity

(** ============================================================================
    SECURITY LABELS
    ============================================================================ *)

(** Complete security label - product of confidentiality, integrity, and taints *)
noeq type sec_label = {
  confidentiality : confidentiality;
  integrity       : integrity;
  taints          : taint_set;
}

(** ============================================================================
    SECURITY LABEL CONSTRUCTORS
    ============================================================================ *)

val sec_public_trusted : sec_label
val sec_secret_trusted : sec_label
val sec_public_untrusted : taint_set -> sec_label
val sec_tainted : taint_kind -> sec_label
val sec_bot : sec_label
val sec_top : sec_label

(** ============================================================================
    SECURITY LABEL ORDERING
    ============================================================================ *)

(**
 * Confidentiality ordering: Public < Secret
 * Marked inline_for_extraction for efficient evaluation.
 *)
val conf_leq : c1:confidentiality -> c2:confidentiality -> bool

(**
 * Integrity ordering: Trusted < Untrusted (for taint flow)
 * Untrusted is "higher" because tainted data can flow to more tainted.
 *)
val integ_leq : i1:integrity -> i2:integrity -> bool

(** Check if taint kind is in set - recursive *)
val taint_in_set : k:taint_kind -> ks:taint_set -> bool

(** Taint set subset ordering - recursive *)
val taint_set_subset : ks1:taint_set -> ks2:taint_set -> bool

(**
 * Security label ordering (product order).
 * l1 <= l2 means data at l1 can flow to l2.
 *)
val sec_label_leq : l1:sec_label -> l2:sec_label -> bool

(** ============================================================================
    SECURITY LABEL LATTICE OPERATIONS
    ============================================================================ *)

(** Confidentiality join (least upper bound) *)
val conf_join : c1:confidentiality -> c2:confidentiality -> confidentiality

(** Confidentiality meet (greatest lower bound) *)
val conf_meet : c1:confidentiality -> c2:confidentiality -> confidentiality

(** Integrity join (least upper bound) *)
val integ_join : i1:integrity -> i2:integrity -> integrity

(** Integrity meet (greatest lower bound) *)
val integ_meet : i1:integrity -> i2:integrity -> integrity

(** Taint set union (join) - recursive *)
val taint_set_union : ks1:taint_set -> ks2:taint_set -> taint_set

(** Taint set intersection (meet) - recursive *)
val taint_set_intersect : ks1:taint_set -> ks2:taint_set -> taint_set

(** Security label join (least upper bound) *)
val sec_label_join : l1:sec_label -> l2:sec_label -> sec_label

(** Security label meet (greatest lower bound) *)
val sec_label_meet : l1:sec_label -> l2:sec_label -> sec_label

(** ============================================================================
    LATTICE LAW LEMMAS - REFLEXIVITY
    ============================================================================ *)

val taint_kind_eq_refl : k:taint_kind ->
  Lemma (ensures taint_kind_eq k k = true)
        [SMTPat (taint_kind_eq k k)]

val conf_leq_refl : c:confidentiality ->
  Lemma (ensures conf_leq c c = true)
        [SMTPat (conf_leq c c)]

val integ_leq_refl : i:integrity ->
  Lemma (ensures integ_leq i i = true)
        [SMTPat (integ_leq i i)]

(** taint_in_set with head - element is in set if it's the head *)
val taint_in_set_head : k:taint_kind -> rest:taint_set ->
  Lemma (ensures taint_in_set k (k :: rest) = true)
        [SMTPat (taint_in_set k (k :: rest))]

val taint_set_subset_refl : ks:taint_set ->
  Lemma (ensures taint_set_subset ks ks = true)
        (decreases ks)
        [SMTPat (taint_set_subset ks ks)]

val sec_label_leq_refl : l:sec_label ->
  Lemma (ensures sec_label_leq l l = true)
        [SMTPat (sec_label_leq l l)]

(** ============================================================================
    LATTICE LAW LEMMAS - TRANSITIVITY
    ============================================================================ *)

val conf_leq_trans : c1:confidentiality -> c2:confidentiality -> c3:confidentiality ->
  Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c3 = true)
        (ensures conf_leq c1 c3 = true)

val integ_leq_trans : i1:integrity -> i2:integrity -> i3:integrity ->
  Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i3 = true)
        (ensures integ_leq i1 i3 = true)

val taint_in_set_trans : k:taint_kind -> ks1:taint_set -> ks2:taint_set ->
  Lemma (requires taint_in_set k ks1 = true /\ taint_set_subset ks1 ks2 = true)
        (ensures taint_in_set k ks2 = true)
        (decreases ks1)

val taint_set_subset_trans : ks1:taint_set -> ks2:taint_set -> ks3:taint_set ->
  Lemma (requires taint_set_subset ks1 ks2 = true /\ taint_set_subset ks2 ks3 = true)
        (ensures taint_set_subset ks1 ks3 = true)
        (decreases ks1)

val sec_label_leq_trans : l1:sec_label -> l2:sec_label -> l3:sec_label ->
  Lemma (requires sec_label_leq l1 l2 = true /\ sec_label_leq l2 l3 = true)
        (ensures sec_label_leq l1 l3 = true)

(** ============================================================================
    LATTICE LAW LEMMAS - ANTISYMMETRY
    ============================================================================ *)

val conf_leq_antisym : c1:confidentiality -> c2:confidentiality ->
  Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c1 = true)
        (ensures c1 = c2)

val integ_leq_antisym : i1:integrity -> i2:integrity ->
  Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i1 = true)
        (ensures i1 = i2)

(** ============================================================================
    LATTICE LAW LEMMAS - JOIN IS LEAST UPPER BOUND
    ============================================================================ *)

(** Join is an upper bound *)
val sec_label_join_upper_l : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq l1 (sec_label_join l1 l2) = true)
        [SMTPat (sec_label_join l1 l2)]

val sec_label_join_upper_r : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq l2 (sec_label_join l1 l2) = true)

(** Join is the least upper bound *)
val sec_label_join_lub : l1:sec_label -> l2:sec_label -> u:sec_label ->
  Lemma (requires sec_label_leq l1 u = true /\ sec_label_leq l2 u = true)
        (ensures sec_label_leq (sec_label_join l1 l2) u = true)

(** ============================================================================
    LATTICE LAW LEMMAS - MEET IS GREATEST LOWER BOUND
    ============================================================================ *)

(** Meet is a lower bound *)
val sec_label_meet_lower_l : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l1 = true)
        [SMTPat (sec_label_meet l1 l2)]

val sec_label_meet_lower_r : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l2 = true)

(** Meet is the greatest lower bound *)
val sec_label_meet_glb : l1:sec_label -> l2:sec_label -> lb:sec_label ->
  Lemma (requires sec_label_leq lb l1 = true /\ sec_label_leq lb l2 = true)
        (ensures sec_label_leq lb (sec_label_meet l1 l2) = true)

(** ============================================================================
    LATTICE LAW LEMMAS - COMMUTATIVITY AND IDEMPOTENCE
    ============================================================================ *)

(** sec_label_join is commutative up to set equivalence *)
val sec_label_join_comm_equiv : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_join l1 l2) (sec_label_join l2 l1) = true /\
                  sec_label_leq (sec_label_join l2 l1) (sec_label_join l1 l2) = true)

val sec_label_join_idem : l:sec_label ->
  Lemma (ensures sec_label_join l l == l)

(** sec_label_meet is commutative up to set equivalence *)
val sec_label_meet_comm_equiv : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) (sec_label_meet l2 l1) = true /\
                  sec_label_leq (sec_label_meet l2 l1) (sec_label_meet l1 l2) = true)

val sec_label_meet_idem : l:sec_label ->
  Lemma (ensures sec_label_meet l l == l)

(** ============================================================================
    SECURITY-TYPED TYPES
    ============================================================================ *)

(** Security-typed type: base type + security label *)
noeq type sec_type = {
  base : brrr_type;
  label : sec_label;
}

val mk_sec_type : brrr_type -> sec_label -> sec_type
val untainted_type : brrr_type -> sec_type
val tainted_type : brrr_type -> taint_kind -> sec_type
val secret_type : brrr_type -> sec_type

(** Security-typed subtyping *)
val sec_type_subtype : st1:sec_type -> st2:sec_type -> bool

val sec_type_subtype_refl : st:sec_type ->
  Lemma (ensures sec_type_subtype st st = true)
        [SMTPat (sec_type_subtype st st)]

(** ============================================================================
    SECURITY FUNCTION TYPES
    ============================================================================ *)

(** Security role of a function *)
type sec_role =
  | SrNone      : sec_role
  | SrSource    : list taint_kind -> sec_role
  | SrSink      : list taint_kind -> sec_role
  | SrSanitizer : list taint_kind -> sec_role
  | SrValidator : list taint_kind -> sec_role

(** Security-typed function parameter *)
noeq type sec_param = {
  sp_name : option string;
  sp_type : sec_type;
  sp_mode : mode;
}

(** Security-typed function type *)
noeq type sec_func_type = {
  sf_params      : list sec_param;
  sf_return      : sec_type;
  sf_effects     : effect_row;
  sf_role        : sec_role;
  sf_is_unsafe   : bool;
}

(** ============================================================================
    PC (PROGRAM COUNTER) LABEL
    ============================================================================ *)

type pc_label = sec_label

val initial_pc : pc_label
val raise_pc : pc:pc_label -> guard_label:sec_label -> pc_label
val check_flow : pc:pc_label -> rhs:sec_label -> lhs:sec_label -> bool

(** ============================================================================
    TAINT OPERATIONS
    ============================================================================ *)

val remove_taint : k:taint_kind -> ks:taint_set -> taint_set
val remove_taints : to_remove:list taint_kind -> ks:taint_set -> taint_set
val sanitize_label : to_remove:list taint_kind -> l:sec_label -> sec_label
val sanitize_sec_type : to_remove:list taint_kind -> st:sec_type -> sec_type
val has_any_taint : ks:list taint_kind -> l:sec_label -> bool

(** ============================================================================
    TAINT REMOVAL LEMMAS
    ============================================================================ *)

val remove_taint_correct : k:taint_kind -> ks:taint_set ->
  Lemma (ensures taint_in_set k (remove_taint k ks) = false)
        (decreases ks)

val remove_taint_preserves : k:taint_kind -> k':taint_kind -> ks:taint_set ->
  Lemma (requires taint_kind_eq k k' = false)
        (ensures taint_in_set k' (remove_taint k ks) = taint_in_set k' ks)
        (decreases ks)

val sanitize_enables_sink : to_remove:list taint_kind -> l:sec_label ->
  Lemma (ensures not (has_any_taint to_remove (sanitize_label to_remove l)))

(** ============================================================================
    I/O TAINT INTEGRATION
    ============================================================================ *)

val io_source_taints : src:io_source -> taint_set
val io_sink_requirements : snk:io_sink -> taint_set
val effect_input_label : src:io_source -> sec_label
val effect_output_allowed : snk:io_sink -> l:sec_label -> bool

(** ============================================================================
    SECURITY OPERATIONS
    ============================================================================ *)

val sec_unary_result : st:sec_type -> result_base:brrr_type -> sec_type
val sec_binary_result : st1:sec_type -> st2:sec_type -> result_base:brrr_type -> sec_type
val sec_nary_label : sts:list sec_type -> sec_label
val sec_nary_result : sts:list sec_type -> result_base:brrr_type -> sec_type

(** ============================================================================
    SECURITY CONTEXT
    ============================================================================ *)

type sec_ctx_entry = string & sec_type
type sec_ctx = list sec_ctx_entry

val empty_sec_ctx : sec_ctx
val extend_sec_ctx : x:string -> st:sec_type -> ctx:sec_ctx -> sec_ctx
val lookup_sec_ctx : x:string -> ctx:sec_ctx -> option sec_type

(** ============================================================================
    SECURITY ANNOTATIONS
    ============================================================================ *)

noeq type source_annotation = {
  src_name   : string;
  src_taints : list taint_kind;
  src_origin : string;
}

noeq type sink_annotation = {
  snk_name     : string;
  snk_rejects  : list taint_kind;
  snk_params   : list nat;
}

noeq type sanitizer_annotation = {
  san_name    : string;
  san_removes : list taint_kind;
  san_param   : nat;
}

type sec_annotation =
  | AnnSource    : source_annotation -> sec_annotation
  | AnnSink      : sink_annotation -> sec_annotation
  | AnnSanitizer : sanitizer_annotation -> sec_annotation
  | AnnTrusted   : sec_annotation

val sink_check : snk:sink_annotation -> arg_labels:list sec_label -> bool

(** ============================================================================
    BRRR-MACHINE INTEGRATION TYPES
    ============================================================================ *)

type sec_severity =
  | SevCritical : sec_severity
  | SevHigh     : sec_severity
  | SevMedium   : sec_severity
  | SevLow      : sec_severity
  | SevInfo     : sec_severity

noeq type sec_finding = {
  sf_id          : nat;
  sf_kind        : taint_kind;
  sf_severity    : sec_severity;
  sf_source_loc  : option nat;
  sf_sink_loc    : option nat;
  sf_message     : string;
  sf_remediation : option string;
}

noeq type taint_flow_edge = {
  tfe_from_node : nat;
  tfe_to_node   : nat;
  tfe_taints    : taint_set;
  tfe_sanitized : taint_set;
}

noeq type func_taint_summary = {
  fts_func_id      : nat;
  fts_param_taints : list sec_label;
  fts_return_taint : sec_label;
  fts_role         : sec_role;
  fts_annotations  : list sec_annotation;
}

(** ============================================================================
    WELL-FORMEDNESS
    ============================================================================ *)

val sec_label_wf : l:sec_label -> bool
val sec_type_wf : st:sec_type -> bool

(** ============================================================================
    TAINT EFFECTS (Integrated with Effect System)
    ============================================================================ *)

type taint_effect =
  | ETaintSource    : list taint_kind -> taint_effect
  | ETaintSink      : list taint_kind -> taint_effect
  | ETaintSanitize  : list taint_kind -> taint_effect
  | ETaintPropagate : taint_effect

val taint_effect_to_string : te:taint_effect -> string

(** ============================================================================
    NAMED SECURITY LEVELS (For Extensibility)
    ============================================================================ *)

type sec_level_id = nat

noeq type named_sec_level = {
  level_id   : sec_level_id;
  level_name : string;
}
