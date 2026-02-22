(**
 * =============================================================================
 * BrrrLang.Core.ModuleSystem - Interface
 * =============================================================================
 *
 * ML-style module system for Brrr-Lang IR, providing abstraction, separate
 * compilation, and code reuse through a rich module calculus.
 *
 * Based on brrr_lang_spec_v0.4.tex Part VIII (Module System), which draws
 * from foundational work on ML modules:
 *
 *   - Harper-Lillibridge: A Type-Theoretic Approach to Higher-Order Modules
 *     with Sharing (POPL '94)
 *   - Dreyer-Crary-Harper: A Type System for Higher-Order Modules (POPL '03)
 *   - Leroy: A Modular Module System (JFP 2000)
 *   - Rossberg-Russo-Dreyer: F-ing Modules (JFP 2014)
 *
 * =============================================================================
 * FEATURES
 * =============================================================================
 *
 *   - Module signatures with type, value, and effect members
 *   - First-class modules and higher-order functors
 *   - Signature subtyping with proper variance
 *   - Sealing for abstraction (existential types / opaque ascription)
 *   - Functor application with type substitution
 *   - Where clauses for type sharing/refinement
 *   - Mixin composition with diamond conflict resolution
 *   - Circular dependency detection via DFS
 *   - Topological sort for compilation order
 *
 * =============================================================================
 * KEY INVARIANTS (Mechanized Theorems)
 * =============================================================================
 *
 *   - Signature subtyping is reflexive, transitive (preorder)
 *   - Type/value/effect member equality is an equivalence relation
 *   - Functor application preserves well-formedness
 *   - Sealing respects signature compatibility
 *   - Where clause application produces a subtype
 *   - Module dependency graph must be acyclic
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Kinds
 *)
module BrrrModuleSystem

open FStar.List.Tot
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrKinds

(** ============================================================================
    MODULE IDENTIFIERS AND NAMESPACE RESOLUTION
    ============================================================================ *)

(** Module variable identifier - a simple string name. *)
type module_var = string

(** Module path: qualified name for accessing nested modules.
    Paths enable hierarchical module access:
      MPVar "M"                         -- Simple reference: M
      MPDot (MPVar "M") "N"             -- Qualified: M.N
      MPDot (MPDot (MPVar "M") "N") "P" -- Deep nesting: M.N.P *)
noeq type module_path =
  | MPVar   : module_var -> module_path
  | MPDot   : module_path -> string -> module_path

(** ============================================================================
    SOURCE LOCATION TRACKING
    ============================================================================ *)

(** Source position: file, line, column *)
type source_pos = {
  sp_file   : string;
  sp_line   : nat;
  sp_column : nat
}

(** Source range: span from start to end position *)
type source_range = source_pos & source_pos

(** Dummy position for synthetic/compiler-generated nodes *)
val dummy_source_pos : source_pos

(** Dummy range for synthetic/compiler-generated nodes *)
val dummy_source_range : source_range

(** Format position as "file:(line,col)" *)
val string_of_source_pos : source_pos -> string

(** Format range for error messages *)
val string_of_source_range : source_range -> string

(** Comments associated with AST nodes *)
type comments = list string

(** Metadata wrapper for AST nodes following EverParse pattern.
    Carries source location and associated comments through the AST. *)
noeq type with_meta_t 'a = {
  meta_value    : 'a;
  meta_range    : source_range;
  meta_comments : comments
}

(** Create a located value with given range *)
val with_range : #a:Type -> value:a -> r:source_range -> with_meta_t a

(** Create a located value with range and comments *)
val with_meta : #a:Type -> value:a -> r:source_range -> c:comments -> with_meta_t a

(** Create a located value with dummy range (for synthetic nodes) *)
val no_range : #a:Type -> value:a -> with_meta_t a

(** Extract value from metadata wrapper *)
val meta_value_of : #a:Type -> with_meta_t a -> a

(** Extract range from metadata wrapper *)
val meta_range_of : #a:Type -> with_meta_t a -> source_range

(** Map function over wrapped value, preserving location *)
val meta_map : #a:Type -> #b:Type -> (a -> b) -> with_meta_t a -> with_meta_t b

(** ============================================================================
    MODULE VISIBILITY
    ============================================================================ *)

(** Module member visibility levels.
    Public   - Visible to all modules (exported in external signature)
    Internal - Visible within the same package (not exported externally)
    Private  - Visible only within the defining module (never exported) *)
type module_visibility =
  | MVPublic   : module_visibility
  | MVInternal : module_visibility
  | MVPrivate  : module_visibility

(** Default visibility for members without explicit annotation *)
val default_visibility : module_visibility

(** Check if visibility v1 is at least as permissive as v2 *)
val visibility_leq : module_visibility -> module_visibility -> bool

(** Check if visibility v1 is strictly more permissive than v2 *)
val visibility_lt : module_visibility -> module_visibility -> bool

(** Visibility is reflexive *)
val visibility_leq_refl : v:module_visibility ->
  Lemma (visibility_leq v v = true) [SMTPat (visibility_leq v v)]

(** Visibility is transitive *)
val visibility_leq_trans : v1:module_visibility -> v2:module_visibility -> v3:module_visibility ->
  Lemma (requires visibility_leq v1 v2 = true /\ visibility_leq v2 v3 = true)
        (ensures visibility_leq v1 v3 = true)

(** String representation of visibility *)
val string_of_visibility : module_visibility -> string

(** ============================================================================
    SHADOW CHECKING
    ============================================================================ *)

(** Result of shadow check: either success or error with location. *)
type shadow_result =
  | ShadowOK    : shadow_result
  | ShadowError : name:string -> prev_range:source_range -> new_range:source_range -> shadow_result

(** Check if a type name would shadow an existing binding *)
val check_shadow_type : name:type_name -> new_range:source_range ->
                        existing:list (type_name & source_range) -> shadow_result

(** Check if a value name would shadow an existing binding *)
val check_shadow_value : name:var_id -> new_range:source_range ->
                         existing:list (var_id & source_range) -> shadow_result

(** Check if an effect name would shadow an existing binding *)
val check_shadow_effect : name:string -> new_range:source_range ->
                          existing:list (string & source_range) -> shadow_result

(** Format shadow error message *)
val format_shadow_error : shadow_result -> option string

(** ============================================================================
    EFFECT SIGNATURE
    ============================================================================ *)

(** Effect signature: effect name with its operations and metadata *)
noeq type effect_sig = {
  eff_sig_name       : string;
  eff_sig_ops        : list (string & brrr_type);
  eff_sig_visibility : module_visibility;
  eff_sig_range      : source_range
}

(** Extract visibility from effect signature *)
val effect_sig_visibility : effect_sig -> module_visibility

(** Extract source range from effect signature *)
val effect_sig_range : effect_sig -> source_range

(** Check if effect signature is visible at given visibility level *)
val effect_sig_visible_at : effect_sig -> module_visibility -> bool

(** Create effect signature with default visibility *)
val mk_effect_sig : name:string -> ops:list (string & brrr_type) -> effect_sig

(** Create effect signature with explicit visibility and location *)
val mk_effect_sig_with_meta : name:string -> ops:list (string & brrr_type) ->
                               v:module_visibility -> r:source_range -> effect_sig

(** ============================================================================
    TYPE MEMBER
    ============================================================================ *)

(** Type members can be opaque (abstract) or transparent (concrete).
    TMOpaque: "type T : K" - representation hidden
    TMTransparent: "type T : K = tau" - representation known *)
noeq type type_member =
  | TMOpaque      : type_name -> kind -> module_visibility -> source_range -> type_member
  | TMTransparent : type_name -> kind -> brrr_type -> module_visibility -> source_range -> type_member

(** Extract name from type member *)
val type_member_name : type_member -> type_name

(** Extract kind from type member *)
val type_member_kind : type_member -> kind

(** Extract visibility from type member *)
val type_member_visibility : type_member -> module_visibility

(** Extract source range from type member *)
val type_member_range : type_member -> source_range

(** Check if type member is opaque *)
val is_opaque : type_member -> bool

(** Check if type member is transparent *)
val is_transparent : type_member -> bool

(** Get definition of transparent type member *)
val type_member_def : type_member -> option brrr_type

(** Check if type member is visible at given visibility level *)
val type_member_visible_at : type_member -> module_visibility -> bool

(** Create opaque type member with default visibility *)
val mk_opaque_type : name:type_name -> k:kind -> type_member

(** Create opaque type member with explicit visibility and location *)
val mk_opaque_type_with_meta : name:type_name -> k:kind -> v:module_visibility -> r:source_range -> type_member

(** Create transparent type member with default visibility *)
val mk_transparent_type : name:type_name -> k:kind -> t:brrr_type -> type_member

(** Create transparent type member with explicit visibility and location *)
val mk_transparent_type_with_meta : name:type_name -> k:kind -> t:brrr_type ->
                                     v:module_visibility -> r:source_range -> type_member

(** ============================================================================
    VALUE MEMBER
    ============================================================================ *)

(** Value member in a signature: name with type scheme and metadata *)
noeq type value_member = {
  val_name       : var_id;
  val_scheme     : type_scheme;
  val_visibility : module_visibility;
  val_range      : source_range
}

(** Extract visibility from value member *)
val value_member_visibility : value_member -> module_visibility

(** Extract source range from value member *)
val value_member_range : value_member -> source_range

(** Check if value member is visible at given visibility level *)
val value_member_visible_at : value_member -> module_visibility -> bool

(** Create value member with default visibility *)
val mk_value_member : name:var_id -> scheme:type_scheme -> value_member

(** Create value member with explicit visibility and location *)
val mk_value_member_with_meta : name:var_id -> scheme:type_scheme ->
                                 v:module_visibility -> r:source_range -> value_member

(** ============================================================================
    MODULE SIGNATURE
    ============================================================================ *)

(** Module signature: the interface of a module *)
noeq type signature = {
  sig_types   : list type_member;
  sig_values  : list value_member;
  sig_effects : list effect_sig
}

(** Empty signature *)
val empty_sig : signature

(** Extend signature with a type member *)
val sig_add_type : type_member -> signature -> signature

(** Extend signature with a value member *)
val sig_add_value : value_member -> signature -> signature

(** Extend signature with an effect member *)
val sig_add_effect : effect_sig -> signature -> signature

(** Lookup type member by name *)
val lookup_type_member : type_name -> list type_member -> option type_member

(** Lookup value member by name *)
val lookup_value_member : var_id -> list value_member -> option value_member

(** Lookup effect member by name *)
val lookup_effect_member : string -> list effect_sig -> option effect_sig

(** ============================================================================
    VISIBILITY FILTERING
    ============================================================================ *)

(** Filter type members by visibility threshold *)
val filter_type_members_by_visibility : module_visibility -> list type_member -> list type_member

(** Filter value members by visibility threshold *)
val filter_value_members_by_visibility : module_visibility -> list value_member -> list value_member

(** Filter effect members by visibility threshold *)
val filter_effect_members_by_visibility : module_visibility -> list effect_sig -> list effect_sig

(** Filter entire signature by visibility *)
val filter_signature_by_visibility : module_visibility -> signature -> signature

(** Export signature: filter to only publicly visible members *)
val export_signature : signature -> signature

(** Internal signature: filter to internally and publicly visible members *)
val internal_signature : signature -> signature

(** Filtering preserves well-formedness *)
val collect_type_member_names_ranges : list type_member -> list (type_name & source_range)

(** Collect value member names and ranges for shadow checking *)
val collect_value_member_names_ranges : list value_member -> list (var_id & source_range)

(** Collect effect member names and ranges for shadow checking *)
val collect_effect_member_names_ranges : list effect_sig -> list (string & source_range)

(** Check if adding a type member would shadow existing members *)
val check_type_member_shadow : type_member -> list type_member -> shadow_result

(** Check if adding a value member would shadow existing members *)
val check_value_member_shadow : value_member -> list value_member -> shadow_result

(** Check if adding an effect member would shadow existing members *)
val check_effect_member_shadow : effect_sig -> list effect_sig -> shadow_result

(** ============================================================================
    FUNCTOR MODE
    ============================================================================ *)

(** Functor mode determines type sharing semantics across applications.
    Applicative: F(M) = F(M') when M equiv M' - types shared
    Generative: F(M) <> F(M') even when M equiv M' - fresh types per application *)
type functor_mode =
  | Applicative
  | Generative

(** Default functor mode is applicative *)
val default_functor_mode : functor_mode

(** Type stamp for tracking generative type identity *)
type type_stamp = nat

(** Stamp state for generating fresh stamps *)
type stamp_state = {
  next_stamp : type_stamp
}

(** Initial stamp state *)
val initial_stamp_state : stamp_state

(** Generate a fresh stamp and update state *)
val fresh_stamp : stamp_state -> (type_stamp & stamp_state)

(** Stamped type: tracks generative identity for abstract types *)
noeq type stamped_type =
  | Unstamped   : brrr_type -> stamped_type
  | Stamped     : type_stamp -> type_name -> stamped_type

(** Extract underlying type from stamped type (if unstamped) *)
val unstamp_type : stamped_type -> option brrr_type

(** Check if two stamped types are equal *)
val stamped_type_eq : stamped_type -> stamped_type -> bool

(** ============================================================================
    MODULE TYPES
    ============================================================================ *)

(** Module types classify modules.
    MTSig: Modules implementing signature s
    MTFunctor: Functors from param to result with given mode *)
noeq type module_type =
  | MTSig     : signature -> module_type
  | MTFunctor : module_var -> module_type -> module_type -> functor_mode -> module_type

(** Size of module type - for termination measures *)
val module_type_size : module_type -> Tot nat

(** ============================================================================
    MODULE DECLARATIONS AND EXPRESSIONS
    ============================================================================ *)

(** Module declaration: a single item in a structure *)
noeq type module_decl =
  | MDType   : type_member -> module_decl
  | MDVal    : var_id -> brrr_type -> module_decl
  | MDEffect : effect_sig -> module_decl
  | MDModule : module_var -> module_expr -> module_decl

(** Module expression: constructs modules *)
and module_expr =
  | MEStruct  : list module_decl -> module_expr
  | MEFunctor : module_var -> module_type -> functor_mode -> module_expr -> module_expr
  | MEApp     : module_expr -> module_expr -> module_expr
  | MEPath    : module_path -> module_expr
  | MESeal    : module_expr -> module_type -> module_expr

(** Size of module expression - for termination *)
val module_expr_size : module_expr -> Tot nat

(** Size of module declaration - for termination *)
val module_decl_size : module_decl -> Tot nat

(** Size of module declaration list - for termination *)
val module_decl_list_size : list module_decl -> Tot nat

(** ============================================================================
    EQUALITY RELATIONS
    ============================================================================ *)

(** Type member equality *)
val type_member_eq : type_member -> type_member -> bool

(** Type member equality is reflexive *)
val type_member_eq_refl : tm:type_member ->
  Lemma (type_member_eq tm tm = true) [SMTPat (type_member_eq tm tm)]

(** Type member equality is symmetric *)
val type_member_eq_sym : tm1:type_member -> tm2:type_member ->
  Lemma (requires type_member_eq tm1 tm2 = true)
        (ensures type_member_eq tm2 tm1 = true)

(** Type member equality is transitive *)
val type_member_eq_trans : tm1:type_member -> tm2:type_member -> tm3:type_member ->
  Lemma (requires type_member_eq tm1 tm2 = true /\ type_member_eq tm2 tm3 = true)
        (ensures type_member_eq tm1 tm3 = true)

(** Type scheme equality *)
val type_scheme_eq : type_scheme -> type_scheme -> bool

(** Value member equality *)
val value_member_eq : value_member -> value_member -> bool

(** Value member equality is reflexive *)
val value_member_eq_refl : vm:value_member ->
  Lemma (value_member_eq vm vm = true) [SMTPat (value_member_eq vm vm)]

(** Value member equality is symmetric *)
val value_member_eq_sym : vm1:value_member -> vm2:value_member ->
  Lemma (requires value_member_eq vm1 vm2 = true)
        (ensures value_member_eq vm2 vm1 = true)

(** Value member equality is transitive *)
val value_member_eq_trans : vm1:value_member -> vm2:value_member -> vm3:value_member ->
  Lemma (requires value_member_eq vm1 vm2 = true /\ value_member_eq vm2 vm3 = true)
        (ensures value_member_eq vm1 vm3 = true)

(** Effect operation list equality *)
val effect_ops_eq : list (string & brrr_type) -> list (string & brrr_type) -> bool

(** Effect signature equality *)
val effect_sig_eq : effect_sig -> effect_sig -> bool

(** Effect signature equality is reflexive *)
val effect_sig_eq_refl : es:effect_sig ->
  Lemma (effect_sig_eq es es = true) [SMTPat (effect_sig_eq es es)]

(** Effect signature equality is symmetric *)
val effect_sig_eq_sym : es1:effect_sig -> es2:effect_sig ->
  Lemma (requires effect_sig_eq es1 es2 = true)
        (ensures effect_sig_eq es2 es1 = true)

(** Effect signature equality is transitive *)
val effect_sig_eq_trans : es1:effect_sig -> es2:effect_sig -> es3:effect_sig ->
  Lemma (requires effect_sig_eq es1 es2 = true /\ effect_sig_eq es2 es3 = true)
        (ensures effect_sig_eq es1 es3 = true)

(** Signature equality *)
val signature_eq : signature -> signature -> bool

(** Signature equality is reflexive *)
val signature_eq_refl : s:signature ->
  Lemma (signature_eq s s = true) [SMTPat (signature_eq s s)]

(** Signature equality is symmetric *)
val signature_eq_sym : s1:signature -> s2:signature ->
  Lemma (requires signature_eq s1 s2 = true)
        (ensures signature_eq s2 s1 = true)

(** Signature equality is transitive *)
val signature_eq_trans : s1:signature -> s2:signature -> s3:signature ->
  Lemma (requires signature_eq s1 s2 = true /\ signature_eq s2 s3 = true)
        (ensures signature_eq s1 s3 = true)

(** Module type equality *)
val module_type_eq : module_type -> module_type -> Tot bool

(** Module type equality is reflexive *)
val module_type_eq_refl : mt:module_type ->
  Lemma (ensures module_type_eq mt mt = true) (decreases mt) [SMTPat (module_type_eq mt mt)]

(** Module type equality is symmetric *)
val module_type_eq_sym : mt1:module_type -> mt2:module_type ->
  Lemma (requires module_type_eq mt1 mt2 = true)
        (ensures module_type_eq mt2 mt1 = true)

(** Module type equality is transitive *)
val module_type_eq_trans : mt1:module_type -> mt2:module_type -> mt3:module_type ->
  Lemma (requires module_type_eq mt1 mt2 = true /\ module_type_eq mt2 mt3 = true)
        (ensures module_type_eq mt1 mt3 = true)

(** ============================================================================
    SUBTYPING RELATIONS
    ============================================================================ *)

(** Type member subtyping *)
val type_member_sub : type_member -> type_member -> bool

(** Type member subtyping is reflexive *)
val type_member_sub_refl : tm:type_member ->
  Lemma (type_member_sub tm tm = true) [SMTPat (type_member_sub tm tm)]

(** Type scheme subtyping *)
val type_scheme_sub : type_scheme -> type_scheme -> bool

(** Value member subtyping *)
val value_member_sub : value_member -> value_member -> bool

(** Value member subtyping is reflexive *)
val value_member_sub_refl : vm:value_member ->
  Lemma (value_member_sub vm vm = true) [SMTPat (value_member_sub vm vm)]

(** Effect operation subtyping *)
val effect_ops_sub : list (string & brrr_type) -> list (string & brrr_type) -> bool

(** Effect signature subtyping *)
val effect_sig_sub : effect_sig -> effect_sig -> bool

(** Effect signature subtyping is reflexive *)
val effect_sig_sub_refl : es:effect_sig ->
  Lemma (effect_sig_sub es es = true) [SMTPat (effect_sig_sub es es)]

(** Check if member names are unique in a type member list *)
val type_member_names_unique : list type_member -> bool

(** Check if member names are unique in a value member list *)
val value_member_names_unique : list value_member -> bool

(** Check if member names are unique in an effect member list *)
val effect_member_names_unique : list effect_sig -> bool

(** Well-formed signature: all member names are unique *)
val wf_sig_names : signature -> bool

(** Signature subtyping *)
val filter_signature_preserves_wf : vis:module_visibility -> sig:signature ->
  Lemma (requires wf_sig_names sig = true)
        (ensures wf_sig_names (filter_signature_by_visibility vis sig) = true)

(** Collect type member names and ranges for shadow checking *)
val signature_sub : signature -> signature -> bool

(** Signature subtyping is reflexive for well-formed signatures *)
val signature_sub_refl : s:signature ->
  Lemma (requires wf_sig_names s = true)
        (ensures signature_sub s s = true)

(** Signature subtyping is transitive *)
val signature_sub_trans : s1:signature -> s2:signature -> s3:signature ->
  Lemma (requires signature_sub s1 s2 = true /\ signature_sub s2 s3 = true)
        (ensures signature_sub s1 s3 = true)

(** Module type subtyping *)
val module_type_sub : mt1:module_type -> mt2:module_type -> Tot bool

(** Well-formed module type: all signatures have unique names *)
val wf_module_type_names : module_type -> Tot bool

(** Module type subtyping is reflexive for well-formed module types *)
val module_type_sub_refl : mt:module_type ->
  Lemma (requires wf_module_type_names mt = true)
        (ensures module_type_sub mt mt = true)

(** Module type subtyping is transitive *)
val module_type_sub_trans : mt1:module_type -> mt2:module_type -> mt3:module_type ->
  Lemma (requires module_type_sub mt1 mt2 = true /\ module_type_sub mt2 mt3 = true)
        (ensures module_type_sub mt1 mt3 = true)

(** ============================================================================
    TYPE SUBSTITUTION IN SIGNATURES
    ============================================================================ *)

(** Substitute a type variable in a type member *)
val subst_in_type_member : type_var -> brrr_type -> type_member -> type_member

(** Substitute in type member list *)
val subst_in_type_members : type_var -> brrr_type -> list type_member -> list type_member

(** Substitute in type scheme *)
val subst_in_type_scheme : type_var -> brrr_type -> type_scheme -> type_scheme

(** Substitute in value member *)
val subst_in_value_member : type_var -> brrr_type -> value_member -> value_member

(** Substitute in value member list *)
val subst_in_value_members : type_var -> brrr_type -> list value_member -> list value_member

(** Substitute in effect signature *)
val subst_in_effect_sig : type_var -> brrr_type -> effect_sig -> effect_sig

(** Substitute in effect signature list *)
val subst_in_effect_sigs : type_var -> brrr_type -> list effect_sig -> list effect_sig

(** Substitute type variable in signature *)
val subst_in_signature : type_var -> brrr_type -> signature -> signature

(** Substitute type variable in module type *)
val subst_in_module_type : type_var -> brrr_type -> module_type -> Tot module_type

(** ============================================================================
    MODULE ENVIRONMENT
    ============================================================================ *)

(** Module environment: maps module variables to their types *)
type module_env = list (module_var & module_type)

(** Empty module environment *)
val empty_module_env : module_env

(** Extend module environment *)
val extend_module_env : module_var -> module_type -> module_env -> module_env

(** Lookup module variable *)
val lookup_module_var : module_var -> module_env -> option module_type

(** Resolve a module path to a module type *)
val resolve_path : module_env -> module_path -> option module_type

(** ============================================================================
    MODULE TYPE CHECKING
    ============================================================================ *)

(** Result of module type checking *)
noeq type module_check_result =
  | ModuleOk  : module_type -> module_check_result
  | ModuleErr : string -> module_check_result

(** Infer signature from module declarations *)
val infer_decls_sig : list module_decl -> signature

(** Type-check a module expression and return its module type *)
val check_module_expr : env:module_env -> me:module_expr -> Tot module_check_result

(** ============================================================================
    FUNCTOR APPLICATION
    ============================================================================ *)

(** Apply a functor type to an argument module type *)
val apply_functor : module_type -> module_type -> option module_type

(** Get functor mode from module type *)
val get_functor_mode : module_type -> option functor_mode

(** Check if functor is applicative *)
val is_applicative_functor : module_type -> bool

(** Check if functor is generative *)
val is_generative_functor : module_type -> bool

(** Get parameter type from functor *)
val get_functor_param : mt:module_type{MTFunctor? mt} -> module_type

(** Functor application preserves well-formedness *)
val functor_app_well_formed : func:module_type -> arg:module_type ->
  Lemma (requires MTFunctor? func /\ module_type_sub arg (get_functor_param func) = true)
        (ensures Some? (apply_functor func arg))

(** ============================================================================
    SEALING SEMANTICS
    ============================================================================ *)

(** Sealing operation: hide implementation details *)
val seal_module : module_type -> module_type -> option module_type

(** Sealing respects subtyping *)
val seal_respects_subtype : impl:module_type -> seal:module_type ->
  Lemma (requires module_type_sub impl seal = true)
        (ensures Some? (seal_module impl seal) /\ Some?.v (seal_module impl seal) == seal)

(** ============================================================================
    WELL-FORMEDNESS PREDICATES
    ============================================================================ *)

(** Well-formed type members *)
val wf_type_members : list type_member -> bool

(** Well-formed signature *)
val wf_signature : signature -> bool

(** Well-formed module type *)
val wf_module_type : module_type -> Tot bool

(** ============================================================================
    SIGNATURE STRENGTHENING
    ============================================================================ *)

(** Strengthen a type member by making it transparent *)
val strengthen_type_member : option brrr_type -> type_member -> type_member

(** Strengthen type members with known definitions *)
val strengthen_type_members : list (type_name & brrr_type) -> list type_member -> list type_member

(** Strengthen signature with known type definitions *)
val strengthen_signature : list (type_name & brrr_type) -> signature -> signature

(** ============================================================================
    SIGNATURE MATCHING
    ============================================================================ *)

(** Check if a module expression matches a module type *)
val check_module_against_type : module_env -> module_expr -> module_type -> module_check_result

(** ============================================================================
    CONVENIENCE CONSTRUCTORS
    ============================================================================ *)

(** Create a simple signature with one value binding *)
val sig_val : var_id -> brrr_type -> signature

(** Create a simple signature with one opaque type *)
val sig_abstract_type : type_name -> kind -> signature

(** Create a simple signature with one transparent type *)
val sig_concrete_type : type_name -> kind -> brrr_type -> signature

(** Create a functor type with default applicative mode *)
val mk_functor_type : module_var -> signature -> signature -> module_type

(** Create a functor type with explicit mode *)
val mk_functor_type_with_mode : module_var -> signature -> signature -> functor_mode -> module_type

(** Create a generative functor type *)
val mk_generative_functor_type : module_var -> signature -> signature -> module_type

(** Create a simple module expression with one value *)
val me_single_val : var_id -> brrr_type -> module_expr

(** Create a sealed module *)
val me_sealed : module_expr -> signature -> module_expr

(** ============================================================================
    WHERE CLAUSES
    ============================================================================ *)

(** A where clause refines an abstract type to a concrete type *)
noeq type where_clause = {
  wc_type_path : type_name;
  wc_definition : brrr_type;
  wc_kind : kind
}

(** Create a where clause with explicit kind *)
val mk_where_clause : type_name -> kind -> brrr_type -> where_clause

(** Create a where clause inferring kind as KStar *)
val mk_where_clause_simple : type_name -> brrr_type -> where_clause

(** Where clause equality *)
val where_clause_eq : where_clause -> where_clause -> bool

(** Where clause equality is reflexive *)
val where_clause_eq_refl : wc:where_clause ->
  Lemma (where_clause_eq wc wc = true) [SMTPat (where_clause_eq wc wc)]

(** Where clause equality is symmetric *)
val where_clause_eq_sym : wc1:where_clause -> wc2:where_clause ->
  Lemma (requires where_clause_eq wc1 wc2 = true)
        (ensures where_clause_eq wc2 wc1 = true)

(** Where clause equality is transitive *)
val where_clause_eq_trans : wc1:where_clause -> wc2:where_clause -> wc3:where_clause ->
  Lemma (requires where_clause_eq wc1 wc2 = true /\ where_clause_eq wc2 wc3 = true)
        (ensures where_clause_eq wc1 wc3 = true)

(** Apply a where clause to type members *)
val apply_where_to_type_members : where_clause -> list type_member -> list type_member

(** Apply a where clause to a signature *)
val apply_where_clause : where_clause -> signature -> signature

(** Apply multiple where clauses in sequence *)
val apply_where_clauses : list where_clause -> signature -> Tot signature

(** ============================================================================
    REFINED SIGNATURE TYPE
    ============================================================================ *)

(** A refined signature is a base signature with where clauses *)
noeq type refined_signature = {
  rs_base : signature;
  rs_wheres : list where_clause
}

(** Create a refined signature from base *)
val refine_signature : signature -> list where_clause -> refined_signature

(** Create from plain signature (no where clauses) *)
val unrefined : signature -> refined_signature

(** Add a where clause to a refined signature *)
val add_where : where_clause -> refined_signature -> refined_signature

(** Flatten a refined signature by applying all where clauses *)
val flatten_refined_sig : refined_signature -> signature

(** Size for termination *)
val refined_sig_size : refined_signature -> nat

(** ============================================================================
    WHERE CLAUSE VALIDATION
    ============================================================================ *)

(** Check if a where clause is valid for a signature *)
val where_clause_valid : where_clause -> signature -> bool

(** Check all where clauses are valid *)
val where_clauses_valid : list where_clause -> signature -> bool

(** Well-formedness of refined signature *)
val wf_refined_signature : refined_signature -> bool

(** Where clause well-kindedness *)
val where_clause_well_kinded : kind_ctx -> where_clause -> bool

(** ============================================================================
    SUBTYPING WITH WHERE CLAUSES
    ============================================================================ *)

(** Where clause subtyping *)
val where_clause_sub : where_clause -> where_clause -> bool

(** Refined signature subtyping *)
val refined_signature_sub : refined_signature -> refined_signature -> bool

(** Where clause subtyping is reflexive *)
val where_clause_sub_refl : wc:where_clause ->
  Lemma (where_clause_sub wc wc = true) [SMTPat (where_clause_sub wc wc)]

(** Where clause subtyping is transitive *)
val where_clause_sub_trans : wc1:where_clause -> wc2:where_clause -> wc3:where_clause ->
  Lemma (requires where_clause_sub wc1 wc2 = true /\ where_clause_sub wc2 wc3 = true)
        (ensures where_clause_sub wc1 wc3 = true)

(** Applying a valid where clause produces a subtype signature *)
val apply_where_produces_subtype : wc:where_clause -> sig:signature ->
  Lemma (requires where_clause_valid wc sig = true /\ wf_sig_names sig = true)
        (ensures signature_sub (apply_where_clause wc sig) sig = true)

(** ============================================================================
    FUNCTOR APPLICATION WITH TYPE SHARING
    ============================================================================ *)

(** Collect type equalities from a signature *)
val collect_type_equalities : signature -> list where_clause

(** Apply functor with sharing *)
val apply_functor_with_sharing : module_type -> module_type -> option refined_signature

(** ============================================================================
    EXTENDED MODULE TYPE WITH WHERE CLAUSES
    ============================================================================ *)

(** Module type with optional where clause refinements *)
noeq type module_type_refined =
  | MTRSig     : refined_signature -> module_type_refined
  | MTRFunctor : module_var -> module_type_refined -> module_type_refined -> functor_mode -> module_type_refined

(** Convert plain module type to refined *)
val module_type_to_refined : module_type -> Tot module_type_refined

(** Flatten refined module type to plain module type *)
val flatten_module_type_refined : module_type_refined -> Tot module_type

(** Add where clause to module type *)
val add_where_to_module_type : where_clause -> module_type_refined -> module_type_refined

(** Size of module_type_refined for termination proofs *)
val module_type_refined_size : module_type_refined -> Tot nat

(** Module type refined subtyping *)
val module_type_refined_sub : module_type_refined -> module_type_refined -> Tot bool

(** ============================================================================
    WHERE CLAUSE LOOKUP
    ============================================================================ *)

(** Lookup type in refined signature *)
val lookup_type_in_refined : type_name -> refined_signature -> option type_member

(** Lookup value in refined signature *)
val lookup_value_in_refined : var_id -> refined_signature -> option value_member

(** Lookup effect in refined signature *)
val lookup_effect_in_refined : string -> refined_signature -> option effect_sig

(** ============================================================================
    SUBSTITUTION IN WHERE CLAUSES
    ============================================================================ *)

(** Substitute type variable in where clause *)
val subst_in_where_clause : type_var -> brrr_type -> where_clause -> where_clause

(** Substitute in where clause list *)
val subst_in_where_clauses : type_var -> brrr_type -> list where_clause -> list where_clause

(** Substitute in refined signature *)
val subst_in_refined_signature : type_var -> brrr_type -> refined_signature -> refined_signature

(** Substitute in refined module type *)
val subst_in_module_type_refined : type_var -> brrr_type -> module_type_refined -> Tot module_type_refined

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR WHERE CLAUSES
    ============================================================================ *)

(** Create signature with single where clause *)
val sig_where : signature -> type_name -> brrr_type -> signature

(** Create signature with multiple where clauses *)
val sig_where_many : signature -> list (type_name & brrr_type) -> signature

(** Create refined signature with where clause *)
val refined_where : signature -> type_name -> kind -> brrr_type -> refined_signature

(** Chain where clauses *)
val chain_where : refined_signature -> type_name -> kind -> brrr_type -> refined_signature

(** ============================================================================
    TYPE SHARING ANALYSIS
    ============================================================================ *)

(** Type sharing info for analysis *)
noeq type type_sharing_info = {
  tsi_path : type_name;
  tsi_shared_with : brrr_type;
  tsi_source : string
}

(** Extract type sharing information from where clauses *)
val where_clause_to_sharing : string -> where_clause -> type_sharing_info

(** Collect all type sharing from a refined signature *)
val collect_sharing_info : string -> refined_signature -> list type_sharing_info

(** Check if two modules share a type *)
val modules_share_type : refined_signature -> refined_signature -> type_name -> bool

(** ============================================================================
    APPLICATIVE VS GENERATIVE FUNCTOR SEMANTICS
    ============================================================================ *)

(** Result of functor application with mode-aware semantics *)
noeq type functor_app_result = {
  far_result_type  : module_type;
  far_mode         : functor_mode;
  far_stamp        : option type_stamp;
  far_type_sharing : list type_sharing_info
}

(** Stamp abstract types in a signature *)
val stamp_signature : type_stamp -> signature -> signature

(** Stamp abstract types in a module type *)
val stamp_module_type : type_stamp -> module_type -> module_type

(** Apply functor with full mode-aware semantics *)
val apply_functor_with_mode : module_type -> module_type -> stamp_state ->
                               option (functor_app_result & stamp_state)

(** Check applicative property *)
val check_applicative_property : module_type -> module_type -> module_type -> bool

(** ============================================================================
    FUNCTOR INSTANTIATION TRACKING
    ============================================================================ *)

(** Functor instantiation record *)
noeq type functor_instantiation = {
  fi_functor_path  : string;
  fi_arg_type      : module_type;
  fi_result_type   : module_type;
  fi_mode          : functor_mode;
  fi_stamp         : option type_stamp;
  fi_location      : string
}

(** Functor instantiation context *)
type functor_instantiation_ctx = list functor_instantiation

(** Empty instantiation context *)
val empty_fi_ctx : functor_instantiation_ctx

(** Record a functor instantiation *)
val record_instantiation : functor_instantiation -> functor_instantiation_ctx -> functor_instantiation_ctx

(** Find all instantiations of a specific functor *)
val find_functor_instantiations : string -> functor_instantiation_ctx -> list functor_instantiation

(** Check if two instantiations share types *)
val instantiations_share_types : functor_instantiation -> functor_instantiation -> bool

(** Collect generative stamps *)
val collect_generative_stamps : functor_instantiation_ctx -> list type_stamp

(** Find conflicting instantiations *)
val find_conflicting_instantiations : functor_instantiation_ctx ->
                                       list (functor_instantiation & functor_instantiation)

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR FUNCTOR MODE
    ============================================================================ *)

(** Create an applicative functor expression *)
val me_applicative_functor : module_var -> module_type -> module_expr -> module_expr

(** Create a generative functor expression *)
val me_generative_functor : module_var -> module_type -> module_expr -> module_expr

(** Create a default (applicative) functor expression *)
val me_functor : module_var -> module_type -> module_expr -> module_expr

(** ============================================================================
    MIXIN COMPOSITION SYSTEM
    ============================================================================ *)

(** A mixin is a partial module with provided and required parts *)
noeq type mixin_signature = {
  mixin_provided : signature;
  mixin_required : signature
}

(** Create an empty mixin *)
val empty_mixin_sig : mixin_signature

(** Create a mixin from a signature (requires nothing) *)
val mixin_from_sig : signature -> mixin_signature

(** Create a pure requirement mixin (provides nothing) *)
val mixin_requires : signature -> mixin_signature

(** Create a mixin with both provided and required *)
val mk_mixin : signature -> signature -> mixin_signature

(** Get all type names from a signature *)
val sig_type_names : signature -> list type_name

(** Get all value names from a signature *)
val sig_value_names : signature -> list var_id

(** Get all effect names from a signature *)
val sig_effect_names : signature -> list string

(** Check if two lists are disjoint *)
val lists_disjoint : #a:eqtype -> list a -> list a -> bool

(** Check if two signatures are name-disjoint *)
val signatures_disjoint : signature -> signature -> bool

(** Well-formedness of mixin signature *)
val wf_mixin_signature : mixin_signature -> bool

(** Mixin signature equality *)
val mixin_signature_eq : mixin_signature -> mixin_signature -> bool

(** Mixin signature equality is reflexive *)
val mixin_signature_eq_refl : m:mixin_signature ->
  Lemma (mixin_signature_eq m m = true) [SMTPat (mixin_signature_eq m m)]

(** Mixin signature equality is symmetric *)
val mixin_signature_eq_sym : m1:mixin_signature -> m2:mixin_signature ->
  Lemma (requires mixin_signature_eq m1 m2 = true)
        (ensures mixin_signature_eq m2 m1 = true)

(** ============================================================================
    INCLUDE AND COMPOSITION OPERATIONS
    ============================================================================ *)

(** Include adds all members from base into extension *)
val include_signature : signature -> signature -> option signature

(** Typing rule for include *)
val include_typing : module_env -> module_path -> option signature

(** Include multiple modules in sequence *)
val include_signatures : list signature -> option signature

(** Compose two signatures (disjoint union) *)
val compose_signatures : signature -> signature -> option signature

(** Compose two module types *)
val compose_module_types : module_type -> module_type -> option module_type

(** Compose multiple module types in sequence *)
val compose_module_types_list : list module_type -> option module_type

(** Composition is commutative for signatures *)
val compose_signatures_commutative : s1:signature -> s2:signature ->
  Lemma (requires signatures_disjoint s1 s2 = true)
        (ensures signatures_disjoint s2 s1 = true)

(** ============================================================================
    MIXIN LINEAR COMPOSITION
    ============================================================================ *)

(** Remove satisfied requirements from a signature *)
val remove_satisfied : signature -> signature -> signature

(** Compose two mixin signatures *)
val compose_mixin_signatures : mixin_signature -> mixin_signature -> option mixin_signature

(** ============================================================================
    OVERRIDE MECHANISM
    ============================================================================ *)

(** Override specification *)
noeq type override_spec =
  | OverrideType   : type_name -> brrr_type -> override_spec
  | OverrideVal    : var_id -> brrr_type -> override_spec
  | OverrideEffect : effect_sig -> override_spec

(** Get the name being overridden *)
val override_name : override_spec -> string

(** Apply a single override to a signature *)
val apply_override : override_spec -> signature -> signature

(** Apply multiple overrides in sequence *)
val apply_overrides : list override_spec -> signature -> signature

(** Check if an override is valid for a signature *)
val override_valid : override_spec -> signature -> bool

(** Validate all overrides *)
val overrides_valid : list override_spec -> signature -> bool

(** ============================================================================
    DIAMOND PROBLEM DETECTION AND RESOLUTION
    ============================================================================ *)

(** A diamond conflict represents a name collision *)
noeq type diamond_conflict =
  | TypeConflict   : type_name -> type_member -> type_member -> diamond_conflict
  | ValueConflict  : var_id -> value_member -> value_member -> diamond_conflict
  | EffectConflict : string -> effect_sig -> effect_sig -> diamond_conflict

(** Get the conflict name *)
val conflict_name : diamond_conflict -> string

(** Find all diamond conflicts between two signatures *)
val find_diamond_conflicts : signature -> signature -> list diamond_conflict

(** Check if a conflict is resolved by an override *)
val conflict_resolved_by : diamond_conflict -> override_spec -> bool

(** Check if all conflicts are resolved *)
val all_conflicts_resolved : list diamond_conflict -> list override_spec -> bool

(** Compose with diamond resolution *)
val compose_with_resolution : signature -> signature -> list override_spec -> option signature

(** ============================================================================
    MIXIN COMPLETION
    ============================================================================ *)

(** Check if an implementation satisfies mixin requirements *)
val mixin_requirements_satisfied : mixin_signature -> signature -> bool

(** Complete a mixin with an implementation *)
val complete_mixin : mixin_signature -> signature -> option signature

(** Complete a mixin with conflict resolution *)
val complete_mixin_with_resolution : mixin_signature -> signature -> list override_spec -> option signature

(** ============================================================================
    MIXIN-AWARE MODULE EXPRESSIONS
    ============================================================================ *)

(** Mixin-aware module expression *)
noeq type mixin_module_expr =
  | MMStruct   : list module_decl -> mixin_module_expr
  | MMFunctor  : module_var -> module_type -> functor_mode -> mixin_module_expr -> mixin_module_expr
  | MMApp      : mixin_module_expr -> mixin_module_expr -> mixin_module_expr
  | MMPath     : module_path -> mixin_module_expr
  | MMSeal     : mixin_module_expr -> module_type -> mixin_module_expr
  | MMInclude  : mixin_module_expr -> mixin_module_expr
  | MMCompose  : mixin_module_expr -> mixin_module_expr -> mixin_module_expr
  | MMWith     : mixin_module_expr -> list override_spec -> mixin_module_expr
  | MMMixin    : mixin_signature -> mixin_module_expr

(** Convert regular module_expr to mixin_module_expr *)
val module_expr_to_mixin : module_expr -> Tot mixin_module_expr

(** ============================================================================
    MIXIN MODULE TYPE CHECKING
    ============================================================================ *)

(** Result of mixin module type checking *)
noeq type mixin_check_result =
  | MixinOk    : module_type -> mixin_check_result
  | MixinPart  : mixin_signature -> mixin_check_result
  | MixinErr   : string -> mixin_check_result

(** Type-check a mixin module expression *)
val check_mixin_module : module_env -> mixin_module_expr -> Tot mixin_check_result

(** ============================================================================
    MIXIN ANALYSIS
    ============================================================================ *)

(** Mixin provenance *)
noeq type mixin_provenance = {
  mp_mixin_name : string;
  mp_binding_name : string;
  mp_binding_kind : string;
  mp_is_override : bool;
  mp_original_source : option string
}

(** Mixin dependency edge *)
noeq type mixin_dependency = {
  md_provider : string;
  md_consumer : string;
  md_binding : string;
  md_kind : string
}

(** Mixin analysis context *)
noeq type mixin_analysis_ctx = {
  mac_provenances : list mixin_provenance;
  mac_dependencies : list mixin_dependency;
  mac_conflicts : list diamond_conflict;
  mac_unresolved : list diamond_conflict
}

(** Empty analysis context *)
val empty_mixin_analysis_ctx : mixin_analysis_ctx

(** Record provenance for a type member *)
val record_type_provenance : string -> type_member -> bool -> mixin_provenance

(** Record provenance for a value member *)
val record_value_provenance : string -> value_member -> bool -> mixin_provenance

(** Record a dependency between mixins *)
val record_dependency : string -> string -> string -> string -> mixin_dependency

(** Analyze a mixin composition *)
val analyze_mixin_composition : string -> mixin_signature -> string -> mixin_signature -> mixin_analysis_ctx

(** Mark conflicts as resolved *)
val mark_conflicts_resolved : mixin_analysis_ctx -> list override_spec -> mixin_analysis_ctx

(** Check if analysis found any issues *)
val mixin_analysis_has_errors : mixin_analysis_ctx -> bool

(** Get all unresolved conflict names *)
val get_unresolved_conflict_names : mixin_analysis_ctx -> list string

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR MIXINS
    ============================================================================ *)

(** Create a simple mixin with one type requirement *)
val mixin_require_type : type_name -> kind -> mixin_signature

(** Create a simple mixin with one value requirement *)
val mixin_require_val : var_id -> brrr_type -> mixin_signature

(** Create a mixin that provides a type *)
val mixin_provide_type : type_name -> kind -> brrr_type -> mixin_signature

(** Create a mixin that provides a value *)
val mixin_provide_val : var_id -> brrr_type -> mixin_signature

(** Create a mixin expression from a signature *)
val mm_from_sig : signature -> mixin_module_expr

(** Create a composition expression *)
val mm_compose : mixin_module_expr -> mixin_module_expr -> mixin_module_expr

(** Create a with-override expression *)
val mm_with : mixin_module_expr -> list override_spec -> mixin_module_expr

(** Create an include expression *)
val mm_include : mixin_module_expr -> mixin_module_expr

(** ============================================================================
    MODULE DEPENDENCY GRAPH
    ============================================================================ *)

(** Module name type *)
type module_name = string

(** Dependency edge *)
noeq type dep_edge = {
  de_from : module_name;
  de_to   : module_name;
  de_kind : string
}

(** Dependency graph *)
noeq type dep_graph = {
  dg_nodes : list module_name;
  dg_edges : list dep_edge
}

(** Empty dependency graph *)
val empty_dep_graph : dep_graph

(** Add a module to the graph *)
val add_module_to_graph : module_name -> dep_graph -> dep_graph

(** Add a dependency edge to the graph *)
val add_dep_edge : dep_edge -> dep_graph -> dep_graph

(** Get all modules that a given module depends on *)
val get_dependencies : module_name -> dep_graph -> list module_name

(** Get all modules that depend on a given module *)
val get_dependents : module_name -> dep_graph -> list module_name

(** ============================================================================
    CIRCULAR DEPENDENCY DETECTION
    ============================================================================ *)

(** DFS state for cycle detection *)
noeq type dfs_state = {
  ds_visited  : list module_name;
  ds_in_stack : list module_name;
  ds_cycle    : option (list module_name)
}

(** Initial DFS state *)
val init_dfs_state : dfs_state

(** Check if we've found a cycle *)
val has_cycle : dfs_state -> bool

(** Check if node is visited *)
val is_visited : module_name -> dfs_state -> bool

(** Check if node is in current DFS stack *)
val is_in_stack : module_name -> dfs_state -> bool

(** Mark node as visited *)
val finish_node : module_name -> dfs_state -> dfs_state

(** Push node onto DFS stack *)
val push_stack : module_name -> dfs_state -> dfs_state

(** Extract cycle from stack *)
val extract_cycle : module_name -> dfs_state -> list module_name

(** Record a detected cycle *)
val record_cycle : module_name -> dfs_state -> dfs_state

(** DFS visit with fuel *)
val dfs_visit : dep_graph -> module_name -> dfs_state -> nat -> Tot dfs_state

(** DFS visit all nodes *)
val dfs_visit_all : dep_graph -> list module_name -> dfs_state -> nat -> Tot dfs_state

(** Detect cycles in the dependency graph *)
val detect_circular_deps : dep_graph -> option (list module_name)

(** Check if dependency graph is acyclic *)
val is_acyclic : dep_graph -> bool

(** ============================================================================
    TOPOLOGICAL SORT
    ============================================================================ *)

(** Compute in-degrees for each node *)
val compute_in_degrees : dep_graph -> list (module_name & nat)

(** Find nodes with zero in-degree *)
val find_zero_indegree : list (module_name & nat) -> list module_name

(** Topological sort of dependency graph *)
val topological_sort : dep_graph -> option (list module_name)

(** Reverse topological sort *)
val reverse_topological_sort : dep_graph -> option (list module_name)

(** ============================================================================
    MODULE DEPENDENCY LEMMAS
    ============================================================================ *)

(** Empty graph is acyclic *)
val empty_graph_acyclic : unit -> Lemma (is_acyclic empty_dep_graph = true)

(** Adding module preserves length *)
val add_module_preserves_length : name:module_name -> g:dep_graph ->
  Lemma (List.Tot.length (add_module_to_graph name g).dg_nodes >= List.Tot.length g.dg_nodes)

(** Adding edge preserves nodes *)
val add_edge_preserves_nodes : e:dep_edge -> g:dep_graph ->
  Lemma (List.Tot.length (add_dep_edge e g).dg_nodes >= List.Tot.length g.dg_nodes)

(** Topological sort of acyclic graph succeeds *)
val module_deps_acyclic : g:dep_graph ->
  Lemma (requires is_acyclic g = true)
        (ensures Some? (topological_sort g))

(** ============================================================================
    IMPORT VERIFICATION
    ============================================================================ *)

(** Module import record *)
noeq type module_import = {
  mi_from   : module_name;
  mi_items  : list string;
  mi_alias  : option string
}

(** Import resolution result *)
noeq type import_result =
  | ImportOk    : signature -> import_result
  | ImportErr   : string -> import_result

(** Well-formed kind check *)
val wf_kind : kind_ctx -> kind -> bool

(** Check if a type has a given kind *)
val type_has_kind : kind_ctx -> brrr_type -> kind -> bool

(** Check if dst_ctx extends src_ctx *)
val kind_ctx_extends : kind_ctx -> kind_ctx -> bool

(** Check imported types are well-formed *)
val check_imported_types_wf : kind_ctx -> list type_member -> bool

(** Importing preserves types *)
val import_preserves_types : src_ctx:kind_ctx -> dst_ctx:kind_ctx -> types:list type_member ->
  Lemma (requires check_imported_types_wf src_ctx types = true /\ kind_ctx_extends dst_ctx src_ctx = true)
        (ensures check_imported_types_wf dst_ctx types = true)

(** Build dependency graph from imports *)
val build_import_graph : module_name -> list module_import -> dep_graph -> dep_graph

(** Validate imports don't create circular dependencies *)
val validate_imports_acyclic : module_name -> list module_import -> dep_graph -> option (list module_name)
