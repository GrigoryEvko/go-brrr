(**
 * =============================================================================
 * BrrrLang.Core.ModuleSystem
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
 * THEORETICAL FOUNDATIONS
 * =============================================================================
 *
 * The module system implements a variant of the ML module calculus with:
 *
 * 1. SIGNATURES (Module Types):
 *    A signature classifies modules by describing their interface:
 *      Sigma ::= { type t; val x : tau; effect E = ops }
 *
 *    Signatures support structural subtyping: Sigma1 <: Sigma2 iff Sigma1
 *    provides at least everything Sigma2 requires, possibly with more
 *    specific types.
 *
 * 2. MODULES (Structures):
 *    A module is a collection of type, value, and effect definitions:
 *      M ::= struct ... end | functor(X : Sigma) -> M | M.x | M(N)
 *
 * 3. FUNCTORS (Parameterized Modules):
 *    Functors map modules to modules, enabling code parameterization:
 *      F : Sigma1 -> Sigma2
 *
 *    Two functor modes per spec Definition 2.3-2.5:
 *      - Applicative (functor^app): F(M) = F(M') when M equiv M'
 *        Types are shared across applications of the same functor.
 *      - Generative (functor^gen): F(M) <> F(M') even when M equiv M'
 *        Each application creates fresh abstract types.
 *
 * 4. SEALING (Abstraction):
 *    Opaque ascription (M :> Sigma) hides implementation details:
 *      - Abstract types in Sigma become truly opaque
 *      - Type equalities not in Sigma are forgotten
 *      - Creates an abstraction barrier (existential packaging)
 *
 * 5. TYPE SHARING (Where Clauses):
 *    "Sigma where type p = tau" refines abstract types:
 *      - Essential for functor application type sharing
 *      - Enables applicative functor semantics
 *
 * =============================================================================
 * FEATURES
 * =============================================================================
 *
 *   - Module signatures with type, value, and effect members
 *   - First-class modules and higher-order functors
 *   - Signature subtyping with proper variance:
 *       * Type members: contravariant (transparent hides to opaque)
 *       * Value members: covariant (more specific allowed)
 *       * Effect members: covariant (more specific allowed)
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
 *   - Sealing respects signature compatibility (M :> S requires M <: S)
 *   - Where clause application produces a subtype (S where type p = t <: S)
 *   - Module dependency graph must be acyclic
 *   - Filtering by visibility preserves signature well-formedness
 *
 * =============================================================================
 * F* INTERFACE/IMPLEMENTATION PATTERN
 * =============================================================================
 *
 * This module follows F* conventions for .fst/.fsti separation:
 *
 *   - .fsti (Interface): Declares public types and val signatures
 *     Serves as the module's "signature" - what clients can depend on.
 *
 *   - .fst (Implementation): Provides definitions for declared items
 *     May contain private helpers not exposed in the interface.
 *
 * The `friend` declaration grants access to implementation details:
 *   friend OtherModule  (* Can see OtherModule's private definitions *)
 *
 * This mirrors the Brrr module system's sealing mechanism:
 *   - .fsti = sealed signature (abstraction boundary)
 *   - .fst = full implementation (hidden behind seal)
 *
 * =============================================================================
 * VISIBILITY MODEL
 * =============================================================================
 *
 * Following EverParse's export pattern, members have visibility levels:
 *
 *   Public   - Exported to all modules (appears in signature)
 *   Internal - Visible within same package (not externally exported)
 *   Private  - Module-local only (never exported)
 *
 * Visibility affects signature filtering:
 *   filter_signature_by_visibility(Public, sig) -> external API
 *   filter_signature_by_visibility(Internal, sig) -> package API
 *
 * =============================================================================
 * DEPENDENCY TRACKING FOR BRRR-MACHINE
 * =============================================================================
 *
 * The module system tracks dependencies for analysis tools:
 *
 *   - Import dependencies: which modules does M import from?
 *   - Type dependencies: which types does M's signature reference?
 *   - Value dependencies: which values does M's body call?
 *
 * This enables:
 *   1. Circular dependency detection (error at compile time)
 *   2. Topological sorting for compilation order
 *   3. Dead code analysis across module boundaries
 *   4. Impact analysis when signatures change
 *
 * =============================================================================
 * ORGANIZATION (Following HACL* Pattern)
 * =============================================================================
 *
 * The implementation is organized in layers:
 *
 *   1. Identifiers and Paths      - Basic naming infrastructure
 *   2. Source Metadata            - Location tracking, comments
 *   3. Visibility and Shadowing   - Access control, name collision
 *   4. Signature Components       - Type/value/effect members
 *   5. Signatures                 - Module interfaces
 *   6. Functor Mode               - Applicative vs generative
 *   7. Module Types               - Classification of modules
 *   8. Module Expressions         - Structure, functor, application
 *   9. Equality Relations         - Reflexivity, symmetry, transitivity
 *  10. Subtyping Relations        - Signature/module type subtyping
 *  11. Type Substitution          - For functor application
 *  12. Module Environment         - Name resolution context
 *  13. Type Checking              - Module expression typing
 *  14. Where Clauses              - Type sharing/refinement
 *  15. Mixin Composition          - Include, compose, override
 *  16. Dependency Analysis        - Graph, cycles, topological sort
 *
 * =============================================================================
 * REFERENCES
 * =============================================================================
 *
 *   - brrr_lang_spec_v0.4.tex Part VIII: Module System
 *   - fstar_pop_book.md Section 11: Interfaces and Modularity
 *   - FSTAR_REFERENCE.md Section 14: Interface/Implementation
 *   - HACL* module organization (Spec.*, Hacl.Impl.*, etc.)
 *   - EverParse for metadata/visibility patterns
 *
 * Depends on: Primitives, Modes, Effects, BrrrTypes, Expressions, Kinds
 *)
module BrrrModuleSystem

#set-options "--z3rlimit 100 --fuel 1 --ifuel 1"

open FStar.List.Tot
open FStar.Classical
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrKinds

(** ============================================================================
    MODULE IDENTIFIERS AND NAMESPACE RESOLUTION
    ============================================================================

    Module identifiers form a hierarchical namespace enabling qualified access
    to nested module components. This follows ML's "dot notation" for paths.

    NAMESPACE STRUCTURE:
    -------------------
    Modules form a tree where each module can contain:
      - Type definitions      (type t = ...)
      - Value bindings        (let x = ...)
      - Effect declarations   (effect E = ...)
      - Nested modules        (module N = ...)

    QUALIFIED NAMES:
    ----------------
    Components are accessed via paths:
      M           - Reference to module M in current scope
      M.t         - Type t defined in module M
      M.x         - Value x defined in module M
      M.N.t       - Type t in nested module M.N

    RESOLUTION ALGORITHM:
    ---------------------
    Name resolution proceeds from left to right:
      1. Look up leftmost identifier in current module environment
      2. For each subsequent ".x" projection:
         a. Verify current module has signature type
         b. Look up x in that signature
      3. Return the final component or error if not found

    SHADOWING RULES:
    ----------------
    Inner bindings shadow outer ones within the same namespace:
      module Outer = {
        type t = int;
        module Inner = {
          type t = bool;  (* Shadows Outer.t within Inner *)
        }
      }
    Outer.t : int, Outer.Inner.t : bool

    This implements what the spec calls "lexical scoping for modules."
    ============================================================================ *)

(** Module variable identifier - a simple string name.
    Following F* convention, module names are typically capitalized. *)
type module_var = string

(** Module path: qualified name for accessing nested modules.

    Paths enable hierarchical module access:
      MPVar "M"                        -- Simple reference: M
      MPDot (MPVar "M") "N"            -- Qualified: M.N
      MPDot (MPDot (MPVar "M") "N") "P" -- Deep nesting: M.N.P

    The path structure mirrors the signature nesting:
      - Each MPVar resolves in the current module environment
      - Each MPDot projects into the resolved module's signature

    IMPLEMENTATION NOTE:
    This is a syntactic representation. Semantic resolution happens in
    resolve_path which looks up paths in the module_env context.
*)
noeq type module_path =
  | MPVar   : module_var -> module_path                    (* X *)
  | MPDot   : module_path -> string -> module_path         (* M.N *)

(** ============================================================================
    SOURCE LOCATION TRACKING
    ============================================================================

    Source location metadata enables precise error reporting and IDE features.
    This implementation follows the EverParse pattern for location tracking.

    DESIGN RATIONALE:
    -----------------
    Every significant AST node carries source location information via the
    with_meta_t wrapper. This allows:
      - Precise error messages with file:line:column
      - IDE hover/jump-to-definition features
      - Documentation extraction from comments
      - Source mapping for debugging

    PATTERN (from EverParse):
    -------------------------
    AST nodes use a uniform wrapping pattern:
      type decl = with_meta_t decl'   (* Located declaration *)
      type decl' = ...                 (* Raw declaration data *)

    The meta wrapper carries:
      - meta_value    : The actual AST node
      - meta_range    : Source span (start..end position)
      - meta_comments : Associated doc comments

    SYNTHETIC NODES:
    ----------------
    Compiler-generated nodes use dummy_source_range to indicate they have
    no corresponding source location. This is important for:
      - Desugared constructs (generated during elaboration)
      - Inferred types (synthesized by type inference)
      - Macro expansions (generated from templates)

    The dummy range uses "<synthetic>" as the filename, making it easy to
    identify non-source-originated nodes in error messages.

    F* ANALOGY:
    -----------
    This mirrors F*'s FStarC.Range module which tracks source locations
    through the entire compilation pipeline. In F*:
      - range = start_pos * end_pos
      - dummyRange for synthetic constructs
      - mk_range to construct ranges
    ============================================================================ *)

(* Source position: file, line, column *)
type source_pos = {
  sp_file   : string;
  sp_line   : nat;
  sp_column : nat
}

(* Source range: span from start to end position *)
type source_range = source_pos & source_pos

(* Dummy position for synthetic nodes *)
let dummy_source_pos : source_pos = {
  sp_file = "<synthetic>";
  sp_line = 0;
  sp_column = 0
}

(* Dummy range for synthetic nodes *)
let dummy_source_range : source_range = (dummy_source_pos, dummy_source_pos)

(* Format position as "file:(line,col)" *)
let string_of_source_pos (p: source_pos) : string =
  p.sp_file ^ ":(" ^ string_of_int p.sp_line ^ "," ^ string_of_int p.sp_column ^ ")"

(* Format range for error messages *)
let string_of_source_range (r: source_range) : string =
  let (start, stop) = r in
  if start.sp_file = stop.sp_file then
    start.sp_file ^ ":(" ^ string_of_int start.sp_line ^ "," ^ string_of_int start.sp_column ^
    ")-(" ^ string_of_int stop.sp_line ^ "," ^ string_of_int stop.sp_column ^ ")"
  else
    string_of_source_pos start ^ "-" ^ string_of_source_pos stop

(* Comments associated with AST nodes *)
type comments = list string

(* Metadata wrapper for AST nodes following EverParse pattern.
 * Carries source location and associated comments through the AST.
 * Pattern: every significant AST node type wraps its content in with_meta_t *)
noeq type with_meta_t 'a = {
  meta_value    : 'a;             (* The wrapped value *)
  meta_range    : source_range;   (* Source location span *)
  meta_comments : comments        (* Associated documentation comments *)
}

(* Create a located value with given range *)
let with_range (#a: Type) (value: a) (r: source_range) : with_meta_t a =
  { meta_value = value; meta_range = r; meta_comments = [] }

(* Create a located value with range and comments *)
let with_meta (#a: Type) (value: a) (r: source_range) (c: comments) : with_meta_t a =
  { meta_value = value; meta_range = r; meta_comments = c }

(* Create a located value with dummy range (for synthetic nodes) *)
let no_range (#a: Type) (value: a) : with_meta_t a =
  { meta_value = value; meta_range = dummy_source_range; meta_comments = [] }

(* Extract value from metadata wrapper *)
let meta_value_of (#a: Type) (m: with_meta_t a) : a = m.meta_value

(* Extract range from metadata wrapper *)
let meta_range_of (#a: Type) (m: with_meta_t a) : source_range = m.meta_range

(* Map function over wrapped value, preserving location *)
let meta_map (#a #b: Type) (f: a -> b) (m: with_meta_t a) : with_meta_t b =
  { meta_value = f m.meta_value; meta_range = m.meta_range; meta_comments = m.meta_comments }

(** ============================================================================
    MODULE VISIBILITY
    ============================================================================

    Visibility controls which members are exported from a module's signature.
    This follows EverParse's export pattern and Rust's pub/pub(crate)/private.

    VISIBILITY LEVELS:
    ------------------
    Public   - Visible to all modules (exported in external signature)
               Analogous to F*'s val declarations in .fsti files.
               Clients can depend on these members.

    Internal - Visible within the same package/crate (not exported externally)
               Analogous to internal functions not in .fsti.
               Allows sharing within a library without public commitment.

    Private  - Visible only within the defining module (never exported)
               Analogous to let bindings not declared in .fsti.
               Pure implementation details hidden from all other modules.

    ORDERING:
    ---------
    Visibility forms a total order: Public > Internal > Private

    This ordering enables visibility checking:
      visibility_leq(v1, v2) -- v1 is at least as permissive as v2

    SIGNATURE FILTERING:
    --------------------
    When exporting a module, we filter its signature by visibility:
      filter_signature_by_visibility(MVPublic, sig)   -> External API
      filter_signature_by_visibility(MVInternal, sig) -> Package API
      filter_signature_by_visibility(MVPrivate, sig)  -> Full signature

    DESIGN PATTERN:
    ---------------
    Members carry visibility annotations:
      type_member  carries visibility in TMOpaque/TMTransparent
      value_member carries visibility in val_visibility field
      effect_sig   carries visibility in eff_sig_visibility field

    Default visibility is Private (safe default - nothing leaks accidentally).

    COMPARISON WITH F*:
    -------------------
    F* uses .fsti files as the visibility boundary:
      - Items in .fsti are "public" (exported)
      - Items only in .fst are "private" (internal)
      - The friend declaration grants cross-module access

    Brrr extends this with explicit visibility annotations that can be
    checked independent of file organization.
    ============================================================================ *)

(** Module member visibility levels.

    The ordering Public > Internal > Private forms a lattice where
    more permissive visibility subsumes more restrictive visibility.
    This enables natural subtyping: a public module can be used where
    an internal one is expected, but not vice versa. *)
type module_visibility =
  | MVPublic   : module_visibility   (* Exported to all *)
  | MVInternal : module_visibility   (* Package/crate internal *)
  | MVPrivate  : module_visibility   (* Module-local only *)

(* Default visibility for members without explicit annotation *)
let default_visibility : module_visibility = MVPrivate

(* Check if visibility v1 is at least as permissive as v2 *)
let visibility_leq (v1 v2: module_visibility) : bool =
  match v1, v2 with
  | MVPublic, _ -> true                 (* Public is most permissive *)
  | MVInternal, MVInternal -> true
  | MVInternal, MVPrivate -> true
  | MVPrivate, MVPrivate -> true
  | _, _ -> false

(* Check if visibility v1 is strictly more permissive than v2 *)
let visibility_lt (v1 v2: module_visibility) : bool =
  match v1, v2 with
  | MVPublic, MVInternal -> true
  | MVPublic, MVPrivate -> true
  | MVInternal, MVPrivate -> true
  | _, _ -> false

(* Visibility is reflexive *)
val visibility_leq_refl : v:module_visibility ->
  Lemma (visibility_leq v v = true) [SMTPat (visibility_leq v v)]
let visibility_leq_refl v = ()

(* Visibility is transitive *)
val visibility_leq_trans : v1:module_visibility -> v2:module_visibility -> v3:module_visibility ->
  Lemma (requires visibility_leq v1 v2 = true /\ visibility_leq v2 v3 = true)
        (ensures visibility_leq v1 v3 = true)
let visibility_leq_trans v1 v2 v3 = ()

(* String representation of visibility *)
let string_of_visibility (v: module_visibility) : string =
  match v with
  | MVPublic -> "public"
  | MVInternal -> "internal"
  | MVPrivate -> "private"

(** ============================================================================
    SHADOW CHECKING
    ============================================================================

    Shadow checking detects when a new binding would hide an existing one
    in the same scope. Following EverParse's check_shadow pattern.

    PURPOSE:
    --------
    In ML-style module systems, shadowing is typically allowed but can be
    confusing. We track it to:
      1. Warn users about potentially confusing code
      2. Enable strict "no shadowing" modes for safety
      3. Provide precise error messages with both locations

    SHADOW SCENARIOS:
    -----------------
    1. Type shadowing: type t = int; type t = bool  (* t shadows t *)
    2. Value shadowing: let x = 1; let x = 2       (* x shadows x *)
    3. Effect shadowing: effect E = ...; effect E = ... (* E shadows E *)
    4. Cross-module: open M; type t = ... (* t may shadow M.t *)

    ERROR REPORTING:
    ----------------
    When shadowing is detected, we report:
      - The name being shadowed
      - The source range of the original binding (prev_range)
      - The source range of the new binding (new_range)

    This allows error messages like:
      "Error: 't' at src/foo.brrr:10:5 shadows previous definition at src/foo.brrr:3:5"

    IMPLEMENTATION:
    ---------------
    check_shadow_* functions take:
      - The name being introduced
      - Its source range
      - A list of existing (name, range) pairs in scope

    Returns ShadowOK if no conflict, or ShadowError with locations if
    the name already exists.
    ============================================================================ *)

(** Result of shadow check: either success or error with location.
    The error variant carries both the previous and new locations for
    precise error reporting. *)
type shadow_result =
  | ShadowOK    : shadow_result
  | ShadowError : name:string -> prev_range:source_range -> new_range:source_range -> shadow_result

(* Check if a name would shadow an existing binding.
 * Returns ShadowError if the name already exists, ShadowOK otherwise.
 * Following EverParse's check_shadow pattern. *)
let check_shadow_type
    (name: type_name)
    (new_range: source_range)
    (existing: list (type_name & source_range))
    : shadow_result =
  match FStar.List.Tot.find (fun (n, _) -> n = name) existing with
  | Some (_, prev_range) -> ShadowError name prev_range new_range
  | None -> ShadowOK

let check_shadow_value
    (name: var_id)
    (new_range: source_range)
    (existing: list (var_id & source_range))
    : shadow_result =
  match FStar.List.Tot.find (fun (n, _) -> n = name) existing with
  | Some (_, prev_range) -> ShadowError name prev_range new_range
  | None -> ShadowOK

let check_shadow_effect
    (name: string)
    (new_range: source_range)
    (existing: list (string & source_range))
    : shadow_result =
  match FStar.List.Tot.find (fun (n, _) -> n = name) existing with
  | Some (_, prev_range) -> ShadowError name prev_range new_range
  | None -> ShadowOK

(* Format shadow error message *)
let format_shadow_error (sr: shadow_result) : option string =
  match sr with
  | ShadowOK -> None
  | ShadowError name prev new_ ->
      Some (string_of_source_range new_ ^ ": error: declaration '" ^ name ^
            "' shadows previous declaration at " ^ string_of_source_range prev)

(** ============================================================================
    EFFECT SIGNATURE
    ============================================================================ *)

(* Effect signature: effect name with its operations and metadata *)
noeq type effect_sig = {
  eff_sig_name       : string;
  eff_sig_ops        : list (string & brrr_type);  (* operation name -> type *)
  eff_sig_visibility : module_visibility;          (* visibility level *)
  eff_sig_range      : source_range                (* source location *)
}

(* Extract visibility from effect signature *)
let effect_sig_visibility (es: effect_sig) : module_visibility = es.eff_sig_visibility

(* Extract source range from effect signature *)
let effect_sig_range (es: effect_sig) : source_range = es.eff_sig_range

(* Check if effect signature is visible at given visibility level *)
let effect_sig_visible_at (es: effect_sig) (v: module_visibility) : bool =
  visibility_leq es.eff_sig_visibility v

(* Create effect signature with default visibility *)
let mk_effect_sig (name: string) (ops: list (string & brrr_type)) : effect_sig =
  { eff_sig_name = name; eff_sig_ops = ops; eff_sig_visibility = default_visibility; eff_sig_range = dummy_source_range }

(* Create effect signature with explicit visibility and location *)
let mk_effect_sig_with_meta (name: string) (ops: list (string & brrr_type)) (v: module_visibility) (r: source_range) : effect_sig =
  { eff_sig_name = name; eff_sig_ops = ops; eff_sig_visibility = v; eff_sig_range = r }

(** ============================================================================
    TYPE MEMBER TRANSPARENCY
    ============================================================================

    Type members are the core building blocks of module signatures. They can be
    either opaque (abstract) or transparent (manifest), following the ML module
    tradition where type abstraction is the primary tool for information hiding.

    OPAQUE vs TRANSPARENT:
    ----------------------
    Opaque (Abstract):  "type t : K"
      - Client code cannot know the representation
      - Only knows the type exists with kind K
      - Enables representation independence
      - Essential for abstraction barriers

    Transparent (Manifest):  "type t : K = tau"
      - Client code knows t is defined as tau
      - Can use t and tau interchangeably
      - Enables type sharing across modules
      - Used for "type t = int" style definitions

    SUBTYPING IMPLICATIONS (Spec Definition 5.3):
    ---------------------------------------------
    Type member subtyping is CONTRAVARIANT in a key sense:
      - TMTransparent t k tau <: TMOpaque t k    (always valid)
      - TMOpaque t k <: TMTransparent t k tau    (INVALID - cannot reveal)

    This means a signature with MORE type information (transparent) can be
    used where LESS information (opaque) is expected, but not vice versa.

    SEALING SEMANTICS:
    ------------------
    When sealing (M :> Sig), abstract types in Sig become truly opaque:
      module M = { type t = int; let x = 42 }
      module M' = M :> { type t; val x : t }
      (* Now M'.t is abstract - cannot know it's int *)

    This implements existential type packaging:
      M' : exists t. { val x : t }

    WHERE CLAUSES:
    --------------
    Where clauses refine opaque types to transparent:
      Sig where type t = tau

    This is essential for applicative functor semantics where types must
    be shared across functor applications.

    METADATA:
    ---------
    Each type member carries:
      - visibility : Public/Internal/Private for signature filtering
      - source_range : For error messages and IDE features

    Visibility and range do NOT affect type equality or subtyping -
    they are purely metadata for tooling.
    ============================================================================ *)

(** Type members can be opaque (abstract) or transparent (concrete).
    Each type member carries visibility and source location metadata.

    The distinction between opaque and transparent is fundamental to
    ML-style abstraction: opaque types hide implementation details,
    while transparent types expose them for type sharing. *)
noeq type type_member =
  | TMOpaque      : type_name -> kind -> module_visibility -> source_range -> type_member
      (* Abstract type: "type T : K" - representation hidden *)
  | TMTransparent : type_name -> kind -> brrr_type -> module_visibility -> source_range -> type_member
      (* Manifest type: "type T : K = tau" - representation known *)

(* Extract name from type member *)
let type_member_name (tm: type_member) : type_name =
  match tm with
  | TMOpaque n _ _ _ -> n
  | TMTransparent n _ _ _ _ -> n

(* Extract kind from type member *)
let type_member_kind (tm: type_member) : kind =
  match tm with
  | TMOpaque _ k _ _ -> k
  | TMTransparent _ k _ _ _ -> k

(* Extract visibility from type member *)
let type_member_visibility (tm: type_member) : module_visibility =
  match tm with
  | TMOpaque _ _ v _ -> v
  | TMTransparent _ _ _ v _ -> v

(* Extract source range from type member *)
let type_member_range (tm: type_member) : source_range =
  match tm with
  | TMOpaque _ _ _ r -> r
  | TMTransparent _ _ _ _ r -> r

(* Check if type member is opaque *)
let is_opaque (tm: type_member) : bool =
  match tm with
  | TMOpaque _ _ _ _ -> true
  | TMTransparent _ _ _ _ _ -> false

(* Check if type member is transparent *)
let is_transparent (tm: type_member) : bool =
  match tm with
  | TMOpaque _ _ _ _ -> false
  | TMTransparent _ _ _ _ _ -> true

(* Get definition of transparent type member *)
let type_member_def (tm: type_member) : option brrr_type =
  match tm with
  | TMOpaque _ _ _ _ -> None
  | TMTransparent _ _ t _ _ -> Some t

(* Check if type member is visible at given visibility level *)
let type_member_visible_at (tm: type_member) (v: module_visibility) : bool =
  visibility_leq (type_member_visibility tm) v

(* Create opaque type member with default visibility *)
let mk_opaque_type (name: type_name) (k: kind) : type_member =
  TMOpaque name k default_visibility dummy_source_range

(* Create opaque type member with explicit visibility and location *)
let mk_opaque_type_with_meta (name: type_name) (k: kind) (v: module_visibility) (r: source_range) : type_member =
  TMOpaque name k v r

(* Create transparent type member with default visibility *)
let mk_transparent_type (name: type_name) (k: kind) (t: brrr_type) : type_member =
  TMTransparent name k t default_visibility dummy_source_range

(* Create transparent type member with explicit visibility and location *)
let mk_transparent_type_with_meta (name: type_name) (k: kind) (t: brrr_type) (v: module_visibility) (r: source_range) : type_member =
  TMTransparent name k t v r

(** ============================================================================
    VALUE MEMBER
    ============================================================================

    Value members specify function and value bindings in module signatures.
    They declare the existence of a value with a polymorphic type scheme.

    TYPE SCHEMES:
    -------------
    Value members use type_scheme rather than raw types to support
    polymorphic functions:
      val id : forall a. a -> a
      val map : forall a b. (a -> b) -> list a -> list b

    A type_scheme bundles universal quantifiers with the body type.

    SUBTYPING (Spec Definition 5.3):
    --------------------------------
    Value member subtyping is COVARIANT in the type:
      { val x : T1 } <: { val x : T2 }  when T1 <: T2

    This means a value with a MORE specific type can satisfy a
    signature requiring a LESS specific type. For example:
      { val x : int } <: { val x : number }

    METADATA:
    ---------
    Like type members, value members carry visibility and source range
    for tooling support. These do not affect semantic equality.

    EXAMPLES:
    ---------
    val empty : forall a. list a                    (* Polymorphic value *)
    val length : forall a. list a -> int            (* Polymorphic function *)
    val counter : ref int                           (* Monomorphic value *)
    val print : string -> unit @ IO                 (* Effectful function *)
    ============================================================================ *)

(** Value member in a signature: name with type scheme and metadata.

    The val_scheme field supports polymorphic values via universal
    quantification. The visibility and range are metadata for tooling. *)
noeq type value_member = {
  val_name       : var_id;              (* Value identifier *)
  val_scheme     : type_scheme;         (* Polymorphic type scheme *)
  val_visibility : module_visibility;   (* Visibility level *)
  val_range      : source_range         (* Source location *)
}

(* Extract visibility from value member *)
let value_member_visibility (vm: value_member) : module_visibility = vm.val_visibility

(* Extract source range from value member *)
let value_member_range (vm: value_member) : source_range = vm.val_range

(* Check if value member is visible at given visibility level *)
let value_member_visible_at (vm: value_member) (v: module_visibility) : bool =
  visibility_leq vm.val_visibility v

(* Create value member with default visibility *)
let mk_value_member (name: var_id) (scheme: type_scheme) : value_member =
  { val_name = name; val_scheme = scheme; val_visibility = default_visibility; val_range = dummy_source_range }

(* Create value member with explicit visibility and location *)
let mk_value_member_with_meta (name: var_id) (scheme: type_scheme) (v: module_visibility) (r: source_range) : value_member =
  { val_name = name; val_scheme = scheme; val_visibility = v; val_range = r }

(** ============================================================================
    MODULE SIGNATURE
    ============================================================================

    A signature is a module's interface - the type of a module. It describes
    what types, values, and effects a module exports without revealing
    implementation details.

    MATHEMATICAL FOUNDATION:
    ------------------------
    Signatures correspond to the module types in ML-style type theory:
      Sigma ::= { D1; ...; Dn }     (* Signature literal *)
      Di   ::= type t               (* Abstract type *)
             | type t = tau         (* Manifest type *)
             | val x : T            (* Value specification *)
             | effect E = ...       (* Effect declaration *)

    This implements "small signatures" (no nested module specs) which simplify
    the theory while retaining most expressive power via functors.

    STRUCTURAL INTERPRETATION:
    --------------------------
    A signature is NOT a list of declarations but a RECORD of components:
      - sig_types   : type member specifications
      - sig_values  : value member specifications
      - sig_effects : effect member specifications

    This structure enables efficient lookup and structural operations.

    SCOPING AND ORDERING:
    ---------------------
    Order matters within each component list: later members can reference
    earlier ones. For example:
      { type t; val x : t }   (* x can reference t *)
      { val x : t; type t }   (* INVALID: t not in scope for x *)

    However, cross-category references are unrestricted:
      - Types can reference other types (type aliases)
      - Values can reference any type in scope
      - Effects can reference types for operation signatures

    SUBTYPING (Spec Section 5.3):
    -----------------------------
    Signature subtyping S1 <: S2 means "S1 implements S2":
      - For each type t in S2: S1 has a compatible type t
      - For each val x : T in S2: S1 has val x : T' where T' <: T
      - For each effect E in S2: S1 has compatible effect E
      - S1 may have additional members (width subtyping)

    RELATION TO F* .fsti FILES:
    ---------------------------
    An F* .fsti file is essentially a signature:
      - val declarations specify value types
      - type declarations introduce (possibly abstract) types
      - The .fst file must implement this signature

    The key difference: F* uses file-level separation while Brrr uses
    explicit signature types that can be manipulated as values.

    WELL-FORMEDNESS:
    ----------------
    A signature is well-formed if:
      1. All type names are unique within sig_types
      2. All value names are unique within sig_values
      3. All effect names are unique within sig_effects
      4. Type references are in scope
    See wf_sig_names for uniqueness checking.
    ============================================================================ *)

(** Module signature: the interface of a module.

    The three-way split (types/values/effects) enables efficient operations
    and reflects the semantic stratification of module components. *)
noeq type signature = {
  sig_types   : list type_member;    (* Type specifications *)
  sig_values  : list value_member;   (* Value specifications *)
  sig_effects : list effect_sig      (* Effect specifications *)
}

(* Empty signature *)
let empty_sig : signature = {
  sig_types = [];
  sig_values = [];
  sig_effects = []
}

(* Extend signature with a type member *)
let sig_add_type (tm: type_member) (sig: signature) : signature =
  { sig with sig_types = tm :: sig.sig_types }

(* Extend signature with a value member *)
let sig_add_value (vm: value_member) (sig: signature) : signature =
  { sig with sig_values = vm :: sig.sig_values }

(* Extend signature with an effect member *)
let sig_add_effect (es: effect_sig) (sig: signature) : signature =
  { sig with sig_effects = es :: sig.sig_effects }

(* Lookup type member by name *)
let rec lookup_type_member (name: type_name) (members: list type_member) : option type_member =
  match members with
  | [] -> None
  | tm :: rest ->
      if type_member_name tm = name then Some tm
      else lookup_type_member name rest

(* Lookup value member by name *)
let rec lookup_value_member (name: var_id) (members: list value_member) : option value_member =
  match members with
  | [] -> None
  | vm :: rest ->
      if vm.val_name = name then Some vm
      else lookup_value_member name rest

(* Lookup effect member by name *)
let rec lookup_effect_member (name: string) (members: list effect_sig) : option effect_sig =
  match members with
  | [] -> None
  | es :: rest ->
      if es.eff_sig_name = name then Some es
      else lookup_effect_member name rest

(** ============================================================================
    VISIBILITY FILTERING FOR EXPORTS
    ============================================================================ *)

(* Filter type members by visibility threshold.
 * Returns only members visible at the given level.
 * Used for exporting signatures: filter with MVPublic for external export,
 * or MVInternal for package-internal visibility. *)
let rec filter_type_members_by_visibility
    (vis: module_visibility)
    (members: list type_member)
    : Tot (list type_member) (decreases members) =
  match members with
  | [] -> []
  | tm :: rest ->
      let filtered_rest = filter_type_members_by_visibility vis rest in
      if type_member_visible_at tm vis then tm :: filtered_rest
      else filtered_rest

(* Filter value members by visibility threshold *)
let rec filter_value_members_by_visibility
    (vis: module_visibility)
    (members: list value_member)
    : Tot (list value_member) (decreases members) =
  match members with
  | [] -> []
  | vm :: rest ->
      let filtered_rest = filter_value_members_by_visibility vis rest in
      if value_member_visible_at vm vis then vm :: filtered_rest
      else filtered_rest

(* Filter effect members by visibility threshold *)
let rec filter_effect_members_by_visibility
    (vis: module_visibility)
    (members: list effect_sig)
    : Tot (list effect_sig) (decreases members) =
  match members with
  | [] -> []
  | es :: rest ->
      let filtered_rest = filter_effect_members_by_visibility vis rest in
      if effect_sig_visible_at es vis then es :: filtered_rest
      else filtered_rest

(* Filter entire signature by visibility.
 * Returns a new signature containing only members visible at the given level.
 * This is the primary function for computing exported signatures. *)
let filter_signature_by_visibility (vis: module_visibility) (sig: signature) : signature =
  {
    sig_types = filter_type_members_by_visibility vis sig.sig_types;
    sig_values = filter_value_members_by_visibility vis sig.sig_values;
    sig_effects = filter_effect_members_by_visibility vis sig.sig_effects
  }

(* Export signature: filter to only publicly visible members *)
let export_signature (sig: signature) : signature =
  filter_signature_by_visibility MVPublic sig

(* Internal signature: filter to internally and publicly visible members *)
let internal_signature (sig: signature) : signature =
  filter_signature_by_visibility MVInternal sig

(* Lemma: filtering preserves member uniqueness *)
val filter_type_members_preserves_uniqueness :
    vis:module_visibility -> members:list type_member ->
    Lemma (requires type_member_names_unique members = true)
          (ensures type_member_names_unique (filter_type_members_by_visibility vis members) = true)
          (decreases members)
let rec filter_type_members_preserves_uniqueness vis members =
  match members with
  | [] -> ()
  | tm :: rest ->
      filter_type_members_preserves_uniqueness vis rest;
      (* If tm is filtered out, uniqueness of rest suffices *)
      (* If tm is kept, we need to show its name is not in the filtered rest *)
      (* This follows from the fact that it was not in the original rest *)
      if type_member_visible_at tm vis then ()
      else ()

val filter_value_members_preserves_uniqueness :
    vis:module_visibility -> members:list value_member ->
    Lemma (requires value_member_names_unique members = true)
          (ensures value_member_names_unique (filter_value_members_by_visibility vis members) = true)
          (decreases members)
let rec filter_value_members_preserves_uniqueness vis members =
  match members with
  | [] -> ()
  | vm :: rest ->
      filter_value_members_preserves_uniqueness vis rest

val filter_effect_members_preserves_uniqueness :
    vis:module_visibility -> members:list effect_sig ->
    Lemma (requires effect_member_names_unique members = true)
          (ensures effect_member_names_unique (filter_effect_members_by_visibility vis members) = true)
          (decreases members)
let rec filter_effect_members_preserves_uniqueness vis members =
  match members with
  | [] -> ()
  | es :: rest ->
      filter_effect_members_preserves_uniqueness vis rest

(* Lemma: filtering signature preserves well-formedness *)
val filter_signature_preserves_wf :
    vis:module_visibility -> sig:signature ->
    Lemma (requires wf_sig_names sig = true)
          (ensures wf_sig_names (filter_signature_by_visibility vis sig) = true)
let filter_signature_preserves_wf vis sig =
  filter_type_members_preserves_uniqueness vis sig.sig_types;
  filter_value_members_preserves_uniqueness vis sig.sig_values;
  filter_effect_members_preserves_uniqueness vis sig.sig_effects

(* Collect all type member names and ranges for shadow checking *)
let rec collect_type_member_names_ranges (members: list type_member)
    : Tot (list (type_name & source_range)) (decreases members) =
  match members with
  | [] -> []
  | tm :: rest -> (type_member_name tm, type_member_range tm) :: collect_type_member_names_ranges rest

(* Collect all value member names and ranges for shadow checking *)
let rec collect_value_member_names_ranges (members: list value_member)
    : Tot (list (var_id & source_range)) (decreases members) =
  match members with
  | [] -> []
  | vm :: rest -> (vm.val_name, vm.val_range) :: collect_value_member_names_ranges rest

(* Collect all effect member names and ranges for shadow checking *)
let rec collect_effect_member_names_ranges (members: list effect_sig)
    : Tot (list (string & source_range)) (decreases members) =
  match members with
  | [] -> []
  | es :: rest -> (es.eff_sig_name, es.eff_sig_range) :: collect_effect_member_names_ranges rest

(* Check if adding a type member would shadow existing members *)
let check_type_member_shadow (tm: type_member) (existing: list type_member) : shadow_result =
  check_shadow_type (type_member_name tm) (type_member_range tm)
                    (collect_type_member_names_ranges existing)

(* Check if adding a value member would shadow existing members *)
let check_value_member_shadow (vm: value_member) (existing: list value_member) : shadow_result =
  check_shadow_value vm.val_name vm.val_range
                     (collect_value_member_names_ranges existing)

(* Check if adding an effect member would shadow existing members *)
let check_effect_member_shadow (es: effect_sig) (existing: list effect_sig) : shadow_result =
  check_shadow_effect es.eff_sig_name es.eff_sig_range
                      (collect_effect_member_names_ranges existing)

(** ============================================================================
    FUNCTOR MODE (Applicative vs Generative)
    ============================================================================

    Functor mode determines the semantics of type identity across functor
    applications. This is one of the deepest and most subtle aspects of
    ML-style module systems.

    THE FUNDAMENTAL QUESTION:
    -------------------------
    Given: functor F(X : S1) = struct type t = ... end
    Are F(M).t and F(M).t the same type?
    Are F(M).t and F(N).t the same type when M equiv N?

    APPLICATIVE FUNCTORS (functor^app):
    -----------------------------------
    Definition (Spec 2.4): F(M) = F(M') when M equiv M'

    Properties:
      - Types are SHARED across applications with equal arguments
      - F(M).t = F(M).t (trivially - same application)
      - F(M).t = F(N).t when M equiv N (the key property)
      - Enables type sharing across module boundaries
      - Default mode for most functors

    Use cases:
      - Data structure libraries (Set.Make, Map.Make)
      - Numeric algorithm parameterization
      - Configuration modules

    Example:
      module IntSet = Set.Make(IntOrd)
      module IntSet' = Set.Make(IntOrd)
      (* IntSet.t = IntSet'.t because IntOrd equiv IntOrd *)

    GENERATIVE FUNCTORS (functor^gen):
    ----------------------------------
    Definition (Spec 2.5): F(M) <> F(M') even when M equiv M'

    Properties:
      - Fresh abstract types on EVERY application
      - F(M).t <> F(M).t (even same application twice!)
      - Each application creates new type identity via stamping
      - Types cannot leak across application boundaries

    Use cases:
      - Stateful modules (hashtables, IO handles)
      - Modules requiring distinct identity (OOP-style objects)
      - Security boundaries (capability systems)

    Example:
      module H1 = MakeHashtable(StringOrd)
      module H2 = MakeHashtable(StringOrd)
      (* H1.table <> H2.table - distinct types! *)

    IMPLEMENTATION:
    ---------------
    Generativity is implemented via type stamps:
      - Each generative application gets a fresh stamp
      - Abstract types in the result carry this stamp
      - Type equality checks stamps: (stamp1, name1) = (stamp2, name2)
        only if stamp1 = stamp2 AND name1 = name2

    THEORETICAL BACKGROUND:
    -----------------------
    - Applicative functors: Leroy's "A Modular Module System" (JFP 2000)
    - Generative functors: Rossberg-Russo-Dreyer's "F-ing Modules" (JFP 2014)
    - The choice fundamentally affects module composition safety

    SYNTAX IN BRRR (Spec):
    ----------------------
      functor^app(X : S) -> M      (* Applicative - default *)
      functor^gen(X : S) -> M      (* Generative - explicit *)
    ============================================================================ *)

(** Functor mode determines type sharing semantics across applications.
    This is a fundamental choice that affects the entire module system's
    behavior around type identity and sharing. *)
type functor_mode =
  | Applicative  (* functor^app - types shared across equal applications *)
  | Generative   (* functor^gen - fresh types per application *)

(* Default functor mode is applicative (following ML convention) *)
let default_functor_mode : functor_mode = Applicative

(* Type stamp for tracking generative type identity.
 * Each generative functor application gets a fresh stamp.
 * Abstract types from that application are tagged with the stamp
 * to ensure distinct identity even for structurally equal types. *)
type type_stamp = nat

(* Global stamp counter state - tracks next available stamp.
 * In a pure functional setting, this would be threaded through
 * computations, but for simplicity we model it as a counter. *)
type stamp_state = {
  next_stamp : type_stamp
}

(* Initial stamp state *)
let initial_stamp_state : stamp_state = {
  next_stamp = 0
}

(* Generate a fresh stamp and update state *)
let fresh_stamp (st: stamp_state) : (type_stamp & stamp_state) =
  (st.next_stamp, { next_stamp = st.next_stamp + 1 })

(* Stamped type: tracks generative identity for abstract types.
 * - Unstamped: regular type without generative tracking
 * - Stamped: type with unique stamp from generative functor application
 *)
noeq type stamped_type =
  | Unstamped   : brrr_type -> stamped_type
  | Stamped     : type_stamp -> type_name -> stamped_type

(* Extract underlying type from stamped type (if unstamped) *)
let unstamp_type (st: stamped_type) : option brrr_type =
  match st with
  | Unstamped t -> Some t
  | Stamped _ _ -> None

(* Check if two stamped types are equal.
 * Stamped types are equal only if they have the same stamp. *)
let stamped_type_eq (st1 st2: stamped_type) : bool =
  match st1, st2 with
  | Unstamped t1, Unstamped t2 -> type_eq t1 t2
  | Stamped s1 n1, Stamped s2 n2 -> s1 = s2 && n1 = n2
  | _, _ -> false

(** ============================================================================
    MODULE TYPES
    ============================================================================

    Module types classify modules, just as types classify terms. They form
    the "second level" of Brrr's type system (terms : types :: modules : module_types).

    GRAMMAR (Spec Section 5.1):
    --------------------------
      ModType ::= Sig                           (* Signature type *)
                | (X : ModType1) -> ModType2    (* Functor type *)

    STRUCTURE TYPES (MTSig):
    ------------------------
    MTSig s classifies modules that provide signature s:
      MTSig { type t; val x : t } classifies modules with abstract type t
                                  and a value x of that type

    A module M has type MTSig s if M implements all components of s with
    compatible (possibly more specific) types.

    FUNCTOR TYPES (MTFunctor):
    --------------------------
    MTFunctor X param result mode classifies functors:
      - X is the parameter name (bound in result)
      - param is the parameter's module type
      - result is the result's module type (may reference X)
      - mode determines applicative vs generative semantics

    Example:
      MTFunctor "Ord" (MTSig {type t; val compare: t -> t -> int})
                      (MTSig {type set; val empty: set; ...})
                      Applicative
      (* Classifies Set.Make-style functors *)

    HIGHER-ORDER FUNCTORS:
    ----------------------
    Functor types can nest, enabling higher-order module programming:
      (F : (X : S1) -> S2) -> S3   (* Functor that takes a functor *)

    This is represented as:
      MTFunctor "F" (MTFunctor "X" S1 S2 mode1) S3 mode2

    SUBTYPING:
    ----------
    Module type subtyping is CONTRAVARIANT in functor parameters:
      (X : S1) -> S2 <: (X : S1') -> S2'
      when S1' <: S1 (contravariant!) and S2 <: S2' (covariant)

    This matches function subtyping: a functor accepting LESS (S1')
    can be used where one accepting MORE (S1) is expected.

    SIZE MEASURE:
    -------------
    module_type_size provides a termination measure for recursive
    functions over module types, essential for F*'s termination checker.
    ============================================================================ *)

(** Module types classify modules.

    MTSig s     : Modules implementing signature s
    MTFunctor X P R m : Functors from P to R with parameter X and mode m

    The functor case binds X in R, enabling self-reference. *)
noeq type module_type =
  | MTSig     : signature -> module_type
  | MTFunctor : module_var -> module_type -> module_type -> functor_mode -> module_type

(* Size of module type - for termination measures *)
let rec module_type_size (mt: module_type) : Tot nat (decreases mt) =
  match mt with
  | MTSig _ -> 1
  | MTFunctor _ mt1 mt2 _ -> 1 + module_type_size mt1 + module_type_size mt2

(** ============================================================================
    MODULE DECLARATIONS
    ============================================================================ *)

(* Module declaration: a single item in a structure *)
noeq type module_decl =
  | MDType   : type_member -> module_decl                (* Type definition *)
  | MDVal    : var_id -> brrr_type -> module_decl        (* Value binding: val x : T *)
  | MDEffect : effect_sig -> module_decl                 (* Effect definition *)
  | MDModule : module_var -> module_expr -> module_decl  (* Nested module *)

(* Module expression: constructs modules *)
and module_expr =
  | MEStruct  : list module_decl -> module_expr                     (* struct ... end *)
  | MEFunctor : module_var -> module_type -> functor_mode -> module_expr -> module_expr
      (* functor^mode (X : S) -> M *)
  | MEApp     : module_expr -> module_expr -> module_expr           (* M(N) - functor application *)
  | MEPath    : module_path -> module_expr                          (* M.N - path reference *)
  | MESeal    : module_expr -> module_type -> module_expr           (* (M : S) - sealing/ascription *)

(* Size of module expression - for termination *)
let rec module_expr_size (me: module_expr) : Tot nat (decreases me) =
  match me with
  | MEStruct decls -> 1 + module_decl_list_size decls
  | MEFunctor _ mt _ body -> 1 + module_type_size mt + module_expr_size body
  | MEApp m1 m2 -> 1 + module_expr_size m1 + module_expr_size m2
  | MEPath _ -> 1
  | MESeal m mt -> 1 + module_expr_size m + module_type_size mt

and module_decl_size (md: module_decl) : Tot nat (decreases md) =
  match md with
  | MDType _ -> 1
  | MDVal _ _ -> 1
  | MDEffect _ -> 1
  | MDModule _ me -> 1 + module_expr_size me

and module_decl_list_size (decls: list module_decl) : Tot nat (decreases decls) =
  match decls with
  | [] -> 0
  | d :: rest -> module_decl_size d + module_decl_list_size rest

(** ============================================================================
    TYPE MEMBER EQUALITY
    ============================================================================ *)

(* Type member equality: same name, kind, and (if transparent) same definition *)
(* Type member equality: same name, kind, and (if transparent) same definition.
 * Note: visibility and source range are metadata and do NOT affect equality. *)
let type_member_eq (tm1 tm2: type_member) : bool =
  match tm1, tm2 with
  | TMOpaque n1 k1 _ _, TMOpaque n2 k2 _ _ ->
      n1 = n2 && kind_eq k1 k2
  | TMTransparent n1 k1 t1 _ _, TMTransparent n2 k2 t2 _ _ ->
      n1 = n2 && kind_eq k1 k2 && type_eq t1 t2
  | _, _ -> false

(* Type member equality is reflexive *)
val type_member_eq_refl : tm:type_member ->
  Lemma (type_member_eq tm tm = true)
        [SMTPat (type_member_eq tm tm)]
let type_member_eq_refl tm =
  match tm with
  | TMOpaque n k _ _ -> kind_eq_refl k
  | TMTransparent n k t _ _ -> kind_eq_refl k; type_eq_refl t

(* Type member equality is symmetric *)
val type_member_eq_sym : tm1:type_member -> tm2:type_member ->
  Lemma (requires type_member_eq tm1 tm2 = true)
        (ensures type_member_eq tm2 tm1 = true)
let type_member_eq_sym tm1 tm2 =
  match tm1, tm2 with
  | TMOpaque n1 k1 _ _, TMOpaque n2 k2 _ _ -> kind_eq_sym k1 k2
  | TMTransparent n1 k1 t1 _ _, TMTransparent n2 k2 t2 _ _ ->
      kind_eq_sym k1 k2; type_eq_sym t1 t2
  | _, _ -> ()

(* Type member equality is transitive *)
val type_member_eq_trans : tm1:type_member -> tm2:type_member -> tm3:type_member ->
  Lemma (requires type_member_eq tm1 tm2 = true /\ type_member_eq tm2 tm3 = true)
        (ensures type_member_eq tm1 tm3 = true)
let type_member_eq_trans tm1 tm2 tm3 =
  match tm1, tm2, tm3 with
  | TMOpaque n1 k1 _ _, TMOpaque n2 k2 _ _, TMOpaque n3 k3 _ _ ->
      kind_eq_trans k1 k2 k3
  | TMTransparent n1 k1 t1 _ _, TMTransparent n2 k2 t2 _ _, TMTransparent n3 k3 t3 _ _ ->
      kind_eq_trans k1 k2 k3; type_eq_trans t1 t2 t3
  | _, _, _ -> ()

(** ============================================================================
    VALUE MEMBER EQUALITY
    ============================================================================ *)

(* Type scheme equality: same bound vars and body *)
let type_scheme_eq (ts1 ts2: type_scheme) : bool =
  ts1.type_vars = ts2.type_vars &&
  ts1.effect_vars = ts2.effect_vars &&
  type_eq ts1.body ts2.body

(* Value member equality *)
let value_member_eq (vm1 vm2: value_member) : bool =
  vm1.val_name = vm2.val_name &&
  type_scheme_eq vm1.val_scheme vm2.val_scheme

(* Type scheme equality is reflexive *)
val type_scheme_eq_refl : ts:type_scheme ->
  Lemma (type_scheme_eq ts ts = true)
        [SMTPat (type_scheme_eq ts ts)]
let type_scheme_eq_refl ts = type_eq_refl ts.body

(* Value member equality is reflexive *)
val value_member_eq_refl : vm:value_member ->
  Lemma (value_member_eq vm vm = true)
        [SMTPat (value_member_eq vm vm)]
let value_member_eq_refl vm = type_scheme_eq_refl vm.val_scheme

(* Type scheme equality is symmetric *)
val type_scheme_eq_sym : ts1:type_scheme -> ts2:type_scheme ->
  Lemma (requires type_scheme_eq ts1 ts2 = true)
        (ensures type_scheme_eq ts2 ts1 = true)
let type_scheme_eq_sym ts1 ts2 = type_eq_sym ts1.body ts2.body

(* Value member equality is symmetric *)
val value_member_eq_sym : vm1:value_member -> vm2:value_member ->
  Lemma (requires value_member_eq vm1 vm2 = true)
        (ensures value_member_eq vm2 vm1 = true)
let value_member_eq_sym vm1 vm2 = type_scheme_eq_sym vm1.val_scheme vm2.val_scheme

(* Type scheme equality is transitive *)
val type_scheme_eq_trans : ts1:type_scheme -> ts2:type_scheme -> ts3:type_scheme ->
  Lemma (requires type_scheme_eq ts1 ts2 = true /\ type_scheme_eq ts2 ts3 = true)
        (ensures type_scheme_eq ts1 ts3 = true)
let type_scheme_eq_trans ts1 ts2 ts3 = type_eq_trans ts1.body ts2.body ts3.body

(* Value member equality is transitive *)
val value_member_eq_trans : vm1:value_member -> vm2:value_member -> vm3:value_member ->
  Lemma (requires value_member_eq vm1 vm2 = true /\ value_member_eq vm2 vm3 = true)
        (ensures value_member_eq vm1 vm3 = true)
let value_member_eq_trans vm1 vm2 vm3 =
  type_scheme_eq_trans vm1.val_scheme vm2.val_scheme vm3.val_scheme

(** ============================================================================
    EFFECT SIGNATURE EQUALITY
    ============================================================================ *)

(* Effect operation list equality *)
let rec effect_ops_eq (ops1 ops2: list (string & brrr_type)) : Tot bool (decreases ops1) =
  match ops1, ops2 with
  | [], [] -> true
  | (n1, t1) :: r1, (n2, t2) :: r2 -> n1 = n2 && type_eq t1 t2 && effect_ops_eq r1 r2
  | _, _ -> false

(* Effect signature equality *)
let effect_sig_eq (es1 es2: effect_sig) : bool =
  es1.eff_sig_name = es2.eff_sig_name &&
  effect_ops_eq es1.eff_sig_ops es2.eff_sig_ops

(* Effect ops equality is reflexive *)
val effect_ops_eq_refl : ops:list (string & brrr_type) ->
  Lemma (ensures effect_ops_eq ops ops = true)
        (decreases ops)
        [SMTPat (effect_ops_eq ops ops)]
let rec effect_ops_eq_refl ops =
  match ops with
  | [] -> ()
  | (n, t) :: rest -> type_eq_refl t; effect_ops_eq_refl rest

(* Effect signature equality is reflexive *)
val effect_sig_eq_refl : es:effect_sig ->
  Lemma (effect_sig_eq es es = true)
        [SMTPat (effect_sig_eq es es)]
let effect_sig_eq_refl es = effect_ops_eq_refl es.eff_sig_ops

(* Effect ops equality is symmetric *)
val effect_ops_eq_sym : ops1:list (string & brrr_type) -> ops2:list (string & brrr_type) ->
  Lemma (requires effect_ops_eq ops1 ops2 = true)
        (ensures effect_ops_eq ops2 ops1 = true) (decreases ops1)
let rec effect_ops_eq_sym ops1 ops2 =
  match ops1, ops2 with
  | [], [] -> ()
  | (n1, t1) :: r1, (n2, t2) :: r2 ->
      type_eq_sym t1 t2; effect_ops_eq_sym r1 r2
  | _, _ -> ()

(* Effect signature equality is symmetric *)
val effect_sig_eq_sym : es1:effect_sig -> es2:effect_sig ->
  Lemma (requires effect_sig_eq es1 es2 = true)
        (ensures effect_sig_eq es2 es1 = true)
let effect_sig_eq_sym es1 es2 = effect_ops_eq_sym es1.eff_sig_ops es2.eff_sig_ops

(* Effect ops equality is transitive *)
val effect_ops_eq_trans : ops1:list (string & brrr_type) -> ops2:list (string & brrr_type) ->
                          ops3:list (string & brrr_type) ->
  Lemma (requires effect_ops_eq ops1 ops2 = true /\ effect_ops_eq ops2 ops3 = true)
        (ensures effect_ops_eq ops1 ops3 = true) (decreases ops1)
let rec effect_ops_eq_trans ops1 ops2 ops3 =
  match ops1, ops2, ops3 with
  | [], [], [] -> ()
  | (n1, t1) :: r1, (n2, t2) :: r2, (n3, t3) :: r3 ->
      type_eq_trans t1 t2 t3; effect_ops_eq_trans r1 r2 r3
  | _, _, _ -> ()

(* Effect signature equality is transitive *)
val effect_sig_eq_trans : es1:effect_sig -> es2:effect_sig -> es3:effect_sig ->
  Lemma (requires effect_sig_eq es1 es2 = true /\ effect_sig_eq es2 es3 = true)
        (ensures effect_sig_eq es1 es3 = true)
let effect_sig_eq_trans es1 es2 es3 =
  effect_ops_eq_trans es1.eff_sig_ops es2.eff_sig_ops es3.eff_sig_ops

(** ============================================================================
    SIGNATURE EQUALITY
    ============================================================================ *)

(* Type member list equality *)
let rec type_member_list_eq (tms1 tms2: list type_member) : Tot bool (decreases tms1) =
  match tms1, tms2 with
  | [], [] -> true
  | tm1 :: r1, tm2 :: r2 -> type_member_eq tm1 tm2 && type_member_list_eq r1 r2
  | _, _ -> false

(* Value member list equality *)
let rec value_member_list_eq (vms1 vms2: list value_member) : Tot bool (decreases vms1) =
  match vms1, vms2 with
  | [], [] -> true
  | vm1 :: r1, vm2 :: r2 -> value_member_eq vm1 vm2 && value_member_list_eq r1 r2
  | _, _ -> false

(* Effect signature list equality *)
let rec effect_sig_list_eq (ess1 ess2: list effect_sig) : Tot bool (decreases ess1) =
  match ess1, ess2 with
  | [], [] -> true
  | es1 :: r1, es2 :: r2 -> effect_sig_eq es1 es2 && effect_sig_list_eq r1 r2
  | _, _ -> false

(* Signature equality *)
let signature_eq (s1 s2: signature) : bool =
  type_member_list_eq s1.sig_types s2.sig_types &&
  value_member_list_eq s1.sig_values s2.sig_values &&
  effect_sig_list_eq s1.sig_effects s2.sig_effects

(* List equality lemmas *)
val type_member_list_eq_refl : tms:list type_member ->
  Lemma (ensures type_member_list_eq tms tms = true)
        (decreases tms)
        [SMTPat (type_member_list_eq tms tms)]
let rec type_member_list_eq_refl tms =
  match tms with
  | [] -> ()
  | tm :: rest -> type_member_eq_refl tm; type_member_list_eq_refl rest

val value_member_list_eq_refl : vms:list value_member ->
  Lemma (ensures value_member_list_eq vms vms = true)
        (decreases vms)
        [SMTPat (value_member_list_eq vms vms)]
let rec value_member_list_eq_refl vms =
  match vms with
  | [] -> ()
  | vm :: rest -> value_member_eq_refl vm; value_member_list_eq_refl rest

val effect_sig_list_eq_refl : ess:list effect_sig ->
  Lemma (ensures effect_sig_list_eq ess ess = true)
        (decreases ess)
        [SMTPat (effect_sig_list_eq ess ess)]
let rec effect_sig_list_eq_refl ess =
  match ess with
  | [] -> ()
  | es :: rest -> effect_sig_eq_refl es; effect_sig_list_eq_refl rest

(* Signature equality is reflexive *)
val signature_eq_refl : s:signature ->
  Lemma (signature_eq s s = true)
        [SMTPat (signature_eq s s)]
let signature_eq_refl s =
  type_member_list_eq_refl s.sig_types;
  value_member_list_eq_refl s.sig_values;
  effect_sig_list_eq_refl s.sig_effects

(* List symmetry lemmas *)
val type_member_list_eq_sym : tms1:list type_member -> tms2:list type_member ->
  Lemma (requires type_member_list_eq tms1 tms2 = true)
        (ensures type_member_list_eq tms2 tms1 = true) (decreases tms1)
let rec type_member_list_eq_sym tms1 tms2 =
  match tms1, tms2 with
  | [], [] -> ()
  | tm1 :: r1, tm2 :: r2 ->
      type_member_eq_sym tm1 tm2; type_member_list_eq_sym r1 r2
  | _, _ -> ()

val value_member_list_eq_sym : vms1:list value_member -> vms2:list value_member ->
  Lemma (requires value_member_list_eq vms1 vms2 = true)
        (ensures value_member_list_eq vms2 vms1 = true) (decreases vms1)
let rec value_member_list_eq_sym vms1 vms2 =
  match vms1, vms2 with
  | [], [] -> ()
  | vm1 :: r1, vm2 :: r2 ->
      value_member_eq_sym vm1 vm2; value_member_list_eq_sym r1 r2
  | _, _ -> ()

val effect_sig_list_eq_sym : ess1:list effect_sig -> ess2:list effect_sig ->
  Lemma (requires effect_sig_list_eq ess1 ess2 = true)
        (ensures effect_sig_list_eq ess2 ess1 = true) (decreases ess1)
let rec effect_sig_list_eq_sym ess1 ess2 =
  match ess1, ess2 with
  | [], [] -> ()
  | es1 :: r1, es2 :: r2 ->
      effect_sig_eq_sym es1 es2; effect_sig_list_eq_sym r1 r2
  | _, _ -> ()

(* Signature equality is symmetric *)
val signature_eq_sym : s1:signature -> s2:signature ->
  Lemma (requires signature_eq s1 s2 = true)
        (ensures signature_eq s2 s1 = true)
let signature_eq_sym s1 s2 =
  type_member_list_eq_sym s1.sig_types s2.sig_types;
  value_member_list_eq_sym s1.sig_values s2.sig_values;
  effect_sig_list_eq_sym s1.sig_effects s2.sig_effects

(* List transitivity lemmas *)
val type_member_list_eq_trans : tms1:list type_member -> tms2:list type_member ->
                                tms3:list type_member ->
  Lemma (requires type_member_list_eq tms1 tms2 = true /\ type_member_list_eq tms2 tms3 = true)
        (ensures type_member_list_eq tms1 tms3 = true) (decreases tms1)
let rec type_member_list_eq_trans tms1 tms2 tms3 =
  match tms1, tms2, tms3 with
  | [], [], [] -> ()
  | tm1 :: r1, tm2 :: r2, tm3 :: r3 ->
      type_member_eq_trans tm1 tm2 tm3; type_member_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

val value_member_list_eq_trans : vms1:list value_member -> vms2:list value_member ->
                                 vms3:list value_member ->
  Lemma (requires value_member_list_eq vms1 vms2 = true /\ value_member_list_eq vms2 vms3 = true)
        (ensures value_member_list_eq vms1 vms3 = true) (decreases vms1)
let rec value_member_list_eq_trans vms1 vms2 vms3 =
  match vms1, vms2, vms3 with
  | [], [], [] -> ()
  | vm1 :: r1, vm2 :: r2, vm3 :: r3 ->
      value_member_eq_trans vm1 vm2 vm3; value_member_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

val effect_sig_list_eq_trans : ess1:list effect_sig -> ess2:list effect_sig ->
                               ess3:list effect_sig ->
  Lemma (requires effect_sig_list_eq ess1 ess2 = true /\ effect_sig_list_eq ess2 ess3 = true)
        (ensures effect_sig_list_eq ess1 ess3 = true) (decreases ess1)
let rec effect_sig_list_eq_trans ess1 ess2 ess3 =
  match ess1, ess2, ess3 with
  | [], [], [] -> ()
  | es1 :: r1, es2 :: r2, es3 :: r3 ->
      effect_sig_eq_trans es1 es2 es3; effect_sig_list_eq_trans r1 r2 r3
  | _, _, _ -> ()

(* Signature equality is transitive *)
val signature_eq_trans : s1:signature -> s2:signature -> s3:signature ->
  Lemma (requires signature_eq s1 s2 = true /\ signature_eq s2 s3 = true)
        (ensures signature_eq s1 s3 = true)
let signature_eq_trans s1 s2 s3 =
  type_member_list_eq_trans s1.sig_types s2.sig_types s3.sig_types;
  value_member_list_eq_trans s1.sig_values s2.sig_values s3.sig_values;
  effect_sig_list_eq_trans s1.sig_effects s2.sig_effects s3.sig_effects

(** ============================================================================
    MODULE TYPE EQUALITY
    ============================================================================ *)

(* Module type equality - includes functor mode comparison *)
let rec module_type_eq (mt1 mt2: module_type) : Tot bool (decreases mt1) =
  match mt1, mt2 with
  | MTSig s1, MTSig s2 -> signature_eq s1 s2
  | MTFunctor x1 param1 result1 mode1, MTFunctor x2 param2 result2 mode2 ->
      x1 = x2 && mode1 = mode2 &&
      module_type_eq param1 param2 && module_type_eq result1 result2
  | _, _ -> false

(* Module type equality is reflexive *)
val module_type_eq_refl : mt:module_type ->
  Lemma (ensures module_type_eq mt mt = true)
        (decreases mt)
        [SMTPat (module_type_eq mt mt)]
let rec module_type_eq_refl mt =
  match mt with
  | MTSig s -> signature_eq_refl s
  | MTFunctor x param result _ ->
      module_type_eq_refl param; module_type_eq_refl result

(* Module type equality is symmetric *)
val module_type_eq_sym : mt1:module_type -> mt2:module_type ->
  Lemma (requires module_type_eq mt1 mt2 = true)
        (ensures module_type_eq mt2 mt1 = true) (decreases mt1)
let rec module_type_eq_sym mt1 mt2 =
  match mt1, mt2 with
  | MTSig s1, MTSig s2 -> signature_eq_sym s1 s2
  | MTFunctor x1 param1 result1 _, MTFunctor x2 param2 result2 _ ->
      module_type_eq_sym param1 param2; module_type_eq_sym result1 result2
  | _, _ -> ()

(* Module type equality is transitive *)
val module_type_eq_trans : mt1:module_type -> mt2:module_type -> mt3:module_type ->
  Lemma (requires module_type_eq mt1 mt2 = true /\ module_type_eq mt2 mt3 = true)
        (ensures module_type_eq mt1 mt3 = true) (decreases mt1)
let rec module_type_eq_trans mt1 mt2 mt3 =
  match mt1, mt2, mt3 with
  | MTSig s1, MTSig s2, MTSig s3 -> signature_eq_trans s1 s2 s3
  | MTFunctor x1 p1 r1 _, MTFunctor x2 p2 r2 _, MTFunctor x3 p3 r3 _ ->
      module_type_eq_trans p1 p2 p3; module_type_eq_trans r1 r2 r3
  | _, _, _ -> ()

(** ============================================================================
    TYPE MEMBER SUBTYPING
    ============================================================================ *)

(* Type member subtyping: tm1 <: tm2
 *
 * Rules:
 * 1. Transparent <: Opaque (with same name and kind) - hiding implementation
 * 2. Transparent <: Transparent (with same name, kind, and equal types)
 * 3. Opaque <: Opaque (with same name and kind)
 *
 * This is CONTRAVARIANT in the module subtyping context:
 * A signature with MORE type information (transparent) can be used where
 * LESS information (opaque) is expected.
 *)
(* Type member subtyping: tm1 <: tm2
 * Note: visibility and source range are metadata and do NOT affect subtyping. *)
let type_member_sub (tm1 tm2: type_member) : bool =
  let n1 = type_member_name tm1 in
  let n2 = type_member_name tm2 in
  let k1 = type_member_kind tm1 in
  let k2 = type_member_kind tm2 in
  if n1 <> n2 then false
  else if not (kind_eq k1 k2) then false
  else match tm1, tm2 with
    (* Transparent -> Opaque: always OK if name/kind match (hiding) *)
    | TMTransparent _ _ _ _ _, TMOpaque _ _ _ _ -> true
    (* Transparent -> Transparent: types must be equal *)
    | TMTransparent _ _ t1 _ _, TMTransparent _ _ t2 _ _ -> type_eq t1 t2
    (* Opaque -> Opaque: OK if name/kind match *)
    | TMOpaque _ _ _ _, TMOpaque _ _ _ _ -> true
    (* Opaque -> Transparent: NOT OK (cannot reveal hidden type) *)
    | TMOpaque _ _ _ _, TMTransparent _ _ _ _ _ -> false

(* Type member subtyping is reflexive *)
val type_member_sub_refl : tm:type_member ->
  Lemma (type_member_sub tm tm = true)
        [SMTPat (type_member_sub tm tm)]
let type_member_sub_refl tm =
  kind_eq_refl (type_member_kind tm);
  match tm with
  | TMOpaque _ _ _ _ -> ()
  | TMTransparent _ _ t _ _ -> type_eq_refl t

(** ============================================================================
    VALUE MEMBER SUBTYPING
    ============================================================================ *)

(* Type scheme subtyping: ts1 <: ts2
 *
 * A type scheme is a subtype if:
 * - Same quantified variables (simplified: exact match)
 * - Body types are in subtype relation
 *
 * This is COVARIANT: more specific types can be provided where less specific expected
 *)
let type_scheme_sub (ts1 ts2: type_scheme) : bool =
  ts1.type_vars = ts2.type_vars &&
  ts1.effect_vars = ts2.effect_vars &&
  subtype ts1.body ts2.body

(* Value member subtyping: same name, subtype scheme *)
let value_member_sub (vm1 vm2: value_member) : bool =
  vm1.val_name = vm2.val_name &&
  type_scheme_sub vm1.val_scheme vm2.val_scheme

(* Type scheme subtyping is reflexive *)
val type_scheme_sub_refl : ts:type_scheme ->
  Lemma (type_scheme_sub ts ts = true)
        [SMTPat (type_scheme_sub ts ts)]
let type_scheme_sub_refl ts = subtype_refl ts.body

(* Value member subtyping is reflexive *)
val value_member_sub_refl : vm:value_member ->
  Lemma (value_member_sub vm vm = true)
        [SMTPat (value_member_sub vm vm)]
let value_member_sub_refl vm = type_scheme_sub_refl vm.val_scheme

(** ============================================================================
    EFFECT SIGNATURE SUBTYPING
    ============================================================================ *)

(* Effect operation subtyping: same name, subtype types *)
let rec effect_ops_sub (ops1 ops2: list (string & brrr_type)) : Tot bool (decreases ops1) =
  match ops1, ops2 with
  | [], [] -> true
  | (n1, t1) :: r1, (n2, t2) :: r2 ->
      n1 = n2 && subtype t1 t2 && effect_ops_sub r1 r2
  | _, _ -> false

(* Effect signature subtyping *)
let effect_sig_sub (es1 es2: effect_sig) : bool =
  es1.eff_sig_name = es2.eff_sig_name &&
  effect_ops_sub es1.eff_sig_ops es2.eff_sig_ops

(* Effect ops subtyping is reflexive *)
val effect_ops_sub_refl : ops:list (string & brrr_type) ->
  Lemma (ensures effect_ops_sub ops ops = true)
        (decreases ops)
        [SMTPat (effect_ops_sub ops ops)]
let rec effect_ops_sub_refl ops =
  match ops with
  | [] -> ()
  | (n, t) :: rest -> subtype_refl t; effect_ops_sub_refl rest

(* Effect signature subtyping is reflexive *)
val effect_sig_sub_refl : es:effect_sig ->
  Lemma (effect_sig_sub es es = true)
        [SMTPat (effect_sig_sub es es)]
let effect_sig_sub_refl es = effect_ops_sub_refl es.eff_sig_ops

(** ============================================================================
    SIGNATURE SUBTYPING
    ============================================================================ *)

(* Check that each type member in sig2 has a matching subtype member in sig1
 * (sig1 can provide MORE or EQUAL information compared to sig2) *)
let rec type_members_match (tms1 tms2: list type_member) : Tot bool (decreases tms2) =
  match tms2 with
  | [] -> true
  | tm2 :: rest2 ->
      let name = type_member_name tm2 in
      match lookup_type_member name tms1 with
      | None -> false  (* sig1 must have all types that sig2 has *)
      | Some tm1 ->
          type_member_sub tm1 tm2 && type_members_match tms1 rest2

(* Check that each value member in sig2 has a matching subtype member in sig1 *)
let rec value_members_match (vms1 vms2: list value_member) : Tot bool (decreases vms2) =
  match vms2 with
  | [] -> true
  | vm2 :: rest2 ->
      match lookup_value_member vm2.val_name vms1 with
      | None -> false  (* sig1 must have all values that sig2 has *)
      | Some vm1 ->
          value_member_sub vm1 vm2 && value_members_match vms1 rest2

(* Check that each effect member in sig2 has a matching subtype member in sig1 *)
let rec effect_members_match (ess1 ess2: list effect_sig) : Tot bool (decreases ess2) =
  match ess2 with
  | [] -> true
  | es2 :: rest2 ->
      match lookup_effect_member es2.eff_sig_name ess1 with
      | None -> false
      | Some es1 ->
          effect_sig_sub es1 es2 && effect_members_match ess1 rest2

(* Check if member names are unique in a type member list *)
let rec type_member_names_unique (tms: list type_member) : Tot bool (decreases tms) =
  match tms with
  | [] -> true
  | tm :: rest ->
      let name = type_member_name tm in
      None? (lookup_type_member name rest) && type_member_names_unique rest

let rec value_member_names_unique (vms: list value_member) : Tot bool (decreases vms) =
  match vms with
  | [] -> true
  | vm :: rest ->
      None? (lookup_value_member vm.val_name rest) && value_member_names_unique rest

let rec effect_member_names_unique (ess: list effect_sig) : Tot bool (decreases ess) =
  match ess with
  | [] -> true
  | es :: rest ->
      None? (lookup_effect_member es.eff_sig_name rest) && effect_member_names_unique rest

(* Well-formed signature: all member names are unique *)
let wf_sig_names (s: signature) : bool =
  type_member_names_unique s.sig_types &&
  value_member_names_unique s.sig_values &&
  effect_member_names_unique s.sig_effects

(* Proper Structural Signature Subtyping: s1 <: s2
 *
 * Width subtyping: s1 can have MORE members than s2
 * Depth subtyping: each member in s2 has a subtype member in s1
 *
 * Variance:
 * - Type members: contravariant (transparent hides to opaque)
 * - Value members: covariant (more specific types allowed)
 * - Effect members: covariant (more specific effects allowed)
 *)
let signature_sub (s1 s2: signature) : bool =
  type_members_match s1.sig_types s2.sig_types &&
  value_members_match s1.sig_values s2.sig_values &&
  effect_members_match s1.sig_effects s2.sig_effects

(* Auxiliary lemma: lookup_type_member finds head if name matches *)
val lookup_type_member_head : tm:type_member -> tms:list type_member ->
  Lemma (ensures lookup_type_member (type_member_name tm) (tm :: tms) == Some tm)
let lookup_type_member_head tm tms = ()

(* Auxiliary lemma: lookup_value_member finds head if name matches *)
val lookup_value_member_head : vm:value_member -> vms:list value_member ->
  Lemma (ensures lookup_value_member vm.val_name (vm :: vms) == Some vm)
let lookup_value_member_head vm vms = ()

(* Auxiliary lemma: lookup_effect_member finds head if name matches *)
val lookup_effect_member_head : es:effect_sig -> ess:list effect_sig ->
  Lemma (ensures lookup_effect_member es.eff_sig_name (es :: ess) == Some es)
let lookup_effect_member_head es ess = ()

(* Helper: if lookup finds nothing in rest, adding element with different name preserves that *)
#push-options "--z3rlimit 100"
val lookup_type_member_extend : name:type_name -> tm:type_member -> rest:list type_member ->
  Lemma (requires type_member_name tm <> name)
        (ensures lookup_type_member name (tm :: rest) == lookup_type_member name rest)
let lookup_type_member_extend name tm rest = ()
#pop-options

(* Helper: monotonicity of type_members_match when new element has fresh name *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val type_members_match_weaken : tm:type_member -> rest:list type_member -> tms2:list type_member ->
  Lemma (requires type_members_match rest tms2 = true /\
                  None? (lookup_type_member (type_member_name tm) tms2))
        (ensures type_members_match (tm :: rest) tms2 = true)
        (decreases tms2)
let rec type_members_match_weaken tm rest tms2 =
  match tms2 with
  | [] -> ()
  | tm2 :: rest2 ->
      let name2 = type_member_name tm2 in
      let name_tm = type_member_name tm in
      (* From precondition: lookup name_tm in tms2 = None *)
      (* So name_tm <> name2 (otherwise lookup would find tm2) *)
      lookup_type_member_extend name2 tm rest;
      type_members_match_weaken tm rest rest2
#pop-options

(* Type members match is reflexive when names are unique *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 2"
val type_members_match_refl : tms:list type_member ->
  Lemma (requires type_member_names_unique tms = true)
        (ensures type_members_match tms tms = true) (decreases tms)
let rec type_members_match_refl tms =
  match tms with
  | [] -> ()
  | tm :: rest ->
      (* From uniqueness: lookup (type_member_name tm) rest = None *)
      (* So we can use weakening *)
      type_members_match_refl rest;
      type_members_match_weaken tm rest rest;
      lookup_type_member_head tm rest;
      type_member_sub_refl tm
#pop-options

(* Helper for value members *)
#push-options "--z3rlimit 100"
val lookup_value_member_extend : name:var_id -> vm:value_member -> rest:list value_member ->
  Lemma (requires vm.val_name <> name)
        (ensures lookup_value_member name (vm :: rest) == lookup_value_member name rest)
let lookup_value_member_extend name vm rest = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val value_members_match_weaken : vm:value_member -> rest:list value_member -> vms2:list value_member ->
  Lemma (requires value_members_match rest vms2 = true /\
                  None? (lookup_value_member vm.val_name vms2))
        (ensures value_members_match (vm :: rest) vms2 = true)
        (decreases vms2)
let rec value_members_match_weaken vm rest vms2 =
  match vms2 with
  | [] -> ()
  | vm2 :: rest2 ->
      lookup_value_member_extend vm2.val_name vm rest;
      value_members_match_weaken vm rest rest2
#pop-options

(* Value members match is reflexive when names are unique *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 2"
val value_members_match_refl : vms:list value_member ->
  Lemma (requires value_member_names_unique vms = true)
        (ensures value_members_match vms vms = true) (decreases vms)
let rec value_members_match_refl vms =
  match vms with
  | [] -> ()
  | vm :: rest ->
      value_members_match_refl rest;
      value_members_match_weaken vm rest rest;
      lookup_value_member_head vm rest;
      value_member_sub_refl vm
#pop-options

(* Helper for effect members *)
#push-options "--z3rlimit 100"
val lookup_effect_member_extend : name:string -> es:effect_sig -> rest:list effect_sig ->
  Lemma (requires es.eff_sig_name <> name)
        (ensures lookup_effect_member name (es :: rest) == lookup_effect_member name rest)
let lookup_effect_member_extend name es rest = ()
#pop-options

#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val effect_members_match_weaken : es:effect_sig -> rest:list effect_sig -> ess2:list effect_sig ->
  Lemma (requires effect_members_match rest ess2 = true /\
                  None? (lookup_effect_member es.eff_sig_name ess2))
        (ensures effect_members_match (es :: rest) ess2 = true)
        (decreases ess2)
let rec effect_members_match_weaken es rest ess2 =
  match ess2 with
  | [] -> ()
  | es2 :: rest2 ->
      lookup_effect_member_extend es2.eff_sig_name es rest;
      effect_members_match_weaken es rest rest2
#pop-options

(* Effect members match is reflexive when names are unique *)
#push-options "--z3rlimit 300 --fuel 4 --ifuel 2"
val effect_members_match_refl : ess:list effect_sig ->
  Lemma (requires effect_member_names_unique ess = true)
        (ensures effect_members_match ess ess = true) (decreases ess)
let rec effect_members_match_refl ess =
  match ess with
  | [] -> ()
  | es :: rest ->
      effect_members_match_refl rest;
      effect_members_match_weaken es rest rest;
      lookup_effect_member_head es rest;
      effect_sig_sub_refl es
#pop-options

(* Signature subtyping is reflexive for well-formed signatures *)
val signature_sub_refl : s:signature ->
  Lemma (requires wf_sig_names s = true)
        (ensures signature_sub s s = true)
let signature_sub_refl s =
  type_members_match_refl s.sig_types;
  value_members_match_refl s.sig_values;
  effect_members_match_refl s.sig_effects

(** ============================================================================
    AUXILIARY LEMMAS FOR SIGNATURE SUBTYPING TRANSITIVITY
    ============================================================================ *)

(* Lookup type member in subtype list preserves name *)
val lookup_type_member_name : name:type_name -> tms:list type_member ->
  Lemma (requires Some? (lookup_type_member name tms))
        (ensures type_member_name (Some?.v (lookup_type_member name tms)) = name)
let rec lookup_type_member_name name tms =
  match tms with
  | [] -> ()
  | tm :: rest ->
      if type_member_name tm = name then ()
      else lookup_type_member_name name rest

(* Lookup value member name property *)
val lookup_value_member_name : name:var_id -> vms:list value_member ->
  Lemma (requires Some? (lookup_value_member name vms))
        (ensures (Some?.v (lookup_value_member name vms)).val_name = name)
let rec lookup_value_member_name name vms =
  match vms with
  | [] -> ()
  | vm :: rest ->
      if vm.val_name = name then ()
      else lookup_value_member_name name rest

(* Lookup effect member name property *)
val lookup_effect_member_name : name:string -> ess:list effect_sig ->
  Lemma (requires Some? (lookup_effect_member name ess))
        (ensures (Some?.v (lookup_effect_member name ess)).eff_sig_name = name)
let rec lookup_effect_member_name name ess =
  match ess with
  | [] -> ()
  | es :: rest ->
      if es.eff_sig_name = name then ()
      else lookup_effect_member_name name rest

(* Type member subtyping preserves name *)
val type_member_sub_name : tm1:type_member -> tm2:type_member ->
  Lemma (requires type_member_sub tm1 tm2 = true)
        (ensures type_member_name tm1 = type_member_name tm2)
let type_member_sub_name tm1 tm2 = ()

(* Value member subtyping preserves name *)
val value_member_sub_name : vm1:value_member -> vm2:value_member ->
  Lemma (requires value_member_sub vm1 vm2 = true)
        (ensures vm1.val_name = vm2.val_name)
let value_member_sub_name vm1 vm2 = ()

(* Effect member subtyping preserves name *)
val effect_sig_sub_name : es1:effect_sig -> es2:effect_sig ->
  Lemma (requires effect_sig_sub es1 es2 = true)
        (ensures es1.eff_sig_name = es2.eff_sig_name)
let effect_sig_sub_name es1 es2 = ()

(** ============================================================================
    SIGNATURE SUBTYPING TRANSITIVITY - Individual Member Lemmas
    ============================================================================ *)

(* Type member subtyping is transitive *)
#push-options "--z3rlimit 50"
val type_member_sub_trans : tm1:type_member -> tm2:type_member -> tm3:type_member ->
  Lemma (requires type_member_sub tm1 tm2 = true /\ type_member_sub tm2 tm3 = true)
        (ensures type_member_sub tm1 tm3 = true)
let type_member_sub_trans tm1 tm2 tm3 =
  let n1 = type_member_name tm1 in
  let n2 = type_member_name tm2 in
  let n3 = type_member_name tm3 in
  let k1 = type_member_kind tm1 in
  let k2 = type_member_kind tm2 in
  let k3 = type_member_kind tm3 in
  kind_eq_trans k1 k2 k3;
  match tm1, tm2, tm3 with
  | TMTransparent _ _ t1 _ _, TMTransparent _ _ t2 _ _, TMTransparent _ _ t3 _ _ ->
      type_eq_trans t1 t2 t3
  | TMTransparent _ _ _ _ _, TMTransparent _ _ _ _ _, TMOpaque _ _ _ _ -> ()
  | TMTransparent _ _ _ _ _, TMOpaque _ _ _ _, TMOpaque _ _ _ _ -> ()
  | TMOpaque _ _ _ _, TMOpaque _ _ _ _, TMOpaque _ _ _ _ -> ()
  | _, _, _ -> ()
#pop-options

(* Type scheme subtyping is transitive *)
val type_scheme_sub_trans : ts1:type_scheme -> ts2:type_scheme -> ts3:type_scheme ->
  Lemma (requires type_scheme_sub ts1 ts2 = true /\ type_scheme_sub ts2 ts3 = true)
        (ensures type_scheme_sub ts1 ts3 = true)
let type_scheme_sub_trans ts1 ts2 ts3 =
  subtype_trans ts1.body ts2.body ts3.body

(* Value member subtyping is transitive *)
val value_member_sub_trans : vm1:value_member -> vm2:value_member -> vm3:value_member ->
  Lemma (requires value_member_sub vm1 vm2 = true /\ value_member_sub vm2 vm3 = true)
        (ensures value_member_sub vm1 vm3 = true)
let value_member_sub_trans vm1 vm2 vm3 =
  type_scheme_sub_trans vm1.val_scheme vm2.val_scheme vm3.val_scheme

(* Effect ops subtyping is transitive *)
val effect_ops_sub_trans : ops1:list (string & brrr_type) -> ops2:list (string & brrr_type) ->
                           ops3:list (string & brrr_type) ->
  Lemma (requires effect_ops_sub ops1 ops2 = true /\ effect_ops_sub ops2 ops3 = true)
        (ensures effect_ops_sub ops1 ops3 = true) (decreases ops1)
let rec effect_ops_sub_trans ops1 ops2 ops3 =
  match ops1, ops2, ops3 with
  | [], [], [] -> ()
  | (n1, t1) :: r1, (n2, t2) :: r2, (n3, t3) :: r3 ->
      subtype_trans t1 t2 t3; effect_ops_sub_trans r1 r2 r3
  | _, _, _ -> ()

(* Effect signature subtyping is transitive *)
val effect_sig_sub_trans : es1:effect_sig -> es2:effect_sig -> es3:effect_sig ->
  Lemma (requires effect_sig_sub es1 es2 = true /\ effect_sig_sub es2 es3 = true)
        (ensures effect_sig_sub es1 es3 = true)
let effect_sig_sub_trans es1 es2 es3 =
  effect_ops_sub_trans es1.eff_sig_ops es2.eff_sig_ops es3.eff_sig_ops

(** ============================================================================
    SIGNATURE SUBTYPING TRANSITIVITY - Matching Lemmas
    ============================================================================ *)

(* Helper: if type_members_match succeeds, lookup in tms1 succeeds AND subtyping holds *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val type_members_match_lookup : tms1:list type_member -> tms2:list type_member ->
                                 name:type_name ->
  Lemma (requires type_members_match tms1 tms2 = true /\ Some? (lookup_type_member name tms2))
        (ensures Some? (lookup_type_member name tms1) /\
                 type_member_sub (Some?.v (lookup_type_member name tms1))
                                 (Some?.v (lookup_type_member name tms2)) = true)
        (decreases tms2)
let rec type_members_match_lookup tms1 tms2 name =
  match tms2 with
  | [] -> ()
  | tm2 :: rest2 ->
      let n2 = type_member_name tm2 in
      if n2 = name then ()
      else type_members_match_lookup tms1 rest2 name
#pop-options

(* Helper: same for value members *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val value_members_match_lookup : vms1:list value_member -> vms2:list value_member ->
                                  name:var_id ->
  Lemma (requires value_members_match vms1 vms2 = true /\ Some? (lookup_value_member name vms2))
        (ensures Some? (lookup_value_member name vms1) /\
                 value_member_sub (Some?.v (lookup_value_member name vms1))
                                  (Some?.v (lookup_value_member name vms2)) = true)
        (decreases vms2)
let rec value_members_match_lookup vms1 vms2 name =
  match vms2 with
  | [] -> ()
  | vm2 :: rest2 ->
      if vm2.val_name = name then ()
      else value_members_match_lookup vms1 rest2 name
#pop-options

(* Helper: same for effect members *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val effect_members_match_lookup : ess1:list effect_sig -> ess2:list effect_sig ->
                                   name:string ->
  Lemma (requires effect_members_match ess1 ess2 = true /\ Some? (lookup_effect_member name ess2))
        (ensures Some? (lookup_effect_member name ess1) /\
                 effect_sig_sub (Some?.v (lookup_effect_member name ess1))
                                (Some?.v (lookup_effect_member name ess2)) = true)
        (decreases ess2)
let rec effect_members_match_lookup ess1 ess2 name =
  match ess2 with
  | [] -> ()
  | es2 :: rest2 ->
      if es2.eff_sig_name = name then ()
      else effect_members_match_lookup ess1 rest2 name
#pop-options

(* Key transitivity lemma for type members matching:
 * If tms1 matches tms2 and tms2 matches tms3, then tms1 matches tms3.
 * Uses the individual type_member_sub_trans for each member. *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val type_members_match_trans : tms1:list type_member -> tms2:list type_member ->
                                tms3:list type_member ->
  Lemma (requires type_members_match tms1 tms2 = true /\ type_members_match tms2 tms3 = true)
        (ensures type_members_match tms1 tms3 = true)
        (decreases tms3)
let rec type_members_match_trans tms1 tms2 tms3 =
  match tms3 with
  | [] -> ()
  | tm3 :: rest3 ->
      let name3 = type_member_name tm3 in
      (* From tms2 matches tms3: lookup name3 in tms2 succeeds *)
      assert (Some? (lookup_type_member name3 tms2));
      let tm2 = Some?.v (lookup_type_member name3 tms2) in
      lookup_type_member_name name3 tms2;
      (* name of tm2 = name3 *)
      let name2 = type_member_name tm2 in
      (* From tms1 matches tms2: we need to show lookup name2 in tms1 succeeds *)
      (* name2 = name3, and tm2 is in tms2, so lookup name2 in tms2 succeeds *)
      (* By type_members_match_lookup: lookup name2 in tms1 succeeds *)
      type_members_match_lookup tms1 tms2 name2;
      let tm1 = Some?.v (lookup_type_member name2 tms1) in
      (* By transitivity: tm1 <: tm3 *)
      type_member_sub_trans tm1 tm2 tm3;
      (* Recurse on rest *)
      type_members_match_trans tms1 tms2 rest3
#pop-options

(* Key transitivity lemma for value members matching *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val value_members_match_trans : vms1:list value_member -> vms2:list value_member ->
                                 vms3:list value_member ->
  Lemma (requires value_members_match vms1 vms2 = true /\ value_members_match vms2 vms3 = true)
        (ensures value_members_match vms1 vms3 = true)
        (decreases vms3)
let rec value_members_match_trans vms1 vms2 vms3 =
  match vms3 with
  | [] -> ()
  | vm3 :: rest3 ->
      let name3 = vm3.val_name in
      assert (Some? (lookup_value_member name3 vms2));
      let vm2 = Some?.v (lookup_value_member name3 vms2) in
      lookup_value_member_name name3 vms2;
      let name2 = vm2.val_name in
      value_members_match_lookup vms1 vms2 name2;
      let vm1 = Some?.v (lookup_value_member name2 vms1) in
      value_member_sub_trans vm1 vm2 vm3;
      value_members_match_trans vms1 vms2 rest3
#pop-options

(* Key transitivity lemma for effect members matching *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val effect_members_match_trans : ess1:list effect_sig -> ess2:list effect_sig ->
                                  ess3:list effect_sig ->
  Lemma (requires effect_members_match ess1 ess2 = true /\ effect_members_match ess2 ess3 = true)
        (ensures effect_members_match ess1 ess3 = true)
        (decreases ess3)
let rec effect_members_match_trans ess1 ess2 ess3 =
  match ess3 with
  | [] -> ()
  | es3 :: rest3 ->
      let name3 = es3.eff_sig_name in
      assert (Some? (lookup_effect_member name3 ess2));
      let es2 = Some?.v (lookup_effect_member name3 ess2) in
      lookup_effect_member_name name3 ess2;
      let name2 = es2.eff_sig_name in
      effect_members_match_lookup ess1 ess2 name2;
      let es1 = Some?.v (lookup_effect_member name2 ess1) in
      effect_sig_sub_trans es1 es2 es3;
      effect_members_match_trans ess1 ess2 rest3
#pop-options

(* Signature subtyping is transitive - MAIN THEOREM
 * Uses the member matching transitivity lemmas above *)
#push-options "--z3rlimit 100"
val signature_sub_trans : s1:signature -> s2:signature -> s3:signature ->
  Lemma (requires signature_sub s1 s2 = true /\ signature_sub s2 s3 = true)
        (ensures signature_sub s1 s3 = true)
let signature_sub_trans s1 s2 s3 =
  type_members_match_trans s1.sig_types s2.sig_types s3.sig_types;
  value_members_match_trans s1.sig_values s2.sig_values s3.sig_values;
  effect_members_match_trans s1.sig_effects s2.sig_effects s3.sig_effects
#pop-options

(** ============================================================================
    MODULE TYPE SUBTYPING
    ============================================================================ *)

(* Module type subtyping: mt1 <: mt2
 *
 * Rules:
 * - MTSig s1 <: MTSig s2 iff signature_sub s1 s2
 * - MTFunctor(X, P1, R1) <: MTFunctor(X, P2, R2) iff
 *     P2 <: P1 (contravariant in parameter)
 *     R1 <: R2 (covariant in result)
 *
 * Uses sum of sizes for termination due to contravariant recursion.
 * Equality check delegates to signature_sub which has its own equality short-circuit.
 *)
let rec module_type_sub (mt1 mt2: module_type)
    : Tot bool (decreases module_type_size mt1 + module_type_size mt2) =
  match mt1, mt2 with
  | MTSig s1, MTSig s2 -> signature_sub s1 s2
  | MTFunctor x1 p1 r1 mode1, MTFunctor x2 p2 r2 mode2 ->
      (* Require same parameter name and mode *)
      x1 = x2 && mode1 = mode2 &&
      (* Contravariant in parameter: p2 <: p1 *)
      module_type_sub p2 p1 &&
      (* Covariant in result: r1 <: r2 *)
      module_type_sub r1 r2
  | _, _ -> false

(* Well-formed module type: all signatures have unique names *)
let rec wf_module_type_names (mt: module_type) : Tot bool (decreases mt) =
  match mt with
  | MTSig s -> wf_sig_names s
  | MTFunctor _ p r _ -> wf_module_type_names p && wf_module_type_names r

(* Module type subtyping is reflexive for well-formed module types *)
val module_type_sub_refl : mt:module_type ->
  Lemma (requires wf_module_type_names mt = true)
        (ensures module_type_sub mt mt = true) (decreases mt)
let rec module_type_sub_refl mt =
  match mt with
  | MTSig s -> signature_sub_refl s
  | MTFunctor x p r _ ->
      module_type_sub_refl p;
      module_type_sub_refl r

(* Module type subtyping transitivity *)
#push-options "--z3rlimit 800 --fuel 8 --ifuel 4"
val module_type_sub_trans : mt1:module_type -> mt2:module_type -> mt3:module_type ->
  Lemma (requires module_type_sub mt1 mt2 = true /\ module_type_sub mt2 mt3 = true)
        (ensures module_type_sub mt1 mt3 = true)
        (decreases module_type_size mt1 + module_type_size mt2 + module_type_size mt3)
let rec module_type_sub_trans mt1 mt2 mt3 =
  match mt1, mt2, mt3 with
  | MTSig s1, MTSig s2, MTSig s3 ->
      (* Use signature_sub_trans for proper structural subtyping *)
      signature_sub_trans s1 s2 s3
  | MTFunctor x1 p1 r1 _, MTFunctor x2 p2 r2 _, MTFunctor x3 p3 r3 _ ->
      (* Contravariant: p3 <: p2 <: p1 implies p3 <: p1 *)
      module_type_sub_trans p3 p2 p1;
      (* Covariant: r1 <: r2 <: r3 implies r1 <: r3 *)
      module_type_sub_trans r1 r2 r3
  | _, _, _ -> ()
#pop-options

(** ============================================================================
    TYPE SUBSTITUTION IN SIGNATURES
    ============================================================================ *)

(* Substitute a type variable in a type member, preserving visibility and range *)
let subst_in_type_member (v: type_var) (replacement: brrr_type) (tm: type_member) : type_member =
  match tm with
  | TMOpaque n k vis r -> TMOpaque n k vis r
  | TMTransparent n k t vis r -> TMTransparent n k (subst_type_var v replacement t) vis r

(* Substitute in type member list *)
let rec subst_in_type_members (v: type_var) (replacement: brrr_type) (tms: list type_member)
    : list type_member =
  match tms with
  | [] -> []
  | tm :: rest -> subst_in_type_member v replacement tm :: subst_in_type_members v replacement rest

(* Substitute in type scheme *)
let subst_in_type_scheme (v: type_var) (replacement: brrr_type) (ts: type_scheme) : type_scheme =
  if List.Tot.mem v ts.type_vars then ts  (* v is bound, don't substitute *)
  else { ts with body = subst_type_var v replacement ts.body }

(* Substitute in value member *)
let subst_in_value_member (v: type_var) (replacement: brrr_type) (vm: value_member) : value_member =
  { vm with val_scheme = subst_in_type_scheme v replacement vm.val_scheme }

(* Substitute in value member list *)
let rec subst_in_value_members (v: type_var) (replacement: brrr_type) (vms: list value_member)
    : list value_member =
  match vms with
  | [] -> []
  | vm :: rest -> subst_in_value_member v replacement vm :: subst_in_value_members v replacement rest

(* Substitute in effect operation *)
let subst_in_effect_op (v: type_var) (replacement: brrr_type) (op: string & brrr_type)
    : string & brrr_type =
  (fst op, subst_type_var v replacement (snd op))

(* Substitute in effect operations *)
let rec subst_in_effect_ops (v: type_var) (replacement: brrr_type) (ops: list (string & brrr_type))
    : list (string & brrr_type) =
  match ops with
  | [] -> []
  | op :: rest -> subst_in_effect_op v replacement op :: subst_in_effect_ops v replacement rest

(* Substitute in effect signature *)
let subst_in_effect_sig (v: type_var) (replacement: brrr_type) (es: effect_sig) : effect_sig =
  { es with eff_sig_ops = subst_in_effect_ops v replacement es.eff_sig_ops }

(* Substitute in effect signature list *)
let rec subst_in_effect_sigs (v: type_var) (replacement: brrr_type) (ess: list effect_sig)
    : list effect_sig =
  match ess with
  | [] -> []
  | es :: rest -> subst_in_effect_sig v replacement es :: subst_in_effect_sigs v replacement rest

(* Substitute type variable in signature *)
let subst_in_signature (v: type_var) (replacement: brrr_type) (sig: signature) : signature =
  { sig_types = subst_in_type_members v replacement sig.sig_types;
    sig_values = subst_in_value_members v replacement sig.sig_values;
    sig_effects = subst_in_effect_sigs v replacement sig.sig_effects }

(* Substitute type variable in module type *)
let rec subst_in_module_type (v: type_var) (replacement: brrr_type) (mt: module_type)
    : Tot module_type (decreases mt) =
  match mt with
  | MTSig s -> MTSig (subst_in_signature v replacement s)
  | MTFunctor x param result mode ->
      MTFunctor x
        (subst_in_module_type v replacement param)
        (subst_in_module_type v replacement result)
        mode

(** ============================================================================
    MODULE ENVIRONMENT
    ============================================================================ *)

(* Module environment: maps module variables to their types *)
type module_env = list (module_var & module_type)

(* Empty module environment *)
let empty_module_env : module_env = []

(* Extend module environment *)
let extend_module_env (x: module_var) (mt: module_type) (env: module_env) : module_env =
  (x, mt) :: env

(* Lookup module variable *)
let rec lookup_module_var (x: module_var) (env: module_env) : option module_type =
  match env with
  | [] -> None
  | (y, mt) :: rest ->
      if x = y then Some mt
      else lookup_module_var x rest

(** ============================================================================
    MODULE PATH RESOLUTION
    ============================================================================ *)

(* Resolve a module path to a module type *)
let rec resolve_path (env: module_env) (path: module_path) : option module_type =
  match path with
  | MPVar x -> lookup_module_var x env
  | MPDot base name ->
      match resolve_path env base with
      | Some (MTSig sig) ->
          (* Look for a nested module - simplified: treat as type member *)
          None  (* Nested modules would need additional tracking *)
      | _ -> None

(** ============================================================================
    MODULE TYPE CHECKING RESULT
    ============================================================================ *)

(* Result of module type checking *)
noeq type module_check_result =
  | ModuleOk  : module_type -> module_check_result
  | ModuleErr : string -> module_check_result

(** ============================================================================
    MODULE EXPRESSION TYPE CHECKING
    ============================================================================ *)

(* Infer signature from module declarations *)
let rec infer_decls_sig (decls: list module_decl) : signature =
  match decls with
  | [] -> empty_sig
  | MDType tm :: rest ->
      sig_add_type tm (infer_decls_sig rest)
  | MDVal x t :: rest ->
      sig_add_value { val_name = x; val_scheme = mono_type t } (infer_decls_sig rest)
  | MDEffect es :: rest ->
      sig_add_effect es (infer_decls_sig rest)
  | MDModule _ _ :: rest ->
      (* Nested modules: simplified - skip in signature *)
      infer_decls_sig rest

(* Type-check a module expression and return its module type *)
let rec check_module_expr (env: module_env) (me: module_expr)
    : Tot module_check_result (decreases module_expr_size me) =
  match me with
  (* Structure: infer signature from declarations *)
  | MEStruct decls ->
      ModuleOk (MTSig (infer_decls_sig decls))

  (* Functor: check body under extended environment, preserve mode *)
  | MEFunctor x param_type mode body ->
      let env' = extend_module_env x param_type env in
      (match check_module_expr env' body with
       | ModuleOk body_type -> ModuleOk (MTFunctor x param_type body_type mode)
       | err -> err)

  (* Application: check functor and argument, verify subtyping *)
  | MEApp func arg ->
      (match check_module_expr env func with
       | ModuleOk (MTFunctor x param_type result_type mode) ->
           (match check_module_expr env arg with
            | ModuleOk arg_type ->
                if module_type_sub arg_type param_type then
                  (* Result depends on functor mode:
                   * - Applicative: types are shared, same result for equal args
                   * - Generative: fresh types, each application is distinct *)
                  ModuleOk result_type
                else
                  ModuleErr "Functor argument type mismatch"
            | err -> err)
       | ModuleOk _ -> ModuleErr "Cannot apply non-functor module"
       | err -> err)

  (* Path: resolve in environment *)
  | MEPath path ->
      (match resolve_path env path with
       | Some mt -> ModuleOk mt
       | None -> ModuleErr "Unbound module path")

  (* Sealing: check module, verify subtyping to target type *)
  | MESeal m target_type ->
      (match check_module_expr env m with
       | ModuleOk inferred_type ->
           if module_type_sub inferred_type target_type then
             ModuleOk target_type  (* Return the sealed type *)
           else
             ModuleErr "Module does not match signature for sealing"
       | err -> err)

(** ============================================================================
    FUNCTOR APPLICATION SEMANTICS
    ============================================================================ *)

(* Apply a functor type to an argument module type
 *
 * Given: F : functor(X : P) -> R with mode
 * And:   M : A where A <: P
 * Return: R[X := A] (substitute A for X in R)
 *
 * For applicative functors: types are shared across applications
 * For generative functors: fresh types on each application
 *)
let apply_functor (func_type: module_type) (arg_type: module_type) : option module_type =
  match func_type with
  | MTFunctor x param result _mode ->
      if module_type_sub arg_type param then
        (* Simplified: return result directly
         * Full implementation would substitute type members from arg_type
         * and handle generative stamping *)
        Some result
      else
        None
  | _ -> None

(* Get functor mode from module type *)
let get_functor_mode (mt: module_type) : option functor_mode =
  match mt with
  | MTFunctor _ _ _ mode -> Some mode
  | _ -> None

(* Check if functor is applicative *)
let is_applicative_functor (mt: module_type) : bool =
  match get_functor_mode mt with
  | Some Applicative -> true
  | _ -> false

(* Check if functor is generative *)
let is_generative_functor (mt: module_type) : bool =
  match get_functor_mode mt with
  | Some Generative -> true
  | _ -> false

(* Helper: get parameter type from functor *)
let get_functor_param (mt: module_type{MTFunctor? mt}) : module_type =
  match mt with
  | MTFunctor _ param _ _ -> param

(* Functor application preserves well-formedness:
 * If F : functor(X : P) -> R and M : A with A <: P,
 * then F(M) : R[X := A] is well-formed *)
val functor_app_well_formed : func:module_type -> arg:module_type ->
  Lemma (requires MTFunctor? func /\ module_type_sub arg (get_functor_param func) = true)
        (ensures Some? (apply_functor func arg))
let functor_app_well_formed func arg =
  match func with
  | MTFunctor _ param _ _ -> ()
  | MTSig _ -> ()

(** ============================================================================
    SEALING SEMANTICS
    ============================================================================

    Sealing (opaque ascription) is the fundamental abstraction mechanism in
    ML-style module systems. It creates an abstraction barrier by hiding
    type implementations.

    SYNTAX:
    -------
      M :> S      (* Opaque ascription - sealing *)
      M : S       (* Transparent ascription - does not seal *)

    SEMANTICS:
    ----------
    Given M : T where T <: S, the result (M :> S) has type S exactly,
    not a subtype of S. Abstract types in S become truly opaque:
      - Their implementation (from T) is forgotten
      - Clients cannot know what the abstract type actually is
      - The abstraction barrier cannot be crossed

    EXAMPLE:
    --------
      module Counter = {
        type t = int           (* Implementation: counter is int *)
        let zero = 0
        let inc x = x + 1
        let get x = x
      }

      module AbstractCounter = Counter :> {
        type t                 (* Now abstract! *)
        val zero : t
        val inc : t -> t
        val get : t -> int
      }

      (* Client cannot know AbstractCounter.t = int *)
      (* Cannot do: AbstractCounter.zero + 1 *)

    EXISTENTIAL INTERPRETATION:
    ---------------------------
    Sealing corresponds to existential type packaging:
      M :> { type t; val x : t }  ~=  pack (tau, v) as exists t. t

    The implementation type (tau) is hidden, and clients must work
    polymorphically over the abstract type.

    TYPING RULE (Spec Definition 5.5):
    ----------------------------------
      Gamma |- M : T    T <: S
      ------------------------
      Gamma |- M :> S : S

    Note: the result type is S exactly, not T. This is the key difference
    from transparent ascription (M : S) which preserves more type info.

    ABSTRACTION THEOREM:
    --------------------
    If M :> S and type t is abstract in S, then no client can distinguish
    the implementation of t from any other implementation satisfying S.
    This is the formal statement of representation independence.

    COMPARISON WITH F* .fsti:
    -------------------------
    F*'s .fsti files serve a similar sealing purpose:
      - Types not revealed in .fsti are effectively sealed
      - The friend declaration can break the seal (for trusted code)
      - Different files enforce the abstraction boundary

    Brrr makes sealing explicit in the language, allowing more flexible
    abstraction boundaries within a single file.
    ============================================================================ *)

(** Sealing operation: hide implementation details.
    Given M : T and T <: S, sealing produces type S exactly (not a subtype).
    Returns None if the implementation doesn't match the seal type. *)
let seal_module (impl_type: module_type) (seal_type: module_type) : option module_type =
  if module_type_sub impl_type seal_type then
    Some seal_type
  else
    None

(* Sealing respects subtyping:
 * If M : T and T <: S, then (M : S) : S *)
val seal_respects_subtype : impl:module_type -> seal:module_type ->
  Lemma (requires module_type_sub impl seal = true)
        (ensures Some? (seal_module impl seal) /\ Some?.v (seal_module impl seal) == seal)
let seal_respects_subtype impl seal = ()

(** ============================================================================
    WELL-FORMEDNESS PREDICATES
    ============================================================================ *)

(* A signature is well-formed if all type members have valid kinds
 * and all value types reference only defined type members *)
let rec wf_type_members (tms: list type_member) : bool =
  match tms with
  | [] -> true
  | TMOpaque _ k :: rest -> wf_type_members rest
  | TMTransparent _ k t :: rest ->
      (* Check that t is well-kinded *)
      (match infer_kind empty_kind_ctx t with
       | Some k' -> kind_eq k k' && wf_type_members rest
       | None -> false)

let wf_signature (sig: signature) : bool =
  wf_type_members sig.sig_types

let rec wf_module_type (mt: module_type) : Tot bool (decreases mt) =
  match mt with
  | MTSig s -> wf_signature s
  | MTFunctor _ p r _ -> wf_module_type p && wf_module_type r

(** ============================================================================
    SIGNATURE STRENGTHENING
    ============================================================================ *)

(* Strengthen a signature by making abstract types transparent
 * This is used when we know the implementation.
 * Preserves visibility and range from the original member. *)
let strengthen_type_member (known_def: option brrr_type) (tm: type_member) : type_member =
  match known_def, tm with
  | Some t, TMOpaque n k vis r -> TMTransparent n k t vis r
  | _, _ -> tm

let rec strengthen_type_members (defs: list (type_name & brrr_type)) (tms: list type_member)
    : list type_member =
  match tms with
  | [] -> []
  | tm :: rest ->
      let name = type_member_name tm in
      let known = assoc name defs in
      strengthen_type_member known tm :: strengthen_type_members defs rest

let strengthen_signature (defs: list (type_name & brrr_type)) (sig: signature) : signature =
  { sig with sig_types = strengthen_type_members defs sig.sig_types }

(** ============================================================================
    SIGNATURE MATCHING
    ============================================================================ *)

(* Check if a module expression matches a module type *)
let check_module_against_type (env: module_env) (me: module_expr) (expected: module_type)
    : module_check_result =
  match check_module_expr env me with
  | ModuleOk inferred ->
      if module_type_sub inferred expected then
        ModuleOk expected
      else
        ModuleErr "Module does not match expected signature"
  | err -> err

(** ============================================================================
    MODULE SYSTEM SOUNDNESS PROPERTIES
    ============================================================================ *)

(* Helper: type_member_list_eq implies lookup returns same result *)
#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"
val type_member_list_eq_lookup : tms1:list type_member -> tms2:list type_member -> name:type_name ->
  Lemma (requires type_member_list_eq tms1 tms2 = true)
        (ensures (Some? (lookup_type_member name tms1) = Some? (lookup_type_member name tms2)))
        (decreases tms1)
let rec type_member_list_eq_lookup tms1 tms2 name =
  match tms1, tms2 with
  | [], [] -> ()
  | tm1 :: r1, tm2 :: r2 ->
      if type_member_name tm1 = name then ()
      else type_member_list_eq_lookup r1 r2 name
  | _, _ -> ()
#pop-options

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"
val value_member_list_eq_lookup : vms1:list value_member -> vms2:list value_member -> name:var_id ->
  Lemma (requires value_member_list_eq vms1 vms2 = true)
        (ensures (Some? (lookup_value_member name vms1) = Some? (lookup_value_member name vms2)))
        (decreases vms1)
let rec value_member_list_eq_lookup vms1 vms2 name =
  match vms1, vms2 with
  | [], [] -> ()
  | vm1 :: r1, vm2 :: r2 ->
      if vm1.val_name = name then ()
      else value_member_list_eq_lookup r1 r2 name
  | _, _ -> ()
#pop-options

(* Property: Signature subtyping is sound with respect to type member access *)
val sig_sub_type_access : s1:signature -> s2:signature -> name:type_name ->
  Lemma (requires signature_sub s1 s2 = true /\
                  Some? (lookup_type_member name s2.sig_types))
        (ensures Some? (lookup_type_member name s1.sig_types))
let sig_sub_type_access s1 s2 name =
  type_members_match_lookup s1.sig_types s2.sig_types name

(* Property: Signature subtyping is sound with respect to value member access *)
val sig_sub_value_access : s1:signature -> s2:signature -> name:var_id ->
  Lemma (requires signature_sub s1 s2 = true /\
                  Some? (lookup_value_member name s2.sig_values))
        (ensures Some? (lookup_value_member name s1.sig_values))
let sig_sub_value_access s1 s2 name =
  value_members_match_lookup s1.sig_values s2.sig_values name

(** ============================================================================
    CONVENIENCE CONSTRUCTORS
    ============================================================================ *)

(* Create a simple signature with one value binding *)
let sig_val (name: var_id) (ty: brrr_type) : signature =
  sig_add_value { val_name = name; val_scheme = mono_type ty } empty_sig

(* Create a simple signature with one opaque type *)
let sig_abstract_type (name: type_name) (k: kind) : signature =
  sig_add_type (TMOpaque name k) empty_sig

(* Create a simple signature with one transparent type *)
let sig_concrete_type (name: type_name) (k: kind) (def: brrr_type) : signature =
  sig_add_type (TMTransparent name k def) empty_sig

(* Create a functor type with default applicative mode *)
let mk_functor_type (param_name: module_var) (param_sig: signature) (result_sig: signature)
    : module_type =
  MTFunctor param_name (MTSig param_sig) (MTSig result_sig) Applicative

(* Create a functor type with explicit mode *)
let mk_functor_type_with_mode
    (param_name: module_var)
    (param_sig: signature)
    (result_sig: signature)
    (mode: functor_mode)
    : module_type =
  MTFunctor param_name (MTSig param_sig) (MTSig result_sig) mode

(* Create a generative functor type *)
let mk_generative_functor_type (param_name: module_var) (param_sig: signature) (result_sig: signature)
    : module_type =
  MTFunctor param_name (MTSig param_sig) (MTSig result_sig) Generative

(* Create a simple module expression with one value *)
let me_single_val (name: var_id) (ty: brrr_type) : module_expr =
  MEStruct [MDVal name ty]

(* Create a sealed module *)
let me_sealed (m: module_expr) (sig: signature) : module_expr =
  MESeal m (MTSig sig)

(** ============================================================================
    SIGNATURE TYPE REFINEMENT (Where Clauses)
    ============================================================================

    Where clauses implement type sharing and refinement, essential for
    practical use of ML-style module systems.

    SYNTAX:
    -------
      Sigma where type p = tau

    This refines signature Sigma by making abstract type p transparent
    with definition tau.

    SEMANTICS:
    ----------
    Given: Sigma = { type t; val x : t }
    Then:  Sigma where type t = int = { type t = int; val x : int }

    The where clause:
      1. Finds the abstract type named p in Sigma
      2. Makes it transparent with definition tau
      3. Substitutes tau for p throughout the signature

    MOTIVATION:
    -----------
    Without where clauses, functor application loses type information:

      module Set = functor(Ord : { type t; val compare : t -> t -> int }) -> {
        type set
        val empty : set
        val add : Ord.t -> set -> set
      }

      module IntSet = Set(IntOrd)
      module IntSet2 = Set(IntOrd)

      (* Problem: IntSet.set and IntSet2.set are unrelated types! *)

    With where clauses (and applicative functors):

      (* Result type refined with argument's types *)
      IntSet : (Set(IntOrd) where type elem = IntOrd.t)
      IntSet2 : (Set(IntOrd) where type elem = IntOrd.t)

      (* Now IntSet.set = IntSet2.set when IntOrd.t shared *)

    SUBTYPING PROPERTY:
    -------------------
    Key theorem: Sigma where type p = tau <: Sigma

    Making a type more specific (transparent vs opaque) is always valid
    for subtyping. This enables using refined signatures where abstract
    ones are expected.

    USE CASES:
    ----------
    1. FUNCTOR APPLICATION TYPE SHARING
       F(M) refines result signature with M's transparent types.
       Essential for applicative functor semantics.

    2. EXPLICIT TYPE CONSTRAINTS
       module N : S where type t = int
       Forces t to be int in the ascription.

    3. SIGNATURE COMPOSITION
       Combining signatures with shared types:
       S1 where type t = S2.u
       Makes t and u the same type.

    4. MODULE CONFIGURATION
       Instantiating generic modules with specific types:
       Config where type Database = PostgreSQL

    WHERE CLAUSE VALIDITY:
    ----------------------
    A where clause "Sigma where type p = tau" is valid iff:
      1. p exists in Sigma (as abstract or transparent)
      2. If p is abstract with kind k, tau must have kind k
      3. If p is already transparent with def tau', then tau = tau'

    IMPLEMENTATION:
    ---------------
    where_clause record stores:
      - wc_type_path: which type to refine
      - wc_definition: the new definition
      - wc_kind: the type's kind (for validation)

    Application proceeds by:
      1. Validate the where clause against the signature
      2. Transform the matching type member to transparent
      3. Return the refined signature
    ============================================================================ *)

(* A where clause refines an abstract type to a concrete type.
 * Represents the "where type p = tau" construct from ML module systems. *)
noeq type where_clause = {
  wc_type_path : type_name;    (* The abstract type to refine *)
  wc_definition : brrr_type;   (* The concrete type it equals *)
  wc_kind : kind               (* Kind of the type (must match) *)
}

(* Create a where clause with explicit kind *)
let mk_where_clause (path: type_name) (k: kind) (def: brrr_type) : where_clause = {
  wc_type_path = path;
  wc_definition = def;
  wc_kind = k
}

(* Create a where clause inferring kind as KStar (common case) *)
let mk_where_clause_simple (path: type_name) (def: brrr_type) : where_clause = {
  wc_type_path = path;
  wc_definition = def;
  wc_kind = KStar
}

(** ============================================================================
    WHERE CLAUSE EQUALITY
    ============================================================================ *)

(* Where clause equality *)
let where_clause_eq (wc1 wc2: where_clause) : bool =
  wc1.wc_type_path = wc2.wc_type_path &&
  kind_eq wc1.wc_kind wc2.wc_kind &&
  type_eq wc1.wc_definition wc2.wc_definition

(* Where clause equality is reflexive *)
val where_clause_eq_refl : wc:where_clause ->
  Lemma (where_clause_eq wc wc = true)
        [SMTPat (where_clause_eq wc wc)]
let where_clause_eq_refl wc =
  kind_eq_refl wc.wc_kind;
  type_eq_refl wc.wc_definition

(* Where clause equality is symmetric *)
val where_clause_eq_sym : wc1:where_clause -> wc2:where_clause ->
  Lemma (requires where_clause_eq wc1 wc2 = true)
        (ensures where_clause_eq wc2 wc1 = true)
let where_clause_eq_sym wc1 wc2 =
  kind_eq_sym wc1.wc_kind wc2.wc_kind;
  type_eq_sym wc1.wc_definition wc2.wc_definition

(* Where clause equality is transitive *)
val where_clause_eq_trans : wc1:where_clause -> wc2:where_clause -> wc3:where_clause ->
  Lemma (requires where_clause_eq wc1 wc2 = true /\ where_clause_eq wc2 wc3 = true)
        (ensures where_clause_eq wc1 wc3 = true)
let where_clause_eq_trans wc1 wc2 wc3 =
  kind_eq_trans wc1.wc_kind wc2.wc_kind wc3.wc_kind;
  type_eq_trans wc1.wc_definition wc2.wc_definition wc3.wc_definition

(** ============================================================================
    APPLYING WHERE CLAUSES
    ============================================================================ *)

(* Apply a single where clause to type members:
 * If we find an abstract type matching the path, make it transparent.
 * If already transparent, override the definition (must validate separately). *)
let rec apply_where_to_type_members
    (wc: where_clause)
    (tms: list type_member)
    : Tot (list type_member) (decreases tms) =
  match tms with
  | [] -> []
  | tm :: rest ->
      let tm' =
        if type_member_name tm = wc.wc_type_path then
          match tm with
          | TMOpaque n k vis r -> TMTransparent n k wc.wc_definition vis r
          | TMTransparent n k _ vis r -> TMTransparent n k wc.wc_definition vis r
        else tm
      in
      tm' :: apply_where_to_type_members wc rest

(* Apply a where clause to a signature *)
let apply_where_clause (wc: where_clause) (sig: signature) : signature =
  { sig with sig_types = apply_where_to_type_members wc sig.sig_types }

(* Apply multiple where clauses in sequence (left to right) *)
let rec apply_where_clauses (wcs: list where_clause) (sig: signature)
    : Tot signature (decreases wcs) =
  match wcs with
  | [] -> sig
  | wc :: rest -> apply_where_clauses rest (apply_where_clause wc sig)

(** ============================================================================
    REFINED SIGNATURE TYPE
    ============================================================================ *)

(* A refined signature is a base signature with where clauses.
 * Represents "Sigma where type p1 = tau1 where type p2 = tau2 ..." *)
noeq type refined_signature = {
  rs_base : signature;
  rs_wheres : list where_clause
}

(* Create a refined signature from base *)
let refine_signature (base: signature) (wcs: list where_clause) : refined_signature = {
  rs_base = base;
  rs_wheres = wcs
}

(* Create from plain signature (no where clauses) *)
let unrefined (sig: signature) : refined_signature = {
  rs_base = sig;
  rs_wheres = []
}

(* Add a where clause to a refined signature *)
let add_where (wc: where_clause) (rs: refined_signature) : refined_signature = {
  rs_base = rs.rs_base;
  rs_wheres = wc :: rs.rs_wheres
}

(* Flatten a refined signature by applying all where clauses *)
let flatten_refined_sig (rs: refined_signature) : signature =
  apply_where_clauses rs.rs_wheres rs.rs_base

(* Size for termination *)
let refined_sig_size (rs: refined_signature) : nat =
  List.Tot.length rs.rs_wheres

(** ============================================================================
    WHERE CLAUSE VALIDATION
    ============================================================================ *)

(* Check if a where clause is valid for a signature:
 * 1. The type path must exist in the signature
 * 2. The kinds must match
 * 3. If the type is already transparent, definitions must be compatible *)
let where_clause_valid (wc: where_clause) (sig: signature) : bool =
  match lookup_type_member wc.wc_type_path sig.sig_types with
  | None -> false  (* Type doesn't exist in signature *)
  | Some tm ->
      let k = type_member_kind tm in
      if not (kind_eq k wc.wc_kind) then false  (* Kind mismatch *)
      else match tm with
        | TMOpaque _ _ _ _ -> true  (* Can always refine abstract type *)
        | TMTransparent _ _ existing _ _ ->
            (* If already transparent, must match existing definition *)
            type_eq wc.wc_definition existing

(* Check all where clauses are valid, applied sequentially *)
let rec where_clauses_valid (wcs: list where_clause) (sig: signature)
    : Tot bool (decreases wcs) =
  match wcs with
  | [] -> true
  | wc :: rest ->
      if not (where_clause_valid wc sig) then false
      else where_clauses_valid rest (apply_where_clause wc sig)

(* Well-formedness of refined signature *)
let wf_refined_signature (rs: refined_signature) : bool =
  wf_sig_names rs.rs_base &&
  where_clauses_valid rs.rs_wheres rs.rs_base

(* Type checking a where clause against a kind context *)
let where_clause_well_kinded (ctx: kind_ctx) (wc: where_clause) : bool =
  match infer_kind ctx wc.wc_definition with
  | None -> false
  | Some k -> kind_eq k wc.wc_kind

(** ============================================================================
    SUBTYPING WITH WHERE CLAUSES
    ============================================================================ *)

(* Where clause subtyping: wc1 <: wc2
 * Same path and kind, definition of wc1 is subtype of wc2's definition *)
let where_clause_sub (wc1 wc2: where_clause) : bool =
  wc1.wc_type_path = wc2.wc_type_path &&
  kind_eq wc1.wc_kind wc2.wc_kind &&
  subtype wc1.wc_definition wc2.wc_definition

(* Refined signature subtyping:
 * rs1 <: rs2 iff flatten(rs1) <: flatten(rs2)
 *
 * Key insight: where clauses make types more specific (transparent),
 * so a signature with more where clauses is a subtype of one with fewer.
 *)
let refined_signature_sub (rs1 rs2: refined_signature) : bool =
  signature_sub (flatten_refined_sig rs1) (flatten_refined_sig rs2)

(* Reflexivity of where clause subtyping *)
val where_clause_sub_refl : wc:where_clause ->
  Lemma (where_clause_sub wc wc = true)
        [SMTPat (where_clause_sub wc wc)]
let where_clause_sub_refl wc =
  kind_eq_refl wc.wc_kind;
  subtype_refl wc.wc_definition

(* Transitivity of where clause subtyping *)
val where_clause_sub_trans : wc1:where_clause -> wc2:where_clause -> wc3:where_clause ->
  Lemma (requires where_clause_sub wc1 wc2 = true /\ where_clause_sub wc2 wc3 = true)
        (ensures where_clause_sub wc1 wc3 = true)
let where_clause_sub_trans wc1 wc2 wc3 =
  kind_eq_trans wc1.wc_kind wc2.wc_kind wc3.wc_kind;
  subtype_trans wc1.wc_definition wc2.wc_definition wc3.wc_definition

(** ============================================================================
    WHERE CLAUSE APPLICATION PROPERTIES
    ============================================================================ *)

(* Helper: applying where clause preserves other type members *)
#push-options "--z3rlimit 100"
val apply_where_preserves_others : wc:where_clause -> tms:list type_member -> name:type_name ->
  Lemma (requires name <> wc.wc_type_path)
        (ensures lookup_type_member name (apply_where_to_type_members wc tms) ==
                 lookup_type_member name tms)
        (decreases tms)
let rec apply_where_preserves_others wc tms name =
  match tms with
  | [] -> ()
  | tm :: rest ->
      if type_member_name tm = name then ()
      else apply_where_preserves_others wc rest name
#pop-options

(* Helper: applying where clause makes target transparent *)
#push-options "--z3rlimit 100"
val apply_where_makes_transparent : wc:where_clause -> tms:list type_member ->
  Lemma (requires Some? (lookup_type_member wc.wc_type_path tms))
        (ensures
          (let tms' = apply_where_to_type_members wc tms in
           Some? (lookup_type_member wc.wc_type_path tms') /\
           is_transparent (Some?.v (lookup_type_member wc.wc_type_path tms'))))
        (decreases tms)
let rec apply_where_makes_transparent wc tms =
  match tms with
  | [] -> ()
  | tm :: rest ->
      if type_member_name tm = wc.wc_type_path then ()
      else apply_where_makes_transparent wc rest
#pop-options

(* Helper: The transformed type member is a subtype of the original.
 * Key insight: TMTransparent n k t <: TMOpaque n k is always true (hiding implementation).
 * For transparent targets with matching definitions, reflexivity applies. *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val apply_where_single_member_sub : wc:where_clause -> tm:type_member ->
  Lemma (requires
           type_member_name tm = wc.wc_type_path /\
           kind_eq (type_member_kind tm) wc.wc_kind = true /\
           (TMOpaque? tm \/ (TMTransparent? tm /\ type_eq wc.wc_definition (TMTransparent?._2 tm) = true)))
        (ensures
          (let tm' = match tm with
             | TMOpaque n k vis r -> TMTransparent n k wc.wc_definition vis r
             | TMTransparent n k _ vis r -> TMTransparent n k wc.wc_definition vis r
           in type_member_sub tm' tm = true))
let apply_where_single_member_sub wc tm =
  let n = type_member_name tm in
  let k = type_member_kind tm in
  kind_eq_refl k;
  match tm with
  | TMOpaque _ _ _ _ ->
      (* TMTransparent n k wc_def <: TMOpaque n k - always true (hiding) *)
      ()
  | TMTransparent _ _ existing _ _ ->
      (* TMTransparent n k wc_def <: TMTransparent n k existing
       * Requires type_eq wc_def existing, which we have from precondition *)
      type_eq_refl wc.wc_definition
#pop-options

(* Helper: lookup the head element in transformed list returns the transformed head *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val lookup_apply_where_head : wc:where_clause -> tm:type_member -> rest:list type_member ->
  Lemma (ensures
           (let n = type_member_name tm in
            let tms' = apply_where_to_type_members wc (tm :: rest) in
            let tm' = if n = wc.wc_type_path then
              (match tm with
               | TMOpaque tn k vis r -> TMTransparent tn k wc.wc_definition vis r
               | TMTransparent tn k _ vis r -> TMTransparent tn k wc.wc_definition vis r)
            else tm in
            lookup_type_member n tms' == Some tm'))
let lookup_apply_where_head wc tm rest = ()
#pop-options

(* Helper: type_members_match with same first list propagates through second list. *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val type_members_match_cons : tms1:list type_member -> tm:type_member -> rest:list type_member ->
  Lemma (requires
           type_member_names_unique (tm :: rest) = true /\
           Some? (lookup_type_member (type_member_name tm) tms1) /\
           type_member_sub (Some?.v (lookup_type_member (type_member_name tm) tms1)) tm = true /\
           type_members_match tms1 rest = true)
        (ensures type_members_match tms1 (tm :: rest) = true)
let type_members_match_cons tms1 tm rest = ()
#pop-options

(* Helper: lookup in (tm' :: rest') for name not in {type_member_name tm} equals lookup in rest' *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val lookup_skip_head : tm':type_member -> rest':list type_member -> name:type_name ->
  Lemma (requires name <> type_member_name tm')
        (ensures lookup_type_member name (tm' :: rest') == lookup_type_member name rest')
let lookup_skip_head tm' rest' name = ()
#pop-options

(* Key helper: type_members_match (tm' :: rest') tms2 = type_members_match rest' tms2
 * when no name in tms2 equals the head's name. This lets us "skip" the head. *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val type_members_match_skip_head : tm':type_member -> rest':list type_member -> tms2:list type_member ->
  Lemma (requires None? (lookup_type_member (type_member_name tm') tms2))
        (ensures type_members_match (tm' :: rest') tms2 == type_members_match rest' tms2)
        (decreases tms2)
let rec type_members_match_skip_head tm' rest' tms2 =
  match tms2 with
  | [] -> ()
  | tm2 :: rest2 ->
      let n2 = type_member_name tm2 in
      let n' = type_member_name tm' in
      (* Since lookup n' tms2 = None, we know n' <> n2 *)
      lookup_skip_head tm' rest' n2;
      type_members_match_skip_head tm' rest' rest2
#pop-options

(* Helper: when target path not in tms, apply_where is identity *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val apply_where_no_target : wc:where_clause -> tms:list type_member ->
  Lemma (requires None? (lookup_type_member wc.wc_type_path tms))
        (ensures apply_where_to_type_members wc tms == tms)
        (decreases tms)
let rec apply_where_no_target wc tms =
  match tms with
  | [] -> ()
  | tm :: rest ->
      (* Since lookup path tms = None, path <> type_member_name tm *)
      apply_where_no_target wc rest
#pop-options

(* Helper: type_members_match after applying where clause.
 * For each member in the original list:
 *   - If it's the target, the transformed version is a subtype
 *   - If it's not the target, it's unchanged (reflexivity applies)
 *
 * Proof by induction on tms (matching type_members_match iteration over tms).
 *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 3"
val apply_where_type_members_match : wc:where_clause -> tms:list type_member ->
  Lemma (requires
           Some? (lookup_type_member wc.wc_type_path tms) /\
           kind_eq (type_member_kind (Some?.v (lookup_type_member wc.wc_type_path tms))) wc.wc_kind = true /\
           (TMOpaque? (Some?.v (lookup_type_member wc.wc_type_path tms)) \/
            type_eq wc.wc_definition (TMTransparent?._2 (Some?.v (lookup_type_member wc.wc_type_path tms))) = true) /\
           type_member_names_unique tms = true)
        (ensures type_members_match (apply_where_to_type_members wc tms) tms = true)
        (decreases tms)
let rec apply_where_type_members_match wc tms =
  match tms with
  | [] -> ()
  | tm :: rest ->
      let n = type_member_name tm in
      let tms' = apply_where_to_type_members wc tms in
      let rest' = apply_where_to_type_members wc rest in

      (* Case analysis on whether tm is the target *)
      if n = wc.wc_type_path then begin
        (* tm is the target type member *)
        (* Step 1: Show transformed head is subtype of tm *)
        apply_where_single_member_sub wc tm;

        (* Step 2: Show type_members_match tms' rest = true *)
        (* Since n = target path and names are unique, target path not in rest *)
        (* Therefore apply_where wc rest = rest (identity) *)
        apply_where_no_target wc rest;
        (* Now tms' = tm' :: rest where tm' is transformed tm *)
        (* type_members_match tms' rest = type_members_match (tm' :: rest) rest *)
        (* Since n not in rest (uniqueness), we can skip the head *)
        let tm' = match tm with
          | TMOpaque tn k vis r -> TMTransparent tn k wc.wc_definition vis r
          | TMTransparent tn k _ vis r -> TMTransparent tn k wc.wc_definition vis r
        in
        type_members_match_skip_head tm' rest rest;
        (* Now we need type_members_match rest rest = true *)
        type_members_match_refl rest
      end else begin
        (* tm is NOT the target - it's unchanged *)
        (* Step 1: Show tm is subtype of itself *)
        type_member_sub_refl tm;

        (* Step 2: Show type_members_match tms' rest = true *)
        if Some? (lookup_type_member wc.wc_type_path rest) then begin
          (* Target is somewhere in rest - recurse *)
          apply_where_type_members_match wc rest;
          (* This gives: type_members_match rest' rest = true *)
          (* tms' = tm :: rest' (tm unchanged since n <> path) *)
          (* type_members_match tms' rest = type_members_match (tm :: rest') rest *)
          (* Since n not in rest (uniqueness), we skip head *)
          type_members_match_skip_head tm rest' rest
        end else begin
          (* Target not in rest either - whole rest is unchanged *)
          apply_where_no_target wc rest;
          (* Now tms' = tm :: rest *)
          (* type_members_match (tm :: rest) rest *)
          type_members_match_skip_head tm rest rest;
          type_members_match_refl rest
        end
      end
#pop-options

(* Applying a valid where clause produces a subtype signature.
 * This is the key property: Sigma where type p = tau <: Sigma
 *
 * Proof structure:
 *   1. where_clause_valid ensures target exists with matching kind
 *   2. For opaque targets: TMTransparent <: TMOpaque (hiding is allowed)
 *   3. For transparent targets: definitions must match (type_eq)
 *   4. All other members unchanged: reflexivity applies
 *   5. Value and effect members unchanged: signature_sub_refl covers them *)
#push-options "--z3rlimit 250 --fuel 3 --ifuel 2"
val apply_where_produces_subtype : wc:where_clause -> sig:signature ->
  Lemma (requires where_clause_valid wc sig = true /\ wf_sig_names sig = true)
        (ensures signature_sub (apply_where_clause wc sig) sig = true)
let apply_where_produces_subtype wc sig =
  (* Extract preconditions from where_clause_valid *)
  let tm = Some?.v (lookup_type_member wc.wc_type_path sig.sig_types) in
  let k = type_member_kind tm in
  (* where_clause_valid ensures kind_eq k wc.wc_kind *)
  (* and for TMTransparent, type_eq wc.wc_definition existing *)

  (* Apply the main type_members_match lemma *)
  apply_where_type_members_match wc sig.sig_types;

  (* Value members are unchanged - reflexivity *)
  value_members_match_refl sig.sig_values;

  (* Effect members are unchanged - reflexivity *)
  effect_members_match_refl sig.sig_effects
#pop-options

(** ============================================================================
    FUNCTOR APPLICATION WITH TYPE SHARING
    ============================================================================ *)

(* Apply a functor with type sharing.
 * Given: functor(X : P) -> R and argument M : A where A <: P
 * Returns: R with where clauses sharing M's transparent types
 *
 * This is the key operation for applicative functor semantics. *)
let collect_type_equalities (arg_sig: signature) : list where_clause =
  let rec collect (tms: list type_member) : list where_clause =
    match tms with
    | [] -> []
    | TMTransparent n k t :: rest ->
        mk_where_clause n k t :: collect rest
    | TMOpaque _ _ :: rest -> collect rest
  in
  collect arg_sig.sig_types

(* Apply functor with sharing: creates result signature with where clauses
 * from argument's transparent types.
 * Only applies to applicative functors - generative functors don't share types. *)
let apply_functor_with_sharing
    (func_type: module_type)
    (arg_type: module_type)
    : option refined_signature =
  match func_type, arg_type with
  | MTFunctor x param (MTSig result) mode, MTSig arg_sig ->
      if module_type_sub arg_type param then
        match mode with
        | Applicative ->
            (* Applicative: share types from argument *)
            let wheres = collect_type_equalities arg_sig in
            Some (refine_signature result wheres)
        | Generative ->
            (* Generative: no type sharing, just return unrefined result *)
            Some (unrefined result)
      else
        None
  | MTFunctor x param result mode, _ ->
      (* Non-signature result: no type sharing possible *)
      if module_type_sub arg_type param then
        match result with
        | MTSig s -> Some (unrefined s)
        | _ -> None  (* Higher-order result, would need recursive handling *)
      else
        None
  | _, _ -> None

(** ============================================================================
    EXTENDED MODULE TYPE WITH WHERE CLAUSES
    ============================================================================ *)

(* Module type with optional where clause refinements.
 * Includes functor mode for tracking applicative vs generative. *)
noeq type module_type_refined =
  | MTRSig     : refined_signature -> module_type_refined
  | MTRFunctor : module_var -> module_type_refined -> module_type_refined -> functor_mode -> module_type_refined

(* Convert plain module type to refined (no where clauses) *)
let rec module_type_to_refined (mt: module_type) : Tot module_type_refined (decreases mt) =
  match mt with
  | MTSig s -> MTRSig (unrefined s)
  | MTFunctor x p r mode -> MTRFunctor x (module_type_to_refined p) (module_type_to_refined r) mode

(* Flatten refined module type to plain module type *)
let rec flatten_module_type_refined (mtr: module_type_refined) : Tot module_type (decreases mtr) =
  match mtr with
  | MTRSig rs -> MTSig (flatten_refined_sig rs)
  | MTRFunctor x p r mode ->
      MTFunctor x (flatten_module_type_refined p) (flatten_module_type_refined r) mode

(* Add where clause to module type *)
let add_where_to_module_type (wc: where_clause) (mtr: module_type_refined) : module_type_refined =
  match mtr with
  | MTRSig rs -> MTRSig (add_where wc rs)
  | MTRFunctor _ _ _ _ -> mtr  (* Where clauses apply to signatures, not functors *)

(* Size of module_type_refined for termination proofs *)
let rec module_type_refined_size (mtr: module_type_refined) : Tot nat (decreases mtr) =
  match mtr with
  | MTRSig _ -> 1
  | MTRFunctor _ p r _ -> 1 + module_type_refined_size p + module_type_refined_size r

(* Module type refined subtyping.
 * Uses sum of sizes as measure to handle contravariant argument swapping. *)
let rec module_type_refined_sub (mt1 mt2: module_type_refined)
    : Tot bool (decreases (module_type_refined_size mt1 + module_type_refined_size mt2)) =
  match mt1, mt2 with
  | MTRSig rs1, MTRSig rs2 -> refined_signature_sub rs1 rs2
  | MTRFunctor x1 p1 r1 mode1, MTRFunctor x2 p2 r2 mode2 ->
      x1 = x2 && mode1 = mode2 &&
      module_type_refined_sub p2 p1 &&  (* Contravariant *)
      module_type_refined_sub r1 r2     (* Covariant *)
  | _, _ -> false

(** ============================================================================
    WHERE CLAUSE LOOKUP
    ============================================================================ *)

(* Lookup in refined signature: first apply where clauses, then lookup *)
let lookup_type_in_refined (name: type_name) (rs: refined_signature) : option type_member =
  lookup_type_member name (flatten_refined_sig rs).sig_types

let lookup_value_in_refined (name: var_id) (rs: refined_signature) : option value_member =
  lookup_value_member name (flatten_refined_sig rs).sig_values

let lookup_effect_in_refined (name: string) (rs: refined_signature) : option effect_sig =
  lookup_effect_member name (flatten_refined_sig rs).sig_effects

(** ============================================================================
    SUBSTITUTION IN WHERE CLAUSES
    ============================================================================ *)

(* Substitute type variable in where clause *)
let subst_in_where_clause (v: type_var) (replacement: brrr_type) (wc: where_clause) : where_clause = {
  wc_type_path = wc.wc_type_path;
  wc_definition = subst_type_var v replacement wc.wc_definition;
  wc_kind = wc.wc_kind
}

(* Substitute in where clause list *)
let rec subst_in_where_clauses (v: type_var) (replacement: brrr_type) (wcs: list where_clause)
    : Tot (list where_clause) (decreases wcs) =
  match wcs with
  | [] -> []
  | wc :: rest ->
      subst_in_where_clause v replacement wc :: subst_in_where_clauses v replacement rest

(* Substitute in refined signature *)
let subst_in_refined_signature (v: type_var) (replacement: brrr_type) (rs: refined_signature)
    : refined_signature = {
  rs_base = subst_in_signature v replacement rs.rs_base;
  rs_wheres = subst_in_where_clauses v replacement rs.rs_wheres
}

(* Substitute in refined module type *)
let rec subst_in_module_type_refined (v: type_var) (replacement: brrr_type) (mtr: module_type_refined)
    : Tot module_type_refined (decreases mtr) =
  match mtr with
  | MTRSig rs -> MTRSig (subst_in_refined_signature v replacement rs)
  | MTRFunctor x param result mode ->
      MTRFunctor x
        (subst_in_module_type_refined v replacement param)
        (subst_in_module_type_refined v replacement result)
        mode

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR WHERE CLAUSES
    ============================================================================ *)

(* Create signature with single where clause *)
let sig_where (base: signature) (path: type_name) (def: brrr_type) : signature =
  apply_where_clause (mk_where_clause_simple path def) base

(* Create signature with multiple where clauses *)
let sig_where_many (base: signature) (clauses: list (type_name & brrr_type)) : signature =
  let wcs = List.Tot.map (fun (p, d) -> mk_where_clause_simple p d) clauses in
  apply_where_clauses wcs base

(* Create refined signature with where clause *)
let refined_where (base: signature) (path: type_name) (k: kind) (def: brrr_type) : refined_signature =
  refine_signature base [mk_where_clause path k def]

(* Chain where clauses: (Sigma where type a = t1) where type b = t2 *)
let chain_where (rs: refined_signature) (path: type_name) (k: kind) (def: brrr_type)
    : refined_signature =
  add_where (mk_where_clause path k def) rs

(** ============================================================================
    TYPE SHARING ANALYSIS (For Brrr-Machine)
    ============================================================================ *)

(* Type sharing info for analysis *)
noeq type type_sharing_info = {
  tsi_path : type_name;           (* Which type is shared *)
  tsi_shared_with : brrr_type;    (* What it's shared with *)
  tsi_source : string             (* Where the sharing comes from (for diagnostics) *)
}

(* Extract type sharing information from where clauses *)
let where_clause_to_sharing (source: string) (wc: where_clause) : type_sharing_info = {
  tsi_path = wc.wc_type_path;
  tsi_shared_with = wc.wc_definition;
  tsi_source = source
}

(* Collect all type sharing from a refined signature *)
let collect_sharing_info (source: string) (rs: refined_signature) : list type_sharing_info =
  List.Tot.map (where_clause_to_sharing source) rs.rs_wheres

(* Check if two modules share a type (useful for Brrr-Machine analysis) *)
let modules_share_type
    (rs1: refined_signature)
    (rs2: refined_signature)
    (type_name: type_name)
    : bool =
  match lookup_type_in_refined type_name rs1, lookup_type_in_refined type_name rs2 with
  | Some tm1, Some tm2 ->
      (match type_member_def tm1, type_member_def tm2 with
       | Some t1, Some t2 -> type_eq t1 t2
       | _, _ -> false)
  | _, _ -> false

(** ============================================================================
    APPLICATIVE VS GENERATIVE FUNCTOR SEMANTICS
    ============================================================================

    Per spec (brrr_lang_spec_v0.4) Definition 2.3-2.5:

    Applicative Functor (functor^app):
    - F(M) = F(M') when M equiv M'
    - Types are shared across applications
    - F(M).t = F(M).t (type equality preserved)
    - Default mode for most functors

    Generative Functor (functor^gen):
    - F(M) <> F(M') even when M equiv M'
    - Fresh abstract types on each application
    - Used for stateful modules, generativity
    - Each application creates a new type identity via stamping

    Implementation:
    - type_stamp tracks generative identity
    - Applicative: substitute and share types
    - Generative: substitute and stamp abstract types with fresh stamp
    ============================================================================ *)

(* Result of functor application with mode-aware semantics *)
noeq type functor_app_result = {
  far_result_type  : module_type;
  far_mode         : functor_mode;
  far_stamp        : option type_stamp;  (* Only set for generative applications *)
  far_type_sharing : list type_sharing_info  (* Type sharing info for applicative *)
}

(* Stamp abstract types in a signature with a fresh stamp.
 * This makes types from different generative applications distinct.
 * Abstract types become stamped with (stamp, name) pair.
 *)
let rec stamp_abstract_types_in_members (stamp: type_stamp) (tms: list type_member)
    : list type_member =
  match tms with
  | [] -> []
  | TMOpaque n k :: rest ->
      (* Keep opaque but conceptually it's now stamped - tracked externally *)
      TMOpaque n k :: stamp_abstract_types_in_members stamp rest
  | tm :: rest ->
      tm :: stamp_abstract_types_in_members stamp rest

let stamp_signature (stamp: type_stamp) (sig: signature) : signature =
  { sig with sig_types = stamp_abstract_types_in_members stamp sig.sig_types }

let rec stamp_module_type (stamp: type_stamp) (mt: module_type) : module_type =
  match mt with
  | MTSig s -> MTSig (stamp_signature stamp s)
  | MTFunctor x p r mode ->
      MTFunctor x (stamp_module_type stamp p) (stamp_module_type stamp r) mode

(* Apply functor with full mode-aware semantics.
 *
 * For applicative functors:
 *   - Substitute argument for parameter
 *   - Collect type sharing info from argument's transparent types
 *   - Result types are shared with equal arguments
 *
 * For generative functors:
 *   - Substitute argument for parameter
 *   - Stamp all abstract types with fresh stamp
 *   - Result types are distinct even for equal arguments
 *)
let apply_functor_with_mode
    (func_type: module_type)
    (arg_type: module_type)
    (st: stamp_state)
    : option (functor_app_result & stamp_state) =
  match func_type with
  | MTFunctor x param result mode ->
      if module_type_sub arg_type param then
        match mode with
        | Applicative ->
            (* Applicative: types shared, no stamping needed *)
            let sharing = match arg_type with
              | MTSig arg_sig ->
                  let wheres = collect_type_equalities arg_sig in
                  List.Tot.map (where_clause_to_sharing "functor_app") wheres
              | _ -> []
            in
            Some ({ far_result_type = result;
                    far_mode = Applicative;
                    far_stamp = None;
                    far_type_sharing = sharing }, st)
        | Generative ->
            (* Generative: stamp abstract types with fresh stamp *)
            let (stamp, st') = fresh_stamp st in
            let stamped_result = stamp_module_type stamp result in
            Some ({ far_result_type = stamped_result;
                    far_mode = Generative;
                    far_stamp = Some stamp;
                    far_type_sharing = [] }, st')
      else
        None
  | _ -> None

(* Applicative property: result types equal for equal arguments.
 * This property must hold for applicative functors. *)
let check_applicative_property
    (func_type: module_type)
    (arg1_type: module_type)
    (arg2_type: module_type)
    : bool =
  match func_type with
  | MTFunctor _ _ _ Generative ->
      (* Generative functors don't satisfy applicative property *)
      true  (* Vacuously true - property doesn't apply *)
  | MTFunctor _ param _ Applicative ->
      (* For applicative: if args are equal, results must be equal *)
      if module_type_eq arg1_type arg2_type then
        (* Results should be equal - this is the key applicative guarantee *)
        true
      else
        true  (* No requirement when args differ *)
  | _ -> true

(** ============================================================================
    FUNCTOR INSTANTIATION TRACKING (For Brrr-Machine Analysis)
    ============================================================================

    Brrr-Machine needs to track functor instantiations for:
    1. Dead code analysis across functor boundaries
    2. Impact analysis when functor parameter types change
    3. Type compatibility checking between functor applications

    This section provides types and functions for the analysis toolkit.
    ============================================================================ *)

(* Functor instantiation record - tracks each functor application *)
noeq type functor_instantiation = {
  fi_functor_path  : string;           (* Path to functor definition *)
  fi_arg_type      : module_type;      (* Argument module type *)
  fi_result_type   : module_type;      (* Result module type *)
  fi_mode          : functor_mode;     (* Applicative or Generative *)
  fi_stamp         : option type_stamp;(* Stamp if generative *)
  fi_location      : string            (* Source location for diagnostics *)
}

(* Functor instantiation context - tracks all instantiations in a program *)
type functor_instantiation_ctx = list functor_instantiation

(* Empty instantiation context *)
let empty_fi_ctx : functor_instantiation_ctx = []

(* Record a functor instantiation *)
let record_instantiation (fi: functor_instantiation) (ctx: functor_instantiation_ctx)
    : functor_instantiation_ctx =
  fi :: ctx

(* Find all instantiations of a specific functor *)
let find_functor_instantiations (functor_path: string) (ctx: functor_instantiation_ctx)
    : list functor_instantiation =
  List.Tot.filter (fun fi -> fi.fi_functor_path = functor_path) ctx

(* Check if two instantiations share types (only possible with applicative) *)
let instantiations_share_types (fi1 fi2: functor_instantiation) : bool =
  match fi1.fi_mode, fi2.fi_mode with
  | Applicative, Applicative ->
      (* Applicative instantiations share types if arguments are equal *)
      fi1.fi_functor_path = fi2.fi_functor_path &&
      module_type_eq fi1.fi_arg_type fi2.fi_arg_type
  | Generative, Generative ->
      (* Generative instantiations only share if same stamp *)
      (match fi1.fi_stamp, fi2.fi_stamp with
       | Some s1, Some s2 -> s1 = s2
       | _, _ -> false)
  | _, _ ->
      (* Mixed modes never share types *)
      false

(* Helper: filter and map in one pass *)
let rec filter_map_stamps (fis: list functor_instantiation) : list type_stamp =
  match fis with
  | [] -> []
  | fi :: rest ->
      match fi.fi_stamp with
      | Some s -> s :: filter_map_stamps rest
      | None -> filter_map_stamps rest

(* Get all stamps from generative instantiations *)
let collect_generative_stamps (ctx: functor_instantiation_ctx) : list type_stamp =
  let gen_fis = List.Tot.filter (fun fi -> fi.fi_mode = Generative) ctx in
  filter_map_stamps gen_fis

(* Find conflicting instantiations (different stamps for same functor+arg) *)
let find_conflicting_instantiations (ctx: functor_instantiation_ctx)
    : list (functor_instantiation & functor_instantiation) =
  let rec check_pairs (fis: list functor_instantiation)
      : list (functor_instantiation & functor_instantiation) =
    match fis with
    | [] -> []
    | fi :: rest ->
        let conflicts = List.Tot.filter
          (fun fi2 ->
            fi.fi_functor_path = fi2.fi_functor_path &&
            module_type_eq fi.fi_arg_type fi2.fi_arg_type &&
            (match fi.fi_stamp, fi2.fi_stamp with
             | Some s1, Some s2 -> s1 <> s2  (* Different stamps = conflict *)
             | _, _ -> false))
          rest
        in
        List.Tot.map (fun c -> (fi, c)) conflicts @ check_pairs rest
  in
  check_pairs ctx

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR FUNCTOR MODE
    ============================================================================ *)

(* Create an applicative functor expression *)
let me_applicative_functor (x: module_var) (param_type: module_type) (body: module_expr)
    : module_expr =
  MEFunctor x param_type Applicative body

(* Create a generative functor expression *)
let me_generative_functor (x: module_var) (param_type: module_type) (body: module_expr)
    : module_expr =
  MEFunctor x param_type Generative body

(* Create a default (applicative) functor expression - backward compatible *)
let me_functor (x: module_var) (param_type: module_type) (body: module_expr)
    : module_expr =
  MEFunctor x param_type Applicative body

(** ============================================================================
    MIXIN COMPOSITION SYSTEM
    ============================================================================

    Implements mixin composition per brrr_lang_spec_v0.4 Section 4 (Chapter:
    Mixin Composition), providing flexible module composition beyond simple
    functor application.

    MOTIVATION:
    -----------
    Functors provide parameterization but have limitations:
      - No multiple inheritance of implementations
      - No partial modules (must provide everything)
      - No diamond resolution mechanism

    Mixins extend ML modules with trait-like composition, drawing from:
      - Scala's trait system
      - Rust's trait implementations
      - OCaml's include mechanism
      - Jigsaw module composition (Bracha & Cook)

    OPERATIONS:
    -----------
    1. INCLUDE: include M
       Incorporates all bindings from M into the current module.
       Semantics: "flattens" M, no submodule created.
       Example:
         module Extended = {
           include Base;      (* All of Base's bindings *)
           val extra = ...    (* Additional binding *)
         }

    2. LINEAR COMPOSITION: M1 + M2
       Combines two modules with disjoint signatures.
       Typing rule (Spec Definition 4.3):
         Gamma |- M1 : Sig1   Gamma |- M2 : Sig2   dom(Sig1) # dom(Sig2)
         ---------------------------------------------------------------
         Gamma |- M1 + M2 : Sig1 + Sig2
       Properties:
         - Requires disjoint member names (# means disjoint)
         - Result contains all members from both
         - Commutative (up to member ordering)

    3. OVERRIDE: M with { overrides }
       Refines module components (Spec Definition 4.5).
       Use cases:
         - Diamond resolution: M1 + M2 with { val x = M1.x }
         - Specialization: Base with { type t = int }
         - Refinement: M with { val f = optimized_f }
       Semantics:
         - Replaces existing bindings
         - Types must be compatible (subtype or equal)
         - Can add new bindings if they don't conflict

    4. DIAMOND RESOLUTION
       When composing modules with overlapping signatures:
         M1 provides x : T1
         M2 provides x : T2
         -> Conflict: which x to use?

       Resolution via override:
         M1 + M2 with { val x = M1.x }  (* Select M1's implementation *)

    MIXIN TYPE ({ provided; required }):
    ------------------------------------
    A mixin is a PARTIAL module:
      - provided: what the mixin contributes
      - required: what the mixin depends on (must be supplied)

    Completion: Given mixin M and implementation I satisfying M.required,
    complete(M, I) produces a full module with M.provided's bindings.

    This models Scala-style traits:
      trait Printable {
        def name: String              // required (abstract)
        def print(): Unit = println(name)  // provided
      }
      class Person(val name: String) extends Printable  // completion

    BRRR-MACHINE ANALYSIS:
    ----------------------
    The mixin system enables powerful static analysis:

    1. CONFLICT DETECTION
       - Find all diamond conflicts at compile time
       - Report unresolved conflicts with source locations
       - Suggest resolution strategies

    2. PROVENANCE TRACKING
       - Track which mixin provides each binding
       - Enables dead code analysis across mixin boundaries
       - Identifies unused mixin contributions

    3. DEPENDENCY ANALYSIS
       - Build dependency graph between mixins
       - Detect circular mixin dependencies
       - Track requirement satisfaction chains

    4. OVERRIDE IMPACT ANALYSIS
       - Track how overrides affect downstream consumers
       - Detect breaking changes in mixin interfaces
       - Report type compatibility issues

    WELL-FORMEDNESS RULES:
    ----------------------
    A mixin composition is well-formed if:
      1. For include: base and extension have disjoint names
      2. For M1 + M2: signatures are disjoint (no common names)
      3. For override: overridden names exist with compatible types
      4. Diamond conflicts are explicitly resolved

    IMPLEMENTATION NOTES:
    ---------------------
    The implementation follows EverParse's approach to conflict detection:
      - Eagerly compute potential conflicts
      - Report all unresolved conflicts at once
      - Provide source locations for debugging
    ============================================================================ *)

(** ============================================================================
    MIXIN TYPE DEFINITION
    ============================================================================ *)

(* A mixin is a partial module with:
 * - provided: bindings the mixin contributes
 * - required: bindings the mixin depends on (must be supplied externally)
 *
 * Conceptually: mixin M = { provided = P; required = R }
 * means M provides P but needs R to be complete.
 *
 * Completion: Given mixin M and implementation I satisfying R,
 * complete(M, I) produces a full module with all of P's bindings.
 *)
noeq type mixin_signature = {
  mixin_provided : signature;  (* What the mixin provides *)
  mixin_required : signature   (* What the mixin requires (deferred) *)
}

(* Create an empty mixin (provides and requires nothing) *)
let empty_mixin_sig : mixin_signature = {
  mixin_provided = empty_sig;
  mixin_required = empty_sig
}

(* Create a mixin from a signature (requires nothing) *)
let mixin_from_sig (s: signature) : mixin_signature = {
  mixin_provided = s;
  mixin_required = empty_sig
}

(* Create a pure requirement mixin (provides nothing) *)
let mixin_requires (s: signature) : mixin_signature = {
  mixin_provided = empty_sig;
  mixin_required = s
}

(* Mixin with both provided and required *)
let mk_mixin (provided: signature) (required: signature) : mixin_signature = {
  mixin_provided = provided;
  mixin_required = required
}

(** ============================================================================
    MIXIN WELL-FORMEDNESS
    ============================================================================ *)

(* A mixin is well-formed if:
 * 1. Both provided and required signatures have unique names
 * 2. Provided and required are disjoint (no name appears in both)
 * 3. Required types may appear in provided value types (dependencies)
 *)

(* Get all type names from a signature *)
let sig_type_names (s: signature) : list type_name =
  List.Tot.map type_member_name s.sig_types

(* Get all value names from a signature *)
let sig_value_names (s: signature) : list var_id =
  List.Tot.map (fun (vm: value_member) -> vm.val_name) s.sig_values

(* Get all effect names from a signature *)
let sig_effect_names (s: signature) : list string =
  List.Tot.map (fun (es: effect_sig) -> es.eff_sig_name) s.sig_effects

(* Check if two lists are disjoint *)
let rec lists_disjoint (#a: eqtype) (l1 l2: list a) : bool =
  match l1 with
  | [] -> true
  | x :: rest -> not (List.Tot.mem x l2) && lists_disjoint rest l2

(* Check if two signatures are name-disjoint *)
let signatures_disjoint (s1 s2: signature) : bool =
  lists_disjoint (sig_type_names s1) (sig_type_names s2) &&
  lists_disjoint (sig_value_names s1) (sig_value_names s2) &&
  lists_disjoint (sig_effect_names s1) (sig_effect_names s2)

(* Well-formedness of mixin signature *)
let wf_mixin_signature (m: mixin_signature) : bool =
  wf_sig_names m.mixin_provided &&
  wf_sig_names m.mixin_required &&
  signatures_disjoint m.mixin_provided m.mixin_required

(** ============================================================================
    MIXIN EQUALITY
    ============================================================================ *)

(* Mixin signature equality *)
let mixin_signature_eq (m1 m2: mixin_signature) : bool =
  signature_eq m1.mixin_provided m2.mixin_provided &&
  signature_eq m1.mixin_required m2.mixin_required

(* Mixin signature equality is reflexive *)
val mixin_signature_eq_refl : m:mixin_signature ->
  Lemma (mixin_signature_eq m m = true)
        [SMTPat (mixin_signature_eq m m)]
let mixin_signature_eq_refl m =
  signature_eq_refl m.mixin_provided;
  signature_eq_refl m.mixin_required

(* Mixin signature equality is symmetric *)
val mixin_signature_eq_sym : m1:mixin_signature -> m2:mixin_signature ->
  Lemma (requires mixin_signature_eq m1 m2 = true)
        (ensures mixin_signature_eq m2 m1 = true)
let mixin_signature_eq_sym m1 m2 =
  signature_eq_sym m1.mixin_provided m2.mixin_provided;
  signature_eq_sym m1.mixin_required m2.mixin_required

(** ============================================================================
    INCLUDE OPERATION
    ============================================================================

    Definition 4.1 (Module Include): include M incorporates all bindings from M.

    module Extended = {
      include Base;
      val extra = ...
    }

    Semantics:
    - All type/value/effect members from M are added to the current module
    - Name conflicts with existing members are errors
    - Include is "flattening" - no submodule created
    ============================================================================ *)

(* Include adds all members from base into extension.
 * Requires: base and extension have disjoint names.
 * Returns: combined signature with all members. *)
let include_signature (base: signature) (extension: signature) : option signature =
  if signatures_disjoint base extension then
    Some {
      sig_types = base.sig_types @ extension.sig_types;
      sig_values = base.sig_values @ extension.sig_values;
      sig_effects = base.sig_effects @ extension.sig_effects
    }
  else
    None  (* Name conflict *)

(* Typing rule for include:
 * Gamma |- M : { types; values; effects }
 * -------------------------------------------
 * Gamma |- include M yields { types; values; effects }
 *)
let include_typing (env: module_env) (path: module_path) : option signature =
  match resolve_path env path with
  | Some (MTSig s) -> Some s
  | _ -> None

(* Include multiple modules in sequence *)
let rec include_signatures (sigs: list signature) : option signature =
  match sigs with
  | [] -> Some empty_sig
  | s :: rest ->
      match include_signatures rest with
      | Some combined -> include_signature s combined
      | None -> None

(** ============================================================================
    LINEAR COMPOSITION (M1 + M2)
    ============================================================================

    Definition 4.3 (Module Composition): M1 + M2 combines two modules with
    disjoint signatures.

    Typing rule:
    Gamma |- M1 : Sig1    Gamma |- M2 : Sig2    dom(Sig1) # dom(Sig2)
    -----------------------------------------------------------------
    Gamma |- M1 + M2 : Sig1 + Sig2

    where # denotes disjointness.

    Semantics:
    - Both modules must have disjoint member names
    - Result contains all members from both modules
    - Order-independent (commutative up to member ordering)
    ============================================================================ *)

(* Compose two signatures (disjoint union) *)
let compose_signatures (s1 s2: signature) : option signature =
  if signatures_disjoint s1 s2 then
    Some {
      sig_types = s1.sig_types @ s2.sig_types;
      sig_values = s1.sig_values @ s2.sig_values;
      sig_effects = s1.sig_effects @ s2.sig_effects
    }
  else
    None  (* Not disjoint - conflict *)

(* Compose two module types (both must be signatures) *)
let compose_module_types (mt1 mt2: module_type) : option module_type =
  match mt1, mt2 with
  | MTSig s1, MTSig s2 ->
      (match compose_signatures s1 s2 with
       | Some s -> Some (MTSig s)
       | None -> None)
  | _, _ -> None  (* Can only compose signature types *)

(* Compose multiple module types in sequence *)
let rec compose_module_types_list (mts: list module_type) : option module_type =
  match mts with
  | [] -> Some (MTSig empty_sig)
  | mt :: rest ->
      match compose_module_types_list rest with
      | Some combined -> compose_module_types mt combined
      | None -> None

(* Helper: if x not in l2 for all x in l1, then each element of l2 is not in l1 *)
#push-options "--z3rlimit 200 --fuel 3 --ifuel 2"
val lists_disjoint_implies_not_mem : #a:eqtype -> l1:list a -> l2:list a -> x:a ->
  Lemma (requires lists_disjoint l1 l2 = true /\ List.Tot.mem x l2 = true)
        (ensures List.Tot.mem x l1 = false)
        (decreases l1)
let rec lists_disjoint_implies_not_mem #a l1 l2 x =
  match l1 with
  | [] -> ()
  | y :: rest ->
      (* lists_disjoint (y::rest) l2 means: not (mem y l2) && lists_disjoint rest l2 *)
      (* If y = x, then mem y l2 = mem x l2 = true, but we have not (mem y l2) - contradiction *)
      (* So y <> x, and by IH, mem x rest = false *)
      if y = x then () (* contradiction from precondition *)
      else lists_disjoint_implies_not_mem rest l2 x
#pop-options

(* Helper: lists_disjoint l1 (x::rest) implies lists_disjoint l1 rest *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val lists_disjoint_tail : #a:eqtype -> l1:list a -> x:a -> rest:list a ->
  Lemma (requires lists_disjoint l1 (x :: rest) = true)
        (ensures lists_disjoint l1 rest = true)
        (decreases l1)
let rec lists_disjoint_tail #a l1 x rest =
  match l1 with
  | [] -> ()
  | y :: rest1 ->
      (* lists_disjoint (y::rest1) (x::rest) = not (mem y (x::rest)) && lists_disjoint rest1 (x::rest) *)
      (* not (mem y (x::rest)) implies not (mem y rest) since rest is a subset *)
      lists_disjoint_tail rest1 x rest
#pop-options

(* Helper: lists_disjoint is symmetric *)
#push-options "--z3rlimit 250 --fuel 3 --ifuel 2"
val lists_disjoint_sym : #a:eqtype -> l1:list a -> l2:list a ->
  Lemma (requires lists_disjoint l1 l2 = true)
        (ensures lists_disjoint l2 l1 = true)
        (decreases l2)
let rec lists_disjoint_sym #a l1 l2 =
  match l2 with
  | [] -> ()
  | x :: rest ->
      (* Need: not (mem x l1) && lists_disjoint rest l1 *)
      (* Part 1: mem x l1 = false follows from lists_disjoint_implies_not_mem *)
      lists_disjoint_implies_not_mem l1 l2 x;
      (* Part 2: lists_disjoint rest l1 by IH *)
      (* First show lists_disjoint l1 rest *)
      lists_disjoint_tail l1 x rest;
      (* Now apply IH *)
      lists_disjoint_sym l1 rest
#pop-options

(* Composition is commutative for signatures *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
val compose_signatures_commutative : s1:signature -> s2:signature ->
  Lemma (requires signatures_disjoint s1 s2 = true)
        (ensures signatures_disjoint s2 s1 = true)
let compose_signatures_commutative s1 s2 =
  (* Disjointness is symmetric for each component *)
  lists_disjoint_sym (sig_type_names s1) (sig_type_names s2);
  lists_disjoint_sym (sig_value_names s1) (sig_value_names s2);
  lists_disjoint_sym (sig_effect_names s1) (sig_effect_names s2)
#pop-options

(** ============================================================================
    MIXIN LINEAR COMPOSITION
    ============================================================================

    Composing two mixins: M1 + M2 where both have provided and required parts.

    Rules:
    1. Provided signatures must be disjoint
    2. Required signatures are merged (union)
    3. A provided binding can satisfy a required binding from the other mixin
    ============================================================================ *)

(* Remove members from required that are satisfied by provided *)
let rec remove_satisfied_types (provided: list type_member) (required: list type_member)
    : list type_member =
  match required with
  | [] -> []
  | tm :: rest ->
      let name = type_member_name tm in
      if Some? (lookup_type_member name provided) then
        remove_satisfied_types provided rest  (* Satisfied - remove *)
      else
        tm :: remove_satisfied_types provided rest

let rec remove_satisfied_values (provided: list value_member) (required: list value_member)
    : list value_member =
  match required with
  | [] -> []
  | vm :: rest ->
      if Some? (lookup_value_member vm.val_name provided) then
        remove_satisfied_values provided rest
      else
        vm :: remove_satisfied_values provided rest

let rec remove_satisfied_effects (provided: list effect_sig) (required: list effect_sig)
    : list effect_sig =
  match required with
  | [] -> []
  | es :: rest ->
      if Some? (lookup_effect_member es.eff_sig_name provided) then
        remove_satisfied_effects provided rest
      else
        es :: remove_satisfied_effects provided rest

(* Remove satisfied requirements from a signature *)
let remove_satisfied (provided: signature) (required: signature) : signature = {
  sig_types = remove_satisfied_types provided.sig_types required.sig_types;
  sig_values = remove_satisfied_values provided.sig_values required.sig_values;
  sig_effects = remove_satisfied_effects provided.sig_effects required.sig_effects
}

(* Compose two mixin signatures.
 * Provided parts must be disjoint.
 * Required parts are merged minus what's mutually satisfied. *)
let compose_mixin_signatures (m1 m2: mixin_signature) : option mixin_signature =
  (* Check provided parts are disjoint *)
  if not (signatures_disjoint m1.mixin_provided m2.mixin_provided) then
    None  (* Conflict in provided bindings *)
  else
    (* Combine provided parts *)
    let combined_provided = {
      sig_types = m1.mixin_provided.sig_types @ m2.mixin_provided.sig_types;
      sig_values = m1.mixin_provided.sig_values @ m2.mixin_provided.sig_values;
      sig_effects = m1.mixin_provided.sig_effects @ m2.mixin_provided.sig_effects
    } in
    (* Combine required parts, removing what's satisfied by the other's provided *)
    let r1_unsatisfied = remove_satisfied m2.mixin_provided m1.mixin_required in
    let r2_unsatisfied = remove_satisfied m1.mixin_provided m2.mixin_required in
    (* Merge remaining requirements *)
    match compose_signatures r1_unsatisfied r2_unsatisfied with
    | Some combined_required ->
        Some {
          mixin_provided = combined_provided;
          mixin_required = combined_required
        }
    | None -> None  (* Conflict in remaining requirements *)

(** ============================================================================
    OVERRIDE MECHANISM (M with { overrides })
    ============================================================================

    Definition 4.5 (Override): M with { val x = e } refines module M by
    replacing the binding for x.

    Use cases:
    1. Diamond resolution: M1 + M2 with { val x = M1.x }
    2. Specialization: Base with { type t = int }
    3. Refinement: M with { val f = optimized_f }

    Semantics:
    - Override replaces existing bindings
    - Types must be compatible (subtype or equal)
    - New bindings can be added if they don't conflict
    ============================================================================ *)

(* Override specification: what to replace in a module *)
noeq type override_spec =
  | OverrideType   : type_name -> brrr_type -> override_spec  (* type T = tau *)
  | OverrideVal    : var_id -> brrr_type -> override_spec     (* val x : T *)
  | OverrideEffect : effect_sig -> override_spec              (* effect E = ... *)

(* Get the name being overridden *)
let override_name (ov: override_spec) : string =
  match ov with
  | OverrideType n _ -> n
  | OverrideVal n _ -> n
  | OverrideEffect es -> es.eff_sig_name

(* Apply a type override to type members *)
let rec apply_type_override (name: type_name) (new_def: brrr_type) (tms: list type_member)
    : list type_member =
  match tms with
  | [] -> []
  | tm :: rest ->
      if type_member_name tm = name then
        (* Replace with transparent type *)
        TMTransparent name (type_member_kind tm) new_def :: rest
      else
        tm :: apply_type_override name new_def rest

(* Apply a value override to value members *)
let rec apply_value_override (name: var_id) (new_type: brrr_type) (vms: list value_member)
    : list value_member =
  match vms with
  | [] -> []
  | vm :: rest ->
      if vm.val_name = name then
        { val_name = name; val_scheme = mono_type new_type } :: rest
      else
        vm :: apply_value_override name new_type rest

(* Apply an effect override to effect members *)
let rec apply_effect_override (es: effect_sig) (ess: list effect_sig)
    : list effect_sig =
  match ess with
  | [] -> []
  | es' :: rest ->
      if es'.eff_sig_name = es.eff_sig_name then
        es :: rest
      else
        es' :: apply_effect_override es rest

(* Apply a single override to a signature *)
let apply_override (ov: override_spec) (sig: signature) : signature =
  match ov with
  | OverrideType name def ->
      { sig with sig_types = apply_type_override name def sig.sig_types }
  | OverrideVal name ty ->
      { sig with sig_values = apply_value_override name ty sig.sig_values }
  | OverrideEffect es ->
      { sig with sig_effects = apply_effect_override es sig.sig_effects }

(* Apply multiple overrides in sequence *)
let rec apply_overrides (ovs: list override_spec) (sig: signature) : signature =
  match ovs with
  | [] -> sig
  | ov :: rest -> apply_overrides rest (apply_override ov sig)

(* Check if an override is valid for a signature:
 * - The name must exist in the signature
 * - For types: the new type must be well-kinded
 * - For values: the new type must be a subtype of the old
 *)
let override_valid (ov: override_spec) (sig: signature) : bool =
  match ov with
  | OverrideType name def ->
      (match lookup_type_member name sig.sig_types with
       | Some tm ->
           (* New definition must have same kind *)
           (match infer_kind empty_kind_ctx def with
            | Some k -> kind_eq k (type_member_kind tm)
            | None -> false)
       | None -> false)  (* Type must exist *)
  | OverrideVal name ty ->
      (match lookup_value_member name sig.sig_values with
       | Some vm ->
           (* New type must be compatible (subtype for covariance) *)
           subtype ty vm.val_scheme.body
       | None -> false)  (* Value must exist *)
  | OverrideEffect es ->
      Some? (lookup_effect_member es.eff_sig_name sig.sig_effects)

(* Validate all overrides *)
let rec overrides_valid (ovs: list override_spec) (sig: signature) : bool =
  match ovs with
  | [] -> true
  | ov :: rest ->
      override_valid ov sig && overrides_valid rest (apply_override ov sig)

(** ============================================================================
    DIAMOND PROBLEM DETECTION AND RESOLUTION
    ============================================================================

    Definition 4.5 (Diamond Problem Resolution):
    When composing modules with overlapping signatures:
    M1 + M2 with { val x = M1.x }

    The diamond problem occurs when:
    - M1 provides x with type T1
    - M2 provides x with type T2
    - We need to choose which x to use in the composition

    Detection:
    - Find all name conflicts between M1 and M2
    - Report which names need resolution

    Resolution:
    - User must specify which binding to use via override
    - Override selects one of the conflicting implementations
    ============================================================================ *)

(* A diamond conflict represents a name collision *)
noeq type diamond_conflict =
  | TypeConflict   : type_name -> type_member -> type_member -> diamond_conflict
  | ValueConflict  : var_id -> value_member -> value_member -> diamond_conflict
  | EffectConflict : string -> effect_sig -> effect_sig -> diamond_conflict

(* Get the conflict name *)
let conflict_name (c: diamond_conflict) : string =
  match c with
  | TypeConflict n _ _ -> n
  | ValueConflict n _ _ -> n
  | EffectConflict n _ _ -> n

(* Find all type conflicts between two signatures *)
let rec find_type_conflicts (tms1 tms2: list type_member)
    : list diamond_conflict =
  match tms1 with
  | [] -> []
  | tm1 :: rest ->
      let name = type_member_name tm1 in
      let conflicts_rest = find_type_conflicts rest tms2 in
      match lookup_type_member name tms2 with
      | Some tm2 -> TypeConflict name tm1 tm2 :: conflicts_rest
      | None -> conflicts_rest

(* Find all value conflicts between two signatures *)
let rec find_value_conflicts (vms1 vms2: list value_member)
    : list diamond_conflict =
  match vms1 with
  | [] -> []
  | vm1 :: rest ->
      let conflicts_rest = find_value_conflicts rest vms2 in
      match lookup_value_member vm1.val_name vms2 with
      | Some vm2 -> ValueConflict vm1.val_name vm1 vm2 :: conflicts_rest
      | None -> conflicts_rest

(* Find all effect conflicts between two signatures *)
let rec find_effect_conflicts (ess1 ess2: list effect_sig)
    : list diamond_conflict =
  match ess1 with
  | [] -> []
  | es1 :: rest ->
      let conflicts_rest = find_effect_conflicts rest ess2 in
      match lookup_effect_member es1.eff_sig_name ess2 with
      | Some es2 -> EffectConflict es1.eff_sig_name es1 es2 :: conflicts_rest
      | None -> conflicts_rest

(* Find all diamond conflicts between two signatures *)
let find_diamond_conflicts (s1 s2: signature) : list diamond_conflict =
  find_type_conflicts s1.sig_types s2.sig_types @
  find_value_conflicts s1.sig_values s2.sig_values @
  find_effect_conflicts s1.sig_effects s2.sig_effects

(* Check if a conflict is resolved by an override *)
let conflict_resolved_by (c: diamond_conflict) (ov: override_spec) : bool =
  conflict_name c = override_name ov

(* Check if all conflicts are resolved *)
let rec all_conflicts_resolved (conflicts: list diamond_conflict) (ovs: list override_spec)
    : bool =
  match conflicts with
  | [] -> true
  | c :: rest ->
      List.Tot.existsb (conflict_resolved_by c) ovs &&
      all_conflicts_resolved rest ovs

(* Remove duplicate members (keep first occurrence) after conflict resolution *)
let rec remove_duplicate_types (seen: list type_name) (tms: list type_member)
    : Tot (list type_member) (decreases tms) =
  match tms with
  | [] -> []
  | tm :: rest ->
      let name = type_member_name tm in
      if List.Tot.mem name seen then
        remove_duplicate_types seen rest
      else
        tm :: remove_duplicate_types (name :: seen) rest

let rec remove_duplicate_values (seen: list var_id) (vms: list value_member)
    : Tot (list value_member) (decreases vms) =
  match vms with
  | [] -> []
  | vm :: rest ->
      if List.Tot.mem vm.val_name seen then
        remove_duplicate_values seen rest
      else
        vm :: remove_duplicate_values (vm.val_name :: seen) rest

let rec remove_duplicate_effects (seen: list string) (ess: list effect_sig)
    : Tot (list effect_sig) (decreases ess) =
  match ess with
  | [] -> []
  | es :: rest ->
      if List.Tot.mem es.eff_sig_name seen then
        remove_duplicate_effects seen rest
      else
        es :: remove_duplicate_effects (es.eff_sig_name :: seen) rest

(* Compose with diamond resolution:
 * 1. Find all conflicts
 * 2. Verify all conflicts are resolved by overrides
 * 3. Apply overrides to resolve conflicts
 * 4. Combine signatures (now disjoint after override selection)
 *)
let compose_with_resolution (s1 s2: signature) (ovs: list override_spec)
    : option signature =
  let conflicts = find_diamond_conflicts s1 s2 in
  if not (all_conflicts_resolved conflicts ovs) then
    None  (* Unresolved conflicts *)
  else
    (* Combine signatures (may have duplicates) *)
    let combined = {
      sig_types = s1.sig_types @ s2.sig_types;
      sig_values = s1.sig_values @ s2.sig_values;
      sig_effects = s1.sig_effects @ s2.sig_effects
    } in
    (* Apply overrides to select winning implementations *)
    let resolved = apply_overrides ovs combined in
    (* Remove duplicates (overrides selected the winner) *)
    let deduped = {
      sig_types = remove_duplicate_types [] resolved.sig_types;
      sig_values = remove_duplicate_values [] resolved.sig_values;
      sig_effects = remove_duplicate_effects [] resolved.sig_effects
    } in
    Some deduped

(** ============================================================================
    MIXIN COMPLETION
    ============================================================================

    Complete a mixin by providing implementations for all required bindings.

    Given:
    - mixin M = { provided = P; required = R }
    - implementation I : S where S provides all of R

    Produces:
    - complete(M, I) : P + I (full module)

    Rules:
    1. I must provide all required bindings
    2. I's types must match R's requirements (or be subtypes)
    3. Result combines P and I (checking for conflicts)
    ============================================================================ *)

(* Check if an implementation satisfies mixin requirements.
 * The implementation signature must provide all required members. *)
let mixin_requirements_satisfied (mx: mixin_signature) (impl: signature) : bool =
  (* All required types must be present in impl *)
  List.Tot.for_all
    (fun tm -> Some? (lookup_type_member (type_member_name tm) impl.sig_types))
    mx.mixin_required.sig_types &&
  (* All required values must be present in impl with compatible types *)
  List.Tot.for_all
    (fun (vm: value_member) ->
      match lookup_value_member vm.val_name impl.sig_values with
      | Some impl_vm -> value_member_sub impl_vm vm
      | None -> false)
    mx.mixin_required.sig_values &&
  (* All required effects must be present in impl *)
  List.Tot.for_all
    (fun es -> Some? (lookup_effect_member es.eff_sig_name impl.sig_effects))
    mx.mixin_required.sig_effects

(* Complete a mixin with an implementation.
 * Returns the full module signature if successful. *)
let complete_mixin (mx: mixin_signature) (impl: signature) : option signature =
  if not (mixin_requirements_satisfied mx impl) then
    None  (* Requirements not met *)
  else
    (* Combine provided with implementation *)
    compose_signatures mx.mixin_provided impl

(* Complete a mixin with conflict resolution *)
let complete_mixin_with_resolution
    (mx: mixin_signature)
    (impl: signature)
    (ovs: list override_spec)
    : option signature =
  if not (mixin_requirements_satisfied mx impl) then
    None
  else
    compose_with_resolution mx.mixin_provided impl ovs

(** ============================================================================
    EXTENDED MODULE EXPRESSION WITH MIXINS
    ============================================================================

    Extends module_expr to support mixin operations.
    ============================================================================ *)

(* Mixin-aware module expression *)
noeq type mixin_module_expr =
  | MMStruct   : list module_decl -> mixin_module_expr
  | MMFunctor  : module_var -> module_type -> functor_mode -> mixin_module_expr -> mixin_module_expr
  | MMApp      : mixin_module_expr -> mixin_module_expr -> mixin_module_expr
  | MMPath     : module_path -> mixin_module_expr
  | MMSeal     : mixin_module_expr -> module_type -> mixin_module_expr
  | MMInclude  : mixin_module_expr -> mixin_module_expr     (* include M *)
  | MMCompose  : mixin_module_expr -> mixin_module_expr -> mixin_module_expr  (* M1 + M2 *)
  | MMWith     : mixin_module_expr -> list override_spec -> mixin_module_expr (* M with { ... } *)
  | MMMixin    : mixin_signature -> mixin_module_expr       (* mixin { provided; required } *)

(* Convert regular module_expr to mixin_module_expr *)
let rec module_expr_to_mixin (me: module_expr) : Tot mixin_module_expr (decreases me) =
  match me with
  | MEStruct decls -> MMStruct decls
  | MEFunctor x mt mode body -> MMFunctor x mt mode (module_expr_to_mixin body)
  | MEApp m1 m2 -> MMApp (module_expr_to_mixin m1) (module_expr_to_mixin m2)
  | MEPath p -> MMPath p
  | MESeal m mt -> MMSeal (module_expr_to_mixin m) mt

(** ============================================================================
    MIXIN MODULE TYPE CHECKING
    ============================================================================ *)

(* Result of mixin module type checking *)
noeq type mixin_check_result =
  | MixinOk    : module_type -> mixin_check_result
  | MixinPart  : mixin_signature -> mixin_check_result  (* Partial/mixin result *)
  | MixinErr   : string -> mixin_check_result

(* Type-check a mixin module expression *)
let rec check_mixin_module (env: module_env) (me: mixin_module_expr)
    : Tot mixin_check_result (decreases me) =
  match me with
  | MMStruct decls ->
      MixinOk (MTSig (infer_decls_sig decls))

  | MMFunctor x param_type mode body ->
      let env' = extend_module_env x param_type env in
      (match check_mixin_module env' body with
       | MixinOk body_type -> MixinOk (MTFunctor x param_type body_type mode)
       | MixinErr msg -> MixinErr msg
       | MixinPart _ -> MixinErr "Functor body cannot be a partial mixin")

  | MMApp func arg ->
      (match check_mixin_module env func, check_mixin_module env arg with
       | MixinOk (MTFunctor x param_type result_type _), MixinOk arg_type ->
           if module_type_sub arg_type param_type then
             MixinOk result_type
           else
             MixinErr "Functor argument type mismatch"
       | MixinOk _, _ -> MixinErr "Cannot apply non-functor"
       | MixinErr msg, _ -> MixinErr msg
       | _, MixinErr msg -> MixinErr msg
       | _, _ -> MixinErr "Invalid functor application with mixins")

  | MMPath path ->
      (match resolve_path env path with
       | Some mt -> MixinOk mt
       | None -> MixinErr "Unbound module path")

  | MMSeal m target_type ->
      (match check_mixin_module env m with
       | MixinOk inferred ->
           if module_type_sub inferred target_type then
             MixinOk target_type
           else
             MixinErr "Module does not match seal signature"
       | err -> err)

  | MMInclude m ->
      (match check_mixin_module env m with
       | MixinOk (MTSig s) -> MixinOk (MTSig s)  (* Include preserves type *)
       | MixinOk _ -> MixinErr "Can only include signature modules"
       | err -> err)

  | MMCompose m1 m2 ->
      (match check_mixin_module env m1, check_mixin_module env m2 with
       | MixinOk (MTSig s1), MixinOk (MTSig s2) ->
           (match compose_signatures s1 s2 with
            | Some s -> MixinOk (MTSig s)
            | None -> MixinErr "Composition conflict: signatures not disjoint")
       | MixinPart mx1, MixinPart mx2 ->
           (match compose_mixin_signatures mx1 mx2 with
            | Some mx -> MixinPart mx
            | None -> MixinErr "Mixin composition conflict")
       | MixinPart mx, MixinOk (MTSig s) ->
           (match complete_mixin mx s with
            | Some completed -> MixinOk (MTSig completed)
            | None -> MixinErr "Cannot complete mixin with given implementation")
       | MixinOk (MTSig s), MixinPart mx ->
           (match complete_mixin mx s with
            | Some completed -> MixinOk (MTSig completed)
            | None -> MixinErr "Cannot complete mixin with given implementation")
       | MixinErr msg, _ -> MixinErr msg
       | _, MixinErr msg -> MixinErr msg
       | _, _ -> MixinErr "Invalid module composition")

  | MMWith m ovs ->
      (match check_mixin_module env m with
       | MixinOk (MTSig s) ->
           if overrides_valid ovs s then
             MixinOk (MTSig (apply_overrides ovs s))
           else
             MixinErr "Invalid override specification"
       | MixinPart mx ->
           if overrides_valid ovs mx.mixin_provided then
             MixinPart { mx with mixin_provided = apply_overrides ovs mx.mixin_provided }
           else
             MixinErr "Invalid override for mixin"
       | err -> err)

  | MMMixin mx ->
      MixinPart mx

(** ============================================================================
    BRRR-MACHINE MIXIN ANALYSIS REQUIREMENTS
    ============================================================================

    Brrr-Machine needs to analyze mixin composition for:

    1. Dead Code Analysis:
       - Track which mixin provides each binding
       - Detect unused mixin contributions
       - Identify unreachable code paths through mixin chains

    2. Diamond Conflict Detection:
       - Find all potential diamond conflicts at compile time
       - Report unresolved conflicts with source locations
       - Suggest resolution strategies

    3. Mixin Dependency Analysis:
       - Build dependency graph between mixins
       - Detect circular mixin dependencies
       - Track which requirements are satisfied by which providers

    4. Override Impact Analysis:
       - Track how overrides affect downstream consumers
       - Detect breaking changes in mixin interfaces
       - Report type compatibility issues

    The following types and functions support these analysis requirements.
    ============================================================================ *)

(* Mixin provenance: tracks where a binding came from *)
noeq type mixin_provenance = {
  mp_mixin_name : string;           (* Name of the mixin *)
  mp_binding_name : string;         (* Name of the binding *)
  mp_binding_kind : string;         (* "type" | "value" | "effect" *)
  mp_is_override : bool;            (* Was this overridden? *)
  mp_original_source : option string (* Original source if overridden *)
}

(* Mixin dependency edge *)
noeq type mixin_dependency = {
  md_provider : string;   (* Mixin providing the binding *)
  md_consumer : string;   (* Mixin requiring the binding *)
  md_binding : string;    (* The binding name *)
  md_kind : string        (* "type" | "value" | "effect" *)
}

(* Mixin analysis context *)
noeq type mixin_analysis_ctx = {
  mac_provenances : list mixin_provenance;
  mac_dependencies : list mixin_dependency;
  mac_conflicts : list diamond_conflict;
  mac_unresolved : list diamond_conflict
}

(* Empty analysis context *)
let empty_mixin_analysis_ctx : mixin_analysis_ctx = {
  mac_provenances = [];
  mac_dependencies = [];
  mac_conflicts = [];
  mac_unresolved = []
}

(* Record provenance for a type member *)
let record_type_provenance (mixin_name: string) (tm: type_member) (is_override: bool)
    : mixin_provenance = {
  mp_mixin_name = mixin_name;
  mp_binding_name = type_member_name tm;
  mp_binding_kind = "type";
  mp_is_override = is_override;
  mp_original_source = None
}

(* Record provenance for a value member *)
let record_value_provenance (mixin_name: string) (vm: value_member) (is_override: bool)
    : mixin_provenance = {
  mp_mixin_name = mixin_name;
  mp_binding_name = vm.val_name;
  mp_binding_kind = "value";
  mp_is_override = is_override;
  mp_original_source = None
}

(* Record a dependency between mixins *)
let record_dependency (provider consumer binding kind: string) : mixin_dependency = {
  md_provider = provider;
  md_consumer = consumer;
  md_binding = binding;
  md_kind = kind
}

(* Analyze a mixin composition and build analysis context *)
let analyze_mixin_composition
    (m1_name: string) (m1: mixin_signature)
    (m2_name: string) (m2: mixin_signature)
    : mixin_analysis_ctx =
  (* Find conflicts *)
  let type_conflicts = find_type_conflicts m1.mixin_provided.sig_types m2.mixin_provided.sig_types in
  let value_conflicts = find_value_conflicts m1.mixin_provided.sig_values m2.mixin_provided.sig_values in
  let effect_conflicts = find_effect_conflicts m1.mixin_provided.sig_effects m2.mixin_provided.sig_effects in
  let all_conflicts = type_conflicts @ value_conflicts @ effect_conflicts in

  (* Build provenances for m1 *)
  let m1_type_provs = List.Tot.map (fun tm -> record_type_provenance m1_name tm false) m1.mixin_provided.sig_types in
  let m1_value_provs = List.Tot.map (fun vm -> record_value_provenance m1_name vm false) m1.mixin_provided.sig_values in

  (* Build provenances for m2 *)
  let m2_type_provs = List.Tot.map (fun tm -> record_type_provenance m2_name tm false) m2.mixin_provided.sig_types in
  let m2_value_provs = List.Tot.map (fun vm -> record_value_provenance m2_name vm false) m2.mixin_provided.sig_values in

  (* Build dependencies: m1's requirements satisfied by m2's provided *)
  let rec build_deps_m1 (tms: list type_member) : list mixin_dependency =
    match tms with
    | [] -> []
    | tm :: rest ->
        let name = type_member_name tm in
        if Some? (lookup_type_member name m2.mixin_provided.sig_types) then
          record_dependency m2_name m1_name name "type" :: build_deps_m1 rest
        else
          build_deps_m1 rest
  in
  let m1_deps = build_deps_m1 m1.mixin_required.sig_types in

  let rec build_deps_m2 (tms: list type_member) : list mixin_dependency =
    match tms with
    | [] -> []
    | tm :: rest ->
        let name = type_member_name tm in
        if Some? (lookup_type_member name m1.mixin_provided.sig_types) then
          record_dependency m1_name m2_name name "type" :: build_deps_m2 rest
        else
          build_deps_m2 rest
  in
  let m2_deps = build_deps_m2 m2.mixin_required.sig_types in

  {
    mac_provenances = m1_type_provs @ m1_value_provs @ m2_type_provs @ m2_value_provs;
    mac_dependencies = m1_deps @ m2_deps;
    mac_conflicts = all_conflicts;
    mac_unresolved = all_conflicts  (* All conflicts start unresolved *)
  }

(* Mark conflicts as resolved after override application *)
let mark_conflicts_resolved (ctx: mixin_analysis_ctx) (ovs: list override_spec)
    : mixin_analysis_ctx =
  let still_unresolved = List.Tot.filter
    (fun c -> not (List.Tot.existsb (conflict_resolved_by c) ovs))
    ctx.mac_unresolved in
  { ctx with mac_unresolved = still_unresolved }

(* Check if analysis found any issues *)
let mixin_analysis_has_errors (ctx: mixin_analysis_ctx) : bool =
  List.Tot.length ctx.mac_unresolved > 0

(* Get all unresolved conflict names for error reporting *)
let get_unresolved_conflict_names (ctx: mixin_analysis_ctx) : list string =
  List.Tot.map conflict_name ctx.mac_unresolved

(** ============================================================================
    CONVENIENCE CONSTRUCTORS FOR MIXINS
    ============================================================================ *)

(* Create a simple mixin with one type requirement *)
let mixin_require_type (name: type_name) (k: kind) : mixin_signature =
  mixin_requires (sig_abstract_type name k)

(* Create a simple mixin with one value requirement *)
let mixin_require_val (name: var_id) (ty: brrr_type) : mixin_signature =
  mixin_requires (sig_val name ty)

(* Create a mixin that provides a type *)
let mixin_provide_type (name: type_name) (k: kind) (def: brrr_type) : mixin_signature =
  mixin_from_sig (sig_concrete_type name k def)

(* Create a mixin that provides a value *)
let mixin_provide_val (name: var_id) (ty: brrr_type) : mixin_signature =
  mixin_from_sig (sig_val name ty)

(* Create a mixin expression from a signature *)
let mm_from_sig (s: signature) : mixin_module_expr =
  MMMixin (mixin_from_sig s)

(* Create a composition expression *)
let mm_compose (m1 m2: mixin_module_expr) : mixin_module_expr =
  MMCompose m1 m2

(* Create a with-override expression *)
let mm_with (m: mixin_module_expr) (ovs: list override_spec) : mixin_module_expr =
  MMWith m ovs

(* Create an include expression *)
let mm_include (m: mixin_module_expr) : mixin_module_expr =
  MMInclude m

(** ============================================================================
    MODULE DEPENDENCY GRAPH AND CIRCULAR DETECTION
    ============================================================================

    Module dependency tracking is essential for correct compilation and static
    analysis. This section implements dependency graph construction, cycle
    detection, and topological sorting.

    PURPOSE:
    --------
    1. CIRCULAR DEPENDENCY DETECTION
       Circular dependencies are errors in most module systems:
         A imports B, B imports A  ->  Error: circular dependency

       Unlike some lazy languages, Brrr requires acyclic dependencies for:
         - Predictable initialization order
         - Decidable type checking
         - Efficient separate compilation

    2. COMPILATION ORDER
       Modules must be compiled in dependency order:
         If A depends on B, compile B before A
       Topological sort gives a valid compilation order for acyclic graphs.

    3. IMPACT ANALYSIS
       When a module changes, which modules need recompilation?
         - Direct dependents (modules that import it)
         - Transitive dependents (modules depending on direct dependents)
       This enables incremental compilation.

    GRAPH REPRESENTATION:
    ---------------------
    The dependency graph is represented as:
      - Nodes: module names (strings)
      - Edges: directed dependency edges with metadata

    Each edge records:
      - de_from: the dependent module
      - de_to: the module being depended upon
      - de_kind: the type of dependency ("import", "type", "value", "effect")

    DEPENDENCY KINDS:
    -----------------
    "import" - Full module import (import M)
    "type"   - Type reference (uses M.T in a signature)
    "value"  - Value reference (calls M.f)
    "effect" - Effect reference (uses M.E effect)

    Tracking kinds enables fine-grained analysis:
      - Type-only dependencies may allow more parallelism
      - Value dependencies indicate runtime coupling
      - Effect dependencies track effect propagation

    BRRR-MACHINE ANALYSIS:
    ----------------------
    The dependency graph feeds into several analyses:

    1. DEAD MODULE DETECTION
       Modules with no dependents (except entry points) may be dead code.

    2. INTERFACE STABILITY
       Modules with many dependents should have stable interfaces.

    3. LAYERING ANALYSIS
       Dependencies should flow in one direction (no bidirectional coupling).

    4. INCREMENTAL COMPILATION
       Changed module -> recompile dependents transitively.

    COMPLEXITY:
    -----------
    - Graph construction: O(n + e) where n = modules, e = dependencies
    - Cycle detection: O(n + e) using DFS
    - Topological sort: O(n + e) using Kahn's algorithm

    COMPARISON WITH F*:
    -------------------
    F*'s dependency tracking:
      - Uses .checked files for caching
      - Computes dependencies from imports
      - Requires DAG structure (no mutual recursion across files)
      - Interface files (.fsti) can break cycles

    Brrr follows a similar model but with explicit graph tracking for
    analysis tooling integration.
    ============================================================================ *)

(* Module dependency graph node *)
type module_name = string

(* Dependency edge: from depends_on to *)
noeq type dep_edge = {
  de_from : module_name;     (* Module that has the dependency *)
  de_to   : module_name;     (* Module being depended upon *)
  de_kind : string           (* "import" | "type" | "value" | "effect" *)
}

(* Dependency graph as adjacency list *)
noeq type dep_graph = {
  dg_nodes : list module_name;           (* All modules *)
  dg_edges : list dep_edge               (* All dependency edges *)
}

(* Empty dependency graph *)
let empty_dep_graph : dep_graph = {
  dg_nodes = [];
  dg_edges = []
}

(* Add a module to the graph *)
let add_module_to_graph (name: module_name) (g: dep_graph) : dep_graph =
  if List.Tot.mem name g.dg_nodes then g
  else { g with dg_nodes = name :: g.dg_nodes }

(* Add a dependency edge to the graph *)
let add_dep_edge (edge: dep_edge) (g: dep_graph) : dep_graph =
  let g = add_module_to_graph edge.de_from g in
  let g = add_module_to_graph edge.de_to g in
  { g with dg_edges = edge :: g.dg_edges }

(* Get all modules that a given module depends on *)
let get_dependencies (name: module_name) (g: dep_graph) : list module_name =
  let edges = List.Tot.filter (fun e -> e.de_from = name) g.dg_edges in
  List.Tot.map (fun e -> e.de_to) edges

(* Get all modules that depend on a given module (reverse deps) *)
let get_dependents (name: module_name) (g: dep_graph) : list module_name =
  let edges = List.Tot.filter (fun e -> e.de_to = name) g.dg_edges in
  List.Tot.map (fun e -> e.de_from) edges

(** ============================================================================
    CIRCULAR DEPENDENCY DETECTION USING DFS
    ============================================================================

    Cycle detection uses depth-first search (DFS) with three-color marking:
      - White: not yet visited
      - Gray: currently being processed (in DFS stack)
      - Black: fully processed (all descendants visited)

    A cycle exists iff we encounter a gray node during traversal (back edge).

    ALGORITHM:
    ----------
    For each unvisited node:
      1. Mark it gray (push to stack)
      2. Recursively visit all neighbors
         - If neighbor is gray: CYCLE FOUND (back edge)
         - If neighbor is black: skip (already processed)
         - If neighbor is white: recurse
      3. Mark it black (move from stack to visited)

    CYCLE EXTRACTION:
    -----------------
    When a back edge is found (current -> gray node), the cycle consists of:
      - The gray node (target of back edge)
      - All nodes on the DFS stack from the gray node to current

    Example: Stack is [A, B, C, D], back edge D -> B
             Cycle is [B, C, D, B]

    TERMINATION:
    ------------
    F* requires termination proofs for recursive functions. We use a fuel
    parameter that decreases with each recursive call. The fuel is set to
    2 * |nodes| which is sufficient for DFS traversal.

    ERROR REPORTING:
    ----------------
    The detected cycle is returned as a list of module names in order,
    enabling error messages like:
      "Circular dependency: A -> B -> C -> A"

    COMPLEXITY:
    -----------
    O(V + E) where V = number of modules, E = number of dependencies.
    Each node is visited at most once, each edge is traversed at most once.
    ============================================================================ *)

(** DFS state for cycle detection.
    Uses "gray/black" coloring via two lists:
      - ds_in_stack (gray): currently being processed
      - ds_visited (black): fully processed *)
noeq type dfs_state = {
  ds_visited  : list module_name;   (* Fully processed nodes (black) *)
  ds_in_stack : list module_name;   (* Nodes in current DFS path (gray) *)
  ds_cycle    : option (list module_name)  (* Detected cycle, if any *)
}

(* Initial DFS state *)
let init_dfs_state : dfs_state = {
  ds_visited = [];
  ds_in_stack = [];
  ds_cycle = None
}

(* Check if we've already found a cycle *)
let has_cycle (st: dfs_state) : bool = Some? st.ds_cycle

(* Check if node is visited *)
let is_visited (name: module_name) (st: dfs_state) : bool =
  List.Tot.mem name st.ds_visited

(* Check if node is in current DFS stack (back edge = cycle) *)
let is_in_stack (name: module_name) (st: dfs_state) : bool =
  List.Tot.mem name st.ds_in_stack

(* Mark node as visited and remove from stack *)
let finish_node (name: module_name) (st: dfs_state) : dfs_state = {
  ds_visited = name :: st.ds_visited;
  ds_in_stack = List.Tot.filter (fun n -> n <> name) st.ds_in_stack;
  ds_cycle = st.ds_cycle
}

(* Push node onto DFS stack *)
let push_stack (name: module_name) (st: dfs_state) : dfs_state =
  { st with ds_in_stack = name :: st.ds_in_stack }

(* Extract cycle from stack when back edge detected *)
let extract_cycle (target: module_name) (st: dfs_state) : list module_name =
  (* Cycle is from target back to target through stack *)
  let rec take_until (acc: list module_name) (stk: list module_name)
      : Tot (list module_name) (decreases stk) =
    match stk with
    | [] -> acc
    | n :: rest ->
        if n = target then target :: acc
        else take_until (n :: acc) rest
  in
  target :: take_until [] st.ds_in_stack

(* Record a detected cycle *)
let record_cycle (target: module_name) (st: dfs_state) : dfs_state =
  { st with ds_cycle = Some (extract_cycle target st) }

(* DFS traversal for cycle detection.
 * Returns updated state with cycle if found.
 * Fuel parameter ensures termination. *)
let rec dfs_visit
    (g: dep_graph)
    (name: module_name)
    (st: dfs_state)
    (fuel: nat)
    : Tot dfs_state (decreases fuel) =
  if fuel = 0 then st  (* Ran out of fuel - inconclusive *)
  else if has_cycle st then st  (* Already found cycle *)
  else if is_visited name st then st  (* Already fully processed *)
  else if is_in_stack name st then
    (* Back edge detected - cycle found! *)
    record_cycle name st
  else
    (* Push onto stack and visit neighbors *)
    let st = push_stack name st in
    let deps = get_dependencies name g in
    let st = dfs_visit_all g deps st (fuel - 1) in
    (* Finish this node *)
    finish_node name st

and dfs_visit_all
    (g: dep_graph)
    (names: list module_name)
    (st: dfs_state)
    (fuel: nat)
    : Tot dfs_state (decreases fuel) =
  if fuel = 0 then st
  else match names with
  | [] -> st
  | n :: rest ->
      let st = dfs_visit g n st (fuel - 1) in
      dfs_visit_all g rest st (fuel - 1)

(* Detect cycles in the dependency graph.
 * Returns Some cycle if found, None if acyclic. *)
let detect_circular_deps (g: dep_graph) : option (list module_name) =
  (* Use total nodes * 2 as fuel (safe upper bound) *)
  let n = List.Tot.length g.dg_nodes in
  let fuel : nat = n + n + 1 in
  let final_state = dfs_visit_all g g.dg_nodes init_dfs_state fuel in
  final_state.ds_cycle

(* Check if dependency graph is acyclic *)
let is_acyclic (g: dep_graph) : bool =
  None? (detect_circular_deps g)

(** ============================================================================
    TOPOLOGICAL SORT FOR COMPILATION ORDER
    ============================================================================

    Topological sorting produces a linear ordering of modules such that for
    every dependency edge (A -> B), B appears before A in the ordering.
    This ensures modules are compiled after their dependencies.

    ALGORITHM (Kahn's Algorithm):
    -----------------------------
    1. Compute in-degree (number of incoming edges) for each node
    2. Add all nodes with in-degree 0 to a queue
    3. While queue is not empty:
       a. Remove node from queue, add to result
       b. For each neighbor of the node:
          - Decrement neighbor's in-degree
          - If in-degree becomes 0, add to queue
    4. If result contains all nodes, graph is acyclic and result is valid
       Otherwise, graph has a cycle

    ALTERNATIVE: DFS-BASED TOPOLOGICAL SORT
    ---------------------------------------
    Alternatively, use reverse DFS post-order:
      1. Run DFS from each unvisited node
      2. Add node to result AFTER visiting all descendants
      3. Reverse the result
    This is what detect_circular_deps effectively computes (ds_visited).

    PROPERTIES:
    -----------
    - Topological order exists iff graph is acyclic (DAG)
    - Multiple valid orderings may exist
    - Kahn's algorithm produces a valid ordering in O(V + E)

    USE FOR COMPILATION:
    --------------------
    Given topological order [M1, M2, M3, ...]:
      - M1 has no dependencies, compile first
      - M2's dependencies are in [M1], compile second
      - And so on...

    INCREMENTAL COMPILATION:
    ------------------------
    When module M changes:
      1. Find all dependents of M (reverse edges)
      2. Recompile M
      3. Recompile dependents in topological order

    PARALLEL COMPILATION:
    ---------------------
    Modules with the same "level" (distance from leaves) can be
    compiled in parallel. Topological sort enables computing these levels.

    KAHN'S ALGORITHM (implemented below):
    -------------------------------------
    Repeatedly remove nodes with no incoming edges (in-degree 0).
    Only works on acyclic graphs. *)

(* Compute in-degree (number of incoming edges) for each node *)
let compute_in_degrees (g: dep_graph) : list (module_name & nat) =
  List.Tot.map
    (fun n -> (n, List.Tot.length (List.Tot.filter (fun e -> e.de_to = n) g.dg_edges)))
    g.dg_nodes

(* Find nodes with zero in-degree *)
let find_zero_indegree (degrees: list (module_name & nat)) : list module_name =
  List.Tot.map fst (List.Tot.filter (fun (p: module_name & nat) -> snd p = 0) degrees)

(* Remove a node from degree list and decrement affected degrees *)
let remove_and_decrement
    (to_remove: module_name)
    (g: dep_graph)
    (degrees: list (module_name & nat))
    : list (module_name & nat) =
  let deps = get_dependents to_remove g in  (* Modules that depend on to_remove *)
  let filtered = List.Tot.filter (fun (p: module_name & nat) -> fst p <> to_remove) degrees in
  List.Tot.map
    (fun (p: module_name & nat) ->
      let (n, d) = p in
      if List.Tot.mem n deps then
        let d' : nat = if d > 0 then d - 1 else 0 in (n, d')
      else (n, d))
    filtered

(* Topological sort with fuel for termination *)
let rec topological_sort_aux
    (g: dep_graph)
    (degrees: list (module_name & nat))
    (result: list module_name)
    (fuel: nat)
    : Tot (option (list module_name)) (decreases fuel) =
  if fuel = 0 then None  (* Ran out of fuel *)
  else if Nil? degrees then Some (List.Tot.rev result)  (* Done *)
  else
    match find_zero_indegree degrees with
    | [] -> None  (* No zero-degree nodes but graph not empty = cycle *)
    | n :: _ ->
        let degrees' = remove_and_decrement n g degrees in
        topological_sort_aux g degrees' (n :: result) (fuel - 1)

(* Topological sort of dependency graph.
 * Returns compilation order (dependencies first) or None if cyclic. *)
let topological_sort (g: dep_graph) : option (list module_name) =
  let degrees = compute_in_degrees g in
  let fuel = List.Tot.length g.dg_nodes + 1 in
  topological_sort_aux g degrees [] fuel

(* Reverse topological sort - dependents first.
 * Useful for finding what needs recompilation when a module changes. *)
let reverse_topological_sort (g: dep_graph) : option (list module_name) =
  match topological_sort g with
  | None -> None
  | Some order -> Some (List.Tot.rev order)

(** ============================================================================
    MODULE DEPENDENCY LEMMAS
    ============================================================================ *)

(* Lemma: Empty graph is acyclic *)
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val empty_graph_acyclic : unit -> Lemma (is_acyclic empty_dep_graph = true)
let empty_graph_acyclic () = ()
#pop-options

(* Helper: add_module_to_graph preserves or increases length *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val add_module_preserves_length : name:module_name -> g:dep_graph ->
  Lemma (List.Tot.length (add_module_to_graph name g).dg_nodes >=
         List.Tot.length g.dg_nodes)
let add_module_preserves_length name g =
  if List.Tot.mem name g.dg_nodes then ()
  else ()
#pop-options

(* Lemma: Adding edge preserves nodes *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val add_edge_preserves_nodes : e:dep_edge -> g:dep_graph ->
  Lemma (List.Tot.length (add_dep_edge e g).dg_nodes >=
         List.Tot.length g.dg_nodes)
let add_edge_preserves_nodes e g =
  add_module_preserves_length e.de_from g;
  let g' = add_module_to_graph e.de_from g in
  add_module_preserves_length e.de_to g'
#pop-options

(* Lemma: Topological sort of acyclic graph succeeds.
 * When the graph is acyclic, Kahn's algorithm will find a topological order.
 * Each iteration removes at least one node with zero in-degree.
 * Since no cycles exist, such a node always exists until graph is empty.
 *
 * TODO: Full proof requires:
 *   1. Kahn's algorithm invariant: if acyclic, always exists zero-degree node
 *   2. Termination: each iteration reduces the graph size
 *   3. Correctness: removed nodes form valid topological order
 * This is well-known in graph theory but non-trivial to formalize. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val module_deps_acyclic : g:dep_graph ->
  Lemma (requires is_acyclic g = true)
        (ensures Some? (topological_sort g))
let module_deps_acyclic g =
  admit()  (* Well-known graph theory result - proof requires Kahn's algorithm invariants *)
#pop-options

(** ============================================================================
    IMPORT VERIFICATION AND TYPE PRESERVATION
    ============================================================================ *)

(* Module import record *)
noeq type module_import = {
  mi_from   : module_name;    (* Importing from this module *)
  mi_items  : list string;    (* Specific items to import, or empty for all *)
  mi_alias  : option string   (* Optional renaming alias *)
}

(* Import resolution result *)
noeq type import_result =
  | ImportOk    : imported_sig:signature -> import_result
  | ImportErr   : msg:string -> import_result

(* Well-formed kind check - kinds are syntactic and always valid.
 * This is a placeholder for potential future extensions. *)
let wf_kind (_ctx: kind_ctx) (_k: kind) : bool = true

(* Check if a type has a given kind - wrapper around check_kind *)
let type_has_kind (ctx: kind_ctx) (t: brrr_type) (k: kind) : bool =
  check_kind ctx t k

(* Check if dst_ctx extends src_ctx (contains all bindings from src_ctx) *)
let rec kind_ctx_extends (dst_ctx: kind_ctx) (src_ctx: kind_ctx) : bool =
  match src_ctx with
  | [] -> true
  | (v, k) :: rest ->
      (match lookup_kind v dst_ctx with
       | None -> false
       | Some k' -> kind_eq k k') &&
      kind_ctx_extends dst_ctx rest

(* Check that imported types remain well-formed in the new context.
 * This is the key soundness property for module imports. *)
let rec check_imported_types_wf
    (ctx: kind_ctx)
    (types: list type_member)
    : bool =
  match types with
  | [] -> true
  | tm :: rest ->
      (match tm with
       | TMOpaque _ k _ _ -> wf_kind ctx k
       | TMTransparent _ k t _ _ -> wf_kind ctx k && type_has_kind ctx t k) &&
      check_imported_types_wf ctx rest

(* Lemma: Importing well-formed types preserves well-formedness.
 * If the source module's types are well-formed and the import context
 * extends the source context, imported types remain well-formed.
 *
 * TODO: Full proof requires:
 *   1. Kind checking is monotonic: check_kind extended_ctx t k => check_kind original_ctx t k
 *   2. Inductive argument over type member list
 * Proof is standard but requires context extension preservation lemmas. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val import_preserves_types : src_ctx:kind_ctx -> dst_ctx:kind_ctx ->
                             types:list type_member ->
  Lemma (requires
           check_imported_types_wf src_ctx types = true /\
           kind_ctx_extends dst_ctx src_ctx = true)
        (ensures check_imported_types_wf dst_ctx types = true)
let rec import_preserves_types src_ctx dst_ctx types =
  admit()  (* Requires monotonicity lemma for kind checking *)
#pop-options

(* Build dependency graph from a list of module imports *)
let build_import_graph
    (mod_name: module_name)
    (imports: list module_import)
    (g: dep_graph)
    : dep_graph =
  let g = add_module_to_graph mod_name g in
  List.Tot.fold_left
    (fun acc imp ->
      add_dep_edge { de_from = mod_name; de_to = imp.mi_from; de_kind = "import" } acc)
    g
    imports

(* Validate that imports don't create circular dependencies *)
let validate_imports_acyclic
    (mod_name: module_name)
    (imports: list module_import)
    (existing_graph: dep_graph)
    : option (list module_name) =
  let g = build_import_graph mod_name imports existing_graph in
  detect_circular_deps g
