(**
 * BrrrLang.Core.TypeClasses Interface
 *
 * Type class system for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part IV - Type Classes.
 *
 * ============================================================================
 * THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * Type classes were introduced by Wadler & Blott in their seminal 1989 paper:
 *   "How to make ad-hoc polymorphism less ad hoc" (POPL 1989)
 *
 * Key properties:
 *   - Type inference remains decidable
 *   - Instance resolution is performed at compile time
 *   - No runtime type dispatch overhead (after dictionary passing)
 *
 * References:
 *   - Wadler & Blott 1989: Original type classes paper
 *   - Jones 1999: "Typing Haskell in Haskell" - formal semantics
 *   - Chakravarty et al. 2005: "Associated Types with Class"
 *
 * Depends on: BrrrTypes, Expressions, Kinds, Modes, Effects
 *)
module BrrrTypeClasses

open FStar.List.Tot
open FStar.Classical
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrKinds

(** ============================================================================
    TYPE CLASS NAMES
    ============================================================================ *)

(** Type class identifier - unique name for the class *)
type class_name = string

(** Method name within a class - may be an operator symbol *)
type method_name = string

(** ============================================================================
    CLASS METHOD
    ============================================================================ *)

(**
 * A method declaration in a type class.
 * The method_type is polymorphic, containing the class type parameter.
 *)
noeq type class_method = {
  cm_name : method_name;
  cm_type : brrr_type;
}

(** Check method equality by name and type *)
val method_eq : m1:class_method -> m2:class_method -> bool

(** ============================================================================
    TYPE CLASS DEFINITION
    ============================================================================ *)

(**
 * A type class declaration.
 *
 * Fields:
 *   - tc_name: The class name
 *   - tc_param: The type parameter
 *   - tc_superclasses: List of superclass names
 *   - tc_methods: List of method declarations
 *)
noeq type type_class = {
  tc_name         : class_name;
  tc_param        : type_var;
  tc_superclasses : list class_name;
  tc_methods      : list class_method;
}

(** Check if two type classes are equal *)
val type_class_eq : c1:type_class -> c2:type_class -> bool

(** ============================================================================
    SUPERCLASS CYCLE DETECTION
    ============================================================================ *)

(** Check if a class name is in a list *)
val class_name_in_list : name:class_name -> names:list class_name -> bool

(** Lookup a class by name *)
val lookup_class : name:class_name -> classes:list type_class -> option type_class

(**
 * Depth-first cycle detection from a starting class.
 * Returns true if a cycle is found.
 *)
val detect_superclass_cycle_dfs :
    start:class_name ->
    current:class_name ->
    visited:list class_name ->
    classes:list type_class ->
    fuel:nat ->
    Tot bool (decreases fuel)

(** Helper: Check each superclass for cycles back to start *)
val check_supers_for_cycle :
    start:class_name ->
    supers:list class_name ->
    visited:list class_name ->
    classes:list type_class ->
    fuel:nat ->
    Tot bool (decreases fuel)

(** Check if a class participates in a superclass cycle *)
val has_superclass_cycle : cls:type_class -> classes:list type_class -> bool

(** Check if the entire class hierarchy is acyclic *)
val all_classes_acyclic : classes:list type_class -> bool

(** Lemma: If all_classes_acyclic, then no individual class has a cycle *)
val acyclic_implies_no_individual_cycle :
    classes:list type_class -> cls:type_class ->
    Lemma (requires all_classes_acyclic classes /\ List.Tot.memP cls classes)
          (ensures not (has_superclass_cycle cls classes))
          [SMTPat (all_classes_acyclic classes); SMTPat (List.Tot.memP cls classes)]

(** ============================================================================
    METHOD IMPLEMENTATION
    ============================================================================ *)

(** A method implementation pairs a method name with its expression body *)
type method_impl = method_name & expr

(** Find a method implementation by name *)
val find_method_impl : name:method_name -> impls:list method_impl -> option expr

(** ============================================================================
    CLASS INSTANCE
    ============================================================================ *)

(**
 * An instance of a type class for a specific type.
 *
 * Fields:
 *   - ci_class: The class being implemented
 *   - ci_type: The concrete type implementing the class
 *   - ci_methods: Method implementations
 *)
noeq type class_instance = {
  ci_class   : class_name;
  ci_type    : brrr_type;
  ci_methods : list method_impl;
}

(** Check if an instance implements a specific class for a specific type *)
val instance_matches : inst:class_instance -> cls:class_name -> ty:brrr_type -> bool

(** ============================================================================
    CLASS CONSTRAINT
    ============================================================================ *)

(**
 * A class constraint specifies that a type variable must implement a class.
 *)
noeq type class_constraint = {
  cc_class : class_name;
  cc_var   : type_var;
}

(** Check constraint equality *)
val constraint_eq : c1:class_constraint -> c2:class_constraint -> bool

(** Check if a constraint is in a list *)
val has_constraint : c:class_constraint -> cs:list class_constraint -> bool

(** ============================================================================
    CONSTRAINED TYPE
    ============================================================================ *)

(**
 * A constrained type (qualified type) bundles constraints with a base type.
 *)
noeq type constrained_type = {
  ct_constraints : list class_constraint;
  ct_type        : brrr_type;
}

(** Create an unconstrained type *)
val unconstrained : t:brrr_type -> constrained_type

(** Add a constraint to a constrained type *)
val add_constraint : c:class_constraint -> ct:constrained_type -> constrained_type

(** Check if all constraints are satisfied by a list of instances *)
val constraints_satisfied :
    constraints:list class_constraint ->
    subst:list (type_var & brrr_type) ->
    instances:list class_instance ->
    Tot bool (decreases constraints)

(** ============================================================================
    TYPE CLASS ENVIRONMENT
    ============================================================================ *)

(**
 * Type class environment containing all class definitions and instances.
 *)
noeq type class_env = {
  ce_classes   : list type_class;
  ce_instances : list class_instance;
}

(** Empty class environment *)
val empty_class_env : class_env

(** Add a class to the environment *)
val add_class : c:type_class -> env:class_env -> class_env

(**
 * Add an instance to the environment.
 * WARNING: Does NOT check for overlapping instances or well-formedness.
 * Use add_instance_safe for production code.
 *)
val add_instance : i:class_instance -> env:class_env -> class_env

(** ============================================================================
    INSTANCE RESOLUTION
    ============================================================================ *)

(** Size measure for instance lists *)
val instance_list_size : instances:list class_instance -> nat

(**
 * Find an instance matching a class and type directly (no superclass check).
 *)
val find_direct_instance :
    cls:class_name ->
    ty:brrr_type ->
    instances:list class_instance ->
    Tot (option class_instance) (decreases instances)

(**
 * Check if all superclass instances exist for a given type.
 * Simple non-transitive version.
 *)
val superclasses_satisfied :
    supers:list class_name ->
    ty:brrr_type ->
    instances:list class_instance ->
    Tot bool (decreases supers)

(** Maximum recursion depth for superclass traversal *)
val max_superclass_depth : nat

(**
 * Safe transitive superclass checking with cycle detection.
 *)
val superclasses_satisfied_safe :
    supers:list class_name ->
    ty:brrr_type ->
    instances:list class_instance ->
    classes:list type_class ->
    visited:list class_name ->
    depth:nat ->
    Tot bool (decreases depth)

(**
 * Main instance resolution function.
 *
 * Given a class name and a concrete type, finds a matching instance
 * and verifies all superclass instances exist transitively.
 *)
val resolve_instance :
    cls:class_name ->
    ty:brrr_type ->
    env:class_env ->
    option class_instance

(** ============================================================================
    INSTANCE RESOLUTION CORRECTNESS PROOFS
    ============================================================================ *)

(** Lemma: find_direct_instance returns an instance that matches *)
val find_direct_instance_matches :
    cls:class_name -> ty:brrr_type -> instances:list class_instance ->
    Lemma (ensures (match find_direct_instance cls ty instances with
                    | None -> True
                    | Some inst -> instance_matches inst cls ty = true))
          (decreases instances)

(** Lemma: If find_direct_instance succeeds, the instance is in the list *)
val find_direct_instance_in_list :
    cls:class_name -> ty:brrr_type -> instances:list class_instance ->
    Lemma (ensures (match find_direct_instance cls ty instances with
                    | None -> True
                    | Some inst -> List.Tot.memP inst instances))
          (decreases instances)

(** Main correctness theorem: resolve_instance is sound *)
val resolve_instance_sound :
    cls:class_name -> ty:brrr_type -> env:class_env ->
    Lemma (ensures (match resolve_instance cls ty env with
                    | None -> True
                    | Some inst ->
                        instance_matches inst cls ty = true /\
                        Some? (lookup_class cls env.ce_classes) /\
                        (match lookup_class cls env.ce_classes with
                         | Some class_def ->
                             superclasses_satisfied class_def.tc_superclasses ty env.ce_instances = true
                         | None -> False)))
          [SMTPat (resolve_instance cls ty env)]

(** ============================================================================
    SAFE INSTANCE RESOLUTION
    ============================================================================ *)

(** Instance resolution result with detailed error information *)
type resolve_result =
  | ResolveOk : inst:class_instance -> resolve_result
  | ResolveClassNotFound : cls:class_name -> resolve_result
  | ResolveNoInstance : cls:class_name -> ty:brrr_type -> resolve_result
  | ResolveMissingSuperclass : cls:class_name -> super:class_name -> ty:brrr_type -> resolve_result
  | ResolveCycleDetected : cls:class_name -> resolve_result

(** Find which superclass is missing its instance *)
val find_missing_superclass :
    supers:list class_name ->
    ty:brrr_type ->
    instances:list class_instance ->
    option class_name

(** Safe instance resolution with detailed error reporting *)
val safe_resolve_instance :
    cls:class_name ->
    ty:brrr_type ->
    env:class_env ->
    resolve_result

(** Lemma: safe_resolve_instance terminates for any input *)
val safe_resolve_terminates :
    cls:class_name -> ty:brrr_type -> env:class_env ->
    Lemma (ensures True)
          [SMTPat (safe_resolve_instance cls ty env)]

(** ============================================================================
    CONSTRAINT ENTAILMENT
    ============================================================================ *)

(** Check if a constraint is entailed by instances given a type substitution *)
val constraint_entailed :
    c:class_constraint ->
    subst:list (type_var & brrr_type) ->
    env:class_env ->
    bool

(** Check if all constraints are entailed *)
val all_constraints_entailed :
    constraints:list class_constraint ->
    subst:list (type_var & brrr_type) ->
    env:class_env ->
    Tot bool (decreases constraints)

(** ============================================================================
    METHOD LOOKUP
    ============================================================================ *)

(** Lookup a method in a resolved instance *)
val lookup_method : inst:class_instance -> name:method_name -> option expr

(** Full method resolution: find instance and lookup method *)
val resolve_method :
    cls:class_name ->
    ty:brrr_type ->
    method:method_name ->
    env:class_env ->
    option expr

(** ============================================================================
    TYPE SUBSTITUTION IN CONSTRAINED TYPES
    ============================================================================ *)

(**
 * Apply a type substitution to a constrained type.
 *)
val apply_subst_to_constrained :
    subst:list (type_var & brrr_type) ->
    ct:constrained_type ->
    constrained_type

(** ============================================================================
    STANDARD TYPE CLASSES
    ============================================================================ *)

(** Eq class: equality comparison *)
val eq_class : type_class

(** Ord class: ordering comparison, extends Eq *)
val ord_class : type_class

(** Show class: string representation *)
val show_class : type_class

(** Functor class: mappable containers *)
val functor_class : type_class

(** Applicative class: extends Functor with pure and apply *)
val applicative_class : type_class

(** Monad class: extends Applicative with bind *)
val monad_class : type_class

(** Standard class environment with Eq, Ord, Show, Functor, Applicative, Monad *)
val standard_classes : class_env

(** ============================================================================
    INSTANCE CHECKING
    ============================================================================ *)

(** Check that an instance provides all required methods *)
val has_all_methods : required:list class_method -> provided:list method_impl -> bool

(**
 * Check that an instance is well-formed:
 *   1. The class exists
 *   2. All superclass instances exist
 *   3. All required methods are implemented
 *)
val instance_well_formed : inst:class_instance -> env:class_env -> bool

(** ============================================================================
    COHERENCE - No overlapping instances
    ============================================================================ *)

(** Check if two instances overlap (same class and type) *)
val instances_overlap : i1:class_instance -> i2:class_instance -> bool

(** Check if a new instance would overlap with existing instances *)
val no_overlapping_instances : new_inst:class_instance -> existing:list class_instance -> bool

(** Check coherence of entire environment *)
val env_coherent : env:class_env -> bool

(** ============================================================================
    SAFE INSTANCE ADDITION
    ============================================================================ *)

(** Result type for safe instance addition *)
type add_instance_result =
  | AddInstanceOk : env:class_env -> add_instance_result
  | AddInstanceOverlap : existing_type:brrr_type -> add_instance_result
  | AddInstanceClassNotFound : cls:class_name -> add_instance_result
  | AddInstanceMissingSuperclass : cls:class_name -> super:class_name -> add_instance_result
  | AddInstanceMissingMethod : method:method_name -> add_instance_result

(** Find which method is missing from an instance *)
val find_missing_method : required:list class_method -> provided:list method_impl -> option method_name

(**
 * Safe instance addition with coherence checking.
 *
 * Verifies:
 *   1. No overlapping instances exist
 *   2. The class exists
 *   3. All superclass instances exist
 *   4. All required methods are implemented
 *)
val add_instance_safe : i:class_instance -> env:class_env -> add_instance_result

(** Convenience function: add instance if safe *)
val add_instance_checked : i:class_instance -> env:class_env -> option class_env

(** ============================================================================
    DICTIONARY PASSING TRANSFORMATION
    ============================================================================ *)

(** A dictionary type for a class instance *)
noeq type class_dict = {
  dict_class : class_name;
  dict_type  : brrr_type;
  dict_methods : list method_impl;
}

(** Convert an instance to a dictionary *)
val instance_to_dict : inst:class_instance -> class_dict

(** ============================================================================
    SIZE FUNCTIONS (for termination measures)
    ============================================================================ *)

(** Size of a class constraint list *)
val constraint_list_size : cs:list class_constraint -> nat

(** Size of a type class *)
val type_class_size : c:type_class -> nat

(** Size of class environment *)
val class_env_size : env:class_env -> nat

(** ============================================================================
    DERIVED CONSTRAINTS FROM SUPERCLASSES
    ============================================================================ *)

(**
 * Given a constraint C a, derive all superclass constraints.
 *)
val derive_superclass_constraints :
    c:class_constraint ->
    classes:list type_class ->
    list class_constraint

(** Result type for constraint derivation *)
type derive_result =
  | DeriveComplete : constraints:list class_constraint -> derive_result
  | DeriveFuelExhausted : partial:list class_constraint -> derive_result

(**
 * Derive all constraints including transitive superclasses.
 * Returns DeriveComplete or DeriveFuelExhausted with partial results.
 *)
val derive_all_constraints_safe :
    constraints:list class_constraint ->
    classes:list type_class ->
    fuel:nat ->
    Tot derive_result (decreases fuel)

(** Convenience function returning option *)
val derive_all_constraints_opt :
    constraints:list class_constraint ->
    classes:list type_class ->
    fuel:nat ->
    Tot (option (list class_constraint)) (decreases fuel)

(** Legacy function for backward compatibility *)
val derive_all_constraints :
    constraints:list class_constraint ->
    classes:list type_class ->
    fuel:nat ->
    Tot (list class_constraint) (decreases fuel)

(** ============================================================================
    FINAL VALIDATION
    ============================================================================ *)

(**
 * Complete validation of a class environment.
 *)
val validate_class_env : env:class_env -> bool

(** Validation result type with detailed error information *)
type validation_result =
  | ValidationOk : validation_result
  | ValidationCycleError : offending_class:class_name -> validation_result
  | ValidationMissingInstance : cls:class_name -> ty:brrr_type -> validation_result
  | ValidationOverlapping : cls:class_name -> ty:brrr_type -> validation_result
  | ValidationMissingMethod : inst:class_name -> method:method_name -> validation_result

(** Detailed validation with error reporting *)
val validate_class_env_detailed : env:class_env -> validation_result

(** ============================================================================
    MODULE OWNERSHIP FOR ORPHAN RULES
    ============================================================================ *)

(** Module identifier for tracking instance ownership *)
type module_id = string

(** Ownership information for a class or type *)
noeq type ownership_info = {
  oi_module : module_id;
}

(** Extended class environment with ownership tracking *)
noeq type class_env_ext = {
  cee_base : class_env;
  cee_class_owners : list (class_name & module_id);
  cee_type_owners : list (type_name & module_id);
}

(** Lookup the owning module for a class *)
val lookup_class_owner : cls:class_name -> owners:list (class_name & module_id) -> option module_id

(** Lookup the owning module for a type *)
val lookup_type_owner : ty:type_name -> owners:list (type_name & module_id) -> option module_id

(** Extract the head type name from a type *)
val head_type_name : ty:brrr_type -> option type_name

(** ============================================================================
    TYPE UNIFICATION FOR OVERLAP DETECTION
    ============================================================================ *)

(** Type substitution: maps type variables to types *)
type type_subst = list (type_var & brrr_type)

(** Unification failure reason *)
type unify_fail_reason =
  | ClashConstructor
  | ClashPrimitive
  | ClashArity
  | OccursCheck
  | ClashEffect

(** Unification result *)
type unify_result =
  | UOk : subst:type_subst -> unify_result
  | UFail : t1:brrr_type -> t2:brrr_type -> reason:unify_fail_reason -> unify_result

(** Apply a substitution to a type *)
val apply_subst : subst:type_subst -> t:brrr_type -> Tot brrr_type (decreases t)

(** Compose two substitutions *)
val compose_subst : s1:type_subst -> s2:type_subst -> type_subst

(** Check if a type variable occurs in a type (occurs check) *)
val occurs_in : v:type_var -> t:brrr_type -> Tot bool (decreases t)

(** Maximum unification depth *)
val max_unify_depth : nat

(** Unify two types, returning the most general unifier or failure *)
val unify_types : t1:brrr_type -> t2:brrr_type -> depth:nat
    -> Tot unify_result (decreases depth)

(** Convenience function for unification with default depth *)
val unify : t1:brrr_type -> t2:brrr_type -> unify_result

(** ============================================================================
    COHERENCE RESULT TYPE
    ============================================================================ *)

(** Coherence check result - distinct from well-formedness *)
type coherence_result =
  | Coherent
  | Overlapping : i1:class_instance -> i2:class_instance -> unified_type:brrr_type -> coherence_result
  | Orphan : inst:class_instance -> coherence_result

(** ============================================================================
    OVERLAP DETECTION WITH UNIFICATION
    ============================================================================ *)

(**
 * Check if two instances overlap (same class, unifiable types).
 * Returns Some unified_type if they overlap, None otherwise.
 *)
val instances_overlap_with_unification : i1:class_instance -> i2:class_instance -> option brrr_type

(** Find first overlapping pair in a list of instances *)
val find_overlapping_pair : instances:list class_instance
    -> option (class_instance & class_instance & brrr_type)

(** ============================================================================
    ORPHAN RULE CHECKING
    ============================================================================ *)

(** Check if a module owns a class *)
val owns_class : mod_id:module_id -> cls:class_name -> owners:list (class_name & module_id) -> bool

(** Check if a module owns a type *)
val owns_type : mod_id:module_id -> ty:brrr_type -> owners:list (type_name & module_id) -> bool

(** Check if an instance is an orphan in the given module *)
val is_orphan_instance : inst:class_instance -> current_mod:module_id
    -> class_owners:list (class_name & module_id)
    -> type_owners:list (type_name & module_id) -> bool

(** Find first orphan instance in a list *)
val find_orphan : instances:list class_instance -> current_mod:module_id
    -> class_owners:list (class_name & module_id)
    -> type_owners:list (type_name & module_id) -> option class_instance

(** ============================================================================
    MAIN COHERENCE CHECK
    ============================================================================ *)

(** Check coherence of a list of instances *)
val check_coherence_instances : instances:list class_instance
    -> current_mod:module_id
    -> class_owners:list (class_name & module_id)
    -> type_owners:list (type_name & module_id) -> coherence_result

(** Check coherence of an extended class environment *)
val check_coherence : env:class_env_ext -> current_mod:module_id -> coherence_result

(** Simplified coherence check without orphan rules *)
val check_coherence_simple : env:class_env -> coherence_result

(** ============================================================================
    COHERENCE DECIDABILITY PROOFS
    ============================================================================ *)

(** Lemma: check_coherence always returns one of the three outcomes *)
val coherence_decidable : instances:list class_instance -> current_mod:module_id ->
  class_owners:list (class_name & module_id) -> type_owners:list (type_name & module_id) ->
  Lemma (ensures
           Coherent? (check_coherence_instances instances current_mod class_owners type_owners) \/
           Overlapping? (check_coherence_instances instances current_mod class_owners type_owners) \/
           Orphan? (check_coherence_instances instances current_mod class_owners type_owners))

(** Helper: count matching instances for a type *)
val count_matching_instances : cls:class_name -> ty:brrr_type -> instances:list class_instance -> nat

(** Helper: at most one instance matches a given type *)
val at_most_one_matching : #a:Type -> p:(a -> bool) -> l:list a -> bool

(**
 * Lemma: If coherent, at most one instance matches any given type.
 *)
val coherence_implies_unique_selection : instances:list class_instance -> ty:brrr_type -> cls:class_name ->
  Lemma (requires Coherent? (check_coherence_simple { ce_classes = []; ce_instances = instances }))
        (ensures at_most_one_matching (fun i -> instance_matches i cls ty) instances)

(** Lemma: Unification is decidable *)
val unify_decidable : t1:brrr_type -> t2:brrr_type ->
  Lemma (ensures UOk? (unify t1 t2) \/ UFail? (unify t1 t2))
        [SMTPat (unify t1 t2)]

(** Lemma: Orphan checking is decidable *)
val orphan_check_decidable : inst:class_instance -> mod_id:module_id ->
  class_owners:list (class_name & module_id) -> type_owners:list (type_name & module_id) ->
  Lemma (ensures is_orphan_instance inst mod_id class_owners type_owners = true \/
                 is_orphan_instance inst mod_id class_owners type_owners = false)

(** ============================================================================
    SAFE INSTANCE ADDITION WITH COHERENCE
    ============================================================================ *)

(** Result of adding instance with coherence checking *)
type add_instance_coherent_result =
  | AddCoherentOk : env:class_env -> add_instance_coherent_result
  | AddCoherentOverlap : with_inst:class_instance -> unified_type:brrr_type -> add_instance_coherent_result
  | AddCoherentOrphan : add_instance_coherent_result
  | AddCoherentWellFormednessError : error:add_instance_result -> add_instance_coherent_result

(** Check if new instance overlaps with any existing instance *)
val check_no_overlap_with_existing : new_inst:class_instance -> existing:list class_instance
    -> option (class_instance & brrr_type)

(** Add instance with both well-formedness AND coherence checking *)
val add_instance_coherent : i:class_instance -> env:class_env
    -> current_mod:module_id
    -> class_owners:list (class_name & module_id)
    -> type_owners:list (type_name & module_id) -> add_instance_coherent_result

(** ============================================================================
    COMBINED VALIDATION: WELL-FORMEDNESS + COHERENCE
    ============================================================================ *)

(** Combined validation result *)
type full_validation_result =
  | FullValidationOk : full_validation_result
  | FullValidationWellFormedness : error:validation_result -> full_validation_result
  | FullValidationCoherence : error:coherence_result -> full_validation_result

(** Full validation: well-formedness then coherence *)
val validate_full : env:class_env -> full_validation_result

(** Full validation with extended environment (includes orphan rules) *)
val validate_full_ext : env:class_env_ext -> current_mod:module_id -> full_validation_result

(** Lemma: Full validation is decidable *)
val full_validation_decidable : env:class_env ->
  Lemma (ensures FullValidationOk? (validate_full env) \/
                 FullValidationWellFormedness? (validate_full env) \/
                 FullValidationCoherence? (validate_full env))
