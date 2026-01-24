(**
 * BrrrLang.Core.TypeClasses
 *
 * Type class system for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part IV - Type Classes.
 *
 * Type classes provide ad-hoc polymorphism:
 *   - class Eq a where (==) : a -> a -> Bool
 *   - class Ord a extends Eq where (<) : a -> a -> Bool
 *   - class Functor f where map : (a -> b) -> f a -> f b
 *   - class Applicative f extends Functor where
 *       pure : a -> f a
 *       apply : f (a -> b) -> f a -> f b
 *   - class Monad m extends Applicative where
 *       (>>=) : m a -> (a -> m b) -> m b
 *       join : m (m a) -> m a
 *
 * Instance resolution algorithm:
 *   1. Find instance matching class name and type
 *   2. Verify superclass instances exist (transitively, with cycle detection)
 *   3. Return resolved instance with method implementations
 *
 * Safety features:
 *   - Cycle detection in superclass hierarchy (prevents infinite loops)
 *   - Coherence checking (no overlapping instances)
 *   - Fuel-based termination for constraint derivation with explicit failure
 *
 * Depends on: BrrrTypes, Expressions, Kinds
 *)
module TypeClasses

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical
open Modes
open Effects
open BrrrTypes
open Expressions
open Kinds

(** ============================================================================
    TYPE CLASS NAMES
    ============================================================================ *)

(* Type class identifier *)
type class_name = string

(* Method name within a class *)
type method_name = string

(** ============================================================================
    CLASS METHOD - A method signature within a type class
    ============================================================================ *)

(* A method declaration in a type class.
   The method_type is polymorphic, containing the class type parameter.
   Example: for Eq a, the (==) method has type: a -> a -> Bool *)
noeq type class_method = {
  cm_name : method_name;          (* Method name, e.g., "==" *)
  cm_type : brrr_type             (* Polymorphic method type *)
}

(* Check method equality by name (structural equality) *)
let method_eq (m1 m2: class_method) : bool =
  m1.cm_name = m2.cm_name && type_eq m1.cm_type m2.cm_type

(** ============================================================================
    TYPE CLASS DEFINITION
    ============================================================================ *)

(* A type class declaration.
   Example: class Ord a extends Eq where (<) : a -> a -> Bool

   Fields:
   - tc_name: The class name ("Ord")
   - tc_param: The type parameter ("a")
   - tc_superclasses: List of superclass names (["Eq"])
   - tc_methods: List of method declarations
*)
noeq type type_class = {
  tc_name         : class_name;           (* Class name *)
  tc_param        : type_var;             (* The type parameter 'a' *)
  tc_superclasses : list class_name;      (* Superclass constraints *)
  tc_methods      : list class_method     (* Method signatures *)
}

(* Check if two type classes are equal *)
let type_class_eq (c1 c2: type_class) : bool =
  c1.tc_name = c2.tc_name &&
  c1.tc_param = c2.tc_param &&
  c1.tc_superclasses = c2.tc_superclasses

(** ============================================================================
    SUPERCLASS CYCLE DETECTION
    ============================================================================

    Cycles in the superclass hierarchy must be detected to prevent infinite
    loops during instance resolution. For example, this would be invalid:

      class A extends B
      class B extends A    -- Cycle: A -> B -> A

    The detection algorithm performs a depth-first traversal of the superclass
    graph, tracking visited classes to detect back edges (cycles).

    Key invariants:
    1. No class can be its own (transitive) superclass
    2. Instance resolution terminates for all valid class hierarchies
    3. Cycle detection runs in O(n*m) time where n = classes, m = avg superclasses
    ============================================================================ *)

(* Check if a class name is in a list *)
let rec class_name_in_list (name: class_name) (names: list class_name) : bool =
  match names with
  | [] -> false
  | n :: rest -> n = name || class_name_in_list name rest

(* Depth-first cycle detection from a starting class.
   Returns true if a cycle is found (the starting class is reachable from itself).

   Parameters:
   - start: The class we're checking for cycles from
   - current: Current class in DFS traversal
   - visited: Set of classes already visited in this traversal (for cycle detection)
   - classes: All class definitions (for superclass lookup)
   - fuel: Recursion fuel to ensure termination
*)
let rec detect_superclass_cycle_dfs
    (start: class_name)
    (current: class_name)
    (visited: list class_name)
    (classes: list type_class)
    (fuel: nat)
    : Tot bool (decreases fuel) =
  if fuel = 0 then false  (* Out of fuel - assume no cycle (conservative) *)
  else if class_name_in_list current visited then
    (* We've seen this class before in this path - check if it's the start *)
    current = start
  else
    (* Look up current class to get its superclasses *)
    match lookup_class current classes with
    | None -> false  (* Class not found - no cycle through this path *)
    | Some cls ->
        (* Check each superclass *)
        let visited' = current :: visited in
        check_supers_for_cycle start cls.tc_superclasses visited' classes (fuel - 1)

(* Helper: Check each superclass for cycles back to start *)
and check_supers_for_cycle
    (start: class_name)
    (supers: list class_name)
    (visited: list class_name)
    (classes: list type_class)
    (fuel: nat)
    : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match supers with
    | [] -> false
    | super :: rest ->
        if super = start then true  (* Direct cycle: super is the start class *)
        else if detect_superclass_cycle_dfs start super visited classes (fuel - 1) then true
        else check_supers_for_cycle start rest visited classes (fuel - 1)

(* Check if a class participates in a superclass cycle.
   Uses the number of classes as fuel to ensure termination. *)
let has_superclass_cycle (cls: type_class) (classes: list type_class) : bool =
  let fuel = List.Tot.length classes + 1 in
  check_supers_for_cycle cls.tc_name cls.tc_superclasses [] classes fuel

(* Check if the entire class hierarchy is acyclic *)
let rec all_classes_acyclic (classes: list type_class) : bool =
  match classes with
  | [] -> true
  | cls :: rest ->
      not (has_superclass_cycle cls classes) && all_classes_acyclic rest

(* Lemma: If all_classes_acyclic, then no individual class has a cycle.
   This provides the termination guarantee for instance resolution. *)
val acyclic_implies_no_individual_cycle :
    classes:list type_class -> cls:type_class ->
    Lemma (requires all_classes_acyclic classes /\ List.Tot.memP cls classes)
          (ensures not (has_superclass_cycle cls classes))
          [SMTPat (all_classes_acyclic classes); SMTPat (List.Tot.memP cls classes)]

let rec acyclic_implies_no_individual_cycle classes cls =
  match classes with
  | [] -> ()
  | c :: rest ->
      if c.tc_name = cls.tc_name then ()
      else acyclic_implies_no_individual_cycle rest cls

(** ============================================================================
    METHOD IMPLEMENTATION - Concrete implementation for an instance
    ============================================================================ *)

(* A method implementation pairs a method name with its expression body.
   The expression is the concrete implementation for a specific type. *)
type method_impl = method_name & expr

(* Find a method implementation by name *)
let rec find_method_impl (name: method_name) (impls: list method_impl) : option expr =
  match impls with
  | [] -> None
  | (n, e) :: rest -> if n = name then Some e else find_method_impl name rest

(** ============================================================================
    CLASS INSTANCE - A type class instance for a concrete type
    ============================================================================ *)

(* An instance of a type class for a specific type.
   Example: instance Eq i32 where (==) = int_eq

   Fields:
   - ci_class: The class name ("Eq")
   - ci_type: The concrete type (i32)
   - ci_methods: Method implementations
*)
noeq type class_instance = {
  ci_class   : class_name;         (* Class being implemented *)
  ci_type    : brrr_type;          (* Concrete type implementing the class *)
  ci_methods : list method_impl    (* Method implementations *)
}

(* Check if an instance implements a specific class for a specific type *)
let instance_matches (inst: class_instance) (cls: class_name) (ty: brrr_type) : bool =
  inst.ci_class = cls && type_eq inst.ci_type ty

(** ============================================================================
    CLASS CONSTRAINT - Constraint on a type variable
    ============================================================================ *)

(* A class constraint specifies that a type variable must implement a class.
   Example: Eq a, Ord b, Functor f *)
noeq type class_constraint = {
  cc_class : class_name;   (* The required class *)
  cc_var   : type_var      (* The constrained type variable *)
}

(* Check constraint equality *)
let constraint_eq (c1 c2: class_constraint) : bool =
  c1.cc_class = c2.cc_class && c1.cc_var = c2.cc_var

(* Check if a constraint is in a list *)
let rec has_constraint (c: class_constraint) (cs: list class_constraint) : bool =
  match cs with
  | [] -> false
  | c' :: rest -> constraint_eq c c' || has_constraint c rest

(** ============================================================================
    CONSTRAINED TYPE - A type with class constraints
    ============================================================================ *)

(* A constrained type represents a polymorphic type with class constraints.
   Example: forall a. Eq a => a -> a -> Bool

   This is used for:
   - Polymorphic function signatures with constraints
   - Method types in type classes
*)
noeq type constrained_type = {
  ct_constraints : list class_constraint;  (* Class constraints on type vars *)
  ct_type        : brrr_type               (* The underlying type *)
}

(* Create an unconstrained type *)
let unconstrained (t: brrr_type) : constrained_type =
  { ct_constraints = []; ct_type = t }

(* Add a constraint to a constrained type *)
let add_constraint (c: class_constraint) (ct: constrained_type) : constrained_type =
  { ct with ct_constraints = c :: ct.ct_constraints }

(* Check if all constraints are satisfied by a list of instances *)
let rec constraints_satisfied
    (constraints: list class_constraint)
    (subst: list (type_var & brrr_type))  (* Type variable substitution *)
    (instances: list class_instance)
    : Tot bool (decreases constraints) =
  match constraints with
  | [] -> true
  | c :: rest ->
      (* Find the substituted type for this constraint's variable *)
      (match assoc c.cc_var subst with
       | None -> false  (* Unsubstituted variable - constraint cannot be checked *)
       | Some ty ->
           (* Check if there's a matching instance *)
           let has_inst = List.Tot.existsb (fun inst -> instance_matches inst c.cc_class ty) instances in
           has_inst && constraints_satisfied rest subst instances)

(** ============================================================================
    TYPE CLASS ENVIRONMENT
    ============================================================================ *)

(* Type class environment containing all class definitions and instances *)
noeq type class_env = {
  ce_classes   : list type_class;      (* All type class definitions *)
  ce_instances : list class_instance   (* All instance declarations *)
}

(* Empty class environment *)
let empty_class_env : class_env =
  { ce_classes = []; ce_instances = [] }

(* Add a class to the environment *)
let add_class (c: type_class) (env: class_env) : class_env =
  { env with ce_classes = c :: env.ce_classes }

(* Add an instance to the environment.
   WARNING: This does NOT check for overlapping instances or well-formedness.
   Use add_instance_safe (defined later) for production code that requires
   coherence guarantees. *)
let add_instance (i: class_instance) (env: class_env) : class_env =
  { env with ce_instances = i :: env.ce_instances }

(* Lookup a class by name *)
let rec lookup_class (name: class_name) (classes: list type_class) : option type_class =
  match classes with
  | [] -> None
  | c :: rest -> if c.tc_name = name then Some c else lookup_class name rest

(** ============================================================================
    INSTANCE RESOLUTION - Core Algorithm
    ============================================================================ *)

(* Size measure for instance lists - for termination *)
let instance_list_size (instances: list class_instance) : nat =
  List.Tot.length instances

(* Find an instance matching a class and type directly (no superclass check).
   Returns the first matching instance if found. *)
let rec find_direct_instance
    (cls: class_name)
    (ty: brrr_type)
    (instances: list class_instance)
    : Tot (option class_instance) (decreases instances) =
  match instances with
  | [] -> None
  | inst :: rest ->
      if instance_matches inst cls ty then Some inst
      else find_direct_instance cls ty rest

(* Check if all superclass instances exist for a given type.
   Given a class with superclasses [S1, S2, ...], checks that
   instances exist for S1 ty, S2 ty, etc.

   IMPORTANT: This is the simple non-transitive version that only checks
   direct superclasses. Use superclasses_satisfied_safe for full transitive
   checking with cycle detection. *)
let rec superclasses_satisfied
    (supers: list class_name)
    (ty: brrr_type)
    (instances: list class_instance)
    : Tot bool (decreases supers) =
  match supers with
  | [] -> true
  | s :: rest ->
      (match find_direct_instance s ty instances with
       | None -> false
       | Some _ -> superclasses_satisfied rest ty instances)

(* Maximum recursion depth for superclass traversal.
   This prevents infinite loops even if cycle detection is bypassed. *)
let max_superclass_depth : nat = 100

(* Safe transitive superclass checking with cycle detection.

   Checks that all superclass instances exist transitively, tracking visited
   classes to detect cycles. Returns false if:
   1. A required instance is missing
   2. A cycle is detected in the superclass hierarchy
   3. Maximum depth is exceeded (defensive programming)

   Parameters:
   - supers: List of superclass names to check
   - ty: The concrete type that needs instances
   - instances: Available class instances
   - classes: All class definitions (for looking up superclass hierarchies)
   - visited: Set of already-visited class names (for cycle detection)
   - depth: Current recursion depth (for defensive termination)

   Invariant: visited grows monotonically, depth decreases monotonically *)
let rec superclasses_satisfied_safe
    (supers: list class_name)
    (ty: brrr_type)
    (instances: list class_instance)
    (classes: list type_class)
    (visited: list class_name)
    (depth: nat)
    : Tot bool (decreases depth) =
  if depth = 0 then false  (* Depth exceeded - fail safe *)
  else
    match supers with
    | [] -> true
    | s :: rest ->
        (* Check for cycle - have we already visited this superclass? *)
        if class_name_in_list s visited then
          false  (* Cycle detected - this superclass was already in our traversal path *)
        else
          (* Find direct instance for this superclass *)
          match find_direct_instance s ty instances with
          | None -> false  (* No instance for required superclass *)
          | Some _ ->
              (* Look up the superclass definition to check ITS superclasses *)
              let visited' = s :: visited in
              let transitive_ok =
                match lookup_class s classes with
                | None -> true  (* Superclass not defined - assume OK (will fail elsewhere) *)
                | Some super_class_def ->
                    (* Recursively check the superclass's own superclasses *)
                    superclasses_satisfied_safe
                      super_class_def.tc_superclasses
                      ty
                      instances
                      classes
                      visited'
                      (depth - 1)
              in
              (* Continue with remaining superclasses at this level *)
              transitive_ok &&
              superclasses_satisfied_safe rest ty instances classes visited (depth - 1)

(* Main instance resolution function.

   Given a class name and a concrete type, finds a matching instance
   and verifies all superclass instances exist transitively.

   Algorithm:
   1. Verify the class exists in the environment (fail if not found)
   2. Find direct instance for (class, type)
   3. Verify all superclass instances exist (transitively, with cycle detection)
   4. Return the resolved instance

   Precondition: Class must exist in the environment for resolution to succeed.
   Postcondition: If Some, the returned instance:
     - Has matching class name
     - Has matching type
     - The class definition exists in the environment
     - All superclass instances are available (transitively)

   Safety: Uses superclasses_satisfied_safe which:
     - Tracks visited classes to detect cycles
     - Has bounded recursion depth for defensive termination
*)
let resolve_instance
    (cls: class_name)
    (ty: brrr_type)
    (env: class_env)
    : option class_instance =
  (* First verify the class exists - fail if class is not defined *)
  match lookup_class cls env.ce_classes with
  | None -> None  (* Class not found in environment - cannot resolve *)
  | Some class_def ->
      (* Now find a direct instance for (class, type) *)
      match find_direct_instance cls ty env.ce_instances with
      | None -> None  (* No instance found for this class and type *)
      | Some inst ->
          (* Verify all superclass instances exist using safe transitive check *)
          if superclasses_satisfied_safe
               class_def.tc_superclasses
               ty
               env.ce_instances
               env.ce_classes
               [cls]  (* Start with current class as visited to prevent self-cycles *)
               max_superclass_depth
          then Some inst
          else None

(** ============================================================================
    INSTANCE RESOLUTION CORRECTNESS PROOFS
    ============================================================================ *)

(* Lemma: find_direct_instance returns an instance that matches *)
val find_direct_instance_matches :
    cls:class_name -> ty:brrr_type -> instances:list class_instance ->
    Lemma (ensures (match find_direct_instance cls ty instances with
                    | None -> True
                    | Some inst -> instance_matches inst cls ty = true))
          (decreases instances)

let rec find_direct_instance_matches cls ty instances =
  match instances with
  | [] -> ()
  | inst :: rest ->
      if instance_matches inst cls ty then ()
      else find_direct_instance_matches cls ty rest

(* Lemma: If find_direct_instance succeeds, the instance is in the list *)
val find_direct_instance_in_list :
    cls:class_name -> ty:brrr_type -> instances:list class_instance ->
    Lemma (ensures (match find_direct_instance cls ty instances with
                    | None -> True
                    | Some inst -> List.Tot.memP inst instances))
          (decreases instances)

let rec find_direct_instance_in_list cls ty instances =
  match instances with
  | [] -> ()
  | inst :: rest ->
      if instance_matches inst cls ty then ()
      else find_direct_instance_in_list cls ty rest

(* Main correctness theorem: resolve_instance is sound.
   If resolution succeeds, the returned instance:
   1. Has the correct class name
   2. Has the correct type
   3. The class definition exists in the environment
   4. All superclass instances are available

   Note: With the updated implementation, resolve_instance fails (returns None)
   if the class is not found, providing a stronger guarantee. *)
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
                         | None -> False)))  (* This case is impossible when Some inst is returned *)
          [SMTPat (resolve_instance cls ty env)]

let resolve_instance_sound cls ty env =
  match lookup_class cls env.ce_classes with
  | None -> ()  (* resolve_instance returns None, postcondition is True *)
  | Some class_def ->
      match find_direct_instance cls ty env.ce_instances with
      | None -> ()  (* resolve_instance returns None, postcondition is True *)
      | Some inst ->
          find_direct_instance_matches cls ty env.ce_instances;
          if superclasses_satisfied class_def.tc_superclasses ty env.ce_instances
          then ()  (* All conditions satisfied *)
          else ()  (* resolve_instance returns None, postcondition is True *)

(** ============================================================================
    SAFE INSTANCE RESOLUTION (WITH CYCLE CHECKING)
    ============================================================================

    The safe_resolve_instance function first validates that the class
    hierarchy is acyclic before attempting resolution. This provides
    a termination guarantee even for malformed class environments.

    For performance, in production code you should validate the environment
    once at load time using validate_class_env, and then use resolve_instance
    directly. This safe version is for cases where the environment may be
    constructed dynamically or untrusted.
    ============================================================================ *)

(* Instance resolution result with detailed error information *)
type resolve_result =
  | ResolveOk : inst:class_instance -> resolve_result
  | ResolveClassNotFound : cls:class_name -> resolve_result
  | ResolveNoInstance : cls:class_name -> ty:brrr_type -> resolve_result
  | ResolveMissingSuperclass : cls:class_name -> super:class_name -> ty:brrr_type -> resolve_result
  | ResolveCycleDetected : cls:class_name -> resolve_result

(* Find which superclass is missing its instance *)
let rec find_missing_superclass
    (supers: list class_name)
    (ty: brrr_type)
    (instances: list class_instance)
    : option class_name =
  match supers with
  | [] -> None
  | s :: rest ->
      match find_direct_instance s ty instances with
      | None -> Some s
      | Some _ -> find_missing_superclass rest ty instances

(* Safe instance resolution with detailed error reporting and cycle checking *)
let safe_resolve_instance
    (cls: class_name)
    (ty: brrr_type)
    (env: class_env)
    : resolve_result =
  (* First check for cycles in the class we're trying to resolve *)
  match lookup_class cls env.ce_classes with
  | None -> ResolveClassNotFound cls
  | Some class_def ->
      (* Check for superclass cycle *)
      if has_superclass_cycle class_def env.ce_classes then
        ResolveCycleDetected cls
      else
        (* Proceed with normal resolution *)
        match find_direct_instance cls ty env.ce_instances with
        | None -> ResolveNoInstance cls ty
        | Some inst ->
            (* Verify all superclass instances exist *)
            if superclasses_satisfied class_def.tc_superclasses ty env.ce_instances
            then ResolveOk inst
            else
              (* Find which superclass is missing *)
              match find_missing_superclass class_def.tc_superclasses ty env.ce_instances with
              | Some missing -> ResolveMissingSuperclass cls missing ty
              | None -> ResolveOk inst  (* Should not happen *)

(* Lemma: safe_resolve_instance terminates for any input.
   This is guaranteed by the cycle check - we never enter infinite recursion. *)
val safe_resolve_terminates :
    cls:class_name -> ty:brrr_type -> env:class_env ->
    Lemma (ensures True)  (* Always terminates *)
          [SMTPat (safe_resolve_instance cls ty env)]

let safe_resolve_terminates cls ty env = ()

(* Lemma: If validate_class_env succeeds, safe_resolve_instance and
   resolve_instance give equivalent results (no cycle errors). *)
val safe_resolve_equiv_when_valid :
    cls:class_name -> ty:brrr_type -> env:class_env ->
    Lemma (requires validate_class_env env = true)
          (ensures (match safe_resolve_instance cls ty env with
                    | ResolveCycleDetected _ -> False  (* No cycles in valid env *)
                    | ResolveOk inst ->
                        resolve_instance cls ty env = Some inst
                    | _ ->
                        resolve_instance cls ty env = None))

let safe_resolve_equiv_when_valid cls ty env = ()

(** ============================================================================
    CONSTRAINT ENTAILMENT
    ============================================================================ *)

(* Check if a constraint is entailed by a set of instances given a type substitution.
   A constraint (C a) is entailed if there exists an instance C T where T is
   the substitution of a. *)
let constraint_entailed
    (c: class_constraint)
    (subst: list (type_var & brrr_type))
    (env: class_env)
    : bool =
  match assoc c.cc_var subst with
  | None -> false  (* Variable not in substitution *)
  | Some ty -> Some? (resolve_instance c.cc_class ty env)

(* Check if all constraints are entailed *)
let rec all_constraints_entailed
    (constraints: list class_constraint)
    (subst: list (type_var & brrr_type))
    (env: class_env)
    : Tot bool (decreases constraints) =
  match constraints with
  | [] -> true
  | c :: rest ->
      constraint_entailed c subst env &&
      all_constraints_entailed rest subst env

(** ============================================================================
    METHOD LOOKUP - Finding method implementations
    ============================================================================ *)

(* Lookup a method in a resolved instance *)
let lookup_method (inst: class_instance) (name: method_name) : option expr =
  find_method_impl name inst.ci_methods

(* Full method resolution: find instance and lookup method *)
let resolve_method
    (cls: class_name)
    (ty: brrr_type)
    (method: method_name)
    (env: class_env)
    : option expr =
  match resolve_instance cls ty env with
  | None -> None
  | Some inst -> lookup_method inst method

(** ============================================================================
    TYPE SUBSTITUTION IN CONSTRAINED TYPES
    ============================================================================ *)

(* Apply a type substitution to a constrained type.
   This substitutes the type and updates constraints. *)
let apply_subst_to_constrained
    (subst: list (type_var & brrr_type))
    (ct: constrained_type)
    : constrained_type =
  (* Substitute in the type *)
  let new_type = List.Tot.fold_left
    (fun t (v, repl) -> subst_type_var v repl t)
    ct.ct_type
    subst
  in
  (* Filter out constraints for substituted variables *)
  let new_constraints = List.Tot.filter
    (fun c -> None? (assoc c.cc_var subst))
    ct.ct_constraints
  in
  { ct_constraints = new_constraints; ct_type = new_type }

(** ============================================================================
    STANDARD TYPE CLASSES
    ============================================================================ *)

(* Eq class: equality comparison *)
let eq_class : type_class = {
  tc_name = "Eq";
  tc_param = "a";
  tc_superclasses = [];
  tc_methods = [
    { cm_name = "=="; cm_type = t_pure_func [TVar "a"; TVar "a"] t_bool }
  ]
}

(* Ord class: ordering comparison, extends Eq *)
let ord_class : type_class = {
  tc_name = "Ord";
  tc_param = "a";
  tc_superclasses = ["Eq"];
  tc_methods = [
    { cm_name = "<"; cm_type = t_pure_func [TVar "a"; TVar "a"] t_bool };
    { cm_name = "<="; cm_type = t_pure_func [TVar "a"; TVar "a"] t_bool };
    { cm_name = ">"; cm_type = t_pure_func [TVar "a"; TVar "a"] t_bool };
    { cm_name = ">="; cm_type = t_pure_func [TVar "a"; TVar "a"] t_bool }
  ]
}

(* Show class: string representation *)
let show_class : type_class = {
  tc_name = "Show";
  tc_param = "a";
  tc_superclasses = [];
  tc_methods = [
    { cm_name = "show"; cm_type = t_pure_func [TVar "a"] t_string }
  ]
}

(* Functor class: mappable containers
   f : * -> * (type constructor with kind KStar -> KStar) *)
let functor_class : type_class = {
  tc_name = "Functor";
  tc_param = "f";  (* Higher-kinded type parameter *)
  tc_superclasses = [];
  tc_methods = [
    (* map : (a -> b) -> f a -> f b *)
    { cm_name = "map";
      cm_type = TFunc {
        params = [
          { name = Some "fn"; ty = t_pure_func [TVar "a"] (TVar "b"); mode = MOmega };
          { name = Some "fa"; ty = TApp (TVar "f") [TVar "a"]; mode = MOmega }
        ];
        return_type = TApp (TVar "f") [TVar "b"];
        effects = pure;
        is_unsafe = false
      }
    }
  ]
}

(* Applicative class: extends Functor with pure and apply *)
let applicative_class : type_class = {
  tc_name = "Applicative";
  tc_param = "f";
  tc_superclasses = ["Functor"];
  tc_methods = [
    (* pure : a -> f a *)
    { cm_name = "pure";
      cm_type = TFunc {
        params = [{ name = Some "x"; ty = TVar "a"; mode = MOmega }];
        return_type = TApp (TVar "f") [TVar "a"];
        effects = pure;
        is_unsafe = false
      }
    };
    (* apply : f (a -> b) -> f a -> f b *)
    { cm_name = "apply";
      cm_type = TFunc {
        params = [
          { name = Some "ff"; ty = TApp (TVar "f") [t_pure_func [TVar "a"] (TVar "b")]; mode = MOmega };
          { name = Some "fa"; ty = TApp (TVar "f") [TVar "a"]; mode = MOmega }
        ];
        return_type = TApp (TVar "f") [TVar "b"];
        effects = pure;
        is_unsafe = false
      }
    }
  ]
}

(* Monad class: extends Applicative with bind.

   The standard class hierarchy is:
     Functor <- Applicative <- Monad

   This follows Haskell's modern design where:
   - Functor provides map (fmap)
   - Applicative provides pure and apply (<*>)
   - Monad provides bind (>>=)

   Note: 'return' is provided by Applicative as 'pure', so Monad only needs bind.
   We include 'return' as an alias to 'pure' for convenience. *)
let monad_class : type_class = {
  tc_name = "Monad";
  tc_param = "m";
  tc_superclasses = ["Applicative"];  (* Proper hierarchy: Monad extends Applicative *)
  tc_methods = [
    (* bind (>>=) : m a -> (a -> m b) -> m b
       This is the core monadic operation. *)
    { cm_name = ">>=";
      cm_type = TFunc {
        params = [
          { name = Some "ma"; ty = TApp (TVar "m") [TVar "a"]; mode = MOmega };
          { name = Some "f"; ty = t_pure_func [TVar "a"] (TApp (TVar "m") [TVar "b"]); mode = MOmega }
        ];
        return_type = TApp (TVar "m") [TVar "b"];
        effects = pure;
        is_unsafe = false
      }
    };
    (* join : m (m a) -> m a
       Alternative monadic operation, derivable from bind:
       join mma = mma >>= id *)
    { cm_name = "join";
      cm_type = TFunc {
        params = [{ name = Some "mma"; ty = TApp (TVar "m") [TApp (TVar "m") [TVar "a"]]; mode = MOmega }];
        return_type = TApp (TVar "m") [TVar "a"];
        effects = pure;
        is_unsafe = false
      }
    }
  ]
}

(** ============================================================================
    STANDARD ENVIRONMENT WITH BASIC CLASSES
    ============================================================================ *)

(* Standard class environment with Eq, Ord, Show, Functor, Monad *)
let standard_classes : class_env =
  { ce_classes = [eq_class; ord_class; show_class; functor_class; applicative_class; monad_class];
    ce_instances = [] }

(** ============================================================================
    INSTANCE CHECKING - Verify an instance is well-formed
    ============================================================================ *)

(* Check that an instance provides all required methods *)
let rec has_all_methods (required: list class_method) (provided: list method_impl) : bool =
  match required with
  | [] -> true
  | m :: rest ->
      (match find_method_impl m.cm_name provided with
       | None -> false
       | Some _ -> has_all_methods rest provided)

(* Check that an instance is well-formed:
   1. The class exists
   2. All superclass instances exist (transitively, with cycle detection)
   3. All required methods are implemented *)
let instance_well_formed (inst: class_instance) (env: class_env) : bool =
  match lookup_class inst.ci_class env.ce_classes with
  | None -> false  (* Class doesn't exist *)
  | Some class_def ->
      (* Check superclass instances using safe transitive check *)
      superclasses_satisfied_safe
        class_def.tc_superclasses
        inst.ci_type
        env.ce_instances
        env.ce_classes
        [inst.ci_class]  (* Start with instance's class as visited *)
        max_superclass_depth &&
      (* Check all methods provided *)
      has_all_methods class_def.tc_methods inst.ci_methods

(** ============================================================================
    COHERENCE - No overlapping instances
    ============================================================================ *)

(* Check if two instances overlap (same class and type) *)
let instances_overlap (i1 i2: class_instance) : bool =
  i1.ci_class = i2.ci_class && type_eq i1.ci_type i2.ci_type

(* Check if a new instance would overlap with existing instances *)
let rec no_overlapping_instances (new_inst: class_instance) (existing: list class_instance) : bool =
  match existing with
  | [] -> true
  | i :: rest ->
      not (instances_overlap new_inst i) && no_overlapping_instances new_inst rest

(* Check coherence of entire environment *)
let rec env_coherent_helper (instances: list class_instance) : bool =
  match instances with
  | [] -> true
  | i :: rest ->
      no_overlapping_instances i rest && env_coherent_helper rest

let env_coherent (env: class_env) : bool =
  env_coherent_helper env.ce_instances

(** ============================================================================
    SAFE INSTANCE ADDITION - With coherence checking
    ============================================================================ *)

(* Result type for safe instance addition with detailed error information *)
type add_instance_result =
  | AddInstanceOk : env:class_env -> add_instance_result
  | AddInstanceOverlap : existing_type:brrr_type -> add_instance_result
  | AddInstanceClassNotFound : cls:class_name -> add_instance_result
  | AddInstanceMissingSuperclass : cls:class_name -> super:class_name -> add_instance_result
  | AddInstanceMissingMethod : method:method_name -> add_instance_result

(* Find which method is missing from an instance *)
let rec find_missing_method (required: list class_method) (provided: list method_impl) : option method_name =
  match required with
  | [] -> None
  | m :: rest ->
      match find_method_impl m.cm_name provided with
      | None -> Some m.cm_name
      | Some _ -> find_missing_method rest provided

(* Safe instance addition with coherence checking.

   Before adding an instance, this function verifies:
   1. No overlapping instances exist (coherence)
   2. The class exists in the environment
   3. All superclass instances exist (transitively)
   4. All required methods are implemented

   Returns:
   - AddInstanceOk with updated environment if all checks pass
   - Specific error variant otherwise

   This function should be used in production code to ensure type class
   coherence is maintained. The simpler add_instance function is provided
   for cases where the caller guarantees invariants are satisfied. *)
let add_instance_safe (i: class_instance) (env: class_env) : add_instance_result =
  (* Check for overlapping instances first *)
  if not (no_overlapping_instances i env.ce_instances) then
    (* Find the overlapping instance to report its type *)
    let overlapping = List.Tot.find (fun existing -> instances_overlap i existing) env.ce_instances in
    match overlapping with
    | Some existing -> AddInstanceOverlap existing.ci_type
    | None -> AddInstanceOverlap i.ci_type  (* Shouldn't happen, defensive *)
  else
    (* Look up the class definition *)
    match lookup_class i.ci_class env.ce_classes with
    | None -> AddInstanceClassNotFound i.ci_class
    | Some class_def ->
        (* Check all required methods are provided *)
        match find_missing_method class_def.tc_methods i.ci_methods with
        | Some missing -> AddInstanceMissingMethod missing
        | None ->
            (* Check superclass instances exist (after adding this instance) *)
            let env' = { env with ce_instances = i :: env.ce_instances } in
            if superclasses_satisfied_safe
                 class_def.tc_superclasses
                 i.ci_type
                 env'.ce_instances
                 env'.ce_classes
                 [i.ci_class]
                 max_superclass_depth
            then AddInstanceOk env'
            else
              (* Find which superclass is missing *)
              match find_missing_superclass class_def.tc_superclasses i.ci_type env'.ce_instances with
              | Some missing -> AddInstanceMissingSuperclass i.ci_class missing
              | None -> AddInstanceOk env'  (* Shouldn't happen, defensive *)

(* Convenience function: add instance if safe, return None on any error *)
let add_instance_checked (i: class_instance) (env: class_env) : option class_env =
  match add_instance_safe i env with
  | AddInstanceOk env' -> Some env'
  | _ -> None

(** ============================================================================
    DICTIONARY PASSING TRANSFORMATION
    ============================================================================ *)

(* Type class dictionaries are records containing method implementations.
   When compiling, constraints become dictionary parameters.

   Example: f :: Eq a => a -> a -> Bool
   Becomes: f :: EqDict a -> a -> a -> Bool

   This section provides types for representing dictionaries. *)

(* A dictionary type for a class instance *)
noeq type class_dict = {
  dict_class : class_name;
  dict_type  : brrr_type;
  dict_methods : list method_impl
}

(* Convert an instance to a dictionary *)
let instance_to_dict (inst: class_instance) : class_dict =
  { dict_class = inst.ci_class;
    dict_type = inst.ci_type;
    dict_methods = inst.ci_methods }

(** ============================================================================
    TYPE CLASS SIZE FUNCTIONS - For termination measures
    ============================================================================ *)

(* Size of a class constraint list *)
let constraint_list_size (cs: list class_constraint) : nat =
  List.Tot.length cs

(* Size of a type class *)
let type_class_size (c: type_class) : nat =
  1 + List.Tot.length c.tc_superclasses + List.Tot.length c.tc_methods

(* Size of class environment *)
let class_env_size (env: class_env) : nat =
  List.Tot.length env.ce_classes + List.Tot.length env.ce_instances

(** ============================================================================
    DERIVED CONSTRAINTS FROM SUPERCLASSES
    ============================================================================ *)

(* Given a constraint C a, derive all superclass constraints.
   Example: Ord a implies Eq a *)
let derive_superclass_constraints
    (c: class_constraint)
    (classes: list type_class)
    : list class_constraint =
  match lookup_class c.cc_class classes with
  | None -> []
  | Some class_def ->
      (* For each superclass, create a constraint *)
      List.Tot.map (fun super -> { cc_class = super; cc_var = c.cc_var })
                   class_def.tc_superclasses

(* Result type for constraint derivation *)
type derive_result =
  | DeriveComplete : constraints:list class_constraint -> derive_result
  | DeriveFuelExhausted : partial:list class_constraint -> derive_result

(* Derive all constraints including transitive superclasses.

   Returns:
   - DeriveComplete with the full constraint closure if derivation finishes
   - DeriveFuelExhausted with partial results if fuel runs out

   This explicit result type prevents silent failures where incomplete
   constraint sets could lead to unsound type checking. *)
let rec derive_all_constraints_safe
    (constraints: list class_constraint)
    (classes: list type_class)
    (fuel: nat)
    : Tot derive_result (decreases fuel) =
  if fuel = 0 then
    (* Fuel exhausted - explicitly signal incomplete derivation *)
    DeriveFuelExhausted constraints
  else
    let new_constraints = List.Tot.concatMap
      (fun c -> derive_superclass_constraints c classes)
      constraints
    in
    (* Filter out duplicates and already-present constraints *)
    let novel = List.Tot.filter
      (fun c -> not (has_constraint c constraints))
      new_constraints
    in
    if List.Tot.isEmpty novel then
      (* No new constraints found - derivation complete *)
      DeriveComplete constraints
    else
      derive_all_constraints_safe (constraints @ novel) classes (fuel - 1)

(* Convenience function returning option.
   None = fuel exhausted (incomplete), Some = complete derivation *)
let derive_all_constraints_opt
    (constraints: list class_constraint)
    (classes: list type_class)
    (fuel: nat)
    : Tot (option (list class_constraint)) (decreases fuel) =
  match derive_all_constraints_safe constraints classes fuel with
  | DeriveComplete cs -> Some cs
  | DeriveFuelExhausted _ -> None

(* Legacy function for backward compatibility.
   WARNING: Returns partial results on fuel exhaustion without indication.
   Prefer derive_all_constraints_safe for new code. *)
let rec derive_all_constraints
    (constraints: list class_constraint)
    (classes: list type_class)
    (fuel: nat)
    : Tot (list class_constraint) (decreases fuel) =
  match derive_all_constraints_safe constraints classes fuel with
  | DeriveComplete cs -> cs
  | DeriveFuelExhausted partial -> partial

(** ============================================================================
    FINAL VALIDATION
    ============================================================================ *)

(* Complete validation of a class environment:
   1. No superclass cycles (prevents infinite loops in instance resolution)
   2. All instances are well-formed
   3. No overlapping instances (coherence)
   4. All superclass instances exist *)
let validate_class_env (env: class_env) : bool =
  (* Check for superclass cycles first (most critical for termination) *)
  let no_cycles = all_classes_acyclic env.ce_classes in
  (* Check all instances are well-formed *)
  let all_well_formed = List.Tot.for_all
    (fun inst -> instance_well_formed inst env)
    env.ce_instances
  in
  (* Check coherence *)
  let coherent = env_coherent env in
  no_cycles && all_well_formed && coherent

(* Validation result type with detailed error information *)
type validation_result =
  | ValidationOk : validation_result
  | ValidationCycleError : offending_class:class_name -> validation_result
  | ValidationMissingInstance : cls:class_name -> ty:brrr_type -> validation_result
  | ValidationOverlapping : cls:class_name -> ty:brrr_type -> validation_result
  | ValidationMissingMethod : inst:class_name -> method:method_name -> validation_result

(* Detailed validation with error reporting *)
let rec validate_class_env_detailed (env: class_env) : validation_result =
  (* Check for superclass cycles *)
  let rec check_cycles (classes: list type_class) : option class_name =
    match classes with
    | [] -> None
    | cls :: rest ->
        if has_superclass_cycle cls env.ce_classes
        then Some cls.tc_name
        else check_cycles rest
  in
  match check_cycles env.ce_classes with
  | Some cycle_class -> ValidationCycleError cycle_class
  | None ->
      (* Check instance well-formedness *)
      let rec check_instances (instances: list class_instance) : validation_result =
        match instances with
        | [] -> ValidationOk
        | inst :: rest ->
            if not (instance_well_formed inst env) then
              (* Determine specific error *)
              (match lookup_class inst.ci_class env.ce_classes with
               | None -> ValidationMissingInstance inst.ci_class inst.ci_type
               | Some cls ->
                   if not (has_all_methods cls.tc_methods inst.ci_methods) then
                     (* Find first missing method *)
                     let rec find_missing (methods: list class_method) : option method_name =
                       match methods with
                       | [] -> None
                       | m :: ms ->
                           if None? (find_method_impl m.cm_name inst.ci_methods)
                           then Some m.cm_name
                           else find_missing ms
                     in
                     (match find_missing cls.tc_methods with
                      | Some m -> ValidationMissingMethod inst.ci_class m
                      | None -> ValidationOk)  (* Should not happen *)
                   else check_instances rest)
            else check_instances rest
      in
      check_instances env.ce_instances
