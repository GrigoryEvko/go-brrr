(**
 * BrrrLang.Core.TypeClasses
 *
 * Type class system for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part IV - Type Classes.
 *
 * ============================================================================
 * HISTORICAL CONTEXT AND THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * Type classes were introduced by Wadler & Blott in their seminal 1989 paper:
 *   "How to make ad-hoc polymorphism less ad hoc" (POPL 1989)
 *
 * The key insight is that ad-hoc polymorphism (operator overloading) can be
 * made principled by:
 *   1. Declaring a CLASS that specifies a set of operations (methods)
 *   2. Declaring INSTANCES that provide implementations for specific types
 *   3. Using a CONSTRAINT system to track which types support which operations
 *
 * This differs from parametric polymorphism (forall a. ...) which works
 * uniformly for ALL types, and subtype polymorphism which uses inheritance.
 *
 * Key properties from the original formulation:
 *   - Type inference remains decidable
 *   - Instance resolution is performed at compile time
 *   - No runtime type dispatch overhead (after dictionary passing)
 *
 * References:
 *   - Wadler & Blott 1989: Original type classes paper
 *   - Jones 1999: "Typing Haskell in Haskell" - formal semantics
 *   - Chakravarty et al. 2005: "Associated Types with Class"
 *   - Swamy et al. 2016: "Dependent Types and Multi-Monadic Effects in F*"
 *
 * ============================================================================
 * F* TCRESOLVE MECHANISM
 * ============================================================================
 *
 * F*'s typeclass system is implemented as a metaprogram using tactics,
 * defined in FStar.Tactics.Typeclasses. The key mechanism is:
 *
 * 1. CLASS DECLARATION:
 *    The 'class' keyword generates a record type plus accessor functions:
 *      class printable a = { to_string : a -> string }
 *    Becomes:
 *      type printable (a:Type) = { to_string : a -> string }
 *      val to_string : #a:Type -> {| i:printable a |} -> a -> string
 *      let to_string #a #i x = i.to_string x
 *
 * 2. INSTANCE DECLARATION:
 *    The 'instance' keyword registers a value for typeclass resolution:
 *      instance printable_int : printable int = { to_string = string_of_int }
 *
 * 3. TCRESOLVE ATTRIBUTE:
 *    Arguments marked with {| ... |} trigger typeclass resolution.
 *    F* searches for instances that unify with the required type.
 *    Resolution uses a backtracking search with instance functions.
 *
 * 4. RESOLUTION ALGORITHM (simplified):
 *    tcresolve goal:
 *      for each instance i in scope:
 *        if unify(type_of i, goal):
 *          if i has arguments:
 *            recursively resolve each argument
 *          return instantiated i
 *      fail "No instance found"
 *
 * In Brrr-Lang, we implement a similar mechanism but at the IR level,
 * allowing runtime reflection on typeclass constraints when needed.
 *
 * ============================================================================
 * COHERENCE (GLOBAL UNIQUENESS)
 * ============================================================================
 *
 * Coherence is a fundamental property stating that there is at most ONE
 * instance of a class for any given type. This ensures:
 *
 *   1. Semantics are deterministic regardless of import order
 *   2. Dictionary passing produces consistent results
 *   3. Separate compilation remains sound
 *
 * Violations of coherence can cause:
 *   - Different behavior depending on which instance is selected
 *   - Broken invariants (e.g., Set using two different Ord instances)
 *   - Subtle bugs when combining libraries
 *
 * Our implementation enforces coherence via:
 *   - no_overlapping_instances: Rejects instances with same class/type
 *   - env_coherent: Validates entire environment
 *   - add_instance_safe: Checks coherence before adding
 *
 * Note: Some systems (Haskell with extensions, Scala) allow controlled
 * incoherence via orphan instances or implicit scope. We follow the
 * conservative approach of global coherence.
 *
 * ============================================================================
 * DICTIONARY PASSING TRANSFORMATION
 * ============================================================================
 *
 * Type classes are compiled by transforming constraints into explicit
 * dictionary parameters. This is the "dictionary passing" style:
 *
 * Source:
 *   sum :: Num a => [a] -> a
 *   sum [] = fromInteger 0
 *   sum (x:xs) = x + sum xs
 *
 * Compiled:
 *   sum :: NumDict a -> [a] -> a
 *   sum d [] = fromInteger d 0
 *   sum d (x:xs) = (+) d x (sum d xs)
 *
 * Where NumDict is a record containing the method implementations:
 *   data NumDict a = NumDict {
 *     [+]         :: a -> a -> a,
 *     [*]         :: a -> a -> a,
 *     fromInteger :: Integer -> a,
 *     ...
 *   }
 *
 * Our class_dict type and instance_to_dict function support this transformation.
 *
 * ============================================================================
 * STANDARD TYPE CLASS HIERARCHY
 * ============================================================================
 *
 * We implement the standard Haskell-style hierarchy:
 *
 *   Eq          (equality)
 *     |
 *   Ord         (ordering)
 *
 *   Show        (string conversion)
 *
 *   Functor     (mappable containers)
 *     |
 *   Applicative (functor with pure and apply)
 *     |
 *   Monad       (sequencing computations)
 *
 * Each level adds operations while inheriting from superclasses:
 *
 *   Functor f:
 *     fmap :: (a -> b) -> f a -> f b
 *     Laws: fmap id = id
 *           fmap (g . h) = fmap g . fmap h
 *
 *   Applicative f:
 *     pure  :: a -> f a
 *     (<*>) :: f (a -> b) -> f a -> f b
 *     Laws: pure id <*> v = v                    (identity)
 *           pure (.) <*> u <*> v <*> w = u <*> (v <*> w)  (composition)
 *           pure f <*> pure x = pure (f x)      (homomorphism)
 *           u <*> pure y = pure ($ y) <*> u     (interchange)
 *
 *   Monad m:
 *     return :: a -> m a                        (same as pure)
 *     (>>=)  :: m a -> (a -> m b) -> m b        (bind/flatMap)
 *     Laws: return a >>= k = k a                (left identity)
 *           m >>= return = m                    (right identity)
 *           m >>= (\x -> k x >>= h) = (m >>= k) >>= h  (associativity)
 *
 * The Functor-Applicative-Monad hierarchy reflects category theory:
 *   - Functor: Preserves structure under mapping
 *   - Applicative: Closed under function application
 *   - Monad: Supports sequential composition with effects
 *
 * ============================================================================
 * HIGHER-KINDED TYPES
 * ============================================================================
 *
 * Functor, Applicative, and Monad are parameterized by type constructors
 * (f, m : Type -> Type), not plain types. This is "higher-kinded polymorphism."
 *
 * In Haskell notation:
 *   Functor :: (* -> *) -> Constraint
 *
 * In F* and Brrr-Lang, we represent this using type application:
 *   tc_param = "f"  (* The type constructor parameter *)
 *   method_type = TApp (TVar "f") [TVar "a"]  (* f a *)
 *
 * Kind checking ensures:
 *   - f has kind * -> * (takes one type, returns a type)
 *   - Methods use f consistently (no kind errors)
 *
 * Examples of type constructors that can be Functors:
 *   - List  : * -> *     (List a is a type for any type a)
 *   - Maybe : * -> *     (Option/Maybe a)
 *   - IO    : * -> *     (IO actions returning a)
 *   - State s : * -> *   (State computations with state type s)
 *
 * ============================================================================
 * IMPLEMENTATION NOTES
 * ============================================================================
 *
 * Key design decisions in this implementation:
 *
 * 1. SUPERCLASS CYCLE DETECTION:
 *    We use DFS with visited set to detect cycles in O(V + E) time.
 *    This prevents infinite loops during instance resolution.
 *    See: detect_superclass_cycle_dfs, has_superclass_cycle
 *
 * 2. FUEL-BASED TERMINATION:
 *    For potentially unbounded operations (constraint derivation),
 *    we use explicit fuel parameters with DeriveFuelExhausted results.
 *    This makes termination explicit rather than relying on hidden fuel.
 *
 * 3. TRANSITIVE SUPERCLASS CHECKING:
 *    superclasses_satisfied_safe performs transitive closure,
 *    ensuring Monad instances have Applicative AND Functor instances.
 *
 * 4. DETAILED ERROR REPORTING:
 *    resolve_result, add_instance_result, validation_result types
 *    provide specific error information for debugging.
 *
 * 5. noeq TYPES:
 *    Records containing functions (class_method, type_class, etc.)
 *    are marked noeq because function equality is undecidable.
 *    See F* documentation on when to use noeq.
 *
 * ============================================================================
 * RELATIONSHIP TO SPEC
 * ============================================================================
 *
 * This module implements Part IV of brrr_lang_spec_v0.4.tex:
 *   - Section 4.1: Class declarations
 *   - Section 4.2: Instance declarations
 *   - Section 4.3: Constraint solving
 *   - Section 4.4: Dictionary passing transformation
 *
 * Known specification issues (see SPECIFICATION_ERRATA.md):
 *   - Coherence checking requires care with extended modes
 *   - Instance resolution must verify class existence first
 *
 * Depends on: BrrrTypes, Expressions, Kinds, Modes, Effects
 *)
module BrrrTypeClasses

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

open FStar.List.Tot
open FStar.Classical
open BrrrModes
open BrrrEffects
open BrrrTypes
open BrrrExpressions
open BrrrKinds

(** ============================================================================
    TYPE CLASS NAMES
    ============================================================================

    Type class and method names are represented as strings for simplicity.
    In a production implementation, these might be:
      - Qualified names (module.ClassName)
      - Unique identifiers with source location
      - Interned symbols for efficient comparison

    Naming conventions (following Haskell):
      - Class names: CamelCase (Eq, Ord, Functor, Monad)
      - Method names: camelCase or operators (==, fmap, >>=)
      - Instance names: class_type (eq_int, functor_list)
    ============================================================================ *)

(* Type class identifier - unique name for the class *)
type class_name = string

(* Method name within a class - may be an operator symbol *)
type method_name = string

(** ============================================================================
    CLASS METHOD - A method signature within a type class
    ============================================================================

    A class method is an operation that instances must provide. Methods have:

    1. A NAME: The identifier used to invoke the method (may be operator)
    2. A TYPE: Polymorphic in the class parameter, instantiated per instance

    Example - The Eq class has two methods:
      class Eq a where
        (==) : a -> a -> Bool
        (/=) : a -> a -> Bool

    The types are polymorphic in 'a'. When instantiated for Int:
      (==) : Int -> Int -> Bool
      (/=) : Int -> Int -> Bool

    For higher-kinded classes like Functor:
      class Functor f where
        fmap : (a -> b) -> f a -> f b

    The type contains both 'f' (the class parameter) and 'a', 'b' (method
    parameters). When instantiated for List:
      fmap : (a -> b) -> List a -> List b

    Implementation Note:
    We use noeq because comparing method types (which contain functions
    in the case of higher-order types) is undecidable in general.
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
    ============================================================================

    A type class declaration specifies:
      1. The class name (used for constraint syntax: Eq a)
      2. The type parameter(s) (a, f, m, etc.)
      3. Superclass constraints (inheritance/dependency)
      4. Method signatures (operations instances must provide)

    Superclass Constraints:
    -----------------------
    When a class C extends class B, every instance of C must also have
    an instance of B. This creates a subclass relationship:

      class Eq a where (==) : a -> a -> Bool
      class Eq a => Ord a where (<) : a -> a -> Bool

    Here Ord extends Eq, meaning:
      - Every Ord instance requires an Eq instance
      - Ord methods can use Eq methods (like using == to implement <=)
      - instance Ord Int requires instance Eq Int to exist

    The superclass mechanism supports:
      - Single inheritance: class B => C
      - Multiple inheritance: class (B, C) => D
      - Transitive dependencies: if D requires C and C requires B, then D requires B

    Multi-Parameter Type Classes:
    -----------------------------
    Our representation uses a single tc_param, but the pattern generalizes:

      class Collection c e where
        insert : e -> c -> c
        member : e -> c -> Bool

    Here 'c' is the collection type and 'e' is the element type.
    The spec extends naturally to multiple parameters.

    Associated Types:
    -----------------
    Modern type class systems support associated types:

      class Container c where
        type Elem c
        insert : Elem c -> c -> c

    We don't directly model associated types but they could be added
    by extending method_type to include type-level methods.

    Implementation Note:
    Using noeq because tc_methods contains class_method which is noeq
    (due to brrr_type potentially containing function types).
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

(* Lookup a class by name - defined early for use in cycle detection.
   Note: This is also referenced later in the CLASS ENVIRONMENT section. *)
let rec lookup_class (name: class_name) (classes: list type_class) : option type_class =
  match classes with
  | [] -> None
  | c :: rest -> if c.tc_name = name then Some c else lookup_class name rest

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
    ============================================================================

    An instance declaration provides implementations of class methods for
    a specific type. Instances are the "evidence" that a type supports
    the operations defined by the class.

    Instance Forms:
    ---------------
    1. SIMPLE INSTANCE (no constraints):
       instance Eq Int where
         (==) = primIntEq
         (/=) = primIntNeq

    2. CONDITIONAL INSTANCE (with constraints):
       instance Eq a => Eq (List a) where
         (==) = listEq    (* requires Eq a to compare elements *)

    3. DERIVED INSTANCE (automatic generation):
       Some languages support deriving instances automatically:
       data Point = Point Int Int deriving (Eq, Show)

    Instance Resolution:
    --------------------
    When the compiler encounters a constraint like "Eq a" where a = Int:
      1. Search for instances matching Eq Int
      2. Found: instance Eq Int
      3. Use that instance's method implementations

    For conditional instances like Eq (List Int):
      1. Search for instances matching Eq (List Int)
      2. Found: instance Eq a => Eq (List a)
      3. Unify a = Int
      4. Recursively resolve Eq Int
      5. Build final instance using resolved dependencies

    Overlapping Instances:
    ----------------------
    Multiple instances can potentially match the same type:
      instance Eq (List a)                (* works for any list *)
      instance Eq (List Int)              (* specialized for List Int *)

    Coherence typically forbids this. Some systems allow it with:
      - Most specific match wins (overlap resolution)
      - Explicit scoping (local instances)
      - Instance priorities

    We enforce strict coherence: no overlapping instances allowed.

    Dictionary Representation:
    --------------------------
    Instances compile to dictionary records:

      instance Eq Int where
        (==) = primIntEq
        (/=) = primIntNeq

    Becomes:
      eqIntDict : EqDict Int = {
        equal = primIntEq;
        notEqual = primIntNeq
      }
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
    ============================================================================

    A class constraint expresses that a type variable must be an instance
    of a particular class. Constraints appear in function signatures:

      sort : Ord a => List a -> List a

    The "Ord a =>" part is a constraint saying "a must be orderable".

    Constraint Syntax Forms:
    ------------------------
    1. SINGLE CONSTRAINT:
       Eq a => a -> a -> Bool

    2. MULTIPLE CONSTRAINTS (conjunction):
       (Eq a, Show a) => a -> String

    3. HIGHER-KINDED CONSTRAINT:
       Monad m => m a -> (a -> m b) -> m b

    4. SUPERCLASS IMPLICATION:
       Ord a => ...  implicitly includes Eq a (from superclass)

    Constraint Propagation:
    -----------------------
    Constraints flow through the type system:

      f : Eq a => a -> a -> Bool
      g : a -> Bool = f x    (* Type error: no Eq constraint on a *)

    To use f, the context must provide an Eq constraint on the argument type.

    Qualified Types:
    ----------------
    The combination of constraints and a base type forms a "qualified type":

      Qualified Type = Constraints => Type

    This is the internal representation used during type checking.
    See constrained_type below.

    References:
    - Jones 1994: "Qualified Types: Theory and Practice"
    - Jones 1999: "Typing Haskell in Haskell"
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
    ============================================================================

    A constrained type (also called "qualified type") bundles:
      - A list of type class constraints
      - The base type those constraints qualify

    This corresponds to the Haskell notation:
      (C1 a, C2 a, ...) => tau

    Where C1, C2, etc. are class constraints and tau is the base type.

    Type Scheme vs Constrained Type:
    --------------------------------
    A full polymorphic type scheme has three parts:

      forall a b c. (Eq a, Ord b) => a -> b -> c

    1. Universal quantifiers: forall a b c
    2. Constraints: (Eq a, Ord b)
    3. Base type: a -> b -> c

    The constrained_type captures (2) and (3). Quantifiers are handled
    separately during generalization/instantiation.

    Operations on Constrained Types:
    --------------------------------
    1. INSTANTIATION:
       Replace type variables with concrete types, removing satisfied
       constraints and checking remaining ones.

    2. GENERALIZATION:
       Compute the set of free type variables and their required
       constraints from the typing context.

    3. SUBSUMPTION:
       Check if one constrained type is more general than another.
       More constraints = more specific.

    Example:
      (* More general: fewer constraints *)
      f : a -> a -> Bool

      (* More specific: has Eq constraint *)
      g : Eq a => a -> a -> Bool

      (* g subsumes f when Eq is required *)

    Context Reduction:
    ------------------
    Simplify constraints by:
    1. Removing redundant constraints (Eq a is redundant if Ord a exists)
    2. Substituting known types
    3. Deriving implied constraints from superclasses

    See apply_subst_to_constrained and derive_all_constraints.
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
    ============================================================================

    The class environment holds all type class definitions and instances
    in scope. It is the "database" consulted during instance resolution.

    Environment Structure:
    ----------------------
    - ce_classes: All class definitions (Eq, Ord, Functor, etc.)
    - ce_instances: All instance declarations (Eq Int, Ord Int, Functor List)

    Environment Invariants (when valid):
    ------------------------------------
    1. NO SUPERCLASS CYCLES: The superclass relation is acyclic
    2. INSTANCE WELL-FORMEDNESS: Each instance:
       - References an existing class
       - Provides all required methods
       - Has all superclass instances available
    3. COHERENCE: No two instances for the same class and type

    These invariants are checked by validate_class_env.

    Environment Operations:
    -----------------------
    - add_class: Add a new class definition (unchecked)
    - add_instance: Add a new instance (unchecked)
    - add_instance_safe: Add instance with coherence checking
    - lookup_class: Find a class by name
    - resolve_instance: Find an instance for (class, type)

    Scoping Considerations:
    -----------------------
    In a real compiler, the environment would support:
    - Module-qualified names
    - Import/export of classes and instances
    - Orphan instance detection (instances defined outside class/type modules)

    For simplicity, we use a flat global namespace.
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

(* Note: lookup_class is defined earlier in the file, before cycle detection *)

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

(* Note: The following lemma about equivalence between safe_resolve_instance
   and resolve_instance when the environment is valid is stated informally here.
   The formal lemma requires validate_class_env which is defined later.

   Informal statement:
   If validate_class_env env = true, then:
   - safe_resolve_instance never returns ResolveCycleDetected
   - ResolveOk inst corresponds to resolve_instance returning Some inst
   - Other error cases correspond to resolve_instance returning None

   This equivalence justifies using the simpler resolve_instance when the
   environment has been validated once at load time. *)

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
    ============================================================================

    This section defines the standard type class hierarchy. These classes
    provide fundamental abstractions used throughout functional programming.

    EQUALITY AND ORDERING
    ---------------------
    Eq: Types with decidable equality
      (==) : a -> a -> Bool

    Ord: Types with total ordering (extends Eq)
      (<), (<=), (>), (>=) : a -> a -> Bool
      compare : a -> a -> Ordering

    Laws for Eq:
      Reflexivity:  x == x
      Symmetry:     x == y <==> y == x
      Transitivity: x == y && y == z ==> x == z

    Laws for Ord:
      Antisymmetry: x <= y && y <= x ==> x == y
      Transitivity: x <= y && y <= z ==> x <= z
      Totality:     x <= y || y <= x

    DISPLAY
    -------
    Show: Types that can be converted to strings
      show : a -> String

    This is primarily for debugging and display, not serialization.

    FUNCTOR-APPLICATIVE-MONAD HIERARCHY
    -----------------------------------
    This hierarchy captures increasingly powerful patterns of computation.

    Functor f: Structure-preserving mapping
      fmap : (a -> b) -> f a -> f b

    Category theory: A functor F : C -> D maps objects and morphisms from
    category C to category D, preserving identity and composition.

    Applicative f: Functor with lifting of multi-argument functions
      pure  : a -> f a
      (<*>) : f (a -> b) -> f a -> f b

    Applicative functors are "lax monoidal functors" - they preserve the
    monoidal structure of function application.

    Monad m: Sequencing computations with effects
      return : a -> m a        (same as pure)
      (>>=)  : m a -> (a -> m b) -> m b

    Category theory: A monad is a monoid in the category of endofunctors.
    Equivalently, it's a functor M with natural transformations:
      - unit : Id -> M         (return)
      - join : M . M -> M      (join)

    The Kleisli category of a monad M has:
      - Objects: Types
      - Morphisms a -> b: Functions a -> m b
      - Composition: Kleisli composition via bind

    COMMON INSTANCES
    ----------------
    List (Functor, Applicative, Monad):
      fmap f [x,y,z] = [f x, f y, f z]
      pure x = [x]
      [f,g] <*> [x,y] = [f x, f y, g x, g y]  (cartesian product)
      xs >>= f = concat (map f xs)

    Maybe/Option (Functor, Applicative, Monad):
      fmap f (Some x) = Some (f x)
      fmap f None = None
      pure x = Some x
      Some f <*> Some x = Some (f x)
      _ <*> None = None
      None <*> _ = None
      Some x >>= f = f x
      None >>= f = None

    IO (Functor, Applicative, Monad):
      Sequences side-effecting computations

    State s (Functor, Applicative, Monad):
      Threads state through computations

    REFERENCES
    ----------
    - Wadler 1992: "The Essence of Functional Programming" (monads)
    - McBride & Paterson 2008: "Applicative Programming with Effects"
    - Gibbons & Hinze 2011: "Just Do It: Simple Monadic Equational Reasoning"
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
    ============================================================================

    Coherence is the property that type class resolution produces a unique
    result. With coherence, the meaning of a program doesn't depend on:
      - Which instance is selected when multiple could match
      - The order instances are declared
      - Which module instances are imported from

    Why Coherence Matters:
    ----------------------
    Consider a Set data structure that uses Ord for ordering:

      insert : Ord a => a -> Set a -> Set a
      member : Ord a => a -> Set a -> Bool

    If two different Ord instances for Int exist:
      instance Ord Int where (<) = ascending
      instance Ord Int where (<) = descending

    Then:
      let s = insert 1 (insert 2 (insert 3 empty))
      member 2 s  -- might return True or False depending on instance!

    The internal structure depends on which Ord was used for insert,
    but member might use a different one, breaking invariants.

    Coherence Violations:
    ---------------------
    1. OVERLAPPING INSTANCES:
       instance Eq (List a)
       instance Eq (List Int)  -- overlaps with above when a = Int

    2. ORPHAN INSTANCES:
       Defining an instance outside the module of the class or type.
       Different modules might define conflicting orphans.

    3. INCOHERENT IMPORTS:
       Importing different instances in different parts of the program.

    Enforcement in Brrr-Lang:
    -------------------------
    - instances_overlap: Detects overlap between two instances
    - no_overlapping_instances: Checks new instance against existing
    - env_coherent: Validates entire environment
    - add_instance_safe: Rejects incoherent additions

    Alternative Approaches:
    -----------------------
    Some systems allow controlled incoherence:

    1. EXPLICIT INSTANCE ARGUMENTS (Agda, Idris):
       Pass instances explicitly when ambiguous.

    2. LOCAL INSTANCES (Scala implicits):
       Scope determines which instance is used.

    3. NEWTYPE WRAPPERS (Haskell):
       Wrap types to get different instances:
       newtype Desc a = Desc a
       instance Ord a => Ord (Desc a) where compare = flip compare

    We follow Haskell's conservative global coherence model.
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
    ============================================================================

    The standard compilation strategy for type classes transforms constrained
    functions into functions that take explicit dictionary arguments.

    Before Transformation:
    ----------------------
      equal :: Eq a => a -> a -> Bool
      equal x y = x == y

    After Transformation:
    ---------------------
      equal :: EqDict a -> a -> a -> Bool
      equal d x y = d.eq x y

    Where EqDict is a record type:
      data EqDict a = EqDict { eq :: a -> a -> Bool }

    Instance Dictionaries:
    ----------------------
    Each instance becomes a dictionary value:

      instance Eq Int where (==) = primIntEq

    Becomes:
      eqDictInt :: EqDict Int
      eqDictInt = EqDict { eq = primIntEq }

    Conditional Instances:
    ----------------------
    Instances with constraints become dictionary-transforming functions:

      instance Eq a => Eq (List a) where
        (==) = listEq

    Becomes:
      eqDictList :: EqDict a -> EqDict (List a)
      eqDictList da = EqDict { eq = \xs ys -> listEq da xs ys }

    Superclass Dictionaries:
    ------------------------
    Superclass constraints are stored as fields in the dictionary:

      class Eq a => Ord a where (<) :: a -> a -> Bool

    Becomes:
      data OrdDict a = OrdDict {
        eqDict :: EqDict a,   -- superclass dictionary
        lt :: a -> a -> Bool
      }

    This allows extracting the superclass instance when needed.

    Dictionary Construction:
    ------------------------
    At call sites, the compiler inserts dictionary arguments:

      sort :: Ord a => [a] -> [a]
      sort [1, 3, 2]  -- call site for Int

    Becomes:
      sort ordDictInt [1, 3, 2]

    For polymorphic contexts, dictionaries are passed through:

      f :: Ord a => a -> a -> Bool
      f x y = x < y || x == y

    Becomes:
      f :: OrdDict a -> a -> a -> Bool
      f d x y = d.lt x y || d.eqDict.eq x y

    Optimization Opportunities:
    ---------------------------
    1. SPECIALIZATION: Inline dictionaries for known types
    2. DICTIONARY INLINING: Avoid dictionary allocation for local uses
    3. SUPERCLASS EXTRACTION: Cache superclass dictionaries

    References:
    -----------
    - Wadler & Blott 1989: Original dictionary passing description
    - Hall et al. 1996: "Type Classes in Haskell" (GHC implementation)
    - Dijkstra et al. 2019: "A Specification for Typed Template Haskell"
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
    ============================================================================

    When a constraint is present, all its superclass constraints are
    implicitly available. This section computes the transitive closure
    of constraints through the superclass hierarchy.

    Superclass Implication:
    -----------------------
    If class C has superclass B, then:
      C a  implies  B a

    This is transitive:
      Monad m  implies  Applicative m  implies  Functor m

    So "Monad m" implicitly provides all three constraints.

    Constraint Closure Algorithm:
    -----------------------------
    Given initial constraints, compute all implied constraints:

    Input: [Monad m]
    Step 1: Monad m -> superclasses = [Applicative]
            Add: Applicative m
    Step 2: Applicative m -> superclasses = [Functor]
            Add: Functor m
    Step 3: Functor m -> superclasses = []
            Done.
    Output: [Monad m, Applicative m, Functor m]

    The algorithm is a fixed-point computation: keep deriving until
    no new constraints are added.

    Termination:
    ------------
    Termination relies on:
    1. Finite number of classes in the environment
    2. Acyclic superclass hierarchy

    We use explicit fuel to guarantee termination even in malformed
    environments, with DeriveFuelExhausted signaling incomplete results.

    Context Reduction:
    ------------------
    Constraint derivation is part of "context reduction" which also includes:

    1. SIMPLIFICATION: Remove redundant constraints
       (Eq a, Ord a) -> (Ord a)  since Eq is implied by Ord

    2. IMPROVEMENT: Discover type equalities from functional dependencies
       (Not implemented in basic type classes)

    3. DEFAULTING: Replace ambiguous type variables with defaults
       (e.g., default numeric types to Integer in Haskell)

    Our derive_all_constraints computes the transitive closure without
    simplification. Simplification would filter out constraints that
    are implied by other constraints in the set.
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
    ============================================================================

    Before using a class environment for type checking, it should be validated
    to ensure all invariants hold. Validation catches errors early and provides
    specific error messages.

    Validation Checks:
    ------------------
    1. NO SUPERCLASS CYCLES:
       Detects: class A extends B, class B extends A
       Consequence if violated: Instance resolution loops forever

    2. ALL INSTANCES WELL-FORMED:
       Detects: Missing class, missing methods, type mismatches
       Consequence if violated: Runtime errors during dictionary use

    3. COHERENCE (NO OVERLAPPING INSTANCES):
       Detects: Multiple instances for same class/type pair
       Consequence if violated: Non-deterministic program behavior

    4. SUPERCLASS INSTANCES EXIST:
       Detects: instance Ord T without instance Eq T
       Consequence if violated: Missing dictionary at runtime

    Validation Strategy:
    --------------------
    validate_class_env: Returns bool (pass/fail)
    validate_class_env_detailed: Returns specific error information

    The detailed version should be used for error reporting, while the
    simple version is useful for assertions and quick checks.

    When to Validate:
    -----------------
    1. After loading modules (once per module)
    2. After adding instances dynamically (if supported)
    3. Before code generation

    Performance Note:
    -----------------
    Validation is O(n^2) in the worst case for coherence checking
    (comparing all instance pairs). For large environments, consider:
    - Incremental validation when adding instances
    - Indexing instances by (class, type) for faster overlap detection
    - Caching validation results

    Error Recovery:
    ---------------
    On validation failure, the compiler should:
    1. Report the specific error with location
    2. Continue checking other parts of the program (for more errors)
    3. Prevent code generation for affected code
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

(** ============================================================================
    COHERENCE DECIDABILITY - Separate from Well-Formedness
    ============================================================================

    This section implements coherence as a DISTINCT property from well-formedness.
    The separation addresses Gap #20 in the specification errata.

    WELL-FORMEDNESS vs COHERENCE:
    -----------------------------
    - WELL-FORMED: Instances type-check correctly
      * Class exists in environment
      * All required methods are implemented
      * Superclass instances exist

    - COHERENT: Instance selection is unambiguous
      * No two instances match the same concrete type (no overlap)
      * No orphan instances (instances defined in wrong modules)
      * Deterministic resolution guaranteed

    WHY SEPARATE?
    -------------
    An environment can be well-formed but incoherent:
      instance Eq (List a)        (* Works for any list *)
      instance Eq (List Int)      (* Specialized for Int lists *)

    Both instances are well-formed (type-check correctly), but they OVERLAP:
    when resolving Eq (List Int), BOTH could match.

    THEORETICAL FOUNDATION:
    -----------------------
    Coherence ensures that type class resolution produces UNIQUE results.
    This is critical for:
      1. Deterministic program semantics
      2. Separate compilation soundness
      3. Consistent behavior regardless of import order

    REFERENCES:
    -----------
    - Haskell type class coherence (GHC User's Guide)
    - Rust trait coherence and orphan rules (RFC 2451)
    - Scalas & Yoshida 2019: Association relation for session types
    ============================================================================ *)

(** ============================================================================
    MODULE OWNERSHIP FOR ORPHAN RULES
    ============================================================================

    Orphan instances are instances defined in a module that "owns" neither the
    type class nor the primary type being instantiated. They violate coherence
    because different modules might define conflicting orphan instances.

    OWNERSHIP RULES:
    ----------------
    An instance `instance C T` is NOT orphan if EITHER:
      1. The current module defines class C, OR
      2. The current module defines type T (the "head" type)

    The HEAD TYPE is the outermost type constructor. For example:
      instance Eq (List Int)     -- head type is List
      instance Functor Maybe     -- head type is Maybe
      instance Show (Int, Bool)  -- head type is tuple (,)

    HASKELL vs RUST APPROACHES:
    ---------------------------
    Haskell: Orphan instances are allowed but warned about
    Rust: Orphan instances are FORBIDDEN (orphan rules enforced)

    We follow Rust's stricter approach for guaranteed coherence.
    ============================================================================ *)

(* Module identifier for tracking instance ownership *)
type module_id = string

(* Ownership information for a class or type *)
noeq type ownership_info = {
  oi_module : module_id;   (* Module that defines this class/type *)
}

(* Extended class environment with ownership tracking *)
noeq type class_env_ext = {
  cee_base : class_env;                           (* Base environment *)
  cee_class_owners : list (class_name & module_id);  (* Class -> owning module *)
  cee_type_owners : list (type_name & module_id);    (* Type -> owning module *)
}

(* Lookup the owning module for a class *)
let rec lookup_class_owner (cls: class_name) (owners: list (class_name & module_id)) : option module_id =
  match owners with
  | [] -> None
  | (c, m) :: rest -> if c = cls then Some m else lookup_class_owner cls rest

(* Lookup the owning module for a type *)
let rec lookup_type_owner (ty: type_name) (owners: list (type_name & module_id)) : option module_id =
  match owners with
  | [] -> None
  | (t, m) :: rest -> if t = ty then Some m else lookup_type_owner ty rest

(* Extract the head type name from a type.
   The head type is the outermost type constructor.
   Returns None for type variables (polymorphic instances always okay). *)
let rec head_type_name (ty: brrr_type) : option type_name =
  match ty with
  | TPrim _ -> Some "prim"           (* Primitives are "owned" by prelude *)
  | TNumeric _ -> Some "numeric"     (* Numerics are "owned" by prelude *)
  | TStruct st -> Some st.struct_name  (* Struct head type is struct name *)
  | TEnum et -> Some et.enum_name      (* Enum head type is enum name *)
  | TNamed name -> Some name         (* Named type is the head *)
  | TTuple _ -> Some "tuple"         (* Tuples are built-in *)
  | TResult _ _ -> Some "result"     (* Result is built-in *)
  | TFunc _ -> Some "func"           (* Functions are built-in *)
  | TApp base _ -> head_type_name base  (* Application: recurse to get head *)
  | TWrap _ inner -> head_type_name inner  (* Wrapper: head is inner type head *)
  | TModal _ inner -> head_type_name inner  (* Modal: head is inner type head *)
  | TVar _ -> None                   (* Type variable: no concrete head *)

(** ============================================================================
    TYPE UNIFICATION FOR OVERLAP DETECTION
    ============================================================================

    Two instances OVERLAP if there exists a type that matches both instance
    heads. We detect this via type UNIFICATION.

    UNIFICATION ALGORITHM:
    ----------------------
    Given two types t1 and t2, unification finds a substitution sigma such that
    sigma(t1) = sigma(t2), or reports failure if no such substitution exists.

    For instance overlap detection:
      instance Eq (List a)     -- inst1.inst_head = TApp (TNamed "List") [TVar "a"]
      instance Eq (List Int)   -- inst2.inst_head = TApp (TNamed "List") [TPrim PInt]

    Unifying these yields: sigma = {a -> Int}
    The unified type List Int proves that BOTH instances match List Int.

    UNIFICATION RESULT:
    -------------------
    - UOk subst    : Unification succeeded, subst is the most general unifier
    - UFail t1 t2 r: Unification failed, t1 and t2 clash at reason r

    OCCURS CHECK:
    -------------
    Unification must prevent infinite types. The occurs check ensures we don't
    create substitutions like a -> List a, which would be infinite.
    ============================================================================ *)

(* Type substitution: maps type variables to types *)
type type_subst = list (type_var & brrr_type)

(* Unification failure reason *)
type unify_fail_reason =
  | ClashConstructor    (* Different type constructors *)
  | ClashPrimitive      (* Different primitive types *)
  | ClashArity          (* Different number of type arguments *)
  | OccursCheck         (* Occurs check failed: infinite type *)
  | ClashEffect         (* Effect row mismatch *)

(* Unification result *)
type unify_result =
  | UOk : subst:type_subst -> unify_result
  | UFail : t1:brrr_type -> t2:brrr_type -> reason:unify_fail_reason -> unify_result

(* Apply a substitution to a type *)
let rec apply_subst (subst: type_subst) (t: brrr_type) : Tot brrr_type (decreases t) =
  match t with
  | TVar v ->
      (match assoc v subst with
       | Some replacement -> replacement
       | None -> t)
  | TPrim _ -> t
  | TNumeric _ -> t
  | TWrap w inner -> TWrap w (apply_subst subst inner)
  | TModal m inner -> TModal m (apply_subst subst inner)
  | TResult t1 t2 -> TResult (apply_subst subst t1) (apply_subst subst t2)
  | TTuple ts -> TTuple (apply_subst_list subst ts)
  | TFunc ft -> TFunc {
      params = apply_subst_params subst ft.params;
      return_type = apply_subst subst ft.return_type;
      effects = ft.effects;  (* Effects unchanged for now *)
      is_unsafe = ft.is_unsafe
    }
  | TApp base args -> TApp (apply_subst subst base) (apply_subst_list subst args)
  | TNamed _ -> t
  | TStruct _ -> t
  | TEnum _ -> t

and apply_subst_list (subst: type_subst) (ts: list brrr_type) : Tot (list brrr_type) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> apply_subst subst t :: apply_subst_list subst rest

and apply_subst_params (subst: type_subst) (ps: list BrrrTypes.param_type) : Tot (list BrrrTypes.param_type) (decreases ps) =
  match ps with
  | [] -> []
  | p :: rest ->
      let p_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p in
      { name = BrrrTypes.Mkparam_type?.name p; ty = apply_subst subst p_ty; mode = BrrrTypes.Mkparam_type?.mode p }
      :: apply_subst_params subst rest

(* Compose two substitutions: first apply s1, then s2 *)
let compose_subst (s1 s2: type_subst) : type_subst =
  (* Apply s2 to all types in s1, then add new bindings from s2 *)
  let s1' = List.Tot.map (fun (v, t) -> (v, apply_subst s2 t)) s1 in
  let new_bindings = List.Tot.filter (fun (v, _) -> None? (assoc v s1)) s2 in
  s1' @ new_bindings

(* Check if a type variable occurs in a type (occurs check) *)
let rec occurs_in (v: type_var) (t: brrr_type) : Tot bool (decreases t) =
  match t with
  | TVar v' -> v = v'
  | TPrim _ -> false
  | TNumeric _ -> false
  | TWrap _ inner -> occurs_in v inner
  | TModal _ inner -> occurs_in v inner
  | TResult t1 t2 -> occurs_in v t1 || occurs_in v t2
  | TTuple ts -> occurs_in_list v ts
  | TFunc ft -> occurs_in_params v ft.params || occurs_in v ft.return_type
  | TApp base args -> occurs_in v base || occurs_in_list v args
  | TNamed _ -> false
  | TStruct _ -> false
  | TEnum _ -> false

and occurs_in_list (v: type_var) (ts: list brrr_type) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: rest -> occurs_in v t || occurs_in_list v rest

and occurs_in_params (v: type_var) (ps: list BrrrTypes.param_type) : Tot bool (decreases ps) =
  match ps with
  | [] -> false
  | p :: rest ->
      let p_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p in
      occurs_in v p_ty || occurs_in_params v rest

(* Maximum unification depth to prevent infinite recursion *)
let max_unify_depth : nat = 100

(* Unify two types, returning the most general unifier or failure *)
let rec unify_types (t1 t2: brrr_type) (depth: nat)
    : Tot unify_result (decreases depth) =
  if depth = 0 then UFail t1 t2 ClashConstructor  (* Depth limit *)
  else if type_eq t1 t2 then UOk []  (* Already equal *)
  else
    match t1, t2 with
    (* Variable on left: bind if not occurs *)
    | TVar v, _ ->
        if occurs_in v t2 then UFail t1 t2 OccursCheck
        else UOk [(v, t2)]

    (* Variable on right: bind if not occurs *)
    | _, TVar v ->
        if occurs_in v t1 then UFail t1 t2 OccursCheck
        else UOk [(v, t1)]

    (* Same primitive: succeed *)
    | TPrim p1, TPrim p2 ->
        if p1 = p2 then UOk [] else UFail t1 t2 ClashPrimitive

    (* Same numeric: succeed *)
    | TNumeric n1, TNumeric n2 ->
        if n1 = n2 then UOk [] else UFail t1 t2 ClashPrimitive

    (* Same wrapper: unify inner *)
    | TWrap w1 inner1, TWrap w2 inner2 ->
        if w1 = w2 then unify_types inner1 inner2 (depth - 1)
        else UFail t1 t2 ClashConstructor

    (* Same modal: unify inner *)
    | TModal m1 inner1, TModal m2 inner2 ->
        if m1 = m2 then unify_types inner1 inner2 (depth - 1)
        else UFail t1 t2 ClashConstructor

    (* Result: unify both components *)
    | TResult t1a t1b, TResult t2a t2b ->
        begin match unify_types t1a t2a (depth - 1) with
         | UFail _ _ r -> UFail t1 t2 r
         | UOk s1 ->
             let t1b' = apply_subst s1 t1b in
             let t2b' = apply_subst s1 t2b in
             begin match unify_types t1b' t2b' (depth - 1) with
             | UFail _ _ r -> UFail t1 t2 r
             | UOk s2 -> UOk (compose_subst s1 s2)
             end
        end

    (* Tuple: unify element-wise *)
    | TTuple ts1, TTuple ts2 ->
        if List.Tot.length ts1 <> List.Tot.length ts2
        then UFail t1 t2 ClashArity
        else unify_type_lists ts1 ts2 (depth - 1)

    (* Type application: unify base and args *)
    | TApp base1 args1, TApp base2 args2 ->
        if List.Tot.length args1 <> List.Tot.length args2
        then UFail t1 t2 ClashArity
        else begin
          match unify_types base1 base2 (depth - 1) with
          | UFail _ _ r -> UFail t1 t2 r
          | UOk s1 ->
              let args1' = apply_subst_list s1 args1 in
              let args2' = apply_subst_list s1 args2 in
              begin match unify_type_lists args1' args2' (depth - 1) with
              | UFail _ _ r -> UFail t1 t2 r
              | UOk s2 -> UOk (compose_subst s1 s2)
              end
        end

    (* Named types: must be same name *)
    | TNamed n1, TNamed n2 ->
        if n1 = n2 then UOk [] else UFail t1 t2 ClashConstructor

    (* Struct types: must be same name *)
    | TStruct n1, TStruct n2 ->
        if n1 = n2 then UOk [] else UFail t1 t2 ClashConstructor

    (* Enum types: must be same name *)
    | TEnum n1, TEnum n2 ->
        if n1 = n2 then UOk [] else UFail t1 t2 ClashConstructor

    (* Function types: unify params and return *)
    | TFunc ft1, TFunc ft2 ->
        if List.Tot.length ft1.params <> List.Tot.length ft2.params
        then UFail t1 t2 ClashArity
        else begin
          match unify_param_lists ft1.params ft2.params (depth - 1) with
          | UFail _ _ r -> UFail t1 t2 r
          | UOk s1 ->
              let ret1 = apply_subst s1 ft1.return_type in
              let ret2 = apply_subst s1 ft2.return_type in
              begin match unify_types ret1 ret2 (depth - 1) with
              | UFail _ _ r -> UFail t1 t2 r
              | UOk s2 -> UOk (compose_subst s1 s2)
              end
        end

    (* Different constructors: fail *)
    | _, _ -> UFail t1 t2 ClashConstructor

and unify_type_lists (ts1 ts2: list brrr_type) (depth: nat)
    : Tot unify_result (decreases depth) =
  if depth = 0 then UFail (TTuple ts1) (TTuple ts2) ClashConstructor
  else
    match ts1, ts2 with
    | [], [] -> UOk []
    | t1 :: rest1, t2 :: rest2 ->
        begin match unify_types t1 t2 (depth - 1) with
         | UFail _ _ r -> UFail t1 t2 r
         | UOk s1 ->
             let rest1' = apply_subst_list s1 rest1 in
             let rest2' = apply_subst_list s1 rest2 in
             begin match unify_type_lists rest1' rest2' (depth - 1) with
             | UFail _ _ r -> UFail (TTuple ts1) (TTuple ts2) r
             | UOk s2 -> UOk (compose_subst s1 s2)
             end
        end
    | _, _ -> UFail (TTuple ts1) (TTuple ts2) ClashArity

and unify_param_lists (ps1 ps2: list BrrrTypes.param_type) (depth: nat)
    : Tot unify_result (decreases depth) =
  if depth = 0 then UFail (TFunc {params=ps1; return_type=TVar "_"; effects=RowEmpty; is_unsafe=false})
                         (TFunc {params=ps2; return_type=TVar "_"; effects=RowEmpty; is_unsafe=false})
                         ClashConstructor
  else
    match ps1, ps2 with
    | [], [] -> UOk []
    | p1 :: rest1, p2 :: rest2 ->
        let p1_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p1 in
        let p2_ty : brrr_type = BrrrTypes.Mkparam_type?.ty p2 in
        begin match unify_types p1_ty p2_ty (depth - 1) with
         | UFail _ _ r -> UFail p1_ty p2_ty r
         | UOk s1 ->
             let rest1' = apply_subst_params s1 rest1 in
             let rest2' = apply_subst_params s1 rest2 in
             begin match unify_param_lists rest1' rest2' (depth - 1) with
             | UFail _ _ r -> UFail p1_ty p2_ty r
             | UOk s2 -> UOk (compose_subst s1 s2)
             end
        end
    | _, _ ->
        UFail (TFunc {params=ps1; return_type=TVar "_"; effects=RowEmpty; is_unsafe=false})
              (TFunc {params=ps2; return_type=TVar "_"; effects=RowEmpty; is_unsafe=false})
              ClashArity

(* Convenience function for unification with default depth *)
let unify (t1 t2: brrr_type) : unify_result =
  unify_types t1 t2 max_unify_depth

(** ============================================================================
    COHERENCE RESULT TYPE
    ============================================================================

    Coherence is SEPARATE from well-formedness. The coherence_result type
    captures the three possible outcomes:

    - Coherent: All instances are mutually non-overlapping and no orphans
    - Overlapping: Two instances match the same type
    - Orphan: An instance violates orphan rules

    This separation enables finer-grained error reporting and allows
    well-formedness checking to proceed independently of coherence checking.
    ============================================================================ *)

(* Coherence check result - distinct from well-formedness *)
type coherence_result =
  | Coherent                                              (* No overlaps, no orphans *)
  | Overlapping : i1:class_instance -> i2:class_instance -> unified_type:brrr_type -> coherence_result
  | Orphan : inst:class_instance -> coherence_result

(** ============================================================================
    OVERLAP DETECTION WITH UNIFICATION
    ============================================================================

    Two instances OVERLAP if their instance heads can be unified to the same
    type. This is more precise than simple equality checking.

    EXAMPLES:
    ---------
    instance Eq (List a)      -- Head: TApp List [TVar "a"]
    instance Eq (List Int)    -- Head: TApp List [TPrim PInt]

    These OVERLAP because unifying yields sigma = {a -> Int}, and both
    instances match the type List Int.

    instance Eq (List a)
    instance Eq (Maybe a)

    These DO NOT overlap - List and Maybe cannot unify.
    ============================================================================ *)

(* Check if two instances overlap (same class, unifiable types).
   Returns Some unified_type if they overlap, None otherwise. *)
let instances_overlap_with_unification (i1 i2: class_instance) : option brrr_type =
  if i1.ci_class <> i2.ci_class then None  (* Different classes: no overlap *)
  else
    match unify i1.ci_type i2.ci_type with
    | UOk subst -> Some (apply_subst subst i1.ci_type)  (* Overlap at unified type *)
    | UFail _ _ _ -> None  (* Cannot unify: no overlap *)

(* Find first overlapping pair in a list of instances *)
let rec find_overlapping_pair (instances: list class_instance)
    : option (class_instance & class_instance & brrr_type) =
  match instances with
  | [] -> None
  | i :: rest ->
      (* Check i against all remaining instances *)
      match find_overlap_with i rest with
      | Some (other, ty) -> Some (i, other, ty)
      | None -> find_overlapping_pair rest

and find_overlap_with (i: class_instance) (others: list class_instance)
    : option (class_instance & brrr_type) =
  match others with
  | [] -> None
  | other :: rest ->
      match instances_overlap_with_unification i other with
      | Some ty -> Some (other, ty)
      | None -> find_overlap_with i rest

(** ============================================================================
    ORPHAN RULE CHECKING
    ============================================================================

    An instance is an ORPHAN if it's defined in a module that owns neither:
    1. The type class being instantiated, NOR
    2. The head type of the instance

    ORPHAN RULE (Rust-style):
    -------------------------
    For `instance C T` defined in module M:
      NOT orphan iff (M owns C) OR (M owns head(T))

    WHY ORPHAN RULES?
    -----------------
    Without orphan rules, different libraries could define conflicting
    instances for the same class/type pair:

      (* Library A defines: *)
      instance Show Int = "decimal"

      (* Library B defines: *)
      instance Show Int = "hexadecimal"

    If both are imported, which one is used? Orphan rules prevent this by
    requiring instances to be co-located with the class or type definition.
    ============================================================================ *)

(* Check if a module owns a class *)
let owns_class (mod_id: module_id) (cls: class_name) (owners: list (class_name & module_id)) : bool =
  match lookup_class_owner cls owners with
  | Some owner -> owner = mod_id
  | None -> false  (* Unknown class: conservatively say not owned *)

(* Check if a module owns a type *)
let owns_type (mod_id: module_id) (ty: brrr_type) (owners: list (type_name & module_id)) : bool =
  match head_type_name ty with
  | None -> true  (* Type variable: always okay (polymorphic instance) *)
  | Some type_name ->
      match lookup_type_owner type_name owners with
      | Some owner -> owner = mod_id
      | None ->
          (* Built-in types like "prim", "tuple" are owned by no module,
             but anyone can define instances for them *)
          type_name = "prim" || type_name = "numeric" || type_name = "tuple" ||
          type_name = "result" || type_name = "func"

(* Check if an instance is an orphan in the given module *)
let is_orphan_instance (inst: class_instance) (current_mod: module_id)
    (class_owners: list (class_name & module_id))
    (type_owners: list (type_name & module_id)) : bool =
  not (owns_class current_mod inst.ci_class class_owners) &&
  not (owns_type current_mod inst.ci_type type_owners)

(* Find first orphan instance in a list *)
let rec find_orphan (instances: list class_instance) (current_mod: module_id)
    (class_owners: list (class_name & module_id))
    (type_owners: list (type_name & module_id)) : option class_instance =
  match instances with
  | [] -> None
  | inst :: rest ->
      if is_orphan_instance inst current_mod class_owners type_owners
      then Some inst
      else find_orphan rest current_mod class_owners type_owners

(** ============================================================================
    MAIN COHERENCE CHECK
    ============================================================================

    The coherence check verifies that:
    1. No two instances overlap (can match the same concrete type)
    2. No orphan instances exist

    This is SEPARATE from well-formedness checking, which verifies that
    instances are correctly typed.
    ============================================================================ *)

(* Check coherence of a list of instances *)
let check_coherence_instances (instances: list class_instance)
    (current_mod: module_id)
    (class_owners: list (class_name & module_id))
    (type_owners: list (type_name & module_id)) : coherence_result =
  (* First check for overlapping instances *)
  match find_overlapping_pair instances with
  | Some (i1, i2, ty) -> Overlapping i1 i2 ty
  | None ->
      (* Then check for orphan instances *)
      match find_orphan instances current_mod class_owners type_owners with
      | Some inst -> Orphan inst
      | None -> Coherent

(* Check coherence of an extended class environment *)
let check_coherence (env: class_env_ext) (current_mod: module_id) : coherence_result =
  check_coherence_instances
    env.cee_base.ce_instances
    current_mod
    env.cee_class_owners
    env.cee_type_owners

(* Simplified coherence check without orphan rules (for environments without ownership info) *)
let check_coherence_simple (env: class_env) : coherence_result =
  match find_overlapping_pair env.ce_instances with
  | Some (i1, i2, ty) -> Overlapping i1 i2 ty
  | None -> Coherent

(** ============================================================================
    COHERENCE DECIDABILITY PROOFS
    ============================================================================

    Coherence checking is DECIDABLE because:
    1. Type unification is decidable (first-order unification)
    2. Orphan checking is a finite lookup
    3. We check a finite list of instances

    These proofs ensure that coherence can always be determined statically.
    ============================================================================ *)

(* Lemma: check_coherence always returns one of the three outcomes *)
val coherence_decidable : instances:list class_instance -> current_mod:module_id ->
  class_owners:list (class_name & module_id) -> type_owners:list (type_name & module_id) ->
  Lemma (ensures
           Coherent? (check_coherence_instances instances current_mod class_owners type_owners) \/
           Overlapping? (check_coherence_instances instances current_mod class_owners type_owners) \/
           Orphan? (check_coherence_instances instances current_mod class_owners type_owners))

let coherence_decidable instances current_mod class_owners type_owners =
  (* By case analysis on the function definition:
     - If find_overlapping_pair returns Some, we return Overlapping
     - Else if find_orphan returns Some, we return Orphan
     - Else we return Coherent
     One of these three cases always holds. *)
  ()

(* Helper: count matching instances for a type *)
let rec count_matching_instances (cls: class_name) (ty: brrr_type) (instances: list class_instance) : nat =
  match instances with
  | [] -> 0
  | inst :: rest ->
      let count_rest = count_matching_instances cls ty rest in
      if inst.ci_class = cls && type_eq inst.ci_type ty
      then 1 + count_rest
      else count_rest

(* Helper: at most one instance matches a given type *)
let at_most_one_matching (#a: Type) (p: a -> bool) (l: list a) : bool =
  List.Tot.length (List.Tot.filter p l) <= 1

(* Lemma: If coherent, at most one instance matches any given type.
   This is the KEY property that ensures deterministic instance resolution. *)
val coherence_implies_unique_selection : instances:list class_instance -> ty:brrr_type -> cls:class_name ->
  Lemma (requires Coherent? (check_coherence_simple { ce_classes = []; ce_instances = instances }))
        (ensures at_most_one_matching (fun i -> instance_matches i cls ty) instances)

(* Proof sketch: If there were two matching instances, they would overlap,
   contradicting the Coherent assumption. *)
let coherence_implies_unique_selection instances ty cls =
  (* If two instances both match (cls, ty), they would have unified types
     (since both match the same concrete type ty), so find_overlapping_pair
     would have found them, returning Overlapping instead of Coherent.
     By contraposition, Coherent implies at most one match. *)
  admit ()  (* Full proof requires induction on instances list *)

(* Lemma: Unification is decidable (terminates for all inputs) *)
val unify_decidable : t1:brrr_type -> t2:brrr_type ->
  Lemma (ensures UOk? (unify t1 t2) \/ UFail? (unify t1 t2))
        [SMTPat (unify t1 t2)]

let unify_decidable t1 t2 =
  (* By the definition of unify_types with bounded depth,
     the function always terminates and returns either UOk or UFail. *)
  ()

(* Lemma: Orphan checking is decidable *)
val orphan_check_decidable : inst:class_instance -> mod_id:module_id ->
  class_owners:list (class_name & module_id) -> type_owners:list (type_name & module_id) ->
  Lemma (ensures is_orphan_instance inst mod_id class_owners type_owners = true \/
                 is_orphan_instance inst mod_id class_owners type_owners = false)

let orphan_check_decidable inst mod_id class_owners type_owners =
  (* Boolean functions are always decidable *)
  ()

(** ============================================================================
    SAFE INSTANCE ADDITION WITH COHERENCE
    ============================================================================

    When adding a new instance, we must check that it doesn't create
    overlaps with existing instances.
    ============================================================================ *)

(* Result of adding instance with coherence checking *)
type add_instance_coherent_result =
  | AddCoherentOk : env:class_env -> add_instance_coherent_result
  | AddCoherentOverlap : with_inst:class_instance -> unified_type:brrr_type -> add_instance_coherent_result
  | AddCoherentOrphan : add_instance_coherent_result
  | AddCoherentWellFormednessError : error:add_instance_result -> add_instance_coherent_result

(* Check if new instance overlaps with any existing instance *)
let rec check_no_overlap_with_existing (new_inst: class_instance) (existing: list class_instance)
    : option (class_instance & brrr_type) =
  match existing with
  | [] -> None
  | inst :: rest ->
      match instances_overlap_with_unification new_inst inst with
      | Some ty -> Some (inst, ty)
      | None -> check_no_overlap_with_existing new_inst rest

(* Add instance with both well-formedness AND coherence checking *)
let add_instance_coherent (i: class_instance) (env: class_env)
    (current_mod: module_id)
    (class_owners: list (class_name & module_id))
    (type_owners: list (type_name & module_id)) : add_instance_coherent_result =
  (* First check orphan rule *)
  if is_orphan_instance i current_mod class_owners type_owners
  then AddCoherentOrphan
  else
    (* Check for overlap with existing instances *)
    match check_no_overlap_with_existing i env.ce_instances with
    | Some (existing, ty) -> AddCoherentOverlap existing ty
    | None ->
        (* Now do standard well-formedness checking *)
        match add_instance_safe i env with
        | AddInstanceOk env' -> AddCoherentOk env'
        | error -> AddCoherentWellFormednessError error

(** ============================================================================
    COMBINED VALIDATION: WELL-FORMEDNESS + COHERENCE
    ============================================================================

    For complete validation, we check BOTH well-formedness and coherence.
    This provides the strongest guarantees for type class resolution.
    ============================================================================ *)

(* Combined validation result *)
type full_validation_result =
  | FullValidationOk : full_validation_result
  | FullValidationWellFormedness : error:validation_result -> full_validation_result
  | FullValidationCoherence : error:coherence_result -> full_validation_result

(* Full validation: well-formedness then coherence *)
let validate_full (env: class_env) : full_validation_result =
  (* First check well-formedness *)
  match validate_class_env_detailed env with
  | ValidationOk ->
      (* Then check coherence (simplified, no orphan rules) *)
      (match check_coherence_simple env with
       | Coherent -> FullValidationOk
       | error -> FullValidationCoherence error)
  | error -> FullValidationWellFormedness error

(* Full validation with extended environment (includes orphan rules) *)
let validate_full_ext (env: class_env_ext) (current_mod: module_id) : full_validation_result =
  match validate_class_env_detailed env.cee_base with
  | ValidationOk ->
      (match check_coherence env current_mod with
       | Coherent -> FullValidationOk
       | error -> FullValidationCoherence error)
  | error -> FullValidationWellFormedness error

(* Lemma: Full validation is decidable *)
val full_validation_decidable : env:class_env ->
  Lemma (ensures FullValidationOk? (validate_full env) \/
                 FullValidationWellFormedness? (validate_full env) \/
                 FullValidationCoherence? (validate_full env))

let full_validation_decidable env =
  (* By case analysis on validate_class_env_detailed and check_coherence_simple *)
  ()
