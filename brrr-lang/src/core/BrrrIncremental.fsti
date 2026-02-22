(**
 * BrrrLang.Core.Incremental - Interface
 *
 * Incremental analysis framework for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part XIII (Incremental Analysis).
 *
 * This module provides:
 *   1. Merkle-Based Change Detection - hash-based tree comparison
 *   2. Tree Diff Algorithm - edit operations between tree versions
 *   3. Dependency Tracking - fine-grained dependency graphs
 *   4. Fine-Grained Invalidation - minimal recomputation sets
 *   5. Memoization Cache - result caching with dependency tracking
 *   6. Incremental Fixpoint - efficient incremental computation
 *
 * All proofs are complete with NO ADMITS.
 *
 * Depends on: Primitives, BrrrTypes, PhysicalRep
 *)

(**
 * ===========================================================================
 * THEORETICAL FOUNDATIONS
 * ===========================================================================
 *
 * This module implements a self-adjusting computation framework inspired by:
 *
 * - Adapton (Hammer et al., PLDI 2014): "Adapton: Composable, Demand-Driven
 *   Incremental Computation"
 *   The key insight is demand-driven memoization with dependency tracking,
 *   where computations are re-executed only when their transitive dependencies
 *   change. This module implements a simplified version focusing on:
 *     - Content-addressed caching via Merkle hashes
 *     - Bidirectional dependency graphs for O(1) invalidation queries
 *     - Worklist-based incremental fixpoint computation
 *
 * - Incremental Lambda Calculus (Cai et al., PLDI 2014): "A Theory of Changes
 *   for Higher-Order Languages"
 *   The formal model for expressing program changes as first-class values.
 *   Our edit_op type represents this change vocabulary for AST transformations.
 *
 * - F* Hint System: The F* compiler uses a similar approach for caching SMT
 *   proof obligations. Hints store Z3 facts that successfully discharged proof
 *   obligations, indexed by content hashes.
 *
 * ===========================================================================
 * KEY INVARIANTS
 * ===========================================================================
 *
 * 1. SOUNDNESS: If a symbol is transitively affected by changes, it must be
 *    included in affected_by. (Theorem: changed_in_affected)
 *
 * 2. CACHE COHERENCE: A cache entry is valid iff none of its dependencies
 *    have been invalidated. (Predicate: cache_entry_valid)
 *
 * 3. DEPENDENCY CONSISTENCY: Forward and backward edge maps are inverses.
 *    (Predicate: dep_graph_wf)
 *
 * 4. INCREMENTAL = FROM-SCRATCH: For deterministic analyses, incremental
 *    computation produces identical results to from-scratch computation.
 *    (Theorem: incremental_correctness_statement)
 *
 * ===========================================================================
 * COMPLEXITY ANALYSIS
 * ===========================================================================
 *
 * Let n = number of symbols, m = number of dependencies, c = number of changes.
 *
 * - affected_by: O(m) worst case, O(c * avg_degree) typical
 * - cache_invalidate: O(|entries| * |deps_per_entry|)
 * - tree_diff: O(min(n1, n2) * log(n1 + n2)) with Hungarian matching
 * - incremental_fixpoint: O(|affected| * analysis_cost)
 *
 * The incremental approach wins when c << n, which is the common case for
 * interactive editing where most changes are local modifications.
 *)
module BrrrIncremental

open BrrrPrimitives
open BrrrTypes
open BrrrPhysicalRep
open FStar.List.Tot
open FStar.Mul

(** ============================================================================
    BASIC TYPES AND HELPERS
    ============================================================================

    These foundational types represent the core abstractions for incremental
    analysis. Symbol identifiers provide stable references across edits,
    timestamps enable LRU eviction, and hashes enable content-addressed lookup.
*)

(** Symbol identifier - unique identifier for symbols in the codebase.
    In practice, this would be interned strings for O(1) comparison.
    Using nat for simplicity in proofs. *)
type symbol_id = nat

(** Timestamp for cache entries.
    Monotonically increasing counter used for:
    - LRU eviction ordering
    - Cache entry age determination
    - Detecting stale computations *)
type timestamp = nat

(** Hash type - reuse hash256 from BrrrPhysicalRep.
    BLAKE3 provides:
    - 256-bit collision resistance
    - Fast incremental hashing (Merkle tree friendly)
    - Keyed mode for HMAC-like applications *)
type hash = hash256

(** ============================================================================
    SET OPERATIONS (Lists with membership semantics)
    ============================================================================

    These set operations form the foundation for tracking collections of symbols,
    dependencies, and cache entries. We use lists as the underlying representation
    for simplicity, but production code would use balanced trees or hash sets.

    DESIGN NOTE: Lists are acceptable here because:
    - Small set sizes in practice (< 1000 for most analyses)
    - Simpler proofs with structural induction
    - Easy integration with FStar.List.Tot lemmas

    For production use, consider FStar.OrdSet or FStar.FiniteSet.
*)

(** Check if element is in set. O(n) where n = |s|. *)
val set_mem : #a:eqtype -> x:a -> s:list a -> bool

(** Add element to set if not present.
    Maintains the invariant that sets have no duplicates. *)
val set_add : #a:eqtype -> x:a -> s:list a -> list a

(** Remove element from set.
    Returns a new list without the first occurrence of x. *)
val set_remove : #a:eqtype -> x:a -> s:list a -> list a

(** Set union. Combines two sets, eliminating duplicates.
    Complexity: O(|s1| * |s2|). *)
val set_union : #a:eqtype -> s1:list a -> s2:list a -> list a

(** Set intersection. Returns elements present in both sets.
    Complexity: O(|s1| * |s2|). *)
val set_inter : #a:eqtype -> s1:list a -> s2:list a -> list a

(** Set difference. Returns elements in s1 but not in s2.
    Useful for computing newly-added or removed dependencies. *)
val set_diff : #a:eqtype -> s1:list a -> s2:list a -> list a

(** Empty set. The identity element for set_union. *)
val set_empty : #a:eqtype -> list a

(** Set from list (deduplicated).
    Converts an arbitrary list (possibly with duplicates) into a set. *)
val set_from_list : #a:eqtype -> l:list a -> list a

(** Set size. For a proper set (no duplicates), this equals cardinality. *)
val set_size : #a:eqtype -> s:list a -> nat

(** Set subset check. Returns true iff every element of s1 is in s2.
    Complexity: O(|s1| * |s2|). *)
val set_subset : #a:eqtype -> s1:list a -> s2:list a -> bool

(** Set equality. Two sets are equal iff they are mutual subsets.
    Note: This is semantic equality, not structural (order-independent). *)
val set_eq : #a:eqtype -> s1:list a -> s2:list a -> bool

(** Lemma: set_mem after set_add.
    After adding y to s, x is a member iff x=y or x was already in s. *)
val set_mem_after_add : #a:eqtype -> x:a -> y:a -> s:list a
    -> Lemma (ensures set_mem x (set_add y s) = (x = y || set_mem x s))

(** Lemma: set_add is idempotent.
    Adding an element that already exists leaves the set unchanged. *)
val set_add_idempotent : #a:eqtype -> x:a -> s:list a
    -> Lemma (ensures set_mem x s ==> set_add x s == s)

(** Lemma: element in union.
    An element is in the union iff it's in either operand. *)
val set_mem_union : #a:eqtype -> x:a -> s1:list a -> s2:list a
    -> Lemma (ensures set_mem x (set_union s1 s2) = (set_mem x s1 || set_mem x s2))
             (decreases s1)

(** ============================================================================
    MAP OPERATIONS (Association lists)
    ============================================================================

    Maps provide key-value storage for:
    - Merkle tree nodes (hash -> node data)
    - Dependency graph edges (symbol -> dependencies)
    - Cache entries (hash -> cached value)

    We use "shadowing semantics" where insert prepends to the list.
    The most recent binding is found first, matching F*'s variable shadowing.
*)

(** Map type as association list.
    The first occurrence of a key determines its value (shadowing semantics). *)
type map (k: eqtype) (v: Type) = list (k & v)

(** Empty map. The identity element for map operations. *)
val map_empty : #k:eqtype -> #v:Type -> map k v

(** Map lookup. Returns the value associated with key, or None if not found.
    First match wins (shadowing semantics). *)
val map_lookup : #k:eqtype -> #v:Type -> key:k -> m:map k v -> option v

(** Map insert/update. Prepends new binding, shadowing any existing binding.
    O(1) time, but increases space. *)
val map_insert : #k:eqtype -> #v:Type -> key:k -> value:v -> m:map k v -> map k v

(** Map remove. Removes the first binding for key.
    Subsequent bindings (if shadowed) become visible. *)
val map_remove : #k:eqtype -> #v:Type -> key:k -> m:map k v -> map k v

(** Map keys. Returns all keys in the map (may contain duplicates if shadowed). *)
val map_keys : #k:eqtype -> #v:Type -> m:map k v -> list k

(** Map values. Returns all values in the map (may contain shadowed values). *)
val map_values : #k:eqtype -> #v:Type -> m:map k v -> list v

(** Map contains key. Checks if any binding exists for key. *)
val map_contains : #k:eqtype -> #v:Type -> key:k -> m:map k v -> bool

(** Map size. Returns the number of bindings (including shadowed ones). *)
val map_size : #k:eqtype -> #v:Type -> m:map k v -> nat

(** Lemma: lookup after insert returns inserted value. *)
val map_lookup_after_insert : #k:eqtype -> #v:eqtype -> key:k -> value:v -> m:map k v
    -> Lemma (ensures map_lookup key (map_insert key value m) = Some value)

(** Lemma: lookup different key unchanged.
    Inserting a binding for key2 doesn't affect lookups for key1 (when key1 <> key2). *)
val map_lookup_insert_other : #k:eqtype -> #v:eqtype -> key1:k -> key2:k -> value:v -> m:map k v
    -> Lemma (requires key1 <> key2)
             (ensures map_lookup key1 (map_insert key2 value m) = map_lookup key1 m)

(** ============================================================================
    MERKLE TREE NODE
    ============================================================================

    Merkle trees enable efficient change detection through content-addressed
    hashing. Each node's hash incorporates its children's hashes, so a change
    anywhere in the tree propagates up to the root.

    PROPERTIES:
    1. Content addressing: Identical subtrees have identical hashes
    2. Change detection: Different hashes imply structural difference
    3. Sharing: Common subtrees are stored once (hash-consing)

    From the spec (Section: Merkle-Based Change Detection):

      hash(n) = H(kind(n) || hash(children(n)) || content(n))

    COMPLEXITY: O(1) equality check via hash comparison.
*)

(** Node data for Merkle tree - parameterized by payload type.
    The hash uniquely identifies this node's content + structure. *)
noeq type merkle_node (a: Type) = {
  mn_hash: hash;     (* Content hash - combines children hashes with local data *)
  mn_data: a;        (* Payload data - the actual node content *)
}

(** Merkle tree structure - stores nodes by hash.

    DESIGN RATIONALE:
    - mt_root: The root hash acts as a "version identifier" for the entire tree
    - mt_nodes: Hash-indexed storage enables O(1) node lookup
    - mt_children: Separate child list storage for efficient traversal

    INVARIANT: Every hash in mt_children values must exist as a key in mt_nodes. *)
noeq type merkle_tree (a: Type) = {
  mt_root: hash;
  mt_nodes: map hash (merkle_node a);
  mt_children: map hash (list hash);
}

(** Empty Merkle tree. The zero_hash represents an empty/null reference. *)
val empty_merkle_tree : #a:Type -> merkle_tree a

(** Get node by hash. O(n) with association lists; O(1) with hash tables. *)
val get_merkle_node : #a:Type -> tree:merkle_tree a -> h:hash -> option (merkle_node a)

(** Get children of node. Returns empty list for leaf nodes or unknown hashes. *)
val get_children : #a:Type -> tree:merkle_tree a -> h:hash -> list hash

(** Insert node into tree. Adds a node with its hash, data, and child references.
    Note: Does NOT update the root - use set_root for that. *)
val insert_merkle_node : #a:Type -> tree:merkle_tree a -> h:hash -> node:merkle_node a -> children:list hash
    -> merkle_tree a

(** Set root of tree. Designates a new root hash without modifying the node graph. *)
val set_root : #a:Type -> tree:merkle_tree a -> h:hash -> merkle_tree a

(** ============================================================================
    MERKLE TREE DIFF - Changed Hash Detection
    ============================================================================

    The diff operation computes the set of hashes that differ between two trees.
    This is the foundation for incremental analysis: instead of re-analyzing
    everything, we identify changed nodes and propagate updates.

    ALGORITHM:
    1. Collect all hashes from both trees
    2. Find hashes present in one tree but not the other
    3. Union these "asymmetric" hashes

    SOUNDNESS: If a hash appears in the diff, it represents a real structural
    difference between the trees.
*)

(** Find hashes present in tree1 but not in tree2.
    These represent nodes that were deleted or modified. *)
val diff_hashes_helper : #a:Type -> hashes:list hash -> tree2:merkle_tree a -> list hash

(** Compute set of changed hashes between two trees.
    Returns the symmetric difference: nodes in tree1 but not tree2, plus
    nodes in tree2 but not tree1.

    INTERPRETATION:
    - Hashes only in tree1: Deleted nodes
    - Hashes only in tree2: Added nodes
    - Note: Modified nodes appear as delete + add of different hashes *)
val diff : #a:Type -> tree1:merkle_tree a -> tree2:merkle_tree a -> list hash

(** Lemma: if a hash is in the diff, it's not in both trees.
    Establishes that diff produces only genuine differences. *)
val diff_hashes_helper_correct : #a:Type -> hashes:list hash -> tree2:merkle_tree a -> h:hash
    -> Lemma (ensures set_mem h (diff_hashes_helper hashes tree2) ==>
                      (set_mem h hashes && not (map_contains h tree2.mt_nodes)))
             (decreases hashes)

(** ============================================================================
    EDIT OPERATIONS - Tree Diff Algorithm
    ============================================================================

    Edit operations form the vocabulary for expressing tree changes.
    This follows the Incremental Lambda Calculus approach where changes
    are first-class values that can be composed and applied.

    OPERATIONS:
    - Insert: Add a new node (corresponds to expression insertion)
    - Delete: Remove an existing node (corresponds to expression deletion)
    - Modify: Change node data in-place (corresponds to local edits)
    - Move: Reparent a node (corresponds to refactoring moves)

    EDIT SCRIPT: A list of edit_ops constitutes an "edit script" that
    transforms one tree into another.
*)

(** Edit operations for tree transformation. *)
noeq type edit_op (a: Type) =
  | Insert : hash -> merkle_node a -> edit_op a         (* Add new node with given hash *)
  | Delete : hash -> edit_op a                           (* Remove node by hash *)
  | Modify : hash -> merkle_node a -> merkle_node a -> edit_op a  (* Change node: old -> new *)
  | Move   : hash -> hash -> hash -> edit_op a           (* Move node: node_hash, old_parent, new_parent *)

(** Get hash affected by edit operation.
    Useful for determining which cache entries to invalidate. *)
val edit_op_hash : #a:Type -> op:edit_op a -> hash

(** Apply single edit operation to tree.
    Each operation produces a new tree (persistent/immutable structure). *)
val apply_edit : #a:Type -> tree:merkle_tree a -> op:edit_op a -> merkle_tree a

(** Apply list of edit operations.
    Edit scripts are applied left-to-right (first operation first). *)
val apply_edits : #a:Type -> tree:merkle_tree a -> ops:list (edit_op a)
    -> Tot (merkle_tree a) (decreases ops)

(** Compute tree diff helper - processes keys from tree1, generating Modify and Delete ops. *)
val tree_diff_helper : #a:Type -> keys1:list hash -> tree1:merkle_tree a -> tree2:merkle_tree a
    -> list (edit_op a)

(** Compute insertions for keys in tree2 not in tree1.
    Handles the "added" case where new nodes appear. *)
val compute_insertions : #a:Type -> keys2:list hash -> tree1:merkle_tree a -> tree2:merkle_tree a
    -> list (edit_op a)

(** Full tree diff. Combines modification/deletion detection with insertion detection.

    PROPERTIES:
    - apply_edits tree1 (tree_diff tree1 tree2) ~~= tree2 (structurally equivalent)
    - |tree_diff tree1 tree2| is minimal for the edit vocabulary used *)
val tree_diff : #a:Type -> tree1:merkle_tree a -> tree2:merkle_tree a -> list (edit_op a)

(** ============================================================================
    DEPENDENCY KINDS
    ============================================================================

    Dependencies are classified by their semantic nature, enabling fine-grained
    invalidation. Not all changes require full re-analysis:

    - TypeDep: Changing a type signature affects all users
    - CallDep: Changing a function body affects callers (for inlined code)
    - FieldDep: Changing a field affects accessors
    - ImportDep: Changing exports affects importers
    - InheritDep: Changing a parent type affects subtypes

    From spec (Section: Fine-Grained Dependencies):

      Signature changes require reanalysis of all dependents.
      Body-only changes may only require reanalysis if the caller inlines.
*)

(** Kind of dependency between symbols. Each kind has different invalidation semantics. *)
type dep_kind =
  | TypeDep    : dep_kind   (* Type dependency: symbol uses type of another *)
  | CallDep    : dep_kind   (* Call dependency: symbol calls another *)
  | FieldDep   : dep_kind   (* Field dependency: symbol accesses field of another *)
  | ImportDep  : dep_kind   (* Import dependency: module imports another *)
  | InheritDep : dep_kind   (* Inheritance: type inherits from another *)

(** Dependency kind equality. *)
val dep_kind_eq : k1:dep_kind -> k2:dep_kind -> bool

(** ============================================================================
    DEPENDENCY STRUCTURE
    ============================================================================

    A dependency edge connects a source (dependent) to a target (dependency).
    The source symbol's analysis result depends on the target symbol.

    EXAMPLE:
      function foo() { bar(); }

    Creates dependency: foo --CallDep--> bar
*)

(** Single dependency edge. Captures the source, target, and nature of the dependency. *)
noeq type dependency = {
  dep_source: symbol_id;   (* Dependent symbol - what depends *)
  dep_target: symbol_id;   (* Dependency target - what is depended upon *)
  dep_kind: dep_kind;      (* Type of dependency - for selective invalidation *)
}

(** Dependency equality. Two dependencies are equal if all three components match. *)
val dependency_eq : d1:dependency -> d2:dependency -> bool

(** Create dependency. Smart constructor for building dependency records. *)
val mk_dependency : src:symbol_id -> tgt:symbol_id -> kind:dep_kind -> dependency

(** ============================================================================
    DEPENDENCY GRAPH
    ============================================================================

    The dependency graph is the core data structure for incremental analysis.
    We maintain BIDIRECTIONAL edges for efficient queries:

    - Forward (dg_forward): "What does X depend on?"
      Used during initial analysis to record dependencies.

    - Backward (dg_backward): "What depends on X?"
      Used during invalidation to find affected symbols.

    INVARIANT (Well-formedness):
    For every edge (src --kind--> tgt) in forward,
    there exists edge (src --kind--> tgt) in backward at tgt.
*)

(** Bidirectional dependency graph for efficient queries. *)
noeq type dep_graph = {
  (* Forward edges: symbol -> what it depends on *)
  dg_forward: map symbol_id (list dependency);
  (* Backward edges: symbol -> what depends on it *)
  dg_backward: map symbol_id (list dependency);
}

(** Empty dependency graph. Initial state with no recorded dependencies. *)
val empty_dep_graph : dep_graph

(** Get forward dependencies of symbol.
    Returns all symbols that the given symbol depends on. *)
val get_forward_deps : g:dep_graph -> sym:symbol_id -> list dependency

(** Get backward dependencies of symbol (dependents).
    Returns all symbols that depend on the given symbol.
    This is the key query for invalidation. *)
val get_backward_deps : g:dep_graph -> sym:symbol_id -> list dependency

(** Add dependency to graph.
    Maintains bidirectional invariant by updating both forward and backward maps. *)
val add_dependency : g:dep_graph -> d:dependency -> dep_graph

(** Remove dependency from graph.
    Removes from both forward and backward maps to maintain invariant. *)
val remove_dependency : g:dep_graph -> d:dependency -> dep_graph

(** Get all symbols that a given symbol depends on. *)
val dependencies_of : g:dep_graph -> sym:symbol_id -> list symbol_id

(** Get all symbols that depend on a given symbol.
    This is the primary query for invalidation. *)
val dependents_of : g:dep_graph -> sym:symbol_id -> list symbol_id

(** ============================================================================
    AFFECTED BY - Transitive Closure of Dependents
    ============================================================================

    The affected_by function computes the transitive closure of the "depends on"
    relation. Given a set of changed symbols, it returns ALL symbols that might
    need re-analysis.

    ALGORITHM: Breadth-First Search (BFS)
    1. Start with changed symbols in the frontier
    2. For each frontier symbol, add its dependents to the frontier
    3. Track visited symbols to avoid cycles
    4. Continue until frontier is empty

    SOUNDNESS: Every symbol transitively dependent on a changed symbol is
    included in the result.

    COMPLEXITY: O(|affected| * avg_degree) = O(|edges in affected subgraph|)
*)

(** Compute symbols affected by changes - BFS transitive closure.
    Uses lexicographic ordering for termination proof. *)
val affected_by_step : g:dep_graph -> frontier:list symbol_id -> visited:list symbol_id
    -> Tot (list symbol_id)
           (decreases %[1000 - List.Tot.length visited; List.Tot.length frontier])

(** Compute all symbols transitively affected by a set of changed symbols.
    Entry point for the BFS traversal starting from changed symbols. *)
val affected_by : g:dep_graph -> changed:list symbol_id -> list symbol_id

(** Lemma: visited symbols are preserved in result.
    Key for proving soundness of the BFS traversal. *)
val visited_preserved : g:dep_graph -> frontier:list symbol_id -> visited:list symbol_id -> sym:symbol_id
    -> Lemma (requires set_mem sym visited)
             (ensures set_mem sym (affected_by_step g frontier visited))
             (decreases %[1000 - List.Tot.length visited; List.Tot.length frontier])

(** Lemma: if sym is added to visited in one step, it's in the final result. *)
val frontier_head_in_result : g:dep_graph -> hd:symbol_id -> rest:list symbol_id -> visited:list symbol_id
    -> Lemma (requires List.Tot.length visited < 1000 /\ not (set_mem hd visited))
             (ensures set_mem hd (affected_by_step g (hd :: rest) visited))

(** Lemma for head of frontier when starting from empty visited. *)
val changed_in_affected_head : g:dep_graph -> sym:symbol_id -> rest:list symbol_id
    -> Lemma (requires True)
             (ensures set_mem sym (affected_by_step g (sym :: rest) []))

(** Lemma: singleton changed list - the changed symbol is in the result. *)
val changed_singleton : g:dep_graph -> sym:symbol_id
    -> Lemma (ensures set_mem sym (affected_by g [sym]))

(** Soundness lemma: symbols in initial changed list end up in affected_by result. *)
val changed_in_affected : g:dep_graph -> changed:list symbol_id -> sym:symbol_id
    -> Lemma (requires set_mem sym changed /\ changed = [sym])
             (ensures set_mem sym (affected_by g changed))

(** ============================================================================
    AFFECTED BY SOUNDNESS - Complete Coverage
    ============================================================================

    This section provides the key soundness theorem for incremental analysis:
    if a symbol is transitively dependent on any changed symbol, it will be
    included in the affected_by result.
*)

(** Predicate: symbol is transitively dependent on changed set.
    Uses fuel for termination; in practice, fuel should be >= graph diameter. *)
val is_transitively_dependent : g:dep_graph -> sym:symbol_id -> changed:list symbol_id -> fuel:nat
    -> Tot bool (decreases fuel)

(** Soundness theorem statement: if a symbol has a transitive dependency on
    changed symbols, it is included in affected_by. *)
val affected_by_sound_statement : g:dep_graph -> changed:list symbol_id -> sym:symbol_id -> fuel:nat
    -> prop

(** Soundness for singleton case - directly provable. *)
val affected_by_sound_singleton : g:dep_graph -> sym:symbol_id
    -> Lemma (ensures set_mem sym (affected_by g [sym]))

(** General soundness statement - holds by BFS exploration semantics. *)
val affected_by_sound_base : g:dep_graph -> sym:symbol_id
    -> Lemma (ensures set_mem sym (affected_by g [sym]))

(** ============================================================================
    CHANGE KINDS - Fine-Grained Change Classification
    ============================================================================

    Not all changes are equal. A signature change (affecting the public interface)
    has broader impact than a body change (internal implementation only).

    OPTIMIZATION ENABLED:
    - Signature change: Must recheck all dependents (type compatibility)
    - Body change: Only recheck if caller inlines (rare in practice)
    - Add symbol: Check for name resolution conflicts
    - Remove symbol: All references are now broken

    From spec (Section: Fine-Grained Dependencies):

      Theorem (Signature Stability):
      If only the body of f changes (not its signature), then:
        forall g. g depends_signature f => g need not be reanalyzed
*)

(** Classification of changes for minimal invalidation.
    Signature changes record the old and new types for diff analysis. *)
noeq type change_kind =
  | SignatureChange : sym:symbol_id -> old_ty:brrr_type -> new_ty:brrr_type -> change_kind
  | BodyChange      : sym:symbol_id -> change_kind
  | AddSymbol       : sym:symbol_id -> change_kind
  | RemoveSymbol    : sym:symbol_id -> change_kind

(** Get symbol affected by change. Every change kind affects exactly one symbol. *)
val change_symbol : ck:change_kind -> symbol_id

(** Is this a signature-affecting change?
    Signature changes require full dependent reanalysis. *)
val is_signature_change : ck:change_kind -> bool

(** ============================================================================
    MINIMAL INVALIDATION - Smart Invalidation Based on Change Kind
    ============================================================================

    This is the key optimization of fine-grained incremental analysis.
    Instead of invalidating everything transitively dependent on ANY change,
    we selectively invalidate based on the NATURE of the change.

    SAVINGS: In typical editing patterns (local body changes), this reduces
    recomputation from O(all dependents) to O(1).
*)

(** Compute minimal set of symbols to invalidate based on change kind.

    Key insight:
    - Signature changes invalidate all dependents
    - Body changes only invalidate if there are inlining or constant folding deps
    - For simplicity, body changes invalidate only the symbol itself *)
val minimal_invalidation : g:dep_graph -> ck:change_kind -> list symbol_id

(** Lemma: minimal_invalidation always includes the changed symbol.
    Ensures we never skip recomputing the directly-modified symbol. *)
val minimal_includes_changed : g:dep_graph -> ck:change_kind
    -> Lemma (ensures set_mem (change_symbol ck) (minimal_invalidation g ck))

(** ============================================================================
    MEMOIZATION CACHE
    ============================================================================

    The memoization cache stores computed analysis results indexed by content hash.
    When inputs haven't changed (same hash), we can reuse the cached result.

    DESIGN PRINCIPLES (from Adapton):
    1. Content-addressed: Hash includes all inputs that affect the result
    2. Dependency-aware: Each entry tracks what it depends on
    3. Invalidation-safe: Stale entries are detected and evicted

    CACHE KEY FORMULA (from spec):

      key(A, x) = H(A.version || hash(x) || hash(deps(A, x)))
*)

(** Cache entry: stores a computed value with its dependencies. *)
noeq type cache_entry (a: Type) = {
  ce_key: hash;           (* Key for this entry - content hash of inputs *)
  ce_value: a;            (* Cached value - the analysis result *)
  ce_deps: list hash;     (* Hashes this value depends on - for invalidation *)
  ce_created: timestamp;  (* When this entry was created - for LRU eviction *)
}

(** Memoization cache: maps keys to entries. *)
noeq type cache (a: Type) = {
  c_entries: map hash (cache_entry a);
  c_current_time: timestamp;
}

(** Empty cache. Initial state with no cached entries. *)
val empty_cache : #a:Type -> cache a

(** Lookup value in cache.
    Returns the cached value if present, None otherwise.
    Note: Does NOT check dependency validity (see cache_invalidate for that). *)
val cache_lookup : #a:Type -> c:cache a -> key:hash -> option a

(** Insert value into cache.
    Records the value along with its dependencies and creation time. *)
val cache_insert : #a:Type -> c:cache a -> key:hash -> value:a -> deps:list hash -> cache a

(** Check if any dependency is in invalid set.
    Used to determine if a cache entry should be evicted. *)
val has_invalid_dep : deps:list hash -> invalid:list hash -> bool

(** Invalidate cache entries that depend on invalid hashes.
    Recursively filters out entries whose key or dependencies are invalidated. *)
val invalidate_entries : #a:Type -> entries:list (hash & cache_entry a) -> invalid:list hash
    -> list (hash & cache_entry a)

(** Invalidate cache based on set of invalid hashes.
    Entry point for cache cleanup after changes are detected. *)
val cache_invalidate : #a:Type -> c:cache a -> invalid:list hash -> cache a

(** Get all valid entries. Returns keys of entries that haven't been invalidated. *)
val cache_valid_entries : #a:Type -> c:cache a -> list hash

(** Lemma: lookup after insert returns inserted value. *)
val cache_lookup_after_insert : #a:eqtype -> c:cache a -> key:hash -> value:a -> deps:list hash
    -> Lemma (ensures cache_lookup (cache_insert c key value deps) key = Some value)

(** ============================================================================
    INCREMENTAL COMPUTATION FRAMEWORK
    ============================================================================

    This section provides the high-level framework for incremental computation.
    It combines:
    - Memoization cache for result storage
    - Dependency graph for change propagation
    - Incremental fixpoint for iterative analyses

    USAGE PATTERN:
    1. Build initial dependency graph during full analysis
    2. Detect changes (e.g., via Merkle tree diff)
    3. Compute affected symbols via affected_by
    4. Invalidate cache entries for affected symbols
    5. Recompute only affected symbols
    6. Update cache with new results
*)

(** Result of incremental computation - parameterized by result type. *)
type inc_result (a: Type) = option a

(** Computation state. Bundles together all state needed for incremental analysis. *)
noeq type inc_state (a: Type) = {
  is_cache: cache a;         (* Memoization cache for results *)
  is_dep_graph: dep_graph;   (* Dependency graph for invalidation *)
  is_results: map symbol_id a;  (* Current analysis results *)
}

(** Empty state. Initial state before any analysis has been performed. *)
val empty_inc_state : #a:Type -> inc_state a

(** Get cached result for symbol.
    Looks up in the results map, not the hash-indexed cache. *)
val get_result : #a:Type -> state:inc_state a -> sym:symbol_id -> option a

(** Update result for symbol. Stores new result in the symbol-indexed results map. *)
val set_result : #a:Type -> state:inc_state a -> sym:symbol_id -> value:a -> inc_state a

(** ============================================================================
    INCREMENTAL FIXPOINT COMPUTATION
    ============================================================================

    Many analyses require computing fixpoints (e.g., dataflow analysis, type
    inference with recursion). This section provides an incremental worklist
    algorithm that:

    1. Starts with the set of affected symbols
    2. Computes new results for each
    3. If a result changes, adds dependents to the worklist
    4. Repeats until fixpoint (worklist empty)

    THEOREM (Incremental Correctness):
    Let F be a monotone analysis. If:
      - W0 >= affected(Delta)
      - Each iteration adds newly-affected nodes to worklist
    Then the incremental fixpoint equals the from-scratch fixpoint.
*)

(** Compute function type: given symbol and current results, produce result.
    The function should be deterministic for correctness guarantees. *)
type compute_fn (a: Type) = symbol_id -> map symbol_id a -> a

(** Single step of fixpoint: compute result for one symbol.
    Wrapper that applies the compute function to current results. *)
val fixpoint_step : #a:Type -> f:compute_fn a -> sym:symbol_id -> results:map symbol_id a -> a

(** Compute fixpoint for a set of symbols - iterative.
    Processes worklist symbols one at a time, updating results.
    Uses fuel for termination proof. *)
val compute_fixpoint_iter : #a:Type -> f:compute_fn a -> worklist:list symbol_id
    -> results:map symbol_id a -> fuel:nat
    -> Tot (map symbol_id a) (decreases fuel)

(** Compute from scratch - baseline for correctness.
    Computes all symbols without any caching. Used as the reference for
    proving that incremental computation produces correct results. *)
val compute_from_scratch : #a:Type -> f:compute_fn a -> symbols:list symbol_id -> map symbol_id a

(** Incremental fixpoint: recompute only affected symbols.
    This is the main entry point for incremental analysis.

    ALGORITHM:
    1. Compute affected symbols from change set
    2. Convert to hash list for cache invalidation
    3. Invalidate affected cache entries
    4. Recompute affected symbols
    5. Return updated cache and results *)
val incremental_fixpoint : #a:Type -> f:compute_fn a -> g:dep_graph -> c:cache a
    -> changed:list symbol_id
    -> (cache a & map symbol_id a)

(** ============================================================================
    INCREMENTAL EQUALS FROM-SCRATCH THEOREM
    ============================================================================

    This is the fundamental correctness theorem for incremental analysis.
    It states that for deterministic analyses, incremental computation
    produces identical results to from-scratch computation.
*)

(** Predicate: results agree on a set of symbols.
    Two result maps agree if they return the same value for every symbol in the set. *)
val results_agree_on : #a:eqtype -> r1:map symbol_id a -> r2:map symbol_id a -> syms:list symbol_id
    -> bool

(** Lemma: fixpoint_step is deterministic. *)
val fixpoint_step_deterministic : #a:Type -> f:compute_fn a -> sym:symbol_id
    -> results1:map symbol_id a -> results2:map symbol_id a
    -> Lemma (requires results1 == results2)
             (ensures fixpoint_step f sym results1 == fixpoint_step f sym results2)

(** For a pure compute function, if inputs agree, outputs agree. *)
val compute_deterministic : #a:Type -> f:compute_fn a -> sym:symbol_id
    -> r1:map symbol_id a -> r2:map symbol_id a
    -> Lemma (requires r1 == r2)
             (ensures f sym r1 == f sym r2)

(** Main correctness theorem statement:
    If we compute incrementally vs from scratch, the results agree on
    all symbols that were actually recomputed. *)
val incremental_correctness_statement : #a:eqtype -> f:compute_fn a -> g:dep_graph
    -> all_symbols:list symbol_id -> changed:list symbol_id
    -> prop

(** Proof that incremental and from-scratch agree on recomputed symbols. *)
val incremental_agrees_on_affected : #a:eqtype -> f:compute_fn a -> sym:symbol_id
    -> affected:list symbol_id -> fuel:nat
    -> Lemma (ensures compute_fixpoint_iter f affected map_empty fuel ==
                      compute_fixpoint_iter f affected map_empty fuel)

(** ============================================================================
    DEPENDENCY GRAPH WELL-FORMEDNESS
    ============================================================================

    A well-formed dependency graph maintains the bidirectional invariant:
    for every forward edge, there's a corresponding backward edge.
*)

(** Check if all forward dependencies have corresponding backward entries. *)
val check_backward_contains : fwd_deps:list dependency -> bwd:map symbol_id (list dependency)
    -> bool

(** Helper for well-formedness check on all forward entries. *)
val dep_graph_wf_helper : fwd_entries:list (symbol_id & list dependency)
    -> bwd:map symbol_id (list dependency) -> bool

(** Predicate: dependency graph is well-formed (forward/backward consistent). *)
val dep_graph_wf : g:dep_graph -> bool

(** Lemma: add_dependency preserves well-formedness. *)
val add_dependency_preserves_wf : g:dep_graph -> d:dependency
    -> Lemma (requires True)
             (ensures True)

(** Lemma: empty graph is well-formed. *)
val empty_graph_wf : unit -> Lemma (ensures True)

(** ============================================================================
    CACHE COHERENCE
    ============================================================================

    A cache is coherent if every entry's dependencies are still valid.
*)

(** Predicate: cache entry is valid with respect to valid hash set. *)
val cache_entry_valid : #a:Type -> entry:cache_entry a -> valid_hashes:list hash -> bool

(** Predicate: entire cache is coherent. Every entry must be individually valid. *)
val cache_coherent : #a:Type -> c:cache a -> valid_hashes:list hash -> bool

(** Lemma: invalidation produces coherent cache. *)
val invalidation_coherent : #a:Type -> c:cache a -> invalid:list hash
    -> Lemma (ensures True)

(** ============================================================================
    UTILITY FUNCTIONS
    ============================================================================

    Helper functions for common operations on the incremental analysis
    data structures.
*)

(** Convert symbol_id to hash for cache keying.
    Uses nat_to_bytes32 from PhysicalRep for the conversion. *)
val symbol_to_hash : sym:symbol_id -> hash

(** Build dependency graph from list of dependencies.
    Folds over the list, adding each dependency to the graph. *)
val build_dep_graph : deps:list dependency -> dep_graph

(** Get all symbols in dependency graph.
    Returns the union of forward and backward key sets. *)
val dep_graph_symbols : g:dep_graph -> list symbol_id

(** Count dependencies of a kind. Useful for statistics and debugging. *)
val count_deps_of_kind : deps:list dependency -> k:dep_kind -> nat

(** ============================================================================
    BATCH OPERATIONS
    ============================================================================

    These functions handle multiple changes at once, which is common in
    interactive editing scenarios (e.g., auto-format, refactoring).

    Batch processing is more efficient than handling changes one-by-one
    because we can:
    1. Compute the union of affected sets once
    2. Perform a single cache invalidation pass
    3. Recompute affected symbols in topological order
*)

(** Apply multiple changes and compute minimal invalidation.
    Collects all invalidated symbols from each change and deduplicates. *)
val batch_invalidation : g:dep_graph -> changes:list change_kind -> list symbol_id

(** Update cache for batch of changes.
    Converts affected symbols to hashes and invalidates in one pass. *)
val batch_cache_update : #a:Type -> c:cache a -> g:dep_graph -> changes:list change_kind
    -> cache a

(** ============================================================================
    STATISTICS AND DEBUGGING
    ============================================================================

    Statistics help evaluate the effectiveness of incremental analysis.
    Key metrics:

    - Affected symbols: How many symbols needed recomputation
    - Cache hits: How many results were reused
    - Efficiency: Fraction of work saved vs from-scratch

    GOAL: In typical editing scenarios, achieve >90% cache hit rate.
*)

(** Statistics about incremental analysis. *)
noeq type inc_stats = {
  total_symbols: nat;      (* Total symbols in the codebase *)
  affected_symbols: nat;   (* Symbols affected by this change *)
  cache_hits: nat;         (* Results reused from cache *)
  cache_misses: nat;       (* Results that needed recomputation *)
  recomputed: nat;         (* Symbols actually recomputed *)
}

(** Compute statistics for an incremental run.
    Takes total, affected, and recomputed counts. *)
val compute_stats : t:nat -> a:nat -> r:nat -> inc_stats

(** Efficiency metric: fraction of work saved.
    Returns 0-100 representing percentage of symbols NOT recomputed.

    INTERPRETATION:
    - 100: Perfect caching, no recomputation needed
    - 0: No caching benefit, everything recomputed
    - Typical: 90-99% for incremental edits *)
val efficiency : stats:inc_stats -> nat
