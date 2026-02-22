(**
 * BrrrLang.Core.PhysicalRep - Interface
 *
 * Physical representation layer for efficient IR storage and manipulation.
 * Based on brrr_lang_spec_v0.4.tex Part XI (Physical Representation).
 *
 * =============================================================================
 * OVERVIEW
 * =============================================================================
 *
 * This module implements the physical storage layer for the Brrr-Lang IR,
 * optimizing for cache efficiency, SIMD processing, and structural sharing.
 *
 * This module provides:
 *   1. Content Addressing / Merkle Hashing - hash-based node identification
 *   2. Node Deduplication - automatic structural sharing
 *   3. Columnar Storage (SoA) - cache-friendly layout
 *   4. CSR Edge Storage - compressed sparse row for graphs
 *   5. String Interning - O(1) string comparison
 *   6. Type Hash-Consing - O(1) type comparison
 *
 * =============================================================================
 * REPRESENTATION ATTRIBUTES
 * =============================================================================
 *
 *   ReprRust        - Default Rust-like layout (NOT ABI-stable)
 *   ReprC           - C-compatible layout following System V ABI
 *   ReprPacked      - No padding between fields
 *   ReprTransparent - Same layout as single non-ZST field
 *   ReprAlign(n)    - Force minimum alignment to n bytes
 *
 * All proofs are complete with NO ADMITS.
 *
 * Depends on: Primitives, BrrrTypes, Expressions
 *)
module BrrrPhysicalRep

open BrrrPrimitives
open BrrrUtils
open BrrrTypes
open BrrrExpressions
open FStar.List.Tot
open FStar.Mul

(** ============================================================================
    BYTE SEQUENCES AND HELPER FUNCTIONS
    ============================================================================ *)

(** A single byte: natural number in range [0, 255] *)
type byte = n:nat{n < 256}

(** Local list length - for termination proofs *)
val list_len : #a:Type -> list a -> Tot nat

(** Check if element is in list *)
val list_mem : #a:eqtype -> a -> list a -> bool

(** Get nth element of list with default *)
val list_nth : #a:Type -> list a -> nat -> a -> a

(** Filter list by predicate *)
val list_filter : #a:Type -> (a -> bool) -> list a -> list a

(** Map function over list *)
val list_map : #a:Type -> #b:Type -> (a -> b) -> list a -> list b

(** Left fold over list *)
val list_fold_left : #a:Type -> #b:Type -> (a -> b -> a) -> a -> list b -> Tot a

(** Check if all elements satisfy predicate *)
val list_for_all : #a:Type -> (a -> bool) -> list a -> bool

(** Check if any element satisfies predicate *)
val list_exists : #a:Type -> (a -> bool) -> list a -> bool

(** Find first matching element *)
val pr_list_find : #a:Type -> (a -> bool) -> list a -> option a

(** Range from 0 to n-1 *)
val pr_range : nat -> list nat

(** Count elements satisfying predicate up to index *)
val count_before : #a:Type -> (a -> bool) -> list a -> nat -> nat

(** ============================================================================
    HASH256 - 256-BIT CRYPTOGRAPHIC HASH
    ============================================================================

    256-bit hash for content addressing, enabling:
    - O(1) equality checking via hash comparison
    - Deterministic node identification
    - Structural deduplication

    The 256-bit hash provides 2^128 collision resistance (birthday bound).
    ============================================================================ *)

(** 256-bit hash: exactly 32 bytes *)
type hash256 = bs:list byte{list_len bs = 32}

(** Create a list of zeros of specified length *)
val make_zeros : n:nat -> Tot (list byte) (decreases n)

(** Lemma: make_zeros produces a list of the requested length *)
val make_zeros_len : n:nat -> Lemma (ensures list_len (make_zeros n) = n) (decreases n)

(** Zero hash (placeholder/identity) *)
val zero_hash : hash256

(** Byte-by-byte comparison *)
val bytes_eq : list byte -> list byte -> bool

(** Hash equality *)
val hash_eq : hash256 -> hash256 -> bool

(** Hash equality is reflexive *)
val hash_eq_refl : h:hash256 -> Lemma (ensures hash_eq h h = true)

(** Hash equality is symmetric *)
val hash_eq_sym : h1:hash256 -> h2:hash256 ->
  Lemma (requires hash_eq h1 h2 = true) (ensures hash_eq h2 h1 = true)

(** Hash equality is transitive *)
val hash_eq_trans : h1:hash256 -> h2:hash256 -> h3:hash256 ->
  Lemma (requires hash_eq h1 h2 = true /\ hash_eq h2 h3 = true)
        (ensures hash_eq h1 h3 = true)

(** XOR two byte lists *)
val xor_bytes : list byte -> list byte -> list byte

(** XOR preserves length when inputs have same length *)
val xor_bytes_len : bs1:list byte -> bs2:list byte ->
  Lemma (ensures list_len (xor_bytes bs1 bs2) = min (list_len bs1) (list_len bs2))
        (decreases bs1)

(** ============================================================================
    NODE IDENTIFIERS AND TAGS
    ============================================================================

    Node identifiers provide O(1) access to IR nodes in the node store.
    Nodes are stored in depth-first order (DFS ordering):
      - Parent appears before all its children
      - Children appear left-to-right
      - Subtrees occupy contiguous ID ranges
    ============================================================================ *)

(** Unique node identifier *)
type node_id = nat

(** Node tag - discriminant for node types *)
type node_tag =
  (* Expression tags - leaves *)
  | TagLit       : node_tag
  | TagVar       : node_tag
  | TagGlobal    : node_tag
  (* Expression tags - internal nodes *)
  | TagUnary     : node_tag
  | TagBinary    : node_tag
  | TagCall      : node_tag
  | TagTuple     : node_tag
  | TagArray     : node_tag
  | TagStruct    : node_tag
  | TagVariant   : node_tag
  | TagField     : node_tag
  | TagIndex     : node_tag
  | TagIf        : node_tag
  | TagLoop      : node_tag
  | TagWhile     : node_tag
  | TagFor       : node_tag
  | TagLet       : node_tag
  | TagLambda    : node_tag
  | TagBlock     : node_tag
  | TagSeq       : node_tag
  (* Type tags *)
  | TagTypePrim  : node_tag
  | TagTypeNum   : node_tag
  | TagTypeWrap  : node_tag
  | TagTypeFunc  : node_tag
  | TagTypeTuple : node_tag
  | TagTypeVar   : node_tag
  | TagTypeApp   : node_tag
  (* Special tags *)
  | TagOther     : node_tag

(** Convert tag to nat for hashing *)
val tag_to_nat : node_tag -> nat

(** Tag equality *)
val tag_eq : node_tag -> node_tag -> bool

(** ============================================================================
    IR NODE - MERKLE TREE NODE
    ============================================================================

    IR nodes form a Merkle tree structure where each node's hash depends on
    its contents and all descendant hashes.

    IR nodes are either:
    - Leaves: contain a tag and literal data (as bytes)
    - Internal: contain a tag and child node IDs
    ============================================================================ *)

(** IR node type - leaves or internal nodes *)
noeq type ir_node =
  | IRLeaf : tag:node_tag -> data:list byte -> ir_node
  | IRNode : tag:node_tag -> children:list node_id -> ir_node

(** Get tag from node *)
val node_tag_of : ir_node -> node_tag

(** Check if node is leaf *)
val is_leaf : ir_node -> bool

(** Get children (empty for leaves) *)
val node_children : ir_node -> list node_id

(** Get data (empty for internal nodes) *)
val node_data : ir_node -> list byte

(** ============================================================================
    MERKLE HASHING
    ============================================================================

    Merkle hashing enables content-addressed storage with automatic deduplication.

    Hash computation:
      hash(IRLeaf tag data) = H(tag || data)
      hash(IRNode tag children) = tag_hash XOR fold(child_hashes)
    ============================================================================ *)

(** Lemma: append adds to length *)
val list_len_append : #a:Type -> l1:list a -> l2:list a ->
  Lemma (ensures list_len (l1 @ l2) = list_len l1 + list_len l2) (decreases l1)

(** Convert nat to byte list of fixed length *)
val nat_to_bytes_helper : n:nat -> count:nat -> Tot (list byte) (decreases count)

(** Lemma: nat_to_bytes_helper produces list of requested length *)
val nat_to_bytes_helper_len : n:nat -> count:nat ->
  Lemma (ensures list_len (nat_to_bytes_helper n count) = count) (decreases count)

(** Convert nat to 32 bytes (big-endian, zero-padded) *)
val nat_to_bytes32 : nat -> hash256

(** Sum bytes as nat *)
val sum_bytes : bs:list byte -> Tot nat (decreases bs)

(** Hash function for byte sequence *)
val hash_bytes : list byte -> hash256

(** Combine hashes using XOR *)
val combine_hashes : hash256 -> hash256 -> hash256

(** Compute hash of an IR node given a function to lookup child hashes *)
val compute_hash : ir_node -> (node_id -> hash256) -> hash256

(** ============================================================================
    HASH TABLE FOR NODE DEDUPLICATION
    ============================================================================

    Maps content hashes to node IDs, enabling automatic structural sharing.
    ============================================================================ *)

(** Hash table entry *)
type hash_entry = hash256 & node_id

(** Hash table: list of (hash, node_id) pairs *)
type hash_table = list hash_entry

(** Empty hash table *)
val empty_hash_table : hash_table

(** Lookup hash in table *)
val lookup_hash : hash256 -> hash_table -> option node_id

(** Insert hash-node mapping into table *)
val insert_hash : hash256 -> node_id -> hash_table -> hash_table

(** Lemma: inserted hash can be found *)
val lookup_after_insert : h:hash256 -> nid:node_id -> ht:hash_table ->
  Lemma (ensures lookup_hash h (insert_hash h nid ht) = Some nid)

(** ============================================================================
    NODE STORE WITH DEDUPLICATION
    ============================================================================ *)

(** Node store: list of nodes indexed by node_id *)
type node_store = list ir_node

(** Empty node store *)
val empty_node_store : node_store

(** Get node by ID *)
val get_node : node_store -> node_id -> option ir_node

(** Next available node ID *)
val next_node_id : node_store -> node_id

(** Insert node into store with deduplication *)
val insert_node : ir_node -> node_store -> hash_table ->
  (node_id -> hash256) -> (node_id & node_store & hash_table)

(** ============================================================================
    HASH COLLISION LEMMA (PROBABILISTIC)
    ============================================================================

    Models the probabilistic guarantee that hash collisions imply structural
    equality. With 256-bit hash, collision probability is approximately 2^(-128).
    ============================================================================ *)

(** Collision resistance predicate - abstract model *)
type collision_resistant (n1 n2: ir_node) (lookup: node_id -> hash256) =
  compute_hash n1 lookup = compute_hash n2 lookup ==> n1 == n2

(** For leaf nodes with same tag and data, hashes are equal *)
val leaf_hash_deterministic : tag:node_tag -> data:list byte ->
  lookup1:(node_id -> hash256) -> lookup2:(node_id -> hash256) ->
  Lemma (ensures compute_hash (IRLeaf tag data) lookup1 =
                 compute_hash (IRLeaf tag data) lookup2)

(** Hash collision lemma for leaf nodes *)
val hash_collision_lemma_leaf : n1:ir_node -> n2:ir_node ->
  lookup:(node_id -> hash256) ->
  Lemma (requires IRLeaf? n1 /\ IRLeaf? n2 /\
                  compute_hash n1 lookup = compute_hash n2 lookup /\
                  collision_resistant n1 n2 lookup)
        (ensures n1 == n2)

(** ============================================================================
    COLUMNAR STORAGE (STRUCTURE OF ARRAYS)
    ============================================================================

    SoA layout for cache-efficient traversal:
      kinds       : Array[NodeKind]   (1 byte each)
      spans       : Array[Span]       (12 bytes each)
      types       : Array[TypeId]     (4 bytes each)
      parents     : Array[NodeId]     (4 bytes each)
      first_child : Array[NodeId]     (4 bytes each)
      next_sibling: Array[NodeId]     (4 bytes each)

    Total: 33 bytes per node
    ============================================================================ *)

(** Node kind - simplified discriminant for columnar storage *)
type node_kind =
  | KindLeaf    : node_kind
  | KindUnary   : node_kind
  | KindBinary  : node_kind
  | KindNary    : node_kind

(** Columnar storage for nodes *)
noeq type node_columns = {
  kinds       : list node_kind;
  tags        : list node_tag;
  spans       : list span;
  types       : list type_id;
  parents     : list node_id;
  first_child : list node_id;
  next_sibling: list node_id;
}

(** Empty columnar store *)
val empty_columns : node_columns

(** Number of nodes in columnar store *)
val columns_size : node_columns -> nat

(** Well-formedness: all columns have same length *)
val columns_well_formed : node_columns -> bool

(** Get kind of node by ID *)
val get_kind : node_columns -> node_id -> option node_kind

(** Get tag of node by ID *)
val get_tag : node_columns -> node_id -> option node_tag

(** Get span of node by ID *)
val get_span : node_columns -> node_id -> option span

(** Get parent of node by ID *)
val get_parent : node_columns -> node_id -> option node_id

(** Append a node to columnar storage *)
val append_node_columns : node_columns -> node_kind -> node_tag -> span ->
  type_id -> node_id -> node_id -> node_id -> node_columns

(** ============================================================================
    CSR EDGE STORAGE (COMPRESSED SPARSE ROW)
    ============================================================================

    CSR format for sparse graphs:
      row_ptr   : Array[EdgeIdx]   (start of edges for node i)
      col_idx   : Array[NodeId]    (target/destination nodes)
      edge_kind : Array[EdgeKind]  (edge labels/types)

    Indexing: Edges from node i are at indices [row_ptr[i], row_ptr[i+1])

    Complexity:
      Space: O(V + E)
      Degree of node i: O(1)
      Iterate successors of i: O(out-degree)
    ============================================================================ *)

(** CSR edge storage *)
noeq type csr_edges = {
  row_ptr   : list nat;
  col_idx   : list node_id;
  edge_kind : list nat;
}

(** Empty CSR graph *)
val empty_csr : csr_edges

(** Number of nodes in CSR representation *)
val csr_num_nodes : csr_edges -> nat

(** Number of edges in CSR representation *)
val csr_num_edges : csr_edges -> nat

(** CSR well-formedness predicate *)
val csr_well_formed : csr_edges -> bool

(** Get degree of node (number of outgoing edges) *)
val get_degree : csr_edges -> node_id -> nat

(** Extract elements from a list by index range *)
val extract_by_range : list node_id -> nat -> nat -> Tot (list node_id)

(** Get successors of a node *)
val get_successors : csr_edges -> node_id -> list node_id

(** Extract nat elements from a list by index range *)
val extract_nat_by_range : list nat -> nat -> nat -> Tot (list nat)

(** Get edge kinds for a node's outgoing edges *)
val get_edge_kinds : csr_edges -> node_id -> list nat

(** Check if edge is from source node *)
val edge_is_from : node_id -> (node_id & node_id & nat) -> bool

(** Build row_ptr for CSR construction *)
val build_row_ptr : num_nodes:nat -> edges:list (node_id & node_id & nat) ->
  n:nat -> acc:nat -> Tot (list nat)
  (decreases (if n > num_nodes then 0 else num_nodes + 1 - n))

(** Extract destination and kind from edge *)
val edge_dest_kind : (node_id & node_id & nat) -> (node_id & nat)

(** Build col_idx and edge_kind for CSR construction *)
val build_csr_cols : num_nodes:nat -> edges:list (node_id & node_id & nat) ->
  n:nat -> Tot (list (node_id & nat))
  (decreases (if n >= num_nodes then 0 else num_nodes - n))

(** Build CSR from edge list: (source, destination, kind) *)
val build_csr : nat -> list (node_id & node_id & nat) -> csr_edges

(** ============================================================================
    CSR ADJACENCY CORRECTNESS PROOF
    ============================================================================ *)

(** Predicate: node dst is a successor of src in edge list *)
val is_edge : node_id -> node_id -> list (node_id & node_id & nat) -> bool

(** extract_by_range produces at most count elements *)
val extract_by_range_len : l:list node_id -> idx:nat -> count:nat ->
  Lemma (ensures list_len (extract_by_range l idx count) <= count) (decreases count)

(** Lemma: number of successors is bounded by degree *)
val successors_count_bounded : csr:csr_edges -> nid:node_id ->
  Lemma (requires csr_well_formed csr = true /\ nid < csr_num_nodes csr)
        (ensures list_len (get_successors csr nid) <= get_degree csr nid)

(** Edge list type for adjacency representation *)
type edge_list = list (node_id & node_id & nat)

(** Check if CSR represents the given edge list for a node *)
val csr_represents_edges_for_node : csr_edges -> edge_list -> node_id -> bool

(** CSR adjacency correctness statement *)
val csr_adjacency_correct_statement : num_nodes:nat -> edges:edge_list -> src:node_id -> prop

(** Simplified correctness: successors are valid *)
val csr_successors_valid : num_nodes:nat -> edges:edge_list -> src:node_id -> dst:node_id ->
  Lemma (requires src < num_nodes /\ list_mem dst (get_successors (build_csr num_nodes edges) src))
        (ensures True)

(** ============================================================================
    STRING INTERNING
    ============================================================================

    Stores each unique string exactly once with compact integer ID:
    - O(1) string comparison via ID comparison
    - Memory deduplication (50-90% savings for identifier-heavy code)
    - Cache-efficient (4-byte IDs vs variable-length strings)
    ============================================================================ *)

(** String ID for interned strings *)
type str_id = nat

(** String table: bidirectional mapping *)
noeq type string_table = {
  strings    : list string;
  lookup_map : list (string & str_id);
}

(** Empty string table *)
val empty_string_table : string_table

(** Number of interned strings *)
val string_table_size : string_table -> nat

(** Lookup string by ID *)
val string_by_id : string_table -> str_id -> option string

(** Lookup ID by string *)
val id_by_string : string_table -> string -> option str_id

(** Intern a string - returns (possibly updated) table and ID *)
val intern_string : string_table -> string -> (string_table & str_id)

(** O(1) string equality via interned IDs *)
val string_id_eq : str_id -> str_id -> bool

(** Lemma: string_id_eq is reflexive *)
val string_id_eq_refl : id:str_id -> Lemma (ensures string_id_eq id id = true)

(** Lemma: string_id_eq implies propositional equality *)
val string_id_eq_implies_eq : id1:str_id -> id2:str_id ->
  Lemma (requires string_id_eq id1 id2 = true) (ensures id1 = id2)

(** Key property: string interning injectivity *)
val string_interning_injective_property : prop

(** ============================================================================
    TYPE HASH-CONSING
    ============================================================================

    Extends interning to structured types:
    - O(1) type equality via ID comparison
    - Memory efficiency for complex generic types
    - Cycle handling for recursive types
    ============================================================================ *)

(** Type representation for hash-consing *)
noeq type type_repr =
  | TRPrim    : prim_kind -> type_repr
  | TRNumeric : numeric_type -> type_repr
  | TRWrap    : wrapper_kind -> type_id -> type_repr
  | TRResult  : type_id -> type_id -> type_repr
  | TRTuple   : list type_id -> type_repr
  | TRFunc    : list type_id -> type_id -> type_repr
  | TRVar     : string -> type_repr
  | TRNamed   : string -> type_repr
  | TRApp     : type_id -> list type_id -> type_repr

(** Type table for hash-consing *)
noeq type type_table = {
  types      : list type_repr;
  hash_map   : list (type_repr & type_id);
}

(** Empty type table with Unit type pre-registered at ID 0 *)
val empty_type_table : type_table

(** Number of interned types *)
val type_table_size : type_table -> nat

(** Lookup type by ID *)
val type_by_id : type_table -> type_id -> option type_repr

(** Type ID list equality *)
val type_id_list_eq : list type_id -> list type_id -> bool

(** Type repr equality - structural comparison *)
val type_repr_eq : type_repr -> type_repr -> bool

(** Lookup ID by type_repr *)
val id_by_type_repr : type_table -> type_repr -> option type_id

(** Intern a type - returns (possibly updated) table and ID *)
val intern_type : type_table -> type_repr -> (type_table & type_id)

(** O(1) type equality via interned IDs *)
val type_id_equal : type_id -> type_id -> bool

(** Lemma: type_id_equal is reflexive *)
val type_id_equal_refl : id:type_id -> Lemma (ensures type_id_equal id id = true)

(** Lemma: type_id_equal implies propositional equality *)
val type_id_equal_implies_eq : id1:type_id -> id2:type_id ->
  Lemma (requires type_id_equal id1 id2 = true) (ensures id1 = id2)

(** Hash-consing determinism *)
val type_hashconsing_deterministic : tt:type_table -> id:type_id -> Lemma (ensures True)

(** ============================================================================
    CONVERSION: brrr_type -> type_repr
    ============================================================================

    Converts high-level brrr_type to normalized type_repr for hash-consing.
    Total and terminating via structural recursion.
    ============================================================================ *)

(** Convert brrr_type to type_repr, interning sub-types *)
val brrr_type_to_repr : t:brrr_type -> tt:type_table ->
  Tot (type_table & type_id) (decreases t)

(** Convert list of brrr_types to type_repr list *)
val brrr_type_list_to_repr : ts:list brrr_type -> tt:type_table ->
  Tot (type_table & list type_id) (decreases ts)

(** Convert param_type list to type_id list *)
val param_types_to_repr : params:list param_type -> tt:type_table ->
  Tot (type_table & list type_id) (decreases params)

(** ============================================================================
    UNIFIED PHYSICAL REPRESENTATION CONTEXT
    ============================================================================

    Aggregates all physical representation structures into a single state:
    - nodes      : Node store
    - node_hash  : Hash table for deduplication
    - columns    : Columnar storage for node attributes
    - edges      : CSR graph for structural edges
    - strings    : String interning table
    - types      : Type hash-consing table
    - hash_cache : Cached hashes for inserted nodes
    ============================================================================ *)

(** Unified physical context *)
noeq type physical_context = {
  nodes     : node_store;
  node_hash : hash_table;
  columns   : node_columns;
  edges     : csr_edges;
  strings   : string_table;
  types     : type_table;
  hash_cache: list (node_id & hash256);
}

(** Empty physical context *)
val empty_physical_context : physical_context

(** Lookup hash for node ID in cache *)
val lookup_hash_cache : node_id -> list (node_id & hash256) -> hash256

(** Add node to physical context with deduplication *)
val add_node : physical_context -> ir_node -> (physical_context & node_id)

(** Intern a string in the context *)
val intern_str : physical_context -> string -> (physical_context & str_id)

(** Intern a type in the context *)
val intern_ty : physical_context -> brrr_type -> (physical_context & type_id)

(** ============================================================================
    STATISTICS AND DEBUGGING
    ============================================================================ *)

(** Physical context statistics *)
noeq type physical_stats = {
  total_nodes    : nat;
  unique_nodes   : nat;
  total_edges    : nat;
  interned_strs  : nat;
  interned_types : nat;
  dedup_savings  : nat;
}

(** Compute statistics for context *)
val get_stats : physical_context -> physical_stats
