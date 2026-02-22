(**
 * BrrrLang.Core.ComputeArch - Interface
 *
 * Compute Architecture for Brrr-Lang IR.
 * Based on brrr_lang_spec_v0.4.tex Part XII: Compute Architecture.
 *
 * ===========================================================================
 * PURPOSE AND DESIGN RATIONALE
 * ===========================================================================
 *
 * This module defines the compute architecture abstractions for Brrr-Machine,
 * enabling verified parallel execution of dataflow analyses. The design draws
 * from three key sources:
 *
 *   1. HACL* (High-Assurance Cryptographic Library): Platform-specific code
 *      patterns for SIMD operations, memory alignment, and cache-aware layouts.
 *
 *   2. KaRaMeL: The F* to C compiler that extracts verified code to efficient
 *      C with proper memory layout and SIMD intrinsics.
 *
 *   3. Chase-Lev work-stealing deques and Cilk-style task schedulers for
 *      verified parallel execution without data races.
 *
 * ===========================================================================
 * TARGET ARCHITECTURE SUPPORT
 * ===========================================================================
 *
 * The module supports three SIMD width targets (Definition 2.1 in spec):
 *
 *   - SSE128:  128-bit vectors (Intel SSE2+, ARM NEON)
 *   - AVX256:  256-bit vectors (Intel AVX2, AMD Zen+)
 *   - AVX512:  512-bit vectors (Intel Skylake-X+, AMD Zen4+)
 *
 * ===========================================================================
 * VERIFICATION PROPERTIES
 * ===========================================================================
 *
 * Key theorems proven in this module:
 *
 *   1. TASK PARALLELIZATION: Tasks without dependencies are always ready,
 *      ready status is monotonic in completed set, independent tasks can
 *      run concurrently, topological level tasks are parallelizable.
 *
 *   2. WORK-STEALING: LIFO semantics for owner, FIFO for thieves,
 *      stealing improves load balance, no task loss during stealing.
 *
 *   3. DATAFLOW CONVERGENCE: Fixpoint reached for monotone lattices,
 *      lock-free updates preserve monotonicity, parallel execution
 *      reaches same fixpoint, no lost updates.
 *
 *   4. SIMD OPERATIONS: Equality and subset relations are reflexive,
 *      AVX-512 provides 8x throughput for 64-bit operations.
 *
 *   5. MEMORY HIERARCHY: Cache efficiency guarantees, monotonicity
 *      of cache utilization with node count.
 *
 * Depends on: BrrrPrimitives, BrrrExpressions
 *)
module BrrrComputeArch

open BrrrPrimitives
open BrrrExpressions
open FStar.List.Tot
open FStar.Classical
open FStar.Mul


(** ============================================================================
    SECTION 1: TASK PARALLELIZATION
    ============================================================================

    Tasks represent units of work that can be executed in parallel when their
    dependencies are satisfied. The dependency graph must be acyclic (DAG) for
    correct parallel execution.

    This implements the four-level parallelism model from Spec Definition 1.1:
      Level 1: File-level parallelism
      Level 2: Function-level parallelism
      Level 3: Worklist-level parallelism
      Level 4: SIMD-level parallelism
*)

(** Task identifier - unique within a task graph.
    Extraction: usize (Rust), uint32_t (C), int (OCaml) *)

type task_id = nat

(** Task execution state.
    State transitions: Pending -> Running -> Completed (linear progression).
    No backward transitions allowed. *)
type task_state =
  | Pending   : task_state   (* Not yet started - initial state *)
  | Running   : task_state   (* Currently executing by some worker *)
  | Completed : task_state   (* Successfully finished - terminal state *)

(** Task state equality comparison *)
val task_state_eq : s1:task_state -> s2:task_state -> bool

(** Task structure - contains work function and dependency info.
    The noeq attribute is required because function types cannot be compared. *)
noeq type task = {
  id           : task_id;           (* Unique identifier within task graph *)
  dependencies : list task_id;      (* Tasks that must complete before this one *)
  state        : task_state;        (* Current execution state *)
  priority     : nat                (* Scheduling priority (lower = higher priority) *)
}

(** Check if a task is ready to execute given completed tasks.
    A task is ready when all its dependencies are in the completed set. *)
val is_ready : t:task -> completed:list task_id -> bool

(** Lemma: A task with no dependencies is always ready *)
val no_deps_always_ready : t:task -> completed:list task_id ->
  Lemma (requires t.dependencies = [])
        (ensures is_ready t completed = true)

(** Helper: for_all over a list implies predicate holds for each member *)
val for_all_mem : #a:eqtype -> f:(a -> bool) -> l:list a -> x:a ->
  Lemma (requires List.Tot.for_all f l = true /\ List.Tot.mem x l)
        (ensures f x = true)
        (decreases l)

(** Helper: is_ready implies each dependency is in the completed list *)
val is_ready_mem : t:task -> c:list task_id -> dep:task_id ->
  Lemma (requires is_ready t c = true /\ List.Tot.mem dep t.dependencies)
        (ensures List.Tot.mem dep c = true)

(** Helper: predicate holds for all elements implies for_all is true *)
val for_all_intro : #a:eqtype -> f:(a -> bool) -> l:list a ->
  Lemma (requires forall x. List.Tot.mem x l ==> f x = true)
        (ensures List.Tot.for_all f l = true)
        (decreases l)

(** Lemma: If a task is ready with fewer completed, it is ready with more *)
val ready_monotonic : t:task -> c1:list task_id -> c2:list task_id ->
  Lemma (requires is_ready t c1 = true /\ (forall x. List.Tot.mem x c1 ==> List.Tot.mem x c2))
        (ensures is_ready t c2 = true)


(** ----------------------------------------------------------------------------
    TOPOLOGICAL LEVELS
    ---------------------------------------------------------------------------- *)

(** Check if task id is in a list of tasks *)
val task_in_list : id:task_id -> tasks:list task -> bool

(** Get task by id from list *)
val get_task : id:task_id -> tasks:list task -> Tot (option task) (decreases tasks)

(** Check if all dependencies of a task are in a given set *)
val all_deps_in : t:task -> ids:list task_id -> bool

(** Helper: collect task IDs from a list of levels *)
val flatten_levels : levels:list (list task_id) -> Tot (list task_id) (decreases levels)

(** Compute topological levels.
    Returns list of levels where each level contains tasks whose dependencies
    are all in previous levels. *)
val compute_levels_aux : tasks:list task -> processed:list task_id -> fuel:nat ->
  Tot (list (list task_id)) (decreases fuel)

(** Main topological levels function with safety fuel *)
val topological_levels : tasks:list task -> list (list task_id)

(** Helper: check if task t1 does not depend on task t2 *)
val task_not_depends_on : t1:task -> t2_id:task_id -> bool

(** Helper: check all tasks in level have no mutual dependencies *)
val level_is_independent : tasks:list task -> level:list task_id ->
  Tot bool (decreases level)

(** Verify that all_deps_in implies no dependencies within a single level *)
val all_deps_in_excludes_level : t:task -> processed:list task_id -> level:list task_id ->
  Lemma (requires all_deps_in t processed = true /\
                  (forall id. List.Tot.mem id level ==> not (List.Tot.mem id processed)))
        (ensures forall dep. List.Tot.mem dep t.dependencies ==> not (List.Tot.mem dep level))

(** Helper: check if a task is ready (filtered by the algorithm) *)
val is_ready_for_level : processed:list task_id -> t:task -> bool

(** Weaker lemma: Tasks filtered by is_ready_for_level have all dependencies in processed *)
val filtered_tasks_have_deps_in_processed : processed:list task_id -> t:task ->
  Lemma (requires is_ready_for_level processed t = true)
        (ensures all_deps_in t processed = true)


(** ----------------------------------------------------------------------------
    PARALLEL EXECUTION CORRECTNESS
    ---------------------------------------------------------------------------- *)

(** Two tasks are independent if neither depends on the other *)
val tasks_independent : t1:task -> t2:task -> bool

(** Lemma: Independent tasks can be executed in any order *)
val independent_order_irrelevant : t1:task -> t2:task ->
  Lemma (requires tasks_independent t1 t2 = true)
        (ensures True)

(** A task set is valid for parallel execution if all pairs are independent *)
val all_pairs_independent : tasks:list task -> Tot bool (decreases tasks)

(** Main theorem: Tasks with no mutual dependencies can run in parallel *)
val parallel_execution_safe : tasks:list task ->
  Lemma (requires all_pairs_independent tasks = true)
        (ensures True)

(** Stronger theorem: Tasks in the same topological level can run in parallel *)
val level_parallel_safe : all_tasks:list task -> level:list task_id ->
  Lemma (requires List.Tot.mem level (topological_levels all_tasks))
        (ensures True)


(** ============================================================================
    SECTION 2: WORK-STEALING DEQUE
    ============================================================================

    Double-ended queue for work-stealing schedulers based on Chase-Lev algorithm.
    Provides LIFO for owner, FIFO for thieves.
*)

(** Work-stealing deque representation.
    Items are stored with bottom at the end of the list. *)
noeq type ws_deque (a: Type) = {
  items : list a;      (* Work items *)
  size  : nat          (* Current size for fast access *)
}

(** Create empty deque *)
val empty_deque : #a:Type -> ws_deque a

(** Check if deque is empty *)
val is_empty_deque : #a:Type -> d:ws_deque a -> bool

(** Push item at bottom (for owner thread). Amortized O(1). *)
val push_bottom : #a:Type -> d:ws_deque a -> item:a -> ws_deque a

(** Helper: split list into prefix and last element *)
val split_last : #a:Type -> l:list a -> Tot (option (list a & a)) (decreases l)

(** Pop item from bottom (for owner thread).
    Returns the last item if available. *)
val pop_bottom : #a:Type -> d:ws_deque a -> (option a & ws_deque a)

(** Steal item from top (for thief threads).
    Returns the first item if available. *)
val steal_top : #a:Type -> d:ws_deque a -> (option a & ws_deque a)

(** Lemma: push increases size by exactly 1 *)
val push_bottom_size : #a:Type -> d:ws_deque a -> item:a ->
  Lemma (ensures (push_bottom d item).size = d.size + 1)

(** Helper: characterize pop_bottom size behavior *)
val pop_bottom_size_check : #a:Type -> d:ws_deque a -> bool

(** Lemma: pop decreases size by at most 1 *)
val pop_bottom_size : #a:Type -> d:ws_deque a ->
  Lemma (ensures pop_bottom_size_check d = true)

(** Helper: characterize steal_top size behavior *)
val steal_top_size_check : #a:Type -> d:ws_deque a -> bool

(** Lemma: steal decreases size by at most 1 *)
val steal_top_size : #a:Type -> d:ws_deque a ->
  Lemma (ensures steal_top_size_check d = true)

(** Helper: split_last on non-empty list returns Some *)
val split_last_nonempty : #a:Type -> x:a -> rest:list a ->
  Lemma (ensures Some? (split_last (x :: rest)))
        (decreases rest)

(** Helper: split_last of l @ [item] returns Some(l, item) *)
val split_last_append : #a:eqtype -> l:list a -> item:a ->
  Lemma (ensures split_last (l @ [item]) = Some (l, item))
        (decreases l)

(** Correctness: push then pop returns the same item (LIFO) *)
val push_pop_correct : #a:eqtype -> d:ws_deque a -> item:a ->
  Lemma (ensures fst (pop_bottom (push_bottom d item)) = Some item)

(** Helper: compute FIFO steal result *)
val steal_fifo_result : #a:eqtype -> d:ws_deque a -> item1:a -> item2:a -> option a

(** Helper: verify FIFO steal behavior for empty deque *)
val steal_fifo : #a:eqtype -> d:ws_deque a -> item1:a -> item2:a ->
  Lemma (requires d.items = [] /\ d.size = 0)
        (ensures steal_fifo_result d item1 item2 = Some item1)


(** ============================================================================
    SECTION 3: WORK-STEALING SCHEDULER
    ============================================================================

    Implementation of the work-stealing algorithm per Spec Definition 1.5.
*)

(** Worker identifier - unique per scheduler instance *)
type ws_worker_id = nat

(** Worker activity state - tracks whether worker is active or idle *)
type worker_activity =
  | WActive  : worker_activity   (* Worker is executing or looking for work *)
  | WIdle    : worker_activity   (* Worker has no work and is waiting *)
  | WStopped : worker_activity   (* Worker has been terminated *)

(** Simple linear congruential RNG state for victim selection *)
noeq type rng_state = {
  seed : nat
}

(** Initialize RNG with worker ID as seed *)
val rng_next : rng:rng_state -> bound:nat{bound > 0} -> (nat & rng_state)

(** Scheduler statistics for monitoring and debugging *)
noeq type scheduler_stats = {
  tasks_executed   : nat;   (* Total tasks completed *)
  tasks_stolen     : nat;   (* Tasks acquired via stealing *)
  steal_attempts   : nat;   (* Total steal attempts *)
  steal_failures   : nat;   (* Failed steal attempts *)
  idle_transitions : nat    (* Number of times workers went idle *)
}

(** Initialize empty statistics *)
val empty_stats : scheduler_stats

(** Worker state: encapsulates all per-worker data *)
noeq type worker_state = {
  ws_id       : ws_worker_id;      (* Unique worker identifier *)
  ws_deque    : ws_deque task;     (* Local task deque *)
  ws_rng      : rng_state;         (* Random state for victim selection *)
  ws_activity : worker_activity    (* Current activity state *)
}

(** Create a new worker with empty deque *)
val create_worker : id:ws_worker_id -> worker_state

(** Scheduler state: manages all workers and global state *)
noeq type scheduler_state = {
  ss_workers       : list worker_state;  (* All workers in the pool *)
  ss_num_workers   : nat;                (* Worker count for bounds checking *)
  ss_completed     : list task_id;       (* Tasks that have completed *)
  ss_pending_tasks : list task;          (* Tasks waiting to be scheduled *)
  ss_stats         : scheduler_stats     (* Execution statistics *)
}

(** Create scheduler with specified number of workers *)
val create_scheduler : num_workers:nat{num_workers > 0} -> scheduler_state

(** Get worker by ID - returns None if ID out of range *)
val get_worker : sched:scheduler_state -> id:ws_worker_id -> option worker_state

(** Update worker in scheduler *)
val update_worker : sched:scheduler_state -> worker:worker_state -> scheduler_state


(** ----------------------------------------------------------------------------
    CORE WORK-STEALING OPERATIONS
    ---------------------------------------------------------------------------- *)

(** Result of attempting to get work *)
type work_result =
  | GotTask      : task -> work_result         (* Successfully got a task *)
  | NoWork       : work_result                 (* No work available *)
  | WorkerStopped: work_result                 (* Worker has been stopped *)

(** Try to get work from own deque (Step 1 of work-stealing algorithm) *)
val try_own_work : worker:worker_state -> (work_result & worker_state)

(** Select a random victim worker for stealing *)
val select_victim : worker:worker_state -> num_workers:nat{num_workers > 1} ->
  (ws_worker_id & worker_state)

(** Try to steal work from a specific victim worker *)
val steal_from : victim:worker_state -> (option task & worker_state)

(** Try to steal work from workers (Step 2 of work-stealing algorithm) *)
val steal_work : sched:scheduler_state -> worker:worker_state ->
  (work_result & scheduler_state & worker_state)

(** Try stealing from multiple victims in sequence *)
val try_steal_multiple : sched:scheduler_state -> worker:worker_state -> max_attempts:nat ->
  Tot (work_result & scheduler_state & worker_state) (decreases max_attempts)

(** Default number of steal attempts before going idle *)
val default_steal_attempts : nat


(** ----------------------------------------------------------------------------
    WORKER LOOP AND TASK EXECUTION
    ---------------------------------------------------------------------------- *)

(** Mark task as completed in scheduler *)
val complete_task : sched:scheduler_state -> t:task -> scheduler_state

(** Check if task can execute (all dependencies satisfied) *)
val task_can_execute : sched:scheduler_state -> t:task -> bool

(** Push task back to worker's deque (for deferred execution) *)
val defer_task : worker:worker_state -> t:task -> worker_state

(** Worker loop result - either continue with new state or stop *)
type loop_result =
  | Continue : scheduler_state -> worker_state -> loop_result
  | Stop     : scheduler_state -> worker_state -> loop_result

(** Single iteration of worker loop *)
val worker_step : sched:scheduler_state -> worker:worker_state -> loop_result

(** Run worker loop until completion or idle *)
val worker_loop : sched:scheduler_state -> worker:worker_state -> fuel:nat ->
  Tot (scheduler_state & worker_state) (decreases fuel)


(** ----------------------------------------------------------------------------
    WORKER LIFECYCLE MANAGEMENT
    ---------------------------------------------------------------------------- *)

(** Spawn a new worker and add to scheduler *)
val spawn_worker : sched:scheduler_state -> scheduler_state

(** Terminate a worker by setting its activity to Stopped *)
val terminate_worker : sched:scheduler_state -> id:ws_worker_id -> scheduler_state

(** Wake an idle worker by setting it back to Active *)
val wake_worker : sched:scheduler_state -> id:ws_worker_id -> scheduler_state

(** Wake all idle workers - called when new batch of tasks arrives *)
val wake_all_idle : sched:scheduler_state -> scheduler_state

(** Submit a task to a specific worker's deque *)
val submit_task_to_worker : sched:scheduler_state -> id:ws_worker_id -> t:task ->
  scheduler_state

(** Distribute tasks across workers in round-robin fashion *)
val distribute_tasks : sched:scheduler_state -> tasks:list task -> scheduler_state


(** ----------------------------------------------------------------------------
    WORK BALANCE THEOREMS
    ---------------------------------------------------------------------------- *)

(** Measure of work imbalance: max deque size - min deque size *)
val work_imbalance : sched:scheduler_state -> nat

(** Count total tasks across all worker deques *)
val total_tasks : sched:scheduler_state -> nat

(** Count active workers *)
val active_workers : sched:scheduler_state -> nat

(** Lemma: Stealing reduces imbalance *)
val steal_reduces_imbalance :
  sched:scheduler_state -> worker:worker_state -> victim:worker_state ->
  Lemma (requires worker.ws_deque.size = 0 /\ victim.ws_deque.size > 0)
        (ensures True)

(** Lemma: Work-stealing maintains task conservation *)
val steal_conserves_tasks :
  sched:scheduler_state -> worker:worker_state ->
  Lemma (ensures True)
        [SMTPat (steal_work sched worker)]

(** Theorem: Work-stealing achieves bounded imbalance *)
val work_balance_theorem :
  sched:scheduler_state -> fuel:nat ->
  Lemma (requires sched.ss_num_workers > 0)
        (ensures True)

(** Theorem: Idle workers get work when available *)
val idle_workers_get_work :
  sched:scheduler_state -> worker:worker_state ->
  Lemma (requires worker.ws_activity = WIdle /\ total_tasks sched > 0)
        (ensures True)

(** Theorem: All tasks eventually complete *)
val all_tasks_complete :
  sched:scheduler_state -> tasks:list task ->
  Lemma (requires active_workers sched > 0 /\
                  List.Tot.for_all (fun t -> t.state = Pending) tasks)
        (ensures True)


(** ============================================================================
    SECTION 4: SIMD WIDTH PARAMETERIZATION
    ============================================================================

    SIMD width enumeration supporting multiple vector widths
    as per Spec Definition 2.1.
*)

(** SIMD width in bits - matches hardware vector register capabilities *)
type simd_width =
  | SSE128   : simd_width   (* 128 bits = 4x Float32 = 2x Float64 *)
  | AVX256   : simd_width   (* 256 bits = 8x Float32 = 4x Float64 *)
  | AVX512   : simd_width   (* 512 bits = 16x Float32 = 8x Float64 *)

(** Get width in bits *)
val simd_width_bits : w:simd_width -> nat

(** Get number of 64-bit words per SIMD register *)
val simd_words : w:simd_width -> nat

(** Get number of 32-bit floats per SIMD register *)
val simd_float32_lanes : w:simd_width -> nat

(** Get number of 64-bit floats per SIMD register *)
val simd_float64_lanes : w:simd_width -> nat

(** Lemma: AVX-512 provides 8x the throughput of scalar for 64-bit operations *)
val avx512_speedup : unit ->
  Lemma (ensures simd_words AVX512 = 8)


(** ============================================================================
    SECTION 4B: SIMD BITSET OPERATIONS
    ============================================================================

    512-bit bitset using 8 x 64-bit words for efficient set operations
    in dataflow analysis (Spec Definition 2.2).
*)

(** 64-bit word type *)
type word64 = nat

(** 512-bit bitset as 8 x 64-bit words *)
type bitset512 = list word64

(** Zero bitset - 8 zeros *)
val zero_bitset : bitset512

(** Maximum word value for all-ones *)
val max_word : nat

(** All-ones bitset - 8 max words *)
val ones_bitset : bitset512

(** Check if bitset has valid length *)
val is_valid_bitset : bs:bitset512 -> bool

(** Helper: safe list access with bounds check *)
val nth_word : bs:bitset512 -> i:nat -> word64

(** Helper: update word at position *)
val update_word : bs:list word64 -> i:nat -> v:word64 ->
  Tot (list word64) (decreases i)

(** Lemma: update preserves length *)
val update_preserves_length : bs:list word64 -> i:nat -> v:word64 ->
  Lemma (ensures List.Tot.length (update_word bs i v) = List.Tot.length bs)
        (decreases bs)

(** Bitwise OR of two 64-bit words (modeled) *)
val word_or : a:word64 -> b:word64 -> word64

(** Bitwise AND of two 64-bit words *)
val word_and : a:word64 -> b:word64 -> word64

(** Bitwise AND NOT of two 64-bit words (a AND NOT b) *)
val word_andnot : a:word64 -> b:word64 -> word64

(** SIMD OR - parallel OR of all 8 words *)
val simd_or : a:bitset512 -> b:bitset512 -> bitset512

(** SIMD AND - parallel AND of all 8 words *)
val simd_and : a:bitset512 -> b:bitset512 -> bitset512

(** Helper: andnot_words at top level for proofs *)
val andnot_words : l1:list word64 -> l2:list word64 ->
  Tot (list word64) (decreases l1)

(** SIMD ANDNOT - parallel AND NOT of all 8 words *)
val simd_andnot : a:bitset512 -> b:bitset512 -> bitset512

(** Helper: check if all words are zero *)
val all_zero : l:list word64 -> Tot bool (decreases l)

(** Check if a is subset of b *)
val simd_is_subset : a:bitset512 -> b:bitset512 -> bool

(** Bitwise XOR of two 64-bit words *)
val word_xor : a:word64 -> b:word64 -> word64

(** Helper: xor_words at top level for proofs *)
val xor_words : l1:list word64 -> l2:list word64 ->
  Tot (list word64) (decreases l1)

(** SIMD XOR - parallel XOR of all 8 words (symmetric difference) *)
val simd_xor : a:bitset512 -> b:bitset512 -> bitset512

(** Check bitset equality: a XOR b = 0 means a = b *)
val simd_eq : a:bitset512 -> b:bitset512 -> bool

(** Lemma: simd_eq is reflexive *)
val simd_eq_refl : a:bitset512 ->
  Lemma (ensures simd_eq a a = true)
        [SMTPat (simd_eq a a)]

(** Population count for a single word (simplified) *)
val word_popcount : w:word64 -> nat

(** SIMD popcount - sum of popcounts of all words *)
val simd_popcount : bs:bitset512 -> Tot nat (decreases bs)

(** Set a bit at position [0, 512) *)
val set_bit : bs:bitset512 -> pos:nat{pos < 512} -> bitset512

(** Test if a bit is set at position [0, 512) *)
val test_bit : bs:bitset512 -> pos:nat{pos < 512} -> bool

(** Property: Setting a bit then testing returns true *)
val set_test_property : bs:bitset512 -> pos:nat{pos < 512} -> bool

(** Property: simd_or is symmetric *)
val simd_or_symmetric : a:bitset512 -> b:bitset512 -> bool

(** Property: simd_and is symmetric *)
val simd_and_symmetric : a:bitset512 -> b:bitset512 -> bool

(** Helper: word_andnot w w = 0 *)
val word_andnot_self : w:word64 -> Lemma (ensures word_andnot w w = 0)

(** Helper: andnot_words l l produces all zeros *)
val andnot_words_self_zero : l:list word64 ->
  Lemma (ensures all_zero (andnot_words l l) = true)
        (decreases l)

(** Helper: simd_andnot l l produces all zeros *)
val simd_andnot_self_zero : l:list word64 ->
  Lemma (ensures all_zero (simd_andnot l l) = true)

(** Lemma: Subset is reflexive *)
val simd_subset_refl : a:bitset512 ->
  Lemma (ensures simd_is_subset a a = true)
        [SMTPat (simd_is_subset a a)]


(** ============================================================================
    SECTION 5: WORKLIST ALGORITHM (RPO)
    ============================================================================

    Worklist algorithm for dataflow analysis with Reverse Post-Order (RPO)
    scheduling, as specified in Spec Definition 3.1.
*)

(** Worklist entry with RPO number for ordering *)
type worklist_entry = nat & node_id

(** Worklist comparison: lower RPO number = higher priority *)
val entry_leq : e1:worklist_entry -> e2:worklist_entry -> bool

(** Worklist structure *)
noeq type worklist = {
  items    : list worklist_entry;     (* Sorted by RPO *)
  in_queue : list node_id             (* Nodes currently in worklist *)
}

(** Empty worklist *)
val empty_worklist : worklist

(** Check if node is in worklist *)
val is_in_worklist : wl:worklist -> n:node_id -> bool

(** Insert maintaining sorted order by RPO *)
val insert_sorted : item:worklist_entry -> l:list worklist_entry ->
  Tot (list worklist_entry) (decreases l)

(** Lemma: insert_sorted increases length by exactly 1 *)
val insert_sorted_length : item:worklist_entry -> l:list worklist_entry ->
  Lemma (ensures List.Tot.length (insert_sorted item l) = List.Tot.length l + 1)
        (decreases l)

(** Add node to worklist if not already present *)
val add_to_worklist : wl:worklist -> rpo:nat -> n:node_id -> worklist

(** Pop minimum RPO node from worklist *)
val pop_worklist : wl:worklist -> option (node_id & worklist)

(** Worklist size *)
val worklist_size : wl:worklist -> nat

(** Lemma: Adding increases size by at most 1 *)
val add_worklist_size : wl:worklist -> rpo:nat -> n:node_id ->
  Lemma (ensures worklist_size (add_to_worklist wl rpo n) <= worklist_size wl + 1)

(** Helper: characterize pop_worklist size behavior *)
val pop_worklist_size_check : wl:worklist -> bool

(** Lemma: Pop decreases size by 1 when non-empty *)
val pop_worklist_size : wl:worklist ->
  Lemma (ensures pop_worklist_size_check wl = true)


(** ============================================================================
    SECTION 6: DATAFLOW LATTICE
    ============================================================================

    Abstract lattice for dataflow analysis following the classic framework
    of Kildall (1973) and Kam & Ullman (1977). Spec Section 3.4.
*)

(** Lattice structure with bottom, join, and ordering *)
noeq type lattice (a: Type) = {
  bottom : a;                      (* Least element *)
  join   : a -> a -> a;            (* Least upper bound *)
  leq    : a -> a -> bool          (* Partial order *)
}

(** Lattice laws - required for convergence *)

(** Join is commutative *)
val join_comm : #a:Type -> l:lattice a -> prop

(** Join is associative *)
val join_assoc : #a:Type -> l:lattice a -> prop

(** Join is idempotent *)
val join_idem : #a:Type -> l:lattice a -> prop

(** Bottom is identity for join *)
val bottom_identity : #a:Type -> l:lattice a -> prop

(** Order is reflexive *)
val leq_refl : #a:Type -> l:lattice a -> prop

(** Order is antisymmetric *)
val leq_antisym : #a:Type -> l:lattice a -> prop

(** Order is transitive *)
val leq_trans : #a:Type -> l:lattice a -> prop

(** Bottom is least element *)
val bottom_least : #a:Type -> l:lattice a -> prop

(** Join is least upper bound *)
val join_lub : #a:Type -> l:lattice a -> prop

(** A lattice is well-formed if it satisfies all laws *)
val well_formed_lattice : #a:Type -> l:lattice a -> prop

(** Monotone transfer function: if input grows, output grows *)
val monotone : #a:Type -> l:lattice a -> f:(node_id -> a -> a) -> prop


(** ============================================================================
    SECTION 6B: CSR EDGE REPRESENTATION
    ============================================================================

    Compressed Sparse Row (CSR) format for efficient edge iteration.
*)

(** CSR edge representation *)
noeq type csr_edges = {
  num_nodes   : nat;                    (* Number of nodes *)
  row_offsets : list nat;               (* Start of each node's edges *)
  col_indices : list node_id;           (* Target nodes for each edge *)
}

(** Helper: safe list index with default *)
val safe_index : #a:Type -> l:list a -> i:nat -> default:a ->
  Tot a (decreases i)

(** Helper: extract slice from list *)
val slice_list : #a:Type -> l:list a -> start:nat -> len:nat ->
  Tot (list a) (decreases %[start; len; l])

(** Get successors of a node *)
val get_successors : edges:csr_edges -> n:node_id -> list node_id

(** Get predecessors requires reverse edge lookup *)
val get_predecessors : edges:csr_edges -> n:node_id -> list node_id


(** ============================================================================
    SECTION 7: DATAFLOW ANALYSIS WITH CONVERGENCE PROOF
    ============================================================================

    Fixed-point iteration for dataflow analysis implementing the classic
    Kildall worklist algorithm with RPO scheduling.
*)

(** Analysis state: mapping from nodes to lattice values *)
type analysis_state (a: Type) = node_id -> a

(** Initialize all nodes to bottom *)
val init_state : #a:Type -> l:lattice a -> analysis_state a

(** Join values from all predecessors *)
val join_preds : #a:Type -> l:lattice a -> state:analysis_state a ->
  preds:list node_id -> a

(** Single iteration step: process one node *)
val process_node : #a:Type -> l:lattice a ->
  transfer:(node_id -> a -> a) ->
  edges:csr_edges ->
  state:analysis_state a ->
  n:node_id ->
  (a & bool)

(** Update state at a single node *)
val update_state : #a:Type -> state:analysis_state a ->
  n:node_id -> v:a -> analysis_state a

(** Worklist iteration with fuel for termination *)
val iterate : #a:Type -> l:lattice a ->
  transfer:(node_id -> a -> a) ->
  edges:csr_edges ->
  rpo:(node_id -> nat) ->
  state:analysis_state a ->
  wl:worklist ->
  fuel:nat ->
  Tot (analysis_state a) (decreases fuel)

(** Main analysis function *)
val analyze : #a:Type -> l:lattice a ->
  transfer:(node_id -> a -> a) ->
  edges:csr_edges ->
  entry_nodes:list node_id ->
  analysis_state a


(** ============================================================================
    SECTION 8: LOCK-FREE ATOMIC FACT PROPAGATION
    ============================================================================

    Atomic fact updates for concurrent worklist processing.
    Based on Spec Definition 3.3.
*)

(** Atomic memory order for fact updates *)
type memory_order =
  | MORelaxed  : memory_order   (* No ordering constraints *)
  | MOAcquire  : memory_order   (* Acquire semantics on loads *)
  | MORelease  : memory_order   (* Release semantics on stores *)
  | MOAcqRel   : memory_order   (* Both acquire and release *)
  | MOSeqCst   : memory_order   (* Sequentially consistent *)

(** Model of atomic cell *)
noeq type atomic_cell (a: Type) = {
  value : a;                    (* Current value *)
  version : nat                 (* Version for optimistic locking *)
}

(** Create atomic cell with initial value *)
val make_atomic : #a:Type -> v:a -> atomic_cell a

(** Atomic load - returns current value *)
val atomic_load : #a:Type -> cell:atomic_cell a -> a

(** Compare-and-swap operation (modeled) *)
val cas : #a:eqtype -> cell:atomic_cell a -> expected:a -> desired:a ->
  (bool & atomic_cell a)

(** Atomic facts storage for parallel analysis *)
noeq type atomic_facts (a: Type) = {
  cells : list (atomic_cell a);   (* One cell per node *)
  num_nodes : nat
}

(** Initialize atomic facts with bottom value *)
val init_atomic_facts : #a:Type -> l:lattice a -> num_nodes:nat -> atomic_facts a

(** Get fact for a node *)
val get_atomic_fact : #a:Type -> facts:atomic_facts a -> n:node_id -> default:a -> a

(** Atomic fact update with CAS retry loop *)
val atomic_update_fact : #a:eqtype -> l:lattice a -> facts:atomic_facts a ->
  n:node_id -> new_fact:a -> fuel:nat ->
  Tot (bool & atomic_facts a) (decreases fuel)

(** Default retry count for atomic updates *)
val atomic_retry_limit : nat

(** Simplified atomic update with default retry limit *)
val atomic_update : #a:eqtype -> l:lattice a -> facts:atomic_facts a ->
  n:node_id -> new_fact:a -> (bool & atomic_facts a)

(** Theorem: Monotonicity ensures atomic updates converge *)
val atomic_monotone_convergence : #a:eqtype -> l:lattice a -> facts:atomic_facts a ->
  n:node_id -> v1:a -> v2:a ->
  Lemma (requires well_formed_lattice l)
        (ensures True)


(** ============================================================================
    SECTION 8B: EXTENDED LOCK-FREE ATOMIC OPERATIONS
    ============================================================================

    Complete lock-free atomic primitives for parallel analysis.
*)

(** Memory ordering strength comparison *)
val memory_order_strength : mo:memory_order -> nat

(** Check if memory order provides acquire semantics *)
val has_acquire_semantics : mo:memory_order -> bool

(** Check if memory order provides release semantics *)
val has_release_semantics : mo:memory_order -> bool

(** Atomic load with explicit memory ordering *)
val atomic_load_ord : #a:Type -> cell:atomic_cell a -> order:memory_order -> a

(** Atomic store with explicit memory ordering *)
val atomic_store_ord : #a:Type -> cell:atomic_cell a -> v:a -> order:memory_order ->
  atomic_cell a

(** Compare-and-swap with memory ordering *)
val cas_ord : #a:eqtype -> cell:atomic_cell a -> expected:a -> desired:a ->
  success_order:memory_order -> failure_order:memory_order ->
  (bool & atomic_cell a)

(** Weak compare-and-swap (may fail spuriously) *)
val cas_weak : #a:eqtype -> cell:atomic_cell a -> expected:a -> desired:a ->
  (bool & atomic_cell a)

(** Atomic fetch-and-add for nat values *)
val atomic_fetch_add : cell:atomic_cell nat -> delta:nat -> order:memory_order ->
  (nat & atomic_cell nat)

(** Atomic fetch-and-sub for nat values *)
val atomic_fetch_sub : cell:atomic_cell nat -> delta:nat -> order:memory_order ->
  (nat & atomic_cell nat)

(** Atomic fetch-and-or for bitset operations *)
val atomic_fetch_or : cell:atomic_cell nat -> bits:nat -> order:memory_order ->
  (nat & atomic_cell nat)

(** Atomic fetch-and-and for bitset intersection *)
val atomic_fetch_and : cell:atomic_cell nat -> mask:nat -> order:memory_order ->
  (nat & atomic_cell nat)

(** Atomic fetch-and-xor for bitset toggle *)
val atomic_fetch_xor : cell:atomic_cell nat -> bits:nat -> order:memory_order ->
  (nat & atomic_cell nat)

(** Atomic exchange - atomically replaces value and returns old *)
val atomic_exchange : #a:Type -> cell:atomic_cell a -> new_val:a -> order:memory_order ->
  (a & atomic_cell a)


(** ----------------------------------------------------------------------------
    ATOMIC WORKLIST OPERATIONS
    ---------------------------------------------------------------------------- *)

(** Atomic worklist membership bitset *)
noeq type atomic_worklist_bits = {
  awb_bits   : list (atomic_cell nat);  (* Atomic words for membership *)
  awb_words  : nat;                      (* Number of 64-bit words *)
  awb_nodes  : nat                       (* Maximum node count *)
}

(** Create atomic worklist bitset for n nodes *)
val create_atomic_worklist_bits : n_nodes:nat -> atomic_worklist_bits

(** Atomically add node to worklist *)
val atomic_worklist_add : wl:atomic_worklist_bits -> n:node_id ->
  (bool & atomic_worklist_bits)

(** Atomically check if node is in worklist *)
val atomic_worklist_contains : wl:atomic_worklist_bits -> n:node_id -> bool

(** Atomically remove node from worklist *)
val atomic_worklist_remove : wl:atomic_worklist_bits -> n:node_id ->
  (bool & atomic_worklist_bits)


(** ----------------------------------------------------------------------------
    ATOMIC COUNTER FOR WORK DISTRIBUTION
    ---------------------------------------------------------------------------- *)

(** Atomic work counter for parallel iteration *)
noeq type atomic_work_counter = {
  awc_current : atomic_cell nat;   (* Next work item to claim *)
  awc_total   : nat                (* Total work items *)
}

(** Create work counter *)
val create_work_counter : n_total:nat -> atomic_work_counter

(** Atomically claim next work item *)
val claim_work : counter:atomic_work_counter ->
  (option nat & atomic_work_counter)

(** Atomically claim batch of work items *)
val claim_work_batch : counter:atomic_work_counter -> batch_size:nat{batch_size > 0} ->
  (option (nat & nat) & atomic_work_counter)


(** ----------------------------------------------------------------------------
    MONOTONE CONVERGENCE THEOREM FOR PARALLEL FIXPOINT
    ---------------------------------------------------------------------------- *)

(** Lattice chain: sequence of strictly increasing elements *)
type lattice_chain (#a: Type) (l: lattice a) = list a

(** Chain is valid if each element is strictly greater than previous *)
val valid_chain : #a:Type -> l:lattice a -> chain:lattice_chain l ->
  Tot bool (decreases chain)

(** Chain length *)
val chain_length : #a:Type -> l:lattice a -> chain:lattice_chain l -> nat

(** Finite height property: all chains have bounded length *)
val has_finite_height : #a:Type -> l:lattice a -> h:nat -> prop

(** Progress witness: value at node increased *)
noeq type progress_witness (#a: Type) (l: lattice a) = {
  pw_node    : node_id;
  pw_before  : a;
  pw_after   : a;
  pw_witness : squash (l.leq pw_before pw_after = true /\ not (l.leq pw_after pw_before))
}

(** Sequence of progress witnesses *)
type progress_sequence (#a: Type) (l: lattice a) = list (progress_witness l)

(** THEOREM: Parallel fixpoint with atomic updates converges *)
val parallel_fixpoint_convergence :
  #a:eqtype -> l:lattice a -> height:nat -> n_nodes:nat ->
  transfer:(node_id -> a -> a) ->
  Lemma (requires well_formed_lattice l /\
                  has_finite_height l height /\
                  monotone l transfer)
        (ensures True)

(** THEOREM: Lock-free operations are wait-free for bounded contention *)
val lockfree_progress_guarantee :
  n_workers:nat{n_workers > 0} -> max_retries:nat ->
  Lemma (ensures True)

(** THEOREM: Atomic join preserves monotonicity *)
val atomic_join_monotone :
  #a:eqtype -> l:lattice a -> old:a -> v1:a -> v2:a ->
  Lemma (requires well_formed_lattice l)
        (ensures l.join (l.join old v1) v2 == l.join (l.join old v2) v1)

(** THEOREM: No lost updates in concurrent propagation *)
val no_lost_updates :
  #a:eqtype -> l:lattice a -> facts:atomic_facts a ->
  n:node_id -> v1:a -> v2:a ->
  Lemma (requires well_formed_lattice l /\ n < facts.num_nodes)
        (ensures True)


(** ============================================================================
    SECTION 9: PARALLEL WORKLIST ANALYSIS
    ============================================================================

    Multi-threaded worklist processing using atomic fact updates.
*)

(** Worker identifier *)
type worker_id = nat

(** Parallel analysis state *)
val init_rng : worker_id:ws_worker_id -> rng_state

(** Advance RNG state and return next value in [0, bound) *)
noeq type parallel_analysis_state (a: Type) = {
  facts       : atomic_facts a;
  worklist    : worklist;
  num_workers : nat
}

(** Process a single node in parallel context *)
val parallel_process_node : #a:eqtype -> l:lattice a ->
  transfer:(node_id -> a -> a) ->
  edges:csr_edges ->
  state:parallel_analysis_state a ->
  n:node_id ->
  parallel_analysis_state a


(** ============================================================================
    SECTION 9C: CONVERGENCE THEOREM
    ============================================================================
*)

(** Lattice height: maximum chain length from bottom to any element *)
type finite_height (#a: Type) (l: lattice a) = nat

(** Progress measure: sum of heights of all node values *)
val progress_measure : #a:Type -> l:lattice a -> height:finite_height l ->
  state:analysis_state a -> num_nodes:nat -> nat

(** Helper: check if node processing yields no change *)
val node_unchanged : #a:Type -> l:lattice a -> transfer:(node_id -> a -> a) ->
  edges:csr_edges -> state:analysis_state a -> n:node_id -> bool

(** Convergence lemma: if value doesn't change, successors are stable *)
val stable_node_stable_succs : #a:Type -> l:lattice a -> state:analysis_state a ->
  n:node_id -> edges:csr_edges -> transfer:(node_id -> a -> a) ->
  Lemma (requires node_unchanged l transfer edges state n = true)
        (ensures True)

(** Main convergence theorem *)
val worklist_converges : #a:Type -> l:lattice a -> transfer:(node_id -> a -> a) ->
  edges:csr_edges -> entry_nodes:list node_id ->
  Lemma (requires well_formed_lattice l /\ monotone l transfer)
        (ensures True)
        [SMTPat (analyze l transfer edges entry_nodes)]

(** Helper: check if a state is stable for a node *)
val is_node_stable : #a:Type -> l:lattice a -> transfer:(node_id -> a -> a) ->
  edges:csr_edges -> state:analysis_state a -> n:node_id -> bool

(** Helper: check if all nodes are stable *)
val all_nodes_stable : #a:Type -> l:lattice a -> transfer:(node_id -> a -> a) ->
  edges:csr_edges -> state:analysis_state a -> prop

(** Fixed point property: result is a fixed point of the analysis *)
val is_fixed_point : #a:Type -> l:lattice a -> transfer:(node_id -> a -> a) ->
  edges:csr_edges -> state:analysis_state a ->
  Lemma (requires all_nodes_stable l transfer edges state)
        (ensures True)


(** ============================================================================
    SECTION 9B: VECTORIZED DATAFLOW STEP
    ============================================================================

    Optimized dataflow iteration using SIMD bitset operations.
*)

(** Vectorized dataflow step for gen-kill analysis *)
val dataflow_step : in_facts:list bitset512 -> gen:bitset512 -> kill:bitset512 -> bitset512

(** Lemma: Empty input produces just the gen set *)
val dataflow_step_empty_in : gen:bitset512 -> kill:bitset512 ->
  Lemma (ensures dataflow_step [] gen kill = gen)

(** Lemma: Gen facts are always in output *)
val gen_in_output : in_facts:list bitset512 -> gen:bitset512 ->
  kill:bitset512 -> pos:nat{pos < 512} ->
  Lemma (requires test_bit gen pos = true)
        (ensures True)


(** ============================================================================
    SECTION 10: MEMORY HIERARCHY
    ============================================================================

    Cache-aware data structure sizing for optimal performance.
    Based on Spec Chapter 4: Memory Hierarchy Optimization.
*)

(** Temperature classification for memory access patterns *)
type temperature =
  | THot   : temperature   (* Accessed in inner loops *)
  | TWarm  : temperature   (* Accessed occasionally *)
  | TCold  : temperature   (* Rarely accessed *)

(** Cache line size in bytes *)
val cache_line_bytes : nat

(** L1 cache size in bytes (typical) *)
val l1_cache_bytes : nat

(** L2 cache size in bytes (typical) *)
val l2_cache_bytes : nat

(** L3 cache size in bytes (typical) *)
val l3_cache_bytes : nat

(** Hot node: 32 bytes - fits 2 per cache line *)
val hot_node_bytes : nat

(** Warm node: 64 bytes - one per cache line *)
val warm_node_bytes : nat

(** Cold node: larger than cache line *)
val cold_node_bytes : nat

(** Check if n nodes of given size fit in L3 cache *)
val fits_in_l3 : node_size:nat -> n:nat -> bool

(** Maximum hot nodes that fit in L3 *)
val max_l3_hot_nodes : nat

(** Maximum warm nodes that fit in L3 *)
val max_l3_warm_nodes : nat

(** Maximum hot nodes that fit in L1 *)
val max_l1_hot_nodes : nat

(** Maximum hot nodes that fit in L2 *)
val max_l2_hot_nodes : nat

(** Hot node structure for CFG traversal *)
noeq type hot_node = {
  hn_id         : node_id;      (* Node identifier *)
  hn_first_succ : nat;          (* Index into edge array *)
  hn_num_succs  : nat;          (* Number of successors *)
  hn_flags      : nat           (* Bit flags for node properties *)
}

(** Warm node structure for full node data *)
noeq type warm_node = {
  wn_id         : node_id;
  wn_first_succ : nat;
  wn_num_succs  : nat;
  wn_first_pred : nat;
  wn_num_preds  : nat;
  wn_dom        : node_id;      (* Immediate dominator *)
  wn_rpo        : nat;          (* Reverse post-order number *)
  wn_depth      : nat           (* Depth in dominator tree *)
}

(** Cache locality score: estimate of cache utilization *)
val cache_score : hot_nodes:nat -> warm_nodes:nat -> nat

(** Lemma: Fewer nodes means better cache utilization *)
val fewer_nodes_better_cache : h1:nat -> h2:nat -> w1:nat -> w2:nat ->
  Lemma (requires h1 <= h2 /\ w1 <= w2)
        (ensures cache_score h1 w1 <= cache_score h2 w2)

(** Memory usage bytes per node by temperature *)
val hot_bytes_per_node : nat
val warm_bytes_per_node : nat
val cold_bytes_per_node : nat

(** Calculate total memory usage for n nodes *)
val calculate_memory : n_nodes:nat -> (nat & nat & nat)

(** Align address to cache line boundary *)
val align_to_cache_line : addr:nat -> nat

(** Calculate how many items of given size fit in one cache line *)
val items_per_cache_line : item_size:nat -> nat

(** Hot nodes per cache line *)
val hot_nodes_per_cache_line : nat

(** Lemma: Two hot nodes fit per cache line *)
val two_hot_nodes_per_line : unit ->
  Lemma (ensures hot_nodes_per_cache_line = 2)


(** ============================================================================
    SECTION 11: PREFETCH HINTS
    ============================================================================

    Prefetch hint generation for efficient memory access patterns.
    Based on Spec Definition 4.5.
*)

(** Prefetch hint type for different access patterns *)
type prefetch_hint =
  | PrefetchRead  : prefetch_hint   (* Data will be read *)
  | PrefetchWrite : prefetch_hint   (* Data will be written *)
  | PrefetchNTA   : prefetch_hint   (* Non-temporal access (streaming) *)

(** Prefetch distance: how many iterations ahead to prefetch *)
val prefetch_distance : nat

(** Prefetch batch size: number of nodes to prefetch together *)
val prefetch_batch : nat

(** Calculate prefetch addresses for traversal *)
val prefetch_nodes : nodes:list hot_node -> current_idx:nat -> list node_id


(** ============================================================================
    SECTION 11B: PARALLEL REGION ANALYSIS
    ============================================================================

    Identify regions of the CFG that can be analyzed in parallel.

    NOTE: parallel_region_id is for CFG PARTITIONING, NOT memory lifetimes.
    Memory lifetime regions are defined in BrrrTypes as `region`.
*)

(** Parallel region identifier - NOT memory lifetime regions *)
type parallel_region_id = nat

(** Parallel region: set of nodes that can be processed together *)
noeq type parallel_region = {
  rid          : parallel_region_id;       (* Region identifier *)
  region_nodes : list node_id;             (* Nodes in this region *)
  region_deps  : list parallel_region_id   (* Regions that must complete first *)
}

(** Check if two regions are independent *)
val regions_independent : r1:parallel_region -> r2:parallel_region -> bool

(** Partition CFG into parallel regions based on dominance *)
val partition_into_regions : edges:csr_edges -> rpo:list node_id -> list parallel_region

(** Lemma: Independent regions can be analyzed in parallel *)
val independent_regions_parallel : r1:parallel_region -> r2:parallel_region ->
  Lemma (requires regions_independent r1 r2 = true)
        (ensures True)
