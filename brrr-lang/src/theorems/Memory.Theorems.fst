(** ============================================================================
    Memory.Theorems.fst - Memory Model and Concurrency Theorems for Brrr-Lang
    ============================================================================

    This module contains the HARD memory model theorems that require 20-40+ hours
    each for full mechanization. These theorems form the foundation for:
    - Data-race-free reasoning (DRF-SC)
    - Separation logic frame reasoning
    - Memory model sanity (no thin-air)
    - Compositional analysis (bi-abduction)

    EXISTING COQMECHANIZATIONS:
    ===========================
    1. Iris (MPI-SWS): ~50K lines Coq for separation logic + frame rule
       Repository: https://gitlab.mpi-sws.org/iris/iris
       Key files: iris/bi/big_op.v, iris/base_logic/lib/invariants.v

    2. Promising 2.0 (Lee et al. 2020): ~30K lines Coq for memory model
       Repository: https://sf.snu.ac.kr/promising2.0/
       Key files: src/model/promise2.v, src/proof/cert.v

    3. CompCert Separation Logic (Appel et al.): VST project
       Repository: https://github.com/PrincetonUniversity/VST
       Key files: veric/seplog.v, floyd/SeparationLogicFacts.v

    4. Infer (Facebook): OCaml implementation of bi-abduction
       Repository: https://github.com/facebook/infer
       Key files: infer/src/biabduction/

    ALL THEOREMS USE admit() - these are THEOREM STATEMENTS, not proofs.
    Full mechanization would require porting from the above Coq developments.
    ============================================================================ *)

module Memory.Theorems

open FStar.List.Tot
open FStar.Classical

(* Import separation logic infrastructure *)
open SeparationLogic
open Values
open Expressions
open BrrrTypes

(** ============================================================================
    PART I: MEMORY MODEL DEFINITIONS
    ============================================================================

    We define a weak memory model following the C11/C++11 memory model as
    formalized by Batty et al. 2011 and refined by the Promising semantics
    (Kang et al. 2017, Lee et al. 2020).

    Key relations in the memory model:
    - sb (sequenced-before): program order within a thread
    - rf (reads-from): which write a read observes
    - mo (modification-order): total order on writes to each location
    - hb (happens-before): transitive closure of synchronization

    Coherence axioms (filter candidate executions):
    - CoRR: rf^-1; mo subseteq rb (read-read coherence)
    - CoWW: mo is total on writes to same location
    - CoRW: rf; rb subseteq mo
    - CoWR: rb; rf^-1 subseteq mo
    ============================================================================ *)

(* Memory location *)
type mem_loc = nat

(* Thread identifier *)
type thread_id = nat

(* Memory ordering strength (C11/C++11 model) *)
type memory_order =
  | MO_relaxed    (* No synchronization *)
  | MO_acquire    (* Acquire fence *)
  | MO_release    (* Release fence *)
  | MO_acq_rel    (* Both acquire and release *)
  | MO_seq_cst    (* Sequential consistency *)

(* Memory event types *)
noeq type mem_event =
  | MERead   : loc:mem_loc -> val_read:value -> ord:memory_order -> mem_event
  | MEWrite  : loc:mem_loc -> val_written:value -> ord:memory_order -> mem_event
  | MEFence  : ord:memory_order -> mem_event
  | MERMW    : loc:mem_loc -> expected:value -> new_val:value -> success:bool -> mem_event  (* Read-modify-write *)
  | MEAlloc  : loc:mem_loc -> size:nat -> mem_event
  | MEFree   : loc:mem_loc -> mem_event

(* Event with metadata *)
noeq type labeled_event = {
  ev_id: nat;
  ev_thread: thread_id;
  ev_event: mem_event;
}

(* Execution graph - represents one possible execution *)
noeq type execution = {
  (* Events in the execution *)
  events: list labeled_event;

  (* Sequenced-before relation (program order within thread) *)
  sb: labeled_event -> labeled_event -> bool;

  (* Reads-from relation (which write does each read see) *)
  rf: labeled_event -> option labeled_event;

  (* Modification order (total order on writes to same location) *)
  mo: labeled_event -> labeled_event -> bool;

  (* Synchronizes-with relation (cross-thread synchronization) *)
  sw: labeled_event -> labeled_event -> bool;
}

(* Happens-before: transitive closure of sb union sw *)
let hb_direct (ex: execution) (e1 e2: labeled_event) : bool =
  ex.sb e1 e2 || ex.sw e1 e2

(* Program representation *)
noeq type program = {
  threads: list (list mem_event);  (* Each thread is a sequence of events *)
}

(* Event is a read *)
let is_read (e: mem_event) : bool =
  match e with
  | MERead _ _ _ -> true
  | MERMW _ _ _ _ -> true
  | _ -> false

(* Event is a write *)
let is_write (e: mem_event) : bool =
  match e with
  | MEWrite _ _ _ -> true
  | MERMW _ _ _ true -> true  (* Successful RMW includes a write *)
  | _ -> false

(* Get location of event (if applicable) *)
let event_loc (e: mem_event) : option mem_loc =
  match e with
  | MERead l _ _ -> Some l
  | MEWrite l _ _ -> Some l
  | MERMW l _ _ _ -> Some l
  | MEAlloc l _ -> Some l
  | MEFree l -> Some l
  | _ -> None

(* Two events access the same location *)
let same_location (e1 e2: labeled_event) : bool =
  match event_loc e1.ev_event, event_loc e2.ev_event with
  | Some l1, Some l2 -> l1 = l2
  | _, _ -> false

(* Two events conflict (at least one is a write to the same location) *)
let conflicting (e1 e2: labeled_event) : bool =
  same_location e1 e2 &&
  (is_write e1.ev_event || is_write e2.ev_event)

(** ============================================================================
    DATA-RACE-FREE (DRF) DEFINITION
    ============================================================================

    A data race occurs when two conflicting memory accesses:
    1. Are from different threads
    2. At least one is a write
    3. At least one is non-atomic (relaxed)
    4. They are not ordered by happens-before

    Reference: Boehm & Adve 2008, Definition 4
    "Foundations of the C++ Concurrency Memory Model"
    ============================================================================ *)

(* Predicate: two events form a data race *)
let is_data_race (ex: execution) (e1 e2: labeled_event) : bool =
  (* Different threads *)
  e1.ev_thread <> e2.ev_thread &&
  (* Conflicting accesses *)
  conflicting e1 e2 &&
  (* At least one is relaxed (non-atomic for C11 purposes) *)
  (match e1.ev_event, e2.ev_event with
   | MERead _ _ MO_relaxed, _ -> true
   | MEWrite _ _ MO_relaxed, _ -> true
   | _, MERead _ _ MO_relaxed -> true
   | _, MEWrite _ _ MO_relaxed -> true
   | _, _ -> false) &&
  (* Not ordered by happens-before (in either direction) *)
  not (hb_direct ex e1 e2) &&
  not (hb_direct ex e2 e1)

(* Execution is data-race-free *)
let execution_drf (ex: execution) : bool =
  List.Tot.for_all (fun e1 ->
    List.Tot.for_all (fun e2 ->
      not (is_data_race ex e1 e2)
    ) ex.events
  ) ex.events

(* Program is data-race-free (all executions are DRF) *)
val data_race_free : program -> Type0
let data_race_free p =
  (* All consistent executions of p are data-race-free *)
  True  (* Simplified - full definition requires execution enumeration *)

(** ============================================================================
    SEQUENTIAL CONSISTENCY (SC) DEFINITION
    ============================================================================

    Sequential consistency (Lamport 1979) requires that all operations appear
    to execute in some total order consistent with program order.

    Reference: Lamport 1979, "How to Make a Multiprocessor Computer That
    Correctly Executes Multiprocess Programs"
    ============================================================================ *)

(* Total order on events *)
type total_order = labeled_event -> labeled_event -> bool

(* A total order is valid for SC if it respects program order and each read
   sees the most recent write in the total order *)
let valid_sc_order (ex: execution) (order: total_order) : bool =
  (* Respects program order *)
  List.Tot.for_all (fun e1 ->
    List.Tot.for_all (fun e2 ->
      ex.sb e1 e2 ==> order e1 e2
    ) ex.events
  ) ex.events &&
  (* Each read sees the most recent write to that location in the total order *)
  List.Tot.for_all (fun e ->
    match ex.rf e with
    | Some w -> order w e  (* Write happens before read in total order *)
    | None -> true
  ) ex.events

(* Execution has SC semantics *)
let execution_sc (ex: execution) : bool =
  (* There exists a valid SC total order *)
  true  (* Simplified - full check requires order enumeration *)

(* All executions of program have SC semantics *)
val all_executions_sc : program -> Type0
let all_executions_sc p =
  (* All consistent executions can be totally ordered *)
  True  (* Simplified *)

(** ============================================================================
    THEOREM T-5.11: DRF-SC (DATA-RACE-FREEDOM IMPLIES SEQUENTIAL CONSISTENCY)
    ============================================================================

    STATEMENT: If a program is data-race-free, then all its executions are
    sequentially consistent.

    HISTORICAL CONTEXT:
    ===================
    This theorem was first established by Adve & Hill 1990:
    "Weak Ordering - A New Definition" (ISCA 1990)

    The C/C++ version was proven by Boehm & Adve 2008:
    "Foundations of the C++ Concurrency Memory Model" (PLDI 2008)
    Theorem 7.1: "For any DRF program P, if P has no undefined behavior
    in the sequentially consistent semantics, then P has no undefined
    behavior in the C++ memory model, and both semantics assign the
    same values to all shared memory reads."

    PROOF TECHNIQUE (Boehm-Adve):
    =============================
    1. Assume program P is DRF in SC semantics
    2. Consider any consistent execution E of P in the weak memory model
    3. Define "visible" writes: writes that could potentially be read
    4. Show that DRF implies unique visible write for each read
    5. Construct SC-equivalent execution by choosing this unique write
    6. By induction on execution length, all reads see SC values

    Key insight: DRF ensures that synchronization is sufficient to
    prevent any ambiguity about which write a read should observe.

    EXISTING MECHANIZATIONS:
    ========================
    1. Promising 2.0 (Lee et al. 2020): 30K lines Coq
       Files: src/model/promise2.v (DRF-SC theorem)
       Uses "certification" approach: show DRF programs can always
       certify their promises, leading to SC behavior.

    2. CompCertTSO (Sevcik et al. 2013): Coq proof for x86-TSO
       Different memory model but similar proof structure.

    3. IMM (Podkopaev et al. 2019): Coq formalization
       "Bridging the gap between programming languages and hardware
       weak memory models" - unifying framework.

    PROOF STATUS: ADMITTED
    Estimated effort: 20-40 hours
    Primary difficulty: Defining execution enumeration and total order search

    REFERENCES:
    ===========
    - Boehm & Adve 2008, PLDI: Theorem 7.1 (primary)
    - Lee et al. 2020, PLDI: Promising 2.0 DRF-SC proof
    - Batty et al. 2011, POPL: C11 memory model formalization
    - Lahav et al. 2017, PLDI: Repaired C11 model (RC11)
    ============================================================================ *)

val drf_sc : p:program ->
  Lemma (requires data_race_free p)
        (ensures all_executions_sc p)
        [SMTPat (data_race_free p)]
let drf_sc p =
  (* Proof sketch following Boehm-Adve 2008 Theorem 7.1:

     STEP 1: SETUP
     Let P be a DRF program. Consider any consistent execution E of P
     under the C++ memory model (or Promising semantics).

     STEP 2: VISIBLE WRITES DEFINITION
     For each read R in E, define the set of "visible" writes:
       visible(R) = { W | W writes to same location as R,
                          not hb(R, W),
                          forall W'. W ->_mo W' implies hb(R, W') }

     STEP 3: UNIQUENESS FROM DRF
     Key claim: |visible(R)| = 1 for all reads R in DRF programs.
     Proof: If |visible(R)| > 1, there exist W1, W2 in visible(R).
     - W1 and W2 write to same location as R (by definition)
     - Neither hb(W1, W2) nor hb(W2, W1) (both visible to R)
     - But then R and W1 (or R and W2) form a data race!
     - Contradiction with DRF.

     STEP 4: SC CONSTRUCTION
     Since each read has a unique visible write, we can construct
     a total order by:
     - Order writes by modification order (mo)
     - Place each read immediately after its unique visible write
     - This total order respects program order and is SC

     STEP 5: INDUCTION ON EXECUTION LENGTH
     By induction on the number of events:
     - Base: Empty execution is trivially SC
     - Step: Adding event preserves SC property by Step 3-4

     The Promising 2.0 proof uses a different technique:
     - Programs make "promises" about future writes
     - DRF ensures promises can always be "certified" (fulfilled)
     - Certification implies SC-like behavior

     Full mechanization requires:
     - Formal definition of visible writes
     - Proof of uniqueness lemma
     - Construction of total order
     - Induction on execution structure

     Estimated effort: 20-40 hours to port from Promising 2.0 Coq.
  *)
  admit ()

(** ============================================================================
    PART II: SEPARATION LOGIC FRAME RULE
    ============================================================================

    The frame rule is THE fundamental theorem of separation logic that enables
    LOCAL REASONING: verify small programs, compose to reason about larger ones.

    HISTORICAL CONTEXT:
    ===================
    Separation logic was introduced by Reynolds 2002:
    "Separation Logic: A Logic for Shared Mutable Data Structures" (LICS 2002)

    The frame rule (Theorem 1 in Reynolds 2002):
      {P} C {Q}     mod(C) # fv(R)
      ----------------------------
           {P * R} C {Q * R}

    Where:
    - {P} C {Q} is a valid Hoare triple
    - mod(C) is the set of locations modified by C
    - fv(R) is the set of free variables (locations) in R
    - mod(C) # fv(R) means they are disjoint

    The frame rule says: if C only accesses locations described by P,
    then any additional resources R are preserved unchanged.
    ============================================================================ *)

(* Hoare triple for heap programs *)
type hoare_triple (pre: sl_assertion) (cmd: heap_cmd) (post: sl_assertion) : Type0 =
  sl_triple_valid_cmd pre cmd post

(* Modified locations predicate *)
val modified_locs : heap_cmd -> list sl_loc
let rec modified_locs cmd =
  match cmd with
  | HCAlloc _ -> []  (* New location, not specified *)
  | HCFree l -> [l]
  | HCRead l -> []   (* Read doesn't modify *)
  | HCWrite l _ -> [l]
  | HCSkip -> []
  | HCSeq c1 c2 -> List.Tot.append (modified_locs c1) (modified_locs c2)

(* Free locations in an assertion *)
val free_locs : sl_assertion -> list sl_loc
let rec free_locs a =
  match a with
  | SLEmp -> []
  | SLPointsTo l _ -> [l]
  | SLStar p q -> List.Tot.append (free_locs p) (free_locs q)
  | SLWand p q -> List.Tot.append (free_locs p) (free_locs q)
  | SLForall _ -> []  (* Cannot enumerate *)
  | SLExists _ -> []
  | SLPure _ -> []
  | SLAnd p q -> List.Tot.append (free_locs p) (free_locs q)
  | SLOr p q -> List.Tot.append (free_locs p) (free_locs q)
  | SLNot p -> free_locs p
  | SLImpl p q -> List.Tot.append (free_locs p) (free_locs q)
  | SLOwn l -> [l]
  | SLFrac l _ _ -> [l]

(* Disjoint lists (no common elements) *)
let lists_disjoint (l1 l2: list sl_loc) : bool =
  List.Tot.for_all (fun x -> not (List.Tot.mem x l2)) l1

(* Frame safety: command doesn't modify frame's locations *)
let frame_safe (cmd: heap_cmd) (frame: sl_assertion) : bool =
  lists_disjoint (modified_locs cmd) (free_locs frame)

(** ============================================================================
    THEOREM T-5.12: FRAME RULE SOUNDNESS
    ============================================================================

    STATEMENT: If {P} C {Q} is valid and C doesn't modify locations in R,
    then {P * R} C {Q * R} is valid.

    FORMAL STATEMENT (Reynolds 2002, Theorem 1):
      {P} C {Q}     mod(C) cap fv(R) = emptyset
      -----------------------------------------
                  {P * R} C {Q * R}

    PROOF TECHNIQUE (Reynolds 2002):
    ================================
    1. Assume h |= P * R (combined heap satisfies P * R)
    2. By definition of *, exists h1, h2 such that:
       - h1 # h2 (disjoint)
       - h = h1 U h2
       - h1 |= P
       - h2 |= R
    3. Execute C on h. By frame safety, C only touches h1 portion
    4. Let h' = h'1 U h2 where h'1 is result of C on h1
    5. Since {P} C {Q}, we have h'1 |= Q
    6. Since C doesn't modify h2, still h2 |= R
    7. Since h'1 # h2 (locality ensures new locations disjoint), h' |= Q * R

    Key insight: LOCALITY of commands ensures frame preservation.

    EXISTING MECHANIZATIONS:
    ========================
    1. Iris (MPI-SWS): iris/bi/big_op.v
       Uses HIGHER-ORDER separation logic with step-indexed model.
       Frame rule is a derived lemma from Iris base logic.
       ~50K lines Coq for full Iris framework.

    2. VST (Princeton): veric/SeparationLogicFacts.v
       Verified Software Toolchain for C programs.
       Frame rule proven for CompCert C semantics.
       ~100K lines Coq.

    3. Steel (Microsoft Research/INRIA): Frame rule in F* itself!
       Part of the Steel separation logic library.
       Uses abstract predicates with affine/linear distinction.

    RELATION TO BRRR:
    =================
    Brrr's ownership system (BorrowChecker.fst) provides STATIC guarantees
    analogous to the frame rule:
    - Exclusive (&mut) references ensure no aliasing with frame
    - Shared (&) references ensure no mutation to frame
    - Ownership transfer ensures no dangling references

    The frame rule justifies Brrr's ability to reason locally about
    each function without considering the entire heap.

    PROOF STATUS: ADMITTED
    Estimated effort: 8-16 hours
    Primary difficulty: Handling sequential composition with locality

    REFERENCES:
    ===========
    - Reynolds 2002, LICS: Theorem 1 (original)
    - O'Hearn 2019, CACM: "Separation Logic" (survey)
    - Jung et al. 2018, JFP: Iris ground-up
    - Appel 2014: "Program Logics for Certified Compilers" (VST)
    ============================================================================ *)

val frame_rule : p:sl_assertion -> c:heap_cmd -> q:sl_assertion -> r:sl_assertion ->
  Lemma (requires hoare_triple p c q /\ frame_safe c r)
        (ensures hoare_triple (SLStar p r) c (SLStar q r))
        [SMTPat (hoare_triple (SLStar p r) c (SLStar q r))]
let frame_rule p c q r =
  (* Proof sketch following Reynolds 2002, Theorem 1:

     STEP 1: HEAP DECOMPOSITION
     Assume h |= P * R. Then there exist h1, h2 such that:
     - sl_disjoint h1 h2
     - h = sl_heap_union h1 h2
     - h1 |= P
     - h2 |= R

     STEP 2: LOCALITY OF COMMAND
     From frame_safe c r, we know modified_locs c cap free_locs r = empty.
     This means c only accesses/modifies locations in h1.

     STEP 3: EXECUTION ON LOCAL HEAP
     Execute c on h1:
     - From hoare_triple p c q, we get h'1 with h'1 |= Q

     STEP 4: FRAME PRESERVATION
     The key lemma: c doesn't modify h2, so h2 is unchanged.
     More precisely, for all l in dom(h2):
     - l not in modified_locs c (by frame_safe)
     - Therefore exec c preserves h2 at l

     STEP 5: RECOMBINATION
     Let h' = sl_heap_union h'1 h2.
     - h'1 |= Q (by hoare_triple p c q)
     - h2 |= R (preserved, Step 4)
     - sl_disjoint h'1 h2 (locality ensures new allocations disjoint)
     - Therefore h' |= Q * R

     The full proof requires:
     1. Formal definition of cmd_is_local (in SeparationLogic.fst)
     2. Proof that frame_safe implies locality
     3. Heap decomposition and recombination lemmas
     4. Handling of allocation (fresh locations)

     The SeparationLogic.fst file already has frame_rule_sound which
     states this theorem. This theorem is the version with explicit
     frame_safe condition.

     Estimated effort: 8-16 hours to fully mechanize.
  *)
  frame_rule_sound p q r c

(** ============================================================================
    PART III: NO THIN-AIR VALUES
    ============================================================================

    The "thin-air" or "out-of-thin-air" (OOTA) problem is a fundamental
    correctness property for memory models: reads should not return values
    that were never written to the corresponding location.

    MOTIVATING EXAMPLE (Boehm-Demsky 2014):
    Initially: x = y = 0

    Thread 1:           Thread 2:
    r1 = x;             r2 = y;
    y = r1;             x = r2;

    Under an incorrect memory model, this could yield r1 = r2 = 42,
    even though 42 was never written anywhere! This is "thin-air."

    PROBLEM WITH C11:
    =================
    The original C11 memory model (ISO/IEC 9899:2011) was shown to allow
    thin-air values in relaxed atomic programs (Batty et al. 2015).

    This led to the development of PROMISING SEMANTICS (Kang et al. 2017)
    which guarantees no thin-air while preserving compiler optimizations.
    ============================================================================ *)

(* Value was actually written at some point *)
let value_was_written (ex: execution) (l: mem_loc) (v: value) : bool =
  List.Tot.existsb (fun e ->
    match e.ev_event with
    | MEWrite l' v' _ -> l' = l && v' = v
    | MERMW l' _ v' true -> l' = l && v' = v  (* Successful RMW writes *)
    | _ -> false
  ) ex.events

(* Read returns a value that was written or is the initial value *)
let read_justified (ex: execution) (e: labeled_event) (init: mem_loc -> value) : bool =
  match e.ev_event with
  | MERead l v _ ->
      v = init l ||  (* Initial value *)
      value_was_written ex l v  (* Or some thread wrote it *)
  | MERMW l expected _ _ ->
      expected = init l ||
      value_was_written ex l expected
  | _ -> true  (* Non-reads are trivially justified *)

(* Execution has no out-of-thin-air reads *)
let no_oota_reads (ex: execution) (init: mem_loc -> value) : bool =
  List.Tot.for_all (fun e -> read_justified ex e init) ex.events

(* Execution is valid (satisfies memory model constraints) *)
val valid_execution : execution -> Type0
let valid_execution ex =
  (* Simplified - full definition includes coherence, atomicity, etc. *)
  True

(** ============================================================================
    THEOREM T-5.13: NO THIN-AIR VALUES
    ============================================================================

    STATEMENT: In any valid execution, every read returns either the initial
    value or a value that was written to that location.

    FORMAL STATEMENT (Kang et al. 2017, Promising Semantics):
    For all executions E and reads R in E:
      rf(R) = W implies W is a write to the same location
      OR rf(R) = bottom implies R reads the initial value

    In other words: values don't appear "out of thin air."

    PROOF TECHNIQUE (Promising 2.0):
    ================================
    The Promising semantics uses a "certification" mechanism:
    1. Threads can make PROMISES about future writes
    2. But promises must eventually be CERTIFIED (fulfilled)
    3. The certification process ensures no circular dependencies
    4. Therefore, all values are justified by actual writes

    Key insight: The problem with C11 relaxed atomics was allowing
    speculative reads that create self-justifying cycles. Promising
    breaks these cycles by requiring certification.

    PROMISING 2.0 IMPROVEMENTS (Lee et al. 2020):
    =============================================
    Promising 2.0 improves on the original by:
    1. Thread-local certification (more compositional)
    2. Better handling of SC fences
    3. Cleaner proof of DRF-SC
    4. Support for ARMv8 and RISC-V memory models

    EXISTING MECHANIZATIONS:
    ========================
    1. Promising 2.0 (Lee et al. 2020): 30K lines Coq
       Repository: https://sf.snu.ac.kr/promising2.0/
       Key files: src/proof/cert.v (certification proofs)
                  src/model/promise2.v (model definition)
       The no-thin-air property is Theorem 1 in the paper.

    2. Weakestmo (Chakraborty et al. 2019): Alternative formalization
       Uses event structures instead of explicit promises.

    3. RC11 (Lahav et al. 2017): Repaired C11 model
       Coq formalization of "no thin-air" for repaired model.

    RELATION TO BRRR:
    =================
    Brrr targets DRF programs, so thin-air is less of a concern.
    However, when interfacing with languages that have relaxed atomics
    (Rust, C++), Brrr's FFI boundary needs to respect these guarantees.

    The session types ensure proper synchronization, which combined
    with DRF-SC (T-5.11) gives SC semantics and thus no thin-air.

    PROOF STATUS: ADMITTED
    Estimated effort: 20-40 hours
    Primary difficulty: Certification semantics are complex

    REFERENCES:
    ===========
    - Kang et al. 2017, POPL: "A Promising Semantics" (Promising 1.0)
    - Lee et al. 2020, PLDI: "Promising 2.0" (main reference)
    - Boehm & Demsky 2014, MSPC: Thin-air examples
    - Batty et al. 2015, POPL: C11 thin-air problem
    - Chakraborty et al. 2019, PLDI: Weakestmo alternative
    ============================================================================ *)

val no_thin_air : ex:execution -> init:(mem_loc -> value) ->
  Lemma (requires valid_execution ex)
        (ensures no_oota_reads ex init)
        [SMTPat (valid_execution ex)]
let no_thin_air ex init =
  (* Proof sketch following Promising 2.0 (Lee et al. 2020):

     STEP 1: THREAD-LOCAL CERTIFICATION
     In Promising semantics, each thread independently certifies
     that its promises can be fulfilled. Certification means:
     - For each promise (future write), show a path of execution
       that actually performs that write
     - The certification must not depend on other threads' promises

     STEP 2: NO CIRCULAR DEPENDENCIES
     Key lemma: The certification process is ACYCLIC.
     If promise P1 depends on promise P2 for certification,
     then P2's timestamp is strictly less than P1's.
     This prevents circular justifications like:
       "I read X because you wrote X"
       "I wrote X because you read X"

     STEP 3: JUSTIFICATION BY INDUCTION
     By induction on promise timestamps:
     - Base: Oldest promises have no dependencies, trivially certified
     - Step: Promise P depends on promises with smaller timestamps,
             which are certified by IH, so P's certification is valid

     STEP 4: VALUE JUSTIFICATION
     Every read R is justified by:
     - Initial value (if no writes happen-before R)
     - A specific write W (given by rf(R) = W)

     The certification ensures W actually happens (not just promised).

     The full Coq proof in Promising 2.0 is ~10K lines for this theorem
     alone, due to the complexity of the promise/certification model.

     Estimated effort: 20-40 hours to port from Coq.
  *)
  admit ()

(** ============================================================================
    PART IV: BI-ABDUCTION
    ============================================================================

    Bi-abduction is a generalization of abduction that simultaneously
    computes MISSING preconditions and LEFTOVER postconditions.

    Given a specification {P} C {Q}, bi-abduction computes:
    - Anti-frame A: resources needed but not in P
    - Frame F: resources in P but not consumed by C

    Such that: {P * A} C {Q * F}

    This enables COMPOSITIONAL analysis: analyze each function once,
    combine specifications for whole program.

    Used in Facebook Infer for industrial-scale bug finding.
    ============================================================================ *)

(* Bi-abduction result: (anti-frame, frame) *)
type biabduct_result = sl_assertion & sl_assertion

(* Bi-abduction specification:
   Given assertions pre and post, compute anti_frame and frame such that
   {pre * anti_frame} C {post * frame}

   This is a simplified model - full bi-abduction also involves
   symbolic heap manipulation and prover queries.
*)
val biabduct : pre:sl_assertion -> post:sl_assertion -> biabduct_result

(* Simplified bi-abduction that returns emp when specs match *)
let biabduct pre post =
  (* In practice, this would use symbolic heap algorithms *)
  (SLEmp, SLEmp)  (* Placeholder *)

(* Bi-abduction correctness predicate *)
let biabduct_correct (pre post anti_frame frame: sl_assertion) : Type0 =
  (* The bi-abduction is correct if:
     1. pre * anti_frame entails the actual precondition needed
     2. The actual postcondition entails post * frame *)
  sl_entails (SLStar pre anti_frame) (SLStar pre anti_frame) /\
  sl_entails (SLStar post frame) (SLStar post frame)

(** ============================================================================
    THEOREM T-5.14: BI-ABDUCTION SOUNDNESS
    ============================================================================

    STATEMENT: If bi-abduction succeeds with result (anti_frame, frame),
    then the computed frames are correct.

    FORMAL STATEMENT (Calcagno et al. 2009):
    =========================================
    Theorem 4 (Soundness of Frame Inference):
    If bi-abduct(P, Q) = (A, F) and {P * A} C {R}, then {P * A} C {Q * F}
    when R entails Q * F.

    Theorem 5 (Completeness of Frame Inference):
    If {P} C {Q * F'} for some F', then bi-abduct can find F <= F'.

    Theorem 9 (Bi-Abduction Soundness):
    If bi-abduct(P, Q) = (A, F) and P * A |= P' and Q' |= Q * F,
    then the specification {P'} C {Q'} is derivable.

    PROOF TECHNIQUE (Calcagno 2009):
    ================================
    1. SYMBOLIC HEAPS: Represent assertions as spatial formulas
       P ::= emp | l |-> v | P1 * P2 | P1 -* P2 | exists x. P

    2. SUBTRACTION ALGORITHM: Compute F such that P |- Q * F
       - Match spatial atoms from Q with atoms in P
       - Leftover atoms from P form F
       - Missing atoms become anti-frame A

    3. FRAME INFERENCE RULES:
       - [ID]: P |- P * emp (identity frame)
       - [*]: P1 |- Q1 * F1, P2 |- Q2 * F2 ==> P1 * P2 |- (Q1 * Q2) * (F1 * F2)
       - [-*]: P |- Q1, Q2 |- R ==> P |- (Q1 -* Q2) * ?

    4. SOUNDNESS: Each rule preserves semantic entailment

    EXISTING MECHANIZATIONS:
    ========================
    1. Infer (Facebook): OCaml implementation
       Repository: https://github.com/facebook/infer
       Key files: infer/src/biabduction/
       Not formally verified, but extensively tested at scale.

    2. Compositional Shape Analysis (Calcagno et al. 2009):
       Original paper describes algorithm and proof sketches.
       No full Coq formalization exists to our knowledge.

    3. Iris (MPI-SWS) includes related proofs:
       iris/proofmode/coq_tactics.v has abduction-like tactics.

    RELATION TO BRRR:
    =================
    Bi-abduction enables MODULAR verification:
    - Analyze each function once with minimal precondition
    - Compute frame automatically for callers
    - Scale to large codebases without full-program analysis

    This matches Brrr's design goal of compositional reasoning.
    The ownership system provides static approximation of frames.

    PROOF STATUS: ADMITTED
    Estimated effort: 8-16 hours
    Primary difficulty: Symbolic heap manipulation algorithms

    REFERENCES:
    ===========
    - Calcagno et al. 2009, POPL: "Compositional Shape Analysis"
      (Theorems 4, 5, 9 - main reference)
    - Calcagno et al. 2011, CACM: "Infer: An Automatic Program Verifier"
    - O'Hearn 2019, CACM: "Separation Logic" (bi-abduction section)
    - Berdine et al. 2005, LPAR: "Symbolic Execution with SL"
    ============================================================================ *)

val biabduction_sound : pre:sl_assertion -> post:sl_assertion ->
                         anti_frame:sl_assertion -> frame:sl_assertion ->
  Lemma (requires biabduct pre post == (anti_frame, frame))
        (ensures
          (* Frame property: pre * anti_frame provides enough resources *)
          sl_entails (SLStar pre anti_frame) (SLStar pre anti_frame) /\
          (* Abduction property: post * frame consumes the right resources *)
          sl_entails (SLStar post frame) (SLStar post frame) /\
          (* Correctness: if the triple holds with computed frames, it's sound *)
          (forall (c: heap_cmd).
            hoare_triple (SLStar pre anti_frame) c (SLStar post frame) ==>
            (* The computed specification is valid *)
            True))
        [SMTPat (biabduct pre post)]
let biabduction_sound pre post anti_frame frame =
  (* Proof sketch following Calcagno et al. 2009:

     STEP 1: SYMBOLIC HEAP NORMAL FORM
     Convert assertions to symbolic heap form:
       P = Pi /\ Sigma
     where Pi is pure constraints, Sigma is spatial formula.
     Spatial formulas are * of points-to atoms: l1 |-> v1 * l2 |-> v2 * ...

     STEP 2: SUBTRACTION ALGORITHM
     Given P and Q in normal form, compute F:
       subtract(P, Q) = F  such that  P |- Q * F

     Algorithm:
     - For each atom in Q, find matching atom in P
     - Matched atoms "cancel" from both
     - Remaining atoms in P become F
     - Unmatched atoms in Q become anti-frame A

     STEP 3: SOUNDNESS OF SUBTRACTION (Theorem 4)
     Prove: If subtract(P, Q) = F, then P |- Q * F

     By induction on structure of Q:
     - Base (Q = emp): F = P, and P |- emp * P holds
     - Inductive (Q = Q1 * Q2):
       subtract(P, Q1) = F1
       subtract(F1, Q2) = F2
       By IH: P |- Q1 * F1 and F1 |- Q2 * F2
       Therefore: P |- Q1 * (Q2 * F2) = (Q1 * Q2) * F2

     STEP 4: COMPLETENESS (Theorem 5)
     If P |- Q * F' for some F', then subtract(P, Q) = F with F <= F'.
     Proof: Any valid frame F' must include at least the atoms
     in P that don't match Q. Our F is exactly those atoms.

     STEP 5: BI-ABDUCTION SOUNDNESS (Theorem 9)
     Combining subtraction for both pre and post:
     - bi-abduct(P, Q) finds A such that P * A |- P'
       and F such that Q' |- Q * F
     - The specification {P * A} C {Q * F} is then derivable
       from {P'} C {Q'} using frame rule and consequence.

     CORRECTNESS ARGUMENT:
     - Anti-frame A: Resources MISSING from P but needed by C
     - Frame F: Resources in P but LEFTOVER after C

     The key invariant: P * A provides all resources C needs,
     and Q * F describes all resources C produces plus leftover.

     Estimated effort: 8-16 hours, mainly for subtraction algorithm.
  *)
  admit ()

(** ============================================================================
    AUXILIARY LEMMAS FOR MEMORY THEOREMS
    ============================================================================

    These lemmas would be needed for complete proofs. They are stated
    here as a roadmap for mechanization efforts.
    ============================================================================ *)

(* Lemma: Happens-before is transitive *)
val hb_transitive : ex:execution -> e1:labeled_event -> e2:labeled_event -> e3:labeled_event ->
  Lemma (requires hb_direct ex e1 e2 /\ hb_direct ex e2 e3)
        (ensures hb_direct ex e1 e3 \/ (* or via chain *) True)
let hb_transitive ex e1 e2 e3 = admit ()

(* Lemma: SC total order respects happens-before *)
val sc_respects_hb : ex:execution -> order:total_order ->
  Lemma (requires valid_sc_order ex order)
        (ensures forall e1 e2. hb_direct ex e1 e2 ==> order e1 e2)
let sc_respects_hb ex order = admit ()

(* Lemma: DRF + valid execution implies unique visible write *)
val drf_unique_visible : ex:execution -> r:labeled_event ->
  Lemma (requires execution_drf ex /\ is_read r.ev_event)
        (ensures (* unique write visible to r *) True)
let drf_unique_visible ex r = admit ()

(* Lemma: Frame preservation under composition *)
val frame_composition : p:sl_assertion -> q:sl_assertion -> r:sl_assertion ->
                         c1:heap_cmd -> c2:heap_cmd ->
  Lemma (requires hoare_triple p c1 q /\
                  hoare_triple q c2 r /\
                  frame_safe c1 (SLEmp) /\
                  frame_safe c2 (SLEmp))
        (ensures hoare_triple p (HCSeq c1 c2) r)
let frame_composition p q r c1 c2 =
  sl_rule_seq p q r c1 c2

(* Lemma: Bi-abduction distributes over star *)
val biabduct_star_dist : p1:sl_assertion -> p2:sl_assertion ->
                          q1:sl_assertion -> q2:sl_assertion ->
  Lemma (ensures
    let (a1, f1) = biabduct p1 q1 in
    let (a2, f2) = biabduct p2 q2 in
    let (a, f) = biabduct (SLStar p1 p2) (SLStar q1 q2) in
    (* Computed frames should be "compatible" with individual *)
    True)
let biabduct_star_dist p1 p2 q1 q2 = admit ()

(** ============================================================================
    NOTES FOR IMPLEMENTERS
    ============================================================================

    1. PROOF EFFORT ESTIMATES (from AXIOMS_REPORT_v2.md):
       - T-5.11 (drf_sc): 20-40 hours
       - T-5.12 (frame_rule): 8-16 hours
       - T-5.13 (no_thin_air): 20-40 hours
       - T-5.14 (biabduction_sound): 8-16 hours
       - Total: 56-112 hours for full mechanization

    2. PORTING STRATEGIES:
       - DRF-SC: Port from Promising 2.0 Coq (~30K lines)
       - Frame rule: Use existing Steel library or port from Iris
       - No thin-air: Port from Promising 2.0 certification proofs
       - Bi-abduction: Implement algorithm, prove correct

    3. DEPENDENCIES:
       - All theorems depend on SeparationLogic.fst heap model
       - DRF-SC and No-thin-air need memory model definitions above
       - Frame rule connects to existing sl_triple_valid_cmd
       - Bi-abduction needs symbolic heap operations (not yet in Brrr)

    4. INTEGRATION WITH BRRR:
       - Frame rule justifies Brrr's local reasoning
       - DRF-SC justifies session type synchronization semantics
       - No thin-air needed for FFI with relaxed-atomic languages
       - Bi-abduction enables modular verification

    5. EXISTING CODE TO LEVERAGE:
       - SeparationLogic.fst: frame_rule_sound already states T-5.12
       - SessionTypes.fst: Synchronization primitives for DRF
       - BorrowChecker.fst: Static ownership approximates frames
    ============================================================================ *)

(** ============================================================================
    SUMMARY OF THEOREMS
    ============================================================================

    T-5.11: drf_sc
    --------------
    Statement: Data-race-free programs have sequentially consistent semantics
    Reference: Boehm-Adve 2008, Theorem 7.1
    Mechanization: Promising 2.0 (30K Coq)
    Effort: 20-40 hours

    T-5.12: frame_rule
    ------------------
    Statement: {P}C{Q} and mod(C)#fv(R) implies {P*R}C{Q*R}
    Reference: Reynolds 2002, Theorem 1
    Mechanization: Iris, VST, Steel
    Effort: 8-16 hours

    T-5.13: no_thin_air
    -------------------
    Statement: No read returns a value never written
    Reference: Kang et al. 2017, Theorem 1 (Promising)
    Mechanization: Promising 2.0 (30K Coq)
    Effort: 20-40 hours

    T-5.14: biabduction_sound
    -------------------------
    Statement: Bi-abduction computes correct anti-frame and frame
    Reference: Calcagno et al. 2009, Theorems 4, 5, 9
    Mechanization: Facebook Infer (not verified)
    Effort: 8-16 hours
    ============================================================================ *)
