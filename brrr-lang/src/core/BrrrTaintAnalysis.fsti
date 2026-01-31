(**
 * BrrrLang.Core.TaintAnalysis Interface
 *
 * ============================================================================
 * INFORMATION FLOW ANALYSIS FOR SECURITY VULNERABILITY DETECTION
 * ============================================================================
 *
 * This module implements a STATIC TAINT ANALYSIS framework for tracking the
 * flow of untrusted (tainted) data through programs. Taint analysis is a
 * fundamental technique in security research for detecting vulnerabilities
 * such as SQL injection, cross-site scripting (XSS), and command injection.
 *
 * ============================================================================
 * THEORETICAL FOUNDATIONS
 * ============================================================================
 *
 * The taint analysis is based on the SOURCE-SINK-SANITIZER model:
 *
 *   - SOURCES: Points where untrusted data enters the system
 *     (user input, network data, file contents, environment variables)
 *
 *   - SINKS: Security-sensitive operations that should not receive tainted data
 *     (SQL queries, shell commands, HTML output, file operations)
 *
 *   - SANITIZERS: Functions that properly validate/encode data, removing taint
 *     (SQL escaping, HTML encoding, input validation)
 *
 * A taint analysis violation occurs when tainted data reaches a sink without
 * passing through an appropriate sanitizer.
 *
 * ============================================================================
 * LITERATURE REFERENCES
 * ============================================================================
 *
 * This implementation draws from seminal work in taint analysis:
 *
 *   [1] Livshits, V.B. & Lam, M.S. (2005). "Finding Security Vulnerabilities
 *       in Java Applications with Static Analysis." USENIX Security Symposium.
 *       - Introduced static taint analysis for web application security
 *       - Defined the source-sink-sanitizer model used here
 *
 *   [2] Arzt, S. et al. (2014). "FlowDroid: Precise Context, Flow, Field,
 *       Object-sensitive and Lifecycle-aware Taint Analysis for Android Apps."
 *       PLDI 2014.
 *       - State-of-the-art taint tracking with flow sensitivity
 *       - Inspired our taint kind categorization
 *
 *   [3] Tripp, O. et al. (2009). "TAJ: Effective Taint Analysis of Web
 *       Applications." PLDI 2009.
 *       - Hybrid static/dynamic approach to taint tracking
 *       - Soundness guarantees similar to our lattice-based approach
 *
 *   [4] Denning, D.E. (1976). "A Lattice Model of Secure Information Flow."
 *       Communications of the ACM.
 *       - Original lattice-based information flow model
 *       - Our taint_status forms a bounded lattice following this work
 *
 * ============================================================================
 * TAINT KINDS (Vulnerability Categories)
 * ============================================================================
 *
 * The specification (brrr_lang_spec_v0.4.tex, Section IX-B) defines distinct
 * taint kinds for different vulnerability classes. This module implements
 * five primary kinds based on OWASP Top 10:
 *
 *   TaintSQLi          - SQL Injection (CWE-89)
 *   TaintXSS           - Cross-Site Scripting (CWE-79)
 *   TaintCMDi          - OS Command Injection (CWE-78)
 *   TaintPathTraversal - Path Traversal (CWE-22)
 *   TaintSSRF          - Server-Side Request Forgery (CWE-918)
 *
 * Each kind requires a DIFFERENT sanitizer - SQL escaping does not protect
 * against XSS, and vice versa. This is why we track kinds separately rather
 * than using a single "tainted" flag.
 *
 * ============================================================================
 * SOUNDNESS vs. COMPLETENESS TRADEOFFS
 * ============================================================================
 *
 * This analysis is designed to be SOUND (no false negatives):
 *
 *   - If the analysis says data is untainted, it truly is untainted
 *   - All actual vulnerabilities are detected (may have false positives)
 *   - Taint propagates conservatively through all operations
 *
 * Soundness is guaranteed by the lattice structure:
 *   - taint_join is the LEAST UPPER BOUND (union of taint kinds)
 *   - Operations always propagate taint upward in the lattice
 *   - sanitize is the ONLY way to remove taint
 *
 * The tradeoff is PRECISION (false positives):
 *   - Over-tainting may occur when branches merge
 *   - Aliasing may cause spurious taint propagation
 *   - Context-insensitive analysis may be imprecise
 *
 * Key soundness theorems (proven in BrrrTaintAnalysis.fst):
 *   - sanitize_removes_taint: sanitize k t f does not contain k
 *   - sink_soundness: sink k t = Some v iff t does not contain k
 *   - sanitize_then_sink: sink k (sanitize k t f) = Some _
 *
 * ============================================================================
 * LATTICE STRUCTURE
 * ============================================================================
 *
 * Taint statuses form a BOUNDED JOIN SEMILATTICE:
 *
 *                  Tainted [all kinds]   (TOP - maximally tainted)
 *                         / | \
 *           Tainted [SQLi] Tainted [XSS] ...
 *                         \ | /
 *                       Untainted         (BOTTOM - no taint)
 *
 * Operations satisfy standard lattice laws (all proven without admits):
 *
 *   - IDENTITY:      join Untainted t = t = join t Untainted
 *   - COMMUTATIVITY: join t1 t2 = join t2 t1 (semantically)
 *   - ASSOCIATIVITY: join (join t1 t2) t3 = join t1 (join t2 t3)
 *   - IDEMPOTENCE:   join t t = t
 *   - ABSORPTION:    join t (meet t s) = t, meet t (join t s) = t
 *
 * The partial order taint_leq corresponds to "less tainted than":
 *   t1 <= t2 iff all taint kinds in t1 are also in t2
 *
 * ============================================================================
 * IMPLICIT FLOW TRACKING
 * ============================================================================
 *
 * The module supports IMPLICIT FLOW tracking via PC (program counter) taint.
 * Implicit flows occur through control dependence:
 *
 *   if (tainted_condition) {
 *     x = 1;  (* x is implicitly tainted *)
 *   } else {
 *     x = 0;  (* x is implicitly tainted *)
 *   }
 *
 * The raise_pc_taint operation elevates the PC taint when entering a
 * conditional with a tainted condition. Assignments under elevated PC
 * must target variables with compatible taint levels.
 *
 * ============================================================================
 * USAGE PATTERNS
 * ============================================================================
 *
 * Typical secure code pattern:
 *
 *   (* 1. Data enters from untrusted source *)
 *   let user_input = source TaintSQLi (read_user_input ()) in
 *
 *   (* 2. Sanitize before use *)
 *   let safe_input = sanitize TaintSQLi user_input escape_sql in
 *
 *   (* 3. Use at sink - succeeds because taint was removed *)
 *   match sink TaintSQLi safe_input with
 *   | Some v -> execute_query v
 *   | None -> (* Should not happen if sanitized *) ()
 *
 * ============================================================================
 * MODULE INTERFACE
 * ============================================================================
 *
 * This interface provides:
 *   - Taint kinds for vulnerability categorization
 *   - Taint status type with lattice operations (join, meet, leq)
 *   - Lattice law lemmas (commutativity, associativity, idempotence, absorption)
 *   - Source/Sink/Sanitizer primitives for taint tracking
 *   - Monadic operations for composing tainted computations
 *
 * Soundness properties are proven in the implementation (BrrrTaintAnalysis.fst).
 *)
module BrrrTaintAnalysis

open FStar.List.Tot

(** ============================================================================
    TAINT KINDS (Vulnerability Categories)
    ============================================================================

    Taint kinds categorize the type of security vulnerability. Each kind
    corresponds to a distinct attack vector requiring different mitigation:

    From the OWASP Top 10 (2021) and CWE database:

    | Kind             | Attack                    | CWE  | Mitigation              |
    |------------------|---------------------------|------|-------------------------|
    | TaintSQLi        | SQL Injection             | 89   | Parameterized queries   |
    | TaintXSS         | Cross-Site Scripting      | 79   | Output encoding         |
    | TaintCMDi        | Command Injection         | 78   | Input validation/escape |
    | TaintPathTraversal| Path Traversal           | 22   | Canonicalization        |
    | TaintSSRF        | Server-Side Request Forgery| 918 | URL allowlist           |

    The type forms a finite enumeration enabling decidable equality.
    Extensions to this set should follow the pattern established here.

    NOTE: The specification (brrr_lang_spec_v0.4.tex) mentions potential for
    additional kinds (LDAP injection, XML injection, etc.). The core five
    cover the most critical web application vulnerabilities per OWASP.

    ============================================================================ *)

(**
 * Taint kind enumeration for vulnerability categorization.
 *
 * Each constructor represents a distinct vulnerability class that requires
 * a specific sanitization strategy. Data tainted with one kind may still
 * be safely used in contexts expecting other kinds (e.g., SQL-tainted data
 * can be safely written to a log file).
 *
 * Historical note: This taxonomy follows FlowDroid (Arzt et al. 2014) and
 * extends the original source-sink model of Livshits & Lam (2005).
 *)
type taint_kind =
  | TaintSQLi          : taint_kind  (* SQL Injection - CWE-89 *)
  | TaintXSS           : taint_kind  (* Cross-Site Scripting - CWE-79 *)
  | TaintCMDi          : taint_kind  (* OS Command Injection - CWE-78 *)
  | TaintPathTraversal : taint_kind  (* Path/Directory Traversal - CWE-22 *)
  | TaintSSRF          : taint_kind  (* Server-Side Request Forgery - CWE-918 *)

(**
 * Decidable equality on taint kinds.
 *
 * Using 'unfold' makes this definition visible to the F* normalizer,
 * allowing SMT proofs about taint_kind equality to complete by computation
 * rather than requiring explicit case analysis. This is a key optimization
 * following HACL* patterns (see Lib.IntTypes for similar approach).
 *
 * The strict_on_arguments attribute ensures eager evaluation when both
 * arguments are concrete, improving performance in the normalizer.
 *
 * Implementation note: We use explicit pattern matching rather than
 * deriving equality to maintain control over normalization behavior
 * and ensure optimal SMT encoding.
 *)
[@(strict_on_arguments [0;1])]
unfold
let taint_kind_eq (k1 k2: taint_kind) : bool =
  match k1, k2 with
  | TaintSQLi, TaintSQLi -> true
  | TaintXSS, TaintXSS -> true
  | TaintCMDi, TaintCMDi -> true
  | TaintPathTraversal, TaintPathTraversal -> true
  | TaintSSRF, TaintSSRF -> true
  | _, _ -> false

(**
 * Reflexivity of taint_kind_eq.
 *
 * Every taint kind is equal to itself. Trivial with unfold - the SMT solver
 * can verify this by normalization alone. The SMT pattern triggers this
 * lemma automatically when reflexive equality appears in goals.
 *)
val taint_kind_eq_refl : k:taint_kind ->
    Lemma (ensures taint_kind_eq k k = true)
          [SMTPat (taint_kind_eq k k)]

(**
 * Symmetry of taint_kind_eq.
 *
 * If k1 equals k2, then k2 equals k1. Trivial with unfold - both
 * directions normalize to the same boolean computation.
 *)
val taint_kind_eq_sym : k1:taint_kind -> k2:taint_kind ->
    Lemma (requires taint_kind_eq k1 k2 = true)
          (ensures taint_kind_eq k2 k1 = true)

(**
 * taint_kind_eq implies Leibniz equality.
 *
 * This lemma bridges the gap between our decidable boolean equality
 * and F*'s propositional equality. Essential for rewriting in proofs
 * and for connecting to other definitions using propositional equality.
 *
 * The proof is trivial: with unfold, the normalizer can check all 25
 * cases (5x5) and verify that taint_kind_eq k1 k2 = true only when
 * k1 and k2 are the same constructor.
 *)
val taint_kind_eq_implies_eq : k1:taint_kind -> k2:taint_kind ->
    Lemma (requires taint_kind_eq k1 k2 = true)
          (ensures k1 = k2)

(** ============================================================================
    TAINT STATUS (Lattice Element)
    ============================================================================

    The taint status of a value indicates whether it contains untrusted data
    and, if so, what vulnerability categories apply.

    This type forms the carrier set of our BOUNDED JOIN SEMILATTICE:

                        Tainted [SQLi; XSS; CMDi; PathTraversal; SSRF]
                                          (TOP)
                              /       |        |       \
                   Tainted [SQLi]  [XSS]  [CMDi]  ...  [SSRF]
                              \       |        |       /
                                       Untainted
                                        (BOTTOM)

    The lattice ordering (taint_leq) corresponds to "information leakage":
    Untainted <= Tainted [k] <= Tainted [k1; k2] <= ... <= TOP

    Key insight: A value tainted with MULTIPLE kinds (e.g., [SQLi; XSS])
    requires sanitization for EACH kind before being safe at any sink.
    This models real-world scenarios where user input might be used in
    multiple contexts.

    DESIGN DECISION: We use a list rather than a set for implementation
    simplicity. The merge operations maintain canonical sorted order
    to ensure structural equality implies semantic equality.

    From Denning (1976): "The security class of every variable must
    be bounded by the security class of information stored in it."
    Our lattice enforces this through monotonic taint propagation.

    ============================================================================ *)

(**
 * Taint status - the lattice element tracking taint information.
 *
 * - Untainted: The value is known to be from trusted sources only.
 *   This is the BOTTOM element of the lattice.
 *
 * - Tainted ks: The value may contain data from untrusted sources,
 *   with vulnerability categories listed in ks. Multiple kinds
 *   indicate the value could be exploited in multiple ways.
 *
 * Invariant: Tainted [] is semantically equivalent to Untainted.
 * Use normalize_taint to canonicalize representation.
 *)
type taint_status =
  | Untainted : taint_status  (* Bottom: no taint, fully trusted *)
  | Tainted   : list taint_kind -> taint_status  (* List of vulnerability kinds *)

(**
 * Check if a taint status represents untainted (trusted) data.
 *
 * A value is considered untainted if it is explicitly Untainted OR
 * if it is Tainted with an empty list of kinds. The latter case can
 * occur after sanitizing all taint kinds from a previously tainted value.
 *
 * Using 'unfold' enables normalization-based proofs. When is_untainted
 * appears in a proof goal, F* can compute the result directly rather
 * than requiring case analysis lemmas.
 *
 * Security note: This predicate is used to determine if data is safe
 * to use at any sink. A true result means NO sanitization is required.
 *)
unfold
let is_untainted (t: taint_status) : bool =
  match t with
  | Untainted -> true
  | Tainted [] -> true  (* Empty taint list = effectively untainted *)
  | Tainted _ -> false

(**
 * Normalize taint status to canonical form.
 *
 * This function ensures a canonical representation by converting
 * Tainted [] to Untainted. This is important for:
 *
 *   1. Equality comparisons (structural = semantic)
 *   2. Pattern matching (single case for "untainted")
 *   3. Memory efficiency (Untainted is smaller than Tainted [])
 *
 * Normalization is idempotent: normalize (normalize t) = normalize t
 *
 * Using 'unfold' enables the normalizer to compute through this
 * function, simplifying proofs about taint status equality.
 *)
unfold
let normalize_taint (t: taint_status) : taint_status =
  match t with
  | Untainted -> Untainted
  | Tainted [] -> Untainted  (* Canonicalize empty taint list *)
  | Tainted ks -> Tainted ks

(**
 * Check if a taint status contains a specific taint kind.
 *
 * This is the fundamental query operation for taint analysis:
 * "Is this data potentially dangerous for vulnerability category k?"
 *
 * Properties:
 *   - taint_contains Untainted k = false (for all k)
 *   - taint_contains (Tainted [k]) k = true
 *   - taint_contains (Tainted ks) k = true iff k is in ks
 *
 * Used by sink to check if data is safe for a particular operation.
 * The function is recursive (defined in implementation) so we keep
 * it as a val declaration here.
 *)
val taint_contains : taint_status -> taint_kind -> bool

(** ============================================================================
    TAINT STATUS EQUALITY
    ============================================================================

    Semantic equality on taint statuses. Two statuses are equal if they
    contain exactly the same set of taint kinds. This is SET equality,
    not list equality - the order of kinds does not matter:

        taint_status_eq (Tainted [SQLi; XSS]) (Tainted [XSS; SQLi]) = true

    The implementation uses subset comparison in both directions:
        ks1 = ks2 (as sets) iff ks1 subset ks2 AND ks2 subset ks1

    This definition ensures that the canonical representation produced
    by merge operations gives structural equality when semantic equality
    holds.

    ============================================================================ *)

(**
 * Semantic equality on taint statuses.
 *
 * Compares the SETS of taint kinds, not the list representations.
 * This allows different list orderings to be considered equal.
 *
 * Uses normalize_taint to handle the Tainted [] = Untainted case.
 *)
val taint_status_eq : taint_status -> taint_status -> bool

(**
 * taint_status_eq is reflexive.
 *
 * Every taint status is equal to itself. The SMT pattern enables
 * automatic application when reflexive equality appears in goals.
 *)
val taint_status_eq_refl : t:taint_status ->
    Lemma (ensures taint_status_eq t t = true)
          [SMTPat (taint_status_eq t t)]

(** ============================================================================
    TAINT LATTICE OPERATIONS
    ============================================================================

    The taint status forms a BOUNDED LATTICE with join and meet operations.
    This algebraic structure is fundamental to sound information flow analysis
    (Denning 1976).

    LATTICE STRUCTURE:

        Bottom:  Untainted (no information leakage)
        Top:     Tainted [SQLi; XSS; CMDi; PathTraversal; SSRF] (maximum leakage)
        Join:    Union of taint kinds (least upper bound)
        Meet:    Intersection of taint kinds (greatest lower bound)

    WHY A LATTICE?

    The lattice structure guarantees SOUNDNESS of taint propagation:

    1. Join models INFORMATION COMBINATION: When two values are combined
       (e.g., string concatenation), the result is tainted with the union
       of both sources' taints. This is conservative - we never lose taint.

    2. Meet models INFORMATION FILTERING: When we know a value must satisfy
       multiple constraints, we can take the intersection of possible taints.

    3. Monotonicity ensures NO FALSE NEGATIVES: Operations can only move
       UP in the lattice (more tainted), never down, except through explicit
       sanitization.

    From a category theory perspective, (taint_status, taint_leq) forms a
    thin category where morphisms are unique (the subset relation).
    Join and meet are categorical coproduct and product respectively.

    ============================================================================ *)

(**
 * Join two taint statuses (least upper bound).
 *
 * The join operation computes the UNION of taint kinds:
 *   - join Untainted t = t
 *   - join t Untainted = t
 *   - join (Tainted ks1) (Tainted ks2) = Tainted (ks1 union ks2)
 *
 * This models combining information from two sources. If either source
 * is tainted with a particular kind, the combination is tainted with
 * that kind.
 *
 * SECURITY INTERPRETATION: When you concatenate strings, both strings'
 * taints apply to the result. If str1 is SQLi-tainted and str2 is
 * XSS-tainted, then (str1 + str2) is both SQLi and XSS tainted.
 *
 * ALGEBRAIC PROPERTIES (all proven in BrrrTaintAnalysis.fst):
 *   - Identity: join Untainted t = t = join t Untainted
 *   - Commutativity: join t1 t2 = join t2 t1 (semantically)
 *   - Associativity: join (join t1 t2) t3 = join t1 (join t2 t3)
 *   - Idempotence: join t t = t
 *)
val taint_join : taint_status -> taint_status -> taint_status

(** ============================================================================
    TAINT JOIN PROPERTIES (Semilattice Laws)
    ============================================================================

    These lemmas establish that (taint_status, taint_join, Untainted) forms
    a JOIN SEMILATTICE with identity. All proofs are completed without
    admits in BrrrTaintAnalysis.fst.

    The properties are stated in terms of taint_contains to handle the
    fact that our list representation may have different orderings for
    semantically equal statuses. Structural versions using taint_status_eq
    are also provided in the implementation.

    These lemmas serve as the SOUNDNESS FOUNDATION for taint analysis:
    they ensure that combining tainted values behaves predictably and
    that no taint information is lost through operations.

    ============================================================================ *)

(**
 * Left identity: Untainted is the identity element for join (left).
 *
 * Combining trusted data with any data yields that data unchanged.
 * In security terms: clean data does not "dilute" tainted data.
 *
 * SMT pattern enables automatic application in proof contexts.
 *)
val taint_join_untainted_left : t:taint_status ->
    Lemma (ensures taint_join Untainted t = t)
          [SMTPat (taint_join Untainted t)]

(**
 * Right identity: Untainted is the identity element for join (right).
 *
 * Symmetric case of left identity. Together they establish Untainted
 * as the two-sided identity element.
 *)
val taint_join_untainted_right : t:taint_status ->
    Lemma (ensures taint_join t Untainted = t)
          [SMTPat (taint_join t Untainted)]

(**
 * Commutativity: join t1 t2 has the same taint kinds as join t2 t1.
 *
 * The order of combination does not matter - this is essential for
 * analyzing programs where the order of evaluation may vary.
 *
 * Stated in terms of taint_contains because the list representations
 * may differ in ordering even when the sets are identical.
 *
 * Dual SMT patterns trigger on either argument order.
 *)
val taint_join_comm_contains : t1:taint_status -> t2:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t1 t2) k = taint_contains (taint_join t2 t1) k)
          [SMTPat (taint_contains (taint_join t1 t2) k); SMTPat (taint_contains (taint_join t2 t1) k)]

(**
 * Associativity: (t1 join t2) join t3 = t1 join (t2 join t3).
 *
 * Grouping does not matter - this enables analysis of expressions
 * with multiple operands without worrying about evaluation order.
 *
 * Critical for soundness: ensures taint from all sources is captured
 * regardless of how the computation tree is structured.
 *)
val taint_join_assoc_contains : t1:taint_status -> t2:taint_status -> t3:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join (taint_join t1 t2) t3) k =
                   taint_contains (taint_join t1 (taint_join t2 t3)) k)

(**
 * Idempotence: join t t = t.
 *
 * Combining a value with itself does not change its taint status.
 * This is a key lattice property ensuring the analysis terminates.
 *
 * In fixed-point computation terms: repeated joins eventually stabilize.
 *)
val taint_join_idem_contains : t:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t t) k = taint_contains t k)
          [SMTPat (taint_contains (taint_join t t) k)]

(**
 * Meet of two taint statuses (greatest lower bound).
 *
 * The meet operation computes the INTERSECTION of taint kinds:
 *   - meet Untainted t = Untainted
 *   - meet t Untainted = Untainted
 *   - meet (Tainted ks1) (Tainted ks2) = Tainted (ks1 intersect ks2)
 *
 * This models knowing that a value must satisfy multiple constraints.
 * The result only has kinds present in BOTH operands.
 *
 * SECURITY INTERPRETATION: If you know a value came from a branch where
 * it was SQLi-tainted, and also from a branch where it was XSS-tainted,
 * and the branches are mutually exclusive, you can only be certain of
 * the intersection of taints.
 *
 * NOTE: Meet is less commonly used than join in typical taint analysis.
 * It's included for completeness of the lattice structure and for
 * specialized analyses (e.g., type-state analysis, contract checking).
 *)
val taint_meet : taint_status -> taint_status -> taint_status

(** ============================================================================
    TAINT MEET PROPERTIES (Semilattice Laws)
    ============================================================================

    These lemmas establish that (taint_status, taint_meet, TOP) forms a
    MEET SEMILATTICE. Together with the join semilattice, this gives us
    a complete BOUNDED LATTICE.

    The meet operation is dual to join: where join takes union (sound
    for "any of these taints might apply"), meet takes intersection
    (sound for "only these taints definitely apply").

    ============================================================================ *)

(**
 * Commutativity: meet t1 t2 = meet t2 t1.
 *
 * Intersection is symmetric - the order of operands does not matter.
 *)
val taint_meet_comm_contains : t1:taint_status -> t2:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t1 t2) k = taint_contains (taint_meet t2 t1) k)

(**
 * Idempotence: meet t t = t.
 *
 * Intersecting a set with itself yields that set unchanged.
 *)
val taint_meet_idem_contains : t:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t t) k = taint_contains t k)
          [SMTPat (taint_contains (taint_meet t t) k)]

(** ============================================================================
    LATTICE IDEMPOTENCE (Structural Versions)
    ============================================================================

    Structural versions of idempotence using taint_status_eq.
    These complement the taint_contains-based versions above by
    establishing that the entire status, not just individual kinds,
    is preserved.

    ============================================================================ *)

(**
 * Structural idempotence for join.
 *
 * join t t is semantically equal to t (not just element-wise).
 * Important for canonicalization and equality-based reasoning.
 *)
val taint_join_idempotent : t:taint_status ->
    Lemma (ensures taint_status_eq (taint_join t t) t = true)
          [SMTPat (taint_join t t)]

(**
 * Structural idempotence for meet.
 *
 * meet t t is semantically equal to t.
 *)
val taint_meet_idempotent : t:taint_status ->
    Lemma (ensures taint_status_eq (taint_meet t t) t = true)
          [SMTPat (taint_meet t t)]

(** ============================================================================
    ABSORPTION LAWS
    ============================================================================

    The ABSORPTION LAWS are the defining characteristic of a LATTICE
    (as opposed to just two semilattices). They state that join and meet
    interact in a specific way:

        join(t, meet(t, s)) = t    (Absorption 1)
        meet(t, join(t, s)) = t    (Absorption 2)

    INTUITION:
    - Absorption 1: If you take what t and s have in common (meet),
      then combine with everything in t (join), you just get t back.
    - Absorption 2: If you combine t with s (join), then restrict to
      what's in t (meet), you just get t back.

    These laws are proven both in terms of taint_contains (element-wise)
    and structurally using taint_status_eq.

    FROM LATTICE THEORY: The absorption laws ensure that join and meet
    are mutually definable in terms of the lattice ordering:
        a <= b iff a join b = b iff a meet b = a

    ============================================================================ *)

(**
 * Absorption law 1 (element-wise): join(t, meet(t, s)) = t.
 *
 * Combining t with (what t and s have in common) yields t.
 *)
val taint_absorption1_contains : t:taint_status -> s:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_join t (taint_meet t s)) k = taint_contains t k)

(**
 * Absorption law 2 (element-wise): meet(t, join(t, s)) = t.
 *
 * Restricting (t combined with s) to what's in t yields t.
 *)
val taint_absorption2_contains : t:taint_status -> s:taint_status -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_meet t (taint_join t s)) k = taint_contains t k)

(**
 * Absorption law 1 (structural): join(t, meet(t, s)) = t.
 *
 * Full structural equality version of absorption 1.
 *)
val taint_absorption1 : t:taint_status -> s:taint_status ->
    Lemma (ensures taint_status_eq (taint_join t (taint_meet t s)) t = true)

(**
 * Absorption law 2 (structural): meet(t, join(t, s)) = t.
 *
 * Full structural equality version of absorption 2.
 *)
val taint_absorption2 : t:taint_status -> s:taint_status ->
    Lemma (ensures taint_status_eq (taint_meet t (taint_join t s)) t = true)

(** ============================================================================
    TAINT ORDERING (PARTIAL ORDER)
    ============================================================================

    The lattice ordering taint_leq defines "less tainted than" relation.
    This ordering is fundamental to information flow analysis:

        t1 <= t2  means  "t1 is less tainted than t2"
                  means  "every taint kind in t1 is also in t2"
                  means  "t2 has at least as much information leakage as t1"

    The ordering forms a PARTIAL ORDER satisfying:
        - Reflexivity:    t <= t
        - Antisymmetry:   t1 <= t2 and t2 <= t1 implies t1 = t2
        - Transitivity:   t1 <= t2 and t2 <= t3 implies t1 <= t3

    Combined with join (least upper bound) and meet (greatest lower bound),
    this makes taint_status a BOUNDED LATTICE.

    SECURITY INTERPRETATION:
    The ordering captures the SECURITY LEVEL of data:
        - Untainted is the LEAST secure (BOTTOM) - no restrictions
        - Tainted [all] is the MOST secure (TOP) - maximum restrictions

    This may seem counterintuitive, but remember: MORE taint means MORE
    restrictions on where the data can flow. In the lattice of security
    levels, "more secure" means "fewer places it can go".

    ============================================================================ *)

(**
 * Partial order on taint status.
 *
 * t1 <= t2 iff the set of taint kinds in t1 is a subset of t2.
 *
 * Equivalently: t1 <= t2 iff for all k, taint_contains t1 k implies taint_contains t2 k
 *
 * This is the standard subset ordering on powersets, applied to our
 * representation of taint kind sets.
 *)
val taint_leq : taint_status -> taint_status -> bool

(**
 * Reflexivity: every status is less than or equal to itself.
 *
 * Every set is a subset of itself.
 *)
val taint_leq_refl : t:taint_status ->
    Lemma (ensures taint_leq t t = true)
          [SMTPat (taint_leq t t)]

(**
 * Bottom element: Untainted is the least element.
 *
 * Untainted (the empty set) is a subset of every set.
 * In security terms: trusted data can flow anywhere.
 *)
val taint_leq_bot : t:taint_status ->
    Lemma (ensures taint_leq Untainted t = true)
          [SMTPat (taint_leq Untainted t)]

(**
 * Transitivity: if t1 <= t2 and t2 <= t3, then t1 <= t3.
 *
 * Subset is transitive. Essential for reasoning about chains
 * of taint propagation through multiple operations.
 *)
val taint_leq_trans : t1:taint_status -> t2:taint_status -> t3:taint_status ->
    Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t3 = true)
          (ensures taint_leq t1 t3 = true)

(**
 * Antisymmetry: if t1 <= t2 and t2 <= t1, then t1 = t2.
 *
 * Mutual subset implies equality. Uses taint_status_eq because
 * the list representations may differ.
 *)
val taint_leq_antisym : t1:taint_status -> t2:taint_status ->
    Lemma (requires taint_leq t1 t2 = true /\ taint_leq t2 t1 = true)
          (ensures taint_status_eq t1 t2 = true)

(**
 * Join is the least upper bound.
 *
 * join t1 t2 is the smallest status >= both t1 and t2.
 *
 * This is the key property connecting join to the ordering:
 *   - t1 <= join t1 t2 (join contains all of t1)
 *   - t2 <= join t1 t2 (join contains all of t2)
 *   - For any u with t1 <= u and t2 <= u, we have join t1 t2 <= u (minimality)
 *
 * The minimality property (not stated here) ensures no taint is added
 * beyond what comes from the operands.
 *)
val taint_join_lub : t1:taint_status -> t2:taint_status ->
    Lemma (ensures taint_leq t1 (taint_join t1 t2) = true /\
                   taint_leq t2 (taint_join t1 t2) = true)

(** ============================================================================
    TAINTED VALUES (Value + Taint Pairing)
    ============================================================================

    A TAINTED VALUE pairs a runtime value with its taint status. This is
    the fundamental abstraction for taint tracking - every value in a
    taint-aware program is wrapped with its provenance information.

    TYPE STRUCTURE:

        tainted a = { value : a; taint : taint_status }

    This is essentially a PRODUCT TYPE with a semantic interpretation:
        - The 'value' field holds the actual data
        - The 'taint' field records the security metadata

    DESIGN RATIONALE:

    Using a record type (rather than a pair) provides:
        1. Named field access for clarity
        2. Type abstraction (clients can't forge tainted values)
        3. Extension points for future metadata (e.g., source location)

    The 'noeq' annotation indicates this type does not support decidable
    equality in general (since 'a' might not be an eqtype). This is
    appropriate because comparing tainted values should use taint_status_eq
    on the taint field and type-appropriate equality on the value field.

    FROM FlowDroid (Arzt 2014): "Each data value is associated with a
    taint abstraction representing all possible sources of that value."

    ============================================================================ *)

(**
 * Tainted value record type.
 *
 * Wraps a value of any type with its taint status. The taint metadata
 * propagates through operations via taint_map and taint_map2.
 *
 * The 'noeq' annotation is required because:
 *   1. The type parameter 'a' may not support equality
 *   2. Even if 'a' is eqtype, the semantics of equality for tainted
 *      values requires careful consideration (do we compare values only,
 *      or values AND taint status?)
 *)
noeq type tainted (a: Type) = {
  value : a;           (* The actual runtime value *)
  taint : taint_status (* Security metadata tracking untrusted sources *)
}

(**
 * Create an untainted value.
 *
 * Wraps a trusted value with Untainted status. Use this for:
 *   - Literal values in source code
 *   - Results from trusted computation
 *   - Data from verified sources
 *
 * Equivalent to: { value = v; taint = Untainted }
 *)
val untainted : #a:Type -> a -> tainted a

(**
 * Create a tainted value with a single taint kind.
 *
 * Marks a value as coming from an untrusted source of a specific
 * vulnerability category. This is typically used in source operations.
 *
 * Equivalent to: { value = v; taint = Tainted [k] }
 *)
val tainted_with : #a:Type -> a -> taint_kind -> tainted a

(**
 * Extract the underlying value (UNSAFE - ignores taint).
 *
 * WARNING: This function bypasses taint checking. It should only be used:
 *   - After sanitization (use sink instead for safety)
 *   - In trusted code that handles values specially
 *   - For debugging/logging (where taint doesn't matter)
 *
 * Prefer using sink or is_safe checks before extracting values.
 *)
val get_value : #a:Type -> tainted a -> a

(**
 * Get the taint status of a value.
 *
 * Useful for:
 *   - Debugging taint propagation
 *   - Custom taint policies
 *   - Logging security events
 *)
val get_taint : #a:Type -> tainted a -> taint_status

(**
 * Check if a tainted value is safe (untainted).
 *
 * Returns true iff the value has no taint kinds.
 * Equivalent to: is_untainted (get_taint t)
 *
 * Use this for conditional handling of potentially tainted data:
 *   if is_safe user_data then
 *     (* Use directly *)
 *   else
 *     (* Sanitize first *)
 *)
val is_safe : #a:Type -> tainted a -> bool

(** ============================================================================
    SOURCES, SINKS, AND SANITIZERS
    ============================================================================

    The SOURCE-SINK-SANITIZER model is the foundation of taint analysis.
    This model was formalized by Livshits & Lam (2005) and has become
    standard in both academic and industrial security tools.

    +-----------+        +------------+        +--------+
    |  SOURCE   | -----> | PROPAGATE  | -----> |  SINK  |
    | (taint)   |        | (preserve) |        | (check)|
    +-----------+        +------------+        +--------+
                               |
                               v
                        +------------+
                        | SANITIZER  |
                        | (cleanse)  |
                        +------------+

    SOURCES: Entry points for untrusted data
      - User input forms
      - HTTP request parameters
      - Database query results
      - File contents
      - Environment variables
      - Network sockets

    SINKS: Security-sensitive operations
      - SQL query execution (SQLi)
      - HTML output (XSS)
      - Shell command execution (CMDi)
      - File system operations (PathTraversal)
      - HTTP requests (SSRF)

    SANITIZERS: Validation/encoding functions
      - SQL parameterization or escaping
      - HTML entity encoding
      - Shell argument quoting
      - Path canonicalization
      - URL allowlist validation

    A VULNERABILITY exists when tainted data reaches a sink without
    passing through an appropriate sanitizer for that taint kind.

    KEY INSIGHT: Different sinks require different sanitizers!
    SQL escaping does NOT protect against XSS, and vice versa.
    This is why we track taint kinds separately.

    ============================================================================ *)

(**
 * Mark a value as coming from an untrusted source.
 *
 * This is the INTRODUCTION rule for taint. Call this at program points
 * where untrusted data enters the system.
 *
 * COMMON SOURCE EXAMPLES:
 *   source TaintSQLi (read_query_param "name")
 *   source TaintXSS (read_cookie "session")
 *   source TaintCMDi (read_env_var "USER_INPUT")
 *   source TaintPathTraversal (read_filename_param ())
 *   source TaintSSRF (read_url_param "target")
 *
 * Returns a tainted value with the specified kind.
 * The raw value v is wrapped: { value = v; taint = Tainted [k] }
 *)
val source : #a:Type -> taint_kind -> a -> tainted a

(**
 * Attempt to use a tainted value at a security-sensitive sink.
 *
 * This is the ELIMINATION rule for taint. It checks if the value
 * is safe to use for a particular vulnerability category.
 *
 * BEHAVIOR:
 *   - Returns Some v if the value does NOT contain taint kind k
 *   - Returns None if the value IS tainted with kind k
 *
 * COMMON SINK EXAMPLES:
 *   sink TaintSQLi query        (* Check before SQL execution *)
 *   sink TaintXSS html_fragment (* Check before HTML output *)
 *   sink TaintCMDi command      (* Check before shell exec *)
 *
 * The sink check is CONSERVATIVE (sound): if data MIGHT be tainted
 * with kind k, sink returns None. This prevents false negatives
 * (undetected vulnerabilities) at the cost of potential false positives.
 *
 * IMPORTANT: A value tainted with TaintXSS can successfully pass a
 * TaintSQLi sink! Each sink only checks for its relevant taint kind.
 * Use sink_with_policy for multi-kind checks.
 *)
val sink : #a:Type -> taint_kind -> tainted a -> option a

(**
 * Sanitize a tainted value, removing a specific taint kind.
 *
 * This is the CLEANSING rule for taint. Proper sanitization is the
 * ONLY way to remove taint from a value.
 *
 * PARAMETERS:
 *   - k: The taint kind to remove
 *   - t: The tainted value to sanitize
 *   - sanitizer: A function that actually transforms the value
 *
 * BEHAVIOR:
 *   1. Applies the sanitizer function to the underlying value
 *   2. Removes kind k from the taint status
 *   3. Preserves all other taint kinds
 *
 * IMPORTANT: The sanitizer function should perform ACTUAL sanitization:
 *   - For SQLi: Escape quotes, use parameterized queries
 *   - For XSS: HTML-encode special characters
 *   - For CMDi: Quote shell arguments, use allowlist
 *   - For PathTraversal: Canonicalize and validate against allowlist
 *   - For SSRF: Validate URL against allowlist
 *
 * Using the identity function (fun x -> x) as sanitizer is a BUG -
 * it removes taint without actually protecting against the vulnerability!
 *
 * SOUNDNESS THEOREM (proven in BrrrTaintAnalysis.fst):
 *   After sanitization, the result does not contain the sanitized kind:
 *   taint_contains (sanitize k t f).taint k = false
 *)
val sanitize : #a:Type -> taint_kind -> tainted a -> (a -> a) -> tainted a

(** ============================================================================
    SOUNDNESS THEOREMS
    ============================================================================

    These theorems establish the CORRECTNESS of the taint analysis.
    All proofs are completed WITHOUT ADMITS in BrrrTaintAnalysis.fst.

    SOUNDNESS means: If the analysis says it's safe, it truly is safe.
    In formal terms: No false negatives (undetected vulnerabilities).

    The key soundness properties are:
    1. Sanitization actually removes the specified taint kind
    2. Sanitization does not affect other taint kinds
    3. Sink correctly rejects tainted data
    4. The sanitize-then-sink pattern is guaranteed to succeed

    These properties ensure that following the source-sanitize-sink
    pattern will prevent the corresponding vulnerability class.

    ============================================================================ *)

(**
 * FUNDAMENTAL SANITIZATION THEOREM: sanitize removes the specified taint.
 *
 * After sanitizing for kind k, the result does NOT contain kind k.
 * This is the core correctness property of sanitization.
 *
 * PROOF SKETCH (from BrrrTaintAnalysis.fst):
 *   sanitize removes k from the taint kind list using taint_kind_remove.
 *   The helper lemma taint_kind_remove_not_mem proves that after removal,
 *   the element is not in the resulting list.
 *
 * SECURITY IMPLICATION: Calling sanitize TaintSQLi on user input
 * guarantees the result is safe for SQL sinks, assuming the sanitizer
 * function correctly escapes/validates the input.
 *)
val sanitize_removes_taint : #a:Type -> k:taint_kind -> t:tainted a -> f:(a -> a) ->
    Lemma (ensures taint_contains (sanitize k t f).taint k = false)

(**
 * TAINT PRESERVATION THEOREM: sanitize only removes the specified kind.
 *
 * Sanitizing for kind k does NOT affect other taint kinds k'.
 * If the value was tainted with k' before, it remains tainted with k'.
 *
 * PROOF SKETCH: taint_kind_remove only removes matching elements.
 * The helper lemma taint_kind_remove_preserves proves non-matching
 * elements are preserved.
 *
 * SECURITY IMPLICATION: SQL-sanitizing XSS-tainted data still leaves
 * the XSS taint in place. You must sanitize for EACH vulnerability
 * category separately.
 *
 * This prevents a common bug: assuming one sanitizer protects against
 * all vulnerabilities.
 *)
val sanitize_preserves_other_taints : #a:Type -> k:taint_kind -> k':taint_kind ->
    t:tainted a -> f:(a -> a) ->
    Lemma (requires taint_kind_eq k k' = false /\ taint_contains t.taint k' = true)
          (ensures taint_contains (sanitize k t f).taint k' = true)

(**
 * SINK SOUNDNESS THEOREM: sink correctly classifies values.
 *
 * sink k t returns Some iff t is NOT tainted with kind k.
 * This is an IFF (biconditional), meaning:
 *   - Some? (sink k t) = true  IMPLIES taint_contains t.taint k = false
 *   - taint_contains t.taint k = false IMPLIES Some? (sink k t) = true
 *
 * The first direction ensures NO FALSE NEGATIVES: if sink accepts,
 * the data is truly safe for that vulnerability category.
 *
 * The second direction ensures NO SPURIOUS REJECTIONS: if data is
 * actually safe, sink will accept it.
 *)
val sink_soundness : #a:Type -> k:taint_kind -> t:tainted a ->
    Lemma (ensures Some? (sink k t) <==> taint_contains t.taint k = false)

(**
 * SANITIZE-THEN-SINK THEOREM: the correct usage pattern always works.
 *
 * If you sanitize data for kind k, then use it at a sink for kind k,
 * the sink check will ALWAYS succeed.
 *
 * This theorem encapsulates the INTENDED USAGE PATTERN:
 *   let user_input = source TaintSQLi (read_input ()) in
 *   let safe_input = sanitize TaintSQLi user_input escape_sql in
 *   match sink TaintSQLi safe_input with
 *   | Some v -> execute_sql v    (* This branch is ALWAYS taken *)
 *   | None -> (* Dead code - sanitization guarantees Some *)
 *
 * PROOF: Direct composition of sanitize_removes_taint and sink_soundness.
 *)
val sanitize_then_sink : #a:Type -> k:taint_kind -> t:tainted a -> f:(a -> a) ->
    Lemma (ensures Some? (sink k (sanitize k t f)))

(** ============================================================================
    TAINT PROPAGATION
    ============================================================================

    Taint propagation tracks how taint flows through computations.
    When tainted data is used in an operation, the result inherits taint.

    PROPAGATION RULES (from brrr_lang_spec_v0.4.tex Section IX-B):

    1. UNARY OPERATIONS: Result has same taint as operand
       f(tainted_value) => tainted_result

    2. BINARY OPERATIONS: Result has union of operand taints
       tainted1 op tainted2 => Tainted(kinds1 UNION kinds2)

    3. FUNCTION CALLS: Result tainted if any argument is tainted
       This is CONSERVATIVE - even if the function ignores an argument,
       we still propagate its taint (sound over-approximation).

    4. CONTROL FLOW (implicit flows):
       Assignments in tainted branches are tainted (see pc_taint in .fst)

    The propagation functions taint_map and taint_map2 implement rules
    1 and 2 respectively. They are the CORE of taint tracking - all
    operations on tainted values should use these combinators.

    DESIGN CHOICE: We use EXPLICIT propagation via taint_map/taint_map2
    rather than implicit tracking. This makes the taint flow visible
    in the code and enables static verification of taint properties.

    ============================================================================ *)

(**
 * Apply a unary function to a tainted value, propagating taint.
 *
 * The result has the SAME taint status as the input. This models
 * operations that transform a value without adding external data:
 *   - String transformations (toLowerCase, trim, etc.)
 *   - Numeric operations (negate, abs, etc.)
 *   - Type conversions
 *   - Accessor operations
 *
 * SOUNDNESS: If the input might be malicious, so might the output.
 * There's no operation on a single string that makes SQLi-tainted
 * data safe for SQL queries (except actual sanitization).
 *
 * Example:
 *   let user_input = source TaintSQLi (read_input ()) in
 *   let upper = taint_map String.uppercase user_input in
 *   (* upper is still TaintSQLi-tainted *)
 *)
val taint_map : #a:Type -> #b:Type -> (a -> b) -> tainted a -> tainted b

(**
 * Apply a binary function to two tainted values, joining taints.
 *
 * The result is tainted with the UNION of both inputs' taint kinds.
 * This models operations that combine data from multiple sources:
 *   - String concatenation
 *   - Arithmetic operations
 *   - Collection operations (append, merge)
 *   - Formatting operations
 *
 * SOUNDNESS: If either input might be malicious, the combination
 * might be malicious in the same way. Concatenating safe data with
 * SQLi-tainted data produces SQLi-tainted data.
 *
 * Example:
 *   let prefix = untainted "SELECT * FROM users WHERE name = '" in
 *   let user_name = source TaintSQLi (read_input ()) in
 *   let query = taint_map2 (^) prefix user_name in
 *   (* query is TaintSQLi-tainted due to user_name *)
 *)
val taint_map2 : #a:Type -> #b:Type -> #c:Type -> (a -> b -> c) ->
    tainted a -> tainted b -> tainted c

(** ============================================================================
    PROPAGATION PROPERTIES
    ============================================================================

    These lemmas characterize the precise behavior of taint propagation.
    They enable reasoning about what taint kinds a value has after
    passing through taint_map or taint_map2.

    ============================================================================ *)

(**
 * taint_map preserves taint status exactly.
 *
 * The output has EXACTLY the same taint status as the input.
 * No taint is added or removed by applying a function.
 *)
val taint_map_preserves_taint : #a:Type -> #b:Type -> f:(a -> b) -> t:tainted a ->
    Lemma (ensures (taint_map f t).taint = t.taint)

(**
 * taint_map2 combines taints as union.
 *
 * A taint kind is in the output iff it's in either input.
 * This is the formal statement of the UNION propagation rule.
 *)
val taint_map2_combines_taints : #a:Type -> #b:Type -> #c:Type -> f:(a -> b -> c) ->
    t1:tainted a -> t2:tainted b -> k:taint_kind ->
    Lemma (ensures taint_contains (taint_map2 f t1 t2).taint k =
                   (taint_contains t1.taint k || taint_contains t2.taint k))

(** ============================================================================
    MONADIC OPERATIONS
    ============================================================================

    Tainted values form a MONAD, enabling compositional taint tracking.
    The monadic structure allows chaining taint-aware operations in a
    natural style while automatically propagating taint information.

    MONAD STRUCTURE:

        pure  : a -> tainted a           (lift untainted value)
        bind  : tainted a -> (a -> tainted b) -> tainted b  (sequence)

    MONAD LAWS (proven in BrrrTaintAnalysis.fst):

        Left identity:   bind (pure v) f  =  f v
        Right identity:  bind t pure      =  t
        Associativity:   bind (bind t f) g  =  bind t (fun x -> bind (f x) g)

    Note: Equality here is semantic (via taint_status_eq), not structural,
    due to potential differences in list ordering.

    USAGE PATTERN (pseudo-F# syntax):

        let! x = get_user_input ()     (* x is tainted *)
        let! y = process x             (* y inherits x's taint + any from process *)
        let! z = format_output y       (* z inherits y's taint + any from format *)
        return z                       (* final result has accumulated taint *)

    This monadic style is cleaner than explicit taint_map/taint_map2 for
    complex computations with multiple intermediate values.

    TAINT ACCUMULATION: Unlike the Option or Error monads that short-circuit
    on failure, the taint monad ACCUMULATES information. Each bind joins the
    taint from the input with the taint produced by the continuation.

    ============================================================================ *)

(**
 * Monadic pure: lift an untainted value into the taint monad.
 *
 * Creates a tainted value with Untainted status.
 * This is the UNIT of the monad.
 *
 * Equivalent to: untainted v
 *)
val taint_pure : #a:Type -> a -> tainted a

(**
 * Monadic bind: sequence taint-tracking computations.
 *
 * Extracts the value from t, applies f to get a new tainted value,
 * and joins the taints from both.
 *
 * taint_bind t f =
 *   let result = f t.value in
 *   { value = result.value;
 *     taint = taint_join t.taint result.taint }
 *
 * SOUNDNESS: The result's taint includes:
 *   1. Any taint in the input t
 *   2. Any taint introduced by the continuation f
 *
 * This ensures no taint is lost when chaining operations.
 *
 * COMPARISON WITH OTHER MONADS:
 *   - Option/Maybe: bind short-circuits on None
 *   - Error/Result: bind short-circuits on Error
 *   - Taint: bind ALWAYS continues, accumulating taint
 *
 * The non-short-circuiting behavior is essential for soundness:
 * we must track all possible sources of taint, even if some paths
 * through the computation are "safer" than others.
 *)
val taint_bind : #a:Type -> #b:Type -> tainted a -> (a -> tainted b) -> tainted b
