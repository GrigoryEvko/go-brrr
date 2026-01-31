(**
 * =============================================================================
 * BrrrLang.Core.SecurityTypes - Interface
 * =============================================================================
 *
 * Public interface for the Unified Security Type System of Brrr-Lang.
 *
 * This module provides the formal foundation for information flow control (IFC)
 * and taint analysis, implementing a product lattice combining:
 *
 *   - Confidentiality dimension (prevents data leaks)
 *   - Integrity dimension (tracks trust/taint status)
 *   - Fine-grained taint kind tracking (vulnerability classification)
 *
 * =============================================================================
 * THEORETICAL FOUNDATION
 * =============================================================================
 *
 * This module is based on foundational work in information flow security:
 *
 *   [1] Denning, D.E. (1976). "A Lattice Model of Secure Information Flow."
 *       Communications of the ACM, 19(5):236-243.
 *       - Introduced security lattices for IFC
 *       - Defines the "no read up, no write down" property
 *       - Proves that lattice-based IFC prevents information leaks
 *
 *   [2] Denning, D.E. and Denning, P.J. (1977). "Certification of Programs
 *       for Secure Information Flow." Communications of the ACM, 20(7):504-513.
 *       - Extended to certification of programs
 *       - PC (program counter) label tracking for implicit flows
 *
 *   [3] Myers, A.C. (1999). "JFlow: Practical Mostly-Static Information
 *       Flow Control." POPL 1999.
 *       - Decentralized label model (principals and policies)
 *       - Practical type system for Java
 *
 *   [4] Livshits, V.B. and Lam, M.S. (2005). "Finding Security Vulnerabilities
 *       in Java Applications with Static Analysis." USENIX Security 2005.
 *       - Taint analysis for vulnerability detection
 *       - Source-sink-sanitizer framework
 *
 * =============================================================================
 * LATTICE STRUCTURE
 * =============================================================================
 *
 * The security label forms a PRODUCT LATTICE of three components:
 *
 *                    sec_label = Confidentiality x Integrity x TaintSet
 *
 * CONFIDENTIALITY LATTICE (Two-Point):
 * ------------------------------------
 *
 *                          CSecret
 *                             |
 *                          CPublic
 *
 *   - CPublic: Data that anyone can read (non-sensitive)
 *   - CSecret: Data with restricted access (sensitive)
 *   - Ordering: CPublic <= CSecret (public can flow to secret)
 *   - Join: CPublic join CSecret = CSecret
 *   - Meet: CPublic meet CSecret = CPublic
 *
 *
 * INTEGRITY LATTICE (Two-Point, Inverted for Taint):
 * --------------------------------------------------
 *
 *                         IUntrusted
 *                             |
 *                          ITrusted
 *
 *   - ITrusted: Data from trusted source (sanitized, validated)
 *   - IUntrusted: Data from untrusted source (tainted, user input)
 *   - Ordering: ITrusted <= IUntrusted (trusted can "flow to" untrusted)
 *   - Rationale: Tainted data "pollutes" anything it touches
 *   - Join: ITrusted join IUntrusted = IUntrusted
 *   - Meet: ITrusted meet IUntrusted = ITrusted
 *
 *   NOTE: The integrity ordering is INVERTED from traditional IFC because
 *   we track taint propagation (not integrity levels). Untrusted/tainted
 *   data is "higher" because it represents a larger attack surface.
 *
 *
 * COMBINED PRODUCT LATTICE (Four-Point Diamond):
 * ----------------------------------------------
 *
 *              (CSecret, IUntrusted)  <-- Most restrictive (TOP)
 *                    /         \
 *                   /           \
 *     (CSecret, ITrusted)    (CPublic, IUntrusted)
 *                   \           /
 *                    \         /
 *              (CPublic, ITrusted)  <-- Least restrictive (BOT)
 *
 *   This forms a complete lattice with proper join/meet operations.
 *   The TaintSet dimension adds further granularity within IUntrusted.
 *
 *
 * TAINT SET DIMENSION:
 * --------------------
 *
 *   When integrity = IUntrusted, the taints field tracks WHICH vulnerability
 *   categories the data is susceptible to. This enables:
 *
 *   - Fine-grained taint tracking (SQL injection separate from XSS)
 *   - Targeted sanitization (only remove specific taints)
 *   - Precise sink checking (database rejects SQLi, not XSS)
 *
 *   The taint set forms a lattice under subset ordering:
 *     - Bot: {} (empty set, no taints)
 *     - Top: {all taint kinds}
 *     - Join: set union (accumulates taints)
 *     - Meet: set intersection
 *
 * =============================================================================
 * INFORMATION FLOW RULES
 * =============================================================================
 *
 * The fundamental IFC rule is: data can only flow from LOW to HIGH.
 *
 *   l1 <= l2  means "data at label l1 can safely flow to label l2"
 *
 * This is checked by sec_label_leq, which requires:
 *   1. Confidentiality: c1 <= c2 (can't leak secrets)
 *   2. Integrity: i1 <= i2 (can't forge trust)
 *   3. Taints: taints1 subset of taints2 (can't lose taint tracking)
 *
 * Example flows:
 *   - (Public, Trusted, {}) -> (Secret, Trusted, {})      OK (adding secrecy)
 *   - (Public, Untrusted, {SQLi}) -> (Public, Untrusted, {SQLi, XSS})  OK
 *   - (Secret, Trusted, {}) -> (Public, Trusted, {})      REJECTED (leak!)
 *   - (Public, Untrusted, {SQLi}) -> (Public, Trusted, {})  REJECTED (taint!)
 *
 * =============================================================================
 * THE 13 TAINT KINDS
 * =============================================================================
 *
 * This module defines 13 taint kinds covering common vulnerability classes:
 *
 *   1.  TkSQLi          - SQL Injection
 *   2.  TkXSS           - Cross-Site Scripting
 *   3.  TkCMDi          - Command/Shell Injection
 *   4.  TkPathTraversal - Path Traversal (directory traversal)
 *   5.  TkSSRF          - Server-Side Request Forgery
 *   6.  TkLDAPi         - LDAP Injection
 *   7.  TkXMLi          - XML Injection (including XXE)
 *   8.  TkHeaderi       - HTTP Header Injection (CRLF injection)
 *   9.  TkLogi          - Log Injection (log forging)
 *   10. TkTemplatei     - Template Injection (SSTI)
 *   11. TkDeserial      - Insecure Deserialization
 *   12. TkRedirect      - Open Redirect
 *   13. TkCustom        - User-defined taint kind (extensibility)
 *
 * Each taint kind requires a SPECIFIC sanitizer. For example:
 *   - TkSQLi requires SQL escaping or parameterized queries
 *   - TkXSS requires HTML entity encoding
 *   - TkCMDi requires shell escaping or allow-listing
 *
 * =============================================================================
 * DESIGN PRINCIPLES
 * =============================================================================
 *
 * 1. SECURITY LABELS ARE PART OF THE TYPE SYSTEM
 *    Unlike wrapper types (tainted<T>), security is intrinsic to types.
 *    This enables subtyping and variance tracking through the type system.
 *
 * 2. SANITIZATION AND ENDORSEMENT ARE SEPARATE
 *    - sanitize_label: Removes specific taints (SQL escaping)
 *    - endorse_label: Promotes IUntrusted to ITrusted (explicit decision)
 *    Combining these operations automatically would be a security antipattern.
 *
 * 3. PC LABEL TRACKS IMPLICIT FLOWS
 *    The program counter label prevents implicit flows through control flow:
 *      if (secret) { x = 1; } else { x = 0; }
 *    Here x depends on secret even though secret isn't directly assigned.
 *
 * 4. SOURCES, SINKS, AND SANITIZERS ARE TYPE ANNOTATIONS
 *    Functions can be annotated with security roles:
 *    - Source: Returns tainted data (e.g., read_user_input)
 *    - Sink: Requires untainted data (e.g., execute_sql)
 *    - Sanitizer: Removes specific taints (e.g., escape_html)
 *
 * =============================================================================
 * USAGE PATTERNS
 * =============================================================================
 *
 * Creating security-typed values:
 *
 *   (* Untainted, public value - safest *)
 *   let safe_val = untainted_type TString
 *
 *   (* User input - tainted with multiple kinds *)
 *   let user_input = sec_public_untrusted [TkSQLi; TkXSS; TkCMDi]
 *
 *   (* Secret configuration - trusted but confidential *)
 *   let api_key = secret_type TString
 *
 * Checking flows:
 *
 *   (* Can user input flow to database? *)
 *   let ok = sec_label_leq user_input.label (io_sink_label IODatabase)
 *   (* Returns false - must sanitize first! *)
 *
 * Sanitizing data:
 *
 *   (* Remove SQL injection taint *)
 *   let sql_safe = sanitize_sec_type [TkSQLi] user_input
 *
 *   (* Explicitly endorse if all taints removed *)
 *   match endorse_sec_type fully_sanitized with
 *   | Some trusted -> (* use trusted value *)
 *   | None -> (* taints remain, cannot endorse *)
 *
 * =============================================================================
 * REFERENCES
 * =============================================================================
 *
 * For implementation details, see BrrrSecurityTypes.fst.
 *
 * For specification context, see:
 *   - brrr_lang_spec_v0.4.tex, Part IX (Information Flow)
 *   - brrr_lang_spec_v0.4.tex, Chapter "Taint Analysis"
 *   - SPECIFICATION_ERRATA.md for known corrections
 *
 * For F* patterns, see:
 *   - HACL*/Lib.IntTypes for secrecy_level patterns
 *   - EverParse for parser security annotations
 *
 * =============================================================================
 *)
module BrrrSecurityTypes

open FStar.List.Tot
open BrrrPrimitives
open BrrrModes
open BrrrEffects
open BrrrTypes

(** Z3 solver options - tuned for lattice proofs.
    Low fuel/ifuel sufficient for finite lattice case analysis. *)
#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


(** ============================================================================
    SECTION 1: TAINT KINDS
    ============================================================================

    Taint kinds categorize vulnerability classes. Each kind represents a
    distinct attack vector requiring specific sanitization.

    The taxonomy follows OWASP Top 10 and CWE (Common Weakness Enumeration)
    vulnerability classifications. See:
      - OWASP Top 10: https://owasp.org/www-project-top-ten/
      - CWE: https://cwe.mitre.org/

    IMPORTANT: A value may be tainted with MULTIPLE kinds simultaneously.
    For example, user input from a web form might carry:
      [TkSQLi; TkXSS; TkCMDi; TkPathTraversal]

    Each kind must be sanitized INDEPENDENTLY before the corresponding sink.
    ============================================================================ *)

(**
 * Taint kind enumeration - 13 vulnerability categories.
 *
 * Each constructor represents a distinct attack vector:
 *
 * @TkSQLi          SQL Injection (CWE-89)
 *                  Attack: Malicious SQL in user input
 *                  Sanitizer: Parameterized queries, SQL escaping
 *                  Sink: Database queries
 *
 * @TkXSS           Cross-Site Scripting (CWE-79)
 *                  Attack: Script injection in web pages
 *                  Sanitizer: HTML entity encoding, CSP
 *                  Sink: HTML output, DOM manipulation
 *
 * @TkCMDi          Command Injection (CWE-78)
 *                  Attack: Shell command injection
 *                  Sanitizer: Shell escaping, allow-listing
 *                  Sink: System(), exec(), shell commands
 *
 * @TkPathTraversal Path Traversal (CWE-22)
 *                  Attack: "../" sequences to access arbitrary files
 *                  Sanitizer: Path canonicalization, chroot
 *                  Sink: File system operations
 *
 * @TkSSRF          Server-Side Request Forgery (CWE-918)
 *                  Attack: Force server to make arbitrary requests
 *                  Sanitizer: URL validation, allow-listing
 *                  Sink: HTTP clients, URL fetchers
 *
 * @TkLDAPi         LDAP Injection (CWE-90)
 *                  Attack: Malicious LDAP queries
 *                  Sanitizer: LDAP escaping
 *                  Sink: LDAP queries
 *
 * @TkXMLi          XML Injection (CWE-91) including XXE (CWE-611)
 *                  Attack: Malicious XML, external entity expansion
 *                  Sanitizer: XML escaping, disable external entities
 *                  Sink: XML parsers
 *
 * @TkHeaderi       HTTP Header Injection (CWE-113)
 *                  Attack: CRLF injection in headers
 *                  Sanitizer: Header value encoding
 *                  Sink: HTTP response headers
 *
 * @TkLogi          Log Injection (CWE-117)
 *                  Attack: Forge log entries, inject control chars
 *                  Sanitizer: Log encoding, newline stripping
 *                  Sink: Logging functions
 *
 * @TkTemplatei     Template Injection (CWE-1336)
 *                  Attack: Server-side template injection (SSTI)
 *                  Sanitizer: Template escaping, sandboxing
 *                  Sink: Template engines
 *
 * @TkDeserial      Insecure Deserialization (CWE-502)
 *                  Attack: Malicious serialized objects
 *                  Sanitizer: Type validation, signing
 *                  Sink: Deserialization functions
 *
 * @TkRedirect      Open Redirect (CWE-601)
 *                  Attack: Redirect to attacker-controlled URL
 *                  Sanitizer: URL validation, allow-listing
 *                  Sink: Redirect functions
 *
 * @TkCustom        User-defined taint kind (extensibility point)
 *                  Parameterized by string identifier for custom taints
 *)
type taint_kind =
  | TkSQLi          : taint_kind
  | TkXSS           : taint_kind
  | TkCMDi          : taint_kind
  | TkPathTraversal : taint_kind
  | TkSSRF          : taint_kind
  | TkLDAPi         : taint_kind
  | TkXMLi          : taint_kind
  | TkHeaderi       : taint_kind
  | TkLogi          : taint_kind
  | TkTemplatei     : taint_kind
  | TkDeserial      : taint_kind
  | TkRedirect      : taint_kind
  | TkCustom        : string -> taint_kind

(**
 * Decidable equality on taint kinds.
 * Required for set membership operations on taint_set.
 * Note: TkCustom comparison is string-based.
 *)
val taint_kind_eq : k1:taint_kind -> k2:taint_kind -> bool

(**
 * Taint set: a collection of taint kinds affecting a value.
 *
 * Implemented as a list for simplicity; operations treat it as a set:
 *   - Membership: taint_in_set
 *   - Subset: taint_set_subset
 *   - Union (join): taint_set_union
 *   - Intersection (meet): taint_set_intersect
 *
 * Invariant: Elements should be unique (not enforced statically).
 *
 * Example: User input tainted with multiple kinds:
 *   [TkSQLi; TkXSS; TkCMDi; TkPathTraversal]
 *)
type taint_set = list taint_kind


(** ============================================================================
    SECTION 2: CONFIDENTIALITY AND INTEGRITY DIMENSIONS
    ============================================================================

    These form the two primary dimensions of the security label lattice.

    CONFIDENTIALITY tracks what CAN be read:
      - CPublic: Anyone can read (non-sensitive)
      - CSecret: Only authorized principals can read

    INTEGRITY tracks what CAN be trusted:
      - ITrusted: Data from trusted source (validated, sanitized)
      - IUntrusted: Data from untrusted source (user input, network)

    The product of these forms a FOUR-POINT DIAMOND lattice.
    ============================================================================ *)

(**
 * Confidentiality dimension of the security lattice.
 *
 * Prevents unauthorized data disclosure (information leaks).
 *
 * @CPublic  Data that can be freely disclosed (non-sensitive).
 *           Examples: Public web content, documentation, public APIs
 *
 * @CSecret  Data requiring confidentiality (sensitive).
 *           Examples: API keys, passwords, PII, internal data
 *
 * Ordering: CPublic < CSecret
 * Semantics: Public data can flow to secret context, but not vice versa.
 *)
type confidentiality =
  | CPublic : confidentiality
  | CSecret : confidentiality

(**
 * Integrity dimension of the security lattice.
 *
 * Tracks trust level and taint status of data.
 *
 * @IUntrusted  Data from untrusted source (TAINTED).
 *              Examples: User input, network data, file contents
 *              Must be sanitized before use in security-sensitive operations.
 *
 * @ITrusted    Data from trusted source (CLEAN).
 *              Examples: Constants, validated data, sanitized data
 *              Safe to use in security-sensitive operations.
 *
 * Ordering: ITrusted < IUntrusted
 *
 * NOTE: This ordering is INVERTED from traditional integrity labels!
 * In IFC, high integrity means "more trusted". But for taint tracking,
 * we want tainted data to be "higher" so taint propagates (joins up).
 *
 * Semantics: Trusted data can flow to untrusted context (gets tainted),
 * but untrusted cannot flow to trusted without explicit endorsement.
 *)
type integrity =
  | IUntrusted : integrity
  | ITrusted   : integrity


(** ============================================================================
    SECTION 3: SECURITY LABELS
    ============================================================================

    A security label is the PRODUCT of:
      - Confidentiality level
      - Integrity level
      - Set of taint kinds (when integrity = IUntrusted)

    This forms a complete lattice with computable join/meet operations.
    ============================================================================ *)

(**
 * Complete security label - the core type for information flow control.
 *
 * Combines all three dimensions of security tracking:
 *
 * @field confidentiality  Secrecy level (CPublic or CSecret)
 * @field integrity        Trust level (ITrusted or IUntrusted)
 * @field taints           Vulnerability categories (when untrusted)
 *
 * Well-formedness invariant (see sec_label_wf):
 *   integrity = ITrusted ==> taints = []
 *
 * Trusted data should not have taints; if it has taints, it's not truly trusted.
 *
 * Record type (noeq) because:
 *   - Contains list (taint_set) which doesn't have decidable equality
 *   - Custom set-based equivalence used for proofs (sec_label_equiv)
 *)
noeq type sec_label = {
  confidentiality : confidentiality;
  integrity       : integrity;
  taints          : taint_set;
}


(** ============================================================================
    SECTION 4: SECURITY LABEL CONSTRUCTORS
    ============================================================================

    Convenience constructors for common security label configurations.
    These define the standard points in the product lattice.
    ============================================================================ *)

(**
 * Bottom element: Public, trusted, no taints.
 * This is the SAFEST label - data can flow anywhere.
 * Example: Compile-time constants, literal strings.
 *)
val sec_public_trusted : sec_label

(**
 * Secret but trusted: Confidential but clean data.
 * Example: API keys, passwords stored in config.
 *)
val sec_secret_trusted : sec_label

(**
 * Public but tainted: Non-confidential but untrusted data.
 * Example: User input (not secret, but can't trust it).
 * @param ks  The set of taint kinds this data carries.
 *)
val sec_public_untrusted : taint_set -> sec_label

(**
 * Create a label tainted with a single kind.
 * Convenience for sec_public_untrusted [k].
 * @param k  The single taint kind.
 *)
val sec_tainted : taint_kind -> sec_label

(**
 * Lattice bottom: sec_public_trusted.
 * Most permissive - data can flow to any other label.
 *)
val sec_bot : sec_label

(**
 * Lattice top: Secret, untrusted, with common taints.
 * Most restrictive - nothing can flow to this except itself.
 *)
val sec_top : sec_label


(** ============================================================================
    SECTION 5: SECURITY LABEL ORDERING
    ============================================================================

    The ordering relation l1 <= l2 defines when data can flow from l1 to l2.
    This is the core of information flow control.

    FLOW RULE: l1 <= l2 means "data at l1 can safely flow to l2"

    The ordering is a PRODUCT ORDER on the three components:
      l1 <= l2  iff  c1 <= c2 AND i1 <= i2 AND taints1 subset taints2
    ============================================================================ *)

(**
 * Confidentiality ordering: Public < Secret.
 *
 * CPublic <= CPublic  (reflexive)
 * CPublic <= CSecret  (public can flow to secret)
 * CSecret <= CSecret  (reflexive)
 * CSecret <= CPublic  FALSE (cannot leak secrets!)
 *
 * This prevents information leaks: secret data cannot flow to
 * public contexts where it might be observed by unauthorized parties.
 *)
val conf_leq : c1:confidentiality -> c2:confidentiality -> bool

(**
 * Integrity ordering: Trusted < Untrusted (for taint flow).
 *
 * ITrusted <= ITrusted      (reflexive)
 * ITrusted <= IUntrusted    (trusted can become tainted)
 * IUntrusted <= IUntrusted  (reflexive)
 * IUntrusted <= ITrusted    FALSE (cannot forge trust!)
 *
 * This ensures taint propagation: once data is tainted, it cannot
 * become trusted without explicit endorsement after sanitization.
 *)
val integ_leq : i1:integrity -> i2:integrity -> bool

(**
 * Check if a taint kind is in the taint set.
 * Uses taint_kind_eq for comparison.
 * O(n) where n is set size.
 *)
val taint_in_set : k:taint_kind -> ks:taint_set -> bool

(**
 * Check if one taint set is a subset of another.
 * ks1 subset ks2 iff every element of ks1 is in ks2.
 * O(n*m) where n = |ks1|, m = |ks2|.
 *)
val taint_set_subset : ks1:taint_set -> ks2:taint_set -> bool

(**
 * Security label ordering (product order).
 *
 * l1 <= l2 iff all three components satisfy their orderings:
 *   - conf_leq l1.confidentiality l2.confidentiality
 *   - integ_leq l1.integrity l2.integrity
 *   - taint_set_subset l1.taints l2.taints
 *
 * This is the FUNDAMENTAL flow check: data at l1 can flow to l2
 * only if l1 <= l2.
 *
 * Properties (proven in implementation):
 *   - Reflexive: l <= l
 *   - Transitive: l1 <= l2 /\ l2 <= l3 ==> l1 <= l3
 *   - Antisymmetric (up to set equiv): l1 <= l2 /\ l2 <= l1 ==> l1 =set= l2
 *)
val sec_label_leq : l1:sec_label -> l2:sec_label -> bool


(** ============================================================================
    SECTION 6: SECURITY LABEL LATTICE OPERATIONS
    ============================================================================

    Join and meet operations for combining security labels.

    JOIN (least upper bound): Used when data from multiple sources combines.
    Example: result of (secret + public) has label (secret join public) = secret.

    MEET (greatest lower bound): Used for permission checking.
    Example: Intersection of allowed labels.
    ============================================================================ *)

(**
 * Confidentiality join (least upper bound).
 * CPublic join CPublic = CPublic
 * CPublic join CSecret = CSecret
 * CSecret join CPublic = CSecret
 * CSecret join CSecret = CSecret
 *)
val conf_join : c1:confidentiality -> c2:confidentiality -> confidentiality

(**
 * Confidentiality meet (greatest lower bound).
 * CPublic meet CPublic = CPublic
 * CPublic meet CSecret = CPublic
 * CSecret meet CPublic = CPublic
 * CSecret meet CSecret = CSecret
 *)
val conf_meet : c1:confidentiality -> c2:confidentiality -> confidentiality

(**
 * Integrity join (least upper bound).
 * ITrusted join ITrusted = ITrusted
 * ITrusted join IUntrusted = IUntrusted
 * IUntrusted join ITrusted = IUntrusted
 * IUntrusted join IUntrusted = IUntrusted
 *
 * Semantics: Any untrusted input taints the result.
 *)
val integ_join : i1:integrity -> i2:integrity -> integrity

(**
 * Integrity meet (greatest lower bound).
 * ITrusted meet ITrusted = ITrusted
 * ITrusted meet IUntrusted = ITrusted
 * IUntrusted meet ITrusted = ITrusted
 * IUntrusted meet IUntrusted = IUntrusted
 *)
val integ_meet : i1:integrity -> i2:integrity -> integrity

(**
 * Taint set union (join operation on sets).
 * Combines all taints from both sets.
 *
 * Example: {SQLi, XSS} union {XSS, CMDi} = {SQLi, XSS, CMDi}
 *)
val taint_set_union : ks1:taint_set -> ks2:taint_set -> taint_set

(**
 * Taint set intersection (meet operation on sets).
 * Keeps only taints present in both sets.
 *
 * Example: {SQLi, XSS} intersect {XSS, CMDi} = {XSS}
 *)
val taint_set_intersect : ks1:taint_set -> ks2:taint_set -> taint_set

(**
 * Security label join (least upper bound).
 *
 * Combines labels when data from multiple sources merges:
 *   result.confidentiality = conf_join l1.confidentiality l2.confidentiality
 *   result.integrity = integ_join l1.integrity l2.integrity
 *   result.taints = taint_set_union l1.taints l2.taints
 *
 * Example: Adding user input (tainted) to config value (secret):
 *   (Public, Untrusted, {SQLi}) join (Secret, Trusted, {})
 *   = (Secret, Untrusted, {SQLi})
 *   The result is both secret AND tainted.
 *
 * This is the KEY operation for taint propagation!
 *)
val sec_label_join : l1:sec_label -> l2:sec_label -> sec_label

(**
 * Security label meet (greatest lower bound).
 *
 * Computes the most permissive label that flows to both inputs:
 *   result.confidentiality = conf_meet l1.confidentiality l2.confidentiality
 *   result.integrity = integ_meet l1.integrity l2.integrity
 *   result.taints = taint_set_intersect l1.taints l2.taints
 *)
val sec_label_meet : l1:sec_label -> l2:sec_label -> sec_label


(** ============================================================================
    SECTION 7: LATTICE LAW LEMMAS - REFLEXIVITY
    ============================================================================

    These lemmas prove that the ordering relation is reflexive.
    SMTPat triggers enable automatic instantiation by Z3.
    ============================================================================ *)

(** taint_kind_eq is reflexive: k = k *)
val taint_kind_eq_refl : k:taint_kind ->
  Lemma (ensures taint_kind_eq k k = true)
        [SMTPat (taint_kind_eq k k)]

(** conf_leq is reflexive: c <= c *)
val conf_leq_refl : c:confidentiality ->
  Lemma (ensures conf_leq c c = true)
        [SMTPat (conf_leq c c)]

(** integ_leq is reflexive: i <= i *)
val integ_leq_refl : i:integrity ->
  Lemma (ensures integ_leq i i = true)
        [SMTPat (integ_leq i i)]

(** Element is in set if it's the head *)
val taint_in_set_head : k:taint_kind -> rest:taint_set ->
  Lemma (ensures taint_in_set k (k :: rest) = true)
        [SMTPat (taint_in_set k (k :: rest))]

(** taint_set_subset is reflexive: ks subset ks *)
val taint_set_subset_refl : ks:taint_set ->
  Lemma (ensures taint_set_subset ks ks = true)
        (decreases ks)
        [SMTPat (taint_set_subset ks ks)]

(** sec_label_leq is reflexive: l <= l *)
val sec_label_leq_refl : l:sec_label ->
  Lemma (ensures sec_label_leq l l = true)
        [SMTPat (sec_label_leq l l)]


(** ============================================================================
    SECTION 8: LATTICE LAW LEMMAS - TRANSITIVITY
    ============================================================================

    These lemmas prove that the ordering relation is transitive:
      l1 <= l2 /\ l2 <= l3 ==> l1 <= l3

    Transitivity is essential for multi-step flow analysis.
    ============================================================================ *)

(** Confidentiality ordering is transitive *)
val conf_leq_trans : c1:confidentiality -> c2:confidentiality -> c3:confidentiality ->
  Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c3 = true)
        (ensures conf_leq c1 c3 = true)

(** Integrity ordering is transitive *)
val integ_leq_trans : i1:integrity -> i2:integrity -> i3:integrity ->
  Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i3 = true)
        (ensures integ_leq i1 i3 = true)

(** If k in ks1 and ks1 subset ks2, then k in ks2 *)
val taint_in_set_trans : k:taint_kind -> ks1:taint_set -> ks2:taint_set ->
  Lemma (requires taint_in_set k ks1 = true /\ taint_set_subset ks1 ks2 = true)
        (ensures taint_in_set k ks2 = true)
        (decreases ks1)

(** Taint set subset is transitive *)
val taint_set_subset_trans : ks1:taint_set -> ks2:taint_set -> ks3:taint_set ->
  Lemma (requires taint_set_subset ks1 ks2 = true /\ taint_set_subset ks2 ks3 = true)
        (ensures taint_set_subset ks1 ks3 = true)
        (decreases ks1)

(** Security label ordering is transitive *)
val sec_label_leq_trans : l1:sec_label -> l2:sec_label -> l3:sec_label ->
  Lemma (requires sec_label_leq l1 l2 = true /\ sec_label_leq l2 l3 = true)
        (ensures sec_label_leq l1 l3 = true)


(** ============================================================================
    SECTION 9: LATTICE LAW LEMMAS - ANTISYMMETRY
    ============================================================================

    These lemmas prove that the ordering relation is antisymmetric:
      l1 <= l2 /\ l2 <= l1 ==> l1 = l2

    Note: For sec_label, this holds up to set equivalence (not structural
    equality) because taint_set is a list representing a set.
    ============================================================================ *)

(** Confidentiality ordering is antisymmetric *)
val conf_leq_antisym : c1:confidentiality -> c2:confidentiality ->
  Lemma (requires conf_leq c1 c2 = true /\ conf_leq c2 c1 = true)
        (ensures c1 = c2)

(** Integrity ordering is antisymmetric *)
val integ_leq_antisym : i1:integrity -> i2:integrity ->
  Lemma (requires integ_leq i1 i2 = true /\ integ_leq i2 i1 = true)
        (ensures i1 = i2)


(** ============================================================================
    SECTION 10: LATTICE LAW LEMMAS - JOIN IS LEAST UPPER BOUND
    ============================================================================

    These lemmas prove that join is the LEAST UPPER BOUND (supremum).

    For join to be the LUB:
      1. Upper bound: l1 <= join(l1,l2) and l2 <= join(l1,l2)
      2. Least: For any upper bound u, join(l1,l2) <= u
    ============================================================================ *)

(** Join is an upper bound for the left operand *)
val sec_label_join_upper_l : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq l1 (sec_label_join l1 l2) = true)
        [SMTPat (sec_label_join l1 l2)]

(** Join is an upper bound for the right operand *)
val sec_label_join_upper_r : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq l2 (sec_label_join l1 l2) = true)

(** Join is the LEAST upper bound: any upper bound u >= join *)
val sec_label_join_lub : l1:sec_label -> l2:sec_label -> u:sec_label ->
  Lemma (requires sec_label_leq l1 u = true /\ sec_label_leq l2 u = true)
        (ensures sec_label_leq (sec_label_join l1 l2) u = true)


(** ============================================================================
    SECTION 11: LATTICE LAW LEMMAS - MEET IS GREATEST LOWER BOUND
    ============================================================================

    These lemmas prove that meet is the GREATEST LOWER BOUND (infimum).

    For meet to be the GLB:
      1. Lower bound: meet(l1,l2) <= l1 and meet(l1,l2) <= l2
      2. Greatest: For any lower bound lb, lb <= meet(l1,l2)
    ============================================================================ *)

(** Meet is a lower bound for the left operand *)
val sec_label_meet_lower_l : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l1 = true)
        [SMTPat (sec_label_meet l1 l2)]

(** Meet is a lower bound for the right operand *)
val sec_label_meet_lower_r : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) l2 = true)

(** Meet is the GREATEST lower bound: any lower bound lb <= meet *)
val sec_label_meet_glb : l1:sec_label -> l2:sec_label -> lb:sec_label ->
  Lemma (requires sec_label_leq lb l1 = true /\ sec_label_leq lb l2 = true)
        (ensures sec_label_leq lb (sec_label_meet l1 l2) = true)


(** ============================================================================
    SECTION 12: LATTICE LAW LEMMAS - COMMUTATIVITY AND IDEMPOTENCE
    ============================================================================

    Additional lattice laws required for a complete lattice structure.

    Commutativity: join(a,b) = join(b,a), meet(a,b) = meet(b,a)
    Idempotence: join(a,a) = a, meet(a,a) = a

    Note: Commutativity holds "up to set equivalence" because taint_set
    is implemented as a list (different orderings, same membership).
    ============================================================================ *)

(** Join is commutative up to mutual leq (set equivalence) *)
val sec_label_join_comm_equiv : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_join l1 l2) (sec_label_join l2 l1) = true /\
                  sec_label_leq (sec_label_join l2 l1) (sec_label_join l1 l2) = true)

(** Join is idempotent: join(l,l) = l *)
val sec_label_join_idem : l:sec_label ->
  Lemma (ensures sec_label_join l l == l)

(** Meet is commutative up to mutual leq (set equivalence) *)
val sec_label_meet_comm_equiv : l1:sec_label -> l2:sec_label ->
  Lemma (ensures sec_label_leq (sec_label_meet l1 l2) (sec_label_meet l2 l1) = true /\
                  sec_label_leq (sec_label_meet l2 l1) (sec_label_meet l1 l2) = true)

(** Meet is idempotent: meet(l,l) = l *)
val sec_label_meet_idem : l:sec_label ->
  Lemma (ensures sec_label_meet l l == l)


(** ============================================================================
    SECTION 13: SECURITY-TYPED TYPES
    ============================================================================

    A security-typed type combines a base Brrr-Lang type with a security label.
    This integrates IFC directly into the type system rather than using
    wrapper types.

    Advantages over wrappers:
      - Subtyping respects both base and security dimensions
      - No explicit wrapping/unwrapping in code
      - Type inference can propagate labels
    ============================================================================ *)

(**
 * Security-typed type: base Brrr-Lang type + security label.
 *
 * @field base   The underlying Brrr-Lang type (TInt, TString, etc.)
 * @field label  The security label tracking confidentiality/integrity
 *
 * Example: sec_type = { base = TString; label = {CPublic; IUntrusted; [TkSQLi]} }
 * This represents a string from user input, potentially carrying SQL injection.
 *)
noeq type sec_type = {
  base : brrr_type;
  label : sec_label;
}

(** Create a security-typed type with specified label *)
val mk_sec_type : brrr_type -> sec_label -> sec_type

(** Create an untainted (trusted, public) type - the default safe case *)
val untainted_type : brrr_type -> sec_type

(** Create a tainted type with a single taint kind *)
val tainted_type : brrr_type -> taint_kind -> sec_type

(** Create a secret (confidential, trusted) type *)
val secret_type : brrr_type -> sec_type

(**
 * Security-typed subtyping.
 *
 * st1 <: st2 iff:
 *   1. base(st1) <: base(st2)    (structural subtyping on base)
 *   2. label(st1) <= label(st2)  (security can only increase)
 *
 * This ensures data cannot be coerced to a lower security level.
 *)
val sec_type_subtype : st1:sec_type -> st2:sec_type -> bool

(** Security-typed subtyping is reflexive *)
val sec_type_subtype_refl : st:sec_type ->
  Lemma (ensures sec_type_subtype st st = true)
        [SMTPat (sec_type_subtype st st)]


(** ============================================================================
    SECTION 14: SECURITY FUNCTION TYPES
    ============================================================================

    Functions have security-typed parameters and returns. The security role
    annotation indicates whether the function is a Source, Sink, or Sanitizer.
    ============================================================================ *)

(**
 * Security role of a function.
 *
 * @SrNone       No special security role (ordinary function)
 * @SrSource     Introduces taints - return value is tainted
 *               Example: read_user_input, fetch_url
 * @SrSink       Consumes data - rejects specified taints
 *               Example: execute_sql, system_call
 * @SrSanitizer  Removes taints - cleans specified vulnerability kinds
 *               Example: escape_html, parameterize_query
 * @SrValidator  Partial sanitization - validates without full sanitization
 *               Example: check_email_format (validates but doesn't escape)
 *)
type sec_role =
  | SrNone      : sec_role
  | SrSource    : list taint_kind -> sec_role
  | SrSink      : list taint_kind -> sec_role
  | SrSanitizer : list taint_kind -> sec_role
  | SrValidator : list taint_kind -> sec_role

(** Security-typed function parameter *)
noeq type sec_param = {
  sp_name : option string;   (* Parameter name (for diagnostics) *)
  sp_type : sec_type;        (* Type including security label *)
  sp_mode : mode;            (* Ownership mode (own/borrow/etc.) *)
}

(** Security-typed function type *)
noeq type sec_func_type = {
  sf_params      : list sec_param;  (* Security-typed parameters *)
  sf_return      : sec_type;        (* Security-typed return *)
  sf_effects     : effect_row;      (* Effect signature *)
  sf_role        : sec_role;        (* Source/Sink/Sanitizer role *)
  sf_is_unsafe   : bool;            (* Whether function is unsafe *)
}


(** ============================================================================
    SECTION 15: PC (PROGRAM COUNTER) LABEL
    ============================================================================

    The PC label tracks the security level of the current control flow context.
    This is essential for preventing IMPLICIT FLOWS.

    Implicit flow example:
      if (secret) { x = 1; } else { x = 0; }

    Here x depends on secret even though secret isn't directly assigned to x.
    The PC label ensures assignments are only allowed to variables whose
    label is >= the PC label.

    Reference: Denning & Denning 1977, "Certification of Programs for
    Secure Information Flow"
    ============================================================================ *)

(** PC label is just a security label *)
type pc_label = sec_label

(** Initial PC: public, trusted - no restrictions *)
val initial_pc : pc_label

(**
 * Raise PC when entering a branch guarded by a sensitive condition.
 *
 * Example: if (secret) { ... }
 * Inside the branch, PC = join(PC, label(secret)) = Secret
 * This prevents assigning to public variables inside the secret branch.
 *)
val raise_pc : pc:pc_label -> guard_label:sec_label -> pc_label

(**
 * Check if an assignment is allowed.
 *
 * The rule is: join(pc, rhs_label) <= lhs_label
 *
 * This means:
 *   - RHS value can flow to LHS
 *   - PC context allows assignment to LHS
 *
 * Example: if (secret) { public_var = 1; }
 *   PC = Secret, rhs = Public (literal 1), lhs = Public
 *   join(Secret, Public) = Secret
 *   Secret <= Public? NO - assignment rejected!
 *)
val check_flow : pc:pc_label -> rhs:sec_label -> lhs:sec_label -> bool


(** ============================================================================
    SECTION 16: TAINT OPERATIONS
    ============================================================================

    Operations for manipulating taint sets, particularly SANITIZATION.

    IMPORTANT DESIGN DECISION:
    Sanitization and endorsement are SEPARATE operations!

    - sanitize_label: Removes specific taints but does NOT change integrity
    - endorse_label: Promotes IUntrusted to ITrusted (only if all taints gone)

    This separation is a SECURITY FEATURE. Reasons:
    1. A sanitizer might only handle one attack vector (e.g., SQL injection)
       but the data could still be dangerous for other sinks (e.g., command injection)
    2. Automatic endorsement hides security decisions in code flow
    3. Defense in depth requires explicit trust boundaries
    ============================================================================ *)

(** Remove a single taint kind from a taint set *)
val remove_taint : k:taint_kind -> ks:taint_set -> taint_set

(** Remove multiple taint kinds from a taint set *)
val remove_taints : to_remove:list taint_kind -> ks:taint_set -> taint_set

(**
 * Sanitize a label by removing specified taints.
 *
 * IMPORTANT: This does NOT change integrity!
 * The data remains IUntrusted even after sanitization.
 * Use endorse_label to promote to ITrusted after all taints are removed.
 *)
val sanitize_label : to_remove:list taint_kind -> l:sec_label -> sec_label

(** Sanitize a security-typed type *)
val sanitize_sec_type : to_remove:list taint_kind -> st:sec_type -> sec_type

(** Check if a label has any of the specified taints *)
val has_any_taint : ks:list taint_kind -> l:sec_label -> bool


(** ============================================================================
    SECTION 17: TAINT REMOVAL LEMMAS
    ============================================================================

    Correctness proofs for sanitization operations.
    ============================================================================ *)

(** Sanitization removes the specified taint *)
val remove_taint_correct : k:taint_kind -> ks:taint_set ->
  Lemma (ensures taint_in_set k (remove_taint k ks) = false)
        (decreases ks)

(** Sanitization preserves other taints *)
val remove_taint_preserves : k:taint_kind -> k':taint_kind -> ks:taint_set ->
  Lemma (requires taint_kind_eq k k' = false)
        (ensures taint_in_set k' (remove_taint k ks) = taint_in_set k' ks)
        (decreases ks)

(** After sanitization, sink check passes for removed taints *)
val sanitize_enables_sink : to_remove:list taint_kind -> l:sec_label ->
  Lemma (ensures not (has_any_taint to_remove (sanitize_label to_remove l)))


(** ============================================================================
    SECTION 18: I/O TAINT INTEGRATION
    ============================================================================

    Maps I/O sources and sinks from the Effects module to taint kinds.
    This connects the effect system's I/O tracking with taint analysis.

    Sources introduce taints (user input, network, files).
    Sinks require absence of specific taints (database, shell, files).
    ============================================================================ *)

(**
 * Get taints introduced by an I/O source.
 *
 * IOStdin:     All common taints (user input is dangerous!)
 * IOEnvVar:    Command injection, path traversal
 * IOFileInput: Path traversal
 * IONetworkIn: SSRF, SQLi, XSS, CMDi (network is untrusted)
 * IOUserInput: All common taints
 *)
val io_source_taints : src:io_source -> taint_set

(**
 * Get taint requirements for an I/O sink.
 * Returns taints that MUST BE ABSENT for safe operation.
 *
 * IOStdout/IOStderr: No requirements (informational output)
 * IOFileOutput:      Reject path traversal
 * IONetworkOut:      Reject SSRF
 * IODatabase:        Reject SQL injection
 *)
val io_sink_requirements : snk:io_sink -> taint_set

(** Get the security label for data from an I/O source *)
val effect_input_label : src:io_source -> sec_label

(** Check if output to a sink is allowed with given label *)
val effect_output_allowed : snk:io_sink -> l:sec_label -> bool


(** ============================================================================
    SECTION 19: SECURITY OPERATIONS
    ============================================================================

    Operations for computing result labels from input labels.
    ============================================================================ *)

(** Unary operation result: same security as input *)
val sec_unary_result : st:sec_type -> result_base:brrr_type -> sec_type

(** Binary operation result: joined security of both inputs *)
val sec_binary_result : st1:sec_type -> st2:sec_type -> result_base:brrr_type -> sec_type

(** N-ary operation: compute joined label of all inputs *)
val sec_nary_label : sts:list sec_type -> sec_label

(** N-ary operation result: joined security of all inputs *)
val sec_nary_result : sts:list sec_type -> result_base:brrr_type -> sec_type


(** ============================================================================
    SECTION 20: SECURITY CONTEXT
    ============================================================================

    The security context maps variable names to their security-typed types.
    Used by the security type checker.
    ============================================================================ *)

(** Context entry: variable name paired with security-typed type *)
type sec_ctx_entry = string & sec_type

(** Security context: list of entries (most recent binding first) *)
type sec_ctx = list sec_ctx_entry

(** Empty context *)
val empty_sec_ctx : sec_ctx

(** Extend context with a new binding *)
val extend_sec_ctx : x:string -> st:sec_type -> ctx:sec_ctx -> sec_ctx

(** Look up a variable in the context *)
val lookup_sec_ctx : x:string -> ctx:sec_ctx -> option sec_type


(** ============================================================================
    SECTION 21: SECURITY ANNOTATIONS
    ============================================================================

    Type-level annotations for static security analysis.
    These are attached to function declarations to indicate security roles.
    ============================================================================ *)

(**
 * Source annotation: function introduces taint.
 *
 * @field src_name    Human-readable name for diagnostics
 * @field src_taints  Taint kinds introduced by this source
 * @field src_origin  Category: "user_input", "network", "file", etc.
 *)
noeq type source_annotation = {
  src_name   : string;
  src_taints : list taint_kind;
  src_origin : string;
}

(**
 * Sink annotation: function requires untainted input.
 *
 * @field snk_name     Human-readable name for diagnostics
 * @field snk_rejects  Taint kinds that must be absent
 * @field snk_params   Which parameters must be untainted (0-indexed)
 *)
noeq type sink_annotation = {
  snk_name     : string;
  snk_rejects  : list taint_kind;
  snk_params   : list nat;
}

(**
 * Sanitizer annotation: function removes taint.
 *
 * @field san_name     Human-readable name for diagnostics
 * @field san_removes  Taint kinds removed by this sanitizer
 * @field san_param    Which parameter is sanitized (0-indexed)
 *)
noeq type sanitizer_annotation = {
  san_name    : string;
  san_removes : list taint_kind;
  san_param   : nat;
}

(** Combined security annotation sum type *)
type sec_annotation =
  | AnnSource    : source_annotation -> sec_annotation
  | AnnSink      : sink_annotation -> sec_annotation
  | AnnSanitizer : sanitizer_annotation -> sec_annotation
  | AnnTrusted   : sec_annotation  (* Function is in trusted code base *)

(** Check if passing arguments to a sink is safe *)
val sink_check : snk:sink_annotation -> arg_labels:list sec_label -> bool


(** ============================================================================
    SECTION 22: BRRR-MACHINE INTEGRATION TYPES
    ============================================================================

    Types for Brrr-Machine security analysis reporting and integration.
    ============================================================================ *)

(** Security finding severity *)
type sec_severity =
  | SevCritical : sec_severity  (* Confirmed vulnerability, high impact *)
  | SevHigh     : sec_severity  (* Likely vulnerability *)
  | SevMedium   : sec_severity  (* Possible vulnerability *)
  | SevLow      : sec_severity  (* Minor issue *)
  | SevInfo     : sec_severity  (* Informational only *)

(** Security finding for vulnerability reporting *)
noeq type sec_finding = {
  sf_id          : nat;              (* Unique finding ID *)
  sf_kind        : taint_kind;       (* Vulnerability category *)
  sf_severity    : sec_severity;     (* Severity level *)
  sf_source_loc  : option nat;       (* Source code location *)
  sf_sink_loc    : option nat;       (* Sink code location *)
  sf_message     : string;           (* Human-readable description *)
  sf_remediation : option string;    (* Suggested fix *)
}

(** Taint flow edge for interprocedural analysis *)
noeq type taint_flow_edge = {
  tfe_from_node : nat;               (* Source node ID in call graph *)
  tfe_to_node   : nat;               (* Target node ID *)
  tfe_taints    : taint_set;         (* Taints flowing along edge *)
  tfe_sanitized : taint_set;         (* Taints removed along edge *)
}

(** Function taint summary for interprocedural analysis *)
noeq type func_taint_summary = {
  fts_func_id      : nat;                 (* Function ID *)
  fts_param_taints : list sec_label;      (* Input taint on each param *)
  fts_return_taint : sec_label;           (* Output taint *)
  fts_role         : sec_role;            (* Source/Sink/Sanitizer role *)
  fts_annotations  : list sec_annotation; (* Security annotations *)
}


(** ============================================================================
    SECTION 23: WELL-FORMEDNESS
    ============================================================================

    Predicates for checking well-formedness of security labels and types.
    ============================================================================ *)

(**
 * A security label is well-formed if taints are consistent with integrity.
 *
 * Well-formedness rule:
 *   integrity = ITrusted ==> taints = []
 *
 * Trusted data should not have taints. If it has taints, something is wrong.
 *)
val sec_label_wf : l:sec_label -> bool

(** A security type is well-formed if its label is well-formed *)
val sec_type_wf : st:sec_type -> bool


(** ============================================================================
    SECTION 24: TAINT EFFECTS
    ============================================================================

    Effect constructors for taint tracking in the effect system.
    ============================================================================ *)

(**
 * Taint effect operations.
 *
 * @ETaintSource     Function introduces taints (e.g., read_input)
 * @ETaintSink       Function requires absence of taints (e.g., execute_sql)
 * @ETaintSanitize   Function removes taints (e.g., escape_html)
 * @ETaintPropagate  Operation propagates existing taints (default)
 *)
type taint_effect =
  | ETaintSource    : list taint_kind -> taint_effect
  | ETaintSink      : list taint_kind -> taint_effect
  | ETaintSanitize  : list taint_kind -> taint_effect
  | ETaintPropagate : taint_effect

(** Convert taint effect to string for diagnostics *)
val taint_effect_to_string : te:taint_effect -> string


(** ============================================================================
    SECTION 25: NAMED SECURITY LEVELS (Extensibility)
    ============================================================================

    Support for user-defined security lattice configurations.
    Allows extending beyond the basic two-point lattices.
    ============================================================================ *)

(** Unique identifier for a security level *)
type sec_level_id = nat

(**
 * Named security level for custom lattice configurations.
 *
 * @field level_id    Unique identifier within the lattice
 * @field level_name  Human-readable name (e.g., "TopSecret", "Confidential")
 *)
noeq type named_sec_level = {
  level_id   : sec_level_id;
  level_name : string;
}
