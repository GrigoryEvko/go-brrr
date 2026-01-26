//! Taint tracking for security vulnerability detection
//!
//! Mirrors F* SecurityTypes.fsti taint_kind (lines 61-74).
//!
//! # Taint Kinds
//!
//! Taint kinds categorize security vulnerabilities. This is more fine-grained
//! than just "tainted/untainted" - each kind represents a specific attack vector.
//!
//! # Taint Set Operations
//!
//! `TaintSet` provides set operations with lattice semantics:
//! - `union` is the join (least upper bound) - taints propagate
//! - `intersection` is the meet (greatest lower bound)
//! - Ordering is subset inclusion

use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt;

use crate::effects::{IoSink, IoSource};

/// Categories of taint representing vulnerability classes.
///
/// Based on F* SecurityTypes.fsti:
/// ```fstar
/// type taint_kind =
///   | TkSQLi | TkXSS | TkCMDi | TkPathTraversal | TkSSRF
///   | TkLDAPi | TkXMLi | TkHeaderi | TkLogi | TkTemplatei
///   | TkDeserial | TkRedirect | TkCustom of string
/// ```
///
/// Unlike `TaintLabel` (which represents taint sources like user input),
/// `TaintKind` represents the type of vulnerability that tainted data
/// can cause when reaching a sink.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
#[repr(u8)]
pub enum TaintKind {
    /// SQL Injection (CWE-89)
    SQLi = 0,
    /// Cross-Site Scripting (CWE-79)
    XSS = 1,
    /// Command Injection / OS Command Injection (CWE-78)
    CMDi = 2,
    /// Path Traversal / Directory Traversal (CWE-22)
    PathTraversal = 3,
    /// Server-Side Request Forgery (CWE-918)
    SSRF = 4,
    /// Open Redirect (CWE-601)
    OpenRedirect = 5,
    /// LDAP Injection (CWE-90)
    LDAPi = 6,
    /// XML Injection / XXE (CWE-91, CWE-611)
    XMLi = 7,
    /// Template Injection (CWE-1336)
    TemplateInjection = 8,
    /// Code Injection / Eval Injection (CWE-94)
    CodeInjection = 9,
    /// HTTP Header Injection (CWE-113)
    HeaderInjection = 10,
    /// Log Injection (CWE-117)
    LogInjection = 11,
    /// Deserialization of Untrusted Data (CWE-502)
    Deserialization = 12,
    /// Prototype Pollution - JavaScript specific (CWE-1321)
    PrototypePollution = 13,
    /// Regular Expression DoS (CWE-1333)
    ReDoS = 14,
}

impl TaintKind {
    /// All builtin taint kinds.
    pub const ALL: &'static [Self] = &[
        Self::SQLi,
        Self::XSS,
        Self::CMDi,
        Self::PathTraversal,
        Self::SSRF,
        Self::OpenRedirect,
        Self::LDAPi,
        Self::XMLi,
        Self::TemplateInjection,
        Self::CodeInjection,
        Self::HeaderInjection,
        Self::LogInjection,
        Self::Deserialization,
        Self::PrototypePollution,
        Self::ReDoS,
    ];

    /// Common web application taints (user input typically carries these).
    pub const WEB_COMMON: &'static [Self] = &[
        Self::SQLi,
        Self::XSS,
        Self::CMDi,
        Self::PathTraversal,
        Self::SSRF,
        Self::OpenRedirect,
    ];

    /// Returns the CWE ID for this taint kind.
    #[must_use]
    pub const fn cwe_id(self) -> u32 {
        match self {
            Self::SQLi => 89,
            Self::XSS => 79,
            Self::CMDi => 78,
            Self::PathTraversal => 22,
            Self::SSRF => 918,
            Self::OpenRedirect => 601,
            Self::LDAPi => 90,
            Self::XMLi => 91,
            Self::TemplateInjection => 1336,
            Self::CodeInjection => 94,
            Self::HeaderInjection => 113,
            Self::LogInjection => 117,
            Self::Deserialization => 502,
            Self::PrototypePollution => 1321,
            Self::ReDoS => 1333,
        }
    }

    /// Returns a human-readable name for this taint kind.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::SQLi => "SQL Injection",
            Self::XSS => "Cross-Site Scripting",
            Self::CMDi => "Command Injection",
            Self::PathTraversal => "Path Traversal",
            Self::SSRF => "Server-Side Request Forgery",
            Self::OpenRedirect => "Open Redirect",
            Self::LDAPi => "LDAP Injection",
            Self::XMLi => "XML Injection",
            Self::TemplateInjection => "Template Injection",
            Self::CodeInjection => "Code Injection",
            Self::HeaderInjection => "Header Injection",
            Self::LogInjection => "Log Injection",
            Self::Deserialization => "Unsafe Deserialization",
            Self::PrototypePollution => "Prototype Pollution",
            Self::ReDoS => "Regular Expression DoS",
        }
    }

    /// Format as short symbol for .brrrx output.
    #[must_use]
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::SQLi => "SQLi",
            Self::XSS => "XSS",
            Self::CMDi => "CMDi",
            Self::PathTraversal => "PathTrav",
            Self::SSRF => "SSRF",
            Self::OpenRedirect => "Redirect",
            Self::LDAPi => "LDAPi",
            Self::XMLi => "XMLi",
            Self::TemplateInjection => "TemplateInj",
            Self::CodeInjection => "CodeInj",
            Self::HeaderInjection => "HeaderInj",
            Self::LogInjection => "LogInj",
            Self::Deserialization => "Deser",
            Self::PrototypePollution => "ProtoPoll",
            Self::ReDoS => "ReDoS",
        }
    }

    /// Get discriminant for binary encoding.
    #[must_use]
    pub const fn discriminant(self) -> u8 {
        self as u8
    }

    /// Returns the OWASP Top 10 (2021) category if applicable.
    #[must_use]
    pub const fn owasp_category(self) -> Option<&'static str> {
        match self {
            Self::SQLi
            | Self::CMDi
            | Self::XSS
            | Self::LDAPi
            | Self::XMLi
            | Self::TemplateInjection
            | Self::CodeInjection
            | Self::HeaderInjection
            | Self::LogInjection => Some("A03:2021 - Injection"),

            Self::PathTraversal | Self::OpenRedirect => Some("A01:2021 - Broken Access Control"),

            Self::SSRF => Some("A10:2021 - Server-Side Request Forgery"),

            Self::Deserialization => Some("A08:2021 - Software and Data Integrity Failures"),

            Self::PrototypePollution | Self::ReDoS => None,
        }
    }

    /// Returns the severity level (1-10) for this vulnerability type.
    #[must_use]
    pub const fn severity_score(self) -> u8 {
        match self {
            // Critical: Remote code execution potential
            Self::CMDi | Self::CodeInjection | Self::Deserialization => 10,

            // High: Data breach or significant impact
            Self::SQLi | Self::SSRF | Self::XMLi | Self::TemplateInjection => 9,

            // Medium-High: Client-side attacks or path manipulation
            Self::XSS | Self::PathTraversal | Self::LDAPi => 7,

            // Medium: Redirect attacks or prototype manipulation
            Self::OpenRedirect | Self::HeaderInjection | Self::PrototypePollution => 6,

            // Lower: Logging issues or DoS
            Self::LogInjection | Self::ReDoS => 4,
        }
    }
}

impl Default for TaintKind {
    fn default() -> Self {
        Self::SQLi
    }
}

impl fmt::Display for TaintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ============================================================================
// Custom Taint
// ============================================================================

/// Custom taint kind for user-defined vulnerability categories.
///
/// Maps to F* `TkCustom of string`.
/// Uses string interning for efficient comparison and storage.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CustomTaint(pub Spur);

impl CustomTaint {
    /// Create a new custom taint with the given interned name.
    #[must_use]
    pub const fn new(name: Spur) -> Self {
        Self(name)
    }

    /// Get the interned name key.
    #[must_use]
    pub const fn key(&self) -> Spur {
        self.0
    }
}

// ============================================================================
// Extended Taint
// ============================================================================

/// Extended taint - either builtin or custom.
///
/// This allows extending the taint system with project-specific
/// vulnerability categories while maintaining efficient comparison
/// for builtin kinds.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Taint {
    /// Builtin taint kind (fast path)
    Builtin(TaintKind),
    /// User-defined taint kind
    Custom(CustomTaint),
}

impl Taint {
    /// Check if this is a builtin taint.
    #[must_use]
    pub const fn is_builtin(&self) -> bool {
        matches!(self, Self::Builtin(_))
    }

    /// Get the builtin kind if present.
    #[must_use]
    pub const fn as_builtin(&self) -> Option<TaintKind> {
        match self {
            Self::Builtin(k) => Some(*k),
            Self::Custom(_) => None,
        }
    }

    /// Get the custom taint if present.
    #[must_use]
    pub const fn as_custom(&self) -> Option<&CustomTaint> {
        match self {
            Self::Builtin(_) => None,
            Self::Custom(c) => Some(c),
        }
    }
}

impl From<TaintKind> for Taint {
    fn from(kind: TaintKind) -> Self {
        Self::Builtin(kind)
    }
}

impl From<CustomTaint> for Taint {
    fn from(custom: CustomTaint) -> Self {
        Self::Custom(custom)
    }
}

// ============================================================================
// Taint Set
// ============================================================================

/// Set of taints with lattice operations.
///
/// Mirrors F* `taint_set = list taint_kind` with proper set semantics.
/// The implementation uses `HashSet` for O(1) membership tests.
///
/// # Lattice Structure
///
/// - Bottom: empty set (no taints - clean data)
/// - Top: all taints (maximally tainted)
/// - Join (union): least upper bound - taints propagate
/// - Meet (intersection): greatest lower bound
/// - Order: subset inclusion
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TaintSet {
    /// Builtin taints - stored as HashSet for O(1) operations
    pub builtin: HashSet<TaintKind>,
    /// Custom taints - stored separately
    pub custom: HashSet<CustomTaint>,
}

impl TaintSet {
    /// Empty taint set (bottom of lattice).
    #[must_use]
    pub fn empty() -> Self {
        Self {
            builtin: HashSet::new(),
            custom: HashSet::new(),
        }
    }

    /// Create from builtin taints.
    #[must_use]
    pub fn from_builtins(taints: impl IntoIterator<Item = TaintKind>) -> Self {
        Self {
            builtin: taints.into_iter().collect(),
            custom: HashSet::new(),
        }
    }

    /// Create with a single builtin taint.
    #[must_use]
    pub fn singleton(taint: TaintKind) -> Self {
        let mut builtin = HashSet::new();
        builtin.insert(taint);
        Self {
            builtin,
            custom: HashSet::new(),
        }
    }

    /// Create with all web common taints.
    #[must_use]
    pub fn web_common() -> Self {
        Self::from_builtins(TaintKind::WEB_COMMON.iter().copied())
    }

    /// Check if empty (untainted / bottom element).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.builtin.is_empty() && self.custom.is_empty()
    }

    /// Get total number of taints.
    #[must_use]
    pub fn len(&self) -> usize {
        self.builtin.len() + self.custom.len()
    }

    /// Add a builtin taint.
    pub fn add(&mut self, taint: TaintKind) {
        self.builtin.insert(taint);
    }

    /// Add a custom taint.
    pub fn add_custom(&mut self, taint: CustomTaint) {
        self.custom.insert(taint);
    }

    /// Add an extended taint.
    pub fn add_taint(&mut self, taint: Taint) {
        match taint {
            Taint::Builtin(k) => self.add(k),
            Taint::Custom(c) => self.add_custom(c),
        }
    }

    /// Remove specific taints (sanitization).
    ///
    /// This mirrors F* `remove_taints` - used by sanitizers to
    /// remove specific vulnerability categories.
    pub fn remove(&mut self, taints: &[TaintKind]) {
        for t in taints {
            self.builtin.remove(t);
        }
    }

    /// Remove a single taint.
    pub fn remove_one(&mut self, taint: TaintKind) -> bool {
        self.builtin.remove(&taint)
    }

    /// Check if contains a specific builtin taint.
    #[must_use]
    pub fn contains(&self, taint: TaintKind) -> bool {
        self.builtin.contains(&taint)
    }

    /// Check if contains a specific custom taint.
    #[must_use]
    pub fn contains_custom(&self, taint: &CustomTaint) -> bool {
        self.custom.contains(taint)
    }

    /// Check if contains any of the specified taints.
    #[must_use]
    pub fn contains_any(&self, taints: &[TaintKind]) -> bool {
        taints.iter().any(|t| self.contains(*t))
    }

    /// Union of taint sets (lattice join / least upper bound).
    ///
    /// Taints propagate: if either input has a taint, the result has it.
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self {
            builtin: self.builtin.union(&other.builtin).copied().collect(),
            custom: self.custom.union(&other.custom).cloned().collect(),
        }
    }

    /// In-place union.
    pub fn union_with(&mut self, other: &Self) {
        self.builtin.extend(other.builtin.iter().copied());
        self.custom.extend(other.custom.iter().cloned());
    }

    /// Intersection of taint sets (lattice meet / greatest lower bound).
    #[must_use]
    pub fn intersection(&self, other: &Self) -> Self {
        Self {
            builtin: self.builtin.intersection(&other.builtin).copied().collect(),
            custom: self.custom.intersection(&other.custom).cloned().collect(),
        }
    }

    /// Check if this is a subset of other (lattice ordering).
    #[must_use]
    pub fn is_subset(&self, other: &Self) -> bool {
        self.builtin.is_subset(&other.builtin) && self.custom.is_subset(&other.custom)
    }

    /// Check if this is a superset of other.
    #[must_use]
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    /// Iterate over builtin taints.
    pub fn iter_builtin(&self) -> impl Iterator<Item = TaintKind> + '_ {
        self.builtin.iter().copied()
    }

    /// Iterate over all taints as `Taint` enum.
    pub fn iter(&self) -> impl Iterator<Item = Taint> + '_ {
        self.builtin
            .iter()
            .copied()
            .map(Taint::Builtin)
            .chain(self.custom.iter().cloned().map(Taint::Custom))
    }
}

// ============================================================================
// Taint Status
// ============================================================================

/// Taint status for a value - either clean or tainted.
///
/// This is used for tracking taint through data flow analysis.
/// Normalizes empty taint sets to `Clean` for consistent representation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TaintStatus {
    /// Not tainted (from trusted source)
    Clean,
    /// Tainted with specific vulnerability categories
    Tainted(TaintSet),
}

impl TaintStatus {
    /// Untainted value constant.
    pub const CLEAN: Self = Self::Clean;

    /// Create tainted status, normalizing empty set to clean.
    #[must_use]
    pub fn tainted(taints: TaintSet) -> Self {
        if taints.is_empty() {
            Self::Clean
        } else {
            Self::Tainted(taints)
        }
    }

    /// Create status with a single taint.
    #[must_use]
    pub fn with_taint(taint: TaintKind) -> Self {
        Self::Tainted(TaintSet::singleton(taint))
    }

    /// Check if clean (untainted).
    #[must_use]
    pub const fn is_clean(&self) -> bool {
        matches!(self, Self::Clean)
    }

    /// Check if tainted.
    #[must_use]
    pub const fn is_tainted(&self) -> bool {
        matches!(self, Self::Tainted(_))
    }

    /// Get taints if tainted, None if clean.
    #[must_use]
    pub const fn taints(&self) -> Option<&TaintSet> {
        match self {
            Self::Clean => None,
            Self::Tainted(ts) => Some(ts),
        }
    }

    /// Get taints or empty set.
    #[must_use]
    pub fn taints_or_empty(&self) -> TaintSet {
        match self {
            Self::Clean => TaintSet::empty(),
            Self::Tainted(ts) => ts.clone(),
        }
    }

    /// Join two statuses (union of taints) - lattice join.
    ///
    /// If either is tainted, result is tainted with combined taints.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Clean, Self::Clean) => Self::Clean,
            (Self::Clean, Self::Tainted(ts)) | (Self::Tainted(ts), Self::Clean) => {
                Self::Tainted(ts.clone())
            }
            (Self::Tainted(t1), Self::Tainted(t2)) => Self::Tainted(t1.union(t2)),
        }
    }

    /// In-place join.
    pub fn join_with(&mut self, other: &Self) {
        *self = self.join(other);
    }

    /// Meet two statuses (intersection of taints) - lattice meet.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Clean, _) | (_, Self::Clean) => Self::Clean,
            (Self::Tainted(t1), Self::Tainted(t2)) => Self::tainted(t1.intersection(t2)),
        }
    }

    /// Remove specific taints (sanitization).
    ///
    /// Returns Clean if all taints are removed.
    #[must_use]
    pub fn sanitize(&self, to_remove: &[TaintKind]) -> Self {
        match self {
            Self::Clean => Self::Clean,
            Self::Tainted(ts) => {
                let mut new_ts = ts.clone();
                new_ts.remove(to_remove);
                Self::tainted(new_ts)
            }
        }
    }

    /// Check if contains a specific taint.
    #[must_use]
    pub fn contains(&self, taint: TaintKind) -> bool {
        match self {
            Self::Clean => false,
            Self::Tainted(ts) => ts.contains(taint),
        }
    }
}

impl Default for TaintStatus {
    fn default() -> Self {
        Self::Clean
    }
}

// ============================================================================
// Tainted Wrapper
// ============================================================================

/// Wrapper for tainted values - carries both value and taint status.
///
/// This is a phantom type that tracks taint at the type level,
/// ensuring taint information propagates through operations.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Tainted<T> {
    /// The wrapped value
    pub value: T,
    /// Taint status of the value
    pub status: TaintStatus,
}

impl<T> Tainted<T> {
    /// Create an untainted (clean) value.
    #[must_use]
    pub fn clean(value: T) -> Self {
        Self {
            value,
            status: TaintStatus::Clean,
        }
    }

    /// Create a tainted value with specific taints.
    #[must_use]
    pub fn tainted(value: T, taints: TaintSet) -> Self {
        Self {
            value,
            status: TaintStatus::tainted(taints),
        }
    }

    /// Create a value with single taint.
    #[must_use]
    pub fn with_taint(value: T, taint: TaintKind) -> Self {
        Self {
            value,
            status: TaintStatus::with_taint(taint),
        }
    }

    /// Check if clean.
    #[must_use]
    pub const fn is_clean(&self) -> bool {
        self.status.is_clean()
    }

    /// Check if tainted.
    #[must_use]
    pub const fn is_tainted(&self) -> bool {
        self.status.is_tainted()
    }

    /// Map the inner value, preserving taint status.
    #[must_use]
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Tainted<U> {
        Tainted {
            value: f(self.value),
            status: self.status,
        }
    }

    /// Apply a function that may add taints.
    #[must_use]
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Tainted<U>) -> Tainted<U> {
        let result = f(self.value);
        Tainted {
            value: result.value,
            status: self.status.join(&result.status),
        }
    }

    /// Extract value, discarding taint information.
    ///
    /// WARNING: This loses taint tracking! Only use when you've verified
    /// the value is safe (e.g., after sanitization).
    #[must_use]
    pub fn into_inner(self) -> T {
        self.value
    }

    /// Get reference to inner value.
    #[must_use]
    pub const fn as_ref(&self) -> &T {
        &self.value
    }

    /// Get mutable reference to inner value.
    #[must_use]
    pub fn as_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T: Default> Default for Tainted<T> {
    fn default() -> Self {
        Self::clean(T::default())
    }
}

// ============================================================================
// I/O Source and Sink Taint Mappings
// ============================================================================

/// Returns the taints introduced by an I/O source.
///
/// Different input sources carry different security risks:
/// - User input (stdin, args, network) carries all web-common taints
/// - File input carries path traversal risks
/// - Environment variables can be manipulated
/// - Random/clock are trusted sources
///
/// # Example
///
/// ```ignore
/// use brrr_repr::security::io_source_taints;
/// use brrr_repr::effects::IoSource;
///
/// let taints = io_source_taints(&IoSource::UserInput);
/// assert!(taints.contains(TaintKind::SQLi));
/// assert!(taints.contains(TaintKind::XSS));
/// ```
#[must_use]
pub fn io_source_taints(source: &IoSource) -> TaintSet {
    match source {
        // User-controlled input: carries all common web attack vectors
        IoSource::UserInput | IoSource::Stdin => TaintSet::from_builtins([
            TaintKind::SQLi,
            TaintKind::XSS,
            TaintKind::CMDi,
            TaintKind::PathTraversal,
            TaintKind::SSRF,
            TaintKind::OpenRedirect,
            TaintKind::LDAPi,
            TaintKind::XMLi,
            TaintKind::TemplateInjection,
            TaintKind::CodeInjection,
            TaintKind::HeaderInjection,
            TaintKind::LogInjection,
            TaintKind::Deserialization,
        ]),

        // Network input: all web attack vectors plus deserialization
        IoSource::NetworkIn => TaintSet::from_builtins([
            TaintKind::SQLi,
            TaintKind::XSS,
            TaintKind::CMDi,
            TaintKind::PathTraversal,
            TaintKind::SSRF,
            TaintKind::OpenRedirect,
            TaintKind::LDAPi,
            TaintKind::XMLi,
            TaintKind::TemplateInjection,
            TaintKind::CodeInjection,
            TaintKind::HeaderInjection,
            TaintKind::LogInjection,
            TaintKind::Deserialization,
            TaintKind::PrototypePollution,
        ]),

        // Command line arguments: similar to user input
        IoSource::Args => TaintSet::from_builtins([
            TaintKind::SQLi,
            TaintKind::CMDi,
            TaintKind::PathTraversal,
            TaintKind::SSRF,
            TaintKind::LogInjection,
        ]),

        // Environment variables: can be set by attacker in some contexts
        IoSource::EnvVar(_) => TaintSet::from_builtins([
            TaintKind::CMDi,
            TaintKind::PathTraversal,
            TaintKind::SSRF,
            TaintKind::LogInjection,
        ]),

        // File input: content depends on file origin
        // Path itself may be tainted separately
        IoSource::FileInput(_) => TaintSet::from_builtins([
            TaintKind::XMLi,
            TaintKind::Deserialization,
            TaintKind::CodeInjection,
        ]),

        // Trusted sources: no taint
        IoSource::Random | IoSource::Clock => TaintSet::empty(),
    }
}

/// Returns the taints that an I/O sink is vulnerable to.
///
/// Different output sinks have different vulnerability profiles:
/// - Database sinks are vulnerable to SQL injection
/// - File output is vulnerable to path traversal
/// - Network output is vulnerable to SSRF
/// - Log output is vulnerable to log injection
///
/// If tainted data flows to a sink without proper sanitization
/// for these taint kinds, a vulnerability exists.
///
/// # Example
///
/// ```ignore
/// use brrr_repr::security::io_sink_requirements;
/// use brrr_repr::effects::IoSink;
///
/// let requirements = io_sink_requirements(&IoSink::Database(name));
/// assert!(requirements.contains(TaintKind::SQLi));
/// ```
#[must_use]
pub fn io_sink_requirements(sink: &IoSink) -> TaintSet {
    match sink {
        // Database sink: SQL injection is the primary concern
        IoSink::Database(_) => TaintSet::from_builtins([TaintKind::SQLi, TaintKind::LDAPi]),

        // File output: path traversal and code injection
        IoSink::FileOutput(_) => {
            TaintSet::from_builtins([TaintKind::PathTraversal, TaintKind::CodeInjection])
        }

        // Network output: SSRF and header injection
        IoSink::NetworkOut => TaintSet::from_builtins([
            TaintKind::SSRF,
            TaintKind::HeaderInjection,
            TaintKind::OpenRedirect,
        ]),

        // Log output: log injection
        IoSink::Log => TaintSet::from_builtins([TaintKind::LogInjection]),

        // Stdout/stderr: command injection if used in shell context
        IoSink::Stdout | IoSink::Stderr => {
            TaintSet::from_builtins([TaintKind::CMDi, TaintKind::XSS])
        }

        // Metrics: generally safe but could leak info
        IoSink::Metrics => TaintSet::empty(),
    }
}

/// Check if a source-to-sink flow is potentially vulnerable.
///
/// Returns the set of taints that flow from source to sink without
/// being handled. If the result is non-empty, there's a potential
/// vulnerability.
///
/// # Example
///
/// ```ignore
/// let vulnerable_taints = check_flow_vulnerability(
///     &IoSource::UserInput,
///     &IoSink::Database(db_name),
/// );
/// if !vulnerable_taints.is_empty() {
///     // Potential SQL injection!
/// }
/// ```
#[must_use]
pub fn check_flow_vulnerability(source: &IoSource, sink: &IoSink) -> TaintSet {
    let source_taints = io_source_taints(source);
    let sink_requirements = io_sink_requirements(sink);

    // Intersection: taints that source introduces AND sink is vulnerable to
    source_taints.intersection(&sink_requirements)
}

/// Remove taints from a set, returning a new set.
///
/// This is a functional version of `TaintSet::remove` for use in
/// sanitization contexts.
///
/// Maps to F*: `remove_taints : list taint_kind -> taint_set -> taint_set`
#[must_use]
pub fn remove_taints(to_remove: &[TaintKind], set: &TaintSet) -> TaintSet {
    let mut result = set.clone();
    result.remove(to_remove);
    result
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_has_all_variants() {
        assert_eq!(TaintKind::ALL.len(), 15);
    }

    #[test]
    fn test_web_common_subset() {
        for kind in TaintKind::WEB_COMMON {
            assert!(TaintKind::ALL.contains(kind));
        }
    }

    #[test]
    fn test_cwe_ids() {
        assert_eq!(TaintKind::SQLi.cwe_id(), 89);
        assert_eq!(TaintKind::XSS.cwe_id(), 79);
        assert_eq!(TaintKind::CMDi.cwe_id(), 78);
        assert_eq!(TaintKind::PathTraversal.cwe_id(), 22);
    }

    #[test]
    fn test_severity_ordering() {
        assert!(TaintKind::CMDi.severity_score() > TaintKind::XSS.severity_score());
        assert!(TaintKind::SQLi.severity_score() > TaintKind::LogInjection.severity_score());
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", TaintKind::SQLi), "SQL Injection");
        assert_eq!(format!("{}", TaintKind::XSS), "Cross-Site Scripting");
    }

    #[test]
    fn test_taint_set_operations() {
        let mut t1 = TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS]);
        let t2 = TaintSet::from_builtins([TaintKind::XSS, TaintKind::CMDi]);

        // Union
        let union = t1.union(&t2);
        assert!(union.contains(TaintKind::SQLi));
        assert!(union.contains(TaintKind::XSS));
        assert!(union.contains(TaintKind::CMDi));
        assert_eq!(union.len(), 3);

        // Intersection
        let intersection = t1.intersection(&t2);
        assert!(!intersection.contains(TaintKind::SQLi));
        assert!(intersection.contains(TaintKind::XSS));
        assert!(!intersection.contains(TaintKind::CMDi));
        assert_eq!(intersection.len(), 1);

        // Remove
        t1.remove(&[TaintKind::SQLi]);
        assert!(!t1.contains(TaintKind::SQLi));
        assert!(t1.contains(TaintKind::XSS));
    }

    #[test]
    fn test_taint_set_subset() {
        let t1 = TaintSet::from_builtins([TaintKind::SQLi]);
        let t2 = TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS]);
        let t3 = TaintSet::from_builtins([TaintKind::CMDi]);

        assert!(t1.is_subset(&t2));
        assert!(!t2.is_subset(&t1));
        assert!(!t1.is_subset(&t3));
        assert!(TaintSet::empty().is_subset(&t1));
    }

    #[test]
    fn test_taint_status_join() {
        let clean = TaintStatus::Clean;
        let tainted_sqli = TaintStatus::with_taint(TaintKind::SQLi);
        let tainted_xss = TaintStatus::with_taint(TaintKind::XSS);

        // Clean + Clean = Clean
        assert!(clean.join(&clean).is_clean());

        // Clean + Tainted = Tainted
        let joined = clean.join(&tainted_sqli);
        assert!(joined.is_tainted());
        assert!(joined.contains(TaintKind::SQLi));

        // Tainted + Tainted = Union
        let joined2 = tainted_sqli.join(&tainted_xss);
        assert!(joined2.contains(TaintKind::SQLi));
        assert!(joined2.contains(TaintKind::XSS));
    }

    #[test]
    fn test_taint_status_sanitize() {
        let tainted = TaintStatus::tainted(TaintSet::from_builtins([
            TaintKind::SQLi,
            TaintKind::XSS,
        ]));

        // Partial sanitization
        let partial = tainted.sanitize(&[TaintKind::SQLi]);
        assert!(partial.is_tainted());
        assert!(!partial.contains(TaintKind::SQLi));
        assert!(partial.contains(TaintKind::XSS));

        // Full sanitization
        let full = tainted.sanitize(&[TaintKind::SQLi, TaintKind::XSS]);
        assert!(full.is_clean());
    }

    #[test]
    fn test_tainted_wrapper() {
        let clean_val: Tainted<i32> = Tainted::clean(42);
        assert!(clean_val.is_clean());
        assert_eq!(*clean_val.as_ref(), 42);

        let tainted_val = Tainted::with_taint("user input", TaintKind::SQLi);
        assert!(tainted_val.is_tainted());

        // Map preserves taint
        let mapped = tainted_val.map(|s| s.len());
        assert!(mapped.is_tainted());
        assert_eq!(mapped.value, 10);
    }

    #[test]
    fn test_tainted_and_then() {
        let input = Tainted::with_taint("input", TaintKind::SQLi);

        let result = input.and_then(|s| Tainted::with_taint(s.to_uppercase(), TaintKind::XSS));

        assert!(result.status.contains(TaintKind::SQLi));
        assert!(result.status.contains(TaintKind::XSS));
    }

    #[test]
    fn test_empty_set_normalization() {
        let status = TaintStatus::tainted(TaintSet::empty());
        assert!(status.is_clean());
    }

    #[test]
    fn test_taint_enum() {
        let builtin = Taint::from(TaintKind::SQLi);
        assert!(builtin.is_builtin());
        assert_eq!(builtin.as_builtin(), Some(TaintKind::SQLi));

        let custom = Taint::Custom(CustomTaint(Spur::default()));
        assert!(!custom.is_builtin());
        assert!(custom.as_custom().is_some());
    }

    #[test]
    fn test_io_source_taints_user_input() {
        let taints = io_source_taints(&IoSource::UserInput);
        assert!(taints.contains(TaintKind::SQLi));
        assert!(taints.contains(TaintKind::XSS));
        assert!(taints.contains(TaintKind::CMDi));
        assert!(taints.contains(TaintKind::PathTraversal));
        assert!(!taints.is_empty());
    }

    #[test]
    fn test_io_source_taints_network() {
        let taints = io_source_taints(&IoSource::NetworkIn);
        assert!(taints.contains(TaintKind::SQLi));
        assert!(taints.contains(TaintKind::Deserialization));
        assert!(taints.contains(TaintKind::PrototypePollution));
    }

    #[test]
    fn test_io_source_taints_trusted() {
        let random_taints = io_source_taints(&IoSource::Random);
        assert!(random_taints.is_empty());

        let clock_taints = io_source_taints(&IoSource::Clock);
        assert!(clock_taints.is_empty());
    }

    #[test]
    fn test_io_sink_requirements_database() {
        let reqs = io_sink_requirements(&IoSink::Database(Spur::default()));
        assert!(reqs.contains(TaintKind::SQLi));
        assert!(reqs.contains(TaintKind::LDAPi));
        assert!(!reqs.contains(TaintKind::XSS));
    }

    #[test]
    fn test_io_sink_requirements_log() {
        let reqs = io_sink_requirements(&IoSink::Log);
        assert!(reqs.contains(TaintKind::LogInjection));
        assert!(!reqs.contains(TaintKind::SQLi));
    }

    #[test]
    fn test_check_flow_vulnerability() {
        // User input to database: SQLi is a concern
        let vuln = check_flow_vulnerability(&IoSource::UserInput, &IoSink::Database(Spur::default()));
        assert!(vuln.contains(TaintKind::SQLi));

        // User input to log: LogInjection is a concern
        let vuln2 = check_flow_vulnerability(&IoSource::UserInput, &IoSink::Log);
        assert!(vuln2.contains(TaintKind::LogInjection));

        // Random to database: no vulnerabilities (trusted source)
        let safe = check_flow_vulnerability(&IoSource::Random, &IoSink::Database(Spur::default()));
        assert!(safe.is_empty());
    }

    #[test]
    fn test_remove_taints_fn() {
        let original = TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS, TaintKind::CMDi]);
        let sanitized = remove_taints(&[TaintKind::SQLi, TaintKind::XSS], &original);

        assert!(!sanitized.contains(TaintKind::SQLi));
        assert!(!sanitized.contains(TaintKind::XSS));
        assert!(sanitized.contains(TaintKind::CMDi));

        // Original should be unchanged
        assert!(original.contains(TaintKind::SQLi));
    }
}
