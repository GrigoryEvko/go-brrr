//! Unified security types for the security analysis module.
//!
//! This module provides common types used across all security analyzers,
//! enabling a unified API and consistent output format.

use std::collections::HashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

// =============================================================================
// Unified Severity and Confidence
// =============================================================================

/// Unified severity level for all security findings.
/// Follows standard vulnerability scoring conventions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Informational - may not be exploitable but worth reviewing
    Info,
    /// Low severity - limited impact or requires specific conditions
    Low,
    /// Medium severity - potential for significant impact
    Medium,
    /// High severity - likely exploitable with serious impact
    High,
    /// Critical - easily exploitable with severe consequences
    Critical,
}

impl Default for Severity {
    fn default() -> Self {
        Self::Low
    }
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Info => write!(f, "INFO"),
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
            Self::Critical => write!(f, "CRITICAL"),
        }
    }
}

impl std::str::FromStr for Severity {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "info" | "informational" => Ok(Self::Info),
            "low" => Ok(Self::Low),
            "medium" | "med" => Ok(Self::Medium),
            "high" => Ok(Self::High),
            "critical" | "crit" => Ok(Self::Critical),
            _ => Err(format!("Unknown severity: {s}")),
        }
    }
}

impl Severity {
    /// Returns the CVSS-like numeric score (0.0 - 10.0)
    #[must_use]
    pub const fn cvss_score(&self) -> f64 {
        match self {
            Self::Info => 0.0,
            Self::Low => 3.9,
            Self::Medium => 6.9,
            Self::High => 8.9,
            Self::Critical => 10.0,
        }
    }

    /// Check if this severity is at least as severe as `other`
    #[must_use]
    pub fn at_least(&self, other: Self) -> bool {
        *self >= other
    }
}

/// Confidence level for the detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Confidence {
    /// Low confidence - pattern match only, no data flow confirmation
    Low,
    /// Medium confidence - some data flow indicators but incomplete path
    Medium,
    /// High confidence - clear data flow from source to sink
    High,
}

impl Default for Confidence {
    fn default() -> Self {
        Self::Low
    }
}

impl std::fmt::Display for Confidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
        }
    }
}

impl std::str::FromStr for Confidence {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "low" => Ok(Self::Low),
            "medium" | "med" => Ok(Self::Medium),
            "high" => Ok(Self::High),
            _ => Err(format!("Unknown confidence: {s}")),
        }
    }
}

// =============================================================================
// Location Types
// =============================================================================

/// Unified location in source code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// File path (relative to project root)
    pub file: String,
    /// Start line number (1-indexed)
    pub start_line: usize,
    /// Start column number (1-indexed)
    pub start_column: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// End column number (1-indexed)
    pub end_column: usize,
}

impl Location {
    /// Create a new location from a file path and line/column info.
    #[must_use]
    pub fn new(
        file: impl Into<String>,
        start_line: usize,
        start_column: usize,
        end_line: usize,
        end_column: usize,
    ) -> Self {
        Self {
            file: file.into(),
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    /// Create a single-line location.
    #[must_use]
    pub fn single_line(file: impl Into<String>, line: usize, column: usize) -> Self {
        Self {
            file: file.into(),
            start_line: line,
            start_column: column,
            end_line: line,
            end_column: column,
        }
    }

    /// Make the path relative to a base directory.
    #[must_use]
    pub fn with_relative_path(mut self, base: &Path) -> Self {
        if let Ok(relative) = Path::new(&self.file).strip_prefix(base) {
            self.file = relative.display().to_string();
        }
        self
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.start_line, self.start_column)
    }
}

// =============================================================================
// Security Categories
// =============================================================================

/// Type of injection vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InjectionType {
    /// SQL Injection (CWE-89)
    Sql,
    /// Command Injection / OS Command Injection (CWE-78)
    Command,
    /// Cross-Site Scripting (CWE-79)
    Xss,
    /// Path Traversal / Directory Traversal (CWE-22)
    PathTraversal,
    /// Code Injection via eval/exec (CWE-94)
    Code,
    /// LDAP Injection (CWE-90)
    Ldap,
    /// XML Injection / XXE (CWE-91)
    Xml,
    /// Template Injection (CWE-1336)
    Template,
}

impl std::fmt::Display for InjectionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sql => write!(f, "SQL Injection"),
            Self::Command => write!(f, "Command Injection"),
            Self::Xss => write!(f, "Cross-Site Scripting (XSS)"),
            Self::PathTraversal => write!(f, "Path Traversal"),
            Self::Code => write!(f, "Code Injection"),
            Self::Ldap => write!(f, "LDAP Injection"),
            Self::Xml => write!(f, "XML Injection"),
            Self::Template => write!(f, "Template Injection"),
        }
    }
}

/// Category of security vulnerability.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "type", content = "subtype")]
pub enum SecurityCategory {
    /// Injection vulnerabilities (SQL, Command, XSS, Path Traversal, etc.)
    Injection(InjectionType),
    /// Secrets/credentials exposed in source code
    SecretsExposure,
    /// Weak or insecure cryptographic usage
    WeakCrypto,
    /// Unsafe deserialization (pickle, yaml.load, ObjectInputStream, etc.)
    UnsafeDeserialization,
    /// Regular expression denial of service
    ReDoS,
    /// Insecure configuration
    InsecureConfig,
    /// Authentication/authorization issues
    AuthIssue,
    /// Information disclosure
    InfoDisclosure,
    /// Other security issue
    Other(String),
}

impl std::fmt::Display for SecurityCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Injection(t) => write!(f, "{t}"),
            Self::SecretsExposure => write!(f, "Secrets Exposure"),
            Self::WeakCrypto => write!(f, "Weak Cryptography"),
            Self::UnsafeDeserialization => write!(f, "Unsafe Deserialization"),
            Self::ReDoS => write!(f, "ReDoS"),
            Self::InsecureConfig => write!(f, "Insecure Configuration"),
            Self::AuthIssue => write!(f, "Authentication Issue"),
            Self::InfoDisclosure => write!(f, "Information Disclosure"),
            Self::Other(s) => write!(f, "{s}"),
        }
    }
}

impl SecurityCategory {
    /// Get the CWE ID for this category (if applicable).
    #[must_use]
    pub fn cwe_id(&self) -> Option<u32> {
        match self {
            Self::Injection(InjectionType::Sql) => Some(89),
            Self::Injection(InjectionType::Command) => Some(78),
            Self::Injection(InjectionType::Xss) => Some(79),
            Self::Injection(InjectionType::PathTraversal) => Some(22),
            Self::Injection(InjectionType::Code) => Some(94),
            Self::Injection(InjectionType::Ldap) => Some(90),
            Self::Injection(InjectionType::Xml) => Some(91),
            Self::Injection(InjectionType::Template) => Some(1336),
            Self::SecretsExposure => Some(798), // Use of Hard-coded Credentials
            Self::WeakCrypto => Some(327),       // Broken Crypto
            Self::UnsafeDeserialization => Some(502),
            Self::ReDoS => Some(1333),
            Self::InsecureConfig => Some(16),
            Self::AuthIssue => Some(287),
            Self::InfoDisclosure => Some(200),
            Self::Other(_) => None,
        }
    }

    /// Get the OWASP Top 10 (2021) category if applicable.
    #[must_use]
    pub fn owasp_category(&self) -> Option<&'static str> {
        match self {
            Self::Injection(_) => Some("A03:2021 - Injection"),
            Self::SecretsExposure => Some("A07:2021 - Identification and Authentication Failures"),
            Self::WeakCrypto => Some("A02:2021 - Cryptographic Failures"),
            Self::UnsafeDeserialization => Some("A08:2021 - Software and Data Integrity Failures"),
            Self::InsecureConfig => Some("A05:2021 - Security Misconfiguration"),
            Self::AuthIssue => Some("A07:2021 - Identification and Authentication Failures"),
            Self::InfoDisclosure => Some("A01:2021 - Broken Access Control"),
            Self::ReDoS | Self::Other(_) => None,
        }
    }
}

// =============================================================================
// Unified Security Finding
// =============================================================================

/// A unified security finding that can represent any type of vulnerability.
///
/// This struct provides a consistent interface for all security analyzers,
/// enabling unified reporting, filtering, and output formatting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityFinding {
    /// Unique identifier for the finding type (e.g., "SQLI-001", "CMD-002")
    pub id: String,

    /// Category of the security issue
    pub category: SecurityCategory,

    /// Severity level
    pub severity: Severity,

    /// Confidence in the finding
    pub confidence: Confidence,

    /// Location in source code
    pub location: Location,

    /// Short title describing the issue
    pub title: String,

    /// Detailed description of the vulnerability
    pub description: String,

    /// CWE (Common Weakness Enumeration) reference ID
    pub cwe_id: Option<u32>,

    /// Suggested remediation/fix
    pub remediation: String,

    /// Code snippet showing the vulnerable code
    pub code_snippet: String,

    /// Additional metadata (analyzer-specific information)
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub metadata: HashMap<String, String>,

    /// Whether this finding has been suppressed via comment
    #[serde(default)]
    pub suppressed: bool,

    /// Hash for deduplication (based on location + category)
    #[serde(skip)]
    pub dedup_hash: u64,
}

impl SecurityFinding {
    /// Create a new security finding with required fields.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        category: SecurityCategory,
        severity: Severity,
        confidence: Confidence,
        location: Location,
        title: impl Into<String>,
        description: impl Into<String>,
    ) -> Self {
        let id = id.into();
        let title = title.into();
        let description = description.into();
        let cwe_id = category.cwe_id();

        // Compute deduplication hash
        let dedup_hash = {
            use std::hash::{Hash, Hasher};
            let mut hasher = rustc_hash::FxHasher::default();
            location.file.hash(&mut hasher);
            location.start_line.hash(&mut hasher);
            std::mem::discriminant(&category).hash(&mut hasher);
            hasher.finish()
        };

        Self {
            id,
            category,
            severity,
            confidence,
            location,
            title,
            description,
            cwe_id,
            remediation: String::new(),
            code_snippet: String::new(),
            metadata: HashMap::new(),
            suppressed: false,
            dedup_hash,
        }
    }

    /// Add remediation advice.
    #[must_use]
    pub fn with_remediation(mut self, remediation: impl Into<String>) -> Self {
        self.remediation = remediation.into();
        self
    }

    /// Add code snippet.
    #[must_use]
    pub fn with_code_snippet(mut self, snippet: impl Into<String>) -> Self {
        self.code_snippet = snippet.into();
        self
    }

    /// Add metadata key-value pair.
    #[must_use]
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Override the CWE ID.
    #[must_use]
    pub fn with_cwe(mut self, cwe_id: u32) -> Self {
        self.cwe_id = Some(cwe_id);
        self
    }

    /// Mark as suppressed.
    #[must_use]
    pub fn suppressed(mut self) -> Self {
        self.suppressed = true;
        self
    }

    /// Get a fingerprint for this finding (used for deduplication).
    #[must_use]
    pub fn fingerprint(&self) -> String {
        format!(
            "{}:{}:{}:{}",
            self.location.file,
            self.location.start_line,
            self.id,
            match &self.category {
                SecurityCategory::Injection(t) => format!("injection:{t:?}"),
                SecurityCategory::SecretsExposure => "secrets".to_string(),
                SecurityCategory::WeakCrypto => "crypto".to_string(),
                SecurityCategory::UnsafeDeserialization => "deser".to_string(),
                SecurityCategory::ReDoS => "redos".to_string(),
                SecurityCategory::InsecureConfig => "config".to_string(),
                SecurityCategory::AuthIssue => "auth".to_string(),
                SecurityCategory::InfoDisclosure => "disclosure".to_string(),
                SecurityCategory::Other(s) => format!("other:{s}"),
            }
        )
    }
}

impl PartialEq for SecurityFinding {
    fn eq(&self, other: &Self) -> bool {
        self.dedup_hash == other.dedup_hash && self.id == other.id
    }
}

impl Eq for SecurityFinding {}

impl std::hash::Hash for SecurityFinding {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.dedup_hash.hash(state);
        self.id.hash(state);
    }
}

// =============================================================================
// Scan Configuration
// =============================================================================

/// Configuration for security scanning.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    /// Minimum severity to report
    pub min_severity: Severity,

    /// Minimum confidence to report
    pub min_confidence: Confidence,

    /// Categories to scan (None = all)
    pub categories: Option<Vec<String>>,

    /// Categories to exclude
    pub exclude_categories: Vec<String>,

    /// File patterns to exclude
    pub exclude_patterns: Vec<String>,

    /// Whether to include suppressed findings in the report
    pub include_suppressed: bool,

    /// Whether to deduplicate findings
    pub deduplicate: bool,

    /// Language filter (None = all languages)
    pub language: Option<String>,

    /// Maximum number of files to scan (0 = unlimited)
    pub max_files: usize,

    /// Number of parallel workers (0 = auto)
    pub parallelism: usize,
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            min_severity: Severity::Low,
            min_confidence: Confidence::Low,
            categories: None,
            exclude_categories: Vec::new(),
            exclude_patterns: vec![
                "**/node_modules/**".to_string(),
                "**/.git/**".to_string(),
                "**/vendor/**".to_string(),
                "**/target/**".to_string(),
                "**/__pycache__/**".to_string(),
            ],
            include_suppressed: false,
            deduplicate: true,
            language: None,
            max_files: 0,
            parallelism: 0,
        }
    }
}

impl SecurityConfig {
    /// Create a config that scans all issues.
    #[must_use]
    pub fn all() -> Self {
        Self::default()
    }

    /// Create a config for CI/CD with stricter settings.
    #[must_use]
    pub fn ci() -> Self {
        Self {
            min_severity: Severity::Medium,
            min_confidence: Confidence::Medium,
            ..Self::default()
        }
    }

    /// Set minimum severity.
    #[must_use]
    pub fn with_min_severity(mut self, severity: Severity) -> Self {
        self.min_severity = severity;
        self
    }

    /// Set minimum confidence.
    #[must_use]
    pub fn with_min_confidence(mut self, confidence: Confidence) -> Self {
        self.min_confidence = confidence;
        self
    }

    /// Set language filter.
    #[must_use]
    pub fn with_language(mut self, language: impl Into<String>) -> Self {
        self.language = Some(language.into());
        self
    }

    /// Set categories to scan.
    #[must_use]
    pub fn with_categories(mut self, categories: Vec<String>) -> Self {
        self.categories = Some(categories);
        self
    }

    /// Check if a finding passes the filters.
    #[must_use]
    pub fn should_include(&self, finding: &SecurityFinding) -> bool {
        // Check severity
        if finding.severity < self.min_severity {
            return false;
        }

        // Check confidence
        if finding.confidence < self.min_confidence {
            return false;
        }

        // Check suppression
        if finding.suppressed && !self.include_suppressed {
            return false;
        }

        // Check category filter
        if let Some(ref categories) = self.categories {
            let cat_str = match &finding.category {
                SecurityCategory::Injection(t) => format!("injection:{t:?}").to_lowercase(),
                SecurityCategory::SecretsExposure => "secrets".to_string(),
                SecurityCategory::WeakCrypto => "crypto".to_string(),
                SecurityCategory::UnsafeDeserialization => "deserialization".to_string(),
                SecurityCategory::ReDoS => "redos".to_string(),
                SecurityCategory::InsecureConfig => "config".to_string(),
                SecurityCategory::AuthIssue => "auth".to_string(),
                SecurityCategory::InfoDisclosure => "disclosure".to_string(),
                SecurityCategory::Other(s) => s.to_lowercase(),
            };

            if !categories.iter().any(|c| cat_str.contains(&c.to_lowercase())) {
                return false;
            }
        }

        // Check exclusions
        for excl in &self.exclude_categories {
            let cat_str = match &finding.category {
                SecurityCategory::Injection(t) => format!("injection:{t:?}").to_lowercase(),
                cat => format!("{cat:?}").to_lowercase(),
            };
            if cat_str.contains(&excl.to_lowercase()) {
                return false;
            }
        }

        true
    }
}

// =============================================================================
// Scan Report
// =============================================================================

/// Summary statistics for a security scan.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ScanSummary {
    /// Total number of findings
    pub total_findings: usize,
    /// Number of findings by severity
    pub by_severity: HashMap<String, usize>,
    /// Number of findings by category
    pub by_category: HashMap<String, usize>,
    /// Number of files scanned
    pub files_scanned: usize,
    /// Number of files with findings
    pub files_with_findings: usize,
    /// Number of suppressed findings
    pub suppressed_count: usize,
    /// Number of duplicates removed
    pub duplicates_removed: usize,
    /// Scan duration in milliseconds
    pub scan_duration_ms: u64,
}

impl ScanSummary {
    /// Create a summary from a list of findings.
    #[must_use]
    pub fn from_findings(findings: &[SecurityFinding], files_scanned: usize) -> Self {
        let mut by_severity = HashMap::new();
        let mut by_category = HashMap::new();
        let mut files_with_findings = std::collections::HashSet::new();
        let mut suppressed_count = 0;

        for finding in findings {
            // Count by severity
            *by_severity
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;

            // Count by category
            let cat_name = match &finding.category {
                SecurityCategory::Injection(t) => format!("{t}"),
                cat => format!("{cat}"),
            };
            *by_category.entry(cat_name).or_insert(0) += 1;

            // Track files
            files_with_findings.insert(&finding.location.file);

            // Count suppressed
            if finding.suppressed {
                suppressed_count += 1;
            }
        }

        Self {
            total_findings: findings.len(),
            by_severity,
            by_category,
            files_scanned,
            files_with_findings: files_with_findings.len(),
            suppressed_count,
            duplicates_removed: 0,
            scan_duration_ms: 0,
        }
    }
}

/// Result of a security scan.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityReport {
    /// All findings (after filtering)
    pub findings: Vec<SecurityFinding>,
    /// Summary statistics
    pub summary: ScanSummary,
    /// Version of the scanner
    pub scanner_version: String,
    /// Timestamp of the scan
    pub timestamp: String,
    /// Configuration used
    #[serde(skip_serializing_if = "Option::is_none")]
    pub config: Option<SecurityConfig>,
}

impl SecurityReport {
    /// Create a new security report.
    #[must_use]
    pub fn new(findings: Vec<SecurityFinding>, files_scanned: usize) -> Self {
        let summary = ScanSummary::from_findings(&findings, files_scanned);
        Self {
            findings,
            summary,
            scanner_version: env!("CARGO_PKG_VERSION").to_string(),
            timestamp: chrono_lite_timestamp(),
            config: None,
        }
    }

    /// Check if the scan found any high/critical issues.
    #[must_use]
    pub fn has_critical_findings(&self) -> bool {
        self.findings
            .iter()
            .any(|f| f.severity >= Severity::High && !f.suppressed)
    }

    /// Get the exit code for CI/CD (0 = pass, 1 = fail)
    #[must_use]
    pub fn exit_code(&self, fail_on: Severity) -> i32 {
        if self
            .findings
            .iter()
            .any(|f| f.severity >= fail_on && !f.suppressed)
        {
            1
        } else {
            0
        }
    }
}

/// Simple timestamp without chrono dependency.
fn chrono_lite_timestamp() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = duration.as_secs();
    // Convert to basic ISO format
    let days_since_epoch = secs / 86400;
    let years = 1970 + days_since_epoch / 365;
    format!("{years}-01-01T00:00:00Z")
}

// =============================================================================
// Suppression Comment Parsing
// =============================================================================

/// Check if a line contains a suppression comment for a finding ID.
#[must_use]
pub fn is_suppressed(line: &str, finding_id: &str) -> bool {
    // Support various comment formats:
    // # brrr-ignore: SQLI-001
    // // brrr-ignore: SQLI-001
    // /* brrr-ignore: SQLI-001 */
    // # noqa: SQLI-001
    // # nosec SQLI-001

    let patterns = [
        "brrr-ignore:",
        "brrr-disable:",
        "security-ignore:",
        "nosec",
        "noqa:",
    ];

    let lower = line.to_lowercase();
    for pattern in patterns {
        if let Some(idx) = lower.find(pattern) {
            let rest = &line[idx + pattern.len()..].trim();
            // Check if the finding ID is mentioned
            if rest.contains(finding_id) || rest.contains(&finding_id.to_lowercase()) {
                return true;
            }
            // Also support "all" to suppress all findings on this line
            if rest.starts_with("all") || rest.is_empty() {
                return true;
            }
        }
    }

    false
}

/// Check surrounding lines for suppression comments.
#[must_use]
pub fn check_suppression(source: &str, line_number: usize, finding_id: &str) -> bool {
    let lines: Vec<&str> = source.lines().collect();

    // Check the line itself
    if let Some(line) = lines.get(line_number.saturating_sub(1)) {
        if is_suppressed(line, finding_id) {
            return true;
        }
    }

    // Check the previous line (common pattern)
    if line_number > 1 {
        if let Some(prev_line) = lines.get(line_number.saturating_sub(2)) {
            if is_suppressed(prev_line, finding_id) {
                return true;
            }
        }
    }

    false
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Critical > Severity::High);
        assert!(Severity::High > Severity::Medium);
        assert!(Severity::Medium > Severity::Low);
        assert!(Severity::Low > Severity::Info);
    }

    #[test]
    fn test_severity_from_str() {
        assert_eq!("critical".parse::<Severity>().unwrap(), Severity::Critical);
        assert_eq!("HIGH".parse::<Severity>().unwrap(), Severity::High);
        assert_eq!("med".parse::<Severity>().unwrap(), Severity::Medium);
    }

    #[test]
    fn test_cwe_mapping() {
        assert_eq!(
            SecurityCategory::Injection(InjectionType::Sql).cwe_id(),
            Some(89)
        );
        assert_eq!(
            SecurityCategory::Injection(InjectionType::Command).cwe_id(),
            Some(78)
        );
        assert_eq!(SecurityCategory::UnsafeDeserialization.cwe_id(), Some(502));
    }

    #[test]
    fn test_suppression_detection() {
        assert!(is_suppressed("# brrr-ignore: SQLI-001", "SQLI-001"));
        assert!(is_suppressed("// brrr-ignore: SQLI-001", "SQLI-001"));
        assert!(is_suppressed("# nosec SQLI-001", "SQLI-001"));
        assert!(!is_suppressed("# regular comment", "SQLI-001"));
    }

    #[test]
    fn test_finding_fingerprint() {
        let finding = SecurityFinding::new(
            "SQLI-001",
            SecurityCategory::Injection(InjectionType::Sql),
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "SQL Injection",
            "User input in SQL query",
        );

        let fingerprint = finding.fingerprint();
        assert!(fingerprint.contains("test.py"));
        assert!(fingerprint.contains("10"));
        assert!(fingerprint.contains("SQLI-001"));
    }
}
