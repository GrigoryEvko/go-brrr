//! SARIF (Static Analysis Results Interchange Format) output support.
//!
//! SARIF is a standard format for static analysis tool output, supported by
//! GitHub, GitLab, Azure DevOps, and many other CI/CD platforms.
//!
//! Specification: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use super::types::{Confidence, SecurityCategory, SecurityFinding, SecurityReport, Severity};

// =============================================================================
// SARIF Types (v2.1.0)
// =============================================================================

/// The top-level SARIF log object.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifLog {
    /// The SARIF specification version (always "2.1.0")
    #[serde(rename = "$schema")]
    pub schema: String,
    /// SARIF version
    pub version: String,
    /// Array of run objects
    pub runs: Vec<SarifRun>,
}

impl SarifLog {
    /// Create a new SARIF log with a single run.
    #[must_use]
    pub fn new(run: SarifRun) -> Self {
        Self {
            schema: "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json".to_string(),
            version: "2.1.0".to_string(),
            runs: vec![run],
        }
    }
}

/// A single analysis run.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifRun {
    /// The analysis tool that produced the results
    pub tool: SarifTool,
    /// The results of the analysis
    pub results: Vec<SarifResult>,
    /// Artifacts (files) analyzed
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub artifacts: Vec<SarifArtifact>,
    /// Invocation details
    #[serde(skip_serializing_if = "Option::is_none")]
    pub invocations: Option<Vec<SarifInvocation>>,
}

/// Tool information.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifTool {
    /// The tool driver (main component)
    pub driver: SarifToolComponent,
}

/// Tool component (driver or extension).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifToolComponent {
    /// Tool name
    pub name: String,
    /// Tool version
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    /// Semantic version
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_version: Option<String>,
    /// Tool information URI
    #[serde(skip_serializing_if = "Option::is_none")]
    pub information_uri: Option<String>,
    /// Rules defined by this tool
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rules: Vec<SarifReportingDescriptor>,
}

/// A rule/vulnerability descriptor.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReportingDescriptor {
    /// Rule ID (e.g., "SQLI-001")
    pub id: String,
    /// Short description
    #[serde(skip_serializing_if = "Option::is_none")]
    pub short_description: Option<SarifMessage>,
    /// Full description
    #[serde(skip_serializing_if = "Option::is_none")]
    pub full_description: Option<SarifMessage>,
    /// Help text with remediation guidance
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<SarifMessage>,
    /// Help URI
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help_uri: Option<String>,
    /// Default severity configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub default_configuration: Option<SarifReportingConfiguration>,
    /// Properties bag (for CWE, tags, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub properties: Option<SarifPropertyBag>,
}

/// Reporting configuration (severity level).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReportingConfiguration {
    /// Severity level
    pub level: SarifLevel,
    /// Whether this rule is enabled
    #[serde(skip_serializing_if = "Option::is_none")]
    pub enabled: Option<bool>,
}

/// SARIF severity level.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SarifLevel {
    /// Serious problem
    Error,
    /// Less serious problem
    Warning,
    /// Informational message
    Note,
    /// No level (used for suppressions)
    None,
}

impl From<Severity> for SarifLevel {
    fn from(sev: Severity) -> Self {
        match sev {
            Severity::Critical | Severity::High => Self::Error,
            Severity::Medium => Self::Warning,
            Severity::Low | Severity::Info => Self::Note,
        }
    }
}

/// A message (text or markdown).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifMessage {
    /// Plain text message
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    /// Markdown message
    #[serde(skip_serializing_if = "Option::is_none")]
    pub markdown: Option<String>,
}

impl SarifMessage {
    /// Create a plain text message.
    #[must_use]
    pub fn text(s: impl Into<String>) -> Self {
        Self {
            text: Some(s.into()),
            markdown: None,
        }
    }

    /// Create a markdown message.
    #[must_use]
    pub fn markdown(s: impl Into<String>) -> Self {
        Self {
            text: None,
            markdown: Some(s.into()),
        }
    }
}

/// A result (finding).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifResult {
    /// Rule ID
    pub rule_id: String,
    /// Rule index in the rules array
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_index: Option<usize>,
    /// Severity level
    pub level: SarifLevel,
    /// Message
    pub message: SarifMessage,
    /// Locations where the issue was found
    pub locations: Vec<SarifLocation>,
    /// Code flows (taint tracking paths)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub code_flows: Vec<SarifCodeFlow>,
    /// Related locations
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related_locations: Vec<SarifLocation>,
    /// Fix suggestions
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub fixes: Vec<SarifFix>,
    /// Fingerprints for tracking across runs
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub fingerprints: HashMap<String, String>,
    /// Properties bag
    #[serde(skip_serializing_if = "Option::is_none")]
    pub properties: Option<SarifPropertyBag>,
    /// Suppression info
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub suppressions: Vec<SarifSuppression>,
}

/// A location.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifLocation {
    /// Physical location in a file
    pub physical_location: SarifPhysicalLocation,
    /// Logical location (function name, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub logical_locations: Option<Vec<SarifLogicalLocation>>,
}

/// Physical location (file, region).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifPhysicalLocation {
    /// Artifact (file) location
    pub artifact_location: SarifArtifactLocation,
    /// Region within the file
    #[serde(skip_serializing_if = "Option::is_none")]
    pub region: Option<SarifRegion>,
    /// Context region (surrounding code)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context_region: Option<SarifRegion>,
}

/// File reference.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifArtifactLocation {
    /// URI (file path)
    pub uri: String,
    /// URI base ID (for relative paths)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uri_base_id: Option<String>,
    /// Index in the artifacts array
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<usize>,
}

/// A region within a file.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifRegion {
    /// Start line (1-indexed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_line: Option<usize>,
    /// Start column (1-indexed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_column: Option<usize>,
    /// End line (1-indexed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_line: Option<usize>,
    /// End column (1-indexed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_column: Option<usize>,
    /// Code snippet
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snippet: Option<SarifArtifactContent>,
}

/// Artifact content (code snippet).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifArtifactContent {
    /// Plain text content
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
    /// Binary content (base64)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binary: Option<String>,
}

/// Logical location (function, class, etc.).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifLogicalLocation {
    /// Name (e.g., function name)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Fully qualified name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fully_qualified_name: Option<String>,
    /// Kind (function, method, class, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
}

/// Code flow for taint tracking.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifCodeFlow {
    /// Thread flows
    pub thread_flows: Vec<SarifThreadFlow>,
}

/// Thread flow (sequence of locations).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifThreadFlow {
    /// Locations in order
    pub locations: Vec<SarifThreadFlowLocation>,
}

/// A location in a thread flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifThreadFlowLocation {
    /// Location
    pub location: SarifLocation,
    /// Importance
    #[serde(skip_serializing_if = "Option::is_none")]
    pub importance: Option<String>,
}

/// Fix suggestion.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifFix {
    /// Description of the fix
    pub description: SarifMessage,
    /// Artifact changes
    pub artifact_changes: Vec<SarifArtifactChange>,
}

/// Artifact change (file modification).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifArtifactChange {
    /// File to modify
    pub artifact_location: SarifArtifactLocation,
    /// Replacements to make
    pub replacements: Vec<SarifReplacement>,
}

/// Text replacement.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReplacement {
    /// Region to delete
    pub deleted_region: SarifRegion,
    /// Content to insert
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inserted_content: Option<SarifArtifactContent>,
}

/// An artifact (file).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifArtifact {
    /// File location
    pub location: SarifArtifactLocation,
    /// MIME type
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mime_type: Option<String>,
    /// Length in bytes
    #[serde(skip_serializing_if = "Option::is_none")]
    pub length: Option<usize>,
}

/// Invocation details.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifInvocation {
    /// Whether the run succeeded
    pub execution_successful: bool,
    /// Start time
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_time_utc: Option<String>,
    /// End time
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_time_utc: Option<String>,
    /// Working directory
    #[serde(skip_serializing_if = "Option::is_none")]
    pub working_directory: Option<SarifArtifactLocation>,
}

/// Property bag for custom properties.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifPropertyBag {
    /// CWE IDs
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub cwe: Vec<String>,
    /// Tags
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<String>,
    /// Security severity score (0.0-10.0 CVSS-like)
    #[serde(skip_serializing_if = "Option::is_none", rename = "security-severity")]
    pub security_severity: Option<String>,
    /// Confidence
    #[serde(skip_serializing_if = "Option::is_none")]
    pub confidence: Option<String>,
    /// Additional properties
    #[serde(flatten)]
    pub extra: HashMap<String, serde_json::Value>,
}

/// Suppression info.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifSuppression {
    /// Suppression kind
    pub kind: String,
    /// Justification
    #[serde(skip_serializing_if = "Option::is_none")]
    pub justification: Option<String>,
}

// =============================================================================
// Conversion from SecurityReport to SARIF
// =============================================================================

impl SecurityReport {
    /// Convert the report to SARIF format.
    #[must_use]
    pub fn to_sarif(&self) -> SarifLog {
        // Build rules from unique finding IDs
        let mut rules: Vec<SarifReportingDescriptor> = Vec::new();
        let mut rule_index_map: HashMap<String, usize> = HashMap::new();

        for finding in &self.findings {
            if !rule_index_map.contains_key(&finding.id) {
                rule_index_map.insert(finding.id.clone(), rules.len());
                rules.push(finding_to_rule(finding));
            }
        }

        // Build results
        let results: Vec<SarifResult> = self
            .findings
            .iter()
            .map(|f| finding_to_result(f, rule_index_map.get(&f.id).copied()))
            .collect();

        // Build artifacts from unique files
        let mut artifacts: Vec<SarifArtifact> = Vec::new();
        let mut seen_files: HashMap<String, usize> = HashMap::new();

        for finding in &self.findings {
            if !seen_files.contains_key(&finding.location.file) {
                seen_files.insert(finding.location.file.clone(), artifacts.len());
                artifacts.push(SarifArtifact {
                    location: SarifArtifactLocation {
                        uri: finding.location.file.clone(),
                        uri_base_id: Some("%SRCROOT%".to_string()),
                        index: Some(artifacts.len()),
                    },
                    mime_type: guess_mime_type(&finding.location.file),
                    length: None,
                });
            }
        }

        let tool = SarifTool {
            driver: SarifToolComponent {
                name: "brrr-security".to_string(),
                version: Some(self.scanner_version.clone()),
                semantic_version: Some(self.scanner_version.clone()),
                information_uri: Some(
                    "https://github.com/GrigoryEvko/go-brrr".to_string(),
                ),
                rules,
            },
        };

        let run = SarifRun {
            tool,
            results,
            artifacts,
            invocations: Some(vec![SarifInvocation {
                execution_successful: true,
                start_time_utc: Some(self.timestamp.clone()),
                end_time_utc: Some(self.timestamp.clone()),
                working_directory: None,
            }]),
        };

        SarifLog::new(run)
    }

    /// Serialize to SARIF JSON string.
    ///
    /// # Errors
    /// Returns an error if JSON serialization fails.
    pub fn to_sarif_json(&self) -> Result<String, serde_json::Error> {
        let sarif = self.to_sarif();
        serde_json::to_string_pretty(&sarif)
    }
}

/// Convert a finding to a SARIF rule descriptor.
fn finding_to_rule(finding: &SecurityFinding) -> SarifReportingDescriptor {
    let mut properties = SarifPropertyBag::default();

    if let Some(cwe) = finding.cwe_id {
        properties.cwe.push(format!("CWE-{cwe}"));
    }

    properties.security_severity = Some(format!("{:.1}", finding.severity.cvss_score()));

    // Add category tag
    let tag = match &finding.category {
        SecurityCategory::Injection(t) => format!("injection/{t:?}").to_lowercase(),
        SecurityCategory::SecretsExposure => "secrets".to_string(),
        SecurityCategory::WeakCrypto => "crypto".to_string(),
        SecurityCategory::UnsafeDeserialization => "deserialization".to_string(),
        SecurityCategory::ReDoS => "redos".to_string(),
        SecurityCategory::InsecureConfig => "config".to_string(),
        SecurityCategory::AuthIssue => "auth".to_string(),
        SecurityCategory::InfoDisclosure => "disclosure".to_string(),
        SecurityCategory::Other(s) => s.clone(),
    };
    properties.tags.push(tag);

    // Add OWASP tag if applicable
    if let Some(owasp) = finding.category.owasp_category() {
        properties.tags.push(owasp.to_string());
    }

    let help_uri = finding
        .cwe_id
        .map(|cwe| format!("https://cwe.mitre.org/data/definitions/{cwe}.html"));

    SarifReportingDescriptor {
        id: finding.id.clone(),
        short_description: Some(SarifMessage::text(&finding.title)),
        full_description: Some(SarifMessage::text(&finding.description)),
        help: if finding.remediation.is_empty() {
            None
        } else {
            Some(SarifMessage::markdown(&finding.remediation))
        },
        help_uri,
        default_configuration: Some(SarifReportingConfiguration {
            level: SarifLevel::from(finding.severity),
            enabled: Some(true),
        }),
        properties: Some(properties),
    }
}

/// Convert a finding to a SARIF result.
fn finding_to_result(finding: &SecurityFinding, rule_index: Option<usize>) -> SarifResult {
    let location = SarifLocation {
        physical_location: SarifPhysicalLocation {
            artifact_location: SarifArtifactLocation {
                uri: finding.location.file.clone(),
                uri_base_id: Some("%SRCROOT%".to_string()),
                index: None,
            },
            region: Some(SarifRegion {
                start_line: Some(finding.location.start_line),
                start_column: Some(finding.location.start_column),
                end_line: Some(finding.location.end_line),
                end_column: Some(finding.location.end_column),
                snippet: if finding.code_snippet.is_empty() {
                    None
                } else {
                    Some(SarifArtifactContent {
                        text: Some(finding.code_snippet.clone()),
                        binary: None,
                    })
                },
            }),
            context_region: None,
        },
        logical_locations: None,
    };

    let mut fingerprints = HashMap::new();
    fingerprints.insert(
        "primaryLocationLineHash".to_string(),
        finding.fingerprint(),
    );

    let mut properties = SarifPropertyBag::default();
    properties.confidence = Some(finding.confidence.to_string());

    // Add metadata as properties
    for (k, v) in &finding.metadata {
        properties
            .extra
            .insert(k.clone(), serde_json::Value::String(v.clone()));
    }

    let suppressions = if finding.suppressed {
        vec![SarifSuppression {
            kind: "inSource".to_string(),
            justification: Some("Suppressed via inline comment".to_string()),
        }]
    } else {
        Vec::new()
    };

    SarifResult {
        rule_id: finding.id.clone(),
        rule_index,
        level: SarifLevel::from(finding.severity),
        message: SarifMessage::text(&finding.description),
        locations: vec![location],
        code_flows: Vec::new(),
        related_locations: Vec::new(),
        fixes: Vec::new(),
        fingerprints,
        properties: Some(properties),
        suppressions,
    }
}

/// Guess MIME type from file extension.
fn guess_mime_type(path: &str) -> Option<String> {
    let ext = path.rsplit('.').next()?;
    let mime = match ext {
        "py" => "text/x-python",
        "js" => "text/javascript",
        "ts" => "text/typescript",
        "tsx" | "jsx" => "text/jsx",
        "rs" => "text/x-rust",
        "go" => "text/x-go",
        "java" => "text/x-java",
        "c" | "h" => "text/x-c",
        "cpp" | "cc" | "cxx" | "hpp" => "text/x-c++src",
        "rb" => "text/x-ruby",
        "php" => "text/x-php",
        _ => return None,
    };
    Some(mime.to_string())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::security::types::{InjectionType, Location};

    #[test]
    fn test_sarif_generation() {
        let finding = SecurityFinding::new(
            "SQLI-001",
            SecurityCategory::Injection(InjectionType::Sql),
            Severity::High,
            Confidence::High,
            Location::new("src/api.py", 42, 5, 42, 50),
            "SQL Injection in query",
            "User input is concatenated into SQL query without sanitization",
        )
        .with_remediation("Use parameterized queries")
        .with_code_snippet("cursor.execute(f\"SELECT * FROM users WHERE id = {user_id}\")");

        let report = SecurityReport::new(vec![finding], 10);
        let sarif = report.to_sarif();

        assert_eq!(sarif.version, "2.1.0");
        assert_eq!(sarif.runs.len(), 1);

        let run = &sarif.runs[0];
        assert_eq!(run.tool.driver.name, "brrr-security");
        assert_eq!(run.results.len(), 1);
        assert_eq!(run.tool.driver.rules.len(), 1);

        let result = &run.results[0];
        assert_eq!(result.rule_id, "SQLI-001");
        assert!(matches!(result.level, SarifLevel::Error));
    }

    #[test]
    fn test_sarif_json_output() {
        let finding = SecurityFinding::new(
            "CMD-001",
            SecurityCategory::Injection(InjectionType::Command),
            Severity::Critical,
            Confidence::High,
            Location::new("app.py", 10, 1, 10, 30),
            "Command Injection",
            "os.system called with user input",
        );

        let report = SecurityReport::new(vec![finding], 1);
        let json = report.to_sarif_json().expect("SARIF JSON serialization");

        assert!(json.contains("\"version\": \"2.1.0\""));
        assert!(json.contains("CMD-001"));
        assert!(json.contains("error")); // level
    }
}
