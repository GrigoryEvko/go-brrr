//! SARIF (Static Analysis Results Interchange Format) output support.
//!
//! SARIF is a standard format for static analysis tool output, supported by
//! GitHub, GitLab, Azure DevOps, and many other CI/CD platforms.
//!
//! Specification: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
//!
//! # Features
//!
//! - Full SARIF v2.1.0 compliance
//! - Comprehensive rule definitions with CWE/OWASP mappings
//! - Code flows for taint tracking visualization
//! - Fix suggestions for deterministic remediation
//! - Fingerprinting for tracking across runs
//! - Suppression support
//!
//! # Usage
//!
//! ```ignore
//! use go_brrr::security::{scan_security, SecurityConfig};
//!
//! let report = scan_security("./src", &SecurityConfig::default())?;
//!
//! // Output to stdout
//! println!("{}", report.to_sarif_json()?);
//!
//! // Write to file
//! go_brrr::security::sarif::write_sarif(&report.to_sarif(), "results.sarif")?;
//! ```

use std::collections::HashMap;
use std::io::Write;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::taint::types::{PropagationStep, TaintedValue};
use super::types::{InjectionType, SecurityCategory, SecurityFinding, SecurityReport, Severity};

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

impl Default for SarifLog {
    fn default() -> Self {
        Self {
            schema: "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json".to_string(),
            version: "2.1.0".to_string(),
            runs: Vec::new(),
        }
    }
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

    /// Add a run to the log.
    pub fn add_run(&mut self, run: SarifRun) {
        self.runs.push(run);
    }

    /// Serialize to JSON string.
    ///
    /// # Errors
    /// Returns an error if JSON serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Serialize to compact JSON string (no pretty printing).
    ///
    /// # Errors
    /// Returns an error if JSON serialization fails.
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
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
    /// Original URI base IDs for path resolution
    #[serde(skip_serializing_if = "Option::is_none")]
    pub original_uri_base_ids: Option<HashMap<String, SarifArtifactLocation>>,
}

/// Tool information.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifTool {
    /// The tool driver (main component)
    pub driver: SarifToolComponent,
    /// Tool extensions (plugins)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub extensions: Vec<SarifToolComponent>,
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
    /// Organization
    #[serde(skip_serializing_if = "Option::is_none")]
    pub organization: Option<String>,
    /// Full name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub full_name: Option<String>,
    /// Rules defined by this tool
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rules: Vec<SarifReportingDescriptor>,
    /// Notifications (for warnings/errors about the scan itself)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub notifications: Vec<SarifReportingDescriptor>,
}

/// A rule/vulnerability descriptor.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReportingDescriptor {
    /// Rule ID (e.g., "SQLI-001")
    pub id: String,
    /// Human-readable name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Short description
    #[serde(skip_serializing_if = "Option::is_none")]
    pub short_description: Option<SarifMessage>,
    /// Full description
    #[serde(skip_serializing_if = "Option::is_none")]
    pub full_description: Option<SarifMessage>,
    /// Help text with remediation guidance
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<SarifMultiformatMessageString>,
    /// Help URI
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help_uri: Option<String>,
    /// Default severity configuration
    #[serde(skip_serializing_if = "Option::is_none")]
    pub default_configuration: Option<SarifReportingConfiguration>,
    /// Properties bag (for CWE, tags, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub properties: Option<SarifPropertyBag>,
    /// Relationships to other rules/taxonomies
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub relationships: Vec<SarifReportingDescriptorRelationship>,
}

/// Relationship to another reporting descriptor (e.g., CWE taxonomy).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReportingDescriptorRelationship {
    /// Target descriptor reference
    pub target: SarifReportingDescriptorReference,
    /// Kinds of relationship (e.g., "superset", "relevant")
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub kinds: Vec<String>,
}

/// Reference to a reporting descriptor.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifReportingDescriptorReference {
    /// Descriptor ID
    pub id: String,
    /// Tool component index
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_component: Option<SarifToolComponentReference>,
}

/// Reference to a tool component.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifToolComponentReference {
    /// Component name
    pub name: String,
    /// Component index
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<usize>,
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
    /// Rank (0.0 to 100.0)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rank: Option<f64>,
}

/// SARIF severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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
    /// Message ID for localization
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// Arguments for message format strings
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<String>,
}

impl SarifMessage {
    /// Create a plain text message.
    #[must_use]
    pub fn text(s: impl Into<String>) -> Self {
        Self {
            text: Some(s.into()),
            markdown: None,
            id: None,
            arguments: Vec::new(),
        }
    }

    /// Create a markdown message.
    #[must_use]
    pub fn markdown(s: impl Into<String>) -> Self {
        Self {
            text: None,
            markdown: Some(s.into()),
            id: None,
            arguments: Vec::new(),
        }
    }

    /// Create a message with both text and markdown.
    #[must_use]
    pub fn both(text: impl Into<String>, markdown: impl Into<String>) -> Self {
        Self {
            text: Some(text.into()),
            markdown: Some(markdown.into()),
            id: None,
            arguments: Vec::new(),
        }
    }
}

/// Multiformat message string (for help text).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifMultiformatMessageString {
    /// Plain text content
    pub text: String,
    /// Markdown content
    #[serde(skip_serializing_if = "Option::is_none")]
    pub markdown: Option<String>,
}

impl SarifMultiformatMessageString {
    /// Create with text only.
    #[must_use]
    pub fn text(s: impl Into<String>) -> Self {
        Self {
            text: s.into(),
            markdown: None,
        }
    }

    /// Create with both text and markdown.
    #[must_use]
    pub fn with_markdown(text: impl Into<String>, markdown: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            markdown: Some(markdown.into()),
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
    /// Severity level (overrides rule default)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub level: Option<SarifLevel>,
    /// Kind of result
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
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
    /// Partial fingerprints
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub partial_fingerprints: HashMap<String, String>,
    /// Properties bag
    #[serde(skip_serializing_if = "Option::is_none")]
    pub properties: Option<SarifPropertyBag>,
    /// Suppression info
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub suppressions: Vec<SarifSuppression>,
    /// Hosted viewer URI
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hosted_viewer_uri: Option<String>,
    /// Work item URIs
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub work_item_uris: Vec<String>,
}

/// A location.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifLocation {
    /// Unique ID for this location (for references)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<i32>,
    /// Physical location in a file
    #[serde(skip_serializing_if = "Option::is_none")]
    pub physical_location: Option<SarifPhysicalLocation>,
    /// Logical location (function name, etc.)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub logical_locations: Vec<SarifLogicalLocation>,
    /// Message for this location
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<SarifMessage>,
}

impl SarifLocation {
    /// Create from physical location only.
    #[must_use]
    pub fn physical(loc: SarifPhysicalLocation) -> Self {
        Self {
            id: None,
            physical_location: Some(loc),
            logical_locations: Vec::new(),
            message: None,
        }
    }

    /// Create with message.
    #[must_use]
    pub fn with_message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(SarifMessage::text(msg));
        self
    }

    /// Create with ID.
    #[must_use]
    pub fn with_id(mut self, id: i32) -> Self {
        self.id = Some(id);
        self
    }
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uri: Option<String>,
    /// URI base ID (for relative paths)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uri_base_id: Option<String>,
    /// Index in the artifacts array
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<usize>,
    /// Description
    #[serde(skip_serializing_if = "Option::is_none")]
    pub description: Option<SarifMessage>,
}

impl SarifArtifactLocation {
    /// Create from URI.
    #[must_use]
    pub fn from_uri(uri: impl Into<String>) -> Self {
        Self {
            uri: Some(uri.into()),
            uri_base_id: Some("%SRCROOT%".to_string()),
            index: None,
            description: None,
        }
    }

    /// Create from URI with base ID.
    #[must_use]
    pub fn from_uri_with_base(uri: impl Into<String>, base_id: impl Into<String>) -> Self {
        Self {
            uri: Some(uri.into()),
            uri_base_id: Some(base_id.into()),
            index: None,
            description: None,
        }
    }
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
    /// Character offset
    #[serde(skip_serializing_if = "Option::is_none")]
    pub char_offset: Option<usize>,
    /// Character length
    #[serde(skip_serializing_if = "Option::is_none")]
    pub char_length: Option<usize>,
    /// Byte offset
    #[serde(skip_serializing_if = "Option::is_none")]
    pub byte_offset: Option<usize>,
    /// Byte length
    #[serde(skip_serializing_if = "Option::is_none")]
    pub byte_length: Option<usize>,
    /// Code snippet
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snippet: Option<SarifArtifactContent>,
    /// Message for this region
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<SarifMessage>,
}

impl SarifRegion {
    /// Create a region from line/column info.
    #[must_use]
    pub fn from_lines(
        start_line: usize,
        start_col: usize,
        end_line: usize,
        end_col: usize,
    ) -> Self {
        Self {
            start_line: Some(start_line),
            start_column: Some(start_col),
            end_line: Some(end_line),
            end_column: Some(end_col),
            char_offset: None,
            char_length: None,
            byte_offset: None,
            byte_length: None,
            snippet: None,
            message: None,
        }
    }

    /// Add a code snippet.
    #[must_use]
    pub fn with_snippet(mut self, text: impl Into<String>) -> Self {
        self.snippet = Some(SarifArtifactContent {
            text: Some(text.into()),
            binary: None,
            rendered: None,
        });
        self
    }
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
    /// Rendered content (for rich display)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rendered: Option<SarifMultiformatMessageString>,
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
    /// Decorated name (mangled)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub decorated_name: Option<String>,
    /// Kind (function, method, class, namespace, etc.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    /// Parent index
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_index: Option<i32>,
}

/// Code flow for taint tracking.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifCodeFlow {
    /// Message describing the code flow
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<SarifMessage>,
    /// Thread flows
    pub thread_flows: Vec<SarifThreadFlow>,
}

impl SarifCodeFlow {
    /// Create a code flow from a single thread flow.
    #[must_use]
    pub fn single(thread_flow: SarifThreadFlow) -> Self {
        Self {
            message: None,
            thread_flows: vec![thread_flow],
        }
    }

    /// Create with message.
    #[must_use]
    pub fn with_message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(SarifMessage::text(msg));
        self
    }
}

/// Thread flow (sequence of locations).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifThreadFlow {
    /// Thread ID
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    /// Message describing the thread flow
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<SarifMessage>,
    /// Locations in order
    pub locations: Vec<SarifThreadFlowLocation>,
}

impl SarifThreadFlow {
    /// Create a new thread flow with locations.
    #[must_use]
    pub fn new(locations: Vec<SarifThreadFlowLocation>) -> Self {
        Self {
            id: None,
            message: None,
            locations,
        }
    }
}

/// A location in a thread flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifThreadFlowLocation {
    /// Location
    pub location: SarifLocation,
    /// Index in the execution order (0-based)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub execution_order: Option<i32>,
    /// Importance (essential, important, unimportant)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub importance: Option<String>,
    /// Nesting level
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nesting_level: Option<i32>,
    /// State changes
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub state: HashMap<String, SarifMultiformatMessageString>,
}

impl SarifThreadFlowLocation {
    /// Create from location.
    #[must_use]
    pub fn new(location: SarifLocation) -> Self {
        Self {
            location,
            execution_order: None,
            importance: None,
            nesting_level: None,
            state: HashMap::new(),
        }
    }

    /// Set importance.
    #[must_use]
    pub fn with_importance(mut self, importance: impl Into<String>) -> Self {
        self.importance = Some(importance.into());
        self
    }

    /// Set execution order.
    #[must_use]
    pub fn with_execution_order(mut self, order: i32) -> Self {
        self.execution_order = Some(order);
        self
    }
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

impl SarifFix {
    /// Create a fix with a single replacement.
    #[must_use]
    pub fn single_replacement(
        description: impl Into<String>,
        file: impl Into<String>,
        region: SarifRegion,
        replacement_text: impl Into<String>,
    ) -> Self {
        Self {
            description: SarifMessage::text(description),
            artifact_changes: vec![SarifArtifactChange {
                artifact_location: SarifArtifactLocation::from_uri(file),
                replacements: vec![SarifReplacement {
                    deleted_region: region,
                    inserted_content: Some(SarifArtifactContent {
                        text: Some(replacement_text.into()),
                        binary: None,
                        rendered: None,
                    }),
                }],
            }],
        }
    }
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
    pub length: Option<i64>,
    /// Source language
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_language: Option<String>,
    /// Hashes for integrity
    #[serde(skip_serializing_if = "HashMap::is_empty")]
    pub hashes: HashMap<String, String>,
    /// Encoding
    #[serde(skip_serializing_if = "Option::is_none")]
    pub encoding: Option<String>,
    /// Roles (analysisTarget, resultFile, etc.)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub roles: Vec<String>,
}

/// Invocation details.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifInvocation {
    /// Whether the run succeeded
    pub execution_successful: bool,
    /// Command line
    #[serde(skip_serializing_if = "Option::is_none")]
    pub command_line: Option<String>,
    /// Arguments
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<String>,
    /// Start time
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_time_utc: Option<String>,
    /// End time
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_time_utc: Option<String>,
    /// Working directory
    #[serde(skip_serializing_if = "Option::is_none")]
    pub working_directory: Option<SarifArtifactLocation>,
    /// Exit code
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit_code: Option<i32>,
    /// Process ID
    #[serde(skip_serializing_if = "Option::is_none")]
    pub process_id: Option<i32>,
    /// Machine name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub machine: Option<String>,
    /// Account name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub account: Option<String>,
    /// Tool execution notifications
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tool_execution_notifications: Vec<SarifNotification>,
    /// Tool configuration notifications
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tool_configuration_notifications: Vec<SarifNotification>,
}

/// A notification (warning/error about the scan itself).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifNotification {
    /// Descriptor ID
    #[serde(skip_serializing_if = "Option::is_none")]
    pub descriptor: Option<SarifReportingDescriptorReference>,
    /// Message
    pub message: SarifMessage,
    /// Level
    #[serde(skip_serializing_if = "Option::is_none")]
    pub level: Option<SarifLevel>,
    /// Exception
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exception: Option<SarifException>,
}

/// Exception information.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifException {
    /// Exception kind/type
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    /// Exception message
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// Stack trace
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stack: Option<SarifStack>,
    /// Inner exceptions
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub inner_exceptions: Vec<SarifException>,
}

/// Stack trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifStack {
    /// Frames
    pub frames: Vec<SarifStackFrame>,
    /// Message
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<SarifMessage>,
}

/// Stack frame.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifStackFrame {
    /// Location
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SarifLocation>,
    /// Module name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    /// Thread ID
    #[serde(skip_serializing_if = "Option::is_none")]
    pub thread_id: Option<i32>,
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
    /// Precision (very-high, high, medium, low)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub precision: Option<String>,
    /// Problem severity
    #[serde(skip_serializing_if = "Option::is_none")]
    pub problem_severity: Option<String>,
    /// Additional properties
    #[serde(flatten)]
    pub extra: HashMap<String, serde_json::Value>,
}

/// Suppression info.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SarifSuppression {
    /// Suppression kind (inSource, external)
    pub kind: String,
    /// Suppression state (accepted, underReview, rejected)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub state: Option<String>,
    /// Justification
    #[serde(skip_serializing_if = "Option::is_none")]
    pub justification: Option<String>,
    /// Location of suppression comment
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SarifLocation>,
}

// =============================================================================
// Rule Registry
// =============================================================================

/// Standard rule IDs for security findings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SecurityRuleId {
    // SQL Injection
    SqliConcatenation,
    SqliFstring,
    SqliFormat,
    SqliUnsafeExecute,
    // Command Injection
    CmdiOsSystem,
    CmdiSubprocess,
    CmdiExec,
    CmdiShell,
    // XSS
    XssDomManipulation,
    XssInnerHtml,
    XssDocWrite,
    XssUnsafeRender,
    // Path Traversal
    PathJoinUser,
    PathOpenUser,
    PathReadUser,
    PathWriteUser,
    // Secrets
    SecretApiKey,
    SecretPassword,
    SecretToken,
    SecretPrivateKey,
    SecretAwsKey,
    SecretGeneric,
    // Crypto
    CryptoWeakHash,
    CryptoWeakCipher,
    CryptoHardcodedKey,
    CryptoInsecureRandom,
    CryptoEcbMode,
    // Deserialization
    DeserPickle,
    DeserYaml,
    DeserJson,
    DeserXml,
    // ReDoS
    RedosExponential,
    RedosPolynomial,
    RedosNested,
    // SSRF
    SsrfHttpRequest,
    SsrfUrlFetch,
    SsrfSocket,
    // Log Injection
    LogiCrlf,
    LogiFormatString,
    // Header Injection
    HdriCrlf,
    HdriCookie,
    HdriRedirect,
    // Template Injection
    SstiJinja,
    SstiMako,
    SstiFreemarker,
    SstiGeneric,
    // Other
    Other,
}

impl SecurityRuleId {
    /// Get the string representation of the rule ID.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::SqliConcatenation => "SQLI-001",
            Self::SqliFstring => "SQLI-002",
            Self::SqliFormat => "SQLI-003",
            Self::SqliUnsafeExecute => "SQLI-004",
            Self::CmdiOsSystem => "CMDI-001",
            Self::CmdiSubprocess => "CMDI-002",
            Self::CmdiExec => "CMDI-003",
            Self::CmdiShell => "CMDI-004",
            Self::XssDomManipulation => "XSS-001",
            Self::XssInnerHtml => "XSS-002",
            Self::XssDocWrite => "XSS-003",
            Self::XssUnsafeRender => "XSS-004",
            Self::PathJoinUser => "PATH-001",
            Self::PathOpenUser => "PATH-002",
            Self::PathReadUser => "PATH-003",
            Self::PathWriteUser => "PATH-004",
            Self::SecretApiKey => "SECRET-001",
            Self::SecretPassword => "SECRET-002",
            Self::SecretToken => "SECRET-003",
            Self::SecretPrivateKey => "SECRET-004",
            Self::SecretAwsKey => "SECRET-005",
            Self::SecretGeneric => "SECRET-006",
            Self::CryptoWeakHash => "CRYPTO-001",
            Self::CryptoWeakCipher => "CRYPTO-002",
            Self::CryptoHardcodedKey => "CRYPTO-003",
            Self::CryptoInsecureRandom => "CRYPTO-004",
            Self::CryptoEcbMode => "CRYPTO-005",
            Self::DeserPickle => "DESER-001",
            Self::DeserYaml => "DESER-002",
            Self::DeserJson => "DESER-003",
            Self::DeserXml => "DESER-004",
            Self::RedosExponential => "REDOS-001",
            Self::RedosPolynomial => "REDOS-002",
            Self::RedosNested => "REDOS-003",
            Self::SsrfHttpRequest => "SSRF-001",
            Self::SsrfUrlFetch => "SSRF-002",
            Self::SsrfSocket => "SSRF-003",
            Self::LogiCrlf => "LOGI-001",
            Self::LogiFormatString => "LOGI-002",
            Self::HdriCrlf => "HDRI-001",
            Self::HdriCookie => "HDRI-002",
            Self::HdriRedirect => "HDRI-003",
            Self::SstiJinja => "SSTI-001",
            Self::SstiMako => "SSTI-002",
            Self::SstiFreemarker => "SSTI-003",
            Self::SstiGeneric => "SSTI-004",
            Self::Other => "OTHER-001",
        }
    }

    /// Get the CWE ID for this rule.
    #[must_use]
    pub fn cwe_id(&self) -> Option<u32> {
        match self {
            Self::SqliConcatenation
            | Self::SqliFstring
            | Self::SqliFormat
            | Self::SqliUnsafeExecute => Some(89),
            Self::CmdiOsSystem | Self::CmdiSubprocess | Self::CmdiExec | Self::CmdiShell => {
                Some(78)
            }
            Self::XssDomManipulation
            | Self::XssInnerHtml
            | Self::XssDocWrite
            | Self::XssUnsafeRender => Some(79),
            Self::PathJoinUser | Self::PathOpenUser | Self::PathReadUser | Self::PathWriteUser => {
                Some(22)
            }
            Self::SecretApiKey
            | Self::SecretPassword
            | Self::SecretToken
            | Self::SecretPrivateKey
            | Self::SecretAwsKey
            | Self::SecretGeneric => Some(798),
            Self::CryptoWeakHash => Some(328),
            Self::CryptoWeakCipher => Some(327),
            Self::CryptoHardcodedKey => Some(321),
            Self::CryptoInsecureRandom => Some(330),
            Self::CryptoEcbMode => Some(327),
            Self::DeserPickle | Self::DeserYaml | Self::DeserJson | Self::DeserXml => Some(502),
            Self::RedosExponential | Self::RedosPolynomial | Self::RedosNested => Some(1333),
            Self::SsrfHttpRequest | Self::SsrfUrlFetch | Self::SsrfSocket => Some(918),
            Self::LogiCrlf | Self::LogiFormatString => Some(117),
            Self::HdriCrlf | Self::HdriCookie | Self::HdriRedirect => Some(113),
            Self::SstiJinja | Self::SstiMako | Self::SstiFreemarker | Self::SstiGeneric => {
                Some(1336)
            }
            Self::Other => None,
        }
    }

    /// Get the rule name.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::SqliConcatenation => "SQL Injection via String Concatenation",
            Self::SqliFstring => "SQL Injection via F-String",
            Self::SqliFormat => "SQL Injection via Format String",
            Self::SqliUnsafeExecute => "SQL Injection via Unsafe Execute",
            Self::CmdiOsSystem => "Command Injection via os.system()",
            Self::CmdiSubprocess => "Command Injection via subprocess",
            Self::CmdiExec => "Command Injection via exec()",
            Self::CmdiShell => "Command Injection via Shell Execution",
            Self::XssDomManipulation => "XSS via DOM Manipulation",
            Self::XssInnerHtml => "XSS via innerHTML",
            Self::XssDocWrite => "XSS via document.write()",
            Self::XssUnsafeRender => "XSS via Unsafe Rendering",
            Self::PathJoinUser => "Path Traversal via os.path.join()",
            Self::PathOpenUser => "Path Traversal via open()",
            Self::PathReadUser => "Path Traversal via File Read",
            Self::PathWriteUser => "Path Traversal via File Write",
            Self::SecretApiKey => "Hardcoded API Key",
            Self::SecretPassword => "Hardcoded Password",
            Self::SecretToken => "Hardcoded Token",
            Self::SecretPrivateKey => "Hardcoded Private Key",
            Self::SecretAwsKey => "Hardcoded AWS Credentials",
            Self::SecretGeneric => "Hardcoded Secret",
            Self::CryptoWeakHash => "Weak Hash Algorithm",
            Self::CryptoWeakCipher => "Weak Encryption Algorithm",
            Self::CryptoHardcodedKey => "Hardcoded Cryptographic Key",
            Self::CryptoInsecureRandom => "Insecure Random Number Generation",
            Self::CryptoEcbMode => "Insecure ECB Mode",
            Self::DeserPickle => "Unsafe Pickle Deserialization",
            Self::DeserYaml => "Unsafe YAML Deserialization",
            Self::DeserJson => "Unsafe JSON Deserialization",
            Self::DeserXml => "Unsafe XML Deserialization (XXE)",
            Self::RedosExponential => "ReDoS: Exponential Complexity",
            Self::RedosPolynomial => "ReDoS: Polynomial Complexity",
            Self::RedosNested => "ReDoS: Nested Quantifiers",
            Self::SsrfHttpRequest => "SSRF via HTTP Request",
            Self::SsrfUrlFetch => "SSRF via URL Fetch",
            Self::SsrfSocket => "SSRF via Socket Connection",
            Self::LogiCrlf => "Log Injection via CRLF",
            Self::LogiFormatString => "Log Injection via Format String",
            Self::HdriCrlf => "HTTP Header Injection via CRLF",
            Self::HdriCookie => "Cookie Injection",
            Self::HdriRedirect => "Open Redirect",
            Self::SstiJinja => "SSTI in Jinja2 Template",
            Self::SstiMako => "SSTI in Mako Template",
            Self::SstiFreemarker => "SSTI in FreeMarker Template",
            Self::SstiGeneric => "Server-Side Template Injection",
            Self::Other => "Security Issue",
        }
    }

    /// Get the short description.
    #[must_use]
    pub fn short_description(&self) -> &'static str {
        match self {
            Self::SqliConcatenation => "User input concatenated into SQL query",
            Self::SqliFstring => "User input in SQL query via f-string",
            Self::SqliFormat => "User input in SQL query via format()",
            Self::SqliUnsafeExecute => "User input passed to unsafe execute",
            Self::CmdiOsSystem => "User input passed to os.system()",
            Self::CmdiSubprocess => "User input passed to subprocess with shell=True",
            Self::CmdiExec => "User input passed to exec() or eval()",
            Self::CmdiShell => "User input executed in shell context",
            Self::XssDomManipulation => "User input inserted into DOM without encoding",
            Self::XssInnerHtml => "User input assigned to innerHTML",
            Self::XssDocWrite => "User input passed to document.write()",
            Self::XssUnsafeRender => "User input rendered without escaping",
            Self::PathJoinUser => "User input in path join operation",
            Self::PathOpenUser => "User input in file open operation",
            Self::PathReadUser => "User input in file read operation",
            Self::PathWriteUser => "User input in file write operation",
            Self::SecretApiKey => "API key found in source code",
            Self::SecretPassword => "Password found in source code",
            Self::SecretToken => "Authentication token in source code",
            Self::SecretPrivateKey => "Private key found in source code",
            Self::SecretAwsKey => "AWS credentials in source code",
            Self::SecretGeneric => "Potential secret in source code",
            Self::CryptoWeakHash => "Weak hash algorithm (MD5, SHA1)",
            Self::CryptoWeakCipher => "Weak encryption (DES, RC4, Blowfish)",
            Self::CryptoHardcodedKey => "Cryptographic key hardcoded in source",
            Self::CryptoInsecureRandom => "Non-cryptographic PRNG for security",
            Self::CryptoEcbMode => "ECB mode used for block cipher",
            Self::DeserPickle => "Pickle deserialization of untrusted data",
            Self::DeserYaml => "YAML load without safe loader",
            Self::DeserJson => "Unsafe JSON deserialization",
            Self::DeserXml => "XML parsing vulnerable to XXE",
            Self::RedosExponential => "Regex with exponential backtracking",
            Self::RedosPolynomial => "Regex with polynomial complexity",
            Self::RedosNested => "Regex with nested quantifiers",
            Self::SsrfHttpRequest => "User-controlled URL in HTTP request",
            Self::SsrfUrlFetch => "User-controlled URL fetch",
            Self::SsrfSocket => "User-controlled socket connection",
            Self::LogiCrlf => "CRLF characters in log output",
            Self::LogiFormatString => "Format string in log with user input",
            Self::HdriCrlf => "CRLF in HTTP header value",
            Self::HdriCookie => "User input in Set-Cookie header",
            Self::HdriRedirect => "User input in redirect location",
            Self::SstiJinja => "User input in Jinja2 template",
            Self::SstiMako => "User input in Mako template",
            Self::SstiFreemarker => "User input in FreeMarker template",
            Self::SstiGeneric => "User input in server-side template",
            Self::Other => "Potential security issue detected",
        }
    }

    /// Get the full help text with remediation.
    #[must_use]
    pub fn help_text(&self) -> &'static str {
        match self {
            Self::SqliConcatenation | Self::SqliFstring | Self::SqliFormat | Self::SqliUnsafeExecute => {
                "**Problem**: User input is included in SQL queries without proper parameterization, allowing attackers to modify query logic.\n\n\
                 **Impact**: Data theft, data modification, authentication bypass, database destruction.\n\n\
                 **Fix**: Use parameterized queries (prepared statements) instead of string concatenation.\n\n\
                 ```python\n\
                 # Bad\n\
                 cursor.execute(f\"SELECT * FROM users WHERE id = {user_id}\")\n\n\
                 # Good\n\
                 cursor.execute(\"SELECT * FROM users WHERE id = ?\", (user_id,))\n\
                 ```"
            }
            Self::CmdiOsSystem | Self::CmdiSubprocess | Self::CmdiExec | Self::CmdiShell => {
                "**Problem**: User input is passed to shell commands, allowing arbitrary command execution.\n\n\
                 **Impact**: Full system compromise, data theft, malware installation.\n\n\
                 **Fix**: Avoid shell=True, use argument lists, validate/sanitize input.\n\n\
                 ```python\n\
                 # Bad\n\
                 subprocess.run(f\"ls {user_dir}\", shell=True)\n\n\
                 # Good\n\
                 subprocess.run([\"ls\", user_dir], shell=False)\n\
                 ```"
            }
            Self::XssDomManipulation | Self::XssInnerHtml | Self::XssDocWrite | Self::XssUnsafeRender => {
                "**Problem**: User input is rendered in HTML without proper encoding.\n\n\
                 **Impact**: Session hijacking, defacement, credential theft, malware distribution.\n\n\
                 **Fix**: Use framework auto-escaping, Content-Security-Policy, textContent instead of innerHTML.\n\n\
                 ```javascript\n\
                 // Bad\n\
                 element.innerHTML = userInput;\n\n\
                 // Good\n\
                 element.textContent = userInput;\n\
                 ```"
            }
            Self::PathJoinUser | Self::PathOpenUser | Self::PathReadUser | Self::PathWriteUser => {
                "**Problem**: User input in file paths allows directory traversal (../).\n\n\
                 **Impact**: Reading sensitive files, overwriting system files, code execution.\n\n\
                 **Fix**: Validate paths, use allowlists, resolve and check base directory.\n\n\
                 ```python\n\
                 # Bad\n\
                 with open(os.path.join(base_dir, user_file)) as f: ...\n\n\
                 # Good\n\
                 path = os.path.realpath(os.path.join(base_dir, user_file))\n\
                 if not path.startswith(os.path.realpath(base_dir)):\n\
                     raise ValueError(\"Invalid path\")\n\
                 ```"
            }
            Self::SecretApiKey | Self::SecretPassword | Self::SecretToken | Self::SecretPrivateKey | Self::SecretAwsKey | Self::SecretGeneric => {
                "**Problem**: Secrets hardcoded in source code can be extracted from repositories.\n\n\
                 **Impact**: Unauthorized access, data breaches, account compromise.\n\n\
                 **Fix**: Use environment variables, secret management services (Vault, AWS Secrets Manager).\n\n\
                 ```python\n\
                 # Bad\n\
                 api_key = \"sk_live_abc123\"\n\n\
                 # Good\n\
                 api_key = os.environ[\"API_KEY\"]\n\
                 ```"
            }
            Self::CryptoWeakHash | Self::CryptoWeakCipher | Self::CryptoHardcodedKey | Self::CryptoInsecureRandom | Self::CryptoEcbMode => {
                "**Problem**: Weak cryptographic algorithms or improper key management.\n\n\
                 **Impact**: Data decryption, authentication bypass, integrity violations.\n\n\
                 **Fix**: Use strong algorithms (AES-256, SHA-256+), proper key management, secure random.\n\n\
                 ```python\n\
                 # Bad\n\
                 hashlib.md5(password.encode())\n\n\
                 # Good\n\
                 hashlib.pbkdf2_hmac('sha256', password.encode(), salt, 100000)\n\
                 ```"
            }
            Self::DeserPickle | Self::DeserYaml | Self::DeserJson | Self::DeserXml => {
                "**Problem**: Deserializing untrusted data can execute arbitrary code.\n\n\
                 **Impact**: Remote code execution, full system compromise.\n\n\
                 **Fix**: Use safe loaders, validate before deserializing, use data-only formats.\n\n\
                 ```python\n\
                 # Bad\n\
                 pickle.loads(user_data)\n\n\
                 # Good\n\
                 json.loads(user_data)\n\
                 ```"
            }
            Self::RedosExponential | Self::RedosPolynomial | Self::RedosNested => {
                "**Problem**: Regular expression can cause catastrophic backtracking.\n\n\
                 **Impact**: Denial of service, application hang.\n\n\
                 **Fix**: Use atomic groups, possessive quantifiers, or rewrite regex.\n\n\
                 ```python\n\
                 # Bad\n\
                 re.match(r'(a+)+b', user_input)\n\n\
                 # Good\n\
                 re.match(r'a+b', user_input)\n\
                 ```"
            }
            Self::SsrfHttpRequest | Self::SsrfUrlFetch | Self::SsrfSocket => {
                "**Problem**: User-controlled URLs can access internal services.\n\n\
                 **Impact**: Internal network scanning, cloud metadata theft, service abuse.\n\n\
                 **Fix**: Validate URLs against allowlist, block private IP ranges.\n\n\
                 ```python\n\
                 # Bad\n\
                 requests.get(user_url)\n\n\
                 # Good\n\
                 if is_allowed_url(user_url):\n\
                     requests.get(user_url)\n\
                 ```"
            }
            Self::LogiCrlf | Self::LogiFormatString => {
                "**Problem**: User input in logs can forge entries or inject malicious data.\n\n\
                 **Impact**: Log tampering, log injection attacks, compliance violations.\n\n\
                 **Fix**: Sanitize CRLF characters, use structured logging.\n\n\
                 ```python\n\
                 # Bad\n\
                 logger.info(f\"User login: {username}\")\n\n\
                 # Good\n\
                 logger.info(\"User login\", extra={\"username\": sanitize(username)})\n\
                 ```"
            }
            Self::HdriCrlf | Self::HdriCookie | Self::HdriRedirect => {
                "**Problem**: User input in HTTP headers can inject new headers.\n\n\
                 **Impact**: Session hijacking, cache poisoning, phishing via open redirect.\n\n\
                 **Fix**: Validate and encode header values, use allowlists for redirects.\n\n\
                 ```python\n\
                 # Bad\n\
                 response.headers[\"Location\"] = user_url\n\n\
                 # Good\n\
                 if is_safe_redirect(user_url):\n\
                     response.headers[\"Location\"] = user_url\n\
                 ```"
            }
            Self::SstiJinja | Self::SstiMako | Self::SstiFreemarker | Self::SstiGeneric => {
                "**Problem**: User input in templates can execute arbitrary code.\n\n\
                 **Impact**: Remote code execution, data theft, full server compromise.\n\n\
                 **Fix**: Never pass user input as template source, use sandboxed templates.\n\n\
                 ```python\n\
                 # Bad\n\
                 Template(user_input).render()\n\n\
                 # Good\n\
                 Template(\"Hello {{ name }}\").render(name=user_input)\n\
                 ```"
            }
            Self::Other => {
                "**Problem**: A potential security issue was detected.\n\n\
                 **Impact**: Varies depending on the specific issue.\n\n\
                 **Fix**: Review the code and apply appropriate security measures."
            }
        }
    }
}

impl std::fmt::Display for SecurityRuleId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Get all standard rules as SARIF reporting descriptors.
#[must_use]
pub fn get_all_rules() -> Vec<SarifReportingDescriptor> {
    use SecurityRuleId::*;

    let all_rules = [
        SqliConcatenation,
        SqliFstring,
        SqliFormat,
        SqliUnsafeExecute,
        CmdiOsSystem,
        CmdiSubprocess,
        CmdiExec,
        CmdiShell,
        XssDomManipulation,
        XssInnerHtml,
        XssDocWrite,
        XssUnsafeRender,
        PathJoinUser,
        PathOpenUser,
        PathReadUser,
        PathWriteUser,
        SecretApiKey,
        SecretPassword,
        SecretToken,
        SecretPrivateKey,
        SecretAwsKey,
        SecretGeneric,
        CryptoWeakHash,
        CryptoWeakCipher,
        CryptoHardcodedKey,
        CryptoInsecureRandom,
        CryptoEcbMode,
        DeserPickle,
        DeserYaml,
        DeserJson,
        DeserXml,
        RedosExponential,
        RedosPolynomial,
        RedosNested,
        SsrfHttpRequest,
        SsrfUrlFetch,
        SsrfSocket,
        LogiCrlf,
        LogiFormatString,
        HdriCrlf,
        HdriCookie,
        HdriRedirect,
        SstiJinja,
        SstiMako,
        SstiFreemarker,
        SstiGeneric,
    ];

    all_rules
        .iter()
        .map(|rule| rule_to_descriptor(*rule))
        .collect()
}

/// Convert a rule ID to a SARIF reporting descriptor.
fn rule_to_descriptor(rule: SecurityRuleId) -> SarifReportingDescriptor {
    let mut properties = SarifPropertyBag::default();

    if let Some(cwe) = rule.cwe_id() {
        properties.cwe.push(format!("CWE-{cwe}"));
    }

    // Map rule to OWASP category
    let owasp_tag = match rule {
        SecurityRuleId::SqliConcatenation
        | SecurityRuleId::SqliFstring
        | SecurityRuleId::SqliFormat
        | SecurityRuleId::SqliUnsafeExecute
        | SecurityRuleId::CmdiOsSystem
        | SecurityRuleId::CmdiSubprocess
        | SecurityRuleId::CmdiExec
        | SecurityRuleId::CmdiShell
        | SecurityRuleId::XssDomManipulation
        | SecurityRuleId::XssInnerHtml
        | SecurityRuleId::XssDocWrite
        | SecurityRuleId::XssUnsafeRender
        | SecurityRuleId::PathJoinUser
        | SecurityRuleId::PathOpenUser
        | SecurityRuleId::PathReadUser
        | SecurityRuleId::PathWriteUser
        | SecurityRuleId::LogiCrlf
        | SecurityRuleId::LogiFormatString
        | SecurityRuleId::HdriCrlf
        | SecurityRuleId::HdriCookie
        | SecurityRuleId::HdriRedirect
        | SecurityRuleId::SstiJinja
        | SecurityRuleId::SstiMako
        | SecurityRuleId::SstiFreemarker
        | SecurityRuleId::SstiGeneric => Some("A03:2021-Injection"),
        SecurityRuleId::CryptoWeakHash
        | SecurityRuleId::CryptoWeakCipher
        | SecurityRuleId::CryptoHardcodedKey
        | SecurityRuleId::CryptoInsecureRandom
        | SecurityRuleId::CryptoEcbMode => Some("A02:2021-Cryptographic Failures"),
        SecurityRuleId::SecretApiKey
        | SecurityRuleId::SecretPassword
        | SecurityRuleId::SecretToken
        | SecurityRuleId::SecretPrivateKey
        | SecurityRuleId::SecretAwsKey
        | SecurityRuleId::SecretGeneric => {
            Some("A07:2021-Identification and Authentication Failures")
        }
        SecurityRuleId::DeserPickle
        | SecurityRuleId::DeserYaml
        | SecurityRuleId::DeserJson
        | SecurityRuleId::DeserXml => Some("A08:2021-Software and Data Integrity Failures"),
        SecurityRuleId::SsrfHttpRequest
        | SecurityRuleId::SsrfUrlFetch
        | SecurityRuleId::SsrfSocket => Some("A10:2021-Server-Side Request Forgery"),
        _ => None,
    };

    if let Some(owasp) = owasp_tag {
        properties.tags.push(owasp.to_string());
    }

    // Add security category tag
    properties.tags.push("security".to_string());

    let help_uri = rule
        .cwe_id()
        .map(|cwe| format!("https://cwe.mitre.org/data/definitions/{cwe}.html"));

    SarifReportingDescriptor {
        id: rule.as_str().to_string(),
        name: Some(rule.name().to_string()),
        short_description: Some(SarifMessage::text(rule.short_description())),
        full_description: Some(SarifMessage::text(rule.short_description())),
        help: Some(SarifMultiformatMessageString::with_markdown(
            rule.short_description(),
            rule.help_text(),
        )),
        help_uri,
        default_configuration: Some(SarifReportingConfiguration {
            level: SarifLevel::Error,
            enabled: Some(true),
            rank: None,
        }),
        properties: Some(properties),
        relationships: Vec::new(),
    }
}

// =============================================================================
// Code Flow Conversion
// =============================================================================

/// Convert a tainted value's propagation path to a SARIF code flow.
#[must_use]
pub fn taint_to_code_flow(
    tainted: &TaintedValue,
    sink_file: &str,
    sink_line: usize,
    sink_col: usize,
) -> SarifCodeFlow {
    let mut locations = Vec::new();

    // Add source location
    let source_loc = SarifThreadFlowLocation::new(
        SarifLocation::physical(SarifPhysicalLocation {
            artifact_location: SarifArtifactLocation::from_uri(&tainted.source_location.file),
            region: Some(SarifRegion::from_lines(
                tainted.source_location.line,
                tainted.source_location.column,
                tainted
                    .source_location
                    .end_line
                    .unwrap_or(tainted.source_location.line),
                tainted
                    .source_location
                    .end_column
                    .unwrap_or(tainted.source_location.column + 1),
            )),
            context_region: None,
        })
        .with_message(format!(
            "Taint source: {}",
            tainted
                .labels
                .iter()
                .map(|l| l.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    )
    .with_importance("essential")
    .with_execution_order(0);

    locations.push(source_loc);

    // Add propagation steps
    for (i, step) in tainted.propagation_path.iter().enumerate() {
        let step_loc = SarifThreadFlowLocation::new(
            SarifLocation::physical(SarifPhysicalLocation {
                artifact_location: SarifArtifactLocation::from_uri(&step.location.file),
                region: Some(SarifRegion::from_lines(
                    step.location.line,
                    step.location.column,
                    step.location.end_line.unwrap_or(step.location.line),
                    step.location.end_column.unwrap_or(step.location.column + 1),
                )),
                context_region: None,
            })
            .with_message(format!(
                "Taint {} via {}",
                step.propagation,
                step.operation.as_deref().unwrap_or("data flow")
            )),
        )
        .with_importance("important")
        .with_execution_order((i + 1) as i32);

        locations.push(step_loc);
    }

    // Add sink location
    let sink_loc = SarifThreadFlowLocation::new(
        SarifLocation::physical(SarifPhysicalLocation {
            artifact_location: SarifArtifactLocation::from_uri(sink_file),
            region: Some(SarifRegion::from_lines(
                sink_line,
                sink_col,
                sink_line,
                sink_col + 1,
            )),
            context_region: None,
        })
        .with_message("Taint sink: data reaches sensitive operation"),
    )
    .with_importance("essential")
    .with_execution_order(locations.len() as i32);

    locations.push(sink_loc);

    SarifCodeFlow::single(SarifThreadFlow::new(locations))
        .with_message("Data flow from untrusted source to sensitive sink")
}

/// Convert propagation steps to a SARIF code flow.
#[must_use]
pub fn propagation_steps_to_code_flow(
    steps: &[PropagationStep],
    source_msg: &str,
    sink_msg: &str,
) -> SarifCodeFlow {
    let locations: Vec<SarifThreadFlowLocation> = steps
        .iter()
        .enumerate()
        .map(|(i, step)| {
            let msg = if i == 0 {
                source_msg.to_string()
            } else if i == steps.len() - 1 {
                sink_msg.to_string()
            } else {
                format!(
                    "Taint {} via {}",
                    step.propagation,
                    step.operation.as_deref().unwrap_or("data flow")
                )
            };

            let importance = if i == 0 || i == steps.len() - 1 {
                "essential"
            } else {
                "important"
            };

            SarifThreadFlowLocation::new(
                SarifLocation::physical(SarifPhysicalLocation {
                    artifact_location: SarifArtifactLocation::from_uri(&step.location.file),
                    region: Some(SarifRegion::from_lines(
                        step.location.line,
                        step.location.column,
                        step.location.end_line.unwrap_or(step.location.line),
                        step.location.end_column.unwrap_or(step.location.column + 1),
                    )),
                    context_region: None,
                })
                .with_message(msg),
            )
            .with_importance(importance)
            .with_execution_order(i as i32)
        })
        .collect();

    SarifCodeFlow::single(SarifThreadFlow::new(locations))
}

// =============================================================================
// Fix Generation
// =============================================================================

/// Generate a fix suggestion for a security finding (when deterministic).
#[must_use]
pub fn generate_fix(finding: &SecurityFinding) -> Option<SarifFix> {
    // Only generate fixes for certain categories where we can be confident
    match &finding.category {
        SecurityCategory::Injection(InjectionType::Sql) => {
            // For SQL injection, suggest parameterized queries
            if finding.code_snippet.contains("f\"") || finding.code_snippet.contains("f'") {
                // F-string detected - suggest placeholder replacement
                let region = SarifRegion::from_lines(
                    finding.location.start_line,
                    finding.location.start_column,
                    finding.location.end_line,
                    finding.location.end_column,
                );

                return Some(SarifFix {
                    description: SarifMessage::text(
                        "Replace string formatting with parameterized query. Use '?' or '%s' placeholders and pass values as tuple."
                    ),
                    artifact_changes: vec![SarifArtifactChange {
                        artifact_location: SarifArtifactLocation::from_uri(&finding.location.file),
                        replacements: vec![SarifReplacement {
                            deleted_region: region,
                            inserted_content: Some(SarifArtifactContent {
                                text: Some("# TODO: Replace with parameterized query\n# cursor.execute(\"SELECT * FROM table WHERE col = ?\", (value,))".to_string()),
                                binary: None,
                                rendered: None,
                            }),
                        }],
                    }],
                });
            }
        }
        SecurityCategory::SecretsExposure => {
            // For secrets, suggest environment variable
            return Some(SarifFix {
                description: SarifMessage::text(
                    "Replace hardcoded secret with environment variable or secrets manager.",
                ),
                artifact_changes: vec![SarifArtifactChange {
                    artifact_location: SarifArtifactLocation::from_uri(&finding.location.file),
                    replacements: vec![SarifReplacement {
                        deleted_region: SarifRegion::from_lines(
                            finding.location.start_line,
                            finding.location.start_column,
                            finding.location.end_line,
                            finding.location.end_column,
                        ),
                        inserted_content: Some(SarifArtifactContent {
                            text: Some(
                                "os.environ.get(\"SECRET_NAME\")  # TODO: Set in environment"
                                    .to_string(),
                            ),
                            binary: None,
                            rendered: None,
                        }),
                    }],
                }],
            });
        }
        SecurityCategory::WeakCrypto => {
            // For weak crypto, suggest stronger alternatives
            if finding.code_snippet.contains("md5") {
                return Some(SarifFix {
                    description: SarifMessage::text("Replace MD5 with SHA-256 or stronger."),
                    artifact_changes: vec![SarifArtifactChange {
                        artifact_location: SarifArtifactLocation::from_uri(&finding.location.file),
                        replacements: vec![SarifReplacement {
                            deleted_region: SarifRegion::from_lines(
                                finding.location.start_line,
                                finding.location.start_column,
                                finding.location.end_line,
                                finding.location.end_column,
                            ),
                            inserted_content: Some(SarifArtifactContent {
                                text: Some("hashlib.sha256(data).hexdigest()".to_string()),
                                binary: None,
                                rendered: None,
                            }),
                        }],
                    }],
                });
            }
        }
        _ => {}
    }

    None
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
                        uri: Some(finding.location.file.clone()),
                        uri_base_id: Some("%SRCROOT%".to_string()),
                        index: Some(artifacts.len()),
                        description: None,
                    },
                    mime_type: guess_mime_type(&finding.location.file),
                    length: None,
                    source_language: guess_language(&finding.location.file),
                    hashes: HashMap::new(),
                    encoding: Some("utf-8".to_string()),
                    roles: vec!["analysisTarget".to_string()],
                });
            }
        }

        // Build original URI base IDs
        let mut uri_base_ids = HashMap::new();
        uri_base_ids.insert(
            "%SRCROOT%".to_string(),
            SarifArtifactLocation {
                uri: Some(".".to_string()),
                uri_base_id: None,
                index: None,
                description: Some(SarifMessage::text("The root of the source tree")),
            },
        );

        let tool = SarifTool {
            driver: SarifToolComponent {
                name: "brrr-security".to_string(),
                version: Some(self.scanner_version.clone()),
                semantic_version: Some(self.scanner_version.clone()),
                information_uri: Some("https://github.com/GrigoryEvko/go-brrr".to_string()),
                organization: Some("go-brrr".to_string()),
                full_name: Some("go-brrr Security Scanner".to_string()),
                rules,
                notifications: Vec::new(),
            },
            extensions: Vec::new(),
        };

        let run = SarifRun {
            tool,
            results,
            artifacts,
            invocations: Some(vec![SarifInvocation {
                execution_successful: true,
                command_line: None,
                arguments: Vec::new(),
                start_time_utc: Some(self.timestamp.clone()),
                end_time_utc: Some(self.timestamp.clone()),
                working_directory: None,
                exit_code: None,
                process_id: None,
                machine: None,
                account: None,
                tool_execution_notifications: Vec::new(),
                tool_configuration_notifications: Vec::new(),
            }]),
            original_uri_base_ids: Some(uri_base_ids),
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

    /// Serialize to compact SARIF JSON string.
    ///
    /// # Errors
    /// Returns an error if JSON serialization fails.
    pub fn to_sarif_json_compact(&self) -> Result<String, serde_json::Error> {
        let sarif = self.to_sarif();
        serde_json::to_string(&sarif)
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
    properties.tags.push("security".to_string());

    // Add OWASP tag if applicable
    if let Some(owasp) = finding.category.owasp_category() {
        properties.tags.push(owasp.to_string());
    }

    let help_uri = finding
        .cwe_id
        .map(|cwe| format!("https://cwe.mitre.org/data/definitions/{cwe}.html"));

    SarifReportingDescriptor {
        id: finding.id.clone(),
        name: Some(finding.title.clone()),
        short_description: Some(SarifMessage::text(&finding.title)),
        full_description: Some(SarifMessage::text(&finding.description)),
        help: if finding.remediation.is_empty() {
            None
        } else {
            Some(SarifMultiformatMessageString::with_markdown(
                &finding.remediation,
                &finding.remediation,
            ))
        },
        help_uri,
        default_configuration: Some(SarifReportingConfiguration {
            level: SarifLevel::from(finding.severity),
            enabled: Some(true),
            rank: None,
        }),
        properties: Some(properties),
        relationships: Vec::new(),
    }
}

/// Convert a finding to a SARIF result.
fn finding_to_result(finding: &SecurityFinding, rule_index: Option<usize>) -> SarifResult {
    let region = SarifRegion::from_lines(
        finding.location.start_line,
        finding.location.start_column,
        finding.location.end_line,
        finding.location.end_column,
    );

    let region_with_snippet = if finding.code_snippet.is_empty() {
        region
    } else {
        region.with_snippet(&finding.code_snippet)
    };

    let location = SarifLocation::physical(SarifPhysicalLocation {
        artifact_location: SarifArtifactLocation::from_uri(&finding.location.file),
        region: Some(region_with_snippet),
        context_region: None,
    });

    let mut fingerprints = HashMap::new();
    fingerprints.insert("primaryLocationLineHash".to_string(), finding.fingerprint());

    let mut partial_fingerprints = HashMap::new();
    partial_fingerprints.insert(
        "primaryLocationFilePath".to_string(),
        finding.location.file.clone(),
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
            state: Some("accepted".to_string()),
            justification: Some("Suppressed via inline comment".to_string()),
            location: None,
        }]
    } else {
        Vec::new()
    };

    // Generate fix if possible
    let fixes = generate_fix(finding).into_iter().collect();

    SarifResult {
        rule_id: finding.id.clone(),
        rule_index,
        level: Some(SarifLevel::from(finding.severity)),
        kind: Some("fail".to_string()),
        message: SarifMessage::text(&finding.description),
        locations: vec![location],
        code_flows: Vec::new(), // Would be populated from taint analysis
        related_locations: Vec::new(),
        fixes,
        fingerprints,
        partial_fingerprints,
        properties: Some(properties),
        suppressions,
        hosted_viewer_uri: None,
        work_item_uris: Vec::new(),
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
        "cs" => "text/x-csharp",
        "swift" => "text/x-swift",
        "kt" | "kts" => "text/x-kotlin",
        "scala" => "text/x-scala",
        _ => return None,
    };
    Some(mime.to_string())
}

/// Guess source language from file extension.
fn guess_language(path: &str) -> Option<String> {
    let ext = path.rsplit('.').next()?;
    let lang = match ext {
        "py" => "python",
        "js" => "javascript",
        "ts" => "typescript",
        "tsx" | "jsx" => "javascript",
        "rs" => "rust",
        "go" => "go",
        "java" => "java",
        "c" | "h" => "c",
        "cpp" | "cc" | "cxx" | "hpp" => "cplusplus",
        "rb" => "ruby",
        "php" => "php",
        "cs" => "csharp",
        "swift" => "swift",
        "kt" | "kts" => "kotlin",
        "scala" => "scala",
        _ => return None,
    };
    Some(lang.to_string())
}

// =============================================================================
// File Output
// =============================================================================

/// Write SARIF report to a file.
///
/// # Errors
/// Returns an error if file creation or writing fails.
pub fn write_sarif(report: &SarifLog, path: impl AsRef<Path>) -> std::io::Result<()> {
    let path = path.as_ref();
    let json = serde_json::to_string_pretty(report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

    let mut file = std::fs::File::create(path)?;
    file.write_all(json.as_bytes())?;
    file.flush()?;

    Ok(())
}

/// Write SARIF report to a file (compact JSON, no pretty printing).
///
/// # Errors
/// Returns an error if file creation or writing fails.
pub fn write_sarif_compact(report: &SarifLog, path: impl AsRef<Path>) -> std::io::Result<()> {
    let path = path.as_ref();
    let json = serde_json::to_string(report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

    let mut file = std::fs::File::create(path)?;
    file.write_all(json.as_bytes())?;
    file.flush()?;

    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::security::types::{Confidence, Location};

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
        assert!(matches!(result.level, Some(SarifLevel::Error)));
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

    #[test]
    fn test_sarif_schema_url() {
        let sarif = SarifLog::default();
        assert!(sarif.schema.contains("sarif-schema-2.1.0"));
    }

    #[test]
    fn test_rule_registry() {
        let rules = get_all_rules();
        assert!(!rules.is_empty());

        // Check SQL injection rule
        let sqli_rule = rules.iter().find(|r| r.id == "SQLI-001");
        assert!(sqli_rule.is_some());
        let sqli = sqli_rule.unwrap();
        assert!(sqli
            .properties
            .as_ref()
            .unwrap()
            .cwe
            .contains(&"CWE-89".to_string()));
    }

    #[test]
    fn test_severity_to_level() {
        assert_eq!(SarifLevel::from(Severity::Critical), SarifLevel::Error);
        assert_eq!(SarifLevel::from(Severity::High), SarifLevel::Error);
        assert_eq!(SarifLevel::from(Severity::Medium), SarifLevel::Warning);
        assert_eq!(SarifLevel::from(Severity::Low), SarifLevel::Note);
        assert_eq!(SarifLevel::from(Severity::Info), SarifLevel::Note);
    }

    #[test]
    fn test_rule_id_cwe_mapping() {
        assert_eq!(SecurityRuleId::SqliConcatenation.cwe_id(), Some(89));
        assert_eq!(SecurityRuleId::CmdiOsSystem.cwe_id(), Some(78));
        assert_eq!(SecurityRuleId::XssDomManipulation.cwe_id(), Some(79));
        assert_eq!(SecurityRuleId::PathJoinUser.cwe_id(), Some(22));
        assert_eq!(SecurityRuleId::SecretApiKey.cwe_id(), Some(798));
        assert_eq!(SecurityRuleId::DeserPickle.cwe_id(), Some(502));
    }

    #[test]
    fn test_fix_generation_sql() {
        let finding = SecurityFinding::new(
            "SQLI-002",
            SecurityCategory::Injection(InjectionType::Sql),
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "SQL Injection",
            "F-string SQL",
        )
        .with_code_snippet("cursor.execute(f\"SELECT * FROM users WHERE id = {x}\")");

        let fix = generate_fix(&finding);
        assert!(fix.is_some());
        let fix = fix.unwrap();
        assert!(fix
            .description
            .text
            .as_ref()
            .unwrap()
            .contains("parameterized"));
    }

    #[test]
    fn test_fix_generation_secret() {
        let finding = SecurityFinding::new(
            "SECRET-001",
            SecurityCategory::SecretsExposure,
            Severity::High,
            Confidence::High,
            Location::new("test.py", 5, 1, 5, 30),
            "Hardcoded API Key",
            "API key in source",
        );

        let fix = generate_fix(&finding);
        assert!(fix.is_some());
        let fix = fix.unwrap();
        assert!(fix
            .description
            .text
            .as_ref()
            .unwrap()
            .contains("environment"));
    }

    #[test]
    fn test_mime_type_detection() {
        assert_eq!(
            guess_mime_type("test.py"),
            Some("text/x-python".to_string())
        );
        assert_eq!(guess_mime_type("test.rs"), Some("text/x-rust".to_string()));
        assert_eq!(guess_mime_type("test.go"), Some("text/x-go".to_string()));
        assert_eq!(
            guess_mime_type("test.js"),
            Some("text/javascript".to_string())
        );
        assert_eq!(guess_mime_type("test.unknown"), None);
    }

    #[test]
    fn test_language_detection() {
        assert_eq!(guess_language("test.py"), Some("python".to_string()));
        assert_eq!(guess_language("test.rs"), Some("rust".to_string()));
        assert_eq!(guess_language("test.go"), Some("go".to_string()));
        assert_eq!(guess_language("test.java"), Some("java".to_string()));
    }

    #[test]
    fn test_sarif_message_creation() {
        let text_msg = SarifMessage::text("Hello");
        assert_eq!(text_msg.text, Some("Hello".to_string()));
        assert!(text_msg.markdown.is_none());

        let md_msg = SarifMessage::markdown("**Bold**");
        assert!(md_msg.text.is_none());
        assert_eq!(md_msg.markdown, Some("**Bold**".to_string()));

        let both = SarifMessage::both("Plain", "**Rich**");
        assert_eq!(both.text, Some("Plain".to_string()));
        assert_eq!(both.markdown, Some("**Rich**".to_string()));
    }

    #[test]
    fn test_sarif_region_with_snippet() {
        let region = SarifRegion::from_lines(10, 5, 10, 50).with_snippet("let x = 42;");

        assert_eq!(region.start_line, Some(10));
        assert!(region.snippet.is_some());
        assert_eq!(
            region.snippet.unwrap().text,
            Some("let x = 42;".to_string())
        );
    }

    #[test]
    fn test_sarif_location_builder() {
        let loc = SarifLocation::physical(SarifPhysicalLocation {
            artifact_location: SarifArtifactLocation::from_uri("test.py"),
            region: Some(SarifRegion::from_lines(1, 1, 1, 10)),
            context_region: None,
        })
        .with_message("Test location")
        .with_id(42);

        assert_eq!(loc.id, Some(42));
        assert!(loc.message.is_some());
    }

    #[test]
    fn test_sarif_code_flow() {
        let loc = SarifLocation::physical(SarifPhysicalLocation {
            artifact_location: SarifArtifactLocation::from_uri("test.py"),
            region: Some(SarifRegion::from_lines(1, 1, 1, 10)),
            context_region: None,
        });

        let tfl = SarifThreadFlowLocation::new(loc)
            .with_importance("essential")
            .with_execution_order(0);

        let thread_flow = SarifThreadFlow::new(vec![tfl]);
        let code_flow = SarifCodeFlow::single(thread_flow).with_message("Test flow");

        assert!(code_flow.message.is_some());
        assert_eq!(code_flow.thread_flows.len(), 1);
    }

    #[test]
    fn test_sarif_fix_creation() {
        let fix = SarifFix::single_replacement(
            "Use safer method",
            "test.py",
            SarifRegion::from_lines(10, 1, 10, 20),
            "safe_function()",
        );

        assert_eq!(fix.artifact_changes.len(), 1);
        assert_eq!(fix.artifact_changes[0].replacements.len(), 1);
    }

    #[test]
    fn test_sarif_property_bag() {
        let mut props = SarifPropertyBag::default();
        props.cwe.push("CWE-89".to_string());
        props.tags.push("security".to_string());
        props.security_severity = Some("8.0".to_string());

        assert_eq!(props.cwe.len(), 1);
        assert_eq!(props.tags.len(), 1);
    }

    #[test]
    fn test_deduplication_with_sarif() {
        let finding1 = SecurityFinding::new(
            "SQLI-001",
            SecurityCategory::Injection(InjectionType::Sql),
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "SQL Injection",
            "Test",
        );

        let finding2 = SecurityFinding::new(
            "SQLI-001",
            SecurityCategory::Injection(InjectionType::Sql),
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "SQL Injection",
            "Test",
        );

        let report = SecurityReport::new(vec![finding1, finding2], 1);
        let sarif = report.to_sarif();

        // Deduplication happens before SARIF conversion, so both findings appear
        // if not deduplicated in SecurityReport
        assert!(!sarif.runs[0].results.is_empty());
    }

    #[test]
    fn test_suppression_in_sarif() {
        let mut finding = SecurityFinding::new(
            "TEST-001",
            SecurityCategory::SecretsExposure,
            Severity::High,
            Confidence::High,
            Location::new("test.py", 10, 1, 10, 50),
            "Test",
            "Test finding",
        );
        finding.suppressed = true;

        let report = SecurityReport::new(vec![finding], 1);
        let sarif = report.to_sarif();

        let result = &sarif.runs[0].results[0];
        assert_eq!(result.suppressions.len(), 1);
        assert_eq!(result.suppressions[0].kind, "inSource");
    }
}
