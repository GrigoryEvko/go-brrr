//! Input validation analysis for detecting missing or weak validation.
//!
//! This module detects security vulnerabilities caused by missing or insufficient
//! input validation before data is used in sensitive operations. It tracks validation
//! patterns and ensures each sink receives appropriately validated data.
//!
//! # Validation Types
//!
//! The analyzer tracks several types of validation:
//!
//! - **Type Check**: Verifying data type (isinstance, typeof)
//! - **Length Check**: Limiting input length (len(), .length)
//! - **Range Check**: Numeric bounds validation
//! - **Format Check**: Regex pattern matching
//! - **Allowlist Check**: Checking against permitted values
//! - **Sanitization Check**: Encoding or escaping
//! - **Null Check**: Empty/None validation
//! - **Encoding Check**: Character set validation
//!
//! # Per-Sink Requirements
//!
//! Different sinks have different validation requirements:
//!
//! - **Database queries**: Type check, length check
//! - **File operations**: Path validation, format check
//! - **System commands**: Sanitization, allowlist
//! - **Numeric operations**: Range check, type check
//! - **Serialization**: Type check
//!
//! # Usage
//!
//! ```ignore
//! use brrr::security::input_validation::{InputValidationAnalyzer, analyze_input_validation};
//!
//! // Analyze a file for missing validation
//! let findings = analyze_input_validation("src/api.py", None)?;
//!
//! for finding in &findings {
//!     println!("Missing validation at {}: {:?}", finding.location, finding.missing_validation);
//!     println!("  Input: {} -> Sink: {}", finding.input_source, finding.sink);
//!     println!("  Recommendation: {}", finding.recommendation);
//! }
//! ```

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::security::taint::sinks::SinkCategory;
use crate::security::types::{Confidence, Location, Severity};

// =============================================================================
// Validation Types
// =============================================================================

/// Types of input validation that can be applied.
///
/// Each validation type addresses a specific class of security concern.
/// Multiple validations are often required for complete protection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ValidationType {
    /// Type check (isinstance, typeof, type assertion)
    /// Ensures data is of expected type before processing.
    TypeCheck,

    /// Length check (len(x) < limit, x.length <= max)
    /// Prevents buffer overflow, DoS via large inputs.
    LengthCheck,

    /// Range check (min <= value <= max)
    /// Ensures numeric values are within expected bounds.
    RangeCheck,

    /// Format check (regex validation, email format, etc.)
    /// Verifies input matches expected pattern.
    FormatCheck,

    /// Allowlist check (value in ALLOWED_VALUES)
    /// Restricts input to a known-safe set.
    AllowlistCheck,

    /// Sanitization check (escape, encode, strip)
    /// Transforms potentially dangerous characters.
    SanitizationCheck,

    /// Null/empty check (if not x, if x is None)
    /// Prevents null pointer errors and empty input issues.
    NullCheck,

    /// Encoding check (UTF-8 validation, character set)
    /// Ensures proper character encoding.
    EncodingCheck,
}

impl ValidationType {
    /// Human-readable description of the validation type.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::TypeCheck => "Type validation (verify data type)",
            Self::LengthCheck => "Length validation (limit input size)",
            Self::RangeCheck => "Range validation (numeric bounds check)",
            Self::FormatCheck => "Format validation (regex pattern matching)",
            Self::AllowlistCheck => "Allowlist validation (restrict to known values)",
            Self::SanitizationCheck => "Sanitization (escape or encode input)",
            Self::NullCheck => "Null/empty check (handle missing input)",
            Self::EncodingCheck => "Encoding validation (verify character encoding)",
        }
    }

    /// CWE ID associated with missing this validation.
    #[must_use]
    pub const fn cwe_id(&self) -> u32 {
        match self {
            Self::TypeCheck => 20,         // CWE-20: Improper Input Validation
            Self::LengthCheck => 119,      // CWE-119: Buffer Errors
            Self::RangeCheck => 190,       // CWE-190: Integer Overflow
            Self::FormatCheck => 20,       // CWE-20: Improper Input Validation
            Self::AllowlistCheck => 20,    // CWE-20: Improper Input Validation
            Self::SanitizationCheck => 79, // CWE-79: XSS (varies by context)
            Self::NullCheck => 476,        // CWE-476: NULL Pointer Dereference
            Self::EncodingCheck => 838,    // CWE-838: Inappropriate Encoding
        }
    }

    /// Get all validation types.
    #[must_use]
    pub const fn all() -> &'static [Self] {
        &[
            Self::TypeCheck,
            Self::LengthCheck,
            Self::RangeCheck,
            Self::FormatCheck,
            Self::AllowlistCheck,
            Self::SanitizationCheck,
            Self::NullCheck,
            Self::EncodingCheck,
        ]
    }
}

impl std::fmt::Display for ValidationType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeCheck => write!(f, "type_check"),
            Self::LengthCheck => write!(f, "length_check"),
            Self::RangeCheck => write!(f, "range_check"),
            Self::FormatCheck => write!(f, "format_check"),
            Self::AllowlistCheck => write!(f, "allowlist_check"),
            Self::SanitizationCheck => write!(f, "sanitization_check"),
            Self::NullCheck => write!(f, "null_check"),
            Self::EncodingCheck => write!(f, "encoding_check"),
        }
    }
}

// =============================================================================
// Sink Types and Requirements
// =============================================================================

/// Type of sensitive operation (sink) that requires validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SinkType {
    /// Database query (SQL, NoSQL)
    DatabaseQuery,
    /// File system operation (read, write, delete)
    FileOperation,
    /// System command execution
    SystemCommand,
    /// Numeric operation (division, array index)
    NumericOperation,
    /// Serialization/deserialization
    Serialization,
    /// Network request (HTTP, socket)
    NetworkRequest,
    /// HTML/template output
    HtmlOutput,
    /// Logging operation
    LogOutput,
    /// Authentication/authorization check
    AuthOperation,
    /// Cryptographic operation
    CryptoOperation,
    /// Regular expression compilation
    RegexCompilation,
    /// Memory allocation
    MemoryAllocation,
}

impl SinkType {
    /// Convert from taint SinkCategory.
    pub fn from_sink_category(category: SinkCategory) -> Option<Self> {
        match category {
            SinkCategory::SqlInjection | SinkCategory::NoSqlInjection => Some(Self::DatabaseQuery),
            SinkCategory::PathTraversal => Some(Self::FileOperation),
            SinkCategory::CommandInjection => Some(Self::SystemCommand),
            SinkCategory::XSS | SinkCategory::TemplateInjection => Some(Self::HtmlOutput),
            SinkCategory::SSRF => Some(Self::NetworkRequest),
            SinkCategory::LogInjection => Some(Self::LogOutput),
            SinkCategory::Deserialization => Some(Self::Serialization),
            SinkCategory::RegexInjection => Some(Self::RegexCompilation),
            SinkCategory::MemoryCorruption => Some(Self::MemoryAllocation),
            SinkCategory::CodeExecution => Some(Self::SystemCommand),
            _ => None,
        }
    }

    /// Human-readable description.
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::DatabaseQuery => "Database query execution",
            Self::FileOperation => "File system operation",
            Self::SystemCommand => "System command execution",
            Self::NumericOperation => "Numeric operation",
            Self::Serialization => "Serialization/deserialization",
            Self::NetworkRequest => "Network request",
            Self::HtmlOutput => "HTML/template output",
            Self::LogOutput => "Logging operation",
            Self::AuthOperation => "Authentication operation",
            Self::CryptoOperation => "Cryptographic operation",
            Self::RegexCompilation => "Regular expression compilation",
            Self::MemoryAllocation => "Memory allocation",
        }
    }
}

impl std::fmt::Display for SinkType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description())
    }
}

/// Validation requirements for a specific sink type.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SinkValidationRequirements {
    /// The sink type these requirements apply to.
    pub sink_type: SinkType,

    /// Validations that MUST be present (missing = vulnerability).
    pub required_validations: Vec<ValidationType>,

    /// Validations that SHOULD be present (missing = warning).
    pub recommended_validations: Vec<ValidationType>,
}

impl SinkValidationRequirements {
    /// Get validation requirements for a sink type.
    #[must_use]
    pub fn for_sink(sink_type: SinkType) -> Self {
        match sink_type {
            SinkType::DatabaseQuery => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck],
                recommended_validations: vec![
                    ValidationType::LengthCheck,
                    ValidationType::SanitizationCheck,
                    ValidationType::NullCheck,
                ],
            },
            SinkType::FileOperation => Self {
                sink_type,
                required_validations: vec![
                    ValidationType::FormatCheck, // Path validation
                    ValidationType::SanitizationCheck,
                ],
                recommended_validations: vec![
                    ValidationType::AllowlistCheck,
                    ValidationType::NullCheck,
                    ValidationType::LengthCheck,
                ],
            },
            SinkType::SystemCommand => Self {
                sink_type,
                required_validations: vec![
                    ValidationType::SanitizationCheck,
                    ValidationType::AllowlistCheck,
                ],
                recommended_validations: vec![
                    ValidationType::TypeCheck,
                    ValidationType::LengthCheck,
                    ValidationType::NullCheck,
                ],
            },
            SinkType::NumericOperation => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck, ValidationType::RangeCheck],
                recommended_validations: vec![ValidationType::NullCheck],
            },
            SinkType::Serialization => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck],
                recommended_validations: vec![
                    ValidationType::AllowlistCheck,
                    ValidationType::LengthCheck,
                ],
            },
            SinkType::NetworkRequest => Self {
                sink_type,
                required_validations: vec![
                    ValidationType::FormatCheck, // URL validation
                    ValidationType::AllowlistCheck,
                ],
                recommended_validations: vec![
                    ValidationType::SanitizationCheck,
                    ValidationType::NullCheck,
                ],
            },
            SinkType::HtmlOutput => Self {
                sink_type,
                required_validations: vec![ValidationType::SanitizationCheck],
                recommended_validations: vec![
                    ValidationType::TypeCheck,
                    ValidationType::LengthCheck,
                    ValidationType::EncodingCheck,
                ],
            },
            SinkType::LogOutput => Self {
                sink_type,
                required_validations: vec![],
                recommended_validations: vec![
                    ValidationType::SanitizationCheck,
                    ValidationType::LengthCheck,
                ],
            },
            SinkType::AuthOperation => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck, ValidationType::NullCheck],
                recommended_validations: vec![
                    ValidationType::FormatCheck,
                    ValidationType::LengthCheck,
                ],
            },
            SinkType::CryptoOperation => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck, ValidationType::LengthCheck],
                recommended_validations: vec![
                    ValidationType::EncodingCheck,
                    ValidationType::NullCheck,
                ],
            },
            SinkType::RegexCompilation => Self {
                sink_type,
                required_validations: vec![ValidationType::LengthCheck],
                recommended_validations: vec![
                    ValidationType::FormatCheck,
                    ValidationType::SanitizationCheck,
                ],
            },
            SinkType::MemoryAllocation => Self {
                sink_type,
                required_validations: vec![ValidationType::TypeCheck, ValidationType::RangeCheck],
                recommended_validations: vec![ValidationType::NullCheck],
            },
        }
    }

    /// Check if a set of validations satisfies the requirements.
    pub fn check_validations(&self, applied: &HashSet<ValidationType>) -> ValidationCheckResult {
        let missing_required: Vec<ValidationType> = self
            .required_validations
            .iter()
            .filter(|v| !applied.contains(v))
            .copied()
            .collect();

        let missing_recommended: Vec<ValidationType> = self
            .recommended_validations
            .iter()
            .filter(|v| !applied.contains(v))
            .copied()
            .collect();

        ValidationCheckResult {
            is_valid: missing_required.is_empty(),
            missing_required,
            missing_recommended,
        }
    }
}

/// Result of validation check against requirements.
#[derive(Debug, Clone)]
pub struct ValidationCheckResult {
    /// Whether all required validations are present.
    pub is_valid: bool,
    /// Required validations that are missing.
    pub missing_required: Vec<ValidationType>,
    /// Recommended validations that are missing.
    pub missing_recommended: Vec<ValidationType>,
}

// =============================================================================
// Input Validation Finding
// =============================================================================

/// A finding indicating missing or weak input validation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputValidationFinding {
    /// Location in source code.
    pub location: Location,

    /// Severity of the finding.
    pub severity: Severity,

    /// Confidence in the finding.
    pub confidence: Confidence,

    /// Source of the input (e.g., "request.args.get('id')").
    pub input_source: String,

    /// The sink where the input is used.
    pub sink: String,

    /// Type of the sink.
    pub sink_type: SinkType,

    /// Validations that are missing.
    pub missing_validation: Vec<ValidationType>,

    /// Validations that were detected.
    pub applied_validation: Vec<ValidationType>,

    /// Recommendation for fixing.
    pub recommendation: String,

    /// Code snippet showing the vulnerable code.
    pub code_snippet: String,

    /// Variable name being tracked.
    pub variable: String,

    /// Whether this is a required or recommended validation.
    pub is_required: bool,
}

impl InputValidationFinding {
    /// Create a new finding.
    pub fn new(
        location: Location,
        input_source: impl Into<String>,
        sink: impl Into<String>,
        sink_type: SinkType,
        missing_validation: Vec<ValidationType>,
    ) -> Self {
        let severity = Self::calculate_severity(sink_type, &missing_validation, true);
        let recommendation = Self::generate_recommendation(sink_type, &missing_validation);

        Self {
            location,
            severity,
            confidence: Confidence::High,
            input_source: input_source.into(),
            sink: sink.into(),
            sink_type,
            missing_validation,
            applied_validation: Vec::new(),
            recommendation,
            code_snippet: String::new(),
            variable: String::new(),
            is_required: true,
        }
    }

    /// Calculate severity based on sink type and missing validations.
    fn calculate_severity(
        sink_type: SinkType,
        missing: &[ValidationType],
        is_required: bool,
    ) -> Severity {
        if missing.is_empty() {
            return Severity::Info;
        }

        if !is_required {
            return Severity::Low;
        }

        // High-risk sinks with missing required validation
        match sink_type {
            SinkType::SystemCommand | SinkType::DatabaseQuery => {
                if missing.contains(&ValidationType::SanitizationCheck)
                    || missing.contains(&ValidationType::AllowlistCheck)
                {
                    Severity::Critical
                } else {
                    Severity::High
                }
            }
            SinkType::FileOperation => {
                if missing.contains(&ValidationType::FormatCheck) {
                    Severity::High
                } else {
                    Severity::Medium
                }
            }
            SinkType::HtmlOutput => Severity::Medium,
            SinkType::NumericOperation => {
                if missing.contains(&ValidationType::RangeCheck) {
                    Severity::Medium
                } else {
                    Severity::Low
                }
            }
            SinkType::AuthOperation | SinkType::CryptoOperation => Severity::High,
            _ => Severity::Medium,
        }
    }

    /// Generate a recommendation for the missing validation.
    fn generate_recommendation(sink_type: SinkType, missing: &[ValidationType]) -> String {
        if missing.is_empty() {
            return "All required validations are present.".to_string();
        }

        let mut parts = Vec::new();

        for validation in missing {
            let rec = match (sink_type, validation) {
                (SinkType::DatabaseQuery, ValidationType::TypeCheck) => {
                    "Add type check: `if not isinstance(value, (str, int)): raise ValueError()`"
                }
                (SinkType::DatabaseQuery, ValidationType::LengthCheck) => {
                    "Add length check: `if len(value) > MAX_LENGTH: raise ValueError()`"
                }
                (SinkType::FileOperation, ValidationType::FormatCheck) => {
                    "Validate path format: Use `os.path.realpath()` and check `startswith(base_path)`"
                }
                (SinkType::FileOperation, ValidationType::AllowlistCheck) => {
                    "Use allowlist: `if filename not in ALLOWED_FILES: raise PermissionError()`"
                }
                (SinkType::SystemCommand, ValidationType::SanitizationCheck) => {
                    "Use shlex.quote() or subprocess with list args (shell=False)"
                }
                (SinkType::SystemCommand, ValidationType::AllowlistCheck) => {
                    "Use allowlist for commands: `if cmd not in ALLOWED_COMMANDS: raise ValueError()`"
                }
                (SinkType::NumericOperation, ValidationType::RangeCheck) => {
                    "Add range check: `if not (MIN <= value <= MAX): raise ValueError()`"
                }
                (SinkType::NumericOperation, ValidationType::TypeCheck) => {
                    "Add type check: `if not isinstance(value, (int, float)): raise TypeError()`"
                }
                (SinkType::HtmlOutput, ValidationType::SanitizationCheck) => {
                    "Escape HTML: Use `html.escape()`, `markupsafe.escape()`, or template autoescape"
                }
                (SinkType::NetworkRequest, ValidationType::AllowlistCheck) => {
                    "Validate URL domain: Check against allowlist of permitted hosts"
                }
                (SinkType::NetworkRequest, ValidationType::FormatCheck) => {
                    "Validate URL format: Parse with `urllib.parse.urlparse()` and check scheme"
                }
                (_, ValidationType::NullCheck) => {
                    "Add null/empty check: `if not value: raise ValueError('Required field')`"
                }
                (_, ValidationType::TypeCheck) => {
                    "Add type validation: `isinstance(value, expected_type)`"
                }
                (_, ValidationType::LengthCheck) => {
                    "Add length validation: `len(value) <= MAX_LENGTH`"
                }
                (_, ValidationType::EncodingCheck) => {
                    "Validate encoding: `value.encode('utf-8')` in try/except"
                }
                _ => "Add appropriate input validation before use",
            };
            parts.push(format!("- {}", rec));
        }

        parts.join("\n")
    }

    /// Set applied validations.
    #[must_use]
    pub fn with_applied_validation(mut self, applied: Vec<ValidationType>) -> Self {
        self.applied_validation = applied;
        self
    }

    /// Set code snippet.
    #[must_use]
    pub fn with_code_snippet(mut self, snippet: impl Into<String>) -> Self {
        self.code_snippet = snippet.into();
        self
    }

    /// Set variable name.
    #[must_use]
    pub fn with_variable(mut self, var: impl Into<String>) -> Self {
        self.variable = var.into();
        self
    }

    /// Set confidence level.
    #[must_use]
    pub fn with_confidence(mut self, confidence: Confidence) -> Self {
        self.confidence = confidence;
        self
    }

    /// Mark as recommended (not required) validation.
    #[must_use]
    pub fn as_recommended(mut self) -> Self {
        self.is_required = false;
        self.severity = Self::calculate_severity(self.sink_type, &self.missing_validation, false);
        self
    }

    /// Get a unique identifier for this finding.
    #[must_use]
    pub fn id(&self) -> String {
        format!(
            "VALID-{:03}",
            match self.severity {
                Severity::Critical => 1,
                Severity::High => 2,
                Severity::Medium => 3,
                Severity::Low => 4,
                Severity::Info => 5,
            }
        )
    }
}

// =============================================================================
// Validation Tracking
// =============================================================================

/// Tracks validations applied to a variable.
#[derive(Debug, Clone, Default)]
pub struct VariableValidation {
    /// Variable name.
    pub variable: String,
    /// Validations that have been applied.
    pub validations: HashSet<ValidationType>,
    /// Where the variable was defined.
    pub definition_location: Option<Location>,
    /// Source of the input (if known).
    pub input_source: Option<String>,
    /// Whether this is definitely user input.
    pub is_user_input: bool,
}

impl VariableValidation {
    /// Create a new variable validation tracker.
    pub fn new(variable: impl Into<String>) -> Self {
        Self {
            variable: variable.into(),
            validations: HashSet::new(),
            definition_location: None,
            input_source: None,
            is_user_input: false,
        }
    }

    /// Mark as user input.
    #[must_use]
    pub fn from_user_input(mut self, source: impl Into<String>) -> Self {
        self.is_user_input = true;
        self.input_source = Some(source.into());
        self
    }

    /// Add a validation.
    pub fn add_validation(&mut self, validation: ValidationType) {
        self.validations.insert(validation);
    }

    /// Check if a validation has been applied.
    pub fn has_validation(&self, validation: ValidationType) -> bool {
        self.validations.contains(&validation)
    }
}

/// Validation state tracker for a function/scope.
#[derive(Debug, Clone, Default)]
pub struct ValidationState {
    /// Validation status per variable.
    variables: HashMap<String, VariableValidation>,
}

impl ValidationState {
    /// Create a new validation state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get or create validation tracker for a variable.
    pub fn get_or_create(&mut self, variable: &str) -> &mut VariableValidation {
        if !self.variables.contains_key(variable) {
            self.variables
                .insert(variable.to_string(), VariableValidation::new(variable));
        }
        self.variables.get_mut(variable).unwrap()
    }

    /// Get validation tracker for a variable.
    pub fn get(&self, variable: &str) -> Option<&VariableValidation> {
        self.variables.get(variable)
    }

    /// Mark a variable as user input.
    pub fn mark_user_input(&mut self, variable: &str, source: &str) {
        let tracker = self.get_or_create(variable);
        tracker.is_user_input = true;
        tracker.input_source = Some(source.to_string());
    }

    /// Add a validation to a variable.
    pub fn add_validation(&mut self, variable: &str, validation: ValidationType) {
        self.get_or_create(variable).add_validation(validation);
    }

    /// Propagate validations from source to target (for assignments).
    pub fn propagate(&mut self, target: &str, source: &str) {
        if let Some(source_tracker) = self.variables.get(source) {
            let validations = source_tracker.validations.clone();
            let is_user_input = source_tracker.is_user_input;
            let input_source = source_tracker.input_source.clone();

            let target_tracker = self.get_or_create(target);
            target_tracker.validations.extend(validations);
            if is_user_input {
                target_tracker.is_user_input = true;
                if target_tracker.input_source.is_none() {
                    target_tracker.input_source = input_source;
                }
            }
        }
    }

    /// Get all user input variables.
    pub fn user_input_variables(&self) -> Vec<&VariableValidation> {
        self.variables
            .values()
            .filter(|v| v.is_user_input)
            .collect()
    }
}

// =============================================================================
// Validation Pattern Matchers
// =============================================================================

/// Patterns for detecting validation in Python code.
#[derive(Debug, Default)]
pub struct PythonValidationPatterns {
    /// Patterns that indicate type checking.
    type_check_patterns: Vec<regex::Regex>,
    /// Patterns that indicate length checking.
    length_check_patterns: Vec<regex::Regex>,
    /// Patterns that indicate range checking.
    range_check_patterns: Vec<regex::Regex>,
    /// Patterns that indicate format checking.
    format_check_patterns: Vec<regex::Regex>,
    /// Patterns that indicate allowlist checking.
    allowlist_check_patterns: Vec<regex::Regex>,
    /// Patterns that indicate sanitization.
    sanitization_patterns: Vec<regex::Regex>,
    /// Patterns that indicate null checking.
    null_check_patterns: Vec<regex::Regex>,
}

impl PythonValidationPatterns {
    /// Create patterns for Python.
    pub fn new() -> Self {
        Self {
            type_check_patterns: vec![
                regex::Regex::new(r"isinstance\s*\([^,]+,").unwrap(),
                regex::Regex::new(r"type\s*\([^)]+\)\s*(==|!=|is)").unwrap(),
                regex::Regex::new(r"hasattr\s*\([^,]+,").unwrap(),
            ],
            length_check_patterns: vec![
                regex::Regex::new(r"len\s*\([^)]+\)\s*(<|>|<=|>=|==)").unwrap(),
                regex::Regex::new(r"\.length\s*(<|>|<=|>=|==)").unwrap(),
            ],
            range_check_patterns: vec![
                regex::Regex::new(r"(\d+)\s*(<|<=)\s*\w+\s*(<|<=)\s*(\d+)").unwrap(),
                regex::Regex::new(r"\w+\s*(>=|>)\s*(\d+)\s*and\s*\w+\s*(<|<=)\s*(\d+)").unwrap(),
                regex::Regex::new(r"in\s+range\s*\(").unwrap(),
            ],
            format_check_patterns: vec![
                regex::Regex::new(r"re\.(match|search|fullmatch)\s*\(").unwrap(),
                regex::Regex::new(r"\.match\s*\(").unwrap(),
                regex::Regex::new(r"\.startswith\s*\(").unwrap(),
                regex::Regex::new(r"\.endswith\s*\(").unwrap(),
                regex::Regex::new(r"validate_\w+\s*\(").unwrap(),
            ],
            allowlist_check_patterns: vec![
                regex::Regex::new(r"\w+\s+in\s+\[").unwrap(),
                regex::Regex::new(r"\w+\s+in\s+\{").unwrap(),
                regex::Regex::new(r"\w+\s+in\s+\w+_ALLOWED").unwrap(),
                regex::Regex::new(r"\w+\s+in\s+ALLOWED_\w+").unwrap(),
                regex::Regex::new(r"\w+\s+not\s+in\s+BLOCKED_").unwrap(),
            ],
            sanitization_patterns: vec![
                regex::Regex::new(r"html\.escape\s*\(").unwrap(),
                regex::Regex::new(r"escape\s*\(").unwrap(),
                regex::Regex::new(r"shlex\.quote\s*\(").unwrap(),
                regex::Regex::new(r"quote\s*\(").unwrap(),
                regex::Regex::new(r"sanitize\w*\s*\(").unwrap(),
                regex::Regex::new(r"\.strip\s*\(").unwrap(),
                regex::Regex::new(r"\.replace\s*\(").unwrap(),
            ],
            null_check_patterns: vec![
                regex::Regex::new(r"if\s+not\s+\w+\s*:").unwrap(),
                regex::Regex::new(r"if\s+\w+\s+is\s+None").unwrap(),
                regex::Regex::new(r"if\s+\w+\s*:").unwrap(),
                regex::Regex::new(r"\w+\s+or\s+").unwrap(),
                regex::Regex::new(r"\.get\s*\([^,]+,\s*[^)]+\)").unwrap(),
            ],
        }
    }

    /// Detect validations in a code line.
    pub fn detect_validations(&self, line: &str) -> Vec<ValidationType> {
        let mut validations = Vec::new();

        for pattern in &self.type_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::TypeCheck);
                break;
            }
        }

        for pattern in &self.length_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::LengthCheck);
                break;
            }
        }

        for pattern in &self.range_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::RangeCheck);
                break;
            }
        }

        for pattern in &self.format_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::FormatCheck);
                break;
            }
        }

        for pattern in &self.allowlist_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::AllowlistCheck);
                break;
            }
        }

        for pattern in &self.sanitization_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::SanitizationCheck);
                break;
            }
        }

        for pattern in &self.null_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::NullCheck);
                break;
            }
        }

        validations
    }
}

/// Patterns for detecting validation in TypeScript/JavaScript code.
#[derive(Debug, Default)]
pub struct TypeScriptValidationPatterns {
    type_check_patterns: Vec<regex::Regex>,
    length_check_patterns: Vec<regex::Regex>,
    range_check_patterns: Vec<regex::Regex>,
    format_check_patterns: Vec<regex::Regex>,
    allowlist_check_patterns: Vec<regex::Regex>,
    sanitization_patterns: Vec<regex::Regex>,
    null_check_patterns: Vec<regex::Regex>,
}

impl TypeScriptValidationPatterns {
    /// Create patterns for TypeScript/JavaScript.
    pub fn new() -> Self {
        Self {
            type_check_patterns: vec![
                regex::Regex::new(r"typeof\s+\w+\s*(===|!==)").unwrap(),
                regex::Regex::new(r"instanceof\s+").unwrap(),
                regex::Regex::new(r"Array\.isArray\s*\(").unwrap(),
                regex::Regex::new(r"Number\.isInteger\s*\(").unwrap(),
                regex::Regex::new(r"Number\.isFinite\s*\(").unwrap(),
            ],
            length_check_patterns: vec![
                regex::Regex::new(r"\.length\s*(>|<|>=|<=|===)").unwrap(),
                regex::Regex::new(r"\.size\s*(>|<|>=|<=|===)").unwrap(),
            ],
            range_check_patterns: vec![
                regex::Regex::new(r"\w+\s*(>=|>)\s*\d+\s*&&\s*\w+\s*(<|<=)\s*\d+").unwrap(),
                regex::Regex::new(r"Math\.(min|max)\s*\(").unwrap(),
            ],
            format_check_patterns: vec![
                regex::Regex::new(r"\.test\s*\(").unwrap(),
                regex::Regex::new(r"\.match\s*\(").unwrap(),
                regex::Regex::new(r"new\s+RegExp\s*\(").unwrap(),
                regex::Regex::new(r"\.startsWith\s*\(").unwrap(),
                regex::Regex::new(r"\.endsWith\s*\(").unwrap(),
                regex::Regex::new(r"validate\w*\s*\(").unwrap(),
            ],
            allowlist_check_patterns: vec![
                regex::Regex::new(r"\.includes\s*\(").unwrap(),
                regex::Regex::new(r"\.indexOf\s*\([^)]+\)\s*(>|>=|===)\s*").unwrap(),
                regex::Regex::new(r"\.has\s*\(").unwrap(),
                regex::Regex::new(r"Object\.keys\s*\([^)]+\)\.includes").unwrap(),
            ],
            sanitization_patterns: vec![
                regex::Regex::new(r"DOMPurify\.sanitize\s*\(").unwrap(),
                regex::Regex::new(r"encodeURIComponent\s*\(").unwrap(),
                regex::Regex::new(r"encodeURI\s*\(").unwrap(),
                regex::Regex::new(r"escape\w*\s*\(").unwrap(),
                regex::Regex::new(r"sanitize\w*\s*\(").unwrap(),
                regex::Regex::new(r"\.trim\s*\(").unwrap(),
                regex::Regex::new(r"\.replace\s*\(").unwrap(),
            ],
            null_check_patterns: vec![
                regex::Regex::new(r"if\s*\(\s*!\w+\s*\)").unwrap(),
                regex::Regex::new(r"\?\?").unwrap(), // Nullish coalescing
                regex::Regex::new(r"\?\.\s*").unwrap(), // Optional chaining
                regex::Regex::new(r"===\s*null").unwrap(),
                regex::Regex::new(r"===\s*undefined").unwrap(),
                regex::Regex::new(r"\|\|").unwrap(),
            ],
        }
    }

    /// Detect validations in a code line.
    pub fn detect_validations(&self, line: &str) -> Vec<ValidationType> {
        let mut validations = Vec::new();

        for pattern in &self.type_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::TypeCheck);
                break;
            }
        }

        for pattern in &self.length_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::LengthCheck);
                break;
            }
        }

        for pattern in &self.range_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::RangeCheck);
                break;
            }
        }

        for pattern in &self.format_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::FormatCheck);
                break;
            }
        }

        for pattern in &self.allowlist_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::AllowlistCheck);
                break;
            }
        }

        for pattern in &self.sanitization_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::SanitizationCheck);
                break;
            }
        }

        for pattern in &self.null_check_patterns {
            if pattern.is_match(line) {
                validations.push(ValidationType::NullCheck);
                break;
            }
        }

        validations
    }
}

// =============================================================================
// Input Source Patterns
// =============================================================================

/// Patterns that indicate user input sources.
pub struct InputSourcePatterns {
    python_patterns: Vec<(regex::Regex, &'static str)>,
    typescript_patterns: Vec<(regex::Regex, &'static str)>,
}

impl Default for InputSourcePatterns {
    fn default() -> Self {
        Self::new()
    }
}

impl InputSourcePatterns {
    /// Create input source patterns.
    pub fn new() -> Self {
        Self {
            python_patterns: vec![
                (
                    regex::Regex::new(r#"request\.args\.get\(['"](\w+)['"]"#).unwrap(),
                    "request.args.get",
                ),
                (
                    regex::Regex::new(r#"request\.form\.get\(['"](\w+)['"]"#).unwrap(),
                    "request.form.get",
                ),
                (
                    regex::Regex::new(r#"request\.json\.get\(['"](\w+)['"]"#).unwrap(),
                    "request.json.get",
                ),
                (regex::Regex::new(r"request\.data").unwrap(), "request.data"),
                (
                    regex::Regex::new(r"request\.files").unwrap(),
                    "request.files",
                ),
                (
                    regex::Regex::new(r"request\.headers\.get").unwrap(),
                    "request.headers",
                ),
                (
                    regex::Regex::new(r"request\.cookies\.get").unwrap(),
                    "request.cookies",
                ),
                (regex::Regex::new(r"sys\.argv").unwrap(), "sys.argv"),
                (
                    regex::Regex::new(r"os\.environ\.get").unwrap(),
                    "os.environ",
                ),
                (regex::Regex::new(r"os\.getenv").unwrap(), "os.getenv"),
                (regex::Regex::new(r"input\s*\(").unwrap(), "input()"),
                (regex::Regex::new(r"\.read\s*\(").unwrap(), "file.read"),
                (
                    regex::Regex::new(r"\.readline\s*\(").unwrap(),
                    "file.readline",
                ),
                (regex::Regex::new(r"json\.load\s*\(").unwrap(), "json.load"),
            ],
            typescript_patterns: vec![
                (regex::Regex::new(r"req\.body").unwrap(), "req.body"),
                (regex::Regex::new(r"req\.query").unwrap(), "req.query"),
                (regex::Regex::new(r"req\.params").unwrap(), "req.params"),
                (regex::Regex::new(r"req\.headers").unwrap(), "req.headers"),
                (regex::Regex::new(r"req\.cookies").unwrap(), "req.cookies"),
                (regex::Regex::new(r"process\.argv").unwrap(), "process.argv"),
                (regex::Regex::new(r"process\.env").unwrap(), "process.env"),
                (regex::Regex::new(r"prompt\s*\(").unwrap(), "prompt()"),
                (regex::Regex::new(r"readline").unwrap(), "readline"),
                (
                    regex::Regex::new(r"JSON\.parse\s*\(").unwrap(),
                    "JSON.parse",
                ),
                (
                    regex::Regex::new(r"document\.getElementById").unwrap(),
                    "document.getElementById",
                ),
                (
                    regex::Regex::new(r"document\.querySelector").unwrap(),
                    "document.querySelector",
                ),
                (regex::Regex::new(r"\.value").unwrap(), "input.value"),
                (
                    regex::Regex::new(r"window\.location").unwrap(),
                    "window.location",
                ),
                (
                    regex::Regex::new(r"URLSearchParams").unwrap(),
                    "URLSearchParams",
                ),
            ],
        }
    }

    /// Detect input source in a line.
    pub fn detect_input_source(&self, line: &str, lang: &str) -> Option<String> {
        let patterns = match lang.to_lowercase().as_str() {
            "python" | "py" => &self.python_patterns,
            "typescript" | "ts" | "javascript" | "js" => &self.typescript_patterns,
            _ => return None,
        };

        for (pattern, name) in patterns {
            if pattern.is_match(line) {
                return Some((*name).to_string());
            }
        }

        None
    }
}

// =============================================================================
// Sink Patterns
// =============================================================================

/// Patterns that indicate security-sensitive sinks.
pub struct SinkPatterns {
    python_patterns: Vec<(regex::Regex, &'static str, SinkType)>,
    typescript_patterns: Vec<(regex::Regex, &'static str, SinkType)>,
}

impl Default for SinkPatterns {
    fn default() -> Self {
        Self::new()
    }
}

impl SinkPatterns {
    /// Create sink patterns.
    pub fn new() -> Self {
        Self {
            python_patterns: vec![
                // Database
                (
                    regex::Regex::new(r"cursor\.execute\s*\(").unwrap(),
                    "cursor.execute",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"\.execute\s*\(").unwrap(),
                    ".execute",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"\.executemany\s*\(").unwrap(),
                    ".executemany",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"\.raw\s*\(").unwrap(),
                    ".raw",
                    SinkType::DatabaseQuery,
                ),
                // File operations
                (
                    regex::Regex::new(r"open\s*\(").unwrap(),
                    "open",
                    SinkType::FileOperation,
                ),
                (
                    regex::Regex::new(r"Path\s*\(").unwrap(),
                    "Path",
                    SinkType::FileOperation,
                ),
                (
                    regex::Regex::new(r"os\.remove\s*\(").unwrap(),
                    "os.remove",
                    SinkType::FileOperation,
                ),
                (
                    regex::Regex::new(r"os\.unlink\s*\(").unwrap(),
                    "os.unlink",
                    SinkType::FileOperation,
                ),
                (
                    regex::Regex::new(r"shutil\.").unwrap(),
                    "shutil",
                    SinkType::FileOperation,
                ),
                // System commands
                (
                    regex::Regex::new(r"os\.system\s*\(").unwrap(),
                    "os.system",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"subprocess\.(run|call|Popen)").unwrap(),
                    "subprocess",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"os\.popen\s*\(").unwrap(),
                    "os.popen",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"eval\s*\(").unwrap(),
                    "eval",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"exec\s*\(").unwrap(),
                    "exec",
                    SinkType::SystemCommand,
                ),
                // Network
                (
                    regex::Regex::new(r"requests\.(get|post|put|delete)").unwrap(),
                    "requests",
                    SinkType::NetworkRequest,
                ),
                (
                    regex::Regex::new(r"urllib\.request\.urlopen").unwrap(),
                    "urlopen",
                    SinkType::NetworkRequest,
                ),
                (
                    regex::Regex::new(r"httpx\.(get|post)").unwrap(),
                    "httpx",
                    SinkType::NetworkRequest,
                ),
                // HTML output
                (
                    regex::Regex::new(r"render_template\s*\(").unwrap(),
                    "render_template",
                    SinkType::HtmlOutput,
                ),
                (
                    regex::Regex::new(r"Markup\s*\(").unwrap(),
                    "Markup",
                    SinkType::HtmlOutput,
                ),
                // Serialization
                (
                    regex::Regex::new(r"pickle\.loads?\s*\(").unwrap(),
                    "pickle.load",
                    SinkType::Serialization,
                ),
                (
                    regex::Regex::new(r"yaml\.load\s*\(").unwrap(),
                    "yaml.load",
                    SinkType::Serialization,
                ),
                // Numeric
                (
                    regex::Regex::new(r"\[\s*\w+\s*\]").unwrap(),
                    "array_index",
                    SinkType::NumericOperation,
                ),
                (
                    regex::Regex::new(r"/\s*\w+").unwrap(),
                    "division",
                    SinkType::NumericOperation,
                ),
                // Regex
                (
                    regex::Regex::new(r"re\.(compile|match|search)\s*\([^,]*\w+").unwrap(),
                    "re.compile",
                    SinkType::RegexCompilation,
                ),
            ],
            typescript_patterns: vec![
                // Database
                (
                    regex::Regex::new(r"\.query\s*\(").unwrap(),
                    ".query",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"\.execute\s*\(").unwrap(),
                    ".execute",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"\.run\s*\(").unwrap(),
                    ".run",
                    SinkType::DatabaseQuery,
                ),
                (
                    regex::Regex::new(r"sql`").unwrap(),
                    "sql`",
                    SinkType::DatabaseQuery,
                ),
                // File operations
                (
                    regex::Regex::new(r"fs\.(readFile|writeFile|unlink)").unwrap(),
                    "fs",
                    SinkType::FileOperation,
                ),
                (
                    regex::Regex::new(r"path\.join\s*\(").unwrap(),
                    "path.join",
                    SinkType::FileOperation,
                ),
                // System commands
                (
                    regex::Regex::new(r"child_process\.(exec|spawn)").unwrap(),
                    "child_process",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"eval\s*\(").unwrap(),
                    "eval",
                    SinkType::SystemCommand,
                ),
                (
                    regex::Regex::new(r"new\s+Function\s*\(").unwrap(),
                    "new Function",
                    SinkType::SystemCommand,
                ),
                // Network
                (
                    regex::Regex::new(r"fetch\s*\(").unwrap(),
                    "fetch",
                    SinkType::NetworkRequest,
                ),
                (
                    regex::Regex::new(r"axios\.(get|post)").unwrap(),
                    "axios",
                    SinkType::NetworkRequest,
                ),
                (
                    regex::Regex::new(r"XMLHttpRequest").unwrap(),
                    "XMLHttpRequest",
                    SinkType::NetworkRequest,
                ),
                // HTML output
                (
                    regex::Regex::new(r"\.innerHTML\s*=").unwrap(),
                    "innerHTML",
                    SinkType::HtmlOutput,
                ),
                (
                    regex::Regex::new(r"document\.write\s*\(").unwrap(),
                    "document.write",
                    SinkType::HtmlOutput,
                ),
                (
                    regex::Regex::new(r"dangerouslySetInnerHTML").unwrap(),
                    "dangerouslySetInnerHTML",
                    SinkType::HtmlOutput,
                ),
                // Serialization
                (
                    regex::Regex::new(r"JSON\.parse\s*\([^)]*\w+").unwrap(),
                    "JSON.parse",
                    SinkType::Serialization,
                ),
                // Regex
                (
                    regex::Regex::new(r"new\s+RegExp\s*\([^)]*\w+").unwrap(),
                    "new RegExp",
                    SinkType::RegexCompilation,
                ),
            ],
        }
    }

    /// Detect sink in a line.
    pub fn detect_sink(&self, line: &str, lang: &str) -> Option<(String, SinkType)> {
        let patterns = match lang.to_lowercase().as_str() {
            "python" | "py" => &self.python_patterns,
            "typescript" | "ts" | "javascript" | "js" => &self.typescript_patterns,
            _ => return None,
        };

        for (pattern, name, sink_type) in patterns {
            if pattern.is_match(line) {
                return Some(((*name).to_string(), *sink_type));
            }
        }

        None
    }
}

// =============================================================================
// Input Validation Analyzer
// =============================================================================

/// Configuration for input validation analysis.
#[derive(Debug, Clone)]
pub struct InputValidationConfig {
    /// Minimum severity to report.
    pub min_severity: Severity,
    /// Whether to include recommended (not required) validations.
    pub include_recommended: bool,
    /// Whether to analyze framework validations (Django forms, Pydantic).
    pub analyze_framework_validation: bool,
    /// Maximum number of files to scan.
    pub max_files: usize,
    /// Language filter.
    pub language: Option<String>,
}

impl Default for InputValidationConfig {
    fn default() -> Self {
        Self {
            min_severity: Severity::Low,
            include_recommended: true,
            analyze_framework_validation: true,
            max_files: 0,
            language: None,
        }
    }
}

/// Analyzer for input validation issues.
pub struct InputValidationAnalyzer {
    config: InputValidationConfig,
    python_validation_patterns: PythonValidationPatterns,
    typescript_validation_patterns: TypeScriptValidationPatterns,
    input_source_patterns: InputSourcePatterns,
    sink_patterns: SinkPatterns,
}

impl Default for InputValidationAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl InputValidationAnalyzer {
    /// Create a new analyzer with default configuration.
    pub fn new() -> Self {
        Self::with_config(InputValidationConfig::default())
    }

    /// Create an analyzer with custom configuration.
    pub fn with_config(config: InputValidationConfig) -> Self {
        Self {
            config,
            python_validation_patterns: PythonValidationPatterns::new(),
            typescript_validation_patterns: TypeScriptValidationPatterns::new(),
            input_source_patterns: InputSourcePatterns::new(),
            sink_patterns: SinkPatterns::new(),
        }
    }

    /// Analyze a file for input validation issues.
    pub fn analyze_file(&self, path: &Path) -> Result<Vec<InputValidationFinding>> {
        let source = std::fs::read_to_string(path).map_err(|e| BrrrError::io_with_path(e, path))?;

        let lang = detect_language(path);
        let file_path = path.to_string_lossy().to_string();

        self.analyze_source(&source, &file_path, &lang)
    }

    /// Analyze source code for input validation issues.
    pub fn analyze_source(
        &self,
        source: &str,
        file_path: &str,
        lang: &str,
    ) -> Result<Vec<InputValidationFinding>> {
        let mut findings = Vec::new();
        let mut validation_state = ValidationState::new();

        let lines: Vec<&str> = source.lines().collect();

        // First pass: identify input sources and build validation state
        for (line_num, line) in lines.iter().enumerate() {
            let line_number = line_num + 1;

            // Check for input sources
            if let Some(input_source) = self.input_source_patterns.detect_input_source(line, lang) {
                // Try to extract variable name from assignment
                if let Some(var_name) = extract_assignment_target(line) {
                    validation_state.mark_user_input(&var_name, &input_source);

                    // Set definition location
                    let tracker = validation_state.get_or_create(&var_name);
                    tracker.definition_location =
                        Some(Location::single_line(file_path, line_number, 1));
                }
            }

            // Check for validations
            let validations = self.detect_validations(line, lang);
            for validation in validations {
                // Try to find which variable is being validated
                if let Some(var_name) = extract_validated_variable(line) {
                    validation_state.add_validation(&var_name, validation);
                }
            }

            // Check for assignments (propagation)
            if let Some((target, source_var)) = extract_assignment(line) {
                validation_state.propagate(&target, &source_var);
            }
        }

        // Second pass: check sinks against validation state
        for (line_num, line) in lines.iter().enumerate() {
            let line_number = line_num + 1;

            if let Some((sink_name, sink_type)) = self.sink_patterns.detect_sink(line, lang) {
                // Find variables used in this sink
                let used_vars = extract_variables_in_expression(line);

                for var_name in used_vars {
                    if let Some(tracker) = validation_state.get(&var_name) {
                        if tracker.is_user_input {
                            // Check validation requirements
                            let requirements = SinkValidationRequirements::for_sink(sink_type);
                            let check_result = requirements.check_validations(&tracker.validations);

                            // Report missing required validations
                            if !check_result.missing_required.is_empty() {
                                let mut finding = InputValidationFinding::new(
                                    Location::single_line(file_path, line_number, 1),
                                    tracker.input_source.as_deref().unwrap_or(&var_name),
                                    &sink_name,
                                    sink_type,
                                    check_result.missing_required,
                                );
                                finding = finding
                                    .with_variable(&var_name)
                                    .with_code_snippet(line.trim().to_string())
                                    .with_applied_validation(
                                        tracker.validations.iter().copied().collect(),
                                    );

                                if finding.severity >= self.config.min_severity {
                                    findings.push(finding);
                                }
                            }

                            // Report missing recommended validations
                            if self.config.include_recommended
                                && !check_result.missing_recommended.is_empty()
                            {
                                let mut finding = InputValidationFinding::new(
                                    Location::single_line(file_path, line_number, 1),
                                    tracker.input_source.as_deref().unwrap_or(&var_name),
                                    &sink_name,
                                    sink_type,
                                    check_result.missing_recommended,
                                )
                                .as_recommended();

                                finding = finding
                                    .with_variable(&var_name)
                                    .with_code_snippet(line.trim().to_string())
                                    .with_applied_validation(
                                        tracker.validations.iter().copied().collect(),
                                    )
                                    .with_confidence(Confidence::Medium);

                                if finding.severity >= self.config.min_severity {
                                    findings.push(finding);
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(findings)
    }

    /// Detect validations in a line.
    fn detect_validations(&self, line: &str, lang: &str) -> Vec<ValidationType> {
        match lang.to_lowercase().as_str() {
            "python" | "py" => self.python_validation_patterns.detect_validations(line),
            "typescript" | "ts" | "javascript" | "js" => {
                self.typescript_validation_patterns.detect_validations(line)
            }
            _ => Vec::new(),
        }
    }

    /// Analyze a directory for input validation issues.
    pub fn analyze_directory(&self, path: &Path) -> Result<InputValidationScanResult> {
        let path_str = path
            .to_str()
            .ok_or_else(|| BrrrError::InvalidArgument("Invalid path encoding".to_string()))?;

        let scan_config = match &self.config.language {
            Some(lang) => ScanConfig::for_language(lang),
            None => ScanConfig::default(),
        };

        let scanner = ProjectScanner::new(path_str)?;
        let scan_result = scanner.scan_with_config(&scan_config)?;

        let files: Vec<_> =
            if self.config.max_files > 0 && scan_result.files.len() > self.config.max_files {
                scan_result
                    .files
                    .into_iter()
                    .take(self.config.max_files)
                    .collect()
            } else {
                scan_result.files
            };

        let mut all_findings = Vec::new();
        let mut files_scanned = 0;
        let mut files_with_findings = 0;

        for file_path in &files {
            if let Ok(findings) = self.analyze_file(file_path) {
                files_scanned += 1;
                if !findings.is_empty() {
                    files_with_findings += 1;
                    all_findings.extend(findings);
                }
            }
        }

        Ok(InputValidationScanResult {
            findings: all_findings,
            files_scanned,
            files_with_findings,
        })
    }
}

/// Result of scanning for input validation issues.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputValidationScanResult {
    /// All findings.
    pub findings: Vec<InputValidationFinding>,
    /// Number of files scanned.
    pub files_scanned: usize,
    /// Number of files with findings.
    pub files_with_findings: usize,
}

impl InputValidationScanResult {
    /// Get findings grouped by severity.
    pub fn by_severity(&self) -> HashMap<Severity, Vec<&InputValidationFinding>> {
        let mut grouped = HashMap::new();
        for finding in &self.findings {
            grouped
                .entry(finding.severity)
                .or_insert_with(Vec::new)
                .push(finding);
        }
        grouped
    }

    /// Get findings grouped by sink type.
    pub fn by_sink_type(&self) -> HashMap<SinkType, Vec<&InputValidationFinding>> {
        let mut grouped = HashMap::new();
        for finding in &self.findings {
            grouped
                .entry(finding.sink_type)
                .or_insert_with(Vec::new)
                .push(finding);
        }
        grouped
    }

    /// Check if there are any critical findings.
    pub fn has_critical(&self) -> bool {
        self.findings
            .iter()
            .any(|f| f.severity >= Severity::Critical)
    }
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Detect language from file extension.
fn detect_language(path: &Path) -> String {
    match path.extension().and_then(|e| e.to_str()) {
        Some("py") => "python".to_string(),
        Some("ts") | Some("tsx") => "typescript".to_string(),
        Some("js") | Some("jsx") => "javascript".to_string(),
        Some("go") => "go".to_string(),
        Some("rs") => "rust".to_string(),
        _ => "unknown".to_string(),
    }
}

/// Extract assignment target from a line.
fn extract_assignment_target(line: &str) -> Option<String> {
    let re = regex::Regex::new(r"^\s*(\w+)\s*=").ok()?;
    re.captures(line)
        .and_then(|caps| caps.get(1))
        .map(|m| m.as_str().to_string())
}

/// Extract assignment source and target.
fn extract_assignment(line: &str) -> Option<(String, String)> {
    let re = regex::Regex::new(r"^\s*(\w+)\s*=\s*(\w+)").ok()?;
    re.captures(line).map(|caps| {
        (
            caps.get(1)
                .map(|m| m.as_str().to_string())
                .unwrap_or_default(),
            caps.get(2)
                .map(|m| m.as_str().to_string())
                .unwrap_or_default(),
        )
    })
}

/// Extract the variable being validated.
fn extract_validated_variable(line: &str) -> Option<String> {
    // Look for patterns like isinstance(var, ...), len(var), var in [...]
    let patterns = [
        regex::Regex::new(r"isinstance\s*\(\s*(\w+)\s*,").ok()?,
        regex::Regex::new(r"len\s*\(\s*(\w+)\s*\)").ok()?,
        regex::Regex::new(r"type\s*\(\s*(\w+)\s*\)").ok()?,
        regex::Regex::new(r"(\w+)\s+in\s+\[").ok()?,
        regex::Regex::new(r"if\s+not\s+(\w+)").ok()?,
        regex::Regex::new(r"if\s+(\w+)\s+is\s+None").ok()?,
        regex::Regex::new(r"if\s+(\w+)\s*:").ok()?,
    ];

    for pattern in &patterns {
        if let Some(caps) = pattern.captures(line) {
            if let Some(m) = caps.get(1) {
                return Some(m.as_str().to_string());
            }
        }
    }

    None
}

/// Extract variables used in an expression.
fn extract_variables_in_expression(line: &str) -> Vec<String> {
    let re = regex::Regex::new(r"\b([a-z_][a-z0-9_]*)\b").unwrap();
    let keywords = [
        "if",
        "else",
        "for",
        "while",
        "in",
        "not",
        "and",
        "or",
        "is",
        "None",
        "True",
        "False",
        "return",
        "def",
        "class",
        "import",
        "from",
        "as",
        "try",
        "except",
        "finally",
        "raise",
        "with",
        "yield",
        "lambda",
        "pass",
        "break",
        "continue",
        "global",
        "nonlocal",
        "assert",
        "del",
        "elif",
        "async",
        "await",
        "isinstance",
        "len",
        "type",
        "open",
        "print",
        "str",
        "int",
        "float",
        "bool",
        "list",
        "dict",
        "set",
        "const",
        "let",
        "var",
        "function",
        "typeof",
        "instanceof",
        "new",
        "execute",
        "query",
        "run",
        "call",
        "read",
        "write",
        "get",
        "post",
    ];

    re.captures_iter(line)
        .filter_map(|cap| cap.get(1))
        .map(|m| m.as_str().to_string())
        .filter(|s| !keywords.contains(&s.as_str()))
        .collect()
}

// =============================================================================
// Public API
// =============================================================================

/// Analyze a path for input validation issues.
///
/// # Arguments
///
/// * `path` - Path to file or directory
/// * `lang` - Optional language filter
///
/// # Returns
///
/// Vector of input validation findings.
pub fn analyze_input_validation(
    path: impl AsRef<Path>,
    lang: Option<&str>,
) -> Result<Vec<InputValidationFinding>> {
    let path = path.as_ref();
    let config = InputValidationConfig {
        language: lang.map(String::from),
        ..Default::default()
    };
    let analyzer = InputValidationAnalyzer::with_config(config);

    if path.is_file() {
        analyzer.analyze_file(path)
    } else {
        analyzer.analyze_directory(path).map(|r| r.findings)
    }
}

/// Scan a path (file or directory) for input validation issues.
///
/// # Arguments
///
/// * `path` - Path to file or directory
/// * `config` - Configuration options
///
/// # Returns
///
/// Scan result with findings and statistics.
pub fn scan_input_validation(
    path: impl AsRef<Path>,
    config: InputValidationConfig,
) -> Result<InputValidationScanResult> {
    let path = path.as_ref();
    let analyzer = InputValidationAnalyzer::with_config(config);

    if path.is_file() {
        // Single file analysis
        let findings = analyzer.analyze_file(path)?;
        let files_with_findings = if findings.is_empty() { 0 } else { 1 };
        Ok(InputValidationScanResult {
            findings,
            files_scanned: 1,
            files_with_findings,
        })
    } else {
        // Directory analysis
        analyzer.analyze_directory(path)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validation_type_display() {
        assert_eq!(ValidationType::TypeCheck.to_string(), "type_check");
        assert_eq!(ValidationType::LengthCheck.to_string(), "length_check");
    }

    #[test]
    fn test_sink_validation_requirements() {
        let reqs = SinkValidationRequirements::for_sink(SinkType::DatabaseQuery);
        assert!(!reqs.required_validations.is_empty());
        assert!(reqs
            .required_validations
            .contains(&ValidationType::TypeCheck));
    }

    #[test]
    fn test_validation_check() {
        let reqs = SinkValidationRequirements::for_sink(SinkType::DatabaseQuery);
        let mut applied = HashSet::new();

        // No validations applied
        let result = reqs.check_validations(&applied);
        assert!(!result.is_valid);
        assert!(!result.missing_required.is_empty());

        // Add required validation
        applied.insert(ValidationType::TypeCheck);
        let result = reqs.check_validations(&applied);
        assert!(result.is_valid);
        assert!(result.missing_required.is_empty());
    }

    #[test]
    fn test_python_validation_detection() {
        let patterns = PythonValidationPatterns::new();

        // Type check
        let validations = patterns.detect_validations("if isinstance(x, str):");
        assert!(validations.contains(&ValidationType::TypeCheck));

        // Length check
        let validations = patterns.detect_validations("if len(x) > 100:");
        assert!(validations.contains(&ValidationType::LengthCheck));

        // Null check
        let validations = patterns.detect_validations("if not user_input:");
        assert!(validations.contains(&ValidationType::NullCheck));

        // Format check
        let validations = patterns.detect_validations("if re.match(r'^[a-z]+$', x):");
        assert!(validations.contains(&ValidationType::FormatCheck));
    }

    #[test]
    fn test_typescript_validation_detection() {
        let patterns = TypeScriptValidationPatterns::new();

        // Type check
        let validations = patterns.detect_validations("if (typeof x === 'string')");
        assert!(validations.contains(&ValidationType::TypeCheck));

        // Length check
        let validations = patterns.detect_validations("if (x.length > 100)");
        assert!(validations.contains(&ValidationType::LengthCheck));

        // Null check
        let validations = patterns.detect_validations("const y = x ?? 'default'");
        assert!(validations.contains(&ValidationType::NullCheck));
    }

    #[test]
    fn test_input_source_detection() {
        let patterns = InputSourcePatterns::new();

        // Python
        assert!(patterns
            .detect_input_source("x = request.args.get('id')", "python")
            .is_some());
        assert!(patterns
            .detect_input_source("data = request.json.get('data')", "python")
            .is_some());

        // TypeScript
        assert!(patterns
            .detect_input_source("const id = req.params.id", "typescript")
            .is_some());
        assert!(patterns
            .detect_input_source("const data = req.body", "typescript")
            .is_some());
    }

    #[test]
    fn test_sink_detection() {
        let patterns = SinkPatterns::new();

        // Python
        let result = patterns.detect_sink("cursor.execute(query)", "python");
        assert!(result.is_some());
        assert_eq!(result.unwrap().1, SinkType::DatabaseQuery);

        let result = patterns.detect_sink("os.system(cmd)", "python");
        assert!(result.is_some());
        assert_eq!(result.unwrap().1, SinkType::SystemCommand);

        // TypeScript
        let result = patterns.detect_sink("element.innerHTML = content", "typescript");
        assert!(result.is_some());
        assert_eq!(result.unwrap().1, SinkType::HtmlOutput);
    }

    #[test]
    fn test_extract_variables() {
        let vars = extract_variables_in_expression("cursor.execute(user_query)");
        assert!(vars.contains(&"cursor".to_string()));
        assert!(vars.contains(&"user_query".to_string()));
        assert!(!vars.contains(&"execute".to_string()));
    }

    #[test]
    fn test_analyzer_simple_case() {
        let source = r#"
user_id = request.args.get('id')
cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")
"#;

        let analyzer = InputValidationAnalyzer::new();
        let findings = analyzer
            .analyze_source(source, "test.py", "python")
            .unwrap();

        // Should find missing validation before database query
        assert!(!findings.is_empty());
    }

    #[test]
    fn test_analyzer_with_validation() {
        let source = r#"
user_id = request.args.get('id')
if not isinstance(user_id, str):
    raise ValueError()
if len(user_id) > 100:
    raise ValueError()
cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
"#;

        let analyzer = InputValidationAnalyzer::new();
        let findings = analyzer
            .analyze_source(source, "test.py", "python")
            .unwrap();

        // Required validation is present, should have fewer/no required findings
        let required_findings: Vec<_> = findings.iter().filter(|f| f.is_required).collect();
        assert!(required_findings.is_empty());
    }

    #[test]
    fn test_finding_severity() {
        let finding = InputValidationFinding::new(
            Location::single_line("test.py", 10, 1),
            "request.args.get('id')",
            "cursor.execute",
            SinkType::SystemCommand,
            vec![ValidationType::SanitizationCheck],
        );

        // System command without sanitization should be critical
        assert_eq!(finding.severity, Severity::Critical);
    }

    #[test]
    fn test_finding_recommendation() {
        let finding = InputValidationFinding::new(
            Location::single_line("test.py", 10, 1),
            "user_input",
            "cursor.execute",
            SinkType::DatabaseQuery,
            vec![ValidationType::TypeCheck],
        );

        assert!(!finding.recommendation.is_empty());
        assert!(finding.recommendation.contains("isinstance"));
    }
}
