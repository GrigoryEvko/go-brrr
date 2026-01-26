//! Security annotations for source/sink/sanitizer marking.
//!
//! This module provides annotation types for marking functions with their
//! security roles in taint analysis:
//!
//! - **Sources**: Functions that introduce tainted data (user input, file reads, etc.)
//! - **Sinks**: Functions vulnerable to tainted data (SQL queries, command execution, etc.)
//! - **Sanitizers**: Functions that remove taint (escaping, validation, etc.)
//!
//! # F* Reference (SecurityTypes.fst lines 1095-1120)
//!
//! ```fstar
//! noeq type source_annotation = { src_name: string; src_taints: list taint_kind; src_origin: string }
//! noeq type sink_annotation = { snk_name: string; snk_rejects: list taint_kind; snk_params: list nat }
//! noeq type sanitizer_annotation = { san_name: string; san_removes: list taint_kind; san_param: nat }
//! ```
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::security::{SourceAnnotation, SinkAnnotation, SanitizerAnnotation, TaintKind};
//!
//! // Mark request.get_param as a source of user input
//! let source = SourceAnnotation::user_input(name);
//!
//! // Mark db.execute as a SQL injection sink
//! let sink = SinkAnnotation::sql_query(name, 0);
//!
//! // Mark escape_html as an XSS sanitizer
//! let sanitizer = SanitizerAnnotation::html_escape(name, 0);
//! ```

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::labels::{Integrity, SecurityLabel};
use super::taint::{TaintKind, TaintSet};
use crate::effects::EffectRow;
use crate::types::BrrrType;

// =============================================================================
// Source Annotation
// =============================================================================

/// Annotation marking a function as a taint source.
///
/// Sources are functions that introduce potentially untrusted data into
/// the program. When data flows from a source to a sink without passing
/// through an appropriate sanitizer, a vulnerability is detected.
///
/// # F* Mapping
///
/// Maps to F* SecurityTypes.fst:
/// ```fstar
/// noeq type source_annotation = {
///   src_name   : string;
///   src_taints : list taint_kind;
///   src_origin : string;
/// }
/// ```
///
/// # Fields
///
/// - `name`: Interned identifier of the source function
/// - `taints`: List of taint kinds this source introduces
/// - `origin`: Interned origin descriptor (where taint originates)
/// - `tainted_return`: Whether the return value carries taint
/// - `tainted_params`: Which output parameters are tainted (by index)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SourceAnnotation {
    /// Name of the source function (interned)
    pub name: Spur,

    /// Taint kinds introduced by this source
    pub taints: Vec<TaintKind>,

    /// Origin descriptor (interned) - where taint originates
    /// Maps to F* src_origin
    pub origin: Spur,

    /// Whether the return value is tainted
    pub tainted_return: bool,

    /// Which parameters are tainted (0-indexed, for out-params)
    pub tainted_params: Vec<usize>,
}

impl SourceAnnotation {
    /// Create a new source annotation.
    ///
    /// By default, the return value is tainted and no parameters are tainted.
    pub fn new(name: Spur, taints: Vec<TaintKind>, origin: Spur) -> Self {
        Self {
            name,
            taints,
            origin,
            tainted_return: true,
            tainted_params: Vec::new(),
        }
    }

    /// Create a source for user input (all common web taints).
    ///
    /// User input typically carries all web-related vulnerability risks:
    /// SQLi, XSS, CMDi, PathTraversal, SSRF, OpenRedirect.
    ///
    /// Requires passing an interned "user_input" origin.
    pub fn user_input(name: Spur, origin: Spur) -> Self {
        Self::new(name, TaintKind::WEB_COMMON.to_vec(), origin)
    }

    /// Create a source for file content.
    pub fn file_read(name: Spur, origin: Spur) -> Self {
        Self::new(name, vec![TaintKind::PathTraversal], origin)
    }

    /// Create a source for environment variables.
    pub fn env_var(name: Spur, origin: Spur) -> Self {
        Self::new(
            name,
            vec![TaintKind::CMDi, TaintKind::PathTraversal],
            origin,
        )
    }

    /// Create a source for HTTP request data.
    pub fn http_request(name: Spur, origin: Spur) -> Self {
        Self::new(
            name,
            vec![
                TaintKind::SQLi,
                TaintKind::XSS,
                TaintKind::CMDi,
                TaintKind::PathTraversal,
                TaintKind::SSRF,
                TaintKind::HeaderInjection,
            ],
            origin,
        )
    }

    /// Create a source for deserialized data.
    pub fn deserialized(name: Spur, origin: Spur) -> Self {
        Self::new(
            name,
            vec![TaintKind::Deserialization, TaintKind::CodeInjection],
            origin,
        )
    }

    /// Create a source for database query results.
    pub fn database_result(name: Spur, origin: Spur) -> Self {
        Self::new(name, vec![TaintKind::XSS], origin)
    }

    /// Create a source for external API responses.
    pub fn external_api(name: Spur, origin: Spur) -> Self {
        Self::new(
            name,
            vec![TaintKind::XSS, TaintKind::SSRF],
            origin,
        )
    }

    /// Mark which parameters are tainted (for out-params or callbacks).
    #[must_use]
    pub fn with_tainted_params(mut self, params: Vec<usize>) -> Self {
        self.tainted_params = params;
        self
    }

    /// Mark that the return value is not tainted.
    #[must_use]
    pub fn without_tainted_return(mut self) -> Self {
        self.tainted_return = false;
        self
    }

    /// Check if this source introduces a specific taint kind.
    pub fn introduces(&self, kind: TaintKind) -> bool {
        self.taints.contains(&kind)
    }
}

// =============================================================================
// Sink Annotation
// =============================================================================

/// Annotation marking a function as a taint sink.
///
/// Sinks are functions where tainted data can cause security vulnerabilities.
/// When tainted data reaches a sink without sanitization, the analysis
/// reports a finding.
///
/// # F* Mapping
///
/// Maps to F* SecurityTypes.fst:
/// ```fstar
/// noeq type sink_annotation = {
///   snk_name     : string;
///   snk_rejects  : list taint_kind;
///   snk_params   : list nat;
/// }
/// ```
///
/// # Fields
///
/// - `name`: Interned identifier of the sink function
/// - `rejects`: List of taint kinds that cause vulnerabilities at this sink
/// - `params`: Which parameters must be clean (by index) - maps to snk_params
/// - `vulnerability`: Description of the vulnerability type (extension)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SinkAnnotation {
    /// Name of the sink function (interned)
    pub name: Spur,

    /// Taint kinds that cause vulnerabilities at this sink
    /// Maps to F* snk_rejects
    pub rejects: Vec<TaintKind>,

    /// Which parameters must be clean (0-indexed)
    /// Maps to F* snk_params : list nat
    pub params: Vec<u32>,

    /// Description of the vulnerability (extension beyond F* spec)
    pub vulnerability: String,
}

impl SinkAnnotation {
    /// Create a new sink annotation.
    pub fn new(
        name: Spur,
        rejects: Vec<TaintKind>,
        params: Vec<u32>,
        vulnerability: impl Into<String>,
    ) -> Self {
        Self {
            name,
            rejects,
            params,
            vulnerability: vulnerability.into(),
        }
    }

    /// Create a SQL query execution sink.
    pub fn sql_query(name: Spur, query_param: u32) -> Self {
        Self::new(name, vec![TaintKind::SQLi], vec![query_param], "SQL Injection")
    }

    /// Create a command execution sink.
    pub fn command_exec(name: Spur, cmd_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::CMDi],
            vec![cmd_param],
            "Command Injection",
        )
    }

    /// Create an HTML output sink.
    pub fn html_output(name: Spur, content_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::XSS],
            vec![content_param],
            "Cross-Site Scripting",
        )
    }

    /// Create a file path sink.
    pub fn file_path(name: Spur, path_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::PathTraversal],
            vec![path_param],
            "Path Traversal",
        )
    }

    /// Create a URL sink (for redirects or SSRF).
    pub fn url(name: Spur, url_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::SSRF, TaintKind::OpenRedirect],
            vec![url_param],
            "SSRF/Open Redirect",
        )
    }

    /// Create an eval/code execution sink.
    pub fn code_eval(name: Spur, code_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::CodeInjection],
            vec![code_param],
            "Code Injection",
        )
    }

    /// Create an LDAP query sink.
    pub fn ldap_query(name: Spur, query_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::LDAPi],
            vec![query_param],
            "LDAP Injection",
        )
    }

    /// Create an XML processing sink.
    pub fn xml_parse(name: Spur, xml_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::XMLi],
            vec![xml_param],
            "XML Injection/XXE",
        )
    }

    /// Create a template rendering sink.
    pub fn template_render(name: Spur, template_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::TemplateInjection],
            vec![template_param],
            "Template Injection",
        )
    }

    /// Create a regex compilation sink.
    pub fn regex_compile(name: Spur, pattern_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::ReDoS],
            vec![pattern_param],
            "Regular Expression DoS",
        )
    }

    /// Create an HTTP header sink.
    pub fn http_header(name: Spur, header_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::HeaderInjection],
            vec![header_param],
            "Header Injection",
        )
    }

    /// Create a log output sink.
    pub fn log_output(name: Spur, message_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::LogInjection],
            vec![message_param],
            "Log Injection",
        )
    }

    /// Create a deserialization sink.
    pub fn deserialize(name: Spur, data_param: u32) -> Self {
        Self::new(
            name,
            vec![TaintKind::Deserialization],
            vec![data_param],
            "Unsafe Deserialization",
        )
    }

    /// Check if this sink rejects a specific taint kind.
    pub fn rejects_taint(&self, taint: TaintKind) -> bool {
        self.rejects.contains(&taint)
    }

    /// Check if a parameter is sensitive (must be clean).
    pub fn is_param_sensitive(&self, param_index: u32) -> bool {
        self.params.contains(&param_index)
    }

    /// Get all sensitive parameter indices.
    pub fn sensitive_indices(&self) -> &[u32] {
        &self.params
    }
}

// =============================================================================
// Sanitizer Annotation
// =============================================================================

/// Annotation marking a function as a taint sanitizer.
///
/// Sanitizers are functions that remove or neutralize taint by properly
/// escaping, encoding, or validating input data. When data passes through
/// an appropriate sanitizer, the corresponding taint kind is removed.
///
/// # F* Mapping
///
/// Maps to F* SecurityTypes.fst:
/// ```fstar
/// noeq type sanitizer_annotation = {
///   san_name    : string;
///   san_removes : list taint_kind;
///   san_param   : nat;
/// }
/// ```
///
/// # Fields
///
/// - `name`: Interned identifier of the sanitizer function
/// - `removes`: List of taint kinds this sanitizer removes
/// - `param`: Which parameter receives the tainted input (maps to san_param)
/// - `returns_sanitized`: Whether the return value is sanitized (extension)
/// - `output_param`: Which parameter receives sanitized output (extension)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SanitizerAnnotation {
    /// Name of the sanitizer function (interned)
    pub name: Spur,

    /// Taint kinds removed by this sanitizer
    /// Maps to F* san_removes
    pub removes: Vec<TaintKind>,

    /// Which parameter receives tainted input (0-indexed)
    /// Maps to F* san_param : nat
    pub param: u32,

    /// Whether the return value is sanitized (extension beyond F* spec)
    pub returns_sanitized: bool,

    /// Which output parameter receives sanitized value (extension beyond F* spec)
    pub output_param: Option<u32>,
}

impl SanitizerAnnotation {
    /// Create a new sanitizer annotation.
    ///
    /// By default, the sanitized value is returned (not via out-param).
    pub fn new(name: Spur, removes: Vec<TaintKind>, param: u32) -> Self {
        Self {
            name,
            removes,
            param,
            returns_sanitized: true,
            output_param: None,
        }
    }

    /// Create a SQL escaping sanitizer.
    pub fn sql_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::SQLi], param)
    }

    /// Create an HTML escaping sanitizer.
    pub fn html_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::XSS], param)
    }

    /// Create a path canonicalization sanitizer.
    pub fn path_canonicalize(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::PathTraversal], param)
    }

    /// Create a URL validation sanitizer.
    pub fn url_validate(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::SSRF, TaintKind::OpenRedirect], param)
    }

    /// Create a command argument escaping sanitizer.
    pub fn shell_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::CMDi], param)
    }

    /// Create an LDAP escaping sanitizer.
    pub fn ldap_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::LDAPi], param)
    }

    /// Create an XML escaping sanitizer.
    pub fn xml_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::XMLi], param)
    }

    /// Create a regex pattern sanitizer.
    pub fn regex_escape(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::ReDoS], param)
    }

    /// Create a header value sanitizer.
    pub fn header_sanitize(name: Spur, param: u32) -> Self {
        Self::new(name, vec![TaintKind::HeaderInjection], param)
    }

    /// Create a generic validator that removes all taints.
    ///
    /// Use sparingly - most sanitizers should be specific about
    /// which taint kinds they remove.
    pub fn validate_all(name: Spur, param: u32) -> Self {
        Self::new(name, TaintKind::ALL.to_vec(), param)
    }

    /// Mark that sanitized output goes to an out-param instead of return.
    #[must_use]
    pub fn with_output_param(mut self, out_param: u32) -> Self {
        self.output_param = Some(out_param);
        self.returns_sanitized = false;
        self
    }

    /// Check if this sanitizer removes a specific taint kind.
    pub fn removes_taint(&self, kind: TaintKind) -> bool {
        self.removes.contains(&kind)
    }

    /// Check if this sanitizer is appropriate for a given sink.
    ///
    /// A sanitizer is appropriate if it removes at least one taint kind
    /// that the sink rejects.
    pub fn protects_against(&self, sink: &SinkAnnotation) -> bool {
        self.removes.iter().any(|r| sink.rejects.contains(r))
    }

    /// Get the input parameter index.
    pub const fn input_param(&self) -> u32 {
        self.param
    }
}

// =============================================================================
// Security Role
// =============================================================================

/// Security role of a function in taint analysis.
///
/// Each function can have at most one security role. If a function both
/// introduces and sanitizes taint, it should be split into separate functions
/// or modeled as a transformer.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SecurityRole {
    /// No special security role (default)
    None,

    /// Taint source - introduces tainted data
    Source(SourceAnnotation),

    /// Taint sink - vulnerable to tainted data
    Sink(SinkAnnotation),

    /// Sanitizer - removes or neutralizes taint
    Sanitizer(SanitizerAnnotation),

    /// Validator - like sanitizer but returns bool instead of sanitized value
    /// The original value is considered sanitized only if validator returns true
    Validator(SanitizerAnnotation),
}

impl Default for SecurityRole {
    fn default() -> Self {
        Self::None
    }
}

impl SecurityRole {
    /// Check if this role is a source.
    pub fn is_source(&self) -> bool {
        matches!(self, Self::Source(_))
    }

    /// Check if this role is a sink.
    pub fn is_sink(&self) -> bool {
        matches!(self, Self::Sink(_))
    }

    /// Check if this role is a sanitizer.
    pub fn is_sanitizer(&self) -> bool {
        matches!(self, Self::Sanitizer(_))
    }

    /// Check if this role is a validator.
    pub fn is_validator(&self) -> bool {
        matches!(self, Self::Validator(_))
    }

    /// Get the source annotation if this is a source.
    pub fn as_source(&self) -> Option<&SourceAnnotation> {
        match self {
            Self::Source(s) => Some(s),
            _ => None,
        }
    }

    /// Get the sink annotation if this is a sink.
    pub fn as_sink(&self) -> Option<&SinkAnnotation> {
        match self {
            Self::Sink(s) => Some(s),
            _ => None,
        }
    }

    /// Get the sanitizer annotation if this is a sanitizer or validator.
    pub fn as_sanitizer(&self) -> Option<&SanitizerAnnotation> {
        match self {
            Self::Sanitizer(s) | Self::Validator(s) => Some(s),
            _ => None,
        }
    }
}

// =============================================================================
// Security-Aware Types
// =============================================================================

/// Security-aware parameter with taint information.
///
/// Tracks which taints a parameter may carry, enabling precise
/// taint analysis at function boundaries.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SecParam {
    /// Parameter name (interned)
    pub name: Option<Spur>,

    /// Parameter type with security annotations
    pub ty: SecType,

    /// Index in the parameter list
    pub index: u32,
}

impl SecParam {
    /// Create a new security-aware parameter.
    pub fn new(name: Option<Spur>, ty: SecType, index: u32) -> Self {
        Self { name, ty, index }
    }

    /// Create an unnamed parameter.
    pub fn unnamed(ty: SecType, index: u32) -> Self {
        Self {
            name: None,
            ty,
            index,
        }
    }

    /// Create a named parameter.
    pub fn named(name: Spur, ty: SecType, index: u32) -> Self {
        Self {
            name: Some(name),
            ty,
            index,
        }
    }
}

/// Security-aware type wrapper.
///
/// Wraps a base type with security label information for
/// information flow analysis.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SecType {
    /// Underlying type
    pub base: BrrrType,

    /// Security label for this type
    pub label: SecurityLabel,

    /// Expected taints (for function parameters that should reject certain taints)
    pub expected_taints: Option<Vec<TaintKind>>,
}

impl SecType {
    /// Create a new security type with default (bottom) label.
    pub fn new(base: BrrrType) -> Self {
        Self {
            base,
            label: SecurityLabel::public_trusted(),
            expected_taints: None,
        }
    }

    /// Create a security type with a specific label.
    pub fn with_label(base: BrrrType, label: SecurityLabel) -> Self {
        Self {
            base,
            label,
            expected_taints: None,
        }
    }

    /// Create a security type with expected taints (for sink parameters).
    pub fn with_expected_taints(base: BrrrType, taints: Vec<TaintKind>) -> Self {
        Self {
            base,
            label: SecurityLabel::public_trusted(),
            expected_taints: Some(taints),
        }
    }

    /// Create a tainted security type.
    pub fn tainted(base: BrrrType, taints: TaintSet) -> Self {
        Self {
            base,
            label: SecurityLabel::with_taints(
                super::labels::Confidentiality::Public,
                Integrity::Untrusted,
                taints,
            ),
            expected_taints: None,
        }
    }

    /// Check if this type carries any taints.
    pub fn has_taints(&self) -> bool {
        self.label.has_taints()
    }

    /// Get the taints this type carries.
    pub fn taints(&self) -> &TaintSet {
        self.label.taints()
    }
}

impl Default for SecType {
    fn default() -> Self {
        Self::new(BrrrType::UNIT)
    }
}

/// Security-aware function type.
///
/// Extends the standard function type with security role information
/// for taint analysis at function boundaries.
///
/// Maps conceptually to F* sec_func_type pattern.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SecFuncType {
    /// Security-aware parameters
    pub params: Vec<SecParam>,

    /// Return type with security information
    pub return_type: SecType,

    /// Effect row for this function
    pub effects: EffectRow,

    /// Security role of this function (source, sink, sanitizer, etc.)
    pub role: SecurityRole,
}

impl SecFuncType {
    /// Create a new security function type with no special role.
    pub fn new(params: Vec<SecParam>, return_type: SecType, effects: EffectRow) -> Self {
        Self {
            params,
            return_type,
            effects,
            role: SecurityRole::None,
        }
    }

    /// Create a pure security function type (no effects).
    pub fn pure(params: Vec<SecParam>, return_type: SecType) -> Self {
        Self {
            params,
            return_type,
            effects: EffectRow::PURE,
            role: SecurityRole::None,
        }
    }

    /// Set the security role for this function.
    #[must_use]
    pub fn with_role(mut self, role: SecurityRole) -> Self {
        self.role = role;
        self
    }

    /// Check if this function is a taint source.
    pub fn is_source(&self) -> bool {
        self.role.is_source()
    }

    /// Check if this function is a taint sink.
    pub fn is_sink(&self) -> bool {
        self.role.is_sink()
    }

    /// Check if this function is a sanitizer.
    pub fn is_sanitizer(&self) -> bool {
        self.role.is_sanitizer()
    }

    /// Check if this function is a validator.
    pub fn is_validator(&self) -> bool {
        self.role.is_validator()
    }

    /// Get the taints introduced if this is a source.
    pub fn source_taints(&self) -> Option<&[TaintKind]> {
        self.role.as_source().map(|s| s.taints.as_slice())
    }

    /// Get the taints rejected if this is a sink.
    pub fn sink_rejects(&self) -> Option<&[TaintKind]> {
        self.role.as_sink().map(|s| s.rejects.as_slice())
    }

    /// Get the taints removed if this is a sanitizer.
    pub fn sanitizer_removes(&self) -> Option<&[TaintKind]> {
        self.role.as_sanitizer().map(|s| s.removes.as_slice())
    }
}

impl Default for SecFuncType {
    fn default() -> Self {
        Self {
            params: Vec::new(),
            return_type: SecType::default(),
            effects: EffectRow::PURE,
            role: SecurityRole::None,
        }
    }
}

// =============================================================================
// Label Operations
// =============================================================================

/// Remove specific taints from a security label (sanitization).
///
/// This function removes the specified taint kinds from the label's taint set,
/// modeling the effect of a sanitizer. If all taints are removed, the label
/// becomes clean.
///
/// Maps to F* sanitize_label operation.
///
/// # Example
///
/// ```ignore
/// let tainted = SecurityLabel::with_taints(
///     Confidentiality::Public,
///     Integrity::Untrusted,
///     TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS]),
/// );
/// let sanitized = sanitize_label(&[TaintKind::SQLi], &tainted);
/// // sanitized still has XSS but not SQLi
/// ```
#[must_use]
pub fn sanitize_label(to_remove: &[TaintKind], label: &SecurityLabel) -> SecurityLabel {
    let mut new_taints = label.taints.clone();
    new_taints.remove(to_remove);

    SecurityLabel {
        confidentiality: label.confidentiality,
        integrity: if new_taints.is_empty() {
            Integrity::Trusted
        } else {
            label.integrity
        },
        dlm: label.dlm.clone(),
        taints: new_taints,
    }
}

/// Endorse a label (upgrade to trusted) if it has no taints.
///
/// This operation only succeeds if the label is completely clean (no taints).
/// It represents the point where data has been fully validated and can be
/// trusted for further operations.
///
/// Returns None if the label still has taints, Some with upgraded integrity
/// if the label is clean.
///
/// Maps to F* endorse_label operation.
///
/// # Example
///
/// ```ignore
/// let clean_label = SecurityLabel::public_trusted();
/// let endorsed = endorse_label(&clean_label);
/// assert!(endorsed.is_some());
///
/// let tainted_label = SecurityLabel::with_taints(...);
/// let not_endorsed = endorse_label(&tainted_label);
/// assert!(not_endorsed.is_none());
/// ```
#[must_use]
pub fn endorse_label(label: &SecurityLabel) -> Option<SecurityLabel> {
    if label.taints.is_empty() {
        Some(SecurityLabel {
            confidentiality: label.confidentiality,
            integrity: Integrity::Trusted,
            dlm: label.dlm.clone(),
            taints: TaintSet::empty(),
        })
    } else {
        None
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    fn test_rodeo() -> Rodeo {
        Rodeo::default()
    }

    #[test]
    fn test_source_annotation() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("get_param");
        let origin = rodeo.get_or_intern("user_input");

        let source = SourceAnnotation::user_input(name, origin);

        assert!(source.introduces(TaintKind::SQLi));
        assert!(source.introduces(TaintKind::XSS));
        assert!(source.introduces(TaintKind::CMDi));
        assert!(!source.introduces(TaintKind::ReDoS));
        assert!(source.tainted_return);
        assert!(source.tainted_params.is_empty());
    }

    #[test]
    fn test_source_with_tainted_params() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("read_file");
        let origin = rodeo.get_or_intern("file_read");

        let source = SourceAnnotation::file_read(name, origin)
            .without_tainted_return()
            .with_tainted_params(vec![1, 2]);

        assert!(!source.tainted_return);
        assert_eq!(source.tainted_params, vec![1, 2]);
    }

    #[test]
    fn test_sink_annotation() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("execute_query");

        let sink = SinkAnnotation::sql_query(name, 0);

        assert!(sink.rejects_taint(TaintKind::SQLi));
        assert!(!sink.rejects_taint(TaintKind::XSS));
        assert!(sink.is_param_sensitive(0));
        assert!(!sink.is_param_sensitive(1));
    }

    #[test]
    fn test_sink_url() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("fetch_url");

        let sink = SinkAnnotation::url(name, 0);

        assert!(sink.rejects_taint(TaintKind::SSRF));
        assert!(sink.rejects_taint(TaintKind::OpenRedirect));
        assert!(!sink.rejects_taint(TaintKind::SQLi));
    }

    #[test]
    fn test_sanitizer_annotation() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("escape_html");

        let sanitizer = SanitizerAnnotation::html_escape(name, 0);

        assert!(sanitizer.removes_taint(TaintKind::XSS));
        assert!(!sanitizer.removes_taint(TaintKind::SQLi));
        assert!(sanitizer.returns_sanitized);
        assert!(sanitizer.output_param.is_none());
    }

    #[test]
    fn test_sanitizer_protects_sink() {
        let mut rodeo = test_rodeo();
        let escape_name = rodeo.get_or_intern("escape_html");
        let render_name = rodeo.get_or_intern("render_template");

        let sanitizer = SanitizerAnnotation::html_escape(escape_name, 0);
        let xss_sink = SinkAnnotation::html_output(render_name, 0);

        assert!(sanitizer.protects_against(&xss_sink));

        let sql_sink = SinkAnnotation::sql_query(render_name, 0);
        assert!(!sanitizer.protects_against(&sql_sink));
    }

    #[test]
    fn test_sanitizer_with_output_param() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("sanitize");

        let sanitizer = SanitizerAnnotation::html_escape(name, 0).with_output_param(1);

        assert!(!sanitizer.returns_sanitized);
        assert_eq!(sanitizer.output_param, Some(1));
    }

    #[test]
    fn test_validate_all() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("validate_input");

        let sanitizer = SanitizerAnnotation::validate_all(name, 0);

        // Should remove all taint kinds
        for kind in TaintKind::ALL {
            assert!(sanitizer.removes_taint(*kind));
        }
    }

    #[test]
    fn test_security_role() {
        let mut rodeo = test_rodeo();
        let name = rodeo.get_or_intern("func");
        let origin = rodeo.get_or_intern("user_input");

        let source_role = SecurityRole::Source(SourceAnnotation::user_input(name, origin));
        assert!(source_role.is_source());
        assert!(!source_role.is_sink());
        assert!(source_role.as_source().is_some());
        assert!(source_role.as_sink().is_none());

        let sink_role = SecurityRole::Sink(SinkAnnotation::sql_query(name, 0));
        assert!(!sink_role.is_source());
        assert!(sink_role.is_sink());

        let sanitizer_role = SecurityRole::Sanitizer(SanitizerAnnotation::html_escape(name, 0));
        assert!(sanitizer_role.is_sanitizer());
        assert!(sanitizer_role.as_sanitizer().is_some());

        let validator_role = SecurityRole::Validator(SanitizerAnnotation::html_escape(name, 0));
        assert!(validator_role.is_validator());
        assert!(validator_role.as_sanitizer().is_some());
    }

    #[test]
    fn test_default_role() {
        let role = SecurityRole::default();
        assert!(matches!(role, SecurityRole::None));
    }

    #[test]
    fn test_sec_type() {
        let sec_type = SecType::new(BrrrType::STRING);
        assert!(!sec_type.has_taints());

        let tainted = SecType::tainted(
            BrrrType::STRING,
            TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS]),
        );
        assert!(tainted.has_taints());
        assert!(tainted.taints().contains(TaintKind::SQLi));
        assert!(tainted.taints().contains(TaintKind::XSS));
    }

    #[test]
    fn test_sec_func_type() {
        let mut rodeo = test_rodeo();
        let param_name = rodeo.get_or_intern("input");
        let func_name = rodeo.get_or_intern("process");
        let origin = rodeo.get_or_intern("user_input");

        let params = vec![SecParam::named(
            param_name,
            SecType::new(BrrrType::STRING),
            0,
        )];
        let return_type = SecType::new(BrrrType::STRING);

        let func = SecFuncType::pure(params, return_type)
            .with_role(SecurityRole::Source(SourceAnnotation::user_input(func_name, origin)));

        assert!(func.is_source());
        assert!(!func.is_sink());
        assert!(func.source_taints().is_some());
    }

    #[test]
    fn test_sanitize_label() {
        use super::super::labels::Confidentiality;

        let tainted = SecurityLabel::with_taints(
            Confidentiality::Public,
            Integrity::Untrusted,
            TaintSet::from_builtins([TaintKind::SQLi, TaintKind::XSS]),
        );

        // Partial sanitization
        let partial = sanitize_label(&[TaintKind::SQLi], &tainted);
        assert!(!partial.taints.contains(TaintKind::SQLi));
        assert!(partial.taints.contains(TaintKind::XSS));
        assert_eq!(partial.integrity, Integrity::Untrusted);

        // Full sanitization
        let full = sanitize_label(&[TaintKind::SQLi, TaintKind::XSS], &tainted);
        assert!(full.taints.is_empty());
        assert_eq!(full.integrity, Integrity::Trusted);
    }

    #[test]
    fn test_endorse_label() {
        use super::super::labels::Confidentiality;

        // Clean label can be endorsed
        let clean = SecurityLabel::public_trusted();
        let endorsed = endorse_label(&clean);
        assert!(endorsed.is_some());
        assert_eq!(endorsed.unwrap().integrity, Integrity::Trusted);

        // Tainted label cannot be endorsed
        let tainted = SecurityLabel::with_taints(
            Confidentiality::Public,
            Integrity::Untrusted,
            TaintSet::singleton(TaintKind::SQLi),
        );
        let not_endorsed = endorse_label(&tainted);
        assert!(not_endorsed.is_none());
    }
}
