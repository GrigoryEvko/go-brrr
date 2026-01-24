//! Common taint sink definitions and utilities.
//!
//! This module provides shared infrastructure for taint sink definitions
//! across all language modules. It centralizes common patterns and provides
//! macros to reduce boilerplate.

use super::{SanitizerContext, Sink, SinkCategory};

/// Severity levels for taint sinks, matching CVSS-like scoring.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Informational - no direct security impact (1-2)
    Info = 1,
    /// Low severity - limited impact (3-4)
    Low = 3,
    /// Medium severity - moderate impact (5-6)
    Medium = 5,
    /// High severity - significant impact (7-8)
    High = 7,
    /// Critical severity - severe impact (9-10)
    Critical = 9,
}

impl Severity {
    /// Convert severity to numeric value (1-10 scale).
    #[inline]
    pub const fn as_u8(self) -> u8 {
        match self {
            Self::Info => 2,
            Self::Low => 4,
            Self::Medium => 6,
            Self::High => 8,
            Self::Critical => 10,
        }
    }

    /// Create from numeric value.
    #[inline]
    pub const fn from_u8(val: u8) -> Self {
        match val {
            0..=2 => Self::Info,
            3..=4 => Self::Low,
            5..=6 => Self::Medium,
            7..=8 => Self::High,
            _ => Self::Critical,
        }
    }
}

/// Lightweight static sink definition for compile-time sink catalogs.
///
/// This is a minimal representation of a taint sink that can be used
/// for static definitions. It can be converted to a full `Sink` at runtime.
#[derive(Debug, Clone, Copy)]
pub struct TaintSinkDef {
    /// Pattern to match function/method calls
    pub name: &'static str,
    /// Vulnerability category
    pub category: SinkCategory,
    /// Base severity level
    pub severity: Severity,
    /// Whether this sink requires sanitization (almost always true)
    pub requires_sanitization: bool,
    /// Brief description
    pub description: &'static str,
}

impl TaintSinkDef {
    /// Create a new taint sink definition.
    #[inline]
    pub const fn new(
        name: &'static str,
        category: SinkCategory,
        severity: Severity,
        description: &'static str,
    ) -> Self {
        Self {
            name,
            category,
            severity,
            requires_sanitization: true,
            description,
        }
    }

    /// Create a SQL injection sink definition.
    #[inline]
    pub const fn sql(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::SqlInjection, Severity::High, description)
    }

    /// Create a command injection sink definition.
    #[inline]
    pub const fn command(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::CommandInjection,
            Severity::Critical,
            description,
        )
    }

    /// Create an XSS sink definition.
    #[inline]
    pub const fn xss(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::XSS, Severity::High, description)
    }

    /// Create a path traversal sink definition.
    #[inline]
    pub const fn path(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::PathTraversal,
            Severity::High,
            description,
        )
    }

    /// Create an SSRF sink definition.
    #[inline]
    pub const fn ssrf(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::SSRF, Severity::High, description)
    }

    /// Create a code execution sink definition.
    #[inline]
    pub const fn code_exec(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::CodeExecution,
            Severity::Critical,
            description,
        )
    }

    /// Create a deserialization sink definition.
    #[inline]
    pub const fn deser(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::Deserialization,
            Severity::High,
            description,
        )
    }

    /// Create an LDAP injection sink definition.
    #[inline]
    pub const fn ldap(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::LdapInjection, Severity::High, description)
    }

    /// Create an XPath injection sink definition.
    #[inline]
    pub const fn xpath(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::XPathInjection,
            Severity::Medium,
            description,
        )
    }

    /// Create a log injection sink definition.
    #[inline]
    pub const fn log(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::LogInjection, Severity::Low, description)
    }

    /// Create a header injection sink definition.
    #[inline]
    pub const fn header(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::HeaderInjection,
            Severity::Medium,
            description,
        )
    }

    /// Create an open redirect sink definition.
    #[inline]
    pub const fn redirect(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::OpenRedirect,
            Severity::Medium,
            description,
        )
    }

    /// Create a template injection sink definition.
    #[inline]
    pub const fn template(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::TemplateInjection,
            Severity::High,
            description,
        )
    }

    /// Create a memory corruption sink definition.
    #[inline]
    pub const fn memory(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::MemoryCorruption,
            Severity::Critical,
            description,
        )
    }

    /// Create an XML injection sink definition.
    #[inline]
    pub const fn xml(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::XmlInjection, Severity::High, description)
    }

    /// Create a NoSQL injection sink definition.
    #[inline]
    pub const fn nosql(name: &'static str, description: &'static str) -> Self {
        Self::new(
            name,
            SinkCategory::NoSqlInjection,
            Severity::High,
            description,
        )
    }

    /// Create a regex injection sink definition.
    #[inline]
    pub const fn regex(name: &'static str, description: &'static str) -> Self {
        Self::new(name, SinkCategory::RegexInjection, Severity::Low, description)
    }

    /// Convert this static definition to a full `Sink` instance.
    pub fn into_sink(self) -> Sink {
        let mut sink = Sink::new(self.name, self.category);
        sink.severity_override = Some(self.severity.as_u8());
        sink.description = self.description.to_string();
        sink
    }
}

impl From<TaintSinkDef> for Sink {
    fn from(def: TaintSinkDef) -> Self {
        def.into_sink()
    }
}

/// Macro for bulk sink registration to reduce boilerplate.
///
/// # Usage
/// ```ignore
/// register_sinks!(registry, sql,
///     ("cursor.execute", "SQLite cursor execute"),
///     ("cursor.executemany", "SQLite cursor executemany"),
/// );
/// ```
#[macro_export]
macro_rules! register_sinks {
    // SQL injection sinks
    ($registry:expr, sql, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::sql($pattern, $desc));
        )*
    };
    // Command injection sinks
    ($registry:expr, command, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::command($pattern, $desc));
        )*
    };
    // XSS sinks
    ($registry:expr, xss, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::xss($pattern, $desc));
        )*
    };
    // Path traversal sinks
    ($registry:expr, path, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::path($pattern, $desc));
        )*
    };
    // SSRF sinks
    ($registry:expr, ssrf, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::ssrf($pattern, $desc));
        )*
    };
    // Code execution sinks
    ($registry:expr, code_exec, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::code_exec($pattern, $desc));
        )*
    };
    // LDAP injection sinks
    ($registry:expr, ldap, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::ldap($pattern, $desc));
        )*
    };
    // XPath injection sinks
    ($registry:expr, xpath, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::xpath($pattern, $desc));
        )*
    };
    // Log injection sinks
    ($registry:expr, log, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::log($pattern, $desc));
        )*
    };
    // Header injection sinks
    ($registry:expr, header, $(($pattern:expr, $desc:expr)),* $(,)?) => {
        $(
            $registry.add($crate::security::taint::sinks::Sink::header($pattern, $desc));
        )*
    };
}

/// Helper to get default sanitizers for a sink category.
///
/// This consolidates the logic that was potentially duplicated across modules.
pub fn default_sanitizers_for(category: SinkCategory) -> Vec<SanitizerContext> {
    match category {
        SinkCategory::SqlInjection | SinkCategory::NoSqlInjection => vec![
            SanitizerContext::SqlParameterized,
            SanitizerContext::SqlOrm,
            SanitizerContext::SqlEscape,
        ],
        SinkCategory::CommandInjection => vec![
            SanitizerContext::CommandList,
            SanitizerContext::ShellEscape,
            SanitizerContext::CommandAllowlist,
        ],
        SinkCategory::XSS => vec![
            SanitizerContext::HtmlEscape,
            SanitizerContext::DomSanitize,
            SanitizerContext::ContentSecurityPolicy,
            SanitizerContext::JavaScriptEscape,
        ],
        SinkCategory::PathTraversal => vec![
            SanitizerContext::PathCanonicalize,
            SanitizerContext::PathAllowlist,
            SanitizerContext::PathBasename,
            SanitizerContext::PathSafeJoin,
        ],
        SinkCategory::CodeExecution => vec![SanitizerContext::InputAllowlist],
        SinkCategory::SSRF => vec![
            SanitizerContext::UrlDomainAllowlist,
            SanitizerContext::UrlSchemeValidation,
            SanitizerContext::UrlPrivateIpBlock,
        ],
        SinkCategory::LogInjection => vec![
            SanitizerContext::LogNewlineRemove,
            SanitizerContext::LogEncode,
        ],
        SinkCategory::HeaderInjection => vec![
            SanitizerContext::HeaderCrlfRemove,
            SanitizerContext::HeaderEncode,
        ],
        SinkCategory::XPathInjection => vec![
            SanitizerContext::XPathParameterized,
            SanitizerContext::XPathEscape,
        ],
        SinkCategory::LdapInjection => vec![
            SanitizerContext::LdapDnEscape,
            SanitizerContext::LdapFilterEscape,
        ],
        SinkCategory::TemplateInjection => vec![
            SanitizerContext::TemplateSandbox,
            SanitizerContext::TemplateAutoescape,
        ],
        SinkCategory::Deserialization => vec![
            SanitizerContext::DeserializeSafeFormat,
            SanitizerContext::DeserializeTypeAllowlist,
            SanitizerContext::DeserializeSignatureVerify,
        ],
        SinkCategory::XmlInjection => vec![
            SanitizerContext::XmlDisableExternalEntities,
            SanitizerContext::XmlEntityEncode,
        ],
        SinkCategory::OpenRedirect => vec![
            SanitizerContext::UrlDomainAllowlist,
            SanitizerContext::UrlSchemeValidation,
        ],
        SinkCategory::RegexInjection => vec![
            SanitizerContext::RegexEscape,
            SanitizerContext::RegexTimeout,
            SanitizerContext::LengthLimit,
        ],
        SinkCategory::MemoryCorruption => vec![
            SanitizerContext::TypeValidation,
            SanitizerContext::LengthLimit,
        ],
        SinkCategory::EmailHeaderInjection => vec![SanitizerContext::EmailHeaderSanitize],
    }
}

/// Check if a sanitizer context is effective against a target sink category.
///
/// This is a convenience function that wraps `SanitizerContext::is_effective_against`.
#[inline]
pub fn is_effective_sanitizer(sanitizer: SanitizerContext, target: SinkCategory) -> bool {
    sanitizer.is_effective_against(target)
}

/// Get all effective sanitizers for a given sink category.
///
/// Returns sanitizers that can mitigate vulnerabilities for this category.
pub fn effective_sanitizers_for(category: SinkCategory) -> Vec<SanitizerContext> {
    // Use static list from the category's recommended sanitizers
    category
        .recommended_sanitizers()
        .iter()
        .filter_map(|name| sanitizer_from_name(name))
        .collect()
}

/// Map a sanitizer name to its context (for lookup purposes).
fn sanitizer_from_name(name: &str) -> Option<SanitizerContext> {
    match name {
        "parameterized_query" | "prepared_statement" => Some(SanitizerContext::SqlParameterized),
        "django_orm" | "sqlalchemy_text" => Some(SanitizerContext::SqlOrm),
        "escape_string" | "quote_literal" => Some(SanitizerContext::SqlEscape),
        "shlex_quote" | "shlex_split" | "shell_escape" | "escapeshellarg" | "escapeshellcmd" => {
            Some(SanitizerContext::ShellEscape)
        }
        "subprocess_list" => Some(SanitizerContext::CommandList),
        "html_escape" | "escape" | "markupsafe_escape" | "cgi_escape" => {
            Some(SanitizerContext::HtmlEscape)
        }
        "sanitize_html" | "DOMPurify" | "bleach_clean" => Some(SanitizerContext::DomSanitize),
        "path_join" | "realpath" | "abspath" | "normpath" | "safe_join" => {
            Some(SanitizerContext::PathCanonicalize)
        }
        "secure_filename" | "basename" => Some(SanitizerContext::PathBasename),
        "url_validate" | "scheme_validate" => Some(SanitizerContext::UrlSchemeValidation),
        "domain_allowlist" => Some(SanitizerContext::UrlDomainAllowlist),
        "is_private_ip" => Some(SanitizerContext::UrlPrivateIpBlock),
        "url_parse" => Some(SanitizerContext::UrlEncode),
        "log_escape" | "replace_newlines" | "sanitize_log" => {
            Some(SanitizerContext::LogNewlineRemove)
        }
        "header_escape" | "remove_crlf" | "validate_header" => {
            Some(SanitizerContext::HeaderCrlfRemove)
        }
        "ldap_escape" | "escape_filter" => Some(SanitizerContext::LdapFilterEscape),
        "parameterized_xpath" => Some(SanitizerContext::XPathParameterized),
        "autoescape" | "safe_render" => Some(SanitizerContext::TemplateAutoescape),
        "sandbox_template" => Some(SanitizerContext::TemplateSandbox),
        "json_loads" | "safe_load" => Some(SanitizerContext::DeserializeSafeFormat),
        "restricted_deserialize" => Some(SanitizerContext::DeserializeTypeAllowlist),
        "defusedxml" | "disable_external_entities" | "lxml_safe_parse" => {
            Some(SanitizerContext::XmlDisableExternalEntities)
        }
        "url_for" | "is_safe_url" | "validate_redirect" => {
            Some(SanitizerContext::UrlSchemeValidation)
        }
        "re_escape" | "regex_escape" | "literal_pattern" => Some(SanitizerContext::RegexEscape),
        "bounds_check" | "safe_alloc" | "size_validate" => Some(SanitizerContext::TypeValidation),
        "email_escape" | "validate_email" | "header_encode" => {
            Some(SanitizerContext::EmailHeaderSanitize)
        }
        "ast_literal_eval" | "json_parse" | "safe_eval" => Some(SanitizerContext::InputAllowlist),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_severity_conversion() {
        assert_eq!(Severity::Info.as_u8(), 2);
        assert_eq!(Severity::Low.as_u8(), 4);
        assert_eq!(Severity::Medium.as_u8(), 6);
        assert_eq!(Severity::High.as_u8(), 8);
        assert_eq!(Severity::Critical.as_u8(), 10);

        assert_eq!(Severity::from_u8(1), Severity::Info);
        assert_eq!(Severity::from_u8(4), Severity::Low);
        assert_eq!(Severity::from_u8(6), Severity::Medium);
        assert_eq!(Severity::from_u8(8), Severity::High);
        assert_eq!(Severity::from_u8(10), Severity::Critical);
    }

    #[test]
    fn test_taint_sink_def_factories() {
        let sql = TaintSinkDef::sql("cursor.execute", "SQL execute");
        assert_eq!(sql.category, SinkCategory::SqlInjection);
        assert_eq!(sql.severity, Severity::High);

        let cmd = TaintSinkDef::command("os.system", "OS command");
        assert_eq!(cmd.category, SinkCategory::CommandInjection);
        assert_eq!(cmd.severity, Severity::Critical);

        let xss = TaintSinkDef::xss("innerHTML", "DOM XSS");
        assert_eq!(xss.category, SinkCategory::XSS);
        assert_eq!(xss.severity, Severity::High);
    }

    #[test]
    fn test_taint_sink_def_to_sink() {
        let def = TaintSinkDef::sql("cursor.execute", "SQL execute");
        let sink: Sink = def.into();

        assert_eq!(sink.function_pattern, "cursor.execute");
        assert_eq!(sink.category, SinkCategory::SqlInjection);
        assert_eq!(sink.severity(), 8); // High severity
    }

    #[test]
    fn test_default_sanitizers() {
        let sql_sanitizers = default_sanitizers_for(SinkCategory::SqlInjection);
        assert!(sql_sanitizers.contains(&SanitizerContext::SqlParameterized));

        let cmd_sanitizers = default_sanitizers_for(SinkCategory::CommandInjection);
        assert!(cmd_sanitizers.contains(&SanitizerContext::ShellEscape));

        let xss_sanitizers = default_sanitizers_for(SinkCategory::XSS);
        assert!(xss_sanitizers.contains(&SanitizerContext::HtmlEscape));
    }

    #[test]
    fn test_effective_sanitizer_check() {
        assert!(is_effective_sanitizer(
            SanitizerContext::HtmlEscape,
            SinkCategory::XSS
        ));
        assert!(!is_effective_sanitizer(
            SanitizerContext::HtmlEscape,
            SinkCategory::SqlInjection
        ));

        assert!(is_effective_sanitizer(
            SanitizerContext::SqlParameterized,
            SinkCategory::SqlInjection
        ));
        assert!(!is_effective_sanitizer(
            SanitizerContext::SqlParameterized,
            SinkCategory::XSS
        ));
    }

    #[test]
    fn test_sanitizer_from_name() {
        assert_eq!(
            sanitizer_from_name("parameterized_query"),
            Some(SanitizerContext::SqlParameterized)
        );
        assert_eq!(
            sanitizer_from_name("html_escape"),
            Some(SanitizerContext::HtmlEscape)
        );
        assert_eq!(
            sanitizer_from_name("shlex_quote"),
            Some(SanitizerContext::ShellEscape)
        );
        assert_eq!(sanitizer_from_name("unknown_sanitizer"), None);
    }
}
