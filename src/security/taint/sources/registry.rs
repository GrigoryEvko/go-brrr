//! Taint source definitions per language.
//!
//! This module defines the APIs, functions, and patterns that introduce
//! tainted data into a program. These are the entry points where external
//! (potentially untrusted) data enters the application.
//!
//! # Organization
//!
//! Sources are organized by:
//! 1. Language (Python, TypeScript, Go, Rust, etc.)
//! 2. Category (UserInput, File, Network, Database, etc.)
//! 3. Specificity (exact match, prefix match, regex pattern)

use crate::security::taint::types::TaintLabel;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

// =============================================================================
// Source Definition
// =============================================================================

/// Matching strategy for source patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MatchStrategy {
    /// Exact string match
    Exact,
    /// Prefix match (source starts with pattern)
    Prefix,
    /// Suffix match (source ends with pattern)
    Suffix,
    /// Contains match (pattern anywhere in source)
    Contains,
    /// Regex pattern match
    Regex,
}

/// A taint source definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintSource {
    /// The pattern to match (function name, attribute access, etc.)
    pub pattern: String,
    /// Taint label to apply when this source is matched
    pub label: TaintLabel,
    /// Matching strategy
    pub strategy: MatchStrategy,
    /// Description of this source
    pub description: String,
    /// Confidence level (0.0-1.0)
    pub confidence: f64,
    /// Whether this requires specific context (e.g., inside a function)
    pub requires_context: Option<String>,
    /// Compiled regex (for Regex strategy)
    #[serde(skip)]
    compiled_regex: Option<Regex>,
}

impl TaintSource {
    /// Create a new exact-match source.
    pub fn exact(pattern: impl Into<String>, label: TaintLabel, description: impl Into<String>) -> Self {
        Self {
            pattern: pattern.into(),
            label,
            strategy: MatchStrategy::Exact,
            description: description.into(),
            confidence: 1.0,
            requires_context: None,
            compiled_regex: None,
        }
    }

    /// Create a prefix-match source.
    pub fn prefix(pattern: impl Into<String>, label: TaintLabel, description: impl Into<String>) -> Self {
        Self {
            pattern: pattern.into(),
            label,
            strategy: MatchStrategy::Prefix,
            description: description.into(),
            confidence: 0.9,
            requires_context: None,
            compiled_regex: None,
        }
    }

    /// Create a contains-match source.
    pub fn contains(pattern: impl Into<String>, label: TaintLabel, description: impl Into<String>) -> Self {
        Self {
            pattern: pattern.into(),
            label,
            strategy: MatchStrategy::Contains,
            description: description.into(),
            confidence: 0.8,
            requires_context: None,
            compiled_regex: None,
        }
    }

    /// Create a suffix-match source.
    pub fn suffix(pattern: impl Into<String>, label: TaintLabel, description: impl Into<String>) -> Self {
        Self {
            pattern: pattern.into(),
            label,
            strategy: MatchStrategy::Suffix,
            description: description.into(),
            confidence: 0.85,
            requires_context: None,
            compiled_regex: None,
        }
    }

    /// Create a regex-match source.
    pub fn regex(pattern: impl Into<String>, label: TaintLabel, description: impl Into<String>) -> Self {
        let pattern_str = pattern.into();
        let compiled = Regex::new(&pattern_str).ok();
        Self {
            pattern: pattern_str,
            label,
            strategy: MatchStrategy::Regex,
            description: description.into(),
            confidence: 0.85,
            requires_context: None,
            compiled_regex: compiled,
        }
    }

    /// Set confidence level.
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence.clamp(0.0, 1.0);
        self
    }

    /// Set required context.
    #[allow(dead_code)]
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.requires_context = Some(context.into());
        self
    }

    /// Check if a string matches this source pattern.
    pub fn matches(&self, input: &str) -> bool {
        match self.strategy {
            MatchStrategy::Exact => input == self.pattern,
            MatchStrategy::Prefix => input.starts_with(&self.pattern),
            MatchStrategy::Suffix => input.ends_with(&self.pattern),
            MatchStrategy::Contains => input.contains(&self.pattern),
            MatchStrategy::Regex => {
                if let Some(ref regex) = self.compiled_regex {
                    regex.is_match(input)
                } else {
                    Regex::new(&self.pattern)
                        .map(|r| r.is_match(input))
                        .unwrap_or(false)
                }
            }
        }
    }
}

// =============================================================================
// Source Registry
// =============================================================================

/// Registry of taint sources for a language.
#[derive(Debug, Default)]
pub struct SourceRegistry {
    /// All registered sources
    sources: Vec<TaintSource>,
    /// Index by label for faster lookups
    by_label: HashMap<TaintLabel, Vec<usize>>,
}

impl SourceRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a source to the registry.
    pub fn add(&mut self, source: TaintSource) {
        let idx = self.sources.len();
        let label = source.label.clone();
        self.sources.push(source);
        self.by_label.entry(label).or_default().push(idx);
    }

    /// Find all sources matching an input string.
    pub fn find_matches(&self, input: &str) -> Vec<&TaintSource> {
        self.sources.iter().filter(|s| s.matches(input)).collect()
    }

    /// Find sources for a specific label.
    #[allow(dead_code)]
    pub fn sources_for_label(&self, label: &TaintLabel) -> Vec<&TaintSource> {
        self.by_label
            .get(label)
            .map(|indices| indices.iter().map(|&i| &self.sources[i]).collect())
            .unwrap_or_default()
    }

    /// Get all registered sources.
    pub fn all_sources(&self) -> &[TaintSource] {
        &self.sources
    }

    /// Get the number of registered sources.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.sources.len()
    }

    /// Check if registry is empty.
    pub fn is_empty(&self) -> bool {
        self.sources.is_empty()
    }
}

// =============================================================================
// Python Sources
// =============================================================================

/// Get the taint source registry for Python.
pub fn get_python_sources() -> SourceRegistry {
    let mut registry = SourceRegistry::new();

    // Flask request sources
    registry.add(TaintSource::prefix("request.args", TaintLabel::UserInput, "Flask query string"));
    registry.add(TaintSource::prefix("request.form", TaintLabel::UserInput, "Flask form data"));
    registry.add(TaintSource::prefix("request.data", TaintLabel::UserInput, "Flask raw body"));
    registry.add(TaintSource::prefix("request.json", TaintLabel::UserInput, "Flask JSON body"));
    registry.add(TaintSource::prefix("request.files", TaintLabel::UserInput, "Flask uploads"));
    registry.add(TaintSource::prefix("request.values", TaintLabel::UserInput, "Flask args+form"));
    registry.add(TaintSource::prefix("request.headers", TaintLabel::HttpHeader, "Flask headers"));
    registry.add(TaintSource::prefix("request.cookies", TaintLabel::Cookie, "Flask cookies"));
    registry.add(TaintSource::exact("request.path", TaintLabel::UrlData, "Flask URL path"));
    registry.add(TaintSource::exact("request.url", TaintLabel::UrlData, "Flask full URL"));

    // Django request sources
    registry.add(TaintSource::prefix("request.GET", TaintLabel::UserInput, "Django GET params"));
    registry.add(TaintSource::prefix("request.POST", TaintLabel::UserInput, "Django POST params"));
    registry.add(TaintSource::prefix("request.FILES", TaintLabel::UserInput, "Django uploads"));
    registry.add(TaintSource::prefix("request.COOKIES", TaintLabel::Cookie, "Django cookies"));
    registry.add(TaintSource::prefix("request.META", TaintLabel::HttpHeader, "Django metadata"));
    registry.add(TaintSource::exact("request.body", TaintLabel::UserInput, "Django raw body"));

    // FastAPI sources
    registry.add(TaintSource::regex(r"\bQuery\(", TaintLabel::UserInput, "FastAPI Query"));
    registry.add(TaintSource::regex(r"\bBody\(", TaintLabel::UserInput, "FastAPI Body"));
    registry.add(TaintSource::regex(r"\bPath\(", TaintLabel::UrlData, "FastAPI Path"));
    registry.add(TaintSource::regex(r"\bHeader\(", TaintLabel::HttpHeader, "FastAPI Header"));
    registry.add(TaintSource::regex(r"\bCookie\(", TaintLabel::Cookie, "FastAPI Cookie"));
    registry.add(TaintSource::regex(r"\bForm\(", TaintLabel::UserInput, "FastAPI Form"));
    registry.add(TaintSource::regex(r"\bFile\(", TaintLabel::UserInput, "FastAPI File"));

    // Standard library sources
    registry.add(TaintSource::exact("input", TaintLabel::Stdin, "Python input()"));
    registry.add(TaintSource::exact("input()", TaintLabel::Stdin, "Python input()"));
    registry.add(TaintSource::exact("sys.stdin", TaintLabel::Stdin, "Standard input"));
    registry.add(TaintSource::prefix("sys.stdin.read", TaintLabel::Stdin, "Reading stdin"));
    registry.add(TaintSource::exact("sys.argv", TaintLabel::ProcessArgs, "CLI arguments"));

    // Environment variables
    registry.add(TaintSource::prefix("os.environ", TaintLabel::Environment, "Environment dict"));
    registry.add(TaintSource::exact("os.getenv", TaintLabel::Environment, "Get env var"));

    // File operations
    registry.add(TaintSource::exact("open", TaintLabel::FileContent, "File open").with_confidence(0.7));
    registry.add(TaintSource::suffix(".read()", TaintLabel::FileContent, "File read"));
    registry.add(TaintSource::suffix(".readline()", TaintLabel::FileContent, "File readline"));
    registry.add(TaintSource::suffix(".readlines()", TaintLabel::FileContent, "File readlines"));

    // Network operations
    registry.add(TaintSource::prefix("requests.get", TaintLabel::NetworkData, "HTTP GET"));
    registry.add(TaintSource::prefix("requests.post", TaintLabel::NetworkData, "HTTP POST"));
    registry.add(TaintSource::prefix("httpx.", TaintLabel::NetworkData, "HTTPX client"));
    registry.add(TaintSource::prefix("aiohttp.", TaintLabel::NetworkData, "AIOHTTP client"));

    // Database operations
    registry.add(TaintSource::suffix(".fetchone()", TaintLabel::DatabaseQuery, "DB fetch one"));
    registry.add(TaintSource::suffix(".fetchall()", TaintLabel::DatabaseQuery, "DB fetch all"));
    registry.add(TaintSource::suffix(".fetchmany(", TaintLabel::DatabaseQuery, "DB fetch many"));

    // Deserialization
    registry.add(TaintSource::exact("json.loads", TaintLabel::DeserializedData, "JSON deserialize"));
    registry.add(TaintSource::exact("json.load", TaintLabel::DeserializedData, "JSON file deserialize"));
    registry.add(TaintSource::exact("pickle.loads", TaintLabel::DeserializedData, "Pickle deserialize"));
    registry.add(TaintSource::exact("pickle.load", TaintLabel::DeserializedData, "Pickle file deserialize"));
    registry.add(TaintSource::exact("yaml.load", TaintLabel::DeserializedData, "YAML deserialize"));

    // External APIs
    registry.add(TaintSource::suffix(".json()", TaintLabel::ExternalApi, "Response JSON"));
    registry.add(TaintSource::suffix(".text", TaintLabel::ExternalApi, "Response text").with_confidence(0.7));

    registry
}

// =============================================================================
// TypeScript/JavaScript Sources
// =============================================================================

/// Get the taint source registry for TypeScript/JavaScript.
pub fn get_typescript_sources() -> SourceRegistry {
    let mut registry = SourceRegistry::new();

    // Express.js request sources
    registry.add(TaintSource::prefix("req.body", TaintLabel::UserInput, "Express body"));
    registry.add(TaintSource::prefix("req.query", TaintLabel::UserInput, "Express query"));
    registry.add(TaintSource::prefix("req.params", TaintLabel::UrlData, "Express params"));
    registry.add(TaintSource::prefix("req.headers", TaintLabel::HttpHeader, "Express headers"));
    registry.add(TaintSource::prefix("req.cookies", TaintLabel::Cookie, "Express cookies"));
    registry.add(TaintSource::exact("req.path", TaintLabel::UrlData, "Express path"));
    registry.add(TaintSource::exact("req.url", TaintLabel::UrlData, "Express URL"));

    // Fastify request sources
    registry.add(TaintSource::prefix("request.body", TaintLabel::UserInput, "Fastify body"));
    registry.add(TaintSource::prefix("request.query", TaintLabel::UserInput, "Fastify query"));
    registry.add(TaintSource::prefix("request.params", TaintLabel::UrlData, "Fastify params"));
    registry.add(TaintSource::prefix("request.headers", TaintLabel::HttpHeader, "Fastify headers"));

    // Node.js / Browser globals
    registry.add(TaintSource::exact("process.argv", TaintLabel::ProcessArgs, "Node CLI args"));
    registry.add(TaintSource::prefix("process.env", TaintLabel::Environment, "Node env vars"));
    registry.add(TaintSource::exact("process.stdin", TaintLabel::Stdin, "Node stdin"));

    // Browser DOM
    registry.add(TaintSource::prefix("document.location", TaintLabel::UrlData, "Browser location"));
    registry.add(TaintSource::prefix("window.location", TaintLabel::UrlData, "Window location"));
    registry.add(TaintSource::exact("location.href", TaintLabel::UrlData, "Current URL"));
    registry.add(TaintSource::exact("location.search", TaintLabel::UrlData, "URL query string"));
    registry.add(TaintSource::exact("location.hash", TaintLabel::UrlData, "URL hash"));
    registry.add(TaintSource::prefix("document.cookie", TaintLabel::Cookie, "Document cookies"));

    // Form/DOM input sources
    registry.add(TaintSource::suffix(".value", TaintLabel::UserInput, "DOM element value").with_confidence(0.6));
    registry.add(TaintSource::suffix(".innerHTML", TaintLabel::UserInput, "DOM innerHTML").with_confidence(0.5));
    registry.add(TaintSource::exact("FormData", TaintLabel::UserInput, "FormData object"));

    // Network operations
    registry.add(TaintSource::exact("fetch", TaintLabel::NetworkData, "Fetch API").with_confidence(0.8));
    registry.add(TaintSource::prefix("axios.", TaintLabel::NetworkData, "Axios HTTP client"));
    registry.add(TaintSource::exact("XMLHttpRequest", TaintLabel::NetworkData, "XHR response"));
    registry.add(TaintSource::suffix(".responseText", TaintLabel::NetworkData, "XHR response text"));

    // File operations
    registry.add(TaintSource::exact("fs.readFileSync", TaintLabel::FileContent, "Sync file read"));
    registry.add(TaintSource::exact("fs.readFile", TaintLabel::FileContent, "Async file read"));
    registry.add(TaintSource::prefix("fs.promises.readFile", TaintLabel::FileContent, "Promise file read"));
    registry.add(TaintSource::exact("FileReader", TaintLabel::FileContent, "Browser FileReader"));

    // Deserialization
    registry.add(TaintSource::exact("JSON.parse", TaintLabel::DeserializedData, "JSON parsing"));
    registry.add(TaintSource::exact("eval", TaintLabel::DeserializedData, "JavaScript eval"));
    registry.add(TaintSource::regex(r"new\s+Function\(", TaintLabel::DeserializedData, "Dynamic function"));

    // WebSocket
    registry.add(TaintSource::suffix(".onmessage", TaintLabel::NetworkData, "WebSocket message").with_confidence(0.7));
    registry.add(TaintSource::suffix("event.data", TaintLabel::NetworkData, "WebSocket data").with_confidence(0.7));

    registry
}

// =============================================================================
// Go Sources
// =============================================================================

/// Get the taint source registry for Go.
pub fn get_go_sources() -> SourceRegistry {
    let mut registry = SourceRegistry::new();

    // net/http request sources
    registry.add(TaintSource::prefix("r.URL.Query", TaintLabel::UserInput, "URL query params"));
    registry.add(TaintSource::prefix("r.FormValue", TaintLabel::UserInput, "Form value"));
    registry.add(TaintSource::prefix("r.PostFormValue", TaintLabel::UserInput, "POST form value"));
    registry.add(TaintSource::prefix("r.Body", TaintLabel::UserInput, "Request body"));
    registry.add(TaintSource::prefix("r.Header", TaintLabel::HttpHeader, "Request headers"));
    registry.add(TaintSource::suffix(".Cookie(", TaintLabel::Cookie, "Cookie value"));
    registry.add(TaintSource::exact("r.URL.Path", TaintLabel::UrlData, "URL path"));

    // Gin framework
    registry.add(TaintSource::suffix(".Query(", TaintLabel::UserInput, "Gin query param"));
    registry.add(TaintSource::suffix(".PostForm(", TaintLabel::UserInput, "Gin POST form"));
    registry.add(TaintSource::suffix(".Param(", TaintLabel::UrlData, "Gin URL param"));
    registry.add(TaintSource::suffix(".ShouldBindJSON(", TaintLabel::UserInput, "Gin JSON binding"));

    // Echo framework
    registry.add(TaintSource::suffix(".QueryParam(", TaintLabel::UserInput, "Echo query param"));
    registry.add(TaintSource::suffix(".FormValue(", TaintLabel::UserInput, "Echo form value"));
    registry.add(TaintSource::suffix(".Bind(", TaintLabel::UserInput, "Echo request binding"));

    // Standard library
    registry.add(TaintSource::exact("os.Args", TaintLabel::ProcessArgs, "CLI arguments"));
    registry.add(TaintSource::exact("os.Getenv", TaintLabel::Environment, "Environment variable"));
    registry.add(TaintSource::prefix("os.Stdin", TaintLabel::Stdin, "Standard input"));

    // File operations
    registry.add(TaintSource::exact("os.ReadFile", TaintLabel::FileContent, "Read entire file"));
    registry.add(TaintSource::exact("ioutil.ReadFile", TaintLabel::FileContent, "Read file (deprecated)"));
    registry.add(TaintSource::suffix(".Read(", TaintLabel::FileContent, "Read from reader").with_confidence(0.5));
    registry.add(TaintSource::suffix(".ReadAll(", TaintLabel::FileContent, "Read all from reader"));

    // Network
    registry.add(TaintSource::exact("http.Get", TaintLabel::NetworkData, "HTTP GET"));
    registry.add(TaintSource::exact("http.Post", TaintLabel::NetworkData, "HTTP POST"));
    registry.add(TaintSource::suffix("Client.Do(", TaintLabel::NetworkData, "HTTP client request"));

    // Deserialization
    registry.add(TaintSource::suffix("json.Unmarshal(", TaintLabel::DeserializedData, "JSON unmarshal"));
    registry.add(TaintSource::suffix("json.Decode(", TaintLabel::DeserializedData, "JSON decode"));
    registry.add(TaintSource::suffix("xml.Unmarshal(", TaintLabel::DeserializedData, "XML unmarshal"));
    registry.add(TaintSource::suffix("gob.Decode(", TaintLabel::DeserializedData, "Gob decode"));

    // Database
    registry.add(TaintSource::suffix(".Scan(", TaintLabel::DatabaseQuery, "Database row scan"));
    registry.add(TaintSource::suffix(".QueryRow(", TaintLabel::DatabaseQuery, "Single row query"));

    registry
}

// =============================================================================
// Rust Sources
// =============================================================================

/// Get the taint source registry for Rust.
pub fn get_rust_sources() -> SourceRegistry {
    let mut registry = SourceRegistry::new();

    // Axum framework
    registry.add(TaintSource::exact("Query", TaintLabel::UserInput, "Axum query params").with_confidence(0.8));
    registry.add(TaintSource::exact("Form", TaintLabel::UserInput, "Axum form data").with_confidence(0.8));
    registry.add(TaintSource::exact("Json", TaintLabel::UserInput, "Axum JSON body").with_confidence(0.8));
    registry.add(TaintSource::exact("Path", TaintLabel::UrlData, "Axum path params").with_confidence(0.8));
    registry.add(TaintSource::exact("TypedHeader", TaintLabel::HttpHeader, "Axum typed header"));

    // Actix-web framework
    registry.add(TaintSource::exact("web::Query", TaintLabel::UserInput, "Actix query params"));
    registry.add(TaintSource::exact("web::Form", TaintLabel::UserInput, "Actix form data"));
    registry.add(TaintSource::exact("web::Json", TaintLabel::UserInput, "Actix JSON body"));
    registry.add(TaintSource::exact("web::Path", TaintLabel::UrlData, "Actix path params"));
    registry.add(TaintSource::prefix("req.headers()", TaintLabel::HttpHeader, "Actix headers"));

    // Standard library
    registry.add(TaintSource::exact("std::env::args", TaintLabel::ProcessArgs, "CLI arguments"));
    registry.add(TaintSource::exact("std::env::var", TaintLabel::Environment, "Environment variable"));
    registry.add(TaintSource::exact("std::io::stdin", TaintLabel::Stdin, "Standard input"));

    // File operations
    registry.add(TaintSource::exact("std::fs::read", TaintLabel::FileContent, "Read file to bytes"));
    registry.add(TaintSource::exact("std::fs::read_to_string", TaintLabel::FileContent, "Read file to string"));
    registry.add(TaintSource::suffix(".read_to_string(", TaintLabel::FileContent, "Read to string method"));
    registry.add(TaintSource::suffix(".read_to_end(", TaintLabel::FileContent, "Read to end method"));

    // Network
    registry.add(TaintSource::prefix("reqwest::", TaintLabel::NetworkData, "Reqwest HTTP client"));
    registry.add(TaintSource::suffix(".text().await", TaintLabel::NetworkData, "Response text"));
    registry.add(TaintSource::suffix(".json().await", TaintLabel::NetworkData, "Response JSON"));

    // Deserialization
    registry.add(TaintSource::prefix("serde_json::from_", TaintLabel::DeserializedData, "JSON deserialize"));
    registry.add(TaintSource::prefix("serde_yaml::from_", TaintLabel::DeserializedData, "YAML deserialize"));
    registry.add(TaintSource::prefix("toml::from_", TaintLabel::DeserializedData, "TOML deserialize"));

    // Database (sqlx)
    registry.add(TaintSource::suffix(".fetch_one(", TaintLabel::DatabaseQuery, "DB fetch one"));
    registry.add(TaintSource::suffix(".fetch_all(", TaintLabel::DatabaseQuery, "DB fetch all"));
    registry.add(TaintSource::suffix(".fetch_optional(", TaintLabel::DatabaseQuery, "DB fetch optional"));

    registry
}

// =============================================================================
// Unified Source Lookup
// =============================================================================

/// Get the taint source registry for a language.
pub fn get_sources_for_language(language: &str) -> SourceRegistry {
    match language.to_lowercase().as_str() {
        "python" | "py" => get_python_sources(),
        "typescript" | "ts" | "javascript" | "js" | "tsx" | "jsx" => get_typescript_sources(),
        "go" | "golang" => get_go_sources(),
        "rust" | "rs" => get_rust_sources(),
        _ => SourceRegistry::new(),
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_python_flask_sources() {
        let registry = get_python_sources();

        let matches = registry.find_matches("request.args.get('id')");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.label == TaintLabel::UserInput));
    }

    #[test]
    fn test_python_stdlib_sources() {
        let registry = get_python_sources();

        let matches = registry.find_matches("input()");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.label == TaintLabel::Stdin));

        let matches = registry.find_matches("sys.argv");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.label == TaintLabel::ProcessArgs));
    }

    #[test]
    fn test_typescript_express_sources() {
        let registry = get_typescript_sources();

        let matches = registry.find_matches("req.body.username");
        assert!(!matches.is_empty());
        assert!(matches.iter().any(|s| s.label == TaintLabel::UserInput));
    }

    #[test]
    fn test_match_strategies() {
        let exact = TaintSource::exact("input", TaintLabel::Stdin, "test");
        assert!(exact.matches("input"));
        assert!(!exact.matches("input()"));

        let prefix = TaintSource::prefix("request.args", TaintLabel::UserInput, "test");
        assert!(prefix.matches("request.args.get('id')"));
        assert!(!prefix.matches("args"));

        let suffix = TaintSource::suffix(".read()", TaintLabel::FileContent, "test");
        assert!(suffix.matches("file.read()"));
        assert!(!suffix.matches("read()x"));
    }

    #[test]
    fn test_regex_matching() {
        let regex_source = TaintSource::regex(r"\bQuery\(", TaintLabel::UserInput, "test");
        assert!(regex_source.matches("Query('name')"));
        assert!(regex_source.matches("x = Query("));
        assert!(!regex_source.matches("QueryBuilder"));
    }

    #[test]
    fn test_get_sources_for_language() {
        let py = get_sources_for_language("python");
        assert!(!py.is_empty());

        let ts = get_sources_for_language("TypeScript");
        assert!(!ts.is_empty());

        let unknown = get_sources_for_language("brainfuck");
        assert!(unknown.is_empty());
    }
}
