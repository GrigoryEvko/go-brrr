//! Taint analysis infrastructure.
//!
//! This module provides the foundational infrastructure for tracking how
//! potentially untrusted (tainted) data flows through a program. It enables
//! detection of security vulnerabilities where user-controlled input reaches
//! sensitive operations without proper sanitization.
//!
//! # Architecture
//!
//! The taint analysis system consists of four main components:
//!
//! 1. **Types** ([`types`]): Core data structures for representing taint
//!    - `TaintLabel`: Categories of taint sources
//!    - `TaintedValue`: A value with taint metadata
//!    - `TaintPropagation`: Rules for taint flow
//!    - `TaintState`: Aggregated state during analysis
//!
//! 2. **Propagation** ([`propagation`]): The taint propagation engine
//!    - `PropagationEngine`: Main analysis engine
//!    - `TaintedDFG`: DFG annotated with taint information
//!    - `TaintFlow`: Detected source-to-sink flows
//!    - `PropagationRules`: Function-level propagation rules
//!
//! 3. **Sources** ([`sources`]): Definitions of taint entry points
//!    - Web framework request handling
//!    - File system operations
//!    - Network operations
//!    - Command line arguments
//!    - Environment variables
//!
//! 4. **Sinks** ([`sinks`]): Security-sensitive operations
//!    - SQL queries (injection)
//!    - Command execution (injection)
//!    - HTML output (XSS)
//!    - File operations (path traversal)
//!    - Network requests (SSRF)
//!
//! # Taint Propagation Semantics
//!
//! ## Basic Propagation
//!
//! ```text
//! x = tainted_input   # x is tainted
//! y = x               # y is tainted (copy)
//! z = x + y           # z is tainted (merge)
//! w = sanitize(z)     # w is NOT tainted (sanitized)
//! ```
//!
//! ## Through Collections
//!
//! The analysis uses conservative approximation for collections:
//!
//! ```text
//! arr = [tainted_value]   # entire array is tainted
//! elem = arr[0]           # elem is tainted
//! elem = arr[5]           # elem is tainted (conservative)
//! ```
//!
//! ## Through Object Properties
//!
//! ```text
//! obj.data = tainted    # obj.data is tainted, obj is tainted (conservative)
//! x = obj.data          # x is tainted
//! y = obj.other         # y may be tainted (if conservative mode)
//! ```
//!
//! ## Through Function Returns
//!
//! ```text
//! def process(x):
//!     return x.upper()  # return is tainted if x is tainted
//!
//! result = process(tainted)  # result is tainted
//! ```
//!
//! # Usage Example
//!
//! ```ignore
//! use go_brrr::security::taint::{
//!     PropagationEngine, TaintLabel, Location,
//!     get_python_sources, get_python_sinks,
//! };
//!
//! // Create the propagation engine
//! let mut engine = PropagationEngine::new();
//!
//! // Introduce taint from user input
//! let loc = Location::new("app.py", 10, 1);
//! engine.introduce_taint("user_id", TaintLabel::UserInput, loc, Some("request.args.get('id')"));
//!
//! // Propagate through operations
//! let loc2 = Location::new("app.py", 11, 1);
//! engine.propagate_assignment("query_param", "user_id", loc2);
//!
//! // Check at sink
//! let sink_loc = Location::new("app.py", 15, 1);
//! engine.check_sink("query_param", "sql_query", sink_loc);
//!
//! // Get findings
//! for finding in engine.findings() {
//!     println!("Taint flow: {} -> {}", finding.source, finding.sink);
//!     println!("  Labels: {:?}", finding.labels);
//!     println!("  Variable: {}", finding.variable);
//! }
//! ```
//!
//! # Language Support
//!
//! The taint analysis supports multiple languages with language-specific
//! source and sink definitions:
//!
//! - **Python**: Flask, Django, FastAPI, standard library
//! - **TypeScript/JavaScript**: Express, Fastify, DOM APIs, Node.js
//! - **Go**: net/http, Gin, Echo frameworks
//! - **Rust**: Axum, Actix-web, standard library
//!
//! # Integration with Other Modules
//!
//! This module provides the infrastructure used by specific vulnerability
//! detectors in the security module:
//!
//! - `security::injection::sql` - SQL injection detection
//! - `security::injection::command` - Command injection detection
//! - `security::injection::xss` - XSS detection
//! - `security::injection::path_traversal` - Path traversal detection
//!
//! Those modules use the taint infrastructure for more precise analysis.

pub mod propagation;
pub mod sinks;
pub mod sources;
pub mod types;

// Re-export commonly used types for convenience
pub use propagation::{
    PropagationEngine, TaintFlow, TaintedDFG,
};
pub use sinks::{
    get_sinks_for_language,
    SinkCategory,
};
pub use sources::{
    get_sources_for_language, TaintSource,
};
pub use types::TaintLabel;

// =============================================================================
// Convenience Functions
// =============================================================================

/// Analyze a function's DFG for taint flows.
///
/// This is a convenience function that creates a tainted DFG, marks sources
/// and sinks based on the language, and runs the propagation engine.
///
/// # Arguments
///
/// * `dfg` - The data flow graph to analyze
/// * `language` - Language of the source code
/// * `file_path` - Path to the source file (for location reporting)
///
/// # Returns
///
/// Vector of detected taint flows from sources to sinks.
pub fn analyze_function_taint(
    dfg: &crate::dfg::types::DFGInfo,
    language: &str,
    file_path: &str,
) -> Vec<TaintFlow> {
    let sources = get_sources_for_language(language);
    let sinks = get_sinks_for_language(language);

    // Create tainted DFG
    let mut tainted_dfg = TaintedDFG::from_dfg(dfg, file_path);

    // This is a simplified version - in practice, you'd need to
    // analyze the AST to find source and sink calls within the function.
    // Here we just demonstrate the infrastructure.

    // Mark sources (would need AST analysis to find actual source calls)
    for edge in &dfg.edges {
        for source in sources.all_sources() {
            if TaintSource::matches(source, &edge.variable) {
                tainted_dfg.mark_source(edge.from_line, source.label.clone());
            }
        }
    }

    // Mark sinks (would need AST analysis to find actual sink calls)
    for edge in &dfg.edges {
        for sink in sinks.all_sinks() {
            if edge.variable.contains(sink.pattern()) {
                tainted_dfg.mark_sink(edge.to_line);
            }
        }
    }

    // Run propagation
    let mut engine = PropagationEngine::new();
    engine.analyze_dfg(&mut tainted_dfg)
}

/// Quick check if a code pattern is a known taint source.
///
/// # Arguments
///
/// * `pattern` - Code pattern to check (e.g., "request.args.get")
/// * `language` - Programming language
///
/// # Returns
///
/// Vector of matching taint labels if this is a source, empty otherwise.
pub fn is_taint_source(pattern: &str, language: &str) -> Vec<TaintLabel> {
    let sources = get_sources_for_language(language);
    sources
        .find_matches(pattern)
        .iter()
        .map(|s| s.label.clone())
        .collect()
}

/// Quick check if a code pattern is a known taint sink.
///
/// # Arguments
///
/// * `pattern` - Code pattern to check (e.g., "cursor.execute")
/// * `language` - Programming language
///
/// # Returns
///
/// Vector of matching sink categories if this is a sink, empty otherwise.
pub fn is_taint_sink(pattern: &str, language: &str) -> Vec<SinkCategory> {
    let sinks = get_sinks_for_language(language);
    sinks
        .find_matches(pattern)
        .iter()
        .map(|s| s.category)
        .collect()
}

/// Get recommended sanitizers for a sink category.
///
/// # Arguments
///
/// * `category` - The sink category
///
/// # Returns
///
/// List of recommended sanitizer names.
pub fn get_sanitizers_for_sink(category: SinkCategory) -> &'static [&'static str] {
    category.recommended_sanitizers()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use super::sinks::{get_python_sinks, get_typescript_sinks};
    use super::sources::{get_python_sources, get_typescript_sources};
    use super::types::{Location, TaintedValue, TaintState};

    #[test]
    fn test_is_taint_source() {
        let labels = is_taint_source("request.args.get('id')", "python");
        assert!(!labels.is_empty());
        assert!(labels.contains(&TaintLabel::UserInput));

        let labels = is_taint_source("req.body.username", "typescript");
        assert!(!labels.is_empty());
        assert!(labels.contains(&TaintLabel::UserInput));

        let labels = is_taint_source("some_random_function", "python");
        assert!(labels.is_empty());
    }

    #[test]
    fn test_is_taint_sink() {
        let categories = is_taint_sink("cursor.execute", "python");
        assert!(!categories.is_empty());
        assert!(categories.contains(&SinkCategory::SqlInjection));

        let categories = is_taint_sink("subprocess.run", "python");
        assert!(!categories.is_empty());
        assert!(categories.contains(&SinkCategory::CommandInjection));

        let categories = is_taint_sink("safe_function", "python");
        assert!(categories.is_empty());
    }

    #[test]
    fn test_get_sanitizers_for_sink() {
        let sanitizers = get_sanitizers_for_sink(SinkCategory::SqlInjection);
        assert!(sanitizers.contains(&"parameterized_query"));

        let sanitizers = get_sanitizers_for_sink(SinkCategory::XSS);
        assert!(sanitizers.contains(&"html_escape"));

        let sanitizers = get_sanitizers_for_sink(SinkCategory::CommandInjection);
        assert!(sanitizers.contains(&"shell_escape"));
    }

    #[test]
    fn test_module_integration() {
        // Test that all components work together
        let mut engine = PropagationEngine::new();
        let loc1 = Location::new("test.py", 1, 1);
        let loc2 = Location::new("test.py", 2, 1);
        let sink_loc = Location::new("test.py", 10, 1);

        // Introduce taint
        engine.introduce_taint("user_input", TaintLabel::UserInput, loc1, None);

        // Propagate
        engine.propagate_assignment("query", "user_input", loc2);

        // Check sink
        engine.check_sink("query", "sql_query", sink_loc);

        // Verify finding
        assert_eq!(engine.findings().len(), 1);
        let finding = &engine.findings()[0];
        assert!(finding.labels.contains(&TaintLabel::UserInput));
        assert_eq!(finding.sink_type, "sql_query");
    }

    #[test]
    fn test_end_to_end_python() {
        // Simulate a complete Python analysis
        let sources = get_python_sources();
        let sinks = get_python_sinks();

        // Find Flask request source
        let request_matches = sources.find_matches("request.args.get");
        assert!(!request_matches.is_empty());
        assert!(request_matches
            .iter()
            .any(|s| s.label == TaintLabel::UserInput));

        // Find SQL sink
        let sql_matches = sinks.find_matches("cursor.execute");
        assert!(!sql_matches.is_empty());
        assert!(sql_matches
            .iter()
            .any(|s| s.category == SinkCategory::SqlInjection));

        // Check sanitizer compatibility
        let sql_sink = sql_matches
            .iter()
            .find(|s| s.category == SinkCategory::SqlInjection)
            .unwrap();
        assert!(sql_sink.accepts_sanitizer(sinks::SanitizerContext::SqlParameterized));
        assert!(!sql_sink.accepts_sanitizer(sinks::SanitizerContext::HtmlEscape));
    }

    #[test]
    fn test_end_to_end_typescript() {
        let sources = get_typescript_sources();
        let sinks = get_typescript_sinks();

        // Find Express request source
        let body_matches = sources.find_matches("req.body");
        assert!(!body_matches.is_empty());

        // Find XSS sink
        let xss_matches = sinks.find_matches("innerHTML");
        assert!(!xss_matches.is_empty());
        assert!(xss_matches.iter().any(|s| s.category == SinkCategory::XSS));
    }

    #[test]
    fn test_taint_state_operations() {
        let mut state = TaintState::new();
        let loc = Location::new("test.py", 1, 1);

        // Set and check variable taint
        state.set_variable("x", TaintedValue::new(TaintLabel::UserInput, loc.clone()));
        assert!(state.is_variable_tainted("x"));
        assert!(!state.is_variable_tainted("y"));

        // Set and check property taint
        state.set_property(
            "obj",
            "data",
            TaintedValue::new(TaintLabel::FileContent, loc.clone()),
        );
        let prop_taint = state.get_property("obj", "data");
        assert!(prop_taint.is_some());
        assert!(prop_taint.unwrap().has_label(&TaintLabel::FileContent));

        // Set and check collection taint
        state.set_collection("arr", TaintedValue::new(TaintLabel::NetworkData, loc));
        let coll_taint = state.get_collection("arr");
        assert!(coll_taint.is_some());
        assert!(coll_taint.unwrap().has_label(&TaintLabel::NetworkData));
    }
}
