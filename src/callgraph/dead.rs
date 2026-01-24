//! Dead code detection.
//!
//! Identifies unreachable functions in a codebase by computing reachability
//! from detected entry points. Uses heuristics to minimize false positives
//! from callbacks, event handlers, and dynamically-invoked functions.
//!
//! # Algorithm
//!
//! 1. Detect entry points (main, tests, CLI handlers, API endpoints, exports)
//! 2. BFS traversal from entry points marking all reachable functions
//! 3. Filter remaining functions for false positives (callbacks, handlers)
//! 4. Return truly unreachable functions as dead code
//!
//! # Entry Point Patterns
//!
//! - Main functions: `main`, `Main`, `run`, `app`, `start`
//! - Test functions: `test_*`, `Test*`, `*_test`, `*Tests`, `spec_*`
//! - CLI handlers: `cmd_*`, `handle_*`, `run_*`, `execute_*`
//! - API endpoints: `api_*`, `get_*`, `post_*`, `put_*`, `delete_*`, `patch_*`
//! - Framework hooks: `setup`, `teardown`, `init`, `cleanup`, `configure`
//! - Pytest hooks: `pytest_*` (pytest_configure, pytest_collection, pytest_runtest_setup, etc.)
//! - Python dunder: `__init__`, `__main__`, `__call__`, etc.

use std::collections::{HashSet, VecDeque};

use fixedbitset::FixedBitSet;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::callgraph::types::{CallGraph, FunctionRef};

/// Result of dead code analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadCodeResult {
    /// Functions identified as dead (unreachable)
    pub dead_functions: Vec<DeadFunction>,
    /// Total count
    pub total_dead: usize,
    /// Entry points used for analysis
    pub entry_points: Vec<String>,
    /// Functions filtered as likely false positives
    pub filtered_count: usize,
    /// Analysis statistics
    pub stats: DeadCodeStats,
}

/// A dead (unreachable) function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadFunction {
    /// File containing the function
    pub file: String,
    /// Function name
    pub name: String,
    /// Fully qualified name
    pub qualified_name: Option<String>,
    /// Line number
    pub line: Option<usize>,
    /// Reason this function is considered dead
    pub reason: DeadReason,
    /// Confidence score (0.0 - 1.0)
    pub confidence: f64,
}

/// Reason why a function is considered dead.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum DeadReason {
    /// Not reachable from any entry point
    Unreachable,
    /// Defined but never called anywhere
    NeverCalled,
    /// Only called from other dead functions
    CalledOnlyByDead,
}

/// Statistics from dead code analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DeadCodeStats {
    /// Total functions analyzed
    pub total_functions: usize,
    /// Functions marked as entry points
    pub entry_point_count: usize,
    /// Functions reachable from entry points
    pub reachable_count: usize,
    /// Functions filtered as false positives
    pub filtered_as_callback: usize,
    pub filtered_as_handler: usize,
    pub filtered_as_decorator: usize,
    pub filtered_as_dynamic: usize,
}

/// Configuration for dead code detection.
#[derive(Debug, Clone)]
pub struct DeadCodeConfig {
    /// Minimum confidence threshold for reporting (0.0 - 1.0)
    pub min_confidence: f64,
    /// Additional entry point patterns (regex-like simple patterns)
    pub extra_entry_patterns: Vec<String>,
    /// Additional false positive patterns to filter
    pub filter_patterns: Vec<String>,
    /// Language-specific mode (enables language-specific heuristics)
    pub language: Option<String>,
    /// Include functions matching public API patterns (get_, set_, PascalCase, etc.) as entry points.
    ///
    /// WARNING: This is EXTREMELY permissive and causes massive false negatives!
    /// The `is_likely_public_api()` function matches 50-70% of functions because it includes:
    /// - Any function starting with uppercase (PascalCase) - matches most Java/Go/Rust functions
    /// - get_/set_ prefixed functions
    /// - is_/has_/can_/should_ prefixed functions
    /// - with_/from_/to_/as_ prefixed functions
    ///
    /// Default: false (matches Python `brrr dead` behavior which only checks specific patterns)
    ///
    /// Only enable this if you want to be extremely conservative and avoid false positives,
    /// at the cost of missing most actual dead code.
    pub include_public_api_patterns: bool,
}

impl Default for DeadCodeConfig {
    fn default() -> Self {
        Self {
            min_confidence: 0.7,
            extra_entry_patterns: Vec::new(),
            filter_patterns: Vec::new(),
            language: None,
            include_public_api_patterns: false, // Off by default - too permissive!
        }
    }
}

/// Entry point category for classification.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EntryPointKind {
    Main,
    Test,
    CliHandler,
    ApiEndpoint,
    FrameworkHook,
    PythonDunder,
}

/// Detect entry points in the call graph with custom configuration.
///
/// Entry points are functions that are never called but are likely
/// intentionally public (main, test functions, exported API, etc.)
///
/// This function uses comprehensive heuristics to identify entry points
/// across multiple programming paradigms and frameworks.
pub fn detect_entry_points_with_config(
    graph: &CallGraph,
    config: &DeadCodeConfig,
) -> Vec<FunctionRef> {
    let all_funcs = graph.all_functions();
    let called: FxHashSet<_> = graph.edges.iter().map(|e| &e.callee).collect();

    all_funcs
        .iter()
        .filter(|f| !called.contains(f) || is_definitely_entry_point(&f.name))
        .filter(|f| is_likely_entry_point(&f.name, Some(config)))
        .cloned()
        .collect()
}

/// Classify the type of entry point for a function name.
pub fn classify_entry_point(name: &str) -> Option<EntryPointKind> {
    // Main entry points
    if name == "main" || name == "Main" || name == "__main__" {
        return Some(EntryPointKind::Main);
    }

    // Test functions - comprehensive patterns
    if name.starts_with("test_")
        || name.starts_with("Test")
        || name.ends_with("_test")
        || name.ends_with("Test")
        || name.ends_with("Tests")
        || name.starts_with("spec_")
        || name.ends_with("_spec")
        || name.starts_with("it_")
        || name.starts_with("should_")
        || name == "setUp"
        || name == "tearDown"
        || name == "setUpClass"
        || name == "tearDownClass"
        || name == "beforeEach"
        || name == "afterEach"
        || name == "beforeAll"
        || name == "afterAll"
    {
        return Some(EntryPointKind::Test);
    }

    // Pytest plugin hooks (pytest_configure, pytest_collection, pytest_runtest_setup, etc.)
    // These are dynamically called by the pytest framework and should not be reported as dead code
    if name.starts_with("pytest_") {
        return Some(EntryPointKind::FrameworkHook);
    }

    // Conftest hooks (conftest.py functions called by pytest)
    if name.starts_with("conftest_") {
        return Some(EntryPointKind::FrameworkHook);
    }

    // CLI handlers
    if name.starts_with("cmd_")
        || name.starts_with("handle_")
        || name.starts_with("run_")
        || name.starts_with("execute_")
        || name.starts_with("do_")
        || name.starts_with("action_")
        || name.starts_with("command_")
    {
        return Some(EntryPointKind::CliHandler);
    }

    // API endpoints - REST patterns
    if name.starts_with("api_")
        || name.starts_with("get_")
        || name.starts_with("post_")
        || name.starts_with("put_")
        || name.starts_with("delete_")
        || name.starts_with("patch_")
        || name.starts_with("list_")
        || name.starts_with("create_")
        || name.starts_with("update_")
        || name.starts_with("destroy_")
        || name.starts_with("index_")
        || name.starts_with("show_")
        || name.starts_with("new_")
        || name.starts_with("edit_")
    {
        return Some(EntryPointKind::ApiEndpoint);
    }

    // Framework hooks and lifecycle methods
    if name == "setup"
        || name == "teardown"
        || name == "init"
        || name == "cleanup"
        || name == "configure"
        || name == "register"
        || name == "bootstrap"
        || name == "mount"
        || name == "unmount"
        || name == "render"
        || name == "componentDidMount"
        || name == "componentWillUnmount"
        || name == "ngOnInit"
        || name == "ngOnDestroy"
        || name == "created"
        || name == "mounted"
        || name == "destroyed"
    {
        return Some(EntryPointKind::FrameworkHook);
    }

    // Python dunder methods (special methods)
    if name.starts_with("__") && name.ends_with("__") {
        return Some(EntryPointKind::PythonDunder);
    }

    None
}

/// Check if a function name looks like an entry point.
///
/// When `config` is None, uses conservative defaults (public API patterns disabled).
/// When `config` is Some, respects the `include_public_api_patterns` and `extra_entry_patterns` settings.
fn is_likely_entry_point(name: &str, config: Option<&DeadCodeConfig>) -> bool {
    // Core entry point patterns (always checked)
    if classify_entry_point(name).is_some() || is_likely_callback(name) || is_likely_factory(name) {
        return true;
    }

    // Check user-defined custom entry patterns
    if let Some(cfg) = config {
        for pattern in &cfg.extra_entry_patterns {
            if name.contains(pattern) {
                return true;
            }
        }

        // Only check public API patterns if explicitly enabled (opt-in)
        // This is disabled by default because it matches 50-70% of functions
        if cfg.include_public_api_patterns && is_likely_public_api(name) {
            return true;
        }
    }

    false
}

/// Check if a function name is definitely an entry point regardless of call status.
fn is_definitely_entry_point(name: &str) -> bool {
    name == "main"
        || name == "Main"
        || name == "__main__"
        || name == "app"
        || name == "start"
        || name == "run"
}

/// Check if name looks like a callback function (likely dynamically invoked).
///
/// Uses strict pattern matching to avoid false positives on common English words
/// like "once", "online", "only", "ongoing", "handler" (as regular word).
fn is_likely_callback(name: &str) -> bool {
    // on_ prefix is always a callback pattern (on_click, on_submit)
    name.starts_with("on_")
        // onX where X is uppercase: camelCase callback like onClick, onSubmit
        // Avoids false positives: once, online, only, ongoing
        || (name.starts_with("on")
            && name.len() > 2
            && name.chars().nth(2).map(|c| c.is_ascii_uppercase()).unwrap_or(false))
        // OnX where X is uppercase: PascalCase like OnClick, OnSubmit
        // Avoids false positives: Ongoing, Online, Once (capitalized)
        || (name.starts_with("On")
            && name.len() > 2
            && name.chars().nth(2).map(|c| c.is_ascii_uppercase()).unwrap_or(false))
        || name.ends_with("_callback")
        || name.ends_with("Callback")
        || name.ends_with("_handler")
        || name.ends_with("Handler")
        || name.ends_with("_listener")
        || name.ends_with("Listener")
        // handleX where X is uppercase: camelCase like handleClick, handleSubmit
        // Avoids false positives: handler, handling
        || (name.starts_with("handle")
            && name.len() > 6
            && name.chars().nth(6).map(|c| c.is_ascii_uppercase()).unwrap_or(false))
        // handle_ prefix is always a handler pattern
        || name.starts_with("handle_")
        || name.contains("Callback")
        || name.contains("Handler")
}

/// Check if name looks like a factory function.
fn is_likely_factory(name: &str) -> bool {
    name.starts_with("create_")
        || name.starts_with("make_")
        || name.starts_with("build_")
        || name.starts_with("new_")
        || name.ends_with("_factory")
        || name.ends_with("Factory")
        || name.starts_with("Create")
        || name.starts_with("Make")
        || name.starts_with("Build")
        || name.starts_with("New")
}

/// Check if name looks like intentionally public API.
///
/// Uses strict pattern matching to avoid false positives on common words
/// like "gettext", "getter", "getaway", "settings", "settle", "setup".
fn is_likely_public_api(name: &str) -> bool {
    if name.starts_with('_') {
        return false;
    }

    // Getter pattern: get_ or getX (camelCase)
    // Avoids false positives: gettext, getter, getaway
    let is_getter = name.starts_with("get_")
        || (name.starts_with("get")
            && name.len() > 3
            && name
                .chars()
                .nth(3)
                .map(|c| c.is_uppercase())
                .unwrap_or(false));

    // Setter pattern: set_ or setX (camelCase)
    // Avoids false positives: settings, settle, setup, setter
    let is_setter = name.starts_with("set_")
        || (name.starts_with("set")
            && name.len() > 3
            && name
                .chars()
                .nth(3)
                .map(|c| c.is_uppercase())
                .unwrap_or(false));

    // Boolean accessor patterns (always use underscore convention)
    let is_boolean_accessor = name.starts_with("is_")
        || name.starts_with("has_")
        || name.starts_with("can_")
        || name.starts_with("should_");

    // Builder/converter patterns (always use underscore convention)
    let is_builder = name.starts_with("with_")
        || name.starts_with("from_")
        || name.starts_with("to_")
        || name.starts_with("as_");

    // Public API by naming convention (PascalCase class/type names)
    let is_public_by_case = name
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    is_getter || is_setter || is_boolean_accessor || is_builder || is_public_by_case
}

/// Analyze dead code in a project.
#[allow(dead_code)]
pub fn analyze_dead_code(graph: &CallGraph) -> DeadCodeResult {
    analyze_dead_code_with_config(graph, &DeadCodeConfig::default())
}

/// Analyze dead code with custom configuration.
pub fn analyze_dead_code_with_config(graph: &CallGraph, config: &DeadCodeConfig) -> DeadCodeResult {
    let entry_points = detect_entry_points_with_config(graph, config);
    let all_funcs = graph.all_functions();

    let mut stats = DeadCodeStats {
        total_functions: all_funcs.len(),
        entry_point_count: entry_points.len(),
        ..Default::default()
    };

    // Compute reachable functions via BFS
    let reachable = compute_reachability(graph, &entry_points);
    stats.reachable_count = reachable.len();

    // Find potentially dead functions
    // NOTE: Using manual iteration instead of .difference() because all_funcs
    // returns std::collections::HashSet but reachable is FxHashSet (type mismatch).
    let mut potentially_dead: Vec<_> = all_funcs
        .iter()
        .filter(|f| !reachable.contains(*f) && !entry_points.contains(*f))
        .cloned()
        .collect();

    // Filter false positives and compute confidence
    let mut dead_functions = Vec::new();
    let mut filtered_count = 0;

    for func in potentially_dead.drain(..) {
        let (is_false_positive, filter_reason) = check_false_positive(&func, config);

        if is_false_positive {
            filtered_count += 1;
            match filter_reason.as_str() {
                "callback" => stats.filtered_as_callback += 1,
                "handler" => stats.filtered_as_handler += 1,
                "decorator" => stats.filtered_as_decorator += 1,
                "dynamic" => stats.filtered_as_dynamic += 1,
                _ => {}
            }
            continue;
        }

        let confidence = compute_confidence(&func, graph, &reachable);

        if confidence >= config.min_confidence {
            let reason = determine_dead_reason(&func, graph, &reachable);

            dead_functions.push(DeadFunction {
                file: func.file.clone(),
                name: func.name.clone(),
                qualified_name: func.qualified_name.clone(),
                line: None, // Would need index for line numbers
                reason,
                confidence,
            });
        }
    }

    DeadCodeResult {
        total_dead: dead_functions.len(),
        dead_functions,
        entry_points: entry_points.iter().map(|f| f.name.clone()).collect(),
        filtered_count,
        stats,
    }
}

/// Compute reachability from entry points using BFS.
///
/// Returns the set of all functions reachable from any entry point.
/// Returns `std::collections::HashSet` for compatibility with `CallGraph::all_functions()`.
///
/// # Performance
///
/// Uses index-based BFS to avoid cloning `FunctionRef` during traversal.
/// Uses FixedBitSet for O(1) visited tracking with ~8x less memory than Vec<bool>.
/// Internally uses FxHashMap for fast index lookups.
/// Only clones once at the end when building the final result set.
fn compute_reachability(graph: &CallGraph, entry_points: &[FunctionRef]) -> HashSet<FunctionRef> {
    // Collect all functions once and build index mapping (uses cached result)
    let all_funcs: Vec<FunctionRef> = graph.all_functions().iter().cloned().collect();
    if all_funcs.is_empty() {
        return HashSet::new();
    }

    // Use FxHashMap for fast index lookups during traversal
    let func_to_idx: FxHashMap<&FunctionRef, usize> =
        all_funcs.iter().enumerate().map(|(i, f)| (f, i)).collect();

    // Use FixedBitSet for O(1) visited tracking (~8x less memory than Vec<bool>)
    let mut visited = FixedBitSet::with_capacity(all_funcs.len());

    // Initialize queue with entry point indices
    let mut queue: VecDeque<usize> = entry_points
        .iter()
        .filter_map(|f| func_to_idx.get(f).copied())
        .collect();

    // BFS traversal using indices (no cloning during traversal)
    while let Some(idx) = queue.pop_front() {
        if !visited.contains(idx) {
            visited.insert(idx);
            let func = &all_funcs[idx];

            // Add all callees to queue
            if let Some(callees) = graph.callees.get(func) {
                for callee in callees {
                    if let Some(&callee_idx) = func_to_idx.get(callee) {
                        if !visited.contains(callee_idx) {
                            queue.push_back(callee_idx);
                        }
                    }
                }
            }
        }
    }

    // Convert back to FunctionRef set (single clone per reachable function)
    visited
        .ones()
        .map(|i| all_funcs[i].clone())
        .collect()
}

/// Check if a function is likely a false positive for dead code.
///
/// Returns (is_false_positive, reason).
fn check_false_positive(func: &FunctionRef, config: &DeadCodeConfig) -> (bool, String) {
    let name = &func.name;

    // Callback patterns - dynamically invoked
    // Note: is_likely_callback() already handles on_, onX (camelCase), OnX (PascalCase)
    // with strict uppercase checks to avoid false positives like "once", "ongoing"
    if is_likely_callback(name) {
        return (true, "callback".to_string());
    }

    // Event-specific patterns NOT covered by is_likely_callback()
    // (which handles _handler, Handler, _callback, Callback, _listener, Listener)
    if name.ends_with("_event") || name.ends_with("Event") {
        return (true, "handler".to_string());
    }

    // Decorator-registered patterns
    if name.starts_with("route_")
        || name.starts_with("endpoint_")
        || name.starts_with("task_")
        || name.starts_with("job_")
        || name.starts_with("signal_")
        || name.starts_with("hook_")
    {
        return (true, "decorator".to_string());
    }

    // Dynamic dispatch patterns (visitor pattern, dispatch methods)
    // Note: process_* is intentionally NOT included as it's a common naming
    // pattern for regular data processing functions
    if name.starts_with("visit_")
        || name.starts_with("Visit")
        || name.starts_with("dispatch_")
        || name.starts_with("Dispatch")
        || name.contains("Strategy")
        || name.contains("Visitor")
    {
        return (true, "dynamic".to_string());
    }

    // Protocol/interface implementation patterns
    if name.starts_with("impl_") || is_protocol_method(name) {
        return (true, "dynamic".to_string());
    }

    // Check user-defined filter patterns
    for pattern in &config.filter_patterns {
        if name.contains(pattern) {
            return (true, "user_filter".to_string());
        }
    }

    (false, String::new())
}

/// Check if name is a common protocol/interface method.
fn is_protocol_method(name: &str) -> bool {
    matches!(
        name,
        "next"
            | "iter"
            | "len"
            | "hash"
            | "eq"
            | "cmp"
            | "clone"
            | "drop"
            | "deref"
            | "index"
            | "call"
            | "enter"
            | "exit"
            | "read"
            | "write"
            | "close"
            | "flush"
            | "seek"
            | "accept"
            | "connect"
            | "bind"
            | "listen"
            | "send"
            | "recv"
    )
}

/// Check if file path is NOT in commonly called module paths.
///
/// Files outside common paths (api, public, lib, src root) are more likely to contain dead code.
fn is_in_common_module_path(file_path: &str) -> bool {
    // Common public-facing module paths that are less likely to have dead code
    const COMMON_PATHS: &[&str] = &[
        "/api/",
        "/public/",
        "/lib/",
        "/handlers/",
        "/routes/",
        "/controllers/",
        "/endpoints/",
        "/views/",
        "/services/",
        "/commands/",
    ];

    for path in COMMON_PATHS {
        if file_path.contains(path) {
            return true;
        }
    }

    false
}

/// Compute confidence score for a potentially dead function.
///
/// Higher confidence means more likely to be truly dead.
/// Uses balanced scoring starting from neutral (0.5) with symmetric
/// increases and decreases based on multiple factors.
///
/// # Scoring Factors
///
/// **Increases (more likely dead):**
/// - No callers at all: +0.2
/// - Calls other dead functions: +0.1 per dead callee (capped at +0.3)
/// - Private naming convention (_prefix): +0.1
/// - Not in common module paths: +0.1
///
/// **Decreases (less likely dead):**
/// - Public naming convention (PascalCase): -0.15
/// - Very short name (likely utility/interface method): -0.1
/// - Factory/builder pattern: -0.15
/// - In public module path (/api/, /public/): -0.2
fn compute_confidence(
    func: &FunctionRef,
    graph: &CallGraph,
    reachable: &HashSet<FunctionRef>,
) -> f64 {
    let mut confidence: f64 = 0.5; // Start neutral
    let name = &func.name;

    // === INCREASE confidence (more likely dead) ===

    // Has no callers at all - strong indicator of dead code
    if !graph.callers.contains_key(func) {
        confidence += 0.2;
    }

    // Calls other dead functions - if callees are dead, caller is likely dead too
    if let Some(callees) = graph.callees.get(func) {
        let dead_callees = callees.iter().filter(|c| !reachable.contains(*c)).count();
        if dead_callees > 0 {
            // Scale bonus: +0.1 per dead callee, capped at +0.3
            confidence += 0.1 * (dead_callees.min(3) as f64);
        }
    }

    // Private naming convention (single underscore prefix, not dunder)
    // Private functions are more likely to be dead if unreachable
    if name.starts_with('_') && !name.starts_with("__") {
        confidence += 0.1;
    }

    // Not in commonly called module paths
    if !is_in_common_module_path(&func.file) {
        confidence += 0.1;
    }

    // === DECREASE confidence (less likely dead) ===

    // Public naming convention (PascalCase) - may be called externally
    if name
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false)
    {
        confidence -= 0.15;
    }

    // Very short name (likely utility or interface method)
    if name.len() <= 3 {
        confidence -= 0.1;
    }

    // Factory/builder pattern - often called via dependency injection
    if is_likely_factory(name) {
        confidence -= 0.15;
    }

    // In public module path - higher chance of external usage
    if func.file.contains("/api/") || func.file.contains("/public/") {
        confidence -= 0.2;
    }

    confidence.clamp(0.0, 1.0)
}

/// Determine why a function is considered dead.
fn determine_dead_reason(
    func: &FunctionRef,
    graph: &CallGraph,
    reachable: &HashSet<FunctionRef>,
) -> DeadReason {
    // Check if never called
    if !graph.callers.contains_key(func) {
        return DeadReason::NeverCalled;
    }

    // Check if only called by other dead functions
    if let Some(callers) = graph.callers.get(func) {
        let live_callers = callers.iter().filter(|c| reachable.contains(*c)).count();
        if live_callers == 0 {
            return DeadReason::CalledOnlyByDead;
        }
    }

    DeadReason::Unreachable
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::types::CallEdge;

    fn create_test_graph() -> CallGraph {
        let mut graph = CallGraph::default();

        // main -> helper -> utility
        // orphan_func (not called)
        // test_something (entry point)
        // dead_island -> dead_helper (isolated)

        let main_ref = FunctionRef {
            file: "main.py".to_string(),
            name: "main".to_string(),
            qualified_name: Some("main.main".to_string()),
        };
        let helper_ref = FunctionRef {
            file: "main.py".to_string(),
            name: "helper".to_string(),
            qualified_name: Some("main.helper".to_string()),
        };
        let utility_ref = FunctionRef {
            file: "utils.py".to_string(),
            name: "utility".to_string(),
            qualified_name: Some("utils.utility".to_string()),
        };
        let orphan_ref = FunctionRef {
            file: "orphan.py".to_string(),
            name: "orphan_func".to_string(),
            qualified_name: Some("orphan.orphan_func".to_string()),
        };
        let test_ref = FunctionRef {
            file: "test_main.py".to_string(),
            name: "test_something".to_string(),
            qualified_name: Some("test_main.test_something".to_string()),
        };
        let dead_island_ref = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_island".to_string(),
            qualified_name: Some("dead.dead_island".to_string()),
        };
        let dead_helper_ref = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_helper".to_string(),
            qualified_name: Some("dead.dead_helper".to_string()),
        };

        graph.edges.push(CallEdge {
            caller: main_ref.clone(),
            callee: helper_ref.clone(),
            call_line: 5,
        });
        graph.edges.push(CallEdge {
            caller: helper_ref.clone(),
            callee: utility_ref.clone(),
            call_line: 10,
        });
        graph.edges.push(CallEdge {
            caller: test_ref.clone(),
            callee: helper_ref.clone(),
            call_line: 3,
        });
        graph.edges.push(CallEdge {
            caller: dead_island_ref.clone(),
            callee: dead_helper_ref.clone(),
            call_line: 2,
        });
        // orphan_ref has no edges (never called, calls nothing)

        // Need to add orphan to the graph somehow - add a self-reference edge
        // Actually, for testing, let's add it calling utility
        graph.edges.push(CallEdge {
            caller: orphan_ref.clone(),
            callee: utility_ref.clone(),
            call_line: 1,
        });

        graph.build_indexes();
        graph
    }

    #[test]
    fn test_detect_entry_points() {
        let graph = create_test_graph();
        let entry_points = detect_entry_points_with_config(&graph, &DeadCodeConfig::default());

        // Should detect main and test_something as entry points
        let names: Vec<_> = entry_points.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"main"));
        assert!(names.contains(&"test_something"));
    }

    #[test]
    fn test_classify_entry_point() {
        assert_eq!(classify_entry_point("main"), Some(EntryPointKind::Main));
        assert_eq!(classify_entry_point("test_foo"), Some(EntryPointKind::Test));
        assert_eq!(
            classify_entry_point("cmd_deploy"),
            Some(EntryPointKind::CliHandler)
        );
        assert_eq!(
            classify_entry_point("api_users"),
            Some(EntryPointKind::ApiEndpoint)
        );
        assert_eq!(
            classify_entry_point("__init__"),
            Some(EntryPointKind::PythonDunder)
        );
        assert_eq!(
            classify_entry_point("setup"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(classify_entry_point("random_name"), None);
    }

    #[test]
    fn test_classify_entry_point_pytest_hooks() {
        // BUG-006 fix: pytest plugin hooks should be classified as FrameworkHook
        // These are dynamically called by pytest and should not be reported as dead code

        // Common pytest plugin hooks
        assert_eq!(
            classify_entry_point("pytest_configure"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_collection"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_runtest_setup"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_runtest_teardown"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_sessionstart"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_sessionfinish"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_addoption"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_collection_modifyitems"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("pytest_generate_tests"),
            Some(EntryPointKind::FrameworkHook)
        );

        // Conftest hooks
        assert_eq!(
            classify_entry_point("conftest_setup"),
            Some(EntryPointKind::FrameworkHook)
        );
        assert_eq!(
            classify_entry_point("conftest_teardown"),
            Some(EntryPointKind::FrameworkHook)
        );

        // Ensure other patterns are not affected
        assert_eq!(
            classify_entry_point("test_pytest_works"),
            Some(EntryPointKind::Test)
        );
        assert_eq!(classify_entry_point("regular_function"), None);
    }

    #[test]
    fn test_is_likely_callback() {
        // Positive cases - should be detected as callbacks
        assert!(is_likely_callback("on_click"));
        assert!(is_likely_callback("on_submit"));
        assert!(is_likely_callback("onClick"));
        assert!(is_likely_callback("onSubmit"));
        assert!(is_likely_callback("OnClick"));
        assert!(is_likely_callback("OnSubmit"));
        assert!(is_likely_callback("button_callback"));
        assert!(is_likely_callback("MyHandler"));
        assert!(is_likely_callback("handleClick"));
        assert!(is_likely_callback("handleSubmit"));
        assert!(is_likely_callback("handle_click"));
        assert!(is_likely_callback("event_listener"));
        assert!(is_likely_callback("EventListener"));
        assert!(is_likely_callback("MyCallback"));

        // Negative cases - should NOT be detected as callbacks
        assert!(!is_likely_callback("process_data"));
        assert!(!is_likely_callback("calculate"));
    }

    #[test]
    fn test_callback_detection_not_too_broad() {
        // BUG-001: These common English words should NOT be detected as callbacks
        // They were false positives due to overly broad starts_with("on")
        assert!(!is_likely_callback("once"));
        assert!(!is_likely_callback("online"));
        assert!(!is_likely_callback("only"));
        assert!(!is_likely_callback("ongoing"));
        assert!(!is_likely_callback("onward"));
        assert!(!is_likely_callback("onset"));

        // PascalCase variants should also not match
        assert!(!is_likely_callback("Once"));
        assert!(!is_likely_callback("Online"));
        assert!(!is_likely_callback("Only"));
        assert!(!is_likely_callback("Ongoing"));

        // "handle" as part of other words should not match
        // Note: "handler" does NOT end with "Handler" (uppercase H), so it correctly does not match
        assert!(!is_likely_callback("handler"));
        assert!(!is_likely_callback("handling"));
        assert!(!is_likely_callback("handled"));

        // Edge cases - too short
        assert!(!is_likely_callback("on"));
        assert!(!is_likely_callback("On"));

        // But valid callbacks should still work
        assert!(is_likely_callback("onClick"));
        assert!(is_likely_callback("on_click"));
        assert!(is_likely_callback("OnClick"));
        assert!(is_likely_callback("handleClick"));
        assert!(is_likely_callback("handle_click"));
    }

    #[test]
    fn test_is_likely_factory() {
        assert!(is_likely_factory("create_user"));
        assert!(is_likely_factory("make_config"));
        assert!(is_likely_factory("build_query"));
        assert!(is_likely_factory("UserFactory"));
        assert!(!is_likely_factory("process_user"));
    }

    #[test]
    fn test_is_likely_public_api() {
        // Positive cases - should be detected as public API

        // Getters - snake_case with underscore
        assert!(is_likely_public_api("get_user"));
        assert!(is_likely_public_api("get_value"));
        assert!(is_likely_public_api("get_config"));

        // Getters - camelCase
        assert!(is_likely_public_api("getUser"));
        assert!(is_likely_public_api("getValue"));
        assert!(is_likely_public_api("getConfig"));

        // Setters - snake_case with underscore
        assert!(is_likely_public_api("set_user"));
        assert!(is_likely_public_api("set_value"));
        assert!(is_likely_public_api("set_config"));

        // Setters - camelCase
        assert!(is_likely_public_api("setUser"));
        assert!(is_likely_public_api("setValue"));
        assert!(is_likely_public_api("setConfig"));

        // Boolean accessors
        assert!(is_likely_public_api("is_valid"));
        assert!(is_likely_public_api("has_data"));
        assert!(is_likely_public_api("can_proceed"));
        assert!(is_likely_public_api("should_retry"));

        // Builder/converter patterns
        assert!(is_likely_public_api("with_timeout"));
        assert!(is_likely_public_api("from_bytes"));
        assert!(is_likely_public_api("to_string"));
        assert!(is_likely_public_api("as_ref"));

        // PascalCase (public types/classes)
        assert!(is_likely_public_api("UserManager"));
        assert!(is_likely_public_api("Config"));
    }

    #[test]
    fn test_public_api_detection_not_too_broad() {
        // BUG-002: These common English words should NOT be detected as public API
        // They were false positives due to overly broad starts_with("get")/starts_with("set")

        // get* false positives
        assert!(!is_likely_public_api("gettext"));
        assert!(!is_likely_public_api("getter"));
        assert!(!is_likely_public_api("getaway"));
        assert!(!is_likely_public_api("getopt"));
        assert!(!is_likely_public_api("getenv")); // lowercase 'e' after "get"

        // set* false positives
        assert!(!is_likely_public_api("settings"));
        assert!(!is_likely_public_api("settle"));
        assert!(!is_likely_public_api("setup"));
        assert!(!is_likely_public_api("setter"));
        assert!(!is_likely_public_api("setback"));

        // Edge cases - too short
        assert!(!is_likely_public_api("get"));
        assert!(!is_likely_public_api("set"));

        // Private functions (underscore prefix)
        assert!(!is_likely_public_api("_get_value"));
        assert!(!is_likely_public_api("_set_value"));
        assert!(!is_likely_public_api("_private"));

        // Regular function names (not public API patterns)
        assert!(!is_likely_public_api("process_data"));
        assert!(!is_likely_public_api("calculate"));
        assert!(!is_likely_public_api("helper"));
    }

    #[test]
    fn test_analyze_dead_code() {
        let graph = create_test_graph();
        let result = analyze_dead_code(&graph);

        // dead_island and dead_helper should be detected as dead
        // orphan_func might be detected depending on heuristics
        assert!(result.total_dead > 0);

        // Check stats
        assert!(result.stats.entry_point_count > 0);
        assert!(result.stats.reachable_count > 0);
    }

    #[test]
    fn test_compute_reachability() {
        let graph = create_test_graph();
        let entry_points = detect_entry_points_with_config(&graph, &DeadCodeConfig::default());
        let reachable = compute_reachability(&graph, &entry_points);

        // main, helper, utility should be reachable
        // test_something should be reachable (it's an entry point)
        assert!(reachable.iter().any(|f| f.name == "main"));
        assert!(reachable.iter().any(|f| f.name == "helper"));
        assert!(reachable.iter().any(|f| f.name == "utility"));
        assert!(reachable.iter().any(|f| f.name == "test_something"));

        // dead_island should NOT be reachable
        assert!(!reachable.iter().any(|f| f.name == "dead_island"));
    }

    #[test]
    fn test_check_false_positive() {
        let config = DeadCodeConfig::default();

        let callback_func = FunctionRef {
            file: "test.py".to_string(),
            name: "on_click".to_string(),
            qualified_name: None,
        };
        let (is_fp, reason) = check_false_positive(&callback_func, &config);
        assert!(is_fp);
        assert_eq!(reason, "callback");

        let normal_func = FunctionRef {
            file: "test.py".to_string(),
            name: "process_data".to_string(),
            qualified_name: None,
        };
        let (is_fp, _) = check_false_positive(&normal_func, &config);
        assert!(!is_fp);
    }

    #[test]
    fn test_check_false_positive_no_redundant_handler_detection() {
        // BUG-007 fix: check_false_positive() should NOT have redundant on_/On checks
        // that bypass is_likely_callback()'s strict uppercase requirements.
        // Words like "Ongoing", "Online", "Once" should NOT be false positives.
        let config = DeadCodeConfig::default();

        // These common words should NOT be marked as handlers/callbacks
        // because they don't follow the callback pattern (third char must be uppercase)
        let false_positive_cases = ["Ongoing", "Online", "Once", "Onward", "Onset"];
        for name in false_positive_cases {
            let func = FunctionRef {
                file: "test.py".to_string(),
                name: name.to_string(),
                qualified_name: None,
            };
            let (is_fp, reason) = check_false_positive(&func, &config);
            assert!(
                !is_fp,
                "{} should NOT be a false positive, but got reason: {}",
                name, reason
            );
        }

        // Proper callbacks with uppercase third char SHOULD still be detected
        let valid_callbacks = ["OnClick", "OnSubmit", "OnChange", "on_click", "onClick"];
        for name in valid_callbacks {
            let func = FunctionRef {
                file: "test.py".to_string(),
                name: name.to_string(),
                qualified_name: None,
            };
            let (is_fp, reason) = check_false_positive(&func, &config);
            assert!(
                is_fp && reason == "callback",
                "{} should be detected as callback, but got: is_fp={}, reason={}",
                name,
                is_fp,
                reason
            );
        }

        // Event patterns (not covered by is_likely_callback) should still be detected
        let event_handlers = ["user_event", "MouseEvent", "handle_event", "KeyboardEvent"];
        for name in event_handlers {
            let func = FunctionRef {
                file: "test.py".to_string(),
                name: name.to_string(),
                qualified_name: None,
            };
            let (is_fp, _) = check_false_positive(&func, &config);
            assert!(
                is_fp,
                "{} should be detected as false positive (event handler)",
                name
            );
        }
    }

    #[test]
    fn test_dead_reason_classification() {
        let mut graph = CallGraph::default();

        let caller = FunctionRef {
            file: "a.py".to_string(),
            name: "caller".to_string(),
            qualified_name: None,
        };
        let callee = FunctionRef {
            file: "a.py".to_string(),
            name: "callee".to_string(),
            qualified_name: None,
        };
        let orphan = FunctionRef {
            file: "a.py".to_string(),
            name: "orphan".to_string(),
            qualified_name: None,
        };

        graph.edges.push(CallEdge {
            caller: caller.clone(),
            callee: callee.clone(),
            call_line: 1,
        });
        graph.build_indexes();

        let mut reachable = HashSet::new();
        reachable.insert(caller.clone());

        // orphan is never called
        let reason = determine_dead_reason(&orphan, &graph, &reachable);
        assert_eq!(reason, DeadReason::NeverCalled);

        // callee is called only by reachable caller, so actually not dead
        // But if we make caller not reachable...
        let empty_reachable = HashSet::new();
        let reason = determine_dead_reason(&callee, &graph, &empty_reachable);
        assert_eq!(reason, DeadReason::CalledOnlyByDead);
    }

    #[test]
    fn test_config_min_confidence() {
        let graph = create_test_graph();

        // With high confidence threshold, should filter more
        let config = DeadCodeConfig {
            min_confidence: 0.99,
            ..Default::default()
        };
        let result = analyze_dead_code_with_config(&graph, &config);

        // With lower threshold, should report more
        let config_low = DeadCodeConfig {
            min_confidence: 0.1,
            ..Default::default()
        };
        let result_low = analyze_dead_code_with_config(&graph, &config_low);

        // Lower threshold should find same or more dead code
        assert!(result_low.total_dead >= result.total_dead);
    }

    #[test]
    fn test_user_defined_filter_patterns() {
        let graph = create_test_graph();

        // Add custom filter pattern
        let config = DeadCodeConfig {
            filter_patterns: vec!["orphan".to_string()],
            ..Default::default()
        };

        let result = analyze_dead_code_with_config(&graph, &config);

        // orphan_func should be filtered out
        assert!(!result
            .dead_functions
            .iter()
            .any(|f| f.name.contains("orphan")));
    }

    #[test]
    fn test_include_public_api_patterns_opt_in() {
        // BUG-003 fix verification: is_likely_public_api() is too permissive
        // and should be opt-in via config.include_public_api_patterns

        let default_config = DeadCodeConfig::default();
        assert!(!default_config.include_public_api_patterns); // Should be false by default

        // PascalCase functions should NOT be entry points with default config
        // (Note: these don't start with Create/Make/Build/New which would be factories)
        assert!(!is_likely_entry_point("UserManager", Some(&default_config)));
        assert!(!is_likely_entry_point("Config", Some(&default_config)));
        assert!(!is_likely_entry_point(
            "DatabaseConnection",
            Some(&default_config)
        ));

        // camelCase getters/setters should NOT be entry points with default config
        // (Note: get_/set_ with underscore ARE entry points via classify_entry_point
        // as API endpoints, so we test camelCase versions like getUser, setValue)
        assert!(!is_likely_entry_point("getUser", Some(&default_config)));
        assert!(!is_likely_entry_point("setValue", Some(&default_config)));
        assert!(!is_likely_entry_point("getData", Some(&default_config)));
        assert!(!is_likely_entry_point("setConfig", Some(&default_config)));

        // Boolean accessors should NOT be entry points with default config
        // (is_, has_, can_ are in is_likely_public_api but NOT in classify_entry_point)
        assert!(!is_likely_entry_point("is_valid", Some(&default_config)));
        assert!(!is_likely_entry_point("has_data", Some(&default_config)));
        assert!(!is_likely_entry_point("can_proceed", Some(&default_config)));

        // Builder/converter patterns should NOT be entry points with default config
        // (from_, to_, with_, as_ are in is_likely_public_api but NOT classify_entry_point)
        assert!(!is_likely_entry_point("from_bytes", Some(&default_config)));
        assert!(!is_likely_entry_point("to_string", Some(&default_config)));
        assert!(!is_likely_entry_point(
            "with_timeout",
            Some(&default_config)
        ));
        assert!(!is_likely_entry_point("as_ref", Some(&default_config)));

        // But they SHOULD be entry points when include_public_api_patterns is enabled
        let permissive_config = DeadCodeConfig {
            include_public_api_patterns: true,
            ..Default::default()
        };

        assert!(is_likely_entry_point(
            "UserManager",
            Some(&permissive_config)
        ));
        assert!(is_likely_entry_point("getUser", Some(&permissive_config)));
        assert!(is_likely_entry_point("is_valid", Some(&permissive_config)));
        assert!(is_likely_entry_point(
            "from_bytes",
            Some(&permissive_config)
        ));
        assert!(is_likely_entry_point("to_string", Some(&permissive_config)));

        // Core entry points should ALWAYS work regardless of config
        assert!(is_likely_entry_point("main", Some(&default_config)));
        assert!(is_likely_entry_point(
            "test_something",
            Some(&default_config)
        ));
        assert!(is_likely_entry_point("onClick", Some(&default_config))); // callback
        assert!(is_likely_entry_point("create_user", Some(&default_config))); // factory (create_ prefix)
        assert!(is_likely_entry_point("get_user", Some(&default_config))); // API endpoint (get_ prefix)
    }

    #[test]
    fn test_extra_entry_patterns() {
        // Test that extra_entry_patterns config works correctly

        let config = DeadCodeConfig {
            extra_entry_patterns: vec!["plugin_".to_string(), "hook_".to_string()],
            ..Default::default()
        };

        // Custom patterns should match
        assert!(is_likely_entry_point("plugin_load", Some(&config)));
        assert!(is_likely_entry_point("plugin_unload", Some(&config)));
        assert!(is_likely_entry_point("hook_before", Some(&config)));
        assert!(is_likely_entry_point("hook_after", Some(&config)));

        // Without config, these should NOT match
        assert!(!is_likely_entry_point(
            "plugin_load",
            Some(&DeadCodeConfig::default())
        ));
        assert!(!is_likely_entry_point(
            "hook_before",
            Some(&DeadCodeConfig::default())
        ));

        // Regular functions should still not match
        assert!(!is_likely_entry_point("process_data", Some(&config)));
        assert!(!is_likely_entry_point("helper", Some(&config)));
    }

    #[test]
    fn test_balanced_confidence_scoring() {
        // BUG-008 fix verification: Confidence scoring should be balanced
        // - Start at 0.5 (neutral), not 1.0
        // - Short utility functions should NOT get high confidence
        // - Multiple factors should contribute symmetrically

        let mut graph = CallGraph::default();

        // Create test functions with different characteristics
        let short_func = FunctionRef {
            file: "utils.py".to_string(),
            name: "x".to_string(), // Very short name (1 char)
            qualified_name: None,
        };

        let pascal_case_func = FunctionRef {
            file: "models.py".to_string(),
            name: "UserManager".to_string(), // PascalCase
            qualified_name: None,
        };

        let private_func = FunctionRef {
            file: "internal.py".to_string(),
            name: "_helper".to_string(), // Private naming
            qualified_name: None,
        };

        let api_func = FunctionRef {
            file: "src/api/routes.py".to_string(),
            name: "process_request".to_string(),
            qualified_name: None,
        };

        let dead_caller = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_caller".to_string(),
            qualified_name: None,
        };

        let dead_callee1 = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_callee1".to_string(),
            qualified_name: None,
        };

        let dead_callee2 = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_callee2".to_string(),
            qualified_name: None,
        };

        let dead_callee3 = FunctionRef {
            file: "dead.py".to_string(),
            name: "dead_callee3".to_string(),
            qualified_name: None,
        };

        let factory_func = FunctionRef {
            file: "factories.py".to_string(),
            name: "create_user".to_string(), // Factory pattern
            qualified_name: None,
        };

        // Add edges for dead_caller calling multiple dead functions
        graph.edges.push(CallEdge {
            caller: dead_caller.clone(),
            callee: dead_callee1.clone(),
            call_line: 1,
        });
        graph.edges.push(CallEdge {
            caller: dead_caller.clone(),
            callee: dead_callee2.clone(),
            call_line: 2,
        });
        graph.edges.push(CallEdge {
            caller: dead_caller.clone(),
            callee: dead_callee3.clone(),
            call_line: 3,
        });

        graph.build_indexes();

        // Empty reachable set (all functions are "dead" for testing purposes)
        let reachable = HashSet::new();

        // Test 1: Short function should NOT get high confidence (was 0.8 with old code)
        // With balanced scoring: 0.5 (base) + 0.2 (no callers) + 0.1 (not in common path) - 0.1 (short) = 0.7
        let short_conf = compute_confidence(&short_func, &graph, &reachable);
        assert!(
            short_conf < 0.8,
            "Short function 'x' should have confidence < 0.8, got {}",
            short_conf
        );
        assert!(
            short_conf >= 0.6 && short_conf <= 0.75,
            "Short function 'x' should have balanced confidence around 0.7, got {}",
            short_conf
        );

        // Test 2: PascalCase function should have lower confidence
        // 0.5 (base) + 0.2 (no callers) + 0.1 (not in common path) - 0.15 (PascalCase) = 0.65
        let pascal_conf = compute_confidence(&pascal_case_func, &graph, &reachable);
        assert!(
            pascal_conf < short_conf,
            "PascalCase function should have lower confidence than short function"
        );

        // Test 3: Private function should have higher confidence
        // 0.5 (base) + 0.2 (no callers) + 0.1 (not in common path) + 0.1 (private) = 0.9
        let private_conf = compute_confidence(&private_func, &graph, &reachable);
        assert!(
            private_conf > short_conf,
            "Private function should have higher confidence than short function"
        );

        // Test 4: Function in /api/ should have lower confidence
        // 0.5 (base) + 0.2 (no callers) - 0.2 (in /api/) = 0.5
        // Note: is_in_common_module_path returns true, so no +0.1 for that
        let api_conf = compute_confidence(&api_func, &graph, &reachable);
        assert!(
            api_conf <= 0.55,
            "Function in /api/ path should have confidence around 0.5, got {}",
            api_conf
        );

        // Test 5: Function calling multiple dead functions should have high confidence
        // 0.5 (base) + 0.1 (not in common path) + 0.3 (3 dead callees, capped) = 0.9
        // Note: has callers/callees so no +0.2 for no callers
        let dead_caller_conf = compute_confidence(&dead_caller, &graph, &reachable);
        assert!(
            dead_caller_conf >= 0.8,
            "Function calling 3 dead functions should have confidence >= 0.8, got {}",
            dead_caller_conf
        );

        // Test 6: Factory function should have reduced confidence
        // 0.5 (base) + 0.2 (no callers) + 0.1 (not in common path) - 0.15 (factory) = 0.65
        let factory_conf = compute_confidence(&factory_func, &graph, &reachable);
        assert!(
            factory_conf < 0.7,
            "Factory function should have confidence < 0.7, got {}",
            factory_conf
        );

        // Test 7: Verify base confidence is now 0.5 (neutral) instead of 1.0
        // A function with no special characteristics should be around 0.5 + 0.2 (no callers) = 0.7
        let neutral_func = FunctionRef {
            file: "src/lib/module.py".to_string(), // In /lib/ path
            name: "process".to_string(),           // Generic name, 7 chars
            qualified_name: None,
        };
        let neutral_conf = compute_confidence(&neutral_func, &graph, &reachable);
        // 0.5 (base) + 0.2 (no callers) = 0.7 (in common path, so no +0.1)
        assert!(
            neutral_conf >= 0.6 && neutral_conf <= 0.75,
            "Neutral function should have confidence around 0.7, got {}",
            neutral_conf
        );
    }

    #[test]
    fn test_is_in_common_module_path() {
        // Test the helper function for module path detection
        assert!(is_in_common_module_path("/project/api/routes.py"));
        assert!(is_in_common_module_path("src/public/index.html"));
        assert!(is_in_common_module_path("/app/lib/utils.py"));
        assert!(is_in_common_module_path("src/handlers/user.py"));
        assert!(is_in_common_module_path("/project/routes/auth.ts"));
        assert!(is_in_common_module_path("app/controllers/main.rb"));
        assert!(is_in_common_module_path("src/endpoints/v1.py"));
        assert!(is_in_common_module_path("/app/views/home.py"));
        assert!(is_in_common_module_path("backend/services/auth.py"));
        assert!(is_in_common_module_path("cli/commands/deploy.py"));

        // Non-common paths should return false
        assert!(!is_in_common_module_path("src/utils/helper.py"));
        assert!(!is_in_common_module_path("internal/processor.py"));
        assert!(!is_in_common_module_path("core/database.py"));
        assert!(!is_in_common_module_path("models/user.py"));
        assert!(!is_in_common_module_path("tests/test_main.py"));
    }
}
