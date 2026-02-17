//! Impact analysis (reverse call graph).
//!
//! Analyzes the impact of changing a function by finding all functions
//! that directly or transitively call it. Uses BFS traversal to track
//! exact distance from the target function.
//!
//! # Depth Semantics
//!
//! The `max_depth` parameter controls how many levels of the call hierarchy
//! are **explored** (matching Python semantics):
//!
//! - `max_depth = 0`: NO exploration - returns only direct callers (distance 1), truncated
//! - `max_depth = 1`: Explore direct callers (distance 1), finding their callers (distance 2)
//! - `max_depth = 2`: Explore up to distance 2, finding callers up to distance 3
//! - `max_depth = N`: Explore up to distance N, potentially discovering callers at distance N+1
//!
//! This matches Python's recursive `_build_caller_tree` where `depth <= 0` causes
//! immediate truncation with no further exploration.
//!
//! # Usage
//!
//! ```ignore
//! use brrr::callgraph::impact::{analyze_impact, ImpactConfig};
//!
//! let config = ImpactConfig::new()
//!     .with_depth(3)  // Explore up to depth 3, find callers up to depth 4
//!     .exclude_tests();
//!
//! let result = analyze_impact(&graph, "process_data", config);
//! println!("{}", result.to_llm_context());
//! ```

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::callgraph::types::{CallGraph, FunctionRef};

/// Configuration for impact analysis.
#[derive(Debug, Clone)]
pub struct ImpactConfig {
    /// Maximum depth to traverse (0 = NO traversal, direct callers only).
    ///
    /// This controls how many levels of the call hierarchy are explored:
    /// - `max_depth = 0`: NO exploration - returns only direct callers (distance 1)
    /// - `max_depth = 1`: Explore direct callers to find distance 2 callers
    /// - `max_depth = 2`: Explore up to distance 2, finding callers up to distance 3
    /// - `max_depth = N`: Explore up to distance N, potentially finding callers at distance N+1
    ///
    /// This matches Python semantics where `depth <= 0` causes immediate truncation.
    /// Note: The depth controls exploration, not the maximum distance in results.
    pub max_depth: usize,
    /// Filter by language (e.g., "python", "rust").
    pub language: Option<String>,
    /// Glob patterns to include (e.g., "src/**/*.rs").
    pub include_patterns: Vec<String>,
    /// Glob patterns to exclude (e.g., "**/test/**").
    pub exclude_patterns: Vec<String>,
    /// Whether to exclude test files from results.
    pub exclude_tests: bool,
    /// Whether to include call site information.
    pub include_call_sites: bool,
    /// If true, each node appears only once (first path wins, BFS behavior).
    /// If false, all paths are explored with per-branch visited sets (DFS, Python semantics).
    /// When false, the minimum distance across all paths is recorded for each node.
    ///
    /// For diamond-shaped call graphs like:
    /// ```text
    ///     A
    ///    / \
    ///   B   C
    ///    \ /
    ///     D (target)
    /// ```
    /// - `deduplicate_paths = true`: A appears once at distance 2 (via first explored path)
    /// - `deduplicate_paths = false`: All paths explored, A at minimum distance 2 with aggregated call sites
    pub deduplicate_paths: bool,
}

impl Default for ImpactConfig {
    fn default() -> Self {
        Self {
            max_depth: 0,
            language: None,
            include_patterns: Vec::new(),
            exclude_patterns: Vec::new(),
            exclude_tests: false,
            include_call_sites: false,
            deduplicate_paths: true, // Default to current Rust behavior for backward compatibility
        }
    }
}

impl ImpactConfig {
    /// Create a new default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set maximum traversal depth.
    ///
    /// The depth controls how many levels of callers are explored. With depth N,
    /// the algorithm explores callers up to distance N from the target, which
    /// means callers at distance N+1 may be discovered but not explored further.
    pub fn with_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    /// Filter results by language.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn with_language(mut self, lang: &str) -> Self {
        self.language = Some(lang.to_string());
        self
    }

    /// Add file patterns to include.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn with_includes(mut self, patterns: &[&str]) -> Self {
        self.include_patterns = patterns.iter().map(|s| (*s).to_string()).collect();
        self
    }

    /// Add file patterns to exclude.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn with_excludes(mut self, patterns: &[&str]) -> Self {
        self.exclude_patterns = patterns.iter().map(|s| (*s).to_string()).collect();
        self
    }

    /// Exclude test files from results.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn exclude_tests(mut self) -> Self {
        self.exclude_tests = true;
        self
    }

    /// Include call site line numbers in results.
    pub fn with_call_sites(mut self) -> Self {
        self.include_call_sites = true;
        self
    }

    /// Enable or disable path deduplication.
    ///
    /// When enabled (default), each node appears only once using BFS traversal.
    /// When disabled, all paths are explored using DFS with per-branch visited sets,
    /// matching Python's `_build_caller_tree` semantics where `visited.copy()` is used.
    ///
    /// Use `false` for complete path exploration in diamond-shaped call graphs.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn with_deduplicate_paths(mut self, deduplicate: bool) -> Self {
        self.deduplicate_paths = deduplicate;
        self
    }

    /// Disable path deduplication to explore all paths (Python-compatible mode).
    ///
    /// This is a convenience method equivalent to `with_deduplicate_paths(false)`.
    // Builder API for library consumers
    #[allow(dead_code)]
    pub fn explore_all_paths(mut self) -> Self {
        self.deduplicate_paths = false;
        self
    }
}

/// Result of impact analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImpactResult {
    /// Target function analyzed.
    pub target: String,
    /// File containing the target (if resolved to single file).
    pub target_file: Option<String>,
    /// Depth of analysis performed.
    pub depth: usize,
    /// Functions that directly or indirectly call the target.
    pub callers: Vec<CallerInfo>,
    /// Total count of affected functions.
    pub total_affected: usize,
    /// Callers grouped by distance level.
    pub by_distance: FxHashMap<usize, usize>,
    /// Callers grouped by file.
    pub by_file: FxHashMap<String, usize>,
}

impl ImpactResult {
    /// Generate LLM-ready context string.
    ///
    /// Produces a structured text format suitable for LLM consumption,
    /// organized by distance from the target function.
    // Public API for library consumers
    #[allow(dead_code)]
    pub fn to_llm_context(&self) -> String {
        let mut output = String::with_capacity(4096);

        // Header
        output.push_str(&format!("# Impact Analysis: {}\n\n", self.target));

        if let Some(ref file) = self.target_file {
            output.push_str(&format!("Target file: {}\n", file));
        }

        output.push_str(&format!(
            "Total affected: {} functions at {} depth levels\n\n",
            self.total_affected,
            self.by_distance.len()
        ));

        // Group callers by distance
        let mut by_distance: FxHashMap<usize, Vec<&CallerInfo>> = FxHashMap::default();
        for caller in &self.callers {
            by_distance.entry(caller.distance).or_default().push(caller);
        }

        // Output by distance level
        let mut distances: Vec<_> = by_distance.keys().copied().collect();
        distances.sort();

        for distance in distances {
            let callers = &by_distance[&distance];
            output.push_str(&format!(
                "## Distance {} ({} functions)\n\n",
                distance,
                callers.len()
            ));

            // Group by file within distance level
            let mut by_file: FxHashMap<&str, Vec<&CallerInfo>> = FxHashMap::default();
            for caller in callers {
                by_file.entry(&caller.file).or_default().push(caller);
            }

            let mut files: Vec<_> = by_file.keys().copied().collect();
            files.sort();

            for file in files {
                let file_callers = &by_file[file];
                output.push_str(&format!("### {}\n", file));

                for caller in file_callers {
                    output.push_str(&format!("- {}", caller.name));
                    if !caller.call_sites.is_empty() {
                        let sites: Vec<_> =
                            caller.call_sites.iter().map(|s| s.to_string()).collect();
                        output.push_str(&format!(" (lines: {})", sites.join(", ")));
                    }
                    output.push('\n');
                }
                output.push('\n');
            }
        }

        // Summary section
        output.push_str("## Summary by File\n\n");
        let mut file_counts: Vec<_> = self.by_file.iter().collect();
        file_counts.sort_by(|a, b| b.1.cmp(a.1)); // Sort by count descending

        for (file, count) in file_counts.iter().take(10) {
            output.push_str(&format!("- {}: {} functions\n", file, count));
        }

        if file_counts.len() > 10 {
            output.push_str(&format!(
                "- ... and {} more files\n",
                file_counts.len() - 10
            ));
        }

        output
    }

    /// Convert to JSON for API consumption.
    // Public API for library consumers
    #[allow(dead_code)]
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "target": self.target,
            "target_file": self.target_file,
            "depth": self.depth,
            "total_affected": self.total_affected,
            "callers": self.callers,
            "by_distance": self.by_distance,
            "by_file": self.by_file
        })
    }
}

/// Information about a caller function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallerInfo {
    /// File containing the caller.
    pub file: String,
    /// Function name.
    pub name: String,
    /// Fully qualified name (if available).
    pub qualified_name: Option<String>,
    /// Distance from target (1 = direct caller, 2 = caller of caller, etc.).
    pub distance: usize,
    /// Line numbers where calls to the target occur.
    pub call_sites: Vec<usize>,
}

/// Analyze impact of changing a function.
///
/// Finds all functions that directly or indirectly call the target function,
/// tracking the exact distance (number of call chain hops) from the target.
///
/// The traversal strategy depends on `config.deduplicate_paths`:
/// - `true` (default): BFS with global visited set - each node appears once, first path wins
/// - `false`: DFS with per-path visited sets - all paths explored, minimum distance recorded
///
/// # Arguments
///
/// * `graph` - The call graph to analyze
/// * `target` - Name of the target function (can be unqualified)
/// * `config` - Configuration for filtering and depth limits
///
/// # Returns
///
/// An `ImpactResult` containing all callers with their distances and call sites.
pub fn analyze_impact(graph: &CallGraph, target: &str, config: ImpactConfig) -> ImpactResult {
    // Build reverse index: callee -> [(caller, call_line)]
    // The reverse index uses full FunctionRef identity (file + name + qualified_name),
    // ensuring that functions with the same name in different files are tracked separately.
    let reverse_index = build_reverse_index(graph);

    // Build name index for O(1) lookup by function name.
    // This enables efficient target matching without O(E) linear scans.
    // Complexity: O(V) where V = unique callees, done once before BFS/DFS.
    let name_index = build_name_index(&reverse_index);

    // Find all functions matching the target name using O(1) name index lookup.
    // Previous implementation used O(E) scan through all_functions().
    // Use FxHashSet for O(1) membership testing (BUG-018 fix: prevents O(n) linear search)
    let target_matches: FxHashSet<FunctionRef> = find_matching_targets_indexed(&name_index, target)
        .into_iter()
        .cloned()
        .collect();

    if target_matches.is_empty() {
        return ImpactResult {
            target: target.to_string(),
            target_file: None,
            depth: 0,
            callers: Vec::new(),
            total_affected: 0,
            by_distance: FxHashMap::default(),
            by_file: FxHashMap::default(),
        };
    }

    // Determine target file (if unique)
    let target_file = if target_matches.len() == 1 {
        target_matches.iter().next().map(|f| f.file.clone())
    } else {
        None
    };

    // Branch based on deduplication mode
    let callers_map = if config.deduplicate_paths {
        // BFS with global visited set (original Rust behavior)
        analyze_impact_bfs(&reverse_index, &target_matches, &config)
    } else {
        // DFS with per-path visited sets (Python-compatible behavior)
        analyze_impact_dfs(&reverse_index, &target_matches, &config)
    };

    // Convert to CallerInfo list
    let mut callers: Vec<CallerInfo> = callers_map
        .into_iter()
        .map(|(func, (distance, call_sites))| CallerInfo {
            file: func.file.clone(),
            name: func.name.clone(),
            qualified_name: func.qualified_name.clone(),
            distance,
            call_sites,
        })
        .collect();

    // Sort by distance, then by file, then by name
    callers.sort_by(|a, b| {
        a.distance
            .cmp(&b.distance)
            .then_with(|| a.file.cmp(&b.file))
            .then_with(|| a.name.cmp(&b.name))
    });

    // Calculate statistics
    let total_affected = callers.len();
    let max_distance = callers.iter().map(|c| c.distance).max().unwrap_or(0);

    let mut by_distance: FxHashMap<usize, usize> = FxHashMap::default();
    let mut by_file: FxHashMap<String, usize> = FxHashMap::default();

    for caller in &callers {
        *by_distance.entry(caller.distance).or_insert(0) += 1;
        *by_file.entry(caller.file.clone()).or_insert(0) += 1;
    }

    ImpactResult {
        target: target.to_string(),
        target_file,
        depth: max_distance,
        callers,
        total_affected,
        by_distance,
        by_file,
    }
}

/// BFS traversal with global visited set (original Rust behavior).
///
/// Each node appears only once - the first path to reach it determines its distance.
/// This is efficient for large graphs but may miss some path information in diamond
/// patterns.
///
/// Complexity: O(V + E) where V = visited nodes, E = edges traversed.
/// Uses O(1) FxHashMap lookups via reverse_index (keyed by full FunctionRef).
fn analyze_impact_bfs(
    reverse_index: &ReverseIndex,
    target_matches: &FxHashSet<FunctionRef>,
    config: &ImpactConfig,
) -> FxHashMap<FunctionRef, (usize, Vec<usize>)> {
    let mut visited: FxHashSet<FunctionRef> = FxHashSet::default();
    let mut callers_map: FxHashMap<FunctionRef, (usize, Vec<usize>)> = FxHashMap::default();
    let mut queue: VecDeque<(FunctionRef, usize)> = VecDeque::new();

    // Initialize queue with direct callers of all matching targets
    for target_ref in target_matches {
        if let Some(callers) = reverse_index.get(target_ref) {
            for (caller, call_line) in callers {
                if !visited.contains(caller) && should_include(caller, config) {
                    visited.insert(caller.clone());
                    let entry = callers_map.entry(caller.clone()).or_insert((1, Vec::new()));
                    if config.include_call_sites {
                        entry.1.push(*call_line);
                    }
                    queue.push_back((caller.clone(), 1));
                }
            }
        }
    }

    // BFS traversal - max_depth controls exploration depth
    let max_depth = config.max_depth;

    while let Some((func, distance)) = queue.pop_front() {
        // Stop exploring beyond max depth
        if distance > max_depth {
            continue;
        }

        if let Some(callers) = reverse_index.get(&func) {
            for (caller, call_line) in callers {
                if !visited.contains(caller) && should_include(caller, config) {
                    visited.insert(caller.clone());
                    let new_distance = distance + 1;
                    let entry = callers_map
                        .entry(caller.clone())
                        .or_insert((new_distance, Vec::new()));
                    if config.include_call_sites {
                        entry.1.push(*call_line);
                    }
                    queue.push_back((caller.clone(), new_distance));
                }
            }
        }
    }

    callers_map
}

/// DFS traversal with per-path visited sets (Python-compatible behavior).
///
/// Explores all paths independently, like Python's `_build_caller_tree` with
/// `visited.copy()`. Each node can be explored through multiple paths, but
/// appears once in the output with the minimum distance across all paths.
/// Call sites are aggregated from all paths.
///
/// This matches Python semantics for diamond-shaped call graphs:
/// ```text
///     A
///    / \
///   B   C
///    \ /
///     D (target)
/// ```
/// Both paths D->B->A and D->C->A are explored, and A gets the minimum distance.
///
/// Complexity: O(V + E) for simple graphs, potentially O(V * paths) for diamond patterns.
/// Uses O(1) FxHashMap lookups via reverse_index (keyed by full FunctionRef).
fn analyze_impact_dfs(
    reverse_index: &ReverseIndex,
    target_matches: &FxHashSet<FunctionRef>,
    config: &ImpactConfig,
) -> FxHashMap<FunctionRef, (usize, Vec<usize>)> {
    let mut all_callers: FxHashMap<FunctionRef, (usize, Vec<usize>)> = FxHashMap::default();
    let max_depth = config.max_depth;

    /// Recursive DFS helper with per-path visited set.
    fn dfs_explore(
        func: &FunctionRef,
        distance: usize,
        max_depth: usize,
        visited: &mut FxHashSet<FunctionRef>,
        reverse_index: &FxHashMap<FunctionRef, Vec<(FunctionRef, usize)>>,
        all_callers: &mut FxHashMap<FunctionRef, (usize, Vec<usize>)>,
        config: &ImpactConfig,
    ) {
        // Base case: beyond max exploration depth or cycle in current path
        if distance > max_depth || visited.contains(func) {
            return;
        }

        // Mark as visited in THIS path
        visited.insert(func.clone());

        // Explore callers of this function
        if let Some(callers) = reverse_index.get(func) {
            for (caller, call_line) in callers {
                if !should_include(caller, config) {
                    continue;
                }

                let new_distance = distance + 1;

                // Update or insert caller with minimum distance
                let entry = all_callers
                    .entry(caller.clone())
                    .or_insert((new_distance, Vec::new()));

                // Take minimum distance if seen via multiple paths
                entry.0 = entry.0.min(new_distance);

                // Aggregate call sites from all paths (avoid duplicates)
                if config.include_call_sites && !entry.1.contains(call_line) {
                    entry.1.push(*call_line);
                }

                // Recurse with CLONED visited set (Python semantics: visited.copy())
                let mut branch_visited = visited.clone();
                dfs_explore(
                    caller,
                    new_distance,
                    max_depth,
                    &mut branch_visited,
                    reverse_index,
                    all_callers,
                    config,
                );
            }
        }
    }

    // Start DFS from each target's direct callers
    for target_ref in target_matches {
        if let Some(callers) = reverse_index.get(target_ref) {
            for (caller, call_line) in callers {
                if !should_include(caller, config) {
                    continue;
                }

                // Record direct caller (distance 1)
                let entry = all_callers.entry(caller.clone()).or_insert((1, Vec::new()));
                entry.0 = entry.0.min(1);
                if config.include_call_sites && !entry.1.contains(call_line) {
                    entry.1.push(*call_line);
                }

                // Start DFS from this direct caller with fresh per-path visited set
                let mut visited = FxHashSet::default();
                visited.insert(target_ref.clone()); // Don't revisit target
                dfs_explore(
                    caller,
                    1,
                    max_depth,
                    &mut visited,
                    reverse_index,
                    &mut all_callers,
                    config,
                );
            }
        }
    }

    all_callers
}

/// Reverse index: callee -> [(caller, call_line)].
type ReverseIndex = FxHashMap<FunctionRef, Vec<(FunctionRef, usize)>>;

/// Name-based index for O(1) lookup of functions by name.
/// Maps function name -> all FunctionRefs with that name.
type NameIndex<'a> = FxHashMap<&'a str, Vec<&'a FunctionRef>>;

/// Build reverse index: callee -> [(caller, call_line)].
fn build_reverse_index(graph: &CallGraph) -> ReverseIndex {
    let mut index: ReverseIndex = FxHashMap::default();

    for edge in &graph.edges {
        index
            .entry(edge.callee.clone())
            .or_default()
            .push((edge.caller.clone(), edge.call_line));
    }

    index
}

/// Build name index for O(1) lookup by function name.
/// This avoids O(E) linear scans when matching by name during BFS/DFS.
fn build_name_index(reverse_index: &ReverseIndex) -> NameIndex<'_> {
    let mut name_index: NameIndex<'_> = FxHashMap::default();

    for func_ref in reverse_index.keys() {
        name_index
            .entry(func_ref.name.as_str())
            .or_default()
            .push(func_ref);
    }

    name_index
}

/// Find all function refs that match the target name using O(1) name index lookup.
///
/// This replaces the previous O(V) scan with O(1) lookup by name, plus O(k) where
/// k is the number of functions with matching names (typically small).
fn find_matching_targets_indexed<'a>(
    name_index: &'a NameIndex<'a>,
    target: &str,
) -> Vec<&'a FunctionRef> {
    let mut matches = Vec::new();

    // O(1) lookup by exact name match
    if let Some(funcs) = name_index.get(target) {
        matches.extend(funcs.iter().copied());
    }

    // Also check for qualified name matches (target might be "Class.method")
    // This requires checking all entries, but only when target contains '.'
    if target.contains('.') {
        for (_name, funcs) in name_index.iter() {
            for func in funcs.iter() {
                if let Some(ref qn) = func.qualified_name {
                    if qn == target || qn.ends_with(&format!(".{}", target)) {
                        // Avoid duplicates (already matched by name)
                        if func.name != target {
                            matches.push(*func);
                        }
                    }
                }
            }
        }
    } else {
        // Check if any function has qualified_name ending with ".{target}"
        // This is for cases like searching "method" when qualified_name is "Class.method"
        for funcs in name_index.values() {
            for func in funcs.iter() {
                if func.name != target {
                    if let Some(ref qn) = func.qualified_name {
                        if qn.ends_with(&format!(".{}", target)) {
                            matches.push(*func);
                        }
                    }
                }
            }
        }
    }

    matches
}

/// Find all function refs that match the target name (legacy O(V) implementation).
///
/// Prefer `find_matching_targets_indexed` when a name index is available.
/// Kept for API compatibility and as fallback when name index is not available.
#[allow(dead_code)]
fn find_matching_targets(graph: &CallGraph, target: &str) -> Vec<FunctionRef> {
    let all_funcs = graph.all_functions();

    all_funcs
        .iter()
        .filter(|f| {
            // Match by name
            if f.name == target {
                return true;
            }

            // Match by qualified name
            if let Some(ref qn) = f.qualified_name {
                if qn == target || qn.ends_with(&format!(".{}", target)) {
                    return true;
                }
            }

            false
        })
        .cloned()
        .collect()
}

/// Check if a function should be included based on config filters.
fn should_include(func: &FunctionRef, config: &ImpactConfig) -> bool {
    // Language filter
    if let Some(ref lang) = config.language {
        if !matches_language(&func.file, lang) {
            return false;
        }
    }

    // Test file exclusion
    if config.exclude_tests && is_test_file(&func.file) {
        return false;
    }

    // Include patterns (if any, file must match at least one)
    if !config.include_patterns.is_empty() {
        let matches_any = config
            .include_patterns
            .iter()
            .any(|p| glob_match(p, &func.file));
        if !matches_any {
            return false;
        }
    }

    // Exclude patterns
    for pattern in &config.exclude_patterns {
        if glob_match(pattern, &func.file) {
            return false;
        }
    }

    true
}

/// Check if a file path matches a language by extension.
fn matches_language(file: &str, lang: &str) -> bool {
    let extensions: &[&str] = match lang {
        "python" => &[".py", ".pyi"],
        "typescript" => &[".ts", ".tsx"],
        "javascript" => &[".js", ".jsx", ".mjs"],
        "rust" => &[".rs"],
        "go" => &[".go"],
        "java" => &[".java"],
        "c" => &[".c", ".h"],
        "cpp" => &[".cpp", ".cc", ".cxx", ".hpp", ".hxx", ".cu", ".cuh"],
        "csharp" => &[".cs"],
        "ruby" => &[".rb"],
        "php" => &[".php"],
        "swift" => &[".swift"],
        "kotlin" => &[".kt", ".kts"],
        "scala" => &[".scala", ".sc"],
        _ => return true, // Unknown language, don't filter
    };

    extensions.iter().any(|ext| file.ends_with(ext))
}

/// Check if a file is likely a test file.
///
/// Supports common test file conventions across languages:
/// - Python: `test_*.py`, `*_test.py`
/// - Java/Kotlin: `*Test.java`, `Test*.java`, `*Test.kt`, `Test*.kt`
/// - JavaScript/TypeScript: `*.test.js`, `*.spec.ts`, etc.
/// - Go: `*_test.go`
/// - Rust: `*_test.rs`, `tests.rs`
/// - Ruby: `*_spec.rb`
fn is_test_file(file: &str) -> bool {
    let path_lower = file.to_lowercase();

    // Common test directory patterns (check both embedded and prefix positions)
    if path_lower.contains("/test/")
        || path_lower.contains("/tests/")
        || path_lower.contains("/__tests__/")
        || path_lower.contains("/spec/")
        || path_lower.contains("/specs/")
        || path_lower.starts_with("test/")
        || path_lower.starts_with("tests/")
        || path_lower.starts_with("__tests__/")
        || path_lower.starts_with("spec/")
        || path_lower.starts_with("specs/")
    {
        return true;
    }

    // Extract filename (handle both Unix and Windows paths)
    let filename = file
        .rsplit(|c| c == '/' || c == '\\')
        .next()
        .unwrap_or(file);
    let filename_lower = filename.to_lowercase();

    // Python test patterns: test_*.py, *_test.py
    if filename_lower.starts_with("test_") && filename_lower.ends_with(".py") {
        return true;
    }
    if filename_lower.ends_with("_test.py") {
        return true;
    }

    // Java test patterns (case-sensitive for proper conventions)
    // JUnit convention: UserTest.java, ServiceTest.java
    if filename.ends_with("Test.java") {
        return true;
    }
    // TestNG convention: TestUser.java, TestService.java
    // Requires "Test" + uppercase letter to avoid matching "Testing...", "Testable...", etc.
    if filename.starts_with("Test")
        && filename.ends_with(".java")
        && filename.len() > 9
        && filename.chars().nth(4).map_or(false, |c| c.is_uppercase())
    {
        return true;
    }
    // Python-style in Java: test_user.java (lowercase check)
    if filename_lower.starts_with("test_") && filename_lower.ends_with(".java") {
        return true;
    }

    // Kotlin test patterns (mirrors Java conventions)
    if filename.ends_with("Test.kt") {
        return true;
    }
    // TestNG convention for Kotlin: TestUser.kt, TestService.kt
    if filename.starts_with("Test")
        && filename.ends_with(".kt")
        && filename.len() > 7
        && filename.chars().nth(4).map_or(false, |c| c.is_uppercase())
    {
        return true;
    }
    if filename_lower.starts_with("test_") && filename_lower.ends_with(".kt") {
        return true;
    }

    // JavaScript/TypeScript test patterns
    if filename_lower.ends_with(".test.js")
        || filename_lower.ends_with(".test.ts")
        || filename_lower.ends_with(".test.jsx")
        || filename_lower.ends_with(".test.tsx")
        || filename_lower.ends_with(".spec.js")
        || filename_lower.ends_with(".spec.ts")
        || filename_lower.ends_with(".spec.jsx")
        || filename_lower.ends_with(".spec.tsx")
    {
        return true;
    }

    // Go test pattern: *_test.go
    if filename_lower.ends_with("_test.go") {
        return true;
    }

    // Rust test patterns: *_test.rs, tests.rs
    if filename_lower.ends_with("_test.rs") || filename_lower == "tests.rs" {
        return true;
    }

    // Ruby test patterns: *_spec.rb, *_test.rb
    if filename_lower.ends_with("_spec.rb") || filename_lower.ends_with("_test.rb") {
        return true;
    }

    // C# test patterns: *Tests.cs, *Test.cs
    if filename.ends_with("Test.cs") || filename.ends_with("Tests.cs") {
        return true;
    }

    // Generic test_ prefix (catches remaining cases)
    if filename_lower.starts_with("test_") {
        return true;
    }

    false
}

/// Simple glob matching for file patterns.
///
/// Supports:
/// - `*` matches any sequence of characters except `/`
/// - `**` matches any sequence including `/`
/// - `?` matches any single character
fn glob_match(pattern: &str, path: &str) -> bool {
    // Normalize paths for consistent matching
    let pattern = pattern.replace('\\', "/");
    let path = path.replace('\\', "/");

    glob_match_recursive(&pattern, &path)
}

fn glob_match_recursive(pattern: &str, path: &str) -> bool {
    let mut pat_chars = pattern.chars().peekable();
    let mut path_chars = path.chars().peekable();

    while let Some(pc) = pat_chars.next() {
        match pc {
            '*' => {
                // Check for **
                if pat_chars.peek() == Some(&'*') {
                    pat_chars.next(); // consume second *

                    // Skip optional path separator after **
                    if pat_chars.peek() == Some(&'/') {
                        pat_chars.next();
                    }

                    let remaining_pattern: String = pat_chars.collect();

                    // ** matches everything
                    if remaining_pattern.is_empty() {
                        return true;
                    }

                    // Try matching remaining pattern at every position
                    let remaining_path: String = path_chars.collect();
                    for i in 0..=remaining_path.len() {
                        if glob_match_recursive(&remaining_pattern, &remaining_path[i..]) {
                            return true;
                        }
                    }
                    return false;
                } else {
                    // Single * - match until next /
                    let remaining_pattern: String = pat_chars.collect();

                    if remaining_pattern.is_empty() {
                        // * at end matches rest of current segment
                        return !path_chars.any(|c| c == '/');
                    }

                    // Try matching remaining pattern after consuming non-/ chars
                    let remaining_path: String = path_chars.collect();
                    for i in 0..=remaining_path.len() {
                        if i > 0 && remaining_path.chars().nth(i - 1) == Some('/') {
                            break; // * doesn't match across /
                        }
                        if glob_match_recursive(&remaining_pattern, &remaining_path[i..]) {
                            return true;
                        }
                    }
                    return false;
                }
            }
            '?' => {
                // Match any single character except /
                match path_chars.next() {
                    Some(c) if c != '/' => continue,
                    _ => return false,
                }
            }
            c => {
                // Literal character match
                match path_chars.next() {
                    Some(pc) if pc == c => continue,
                    _ => return false,
                }
            }
        }
    }

    // Pattern consumed - path should also be consumed
    path_chars.next().is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::types::CallEdge;

    fn create_test_graph() -> CallGraph {
        let mut graph = CallGraph::default();

        // Build a call chain: main -> process -> validate -> helper
        let edges = vec![
            CallEdge {
                caller: FunctionRef {
                    file: "src/main.py".to_string(),
                    name: "main".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/process.py".to_string(),
                    name: "process".to_string(),
                    qualified_name: None,
                },
                call_line: 10,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/process.py".to_string(),
                    name: "process".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/validate.py".to_string(),
                    name: "validate".to_string(),
                    qualified_name: None,
                },
                call_line: 25,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/validate.py".to_string(),
                    name: "validate".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/helper.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: None,
                },
                call_line: 15,
            },
            // Additional caller of helper from tests
            CallEdge {
                caller: FunctionRef {
                    file: "tests/test_helper.py".to_string(),
                    name: "test_helper".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/helper.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: None,
                },
                call_line: 8,
            },
        ];

        graph.edges = edges;
        graph.build_indexes();
        graph
    }

    #[test]
    fn test_basic_impact_analysis() {
        let graph = create_test_graph();
        let config = ImpactConfig::new().with_depth(10);
        let result = analyze_impact(&graph, "helper", config);

        assert_eq!(result.target, "helper");
        assert_eq!(result.total_affected, 4); // validate, process, main, test_helper
    }

    #[test]
    fn test_impact_with_depth_limit() {
        let graph = create_test_graph();
        // depth=1 means: explore distance 1 nodes, which discovers distance 2 callers
        // With the call chain: main -> process -> validate -> helper
        // - validate, test_helper are at distance 1 (direct callers)
        // - process is at distance 2 (found by exploring validate)
        let config = ImpactConfig::new().with_depth(1);
        let result = analyze_impact(&graph, "helper", config);

        // Distance 1 callers (validate, test_helper) + distance 2 (process)
        assert_eq!(result.total_affected, 3);
        assert!(result.callers.iter().all(|c| c.distance <= 2));

        // Verify we have both distance 1 and distance 2 callers
        let distance_1_count = result.callers.iter().filter(|c| c.distance == 1).count();
        let distance_2_count = result.callers.iter().filter(|c| c.distance == 2).count();
        assert_eq!(distance_1_count, 2); // validate, test_helper
        assert_eq!(distance_2_count, 1); // process
    }

    #[test]
    fn test_impact_depth_zero_no_traversal() {
        // BUG-014 FIX: Verify max_depth=0 means NO traversal (Python semantics)
        // Previously, max_depth=0 was incorrectly converted to usize::MAX (unlimited)
        let graph = create_test_graph();
        // depth=0 means: NO exploration - return only direct callers, don't explore them
        // With the call chain: main -> process -> validate -> helper
        // - validate, test_helper are at distance 1 (direct callers) - INCLUDED
        // - process, main should NOT be found because we don't explore distance 1 nodes
        let config = ImpactConfig::new().with_depth(0);
        let result = analyze_impact(&graph, "helper", config);

        // Should only have direct callers (distance 1), no further exploration
        assert_eq!(result.total_affected, 2); // validate and test_helper only
        assert!(
            result.callers.iter().all(|c| c.distance == 1),
            "All callers should be at distance 1 when max_depth=0"
        );

        // Verify we have the right direct callers
        let caller_names: Vec<&str> = result.callers.iter().map(|c| c.name.as_str()).collect();
        assert!(
            caller_names.contains(&"validate"),
            "validate should be a direct caller"
        );
        assert!(
            caller_names.contains(&"test_helper"),
            "test_helper should be a direct caller"
        );

        // Verify we do NOT have indirect callers (would be present if bug existed)
        assert!(
            !caller_names.contains(&"process"),
            "process should NOT be found with max_depth=0"
        );
        assert!(
            !caller_names.contains(&"main"),
            "main should NOT be found with max_depth=0"
        );
    }

    #[test]
    fn test_impact_exclude_tests() {
        let graph = create_test_graph();
        let config = ImpactConfig::new().with_depth(10).exclude_tests();
        let result = analyze_impact(&graph, "helper", config);

        // Should exclude test_helper
        assert_eq!(result.total_affected, 3);
        assert!(!result.callers.iter().any(|c| c.name == "test_helper"));
    }

    #[test]
    fn test_impact_language_filter() {
        let graph = create_test_graph();
        let config = ImpactConfig::new().with_depth(10).with_language("python");
        let result = analyze_impact(&graph, "helper", config);

        // All files are .py, so all should match
        assert_eq!(result.total_affected, 4);
    }

    #[test]
    fn test_impact_distance_tracking() {
        let graph = create_test_graph();
        let config = ImpactConfig::new().with_depth(10).exclude_tests();
        let result = analyze_impact(&graph, "helper", config);

        // Check distances
        let validate = result
            .callers
            .iter()
            .find(|c| c.name == "validate")
            .unwrap();
        assert_eq!(validate.distance, 1);

        let process = result.callers.iter().find(|c| c.name == "process").unwrap();
        assert_eq!(process.distance, 2);

        let main_fn = result.callers.iter().find(|c| c.name == "main").unwrap();
        assert_eq!(main_fn.distance, 3);
    }

    #[test]
    fn test_impact_nonexistent_target() {
        let graph = create_test_graph();
        let config = ImpactConfig::new();
        let result = analyze_impact(&graph, "nonexistent", config);

        assert_eq!(result.total_affected, 0);
        assert!(result.callers.is_empty());
    }

    #[test]
    fn test_glob_match() {
        // Basic matches
        assert!(glob_match("*.py", "test.py"));
        assert!(!glob_match("*.py", "test.rs"));

        // Double star
        assert!(glob_match("**/*.py", "src/lib/test.py"));
        assert!(glob_match("**/test/**", "foo/test/bar.py"));

        // Question mark
        assert!(glob_match("test?.py", "test1.py"));
        assert!(!glob_match("test?.py", "test12.py"));
    }

    #[test]
    fn test_is_test_file() {
        // Directory-based detection
        assert!(is_test_file("tests/test_main.py"));
        assert!(is_test_file("src/__tests__/component.test.ts"));
        assert!(is_test_file("test/helper_test.go"));
        assert!(is_test_file("src/spec/model_spec.rb"));
        assert!(is_test_file("specs/integration.rb"));

        // Python patterns
        assert!(is_test_file("test_main.py"));
        assert!(is_test_file("src/test_utils.py"));
        assert!(is_test_file("helper_test.py"));

        // Java patterns (BUG-008 fix: JUnit and TestNG conventions)
        assert!(is_test_file("UserTest.java")); // JUnit convention
        assert!(is_test_file("src/UserServiceTest.java"));
        assert!(is_test_file("TestUser.java")); // TestNG convention
        assert!(is_test_file("src/TestUserService.java"));
        assert!(is_test_file("test_user.java")); // Python-style
        assert!(is_test_file("Test.java")); // Matches JUnit pattern (*Test.java)
        assert!(!is_test_file("Contest.java")); // Contains "test" but not a test file

        // Kotlin patterns
        assert!(is_test_file("UserTest.kt"));
        assert!(is_test_file("TestUser.kt"));
        assert!(is_test_file("test_user.kt"));
        assert!(is_test_file("Test.kt")); // Matches JUnit pattern (*Test.kt)

        // JavaScript/TypeScript patterns
        assert!(is_test_file("component.test.js"));
        assert!(is_test_file("component.test.ts"));
        assert!(is_test_file("component.test.jsx"));
        assert!(is_test_file("component.test.tsx"));
        assert!(is_test_file("component.spec.js"));
        assert!(is_test_file("component.spec.ts"));

        // Go patterns
        assert!(is_test_file("main_test.go"));
        assert!(is_test_file("handler_test.go"));

        // Rust patterns
        assert!(is_test_file("parser_test.rs"));
        assert!(is_test_file("tests.rs"));

        // Ruby patterns
        assert!(is_test_file("model_spec.rb"));
        assert!(is_test_file("helper_test.rb"));

        // C# patterns
        assert!(is_test_file("UserTest.cs"));
        assert!(is_test_file("UserTests.cs"));

        // Non-test files
        assert!(!is_test_file("src/main.py"));
        assert!(!is_test_file("lib/process.rs"));
        assert!(!is_test_file("src/TestingFramework.java")); // Not a test, just has "Testing" in name
        assert!(!is_test_file("src/LatestNews.java")); // Contains "test" substring
    }

    #[test]
    fn test_llm_context_output() {
        let graph = create_test_graph();
        let config = ImpactConfig::new().with_depth(10).exclude_tests();
        let result = analyze_impact(&graph, "helper", config);

        let context = result.to_llm_context();

        assert!(context.contains("# Impact Analysis: helper"));
        assert!(context.contains("Distance 1"));
        assert!(context.contains("validate"));
        assert!(context.contains("Distance 2"));
        assert!(context.contains("process"));
    }

    /// Test that functions with the same name in different files are NOT conflated.
    /// This is BUG-010: Name-only matching was incorrectly treating callers of
    /// a.py:helper and b.py:helper as callers of the same function.
    #[test]
    fn test_same_name_different_files_not_conflated() {
        let mut graph = CallGraph::default();

        // Create two helper functions in different files
        // a.py:helper is called by caller_a
        // b.py:helper is called by caller_b
        let edges = vec![
            CallEdge {
                caller: FunctionRef {
                    file: "src/caller_a.py".to_string(),
                    name: "caller_a".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/a.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: None,
                },
                call_line: 10,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/caller_b.py".to_string(),
                    name: "caller_b".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/b.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: None,
                },
                call_line: 20,
            },
            // Also add transitive callers to test BFS doesn't conflate
            CallEdge {
                caller: FunctionRef {
                    file: "src/main_a.py".to_string(),
                    name: "main_a".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/caller_a.py".to_string(),
                    name: "caller_a".to_string(),
                    qualified_name: None,
                },
                call_line: 5,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/main_b.py".to_string(),
                    name: "main_b".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/caller_b.py".to_string(),
                    name: "caller_b".to_string(),
                    qualified_name: None,
                },
                call_line: 15,
            },
        ];

        graph.edges = edges;
        graph.build_indexes();

        // Analyze impact of a.py:helper - should only find caller_a and main_a
        let config = ImpactConfig::new().with_depth(10);

        // Search for the specific file's helper by using find_matching_targets behavior
        // When searching for "helper", both a.py:helper and b.py:helper match
        // BUT their callers should be tracked separately
        let result = analyze_impact(&graph, "helper", config);

        // With the fix: searching for "helper" matches BOTH a.py:helper and b.py:helper
        // So we get callers of both: caller_a, caller_b, main_a, main_b
        assert_eq!(result.total_affected, 4);

        // Verify caller_a is at distance 1 (direct caller of a.py:helper)
        let caller_a = result
            .callers
            .iter()
            .find(|c| c.name == "caller_a")
            .expect("caller_a should be found");
        assert_eq!(caller_a.distance, 1);
        assert_eq!(caller_a.file, "src/caller_a.py");

        // Verify caller_b is at distance 1 (direct caller of b.py:helper)
        let caller_b = result
            .callers
            .iter()
            .find(|c| c.name == "caller_b")
            .expect("caller_b should be found");
        assert_eq!(caller_b.distance, 1);
        assert_eq!(caller_b.file, "src/caller_b.py");

        // Verify main_a is at distance 2 (calls caller_a which calls a.py:helper)
        let main_a = result
            .callers
            .iter()
            .find(|c| c.name == "main_a")
            .expect("main_a should be found");
        assert_eq!(main_a.distance, 2);

        // Verify main_b is at distance 2 (calls caller_b which calls b.py:helper)
        let main_b = result
            .callers
            .iter()
            .find(|c| c.name == "main_b")
            .expect("main_b should be found");
        assert_eq!(main_b.distance, 2);

        // CRITICAL: main_a should NOT be reachable from b.py:helper's call chain
        // and main_b should NOT be reachable from a.py:helper's call chain
        // Before the fix, name-only matching would have made them appear at wrong distances
        // or created false transitive relationships.
    }

    /// Test that targeting a specific file's function only returns its callers.
    #[test]
    fn test_qualified_target_isolates_file() {
        let mut graph = CallGraph::default();

        // Same setup: two helper functions in different files
        let edges = vec![
            CallEdge {
                caller: FunctionRef {
                    file: "src/caller_a.py".to_string(),
                    name: "caller_a".to_string(),
                    qualified_name: Some("module_a.caller_a".to_string()),
                },
                callee: FunctionRef {
                    file: "src/a.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: Some("module_a.helper".to_string()),
                },
                call_line: 10,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/caller_b.py".to_string(),
                    name: "caller_b".to_string(),
                    qualified_name: Some("module_b.caller_b".to_string()),
                },
                callee: FunctionRef {
                    file: "src/b.py".to_string(),
                    name: "helper".to_string(),
                    qualified_name: Some("module_b.helper".to_string()),
                },
                call_line: 20,
            },
        ];

        graph.edges = edges;
        graph.build_indexes();

        // Search by qualified name - should only find caller_a
        let config = ImpactConfig::new().with_depth(10);
        let result = analyze_impact(&graph, "module_a.helper", config.clone());

        // Should only find caller_a, not caller_b
        assert_eq!(result.total_affected, 1);
        assert_eq!(result.callers[0].name, "caller_a");
        assert_eq!(result.callers[0].file, "src/caller_a.py");

        // Search for module_b.helper - should only find caller_b
        let result_b = analyze_impact(&graph, "module_b.helper", config);
        assert_eq!(result_b.total_affected, 1);
        assert_eq!(result_b.callers[0].name, "caller_b");
        assert_eq!(result_b.callers[0].file, "src/caller_b.py");
    }

    /// Create a diamond-shaped call graph for testing path deduplication.
    ///
    /// ```text
    ///     A
    ///    / \
    ///   B   C
    ///    \ /
    ///     D (target)
    /// ```
    fn create_diamond_graph() -> CallGraph {
        let mut graph = CallGraph::default();

        let edges = vec![
            // D is called by B and C (two paths to reach A)
            CallEdge {
                caller: FunctionRef {
                    file: "src/b.py".to_string(),
                    name: "B".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/d.py".to_string(),
                    name: "D".to_string(),
                    qualified_name: None,
                },
                call_line: 10,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/c.py".to_string(),
                    name: "C".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/d.py".to_string(),
                    name: "D".to_string(),
                    qualified_name: None,
                },
                call_line: 20,
            },
            // A calls both B and C
            CallEdge {
                caller: FunctionRef {
                    file: "src/a.py".to_string(),
                    name: "A".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/b.py".to_string(),
                    name: "B".to_string(),
                    qualified_name: None,
                },
                call_line: 5,
            },
            CallEdge {
                caller: FunctionRef {
                    file: "src/a.py".to_string(),
                    name: "A".to_string(),
                    qualified_name: None,
                },
                callee: FunctionRef {
                    file: "src/c.py".to_string(),
                    name: "C".to_string(),
                    qualified_name: None,
                },
                call_line: 6,
            },
        ];

        graph.edges = edges;
        graph.build_indexes();
        graph
    }

    /// Test BFS behavior (deduplicate_paths=true, default) on diamond graph.
    ///
    /// BFS with global visited: A appears once at distance 2 via the first explored path.
    #[test]
    fn test_diamond_graph_bfs_deduplication() {
        let graph = create_diamond_graph();
        let config = ImpactConfig::new().with_depth(10); // Default: deduplicate_paths = true

        let result = analyze_impact(&graph, "D", config);

        // B and C are direct callers (distance 1)
        // A is at distance 2 (caller of B and C)
        assert_eq!(result.total_affected, 3);

        // Verify B and C are at distance 1
        let b = result.callers.iter().find(|c| c.name == "B").unwrap();
        assert_eq!(b.distance, 1);

        let c = result.callers.iter().find(|c| c.name == "C").unwrap();
        assert_eq!(c.distance, 1);

        // Verify A is at distance 2 (via whichever path was explored first)
        let a = result.callers.iter().find(|c| c.name == "A").unwrap();
        assert_eq!(a.distance, 2);

        // With BFS deduplication, A appears exactly once
        let a_count = result.callers.iter().filter(|c| c.name == "A").count();
        assert_eq!(a_count, 1);
    }

    /// Test DFS behavior (deduplicate_paths=false) on diamond graph.
    ///
    /// DFS with per-path visited: All paths explored, A recorded with minimum distance.
    #[test]
    fn test_diamond_graph_dfs_all_paths() {
        let graph = create_diamond_graph();
        let config = ImpactConfig::new().with_depth(10).explore_all_paths(); // deduplicate_paths = false

        let result = analyze_impact(&graph, "D", config);

        // Same result count - A appears once in output (with aggregated info)
        assert_eq!(result.total_affected, 3);

        // Verify B and C are at distance 1
        let b = result.callers.iter().find(|c| c.name == "B").unwrap();
        assert_eq!(b.distance, 1);

        let c = result.callers.iter().find(|c| c.name == "C").unwrap();
        assert_eq!(c.distance, 1);

        // Verify A is at distance 2 (minimum across all paths)
        let a = result.callers.iter().find(|c| c.name == "A").unwrap();
        assert_eq!(a.distance, 2);

        // A still appears once in output (but both paths were explored internally)
        let a_count = result.callers.iter().filter(|c| c.name == "A").count();
        assert_eq!(a_count, 1);
    }

    /// Test that DFS mode aggregates call sites from all paths.
    #[test]
    fn test_diamond_graph_dfs_aggregates_call_sites() {
        let graph = create_diamond_graph();
        let config = ImpactConfig::new()
            .with_depth(10)
            .with_call_sites()
            .explore_all_paths();

        let result = analyze_impact(&graph, "D", config);

        // A calls B at line 5 and C at line 6
        // In DFS mode, A's call sites should include both paths' call info
        let a = result.callers.iter().find(|c| c.name == "A").unwrap();

        // A should have call site info from both paths (lines 5 and 6 where it calls B and C)
        // Note: The call sites recorded are where A calls B/C, not where B/C call D
        assert_eq!(
            a.call_sites.len(),
            2,
            "A should have 2 call sites (via B and C)"
        );
        assert!(
            a.call_sites.contains(&5),
            "Should include call site line 5 (A->B)"
        );
        assert!(
            a.call_sites.contains(&6),
            "Should include call site line 6 (A->C)"
        );
    }

    /// Test that BFS mode may miss some call sites in diamond patterns.
    #[test]
    fn test_diamond_graph_bfs_call_sites() {
        let graph = create_diamond_graph();
        let config = ImpactConfig::new().with_depth(10).with_call_sites(); // Default: deduplicate_paths = true

        let result = analyze_impact(&graph, "D", config);

        // With BFS, A is visited via the first path only
        // So it may only have one call site (depends on traversal order)
        let a = result.callers.iter().find(|c| c.name == "A").unwrap();

        // BFS records call site from the first path that discovers A
        assert!(
            a.call_sites.len() >= 1,
            "A should have at least 1 call site"
        );
    }

    /// Test that explore_all_paths builder method works correctly.
    #[test]
    fn test_explore_all_paths_builder() {
        let config = ImpactConfig::new().explore_all_paths();
        assert!(!config.deduplicate_paths);

        let config2 = ImpactConfig::new().with_deduplicate_paths(false);
        assert!(!config2.deduplicate_paths);

        let config3 = ImpactConfig::new().with_deduplicate_paths(true);
        assert!(config3.deduplicate_paths);
    }

    /// Test default config has deduplicate_paths=true for backward compatibility.
    #[test]
    fn test_default_config_backward_compatible() {
        let config = ImpactConfig::default();
        assert!(
            config.deduplicate_paths,
            "Default should use deduplication for backward compatibility"
        );

        let config2 = ImpactConfig::new();
        assert!(
            config2.deduplicate_paths,
            "ImpactConfig::new() should also use deduplication"
        );
    }
}
