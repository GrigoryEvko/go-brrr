//! Circular dependency detection for multi-level code analysis.
//!
//! This module provides comprehensive circular dependency detection using
//! Tarjan's algorithm for strongly connected components (SCCs). It detects
//! cycles at multiple granularity levels:
//!
//! - **Module/Package level**: Import cycles (A imports B imports A)
//! - **Class level**: Class usage cycles (A uses B uses A)
//! - **Function level**: Call cycles (A calls B calls A)
//!
//! # Algorithm
//!
//! Uses Tarjan's SCC algorithm with O(V + E) complexity:
//! 1. Build dependency graph from imports/usages/calls
//! 2. Run iterative DFS with lowlink tracking
//! 3. Identify SCCs with size > 1 (each is a cycle)
//! 4. Analyze cycle severity and suggest breaking strategies
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::circular::{detect_circular_dependencies, CircularConfig};
//!
//! let config = CircularConfig::default()
//!     .with_level(DependencyLevel::Module);
//!
//! let result = detect_circular_dependencies("./src", Some(config))?;
//!
//! for cycle in &result.cycles {
//!     println!("Cycle: {:?} (severity: {:?})", cycle.participants, cycle.severity);
//! }
//!
//! for suggestion in &result.suggestions {
//!     println!("Break {:?} -> {:?} using {}",
//!         suggestion.remove_edge.0, suggestion.remove_edge.1, suggestion.technique);
//! }
//! ```

use fixedbitset::FixedBitSet;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use thiserror::Error;

use crate::ast::extractor::AstExtractor;
use crate::ast::types::{ClassInfo, ImportInfo};
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::callgraph::{indexer, resolver};

// =============================================================================
// ERROR TYPES
// =============================================================================

/// Errors that can occur during circular dependency detection.
#[derive(Debug, Error)]
pub enum CircularError {
    /// Failed to scan project files.
    #[error("Failed to scan project: {0}")]
    ScanError(String),

    /// Failed to parse a source file.
    #[error("Failed to parse file {path}: {message}")]
    ParseError { path: String, message: String },

    /// IO error during file operations.
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// Invalid configuration.
    #[error("Invalid configuration: {0}")]
    ConfigError(String),
}

/// Result type for circular dependency operations.
pub type Result<T> = std::result::Result<T, CircularError>;

// =============================================================================
// CORE TYPES
// =============================================================================

/// Level of dependency analysis granularity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum DependencyLevel {
    /// Package-level dependencies (directory/namespace boundaries)
    Package,
    /// Module-level dependencies (file-to-file imports)
    #[default]
    Module,
    /// Class-level dependencies (class-to-class usage)
    Class,
    /// Function-level dependencies (function call cycles)
    Function,
}

impl std::fmt::Display for DependencyLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Package => write!(f, "package"),
            Self::Module => write!(f, "module"),
            Self::Class => write!(f, "class"),
            Self::Function => write!(f, "function"),
        }
    }
}

/// Severity of a circular dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// Low severity - might be intentional tight coupling
    Low,
    /// Medium severity - small cycles (2 nodes)
    Medium,
    /// High severity - larger cycles (3+ nodes)
    High,
    /// Critical severity - nested/overlapping cycles
    Critical,
}

impl std::fmt::Display for Severity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

impl Default for Severity {
    fn default() -> Self {
        Self::Low
    }
}

/// A single dependency cycle detected in the codebase.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyCycle {
    /// The level at which this cycle was detected.
    pub level: DependencyLevel,

    /// Participants in the cycle (module names, class names, or function names).
    pub participants: Vec<String>,

    /// The edges forming the cycle: [(A, B), (B, C), (C, A)].
    pub cycle_path: Vec<(String, String)>,

    /// Severity based on cycle size and characteristics.
    pub severity: Severity,

    /// Files involved in this cycle.
    pub files: Vec<String>,

    /// Whether this cycle involves test code.
    pub involves_tests: bool,

    /// Whether this appears to be intentional (e.g., tightly coupled modules).
    pub likely_intentional: bool,
}

impl DependencyCycle {
    /// Create a new dependency cycle.
    fn new(level: DependencyLevel, participants: Vec<String>) -> Self {
        let cycle_path = Self::build_cycle_path(&participants);
        let severity = Self::calculate_severity(&participants, false);

        Self {
            level,
            participants,
            cycle_path,
            severity,
            files: Vec::new(),
            involves_tests: false,
            likely_intentional: false,
        }
    }

    /// Build the cycle path from participants.
    fn build_cycle_path(participants: &[String]) -> Vec<(String, String)> {
        if participants.is_empty() {
            return Vec::new();
        }

        let mut path = Vec::with_capacity(participants.len());
        for i in 0..participants.len() {
            let from = &participants[i];
            let to = &participants[(i + 1) % participants.len()];
            path.push((from.clone(), to.clone()));
        }
        path
    }

    /// Calculate severity based on cycle characteristics.
    fn calculate_severity(participants: &[String], is_nested: bool) -> Severity {
        if is_nested {
            Severity::Critical
        } else {
            match participants.len() {
                0 | 1 => Severity::Low,
                2 => Severity::Medium,
                3..=5 => Severity::High,
                _ => Severity::Critical,
            }
        }
    }

    /// Mark this cycle as nested (part of overlapping cycles).
    pub fn mark_as_nested(&mut self) {
        self.severity = Severity::Critical;
    }

    /// Check if a participant is likely a test module/class/function.
    fn is_test_participant(name: &str) -> bool {
        let lower = name.to_lowercase();
        lower.starts_with("test_")
            || lower.ends_with("_test")
            || lower.ends_with("_tests")
            || lower.contains("/test/")
            || lower.contains("/tests/")
            || lower.contains("\\test\\")
            || lower.contains("\\tests\\")
            || lower.starts_with("test::")
    }

    /// Update test involvement flag.
    pub fn update_test_involvement(&mut self) {
        self.involves_tests = self
            .participants
            .iter()
            .any(|s| Self::is_test_participant(s))
            || self.files.iter().any(|s| Self::is_test_participant(s));
    }
}

/// Suggestion for breaking a circular dependency.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BreakingSuggestion {
    /// The edge to remove: (from, to).
    pub remove_edge: (String, String),

    /// Suggested refactoring technique.
    pub technique: String,

    /// Detailed description of the suggestion.
    pub description: String,

    /// Number of cycles this would break.
    pub impact: u32,

    /// Confidence score (0.0 - 1.0).
    pub confidence: f64,

    /// Estimated effort (low, medium, high).
    pub effort: String,
}

impl BreakingSuggestion {
    /// Create a new breaking suggestion.
    fn new(edge: (String, String), technique: &str, description: &str, impact: u32) -> Self {
        Self {
            remove_edge: edge,
            technique: technique.to_string(),
            description: description.to_string(),
            impact,
            confidence: 0.7,
            effort: "medium".to_string(),
        }
    }
}

/// Complete report of circular dependency analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircularDependencyReport {
    /// All detected cycles.
    pub cycles: Vec<DependencyCycle>,

    /// Total number of unique modules/classes/functions involved in cycles.
    pub total_participants_in_cycles: usize,

    /// Total number of unique files involved in cycles.
    pub total_files_in_cycles: usize,

    /// Breaking suggestions ordered by impact.
    pub suggestions: Vec<BreakingSuggestion>,

    /// Statistics about the analysis.
    pub stats: CircularStats,

    /// Analysis configuration used.
    pub config: CircularConfig,
}

/// Statistics from circular dependency analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CircularStats {
    /// Total nodes analyzed.
    pub total_nodes: usize,

    /// Total edges analyzed.
    pub total_edges: usize,

    /// Number of cycles found.
    pub cycle_count: usize,

    /// Number of critical cycles.
    pub critical_count: usize,

    /// Number of high severity cycles.
    pub high_count: usize,

    /// Number of medium severity cycles.
    pub medium_count: usize,

    /// Number of low severity cycles.
    pub low_count: usize,

    /// Number of cycles involving tests (informational).
    pub test_cycles: usize,

    /// Largest cycle size.
    pub max_cycle_size: usize,

    /// Average cycle size.
    pub avg_cycle_size: f64,

    /// Time taken for analysis (milliseconds).
    pub analysis_time_ms: u64,
}

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for circular dependency detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircularConfig {
    /// Dependency level to analyze.
    pub level: DependencyLevel,

    /// Minimum severity to report.
    pub min_severity: Severity,

    /// Include test dependencies in analysis.
    pub include_tests: bool,

    /// Exclude cycles that appear intentional (tightly coupled modules).
    pub exclude_intentional: bool,

    /// Language filter (None = all languages).
    pub language: Option<String>,

    /// Maximum number of cycles to report.
    pub max_cycles: usize,

    /// Maximum number of suggestions to generate.
    pub max_suggestions: usize,

    /// Maximum files to analyze.
    pub max_files: usize,
}

impl Default for CircularConfig {
    fn default() -> Self {
        Self {
            level: DependencyLevel::Module,
            min_severity: Severity::Low,
            include_tests: false,
            exclude_intentional: false,
            language: None,
            max_cycles: 100,
            max_suggestions: 20,
            max_files: 5000,
        }
    }
}

impl CircularConfig {
    /// Create config for module-level analysis.
    pub fn module_level() -> Self {
        Self {
            level: DependencyLevel::Module,
            ..Default::default()
        }
    }

    /// Create config for class-level analysis.
    pub fn class_level() -> Self {
        Self {
            level: DependencyLevel::Class,
            ..Default::default()
        }
    }

    /// Create config for function-level analysis.
    pub fn function_level() -> Self {
        Self {
            level: DependencyLevel::Function,
            ..Default::default()
        }
    }

    /// Create config for package-level analysis.
    pub fn package_level() -> Self {
        Self {
            level: DependencyLevel::Package,
            ..Default::default()
        }
    }

    /// Set the dependency level.
    pub fn with_level(mut self, level: DependencyLevel) -> Self {
        self.level = level;
        self
    }

    /// Set minimum severity filter.
    pub fn with_min_severity(mut self, severity: Severity) -> Self {
        self.min_severity = severity;
        self
    }

    /// Include test dependencies.
    pub fn with_tests(mut self) -> Self {
        self.include_tests = true;
        self
    }

    /// Set language filter.
    pub fn with_language(mut self, lang: &str) -> Self {
        self.language = Some(lang.to_string());
        self
    }
}

// =============================================================================
// TARJAN'S ALGORITHM FOR STRONGLY CONNECTED COMPONENTS
// =============================================================================

/// Tarjan's algorithm state for SCC detection.
struct TarjanState {
    /// Current DFS index counter.
    index: u32,
    /// Stack of nodes in current DFS path.
    stack: Vec<usize>,
    /// Set of nodes currently on stack (for O(1) lookup). Uses FixedBitSet for cache efficiency.
    on_stack: FixedBitSet,
    /// DFS index for each node.
    indices: FxHashMap<usize, u32>,
    /// Lowlink value for each node.
    lowlinks: FxHashMap<usize, u32>,
    /// Resulting SCCs.
    sccs: Vec<Vec<usize>>,
}

impl TarjanState {
    /// Create new Tarjan state with capacity for `node_count` nodes.
    fn new(node_count: usize) -> Self {
        Self {
            index: 0,
            stack: Vec::with_capacity(node_count),
            on_stack: FixedBitSet::with_capacity(node_count),
            indices: FxHashMap::default(),
            lowlinks: FxHashMap::default(),
            sccs: Vec::new(),
        }
    }
}

/// Dependency graph for SCC analysis.
struct DependencyGraph {
    /// Node names (index -> name).
    nodes: Vec<String>,
    /// Node name to index mapping.
    node_indices: FxHashMap<String, usize>,
    /// Adjacency list: node index -> set of neighbor indices.
    edges: FxHashMap<usize, FxHashSet<usize>>,
    /// File associations for each node.
    node_files: FxHashMap<usize, FxHashSet<String>>,
}

impl DependencyGraph {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            node_indices: FxHashMap::default(),
            edges: FxHashMap::default(),
            node_files: FxHashMap::default(),
        }
    }

    /// Add a node, returning its index.
    fn add_node(&mut self, name: &str) -> usize {
        if let Some(&idx) = self.node_indices.get(name) {
            return idx;
        }
        let idx = self.nodes.len();
        self.nodes.push(name.to_string());
        self.node_indices.insert(name.to_string(), idx);
        self.edges.insert(idx, FxHashSet::default());
        idx
    }

    /// Add an edge from source to target.
    fn add_edge(&mut self, from: usize, to: usize) {
        // Avoid self-loops (intentional recursion is OK at function level)
        if from != to {
            self.edges.entry(from).or_default().insert(to);
        }
    }

    /// Associate a file with a node.
    fn add_file(&mut self, node_idx: usize, file: &str) {
        self.node_files
            .entry(node_idx)
            .or_default()
            .insert(file.to_string());
    }

    /// Get node name by index.
    fn node_name(&self, idx: usize) -> &str {
        &self.nodes[idx]
    }

    /// Get files for a node.
    fn node_files_list(&self, idx: usize) -> Vec<String> {
        self.node_files
            .get(&idx)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Total number of nodes.
    fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Total number of edges.
    fn edge_count(&self) -> usize {
        self.edges.values().map(|e| e.len()).sum()
    }

    /// Find all strongly connected components using Tarjan's algorithm.
    ///
    /// This is an iterative implementation to avoid stack overflow on large graphs.
    fn find_sccs(&self) -> Vec<Vec<usize>> {
        let node_count = self.nodes.len();
        let mut state = TarjanState::new(node_count);

        // Process all nodes (handles disconnected components)
        for start in 0..node_count {
            if !state.indices.contains_key(&start) {
                self.tarjan_iterative(start, &mut state);
            }
        }

        state.sccs
    }

    /// Iterative Tarjan's algorithm for a single component.
    ///
    /// Uses explicit stack to avoid recursion depth issues.
    fn tarjan_iterative(&self, start: usize, state: &mut TarjanState) {
        // Work item: (node, phase, neighbor_iterator_position)
        // phase 0: initial visit
        // phase 1: processing neighbors
        // phase 2: post-processing (after all neighbors done)
        let mut work_stack: Vec<(usize, u8, usize)> = vec![(start, 0, 0)];

        while let Some((v, phase, neighbor_pos)) = work_stack.pop() {
            match phase {
                0 => {
                    // Initial visit - assign index and lowlink
                    state.indices.insert(v, state.index);
                    state.lowlinks.insert(v, state.index);
                    state.index += 1;
                    state.stack.push(v);
                    state.on_stack.insert(v);

                    // Move to neighbor processing phase
                    work_stack.push((v, 1, 0));
                }
                1 => {
                    // Processing neighbors
                    let neighbors: Vec<usize> = self
                        .edges
                        .get(&v)
                        .map(|e| e.iter().copied().collect())
                        .unwrap_or_default();

                    if neighbor_pos < neighbors.len() {
                        let w = neighbors[neighbor_pos];

                        // Continue with next neighbor after this one
                        work_stack.push((v, 1, neighbor_pos + 1));

                        if !state.indices.contains_key(&w) {
                            // Neighbor not yet visited - recurse
                            work_stack.push((w, 0, 0));
                        } else if state.on_stack.contains(w) {
                            // Neighbor on stack - update lowlink
                            let w_index = state.indices[&w];
                            let v_lowlink = state.lowlinks.get_mut(&v).unwrap();
                            *v_lowlink = (*v_lowlink).min(w_index);
                        }
                    } else {
                        // All neighbors processed - move to post-processing
                        work_stack.push((v, 2, 0));
                    }
                }
                2 => {
                    // Post-processing: update parent's lowlink and check for SCC root
                    // First, update lowlinks from children
                    let neighbors: Vec<usize> = self
                        .edges
                        .get(&v)
                        .map(|e| e.iter().copied().collect())
                        .unwrap_or_default();

                    for &w in &neighbors {
                        if let Some(&w_lowlink) = state.lowlinks.get(&w) {
                            let v_lowlink = state.lowlinks.get_mut(&v).unwrap();
                            *v_lowlink = (*v_lowlink).min(w_lowlink);
                        }
                    }

                    // Check if v is root of an SCC
                    let v_index = state.indices[&v];
                    let v_lowlink = state.lowlinks[&v];

                    if v_lowlink == v_index {
                        // v is root - pop SCC from stack
                        let mut scc = Vec::new();
                        loop {
                            let w = state.stack.pop().unwrap();
                            state.on_stack.set(w, false);
                            scc.push(w);
                            if w == v {
                                break;
                            }
                        }
                        state.sccs.push(scc);
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}

// =============================================================================
// DEPENDENCY GRAPH BUILDERS
// =============================================================================

/// Build module-level dependency graph from imports.
fn build_module_graph(project_path: &Path, config: &CircularConfig) -> Result<DependencyGraph> {
    let scanner = ProjectScanner::new(project_path.to_str().unwrap_or("."))
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    let scan_config = match &config.language {
        Some(lang) if lang != "all" => ScanConfig::for_language(lang),
        _ => ScanConfig::default(),
    };

    let scan_result = scanner
        .scan_with_config(&scan_config)
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    let mut graph = DependencyGraph::new();
    let project_root = project_path
        .canonicalize()
        .unwrap_or_else(|_| project_path.to_path_buf());

    for file_path in scan_result.files.iter().take(config.max_files) {
        // Skip test files if not including tests
        if !config.include_tests && is_test_file(file_path) {
            continue;
        }

        // Parse the file to extract imports
        let module_info = match AstExtractor::extract_file(file_path) {
            Ok(info) => info,
            Err(_) => continue, // Skip unparseable files
        };

        // Compute module name from file path
        let module_name = path_to_module_name(file_path, &project_root);
        let source_idx = graph.add_node(&module_name);
        graph.add_file(source_idx, &file_path.to_string_lossy());

        // Process imports
        for import in &module_info.imports {
            let target_module = resolve_import_to_module(import, file_path, &project_root);
            if let Some(target) = target_module {
                // Skip standard library and external imports
                if is_internal_module(&target, &project_root) {
                    let target_idx = graph.add_node(&target);
                    graph.add_edge(source_idx, target_idx);
                }
            }
        }
    }

    Ok(graph)
}

/// Build package-level dependency graph (aggregated by directory).
fn build_package_graph(project_path: &Path, config: &CircularConfig) -> Result<DependencyGraph> {
    // First build module graph
    let module_graph = build_module_graph(project_path, config)?;

    // Aggregate by package (directory)
    let mut package_graph = DependencyGraph::new();
    let mut module_to_package: FxHashMap<String, String> = FxHashMap::default();

    // Map modules to packages
    for node_name in &module_graph.nodes {
        let package = module_to_package_name(node_name);
        module_to_package.insert(node_name.clone(), package);
    }

    // Build package edges
    for (source_idx, targets) in &module_graph.edges {
        let source_module = module_graph.node_name(*source_idx);
        let source_package = module_to_package.get(source_module).unwrap();
        let source_pkg_idx = package_graph.add_node(source_package);

        // Copy file associations
        for file in module_graph.node_files_list(*source_idx) {
            package_graph.add_file(source_pkg_idx, &file);
        }

        for &target_idx in targets {
            let target_module = module_graph.node_name(target_idx);
            let target_package = module_to_package.get(target_module).unwrap();

            // Only add cross-package edges
            if source_package != target_package {
                let target_pkg_idx = package_graph.add_node(target_package);
                package_graph.add_edge(source_pkg_idx, target_pkg_idx);
            }
        }
    }

    Ok(package_graph)
}

/// Build class-level dependency graph.
fn build_class_graph(project_path: &Path, config: &CircularConfig) -> Result<DependencyGraph> {
    let scanner = ProjectScanner::new(project_path.to_str().unwrap_or("."))
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    let scan_config = match &config.language {
        Some(lang) if lang != "all" => ScanConfig::for_language(lang),
        _ => ScanConfig::default(),
    };

    let scan_result = scanner
        .scan_with_config(&scan_config)
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    let mut graph = DependencyGraph::new();
    let project_root = project_path
        .canonicalize()
        .unwrap_or_else(|_| project_path.to_path_buf());

    // First pass: collect all class definitions
    let mut class_to_file: FxHashMap<String, String> = FxHashMap::default();
    let mut file_classes: FxHashMap<String, Vec<ClassInfo>> = FxHashMap::default();

    for file_path in scan_result.files.iter().take(config.max_files) {
        if !config.include_tests && is_test_file(file_path) {
            continue;
        }

        let module_info = match AstExtractor::extract_file(file_path) {
            Ok(info) => info,
            Err(_) => continue,
        };

        let module_name = path_to_module_name(file_path, &project_root);
        let file_str = file_path.to_string_lossy().to_string();

        for class in &module_info.classes {
            let fqn = format!("{}.{}", module_name, class.name);
            class_to_file.insert(fqn.clone(), file_str.clone());
            class_to_file.insert(class.name.clone(), file_str.clone());
        }

        file_classes.insert(file_str, module_info.classes);
    }

    // Second pass: build dependency edges from class usage
    for (file_path, classes) in &file_classes {
        for class in classes {
            let file_p = Path::new(file_path);
            let module_name = path_to_module_name(file_p, &project_root);
            let source_fqn = format!("{}.{}", module_name, class.name);
            let source_idx = graph.add_node(&source_fqn);
            graph.add_file(source_idx, file_path);

            // Check base classes (inheritance)
            for base in &class.bases {
                if let Some(target_file) = class_to_file.get(base) {
                    let target_path = Path::new(target_file);
                    let target_module = path_to_module_name(target_path, &project_root);
                    let target_fqn = format!("{}.{}", target_module, base);
                    let target_idx = graph.add_node(&target_fqn);
                    graph.add_file(target_idx, target_file);
                    graph.add_edge(source_idx, target_idx);
                }
            }

            // Check method return types for class references
            for method in &class.methods {
                if let Some(ref return_type) = method.return_type {
                    // Extract simple class name from return type
                    let type_name = extract_class_name(return_type);
                    if let Some(target_file) = class_to_file.get(&type_name) {
                        let target_path = Path::new(target_file);
                        let target_module = path_to_module_name(target_path, &project_root);
                        let target_fqn = format!("{}.{}", target_module, type_name);
                        let target_idx = graph.add_node(&target_fqn);
                        graph.add_file(target_idx, target_file);
                        graph.add_edge(source_idx, target_idx);
                    }
                }
            }
        }
    }

    Ok(graph)
}

/// Extract simple class name from a type annotation (handles generics, Optional, etc.)
fn extract_class_name(type_str: &str) -> String {
    // Remove common wrappers like Optional[X], List[X], etc.
    let trimmed = type_str.trim();
    if let Some(inner_start) = trimmed.find('[') {
        if let Some(inner_end) = trimmed.rfind(']') {
            return trimmed[inner_start + 1..inner_end].to_string();
        }
    }
    trimmed.to_string()
}

/// Build function-level dependency graph from call graph.
fn build_function_graph(project_path: &Path, config: &CircularConfig) -> Result<DependencyGraph> {
    let scanner = ProjectScanner::new(project_path.to_str().unwrap_or("."))
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    let scan_config = match &config.language {
        Some(lang) if lang != "all" => ScanConfig::for_language(lang),
        _ => ScanConfig::default(),
    };

    let scan_result = scanner
        .scan_with_config(&scan_config)
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    // Filter files and collect PathBufs
    let files: Vec<PathBuf> = scan_result
        .files
        .into_iter()
        .take(config.max_files)
        .filter(|f| config.include_tests || !is_test_file(f))
        .collect();

    // Build function index
    let index = indexer::FunctionIndex::build(&files)
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    // Resolve calls
    let call_graph = resolver::resolve_calls(&files, &index, project_path)
        .map_err(|e| CircularError::ScanError(e.to_string()))?;

    // Convert to dependency graph
    let mut graph = DependencyGraph::new();

    for edge in &call_graph.edges {
        let caller_name = edge
            .caller
            .qualified_name
            .as_deref()
            .unwrap_or(&edge.caller.name);
        let callee_name = edge
            .callee
            .qualified_name
            .as_deref()
            .unwrap_or(&edge.callee.name);

        let caller_idx = graph.add_node(caller_name);
        let callee_idx = graph.add_node(callee_name);

        if !edge.caller.file.is_empty() {
            graph.add_file(caller_idx, &edge.caller.file);
        }
        if !edge.callee.file.is_empty() {
            graph.add_file(callee_idx, &edge.callee.file);
        }

        graph.add_edge(caller_idx, callee_idx);
    }

    Ok(graph)
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Check if a file is a test file.
fn is_test_file(path: &Path) -> bool {
    let path_str = path.to_string_lossy().to_lowercase();
    path_str.contains("/test/")
        || path_str.contains("/tests/")
        || path_str.contains("\\test\\")
        || path_str.contains("\\tests\\")
        || path_str.contains("_test.")
        || path_str.contains("_tests.")
        || path_str.contains("test_")
        || path_str.ends_with("_test.py")
        || path_str.ends_with("_test.rs")
        || path_str.ends_with("_test.go")
        || path_str.ends_with(".test.ts")
        || path_str.ends_with(".test.js")
        || path_str.ends_with(".spec.ts")
        || path_str.ends_with(".spec.js")
}

/// Convert file path to module name.
fn path_to_module_name(path: &Path, project_root: &Path) -> String {
    let relative = path.strip_prefix(project_root).unwrap_or(path);

    let module_path = relative
        .with_extension("")
        .to_string_lossy()
        .replace(['/', '\\'], ".");

    // Remove leading dots
    module_path.trim_start_matches('.').to_string()
}

/// Extract package name from module name.
fn module_to_package_name(module: &str) -> String {
    match module.rsplit_once('.') {
        Some((package, _)) => package.to_string(),
        None => module.to_string(), // Top-level module is its own package
    }
}

/// Resolve an import to a module name.
fn resolve_import_to_module(
    import: &ImportInfo,
    source_file: &Path,
    project_root: &Path,
) -> Option<String> {
    if import.level > 0 {
        // Relative import - resolve from source file
        let source_module = path_to_module_name(source_file, project_root);
        let parts: Vec<&str> = source_module.split('.').collect();

        if import.level > parts.len() {
            return None; // Invalid relative import
        }

        let base_parts = &parts[..parts.len().saturating_sub(import.level)];
        let base = base_parts.join(".");

        if import.module.is_empty() {
            // from . import foo or from .. import foo
            if !import.names.is_empty() {
                Some(format!("{}.{}", base, import.names[0]))
            } else {
                Some(base)
            }
        } else {
            Some(format!("{}.{}", base, import.module))
        }
    } else {
        // Absolute import
        Some(import.module.clone())
    }
}

/// Check if a module is internal to the project.
fn is_internal_module(module: &str, _project_root: &Path) -> bool {
    // Common standard library and third-party prefixes to exclude
    const EXTERNAL_PREFIXES: &[&str] = &[
        "std",
        "core",
        "alloc", // Rust
        "os",
        "sys",
        "io",
        "re",
        "json",
        "time",
        "datetime",
        "collections",
        "typing", // Python
        "fmt",
        "net",
        "http",
        "context",
        "sync",
        "encoding", // Go
        "java.",
        "javax.",
        "sun.",
        "com.google",
        "org.apache", // Java
        "react",
        "vue",
        "angular",
        "express",
        "lodash",
        "axios", // JS/TS
    ];

    let lower = module.to_lowercase();

    // Check against known external prefixes
    for prefix in EXTERNAL_PREFIXES {
        if lower.starts_with(prefix) || lower == *prefix {
            return false;
        }
    }

    // Heuristic: if module has no dots, it might be a stdlib module
    // but we'll include it for safety
    true
}

// =============================================================================
// CYCLE ANALYSIS AND SUGGESTIONS
// =============================================================================

/// Convert SCCs to dependency cycles.
fn sccs_to_cycles(
    sccs: Vec<Vec<usize>>,
    graph: &DependencyGraph,
    level: DependencyLevel,
) -> Vec<DependencyCycle> {
    let mut cycles = Vec::new();

    for scc in sccs {
        // Only SCCs with more than one node represent cycles
        if scc.len() > 1 {
            let participants: Vec<String> = scc
                .iter()
                .map(|&idx| graph.node_name(idx).to_string())
                .collect();

            let mut cycle = DependencyCycle::new(level, participants);

            // Collect files
            let mut all_files = FxHashSet::default();
            for &idx in &scc {
                for file in graph.node_files_list(idx) {
                    all_files.insert(file);
                }
            }
            cycle.files = all_files.into_iter().collect();
            cycle.update_test_involvement();

            // Check if likely intentional (same package/directory)
            if level == DependencyLevel::Module || level == DependencyLevel::Class {
                let packages: FxHashSet<String> = cycle
                    .participants
                    .iter()
                    .map(|p| module_to_package_name(p))
                    .collect();
                cycle.likely_intentional = packages.len() == 1;
            }

            cycles.push(cycle);
        }
    }

    // Sort by severity (descending) then by size (descending)
    cycles.sort_by(|a, b| {
        b.severity
            .cmp(&a.severity)
            .then_with(|| b.participants.len().cmp(&a.participants.len()))
    });

    cycles
}

/// Detect nested/overlapping cycles and mark them as critical.
fn detect_nested_cycles(cycles: &mut [DependencyCycle]) {
    // Build participant sets for each cycle
    let participant_sets: Vec<FxHashSet<String>> = cycles
        .iter()
        .map(|c| c.participants.iter().cloned().collect())
        .collect();

    // Collect indices of cycles that need to be marked as nested
    let mut nested_indices = FixedBitSet::with_capacity(cycles.len());

    // Check for overlaps
    for i in 0..participant_sets.len() {
        for j in (i + 1)..participant_sets.len() {
            let has_overlap = participant_sets[i]
                .intersection(&participant_sets[j])
                .next()
                .is_some();

            // If cycles share participants, they're nested/overlapping
            if has_overlap {
                nested_indices.insert(i);
                nested_indices.insert(j);
            }
        }
    }

    // Mark nested cycles
    for idx in nested_indices.ones() {
        cycles[idx].mark_as_nested();
    }
}

/// Generate suggestions for breaking cycles.
fn generate_suggestions(
    cycles: &[DependencyCycle],
    _graph: &DependencyGraph,
    max_suggestions: usize,
) -> Vec<BreakingSuggestion> {
    let mut edge_impact: FxHashMap<(String, String), u32> = FxHashMap::default();

    // Count how many cycles each edge participates in
    for cycle in cycles {
        for (from, to) in &cycle.cycle_path {
            *edge_impact.entry((from.clone(), to.clone())).or_insert(0) += 1;
        }
    }

    // Sort edges by impact (most impactful first)
    let mut edges: Vec<_> = edge_impact.into_iter().collect();
    edges.sort_by(|a, b| b.1.cmp(&a.1));

    // Generate suggestions for top edges
    let mut suggestions = Vec::new();

    for ((from, to), impact) in edges.into_iter().take(max_suggestions) {
        let technique = determine_breaking_technique(&from, &to);
        let description = generate_suggestion_description(&from, &to, &technique);

        let mut suggestion = BreakingSuggestion::new((from, to), &technique, &description, impact);

        // Estimate effort based on technique
        suggestion.effort = match technique.as_str() {
            "Extract interface" => "medium",
            "Move to common module" => "high",
            "Dependency injection" => "medium",
            "Lazy import" => "low",
            "Event-based decoupling" => "high",
            _ => "medium",
        }
        .to_string();

        suggestions.push(suggestion);
    }

    suggestions
}

/// Determine the best technique for breaking a dependency.
fn determine_breaking_technique(from: &str, to: &str) -> String {
    // Simple heuristics based on names
    let from_lower = from.to_lowercase();
    let to_lower = to.to_lowercase();

    if from_lower.contains("service") || to_lower.contains("service") {
        "Dependency injection".to_string()
    } else if from_lower.contains("handler") || to_lower.contains("handler") {
        "Event-based decoupling".to_string()
    } else if from_lower.contains("model") || to_lower.contains("model") {
        "Move to common module".to_string()
    } else if from_lower.contains("utils") || to_lower.contains("utils") {
        "Move to common module".to_string()
    } else {
        "Extract interface".to_string()
    }
}

/// Generate a description for a breaking suggestion.
fn generate_suggestion_description(from: &str, to: &str, technique: &str) -> String {
    match technique {
        "Extract interface" => {
            format!(
                "Create an interface/protocol for '{}' that '{}' can depend on instead of the concrete implementation",
                to, from
            )
        }
        "Move to common module" => {
            format!(
                "Extract shared types/functions used by both '{}' and '{}' into a separate module",
                from, to
            )
        }
        "Dependency injection" => {
            format!(
                "Pass '{}' as a parameter to '{}' instead of importing it directly",
                to, from
            )
        }
        "Lazy import" => {
            format!(
                "Use lazy/deferred import of '{}' in '{}' to break initialization-time cycle",
                to, from
            )
        }
        "Event-based decoupling" => {
            format!(
                "Replace direct calls from '{}' to '{}' with event emission and subscription",
                from, to
            )
        }
        _ => format!("Refactor dependency from '{}' to '{}'", from, to),
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect circular dependencies in a project.
///
/// # Arguments
///
/// * `path` - Path to the project root directory.
/// * `config` - Optional configuration (uses defaults if None).
///
/// # Returns
///
/// A `CircularDependencyReport` containing all detected cycles and suggestions.
///
/// # Example
///
/// ```ignore
/// let report = detect_circular_dependencies("./src", None)?;
/// println!("Found {} cycles", report.cycles.len());
/// ```
pub fn detect_circular_dependencies(
    path: &str,
    config: Option<CircularConfig>,
) -> Result<CircularDependencyReport> {
    let start_time = std::time::Instant::now();
    let config = config.unwrap_or_default();
    let project_path = Path::new(path);

    // Build appropriate dependency graph based on level
    let graph = match config.level {
        DependencyLevel::Package => build_package_graph(project_path, &config)?,
        DependencyLevel::Module => build_module_graph(project_path, &config)?,
        DependencyLevel::Class => build_class_graph(project_path, &config)?,
        DependencyLevel::Function => build_function_graph(project_path, &config)?,
    };

    // Find SCCs using Tarjan's algorithm
    let sccs = graph.find_sccs();

    // Convert SCCs to cycles
    let mut cycles = sccs_to_cycles(sccs, &graph, config.level);

    // Detect nested cycles
    detect_nested_cycles(&mut cycles);

    // Filter by configuration
    if !config.include_tests {
        cycles.retain(|c| !c.involves_tests);
    }
    if config.exclude_intentional {
        cycles.retain(|c| !c.likely_intentional);
    }
    cycles.retain(|c| c.severity >= config.min_severity);

    // Limit results
    cycles.truncate(config.max_cycles);

    // Generate suggestions
    let suggestions = generate_suggestions(&cycles, &graph, config.max_suggestions);

    // Compute statistics (collect owned values to avoid borrow issues)
    let mut participants_set: FxHashSet<String> = FxHashSet::default();
    let mut files_set: FxHashSet<String> = FxHashSet::default();

    for cycle in &cycles {
        for p in &cycle.participants {
            participants_set.insert(p.clone());
        }
        for f in &cycle.files {
            files_set.insert(f.clone());
        }
    }

    let total_participants = participants_set.len();
    let total_files = files_set.len();

    let cycle_sizes: Vec<usize> = cycles.iter().map(|c| c.participants.len()).collect();
    let max_cycle_size = cycle_sizes.iter().copied().max().unwrap_or(0);
    let avg_cycle_size = if cycle_sizes.is_empty() {
        0.0
    } else {
        cycle_sizes.iter().sum::<usize>() as f64 / cycle_sizes.len() as f64
    };

    let stats = CircularStats {
        total_nodes: graph.node_count(),
        total_edges: graph.edge_count(),
        cycle_count: cycles.len(),
        critical_count: cycles
            .iter()
            .filter(|c| c.severity == Severity::Critical)
            .count(),
        high_count: cycles
            .iter()
            .filter(|c| c.severity == Severity::High)
            .count(),
        medium_count: cycles
            .iter()
            .filter(|c| c.severity == Severity::Medium)
            .count(),
        low_count: cycles
            .iter()
            .filter(|c| c.severity == Severity::Low)
            .count(),
        test_cycles: cycles.iter().filter(|c| c.involves_tests).count(),
        max_cycle_size,
        avg_cycle_size,
        analysis_time_ms: start_time.elapsed().as_millis() as u64,
    };

    Ok(CircularDependencyReport {
        cycles,
        total_participants_in_cycles: total_participants,
        total_files_in_cycles: total_files,
        suggestions,
        stats,
        config,
    })
}

/// Format a circular dependency report as human-readable text.
pub fn format_circular_report(report: &CircularDependencyReport) -> String {
    let mut output = String::new();

    // Header
    output.push_str(&format!(
        "Circular Dependency Analysis ({} level)\n",
        report.config.level
    ));
    output.push_str(&format!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"));

    // Summary
    output.push_str("Summary:\n");
    output.push_str(&format!("  Total cycles: {}\n", report.stats.cycle_count));
    output.push_str(&format!("  Critical: {}\n", report.stats.critical_count));
    output.push_str(&format!("  High: {}\n", report.stats.high_count));
    output.push_str(&format!("  Medium: {}\n", report.stats.medium_count));
    output.push_str(&format!("  Low: {}\n", report.stats.low_count));
    output.push_str(&format!(
        "  Participants in cycles: {}\n",
        report.total_participants_in_cycles
    ));
    output.push_str(&format!(
        "  Files involved: {}\n",
        report.total_files_in_cycles
    ));
    output.push_str(&format!(
        "  Analysis time: {}ms\n\n",
        report.stats.analysis_time_ms
    ));

    // Cycles
    if !report.cycles.is_empty() {
        output.push_str("Detected Cycles:\n");
        output.push_str("────────────────\n");

        for (i, cycle) in report.cycles.iter().enumerate() {
            let severity_marker = match cycle.severity {
                Severity::Critical => "[CRITICAL]",
                Severity::High => "[HIGH]",
                Severity::Medium => "[MEDIUM]",
                Severity::Low => "[LOW]",
            };

            output.push_str(&format!(
                "\n{}. {} {} (size: {})\n",
                i + 1,
                severity_marker,
                if cycle.likely_intentional {
                    "(likely intentional)"
                } else {
                    ""
                },
                cycle.participants.len()
            ));

            // Show cycle path
            output.push_str("   Path: ");
            for (j, (from, to)) in cycle.cycle_path.iter().enumerate() {
                if j == 0 {
                    output.push_str(&format!("{} -> {}", from, to));
                } else {
                    output.push_str(&format!(" -> {}", to));
                }
            }
            output.push('\n');

            // Show files if few enough
            if cycle.files.len() <= 5 {
                output.push_str("   Files: ");
                output.push_str(&cycle.files.join(", "));
                output.push('\n');
            } else {
                output.push_str(&format!("   Files: {} files involved\n", cycle.files.len()));
            }
        }
    } else {
        output.push_str("No circular dependencies detected.\n");
    }

    // Suggestions
    if !report.suggestions.is_empty() {
        output.push_str("\nBreaking Suggestions:\n");
        output.push_str("────────────────────\n");

        for (i, suggestion) in report.suggestions.iter().enumerate() {
            output.push_str(&format!(
                "\n{}. {} (breaks {} cycle{})\n",
                i + 1,
                suggestion.technique,
                suggestion.impact,
                if suggestion.impact == 1 { "" } else { "s" }
            ));
            output.push_str(&format!(
                "   Remove: {} -> {}\n",
                suggestion.remove_edge.0, suggestion.remove_edge.1
            ));
            output.push_str(&format!("   {}\n", suggestion.description));
            output.push_str(&format!("   Effort: {}\n", suggestion.effort));
        }
    }

    output
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tarjan_simple_cycle() {
        let mut graph = DependencyGraph::new();
        let a = graph.add_node("A");
        let b = graph.add_node("B");
        let c = graph.add_node("C");

        // A -> B -> C -> A
        graph.add_edge(a, b);
        graph.add_edge(b, c);
        graph.add_edge(c, a);

        let sccs = graph.find_sccs();

        // Should find one SCC containing all three nodes
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 3);
    }

    #[test]
    fn test_tarjan_no_cycle() {
        let mut graph = DependencyGraph::new();
        let a = graph.add_node("A");
        let b = graph.add_node("B");
        let c = graph.add_node("C");

        // A -> B -> C (linear, no cycle)
        graph.add_edge(a, b);
        graph.add_edge(b, c);

        let sccs = graph.find_sccs();

        // Should find three SCCs, each with one node
        assert_eq!(sccs.len(), 3);
        assert!(sccs.iter().all(|scc| scc.len() == 1));
    }

    #[test]
    fn test_tarjan_multiple_cycles() {
        let mut graph = DependencyGraph::new();
        let a = graph.add_node("A");
        let b = graph.add_node("B");
        let c = graph.add_node("C");
        let d = graph.add_node("D");

        // Cycle 1: A -> B -> A
        graph.add_edge(a, b);
        graph.add_edge(b, a);

        // Cycle 2: C -> D -> C
        graph.add_edge(c, d);
        graph.add_edge(d, c);

        let sccs = graph.find_sccs();

        // Should find two SCCs with 2 nodes each
        let large_sccs: Vec<_> = sccs.iter().filter(|scc| scc.len() > 1).collect();
        assert_eq!(large_sccs.len(), 2);
    }

    #[test]
    fn test_tarjan_self_loop_ignored() {
        let mut graph = DependencyGraph::new();
        let a = graph.add_node("A");

        // Self-loop is ignored
        graph.add_edge(a, a);

        let sccs = graph.find_sccs();

        // Should find one SCC with one node (self-loop doesn't make SCC > 1)
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 1);
    }

    #[test]
    fn test_cycle_severity() {
        // 2 nodes = Medium
        let cycle2 = DependencyCycle::new(
            DependencyLevel::Module,
            vec!["A".to_string(), "B".to_string()],
        );
        assert_eq!(cycle2.severity, Severity::Medium);

        // 3 nodes = High
        let cycle3 = DependencyCycle::new(
            DependencyLevel::Module,
            vec!["A".to_string(), "B".to_string(), "C".to_string()],
        );
        assert_eq!(cycle3.severity, Severity::High);

        // 6+ nodes = Critical
        let cycle6 = DependencyCycle::new(
            DependencyLevel::Module,
            vec![
                "A".to_string(),
                "B".to_string(),
                "C".to_string(),
                "D".to_string(),
                "E".to_string(),
                "F".to_string(),
            ],
        );
        assert_eq!(cycle6.severity, Severity::Critical);
    }

    #[test]
    fn test_path_to_module_name() {
        let root = Path::new("/project");
        let file = Path::new("/project/src/utils/helpers.py");

        let module = path_to_module_name(file, root);
        assert_eq!(module, "src.utils.helpers");
    }

    #[test]
    fn test_module_to_package_name() {
        assert_eq!(module_to_package_name("src.utils.helpers"), "src.utils");
        assert_eq!(module_to_package_name("main"), "main");
    }

    #[test]
    fn test_is_test_file() {
        assert!(is_test_file(Path::new("/project/tests/test_utils.py")));
        assert!(is_test_file(Path::new("/project/src/utils_test.py")));
        assert!(is_test_file(Path::new("/project/src/utils.test.ts")));
        assert!(is_test_file(Path::new("/project/src/utils.spec.js")));
        assert!(!is_test_file(Path::new("/project/src/utils.py")));
    }

    #[test]
    fn test_config_builder() {
        let config = CircularConfig::default()
            .with_level(DependencyLevel::Class)
            .with_min_severity(Severity::High)
            .with_tests()
            .with_language("python");

        assert_eq!(config.level, DependencyLevel::Class);
        assert_eq!(config.min_severity, Severity::High);
        assert!(config.include_tests);
        assert_eq!(config.language, Some("python".to_string()));
    }

    #[test]
    fn test_cycle_path_building() {
        let participants = vec!["A".to_string(), "B".to_string(), "C".to_string()];
        let path = DependencyCycle::build_cycle_path(&participants);

        assert_eq!(path.len(), 3);
        assert_eq!(path[0], ("A".to_string(), "B".to_string()));
        assert_eq!(path[1], ("B".to_string(), "C".to_string()));
        assert_eq!(path[2], ("C".to_string(), "A".to_string()));
    }

    #[test]
    fn test_breaking_technique_selection() {
        assert_eq!(
            determine_breaking_technique("UserService", "UserRepository"),
            "Dependency injection"
        );
        assert_eq!(
            determine_breaking_technique("EventHandler", "Logger"),
            "Event-based decoupling"
        );
        assert_eq!(
            determine_breaking_technique("UserModel", "BaseModel"),
            "Move to common module"
        );
    }
}
