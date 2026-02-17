//! Coupling metrics calculation for software architecture analysis.
//!
//! This module calculates afferent and efferent coupling metrics to measure
//! the dependencies between modules/files in a codebase. These metrics help
//! identify architectural issues and guide refactoring decisions.
//!
//! # Metrics
//!
//! - **Ca (Afferent Coupling)**: Number of modules that depend ON this module
//! - **Ce (Efferent Coupling)**: Number of modules this module depends ON
//! - **Instability (I)**: Ce / (Ca + Ce) - ranges from 0 (stable) to 1 (unstable)
//! - **Abstractness (A)**: abstract_types / total_types - ratio of abstract types
//! - **Distance (D)**: |A + I - 1| - distance from the main sequence
//!
//! # Main Sequence Analysis
//!
//! The "main sequence" is the line A + I = 1 on a plot of Abstractness vs Instability.
//! Modules near this line have a good balance between stability and abstractness:
//!
//! - **Zone of Pain** (A=0, I=0): Concrete and stable - hard to change, rigid
//! - **Zone of Uselessness** (A=1, I=1): Abstract and unstable - maximally flexible but unused
//!
//! Modules far from the main sequence may indicate architectural problems.
//!
//! # Dependency Types
//!
//! The analysis tracks four types of dependencies:
//!
//! - **Import**: Direct import statements (e.g., `import foo`, `use crate::bar`)
//! - **Call**: Function calls across module boundaries
//! - **Type**: Using types defined in another module (parameters, return types)
//! - **Inheritance**: Class inheritance relationships
//!
//! # Example
//!
//! ```ignore
//! use brrr::metrics::coupling::{analyze_coupling, CouplingLevel};
//!
//! let result = analyze_coupling("./src", Some("python"), CouplingLevel::File)?;
//! for module in &result.modules {
//!     println!("{}: Ca={}, Ce={}, I={:.2}, D={:.2}",
//!         module.module, module.afferent, module.efferent,
//!         module.instability, module.distance);
//!     if module.distance > 0.5 {
//!         println!("  WARNING: Far from main sequence!");
//!     }
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tracing::debug;

use crate::ast::extractor::AstExtractor;
use crate::ast::types::{ClassInfo, ImportInfo};
use crate::callgraph;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::callgraph::types::CallGraph;
use crate::lang::LanguageRegistry;

// =============================================================================
// ERROR TYPE
// =============================================================================

/// Errors that can occur during coupling analysis.
#[derive(Error, Debug)]
pub enum CouplingError {
    /// Failed to scan project files
    #[error("Project scan failed: {0}")]
    ScanError(String),

    /// Failed to parse source file
    #[error("Parse error in {file}: {message}")]
    ParseError { file: String, message: String },

    /// Failed to build call graph
    #[error("Call graph construction failed: {0}")]
    CallGraphError(String),

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

// =============================================================================
// TYPES
// =============================================================================

/// Level of granularity for coupling analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum CouplingLevel {
    /// Analyze dependencies between individual files
    #[default]
    File,
    /// Analyze dependencies between directories/packages
    Module,
    /// Analyze dependencies between classes
    Class,
}

impl std::fmt::Display for CouplingLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File => write!(f, "file"),
            Self::Module => write!(f, "module"),
            Self::Class => write!(f, "class"),
        }
    }
}

impl std::str::FromStr for CouplingLevel {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "file" => Ok(Self::File),
            "module" | "package" | "directory" => Ok(Self::Module),
            "class" => Ok(Self::Class),
            _ => Err(format!(
                "Unknown coupling level: '{}'. Valid values: file, module, class",
                s
            )),
        }
    }
}

/// Type of dependency between modules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DependencyType {
    /// Import statement (e.g., `import foo`, `use crate::bar`)
    Import,
    /// Function call across module boundary
    Call,
    /// Type usage (parameters, return types, variables)
    Type,
    /// Class inheritance
    Inheritance,
}

impl std::fmt::Display for DependencyType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Import => write!(f, "import"),
            Self::Call => write!(f, "call"),
            Self::Type => write!(f, "type"),
            Self::Inheritance => write!(f, "inheritance"),
        }
    }
}

/// A single dependency edge between two modules.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyEdge {
    /// Source module (the one that depends)
    pub from: String,
    /// Target module (the one being depended upon)
    pub to: String,
    /// Type of dependency
    pub dependency_type: DependencyType,
    /// Specific items involved (function names, class names, etc.)
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub items: Vec<String>,
}

/// Coupling metrics for a single module.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CouplingMetrics {
    /// Module/file/class name
    pub module: String,
    /// Full path (for files) or qualified name
    pub path: String,
    /// Afferent coupling (Ca): number of modules that depend ON this module
    pub afferent: u32,
    /// Efferent coupling (Ce): number of modules this module depends ON
    pub efferent: u32,
    /// Instability: I = Ce / (Ca + Ce), ranges from 0 (stable) to 1 (unstable)
    pub instability: f64,
    /// Abstractness: A = abstract_types / total_types
    pub abstractness: f64,
    /// Distance from main sequence: D = |A + I - 1|
    pub distance: f64,
    /// Total number of types (classes, interfaces, traits) defined
    pub total_types: u32,
    /// Number of abstract types (interfaces, abstract classes, traits)
    pub abstract_types: u32,
    /// List of modules that depend on this module (incoming)
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub dependents: Vec<String>,
    /// List of modules this module depends on (outgoing)
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub dependencies: Vec<String>,
    /// Breakdown by dependency type
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub by_type: HashMap<String, u32>,
}

impl CouplingMetrics {
    /// Create new coupling metrics for a module.
    #[must_use]
    pub fn new(module: String, path: String) -> Self {
        Self {
            module,
            path,
            afferent: 0,
            efferent: 0,
            instability: 0.0,
            abstractness: 0.0,
            distance: 1.0, // Maximum distance when no data
            total_types: 0,
            abstract_types: 0,
            dependents: Vec::new(),
            dependencies: Vec::new(),
            by_type: HashMap::new(),
        }
    }

    /// Calculate derived metrics (instability, abstractness, distance).
    pub fn calculate_derived(&mut self) {
        // Instability: I = Ce / (Ca + Ce)
        let total_coupling = self.afferent + self.efferent;
        self.instability = if total_coupling > 0 {
            f64::from(self.efferent) / f64::from(total_coupling)
        } else {
            0.0 // No dependencies = maximally stable
        };

        // Abstractness: A = abstract_types / total_types
        self.abstractness = if self.total_types > 0 {
            f64::from(self.abstract_types) / f64::from(self.total_types)
        } else {
            0.0 // No types = concrete
        };

        // Distance from main sequence: D = |A + I - 1|
        self.distance = (self.abstractness + self.instability - 1.0).abs();
    }

    /// Check if this module is in the "Zone of Pain" (stable and concrete).
    ///
    /// Modules in this zone are hard to change because they have many dependents
    /// but provide no abstraction.
    #[must_use]
    pub fn is_in_zone_of_pain(&self) -> bool {
        self.instability < 0.2 && self.abstractness < 0.2 && self.afferent > 0
    }

    /// Check if this module is in the "Zone of Uselessness" (unstable and abstract).
    ///
    /// Modules in this zone are maximally flexible but likely unused.
    #[must_use]
    pub fn is_in_zone_of_uselessness(&self) -> bool {
        self.instability > 0.8 && self.abstractness > 0.8
    }

    /// Get a description of the module's position relative to the main sequence.
    #[must_use]
    pub fn position_description(&self) -> &'static str {
        if self.distance < 0.1 {
            "On main sequence (well-balanced)"
        } else if self.is_in_zone_of_pain() {
            "Zone of Pain (stable, concrete - rigid)"
        } else if self.is_in_zone_of_uselessness() {
            "Zone of Uselessness (unstable, abstract)"
        } else if self.distance < 0.3 {
            "Near main sequence"
        } else if self.distance < 0.5 {
            "Moderately far from main sequence"
        } else {
            "Far from main sequence (consider refactoring)"
        }
    }
}

/// Risk level for coupling issues.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CouplingRisk {
    /// Low risk - good balance
    Low,
    /// Medium risk - some concern
    Medium,
    /// High risk - architectural issue
    High,
    /// Critical - severe architectural problem
    Critical,
}

impl CouplingRisk {
    /// Classify distance from main sequence into risk level.
    #[must_use]
    pub fn from_distance(distance: f64) -> Self {
        if distance < 0.2 {
            Self::Low
        } else if distance < 0.4 {
            Self::Medium
        } else if distance < 0.6 {
            Self::High
        } else {
            Self::Critical
        }
    }

    /// Get ANSI color code for CLI output.
    #[must_use]
    pub const fn color_code(&self) -> &'static str {
        match self {
            Self::Low => "\x1b[32m",      // Green
            Self::Medium => "\x1b[33m",   // Yellow
            Self::High => "\x1b[31m",     // Red
            Self::Critical => "\x1b[35m", // Magenta
        }
    }
}

impl std::fmt::Display for CouplingRisk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "low"),
            Self::Medium => write!(f, "medium"),
            Self::High => write!(f, "high"),
            Self::Critical => write!(f, "critical"),
        }
    }
}

/// Aggregate statistics for coupling analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CouplingStats {
    /// Total number of modules analyzed
    pub total_modules: usize,
    /// Total number of dependency edges
    pub total_dependencies: usize,
    /// Average afferent coupling
    pub avg_afferent: f64,
    /// Average efferent coupling
    pub avg_efferent: f64,
    /// Average instability
    pub avg_instability: f64,
    /// Average distance from main sequence
    pub avg_distance: f64,
    /// Number of modules in Zone of Pain
    pub zone_of_pain_count: usize,
    /// Number of modules in Zone of Uselessness
    pub zone_of_uselessness_count: usize,
    /// Modules with highest afferent coupling (most depended upon)
    pub most_depended: Vec<String>,
    /// Modules with highest efferent coupling (most dependencies)
    pub most_dependent: Vec<String>,
    /// Risk distribution
    pub risk_distribution: HashMap<String, usize>,
}

impl Default for CouplingStats {
    fn default() -> Self {
        Self {
            total_modules: 0,
            total_dependencies: 0,
            avg_afferent: 0.0,
            avg_efferent: 0.0,
            avg_instability: 0.0,
            avg_distance: 0.0,
            zone_of_pain_count: 0,
            zone_of_uselessness_count: 0,
            most_depended: Vec::new(),
            most_dependent: Vec::new(),
            risk_distribution: HashMap::new(),
        }
    }
}

/// Complete coupling analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CouplingAnalysis {
    /// Path analyzed
    pub path: PathBuf,
    /// Language (if filtered)
    pub language: Option<String>,
    /// Level of analysis
    pub level: CouplingLevel,
    /// Coupling metrics for each module
    pub modules: Vec<CouplingMetrics>,
    /// All dependency edges
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub edges: Vec<DependencyEdge>,
    /// Aggregate statistics
    pub stats: CouplingStats,
    /// Circular dependencies detected
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub circular_dependencies: Vec<Vec<String>>,
}

// =============================================================================
// STANDARD LIBRARY DETECTION
// =============================================================================

/// Known standard library module prefixes by language.
fn get_stdlib_prefixes(lang: &str) -> &'static [&'static str] {
    match lang {
        "python" => &[
            "os",
            "sys",
            "io",
            "re",
            "json",
            "csv",
            "math",
            "random",
            "datetime",
            "time",
            "collections",
            "itertools",
            "functools",
            "operator",
            "string",
            "typing",
            "abc",
            "enum",
            "dataclasses",
            "pathlib",
            "shutil",
            "tempfile",
            "subprocess",
            "threading",
            "multiprocessing",
            "asyncio",
            "concurrent",
            "socket",
            "http",
            "urllib",
            "email",
            "html",
            "xml",
            "logging",
            "unittest",
            "pytest",
            "doctest",
            "pdb",
            "traceback",
            "warnings",
            "contextlib",
            "copy",
            "pickle",
            "shelve",
            "sqlite3",
            "hashlib",
            "hmac",
            "secrets",
            "struct",
            "codecs",
            "unicodedata",
            "locale",
            "gettext",
            "argparse",
            "configparser",
            "statistics",
            "fractions",
            "decimal",
            "numbers",
            "cmath",
            "array",
            "bisect",
            "heapq",
            "queue",
            "types",
            "weakref",
            "gc",
            "inspect",
            "dis",
            "ast",
            "builtins",
            "__future__",
            "importlib",
        ],
        "rust" => &["std", "core", "alloc", "proc_macro", "test"],
        "go" => &[
            "fmt",
            "os",
            "io",
            "bufio",
            "bytes",
            "strings",
            "strconv",
            "unicode",
            "regexp",
            "path",
            "filepath",
            "sort",
            "container",
            "encoding",
            "json",
            "xml",
            "csv",
            "html",
            "template",
            "text",
            "net",
            "http",
            "url",
            "mime",
            "crypto",
            "hash",
            "math",
            "rand",
            "time",
            "log",
            "flag",
            "testing",
            "sync",
            "atomic",
            "context",
            "errors",
            "runtime",
            "reflect",
            "unsafe",
            "syscall",
            "os/exec",
            "os/signal",
            "io/ioutil",
            "io/fs",
            "embed",
            "database/sql",
            "archive",
            "compress",
            "image",
            "debug",
        ],
        "typescript" | "javascript" => &[
            "fs",
            "path",
            "os",
            "util",
            "events",
            "stream",
            "http",
            "https",
            "url",
            "querystring",
            "crypto",
            "zlib",
            "buffer",
            "process",
            "child_process",
            "cluster",
            "dns",
            "net",
            "tls",
            "dgram",
            "readline",
            "repl",
            "vm",
            "assert",
            "console",
            "timers",
            "perf_hooks",
            "async_hooks",
            "worker_threads",
        ],
        "java" => &[
            "java.lang",
            "java.util",
            "java.io",
            "java.nio",
            "java.net",
            "java.sql",
            "java.text",
            "java.time",
            "java.math",
            "java.security",
            "java.awt",
            "javax.swing",
            "javax.servlet",
            "org.w3c",
            "org.xml",
        ],
        "c" | "cpp" => &[
            "stdio",
            "stdlib",
            "string",
            "math",
            "time",
            "ctype",
            "errno",
            "assert",
            "stddef",
            "stdint",
            "stdbool",
            "limits",
            "float",
            "stdarg",
            "setjmp",
            "signal",
            "locale",
            "wchar",
            "wctype",
            "complex",
            "fenv",
            "inttypes",
            "iso646",
            "tgmath",
            "stdalign",
            "stdatomic",
            "stdnoreturn",
            "threads",
            // C++ standard library
            "iostream",
            "fstream",
            "sstream",
            "iomanip",
            "vector",
            "list",
            "deque",
            "array",
            "forward_list",
            "set",
            "map",
            "unordered_set",
            "unordered_map",
            "stack",
            "queue",
            "priority_queue",
            "algorithm",
            "iterator",
            "memory",
            "functional",
            "numeric",
            "random",
            "chrono",
            "thread",
            "mutex",
            "atomic",
            "condition_variable",
            "future",
            "regex",
            "filesystem",
            "optional",
            "variant",
            "any",
            "string_view",
            "charconv",
            "execution",
            "ranges",
        ],
        _ => &[],
    }
}

/// Check if a module name is a standard library module.
fn is_stdlib_module(module: &str, lang: &str) -> bool {
    let prefixes = get_stdlib_prefixes(lang);

    // Check exact match or prefix match
    for prefix in prefixes {
        if module == *prefix {
            return true;
        }
        // Check with dot separator (Python, Java)
        if module.starts_with(&format!("{}.", prefix)) {
            return true;
        }
        // Check with slash separator (Go, TypeScript/Node)
        if module.starts_with(&format!("{}/", prefix)) {
            return true;
        }
    }

    // Language-specific checks
    match lang {
        "python" => {
            // Python private/internal modules
            module.starts_with('_') && !module.starts_with("__")
        }
        "rust" => {
            // Rust standard library crates
            module == "std"
                || module.starts_with("std::")
                || module == "core"
                || module.starts_with("core::")
                || module == "alloc"
                || module.starts_with("alloc::")
        }
        "go" => {
            // Go stdlib doesn't use external domain prefixes
            !module.contains('.') || module.starts_with("golang.org/x/")
        }
        _ => false,
    }
}

// =============================================================================
// DEPENDENCY EXTRACTION
// =============================================================================

/// Information extracted from a single file.
#[derive(Debug, Default)]
struct FileInfo {
    /// Canonical file path
    path: PathBuf,
    /// Relative path from project root
    relative_path: String,
    /// Module name (derived from path) - kept for potential future use
    #[allow(dead_code)]
    module_name: String,
    /// Parent directory/package
    parent_module: String,
    /// Language - kept for potential future use
    #[allow(dead_code)]
    language: String,
    /// Import dependencies
    imports: Vec<ImportInfo>,
    /// Classes defined in this file
    classes: Vec<ClassInfo>,
    /// Functions defined (for call graph)
    functions: Vec<String>,
    /// Total types defined
    total_types: u32,
    /// Abstract types (interfaces, abstract classes, traits)
    abstract_types: u32,
}

impl FileInfo {
    /// Derive module name from file path.
    fn derive_module_name(path: &Path, project_root: &Path) -> (String, String) {
        let relative = path.strip_prefix(project_root).unwrap_or(path);

        // Remove extension
        let module_name = relative
            .with_extension("")
            .to_string_lossy()
            .replace('\\', "/")
            .replace('/', ".");

        // Parent module (directory)
        let parent = relative
            .parent()
            .map(|p| p.to_string_lossy().replace('\\', "/").replace('/', "."))
            .unwrap_or_default();

        (module_name, parent)
    }
}

/// Extract file information for coupling analysis.
fn extract_file_info(
    path: &Path,
    project_root: &Path,
    lang: &str,
) -> std::result::Result<FileInfo, CouplingError> {
    let source = std::fs::read(path).map_err(CouplingError::IoError)?;

    let (module_name, parent_module) = FileInfo::derive_module_name(path, project_root);

    let mut info = FileInfo {
        path: path.to_path_buf(),
        relative_path: path
            .strip_prefix(project_root)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string(),
        module_name,
        parent_module,
        language: lang.to_string(),
        ..Default::default()
    };

    // Get language handler
    let registry = LanguageRegistry::global();
    let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    let Some(language) = registry.get_by_extension(ext) else {
        return Ok(info);
    };

    // Parse the file
    let mut parser = language.parser().map_err(|e| CouplingError::ParseError {
        file: path.display().to_string(),
        message: format!("{}", e),
    })?;

    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| CouplingError::ParseError {
            file: path.display().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    // Extract imports
    info.imports = language.extract_imports(&tree, &source);

    // Extract classes and count types
    let module_info = AstExtractor::extract_file(path).ok();
    if let Some(module) = module_info {
        for class in &module.classes {
            info.total_types += 1;

            // Check if abstract (heuristic based on language)
            let is_abstract = match lang {
                "python" => {
                    // ABC base class or has abstractmethod decorators
                    class
                        .bases
                        .iter()
                        .any(|b: &String| b.contains("ABC") || b.contains("Abstract"))
                        || class
                            .docstring
                            .as_ref()
                            .map(|d| d.contains("abstract"))
                            .unwrap_or(false)
                }
                "rust" => {
                    // Traits are abstract
                    class.name.starts_with("trait ")
                        || class
                            .docstring
                            .as_ref()
                            .map(|d| d.contains("trait"))
                            .unwrap_or(false)
                }
                "typescript" | "javascript" => {
                    // Interfaces are abstract
                    class
                        .docstring
                        .as_ref()
                        .map(|d| d.contains("interface"))
                        .unwrap_or(false)
                }
                "java" => {
                    // Interface or abstract class
                    class
                        .docstring
                        .as_ref()
                        .map(|d| d.contains("interface") || d.contains("abstract class"))
                        .unwrap_or(false)
                }
                "go" => {
                    // Interfaces in Go
                    class
                        .docstring
                        .as_ref()
                        .map(|d| d.contains("interface"))
                        .unwrap_or(false)
                }
                _ => false,
            };

            if is_abstract {
                info.abstract_types += 1;
            }

            info.classes.push(class.clone());
        }

        // Extract function names
        for func in &module.functions {
            info.functions.push(func.name.clone());
        }
        for class in &module.classes {
            for method in &class.methods {
                info.functions
                    .push(format!("{}.{}", class.name, method.name));
            }
        }
    }

    Ok(info)
}

// =============================================================================
// DEPENDENCY GRAPH BUILDING
// =============================================================================

/// Build dependency graph from extracted file information.
struct DependencyGraph {
    /// All modules (by canonical name)
    modules: HashMap<String, CouplingMetrics>,
    /// Edges: (from, to) -> dependency types
    edges: HashMap<(String, String), HashSet<DependencyType>>,
    /// Detailed edges for output
    edge_list: Vec<DependencyEdge>,
}

impl DependencyGraph {
    fn new() -> Self {
        Self {
            modules: HashMap::new(),
            edges: HashMap::new(),
            edge_list: Vec::new(),
        }
    }

    /// Add or get a module.
    fn get_or_insert_module(&mut self, name: &str, path: &str) -> &mut CouplingMetrics {
        self.modules
            .entry(name.to_string())
            .or_insert_with(|| CouplingMetrics::new(name.to_string(), path.to_string()))
    }

    /// Add a dependency edge.
    fn add_dependency(
        &mut self,
        from: &str,
        to: &str,
        dep_type: DependencyType,
        items: Vec<String>,
    ) {
        // Skip self-dependencies
        if from == to {
            return;
        }

        let key = (from.to_string(), to.to_string());
        let types = self.edges.entry(key.clone()).or_default();
        let is_new_type = types.insert(dep_type);

        // Add to edge list if this is a new edge type
        if is_new_type {
            self.edge_list.push(DependencyEdge {
                from: from.to_string(),
                to: to.to_string(),
                dependency_type: dep_type,
                items,
            });
        }
    }

    /// Calculate coupling metrics from edges.
    fn calculate_metrics(&mut self) {
        // First pass: count afferent (Ca) and efferent (Ce)
        for ((from, to), _types) in &self.edges {
            // Efferent: from depends on to
            if let Some(m) = self.modules.get_mut(from) {
                if !m.dependencies.contains(to) {
                    m.efferent += 1;
                    m.dependencies.push(to.clone());
                }
            }

            // Afferent: to is depended upon by from
            if let Some(m) = self.modules.get_mut(to) {
                if !m.dependents.contains(from) {
                    m.afferent += 1;
                    m.dependents.push(from.clone());
                }
            }
        }

        // Count dependency types per module
        for ((from, _to), types) in &self.edges {
            if let Some(m) = self.modules.get_mut(from) {
                for t in types {
                    *m.by_type.entry(t.to_string()).or_insert(0) += 1;
                }
            }
        }

        // Second pass: calculate derived metrics
        for metrics in self.modules.values_mut() {
            metrics.calculate_derived();
        }
    }

    /// Detect circular dependencies using DFS.
    fn detect_cycles(&self) -> Vec<Vec<String>> {
        let mut cycles = Vec::new();
        let mut visited = HashSet::new();
        let mut rec_stack = Vec::new();
        let mut on_stack = HashSet::new();

        for module in self.modules.keys() {
            if !visited.contains(module) {
                self.dfs_cycle(
                    module,
                    &mut visited,
                    &mut rec_stack,
                    &mut on_stack,
                    &mut cycles,
                );
            }
        }

        // Remove duplicate cycles (same nodes, different starting points)
        let mut unique_cycles: Vec<Vec<String>> = Vec::new();
        for cycle in cycles {
            let normalized = Self::normalize_cycle(&cycle);
            if !unique_cycles
                .iter()
                .any(|c| Self::normalize_cycle(c) == normalized)
            {
                unique_cycles.push(cycle);
            }
        }

        unique_cycles
    }

    fn dfs_cycle(
        &self,
        node: &str,
        visited: &mut HashSet<String>,
        rec_stack: &mut Vec<String>,
        on_stack: &mut HashSet<String>,
        cycles: &mut Vec<Vec<String>>,
    ) {
        visited.insert(node.to_string());
        rec_stack.push(node.to_string());
        on_stack.insert(node.to_string());

        if let Some(metrics) = self.modules.get(node) {
            for dep in &metrics.dependencies {
                if !visited.contains(dep) {
                    self.dfs_cycle(dep, visited, rec_stack, on_stack, cycles);
                } else if on_stack.contains(dep) {
                    // Found a cycle
                    let start_idx = rec_stack.iter().position(|n| n == dep).unwrap_or(0);
                    let cycle: Vec<String> = rec_stack[start_idx..].to_vec();
                    if cycle.len() > 1 {
                        cycles.push(cycle);
                    }
                }
            }
        }

        rec_stack.pop();
        on_stack.remove(node);
    }

    fn normalize_cycle(cycle: &[String]) -> Vec<String> {
        if cycle.is_empty() {
            return Vec::new();
        }

        // Find the minimum element to start from
        let min_idx = cycle
            .iter()
            .enumerate()
            .min_by_key(|(_, v)| *v)
            .map(|(i, _)| i)
            .unwrap_or(0);

        // Rotate so minimum is first
        let mut normalized: Vec<String> = cycle[min_idx..].to_vec();
        normalized.extend_from_slice(&cycle[..min_idx]);
        normalized
    }
}

// =============================================================================
// MAIN ANALYSIS FUNCTIONS
// =============================================================================

/// Analyze coupling metrics for a project.
///
/// # Arguments
///
/// * `path` - Path to the project root
/// * `lang` - Optional language filter
/// * `level` - Granularity level (file, module, or class)
///
/// # Returns
///
/// Complete coupling analysis with metrics for each module.
pub fn analyze_coupling(
    path: impl AsRef<Path>,
    lang: Option<&str>,
    level: CouplingLevel,
) -> std::result::Result<CouplingAnalysis, CouplingError> {
    let path = path.as_ref();
    let project_root = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

    debug!("Analyzing coupling for {:?} at {:?} level", path, level);

    // Scan for source files
    let scanner = ProjectScanner::new(path.to_str().unwrap_or("."))
        .map_err(|e| CouplingError::ScanError(e.to_string()))?;

    let config = match lang {
        Some(l) if l != "all" => ScanConfig::for_language(l),
        _ => ScanConfig::default(),
    };

    let scan_result = scanner
        .scan_with_config(&config)
        .map_err(|e| CouplingError::ScanError(e.to_string()))?;

    let files = scan_result.files;
    debug!("Found {} files to analyze", files.len());

    // Determine language for stdlib detection
    let detected_lang = lang.unwrap_or_else(|| {
        // Auto-detect from first file
        files
            .first()
            .and_then(|f| f.extension())
            .and_then(|e| e.to_str())
            .map(|ext| match ext {
                "py" => "python",
                "rs" => "rust",
                "go" => "go",
                "ts" | "tsx" => "typescript",
                "js" | "jsx" => "javascript",
                "java" => "java",
                "c" | "h" => "c",
                "cpp" | "cc" | "cxx" | "hpp" | "cu" | "cuh" => "cpp",
                _ => "unknown",
            })
            .unwrap_or("unknown")
    });

    // Extract file information in parallel
    let file_infos: Vec<FileInfo> = files
        .par_iter()
        .filter_map(|file| extract_file_info(file, &project_root, detected_lang).ok())
        .collect();

    debug!("Extracted info from {} files", file_infos.len());

    // Build dependency graph
    let mut graph = DependencyGraph::new();

    // Add all modules first
    for info in &file_infos {
        let module_name = match level {
            CouplingLevel::File => info.relative_path.clone(),
            CouplingLevel::Module => {
                if info.parent_module.is_empty() {
                    "(root)".to_string()
                } else {
                    info.parent_module.clone()
                }
            }
            CouplingLevel::Class => {
                // Will add classes individually below
                continue;
            }
        };

        let m = graph.get_or_insert_module(&module_name, &info.relative_path);
        m.total_types += info.total_types;
        m.abstract_types += info.abstract_types;
    }

    // For class level, add each class as a module
    if level == CouplingLevel::Class {
        for info in &file_infos {
            for class in &info.classes {
                let class_name = format!("{}:{}", info.relative_path, class.name);
                let m = graph.get_or_insert_module(&class_name, &info.relative_path);
                m.total_types = 1;

                // Check if abstract
                let is_abstract = match detected_lang {
                    "python" => class.bases.iter().any(|b: &String| b.contains("ABC")),
                    "rust" => class.name.starts_with("trait "),
                    _ => false,
                };
                m.abstract_types = if is_abstract { 1 } else { 0 };
            }
        }
    }

    // Add import dependencies
    for info in &file_infos {
        let from_module = match level {
            CouplingLevel::File => info.relative_path.clone(),
            CouplingLevel::Module => {
                if info.parent_module.is_empty() {
                    "(root)".to_string()
                } else {
                    info.parent_module.clone()
                }
            }
            CouplingLevel::Class => continue, // Handle separately
        };

        for import in &info.imports {
            // Skip standard library imports
            if is_stdlib_module(&import.module, detected_lang) {
                continue;
            }

            // Skip empty modules (relative imports with no module)
            if import.module.is_empty() && import.level == 0 {
                continue;
            }

            // Resolve target module based on level
            let to_module = match level {
                CouplingLevel::File => {
                    // Try to find the actual file
                    resolve_import_to_file(&import.module, &file_infos, detected_lang)
                }
                CouplingLevel::Module => {
                    // Use the first component as package
                    import
                        .module
                        .split('.')
                        .next()
                        .or_else(|| import.module.split('/').next())
                        .unwrap_or(&import.module)
                        .to_string()
                }
                CouplingLevel::Class => continue,
            };

            if !to_module.is_empty() && to_module != from_module {
                // Ensure target module exists in graph
                graph.get_or_insert_module(&to_module, &to_module);

                graph.add_dependency(
                    &from_module,
                    &to_module,
                    DependencyType::Import,
                    import.names.clone(),
                );
            }
        }

        // Add inheritance dependencies
        for class in &info.classes {
            for base in &class.bases {
                // Skip builtin bases
                if is_stdlib_module(base, detected_lang) {
                    continue;
                }

                // Try to find where the base class is defined
                if let Some(base_file) = find_class_definition(base, &file_infos) {
                    let to_module = match level {
                        CouplingLevel::File => base_file.relative_path.clone(),
                        CouplingLevel::Module => base_file.parent_module.clone(),
                        CouplingLevel::Class => format!("{}:{}", base_file.relative_path, base),
                    };

                    if !to_module.is_empty() && to_module != from_module {
                        graph.get_or_insert_module(&to_module, &to_module);

                        let from = if level == CouplingLevel::Class {
                            format!("{}:{}", info.relative_path, class.name)
                        } else {
                            from_module.clone()
                        };

                        graph.add_dependency(
                            &from,
                            &to_module,
                            DependencyType::Inheritance,
                            vec![base.clone()],
                        );
                    }
                }
            }
        }
    }

    // Build call graph for call dependencies
    if let Ok(call_graph) = callgraph::build_with_config(path.to_str().unwrap_or("."), lang, false)
    {
        add_call_dependencies(&mut graph, &call_graph, &file_infos, level, &project_root);
    }

    // Calculate metrics
    graph.calculate_metrics();

    // Detect cycles
    let circular_dependencies = graph.detect_cycles();

    // Build statistics
    let stats = calculate_stats(&graph);

    // Collect results
    let mut modules: Vec<CouplingMetrics> = graph.modules.into_values().collect();
    modules.sort_by(|a, b| {
        // Sort by distance from main sequence (worst first)
        b.distance
            .partial_cmp(&a.distance)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    Ok(CouplingAnalysis {
        path: path.to_path_buf(),
        language: lang.map(String::from),
        level,
        modules,
        edges: graph.edge_list,
        stats,
        circular_dependencies,
    })
}

/// Analyze coupling for a single file.
pub fn analyze_file_coupling(
    file: impl AsRef<Path>,
    lang: Option<&str>,
) -> std::result::Result<CouplingMetrics, CouplingError> {
    let file = file.as_ref();
    let parent = file.parent().unwrap_or(Path::new("."));

    let analysis = analyze_coupling(parent, lang, CouplingLevel::File)?;

    let relative = file.file_name().and_then(|n| n.to_str()).unwrap_or("");

    analysis
        .modules
        .into_iter()
        .find(|m| m.path.contains(relative) || m.module.contains(relative))
        .ok_or_else(|| CouplingError::ParseError {
            file: file.display().to_string(),
            message: "File not found in analysis results".to_string(),
        })
}

// =============================================================================
// HELPER FUNCTIONS
// =============================================================================

/// Resolve an import to a file path.
fn resolve_import_to_file(module: &str, files: &[FileInfo], lang: &str) -> String {
    // Convert module path to potential file paths
    let candidates: Vec<String> = match lang {
        "python" => {
            let path = module.replace('.', "/");
            vec![format!("{}.py", path), format!("{}/__init__.py", path)]
        }
        "rust" => {
            let path = module.replace("::", "/");
            vec![format!("{}.rs", path), format!("{}/mod.rs", path)]
        }
        "go" => {
            vec![module.to_string()]
        }
        "typescript" | "javascript" => {
            let path = module.replace('.', "/");
            vec![
                format!("{}.ts", path),
                format!("{}.tsx", path),
                format!("{}.js", path),
                format!("{}.jsx", path),
                format!("{}/index.ts", path),
                format!("{}/index.js", path),
            ]
        }
        _ => vec![module.to_string()],
    };

    // Find matching file
    for info in files {
        for candidate in &candidates {
            if info.relative_path.ends_with(candidate) || info.relative_path == *candidate {
                return info.relative_path.clone();
            }
        }
    }

    // Fallback to first segment as approximation
    module
        .split('.')
        .next()
        .or_else(|| module.split('/').next())
        .unwrap_or(module)
        .to_string()
}

/// Find where a class is defined.
fn find_class_definition<'a>(class_name: &str, files: &'a [FileInfo]) -> Option<&'a FileInfo> {
    files
        .iter()
        .find(|info| info.classes.iter().any(|c| c.name == class_name))
}

/// Add call dependencies from call graph.
fn add_call_dependencies(
    graph: &mut DependencyGraph,
    call_graph: &CallGraph,
    files: &[FileInfo],
    level: CouplingLevel,
    project_root: &Path,
) {
    // Build file path -> module mapping
    let file_to_module: HashMap<String, String> = files
        .iter()
        .map(|f| {
            let module = match level {
                CouplingLevel::File => f.relative_path.clone(),
                CouplingLevel::Module => {
                    if f.parent_module.is_empty() {
                        "(root)".to_string()
                    } else {
                        f.parent_module.clone()
                    }
                }
                CouplingLevel::Class => f.relative_path.clone(), // Will refine below
            };
            (f.path.to_string_lossy().to_string(), module)
        })
        .collect();

    for edge in &call_graph.edges {
        let from_file = &edge.caller.file;
        let to_file = &edge.callee.file;

        // Skip if either file is unknown
        if from_file.is_empty() || to_file.is_empty() {
            continue;
        }

        // Resolve to modules
        let from_module = file_to_module.get(from_file).cloned().unwrap_or_else(|| {
            Path::new(from_file)
                .strip_prefix(project_root)
                .unwrap_or(Path::new(from_file))
                .to_string_lossy()
                .to_string()
        });

        let to_module = file_to_module.get(to_file).cloned().unwrap_or_else(|| {
            Path::new(to_file)
                .strip_prefix(project_root)
                .unwrap_or(Path::new(to_file))
                .to_string_lossy()
                .to_string()
        });

        // For class level, try to include class name
        let (from_mod, to_mod) = if level == CouplingLevel::Class {
            let from = if let Some(ref qn) = edge.caller.qualified_name {
                if qn.contains('.') {
                    let parts: Vec<&str> = qn.split('.').collect();
                    if parts.len() >= 2 {
                        format!("{}:{}", from_module, parts[0])
                    } else {
                        from_module.clone()
                    }
                } else {
                    from_module.clone()
                }
            } else {
                from_module.clone()
            };

            let to = if let Some(ref qn) = edge.callee.qualified_name {
                if qn.contains('.') {
                    let parts: Vec<&str> = qn.split('.').collect();
                    if parts.len() >= 2 {
                        format!("{}:{}", to_module, parts[0])
                    } else {
                        to_module.clone()
                    }
                } else {
                    to_module.clone()
                }
            } else {
                to_module.clone()
            };

            (from, to)
        } else {
            (from_module, to_module)
        };

        if from_mod != to_mod {
            graph.get_or_insert_module(&from_mod, &from_mod);
            graph.get_or_insert_module(&to_mod, &to_mod);

            graph.add_dependency(
                &from_mod,
                &to_mod,
                DependencyType::Call,
                vec![edge.callee.name.clone()],
            );
        }
    }
}

/// Calculate aggregate statistics.
fn calculate_stats(graph: &DependencyGraph) -> CouplingStats {
    let modules: Vec<&CouplingMetrics> = graph.modules.values().collect();
    let n = modules.len();

    if n == 0 {
        return CouplingStats::default();
    }

    let total_afferent: u32 = modules.iter().map(|m| m.afferent).sum();
    let total_efferent: u32 = modules.iter().map(|m| m.efferent).sum();
    let total_instability: f64 = modules.iter().map(|m| m.instability).sum();
    let total_distance: f64 = modules.iter().map(|m| m.distance).sum();

    let zone_of_pain = modules.iter().filter(|m| m.is_in_zone_of_pain()).count();
    let zone_of_uselessness = modules
        .iter()
        .filter(|m| m.is_in_zone_of_uselessness())
        .count();

    // Find most depended-upon modules (highest Ca)
    let mut sorted_by_afferent: Vec<_> = modules.iter().collect();
    sorted_by_afferent.sort_by(|a, b| b.afferent.cmp(&a.afferent));
    let most_depended: Vec<String> = sorted_by_afferent
        .iter()
        .take(5)
        .filter(|m| m.afferent > 0)
        .map(|m| m.module.clone())
        .collect();

    // Find most dependent modules (highest Ce)
    let mut sorted_by_efferent: Vec<_> = modules.iter().collect();
    sorted_by_efferent.sort_by(|a, b| b.efferent.cmp(&a.efferent));
    let most_dependent: Vec<String> = sorted_by_efferent
        .iter()
        .take(5)
        .filter(|m| m.efferent > 0)
        .map(|m| m.module.clone())
        .collect();

    // Risk distribution
    let mut risk_distribution: HashMap<String, usize> = HashMap::new();
    for m in &modules {
        let risk = CouplingRisk::from_distance(m.distance);
        *risk_distribution.entry(risk.to_string()).or_insert(0) += 1;
    }

    CouplingStats {
        total_modules: n,
        total_dependencies: graph.edges.len(),
        avg_afferent: f64::from(total_afferent) / n as f64,
        avg_efferent: f64::from(total_efferent) / n as f64,
        avg_instability: total_instability / n as f64,
        avg_distance: total_distance / n as f64,
        zone_of_pain_count: zone_of_pain,
        zone_of_uselessness_count: zone_of_uselessness,
        most_depended,
        most_dependent,
        risk_distribution,
    }
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::str::FromStr;
    use tempfile::TempDir;

    #[test]
    fn test_coupling_level_parsing() {
        assert_eq!(
            CouplingLevel::from_str("file").unwrap(),
            CouplingLevel::File
        );
        assert_eq!(
            CouplingLevel::from_str("module").unwrap(),
            CouplingLevel::Module
        );
        assert_eq!(
            CouplingLevel::from_str("package").unwrap(),
            CouplingLevel::Module
        );
        assert_eq!(
            CouplingLevel::from_str("class").unwrap(),
            CouplingLevel::Class
        );
        assert!(CouplingLevel::from_str("invalid").is_err());
    }

    #[test]
    fn test_coupling_metrics_calculation() {
        let mut metrics = CouplingMetrics::new("test".to_string(), "test.py".to_string());
        metrics.afferent = 3;
        metrics.efferent = 7;
        metrics.total_types = 10;
        metrics.abstract_types = 2;
        metrics.calculate_derived();

        // I = 7 / (3 + 7) = 0.7
        assert!((metrics.instability - 0.7).abs() < 0.001);

        // A = 2 / 10 = 0.2
        assert!((metrics.abstractness - 0.2).abs() < 0.001);

        // D = |0.2 + 0.7 - 1| = 0.1
        assert!((metrics.distance - 0.1).abs() < 0.001);
    }

    #[test]
    fn test_zone_detection() {
        // Zone of Pain: stable (low I) and concrete (low A)
        let mut pain = CouplingMetrics::new("pain".to_string(), "pain.py".to_string());
        pain.afferent = 10;
        pain.efferent = 1;
        pain.total_types = 5;
        pain.abstract_types = 0;
        pain.calculate_derived();
        assert!(pain.is_in_zone_of_pain());
        assert!(!pain.is_in_zone_of_uselessness());

        // Zone of Uselessness: unstable (high I) and abstract (high A)
        let mut useless = CouplingMetrics::new("useless".to_string(), "useless.py".to_string());
        useless.afferent = 1;
        useless.efferent = 10;
        useless.total_types = 5;
        useless.abstract_types = 5;
        useless.calculate_derived();
        assert!(!useless.is_in_zone_of_pain());
        assert!(useless.is_in_zone_of_uselessness());
    }

    #[test]
    fn test_stdlib_detection() {
        // Python
        assert!(is_stdlib_module("os", "python"));
        assert!(is_stdlib_module("os.path", "python"));
        assert!(is_stdlib_module("collections", "python"));
        assert!(!is_stdlib_module("mypackage", "python"));

        // Rust
        assert!(is_stdlib_module("std", "rust"));
        assert!(is_stdlib_module("std::collections", "rust"));
        assert!(!is_stdlib_module("my_crate", "rust"));

        // Go
        assert!(is_stdlib_module("fmt", "go"));
        assert!(is_stdlib_module("net/http", "go"));
        assert!(!is_stdlib_module("github.com/user/pkg", "go"));
    }

    #[test]
    fn test_cycle_normalization() {
        let cycle1 = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let cycle2 = vec!["b".to_string(), "c".to_string(), "a".to_string()];

        let norm1 = DependencyGraph::normalize_cycle(&cycle1);
        let norm2 = DependencyGraph::normalize_cycle(&cycle2);

        assert_eq!(norm1, norm2);
    }

    #[test]
    fn test_risk_from_distance() {
        assert_eq!(CouplingRisk::from_distance(0.1), CouplingRisk::Low);
        assert_eq!(CouplingRisk::from_distance(0.3), CouplingRisk::Medium);
        assert_eq!(CouplingRisk::from_distance(0.5), CouplingRisk::High);
        assert_eq!(CouplingRisk::from_distance(0.7), CouplingRisk::Critical);
    }

    #[test]
    fn test_analyze_simple_project() {
        let temp = TempDir::new().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(&src).unwrap();

        // Create a simple Python module
        fs::write(
            src.join("main.py"),
            r#"
from utils import helper

def main():
    helper()
"#,
        )
        .unwrap();

        fs::write(
            src.join("utils.py"),
            r#"
def helper():
    pass
"#,
        )
        .unwrap();

        let result = analyze_coupling(temp.path(), Some("python"), CouplingLevel::File);
        assert!(result.is_ok());

        let analysis = result.unwrap();
        assert!(!analysis.modules.is_empty());
        assert!(analysis.stats.total_modules >= 2);
    }

    #[test]
    fn test_dependency_edge_creation() {
        let mut graph = DependencyGraph::new();

        graph.get_or_insert_module("a", "a.py");
        graph.get_or_insert_module("b", "b.py");

        graph.add_dependency("a", "b", DependencyType::Import, vec!["foo".to_string()]);
        graph.add_dependency("a", "b", DependencyType::Call, vec!["bar".to_string()]);

        graph.calculate_metrics();

        let a = graph.modules.get("a").unwrap();
        let b = graph.modules.get("b").unwrap();

        assert_eq!(a.efferent, 1);
        assert_eq!(a.afferent, 0);
        assert_eq!(b.efferent, 0);
        assert_eq!(b.afferent, 1);
    }

    #[test]
    fn test_self_dependency_ignored() {
        let mut graph = DependencyGraph::new();

        graph.get_or_insert_module("a", "a.py");
        graph.add_dependency("a", "a", DependencyType::Import, vec![]);

        graph.calculate_metrics();

        let a = graph.modules.get("a").unwrap();
        assert_eq!(a.efferent, 0);
        assert_eq!(a.afferent, 0);
    }
}
