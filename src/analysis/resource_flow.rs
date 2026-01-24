//! Resource flow tracking analysis.
//!
//! This module provides path-sensitive analysis to track resource lifecycle
//! (acquire/release) and detect:
//! - Resource leaks (acquired but never released)
//! - Double-free/double-close bugs
//! - Use-after-release bugs
//!
//! # Supported Resource Types
//!
//! - File handles (`open()`, `File::open()`, `os.Open()`)
//! - Database connections (`connect()`, `Connection()`)
//! - Network sockets
//! - Locks/Mutexes (`lock.acquire()`, `Mutex::lock()`)
//! - Memory allocations
//! - Transactions
//! - Thread handles
//!
//! # Language Support
//!
//! - Python: `with` statement (context managers), explicit `close()`
//! - Rust: RAII, `Drop` trait automatic release
//! - Go: `defer`, explicit `Close()`
//! - JavaScript/TypeScript: `.close()`, callback patterns

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::cfg::types::{BlockId, BlockType, CFGInfo};
use crate::error::{BrrrError, Result};

// =============================================================================
// CORE TYPES
// =============================================================================

/// Type of resource being tracked.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ResourceType {
    /// File handle from `open()`, `File::open()`, `os.Open()`, etc.
    FileHandle,
    /// Database connection from `connect()`, `Connection()`, etc.
    DatabaseConnection,
    /// Network socket
    NetworkSocket,
    /// Mutex/lock acquired via `lock()`, `acquire()`, etc.
    Lock,
    /// Memory allocation (C/C++ `malloc`/`new`)
    MemoryAllocation,
    /// Database transaction
    Transaction,
    /// Thread or goroutine handle
    ThreadHandle,
    /// Custom resource type with user-defined name
    Custom(String),
}

impl std::fmt::Display for ResourceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FileHandle => write!(f, "file_handle"),
            Self::DatabaseConnection => write!(f, "database_connection"),
            Self::NetworkSocket => write!(f, "network_socket"),
            Self::Lock => write!(f, "lock"),
            Self::MemoryAllocation => write!(f, "memory_allocation"),
            Self::Transaction => write!(f, "transaction"),
            Self::ThreadHandle => write!(f, "thread_handle"),
            Self::Custom(name) => write!(f, "custom:{}", name),
        }
    }
}

/// Current state of a resource in the analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ResourceState {
    /// Resource has not been acquired yet
    Unacquired,
    /// Resource has been acquired and is active
    Acquired,
    /// Resource has been properly released
    Released,
    /// Resource was acquired but never released (leak)
    Leaked,
    /// Resource was released more than once
    DoubleFree,
    /// Resource state is unknown (conflicting paths)
    Unknown,
}

impl std::fmt::Display for ResourceState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unacquired => write!(f, "unacquired"),
            Self::Acquired => write!(f, "acquired"),
            Self::Released => write!(f, "released"),
            Self::Leaked => write!(f, "leaked"),
            Self::DoubleFree => write!(f, "double_free"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Source location in the code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// File path (relative to project root)
    pub file: String,
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed, optional)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub column: Option<usize>,
    /// Code snippet at this location
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snippet: Option<String>,
}

impl Location {
    /// Create a new location.
    #[must_use]
    pub fn new(file: impl Into<String>, line: usize) -> Self {
        Self {
            file: file.into(),
            line,
            column: None,
            snippet: None,
        }
    }

    /// Create a location with column information.
    #[must_use]
    pub fn with_column(mut self, column: usize) -> Self {
        self.column = Some(column);
        self
    }

    /// Create a location with a code snippet.
    #[must_use]
    pub fn with_snippet(mut self, snippet: impl Into<String>) -> Self {
        self.snippet = Some(snippet.into());
        self
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line)?;
        if let Some(col) = self.column {
            write!(f, ":{}", col)?;
        }
        Ok(())
    }
}

/// A tracked resource with its lifecycle information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Resource {
    /// Unique identifier for this resource instance
    pub id: usize,
    /// Type of resource
    pub resource_type: ResourceType,
    /// Variable name holding the resource
    pub variable: String,
    /// Location where resource was acquired
    pub acquire_location: Location,
    /// Locations where resource was released (may have multiple in different paths)
    pub release_locations: Vec<Location>,
    /// Current state of the resource
    pub state: ResourceState,
    /// Scope level where resource was acquired (for RAII tracking)
    pub scope_level: usize,
    /// Whether this resource is managed by a context manager/RAII/defer
    pub is_managed: bool,
    /// Original acquire expression (e.g., "open('file.txt')")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub acquire_expression: Option<String>,
}

/// Acquire pattern recognized in code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AcquirePattern {
    /// Function/method name that acquires the resource
    pub function_name: String,
    /// Type of resource this pattern acquires
    pub resource_type: ResourceType,
    /// Whether this is a context manager pattern (Python `with`)
    pub is_context_manager: bool,
    /// Whether this uses RAII (Rust automatic drop)
    pub is_raii: bool,
    /// Whether this uses defer (Go)
    pub uses_defer: bool,
    /// Language this pattern applies to
    pub language: String,
}

/// Release pattern recognized in code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReleasePattern {
    /// Function/method name that releases the resource
    pub function_name: String,
    /// Type of resource this pattern releases
    pub resource_type: ResourceType,
    /// Language this pattern applies to
    pub language: String,
}

// =============================================================================
// ANALYSIS RESULTS
// =============================================================================

/// A detected resource leak.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceLeak {
    /// The leaked resource
    pub resource: Resource,
    /// Paths through the CFG where the resource is not released
    /// Each path is a sequence of locations from acquire to function exit
    pub leak_paths: Vec<Vec<Location>>,
    /// Severity of the leak (higher = more severe)
    pub severity: LeakSeverity,
    /// Suggested fix for this leak
    pub suggestion: String,
}

/// Severity of a resource leak.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LeakSeverity {
    /// Low severity (e.g., small allocation in short-lived function)
    Low,
    /// Medium severity (e.g., file handle in non-critical path)
    Medium,
    /// High severity (e.g., database connection, lock)
    High,
    /// Critical severity (e.g., lock in concurrent code, memory in loop)
    Critical,
}

impl LeakSeverity {
    /// Get severity weight for sorting (higher = worse).
    #[must_use]
    pub const fn weight(&self) -> u8 {
        match self {
            Self::Low => 1,
            Self::Medium => 2,
            Self::High => 3,
            Self::Critical => 4,
        }
    }
}

/// A detected double-release (double-free, double-close) bug.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DoubleRelease {
    /// The affected resource
    pub resource: Resource,
    /// Location of first release
    pub first_release: Location,
    /// Location of second release
    pub second_release: Location,
    /// Control flow path from first to second release
    pub path: Vec<Location>,
}

/// A detected use-after-release bug.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UseAfterRelease {
    /// The affected resource
    pub resource: Resource,
    /// Location where resource was released
    pub release_location: Location,
    /// Location where resource was used after release
    pub use_location: Location,
    /// The operation performed on the released resource
    pub operation: String,
}

/// Complete resource flow analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceFlowAnalysis {
    /// File being analyzed
    pub file: String,
    /// Function being analyzed
    pub function_name: String,
    /// All tracked resources
    pub resources: Vec<Resource>,
    /// Detected resource leaks
    pub leaks: Vec<ResourceLeak>,
    /// Detected double-release bugs
    pub double_releases: Vec<DoubleRelease>,
    /// Detected use-after-release bugs
    pub use_after_release: Vec<UseAfterRelease>,
    /// Statistics about the analysis
    pub stats: AnalysisStats,
    /// Safe patterns detected (context managers, RAII, defer)
    pub safe_patterns: Vec<SafePattern>,
}

/// Statistics about the resource flow analysis.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AnalysisStats {
    /// Total resources tracked
    pub total_resources: usize,
    /// Resources properly released
    pub properly_released: usize,
    /// Resources leaked
    pub leaked: usize,
    /// Double-release bugs found
    pub double_releases: usize,
    /// Use-after-release bugs found
    pub use_after_release: usize,
    /// Resources managed by safe patterns (RAII, context manager, defer)
    pub safely_managed: usize,
    /// Number of CFG paths analyzed
    pub paths_analyzed: usize,
    /// Analysis time in milliseconds
    pub analysis_time_ms: u64,
}

/// A safe resource management pattern detected in code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafePattern {
    /// Type of safe pattern
    pub pattern_type: SafePatternType,
    /// Location where the pattern is used
    pub location: Location,
    /// Resource variable managed by this pattern
    pub variable: String,
    /// Description of the pattern
    pub description: String,
}

/// Type of safe resource management pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SafePatternType {
    /// Python `with` statement
    ContextManager,
    /// Rust RAII (automatic Drop)
    Raii,
    /// Go `defer` statement
    Defer,
    /// Java try-with-resources
    TryWithResources,
    /// C++ RAII with unique_ptr/shared_ptr
    SmartPointer,
}

// =============================================================================
// PATTERN REGISTRY
// =============================================================================

/// Registry of acquire/release patterns for different languages.
#[derive(Debug, Clone)]
pub struct PatternRegistry {
    /// Acquire patterns by language
    acquire_patterns: HashMap<String, Vec<AcquirePattern>>,
    /// Release patterns by language
    release_patterns: HashMap<String, Vec<ReleasePattern>>,
}

impl Default for PatternRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl PatternRegistry {
    /// Create a new pattern registry with built-in patterns.
    #[must_use]
    pub fn new() -> Self {
        let mut registry = Self {
            acquire_patterns: HashMap::new(),
            release_patterns: HashMap::new(),
        };
        registry.register_python_patterns();
        registry.register_rust_patterns();
        registry.register_go_patterns();
        registry.register_javascript_patterns();
        registry.register_c_cpp_patterns();
        registry.register_java_patterns();
        registry
    }

    fn register_python_patterns(&mut self) {
        let lang = "python".to_string();

        // File operations
        self.add_acquire_pattern(AcquirePattern {
            function_name: "open".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Database connections
        for func in &[
            "connect",
            "Connection",
            "create_connection",
            "get_connection",
        ] {
            self.add_acquire_pattern(AcquirePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::DatabaseConnection,
                is_context_manager: false,
                is_raii: false,
                uses_defer: false,
                language: lang.clone(),
            });
        }

        // Locks
        for func in &["acquire", "Lock", "RLock", "Semaphore"] {
            self.add_acquire_pattern(AcquirePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::Lock,
                is_context_manager: false,
                is_raii: false,
                uses_defer: false,
                language: lang.clone(),
            });
        }

        // Release patterns
        for func in &["close", "release", "disconnect", "shutdown"] {
            self.add_release_pattern(ReleasePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::FileHandle,
                language: lang.clone(),
            });
        }
    }

    fn register_rust_patterns(&mut self) {
        let lang = "rust".to_string();

        // File operations - all RAII
        self.add_acquire_pattern(AcquirePattern {
            function_name: "File::open".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "File::create".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        // Mutex locks - RAII via MutexGuard
        self.add_acquire_pattern(AcquirePattern {
            function_name: "Mutex::lock".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "RwLock::read".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "RwLock::write".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        // Database connections
        self.add_acquire_pattern(AcquirePattern {
            function_name: "Connection::open".to_string(),
            resource_type: ResourceType::DatabaseConnection,
            is_context_manager: false,
            is_raii: true,
            uses_defer: false,
            language: lang.clone(),
        });

        // Memory allocation (Box, Vec, etc. are RAII)
        for func in &["Box::new", "Vec::new", "Arc::new", "Rc::new"] {
            self.add_acquire_pattern(AcquirePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::MemoryAllocation,
                is_context_manager: false,
                is_raii: true,
                uses_defer: false,
                language: lang.clone(),
            });
        }
    }

    fn register_go_patterns(&mut self) {
        let lang = "go".to_string();

        // File operations
        self.add_acquire_pattern(AcquirePattern {
            function_name: "os.Open".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "os.Create".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "os.OpenFile".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Mutex operations
        self.add_acquire_pattern(AcquirePattern {
            function_name: "Lock".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "RLock".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Database connections
        self.add_acquire_pattern(AcquirePattern {
            function_name: "sql.Open".to_string(),
            resource_type: ResourceType::DatabaseConnection,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Release patterns
        self.add_release_pattern(ReleasePattern {
            function_name: "Close".to_string(),
            resource_type: ResourceType::FileHandle,
            language: lang.clone(),
        });

        self.add_release_pattern(ReleasePattern {
            function_name: "Unlock".to_string(),
            resource_type: ResourceType::Lock,
            language: lang.clone(),
        });

        self.add_release_pattern(ReleasePattern {
            function_name: "RUnlock".to_string(),
            resource_type: ResourceType::Lock,
            language: lang.clone(),
        });
    }

    fn register_javascript_patterns(&mut self) {
        let lang = "javascript".to_string();

        // File operations (Node.js fs)
        self.add_acquire_pattern(AcquirePattern {
            function_name: "fs.open".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "fs.openSync".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Database connections
        self.add_acquire_pattern(AcquirePattern {
            function_name: "createConnection".to_string(),
            resource_type: ResourceType::DatabaseConnection,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "connect".to_string(),
            resource_type: ResourceType::DatabaseConnection,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Release patterns
        for func in &["close", "closeSync", "end", "destroy", "release"] {
            self.add_release_pattern(ReleasePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::FileHandle,
                language: lang.clone(),
            });
        }
    }

    fn register_c_cpp_patterns(&mut self) {
        // C patterns
        let c_lang = "c".to_string();

        self.add_acquire_pattern(AcquirePattern {
            function_name: "fopen".to_string(),
            resource_type: ResourceType::FileHandle,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: c_lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "malloc".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: c_lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "calloc".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: c_lang.clone(),
        });

        self.add_acquire_pattern(AcquirePattern {
            function_name: "realloc".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: c_lang.clone(),
        });

        self.add_release_pattern(ReleasePattern {
            function_name: "fclose".to_string(),
            resource_type: ResourceType::FileHandle,
            language: c_lang.clone(),
        });

        self.add_release_pattern(ReleasePattern {
            function_name: "free".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            language: c_lang,
        });

        // C++ patterns
        let cpp_lang = "cpp".to_string();

        self.add_acquire_pattern(AcquirePattern {
            function_name: "new".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: cpp_lang.clone(),
        });

        // Smart pointers are RAII
        for func in &["make_unique", "make_shared", "unique_ptr", "shared_ptr"] {
            self.add_acquire_pattern(AcquirePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::MemoryAllocation,
                is_context_manager: false,
                is_raii: true,
                uses_defer: false,
                language: cpp_lang.clone(),
            });
        }

        self.add_release_pattern(ReleasePattern {
            function_name: "delete".to_string(),
            resource_type: ResourceType::MemoryAllocation,
            language: cpp_lang,
        });
    }

    fn register_java_patterns(&mut self) {
        let lang = "java".to_string();

        // File operations
        for func in &[
            "FileInputStream",
            "FileOutputStream",
            "FileReader",
            "FileWriter",
            "BufferedReader",
            "BufferedWriter",
        ] {
            self.add_acquire_pattern(AcquirePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::FileHandle,
                is_context_manager: false,
                is_raii: false,
                uses_defer: false,
                language: lang.clone(),
            });
        }

        // Database connections
        self.add_acquire_pattern(AcquirePattern {
            function_name: "DriverManager.getConnection".to_string(),
            resource_type: ResourceType::DatabaseConnection,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Locks
        self.add_acquire_pattern(AcquirePattern {
            function_name: "lock".to_string(),
            resource_type: ResourceType::Lock,
            is_context_manager: false,
            is_raii: false,
            uses_defer: false,
            language: lang.clone(),
        });

        // Release patterns
        for func in &["close", "release", "unlock", "dispose"] {
            self.add_release_pattern(ReleasePattern {
                function_name: (*func).to_string(),
                resource_type: ResourceType::FileHandle,
                language: lang.clone(),
            });
        }
    }

    fn add_acquire_pattern(&mut self, pattern: AcquirePattern) {
        self.acquire_patterns
            .entry(pattern.language.clone())
            .or_default()
            .push(pattern);
    }

    fn add_release_pattern(&mut self, pattern: ReleasePattern) {
        self.release_patterns
            .entry(pattern.language.clone())
            .or_default()
            .push(pattern);
    }

    /// Get acquire patterns for a language.
    #[must_use]
    pub fn get_acquire_patterns(&self, language: &str) -> &[AcquirePattern] {
        self.acquire_patterns
            .get(language)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Get release patterns for a language.
    #[must_use]
    pub fn get_release_patterns(&self, language: &str) -> &[ReleasePattern] {
        self.release_patterns
            .get(language)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Check if a function call is an acquire operation.
    #[must_use]
    pub fn is_acquire(&self, language: &str, func_name: &str) -> Option<&AcquirePattern> {
        self.get_acquire_patterns(language)
            .iter()
            .find(|p| func_name.contains(&p.function_name) || p.function_name.contains(func_name))
    }

    /// Check if a function call is a release operation.
    #[must_use]
    pub fn is_release(&self, language: &str, func_name: &str) -> Option<&ReleasePattern> {
        self.get_release_patterns(language)
            .iter()
            .find(|p| func_name.contains(&p.function_name) || p.function_name.contains(func_name))
    }
}

// =============================================================================
// RESOURCE FLOW ANALYZER
// =============================================================================

/// Resource state at a specific program point.
#[derive(Debug, Clone)]
struct ResourceStateMap {
    /// Resource variable -> state
    states: HashMap<String, ResourceState>,
}

impl ResourceStateMap {
    fn new() -> Self {
        Self {
            states: HashMap::new(),
        }
    }

    fn get(&self, variable: &str) -> ResourceState {
        self.states
            .get(variable)
            .copied()
            .unwrap_or(ResourceState::Unacquired)
    }

    fn set(&mut self, variable: String, state: ResourceState) {
        self.states.insert(variable, state);
    }

    fn merge(&self, other: &Self) -> Self {
        let mut merged = Self::new();

        // Collect all variables from both maps
        let all_vars: HashSet<_> = self.states.keys().chain(other.states.keys()).collect();

        for var in all_vars {
            let state1 = self.get(var);
            let state2 = other.get(var);

            let merged_state = match (state1, state2) {
                // Same state in both paths
                (s1, s2) if s1 == s2 => s1,
                // One path acquired, other didn't -> potential leak on some path
                (ResourceState::Acquired, ResourceState::Unacquired)
                | (ResourceState::Unacquired, ResourceState::Acquired) => ResourceState::Unknown,
                // One path released, other acquired -> potential leak
                (ResourceState::Acquired, ResourceState::Released)
                | (ResourceState::Released, ResourceState::Acquired) => ResourceState::Unknown,
                // Any path with double-free propagates
                (ResourceState::DoubleFree, _) | (_, ResourceState::DoubleFree) => {
                    ResourceState::DoubleFree
                }
                // Any path with leak propagates
                (ResourceState::Leaked, _) | (_, ResourceState::Leaked) => ResourceState::Leaked,
                // Unknown merges with anything
                (ResourceState::Unknown, _) | (_, ResourceState::Unknown) => ResourceState::Unknown,
                // Default to unknown for any other combination
                _ => ResourceState::Unknown,
            };

            merged.set(var.clone(), merged_state);
        }

        merged
    }
}

/// Analyzer for resource flow.
pub struct ResourceFlowAnalyzer {
    /// Pattern registry for acquire/release detection
    pattern_registry: PatternRegistry,
    /// Language being analyzed
    language: String,
    /// Maximum path depth for analysis
    max_path_depth: usize,
}

impl ResourceFlowAnalyzer {
    /// Create a new analyzer for the given language.
    #[must_use]
    pub fn new(language: impl Into<String>) -> Self {
        Self {
            pattern_registry: PatternRegistry::new(),
            language: language.into(),
            max_path_depth: 1000,
        }
    }

    /// Set maximum path depth for analysis.
    #[must_use]
    pub fn with_max_path_depth(mut self, depth: usize) -> Self {
        self.max_path_depth = depth;
        self
    }

    /// Analyze resource flow in a CFG.
    pub fn analyze(&self, cfg: &CFGInfo, file: &str, source: &str) -> Result<ResourceFlowAnalysis> {
        let start = std::time::Instant::now();
        let source_lines: Vec<&str> = source.lines().collect();

        // Extract resources from CFG blocks
        let resources = self.extract_resources(cfg, file, &source_lines);

        // Detect safe patterns (context managers, RAII, defer)
        let safe_patterns = self.detect_safe_patterns(cfg, file, &source_lines);

        // Track which resources are safely managed
        let safely_managed_vars: HashSet<String> =
            safe_patterns.iter().map(|p| p.variable.clone()).collect();

        // Perform path-sensitive analysis
        let (leaks, double_releases, use_after_release, paths_analyzed) =
            self.analyze_paths(cfg, &resources, &safely_managed_vars, file, &source_lines);

        // Build statistics
        let stats = AnalysisStats {
            total_resources: resources.len(),
            properly_released: resources
                .iter()
                .filter(|r| r.state == ResourceState::Released)
                .count(),
            leaked: leaks.len(),
            double_releases: double_releases.len(),
            use_after_release: use_after_release.len(),
            safely_managed: safe_patterns.len(),
            paths_analyzed,
            analysis_time_ms: start.elapsed().as_millis() as u64,
        };

        Ok(ResourceFlowAnalysis {
            file: file.to_string(),
            function_name: cfg.function_name.clone(),
            resources,
            leaks,
            double_releases,
            use_after_release,
            stats,
            safe_patterns,
        })
    }

    /// Extract resources from CFG blocks.
    fn extract_resources(&self, cfg: &CFGInfo, file: &str, source_lines: &[&str]) -> Vec<Resource> {
        let mut resources = Vec::new();
        let mut resource_id = 0;

        for block in cfg.blocks.values() {
            for statement in &block.statements {
                // Check for acquire patterns
                if let Some(pattern) = self.pattern_registry.is_acquire(&self.language, statement) {
                    // Extract variable name from assignment
                    if let Some(var_name) = self.extract_variable_name(statement) {
                        let snippet = source_lines
                            .get(block.start_line.saturating_sub(1))
                            .map(|s| s.trim().to_string());

                        let resource = Resource {
                            id: resource_id,
                            resource_type: pattern.resource_type.clone(),
                            variable: var_name,
                            acquire_location: Location {
                                file: file.to_string(),
                                line: block.start_line,
                                column: None,
                                snippet,
                            },
                            release_locations: Vec::new(),
                            state: ResourceState::Acquired,
                            scope_level: 0,
                            is_managed: pattern.is_raii || pattern.is_context_manager,
                            acquire_expression: Some(statement.clone()),
                        };

                        resources.push(resource);
                        resource_id += 1;
                    }
                }
            }

            // Check function calls for acquire patterns
            for func_call in &block.func_calls {
                if let Some(pattern) = self.pattern_registry.is_acquire(&self.language, func_call) {
                    let snippet = source_lines
                        .get(block.start_line.saturating_sub(1))
                        .map(|s| s.trim().to_string());

                    // Try to find the variable from the statement or use a synthetic name
                    let var_name = format!("resource_{}", resource_id);

                    let resource = Resource {
                        id: resource_id,
                        resource_type: pattern.resource_type.clone(),
                        variable: var_name,
                        acquire_location: Location {
                            file: file.to_string(),
                            line: block.start_line,
                            column: None,
                            snippet,
                        },
                        release_locations: Vec::new(),
                        state: ResourceState::Acquired,
                        scope_level: 0,
                        is_managed: pattern.is_raii || pattern.is_context_manager,
                        acquire_expression: Some(func_call.clone()),
                    };

                    resources.push(resource);
                    resource_id += 1;
                }
            }
        }

        resources
    }

    /// Extract variable name from an assignment statement.
    fn extract_variable_name(&self, statement: &str) -> Option<String> {
        // Handle common assignment patterns:
        // Python/JS: "var = func()"
        // Rust: "let var = func()"
        // Go: "var := func()" or "var, err := func()"

        let trimmed = statement.trim();

        // Rust let binding
        if trimmed.starts_with("let ") {
            let rest = &trimmed[4..];
            if let Some(eq_pos) = rest.find('=') {
                let var_part = rest[..eq_pos].trim();
                // Handle "let mut var" or "let var: Type"
                let var = var_part
                    .strip_prefix("mut ")
                    .unwrap_or(var_part)
                    .split(':')
                    .next()
                    .map(str::trim)?;
                return Some(var.to_string());
            }
        }

        // Go short declaration
        if let Some(pos) = trimmed.find(":=") {
            let var_part = trimmed[..pos].trim();
            // Handle "var, err := func()"
            let var = var_part.split(',').next().map(str::trim)?;
            return Some(var.to_string());
        }

        // Simple assignment
        if let Some(pos) = trimmed.find('=') {
            // Avoid compound operators like +=, -=, etc.
            if pos > 0
                && !matches!(
                    trimmed.chars().nth(pos - 1),
                    Some('+' | '-' | '*' | '/' | '!' | '<' | '>' | '&' | '|')
                )
            {
                let var_part = trimmed[..pos].trim();
                // Handle "const var" or "var var" declarations
                let var = var_part.split_whitespace().last()?;
                return Some(var.to_string());
            }
        }

        None
    }

    /// Detect safe resource management patterns.
    fn detect_safe_patterns(
        &self,
        cfg: &CFGInfo,
        file: &str,
        source_lines: &[&str],
    ) -> Vec<SafePattern> {
        let mut patterns = Vec::new();

        for block in cfg.blocks.values() {
            // Check for Python with blocks
            if matches!(block.block_type, BlockType::AsyncWithBlock) {
                for statement in &block.statements {
                    if statement.contains("with ") || statement.contains("async with ") {
                        if let Some(var) = self.extract_context_manager_var(statement) {
                            let snippet = source_lines
                                .get(block.start_line.saturating_sub(1))
                                .map(|s| s.trim().to_string());

                            patterns.push(SafePattern {
                                pattern_type: SafePatternType::ContextManager,
                                location: Location {
                                    file: file.to_string(),
                                    line: block.start_line,
                                    column: None,
                                    snippet,
                                },
                                variable: var,
                                description: "Python context manager ensures automatic cleanup"
                                    .to_string(),
                            });
                        }
                    }
                }
            }

            // Check for Go defer patterns
            if matches!(block.block_type, BlockType::DeferredCall) {
                for statement in &block.statements {
                    if statement.contains("defer ") {
                        if let Some(var) = self.extract_defer_var(statement) {
                            let snippet = source_lines
                                .get(block.start_line.saturating_sub(1))
                                .map(|s| s.trim().to_string());

                            patterns.push(SafePattern {
                                pattern_type: SafePatternType::Defer,
                                location: Location {
                                    file: file.to_string(),
                                    line: block.start_line,
                                    column: None,
                                    snippet,
                                },
                                variable: var,
                                description: "Go defer ensures cleanup on function exit"
                                    .to_string(),
                            });
                        }
                    }
                }
            }

            // Check for RAII patterns in Rust
            if self.language == "rust" {
                for func_call in &block.func_calls {
                    if let Some(pattern) = self.pattern_registry.is_acquire("rust", func_call) {
                        if pattern.is_raii {
                            let snippet = source_lines
                                .get(block.start_line.saturating_sub(1))
                                .map(|s| s.trim().to_string());

                            patterns.push(SafePattern {
                                pattern_type: SafePatternType::Raii,
                                location: Location {
                                    file: file.to_string(),
                                    line: block.start_line,
                                    column: None,
                                    snippet,
                                },
                                variable: format!("raii_{}", block.start_line),
                                description: "Rust RAII ensures automatic cleanup via Drop"
                                    .to_string(),
                            });
                        }
                    }
                }
            }

            // Check for C++ smart pointers
            if self.language == "cpp" {
                for func_call in &block.func_calls {
                    if func_call.contains("unique_ptr")
                        || func_call.contains("shared_ptr")
                        || func_call.contains("make_unique")
                        || func_call.contains("make_shared")
                    {
                        let snippet = source_lines
                            .get(block.start_line.saturating_sub(1))
                            .map(|s| s.trim().to_string());

                        patterns.push(SafePattern {
                            pattern_type: SafePatternType::SmartPointer,
                            location: Location {
                                file: file.to_string(),
                                line: block.start_line,
                                column: None,
                                snippet,
                            },
                            variable: format!("smart_ptr_{}", block.start_line),
                            description: "C++ smart pointer ensures automatic cleanup".to_string(),
                        });
                    }
                }
            }
        }

        patterns
    }

    /// Extract variable from Python context manager statement.
    fn extract_context_manager_var(&self, statement: &str) -> Option<String> {
        // "with open('file') as f:" -> "f"
        // "with lock:" -> "lock"
        if let Some(as_pos) = statement.find(" as ") {
            let after_as = &statement[as_pos + 4..];
            let var = after_as.split(':').next()?.trim();
            return Some(var.to_string());
        }

        // No "as" clause - extract the context manager expression
        let with_pos = statement.find("with ")?;
        let rest = &statement[with_pos + 5..];
        let var = rest.split(':').next()?.trim();
        Some(var.to_string())
    }

    /// Extract variable from Go defer statement.
    fn extract_defer_var(&self, statement: &str) -> Option<String> {
        // "defer file.Close()" -> "file"
        let defer_pos = statement.find("defer ")?;
        let rest = &statement[defer_pos + 6..];

        // Find the object being called
        if let Some(dot_pos) = rest.find('.') {
            let var = rest[..dot_pos].trim();
            return Some(var.to_string());
        }

        None
    }

    /// Perform path-sensitive analysis.
    fn analyze_paths(
        &self,
        cfg: &CFGInfo,
        resources: &[Resource],
        safely_managed: &HashSet<String>,
        file: &str,
        source_lines: &[&str],
    ) -> (
        Vec<ResourceLeak>,
        Vec<DoubleRelease>,
        Vec<UseAfterRelease>,
        usize,
    ) {
        let mut leaks = Vec::new();
        let mut double_releases = Vec::new();
        let mut use_after_release = Vec::new();

        // Build resource variable set
        let resource_vars: HashMap<&str, &Resource> =
            resources.iter().map(|r| (r.variable.as_str(), r)).collect();

        // Track state at each block
        let mut block_states: HashMap<BlockId, ResourceStateMap> = HashMap::new();

        // Initialize entry block
        block_states.insert(cfg.entry, ResourceStateMap::new());

        // Topological order for forward analysis
        let order = cfg.topological_order();
        let mut paths_analyzed = 0;

        // Forward dataflow analysis
        for block_id in &order {
            let block = match cfg.blocks.get(block_id) {
                Some(b) => b,
                None => continue,
            };

            // Get incoming states from predecessors
            let predecessors = cfg.predecessors(*block_id);
            let incoming_state = if predecessors.is_empty() {
                ResourceStateMap::new()
            } else {
                let mut merged = block_states
                    .get(&predecessors[0])
                    .cloned()
                    .unwrap_or_else(ResourceStateMap::new);

                for pred in &predecessors[1..] {
                    if let Some(pred_state) = block_states.get(pred) {
                        merged = merged.merge(pred_state);
                    }
                }
                merged
            };

            // Process block
            let mut current_state = incoming_state;

            // Check statements for acquire/release
            for statement in &block.statements {
                paths_analyzed += 1;

                // Check for acquire
                if self
                    .pattern_registry
                    .is_acquire(&self.language, statement)
                    .is_some()
                {
                    if let Some(var) = self.extract_variable_name(statement) {
                        current_state.set(var, ResourceState::Acquired);
                    }
                }

                // Check for release
                if let Some(_pattern) = self.pattern_registry.is_release(&self.language, statement)
                {
                    // Find which variable is being released
                    for (var, resource) in &resource_vars {
                        if statement.contains(*var) {
                            let prev_state = current_state.get(var);

                            match prev_state {
                                ResourceState::Released => {
                                    // Double release!
                                    let snippet = source_lines
                                        .get(block.start_line.saturating_sub(1))
                                        .map(|s| s.trim().to_string());

                                    double_releases.push(DoubleRelease {
                                        resource: (*resource).clone(),
                                        first_release: resource
                                            .release_locations
                                            .first()
                                            .cloned()
                                            .unwrap_or_else(|| {
                                                Location::new(file, block.start_line)
                                            }),
                                        second_release: Location {
                                            file: file.to_string(),
                                            line: block.start_line,
                                            column: None,
                                            snippet,
                                        },
                                        path: vec![],
                                    });

                                    current_state
                                        .set((*var).to_string(), ResourceState::DoubleFree);
                                }
                                ResourceState::Acquired => {
                                    current_state.set((*var).to_string(), ResourceState::Released);
                                }
                                _ => {}
                            }
                        }
                    }
                }

                // Check for use after release
                for (var, resource) in &resource_vars {
                    if statement.contains(*var) {
                        let state = current_state.get(var);
                        if state == ResourceState::Released {
                            // Check if this is a release operation itself
                            if self
                                .pattern_registry
                                .is_release(&self.language, statement)
                                .is_none()
                            {
                                let snippet = source_lines
                                    .get(block.start_line.saturating_sub(1))
                                    .map(|s| s.trim().to_string());

                                use_after_release.push(UseAfterRelease {
                                    resource: (*resource).clone(),
                                    release_location: resource
                                        .release_locations
                                        .first()
                                        .cloned()
                                        .unwrap_or_else(|| Location::new(file, block.start_line)),
                                    use_location: Location {
                                        file: file.to_string(),
                                        line: block.start_line,
                                        column: None,
                                        snippet,
                                    },
                                    operation: statement.clone(),
                                });
                            }
                        }
                    }
                }
            }

            // Check func_calls for release
            for func_call in &block.func_calls {
                if self
                    .pattern_registry
                    .is_release(&self.language, func_call)
                    .is_some()
                {
                    for (var, _) in &resource_vars {
                        if func_call.contains(*var) {
                            let prev_state = current_state.get(var);
                            if prev_state == ResourceState::Acquired {
                                current_state.set((*var).to_string(), ResourceState::Released);
                            }
                        }
                    }
                }
            }

            block_states.insert(*block_id, current_state);
        }

        // Check for leaks at exit blocks
        for exit_id in &cfg.exits {
            if let Some(exit_state) = block_states.get(exit_id) {
                for (var, resource) in &resource_vars {
                    // Skip safely managed resources
                    if safely_managed.contains(*var) {
                        continue;
                    }

                    // Skip RAII resources
                    if resource.is_managed {
                        continue;
                    }

                    let state = exit_state.get(var);
                    if state == ResourceState::Acquired {
                        let severity = match resource.resource_type {
                            ResourceType::Lock => LeakSeverity::Critical,
                            ResourceType::DatabaseConnection => LeakSeverity::High,
                            ResourceType::FileHandle | ResourceType::NetworkSocket => {
                                LeakSeverity::Medium
                            }
                            ResourceType::MemoryAllocation => LeakSeverity::High,
                            _ => LeakSeverity::Medium,
                        };

                        let suggestion = self.generate_leak_suggestion(resource);

                        leaks.push(ResourceLeak {
                            resource: (*resource).clone(),
                            leak_paths: vec![vec![resource.acquire_location.clone()]],
                            severity,
                            suggestion,
                        });
                    }
                }
            }
        }

        (leaks, double_releases, use_after_release, paths_analyzed)
    }

    /// Generate a suggestion for fixing a leak.
    fn generate_leak_suggestion(&self, resource: &Resource) -> String {
        match self.language.as_str() {
            "python" => format!(
                "Use a context manager: `with {} as {}:` to ensure automatic cleanup",
                resource.acquire_expression.as_deref().unwrap_or("resource"),
                resource.variable
            ),
            "rust" => {
                "Rust uses RAII; ensure the resource is dropped at the correct scope".to_string()
            }
            "go" => format!(
                "Add `defer {}.Close()` immediately after acquiring the resource",
                resource.variable
            ),
            "javascript" | "typescript" => format!(
                "Use try/finally or add `{}.close()` in a finally block",
                resource.variable
            ),
            "java" => format!(
                "Use try-with-resources: `try ({} {} = ...) {{ }}`",
                resource.resource_type, resource.variable
            ),
            "c" => format!(
                "Add `fclose({})` or `free({})` before function return",
                resource.variable, resource.variable
            ),
            "cpp" => format!(
                "Use RAII wrapper or smart pointer instead of raw `{}`",
                resource.variable
            ),
            _ => format!("Ensure `{}` is properly released", resource.variable),
        }
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Analyze resource flow in a source file.
///
/// # Arguments
/// * `file_path` - Path to the source file
/// * `function_name` - Name of the function to analyze
/// * `language` - Programming language (auto-detected if None)
///
/// # Returns
/// * `ResourceFlowAnalysis` containing detected issues and statistics
pub fn analyze_resource_flow(
    file_path: &Path,
    function_name: &str,
    language: Option<&str>,
) -> Result<ResourceFlowAnalysis> {
    use crate::lang::registry::LanguageRegistry;

    // Read source file
    let source =
        std::fs::read_to_string(file_path).map_err(|e| BrrrError::io_with_path(e, file_path))?;

    // Detect language
    let registry = LanguageRegistry::global();
    let lang = match language {
        Some(l) => l.to_string(),
        None => match registry.detect_language(file_path) {
            Some(l) => l.name().to_string(),
            None => {
                return Err(BrrrError::UnsupportedLanguage(
                    file_path
                        .extension()
                        .and_then(|e| e.to_str())
                        .unwrap_or("unknown")
                        .to_string(),
                ))
            }
        },
    };

    // Get language handler
    let lang_handler = registry
        .get_by_name(&lang)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(lang.clone()))?;

    // Parse source
    let mut parser = lang_handler.parser()?;
    let tree = parser
        .parse(source.as_bytes(), None)
        .ok_or_else(|| BrrrError::Parse {
            file: file_path.display().to_string(),
            message: "Failed to parse source file".to_string(),
        })?;

    // Find the function
    let file_path_str = file_path.display().to_string();
    let root = tree.root_node();
    let mut cfg_opt = None;

    // Walk tree to find function
    let mut cursor = root.walk();
    let mut found = false;

    for node in root.children(&mut cursor) {
        if let Some(func_info) = lang_handler.extract_function(node, source.as_bytes()) {
            if func_info.name == function_name {
                cfg_opt = Some(lang_handler.build_cfg(node, source.as_bytes())?);
                found = true;
                break;
            }
        }
    }

    if !found {
        return Err(BrrrError::FunctionNotFound(function_name.to_string()));
    }

    let cfg = cfg_opt.ok_or_else(|| BrrrError::FunctionNotFound(function_name.to_string()))?;

    // Analyze resource flow
    let analyzer = ResourceFlowAnalyzer::new(&lang);
    analyzer.analyze(&cfg, &file_path_str, &source)
}

/// Analyze resource flow from source code directly.
pub fn analyze_resource_flow_from_source(
    source: &str,
    function_name: &str,
    language: &str,
    file_name: &str,
) -> Result<ResourceFlowAnalysis> {
    use crate::lang::registry::LanguageRegistry;

    let registry = LanguageRegistry::global();
    let lang_handler = registry
        .get_by_name(language)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(language.to_string()))?;

    // Parse source
    let mut parser = lang_handler.parser()?;
    let tree = parser
        .parse(source.as_bytes(), None)
        .ok_or_else(|| BrrrError::Parse {
            file: file_name.to_string(),
            message: "Failed to parse source".to_string(),
        })?;

    // Find the function
    let root = tree.root_node();
    let mut cfg_opt = None;
    let mut cursor = root.walk();

    for node in root.children(&mut cursor) {
        if let Some(func_info) = lang_handler.extract_function(node, source.as_bytes()) {
            if func_info.name == function_name {
                cfg_opt = Some(lang_handler.build_cfg(node, source.as_bytes())?);
                break;
            }
        }
    }

    let cfg = cfg_opt.ok_or_else(|| BrrrError::FunctionNotFound(function_name.to_string()))?;

    // Analyze resource flow
    let analyzer = ResourceFlowAnalyzer::new(language);
    analyzer.analyze(&cfg, file_name, source)
}

/// Format resource flow analysis as text.
pub fn format_resource_flow_text(analysis: &ResourceFlowAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Resource Flow Analysis: {}\n",
        analysis.function_name
    ));
    output.push_str(&format!("File: {}\n", analysis.file));
    output.push_str(&"=".repeat(60));
    output.push('\n');

    // Summary
    output.push_str("\nSUMMARY\n");
    output.push_str(&"-".repeat(40));
    output.push('\n');
    output.push_str(&format!(
        "  Total resources: {}\n",
        analysis.stats.total_resources
    ));
    output.push_str(&format!(
        "  Properly released: {}\n",
        analysis.stats.properly_released
    ));
    output.push_str(&format!(
        "  Safely managed (RAII/with/defer): {}\n",
        analysis.stats.safely_managed
    ));
    output.push_str(&format!("  Leaks detected: {}\n", analysis.stats.leaked));
    output.push_str(&format!(
        "  Double-release bugs: {}\n",
        analysis.stats.double_releases
    ));
    output.push_str(&format!(
        "  Use-after-release bugs: {}\n",
        analysis.stats.use_after_release
    ));
    output.push('\n');

    // Leaks
    if !analysis.leaks.is_empty() {
        output.push_str("RESOURCE LEAKS\n");
        output.push_str(&"-".repeat(40));
        output.push('\n');

        for leak in &analysis.leaks {
            output.push_str(&format!(
                "  [{}] {} `{}`\n",
                leak.severity.weight(),
                leak.resource.resource_type,
                leak.resource.variable
            ));
            output.push_str(&format!(
                "    Acquired at: {}\n",
                leak.resource.acquire_location
            ));
            if let Some(expr) = &leak.resource.acquire_expression {
                output.push_str(&format!("    Expression: {}\n", expr));
            }
            output.push_str(&format!("    Suggestion: {}\n", leak.suggestion));
            output.push('\n');
        }
    }

    // Double releases
    if !analysis.double_releases.is_empty() {
        output.push_str("DOUBLE-RELEASE BUGS\n");
        output.push_str(&"-".repeat(40));
        output.push('\n');

        for dr in &analysis.double_releases {
            output.push_str(&format!(
                "  {} `{}`\n",
                dr.resource.resource_type, dr.resource.variable
            ));
            output.push_str(&format!("    First release: {}\n", dr.first_release));
            output.push_str(&format!("    Second release: {}\n", dr.second_release));
            output.push('\n');
        }
    }

    // Use after release
    if !analysis.use_after_release.is_empty() {
        output.push_str("USE-AFTER-RELEASE BUGS\n");
        output.push_str(&"-".repeat(40));
        output.push('\n');

        for uar in &analysis.use_after_release {
            output.push_str(&format!(
                "  {} `{}`\n",
                uar.resource.resource_type, uar.resource.variable
            ));
            output.push_str(&format!("    Released at: {}\n", uar.release_location));
            output.push_str(&format!("    Used at: {}\n", uar.use_location));
            output.push_str(&format!("    Operation: {}\n", uar.operation));
            output.push('\n');
        }
    }

    // Safe patterns
    if !analysis.safe_patterns.is_empty() {
        output.push_str("SAFE PATTERNS DETECTED\n");
        output.push_str(&"-".repeat(40));
        output.push('\n');

        for pattern in &analysis.safe_patterns {
            output.push_str(&format!(
                "  {:?} at {}\n",
                pattern.pattern_type, pattern.location
            ));
            output.push_str(&format!("    Variable: {}\n", pattern.variable));
            output.push_str(&format!("    {}\n", pattern.description));
            output.push('\n');
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
    fn test_pattern_registry_python() {
        let registry = PatternRegistry::new();

        // Check acquire patterns
        assert!(registry.is_acquire("python", "open").is_some());
        assert!(registry.is_acquire("python", "connect").is_some());
        assert!(registry.is_acquire("python", "acquire").is_some());

        // Check release patterns
        assert!(registry.is_release("python", "close").is_some());
        assert!(registry.is_release("python", "release").is_some());
    }

    #[test]
    fn test_pattern_registry_rust() {
        let registry = PatternRegistry::new();

        // Check acquire patterns (RAII)
        let file_open = registry.is_acquire("rust", "File::open");
        assert!(file_open.is_some());
        assert!(file_open.unwrap().is_raii);

        let mutex_lock = registry.is_acquire("rust", "Mutex::lock");
        assert!(mutex_lock.is_some());
        assert!(mutex_lock.unwrap().is_raii);
    }

    #[test]
    fn test_pattern_registry_go() {
        let registry = PatternRegistry::new();

        assert!(registry.is_acquire("go", "os.Open").is_some());
        assert!(registry.is_release("go", "Close").is_some());
        assert!(registry.is_release("go", "Unlock").is_some());
    }

    #[test]
    fn test_extract_variable_name() {
        let analyzer = ResourceFlowAnalyzer::new("python");

        // Python assignment
        assert_eq!(
            analyzer.extract_variable_name("f = open('file.txt')"),
            Some("f".to_string())
        );

        // Rust let binding
        let rust_analyzer = ResourceFlowAnalyzer::new("rust");
        assert_eq!(
            rust_analyzer.extract_variable_name("let file = File::open(path)"),
            Some("file".to_string())
        );
        assert_eq!(
            rust_analyzer.extract_variable_name("let mut handle = File::create(path)"),
            Some("handle".to_string())
        );

        // Go short declaration
        let go_analyzer = ResourceFlowAnalyzer::new("go");
        assert_eq!(
            go_analyzer.extract_variable_name("file := os.Open(path)"),
            Some("file".to_string())
        );
        assert_eq!(
            go_analyzer.extract_variable_name("file, err := os.Open(path)"),
            Some("file".to_string())
        );
    }

    #[test]
    fn test_resource_state_merge() {
        let mut state1 = ResourceStateMap::new();
        state1.set("file".to_string(), ResourceState::Acquired);

        let mut state2 = ResourceStateMap::new();
        state2.set("file".to_string(), ResourceState::Released);

        let merged = state1.merge(&state2);

        // Different states should merge to Unknown
        assert_eq!(merged.get("file"), ResourceState::Unknown);
    }

    #[test]
    fn test_leak_severity_ordering() {
        assert!(LeakSeverity::Critical.weight() > LeakSeverity::High.weight());
        assert!(LeakSeverity::High.weight() > LeakSeverity::Medium.weight());
        assert!(LeakSeverity::Medium.weight() > LeakSeverity::Low.weight());
    }

    #[test]
    fn test_location_display() {
        let loc = Location::new("src/main.py", 42);
        assert_eq!(loc.to_string(), "src/main.py:42");

        let loc_with_col = loc.with_column(10);
        assert_eq!(loc_with_col.to_string(), "src/main.py:42:10");
    }

    #[test]
    fn test_resource_type_display() {
        assert_eq!(ResourceType::FileHandle.to_string(), "file_handle");
        assert_eq!(
            ResourceType::DatabaseConnection.to_string(),
            "database_connection"
        );
        assert_eq!(
            ResourceType::Custom("my_resource".to_string()).to_string(),
            "custom:my_resource"
        );
    }

    #[test]
    fn test_context_manager_var_extraction() {
        let analyzer = ResourceFlowAnalyzer::new("python");

        assert_eq!(
            analyzer.extract_context_manager_var("with open('file') as f:"),
            Some("f".to_string())
        );

        assert_eq!(
            analyzer.extract_context_manager_var("with lock:"),
            Some("lock".to_string())
        );
    }

    #[test]
    fn test_defer_var_extraction() {
        let analyzer = ResourceFlowAnalyzer::new("go");

        assert_eq!(
            analyzer.extract_defer_var("defer file.Close()"),
            Some("file".to_string())
        );

        assert_eq!(
            analyzer.extract_defer_var("defer mu.Unlock()"),
            Some("mu".to_string())
        );
    }

    // Integration test with actual CFG would require setting up the full
    // language infrastructure, which is tested in the CLI integration tests
}
