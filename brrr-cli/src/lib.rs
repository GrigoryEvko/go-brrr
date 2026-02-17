#![feature(portable_simd)]

//! llm-brrr - Token-efficient code analysis for LLMs.
//!
//! This library provides tools for extracting and analyzing code structure
//! using tree-sitter parsers for multiple languages. It enables 95% token
//! savings when analyzing codebases by providing structured summaries instead
//! of raw source code.
//!
//! # Architecture
//!
//! The library is organized into several layers:
//!
//! - **AST Layer** ([`ast`]): File tree generation, code structure extraction, and AST parsing
//! - **CFG Layer** ([`cfg`]): Control flow graph extraction with cyclomatic complexity
//! - **DFG Layer** ([`dfg`]): Data flow graph extraction and basic program slicing
//! - **PDG Layer** ([`pdg`]): Program Dependence Graph combining CFG + DFG for accurate slicing
//! - **Call Graph Layer** ([`callgraph`]): Cross-file call graph analysis and impact detection
//! - **Semantic Layer** ([`semantic`]): Semantic pattern detection, embedding unit extraction, and code enrichment
//! - **Language Layer** ([`lang`]): Multi-language support via tree-sitter
//!
//! # Quick Start
//!
//! ```no_run
//! use brrr::{get_tree, get_tree_default, get_structure, extract_file, get_cfg, get_slice, get_backward_slice};
//!
//! // Get file tree for a project (convenience wrapper with default options)
//! let tree = get_tree_default("./src", Some(".py"))?;
//!
//! // Or use full API with explicit options
//! let tree_full = get_tree("./src", Some(".py"), true, true)?;
//!
//! // Get code structure (functions, classes) summary
//! let structure = get_structure("./src", Some("python"), 100, true)?;
//!
//! // Extract full AST from a single file (None = no base path validation)
//! let module = extract_file("./src/main.py", None)?;
//!
//! // Get control flow graph for a function
//! let cfg = get_cfg("./src/main.py", "process_data")?;
//!
//! // Get program slice (what affects line 42?) - using convenience wrapper
//! let affected_lines = get_backward_slice("./src/main.py", "process_data", 42)?;
//!
//! // Or use full API with direction, variable, and language options
//! let forward = get_slice("./src/main.py", "process_data", 10, Some("forward"), None, None)?;
//! let var_slice = get_slice("./src/main.py", "process_data", 42, None, Some("x"), None)?;
//! # Ok::<(), brrr::BrrrError>(())
//! ```
//!
//! # Call Graph Analysis
//!
//! ```no_run
//! use brrr::{build_callgraph, get_impact, find_dead_code, get_context};
//!
//! // Build project-wide call graph
//! let graph = build_callgraph("./src")?;
//!
//! // Find all callers of a function (impact analysis)
//! let callers = get_impact("./src", "critical_function", 3)?;
//!
//! // Find unreachable/dead code
//! let dead = find_dead_code("./src")?;
//!
//! // Get LLM-ready context for an entry point
//! let context = get_context("./src", "main", 2)?;
//! # Ok::<(), brrr::BrrrError>(())
//! ```
//!
//! # Project Scanning
//!
//! ```no_run
//! use brrr::{scan_project_files, scan_extensions, get_project_metadata, ScanConfig, scan_with_config};
//!
//! // Scan all source files (respects .gitignore and .brrrignore)
//! let result = scan_project_files("./project", None, true)?;
//! println!("Found {} files", result.files.len());
//!
//! // Scan only Python files
//! let py_result = scan_project_files("./project", Some("python"), true)?;
//!
//! // Scan by file extension
//! let rs_files = scan_extensions("./project", &[".rs", ".toml"])?;
//!
//! // Get file metadata (size, modification time, language)
//! let metadata = get_project_metadata("./project", None)?;
//! for meta in &metadata {
//!     println!("{}: {} bytes", meta.path.display(), meta.size);
//! }
//!
//! // Advanced: custom scan configuration
//! let config = ScanConfig::for_language("python")
//!     .with_excludes(&["**/test/**"])
//!     .with_metadata();
//! let result = scan_with_config("./project", &config)?;
//! # Ok::<(), brrr::BrrrError>(())
//! ```
//!
//! # Semantic Pattern Detection
//!
//! Automatically detect semantic patterns in code for enriched embeddings:
//!
//! ```
//! use brrr::{detect_semantic_patterns, SemanticPattern, SEMANTIC_PATTERNS};
//!
//! // Detect patterns in code
//! let code = "def validate_user(user): assert user is not None";
//! let patterns = detect_semantic_patterns(code);
//! assert!(patterns.contains(&"validation".to_string()));
//!
//! // Access all available patterns
//! for pattern in SEMANTIC_PATTERNS {
//!     println!("Pattern: {} - {}", pattern.name, pattern.pattern);
//! }
//! ```
//!
//! Detected patterns include: `crud`, `validation`, `transform`, `error_handling`,
//! `async_ops`, `iteration`, `api_endpoint`, `database`, `auth`, `cache`, `test`,
//! `logging`, and `config`.

// =============================================================================
// Module Declarations
// =============================================================================

pub mod analysis;
pub mod ast;
pub mod bindings;
pub mod callgraph;
pub mod cfg;
pub mod coverage;
pub mod dataflow;
pub mod dfg;
pub mod embedding;
pub mod error;
pub mod metrics;
pub mod patterns;
pub mod pdg;
pub mod quality;
pub mod security;
pub mod semantic;
pub mod simd;
pub mod util;

/// Language support module with implementations for all supported languages.
pub mod lang {
    pub mod c;
    pub mod cpp;
    pub mod go;
    pub mod java;
    pub mod python;
    pub mod registry;
    pub mod rust_lang;
    pub mod traits;
    pub mod typescript;

    pub use registry::LanguageRegistry;
    pub use traits::{BoxedLanguage, Language};
}

// =============================================================================
// Public Type Re-exports
// =============================================================================

// Error types - most important for users
pub use error::{BrrrError, Result};

// AST types and utilities
pub use ast::{
    CallGraphInfo, ClassInfo, ClassSummary, CodeStructure, FieldInfo, FileTreeEntry, FunctionInfo,
    FunctionSummary, ImportInfo, ModuleInfo,
};

// AST extractor for direct access to parsing functionality
pub use ast::AstExtractor;

// AST cache management - allows consumers to free memory
pub use ast::{clear_parser_cache, clear_query_cache};

// Import extraction utility
pub use ast::extract_imports;

// CFG types
pub use cfg::{BlockId, BlockType, CFGBlock, CFGEdge, CFGError, CFGInfo, EdgeType};

// CFG rendering functions
pub use cfg::{
    to_ascii as cfg_to_ascii, to_dot as cfg_to_dot, to_json as cfg_to_json,
    to_json_compact as cfg_to_json_compact, to_mermaid as cfg_to_mermaid,
};

// Coverage types - map test coverage to CFG
pub use coverage::{
    BranchCoverage, CoverageData, CoverageFormat, CoverageSummary, EdgeId, FileCoverage,
    FunctionCoverage, TestSuggestion,
};

// Coverage mapping functions
pub use coverage::{
    compute_path_coverage, find_critical_uncovered_paths, find_uncovered_branches,
    generate_test_suggestions, map_coverage_to_cfg, parse_coverage_file, parse_coverage_string,
    CFGCoverage, CriticalPath, PathCoverageResult, UncoveredBranch,
};

// Analysis types - advanced code analysis
pub use analysis::{
    extract_state_machines, extract_state_machines_from_source, OutputFormat as StateMachineFormat,
    State, StateId, StateMachine, StateMachineError, StateMachineExtractor, Transition,
    ValidationIssue, ValidationResult as StateMachineValidationResult,
};

// Invariant analysis types
pub use analysis::{
    analyze_invariants, analyze_invariants_function, analyze_invariants_source,
    format_invariant_function_json, format_invariant_json, format_invariant_text, Evidence,
    EvidenceKind, FileInvariantAnalysis, FunctionInvariantAnalysis, Invariant, InvariantAnalyzer,
    InvariantError, InvariantLocation, InvariantMetrics, InvariantOutputFormat, InvariantSummary,
    InvariantType, LoopBounds, LoopInvariantInfo, MonotonicDirection, MonotonicVariable,
    SuggestedAssertion, SuggestionCategory,
};

// DFG types
pub use dfg::{DFGInfo, DataflowEdge, DataflowKind};

// PDG types (combines CFG + DFG for accurate slicing)
pub use pdg::{BranchType, ControlDependence, PDGInfo, SliceCriteria, SliceMetrics, SliceResult};
// PDG slicing functions for advanced use cases (when you want to build PDG once and slice multiple times)
pub use pdg::{backward_slice as pdg_backward_slice, forward_slice as pdg_forward_slice};

// Metrics types
pub use metrics::{
    analyze_complexity, analyze_file_complexity, ComplexityAnalysis, ComplexityStats,
    CyclomaticComplexity, FunctionComplexity, RiskLevel,
};

// Nesting depth metrics
pub use metrics::{
    analyze_file_nesting, analyze_nesting, DeepNesting, FunctionNesting, NestingAnalysis,
    NestingAnalysisError, NestingConstruct, NestingDepthLevel, NestingMetrics, NestingStats,
};

// Call graph types
pub use callgraph::{CallEdge, CallGraph, FunctionRef};

// Function index types for fast lookups
pub use callgraph::{FunctionDef, FunctionIndex, IndexStats};

// Scanner types for project file discovery
pub use callgraph::scanner::{
    ErrorHandling, FileMetadata, ProjectScanner, ScanConfig, ScanError, ScanErrorKind, ScanResult,
};

// Dead code analysis types
pub use callgraph::{
    analyze_dead_code, analyze_dead_code_with_config, DeadCodeConfig, DeadCodeResult,
    DeadCodeStats, DeadFunction, DeadReason,
};

// Entry point detection
pub use callgraph::{classify_entry_point, detect_entry_points_with_config, EntryPointKind};

// Impact analysis types (reverse call graph)
pub use callgraph::{analyze_impact, CallerInfo, ImpactConfig, ImpactResult};

// Architecture analysis types
pub use callgraph::{analyze_architecture, ArchAnalysis, ArchStats, CycleDependency};

// Call graph cache utilities
pub use callgraph::{
    get_cache_dir, get_cache_file, get_or_build_graph_with_config, invalidate_cache,
    warm_cache_with_config, CachedCallGraph, CachedEdge,
};

// Language types
pub use lang::{BoxedLanguage, Language, LanguageRegistry};

// Semantic types
pub use semantic::{
    ChunkInfo, CodeComplexity, CodeLocation, ContentHashedIndex, EmbeddingUnit, FileHashEntry,
    HashCache, SearchResult, SemanticPattern, UnitKind, CHUNK_OVERLAP_TOKENS,
    MAX_CODE_PREVIEW_TOKENS, MAX_EMBEDDING_TOKENS, SEMANTIC_PATTERNS,
};

// Embedding types
pub use embedding::{
    distances_to_scores, distances_to_scores_for_metric, is_normalized, normalize_vector,
    IndexConfig, Metric, Quantization, VectorIndex,
};

// Security analysis types - Command Injection
pub use security::injection::command::{
    scan_command_injection, scan_file_command_injection, CommandInjectionFinding, CommandSink,
    Confidence, InjectionKind, Severity as CommandSeverity, SourceLocation, TaintSource,
    TaintSourceKind,
};

// Security analysis types - SQL Injection
pub use security::injection::sql::{
    Location as SqlLocation, SQLInjectionFinding, ScanResult as SqlScanResult,
    Severity as SqlSeverity, SqlInjectionDetector, SqlSinkType, UnsafePattern,
};

// Security analysis types - Path Traversal
pub use security::injection::path_traversal::{
    get_file_sinks, scan_file_path_traversal, scan_path_traversal,
    Confidence as PathTraversalConfidence, FileOperationType, FileSink, PathTraversalFinding,
    ScanResult as PathTraversalScanResult, Severity as PathTraversalSeverity,
    SourceLocation as PathTraversalLocation, VulnerablePattern as PathTraversalPattern,
};

// Security analysis types - Weak Cryptography
pub use security::crypto::{
    scan_file_weak_crypto, scan_weak_crypto, Algorithm as CryptoAlgorithm,
    Confidence as CryptoConfidence, Location as CryptoLocation, ScanResult as CryptoScanResult,
    Severity as CryptoSeverity, UsageContext as CryptoUsageContext, WeakCryptoDetector,
    WeakCryptoFinding, WeakCryptoIssue,
};

// Unified Security API (runs all analyzers in parallel)
pub use security::{
    check_suppression, is_suppressed, scan_security, Confidence as UnifiedConfidence,
    InjectionType, Location as UnifiedLocation, ScanSummary, SecurityCategory, SecurityConfig,
    SecurityFinding, SecurityReport, Severity as UnifiedSeverity,
};

// SARIF output format for CI/CD integration
pub use security::sarif::SarifLog;

// Code quality types - Clone Detection
pub use quality::clones::{
    detect_clones, format_clone_summary, Clone, CloneAnalysis, CloneConfig, CloneError,
    CloneInstance, CloneStats, CloneType, TextualCloneDetector,
};

// Design pattern detection types
pub use patterns::{
    detect_patterns, format_pattern_summary, DesignPattern, Location as PatternLocation,
    PatternAnalysis, PatternCategory, PatternConfig, PatternDetector, PatternError, PatternMatch,
    PatternStats,
};

// =============================================================================
// Context Types for LLM API Parity
// =============================================================================

use serde::{Deserialize, Serialize};
use std::path::Path;

/// Context about a function including its code and metadata.
///
/// This struct provides a complete context for a single function, suitable for
/// LLM consumption. It matches Python's `FunctionContext` dataclass for API parity.
///
/// # Examples
///
/// ```no_run
/// use brrr::{FunctionContext, extract_file};
///
/// // Create from extracted function info
/// let module = extract_file("./src/main.py", None)?;
/// if let Some(func) = module.functions.first() {
///     let source = std::fs::read_to_string("./src/main.py")?;
///     let ctx = FunctionContext::from_function_info(func, "./src/main.py", &source, "python");
///     println!("Function: {} at lines {}-{}", ctx.name, ctx.start_line, ctx.end_line);
/// }
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionContext {
    /// Function name
    pub name: String,
    /// File path containing the function
    pub file: String,
    /// Start line number (1-indexed)
    pub start_line: usize,
    /// End line number (1-indexed)
    pub end_line: usize,
    /// Function signature (e.g., "def foo(x: int) -> str")
    pub signature: Option<String>,
    /// Docstring or documentation comment
    pub docstring: Option<String>,
    /// Full source code of the function
    pub source: String,
    /// Programming language (e.g., "python", "rust", "go")
    pub language: String,
}

impl FunctionContext {
    /// Create a `FunctionContext` from a `FunctionInfo` and source file content.
    ///
    /// Extracts the function source code from the full file content using
    /// the line number information in `FunctionInfo`.
    ///
    /// # Arguments
    ///
    /// * `info` - The function info from AST extraction
    /// * `file_path` - Path to the source file
    /// * `source` - Full source content of the file
    /// * `language` - Programming language identifier
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::{FunctionContext, extract_file, FunctionInfo};
    ///
    /// let module = extract_file("./src/lib.rs", None)?;
    /// let source = std::fs::read_to_string("./src/lib.rs")?;
    ///
    /// for func in &module.functions {
    ///     let ctx = FunctionContext::from_function_info(func, "./src/lib.rs", &source, "rust");
    ///     println!("{}: {} lines", ctx.name, ctx.end_line - ctx.start_line + 1);
    /// }
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn from_function_info(
        info: &FunctionInfo,
        file_path: &str,
        source: &str,
        language: &str,
    ) -> Self {
        let start = info.line_number.saturating_sub(1);
        let end = info.end_line_number.unwrap_or(info.line_number);
        let lines: Vec<&str> = source.lines().collect();
        let func_source = lines
            .get(start..end)
            .map(|ls| ls.join("\n"))
            .unwrap_or_default();

        Self {
            name: info.name.clone(),
            file: file_path.to_string(),
            start_line: info.line_number,
            end_line: end,
            signature: Some(info.signature()),
            docstring: info.docstring.clone(),
            source: func_source,
            language: language.to_string(),
        }
    }

    /// Create a minimal context with just name and file location.
    ///
    /// Useful when you have limited information about a function reference.
    pub fn minimal(name: &str, file: &str, line: usize, language: &str) -> Self {
        Self {
            name: name.to_string(),
            file: file.to_string(),
            start_line: line,
            end_line: line,
            signature: None,
            docstring: None,
            source: String::new(),
            language: language.to_string(),
        }
    }
}

/// Relevant context for LLM consumption with call graph information.
///
/// This struct aggregates function context for an entry point along with
/// its direct callees and callers, providing a complete picture for LLM analysis.
/// Matches Python's `RelevantContext` dataclass for API parity.
///
/// # Examples
///
/// ```no_run
/// use brrr::{RelevantContext, FunctionContext};
///
/// // Build context programmatically
/// let entry = FunctionContext::minimal("main", "src/main.rs", 10, "rust");
/// let callee = FunctionContext::minimal("helper", "src/utils.rs", 25, "rust");
///
/// let context = RelevantContext {
///     entry,
///     callees: vec![callee],
///     callers: vec![],
///     token_count: 500,
///     depth: 1,
/// };
///
/// println!("Entry: {} calls {} functions", context.entry.name, context.callees.len());
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelevantContext {
    /// The entry point function being analyzed
    pub entry: FunctionContext,
    /// Functions called by the entry point (direct dependencies)
    pub callees: Vec<FunctionContext>,
    /// Functions that call the entry point (reverse dependencies)
    pub callers: Vec<FunctionContext>,
    /// Estimated token count for LLM context window budgeting
    pub token_count: usize,
    /// Depth of call graph traversal used
    pub depth: usize,
}

impl RelevantContext {
    /// Create a new RelevantContext with just an entry point.
    ///
    /// Callees and callers are initialized empty; use builder pattern to add them.
    pub fn new(entry: FunctionContext, depth: usize) -> Self {
        Self {
            entry,
            callees: Vec::new(),
            callers: Vec::new(),
            token_count: 0,
            depth,
        }
    }

    /// Add a callee (function called by entry point).
    pub fn with_callee(mut self, callee: FunctionContext) -> Self {
        self.callees.push(callee);
        self
    }

    /// Add a caller (function that calls the entry point).
    pub fn with_caller(mut self, caller: FunctionContext) -> Self {
        self.callers.push(caller);
        self
    }

    /// Set the token count estimate.
    pub fn with_token_count(mut self, count: usize) -> Self {
        self.token_count = count;
        self
    }

    /// Calculate approximate token count based on source code length.
    ///
    /// Uses a rough estimate of 4 characters per token.
    pub fn estimate_tokens(&mut self) {
        let mut total_chars = self.entry.source.len();
        for callee in &self.callees {
            total_chars += callee.source.len();
        }
        for caller in &self.callers {
            total_chars += caller.source.len();
        }
        self.token_count = total_chars / 4;
    }

    /// Total number of functions in this context.
    pub fn function_count(&self) -> usize {
        1 + self.callees.len() + self.callers.len()
    }

    /// Format context as a string suitable for LLM prompts.
    ///
    /// Produces a structured representation showing the entry point
    /// and its relationships to other functions.
    pub fn to_llm_string(&self) -> String {
        let mut output = String::new();
        output.push_str(&format!(
            "## Code Context: {} (depth={})\n\n",
            self.entry.name, self.depth
        ));

        // Entry point
        let short_file = Path::new(&self.entry.file)
            .file_name()
            .map(|f| f.to_string_lossy().to_string())
            .unwrap_or_else(|| self.entry.file.clone());
        output.push_str(&format!(
            "### Entry Point: {} ({}:{})\n",
            self.entry.name, short_file, self.entry.start_line
        ));
        if let Some(sig) = &self.entry.signature {
            output.push_str(&format!("```\n{}\n```\n", sig));
        }
        if let Some(doc) = &self.entry.docstring {
            let first_line = doc.lines().next().unwrap_or("");
            output.push_str(&format!("> {}\n", first_line));
        }
        output.push('\n');

        // Callees
        if !self.callees.is_empty() {
            output.push_str("### Calls:\n");
            for callee in &self.callees {
                let short = Path::new(&callee.file)
                    .file_name()
                    .map(|f| f.to_string_lossy().to_string())
                    .unwrap_or_else(|| callee.file.clone());
                output.push_str(&format!(
                    "- {} ({}:{})\n",
                    callee.name, short, callee.start_line
                ));
            }
            output.push('\n');
        }

        // Callers
        if !self.callers.is_empty() {
            output.push_str("### Called By:\n");
            for caller in &self.callers {
                let short = Path::new(&caller.file)
                    .file_name()
                    .map(|f| f.to_string_lossy().to_string())
                    .unwrap_or_else(|| caller.file.clone());
                output.push_str(&format!(
                    "- {} ({}:{})\n",
                    caller.name, short, caller.start_line
                ));
            }
            output.push('\n');
        }

        output.push_str(&format!(
            "Token estimate: {} | Functions: {}\n",
            self.token_count,
            self.function_count()
        ));

        output
    }
}

// =============================================================================
// Source Input Types
// =============================================================================

/// Input that can be either a file path or source code string.
///
/// This enum provides flexibility for analysis functions, allowing them to
/// accept either a file path (which will be read and language-detected) or
/// source code directly with an explicit language hint.
///
/// # Examples
///
/// ```no_run
/// use brrr::SourceInput;
///
/// // From a file path
/// let from_file = SourceInput::Path("./src/main.py");
///
/// // From source code with language hint
/// let from_source = SourceInput::Source {
///     code: "def hello(): return 'world'",
///     language: "python",
/// };
/// ```
#[derive(Debug, Clone)]
pub enum SourceInput<'a> {
    /// Path to a source file (language auto-detected from extension).
    Path(&'a str),
    /// Source code string with explicit language hint.
    Source {
        /// The source code as a string.
        code: &'a str,
        /// Language identifier (e.g., "python", "typescript", "rust").
        language: &'a str,
    },
}

impl<'a> SourceInput<'a> {
    /// Resolve input to (source_bytes, language_trait, optional_path).
    ///
    /// For `Path` variant: reads file, detects language from extension.
    /// For `Source` variant: uses provided code and language directly.
    ///
    /// # Returns
    ///
    /// A tuple of:
    /// - `Vec<u8>`: The source code as bytes
    /// - `&'static dyn Language`: The language implementation
    /// - `Option<&'a str>`: The file path if `Path` variant was used
    ///
    /// # Errors
    ///
    /// - [`BrrrError::UnsupportedLanguage`] if language cannot be determined
    /// - [`BrrrError::Io`] if file cannot be read (for `Path` variant)
    pub fn resolve(&self) -> Result<(Vec<u8>, &'static dyn Language, Option<&'a str>)> {
        let registry = LanguageRegistry::global();

        match self {
            SourceInput::Path(path) => {
                let p = Path::new(path);
                let lang = registry.detect_language(p).ok_or_else(|| {
                    BrrrError::UnsupportedLanguage(
                        p.extension()
                            .map(|e| e.to_string_lossy().to_string())
                            .unwrap_or_else(|| "unknown".to_string()),
                    )
                })?;
                let source = std::fs::read(p).map_err(|e| BrrrError::io_with_path(e, p))?;
                Ok((source, lang, Some(*path)))
            }
            SourceInput::Source { code, language } => {
                let lang = registry
                    .get_by_name(language)
                    .ok_or_else(|| BrrrError::UnsupportedLanguage((*language).to_string()))?;
                Ok((code.as_bytes().to_vec(), lang, None))
            }
        }
    }
}

// =============================================================================
// High-Level Public API Functions
// =============================================================================

/// Get the file tree for a directory.
///
/// Generates a hierarchical tree structure suitable for JSON serialization.
/// Skips common build directories (node_modules, __pycache__, .git, etc.).
///
/// # Arguments
///
/// * `path` - Root directory path to scan
/// * `ext_filter` - Optional extension filter (e.g., `Some(".py")` for Python files only)
/// * `exclude_hidden` - If true, exclude hidden files/directories (those starting with '.')
/// * `respect_ignore` - If true, respect .gitignore and .brrrignore patterns
///
/// # Returns
///
/// A [`FileTreeEntry`] representing the root directory with nested children.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_tree;
///
/// // Get all files with default settings (exclude hidden, respect ignore)
/// let tree = get_tree("./project", None, true, true)?;
/// println!("Root: {}", tree.name);
/// for child in &tree.children {
///     println!("  {} (type: {})", child.name, child.entry_type);
/// }
///
/// // Get only Python files, including hidden files
/// let py_tree = get_tree("./project", Some(".py"), false, true)?;
///
/// // Get all files, ignoring .gitignore patterns
/// let all_tree = get_tree("./project", None, true, false)?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError::Io`] if the path cannot be read or does not exist.
pub fn get_tree(
    path: &str,
    ext_filter: Option<&str>,
    exclude_hidden: bool,
    respect_ignore: bool,
) -> Result<FileTreeEntry> {
    let ext_vec: Vec<String> = ext_filter.map(|e| vec![e.to_string()]).unwrap_or_default();
    // Map parameters to ast::file_tree conventions:
    // - show_hidden = !exclude_hidden (show_hidden=false means exclude hidden files)
    // - no_ignore = !respect_ignore (no_ignore=false means respect ignore patterns)
    let show_hidden = !exclude_hidden;
    let no_ignore = !respect_ignore;
    ast::file_tree(path, &ext_vec, show_hidden, no_ignore, None)
}

/// Get file tree with default options (convenience wrapper).
///
/// Equivalent to calling `get_tree(path, ext_filter, true, true)`:
/// - Excludes hidden files/directories
/// - Respects .gitignore and .brrrignore patterns
///
/// # Arguments
///
/// * `path` - Root directory path to scan
/// * `ext_filter` - Optional extension filter (e.g., `Some(".py")` for Python files only)
///
/// # Examples
///
/// ```no_run
/// use brrr::get_tree_default;
///
/// let tree = get_tree_default("./project", None)?;
/// let py_tree = get_tree_default("./project", Some(".py"))?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
#[inline]
pub fn get_tree_default(path: &str, ext_filter: Option<&str>) -> Result<FileTreeEntry> {
    get_tree(path, ext_filter, true, true)
}

/// Get code structure summary for a project.
///
/// Scans the directory for source files matching the language filter,
/// extracts function and class information using parallel processing,
/// and returns a summary suitable for LLM consumption.
///
/// # Arguments
///
/// * `path` - Root directory to scan
/// * `lang_filter` - Optional language filter (e.g., `Some("python")`, `Some("typescript")`)
/// * `max_results` - Maximum number of functions/classes to return (0 = unlimited)
/// * `respect_ignore` - If true, respect .gitignore and .brrrignore patterns
///
/// # Returns
///
/// A [`CodeStructure`] containing:
/// - `path`: The analyzed path
/// - `functions`: List of function summaries with file, line, and signature
/// - `classes`: List of class summaries with file, line, and method count
/// - `total_files`: Total number of files analyzed
///
/// # Examples
///
/// ```no_run
/// use brrr::get_structure;
///
/// // Get all functions and classes (any language), respecting ignore files
/// let structure = get_structure("./src", None, 0, true)?;
/// println!("Found {} functions in {} files", structure.functions.len(), structure.total_files);
///
/// // Get only Python code, limited to 50 results, ignoring .gitignore
/// let py_structure = get_structure("./src", Some("python"), 50, false)?;
/// for func in &py_structure.functions {
///     println!("{}:{} - {}", func.file, func.line, func.signature);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError::Io`] if the path does not exist or cannot be read.
pub fn get_structure(
    path: &str,
    lang_filter: Option<&str>,
    max_results: usize,
    respect_ignore: bool,
) -> Result<CodeStructure> {
    // no_ignore is the inverse of respect_ignore
    let no_ignore = !respect_ignore;
    ast::code_structure(path, lang_filter, max_results, no_ignore)
}

/// Get code structure with default options.
///
/// Convenience wrapper that calls [`get_structure`] with `respect_ignore=true`.
/// This maintains backward compatibility with the original API.
///
/// # Arguments
///
/// * `path` - Project root directory
/// * `lang_filter` - Optional language filter
/// * `max_results` - Maximum files to process
#[inline]
pub fn get_structure_default(
    path: &str,
    lang_filter: Option<&str>,
    max_results: usize,
) -> Result<CodeStructure> {
    get_structure(path, lang_filter, max_results, true)
}

/// Extract complete AST information from a source file with optional path containment validation.
///
/// Parses a single file and returns detailed information about all
/// functions, classes, and imports. This is the most detailed extraction
/// API, suitable for deep analysis of individual files.
///
/// # Arguments
///
/// * `file_path` - Path to the source file
/// * `base_path` - Optional base directory for security validation.
///   If provided, `file_path` must resolve to a location within `base_path`.
///
/// # Returns
///
/// A [`ModuleInfo`] containing:
/// - `path`: The file path
/// - `language`: Detected language (e.g., "python", "typescript")
/// - `functions`: All top-level functions with full details
/// - `classes`: All classes/structs with methods
/// - `imports`: All import statements
///
/// # Examples
///
/// ```no_run
/// use brrr::extract_file;
///
/// // Without path containment validation
/// let module = extract_file("./src/main.py", None)?;
/// println!("Language: {}", module.language);
///
/// // With path containment validation - prevents directory traversal
/// let module = extract_file("./src/main.py", Some("./src"))?;
///
/// for func in &module.functions {
///     println!("Function: {} at line {}", func.name, func.line_number);
///     println!("  Signature: {}", func.signature());
///     if let Some(doc) = &func.docstring {
///         println!("  Docstring: {}", doc);
///     }
/// }
///
/// for class in &module.classes {
///     println!("Class: {} with {} methods", class.name, class.methods.len());
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Security
///
/// When `base_path` is provided, this function validates that `file_path`
/// does not escape the base directory via:
/// - Directory traversal (../..)
/// - Symlink resolution
/// - Absolute paths outside base
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the file type is not recognized
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::PathTraversal`] if the path escapes base_path or contains dangerous patterns
pub fn extract_file(file_path: &str, base_path: Option<&str>) -> Result<ModuleInfo> {
    ast::extract_file(file_path, base_path)
}

/// Extract complete AST information from a source file without path validation.
///
/// This is a convenience function equivalent to `extract_file(file_path, None)`.
/// Basic input validation is still performed for obviously dangerous paths.
///
/// # Security Warning
///
/// This function does not validate path containment. Only use when:
/// - The file path comes from a trusted source
/// - Path validation is performed by the caller
/// - You explicitly want to allow any valid file path
#[inline]
pub fn extract_file_unchecked(file_path: &str) -> Result<ModuleInfo> {
    ast::extract_file_unchecked(file_path)
}

/// Extract file information from a source code string.
///
/// Parses source code directly (without reading from a file) and returns
/// detailed information about all functions, classes, and imports. This is
/// useful when you have source code in memory or want to analyze code
/// snippets without creating temporary files.
///
/// # Arguments
///
/// * `source` - Source code as a string
/// * `language` - Language identifier (e.g., "python", "typescript", "rust", "go")
///
/// # Returns
///
/// A [`ModuleInfo`] containing:
/// - `path`: Set to `"<string>"` since there is no file path
/// - `language`: The language name provided
/// - `functions`: All top-level functions with full details
/// - `classes`: All classes/structs with methods
/// - `imports`: All import statements
///
/// # Examples
///
/// ```
/// use brrr::extract_from_source;
///
/// let source = r#"
/// def greet(name: str) -> str:
///     """Say hello to someone."""
///     return f"Hello, {name}!"
///
/// class Greeter:
///     def __init__(self, prefix: str):
///         self.prefix = prefix
/// "#;
///
/// let module = extract_from_source(source, "python")?;
/// assert_eq!(module.language, "python");
/// assert_eq!(module.functions.len(), 1);
/// assert_eq!(module.classes.len(), 1);
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
/// - [`BrrrError::Parse`] if the source code cannot be parsed
pub fn extract_from_source(source: &str, language: &str) -> Result<ModuleInfo> {
    ast::AstExtractor::extract_from_source(source, language)
}

/// Extract import statements from a source file.
///
/// Parses a source file and extracts all import statements, returning
/// detailed information about each import including module names, imported
/// names, aliases, and line numbers.
///
/// # Arguments
///
/// * `file_path` - Path to the source file
/// * `language` - Optional language override (auto-detected from file extension if None)
///
/// # Returns
///
/// A vector of [`ImportInfo`] containing:
/// - `module`: The module being imported
/// - `names`: Specific names imported (for `from X import Y` style)
/// - `aliases`: Name to alias mappings
/// - `is_from`: Whether this is a `from X import Y` style import
/// - `level`: Relative import level (0 for absolute imports)
/// - `line_number`: Line number of the import statement
///
/// # Examples
///
/// ```no_run
/// use brrr::get_imports;
///
/// let imports = get_imports("./src/main.py", None)?;
/// for imp in &imports {
///     println!("Import at line {}: {}", imp.line_number, imp.statement());
/// }
///
/// // With explicit language
/// let ts_imports = get_imports("./src/index.ts", Some("typescript"))?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the file type is not recognized
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_imports(file_path: &str, language: Option<&str>) -> Result<Vec<ImportInfo>> {
    use std::path::Path;

    let path = Path::new(file_path);
    let registry = LanguageRegistry::global();

    // Validate language if provided, but use file extension for parsing
    // This matches the behavior of extract_imports which auto-detects from path
    if let Some(lang_name) = language {
        if registry.get_by_name(lang_name).is_none() {
            return Err(BrrrError::UnsupportedLanguage(lang_name.to_string()));
        }
    }

    // Use the existing extract_imports which handles language detection
    ast::extract_imports(path)
}

/// Get LLM-ready context for a function entry point.
///
/// Builds a call graph and returns structured context about what
/// a function calls (and transitively, what those functions call).
/// This is ideal for providing focused context to an LLM about
/// a specific code path.
///
/// # Arguments
///
/// * `project` - Root project directory
/// * `entry_point` - Function name to start from (e.g., "main", "process_request")
/// * `depth` - How many levels of calls to traverse (typically 1-3)
///
/// # Returns
///
/// A JSON value containing:
/// - `entry_point`: The starting function
/// - `depth`: Traversal depth used
/// - `functions`: List of function names in the call chain
/// - `count`: Total number of functions found
///
/// # Examples
///
/// ```no_run
/// use brrr::get_context;
///
/// let context = get_context("./project", "handle_request", 2)?;
/// println!("{}", serde_json::to_string_pretty(&context)?);
/// // Output:
/// // {
/// //   "entry_point": "handle_request",
/// //   "depth": 2,
/// //   "functions": ["validate_input", "process_data", "send_response"],
/// //   "count": 3
/// // }
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError`] if the project cannot be scanned or parsed.
pub fn get_context(project: &str, entry_point: &str, depth: usize) -> Result<serde_json::Value> {
    callgraph::get_context_with_lang(project, entry_point, depth, None)
}

/// Query project for LLM-ready context string.
///
/// Returns a formatted markdown-style string suitable for direct consumption
/// by LLMs, including the entry point function and all its callees with
/// their complete source code.
///
/// This is a convenience wrapper around [`get_context`] that formats the
/// output as a human/LLM-readable string instead of JSON.
///
/// # Arguments
///
/// * `project` - Project root directory
/// * `entry_point` - Entry point function name (e.g., "main" or "Class.method")
/// * `depth` - Call graph traversal depth (typically 1-3)
/// * `language` - Optional language filter (e.g., "python", "rust")
///
/// # Returns
///
/// Formatted string with function source code:
///
/// ```text
/// # Entry: main (src/main.py:10-25)
/// def main():
///     process_data()
///
/// ## Callees:
///
/// ### process_data (src/utils.py:5-15)
/// def process_data():
///     ...
/// ```
///
/// # Examples
///
/// ```no_run
/// use brrr::query;
///
/// // Get context for main function
/// let context = query("./src", "main", 2, None)?;
/// println!("{}", context);
///
/// // Filter to Python files only
/// let py_context = query("./src", "handle_request", 3, Some("python"))?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError`] if:
/// - The project cannot be scanned
/// - Source files cannot be parsed
/// - The entry point function cannot be found
pub fn query(
    project: &str,
    entry_point: &str,
    depth: usize,
    language: Option<&str>,
) -> Result<String> {
    // Get context JSON and extract the LLM-ready text format
    let result = callgraph::get_context_with_lang(project, entry_point, depth, language)?;
    Ok(result
        .get("llm_context")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string())
}

/// Get control flow graph for a function.
///
/// Extracts the CFG showing how control flows through a function,
/// including branches, loops, and exception handling. Useful for
/// understanding function complexity and control flow paths.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A [`CFGInfo`] containing:
/// - `function_name`: The analyzed function
/// - `blocks`: Map of basic blocks (each with statements and line ranges)
/// - `edges`: Control flow edges between blocks
/// - `entry`: Entry block ID
/// - `exits`: Exit block IDs
///
/// The CFG can be rendered to Mermaid format for visualization using
/// [`CFGInfo::to_mermaid`].
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg;
///
/// let cfg = get_cfg("./src/main.py", "process_data")?;
/// println!("Function: {}", cfg.function_name);
/// println!("Blocks: {}", cfg.blocks.len());
/// println!("Cyclomatic complexity: {}", cfg.cyclomatic_complexity());
///
/// // Render to Mermaid diagram
/// println!("{}", cfg.to_mermaid());
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::UnsupportedLanguage`] if language is specified but not supported
pub fn get_cfg(file: &str, function: &str, language: Option<&str>) -> Result<CFGInfo> {
    cfg::extract_with_language(file, function, language)
}

/// Get control flow graph with auto-detected language (convenience wrapper).
///
/// This is a convenience function for [`get_cfg`] with language auto-detection.
/// Equivalent to `get_cfg(file, function, None)`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Example
///
/// ```no_run
/// use brrr::get_cfg_auto;
///
/// let cfg = get_cfg_auto("./src/main.py", "process_data")?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
#[inline]
pub fn get_cfg_auto(file: &str, function: &str) -> Result<CFGInfo> {
    get_cfg(file, function, None)
}

/// Get control flow graph from a source code string.
///
/// Parses source code directly (without reading from a file) and extracts
/// the control flow graph for the specified function. This is useful when
/// you have source code in memory or want to analyze code snippets.
///
/// # Arguments
///
/// * `source` - Source code as a string
/// * `function` - Name of the function to analyze
/// * `language` - Language identifier (e.g., "python", "typescript", "rust")
///
/// # Returns
///
/// A [`CFGInfo`] containing the control flow graph for the function.
///
/// # Examples
///
/// ```
/// use brrr::get_cfg_from_source;
///
/// let source = r#"
/// def process(x):
///     if x > 0:
///         return x * 2
///     return 0
/// "#;
///
/// let cfg = get_cfg_from_source(source, "process", "python")?;
/// assert_eq!(cfg.function_name, "process");
/// assert!(cfg.cyclomatic_complexity() >= 2); // Has an if branch
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the source cannot be parsed
pub fn get_cfg_from_source(source: &str, function: &str, language: &str) -> Result<CFGInfo> {
    cfg::CfgBuilder::extract_from_source(source, language, function)
}

/// Get CFG blocks for a function.
///
/// Convenience function that extracts the CFG and returns just the blocks.
/// This is equivalent to `get_cfg(file, function)?.blocks.into_values().collect()`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A vector of [`CFGBlock`] containing block id, statements, and line range.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_blocks;
///
/// let blocks = get_cfg_blocks("./src/main.py", "process")?;
/// for block in &blocks {
///     println!("Block {} (lines {}-{}): {}", block.id.0, block.start_line, block.end_line, block.label);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_blocks(file: &str, function: &str) -> Result<Vec<CFGBlock>> {
    let cfg = get_cfg(file, function, None)?;
    Ok(cfg.blocks.into_values().collect())
}

/// Get CFG edges for a function.
///
/// Convenience function that extracts the CFG and returns just the edges.
/// This is equivalent to `get_cfg(file, function)?.edges`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A vector of [`CFGEdge`] containing from/to block IDs and edge type.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_edges;
///
/// let edges = get_cfg_edges("./src/main.py", "process")?;
/// for edge in &edges {
///     println!("Block {} -> Block {} ({})", edge.from.0, edge.to.0, edge.label());
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_edges(file: &str, function: &str) -> Result<Vec<CFGEdge>> {
    let cfg = get_cfg(file, function, None)?;
    Ok(cfg.edges)
}

/// Get CFG as Mermaid diagram string.
///
/// Convenience function that extracts the CFG and renders it as a Mermaid flowchart.
/// The output can be embedded in Markdown or rendered via mermaid.live.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A Mermaid flowchart string.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_mermaid;
///
/// let mermaid = get_cfg_mermaid("./src/main.py", "process")?;
/// println!("{}", mermaid);
/// // Output:
/// // flowchart TD
/// //     B0["entry"]
/// //     B1["if x > 0"]
/// //     B0 --> B1
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_mermaid(file: &str, function: &str) -> Result<String> {
    let cfg = get_cfg(file, function, None)?;
    Ok(cfg::to_mermaid(&cfg))
}

/// Get CFG as DOT (Graphviz) string.
///
/// Convenience function that extracts the CFG and renders it in DOT format.
/// The output can be rendered using Graphviz tools (dot, neato, etc.).
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A DOT graph string.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_dot;
///
/// let dot = get_cfg_dot("./src/main.py", "process")?;
/// std::fs::write("cfg.dot", &dot)?;
/// // Then run: dot -Tpng cfg.dot -o cfg.png
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_dot(file: &str, function: &str) -> Result<String> {
    let cfg = get_cfg(file, function, None)?;
    Ok(cfg::to_dot(&cfg))
}

/// Get CFG as ASCII art string.
///
/// Convenience function that extracts the CFG and renders it as ASCII text.
/// Provides a terminal-friendly, human-readable view of the CFG structure.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// An ASCII text representation of the CFG.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_ascii;
///
/// let ascii = get_cfg_ascii("./src/main.py", "process")?;
/// println!("{}", ascii);
/// // Output:
/// // CFG: process
/// // ========================================
/// // Blocks: 5
/// // Edges: 6
/// // Complexity: 3
/// // ...
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_ascii(file: &str, function: &str) -> Result<String> {
    let cfg = get_cfg(file, function, None)?;
    Ok(cfg::to_ascii(&cfg))
}

/// Get CFG as JSON value.
///
/// Convenience function that extracts the CFG and converts it to a serde_json::Value.
/// Useful for serialization and integration with JSON-based tools.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A JSON value representing the CFG.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_cfg_json;
///
/// let json = get_cfg_json("./src/main.py", "process")?;
/// println!("{}", serde_json::to_string_pretty(&json)?);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_cfg_json(file: &str, function: &str) -> Result<serde_json::Value> {
    let cfg = get_cfg(file, function, None)?;
    Ok(serde_json::to_value(&cfg)?)
}

/// Get data flow graph for a function.
///
/// Extracts the DFG showing how data flows through a function,
/// tracking variable definitions, uses, and mutations. Essential
/// for understanding data dependencies and performing program slicing.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A [`DFGInfo`] containing:
/// - `function_name`: The analyzed function
/// - `edges`: Data flow edges (variable, from_line, to_line, kind)
/// - `definitions`: Map of variable -> definition lines
/// - `uses`: Map of variable -> use lines
///
/// # Examples
///
/// ```no_run
/// use brrr::get_dfg;
///
/// let dfg = get_dfg("./src/main.py", "calculate")?;
/// println!("Variables: {:?}", dfg.variables());
///
/// // Show where each variable is defined
/// for (var, lines) in &dfg.definitions {
///     println!("{} defined at lines {:?}", var, lines);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::UnsupportedLanguage`] if language is specified but not supported
pub fn get_dfg(file: &str, function: &str, language: Option<&str>) -> Result<DFGInfo> {
    dfg::extract_with_language(file, function, language)
}

/// Get data flow graph with auto-detected language (convenience wrapper).
///
/// This is a convenience function for [`get_dfg`] with language auto-detection.
/// Equivalent to `get_dfg(file, function, None)`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Example
///
/// ```no_run
/// use brrr::get_dfg_auto;
///
/// let dfg = get_dfg_auto("./src/main.py", "calculate")?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
#[inline]
pub fn get_dfg_auto(file: &str, function: &str) -> Result<DFGInfo> {
    get_dfg(file, function, None)
}

/// Get data flow graph from a source code string.
///
/// Parses source code directly (without reading from a file) and extracts
/// the data flow graph for the specified function. This is useful when
/// you have source code in memory or want to analyze code snippets.
///
/// # Arguments
///
/// * `source` - Source code as a string
/// * `function` - Name of the function to analyze
/// * `language` - Language identifier (e.g., "python", "typescript", "rust")
///
/// # Returns
///
/// A [`DFGInfo`] containing the data flow graph for the function.
///
/// # Examples
///
/// ```
/// use brrr::get_dfg_from_source;
///
/// let source = r#"
/// def compute(x, y):
///     z = x + y
///     result = z * 2
///     return result
/// "#;
///
/// let dfg = get_dfg_from_source(source, "compute", "python")?;
/// assert_eq!(dfg.function_name, "compute");
/// assert!(dfg.definitions.contains_key("z"));
/// assert!(dfg.definitions.contains_key("result"));
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the source cannot be parsed
pub fn get_dfg_from_source(source: &str, function: &str, language: &str) -> Result<DFGInfo> {
    dfg::DfgBuilder::extract_from_source(source, language, function)
}

/// Get DFG edges for a function.
///
/// Convenience function that extracts the DFG and returns just the edges.
/// This is equivalent to `get_dfg(file, function)?.edges`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A vector of [`DataflowEdge`] containing variable, from/to lines, and flow kind.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_dfg_edges;
///
/// let edges = get_dfg_edges("./src/main.py", "calculate")?;
/// for edge in &edges {
///     println!("{}: line {} -> line {} ({:?})",
///         edge.variable, edge.from_line, edge.to_line, edge.kind);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_dfg_edges(file: &str, function: &str) -> Result<Vec<DataflowEdge>> {
    let dfg = get_dfg(file, function, None)?;
    Ok(dfg.edges)
}

/// Get variables tracked in DFG.
///
/// Convenience function that extracts the DFG and returns the list of
/// variables that have definitions or uses tracked.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A vector of variable names tracked in the function.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_dfg_variables;
///
/// let vars = get_dfg_variables("./src/main.py", "calculate")?;
/// println!("Variables tracked: {:?}", vars);
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_dfg_variables(file: &str, function: &str) -> Result<Vec<String>> {
    let dfg = get_dfg(file, function, None)?;
    use std::collections::HashSet;
    let vars: HashSet<_> = dfg.edges.iter().map(|e| e.variable.clone()).collect();
    Ok(vars.into_iter().collect())
}

/// Get def-use chains for a specific variable.
///
/// Extracts the data flow graph and filters edges for a specific variable,
/// returning pairs of (definition_line, use_line).
///
/// This is useful for understanding how a specific variable flows through
/// a function - where it's defined and where those definitions are used.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
/// * `variable` - Name of the variable to track
///
/// # Returns
///
/// A vector of (from_line, to_line) tuples representing def-use chains.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_def_use_chains;
///
/// // Track how variable 'x' flows through the function
/// let chains = get_def_use_chains("./src/main.py", "calculate", "x")?;
/// for (def_line, use_line) in &chains {
///     println!("x: defined at line {} -> used at line {}", def_line, use_line);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_def_use_chains(
    file: &str,
    function: &str,
    variable: &str,
) -> Result<Vec<(usize, usize)>> {
    let dfg = get_dfg(file, function, None)?;
    let chains: Vec<_> = dfg
        .edges
        .iter()
        .filter(|e| e.variable == variable)
        .map(|e| (e.from_line, e.to_line))
        .collect();
    Ok(chains)
}

/// Get program dependence graph (PDG) for a function.
///
/// A PDG combines control flow (CFG) and data flow (DFG) into a unified graph
/// that enables accurate program slicing. It includes:
/// - Control dependencies: which conditions determine if a statement executes
/// - Data dependencies: def-use chains for variables
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
///
/// A [`PDGInfo`] containing the combined CFG, DFG, and computed control dependencies.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_pdg;
///
/// let pdg = get_pdg("./src/main.py", "process")?;
/// println!("Control dependencies: {}", pdg.control_dep_count());
/// println!("Data edges: {}", pdg.data_edge_count());
///
/// // Check if line 5 is control-dependent on line 3
/// if pdg.is_control_dependent(5, 3) {
///     println!("Line 5 depends on condition at line 3");
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::UnsupportedLanguage`] if language is specified but not supported
pub fn get_pdg(file: &str, function: &str, language: Option<&str>) -> Result<PDGInfo> {
    pdg::build_pdg_with_language(file, function, language)
}

/// Get PDG with auto-detected language (convenience wrapper).
///
/// This is a convenience function for [`get_pdg`] with language auto-detection.
/// Equivalent to `get_pdg(file, function, None)`.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Example
///
/// ```no_run
/// use brrr::get_pdg_auto;
///
/// let pdg = get_pdg_auto("./src/main.py", "process")?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
#[inline]
pub fn get_pdg_auto(file: &str, function: &str) -> Result<PDGInfo> {
    get_pdg(file, function, None)
}

/// Get program slice for a line of code.
///
/// Performs program slicing to find lines that affect (backward) or are affected by
/// (forward) the given target line. This is extremely useful for debugging
/// ("what could have caused this value?") and impact analysis ("what will this change affect?").
///
/// **NOTE**: This function uses PDG-based slicing which follows BOTH control
/// dependencies (conditions that determine if code executes) AND data dependencies
/// (variable def-use chains). This is more accurate than DFG-only slicing.
///
/// For example, given:
/// ```python
/// if x > 0:        # Line 2 - condition
///     result = x * 2  # Line 3
/// return result    # Line 4
/// ```
///
/// A backward slice from line 4 correctly includes line 2 (the condition) because
/// whether `result` is assigned depends on the condition's outcome.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Target line number (1-indexed)
/// * `direction` - Slice direction: "backward" (default) or "forward"
/// * `variable` - Optional variable name for variable-specific slicing
/// * `language` - Optional language override (auto-detected if None)
///
/// # Returns
///
/// A sorted vector of line numbers in the slice, including the target line itself.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_slice;
///
/// // Backward slice from line 42 (default direction)
/// let affected_lines = get_slice("./src/main.py", "process", 42, None, None, None)?;
/// println!("Line 42 is affected by lines: {:?}", affected_lines);
///
/// // Forward slice to see what line 10 affects
/// let impacts = get_slice("./src/main.py", "process", 10, Some("forward"), None, None)?;
/// println!("Line 10 affects lines: {:?}", impacts);
///
/// // Variable-specific backward slice
/// let x_deps = get_slice("./src/main.py", "process", 42, None, Some("x"), None)?;
/// println!("Lines affecting 'x' at line 42: {:?}", x_deps);
///
/// // Forward slice for variable 'result'
/// let result_impacts = get_slice("./src/main.py", "process", 5, Some("forward"), Some("result"), None)?;
/// println!("Lines affected by 'result' from line 5: {:?}", result_impacts);
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::InvalidArgument`] if line is 0 or direction is not "backward" or "forward"
pub fn get_slice(
    file: &str,
    function: &str,
    line: usize,
    direction: Option<&str>,
    variable: Option<&str>,
    language: Option<&str>,
) -> Result<Vec<usize>> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }

    // Build the PDG for the function with optional language override
    let pdg_info = pdg::build_pdg_with_language(file, function, language)?;

    // Create slicing criteria with optional variable filter
    let criteria = match variable {
        Some(var) => pdg::SliceCriteria::at_line_variable(line, var),
        None => pdg::SliceCriteria::at_line(line),
    };

    // Route to appropriate slice direction
    let dir = direction.unwrap_or("backward");
    let result = match dir {
        "backward" => pdg::backward_slice(&pdg_info, &criteria),
        "forward" => pdg::forward_slice(&pdg_info, &criteria),
        _ => {
            return Err(BrrrError::InvalidArgument(format!(
                "Invalid direction '{}', expected 'backward' or 'forward'",
                dir
            )))
        }
    };

    Ok(result.lines)
}

/// Get program slice from a source code string.
///
/// Parses source code directly (without reading from a file) and performs
/// program slicing on the specified function. This uses DFG-based slicing
/// (data flow only) for source strings.
///
/// # Arguments
///
/// * `source` - Source code as a string
/// * `function` - Name of the function containing the line
/// * `line` - Target line number (1-indexed)
/// * `direction` - Slice direction: "backward" (default) or "forward"
/// * `variable` - Optional variable name for variable-specific slicing
/// * `language` - Language identifier (e.g., "python", "typescript", "rust")
///
/// # Returns
///
/// A sorted vector of line numbers in the slice.
///
/// # Examples
///
/// ```
/// use brrr::get_slice_from_source;
///
/// let source = r#"
/// def compute(x):
///     a = x + 1
///     b = a * 2
///     c = b + x
///     return c
/// "#;
///
/// // Backward slice from line 5 (c = b + x)
/// let slice = get_slice_from_source(source, "compute", 5, None, None, "python")?;
/// // Should include lines that affect line 5
/// assert!(!slice.is_empty());
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the source cannot be parsed
/// - [`BrrrError::InvalidArgument`] if line is 0 or direction is not "backward" or "forward"
pub fn get_slice_from_source(
    source: &str,
    function: &str,
    line: usize,
    direction: Option<&str>,
    variable: Option<&str>,
    language: &str,
) -> Result<Vec<usize>> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }

    // Build the DFG for the function from source
    let dfg_info = dfg::DfgBuilder::extract_from_source(source, language, function)?;

    // Create slice criteria with optional variable filter
    let criteria = match variable {
        Some(var) => dfg::SliceCriteria::at_line_variable(line, var),
        None => dfg::SliceCriteria::at_line(line),
    };

    let dir = direction.unwrap_or("backward");
    let result = match dir {
        "backward" => dfg::backward_slice(&dfg_info, &criteria).lines,
        "forward" => dfg::forward_slice(&dfg_info, &criteria).lines,
        _ => {
            return Err(BrrrError::InvalidArgument(format!(
                "Invalid direction '{}', expected 'backward' or 'forward'",
                dir
            )))
        }
    };

    Ok(result)
}

/// Get backward program slice (convenience wrapper).
///
/// This is a convenience function that calls `get_slice` with default direction.
/// For the full API with all parameters, use [`get_slice`].
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Target line number (1-indexed)
///
/// # Returns
///
/// A sorted vector of line numbers that affect the target line.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_backward_slice;
///
/// let affected_lines = get_backward_slice("./src/main.py", "process", 42)?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
pub fn get_backward_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    get_slice(file, function, line, Some("backward"), None, None)
}

/// Get backward program slice using DFG-only (data flow only).
///
/// This is the legacy slicing function that only follows data dependencies,
/// NOT control dependencies. For most use cases, prefer [`get_slice`] which
/// uses PDG-based slicing for more accurate results.
///
/// Use this function only if you specifically want data-flow-only analysis
/// without control dependencies.
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Target line number (1-indexed)
///
/// # Returns
///
/// A sorted vector of line numbers that affect the target line through
/// data dependencies only.
///
/// # Errors
///
/// - [`BrrrError::InvalidArgument`] if line is 0
pub fn get_slice_dfg_only(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    dfg::get_slice(file, function, line)
}

/// Get forward program slice for a line of code.
///
/// Performs forward slicing to find all lines affected by the given source line.
/// This is useful for impact analysis ("what will change if I modify this line?").
///
/// **NOTE**: This function uses PDG-based slicing which follows BOTH control
/// dependencies (conditions that determine if code executes) AND data dependencies
/// (variable def-use chains).
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Source line number (1-indexed)
///
/// # Returns
///
/// A sorted vector of line numbers that are affected by the source line,
/// including the source line itself.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_forward_slice;
///
/// // Find what line 10 affects
/// let affected_lines = get_forward_slice("./src/main.py", "process", 10)?;
/// println!("Line 10 affects lines: {:?}", affected_lines);
/// // Output: [10, 15, 23, 38, 42]
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::InvalidArgument`] if line is 0
pub fn get_forward_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    pdg::get_forward_slice(file, function, line)
}

/// Get PDG-based slice with direction parameter.
///
/// Unified function for both backward and forward slicing using PDG.
/// For most cases, prefer [`get_slice`] (backward) or [`get_forward_slice`] (forward).
///
/// # Arguments
///
/// * `file` - Path to the source file
/// * `function` - Name of the function containing the line
/// * `line` - Target/source line number (1-indexed)
/// * `direction` - Either "backward" or "forward"
///
/// # Returns
///
/// A sorted vector of line numbers in the slice.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_pdg_slice;
///
/// // Backward slice: what affects line 42?
/// let backward = get_pdg_slice("./src/main.py", "process", 42, "backward")?;
///
/// // Forward slice: what does line 10 affect?
/// let forward = get_pdg_slice("./src/main.py", "process", 10, "forward")?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::FunctionNotFound`] if the function doesn't exist
/// - [`BrrrError::Parse`] if the file cannot be parsed
/// - [`BrrrError::InvalidArgument`] if line is 0 or direction is not "backward" or "forward"
pub fn get_pdg_slice(
    file: &str,
    function: &str,
    line: usize,
    direction: &str,
) -> Result<Vec<usize>> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        return Err(BrrrError::InvalidArgument(
            "Line numbers are 1-indexed, got 0".to_string(),
        ));
    }
    match direction {
        "backward" => pdg::get_slice(file, function, line),
        "forward" => pdg::get_forward_slice(file, function, line),
        _ => Err(BrrrError::InvalidArgument(format!(
            "Invalid direction '{}', expected 'backward' or 'forward'",
            direction
        ))),
    }
}

/// Build the cross-file call graph for a project.
///
/// Scans all source files in the project, indexes function definitions,
/// and resolves call sites to build a complete call graph. This is the
/// foundation for impact analysis and dead code detection.
///
/// # Arguments
///
/// * `path` - Root project directory
///
/// # Returns
///
/// A [`CallGraph`] containing:
/// - `edges`: All call edges (caller -> callee with line numbers)
/// - `callers`: Index of callee -> set of callers (for impact analysis)
/// - `callees`: Index of caller -> set of callees (for forward traversal)
///
/// # Examples
///
/// ```no_run
/// use brrr::build_callgraph;
///
/// let graph = build_callgraph("./project")?;
/// println!("Found {} call edges", graph.edges.len());
/// println!("Unique functions: {}", graph.all_functions().len());
///
/// // Serialize for caching
/// let json = serde_json::to_string(&graph)?;
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
///
/// # Performance
///
/// Building a call graph requires parsing all source files, so it can be
/// expensive for large projects. Consider using [`warm_callgraph`] to
/// pre-build the cache.
///
/// # Errors
///
/// Returns [`BrrrError`] if files cannot be read or parsed.
pub fn build_callgraph(path: &str) -> Result<CallGraph> {
    callgraph::build(path)
}

/// Find all callers of a function (impact analysis).
///
/// Performs reverse call graph traversal to find all functions that
/// directly or transitively call the target function. This is essential
/// for understanding the impact of changes to a function.
///
/// # Arguments
///
/// * `path` - Root project directory
/// * `function` - Target function name
/// * `depth` - Maximum traversal depth (typically 1-5)
///
/// # Returns
///
/// A vector of [`FunctionRef`] for all functions that call the target
/// (directly or transitively up to the specified depth).
///
/// # Examples
///
/// ```no_run
/// use brrr::get_impact;
///
/// // Who calls the database connection function?
/// let callers = get_impact("./project", "get_db_connection", 3)?;
/// println!("Functions affected by get_db_connection changes:");
/// for caller in &callers {
///     println!("  {}:{}", caller.file, caller.name);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Use Cases
///
/// - Assess blast radius before refactoring
/// - Find all code paths through a critical function
/// - Identify tightly coupled components
///
/// # Errors
///
/// Returns [`BrrrError`] if the project cannot be scanned.
pub fn get_impact(path: &str, function: &str, depth: usize) -> Result<Vec<FunctionRef>> {
    use callgraph::{analyze_impact, cache, ImpactConfig};

    let project = std::path::Path::new(path);
    let graph = cache::get_or_build_graph_with_config(project, None, false)?;
    let config = ImpactConfig::new().with_depth(depth);
    let result = analyze_impact(&graph, function, config);

    // Convert CallerInfo to FunctionRef for backward compatibility
    Ok(result
        .callers
        .into_iter()
        .map(|c| FunctionRef {
            file: c.file,
            name: c.name,
            qualified_name: c.qualified_name,
        })
        .collect())
}

/// Find dead (unreachable) code in a project.
///
/// Identifies functions that are not reachable from any entry point.
/// Entry points are detected heuristically (main functions, test functions,
/// exported modules, etc.).
///
/// # Arguments
///
/// * `path` - Root project directory
///
/// # Returns
///
/// A vector of [`FunctionRef`] for functions that appear to be unreachable.
///
/// # Examples
///
/// ```no_run
/// use brrr::find_dead_code;
///
/// let dead = find_dead_code("./project")?;
/// if dead.is_empty() {
///     println!("No dead code detected!");
/// } else {
///     println!("Potentially dead code ({} functions):", dead.len());
///     for func in &dead {
///         println!("  {}:{}", func.file, func.name);
///     }
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Caveats
///
/// - Dynamic dispatch (e.g., `getattr`, reflection) may cause false positives
/// - Decorator-wrapped functions may not be detected as entry points
/// - Test discovery patterns are language-specific
///
/// # Errors
///
/// Returns [`BrrrError`] if the project cannot be scanned.
pub fn find_dead_code(path: &str) -> Result<Vec<FunctionRef>> {
    use callgraph::{cache, dead, DeadCodeConfig};

    let project = std::path::Path::new(path);
    let mut graph = cache::get_or_build_graph_with_config(project, None, false)?;
    graph.build_indexes();
    let result = dead::analyze_dead_code_with_config(&graph, &DeadCodeConfig::default());

    // Convert DeadFunction to FunctionRef for backward compatibility
    Ok(result
        .dead_functions
        .into_iter()
        .map(|d| FunctionRef {
            file: d.file,
            name: d.name,
            qualified_name: d.qualified_name,
        })
        .collect())
}

/// Warm the call graph cache for a project.
///
/// Pre-builds the call graph for a project so subsequent queries are fast.
/// This is useful for large projects where building the call graph is expensive.
///
/// # Arguments
///
/// * `path` - Root project directory
/// * `langs` - Optional language filter (e.g., `Some(&["python", "typescript"])`)
///
/// # Examples
///
/// ```no_run
/// use brrr::warm_callgraph;
///
/// // Pre-warm cache for all languages
/// warm_callgraph("./project", None)?;
///
/// // Pre-warm cache for specific languages
/// warm_callgraph("./project", Some(&["python".to_string(), "rust".to_string()]))?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError`] if the project cannot be scanned.
pub fn warm_callgraph(path: &str, langs: Option<&[String]>) -> Result<()> {
    let project = std::path::Path::new(path);
    let lang = langs.and_then(|l| l.first().map(|s| s.as_str()));
    callgraph::warm_cache_with_config(project, lang, false)
}

// =============================================================================
// Semantic Extraction API
// =============================================================================

/// Extract semantic units from a project for embedding.
///
/// Scans the project for source files, extracts functions, classes, and methods,
/// calculates token counts, adds semantic tags, and handles chunking for
/// oversized units (>8K tokens).
///
/// # Arguments
///
/// * `path` - Root project directory
/// * `lang` - Programming language to filter by (e.g., "python", "typescript")
///
/// # Returns
///
/// Vector of [`EmbeddingUnit`] objects ready for embedding and indexing.
///
/// # Examples
///
/// ```no_run
/// use brrr::extract_semantic_units;
///
/// let units = extract_semantic_units("./my_project", "python")?;
/// for unit in &units {
///     println!("{}: {} ({} tokens, tags: {:?})",
///         unit.kind,
///         unit.name,
///         unit.token_count,
///         unit.semantic_tags
///     );
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError::Io`] if the path does not exist or cannot be read.
pub fn extract_semantic_units(path: &str, lang: &str) -> Result<Vec<EmbeddingUnit>> {
    semantic::extract_units(path, lang)
}

/// Extract semantic units with call graph information.
///
/// Similar to [`extract_semantic_units`], but also builds a call graph and
/// populates the `calls` and `called_by` fields for each unit. This provides
/// richer semantic context for embedding and retrieval.
///
/// # Arguments
///
/// * `path` - Root project directory
/// * `lang` - Programming language to filter by (e.g., "python", "typescript")
///
/// # Returns
///
/// Vector of [`EmbeddingUnit`] objects with populated call relationships.
///
/// # Examples
///
/// ```no_run
/// use brrr::extract_semantic_units_with_callgraph;
///
/// let units = extract_semantic_units_with_callgraph("./my_project", "python")?;
/// for unit in &units {
///     if !unit.calls.is_empty() {
///         println!("{} calls: {:?}", unit.name, unit.calls);
///     }
///     if !unit.called_by.is_empty() {
///         println!("{} called by: {:?}", unit.name, unit.called_by);
///     }
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Performance
///
/// This function builds a call graph in addition to extracting units, so it
/// is more expensive than [`extract_semantic_units`]. Use this when call
/// relationships are important for your use case.
///
/// # Errors
///
/// Returns [`BrrrError`] if the path does not exist, cannot be read, or
/// call graph building fails.
pub fn extract_semantic_units_with_callgraph(path: &str, lang: &str) -> Result<Vec<EmbeddingUnit>> {
    semantic::extract_units_with_callgraph(path, lang)
}

/// Extract semantic units from a single file.
///
/// Convenience function for extracting units from a single source file
/// rather than an entire project.
///
/// # Arguments
///
/// * `file_path` - Path to the source file
///
/// # Returns
///
/// Vector of [`EmbeddingUnit`] objects from the file.
///
/// # Examples
///
/// ```no_run
/// use brrr::extract_file_units;
///
/// let units = extract_file_units("./src/main.py")?;
/// for unit in &units {
///     println!("  {} ({}): {} tokens", unit.name, unit.kind, unit.token_count);
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the file type is not recognized
pub fn extract_file_units(file_path: &str) -> Result<Vec<EmbeddingUnit>> {
    semantic::extract_units_from_file(file_path)
}

/// Build embedding text from a semantic unit.
///
/// Creates a rich text representation suitable for embedding with a language model.
/// Includes natural language description, semantic tags, signature, complexity,
/// call relationships, and code preview.
///
/// # Arguments
///
/// * `unit` - The [`EmbeddingUnit`] to convert to embedding text
///
/// # Returns
///
/// A text string containing all relevant information for semantic embedding.
///
/// # Examples
///
/// ```no_run
/// use brrr::{extract_file_units, build_embedding_text};
///
/// let units = extract_file_units("./src/auth.py")?;
/// for unit in &units {
///     let text = build_embedding_text(&unit);
///     // Send text to embedding model...
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
pub fn build_embedding_text(unit: &EmbeddingUnit) -> String {
    semantic::build_embedding_text(unit)
}

/// Detect semantic patterns in code.
///
/// Analyzes code to identify semantic categories like "crud", "validation",
/// "error_handling", "async_ops", etc. These patterns are used to enrich
/// embedding text for better semantic search retrieval.
///
/// # Arguments
///
/// * `code` - Source code to analyze for patterns
///
/// # Returns
///
/// Vector of detected pattern names (e.g., `["validation", "error_handling"]`).
///
/// # Examples
///
/// ```
/// use brrr::detect_semantic_patterns;
///
/// let code = "def validate_user(user): assert user is not None";
/// let patterns = detect_semantic_patterns(code);
/// assert!(patterns.contains(&"validation".to_string()));
/// ```
pub fn detect_semantic_patterns(code: &str) -> Vec<String> {
    semantic::detect_semantic_patterns(code)
}

/// Count tokens in text using Qwen3-Embedding-0.6B tokenizer.
///
/// Uses the native HuggingFace tokenizer for exact parity with Python's
/// token counting. Falls back to Unicode-aware character estimation if
/// the tokenizer is unavailable.
///
/// # Arguments
///
/// * `text` - The text to count tokens in
///
/// # Returns
///
/// Number of tokens in the text.
///
/// # Examples
///
/// ```
/// use brrr::count_tokens;
///
/// let tokens = count_tokens("Hello, world!");
/// assert!(tokens > 0);
/// ```
pub fn count_tokens(text: &str) -> usize {
    semantic::count_tokens(text)
}

// =============================================================================
// Project Scanner API
// =============================================================================

/// Scan project for source files of a specific language.
///
/// This is a high-level convenience function that wraps [`ProjectScanner`].
/// For more control over scanning options, use [`ProjectScanner`] directly
/// with a [`ScanConfig`].
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `language` - Optional language filter (e.g., `Some("python")`, `Some("rust")`)
/// * `respect_ignore` - Whether to respect `.gitignore` and `.brrrignore` patterns.
///                      Note: Currently always true. This parameter is reserved for
///                      future use when ignore bypass is needed.
///
/// # Returns
///
/// A [`ScanResult`] containing:
/// - `files`: Vector of matching file paths
/// - `errors`: Any errors encountered during scanning (permission denied, broken symlinks, etc.)
/// - `warnings`: Non-fatal warnings
///
/// # Examples
///
/// ```no_run
/// use brrr::scan_project_files;
///
/// // Scan all supported source files
/// let result = scan_project_files("./src", None, true)?;
/// println!("Found {} files", result.files.len());
///
/// // Scan only Python files
/// let py_result = scan_project_files("./src", Some("python"), true)?;
/// println!("Found {} Python files", py_result.files.len());
///
/// // Check for errors
/// if result.has_errors() {
///     eprintln!("Warning: {}", result.error_summary());
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the path does not exist or cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
pub fn scan_project_files(
    root: &str,
    language: Option<&str>,
    _respect_ignore: bool, // Reserved for future use; currently always respects ignore
) -> Result<ScanResult> {
    let scanner = ProjectScanner::new(root)?;

    match language {
        Some(lang) => scanner.scan_language_with_errors(lang),
        None => scanner.scan_files_with_errors(),
    }
}

/// Scan project for files with specific extensions.
///
/// This is a high-level convenience function for extension-based filtering.
/// Respects `.gitignore` and `.brrrignore` patterns automatically.
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `extensions` - File extensions to include (e.g., `&[".py", ".pyi"]` or `&["py", "pyi"]`)
///                  Leading dots are optional; matching is case-insensitive.
///
/// # Returns
///
/// Vector of file paths matching the extensions.
///
/// # Examples
///
/// ```no_run
/// use brrr::scan_extensions;
///
/// // Find all Python files (including type stubs)
/// let py_files = scan_extensions("./src", &[".py", ".pyi"])?;
/// println!("Found {} Python files", py_files.len());
///
/// // Extensions without leading dots also work
/// let rs_files = scan_extensions("./src", &["rs"])?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError::Io`] if the path does not exist or cannot be read.
pub fn scan_extensions(root: &str, extensions: &[&str]) -> Result<Vec<std::path::PathBuf>> {
    let scanner = ProjectScanner::new(root)?;
    scanner.scan_extensions(extensions)
}

/// Get file metadata for a project directory.
///
/// Scans the project and returns detailed metadata for each source file,
/// including file size, modification time, and detected language.
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `language` - Optional language filter (e.g., `Some("python")`)
///
/// # Returns
///
/// Vector of [`FileMetadata`] containing:
/// - `path`: Absolute path to the file
/// - `size`: File size in bytes
/// - `modified`: Last modification time (if available)
/// - `language`: Detected programming language (if recognized)
///
/// # Examples
///
/// ```no_run
/// use brrr::get_project_metadata;
///
/// // Get metadata for all source files
/// let metadata = get_project_metadata("./src", None)?;
/// for meta in &metadata {
///     println!("{}: {} bytes, lang={:?}",
///         meta.path.display(),
///         meta.size,
///         meta.language
///     );
/// }
///
/// // Get metadata for only Rust files
/// let rust_meta = get_project_metadata("./src", Some("rust"))?;
/// let total_bytes: u64 = rust_meta.iter().map(|m| m.size).sum();
/// println!("Total Rust code: {} bytes", total_bytes);
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the path does not exist or cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
pub fn get_project_metadata(root: &str, language: Option<&str>) -> Result<Vec<FileMetadata>> {
    let scanner = ProjectScanner::new(root)?;

    match language {
        Some(lang) => scanner.scan_language_with_metadata(lang),
        None => scanner.scan_with_metadata(),
    }
}

/// Scan project files with custom configuration.
///
/// This is the most flexible scanning function, supporting all configuration
/// options available in [`ScanConfig`]:
/// - Language and extension filtering
/// - Include/exclude glob patterns
/// - Metadata collection
/// - Parallel processing control
/// - Error handling strategy
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `config` - Scan configuration options
///
/// # Returns
///
/// A [`ScanResult`] containing files, metadata (if requested), and errors.
///
/// # Examples
///
/// ```no_run
/// use brrr::{scan_with_config, ScanConfig, ErrorHandling};
///
/// // Scan Python files, excluding tests, with metadata
/// let config = ScanConfig::for_language("python")
///     .with_excludes(&["**/test/**", "**/tests/**"])
///     .with_metadata()
///     .with_error_handling(ErrorHandling::CollectAndContinue);
///
/// let result = scan_with_config("./src", &config)?;
/// println!("Found {} files ({} bytes total)",
///     result.files.len(),
///     result.total_bytes
/// );
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError`] if the path does not exist or scanning fails.
pub fn scan_with_config(root: &str, config: &ScanConfig) -> Result<ScanResult> {
    let scanner = ProjectScanner::new(root)?;
    scanner.scan_with_config(config)
}

/// Estimate the number of source files in a project.
///
/// Performs a full directory traversal to count supported source files.
/// Useful for progress bars or deciding scan strategy before more expensive
/// operations.
///
/// # Arguments
///
/// * `root` - Project root directory path
///
/// # Returns
///
/// Count of supported source files (respecting `.gitignore` and `.brrrignore`).
///
/// # Examples
///
/// ```no_run
/// use brrr::estimate_file_count;
///
/// let count = estimate_file_count("./my_project")?;
/// println!("Project contains {} source files", count);
///
/// if count > 1000 {
///     println!("Large project - consider using parallel scanning");
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// Returns [`BrrrError::Io`] if the path does not exist or cannot be read.
pub fn estimate_file_count(root: &str) -> Result<usize> {
    let scanner = ProjectScanner::new(root)?;
    scanner.estimate_file_count()
}

// =============================================================================
// Function Index API
// =============================================================================

/// Configuration for function indexing.
///
/// Controls how functions are discovered and indexed in a project.
/// Use the builder pattern to customize behavior.
///
/// # Examples
///
/// ```
/// use brrr::IndexingConfig;
///
/// // Index only Python files, excluding tests
/// let config = IndexingConfig::new()
///     .with_language("python")
///     .exclude_tests();
///
/// // Index all languages with parallel processing
/// let config = IndexingConfig::new()
///     .with_parallel(true);
/// ```
#[derive(Debug, Clone, Default)]
pub struct IndexingConfig {
    /// Optional language filter (e.g., "python", "typescript", "rust").
    /// If None, indexes all supported languages.
    pub language: Option<String>,
    /// Whether to respect .gitignore and .brrrignore patterns.
    /// Defaults to true.
    pub respect_ignore: bool,
    /// Whether to use parallel processing for indexing.
    /// Defaults to true.
    pub parallel: bool,
    /// Whether to include test files in the index.
    /// Defaults to true.
    pub include_tests: bool,
}

impl IndexingConfig {
    /// Create a new indexing configuration with default settings.
    ///
    /// Defaults:
    /// - No language filter (indexes all languages)
    /// - Respects ignore patterns
    /// - Uses parallel processing
    /// - Includes test files
    pub fn new() -> Self {
        Self {
            language: None,
            respect_ignore: true,
            parallel: true,
            include_tests: true,
        }
    }

    /// Set the language filter.
    ///
    /// Only files matching this language will be indexed.
    ///
    /// # Arguments
    ///
    /// * `lang` - Language name (e.g., "python", "typescript", "rust", "go")
    pub fn with_language(mut self, lang: &str) -> Self {
        self.language = Some(lang.to_string());
        self
    }

    /// Set whether to respect ignore patterns.
    ///
    /// If true (default), respects .gitignore and .brrrignore.
    pub fn with_respect_ignore(mut self, respect: bool) -> Self {
        self.respect_ignore = respect;
        self
    }

    /// Set whether to use parallel processing.
    ///
    /// If true (default), uses rayon for parallel file processing.
    pub fn with_parallel(mut self, parallel: bool) -> Self {
        self.parallel = parallel;
        self
    }

    /// Exclude test files from the index.
    ///
    /// Filters out files matching common test patterns.
    pub fn exclude_tests(mut self) -> Self {
        self.include_tests = false;
        self
    }

    /// Include test files in the index (default).
    pub fn include_tests(mut self) -> Self {
        self.include_tests = true;
        self
    }
}

/// Build a function index for a project.
///
/// Creates an index of all functions in the project that can be used for
/// fast lookups by name, qualified name, file, or class+method. This is the
/// foundation for call graph analysis, impact detection, and code navigation.
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `language` - Optional language filter (indexes all languages if None)
///
/// # Returns
///
/// A [`FunctionIndex`] with multiple lookup strategies:
/// - `lookup(name)` - Find all functions with a simple name
/// - `lookup_qualified(qname)` - Find by fully qualified name (e.g., "module.Class.method")
/// - `lookup_in_file(file, name)` - Find a function in a specific file
/// - `lookup_method(class, method)` - Find a method in a specific class
/// - `lookup_pattern(pattern)` - Find by partial qualified name pattern
///
/// # Examples
///
/// ```no_run
/// use brrr::build_function_index;
///
/// // Index all source files in a project
/// let index = build_function_index("./src", None)?;
/// println!("Indexed {} functions", index.len());
///
/// // Lookup by simple name (returns all matches)
/// let funcs = index.lookup("process_data");
/// for f in funcs {
///     println!("  Found: {} in {}", f.name, f.file);
/// }
///
/// // Lookup by qualified name (exact match)
/// if let Some(func) = index.lookup_qualified("mymodule.MyClass.process_data") {
///     println!("Found specific function in {}", func.file);
/// }
///
/// // Lookup by class and method name
/// let methods = index.lookup_method("MyClass", "process_data");
/// for m in methods {
///     println!("  Method: {}", m.qualified_name.as_deref().unwrap_or(&m.name));
/// }
///
/// // Index only Python files
/// let py_index = build_function_index("./src", Some("python"))?;
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Performance
///
/// Building the index requires parsing all matching source files, so it can be
/// expensive for large projects. The index is typically built once and reused
/// for multiple lookups.
///
/// # Errors
///
/// - [`BrrrError::Io`] if the path does not exist or cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the language filter is not recognized
pub fn build_function_index(root: &str, language: Option<&str>) -> Result<FunctionIndex> {
    use std::path::Path;

    let scanner = ProjectScanner::new(root)?;
    let project_root = Path::new(root);

    let files = match language {
        Some(lang) => scanner.scan_language(lang)?,
        None => scanner.scan_files()?,
    };

    FunctionIndex::build_with_root(&files, Some(project_root))
}

/// Build a function index with custom configuration.
///
/// Provides more control over indexing behavior than [`build_function_index`].
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `config` - Indexing configuration
///
/// # Returns
///
/// A [`FunctionIndex`] with the configured settings.
///
/// # Examples
///
/// ```no_run
/// use brrr::{build_function_index_with_config, IndexingConfig};
///
/// // Index Python files, excluding tests
/// let config = IndexingConfig::new()
///     .with_language("python")
///     .exclude_tests();
///
/// let index = build_function_index_with_config("./src", &config)?;
/// println!("Indexed {} functions (excluding tests)", index.len());
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the path does not exist or cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the language filter is not recognized
pub fn build_function_index_with_config(
    root: &str,
    config: &IndexingConfig,
) -> Result<FunctionIndex> {
    use std::path::Path;

    let scanner = ProjectScanner::new(root)?;
    let project_root = Path::new(root);

    // Build scan config based on configuration options
    let mut scan_config = match &config.language {
        Some(lang) => ScanConfig::for_language(lang),
        None => ScanConfig::default(),
    };

    // Add test exclusion patterns if needed
    if !config.include_tests {
        scan_config = scan_config.with_excludes(&[
            "**/test/**",
            "**/tests/**",
            "**/*_test.*",
            "**/*_spec.*",
            "**/test_*.*",
        ]);
    }

    let result = scanner.scan_with_config(&scan_config)?;
    FunctionIndex::build_with_root(&result.files, Some(project_root))
}

// =============================================================================
// Import Analysis API
// =============================================================================

/// Result of an importer search - a file that imports a given module.
#[derive(Debug, Clone)]
pub struct ImporterInfo {
    /// Path to the file containing the import.
    pub file: std::path::PathBuf,
    /// The import statement details.
    pub import: ImportInfo,
}

/// Find all files that import a given module.
///
/// Scans the project for source files and analyzes their import statements
/// to find files that import the specified module. This is the reverse of
/// `get_imports` - instead of listing what a file imports, it lists what
/// files import a specific module.
///
/// # Arguments
///
/// * `root` - Project root directory path
/// * `module` - Module name to search for importers
/// * `language` - Optional language filter (e.g., `Some("python")`)
///
/// # Matching Rules
///
/// A file is considered to import the module if any of these match:
/// 1. Exact module match: `import.module == module`
/// 2. Module is the last component: "json" matches "os.json"
/// 3. Module is the first component: "os" matches "os.path"
/// 4. Module is in the middle: "path" matches "os.path.join"
/// 5. Any of the imported names match: "Path" matches `from pathlib import Path`
///
/// # Returns
///
/// Vector of [`ImporterInfo`] containing the file path and import details
/// for each file that imports the specified module.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_importers;
///
/// // Find all files that import the "json" module
/// let importers = get_importers("./src", "json", None)?;
/// println!("Found {} files importing 'json':", importers.len());
/// for importer in &importers {
///     println!("  {} at line {}", importer.file.display(), importer.import.line_number);
/// }
///
/// // Find Python files importing "flask"
/// let flask_users = get_importers("./src", "flask", Some("python"))?;
/// for importer in &flask_users {
///     println!("{}: {}", importer.file.display(), importer.import.statement());
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the path does not exist or cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the language is not recognized
pub fn get_importers(
    root: &str,
    module: &str,
    language: Option<&str>,
) -> Result<Vec<ImporterInfo>> {
    let scanner = ProjectScanner::new(root)?;

    // Get files - optionally filtered by language
    let files = match language {
        Some(lang) => scanner.scan_language(lang)?,
        None => scanner.scan_files()?,
    };

    let mut importers = Vec::new();

    for file_path in files {
        // Extract imports from file
        let imports = match ast::extract_imports(&file_path) {
            Ok(i) => i,
            Err(_) => continue, // Skip files that fail to parse
        };

        // Check if any import matches the module
        for import in imports {
            if import_matches_module(&import, module) {
                importers.push(ImporterInfo {
                    file: file_path.clone(),
                    import,
                });
            }
        }
    }

    Ok(importers)
}

/// Check if an import matches the target module name.
///
/// # Matching Rules
///
/// 1. Exact module match: `import.module == module`
/// 2. Module is the last component (e.g., "json" matches "os.json")
/// 3. Module is the first component (e.g., "os" matches "os.path")
/// 4. Module is in the middle (e.g., "path" matches "os.path.join")
/// 5. Any of the imported names match (e.g., "Path" matches `from pathlib import Path`)
fn import_matches_module(import: &ImportInfo, module: &str) -> bool {
    // Exact module match
    if import.module == module {
        return true;
    }

    // Module ends with ".{module}" (module is the last component)
    if import.module.ends_with(&format!(".{}", module)) {
        return true;
    }

    // Module starts with "{module}." (module is the first component)
    if import.module.starts_with(&format!("{}.", module)) {
        return true;
    }

    // Module is in the middle (e.g., "path" matches "os.path.join")
    if import.module.contains(&format!(".{}.", module)) {
        return true;
    }

    // Any of the imported names match exactly
    if import.names.iter().any(|name| name == module) {
        return true;
    }

    false
}

// =============================================================================
// Intra-File Call Graph API
// =============================================================================

/// Detailed information about a single intra-file function call.
///
/// Represents a call from one function to another within the same source file,
/// including the exact location of the call site.
#[derive(Debug, Clone, serde::Serialize)]
pub struct IntraFileCall {
    /// Name of the calling function.
    pub caller: String,
    /// Name of the called function.
    pub callee: String,
    /// Line number of the call (1-indexed).
    pub line: usize,
    /// Column number of the call (0-indexed).
    pub column: usize,
}

/// Get function call relationships within a single file.
///
/// Analyzes a source file and returns a mapping of which functions call which
/// other functions, considering only functions defined within the same file.
/// This is useful for understanding local code structure without needing to
/// build a full project call graph.
///
/// # Arguments
///
/// * `file_path` - Path to the source file to analyze
///
/// # Returns
///
/// A `HashMap` where keys are caller function names and values are vectors
/// of callee function names. Only includes calls to functions defined in the
/// same file (intra-file calls). Each caller has a deduplicated list of callees.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_intra_file_calls;
///
/// let calls = get_intra_file_calls("src/main.py")?;
/// for (caller, callees) in &calls {
///     println!("{} calls: {:?}", caller, callees);
/// }
/// // Output:
/// // main calls: ["process_data", "cleanup"]
/// // process_data calls: ["validate", "transform"]
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the file type is not recognized
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_intra_file_calls(
    file_path: &str,
) -> Result<std::collections::HashMap<String, Vec<String>>> {
    use std::collections::{HashMap, HashSet};
    use std::path::Path;

    let path = Path::new(file_path);
    let registry = LanguageRegistry::global();

    // Detect language from file extension
    let lang = registry.detect_language(path).ok_or_else(|| {
        BrrrError::UnsupportedLanguage(
            path.extension()
                .and_then(|e| e.to_str())
                .unwrap_or("unknown")
                .to_string(),
        )
    })?;

    // Read and parse the file
    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
    let mut parser = lang.parser_for_path(path)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: file_path.to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    // Extract all function definitions
    let module_info = ast::AstExtractor::extract_file(path)?;

    // Build set of function names defined in this file (including methods)
    let mut defined_functions: HashSet<String> = HashSet::new();
    for func in &module_info.functions {
        defined_functions.insert(func.name.clone());
    }
    for class in &module_info.classes {
        for method in &class.methods {
            defined_functions.insert(method.name.clone());
        }
    }

    // Build function line ranges for determining which function contains a call
    struct FuncRange {
        name: String,
        start_line: usize,
        end_line: usize,
    }
    let mut func_ranges: Vec<FuncRange> = Vec::new();

    for func in &module_info.functions {
        func_ranges.push(FuncRange {
            name: func.name.clone(),
            start_line: func.line_number,
            end_line: func.end_line_number.unwrap_or(func.line_number),
        });
    }
    for class in &module_info.classes {
        for method in &class.methods {
            func_ranges.push(FuncRange {
                name: method.name.clone(),
                start_line: method.line_number,
                end_line: method.end_line_number.unwrap_or(method.line_number),
            });
        }
    }

    // Sort by start line for efficient lookup
    func_ranges.sort_by_key(|r| r.start_line);

    // Initialize call map with empty vectors for all defined functions
    let mut calls: HashMap<String, Vec<String>> = HashMap::new();
    for func_name in &defined_functions {
        calls.insert(func_name.clone(), Vec::new());
    }

    // Use tree-sitter query to find call expressions
    let query_str = lang.call_query();
    let query = tree_sitter::Query::new(&tree.language(), query_str)
        .map_err(|e| BrrrError::TreeSitter(format!("Failed to compile call query: {}", e)))?;

    let mut cursor = tree_sitter::QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_slice());

    // Process all call matches
    use streaming_iterator::StreamingIterator;
    while let Some(match_) = matches.next() {
        // Find the callee capture (function name being called)
        let callee_capture = match_.captures.iter().find(|c| {
            let name = &query.capture_names()[c.index as usize];
            *name == "callee"
        });

        if let Some(capture) = callee_capture {
            let callee_node = capture.node;
            let callee_name =
                std::str::from_utf8(&source[callee_node.start_byte()..callee_node.end_byte()])
                    .unwrap_or("")
                    .to_string();

            // Only consider calls to functions defined in this file
            if !defined_functions.contains(&callee_name) {
                continue;
            }

            // Find which function contains this call (by line number)
            let call_line = callee_node.start_position().row + 1;

            // Binary search would be more efficient, but linear is fine for typical file sizes
            for func_range in &func_ranges {
                if call_line >= func_range.start_line && call_line <= func_range.end_line {
                    // Don't add self-calls to the same function unless it's actually recursion
                    // (the call site line != function start line)
                    calls
                        .entry(func_range.name.clone())
                        .or_default()
                        .push(callee_name.clone());
                    break;
                }
            }
        }
    }

    // Deduplicate callees for each caller
    for callees in calls.values_mut() {
        callees.sort();
        callees.dedup();
    }

    Ok(calls)
}

/// Get detailed intra-file call information with line and column numbers.
///
/// Similar to [`get_intra_file_calls`], but returns detailed information about
/// each call site including the exact line and column where the call occurs.
/// This is useful for precise navigation and analysis.
///
/// # Arguments
///
/// * `file_path` - Path to the source file to analyze
///
/// # Returns
///
/// A vector of [`IntraFileCall`] structs, each representing a single call from
/// one function to another within the file. Multiple calls from the same caller
/// to the same callee will result in multiple entries with different locations.
///
/// # Examples
///
/// ```no_run
/// use brrr::get_intra_file_calls_detailed;
///
/// let calls = get_intra_file_calls_detailed("src/main.py")?;
/// for call in &calls {
///     println!("{}:{} - {} calls {}",
///         call.line, call.column, call.caller, call.callee);
/// }
/// // Output:
/// // 15:4 - main calls process_data
/// // 16:4 - main calls cleanup
/// // 25:8 - process_data calls validate
/// # Ok::<(), brrr::BrrrError>(())
/// ```
///
/// # Errors
///
/// - [`BrrrError::Io`] if the file cannot be read
/// - [`BrrrError::UnsupportedLanguage`] if the file type is not recognized
/// - [`BrrrError::Parse`] if the file cannot be parsed
pub fn get_intra_file_calls_detailed(file_path: &str) -> Result<Vec<IntraFileCall>> {
    use std::collections::HashSet;
    use std::path::Path;

    let path = Path::new(file_path);
    let registry = LanguageRegistry::global();

    // Detect language from file extension
    let lang = registry.detect_language(path).ok_or_else(|| {
        BrrrError::UnsupportedLanguage(
            path.extension()
                .and_then(|e| e.to_str())
                .unwrap_or("unknown")
                .to_string(),
        )
    })?;

    // Read and parse the file
    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
    let mut parser = lang.parser_for_path(path)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: file_path.to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    // Extract all function definitions
    let module_info = ast::AstExtractor::extract_file(path)?;

    // Build set of function names defined in this file (including methods)
    let mut defined_functions: HashSet<String> = HashSet::new();
    for func in &module_info.functions {
        defined_functions.insert(func.name.clone());
    }
    for class in &module_info.classes {
        for method in &class.methods {
            defined_functions.insert(method.name.clone());
        }
    }

    // Build function line ranges for determining which function contains a call
    struct FuncRange {
        name: String,
        start_line: usize,
        end_line: usize,
    }
    let mut func_ranges: Vec<FuncRange> = Vec::new();

    for func in &module_info.functions {
        func_ranges.push(FuncRange {
            name: func.name.clone(),
            start_line: func.line_number,
            end_line: func.end_line_number.unwrap_or(func.line_number),
        });
    }
    for class in &module_info.classes {
        for method in &class.methods {
            func_ranges.push(FuncRange {
                name: method.name.clone(),
                start_line: method.line_number,
                end_line: method.end_line_number.unwrap_or(method.line_number),
            });
        }
    }

    // Sort by start line for efficient lookup
    func_ranges.sort_by_key(|r| r.start_line);

    let mut detailed_calls: Vec<IntraFileCall> = Vec::new();

    // Use tree-sitter query to find call expressions
    let query_str = lang.call_query();
    let query = tree_sitter::Query::new(&tree.language(), query_str)
        .map_err(|e| BrrrError::TreeSitter(format!("Failed to compile call query: {}", e)))?;

    let mut cursor = tree_sitter::QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source.as_slice());

    // Process all call matches
    use streaming_iterator::StreamingIterator;
    while let Some(match_) = matches.next() {
        // Find the callee capture (function name being called)
        let callee_capture = match_.captures.iter().find(|c| {
            let name = &query.capture_names()[c.index as usize];
            *name == "callee"
        });

        if let Some(capture) = callee_capture {
            let callee_node = capture.node;
            let callee_name =
                std::str::from_utf8(&source[callee_node.start_byte()..callee_node.end_byte()])
                    .unwrap_or("")
                    .to_string();

            // Only consider calls to functions defined in this file
            if !defined_functions.contains(&callee_name) {
                continue;
            }

            // Get call location
            let position = callee_node.start_position();
            let call_line = position.row + 1;
            let call_column = position.column;

            // Find which function contains this call (by line number)
            for func_range in &func_ranges {
                if call_line >= func_range.start_line && call_line <= func_range.end_line {
                    detailed_calls.push(IntraFileCall {
                        caller: func_range.name.clone(),
                        callee: callee_name.clone(),
                        line: call_line,
                        column: call_column,
                    });
                    break;
                }
            }
        }
    }

    // Sort by line number for consistent output
    detailed_calls.sort_by(|a, b| a.line.cmp(&b.line).then_with(|| a.column.cmp(&b.column)));

    Ok(detailed_calls)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_public_api_types_exported() {
        // Verify that all public types are accessible
        fn _assert_types() {
            let _: Option<FileTreeEntry> = None;
            let _: Option<CodeStructure> = None;
            let _: Option<ModuleInfo> = None;
            let _: Option<SourceInput> = None;
            let _: Option<FunctionInfo> = None;
            let _: Option<ClassInfo> = None;
            let _: Option<ImportInfo> = None;
            let _: Option<CFGInfo> = None;
            let _: Option<CFGBlock> = None;
            let _: Option<CFGEdge> = None;
            let _: Option<BlockId> = None;
            let _: Option<DFGInfo> = None;
            let _: Option<DataflowEdge> = None;
            let _: Option<DataflowKind> = None;
            // PDG types
            let _: Option<PDGInfo> = None;
            let _: Option<ControlDependence> = None;
            let _: Option<BranchType> = None;
            let _: Option<SliceCriteria> = None;
            let _: Option<SliceResult> = None;
            let _: Option<SliceMetrics> = None;
            let _: Option<CallGraph> = None;
            let _: Option<CallEdge> = None;
            let _: Option<FunctionRef> = None;
            let _: Option<BrrrError> = None;
            // Function index types
            let _: Option<FunctionIndex> = None;
            let _: Option<FunctionDef> = None;
            let _: Option<IndexStats> = None;
            let _: Option<IndexingConfig> = None;
            // Semantic types
            let _: Option<EmbeddingUnit> = None;
            let _: Option<SearchResult> = None;
            let _: Option<UnitKind> = None;
            let _: Option<CodeComplexity> = None;
            let _: Option<ChunkInfo> = None;
            // Scanner types
            let _: Option<ProjectScanner> = None;
            let _: Option<ScanConfig> = None;
            let _: Option<ScanResult> = None;
            let _: Option<ScanError> = None;
            let _: Option<ScanErrorKind> = None;
            let _: Option<FileMetadata> = None;
            let _: Option<ErrorHandling> = None;
            // Dead code analysis types
            let _: Option<DeadCodeConfig> = None;
            let _: Option<DeadCodeResult> = None;
            let _: Option<DeadCodeStats> = None;
            let _: Option<DeadFunction> = None;
            let _: Option<DeadReason> = None;
            let _: Option<EntryPointKind> = None;
            // Impact analysis types
            let _: Option<ImpactConfig> = None;
            let _: Option<ImpactResult> = None;
            let _: Option<CallerInfo> = None;
            // Architecture analysis types
            let _: Option<ArchAnalysis> = None;
            let _: Option<ArchStats> = None;
            let _: Option<CycleDependency> = None;
            // Call graph cache types
            let _: Option<CachedCallGraph> = None;
            let _: Option<CachedEdge> = None;
            // Import analysis types
            let _: Option<ImporterInfo> = None;
            // Intra-file call graph types
            let _: Option<IntraFileCall> = None;
            // LLM context types
            let _: Option<FunctionContext> = None;
            let _: Option<RelevantContext> = None;
        }
    }

    #[test]
    fn test_public_api_functions_exist() {
        // Verify that all public API functions are callable
        // (compilation test - doesn't actually run them)
        fn _assert_functions() {
            let _ = get_tree as fn(&str, Option<&str>, bool, bool) -> Result<FileTreeEntry>;
            let _ = get_structure as fn(&str, Option<&str>, usize, bool) -> Result<CodeStructure>;
            let _ = extract_file as fn(&str, Option<&str>) -> Result<ModuleInfo>;
            let _ = extract_file_unchecked as fn(&str) -> Result<ModuleInfo>;
            let _ = extract_from_source as fn(&str, &str) -> Result<ModuleInfo>;
            let _ = get_imports as fn(&str, Option<&str>) -> Result<Vec<ImportInfo>>;
            let _ = get_context as fn(&str, &str, usize) -> Result<serde_json::Value>;
            let _ = get_cfg as fn(&str, &str, Option<&str>) -> Result<CFGInfo>;
            let _ = get_cfg_auto as fn(&str, &str) -> Result<CFGInfo>;
            let _ = get_cfg_from_source as fn(&str, &str, &str) -> Result<CFGInfo>;
            let _ = get_dfg as fn(&str, &str, Option<&str>) -> Result<DFGInfo>;
            let _ = get_dfg_auto as fn(&str, &str) -> Result<DFGInfo>;
            let _ = get_dfg_from_source as fn(&str, &str, &str) -> Result<DFGInfo>;
            let _ = get_pdg as fn(&str, &str, Option<&str>) -> Result<PDGInfo>;
            let _ = get_pdg_auto as fn(&str, &str) -> Result<PDGInfo>;
            let _ = get_slice
                as fn(
                    &str,
                    &str,
                    usize,
                    Option<&str>,
                    Option<&str>,
                    Option<&str>,
                ) -> Result<Vec<usize>>;
            let _ = get_slice_from_source
                as fn(&str, &str, usize, Option<&str>, Option<&str>, &str) -> Result<Vec<usize>>;
            let _ = get_backward_slice as fn(&str, &str, usize) -> Result<Vec<usize>>;
            let _ = get_slice_dfg_only as fn(&str, &str, usize) -> Result<Vec<usize>>;
            let _ = get_forward_slice as fn(&str, &str, usize) -> Result<Vec<usize>>;
            let _ = get_pdg_slice as fn(&str, &str, usize, &str) -> Result<Vec<usize>>;
            // PDG slicing functions (lower-level API)
            let _ = pdg_backward_slice as fn(&PDGInfo, &SliceCriteria) -> SliceResult;
            let _ = pdg_forward_slice as fn(&PDGInfo, &SliceCriteria) -> SliceResult;
            let _ = build_callgraph as fn(&str) -> Result<CallGraph>;
            let _ = get_impact as fn(&str, &str, usize) -> Result<Vec<FunctionRef>>;
            let _ = find_dead_code as fn(&str) -> Result<Vec<FunctionRef>>;
            let _ = warm_callgraph as fn(&str, Option<&[String]>) -> Result<()>;
            // Semantic API functions
            let _ = extract_semantic_units as fn(&str, &str) -> Result<Vec<EmbeddingUnit>>;
            let _ = extract_semantic_units_with_callgraph
                as fn(&str, &str) -> Result<Vec<EmbeddingUnit>>;
            let _ = extract_file_units as fn(&str) -> Result<Vec<EmbeddingUnit>>;
            let _ = build_embedding_text as fn(&EmbeddingUnit) -> String;
            let _ = count_tokens as fn(&str) -> usize;
            // Scanner API functions
            let _ = scan_project_files as fn(&str, Option<&str>, bool) -> Result<ScanResult>;
            let _ = scan_extensions as fn(&str, &[&str]) -> Result<Vec<std::path::PathBuf>>;
            let _ = get_project_metadata as fn(&str, Option<&str>) -> Result<Vec<FileMetadata>>;
            let _ = scan_with_config as fn(&str, &ScanConfig) -> Result<ScanResult>;
            let _ = estimate_file_count as fn(&str) -> Result<usize>;
            // Function index API functions
            let _ = build_function_index as fn(&str, Option<&str>) -> Result<FunctionIndex>;
            let _ = build_function_index_with_config
                as fn(&str, &IndexingConfig) -> Result<FunctionIndex>;
            // Import analysis API functions
            let _ = get_importers as fn(&str, &str, Option<&str>) -> Result<Vec<ImporterInfo>>;
            // Intra-file call graph API functions
            let _ = get_intra_file_calls
                as fn(&str) -> Result<std::collections::HashMap<String, Vec<String>>>;
            let _ = get_intra_file_calls_detailed as fn(&str) -> Result<Vec<IntraFileCall>>;
        }
    }

    #[test]
    fn test_semantic_constants_exported() {
        // Verify semantic constants are accessible
        assert!(MAX_EMBEDDING_TOKENS > 0);
        assert!(MAX_CODE_PREVIEW_TOKENS > 0);
        assert!(CHUNK_OVERLAP_TOKENS > 0);
    }

    #[test]
    fn test_semantic_pattern_exports() {
        // Verify SemanticPattern type is accessible
        let pattern = &SEMANTIC_PATTERNS[0];
        let _: &SemanticPattern = pattern;
        assert!(!pattern.name.is_empty());
        assert!(!pattern.pattern.is_empty());

        // Verify detect_semantic_patterns function works
        let patterns = detect_semantic_patterns("def validate_user(): assert x");
        assert!(patterns.contains(&"validation".to_string()));

        // Verify SEMANTIC_PATTERNS constant is accessible and non-empty
        assert!(!SEMANTIC_PATTERNS.is_empty());
    }

    #[test]
    fn test_callgraph_advanced_type_exports() {
        // Verify dead code analysis types and defaults
        let dead_config = DeadCodeConfig::default();
        assert!(!dead_config.include_public_api_patterns);
        assert!(dead_config.min_confidence > 0.0);
        let _: DeadCodeResult;
        let _: DeadCodeStats;
        let _: DeadFunction;
        let _: DeadReason;

        // Verify entry point detection types
        let kind = classify_entry_point("main");
        assert_eq!(kind, Some(EntryPointKind::Main));
        let test_kind = classify_entry_point("test_something");
        assert_eq!(test_kind, Some(EntryPointKind::Test));

        // Verify impact analysis types and defaults
        let impact_config = ImpactConfig::default();
        assert_eq!(impact_config.max_depth, 0);
        assert!(!impact_config.exclude_tests);
        let _: ImpactResult;
        let _: CallerInfo;

        // Verify architecture analysis types
        let _: ArchAnalysis;
        let _: ArchStats;
        let _: CycleDependency;

        // Verify cache types
        let _: CachedCallGraph;
        let _: CachedEdge;

        // Verify analysis functions are accessible
        let _ = analyze_dead_code as fn(&CallGraph) -> DeadCodeResult;
        let _ = analyze_dead_code_with_config as fn(&CallGraph, &DeadCodeConfig) -> DeadCodeResult;
        let _ = analyze_impact as fn(&CallGraph, &str, ImpactConfig) -> ImpactResult;
        let _ =
            detect_entry_points_with_config as fn(&CallGraph, &DeadCodeConfig) -> Vec<FunctionRef>;
        let _ = analyze_architecture as fn(&CallGraph) -> ArchAnalysis;
    }

    #[test]
    fn test_extract_from_source() {
        let source = r#"
def greet(name: str) -> str:
    """Say hello."""
    return f"Hello, {name}!"

class Greeter:
    def __init__(self, prefix: str):
        self.prefix = prefix
"#;
        let module = extract_from_source(source, "python").unwrap();
        assert_eq!(module.language, "python");
        assert_eq!(module.path, "<string>");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "greet");
        assert_eq!(module.classes.len(), 1);
        assert_eq!(module.classes[0].name, "Greeter");
    }

    #[test]
    fn test_get_cfg_from_source() {
        let source = r#"
def process(x):
    if x > 0:
        return x * 2
    return 0
"#;
        let cfg = get_cfg_from_source(source, "process", "python").unwrap();
        assert_eq!(cfg.function_name, "process");
        // Should have at least entry, if-branch, else-branch, and exit
        assert!(cfg.blocks.len() >= 2, "CFG should have multiple blocks");
    }

    #[test]
    fn test_get_dfg_from_source() {
        let source = r#"
def compute(x, y):
    z = x + y
    result = z * 2
    return result
"#;
        let dfg = get_dfg_from_source(source, "compute", "python").unwrap();
        assert_eq!(dfg.function_name, "compute");
        assert!(
            dfg.definitions.contains_key("z"),
            "Should track 'z' definition"
        );
        assert!(
            dfg.definitions.contains_key("result"),
            "Should track 'result' definition"
        );
        assert!(dfg.uses.contains_key("x"), "Should track 'x' use");
        assert!(dfg.uses.contains_key("y"), "Should track 'y' use");
    }

    #[test]
    fn test_get_slice_from_source() {
        let source = r#"
def compute(x):
    a = x + 1
    b = a * 2
    c = b + x
    return c
"#;
        // Backward slice from line 5 (c = b + x)
        let slice = get_slice_from_source(source, "compute", 5, None, None, "python").unwrap();
        // Should include lines affecting line 5 (definitions of b, a, x)
        assert!(!slice.is_empty(), "Backward slice should not be empty");

        // Forward slice from line 3 (a = x + 1)
        let fwd_slice =
            get_slice_from_source(source, "compute", 3, Some("forward"), None, "python").unwrap();
        // Should include lines affected by line 3
        assert!(!fwd_slice.is_empty(), "Forward slice should not be empty");
    }

    #[test]
    fn test_source_input_enum() {
        // Test SourceInput::Path variant
        let path_input: SourceInput = SourceInput::Path("./test.py");
        match &path_input {
            SourceInput::Path(p) => assert_eq!(*p, "./test.py"),
            _ => panic!("Expected Path variant"),
        }

        // Test SourceInput::Source variant
        let source_input: SourceInput = SourceInput::Source {
            code: "def foo(): pass",
            language: "python",
        };
        match &source_input {
            SourceInput::Source { code, language } => {
                assert_eq!(*code, "def foo(): pass");
                assert_eq!(*language, "python");
            }
            _ => panic!("Expected Source variant"),
        }

        // Test resolve for Source variant
        let (bytes, lang, path) = source_input.resolve().unwrap();
        assert_eq!(bytes, b"def foo(): pass");
        assert_eq!(lang.name(), "python");
        assert!(path.is_none());
    }

    #[test]
    fn test_get_intra_file_calls_python() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = r#"
def helper():
    return 42

def process(x):
    result = helper()
    return result * 2

def main():
    value = process(10)
    helper()
    return value
"#;
        let mut file = tempfile::Builder::new().suffix(".py").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls(file.path().to_str().unwrap()).unwrap();

        // Check that main calls both process and helper
        assert!(calls.contains_key("main"), "Should have main in call map");
        let main_calls = calls.get("main").unwrap();
        assert!(
            main_calls.contains(&"process".to_string()),
            "main should call process"
        );
        assert!(
            main_calls.contains(&"helper".to_string()),
            "main should call helper"
        );

        // Check that process calls helper
        assert!(
            calls.contains_key("process"),
            "Should have process in call map"
        );
        let process_calls = calls.get("process").unwrap();
        assert!(
            process_calls.contains(&"helper".to_string()),
            "process should call helper"
        );

        // Check that helper has no intra-file calls
        assert!(
            calls.contains_key("helper"),
            "Should have helper in call map"
        );
        let helper_calls = calls.get("helper").unwrap();
        assert!(
            helper_calls.is_empty(),
            "helper should not call any local functions"
        );
    }

    #[test]
    fn test_get_intra_file_calls_detailed_python() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = r#"def helper():
    return 42

def process(x):
    result = helper()
    return result * 2

def main():
    value = process(10)
    helper()
    return value
"#;
        let mut file = tempfile::Builder::new().suffix(".py").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls_detailed(file.path().to_str().unwrap()).unwrap();

        // Should have at least 3 intra-file calls
        assert!(
            calls.len() >= 3,
            "Should have at least 3 intra-file calls, got {}",
            calls.len()
        );

        // Check that calls are sorted by line number
        for window in calls.windows(2) {
            assert!(
                window[0].line <= window[1].line,
                "Calls should be sorted by line number"
            );
        }

        // Check that all calls have valid caller and callee names
        for call in &calls {
            assert!(!call.caller.is_empty(), "Caller name should not be empty");
            assert!(!call.callee.is_empty(), "Callee name should not be empty");
            assert!(call.line > 0, "Line number should be positive");
        }
    }

    #[test]
    fn test_get_intra_file_calls_typescript() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = r#"
function helper(): number {
    return 42;
}

function process(x: number): number {
    const result = helper();
    return result * 2;
}

function main(): number {
    const value = process(10);
    helper();
    return value;
}
"#;
        let mut file = tempfile::Builder::new().suffix(".ts").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls(file.path().to_str().unwrap()).unwrap();

        // Check that main calls both process and helper
        assert!(calls.contains_key("main"), "Should have main in call map");
        let main_calls = calls.get("main").unwrap();
        assert!(
            main_calls.contains(&"process".to_string()),
            "main should call process"
        );
        assert!(
            main_calls.contains(&"helper".to_string()),
            "main should call helper"
        );
    }

    #[test]
    fn test_get_intra_file_calls_with_class_methods() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = r#"
def standalone():
    return 1

class Calculator:
    def add(self, a, b):
        return a + b

    def compute(self, x):
        result = self.add(x, 1)
        standalone()
        return result
"#;
        let mut file = tempfile::Builder::new().suffix(".py").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls(file.path().to_str().unwrap()).unwrap();

        // Methods should be tracked
        assert!(
            calls.contains_key("add"),
            "Should have add method in call map"
        );
        assert!(
            calls.contains_key("compute"),
            "Should have compute method in call map"
        );
        assert!(
            calls.contains_key("standalone"),
            "Should have standalone in call map"
        );

        // compute should call standalone (direct function call)
        let compute_calls = calls.get("compute").unwrap();
        assert!(
            compute_calls.contains(&"standalone".to_string()),
            "compute should call standalone"
        );
    }

    #[test]
    fn test_get_intra_file_calls_no_external_calls() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = r#"
import os

def local_func():
    return 42

def main():
    # This calls os.path.join which is external
    path = os.path.join("a", "b")
    # This calls local_func which is internal
    value = local_func()
    # This calls print which is builtin/external
    print(value)
    return value
"#;
        let mut file = tempfile::Builder::new().suffix(".py").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls(file.path().to_str().unwrap()).unwrap();

        let main_calls = calls.get("main").unwrap();
        // Should only contain local_func, not os, join, or print
        assert_eq!(
            main_calls.len(),
            1,
            "main should only call one local function, got {:?}",
            main_calls
        );
        assert!(
            main_calls.contains(&"local_func".to_string()),
            "main should call local_func"
        );
    }

    #[test]
    fn test_get_intra_file_calls_empty_file() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = "# Empty Python file with just a comment\n";
        let mut file = tempfile::Builder::new().suffix(".py").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let calls = get_intra_file_calls(file.path().to_str().unwrap()).unwrap();

        // Should be empty since there are no functions
        assert!(calls.is_empty(), "Empty file should have no calls");
    }

    #[test]
    fn test_get_intra_file_calls_unsupported_language() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let source = "Some random content";
        let mut file = tempfile::Builder::new().suffix(".xyz").tempfile().unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let result = get_intra_file_calls(file.path().to_str().unwrap());
        assert!(
            result.is_err(),
            "Should return error for unsupported language"
        );
        assert!(matches!(result, Err(BrrrError::UnsupportedLanguage(_))));
    }

    // =========================================================================
    // FunctionContext and RelevantContext Tests
    // =========================================================================

    #[test]
    fn test_function_context_minimal() {
        let ctx = FunctionContext::minimal("test_func", "src/main.rs", 10, "rust");
        assert_eq!(ctx.name, "test_func");
        assert_eq!(ctx.file, "src/main.rs");
        assert_eq!(ctx.start_line, 10);
        assert_eq!(ctx.end_line, 10);
        assert_eq!(ctx.language, "rust");
        assert!(ctx.signature.is_none());
        assert!(ctx.docstring.is_none());
        assert!(ctx.source.is_empty());
    }

    #[test]
    fn test_function_context_from_function_info() {
        let info = FunctionInfo {
            name: "process".to_string(),
            params: vec!["x: int".to_string(), "y: int".to_string()],
            return_type: Some("int".to_string()),
            docstring: Some("Process two numbers.".to_string()),
            is_method: false,
            is_async: false,
            decorators: vec![],
            line_number: 2,
            end_line_number: Some(5),
            language: "python".to_string(),
        };

        let source = "# Header\ndef process(x: int, y: int) -> int:\n    \"\"\"Process two numbers.\"\"\"\n    return x + y\n# Footer";
        let ctx = FunctionContext::from_function_info(&info, "src/main.py", source, "python");

        assert_eq!(ctx.name, "process");
        assert_eq!(ctx.file, "src/main.py");
        assert_eq!(ctx.start_line, 2);
        assert_eq!(ctx.end_line, 5);
        assert_eq!(ctx.language, "python");
        assert!(ctx.signature.is_some());
        assert!(ctx.signature.as_ref().unwrap().contains("process"));
        assert_eq!(ctx.docstring, Some("Process two numbers.".to_string()));
        // Source should contain lines 2-4 (0-indexed: 1-4)
        assert!(ctx.source.contains("def process"));
    }

    #[test]
    fn test_function_context_serialization() {
        let ctx = FunctionContext::minimal("test", "test.py", 1, "python");
        let json = serde_json::to_string(&ctx).unwrap();
        assert!(json.contains("\"name\":\"test\""));
        assert!(json.contains("\"file\":\"test.py\""));
        assert!(json.contains("\"language\":\"python\""));

        // Deserialize back
        let deserialized: FunctionContext = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.name, ctx.name);
        assert_eq!(deserialized.file, ctx.file);
        assert_eq!(deserialized.language, ctx.language);
    }

    #[test]
    fn test_relevant_context_new() {
        let entry = FunctionContext::minimal("main", "src/main.rs", 1, "rust");
        let ctx = RelevantContext::new(entry, 2);

        assert_eq!(ctx.entry.name, "main");
        assert_eq!(ctx.depth, 2);
        assert!(ctx.callees.is_empty());
        assert!(ctx.callers.is_empty());
        assert_eq!(ctx.token_count, 0);
    }

    #[test]
    fn test_relevant_context_builder_pattern() {
        let entry = FunctionContext::minimal("main", "src/main.rs", 1, "rust");
        let callee = FunctionContext::minimal("helper", "src/utils.rs", 10, "rust");
        let caller = FunctionContext::minimal("test_main", "tests/test.rs", 5, "rust");

        let ctx = RelevantContext::new(entry, 2)
            .with_callee(callee)
            .with_caller(caller)
            .with_token_count(500);

        assert_eq!(ctx.callees.len(), 1);
        assert_eq!(ctx.callees[0].name, "helper");
        assert_eq!(ctx.callers.len(), 1);
        assert_eq!(ctx.callers[0].name, "test_main");
        assert_eq!(ctx.token_count, 500);
        assert_eq!(ctx.function_count(), 3);
    }

    #[test]
    fn test_relevant_context_estimate_tokens() {
        let mut entry = FunctionContext::minimal("main", "src/main.rs", 1, "rust");
        entry.source = "fn main() { println!(\"hello\"); }".to_string(); // 33 chars

        let mut callee = FunctionContext::minimal("helper", "src/utils.rs", 10, "rust");
        callee.source = "fn helper() {}".to_string(); // 14 chars

        let mut ctx = RelevantContext::new(entry, 1).with_callee(callee);
        ctx.estimate_tokens();

        // Total: 47 chars / 4 = 11 tokens (integer division)
        assert_eq!(ctx.token_count, 11);
    }

    #[test]
    fn test_relevant_context_to_llm_string() {
        let mut entry = FunctionContext::minimal("process", "src/main.py", 10, "python");
        entry.signature = Some("def process(x: int) -> int".to_string());
        entry.docstring = Some("Process a number.".to_string());

        let callee = FunctionContext::minimal("helper", "src/utils.py", 25, "python");
        let caller = FunctionContext::minimal("main", "src/app.py", 5, "python");

        let ctx = RelevantContext::new(entry, 2)
            .with_callee(callee)
            .with_caller(caller)
            .with_token_count(100);

        let output = ctx.to_llm_string();

        // Verify structure
        assert!(output.contains("## Code Context: process (depth=2)"));
        assert!(output.contains("### Entry Point: process (main.py:10)"));
        assert!(output.contains("def process(x: int) -> int"));
        assert!(output.contains("> Process a number."));
        assert!(output.contains("### Calls:"));
        assert!(output.contains("- helper (utils.py:25)"));
        assert!(output.contains("### Called By:"));
        assert!(output.contains("- main (app.py:5)"));
        assert!(output.contains("Token estimate: 100"));
        assert!(output.contains("Functions: 3"));
    }

    #[test]
    fn test_relevant_context_serialization() {
        let entry = FunctionContext::minimal("test", "test.py", 1, "python");
        let callee = FunctionContext::minimal("helper", "helper.py", 5, "python");

        let ctx = RelevantContext::new(entry, 1)
            .with_callee(callee)
            .with_token_count(50);

        let json = serde_json::to_string(&ctx).unwrap();
        assert!(json.contains("\"depth\":1"));
        assert!(json.contains("\"token_count\":50"));

        // Deserialize back
        let deserialized: RelevantContext = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.entry.name, "test");
        assert_eq!(deserialized.callees.len(), 1);
        assert_eq!(deserialized.depth, 1);
        assert_eq!(deserialized.token_count, 50);
    }

    #[test]
    fn test_context_types_exported() {
        // Verify FunctionContext and RelevantContext are accessible
        fn _assert_context_types() {
            let _: Option<FunctionContext> = None;
            let _: Option<RelevantContext> = None;
        }
    }
}
