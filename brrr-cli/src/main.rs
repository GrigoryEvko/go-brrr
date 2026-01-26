#![feature(portable_simd)]

//! brrr CLI - Token-efficient code analysis for LLMs.
//!
//! A high-performance Rust implementation of the brrr code analysis toolkit.

use tikv_jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand, ValueEnum};
use sha2::{Digest, Sha256};
use std::io::{BufRead, BufReader, Write};
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing_subscriber::EnvFilter;
use which::which;

mod analysis;
mod ast;
mod callgraph;
mod cfg;
mod coverage;
mod dataflow;
mod dfg;
mod diagnostics;
mod error;
mod lang;
mod metrics;
mod security;
mod simd;
mod util;

// Import project root, language detection, and path validation utilities
use util::path::{
    detect_project_language, get_project_root, require_directory, require_exists, require_file,
};

// =============================================================================
// CLI STRUCTURE
// =============================================================================

/// Token-efficient code analysis for LLMs.
///
/// Provides fast, structured code analysis optimized for feeding context to LLMs.
/// Supports multiple languages through tree-sitter parsers.
#[derive(Parser)]
#[command(
    name = "brrr",
    version,
    author,
    about = "Token-efficient code analysis for LLMs",
    long_about = r#"
Token-efficient code analysis for LLMs.

Examples:
    brrr tree src/                      # File tree for src/
    brrr structure . --lang python      # Code structure for Python files
    brrr extract src/main.py            # Full file analysis
    brrr context main --project .       # LLM context starting from main()
    brrr cfg src/main.py process        # Control flow for process()
    brrr slice src/main.py func 42      # Lines affecting line 42

Ignore Patterns:
    brrr respects .brrrignore files (gitignore syntax).
    Use --no-ignore to bypass ignore patterns.

Semantic Search:
    First run: brrr semantic index . (downloads embedding model)
    Then: brrr semantic search "authentication logic" .
"#
)]
struct Cli {
    /// Ignore .brrrignore patterns (include all files)
    #[arg(long, global = true)]
    no_ignore: bool,

    /// Verbosity level (-v, -vv, -vvv)
    #[arg(short, long, action = clap::ArgAction::Count, global = true)]
    verbose: u8,

    /// Output format (json by default for most commands)
    #[arg(long, global = true, value_enum, default_value = "json")]
    format: OutputFormat,

    /// Output minified/compact JSON (default: pretty-printed)
    #[arg(long, global = true)]
    compact: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Clone, Copy, ValueEnum, Default)]
enum OutputFormat {
    #[default]
    Json,
    /// JSON Lines - one object per line (for streaming/arrays)
    Jsonl,
    Text,
    Mermaid,
    Dot,
    /// CSV format for metrics (functions only)
    Csv,
}

#[derive(Clone, Copy, ValueEnum)]
enum SliceDirection {
    Backward,
    Forward,
}

impl Default for SliceDirection {
    fn default() -> Self {
        Self::Backward
    }
}

/// Output format for translate command
#[derive(Clone, Copy, ValueEnum, Default, Debug)]
enum TranslateOutputFormat {
    /// JSON format (pretty-printed)
    #[default]
    Json,
    /// Compact JSON (minified)
    JsonCompact,
    /// Text summary
    Text,
}

/// Coupling analysis level
#[derive(Clone, Copy, ValueEnum, Default, Debug)]
enum CouplingLevelArg {
    /// Analyze dependencies between individual files
    #[default]
    File,
    /// Analyze dependencies between directories/packages
    Module,
    /// Analyze dependencies between classes
    Class,
}

impl From<CouplingLevelArg> for metrics::CouplingLevel {
    fn from(arg: CouplingLevelArg) -> Self {
        match arg {
            CouplingLevelArg::File => Self::File,
            CouplingLevelArg::Module => Self::Module,
            CouplingLevelArg::Class => Self::Class,
        }
    }
}

/// Circular dependency analysis level
#[derive(Clone, Copy, ValueEnum, Default, Debug)]
enum CircularLevelArg {
    /// Package-level dependencies (directory boundaries)
    Package,
    /// Module-level dependencies (file-to-file imports)
    #[default]
    Module,
    /// Class-level dependencies (class-to-class usage)
    Class,
    /// Function-level dependencies (call graph cycles)
    Function,
}

impl From<CircularLevelArg> for quality::circular::DependencyLevel {
    fn from(arg: CircularLevelArg) -> Self {
        match arg {
            CircularLevelArg::Package => Self::Package,
            CircularLevelArg::Module => Self::Module,
            CircularLevelArg::Class => Self::Class,
            CircularLevelArg::Function => Self::Function,
        }
    }
}

/// Supported programming languages
#[derive(Clone, Copy, ValueEnum, Debug)]
enum Language {
    Python,
    Typescript,
    Javascript,
    Go,
    Rust,
    Java,
    C,
    Cpp,
    Ruby,
    Php,
    Kotlin,
    Swift,
    Csharp,
    Scala,
    Lua,
    Elixir,
}

impl std::fmt::Display for Language {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Language::Python => "python",
            Language::Typescript => "typescript",
            Language::Javascript => "javascript",
            Language::Go => "go",
            Language::Rust => "rust",
            Language::Java => "java",
            Language::C => "c",
            Language::Cpp => "cpp",
            Language::Ruby => "ruby",
            Language::Php => "php",
            Language::Kotlin => "kotlin",
            Language::Swift => "swift",
            Language::Csharp => "csharp",
            Language::Scala => "scala",
            Language::Lua => "lua",
            Language::Elixir => "elixir",
        };
        write!(f, "{}", s)
    }
}

/// Warm cache language options (includes "all")
#[derive(Clone, Copy, ValueEnum, Debug)]
enum WarmLanguage {
    Python,
    Typescript,
    Javascript,
    Go,
    Rust,
    Java,
    C,
    Cpp,
    All,
}

impl Default for WarmLanguage {
    fn default() -> Self {
        Self::Python
    }
}

impl std::fmt::Display for WarmLanguage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            WarmLanguage::Python => "python",
            WarmLanguage::Typescript => "typescript",
            WarmLanguage::Javascript => "javascript",
            WarmLanguage::Go => "go",
            WarmLanguage::Rust => "rust",
            WarmLanguage::Java => "java",
            WarmLanguage::C => "c",
            WarmLanguage::Cpp => "cpp",
            WarmLanguage::All => "all",
        };
        write!(f, "{}", s)
    }
}

/// Semantic search backend options
#[derive(Clone, Copy, ValueEnum, Default)]
enum SemanticBackend {
    #[default]
    Auto,
    Tei,
    SentenceTransformers,
}

/// Semantic search task type for instruction-aware models
/// Accepts both underscore (Python style) and hyphen (kebab-case) formats
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
enum SearchTask {
    #[default]
    #[value(name = "code_search", alias = "code-search")]
    CodeSearch,

    #[value(name = "code_retrieval", alias = "code-retrieval")]
    CodeRetrieval,

    #[value(name = "semantic_search", alias = "semantic-search")]
    SemanticSearch,

    #[value(name = "default")]
    Default,
}

impl SearchTask {
    /// Returns the task string in Python-compatible format (underscores)
    pub fn as_task_string(&self) -> &'static str {
        match self {
            Self::CodeSearch => "code_search",
            Self::CodeRetrieval => "code_retrieval",
            Self::SemanticSearch => "semantic_search",
            Self::Default => "default",
        }
    }
}

// =============================================================================
// SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum Commands {
    /// Show file tree structure
    #[command(
        about = "Show file tree",
        long_about = "Display the file tree structure of a directory in JSON format."
    )]
    Tree {
        /// Directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Filter by extensions (e.g., --ext .py .ts)
        #[arg(long, value_name = "EXT", num_args = 1..)]
        ext: Vec<String>,

        /// Include hidden files (dotfiles)
        #[arg(long)]
        show_hidden: bool,

        /// Maximum directory depth to traverse (default: 100).
        /// Prevents stack overflow from deeply nested directories.
        #[arg(long, value_name = "DEPTH")]
        max_depth: Option<usize>,
    },

    /// Show code structure (functions, classes, methods)
    #[command(
        about = "Show code structure (codemaps)",
        long_about = "Extract functions, classes, and methods from source files."
    )]
    Structure {
        /// Directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language to analyze (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Maximum files to analyze (use --limit or --max for Python CLI compatibility)
        #[arg(long, visible_alias = "max", default_value = "50", value_name = "N")]
        limit: usize,
    },

    /// Search files for a pattern
    #[command(
        about = "Search files for pattern",
        long_about = "Search files for a regex pattern with optional context lines."
    )]
    Search {
        /// Regex pattern to search
        pattern: String,

        /// Directory to search
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Filter by extensions (e.g., --ext .py .ts)
        #[arg(long, value_name = "EXT", num_args = 1..)]
        ext: Vec<String>,

        /// Context lines around match
        #[arg(short = 'C', long, default_value = "0")]
        context: usize,

        /// Maximum results
        #[arg(long, default_value = "100", value_name = "N")]
        max: usize,

        /// Maximum files to scan
        #[arg(long, default_value = "10000")]
        max_files: usize,
    },

    /// Extract full file info (AST analysis)
    #[command(
        about = "Extract full file info",
        long_about = "Extract complete AST info from a file: functions, classes, methods, docstrings."
    )]
    Extract {
        /// File to analyze
        file: PathBuf,

        /// Base directory for path containment validation (security)
        #[arg(long = "base-path", short = 'b', value_name = "DIR")]
        base_path: Option<PathBuf>,

        /// Filter to specific class
        #[arg(long = "class", value_name = "NAME")]
        filter_class: Option<String>,

        /// Filter to specific function
        #[arg(long = "function", value_name = "NAME")]
        filter_function: Option<String>,

        /// Filter to specific method (Class.method)
        #[arg(long = "method", value_name = "CLASS.METHOD")]
        filter_method: Option<String>,
    },

    /// Get LLM-ready context for an entry point
    #[command(
        about = "Get relevant context for LLM",
        long_about = "Build LLM-ready context by following the call graph from an entry point."
    )]
    Context {
        /// Entry point (function_name or Class.method)
        entry: String,

        /// Project root directory
        #[arg(long, default_value = ".")]
        project: PathBuf,

        /// Call depth to follow
        #[arg(long, default_value = "2")]
        depth: usize,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Generate control flow graph for a function
    #[command(
        about = "Control flow graph",
        long_about = "Generate a control flow graph (CFG) for a function, showing branches and loops."
    )]
    Cfg {
        /// Source file
        file: PathBuf,

        /// Function name
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, mermaid, dot)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,
    },

    /// Generate data flow graph for a function
    #[command(
        about = "Data flow graph",
        long_about = "Generate a data flow graph (DFG) for a function, showing variable dependencies."
    )]
    Dfg {
        /// Source file
        file: PathBuf,

        /// Function name
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Compute a program slice
    #[command(
        about = "Program slice",
        long_about = "Compute a program slice: find all lines that affect (backward) or are affected by (forward) a given line."
    )]
    Slice {
        /// Source file
        file: PathBuf,

        /// Function name
        function: String,

        /// Line number to slice from
        line: usize,

        /// Slice direction
        #[arg(long, value_enum, default_value = "backward")]
        direction: SliceDirection,

        /// Variable to track (optional)
        #[arg(long, value_name = "VAR")]
        var: Option<String>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Include extended output (direction, function, target_line, metrics)
        #[arg(long, default_value = "false")]
        extended: bool,
    },

    /// Build cross-file call graph
    #[command(
        about = "Build cross-file call graph",
        long_about = "Build a project-wide call graph showing which functions call which."
    )]
    Calls {
        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Include extended information (call_line, etc.)
        #[arg(long)]
        extended: bool,
    },

    /// Find all callers of a function (reverse call graph)
    #[command(
        about = "Find all callers of a function (reverse call graph)",
        long_about = "Analyze impact: find all functions that call a given function (transitively).\nUseful before refactoring to understand what will be affected."
    )]
    Impact {
        /// Function name to find callers of
        func: String,

        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Maximum depth to traverse
        #[arg(long, default_value = "3")]
        depth: usize,

        /// Filter by file containing this string
        #[arg(long)]
        file: Option<String>,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Find unreachable (dead) code
    #[command(
        about = "Find unreachable (dead) code",
        long_about = "Find functions that are never called (dead code).\nExcludes common entry points like main, test_*, cli, etc."
    )]
    Dead {
        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Additional entry point patterns (e.g., --entry main cli plugin_)
        #[arg(long, value_name = "PATTERN", num_args = 0..)]
        entry: Vec<String>,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Detect architectural layers from call patterns
    #[command(
        about = "Detect architectural layers from call patterns",
        long_about = "Detect architectural layers (entry, middle, leaf) from call patterns.\nIdentifies circular dependencies."
    )]
    Arch {
        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Parse imports from a source file
    #[command(
        about = "Parse imports from a source file",
        long_about = "Parse all import statements from a source file.\nReturns JSON with module names, imported names, and aliases."
    )]
    Imports {
        /// Source file to analyze
        file: PathBuf,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Find all files that import a module
    #[command(
        about = "Find all files that import a module (reverse import lookup)",
        long_about = "Find all files that import a given module.\nComplements 'brrr impact' which tracks function calls."
    )]
    Importers {
        /// Module name to search for importers
        module: String,

        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Pre-build call graph cache for faster queries
    #[command(
        about = "Pre-build call graph cache for faster queries",
        long_about = "Pre-build the call graph cache to speed up subsequent queries.\nRun this once per project before using impact/dead/calls."
    )]
    Warm {
        /// Project root directory
        path: PathBuf,

        /// Build in background process
        #[arg(long)]
        background: bool,

        /// Language (use 'all' for multi-language)
        #[arg(long, value_enum, default_value = "python")]
        lang: WarmLanguage,
    },

    /// Find tests affected by changed files
    #[command(
        about = "Find tests affected by changed files",
        long_about = "Find which tests to run based on changed files.\nUses call graph + import analysis to find affected tests."
    )]
    ChangeImpact {
        /// Files to analyze (default: auto-detect from session/git)
        #[arg(value_name = "FILE")]
        files: Vec<PathBuf>,

        /// Use session-modified files (dirty_flag)
        #[arg(long)]
        session: bool,

        /// Use git diff to find changed files
        #[arg(long)]
        git: bool,

        /// Git ref to diff against
        #[arg(long, default_value = "HEAD~1")]
        git_base: String,

        /// Language (auto-detected if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Max call graph depth
        #[arg(long, default_value = "5")]
        depth: usize,

        /// Actually run the affected tests
        #[arg(long)]
        run: bool,

        /// Project directory to analyze
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Get type and lint diagnostics
    #[command(
        about = "Get type and lint diagnostics",
        long_about = "Run type checker (pyright) and linter (ruff) on code.\nReturns structured errors. Use before tests to catch type errors early."
    )]
    Diagnostics {
        /// File or project directory to check
        target: PathBuf,

        /// Check entire project (default: single file)
        #[arg(long)]
        project: bool,

        /// Skip linter, only run type checker
        #[arg(long)]
        no_lint: bool,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Override language detection
        #[arg(long, value_enum)]
        lang: Option<Language>,
    },

    /// Semantic code search using embeddings
    #[command(subcommand)]
    Semantic(SemanticCommands),

    /// Daemon management for faster repeated queries
    #[command(subcommand)]
    Daemon(DaemonCommands),

    /// Check and install diagnostic tools
    #[command(
        about = "Check and install diagnostic tools (type checkers, linters)",
        long_about = "Check which diagnostic tools (type checkers, linters) are installed.\nCan auto-install missing tools for supported languages."
    )]
    Doctor {
        /// Install missing tools for language (e.g., python, go)
        #[arg(long, value_name = "LANG")]
        install: Option<String>,

        /// Output as JSON
        #[arg(long)]
        json: bool,
    },

    /// Security analysis subcommands
    #[command(subcommand, visible_alias = "sec")]
    Security(SecurityCommands),

    /// Code metrics analysis (use 'brrr metrics <path>' for full report)
    ///
    /// Run without subcommand for unified report: brrr metrics ./src
    /// Or use specific subcommands: brrr metrics complexity ./src
    #[command(subcommand_required = false, args_conflicts_with_subcommands = true)]
    Metrics {
        /// Path to analyze (when no subcommand given, runs full report)
        #[arg(default_value = ".")]
        path: Option<PathBuf>,

        /// Language filter for shorthand mode
        #[arg(long, short = 'l', value_enum)]
        lang: Option<Language>,

        /// Output format for shorthand mode
        #[arg(long, short = 'f', value_enum, default_value = "text")]
        format: Option<OutputFormat>,

        /// Fail on issues (warning, critical) for CI integration
        #[arg(long)]
        fail_on: Option<String>,

        #[command(subcommand)]
        cmd: Option<MetricsCommands>,
    },

    /// Code quality analysis subcommands
    #[command(subcommand)]
    Quality(QualityCommands),

    /// Data flow analysis subcommands
    #[command(subcommand, visible_alias = "df")]
    Dataflow(DataflowCommands),

    /// Coverage analysis and CFG mapping
    #[command(subcommand)]
    Coverage(CoverageCommands),

    /// Advanced code analysis subcommands
    #[command(subcommand)]
    Analyze(AnalyzeCommands),

    /// Translate Go source to Brrr IR
    #[command(
        about = "Translate Go source to Brrr IR",
        long_about = "Translate Go source files to Brrr IR (Intermediate Representation).\n\n\
            This produces a typed expression tree representation of the Go code\n\
            suitable for analysis, transformation, and verification."
    )]
    Translate {
        /// File to translate
        file: PathBuf,

        /// Output only declarations (no function bodies)
        #[arg(long)]
        declarations_only: bool,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        output: TranslateOutputFormat,
    },
}

// =============================================================================
// COVERAGE SUBCOMMANDS
// =============================================================================

/// Coverage format argument
#[derive(Clone, Copy, ValueEnum, Debug)]
enum CoverageFormatArg {
    /// LCOV format (lcov.info)
    Lcov,
    /// Cobertura XML format
    Cobertura,
    /// Python coverage.py JSON
    CoverageJson,
    /// JavaScript Istanbul JSON
    Istanbul,
    /// LLVM coverage JSON
    Llvm,
    /// GNU gcov format
    Gcov,
    /// Java JaCoCo XML
    JaCoCo,
}

impl From<CoverageFormatArg> for coverage::CoverageFormat {
    fn from(arg: CoverageFormatArg) -> Self {
        match arg {
            CoverageFormatArg::Lcov => Self::Lcov,
            CoverageFormatArg::Cobertura => Self::Cobertura,
            CoverageFormatArg::CoverageJson => Self::CoverageJson,
            CoverageFormatArg::Istanbul => Self::Istanbul,
            CoverageFormatArg::Llvm => Self::Llvm,
            CoverageFormatArg::Gcov => Self::Gcov,
            CoverageFormatArg::JaCoCo => Self::JaCoCo,
        }
    }
}

#[derive(Subcommand)]
enum CoverageCommands {
    /// Map coverage data to CFG
    #[command(
        name = "map",
        about = "Map coverage data to CFG for detailed analysis",
        long_about = "Parse coverage data and map it to control flow graph.\n\n\
            Supports multiple coverage formats:\n\
            - lcov: Standard LCOV format (lcov.info)\n\
            - cobertura: Cobertura XML format\n\
            - coverage-json: Python coverage.py JSON\n\
            - istanbul: JavaScript Istanbul/nyc JSON\n\
            - llvm: LLVM coverage JSON export\n\
            - gcov: GNU gcov text format\n\
            - jacoco: Java JaCoCo XML\n\n\
            Output includes:\n\
            - Block and edge coverage\n\
            - Uncovered branches\n\
            - Path coverage analysis\n\
            - Test suggestions"
    )]
    Map {
        /// Coverage file to parse
        coverage_file: PathBuf,

        /// Source file to analyze
        source_file: PathBuf,

        /// Function name to analyze (for CFG extraction)
        #[arg(long, short = 'f')]
        function: String,

        /// Coverage format (auto-detected if not specified)
        #[arg(long, value_enum)]
        format: Option<CoverageFormatArg>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Include test suggestions in output
        #[arg(long)]
        suggest_tests: bool,

        /// Maximum path depth for path coverage analysis
        #[arg(long, default_value = "1000")]
        max_paths: usize,
    },

    /// Parse coverage file and show summary
    #[command(
        name = "parse",
        about = "Parse coverage file and display summary",
        long_about = "Parse a coverage file and display summary statistics.\n\n\
            Shows:\n\
            - Line coverage percentage\n\
            - Branch coverage percentage\n\
            - Function coverage percentage\n\
            - Per-file breakdown"
    )]
    Parse {
        /// Coverage file to parse
        coverage_file: PathBuf,

        /// Coverage format (auto-detected if not specified)
        #[arg(long, value_enum)]
        format: Option<CoverageFormatArg>,

        /// Show per-file details
        #[arg(long)]
        details: bool,
    },

    /// Find uncovered branches in a function
    #[command(
        name = "uncovered",
        about = "Find uncovered branches in a function",
        long_about = "Analyze coverage and CFG to find specific uncovered branches.\n\n\
            Useful for identifying which test cases need to be written.\n\
            Branches are prioritized by importance:\n\
            - Exception handlers (highest priority)\n\
            - Conditional branches (true/false)\n\
            - Error handling paths\n\
            - Loop boundaries"
    )]
    Uncovered {
        /// Coverage file to parse
        coverage_file: PathBuf,

        /// Source file to analyze
        source_file: PathBuf,

        /// Function name to analyze
        #[arg(long, short = 'f')]
        function: String,

        /// Coverage format (auto-detected if not specified)
        #[arg(long, value_enum)]
        format: Option<CoverageFormatArg>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Minimum priority level (1-9, higher = more important)
        #[arg(long, default_value = "1")]
        min_priority: u8,
    },

    /// Suggest test cases for uncovered code
    #[command(
        name = "suggest",
        about = "Suggest test cases for uncovered code",
        long_about = "Analyze coverage gaps and suggest test cases.\n\n\
            Suggestions include:\n\
            - Description of what to test\n\
            - Target lines to cover\n\
            - Suggested test name\n\
            - Priority level"
    )]
    Suggest {
        /// Coverage file to parse
        coverage_file: PathBuf,

        /// Source file to analyze
        source_file: PathBuf,

        /// Function name to analyze
        #[arg(long, short = 'f')]
        function: String,

        /// Coverage format (auto-detected if not specified)
        #[arg(long, value_enum)]
        format: Option<CoverageFormatArg>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Maximum number of suggestions
        #[arg(long, default_value = "10")]
        max: usize,
    },
}

// =============================================================================
// METRICS SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum MetricsCommands {
    /// Analyze cyclomatic complexity
    #[command(
        name = "complexity",
        about = "Calculate cyclomatic complexity for functions",
        long_about = "Calculate cyclomatic complexity using control flow graph analysis.\n\n\
            Cyclomatic complexity measures the number of linearly independent paths\n\
            through a function. Higher values indicate more complex code.\n\n\
            Risk Levels:\n\
            - Low (1-10): Simple, low risk, easy to test\n\
            - Medium (11-20): Moderate complexity, consider refactoring\n\
            - High (21-50): Complex, hard to test and maintain\n\
            - Critical (50+): Refactor immediately\n\n\
            Decision points counted:\n\
            - if, elif/else if, while, for, switch/match cases\n\
            - try/except/catch handlers\n\
            - Boolean operators (&&, ||, and, or) in conditions"
    )]
    Complexity {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show functions with complexity above threshold
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<u32>,

        /// Sort output by complexity (highest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only violation summary (functions exceeding threshold)
        #[arg(long)]
        violations_only: bool,
    },

    /// Analyze cognitive complexity (SonarSource methodology)
    #[command(
        name = "cognitive",
        about = "Calculate cognitive complexity for functions",
        long_about = "Calculate cognitive complexity using SonarSource methodology.\n\n\
            Cognitive complexity measures how difficult code is to understand,\n\
            penalizing deeply nested structures more than cyclomatic complexity.\n\n\
            Key differences from cyclomatic complexity:\n\
            - Nesting penalty: nested structures add to the increment\n\
            - Logical sequences: a && b && c counts as 1, not 2\n\
            - No increment for else (counted with if)\n\n\
            Risk Levels (stricter than cyclomatic):\n\
            - Low (0-5): Simple, easy to understand\n\
            - Medium (6-10): Moderate complexity, consider simplifying\n\
            - High (11-15): Complex, hard to understand\n\
            - Critical (15+): Refactor immediately"
    )]
    Cognitive {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show functions with complexity above threshold
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<u32>,

        /// Sort output by complexity (highest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only violation summary (functions exceeding threshold)
        #[arg(long)]
        violations_only: bool,

        /// Show detailed breakdown of complexity contributions
        #[arg(long, short = 'b')]
        breakdown: bool,
    },

    /// Analyze Halstead complexity metrics
    #[command(
        name = "halstead",
        about = "Calculate Halstead complexity metrics for functions",
        long_about = "Calculate Halstead metrics based on operator and operand counts.\n\n\
            Halstead metrics measure software complexity through vocabulary analysis:\n\n\
            Base Counts:\n\
            - n1: Number of distinct operators\n\
            - n2: Number of distinct operands\n\
            - N1: Total operators\n\
            - N2: Total operands\n\n\
            Derived Metrics:\n\
            - Vocabulary (n): n1 + n2\n\
            - Length (N): N1 + N2\n\
            - Volume (V): N * log2(n) - program size in bits\n\
            - Difficulty (D): (n1/2) * (N2/n2) - error-proneness\n\
            - Effort (E): D * V - mental effort required\n\
            - Time (T): E / 18 - estimated development time (seconds)\n\
            - Bugs (B): V / 3000 - estimated bug count\n\n\
            Language-specific operators are recognized for Python, TypeScript,\n\
            JavaScript, Rust, Go, Java, C, and C++."
    )]
    Halstead {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Sort output by volume (highest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Sort by difficulty instead of volume
        #[arg(long)]
        sort_by_difficulty: bool,

        /// Include detailed operator/operand lists in output
        #[arg(long)]
        show_tokens: bool,
    },

    /// Calculate Maintainability Index
    #[command(
        name = "maintainability",
        about = "Calculate Maintainability Index for functions",
        long_about = "Calculate Maintainability Index combining Halstead Volume, Cyclomatic Complexity, and Lines of Code.\n\n\
            Formula (Visual Studio Standard):\n\
            MI = MAX(0, (171 - 5.2*ln(V) - 0.23*CC - 16.2*ln(LOC)) * 100/171)\n\n\
            Where:\n\
            - V = Halstead Volume (program size in bits)\n\
            - CC = Cyclomatic Complexity (independent paths)\n\
            - LOC = Source Lines of Code (excluding blanks/comments)\n\n\
            Extended formula adds comment bonus:\n\
            MI += 50 * sin(sqrt(2.4 * CM)) where CM = comment percentage\n\n\
            Risk Levels:\n\
            - Low (50-100): Highly maintainable\n\
            - Medium (20-49): Moderately maintainable\n\
            - High (10-19): Hard to maintain\n\
            - Critical (0-9): Very hard to maintain, refactor immediately\n\n\
            Lines of Code types calculated:\n\
            - Physical LOC: Total lines\n\
            - Source LOC: Non-blank lines\n\
            - Effective LOC: Source minus comment-only lines\n\
            - Comment lines: Lines containing comments"
    )]
    Maintainability {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show functions with MI below threshold (low MI is bad)
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<f64>,

        /// Sort output by MI score (lowest first - worst maintainability)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only violation summary (functions below threshold)
        #[arg(long)]
        violations_only: bool,

        /// Use extended formula with comment bonus
        #[arg(long)]
        include_comments: bool,
    },

    /// Analyze lines of code metrics
    #[command(
        name = "loc",
        about = "Calculate lines of code metrics",
        long_about = "Calculate various lines of code metrics using AST-aware analysis.\n\n\
            Metric Types:\n\
            - Physical LOC: Total lines including blanks and comments\n\
            - Source LOC (SLOC): Lines containing actual code\n\
            - Logical LOC: Number of statements (AST-based)\n\
            - Comment LOC (CLOC): Lines containing comments\n\
            - Blank lines: Empty or whitespace-only lines\n\n\
            AST-Aware Features:\n\
            - Multi-line strings not counted as code lines (except docstrings)\n\
            - Accurate statement counting from AST\n\
            - Proper handling of mixed code-and-comment lines\n\n\
            Per-function metrics:\n\
            - Function SLOC with 'too long' detection (>50 lines threshold)\n\
            - Statement count per function\n\
            - Comment density percentage\n\n\
            Use --by-language to see metrics grouped by programming language."
    )]
    Loc {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Show metrics grouped by language
        #[arg(long)]
        by_language: bool,

        /// Sort files by SLOC (largest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Threshold for 'too long' functions (default: 50)
        #[arg(long, short = 't', default_value = "50")]
        function_threshold: u32,

        /// Show only files with oversized functions
        #[arg(long)]
        violations_only: bool,

        /// Show largest N files
        #[arg(long, default_value = "10")]
        top: usize,
    },

    /// Analyze nesting depth metrics
    #[command(
        name = "nesting",
        about = "Calculate nesting depth metrics for functions",
        long_about = "Calculate nesting depth metrics to identify deeply nested code.\n\n\
            Deep nesting is a strong indicator of complexity that makes code harder\n\
            to understand, test, and maintain.\n\n\
            Nesting Constructs Tracked:\n\
            - Control flow: if, for, while, switch/match, try\n\
            - Closures/lambdas: lambda, arrow functions, closures\n\
            - Callbacks: Nested function expressions (especially in JS)\n\
            - Comprehensions: List/dict/set comprehensions with conditions (Python)\n\
            - Blocks: Named blocks in Rust, defer in Go\n\n\
            Risk Levels:\n\
            - Good (1-3): Acceptable nesting, code is readable\n\
            - Acceptable (4-5): Consider simplifying if possible\n\
            - Complex (6-7): Hard to understand, should refactor\n\
            - Severe (8+): Refactor immediately\n\n\
            Suggestions for improvement are provided for deeply nested code."
    )]
    Nesting {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show functions with depth above threshold (default: 5)
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<u32>,

        /// Sort output by nesting depth (highest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only violation summary (functions exceeding threshold)
        #[arg(long)]
        violations_only: bool,

        /// Show detailed breakdown with suggestions
        #[arg(long, short = 'd')]
        details: bool,
    },

    /// Analyze function size metrics
    #[command(
        name = "functions",
        about = "Calculate function size metrics",
        long_about = "Calculate comprehensive size metrics for functions to identify oversized code.\n\n\
            Metrics Calculated:\n\
            - SLOC: Source Lines of Code (excluding blanks/comments)\n\
            - Statements: Number of AST statement nodes\n\
            - Parameters: Number of function parameters\n\
            - Local Variables: Number of variable declarations\n\
            - Return Statements: Number of return/throw points\n\
            - Branches: Number of if/switch/match constructs\n\n\
            Default Thresholds:\n\
            - SLOC: warning > 30, critical > 60\n\
            - Parameters: warning > 5, critical > 8\n\
            - Variables: warning > 10, critical > 15\n\
            - Returns: warning > 5\n\n\
            Context-Aware Analysis:\n\
            - Constructors: adjusted thresholds for params/variables\n\
            - Test functions: longer functions tolerated\n\
            - Configuration: more variables expected\n\
            - Factories: more parameters expected"
    )]
    Functions {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Sort output (sloc, params, score, issues, variables, branches)
        #[arg(long, value_name = "FIELD")]
        sort_by: Option<String>,

        /// Show only functions with issues (violations)
        #[arg(long)]
        violations_only: bool,

        /// SLOC warning threshold (default: 30)
        #[arg(long, default_value = "30")]
        sloc_warn: u32,

        /// SLOC critical threshold (default: 60)
        #[arg(long, default_value = "60")]
        sloc_critical: u32,

        /// Parameters warning threshold (default: 5)
        #[arg(long, default_value = "5")]
        params_warn: u32,

        /// Parameters critical threshold (default: 8)
        #[arg(long, default_value = "8")]
        params_critical: u32,

        /// Show detailed suggestions for each function
        #[arg(long, short = 'd')]
        details: bool,
    },

    /// Analyze coupling metrics (afferent/efferent coupling)
    #[command(
        name = "coupling",
        about = "Calculate coupling metrics for modules",
        long_about = "Calculate afferent/efferent coupling metrics for architectural analysis.\n\n\
            Coupling Metrics:\n\
            - Ca (Afferent Coupling): Number of modules that depend ON this module\n\
            - Ce (Efferent Coupling): Number of modules this module depends ON\n\
            - Instability (I): Ce / (Ca + Ce) - 0=stable, 1=unstable\n\
            - Abstractness (A): abstract_types / total_types\n\
            - Distance (D): |A + I - 1| - distance from main sequence\n\n\
            Main Sequence Analysis:\n\
            - Ideal modules lie on the line A + I = 1\n\
            - Zone of Pain (A=0, I=0): Concrete and stable - hard to change\n\
            - Zone of Uselessness (A=1, I=1): Abstract and unstable\n\n\
            Dependency Types Tracked:\n\
            - Import: Direct import statements\n\
            - Call: Function calls across module boundaries\n\
            - Type: Using types from another module\n\
            - Inheritance: Class inheritance relationships"
    )]
    Coupling {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Analysis level: file, module (directory), or class
        #[arg(long, value_enum, default_value = "file")]
        level: CouplingLevelArg,

        /// Sort output by distance from main sequence (worst first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only modules with distance above threshold
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<f64>,

        /// Show circular dependencies
        #[arg(long)]
        show_cycles: bool,

        /// Show all dependency edges
        #[arg(long)]
        show_edges: bool,
    },

    /// Analyze class cohesion metrics (LCOM variants)
    #[command(
        name = "cohesion",
        about = "Calculate class cohesion metrics (LCOM)",
        long_about = "Calculate Lack of Cohesion of Methods (LCOM) variants for class quality analysis.\n\n\
            LCOM measures how tightly related the methods of a class are. High LCOM indicates\n\
            a class that might be doing too many things and should be split.\n\n\
            LCOM Variants:\n\
            - LCOM1: max(0, P - Q) where P = non-sharing pairs, Q = sharing pairs\n\
            - LCOM2: P - Q (can be negative, indicates good cohesion)\n\
            - LCOM3: Connected components in method-attribute graph\n\
            - LCOM4: LCOM3 + method-to-method call edges\n\n\
            Interpretation:\n\
            - LCOM3 = 1: Perfectly cohesive class\n\
            - LCOM3 > 1: Consider splitting into LCOM3 classes\n\
            - LCOM4 accounts for methods that call each other\n\n\
            Language Support:\n\
            - Python: self.attr access, self.method() calls\n\
            - TypeScript/JS: this.attr, this.method()\n\
            - Rust: self.field, self.method()\n\
            - Go: receiver.field access patterns\n\n\
            Cohesion Levels:\n\
            - High (LCOM3 = 1): Well-designed cohesive class\n\
            - Medium (LCOM3 = 2): Minor cohesion issue\n\
            - Low (LCOM3 = 3-4): Consider splitting\n\
            - VeryLow (LCOM3 >= 5): Strongly recommend splitting"
    )]
    Cohesion {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show classes with LCOM3 above threshold (default: show all)
        #[arg(long, short = 't', value_name = "N")]
        threshold: Option<u32>,

        /// Sort output by LCOM4 (highest first)
        #[arg(long, short = 's')]
        sort: bool,

        /// Show only classes with low cohesion (LCOM3 > 1)
        #[arg(long)]
        violations_only: bool,

        /// Show connected components (which methods belong together)
        #[arg(long)]
        show_components: bool,
    },

    /// Generate unified metrics report combining all analyzers
    #[command(
        name = "report",
        about = "Generate comprehensive metrics report",
        long_about = "Generate a unified metrics report combining all analyzers.\n\n\
            This command runs all metric analyzers in parallel and produces\n\
            a comprehensive report with:\n\n\
            - Project-level summary (averages, totals)\n\
            - Per-file metrics breakdown\n\
            - Per-function unified metrics (CC, cognitive, MI, etc.)\n\
            - Per-class cohesion metrics\n\
            - Detected issues with severity levels\n\n\
            Quality Gates:\n\
            Use --fail-on critical to fail CI if critical issues are found.\n\
            Use --fail-on warning to fail on warnings or critical issues.\n\n\
            Threshold Presets:\n\
            - default: Industry standard thresholds\n\
            - strict: Stricter thresholds for high-quality code\n\
            - relaxed: More permissive for legacy codebases"
    )]
    Report {
        /// Path to file or directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Threshold preset (default, strict, relaxed)
        #[arg(long, default_value = "default")]
        thresholds: String,

        /// Sort functions by field (cyclomatic, cognitive, maintainability, loc, nesting)
        #[arg(long, value_name = "FIELD")]
        sort_by: Option<String>,

        /// Show only functions with issues
        #[arg(long)]
        issues_only: bool,

        /// Skip coupling analysis (faster for large projects)
        #[arg(long)]
        skip_coupling: bool,

        /// Fail with exit code 1 if issues of specified severity found (warning, critical)
        #[arg(long, value_name = "LEVEL")]
        fail_on: Option<String>,

        /// Maximum number of files to analyze (0 = unlimited)
        #[arg(long, default_value = "0")]
        max_files: usize,

        /// Show top N worst functions (default: 20)
        #[arg(long, default_value = "20")]
        top: usize,

        /// Include detailed Halstead token lists
        #[arg(long)]
        show_tokens: bool,
    },
}

// =============================================================================
// SECURITY SUBCOMMANDS
// =============================================================================

/// Security scan output format
#[derive(Clone, Copy, ValueEnum, Default, Debug)]
enum SecurityOutputFormat {
    /// JSON output
    #[default]
    Json,
    /// SARIF output for GitHub/GitLab security tab
    Sarif,
    /// Human-readable text output
    Text,
}

#[derive(Subcommand)]
enum SecurityCommands {
    /// Run all security analyzers (unified scan)
    #[command(
        name = "scan",
        about = "Run all security analyzers on a path",
        long_about = "Run all security analyzers in parallel and generate a unified report.\n\n\
            Analyzers included:\n\
            - SQL Injection (CWE-89)\n\
            - Command Injection (CWE-78)\n\
            - Cross-Site Scripting (XSS) (CWE-79)\n\
            - Path Traversal (CWE-22)\n\
            - Secrets Detection (CWE-798)\n\
            - Weak Cryptography (CWE-327)\n\
            - Unsafe Deserialization (CWE-502)\n\
            - ReDoS (CWE-1333)\n\n\
            Output formats:\n\
            - json: Standard JSON output\n\
            - sarif: SARIF v2.1 format for CI/CD integration (GitHub, GitLab)\n\
            - text: Human-readable text output\n\n\
            Suppression:\n\
            - Use '# brrr-ignore: SQLI-001' or '// brrr-ignore: CMD-002' to suppress findings\n\
            - Also supports 'nosec', 'noqa', 'security-ignore' comment formats\n\n\
            Exit codes:\n\
            - 0: No findings above fail-on threshold\n\
            - 1: Findings found above fail-on threshold\n\n\
            Examples:\n\
            - brrr security scan .                        # Scan current directory\n\
            - brrr security scan src/ --severity high     # Only high/critical issues\n\
            - brrr security scan . --format sarif         # SARIF output for CI\n\
            - brrr security scan . --category injection   # Only injection issues\n\
            - brrr security scan . --fail-on high         # Exit 1 if high+ issues found"
    )]
    Scan {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, sarif, text)
        #[arg(long = "output", value_enum, default_value = "json")]
        output_format: SecurityOutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        confidence: String,

        /// Categories to scan (comma-separated: injection,secrets,crypto,deserialization,redos,all)
        #[arg(long)]
        category: Option<String>,

        /// Severity threshold for exit code 1 (critical, high, medium, low)
        #[arg(long, default_value = "high")]
        fail_on: String,

        /// Include suppressed findings in output
        #[arg(long)]
        include_suppressed: bool,

        /// Maximum number of files to scan (0 = unlimited)
        #[arg(long, default_value = "0")]
        max_files: usize,
    },

    /// Scan for SQL injection vulnerabilities
    #[command(
        name = "sql-injection",
        about = "Scan for SQL injection vulnerabilities",
        long_about = "Detect SQL injection vulnerabilities in Python and TypeScript/JavaScript code.\n\n\
            Detects unsafe patterns:\n\
            - String concatenation: \"SELECT * FROM users WHERE id = \" + user_input\n\
            - f-strings (Python): f\"SELECT * FROM users WHERE id = {user_input}\"\n\
            - Template literals (TS): `SELECT * FROM users WHERE id = ${userId}`\n\
            - Format strings: \"SELECT ... %s\" % user_input\n\n\
            Safe patterns NOT flagged:\n\
            - Parameterized queries: cursor.execute(\"SELECT ... WHERE id = ?\", (id,))\n\
            - ORM methods with proper escaping"
    )]
    SqlInjection {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low)
        #[arg(long, default_value = "low")]
        min_severity: String,
    },

    /// Scan for command injection vulnerabilities
    #[command(
        name = "command-injection",
        about = "Scan for command injection vulnerabilities",
        long_about = "Detect command injection vulnerabilities in source code.\n\n\
            Detects dangerous patterns:\n\
            - os.system(user_input) - Python shell execution\n\
            - subprocess.call(cmd, shell=True) - Python subprocess with shell\n\
            - eval(user_input) / exec(user_input) - Code injection\n\
            - child_process.exec(cmd) - Node.js shell execution\n\
            - Runtime.exec(cmd) - Java process execution\n\
            - system(cmd) / popen(cmd) - C/C++ shell execution\n\
            - exec.Command(cmd) - Go command execution\n\
            - Command::new(cmd) - Rust process spawning\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, C/C++, Java\n\n\
            Severity levels:\n\
            - CRITICAL: Shell execution with user input (os.system, shell=True)\n\
            - HIGH: Process execution with user-controlled path\n\
            - MEDIUM: Argument injection risk\n\
            - LOW: Pattern match only, no confirmed taint"
    )]
    CommandInjection {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, c, cpp, java)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for Cross-Site Scripting (XSS) vulnerabilities
    #[command(
        name = "xss",
        about = "Scan for XSS vulnerabilities",
        long_about = "Detect Cross-Site Scripting (XSS) vulnerabilities in JavaScript/TypeScript code.\n\n\
            Detects dangerous patterns:\n\
            - element.innerHTML = user_input (DOM XSS)\n\
            - document.write(user_input)\n\
            - insertAdjacentHTML(pos, user_input)\n\
            - dangerouslySetInnerHTML={{ __html: user_input }} (React)\n\
            - $(selector).html(user_input) (jQuery)\n\
            - v-html=\"user_input\" (Vue)\n\
            - [innerHTML]=\"user_input\" (Angular)\n\
            - eval(user_input) / new Function(user_input)\n\
            - setTimeout/setInterval with string argument\n\
            - Template literals with HTML: `<div>${user_input}</div>`\n\n\
            Safe patterns NOT flagged:\n\
            - element.textContent = user_input (safe text assignment)\n\
            - element.innerText = user_input (safe text assignment)\n\
            - DOMPurify.sanitize(user_input) (sanitized)\n\
            - encodeURIComponent(user_input) (encoded)\n\n\
            Supports: JavaScript, TypeScript, JSX, TSX, Vue"
    )]
    Xss {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (javascript, typescript)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for path traversal (directory traversal) vulnerabilities
    #[command(
        name = "path-traversal",
        about = "Scan for path traversal vulnerabilities",
        long_about = "Detect path traversal (directory traversal) vulnerabilities in source code.\n\n\
            Path traversal allows attackers to access files outside the intended directory\n\
            by manipulating path inputs with sequences like '../' or absolute paths.\n\n\
            Detects dangerous patterns:\n\
            - open(user_input) - Direct file open without validation\n\
            - os.path.join(base, user_input) - Still vulnerable to absolute paths and ..\n\
            - Path(user_input).read_text() - Python pathlib\n\
            - fs.readFile(user_input) - Node.js file system\n\
            - std::fs::read(user_input) - Rust file system\n\
            - os.Open(path) - Go file system\n\
            - fopen(path) - C file operations\n\
            - shutil.copy/rmtree with user input - Python high-impact operations\n\
            - Hardcoded '../' patterns in strings\n\n\
            Safe patterns NOT flagged:\n\
            - realpath() + startswith() validation\n\
            - os.path.basename() / path.basename() to extract filename\n\
            - Allowlist validation against known filenames\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, C/C++\n\n\
            WARNING: Even with path validation, symlink attacks may still be possible!"
    )]
    PathTraversal {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for hardcoded secrets and credentials
    #[command(
        name = "secrets",
        about = "Scan for hardcoded secrets and credentials",
        long_about = "Detect hardcoded secrets, API keys, and credentials in source code.\n\n\
            Detects secrets from major providers:\n\
            - AWS Access Keys (AKIA...)\n\
            - GitHub Tokens (ghp_, gho_, ghs_, ghr_, github_pat_...)\n\
            - GitLab Tokens (glpat-...)\n\
            - Slack Tokens (xox[baprs]-...)\n\
            - Stripe Keys (sk_live_, sk_test_, rk_live_...)\n\
            - Google API Keys (AIza...)\n\
            - OpenAI Keys (sk-..., sk-proj-...)\n\
            - Anthropic Keys (sk-ant-...)\n\
            - SendGrid Keys (SG....)\n\
            - npm/PyPI Tokens\n\
            - Private Keys (RSA, EC, SSH, PGP)\n\
            - JWTs (eyJ...)\n\
            - Database connection strings with credentials\n\n\
            Also detects:\n\
            - Generic password/api_key/secret assignments\n\
            - High-entropy strings (potential secrets)\n\n\
            NOT flagged (false positive reduction):\n\
            - Environment variable reads: os.environ['KEY'], process.env.KEY\n\
            - Config file reads: config.get('password')\n\
            - Placeholder values: 'YOUR_API_KEY_HERE', 'changeme', 'xxx'\n\
            - Test files (reduced severity)\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, Java, C/C++, Ruby, PHP, YAML, JSON, env files"
    )]
    Secrets {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,

        /// Include high-entropy string detection
        #[arg(long, default_value = "true")]
        include_entropy: bool,
    },

    /// Scan for weak cryptography usage
    #[command(
        name = "crypto",
        about = "Scan for weak cryptography usage",
        long_about = "Detect weak cryptographic algorithms and insecure patterns in source code.\n\n\
            Detects weak algorithms:\n\
            - Hash: MD5, SHA-1 (for security purposes)\n\
            - Cipher: DES, 3DES, RC4, Blowfish\n\
            - RSA < 2048 bits\n\
            - ECB mode (reveals patterns in encrypted data)\n\n\
            Detects insecure usage:\n\
            - Hardcoded encryption keys\n\
            - Hardcoded IVs (should be random)\n\
            - Predictable random for crypto (random.random(), Math.random())\n\n\
            Context-aware detection:\n\
            - SAFE: MD5 for file checksums/cache keys (non-security)\n\
            - SAFE: SHA-1 for git operations (non-security context)\n\
            - UNSAFE: MD5/SHA-1 for passwords, signatures, tokens\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, Java, C/C++"
    )]
    Crypto {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,

        /// Include likely-safe patterns (checksums, cache keys)
        #[arg(long)]
        include_safe: bool,
    },

    /// Scan for unsafe deserialization vulnerabilities
    #[command(
        name = "deserialization",
        about = "Scan for unsafe deserialization vulnerabilities",
        long_about = "Detect unsafe deserialization vulnerabilities that can lead to RCE.\n\n\
            WHY DESERIALIZATION IS DANGEROUS:\n\
            Unsafe deserialization can execute arbitrary code WITHOUT obvious sinks.\n\
            Python pickle's __reduce__ protocol executes code during unpickling.\n\
            Java gadget chains (Commons Collections, etc.) achieve RCE via object graphs.\n\n\
            Detects dangerous patterns:\n\
            - Python: pickle.load/loads, yaml.load (without SafeLoader), marshal,\n\
              shelve.open, dill, cloudpickle, jsonpickle, torch.load, joblib.load\n\
            - Java: ObjectInputStream.readObject(), XMLDecoder, XStream, Kryo, Hessian\n\
            - JavaScript/TypeScript: eval(), new Function(), node-serialize,\n\
              serialize-javascript, js-yaml (unsafe mode)\n\
            - Ruby: Marshal.load, YAML.load (unsafe)\n\
            - PHP: unserialize()\n\n\
            Safe patterns NOT flagged:\n\
            - yaml.safe_load() (Python)\n\
            - YAML.safe_load() (Ruby)\n\
            - JSON.parse() (inherently safe)\n\
            - numpy.load(allow_pickle=False)\n\
            - PHP unserialize with allowed_classes=false\n\n\
            Data flow tracking:\n\
            - HTTP request body/parameters\n\
            - File uploads\n\
            - Network sockets\n\
            - Message queues (Kafka, RabbitMQ, Celery)\n\
            - Database fields\n\n\
            Supports: Python, TypeScript/JavaScript, Java (Ruby, PHP via patterns)"
    )]
    Deserialization {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, java)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,

        /// Include possibly-safe patterns for review
        #[arg(long)]
        include_safe: bool,
    },

    /// Scan for Regular Expression Denial of Service (ReDoS) vulnerabilities
    #[command(
        name = "redos",
        about = "Scan for ReDoS vulnerabilities",
        long_about = "Detect Regular Expression Denial of Service (ReDoS) vulnerabilities.\n\n\
            ReDoS occurs when a regex can be made to take exponential time\n\
            on certain malicious inputs, causing denial of service.\n\n\
            Detects dangerous patterns:\n\
            - Evil regex with nested quantifiers: (a+)+ (a*)*\n\
            - Overlapping alternations: (a|a)+\n\
            - Polynomial complexity patterns\n\
            - Exponential complexity patterns\n\n\
            Patterns in user-facing regex:\n\
            - re.match(user_input, text) - Python\n\
            - new RegExp(user_input) - JavaScript\n\
            - regex::Regex::new(&user_input) - Rust\n\
            - Pattern.compile(user_input) - Java\n\
            - regexp.Compile(user_input) - Go\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, Java"
    )]
    Redos {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for log injection vulnerabilities
    #[command(
        name = "log-injection",
        about = "Scan for log injection vulnerabilities",
        long_about = "Detect log injection vulnerabilities in source code.\n\n\
            Log injection allows attackers to:\n\
            - Forge log entries via newline injection\n\
            - Perform CRLF injection in HTTP logs\n\
            - Exploit log viewers with ANSI terminal escapes\n\
            - Trigger format string attacks (Log4j-style ${jndi:...})\n\
            - Inject HTML/XSS in web-based log viewers\n\n\
            Detects dangerous patterns:\n\
            - Python: logger.info(f'User: {user_input}')\n\
            - TypeScript: console.log(`User: ${userInput}`)\n\
            - Go: log.Printf('User: %s', userInput)\n\
            - Rust: info!('User: {}', user_input)\n\
            - Java: log.info('User: ' + userInput) (Log4j risk)\n\
            - C/C++: printf(user_input) (format string risk)\n\n\
            Safe patterns NOT flagged:\n\
            - Structured logging: logger.info('event', extra={'user': user})\n\
            - Sanitized: logger.info(sanitize(user_input))\n\
            - Input.replace('\\n', '\\\\n') (newline escaped)\n\n\
            CWE References:\n\
            - CWE-117: Log Injection\n\
            - CWE-134: Format String Vulnerability\n\
            - CWE-93: CRLF Injection\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, Java, C/C++"
    )]
    LogInjection {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java, c, cpp)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for HTTP header injection vulnerabilities
    #[command(
        name = "header-injection",
        about = "Scan for HTTP header injection vulnerabilities",
        long_about = "Detect HTTP header injection vulnerabilities.\n\n\
            Attacks: CRLF injection, open redirect, session fixation,\n\
            cache poisoning, X-Forwarded-* bypass.\n\n\
            Critical headers: Location, Set-Cookie, Content-Type,\n\
            Content-Disposition, X-Forwarded-*\n\n\
            CWE: 113 (Response Splitting), 601 (Redirect), 384 (Session Fix)"
    )]
    HeaderInjection {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for Server-Side Template Injection (SSTI) vulnerabilities
    #[command(
        name = "template-injection",
        about = "Scan for template injection (SSTI) vulnerabilities",
        long_about = "Detect Server-Side Template Injection vulnerabilities in source code.\n\n\
            SSTI occurs when user input is embedded into template strings that are\n\
            processed by a server-side template engine, potentially leading to RCE.\n\n\
            Detects dangerous patterns:\n\n\
            Python:\n\
            - render_template_string(user_input) - Flask SSTI\n\
            - Template(user_input).render() - Jinja2 direct\n\
            - jinja2.from_string(user_input)\n\
            - mako.template.Template(user_input) - Mako RCE\n\
            - tornado.template.Template(user_input)\n\n\
            JavaScript/TypeScript:\n\
            - ejs.render(user_input) - EJS SSTI\n\
            - Handlebars.compile(user_input)\n\
            - pug.render(user_input) - Pug/Jade\n\
            - nunjucks.renderString(user_input)\n\
            - new Function('return `' + input + '`')\n\n\
            Ruby:\n\
            - ERB.new(user_input).result - Full Ruby execution\n\
            - Liquid::Template.parse(user_input)\n\n\
            Unsafe filter detection:\n\
            - {{ var|safe }} - Disables escaping\n\
            - {% autoescape false %}\n\
            - mark_safe(user_input) - Django\n\n\
            Safe patterns NOT flagged:\n\
            - render_template('page.html', name=name) - Variables passed safely\n\
            - SandboxedEnvironment().from_string(template) - Jinja2 sandbox\n\n\
            CWE Reference: CWE-1336 (Template Injection)\n\n\
            Supports: Python, TypeScript/JavaScript, Ruby"
    )]
    TemplateInjection {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, ruby)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for Server-Side Request Forgery (SSRF) vulnerabilities
    #[command(
        name = "ssrf",
        about = "Scan for SSRF vulnerabilities",
        long_about = "Detect Server-Side Request Forgery (SSRF) vulnerabilities in source code.\n\n\
            SSRF allows attackers to induce the server to make requests to unintended\n\
            locations, potentially accessing internal services, cloud metadata, etc.\n\n\
            Detects dangerous patterns:\n\
            - Full URL control: requests.get(user_url)\n\
            - Partial URL control: requests.get(f'http://{user_host}/api')\n\
            - fetch(user_url) - JavaScript/TypeScript\n\
            - axios.get(user_url) - Node.js\n\
            - http.Get(url) - Go\n\
            - reqwest::get(url) - Rust\n\
            - URL.openConnection() - Java\n\n\
            Cloud metadata detection:\n\
            - AWS/GCP/Azure: 169.254.169.254\n\
            - Alibaba Cloud: 100.100.100.200\n\
            - GCP: metadata.google.internal\n\
            - Internal networks: 10.x, 172.16.x, 192.168.x\n\n\
            URL bypass detection:\n\
            - user@host patterns (auth bypass)\n\
            - Localhost variants: 127.0.0.1, 0.0.0.0, ::1\n\
            - Encoded IPs: 0x7f000001, %31%36%39\n\n\
            Safe patterns NOT flagged:\n\
            - URL allowlist validation\n\
            - Scheme/host validation before request\n\
            - Hardcoded safe URLs\n\n\
            Supports: Python, TypeScript/JavaScript, Go, Rust, Java"
    )]
    Ssrf {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript, go, rust, java)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },

    /// Scan for missing or weak input validation
    #[command(
        name = "input-validation",
        about = "Scan for missing or weak input validation",
        long_about = "Detect missing or weak input validation before data is used in sensitive operations.\n\n\
            Tracks validation patterns:\n\
            - Type check: isinstance(x, str), typeof x === 'string'\n\
            - Length check: len(x) > 100, x.length <= max\n\
            - Range check: 0 <= value <= 100\n\
            - Format check: re.match(pattern, x), regex.test(x)\n\
            - Allowlist check: x in ALLOWED_VALUES, allowlist.includes(x)\n\
            - Sanitization: html.escape(x), encodeURIComponent(x)\n\
            - Null check: if not x, if (x ?? default)\n\n\
            Per-sink validation requirements:\n\
            - Database queries: Need type check, length check\n\
            - File operations: Need path validation, format check\n\
            - System commands: Need sanitization, allowlist\n\
            - Numeric operations: Need range check, type check\n\
            - Serialization: Need type check\n\n\
            The analyzer builds a validation graph that:\n\
            - Tracks which validations apply to each variable\n\
            - Propagates validation status through assignments\n\
            - Checks at sink points for required validations\n\n\
            Supports: Python, TypeScript/JavaScript"
    )]
    InputValidation {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, typescript, javascript)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Include recommended (not just required) validations
        #[arg(long, default_value = "true")]
        include_recommended: bool,

        /// Maximum number of files to scan (0 = unlimited)
        #[arg(long, default_value = "0")]
        max_files: usize,
    },

    /// Scan for JavaScript Prototype Pollution vulnerabilities
    #[command(
        name = "prototype-pollution",
        about = "Scan for prototype pollution vulnerabilities",
        long_about = "Detect JavaScript Prototype Pollution vulnerabilities (CWE-1321).\n\n\
            Prototype pollution allows attackers to modify JavaScript object prototypes,\n\
            leading to property injection, security bypasses, or RCE via gadget chains.\n\n\
            Dangerous patterns detected:\n\
            - Direct: obj.__proto__.x = y, Object.prototype.x = y\n\
            - Bracket: obj[userKey] = value (key could be '__proto__')\n\
            - Deep merge: _.merge(target, userObj), $.extend(true, ...)\n\
            - Recursive set: _.set(obj, userPath, value)\n\
            - Object spread: {...userObj}\n\n\
            Vulnerable functions:\n\
            - lodash: merge, defaultsDeep, set, setWith\n\
            - jQuery: $.extend(true, ...)\n\
            - deepmerge, merge-deep, dot-prop\n\n\
            Gadget chains (RCE potential):\n\
            - child_process.spawn (env pollution)\n\
            - require (mainModule pollution)\n\
            - ejs.render (opts pollution)\n\
            - handlebars.compile, pug.compile\n\n\
            Safe patterns NOT flagged:\n\
            - Object.create(null) as base\n\
            - Map instead of object\n\
            - hasOwnProperty check before assignment\n\
            - Object.freeze on prototype\n\n\
            Supports: JavaScript, TypeScript, JSX, TSX"
    )]
    PrototypePollution {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (javascript, typescript)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (critical, high, medium, low, info)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Minimum confidence level (high, medium, low)
        #[arg(long, default_value = "low")]
        min_confidence: String,
    },
}

// =============================================================================
// DATAFLOW SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum DataflowCommands {
    /// Analyze live variables (backward data flow analysis)
    #[command(
        name = "live-vars",
        about = "Analyze live variables in a function",
        long_about = "Perform live variable analysis to find which variables are live at each program point.\n\n\
            A variable is 'live' at a point if its value may be used before being redefined.\n\
            This is a backward data flow analysis that flows from uses to definitions.\n\n\
            Applications:\n\
            - Dead store detection: x = 5; x = 10; (first assignment is dead)\n\
            - Unused parameter detection\n\
            - Register allocation hints (non-interfering vars can share registers)\n\
            - Memory optimization (can free when not live)\n\n\
            Data Flow Equations:\n\
            - USE[B] = variables used in B before any definition\n\
            - DEF[B] = variables defined in B\n\
            - IN[B]  = USE[B] UNION (OUT[B] - DEF[B])\n\
            - OUT[B] = UNION(IN[S]) for all successors S"
    )]
    LiveVars {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Show interference graph (variables that are live at the same time)
        #[arg(long)]
        interference: bool,

        /// Only show dead stores (suppress other output)
        #[arg(long)]
        dead_stores_only: bool,
    },

    /// Analyze reaching definitions (forward data flow analysis)
    #[command(
        name = "reaching-defs",
        about = "Analyze reaching definitions in a function",
        long_about = "Perform reaching definitions analysis to find which definitions reach each use.\n\n\
            A definition 'reaches' a program point if there is a path from the definition\n\
            to that point without any redefinition of the variable.\n\n\
            Applications:\n\
            - Uninitialized variable detection\n\
            - Def-use chain construction\n\
            - Copy propagation analysis\n\
            - Dead code detection"
    )]
    ReachingDefs {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Show def-use chains
        #[arg(long)]
        chains: bool,
    },

    /// Constant propagation analysis (forward data flow analysis)
    #[command(
        name = "constants",
        about = "Analyze constant propagation in a function",
        long_about = "Perform constant propagation analysis to find which variables have known constant values.\n\n\
            Constant propagation tracks variables that hold constant values throughout execution.\n\
            This is a forward data flow analysis that flows from definitions to uses.\n\n\
            Lattice structure (per variable):\n\
            - Bottom: undefined/unreachable\n\
            - Constant(v): known constant value v\n\
            - Top: unknown/not constant\n\n\
            Applications:\n\
            - Constant folding: x = 2 + 3 becomes x = 5\n\
            - Dead branch elimination: if (true) always takes one branch\n\
            - Optimization hints for the compiler"
    )]
    Constants {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show folding opportunities and dead branches
        #[arg(long)]
        optimizations_only: bool,
    },

    /// Very busy expressions analysis (backward data flow with intersection)
    #[command(
        name = "very-busy",
        about = "Analyze very busy (anticipable) expressions in a function",
        long_about = "Perform very busy expressions analysis to find expressions that will definitely\n\
            be computed on ALL paths from a program point before any operand is redefined.\n\n\
            This is a backward data flow analysis with INTERSECTION at join points,\n\
            making it stricter than live variable analysis.\n\n\
            Key difference from live variables:\n\
            - Live Variables: UNION at joins (may be used on some path)\n\
            - Very Busy: INTERSECTION at joins (must be used on all paths)\n\n\
            Data Flow Equations:\n\
            - USE[B] = expressions computed in B before any operand is redefined\n\
            - KILL[B] = expressions containing variables defined in B\n\
            - OUT[B] = INTERSECTION(IN[S]) for all successors S\n\
            - IN[B] = USE[B] UNION (OUT[B] - KILL[B])\n\n\
            Applications:\n\
            - Code hoisting: move common expressions before conditionals\n\
            - Partial redundancy elimination (PRE)\n\
            - Speculative computation optimization\n\n\
            Example:\n\
            if cond:           # a + b is very busy here\n\
                x = a + b      # Can hoist to: t = a + b\n\
            else:              # before the if statement\n\
                y = a + b"
    )]
    VeryBusy {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show hoisting opportunities (suppress full analysis output)
        #[arg(long)]
        hoisting_only: bool,
    },

    /// Available expressions analysis (forward data flow with intersection)
    #[command(
        name = "available-exprs",
        about = "Analyze available expressions for CSE optimization",
        long_about = "Perform available expressions analysis to find expressions that have been\n\
            computed on ALL paths to each program point and whose operands have not been redefined.\n\n\
            This is a FORWARD data flow analysis with INTERSECTION at join points,\n\
            making it a must-analysis (unlike reaching definitions which is may-analysis).\n\n\
            Key properties:\n\
            - Forward flow: tracks what has been computed before this point\n\
            - Intersection at joins: expression must be available on ALL paths\n\
            - Killed by redefinition: if any variable in expression is modified\n\n\
            Data Flow Equations:\n\
            - GEN[B] = expressions computed in B (not later killed)\n\
            - KILL[B] = expressions containing variables defined in B\n\
            - IN[B] = INTERSECTION(OUT[P]) for all predecessors P\n\
            - OUT[B] = GEN[B] UNION (IN[B] - KILL[B])\n\n\
            Applications:\n\
            - Common Subexpression Elimination (CSE): reuse previously computed values\n\
            - Loop-invariant code motion: identify expressions that can be hoisted\n\
            - Redundant computation detection: find unnecessary recalculations\n\n\
            Example:\n\
            x = a + b        # Expression a+b computed\n\
            y = a + b        # a+b is AVAILABLE - CSE opportunity!\n\
            a = 10           # Kills a+b\n\
            z = a + b        # a+b NOT available (must recompute)"
    )]
    AvailableExprs {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show CSE opportunities (suppress full analysis output)
        #[arg(long)]
        cse_only: bool,
    },
}

// =============================================================================
// QUALITY SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum QualityCommands {
    /// Detect code clones (duplicate code)
    #[command(
        name = "clones",
        about = "Detect code clones (duplicate code)",
        long_about = "Detect code duplicates (clones) using textual analysis.\n\n\
            Type-1 Clone Detection:\n\
            - Exact copies ignoring whitespace and comments\n\
            - Uses rolling hash (Rabin fingerprint) algorithm\n\
            - Memory-efficient streaming for large codebases\n\n\
            Automatic Exclusions:\n\
            - License headers (MIT, Apache, GPL, etc.)\n\
            - Test fixtures (intentional duplication)\n\
            - Generated code (protobuf, thrift, etc.)\n\n\
            Output includes:\n\
            - Clone groups with all instances\n\
            - Total duplicated lines and percentage\n\
            - File locations and preview snippets"
    )]
    Clones {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Minimum clone size in lines (default: 6)
        #[arg(long, short = 'm', default_value = "6")]
        min_lines: usize,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Include license headers in detection (default: exclude)
        #[arg(long)]
        include_licenses: bool,

        /// Include test fixtures in detection (default: exclude)
        #[arg(long)]
        include_tests: bool,

        /// Include generated code in detection (default: exclude)
        #[arg(long)]
        include_generated: bool,

        /// Maximum file size in bytes (default: 1MB)
        #[arg(long, default_value = "1048576")]
        max_file_size: u64,
    },

    /// Detect structural code clones (Type-2/Type-3)
    #[command(
        name = "structural-clones",
        about = "Detect structural code clones (Type-2/Type-3)",
        long_about = "Detect code duplicates based on AST structure.\n\n\
            Clone Types:\n\
            - Type-2: Same structure with different identifiers/literals\n\
            - Type-3: Similar structure with small modifications\n\n\
            Algorithm:\n\
            - Normalizes function ASTs to canonical form\n\
            - Replaces identifiers with placeholders ($VAR1, $VAR2)\n\
            - Replaces literals with type markers ($INT, $STRING)\n\
            - Hashes normalized form for fast Type-2 detection\n\
            - Computes edit distance for Type-3 similarity\n\n\
            Example (original -> normalized):\n\
            def calc_area(width, height):\n\
                return width * height\n\
            \n\
            Normalized: def $FUNC($PARAM1, $PARAM2): return $PARAM1 * $PARAM2\n\n\
            Filters out likely false positives:\n\
            - Simple getters/setters\n\
            - Interface/trait implementations\n\
            - Test functions (optional)"
    )]
    StructuralClones {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Similarity threshold for Type-3 detection (0.0-1.0)
        #[arg(long, short = 's', default_value = "0.8")]
        similarity: f64,

        /// Minimum AST nodes for a function to be considered
        #[arg(long, default_value = "10")]
        min_nodes: usize,

        /// Minimum lines for a function to be considered
        #[arg(long, short = 'm', default_value = "3")]
        min_lines: usize,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Detect only Type-2 (exact structural) clones
        #[arg(long)]
        type2_only: bool,

        /// Detect only Type-3 (near-miss) clones
        #[arg(long)]
        type3_only: bool,

        /// Include test functions in detection (default: exclude)
        #[arg(long)]
        include_tests: bool,

        /// Include accessors (getters/setters) in detection (default: exclude)
        #[arg(long)]
        include_accessors: bool,

        /// Include interface implementations in detection (default: exclude)
        #[arg(long)]
        include_interface_impls: bool,

        /// Show filtered (likely false positive) clones
        #[arg(long)]
        show_filtered: bool,

        /// Maximum file size in bytes (default: 1MB)
        #[arg(long, default_value = "1048576")]
        max_file_size: u64,

        /// Maximum functions to compare for Type-3 (default: 1000)
        #[arg(long, default_value = "1000")]
        max_comparisons: usize,
    },

    /// Detect God classes (classes that do too much)
    #[command(
        name = "god-class",
        about = "Detect God classes (classes that violate Single Responsibility Principle)",
        long_about = "Detect God classes using weighted scoring based on multiple indicators.\n\n\
            Indicators:\n\
            - Method count: Classes with > 20 methods (+2 per excess method)\n\
            - Attribute count: Classes with > 15 attributes (+1 per excess attribute)\n\
            - Line count: Classes with > 500 lines (+1 per 100 excess lines)\n\
            - LCOM (cohesion): Classes with LCOM3 > 2 (+5 per excess component)\n\
            - Complexity: Sum of all method complexities\n\n\
            Severity Levels:\n\
            - Low (score 10-20): Minor issues, consider reviewing\n\
            - Medium (score 20-35): Notable issues, should refactor\n\
            - High (score 35-50): Serious issues, strongly recommend refactoring\n\
            - Critical (score 50+): Severe issues, refactor immediately\n\n\
            Automatic Exclusions:\n\
            - Test classes (TestCase, *Test, *Spec)\n\
            - Generated code (detected by markers in path)\n\n\
            Output includes:\n\
            - Class name, location, and line range\n\
            - Indicator values and score breakdown\n\
            - Suggested class splits based on responsibility analysis"
    )]
    GodClass {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Score threshold for God class detection (default: 10.0)
        #[arg(long, short = 't', default_value = "10.0")]
        threshold: f64,

        /// Method count threshold (default: 20)
        #[arg(long, default_value = "20")]
        method_threshold: u32,

        /// Attribute count threshold (default: 15)
        #[arg(long, default_value = "15")]
        attribute_threshold: u32,

        /// Line count threshold (default: 500)
        #[arg(long, default_value = "500")]
        line_threshold: u32,

        /// LCOM threshold (default: 2)
        #[arg(long, default_value = "2")]
        lcom_threshold: u32,

        /// Include test classes in detection (default: exclude)
        #[arg(long)]
        include_tests: bool,

        /// Include framework classes in detection (default: include)
        #[arg(long)]
        exclude_framework: bool,

        /// Include generated code in detection (default: exclude)
        #[arg(long)]
        include_generated: bool,

        /// Maximum file size in bytes (default: 1MB)
        #[arg(long, default_value = "1048576")]
        max_file_size: u64,

        /// Minimum severity to report (low, medium, high, critical)
        #[arg(long, default_value = "low")]
        min_severity: String,
    },

    /// Detect long methods (methods that are too long and complex)
    #[command(
        name = "long-method",
        about = "Detect long methods (methods with too much code/complexity)",
        long_about = "Detect methods that are too long and complex using multiple metrics.\n\n\
            Detection Metrics:\n\
            - Lines of code: Methods > 30 lines (configurable)\n\
            - Statements: Methods > 25 statements (configurable)\n\
            - Local variables: Methods > 10 variables (configurable)\n\
            - Cyclomatic complexity: Methods > 10 (configurable)\n\
            - Nesting depth: Methods > 4 levels deep (configurable)\n\
            - Parameters: Methods > 5 parameters (configurable)\n\n\
            Context-Aware Analysis:\n\
            - Test methods: Higher thresholds (often have long setup)\n\
            - Constructors: Higher thresholds for DI setup\n\
            - Factory methods: Adjusted for object construction\n\
            - Configuration methods: Adjusted for initialization\n\n\
            Severity Levels:\n\
            - Minor: 1 threshold exceeded\n\
            - Moderate: 2 thresholds exceeded\n\
            - Major: 3 thresholds exceeded\n\
            - Critical: 4+ thresholds exceeded\n\n\
            Output includes:\n\
            - Detailed metrics for each flagged method\n\
            - Extraction candidates (loop bodies, conditionals, try blocks)\n\
            - Refactoring suggestions with line ranges\n\
            - Suggested method names for extractions"
    )]
    LongMethod {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Maximum lines threshold (default: 30)
        #[arg(long, default_value = "30")]
        max_lines: u32,

        /// Maximum statements threshold (default: 25)
        #[arg(long, default_value = "25")]
        max_statements: u32,

        /// Maximum variables threshold (default: 10)
        #[arg(long, default_value = "10")]
        max_variables: u32,

        /// Maximum cyclomatic complexity threshold (default: 10)
        #[arg(long, default_value = "10")]
        max_complexity: u32,

        /// Maximum nesting depth threshold (default: 4)
        #[arg(long, default_value = "4")]
        max_nesting: u32,

        /// Maximum parameters threshold (default: 5)
        #[arg(long, default_value = "5")]
        max_parameters: u32,

        /// Use strict thresholds (20 lines, 6 complexity)
        #[arg(long)]
        strict: bool,

        /// Use lenient thresholds (50 lines, 15 complexity)
        #[arg(long)]
        lenient: bool,

        /// Disable context-aware threshold adjustments
        #[arg(long)]
        no_context: bool,

        /// Show extraction candidates and suggestions
        #[arg(long)]
        show_suggestions: bool,

        /// Minimum severity to report (minor, moderate, major, critical)
        #[arg(long, default_value = "minor")]
        min_severity: String,

        /// Sort by score (worst methods first)
        #[arg(long, short = 's')]
        sort: bool,
    },

    /// Detect circular dependencies
    #[command(
        name = "circular",
        about = "Detect circular dependencies in imports, classes, or call graph",
        long_about = "Detect circular dependencies at multiple granularity levels.\n\n\
            Dependency Levels:\n\
            - Package: Package-to-package cycles (directory boundaries)\n\
            - Module: File-to-file import cycles (A imports B imports A)\n\
            - Class: Class usage cycles (A uses B uses A)\n\
            - Function: Call graph cycles (A calls B calls A)\n\n\
            Algorithm:\n\
            - Uses Tarjan's algorithm for Strongly Connected Components (SCCs)\n\
            - O(V + E) complexity for efficient analysis\n\
            - Detects nested/overlapping cycles and marks them critical\n\n\
            Severity Levels:\n\
            - Low: Single-package tight coupling (may be intentional)\n\
            - Medium: 2-node cycles\n\
            - High: 3-5 node cycles\n\
            - Critical: 6+ node cycles or nested cycles\n\n\
            Output includes:\n\
            - All detected cycles with participants and files\n\
            - Severity assessment and test involvement flags\n\
            - Breaking suggestions with impact scores\n\
            - Recommended refactoring techniques"
    )]
    Circular {
        /// Path to project directory to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Dependency level to analyze (package, module, class, function)
        #[arg(long, short = 'l', value_enum, default_value = "module")]
        level: CircularLevelArg,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum severity to report (low, medium, high, critical)
        #[arg(long, default_value = "low")]
        min_severity: String,

        /// Include test dependencies in analysis
        #[arg(long)]
        include_tests: bool,

        /// Exclude cycles that appear intentional (tightly coupled modules)
        #[arg(long)]
        exclude_intentional: bool,

        /// Maximum number of cycles to report
        #[arg(long, default_value = "100")]
        max_cycles: usize,

        /// Maximum number of breaking suggestions to generate
        #[arg(long, default_value = "20")]
        max_suggestions: usize,
    },

    /// Detect design patterns
    #[command(
        name = "patterns",
        about = "Detect design patterns in code",
        long_about = "Detect common design patterns using AST analysis and heuristics.\n\n\
            Creational Patterns:\n\
            - Singleton: Private constructor, static instance, getInstance()\n\
            - Factory: Methods returning interface types, *Factory naming\n\
            - Builder: Method chaining, build() method, fluent setters\n\n\
            Structural Patterns:\n\
            - Adapter: Wraps another class, implements different interface\n\
            - Decorator: Wraps same interface, delegates to component\n\
            - Proxy: Same interface, controls access to subject\n\n\
            Behavioral Patterns:\n\
            - Observer: Subscribe/notify pattern, listener collections\n\
            - Strategy: Interface with multiple implementations\n\
            - Command: execute() method, encapsulates action\n\n\
            Modern Patterns:\n\
            - Dependency Injection: Constructor injection, interface dependencies\n\
            - Repository: Data access abstraction with CRUD methods\n\n\
            Confidence Scoring:\n\
            - 0.9-1.0: Very high confidence (explicit implementation)\n\
            - 0.7-0.9: High confidence (strong heuristic match)\n\
            - 0.5-0.7: Medium confidence (partial match)\n\
            - 0.3-0.5: Low confidence (weak signals)\n\n\
            Language-specific idioms:\n\
            - Python: __new__ for singleton\n\
            - Rust: traits, lazy_static/OnceCell\n\
            - Go: implicit interfaces\n\
            - Java/TypeScript: standard OOP patterns"
    )]
    Patterns {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Filter to specific pattern (singleton, factory, builder, observer, strategy, etc.)
        #[arg(long, short = 'p')]
        pattern: Option<String>,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Minimum confidence threshold (0.0-1.0)
        #[arg(long, short = 'c', default_value = "0.5")]
        min_confidence: f64,

        /// Include test files in detection
        #[arg(long)]
        include_tests: bool,

        /// Include generated code in detection
        #[arg(long)]
        include_generated: bool,

        /// Disable modern pattern detection (DI, Repository)
        #[arg(long)]
        no_modern: bool,

        /// Maximum file size in bytes (default: 1MB)
        #[arg(long, default_value = "1048576")]
        max_file_size: u64,
    },

    /// Analyze test quality metrics (assertion density, isolation, mutation score estimation)
    #[command(
        name = "test-quality",
        about = "Analyze test quality metrics",
        long_about = "Analyze test quality beyond coverage with assertion density and mutation score estimation.\n\n\
            Metrics:\n\
            - Assertion Density: Number of assertions per test function\n\
            - Test Isolation: Detection of shared state and external dependencies\n\
            - Boundary Testing: Detection of edge case coverage\n\
            - Mutation Score Estimation: Heuristic likelihood of catching mutations\n\n\
            Assertion Patterns by Language:\n\
            - Python: assert, assertEqual, assertTrue, pytest.raises, mock.assert_*\n\
            - JavaScript/TypeScript: expect().toBe(), assert.equal(), toThrow()\n\
            - Rust: assert!, assert_eq!, assert_ne!, #[should_panic]\n\
            - Go: t.Error, t.Errorf, t.Fatal, testify/assert\n\
            - Java: assertEquals, assertTrue, assertThrows, verify()\n\n\
            Quality Grades:\n\
            - A: >= 4 assertions/test, comprehensive testing\n\
            - B: 3 assertions/test, good coverage\n\
            - C: 2 assertions/test, basic testing\n\
            - D: 1 assertion/test, weak testing\n\
            - F: 0 assertions, test does nothing\n\n\
            Output includes:\n\
            - Per-file and per-test metrics\n\
            - Weak test identification with issues\n\
            - Improvement suggestions sorted by priority"
    )]
    TestQuality {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Use strict configuration (higher thresholds)
        #[arg(long)]
        strict: bool,

        /// Use lenient configuration (lower thresholds)
        #[arg(long)]
        lenient: bool,

        /// Minimum assertion density threshold (default: 2.0)
        #[arg(long, default_value = "2.0")]
        min_density: f64,

        /// Flag tests with only one assertion
        #[arg(long, default_value = "true")]
        flag_single_assertion: bool,

        /// Analyze mock usage
        #[arg(long, default_value = "true")]
        analyze_mocks: bool,

        /// Check for boundary testing (edge cases)
        #[arg(long, default_value = "true")]
        check_boundaries: bool,

        /// Estimate mutation score
        #[arg(long, default_value = "true")]
        estimate_mutations: bool,

        /// Show weak tests only
        #[arg(long)]
        weak_only: bool,

        /// Minimum grade to pass (A, B, C, D)
        #[arg(long)]
        min_grade: Option<char>,
    },

    /// Analyze documentation coverage
    #[command(
        name = "doc-coverage",
        about = "Analyze documentation coverage and quality",
        long_about = "Analyze documentation coverage for code quality assessment.\n\n\
            Documentation Types Checked:\n\
            - Module/file level docstrings\n\
            - Class/struct docstrings\n\
            - Function/method docstrings\n\
            - Parameter documentation\n\
            - Return value documentation\n\
            - Exception/error documentation\n\
            - Usage examples\n\n\
            Quality Scoring (0-5):\n\
            - 0: No documentation\n\
            - 1: Has docstring but minimal (just name restatement)\n\
            - 2: Documents purpose\n\
            - 3: Documents parameters/returns\n\
            - 4: Has usage examples\n\
            - 5: Comprehensive (purpose + params + examples)\n\n\
            Language Support:\n\
            - Python: \"\"\"docstring\"\"\" with Google/NumPy/Sphinx formats\n\
            - TypeScript/JavaScript: /** JSDoc */ comments\n\
            - Rust: /// line doc or /** */ block doc\n\
            - Go: // comment before function\n\
            - Java: /** Javadoc */ comments\n\n\
            Output includes:\n\
            - Coverage rate by type (module, class, function, method)\n\
            - List of undocumented public items\n\
            - Quality score per file\n\
            - Documentation TODOs sorted by priority"
    )]
    DocCoverage {
        /// Path to file or directory to scan
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only analyze public items
        #[arg(long)]
        public_only: bool,

        /// Minimum quality score for an item to be considered documented (0-5)
        #[arg(long, default_value = "2")]
        min_quality: u8,

        /// Check for parameter documentation
        #[arg(long, default_value = "true")]
        check_params: bool,

        /// Check for return value documentation
        #[arg(long, default_value = "true")]
        check_returns: bool,

        /// Check for exception/error documentation
        #[arg(long, default_value = "true")]
        check_exceptions: bool,

        /// Check for examples
        #[arg(long, default_value = "true")]
        check_examples: bool,

        /// Flag docstrings that just restate function name
        #[arg(long, default_value = "true")]
        flag_restatement: bool,

        /// Use strict configuration (public only, min score 3)
        #[arg(long)]
        strict: bool,

        /// Use lenient configuration (public only, min score 1, no param checks)
        #[arg(long)]
        lenient: bool,

        /// Minimum lines for a function to require documentation
        #[arg(long, default_value = "3")]
        min_lines: u32,
    },

    /// Detect semantically similar code (Type-4 clones)
    #[command(
        name = "semantic-clones",
        about = "Detect semantically similar code using embedding-based analysis",
        long_about = "Detect Type-4 (semantic) code clones using embedding-based similarity.\n\n\
            Algorithm:\n\
            - Extracts code units (functions, methods, classes)\n\
            - Generates embeddings using TEI server (or placeholders for testing)\n\
            - Computes cosine similarity between all unit pairs\n\
            - Clusters similar units and suggests refactoring\n\n\
            Similarity Thresholds:\n\
            - Identical (>=98%): Semantically equivalent code\n\
            - High (>=90%): Strong deduplication candidates\n\
            - Medium (>=80%): Review for consolidation\n\
            - Low (>=70%): Informational only\n\n\
            Output Formats:\n\
            - json: Full structured output with metadata\n\
            - text: Human-readable summary with file:line references\n\
            - dot: Graph format for visualization\n\n\
            Examples:\n\
            brrr quality semantic-clones ./src --threshold 0.85\n\
            brrr quality semantic-clones ./src --cross-file-only --format text\n\
            brrr quality semantic-clones ./src --suggest-refactor"
    )]
    SemanticClones {
        /// Path to analyze
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Minimum similarity threshold (0.0-1.0)
        #[arg(long, default_value = "0.80")]
        threshold: f32,

        /// Minimum lines for a unit to be considered
        #[arg(long, default_value = "5")]
        min_lines: usize,

        /// Only compare across different files
        #[arg(long)]
        cross_file_only: bool,

        /// Include test files
        #[arg(long)]
        include_tests: bool,

        /// Output format (json, text, dot)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Generate refactoring suggestions
        #[arg(long)]
        suggest_refactor: bool,

        /// Maximum results to show
        #[arg(long, default_value = "100")]
        max_results: usize,

        /// Language filter (python, rust, typescript, etc.)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// TEI server URL for embeddings
        #[arg(long, default_value = "http://localhost:8080")]
        tei_url: String,
    },

    /// Find code similar to a specific location
    #[command(
        name = "similar-to",
        about = "Find code similar to a specific function or location",
        long_about = "Find code units similar to a specific location using semantic analysis.\n\n\
            Location Formats:\n\
            - file.py:function_name - Find function by name\n\
            - file.py:ClassName.method_name - Find method by class.method\n\
            - file.py:42 - Find unit containing line 42\n\n\
            Examples:\n\
            brrr quality similar-to src/auth.py:authenticate --k 10\n\
            brrr quality similar-to src/models.py:User.validate ./src"
    )]
    SimilarTo {
        /// Location (file:function_name or file:line)
        location: String,

        /// Number of similar results
        #[arg(long, short, default_value = "10")]
        k: usize,

        /// Path to search in
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Minimum similarity threshold (0.0-1.0)
        #[arg(long, default_value = "0.70")]
        threshold: f32,

        /// Output format
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Language filter
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// TEI server URL for embeddings
        #[arg(long, default_value = "http://localhost:8080")]
        tei_url: String,
    },
}

// =============================================================================
// ANALYZE SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum AnalyzeCommands {
    /// Track resource lifecycle (acquire/release) to detect leaks
    #[command(
        name = "resource-flow",
        about = "Analyze resource lifecycle to detect leaks and bugs",
        long_about = "Track resource lifecycle (acquire/release) to detect:\n\n\
            - Resource leaks (acquired but never released)\n\
            - Double-free/double-close bugs\n\
            - Use-after-release bugs\n\n\
            Supported Resource Types:\n\
            - File handles (open, File::open, os.Open)\n\
            - Database connections (connect, Connection)\n\
            - Network sockets\n\
            - Locks/Mutexes (lock.acquire, Mutex::lock)\n\
            - Memory allocations (malloc, new)\n\n\
            Safe Patterns Detected:\n\
            - Python: with statement (context managers)\n\
            - Rust: RAII, Drop trait automatic release\n\
            - Go: defer statement\n\
            - Java: try-with-resources\n\
            - C++: smart pointers (unique_ptr, shared_ptr)\n\n\
            The analysis is path-sensitive, tracking resource state along\n\
            control flow paths to detect leaks on exception paths."
    )]
    ResourceFlow {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze
        function: String,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show issues (suppress safe patterns and stats)
        #[arg(long)]
        issues_only: bool,

        /// Minimum severity to report (critical, high, medium, low)
        #[arg(long, default_value = "low")]
        min_severity: String,
    },

    /// Infer invariants (preconditions, postconditions, loop invariants)
    #[command(
        name = "invariants",
        about = "Infer invariants from code (preconditions, postconditions, loop invariants)",
        long_about = "Infer program invariants from source code:\n\n\
            Preconditions (must hold before function execution):\n\
            - Explicit assertions (assert x > 0)\n\
            - Guard clauses (if x is None: raise)\n\
            - Type checks (if not isinstance(x, int): raise)\n\
            - Range checks (if x < 0: raise)\n\n\
            Postconditions (must hold after function execution):\n\
            - Return value assertions\n\
            - Final assertions before return\n\
            - Return type constraints\n\n\
            Loop Invariants (hold at each iteration):\n\
            - Variables not modified in loop body\n\
            - Bounds on loop variables\n\
            - Monotonicity (always increasing/decreasing)\n\n\
            Each invariant has a confidence score (0.0-1.0):\n\
            - 1.0: Explicit assertion\n\
            - 0.9: Guard clause with raise/throw\n\
            - 0.8: Type check\n\
            - 0.7: Comparison check\n\
            - 0.5-0.6: Inferred from patterns"
    )]
    Invariants {
        /// Source file to analyze
        file: PathBuf,

        /// Function name to analyze (analyzes all if not specified)
        #[arg(long)]
        function: Option<String>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Only show preconditions
        #[arg(long)]
        preconditions_only: bool,

        /// Only show postconditions
        #[arg(long)]
        postconditions_only: bool,

        /// Only show loop invariants
        #[arg(long)]
        loop_invariants_only: bool,

        /// Include suggested assertions
        #[arg(long, default_value = "true")]
        suggestions: bool,

        /// Minimum confidence level for inferred invariants (0.0-1.0)
        #[arg(long, default_value = "0.5")]
        min_confidence: f64,
    },

    /// Extract implicit state machines from code
    #[command(
        name = "state-machine",
        about = "Extract implicit state machines from code",
        long_about = "Extract implicit finite state machines from code that manages state\n\
            through variables, enums, or string comparisons.\n\n\
            Detects patterns like:\n\
            - Variables named `state`, `status`, `phase`, `mode`\n\
            - String/enum comparisons in conditions\n\
            - Variable set to string literals/enum values\n\
            - Transitions guarded by current state\n\n\
            Example:\n\
            ```python\n\
            class Connection:\n\
                def __init__(self):\n\
                    self.state = \"disconnected\"\n\n\
                def connect(self):\n\
                    if self.state == \"disconnected\":\n\
                        self.state = \"connecting\"\n\
                        # ... do connection\n\
                        self.state = \"connected\"\n\
            ```\n\n\
            This extracts a state machine:\n\
            disconnected -> connecting -> connected\n\n\
            Output formats:\n\
            - json: Structured data for tooling integration\n\
            - text: Human-readable summary\n\
            - mermaid: Mermaid diagram for documentation\n\
            - dot: Graphviz DOT format for high-quality visualization"
    )]
    StateMachine {
        /// Source file to analyze
        file: PathBuf,

        /// Function or class name to analyze (analyzes all if not specified)
        #[arg(long)]
        scope: Option<String>,

        /// Language (auto-detected from extension if not specified)
        #[arg(long, value_enum)]
        lang: Option<Language>,

        /// Output format (json, text, mermaid, dot)
        #[arg(long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Variable name pattern to track (default: state, status, phase, mode)
        #[arg(long)]
        var_pattern: Option<String>,

        /// Minimum confidence for state detection (0.0-1.0)
        #[arg(long, default_value = "0.5")]
        min_confidence: f64,

        /// Include validation issues in output
        #[arg(long)]
        validate: bool,
    },
}

// =============================================================================
// SEMANTIC SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum SemanticCommands {
    /// Build semantic index for project
    #[command(
        about = "Build semantic index for project",
        long_about = "Build unified semantic index for a project (auto-detects all languages).\nFirst run downloads embedding model (1.3GB default, 80MB for MiniLM)."
    )]
    Index {
        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Language to index (default: all = auto-detect)
        #[arg(long, value_enum, default_value = "all")]
        lang: WarmLanguage,

        /// Embedding model: Qwen/Qwen3-Embedding-0.6B (default) or all-MiniLM-L6-v2 (80MB)
        #[arg(long)]
        model: Option<String>,

        /// Inference backend (default: auto - prefers TEI server if available)
        #[arg(long, value_enum, default_value = "auto")]
        backend: SemanticBackend,

        /// MRL embedding dimension (Qwen3 only). Smaller = faster search, less memory.
        #[arg(long)]
        dimension: Option<usize>,
    },

    /// Search code using natural language queries
    #[command(
        about = "Search semantically",
        long_about = "Search code using natural language queries.\nSearches unified index (all languages). Requires: brrr semantic index ."
    )]
    Search {
        /// Natural language query
        query: String,

        /// Project root
        #[arg(default_value = ".")]
        path: PathBuf,

        /// Number of results
        #[arg(short, long, default_value = "5")]
        k: usize,

        /// Include call graph expansion
        #[arg(long)]
        expand: bool,

        /// Embedding model (uses index model if not specified)
        #[arg(long)]
        model: Option<String>,

        /// Inference backend (tei = text-embeddings-inference server)
        #[arg(long, value_enum, default_value = "auto")]
        backend: SemanticBackend,

        /// Query task type for instruction-aware models
        #[arg(long, value_enum, default_value = "code_search")]
        task: SearchTask,

        /// Bypass index cache and reload from disk
        #[arg(long)]
        force_reload: bool,
    },

    /// Pre-load and warm up embedding model for faster first query
    #[command(
        about = "Pre-load and warm up embedding model for faster first query",
        long_about = "Pre-load the embedding model into memory (and GPU if available).\nThis speeds up the first semantic search by eliminating model load time."
    )]
    Warmup {
        /// Model name (default: Qwen3-Embedding-0.6B)
        #[arg(long)]
        model: Option<String>,
    },

    /// Unload model and free GPU memory
    #[command(
        about = "Unload model and free GPU memory",
        long_about = "Unload the embedding model from memory to free GPU/RAM.\nUseful when you need to free resources for other tasks."
    )]
    Unload,

    /// Index cache management
    #[command(subcommand)]
    Cache(CacheCommands),

    /// Show compute device and backend info
    #[command(
        about = "Show compute device and backend info",
        long_about = "Show detected compute device (CUDA, MPS, CPU) and available backends."
    )]
    Device,

    /// Show GPU/memory statistics
    #[command(
        about = "Show GPU/memory statistics",
        long_about = "Show GPU memory usage and model statistics.\nRequires model to be loaded (run semantic search first)."
    )]
    Memory,
}

#[derive(Subcommand)]
enum CacheCommands {
    /// Clear all cached indexes
    #[command(about = "Clear all cached indexes")]
    Clear,

    /// Show cache statistics
    #[command(about = "Show cache statistics")]
    Stats,

    /// Invalidate index for a specific project
    #[command(about = "Invalidate index for a specific project")]
    Invalidate {
        /// Project path to invalidate
        #[arg(default_value = ".")]
        path: PathBuf,
    },
}

// =============================================================================
// DAEMON SUBCOMMANDS
// =============================================================================

#[derive(Subcommand)]
enum DaemonCommands {
    /// Start daemon for project (background)
    #[command(
        about = "Start daemon for project (background)",
        long_about = "Start the brrr daemon for faster repeated queries."
    )]
    Start {
        /// Project path
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Stop daemon gracefully
    #[command(about = "Stop daemon gracefully")]
    Stop {
        /// Project path
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Check if daemon is running
    #[command(about = "Check if daemon running")]
    Status {
        /// Project path
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Send raw JSON command to daemon
    #[command(about = "Send raw JSON command to daemon")]
    Query {
        /// Command to send (e.g., ping, status, search)
        cmd: String,

        /// Project path
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Notify daemon of file change
    #[command(about = "Notify daemon of file change (triggers reindex at threshold)")]
    Notify {
        /// Path to changed file
        file: PathBuf,

        /// Project path
        #[arg(short, long, default_value = ".")]
        project: PathBuf,
    },

    /// Internal: Run as daemon server (hidden from help)
    #[command(hide = true)]
    Serve {
        /// Project path
        #[arg(short, long)]
        project: PathBuf,
    },
}

// =============================================================================
// JSON FORMATTING HELPER
// =============================================================================

use serde::Serialize;

/// Format a value as JSON, optionally compact.
///
/// By default, outputs pretty-printed JSON for human readability.
/// When `compact` is true, outputs minified JSON for token efficiency.
fn format_json<T: Serialize>(value: &T, compact: bool) -> Result<String> {
    if compact {
        serde_json::to_string(value).context("Failed to serialize JSON")
    } else {
        serde_json::to_string_pretty(value).context("Failed to serialize JSON")
    }
}

// =============================================================================
// MAIN ENTRY POINT
// =============================================================================

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize tracing based on verbosity
    let filter = match cli.verbose {
        0 => EnvFilter::new("warn"),
        1 => EnvFilter::new("info"),
        2 => EnvFilter::new("debug"),
        _ => EnvFilter::new("trace"),
    };

    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .init();

    match cli.command {
        Commands::Tree {
            path,
            ext,
            show_hidden,
            max_depth,
        } => {
            cmd_tree(&path, &ext, show_hidden, cli.no_ignore, max_depth)?;
        }

        Commands::Structure { path, lang, limit } => {
            cmd_structure(&path, lang, limit, cli.no_ignore)?;
        }

        Commands::Search {
            pattern,
            path,
            ext,
            context,
            max,
            max_files,
        } => {
            cmd_search(
                &pattern,
                &path,
                &ext,
                context,
                max,
                max_files,
                cli.no_ignore,
            )?;
        }

        Commands::Extract {
            file,
            base_path,
            filter_class,
            filter_function,
            filter_method,
        } => {
            cmd_extract(
                &file,
                base_path.as_ref(),
                filter_class,
                filter_function,
                filter_method,
                cli.compact,
            )?;
        }

        Commands::Context {
            entry,
            project,
            depth,
            lang,
        } => {
            cmd_context(&entry, &project, depth, lang, cli.compact)?;
        }

        Commands::Cfg {
            file,
            function,
            lang,
            format,
        } => {
            cmd_cfg(&file, &function, lang, format, cli.compact)?;
        }

        Commands::Dfg {
            file,
            function,
            lang,
        } => {
            cmd_dfg(&file, &function, lang, cli.compact)?;
        }

        Commands::Slice {
            file,
            function,
            line,
            direction,
            var,
            lang,
            extended,
        } => {
            cmd_slice(&file, &function, line, direction, var, lang, extended)?;
        }

        Commands::Calls {
            path,
            lang,
            extended,
        } => {
            cmd_calls(&path, lang, extended, cli.no_ignore)?;
        }

        Commands::Impact {
            func,
            path,
            depth,
            file,
            lang,
        } => {
            cmd_impact(&func, &path, depth, file, lang, cli.no_ignore)?;
        }

        Commands::Dead { path, entry, lang } => {
            cmd_dead(&path, &entry, lang, cli.no_ignore)?;
        }

        Commands::Arch { path, lang } => {
            cmd_arch(&path, lang, cli.no_ignore)?;
        }

        Commands::Imports { file, lang } => {
            cmd_imports(&file, lang)?;
        }

        Commands::Importers { module, path, lang } => {
            cmd_importers(&module, &path, lang, cli.no_ignore)?;
        }

        Commands::Warm {
            path,
            background,
            lang,
        } => {
            cmd_warm(&path, background, lang, cli.no_ignore)?;
        }

        Commands::ChangeImpact {
            files,
            session,
            git,
            git_base,
            lang,
            depth,
            run,
            project,
        } => {
            cmd_change_impact(
                &files,
                session,
                git,
                &git_base,
                lang,
                depth,
                run,
                &project,
                cli.no_ignore,
            )?;
        }

        Commands::Diagnostics {
            target,
            project,
            no_lint,
            format,
            lang,
        } => {
            cmd_diagnostics(&target, project, no_lint, format, lang)?;
        }

        Commands::Semantic(subcmd) => {
            cmd_semantic(subcmd, cli.no_ignore).await?;
        }

        Commands::Daemon(subcmd) => {
            cmd_daemon(subcmd).await?;
        }

        Commands::Doctor { install, json } => {
            cmd_doctor(install, json)?;
        }

        Commands::Security(subcmd) => {
            cmd_security(subcmd)?;
        }

        Commands::Metrics {
            path,
            lang,
            format,
            fail_on,
            cmd,
        } => {
            match cmd {
                Some(subcmd) => {
                    // Run specific metrics subcommand
                    cmd_metrics(subcmd)?;
                }
                None => {
                    // Shorthand: brrr metrics <path> runs full report
                    let path = path.unwrap_or_else(|| PathBuf::from("."));
                    let format = format.unwrap_or(OutputFormat::Text);

                    // Run full report with sensible defaults
                    let exit_code = cmd_metrics_report(
                        &path,
                        lang,
                        format,
                        "default",          // threshold_preset
                        None,               // sort_by
                        false,              // issues_only
                        false,              // skip_coupling
                        fail_on.as_deref(), // fail_on
                        0,                  // max_files (unlimited)
                        50,                 // top
                        false,              // show_tokens
                    )?;
                    if exit_code != 0 {
                        std::process::exit(exit_code);
                    }
                }
            }
        }

        Commands::Quality(subcmd) => {
            cmd_quality(subcmd)?;
        }

        Commands::Dataflow(subcmd) => {
            cmd_dataflow(subcmd)?;
        }

        Commands::Coverage(subcmd) => {
            cmd_coverage(subcmd)?;
        }

        Commands::Analyze(subcmd) => {
            cmd_analyze(subcmd)?;
        }

        Commands::Translate {
            file,
            declarations_only,
            output,
        } => {
            cmd_translate(&file, declarations_only, output)?;
        }
    }

    Ok(())
}

// =============================================================================
// TRANSLATE COMMAND HANDLER
// =============================================================================

fn cmd_translate(
    file: &Path,
    declarations_only: bool,
    output: TranslateOutputFormat,
) -> Result<()> {
    use brrr_translate::go::GoTranslator;

    // Validate file exists and is a Go file
    require_file(file)?;
    let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
    if ext != "go" {
        anyhow::bail!("Only Go files (.go) are currently supported for translation");
    }

    // Read source
    let source = std::fs::read(file).context("Failed to read source file")?;

    // Translate
    let mut translator = GoTranslator::new(&source);

    if declarations_only {
        // Only produce declarations (Module metadata)
        let module = translator
            .translate_source()
            .map_err(|e| anyhow::anyhow!("Translation error: {}", e))?;

        match output {
            TranslateOutputFormat::Json => {
                println!("{}", serde_json::to_string_pretty(&module)?);
            }
            TranslateOutputFormat::JsonCompact => {
                println!("{}", serde_json::to_string(&module)?);
            }
            TranslateOutputFormat::Text => {
                println!("Module: {}", module.name);
                println!("Path: {:?}", module.path);
                println!("Declarations: {}", module.declarations.len());
                for decl in &module.declarations {
                    match decl {
                        brrr_repr::decl::Declaration::Function { name, is_public, .. } => {
                            let vis = if *is_public { "pub " } else { "" };
                            println!("  {}fn {}", vis, name);
                        }
                        brrr_repr::decl::Declaration::Type { name, is_public, .. } => {
                            let vis = if *is_public { "pub " } else { "" };
                            println!("  {}type {}", vis, name);
                        }
                        brrr_repr::decl::Declaration::Constant { name, is_public, .. } => {
                            let vis = if *is_public { "pub " } else { "" };
                            println!("  {}const {}", vis, name);
                        }
                        _ => {}
                    }
                }
            }
        }
    } else {
        // Full translation with function bodies
        let translated = translator
            .translate()
            .map_err(|e| anyhow::anyhow!("Translation error: {}", e))?;

        match output {
            TranslateOutputFormat::Json => {
                println!("{}", serde_json::to_string_pretty(&translated)?);
            }
            TranslateOutputFormat::JsonCompact => {
                println!("{}", serde_json::to_string(&translated)?);
            }
            TranslateOutputFormat::Text => {
                println!("Module: {}", translated.module.name);
                println!("Functions: {}", translated.functions.len());
                for func in &translated.functions {
                    let vis = match func.visibility {
                        brrr_repr::types::Visibility::Public => "pub ",
                        _ => "",
                    };
                    let params: Vec<String> = func
                        .params
                        .iter()
                        .map(|p| {
                            if let Some(name) = p.name {
                                format!("{}: {:?}", "param", p.ty)
                            } else {
                                format!("{:?}", p.ty)
                            }
                        })
                        .collect();
                    let has_body = if func.body.is_some() { " {...}" } else { "" };
                    println!(
                        "  {}fn({}) -> {:?}{}",
                        vis,
                        params.join(", "),
                        func.return_type,
                        has_body
                    );
                }
                println!("Types: {}", translated.types.len());
                println!("Constants: {}", translated.constants.len());
                println!("Variables: {}", translated.variables.len());
            }
        }
    }

    Ok(())
}

// =============================================================================
// COVERAGE COMMAND HANDLER
// =============================================================================

fn cmd_coverage(cmd: CoverageCommands) -> Result<()> {
    use coverage::mapping::find_uncovered_branches_with_cfg;

    match cmd {
        CoverageCommands::Map {
            coverage_file,
            source_file,
            function,
            format,
            lang,
            suggest_tests,
            max_paths: _,
        } => {
            // Validate inputs
            require_file(&coverage_file)?;
            require_file(&source_file)?;

            // Parse coverage data
            let cov_format = format.map(coverage::CoverageFormat::from);
            let cov_data = coverage::parse_coverage_file(&coverage_file, cov_format)
                .context("Failed to parse coverage file")?;

            // Extract CFG for the function
            let lang_str = lang.map(|l| l.to_string());
            let cfg_result = cfg::extract_with_language(
                source_file.to_str().unwrap_or(""),
                &function,
                lang_str.as_deref(),
            )
            .context("Failed to extract CFG")?;

            // Map coverage to CFG
            let cfg_coverage = coverage::map_coverage_to_cfg(&cov_data, &cfg_result, &source_file)
                .context("Failed to map coverage to CFG")?;

            // Build output
            let mut output = serde_json::json!({
                "function": cfg_coverage.function_name,
                "block_coverage": cfg_coverage.block_coverage,
                "edge_coverage": cfg_coverage.edge_coverage,
                "path_coverage": cfg_coverage.path_coverage,
                "covered_blocks": cfg_coverage.covered_blocks.len(),
                "uncovered_blocks": cfg_coverage.uncovered_blocks.len(),
                "covered_edges": cfg_coverage.covered_edges.len(),
                "uncovered_edges": cfg_coverage.uncovered_edges.len(),
                "total_paths": cfg_coverage.total_paths,
                "covered_paths": cfg_coverage.covered_paths,
            });

            // Add uncovered branches
            let uncovered = find_uncovered_branches_with_cfg(&cfg_coverage, &cfg_result);
            output["uncovered_branches"] = serde_json::to_value(&uncovered)?;

            // Add test suggestions if requested
            if suggest_tests {
                let suggestions = coverage::generate_test_suggestions(&cfg_coverage, &cfg_result);
                output["test_suggestions"] = serde_json::to_value(&suggestions)?;
            }

            println!("{}", serde_json::to_string_pretty(&output)?);
        }

        CoverageCommands::Parse {
            coverage_file,
            format,
            details,
        } => {
            require_file(&coverage_file)?;

            let cov_format = format.map(coverage::CoverageFormat::from);
            let cov_data = coverage::parse_coverage_file(&coverage_file, cov_format)
                .context("Failed to parse coverage file")?;

            let summary = &cov_data.summary;

            let mut output = serde_json::json!({
                "format": cov_data.source_format.map(|f| f.to_string()),
                "files_count": cov_data.files.len(),
                "summary": {
                    "line_rate": format!("{:.1}%", summary.line_rate * 100.0),
                    "branch_rate": format!("{:.1}%", summary.branch_rate * 100.0),
                    "function_rate": format!("{:.1}%", summary.function_rate * 100.0),
                    "lines_covered": summary.lines_covered,
                    "lines_total": summary.lines_total,
                    "branches_covered": summary.branches_covered,
                    "branches_total": summary.branches_total,
                    "functions_covered": summary.functions_covered,
                    "functions_total": summary.functions_total,
                }
            });

            if details {
                let mut files_detail = Vec::new();
                for (path, file_cov) in &cov_data.files {
                    files_detail.push(serde_json::json!({
                        "path": path.to_string_lossy(),
                        "line_rate": format!("{:.1}%", file_cov.line_rate() * 100.0),
                        "branch_rate": format!("{:.1}%", file_cov.branch_rate() * 100.0),
                        "lines_covered": file_cov.lines_covered.len(),
                        "lines_not_covered": file_cov.lines_not_covered.len(),
                        "branches": file_cov.branches.len(),
                        "functions": file_cov.functions.len(),
                    }));
                }
                output["files"] = serde_json::to_value(files_detail)?;
            }

            println!("{}", serde_json::to_string_pretty(&output)?);
        }

        CoverageCommands::Uncovered {
            coverage_file,
            source_file,
            function,
            format,
            lang,
            min_priority,
        } => {
            require_file(&coverage_file)?;
            require_file(&source_file)?;

            // Parse coverage
            let cov_format = format.map(coverage::CoverageFormat::from);
            let cov_data = coverage::parse_coverage_file(&coverage_file, cov_format)
                .context("Failed to parse coverage file")?;

            // Extract CFG
            let lang_str = lang.map(|l| l.to_string());
            let cfg_result = cfg::extract_with_language(
                source_file.to_str().unwrap_or(""),
                &function,
                lang_str.as_deref(),
            )
            .context("Failed to extract CFG")?;

            // Map coverage
            let cfg_coverage = coverage::map_coverage_to_cfg(&cov_data, &cfg_result, &source_file)
                .context("Failed to map coverage to CFG")?;

            // Find uncovered branches
            let uncovered: Vec<_> = find_uncovered_branches_with_cfg(&cfg_coverage, &cfg_result)
                .into_iter()
                .filter(|b| b.priority >= min_priority)
                .collect();

            let output = serde_json::json!({
                "function": function,
                "uncovered_count": uncovered.len(),
                "branches": uncovered,
            });

            println!("{}", serde_json::to_string_pretty(&output)?);
        }

        CoverageCommands::Suggest {
            coverage_file,
            source_file,
            function,
            format,
            lang,
            max,
        } => {
            require_file(&coverage_file)?;
            require_file(&source_file)?;

            // Parse coverage
            let cov_format = format.map(coverage::CoverageFormat::from);
            let cov_data = coverage::parse_coverage_file(&coverage_file, cov_format)
                .context("Failed to parse coverage file")?;

            // Extract CFG
            let lang_str = lang.map(|l| l.to_string());
            let cfg_result = cfg::extract_with_language(
                source_file.to_str().unwrap_or(""),
                &function,
                lang_str.as_deref(),
            )
            .context("Failed to extract CFG")?;

            // Map coverage
            let cfg_coverage = coverage::map_coverage_to_cfg(&cov_data, &cfg_result, &source_file)
                .context("Failed to map coverage to CFG")?;

            // Generate suggestions
            let mut suggestions = coverage::generate_test_suggestions(&cfg_coverage, &cfg_result);
            suggestions.truncate(max);

            let output = serde_json::json!({
                "function": function,
                "suggestion_count": suggestions.len(),
                "suggestions": suggestions,
            });

            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// =============================================================================
// PROJECT ROOT RESOLUTION
// =============================================================================

/// Resolve the project root directory from a given path.
///
/// Walks up the directory tree looking for common project markers
/// (like `.git`, `Cargo.toml`, `package.json`, etc.). If no project root
/// is found, returns the original path (canonicalized if possible).
///
/// This ensures commands like `brrr calls src/` find the correct project root
/// even when invoked from a subdirectory.
///
/// # Arguments
///
/// * `path` - Starting path (file or directory)
///
/// # Returns
///
/// The detected project root, or the original path if no markers found.
fn resolve_project_root(path: &Path) -> PathBuf {
    // First try to find the project root by walking up
    if let Some(root) = get_project_root(path) {
        return root;
    }

    // Fallback: canonicalize the path or return as-is
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

// =============================================================================
// COMMAND IMPLEMENTATIONS
// =============================================================================

fn cmd_tree(
    path: &PathBuf,
    ext: &[String],
    show_hidden: bool,
    no_ignore: bool,
    max_depth: Option<usize>,
) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    let result = ast::file_tree(
        path.to_str().context("Invalid path")?,
        ext,
        show_hidden,
        no_ignore,
        max_depth,
    )
    .context("Failed to build file tree")?;

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_structure(
    path: &PathBuf,
    lang: Option<Language>,
    limit: usize,
    no_ignore: bool,
) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    // Auto-detect language if not specified
    let lang_str = lang
        .map(|l| l.to_string())
        .unwrap_or_else(|| detect_project_language(path));

    let result = ast::code_structure(
        path.to_str().context("Invalid path")?,
        Some(&lang_str),
        limit,
        no_ignore,
    )
    .context("Failed to extract code structure")?;

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_search(
    pattern: &str,
    path: &PathBuf,
    ext: &[String],
    context_lines: usize,
    max_results: usize,
    max_files: usize,
    no_ignore: bool,
) -> Result<()> {
    use std::io::{BufRead, BufReader};

    // Compile regex pattern with error handling
    let regex = regex::Regex::new(pattern)
        .map_err(|e| anyhow::anyhow!("Invalid regex pattern '{}': {}", pattern, e))?;

    // Validate path exists
    if !path.exists() {
        return Err(anyhow::anyhow!("Path not found: {}", path.display()));
    }

    // Canonicalize root path for security and consistency
    let root_path = path.canonicalize().context("Failed to canonicalize path")?;

    // Configure walker respecting ignore patterns
    let mut walker_builder = ignore::WalkBuilder::new(&root_path);

    if no_ignore {
        // Disable all ignore file processing when --no-ignore is set
        walker_builder
            .git_ignore(false)
            .git_global(false)
            .git_exclude(false)
            .ignore(false);
    } else {
        // Respect .brrrignore in addition to .gitignore (default behavior)
        walker_builder.add_custom_ignore_filename(".brrrignore");
    }

    // Skip hidden files by default (consistent with other commands)
    walker_builder.hidden(true);

    let mut results: Vec<serde_json::Value> = Vec::new();
    let mut files_scanned: usize = 0;
    let mut total_matches: usize = 0;

    // Effective max_results: 0 means unlimited
    let effective_max_results = if max_results == 0 {
        usize::MAX
    } else {
        max_results
    };

    for entry in walker_builder.build() {
        // Check file limit
        if files_scanned >= max_files {
            break;
        }

        // Check result limit
        if results.len() >= effective_max_results {
            break;
        }

        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };

        let file_path = entry.path();

        // Skip directories
        if !file_path.is_file() {
            continue;
        }

        // Apply extension filter if specified
        if !ext.is_empty() {
            let file_ext = file_path
                .extension()
                .and_then(|e| e.to_str())
                .map(|e| format!(".{}", e));

            let matches_ext = file_ext
                .as_ref()
                .map(|fe| {
                    ext.iter().any(|filter_ext| {
                        // Support both ".py" and "py" formats
                        let normalized = if filter_ext.starts_with('.') {
                            filter_ext.clone()
                        } else {
                            format!(".{}", filter_ext)
                        };
                        fe == &normalized
                    })
                })
                .unwrap_or(false);

            if !matches_ext {
                continue;
            }
        }

        files_scanned += 1;

        // Read and search file
        let file = match std::fs::File::open(file_path) {
            Ok(f) => f,
            Err(_) => continue, // Skip unreadable files
        };

        let reader = BufReader::new(file);
        let lines: Vec<String> = reader
            .lines()
            .map_while(|l| l.ok()) // Stop on first read error
            .collect();

        // Search through lines
        for (line_idx, line) in lines.iter().enumerate() {
            // Check result limit before processing
            if results.len() >= effective_max_results {
                break;
            }

            if regex.is_match(line) {
                total_matches += 1;

                // Calculate context window
                let start = line_idx.saturating_sub(context_lines);
                let end = (line_idx + context_lines + 1).min(lines.len());

                // Build context array
                let context: Vec<serde_json::Value> = (start..end)
                    .map(|i| {
                        serde_json::json!({
                            "line_number": i + 1, // 1-indexed for display
                            "content": &lines[i],
                            "is_match": i == line_idx,
                        })
                    })
                    .collect();

                // Compute relative path for cleaner output
                let rel_path = file_path
                    .strip_prefix(&root_path)
                    .unwrap_or(file_path)
                    .display()
                    .to_string();

                results.push(serde_json::json!({
                    "file": rel_path,
                    "line": line_idx + 1, // 1-indexed
                    "match": line,
                    "context": context,
                }));
            }
        }
    }

    // Build output matching Python's search command format
    let result = serde_json::json!({
        "pattern": pattern,
        "total_matches": total_matches,
        "files_scanned": files_scanned,
        "results": results,
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_extract(
    file: &PathBuf,
    base_path: Option<&PathBuf>,
    filter_class: Option<String>,
    filter_function: Option<String>,
    filter_method: Option<String>,
    compact: bool,
) -> Result<()> {
    // Validate file exists and is a regular file
    require_file(file)?;

    let file_path = file.to_str().context("Invalid file path")?;
    let base_path_str = base_path.and_then(|p| p.to_str());

    let mut module =
        ast::extract_file(file_path, base_path_str).context("Failed to extract file info")?;

    // Apply filters if specified
    if let Some(class_name) = &filter_class {
        // Filter to specific class
        module.classes.retain(|c| c.name == *class_name);
        // Clear functions when filtering by class
        module.functions.clear();
    } else if let Some(method_spec) = &filter_method {
        // Parse Class.method syntax
        if let Some((class_name, method_name)) = method_spec.split_once('.') {
            module.classes.retain(|c| c.name == class_name);
            // Filter methods within matching classes
            for class in &mut module.classes {
                class.methods.retain(|m| m.name == method_name);
            }
        }
        // Clear functions when filtering by method
        module.functions.clear();
    } else if let Some(func_name) = &filter_function {
        // Filter to specific function
        module.functions.retain(|f| f.name == *func_name);
        // Clear classes when filtering by function
        module.classes.clear();
    }

    println!("{}", format_json(&module, compact)?);
    Ok(())
}

fn cmd_context(
    entry: &str,
    project: &PathBuf,
    depth: usize,
    lang: Option<Language>,
    compact: bool,
) -> Result<()> {
    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(project);

    // Convert language enum to string for API
    let lang_str = lang.map(|l| l.to_string().to_lowercase());

    let result = callgraph::get_context_with_lang(
        project_root.to_str().context("Invalid project path")?,
        entry,
        depth,
        lang_str.as_deref(),
    )
    .context("Failed to get context")?;

    // Context outputs LLM-ready text, not JSON
    if let Some(text) = result.get("llm_context").and_then(|v| v.as_str()) {
        println!("{}", text);
    } else {
        // Fallback to JSON if no LLM context available
        println!("{}", format_json(&result, compact)?);
    }
    Ok(())
}

fn cmd_cfg(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    compact: bool,
) -> Result<()> {
    // Validate file exists and is a regular file
    require_file(file)?;

    // Convert language enum to string for API
    let lang_str = lang.map(|l| l.to_string().to_lowercase());

    let cfg_result = cfg::extract_with_language(
        file.to_str().context("Invalid file path")?,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to extract CFG")?;

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!("{}", format_json(&cfg_result, compact)?);
        }
        OutputFormat::Mermaid => {
            let mermaid = cfg::render::to_mermaid(&cfg_result);
            println!("{}", mermaid);
        }
        OutputFormat::Dot => {
            let dot = cfg::render::to_dot(&cfg_result);
            println!("{}", dot);
        }
        OutputFormat::Text => {
            // Text format: simplified output
            println!("Control Flow Graph for: {}", function);
            println!("Blocks: {}", cfg_result.blocks.len());
            println!("Edges: {}", cfg_result.edges.len());
            println!("Complexity: {}", cfg_result.cyclomatic_complexity());
            // Sort blocks by ID for consistent output
            let mut block_ids: Vec<_> = cfg_result.blocks.keys().collect();
            block_ids.sort_by_key(|id| id.0);
            for id in block_ids {
                let block = &cfg_result.blocks[id];
                println!(
                    "  Block {}: lines {}-{}",
                    block.id.0, block.start_line, block.end_line
                );
            }
        }
        OutputFormat::Csv => {
            // CSV not supported for CFG - fall back to JSON
            println!("{}", format_json(&cfg_result, compact)?);
        }
    }
    Ok(())
}

fn cmd_dfg(file: &PathBuf, function: &str, lang: Option<Language>, compact: bool) -> Result<()> {
    // Validate file exists and is a regular file
    require_file(file)?;

    // Convert language enum to string for API
    let lang_str = lang.map(|l| l.to_string().to_lowercase());

    let result = dfg::extract_with_language(
        file.to_str().context("Invalid file path")?,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to extract DFG")?;

    println!("{}", format_json(&result, compact)?);
    Ok(())
}

fn cmd_slice(
    file: &PathBuf,
    function: &str,
    line: usize,
    direction: SliceDirection,
    var: Option<String>,
    lang: Option<Language>,
    extended: bool,
) -> Result<()> {
    // Validate line number is 1-indexed (lines start at 1, not 0)
    if line == 0 {
        anyhow::bail!("Line numbers are 1-indexed. Got 0, expected >= 1");
    }

    // Validate file exists and is a regular file
    require_file(file)?;

    let file_path = file.to_str().context("Invalid file path")?;

    // Convert language enum to string for API
    let lang_str = lang.map(|l| l.to_string().to_lowercase());

    // Extract DFG for the function with language hint
    let dfg_info = dfg::extract_with_language(file_path, function, lang_str.as_deref())
        .context("Failed to extract data flow graph")?;

    // Create slice criteria - with or without variable filter
    let criteria = match &var {
        Some(v) => dfg::SliceCriteria::at_line_variable(line, v),
        None => dfg::SliceCriteria::at_line(line),
    };

    // Compute the slice based on direction
    let slice_result = match direction {
        SliceDirection::Backward => dfg::backward_slice(&dfg_info, &criteria),
        SliceDirection::Forward => dfg::forward_slice(&dfg_info, &criteria),
    };

    // Build base output (Python-compatible: only lines and count)
    let mut result = serde_json::json!({
        "lines": slice_result.lines,
        "count": slice_result.lines.len(),
    });

    // Add extended fields only when --extended flag is set
    if extended {
        let obj = result.as_object_mut().unwrap();
        obj.insert("file".to_string(), serde_json::json!(file_path));
        obj.insert("function".to_string(), serde_json::json!(function));
        obj.insert("target_line".to_string(), serde_json::json!(line));
        obj.insert(
            "direction".to_string(),
            serde_json::json!(match direction {
                SliceDirection::Backward => "backward",
                SliceDirection::Forward => "forward",
            }),
        );
        if let Some(ref v) = var {
            obj.insert("variable".to_string(), serde_json::json!(v));
        }
        obj.insert(
            "variables_in_slice".to_string(),
            serde_json::json!(slice_result.variables),
        );
        obj.insert(
            "metrics".to_string(),
            serde_json::json!({
                "slice_size": slice_result.metrics.slice_size,
                "edges_traversed": slice_result.metrics.edges_traversed,
                "slice_ratio": slice_result.metrics.slice_ratio,
                "variable_count": slice_result.metrics.variable_count,
            }),
        );
    }

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_calls(
    path: &PathBuf,
    lang: Option<Language>,
    extended: bool,
    no_ignore: bool,
) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);

    // Auto-detect language if not specified
    let detected_lang = lang
        .map(|l| l.to_string())
        .unwrap_or_else(|| detect_project_language(&project_root));

    // Use cached graph with incremental updates, respecting no_ignore flag
    let graph =
        callgraph::get_or_build_graph_with_config(&project_root, Some(&detected_lang), no_ignore)
            .context("Failed to build call graph")?;

    // Build edges with optional extended fields for Python compatibility
    let edges: Vec<serde_json::Value> = graph
        .edges
        .iter()
        .map(|e| {
            let mut edge = serde_json::json!({
                "from_file": e.caller.file,
                "from_func": e.caller.name,
                "to_file": e.callee.file,
                "to_func": e.callee.name,
            });

            // Only include call_line when extended flag is set
            if extended {
                edge["call_line"] = serde_json::json!(e.call_line);
            }

            edge
        })
        .collect();

    let result = serde_json::json!({
        "edges": edges,
        "count": graph.edges.len(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_impact(
    func: &str,
    path: &PathBuf,
    depth: usize,
    file_filter: Option<String>,
    lang: Option<Language>,
    no_ignore: bool,
) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);

    // Auto-detect language if not specified
    let detected_lang = lang
        .map(|l| l.to_string())
        .unwrap_or_else(|| detect_project_language(&project_root));

    // Build graph with no_ignore support
    let graph =
        callgraph::get_or_build_graph_with_config(&project_root, Some(&detected_lang), no_ignore)
            .context("Failed to build call graph")?;

    // Analyze impact using the graph
    let config = callgraph::ImpactConfig::new().with_depth(depth);
    let result = callgraph::analyze_impact(&graph, func, config);

    // Convert CallerInfo to FunctionRef for output
    let callers: Vec<callgraph::FunctionRef> = result
        .callers
        .into_iter()
        .map(|c| callgraph::FunctionRef {
            file: c.file,
            name: c.name,
            qualified_name: c.qualified_name,
        })
        .collect();

    // Apply file filter if specified
    let filtered: Vec<_> = if let Some(filter) = file_filter {
        callers
            .into_iter()
            .filter(|f| f.file.contains(&filter))
            .collect()
    } else {
        callers
    };

    let result = serde_json::json!({
        "function": func,
        "callers": filtered.iter().map(|f| {
            serde_json::json!({
                "file": f.file,
                "name": f.name,
                "qualified_name": f.qualified_name,
            })
        }).collect::<Vec<_>>(),
        "count": filtered.len(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_dead(
    path: &PathBuf,
    entry_points: &[String],
    lang: Option<Language>,
    no_ignore: bool,
) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);

    // Set language-specific heuristics: use provided language or auto-detect
    let detected_lang = lang
        .map(|l| l.to_string())
        .unwrap_or_else(|| detect_project_language(&project_root));

    // Build graph with no_ignore support
    let mut graph =
        callgraph::get_or_build_graph_with_config(&project_root, Some(&detected_lang), no_ignore)
            .context("Failed to build call graph")?;
    graph.build_indexes();

    // Build configuration with user-provided entry points and language
    let mut config = callgraph::DeadCodeConfig::default();

    // Add custom entry point patterns from --entry flag
    if !entry_points.is_empty() {
        config.extra_entry_patterns = entry_points.to_vec();
    }

    config.language = Some(detected_lang.clone());

    // Analyze dead code with the configured options using the graph built with no_ignore
    let result = callgraph::analyze_dead_code_with_config(&graph, &config);

    // Build comprehensive output with stats and entry points
    let output = serde_json::json!({
        "dead_functions": result.dead_functions.iter().map(|f| {
            serde_json::json!({
                "file": f.file,
                "name": f.name,
                "qualified_name": f.qualified_name,
                "line": f.line,
                "reason": format!("{:?}", f.reason),
                "confidence": f.confidence,
            })
        }).collect::<Vec<_>>(),
        "count": result.total_dead,
        "entry_points_used": result.entry_points,
        "custom_entry_patterns": entry_points,
        "filtered_count": result.filtered_count,
        "stats": {
            "total_functions": result.stats.total_functions,
            "entry_points": result.stats.entry_point_count,
            "reachable": result.stats.reachable_count,
            "filtered_as_callback": result.stats.filtered_as_callback,
            "filtered_as_handler": result.stats.filtered_as_handler,
            "filtered_as_decorator": result.stats.filtered_as_decorator,
            "filtered_as_dynamic": result.stats.filtered_as_dynamic,
        }
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&output).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_arch(path: &PathBuf, lang: Option<Language>, no_ignore: bool) -> Result<()> {
    // Validate path exists and is a directory
    require_directory(path)?;

    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);
    let path_str = project_root.to_str().context("Invalid path")?;

    // Auto-detect language if not specified
    let detected_lang = lang
        .map(|l| l.to_string())
        .unwrap_or_else(|| detect_project_language(&project_root));

    // Build graph with no_ignore support
    let mut graph =
        callgraph::get_or_build_graph_with_config(&project_root, Some(&detected_lang), no_ignore)
            .context("Failed to build call graph")?;
    graph.build_indexes();

    // Analyze architecture using the modular arch module
    let analysis = callgraph::analyze_architecture(&graph);

    // Format output with comprehensive architectural information
    let result = serde_json::json!({
        "root": path_str,
        "layers": {
            "entry": {
                "count": analysis.entry_functions.len(),
                "functions": analysis.entry_functions,
            },
            "middle": {
                "count": analysis.middle_functions.len(),
                "functions": analysis.middle_functions,
            },
            "leaf": {
                "count": analysis.leaf_functions.len(),
                "functions": analysis.leaf_functions,
            },
        },
        "orphan_functions": analysis.orphan_functions,
        "topological_layers": analysis.layers,
        "circular_dependencies": analysis.circular_dependencies,
        "stats": analysis.stats,
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_imports(file: &PathBuf, lang: Option<Language>) -> Result<()> {
    // Validate file exists and is a regular file
    require_file(file)?;

    let path = std::path::Path::new(file);
    let registry = lang::LanguageRegistry::global();

    // Get language handler - use provided language or auto-detect
    let lang_handler = match lang {
        Some(lang_enum) => {
            let lang_name = lang_enum.to_string().to_lowercase();
            registry
                .get_by_name(&lang_name)
                .ok_or_else(|| anyhow::anyhow!("Unsupported language: {}", lang_name))?
        }
        None => registry
            .detect_language(path)
            .ok_or_else(|| anyhow::anyhow!("Could not detect language for: {}", file.display()))?,
    };

    // Use the existing extract_imports function from ast module
    let imports = ast::extract_imports(path).context("Failed to extract imports")?;

    // Convert imports to JSON output format matching Python CLI
    let imports_json: Vec<serde_json::Value> = imports
        .iter()
        .map(|imp| {
            serde_json::json!({
                "module": imp.module,
                "names": imp.names,
                "aliases": imp.aliases,
                "is_from": imp.is_from,
                "level": imp.level,
                "line_number": imp.line_number,
                "statement": imp.statement(),
            })
        })
        .collect();

    let result = serde_json::json!({
        "file": file.display().to_string(),
        "language": lang_handler.name(),
        "imports": imports_json,
        "count": imports_json.len(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

fn cmd_importers(
    module: &str,
    path: &PathBuf,
    lang: Option<Language>,
    no_ignore: bool,
) -> Result<()> {
    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);
    let path_str = project_root.to_str().context("Invalid path")?;

    // Build scanner configuration
    let mut config = callgraph::scanner::ScanConfig::default();

    // Apply language filter: use specified or auto-detect
    let lang_str = lang
        .map(|l| l.to_string().to_lowercase())
        .unwrap_or_else(|| detect_project_language(&project_root));
    config.language = Some(lang_str.clone());

    // Apply no_ignore flag to bypass .gitignore/.brrrignore patterns
    config.no_ignore = no_ignore;

    let scanner = callgraph::scanner::ProjectScanner::new(path_str)
        .context("Failed to create project scanner")?;

    let scan_result = scanner
        .scan_with_config(&config)
        .context("Failed to scan project")?;

    let mut importers = Vec::new();

    // Process each file and extract imports
    for file_path in &scan_result.files {
        // Extract imports from file
        let imports = match ast::extract_imports(file_path) {
            Ok(imports) => imports,
            Err(_) => continue, // Skip files that fail to parse
        };

        // Check if any import matches the target module
        // Collect ALL matching imports, not just the first one
        for imp in &imports {
            if import_matches_module(imp, module) {
                // Compute relative path for cleaner output
                let rel_path = file_path
                    .strip_prefix(&project_root)
                    .unwrap_or(file_path)
                    .display()
                    .to_string();

                importers.push(serde_json::json!({
                    "file": rel_path,
                    "import_statement": imp.statement(),
                    "module": imp.module,
                    "names": imp.names,
                    "line": imp.line_number,
                }));
            }
        }
    }

    let result = serde_json::json!({
        "module": module,
        "root": project_root.display().to_string(),
        "language": lang_str,
        "importers": importers,
        "count": importers.len(),
        "files_scanned": scan_result.files.len(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );
    Ok(())
}

/// Check if an import matches the target module name.
///
/// Matching rules:
/// 1. Exact module match: `import.module == module`
/// 2. Module is the last component (e.g., searching "json" matches "os.json")
/// 3. Module is the first component (e.g., searching "os" matches "os.path")
/// 4. Any of the imported names match (e.g., searching "Path" matches `from pathlib import Path`)
/// 5. Module is an internal component (e.g., searching "path" matches "os.path.join")
fn import_matches_module(import: &ast::ImportInfo, module: &str) -> bool {
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

    // Module is in the middle (e.g., searching "path" matches "os.path.join")
    if import.module.contains(&format!(".{}.", module)) {
        return true;
    }

    // Any of the imported names match exactly
    if import.names.iter().any(|name| name == module) {
        return true;
    }

    false
}

fn cmd_warm(path: &PathBuf, background: bool, lang: WarmLanguage, no_ignore: bool) -> Result<()> {
    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let project_root = resolve_project_root(path);
    let path_str = project_root.to_str().context("Invalid path")?;

    if background {
        // Actually spawn a background process that runs warm without --background
        let exe = std::env::current_exe().context("Failed to get current executable")?;

        let mut cmd = Command::new(&exe);
        cmd.arg("warm");
        cmd.arg(path_str);

        // Pass the language argument
        cmd.args(["--lang", &lang.to_string()]);

        // Pass --no-ignore if it was set
        if no_ignore {
            cmd.arg("--no-ignore");
        }

        // NOTE: Do NOT pass --background to avoid infinite recursion

        // Detach from terminal - redirect all I/O to null
        cmd.stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());

        // On Unix, create a new process group so the process survives terminal close
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }

        let child = cmd.spawn().context("Failed to spawn background process")?;

        println!("Background indexing started (PID: {})", child.id());
        println!("Project: {}", path_str);
        println!("Language: {}", lang);

        return Ok(());
    }

    // Foreground mode - do the actual work
    let lang_str = lang.to_string();
    let lang_filter = if lang_str == "all" {
        None
    } else {
        Some(lang_str.as_str())
    };

    // Use warm_cache_with_config to respect the no_ignore flag
    callgraph::warm_cache_with_config(&project_root, lang_filter, no_ignore)
        .context("Failed to warm cache")?;

    println!("Cache warmed successfully for {}", project_root.display());
    Ok(())
}

/// Get changed files from git diff.
///
/// Runs `git diff --name-only <base>...HEAD` to find files that changed.
fn get_git_changed_files(project: &PathBuf, git_base: &str) -> Result<Vec<PathBuf>> {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(project)
        .arg("diff")
        .arg("--name-only")
        .arg(format!("{}...HEAD", git_base))
        .output()
        .context("Failed to run git diff")?;

    if !output.status.success() {
        // Try without the range syntax (for uncommitted changes)
        let output = std::process::Command::new("git")
            .arg("-C")
            .arg(project)
            .arg("diff")
            .arg("--name-only")
            .arg(git_base)
            .output()
            .context("Failed to run git diff")?;

        if !output.status.success() {
            anyhow::bail!(
                "git diff failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }

        let files: Vec<PathBuf> = String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter(|l| !l.is_empty())
            .map(|l| project.join(l))
            .collect();
        return Ok(files);
    }

    let files: Vec<PathBuf> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| project.join(l))
        .collect();

    Ok(files)
}

/// Get session-modified files (uncommitted changes).
///
/// Runs `git status --porcelain` to find modified files.
fn get_session_dirty_files(project: &PathBuf) -> Result<Vec<PathBuf>> {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(project)
        .arg("status")
        .arg("--porcelain")
        .output()
        .context("Failed to run git status")?;

    if !output.status.success() {
        anyhow::bail!(
            "git status failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let files: Vec<PathBuf> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|l| !l.is_empty())
        .filter_map(|l| {
            // Git status format: "XY filename" where XY is the status
            if l.len() > 3 {
                Some(project.join(l[3..].trim()))
            } else {
                None
            }
        })
        .collect();

    Ok(files)
}

/// Check if a file path is likely a test file.
///
/// Supports common test file conventions across languages.
fn is_test_file_path(file: &str) -> bool {
    let path_lower = file.to_lowercase();

    // Common test directory patterns
    if path_lower.contains("/test/")
        || path_lower.contains("/tests/")
        || path_lower.contains("/__tests__/")
        || path_lower.contains("/spec/")
        || path_lower.contains("/specs/")
        || path_lower.starts_with("test/")
        || path_lower.starts_with("tests/")
        || path_lower.starts_with("__tests__/")
    {
        return true;
    }

    // Extract filename
    let filename = file
        .rsplit(|c| c == '/' || c == '\\')
        .next()
        .unwrap_or(file);
    let filename_lower = filename.to_lowercase();

    // Python test patterns
    if filename_lower.starts_with("test_") && filename_lower.ends_with(".py") {
        return true;
    }
    if filename_lower.ends_with("_test.py") {
        return true;
    }

    // JavaScript/TypeScript test patterns
    if filename_lower.ends_with(".test.js")
        || filename_lower.ends_with(".test.ts")
        || filename_lower.ends_with(".test.jsx")
        || filename_lower.ends_with(".test.tsx")
        || filename_lower.ends_with(".spec.js")
        || filename_lower.ends_with(".spec.ts")
    {
        return true;
    }

    // Go test pattern
    if filename_lower.ends_with("_test.go") {
        return true;
    }

    // Rust test pattern
    if filename_lower.ends_with("_test.rs") || filename_lower == "tests.rs" {
        return true;
    }

    // Java/Kotlin patterns
    if filename.ends_with("Test.java")
        || filename.ends_with("Test.kt")
        || filename.ends_with("Tests.java")
        || filename.ends_with("Tests.kt")
    {
        return true;
    }

    false
}

/// Check if a function name looks like a test function.
///
/// Supports test naming conventions across languages.
fn is_test_function_name(name: &str) -> bool {
    // Python/pytest patterns
    if name.starts_with("test_") || name.ends_with("_test") {
        return true;
    }

    // Java/JUnit patterns
    if name.starts_with("test") && name.chars().nth(4).map_or(false, |c| c.is_uppercase()) {
        return true;
    }
    if name.ends_with("Test") || name.ends_with("Tests") {
        return true;
    }

    // BDD-style patterns
    if name.starts_with("it_") || name.starts_with("should_") || name.starts_with("spec_") {
        return true;
    }
    if name.ends_with("_spec") {
        return true;
    }

    // Test lifecycle methods
    if name == "setUp"
        || name == "tearDown"
        || name == "setUpClass"
        || name == "tearDownClass"
        || name == "beforeEach"
        || name == "afterEach"
        || name == "beforeAll"
        || name == "afterAll"
    {
        return true;
    }

    false
}

/// Run affected tests using the appropriate test runner.
fn run_affected_tests(affected_tests: &[serde_json::Value], project: &PathBuf) -> Result<()> {
    // Group tests by file for efficient execution
    let mut test_files: std::collections::HashSet<String> = std::collections::HashSet::new();
    for test in affected_tests {
        if let Some(file) = test.get("test_file").and_then(|f| f.as_str()) {
            test_files.insert(file.to_string());
        }
    }

    if test_files.is_empty() {
        println!("No tests to run.");
        return Ok(());
    }

    // Detect test runner based on files
    let is_python = test_files.iter().any(|f| f.ends_with(".py"));
    let is_js = test_files
        .iter()
        .any(|f| f.ends_with(".js") || f.ends_with(".ts"));
    let is_rust = test_files.iter().any(|f| f.ends_with(".rs"));
    let is_go = test_files.iter().any(|f| f.ends_with(".go"));

    if is_python {
        // Run pytest with specific files
        let files: Vec<&str> = test_files.iter().map(|s| s.as_str()).collect();
        println!("Running pytest for {} test files...", files.len());
        let status = std::process::Command::new("pytest")
            .args(&files)
            .current_dir(project)
            .status()
            .context("Failed to run pytest")?;
        if !status.success() {
            anyhow::bail!("pytest failed with status: {}", status);
        }
    } else if is_js {
        // Run npm test (or jest directly)
        println!("Running npm test...");
        let status = std::process::Command::new("npm")
            .args(["test", "--"])
            .args(test_files.iter())
            .current_dir(project)
            .status()
            .context("Failed to run npm test")?;
        if !status.success() {
            anyhow::bail!("npm test failed with status: {}", status);
        }
    } else if is_rust {
        // Run cargo test
        println!("Running cargo test...");
        let status = std::process::Command::new("cargo")
            .arg("test")
            .current_dir(project)
            .status()
            .context("Failed to run cargo test")?;
        if !status.success() {
            anyhow::bail!("cargo test failed with status: {}", status);
        }
    } else if is_go {
        // Run go test
        println!("Running go test...");
        let status = std::process::Command::new("go")
            .args(["test", "./..."])
            .current_dir(project)
            .status()
            .context("Failed to run go test")?;
        if !status.success() {
            anyhow::bail!("go test failed with status: {}", status);
        }
    } else {
        println!("Unknown test framework. Test files: {:?}", test_files);
    }

    Ok(())
}

fn cmd_change_impact(
    files: &[PathBuf],
    session: bool,
    git: bool,
    git_base: &str,
    lang: Option<Language>,
    depth: usize,
    run_tests: bool,
    project: &PathBuf,
    _no_ignore: bool,
) -> Result<()> {
    let project_str = project.to_str().context("Invalid project path")?;

    // Determine changed files from various sources
    let changed_files: Vec<PathBuf> = if !files.is_empty() {
        // Explicit files provided
        files.to_vec()
    } else if git {
        // Use git diff
        get_git_changed_files(project, git_base)?
    } else if session {
        // Use session dirty files
        get_session_dirty_files(project)?
    } else {
        // Auto-detect: try git first, then session
        get_git_changed_files(project, git_base)
            .or_else(|_| get_session_dirty_files(project))
            .unwrap_or_default()
    };

    if changed_files.is_empty() {
        let result = serde_json::json!({
            "changed_files": [],
            "affected_tests": [],
            "count": 0,
            "message": "No changed files detected"
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    // Build call graph for the project
    let graph = callgraph::build(project_str).context("Failed to build call graph")?;

    // Track affected tests
    let mut affected_tests: Vec<serde_json::Value> = Vec::new();
    let mut seen_tests: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();

    // Get language registry for detection
    let registry = lang::LanguageRegistry::global();

    // Project-level language detection as fallback
    let project_root = resolve_project_root(project);
    let project_lang = detect_project_language(&project_root);

    for file in &changed_files {
        // Skip non-source files
        let file_str = file.to_string_lossy().to_string();

        // Skip test files themselves (we want to find tests affected by non-test changes)
        if is_test_file_path(&file_str) {
            continue;
        }

        // Determine language for this file (prefer per-file detection, fallback to project-level)
        let file_lang = lang
            .map(|l| l.to_string())
            .or_else(|| registry.detect_language(file).map(|l| l.name().to_string()))
            .unwrap_or_else(|| project_lang.clone());

        // Skip if file doesn't match the detected language (shouldn't happen often)
        let _ = file_lang; // Mark as used

        // Try to extract functions from the changed file
        if !file.exists() {
            continue;
        }

        let module = match ast::extract_file(file.to_str().unwrap_or_default(), None) {
            Ok(m) => m,
            Err(_) => continue, // Skip files we can't parse
        };

        // For each function in the changed file, find test callers
        for func in &module.functions {
            // Use impact analysis to find all callers
            let config = callgraph::ImpactConfig::new()
                .with_depth(depth)
                .with_call_sites();
            let impact = callgraph::impact::analyze_impact(&graph, &func.name, config);

            // Check each caller to see if it's a test
            for caller in &impact.callers {
                let is_test =
                    is_test_file_path(&caller.file) || is_test_function_name(&caller.name);

                if is_test {
                    let test_key = (caller.file.clone(), caller.name.clone());
                    if seen_tests.insert(test_key) {
                        affected_tests.push(serde_json::json!({
                            "test_file": caller.file,
                            "test_function": caller.name,
                            "changed_file": file_str,
                            "changed_function": func.name,
                            "distance": caller.distance,
                        }));
                    }
                }
            }
        }

        // Also check class methods
        for class in &module.classes {
            for method in &class.methods {
                // Build qualified name for the method
                let qualified_name = format!("{}.{}", class.name, method.name);

                // Search by both qualified name and simple method name
                for search_name in [&qualified_name, &method.name] {
                    let config = callgraph::ImpactConfig::new()
                        .with_depth(depth)
                        .with_call_sites();
                    let impact = callgraph::impact::analyze_impact(&graph, search_name, config);

                    for caller in &impact.callers {
                        let is_test =
                            is_test_file_path(&caller.file) || is_test_function_name(&caller.name);

                        if is_test {
                            let test_key = (caller.file.clone(), caller.name.clone());
                            if seen_tests.insert(test_key) {
                                affected_tests.push(serde_json::json!({
                                    "test_file": caller.file,
                                    "test_function": caller.name,
                                    "changed_file": file_str,
                                    "changed_function": qualified_name,
                                    "distance": caller.distance,
                                }));
                            }
                        }
                    }
                }
            }
        }
    }

    // Sort affected tests by file and function name for deterministic output
    affected_tests.sort_by(|a, b| {
        let file_a = a.get("test_file").and_then(|f| f.as_str()).unwrap_or("");
        let file_b = b.get("test_file").and_then(|f| f.as_str()).unwrap_or("");
        let name_a = a
            .get("test_function")
            .and_then(|f| f.as_str())
            .unwrap_or("");
        let name_b = b
            .get("test_function")
            .and_then(|f| f.as_str())
            .unwrap_or("");
        (file_a, name_a).cmp(&(file_b, name_b))
    });

    let output = serde_json::json!({
        "changed_files": changed_files.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
        "affected_tests": affected_tests,
        "count": affected_tests.len(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&output).context("Failed to serialize output")?
    );

    // Optionally run the affected tests
    if run_tests && !affected_tests.is_empty() {
        println!("\n--- Running affected tests ---\n");
        run_affected_tests(&affected_tests, project)?;
    }

    Ok(())
}

fn cmd_diagnostics(
    target: &PathBuf,
    project_mode: bool,
    no_lint: bool,
    format: OutputFormat,
    lang: Option<Language>,
) -> Result<()> {
    // Validate target exists (can be file or directory)
    require_exists(target)?;

    // Convert Language enum to string if provided
    let lang_str = lang.map(|l| match l {
        Language::Python => "python",
        Language::Typescript => "typescript",
        Language::Javascript => "javascript",
        Language::Go => "go",
        Language::Rust => "rust",
        Language::Java => "java",
        Language::C => "c",
        Language::Cpp => "cpp",
        Language::Ruby => "ruby",
        Language::Php => "php",
        Language::Kotlin => "kotlin",
        Language::Swift => "swift",
        Language::Csharp => "csharp",
        Language::Scala => "scala",
        Language::Lua => "lua",
        Language::Elixir => "elixir",
    });

    // Run diagnostics based on mode (project or single file)
    let include_lint = !no_lint;
    let result = if project_mode || target.is_dir() {
        diagnostics::get_project_diagnostics(target, lang_str, include_lint)
            .context("Failed to run project diagnostics")?
    } else {
        diagnostics::get_diagnostics(target, lang_str, include_lint)
            .context("Failed to run diagnostics")?
    };

    // Output based on format
    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            let json_output = serde_json::json!({
                "target": result.target,
                "language": result.language,
                "tools": result.tools,
                "diagnostics": result.diagnostics,
                "error_count": result.error_count,
                "warning_count": result.warning_count,
                "file_count": result.file_count,
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&json_output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", diagnostics::format_diagnostics_text(&result));
        }
        _ => {
            // Default to JSON for other formats
            let json_output = serde_json::json!({
                "target": result.target,
                "language": result.language,
                "tools": result.tools,
                "diagnostics": result.diagnostics,
                "error_count": result.error_count,
                "warning_count": result.warning_count,
                "file_count": result.file_count,
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&json_output).context("Failed to serialize output")?
            );
        }
    }
    Ok(())
}

// =============================================================================
// SEMANTIC INDEX COMMAND IMPLEMENTATION
// =============================================================================

/// Build semantic index for a project.
///
/// This function:
/// 1. Extracts semantic units (functions, classes, methods) from the codebase
/// 2. Builds embedding texts with metadata enrichment
/// 3. Gets embeddings via TEI gRPC server
/// 4. Stores embeddings in a usearch vector index
/// 5. Saves unit metadata alongside the index
///
/// # Arguments
///
/// * `path` - Project root directory
/// * `lang` - Language filter (e.g., "python", "all")
/// * `model` - Embedding model name (e.g., "bge-large-en-v1.5")
/// * `backend` - Embedding backend (tei, sentence_transformers, auto)
/// * `dimension` - Optional MRL embedding dimension (Qwen3 only)
async fn cmd_semantic_index(
    path: &PathBuf,
    lang: WarmLanguage,
    model: Option<String>,
    backend: SemanticBackend,
    dimension: Option<usize>,
) -> Result<()> {
    use brrr::embedding::{IndexConfig, Metric, TeiClient, TeiClientConfig, VectorIndex};
    use brrr::semantic::{build_embedding_text, extract_units};
    use indicatif::{ProgressBar, ProgressStyle};
    use std::time::Instant;

    let start_time = Instant::now();
    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let root = resolve_project_root(path);
    let root_str = root.to_string_lossy();
    let model_name = model.unwrap_or_else(|| "bge-large-en-v1.5".to_string());
    let lang_str = lang.to_string();

    // Determine language filter
    let language_filter = if lang_str == "all" {
        "python"
    } else {
        &lang_str
    };

    eprintln!("Extracting semantic units from: {}", root_str);

    // Step 1: Extract semantic units from the codebase
    let units = if lang_str == "all" {
        // For "all" languages, extract from each supported language
        let languages = [
            "python",
            "typescript",
            "javascript",
            "go",
            "rust",
            "java",
            "c",
            "cpp",
        ];
        let mut all_units = Vec::new();
        for lang in &languages {
            match extract_units(&root_str, lang) {
                Ok(lang_units) => {
                    if !lang_units.is_empty() {
                        eprintln!("  Found {} {} units", lang_units.len(), lang);
                        all_units.extend(lang_units);
                    }
                }
                Err(e) => {
                    tracing::debug!("Failed to extract {} units: {}", lang, e);
                }
            }
        }
        all_units
    } else {
        extract_units(&root_str, language_filter).context("Failed to extract semantic units")?
    };

    if units.is_empty() {
        let result = serde_json::json!({
            "status": "complete",
            "root": root_str,
            "language": lang_str,
            "model": model_name,
            "units_indexed": 0,
            "message": "No code units found to index",
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    eprintln!("Found {} total units to index", units.len());

    // Step 2: Build embedding texts for each unit
    let texts: Vec<String> = units.iter().map(|u| build_embedding_text(u)).collect();

    eprintln!("Built embedding texts for {} units", texts.len());

    // Step 3: Get embeddings based on backend
    // Returns (embeddings, actual_model_name) - model name from TEI server
    let (embeddings, actual_model): (Vec<Vec<f32>>, String) = match backend {
        SemanticBackend::Tei | SemanticBackend::Auto => {
            // Try to connect to TEI server
            let tei_config = TeiClientConfig::from_env();
            eprintln!("Connecting to TEI server at {}", tei_config.endpoint);

            let client = match TeiClient::with_config(tei_config).await {
                Ok(c) => c,
                Err(e) => {
                    if matches!(backend, SemanticBackend::Auto) {
                        // Auto mode: report that no backend is available
                        let result = serde_json::json!({
                            "status": "error",
                            "root": root_str,
                            "language": lang_str,
                            "model": model_name,
                            "units_found": units.len(),
                            "error": format!(
                                "No embedding backend available. TEI server connection failed: {}. \
                                 Local sentence-transformers backend is not yet implemented in Rust CLI. \
                                 Please start a TEI server with: \
                                 docker run --gpus all -p 18080:80 ghcr.io/huggingface/text-embeddings-inference:89-1.8-grpc \
                                 --model-id Qwen/Qwen3-Embedding-0.6B --pooling last-token",
                                e
                            ),
                        });
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&result)
                                .context("Failed to serialize output")?
                        );
                        return Ok(());
                    } else {
                        anyhow::bail!(
                            "Failed to connect to TEI server: {}. \
                             Start a TEI server or use --backend auto.",
                            e
                        );
                    }
                }
            };

            // Get server info for dimension detection and actual model name
            let server_info = client
                .info()
                .await
                .context("Failed to get TEI server info")?;
            let server_model = server_info.model_id.clone();
            eprintln!(
                "Connected to TEI server: model={}, max_input_length={}",
                server_model, server_info.max_input_length
            );

            // Embed texts in batches
            let text_refs: Vec<&str> = texts.iter().map(String::as_str).collect();

            // Create spinner with elapsed time to show progress during embedding generation
            let spinner = ProgressBar::new_spinner();
            spinner.set_style(
                ProgressStyle::default_spinner()
                    .template("{spinner:.cyan} {msg} [{elapsed_precise}]")
                    .expect("Invalid spinner template")
                    .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"),
            );
            spinner.set_message(format!("Generating embeddings for {} texts...", text_refs.len()));
            spinner.enable_steady_tick(std::time::Duration::from_millis(100));

            let mrl_dimension = dimension.map(|d| d as u32);
            let emb = client
                .embed_with_options(&text_refs, true, true, mrl_dimension)
                .await
                .context("Failed to generate embeddings")?;

            spinner.finish_with_message(format!(
                "Generated {} embeddings",
                emb.len()
            ));
            (emb, server_model)
        }
        SemanticBackend::SentenceTransformers => {
            let result = serde_json::json!({
                "status": "error",
                "root": root_str,
                "language": lang_str,
                "model": model_name,
                "units_found": units.len(),
                "error": "Local sentence-transformers backend is not yet implemented in Rust CLI. \
                         Use --backend tei with a running TEI server, or --backend auto to auto-detect.",
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
            return Ok(());
        }
    };

    if embeddings.is_empty() {
        anyhow::bail!("TEI server returned no embeddings");
    }

    let embedding_dim = embeddings[0].len();
    eprintln!(
        "Generated {} embeddings with {} dimensions",
        embeddings.len(),
        embedding_dim
    );

    // Step 4: Build and save vector index
    let index_dir = root.join(".brrr_index");
    std::fs::create_dir_all(&index_dir).context("Failed to create index directory")?;

    let index_path = index_dir.join("vectors.usearch");
    let metadata_path = index_dir.join("metadata.json");

    let config = IndexConfig::new(embedding_dim).with_metric(Metric::InnerProduct);

    let index = VectorIndex::with_config(config).context("Failed to create vector index")?;

    // Reserve capacity for all embeddings
    index
        .reserve(embeddings.len())
        .context("Failed to reserve index capacity")?;

    // Add embeddings to index
    for (i, embedding) in embeddings.iter().enumerate() {
        index
            .add(i as u64, embedding)
            .with_context(|| format!("Failed to add embedding {} to index", i))?;
    }

    eprintln!("Built vector index with {} vectors", index.len());

    // Save vector index
    index
        .save(&index_path)
        .context("Failed to save vector index")?;

    eprintln!("Saved vector index to: {}", index_path.display());

    // Step 5: Save metadata (units) as JSON
    let metadata = serde_json::json!({
        "version": "1.0",
        "model": actual_model,
        "language": lang_str,
        "dimension": embedding_dim,
        "count": units.len(),
        "units": units,
    });

    let metadata_file =
        std::fs::File::create(&metadata_path).context("Failed to create metadata file")?;
    serde_json::to_writer_pretty(metadata_file, &metadata).context("Failed to write metadata")?;

    eprintln!("Saved metadata to: {}", metadata_path.display());

    let elapsed = start_time.elapsed();

    // Output success result
    let result = serde_json::json!({
        "status": "complete",
        "root": root_str,
        "language": lang_str,
        "model": actual_model,
        "units_indexed": units.len(),
        "dimension": embedding_dim,
        "index_path": index_path.display().to_string(),
        "metadata_path": metadata_path.display().to_string(),
        "elapsed_secs": elapsed.as_secs_f64(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );

    Ok(())
}

/// Search the semantic index for code matching a natural language query.
///
/// This function:
/// 1. Loads the vector index from `.brrr_index/vectors.usearch`
/// 2. Loads unit metadata from `.brrr_index/metadata.json`
/// 3. Gets query embedding via TEI gRPC server
/// 4. Searches the index for nearest neighbors
/// 5. Maps results back to code units with scores
///
/// # Arguments
///
/// * `query` - Natural language search query
/// * `path` - Project root directory
/// * `k` - Number of results to return
/// * `expand` - Include call graph expansion in results
/// * `backend` - Embedding backend (tei, sentence_transformers, auto)
/// * `task` - Search task type for instruction-aware models (e.g., Qwen3-Embedding)
async fn cmd_semantic_search(
    query: &str,
    path: &PathBuf,
    k: usize,
    expand: bool,
    backend: SemanticBackend,
    task: SearchTask,
) -> Result<()> {
    use brrr::embedding::{
        get_cached_query_embedding, query_in_cache, TeiClient, TeiClientConfig, VectorIndex,
    };
    use brrr::semantic::EmbeddingUnit;
    use std::time::Instant;

    let start_time = Instant::now();
    // Resolve project root (walks up to find .git, Cargo.toml, etc.)
    let root = resolve_project_root(path);
    let root_str = root.to_string_lossy();
    let num_results = if k == 0 { 10 } else { k };

    // Prepend task instruction for instruction-aware embedding models (e.g., Qwen3-Embedding)
    // This improves search relevance by signaling the embedding model's intended use case
    let query_for_embedding = if task != SearchTask::Default {
        let formatted = format!("Instruct: {}\nQuery: {}", task.as_task_string(), query);
        eprintln!(
            "Using task-aware query with instruction: {}",
            task.as_task_string()
        );
        formatted
    } else {
        query.to_string()
    };

    // Locate index directory
    let index_dir = root.join(".brrr_index");
    let index_path = index_dir.join("vectors.usearch");
    let metadata_path = index_dir.join("metadata.json");

    // Validate index exists
    if !index_path.exists() {
        let result = serde_json::json!({
            "status": "error",
            "query": query,
            "root": root_str,
            "error": format!(
                "No semantic index found at {}. Run 'brrr semantic index' first to build the index.",
                index_path.display()
            ),
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    if !metadata_path.exists() {
        let result = serde_json::json!({
            "status": "error",
            "query": query,
            "root": root_str,
            "error": format!(
                "Metadata file not found at {}. The index may be corrupted. Run 'brrr semantic index' to rebuild.",
                metadata_path.display()
            ),
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    // Load metadata to get units and model info
    eprintln!("Loading index metadata from: {}", metadata_path.display());
    let metadata_file =
        std::fs::File::open(&metadata_path).context("Failed to open metadata file")?;
    let metadata: serde_json::Value =
        serde_json::from_reader(metadata_file).context("Failed to parse metadata JSON")?;

    let units: Vec<EmbeddingUnit> = serde_json::from_value(
        metadata
            .get("units")
            .cloned()
            .unwrap_or(serde_json::json!([])),
    )
    .context("Failed to parse units from metadata")?;

    if units.is_empty() {
        let result = serde_json::json!({
            "status": "complete",
            "query": query,
            "root": root_str,
            "num_results": 0,
            "results": [],
            "message": "Index contains no units",
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    let index_model = metadata
        .get("model")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown");
    let index_dimension = metadata
        .get("dimension")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;

    eprintln!(
        "Loaded metadata: {} units, model={}, dimension={}",
        units.len(),
        index_model,
        index_dimension
    );

    // Load vector index using restore (reads dimensions from file)
    eprintln!("Loading vector index from: {}", index_path.display());
    let index = VectorIndex::restore(&index_path).context("Failed to load vector index")?;

    eprintln!(
        "Loaded index: {} vectors, {} dimensions",
        index.len(),
        index.dimensions()
    );

    // Validate index is not empty
    if index.is_empty() {
        let result = serde_json::json!({
            "status": "complete",
            "query": query,
            "root": root_str,
            "num_results": 0,
            "results": [],
            "message": "Index contains no vectors",
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    // Get query embedding based on backend (with caching)
    // Use query_for_embedding which may include task instruction for instruction-aware models
    let query_embedding: Vec<f32> = match backend {
        SemanticBackend::Tei | SemanticBackend::Auto => {
            // Check cache first before connecting to TEI server
            if query_in_cache(&query_for_embedding).unwrap_or(false) {
                eprintln!("Query embedding found in cache");
                // Retrieve from cache - the compute_fn won't be called since it's cached
                get_cached_query_embedding(&query_for_embedding, |_| {
                    unreachable!("Cache hit should not call compute function")
                })
                .context("Failed to get cached query embedding")?
            } else {
                // Cache miss - need to connect to TEI server and compute
                let tei_config = TeiClientConfig::from_env();
                eprintln!("Connecting to TEI server at {}", tei_config.endpoint);

                let client = match TeiClient::with_config(tei_config).await {
                    Ok(c) => c,
                    Err(e) => {
                        if matches!(backend, SemanticBackend::Auto) {
                            let result = serde_json::json!({
                                "status": "error",
                                "query": query,
                                "root": root_str,
                                "error": format!(
                                    "No embedding backend available. TEI server connection failed: {}. \
                                     Local sentence-transformers backend is not yet implemented in Rust CLI. \
                                     Please start a TEI server with: \
                                     docker run --gpus all -p 18080:80 ghcr.io/huggingface/text-embeddings-inference:1.7 \
                                     --model-id BAAI/bge-large-en-v1.5",
                                    e
                                ),
                            });
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&result)
                                    .context("Failed to serialize output")?
                            );
                            return Ok(());
                        } else {
                            anyhow::bail!(
                                "Failed to connect to TEI server: {}. \
                                 Start a TEI server or use --backend auto.",
                                e
                            );
                        }
                    }
                };

                eprintln!("Computing query embedding...");
                let embeddings = client
                    .embed(&[&query_for_embedding])
                    .await
                    .context("Failed to generate query embedding")?;

                let embedding = embeddings
                    .into_iter()
                    .next()
                    .ok_or_else(|| anyhow::anyhow!("No embedding returned for query"))?;

                // Cache the computed embedding for future queries
                // Use get_cached_query_embedding with a closure that returns the already-computed embedding
                get_cached_query_embedding(&query_for_embedding, |_| Ok(embedding.clone()))
                    .context("Failed to cache query embedding")?
            }
        }
        SemanticBackend::SentenceTransformers => {
            let result = serde_json::json!({
                "status": "error",
                "query": query,
                "root": root_str,
                "error": "Local sentence-transformers backend is not yet implemented in Rust CLI. \
                         Use --backend tei with a running TEI server, or --backend auto to auto-detect.",
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
            return Ok(());
        }
    };

    // Validate embedding dimensions match index
    if query_embedding.len() != index.dimensions() {
        let result = serde_json::json!({
            "status": "error",
            "query": query,
            "root": root_str,
            "error": format!(
                "Dimension mismatch: query embedding has {} dimensions but index has {}. \
                 The TEI server may be using a different model than what was used to build the index.",
                query_embedding.len(),
                index.dimensions()
            ),
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
        return Ok(());
    }

    // Search the index
    eprintln!("Searching for {} nearest neighbors...", num_results);
    let search_results = index
        .search(&query_embedding, num_results)
        .context("Failed to search index")?;

    // Convert distances to similarity scores using the index's metric
    let distances: Vec<f32> = search_results.iter().map(|(_, d)| *d).collect();
    let scores = index.to_similarity_scores(&distances);

    // Build formatted results
    let mut formatted_results: Vec<serde_json::Value> = Vec::new();

    for ((key, _distance), score) in search_results.iter().zip(scores.iter()) {
        let unit_index = *key as usize;

        // Validate key maps to a valid unit
        if unit_index >= units.len() {
            tracing::warn!(
                "Search returned key {} but only {} units in metadata",
                unit_index,
                units.len()
            );
            continue;
        }

        let unit = &units[unit_index];

        // Build result entry
        let mut result_json = serde_json::json!({
            "score": score,
            "file": unit.file,
            "name": unit.name,
            "kind": unit.kind.as_str(),
            "line": unit.start_line,
            "preview": truncate_code_preview(&unit.code, 200),
        });

        // Include signature if available
        if !unit.signature.is_empty() {
            result_json["signature"] = serde_json::json!(unit.signature);
        }

        // Include docstring if available
        if let Some(ref docstring) = unit.docstring {
            result_json["docstring"] = serde_json::json!(truncate_code_preview(docstring, 150));
        }

        // Include semantic tags if any
        if !unit.semantic_tags.is_empty() {
            result_json["semantic_tags"] = serde_json::json!(unit.semantic_tags);
        }

        // Include call graph expansion if requested
        if expand {
            if !unit.calls.is_empty() {
                result_json["calls"] = serde_json::json!(unit.calls);
            }
            if !unit.called_by.is_empty() {
                result_json["called_by"] = serde_json::json!(unit.called_by);
            }
        }

        formatted_results.push(result_json);
    }

    let elapsed = start_time.elapsed();

    // Output results
    let result = serde_json::json!({
        "status": "complete",
        "query": query,
        "root": root_str,
        "num_results": formatted_results.len(),
        "results": formatted_results,
        "elapsed_secs": elapsed.as_secs_f64(),
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&result).context("Failed to serialize output")?
    );

    Ok(())
}

/// Truncate code to a maximum character length, preserving word boundaries.
fn truncate_code_preview(code: &str, max_chars: usize) -> String {
    if code.len() <= max_chars {
        return code.to_string();
    }

    // Find a good break point near the limit
    let truncated = &code[..max_chars];

    // Try to break at a newline or whitespace
    if let Some(pos) = truncated.rfind('\n') {
        if pos > max_chars / 2 {
            return format!("{}...", &code[..pos]);
        }
    }

    if let Some(pos) = truncated.rfind(char::is_whitespace) {
        if pos > max_chars / 2 {
            return format!("{}...", &code[..pos]);
        }
    }

    format!("{}...", truncated)
}

async fn cmd_semantic(subcmd: SemanticCommands, _no_ignore: bool) -> Result<()> {
    match subcmd {
        SemanticCommands::Index {
            path,
            lang,
            model,
            backend,
            dimension,
        } => {
            cmd_semantic_index(&path, lang, model, backend, dimension).await?;
        }

        SemanticCommands::Search {
            query,
            path,
            k,
            expand,
            model: _,
            backend,
            task,
            force_reload: _,
        } => {
            cmd_semantic_search(&query, &path, k, expand, backend, task).await?;
        }

        SemanticCommands::Warmup { model } => {
            let result = serde_json::json!({
                "model": model.unwrap_or_else(|| "Qwen3-Embedding-0.6B".to_string()),
                "status": "not_implemented",
                "error": "Model warmup not yet implemented in Rust CLI"
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }

        SemanticCommands::Unload => {
            println!("Model unloading not yet implemented in Rust CLI");
        }

        SemanticCommands::Cache(cache_cmd) => match cache_cmd {
            CacheCommands::Clear => {
                println!("Cache cleared (not yet implemented)");
            }
            CacheCommands::Stats => {
                let result = serde_json::json!({
                    "cached_projects": 0,
                    "memory_usage_mb": 0,
                    "error": "Cache stats not yet implemented in Rust CLI"
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
            }
            CacheCommands::Invalidate { path } => {
                println!("Cache invalidated for: {}", path.display());
            }
        },

        SemanticCommands::Device => {
            let result = serde_json::json!({
                "device": "cpu",
                "device_count": 1,
                "total_memory_gb": 0,
                "free_memory_gb": 0,
                "supports_bf16": false,
                "tei_available": false,
                "error": "Device detection not yet implemented in Rust CLI"
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }

        SemanticCommands::Memory => {
            let result = serde_json::json!({
                "model_loaded": false,
                "gpu_memory_used_mb": 0,
                "error": "Memory stats not yet implemented in Rust CLI"
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }
    Ok(())
}

// =============================================================================
// DAEMON HELPER FUNCTIONS
// =============================================================================

/// Compute the daemon socket path for a project.
///
/// This matches the Python implementation's algorithm:
/// - Hash the canonicalized project path using SHA256
/// - Take first 16 chars of the hex digest
/// - Create path as `/tmp/brrr-{hash}.sock`
fn get_daemon_socket_path(project: &Path) -> PathBuf {
    // Canonicalize the path to match Python's Path.resolve() behavior
    let canonical = project
        .canonicalize()
        .unwrap_or_else(|_| project.to_path_buf());
    let path_str = canonical.to_string_lossy();

    // Compute SHA256 hash (matches Python's hashlib.sha256)
    let mut hasher = Sha256::new();
    hasher.update(path_str.as_bytes());
    let result = hasher.finalize();

    // Take first 16 hex characters (8 bytes = 16 hex chars)
    let hash_hex: String = result.iter().take(8).map(|b| format!("{b:02x}")).collect();

    PathBuf::from(format!("/tmp/brrr-{hash_hex}.sock"))
}

/// Send a JSON command to the daemon and receive the response.
///
/// Returns Ok(response) if communication succeeded, Err if socket unreachable.
#[cfg(unix)]
fn send_daemon_command(
    socket_path: &Path,
    command: &serde_json::Value,
) -> Result<serde_json::Value> {
    // Connect with a timeout
    let mut stream =
        UnixStream::connect(socket_path).context("Failed to connect to daemon socket")?;

    // Set read/write timeouts to prevent hanging
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .context("Failed to set read timeout")?;
    stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .context("Failed to set write timeout")?;

    // Send command as JSON followed by newline
    let cmd_str = serde_json::to_string(command).context("Failed to serialize command")?;
    stream
        .write_all(cmd_str.as_bytes())
        .context("Failed to write command to socket")?;
    stream
        .write_all(b"\n")
        .context("Failed to write newline to socket")?;
    stream.flush().context("Failed to flush socket")?;

    // Read response (daemon sends JSON followed by newline)
    let mut reader = BufReader::new(&stream);
    let mut response = String::new();
    reader
        .read_line(&mut response)
        .context("Failed to read response from daemon")?;

    // Parse JSON response
    serde_json::from_str(&response).context("Failed to parse daemon response as JSON")
}

/// Placeholder for non-Unix systems
#[cfg(not(unix))]
fn send_daemon_command(
    _socket_path: &Path,
    _command: &serde_json::Value,
) -> Result<serde_json::Value> {
    anyhow::bail!("Daemon communication is only supported on Unix systems")
}

async fn cmd_daemon(subcmd: DaemonCommands) -> Result<()> {
    match subcmd {
        DaemonCommands::Start { project } => {
            #[cfg(not(unix))]
            {
                let result = serde_json::json!({
                    "status": "error",
                    "project": project.display().to_string(),
                    "error": "Daemon is only supported on Unix systems"
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
                return Ok(());
            }

            #[cfg(unix)]
            {
                let canonical = project.canonicalize().unwrap_or_else(|_| project.clone());
                let socket_path = get_daemon_socket_path(&canonical);
                let project_str = canonical.to_string_lossy().to_string();

                // Check if daemon is already running
                if socket_path.exists() {
                    // Try to ping the daemon
                    match send_daemon_command(&socket_path, &serde_json::json!({"cmd": "ping"})) {
                        Ok(_) => {
                            let result = serde_json::json!({
                                "status": "already_running",
                                "project": project_str,
                                "socket": socket_path.display().to_string(),
                                "message": "Daemon is already running for this project"
                            });
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&result)
                                    .context("Failed to serialize output")?
                            );
                            return Ok(());
                        }
                        Err(_) => {
                            // Stale socket, remove it
                            std::fs::remove_file(&socket_path).ok();
                        }
                    }
                }

                // Get current executable path
                let exe =
                    std::env::current_exe().context("Failed to get current executable path")?;

                // Spawn daemon process in background with detached stdio
                let child = Command::new(&exe)
                    .args(["daemon", "serve", "--project", &project_str])
                    .stdin(Stdio::null())
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .spawn()
                    .context("Failed to spawn daemon process")?;

                let pid = child.id();

                // Wait briefly for daemon to start and create socket
                std::thread::sleep(Duration::from_millis(200));

                // Verify daemon started successfully
                let started = if socket_path.exists() {
                    send_daemon_command(&socket_path, &serde_json::json!({"cmd": "ping"})).is_ok()
                } else {
                    false
                };

                let result = serde_json::json!({
                    "status": if started { "started" } else { "starting" },
                    "project": project_str,
                    "pid": pid,
                    "socket": socket_path.display().to_string(),
                    "message": if started {
                        "Daemon started successfully"
                    } else {
                        "Daemon is starting (may take a moment to build call graph)"
                    }
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
            }
        }

        DaemonCommands::Stop { project } => {
            let canonical = project.canonicalize().unwrap_or_else(|_| project.clone());
            let socket_path = get_daemon_socket_path(&canonical);

            if !socket_path.exists() {
                let result = serde_json::json!({
                    "status": "not_running",
                    "project": canonical.display().to_string(),
                    "socket": socket_path.display().to_string(),
                    "message": "No daemon running for this project"
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
                return Ok(());
            }

            // Try to send shutdown command
            match send_daemon_command(&socket_path, &serde_json::json!({"command": "shutdown"})) {
                Ok(response) => {
                    let result = serde_json::json!({
                        "status": "stopped",
                        "project": canonical.display().to_string(),
                        "socket": socket_path.display().to_string(),
                        "daemon_response": response,
                        "message": "Daemon stopped successfully"
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
                Err(_) => {
                    // Socket exists but daemon not responding - clean up stale socket
                    if let Err(e) = std::fs::remove_file(&socket_path) {
                        let result = serde_json::json!({
                            "status": "error",
                            "project": canonical.display().to_string(),
                            "socket": socket_path.display().to_string(),
                            "error": format!("Failed to clean up stale socket: {}", e)
                        });
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&result)
                                .context("Failed to serialize output")?
                        );
                    } else {
                        let result = serde_json::json!({
                            "status": "cleaned",
                            "project": canonical.display().to_string(),
                            "socket": socket_path.display().to_string(),
                            "message": "Cleaned up stale socket (daemon was not responding)"
                        });
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&result)
                                .context("Failed to serialize output")?
                        );
                    }
                }
            }
        }

        DaemonCommands::Status { project } => {
            let canonical = project.canonicalize().unwrap_or_else(|_| project.clone());
            let socket_path = get_daemon_socket_path(&canonical);

            if !socket_path.exists() {
                let result = serde_json::json!({
                    "running": false,
                    "project": canonical.display().to_string(),
                    "socket": socket_path.display().to_string()
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
                return Ok(());
            }

            // Try to connect and get status
            match send_daemon_command(&socket_path, &serde_json::json!({"cmd": "status"})) {
                Ok(status) => {
                    let result = serde_json::json!({
                        "running": true,
                        "project": canonical.display().to_string(),
                        "socket": socket_path.display().to_string(),
                        "uptime_seconds": status.get("uptime"),
                        "requests_handled": status.get("requests"),
                        "cache_stats": status.get("cache"),
                        "daemon_status": status
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
                Err(_) => {
                    // Socket exists but daemon dead or not responding
                    let result = serde_json::json!({
                        "running": false,
                        "project": canonical.display().to_string(),
                        "socket": socket_path.display().to_string(),
                        "stale_socket": true,
                        "message": "Socket exists but daemon is not responding"
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
            }
        }

        DaemonCommands::Query { cmd, project } => {
            let canonical = project.canonicalize().unwrap_or_else(|_| project.clone());
            let socket_path = get_daemon_socket_path(&canonical);

            if !socket_path.exists() {
                let result = serde_json::json!({
                    "status": "error",
                    "command": cmd,
                    "project": canonical.display().to_string(),
                    "error": "No daemon running for this project"
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
                return Ok(());
            }

            match send_daemon_command(&socket_path, &serde_json::json!({"cmd": cmd})) {
                Ok(response) => {
                    let result = serde_json::json!({
                        "status": "ok",
                        "command": cmd,
                        "project": canonical.display().to_string(),
                        "result": response
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
                Err(e) => {
                    let result = serde_json::json!({
                        "status": "error",
                        "command": cmd,
                        "project": canonical.display().to_string(),
                        "error": format!("Failed to query daemon: {}", e)
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
            }
        }

        DaemonCommands::Notify { file, project } => {
            let canonical = project.canonicalize().unwrap_or_else(|_| project.clone());
            let socket_path = get_daemon_socket_path(&canonical);

            if !socket_path.exists() {
                let result = serde_json::json!({
                    "status": "error",
                    "file": file.display().to_string(),
                    "project": canonical.display().to_string(),
                    "error": "No daemon running for this project"
                });
                println!(
                    "{}",
                    serde_json::to_string_pretty(&result).context("Failed to serialize output")?
                );
                return Ok(());
            }

            let notify_cmd = serde_json::json!({
                "cmd": "notify",
                "file": file.display().to_string()
            });

            match send_daemon_command(&socket_path, &notify_cmd) {
                Ok(response) => {
                    let result = serde_json::json!({
                        "status": "ok",
                        "file": file.display().to_string(),
                        "project": canonical.display().to_string(),
                        "result": response
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
                Err(e) => {
                    let result = serde_json::json!({
                        "status": "error",
                        "file": file.display().to_string(),
                        "project": canonical.display().to_string(),
                        "error": format!("Failed to notify daemon: {}", e)
                    });
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&result)
                            .context("Failed to serialize output")?
                    );
                }
            }
        }

        DaemonCommands::Serve { project } => {
            #[cfg(not(unix))]
            {
                anyhow::bail!("Daemon server is only supported on Unix systems");
            }

            #[cfg(unix)]
            {
                cmd_daemon_serve(project).await?;
            }
        }
    }
    Ok(())
}

/// Run the daemon server (internal command, spawned by `daemon start`).
///
/// This function runs the actual daemon server loop that:
/// - Binds to a Unix socket for IPC
/// - Pre-builds the call graph cache for fast queries
/// - Handles incoming requests (ping, status, impact, etc.)
/// - Shuts down after 30 minutes of idle time
#[cfg(unix)]
async fn cmd_daemon_serve(project: PathBuf) -> Result<()> {
    let canonical = project
        .canonicalize()
        .context("Failed to canonicalize project path")?;
    let project_str = canonical.to_string_lossy().to_string();
    let socket_path = get_daemon_socket_path(&canonical);

    // Remove existing socket if present (stale from previous run)
    if socket_path.exists() {
        std::fs::remove_file(&socket_path).context("Failed to remove stale socket")?;
    }

    // Create Unix socket listener
    let listener =
        UnixListener::bind(&socket_path).context("Failed to bind Unix socket for daemon")?;

    // Set non-blocking for graceful shutdown handling
    listener
        .set_nonblocking(true)
        .context("Failed to set non-blocking mode on listener")?;

    eprintln!("Daemon: Starting for project {}", project_str);
    eprintln!("Daemon: Socket at {}", socket_path.display());

    // Pre-build call graph cache
    eprintln!("Daemon: Building call graph cache...");
    let start_time = Instant::now();
    let graph = match callgraph::build(&project_str) {
        Ok(mut g) => {
            // Build indexes for efficient lookups
            g.build_indexes();
            let func_count = g.callers.len() + g.callees.len();
            eprintln!(
                "Daemon: Call graph built in {:?} ({} functions, {} edges)",
                start_time.elapsed(),
                func_count / 2, // Approximate unique functions
                g.edges.len()
            );
            Some(g)
        }
        Err(e) => {
            eprintln!("Daemon: Warning - Failed to build call graph: {}", e);
            None
        }
    };

    // Track daemon state
    let last_activity = Arc::new(parking_lot::Mutex::new(Instant::now()));
    let shutdown_flag = Arc::new(AtomicBool::new(false));
    let request_count = Arc::new(std::sync::atomic::AtomicU64::new(0));
    let idle_timeout = Duration::from_secs(30 * 60); // 30 minutes
    let daemon_start = Instant::now();

    eprintln!(
        "Daemon: Listening (idle timeout: {} min)",
        idle_timeout.as_secs() / 60
    );

    // Main daemon loop
    while !shutdown_flag.load(Ordering::Relaxed) {
        // Check idle timeout
        {
            let last = last_activity.lock();
            if last.elapsed() > idle_timeout {
                eprintln!("Daemon: Idle timeout reached, shutting down");
                break;
            }
        }

        // Accept connections with timeout
        match listener.accept() {
            Ok((mut stream, _)) => {
                // Update activity timestamp
                *last_activity.lock() = Instant::now();
                request_count.fetch_add(1, Ordering::Relaxed);

                // Handle the request
                let mut reader = BufReader::new(&stream);
                let mut request_line = String::new();

                if reader.read_line(&mut request_line).is_ok() {
                    let request_line = request_line.trim();

                    // Parse JSON request
                    let request: serde_json::Value = match serde_json::from_str(request_line) {
                        Ok(v) => v,
                        Err(_) => {
                            let error_response = serde_json::json!({
                                "status": "error",
                                "error": "Invalid JSON request"
                            });
                            let _ = writeln!(stream, "{}", error_response);
                            continue;
                        }
                    };

                    // Handle command
                    let response = handle_daemon_request(
                        &request,
                        &graph,
                        &shutdown_flag,
                        daemon_start,
                        request_count.load(Ordering::Relaxed),
                    );

                    if let Err(e) = writeln!(stream, "{}", response) {
                        eprintln!("Daemon: Failed to send response: {}", e);
                    }
                }
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                // No pending connections, sleep briefly to avoid busy-wait
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => {
                eprintln!("Daemon: Accept error: {}", e);
            }
        }
    }

    // Cleanup
    eprintln!(
        "Daemon: Shutting down (handled {} requests in {:?})",
        request_count.load(Ordering::Relaxed),
        daemon_start.elapsed()
    );
    std::fs::remove_file(&socket_path).ok();

    Ok(())
}

/// Handle a single daemon request and return the JSON response.
#[cfg(unix)]
fn handle_daemon_request(
    request: &serde_json::Value,
    graph: &Option<callgraph::CallGraph>,
    shutdown_flag: &AtomicBool,
    daemon_start: Instant,
    request_count: u64,
) -> String {
    let cmd = request
        .get("cmd")
        .or_else(|| request.get("command"))
        .and_then(|v| v.as_str())
        .unwrap_or("");

    match cmd {
        "ping" => serde_json::json!({
            "status": "ok",
            "pong": true
        })
        .to_string(),

        "status" => {
            let has_graph = graph.is_some();
            let func_count = graph
                .as_ref()
                .map(|g| (g.callers.len() + g.callees.len()) / 2)
                .unwrap_or(0);
            let edge_count = graph.as_ref().map(|g| g.edges.len()).unwrap_or(0);

            serde_json::json!({
                "status": "running",
                "uptime": daemon_start.elapsed().as_secs(),
                "requests": request_count,
                "cache": {
                    "call_graph_loaded": has_graph,
                    "function_count": func_count,
                    "edge_count": edge_count
                }
            })
            .to_string()
        }

        "shutdown" => {
            shutdown_flag.store(true, Ordering::Relaxed);
            serde_json::json!({
                "status": "ok",
                "message": "Daemon shutting down"
            })
            .to_string()
        }

        "notify" => {
            let file = request
                .get("file")
                .and_then(|v| v.as_str())
                .unwrap_or("<unknown>");

            // Track file change for potential re-indexing
            // For now, just acknowledge the notification
            serde_json::json!({
                "status": "ok",
                "acknowledged": true,
                "file": file,
                "note": "File change tracked (re-indexing not yet implemented)"
            })
            .to_string()
        }

        "impact" => {
            let func_name = request
                .get("function")
                .and_then(|v| v.as_str())
                .unwrap_or("");

            if func_name.is_empty() {
                return serde_json::json!({
                    "status": "error",
                    "error": "Missing 'function' parameter"
                })
                .to_string();
            }

            if let Some(ref g) = graph {
                let depth = request.get("depth").and_then(|v| v.as_u64()).unwrap_or(3) as usize;

                let config = callgraph::ImpactConfig::new().with_depth(depth);
                let result = callgraph::analyze_impact(g, func_name, config);

                // Count direct callers (those at distance 1)
                let direct_count = result.by_distance.get(&1).copied().unwrap_or(0);

                serde_json::json!({
                    "status": "ok",
                    "function": func_name,
                    "callers_count": result.callers.len(),
                    "direct_callers": direct_count,
                    "callers": result.callers.iter().take(50).map(|c| {
                        serde_json::json!({
                            "name": c.name,
                            "file": c.file,
                            "distance": c.distance
                        })
                    }).collect::<Vec<_>>()
                })
                .to_string()
            } else {
                serde_json::json!({
                    "status": "error",
                    "error": "Call graph not loaded"
                })
                .to_string()
            }
        }

        "dead" => {
            if let Some(ref g) = graph {
                // Note: dead code analysis requires mutable graph for indexing
                // For daemon, we'll return a simplified result
                serde_json::json!({
                    "status": "ok",
                    "note": "Dead code analysis via daemon not fully implemented",
                    "edge_count": g.edges.len()
                })
                .to_string()
            } else {
                serde_json::json!({
                    "status": "error",
                    "error": "Call graph not loaded"
                })
                .to_string()
            }
        }

        _ => serde_json::json!({
            "status": "error",
            "error": format!("Unknown command: {}", cmd),
            "available_commands": ["ping", "status", "shutdown", "notify", "impact", "dead"]
        })
        .to_string(),
    }
}

/// Tool information for diagnostics check.
struct ToolInfo {
    /// Tool binary name
    name: &'static str,
    /// Language this tool belongs to
    lang: &'static str,
    /// Tool category (type_checker, linter, formatter)
    category: &'static str,
    /// Install command or URL
    install_cmd: &'static str,
    /// Custom version command arguments (None = use --version)
    version_args: Option<&'static [&'static str]>,
}

impl ToolInfo {
    const fn new(
        name: &'static str,
        lang: &'static str,
        category: &'static str,
        install_cmd: &'static str,
    ) -> Self {
        Self {
            name,
            lang,
            category,
            install_cmd,
            version_args: None,
        }
    }

    const fn with_version_args(mut self, args: &'static [&'static str]) -> Self {
        self.version_args = Some(args);
        self
    }
}

/// Get the version string for an installed tool.
fn get_tool_version(tool: &ToolInfo) -> Option<String> {
    let args = tool.version_args.unwrap_or(&["--version"]);

    let output = Command::new(tool.name).args(args).output().ok()?;

    // Try stdout first, then stderr (some tools output version to stderr)
    let version_str = if output.stdout.is_empty() {
        String::from_utf8_lossy(&output.stderr).to_string()
    } else {
        String::from_utf8_lossy(&output.stdout).to_string()
    };

    // Extract first non-empty line and clean it up
    version_str
        .lines()
        .find(|line| !line.trim().is_empty())
        .map(|line| line.trim().to_string())
}

/// Execute an install command.
fn run_install_command(cmd: &str) -> Result<()> {
    // Check if it's a URL (not an executable command)
    if cmd.starts_with("http://") || cmd.starts_with("https://") {
        println!("  Manual installation required. Visit: {}", cmd);
        return Ok(());
    }

    let parts: Vec<&str> = cmd.split_whitespace().collect();
    if parts.is_empty() {
        return Ok(());
    }

    let status = Command::new(parts[0])
        .args(&parts[1..])
        .status()
        .with_context(|| format!("Failed to execute: {}", cmd))?;

    if !status.success() {
        anyhow::bail!("Install command failed with exit code: {:?}", status.code());
    }

    Ok(())
}

fn cmd_doctor(install: Option<String>, json_output: bool) -> Result<()> {
    // Tool definitions with version command overrides where needed
    let tools: &[ToolInfo] = &[
        // Python tools
        ToolInfo::new("pyright", "python", "type_checker", "pip install pyright"),
        ToolInfo::new("ruff", "python", "linter", "pip install ruff"),
        ToolInfo::new("mypy", "python", "type_checker", "pip install mypy"),
        ToolInfo::new("black", "python", "formatter", "pip install black"),
        // TypeScript/JavaScript tools
        ToolInfo::new(
            "tsc",
            "typescript",
            "type_checker",
            "npm install -g typescript",
        ),
        ToolInfo::new("eslint", "typescript", "linter", "npm install -g eslint"),
        ToolInfo::new(
            "prettier",
            "typescript",
            "formatter",
            "npm install -g prettier",
        ),
        // Go tools
        ToolInfo::new("go", "go", "type_checker", "https://go.dev/dl/")
            .with_version_args(&["version"]),
        ToolInfo::new(
            "golangci-lint",
            "go",
            "linter",
            "go install github.com/golangci/golangci-lint/cmd/golangci-lint@latest",
        ),
        // Rust tools
        ToolInfo::new("rustc", "rust", "type_checker", "https://rustup.rs/"),
        ToolInfo::new("cargo", "rust", "build", "https://rustup.rs/"),
        ToolInfo::new(
            "clippy-driver",
            "rust",
            "linter",
            "rustup component add clippy",
        )
        .with_version_args(&["--version"]),
        ToolInfo::new(
            "rustfmt",
            "rust",
            "formatter",
            "rustup component add rustfmt",
        ),
        // Java tools
        ToolInfo::new("javac", "java", "type_checker", "https://adoptium.net/"),
        // C/C++ tools
        ToolInfo::new("clang", "c", "type_checker", "https://releases.llvm.org/"),
        ToolInfo::new("clang-tidy", "c", "linter", "https://releases.llvm.org/"),
        ToolInfo::new(
            "clang-format",
            "c",
            "formatter",
            "https://releases.llvm.org/",
        ),
    ];

    // Handle installation request
    if let Some(ref lang) = install {
        let lang_tools: Vec<_> = tools.iter().filter(|t| t.lang == lang).collect();

        if lang_tools.is_empty() {
            let available_langs: std::collections::HashSet<_> =
                tools.iter().map(|t| t.lang).collect();
            let langs_list: Vec<_> = available_langs.into_iter().collect();
            anyhow::bail!(
                "Unknown language: '{}'. Available: {}",
                lang,
                langs_list.join(", ")
            );
        }

        println!("Installing tools for {}...", lang);
        println!();

        for tool in lang_tools {
            let is_installed = which(tool.name).is_ok();

            if is_installed {
                let version = get_tool_version(tool).unwrap_or_else(|| "unknown".to_string());
                println!("  {} already installed ({})", tool.name, version);
            } else {
                println!("  Installing {}...", tool.name);
                match run_install_command(tool.install_cmd) {
                    Ok(()) => {
                        // Verify installation succeeded
                        if which(tool.name).is_ok() {
                            let version =
                                get_tool_version(tool).unwrap_or_else(|| "unknown".to_string());
                            println!("    Successfully installed {}", version);
                        } else {
                            println!(
                                "    Installation may have succeeded but tool not found in PATH"
                            );
                        }
                    }
                    Err(e) => {
                        eprintln!("    Failed to install {}: {}", tool.name, e);
                    }
                }
            }
        }

        return Ok(());
    }

    // Build tool status list
    let mut status_list = Vec::new();

    for tool in tools {
        let installed = which(tool.name).is_ok();
        let version = if installed {
            get_tool_version(tool)
        } else {
            None
        };
        let path = which(tool.name).ok().map(|p| p.display().to_string());

        status_list.push(serde_json::json!({
            "tool": tool.name,
            "language": tool.lang,
            "category": tool.category,
            "installed": installed,
            "version": version,
            "path": path,
            "install_command": tool.install_cmd,
        }));
    }

    if json_output {
        // Group by language for structured output
        let mut by_language: std::collections::HashMap<&str, Vec<&serde_json::Value>> =
            std::collections::HashMap::new();

        for status in &status_list {
            let lang = status["language"].as_str().unwrap_or("unknown");
            by_language.entry(lang).or_default().push(status);
        }

        let result = serde_json::json!({
            "tools": status_list,
            "by_language": by_language,
            "summary": {
                "total": tools.len(),
                "installed": status_list.iter().filter(|s| s["installed"].as_bool().unwrap_or(false)).count(),
                "missing": status_list.iter().filter(|s| !s["installed"].as_bool().unwrap_or(false)).count(),
            }
        });

        println!(
            "{}",
            serde_json::to_string_pretty(&result).context("Failed to serialize output")?
        );
    } else {
        // Human-readable output
        println!("brrr Diagnostics Check");
        println!("{}", "=".repeat(60));
        println!();

        // Group tools by language
        let mut current_lang = "";

        for (i, tool) in tools.iter().enumerate() {
            if tool.lang != current_lang {
                if !current_lang.is_empty() {
                    println!();
                }
                // Capitalize first letter of language name
                let lang_display = tool
                    .lang
                    .chars()
                    .next()
                    .map(|c| c.to_uppercase().to_string() + &tool.lang[1..])
                    .unwrap_or_else(|| tool.lang.to_string());
                println!("{}:", lang_display);
                current_lang = tool.lang;
            }

            let status = &status_list[i];
            let installed = status["installed"].as_bool().unwrap_or(false);
            let icon = if installed { "[OK]" } else { "[  ]" };

            if installed {
                let version = status["version"]
                    .as_str()
                    .unwrap_or("version unknown")
                    .trim();
                // Truncate long version strings
                let version_display = if version.len() > 40 {
                    format!("{}...", &version[..37])
                } else {
                    version.to_string()
                };
                println!("  {} {} - {}", icon, tool.name, version_display);
            } else {
                println!(
                    "  {} {} - NOT INSTALLED ({})",
                    icon, tool.name, tool.install_cmd
                );
            }
        }

        // Summary
        let installed_count = status_list
            .iter()
            .filter(|s| s["installed"].as_bool().unwrap_or(false))
            .count();
        let total = tools.len();

        println!();
        println!("{}", "-".repeat(60));
        println!("Summary: {}/{} tools installed", installed_count, total);

        if installed_count < total {
            println!();
            println!("To install missing tools for a language:");
            println!("  brrr doctor --install <language>");
            println!();
            println!("Available languages: python, typescript, go, rust, java, c");
        }
    }

    Ok(())
}

// =============================================================================
// SECURITY COMMANDS
// =============================================================================

fn cmd_security(subcmd: SecurityCommands) -> Result<()> {
    match subcmd {
        SecurityCommands::Scan {
            path,
            lang,
            output_format,
            severity,
            confidence,
            category,
            fail_on,
            include_suppressed,
            max_files,
        } => {
            let exit_code = cmd_security_scan(
                &path,
                lang,
                output_format,
                &severity,
                &confidence,
                category.as_deref(),
                &fail_on,
                include_suppressed,
                max_files,
            )?;
            if exit_code != 0 {
                std::process::exit(exit_code);
            }
        }
        SecurityCommands::SqlInjection {
            path,
            lang,
            format,
            min_severity,
        } => {
            cmd_sql_injection(&path, lang, format, &min_severity)?;
        }
        SecurityCommands::CommandInjection {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_command_injection(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::Xss {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_xss(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::PathTraversal {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_path_traversal(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::Secrets {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
            include_entropy,
        } => {
            cmd_secrets(
                &path,
                lang,
                format,
                &min_severity,
                &min_confidence,
                include_entropy,
            )?;
        }
        SecurityCommands::Crypto {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
            include_safe,
        } => {
            cmd_crypto(
                &path,
                lang,
                format,
                &min_severity,
                &min_confidence,
                include_safe,
            )?;
        }
        SecurityCommands::Deserialization {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
            include_safe,
        } => {
            cmd_deserialization(
                &path,
                lang,
                format,
                &min_severity,
                &min_confidence,
                include_safe,
            )?;
        }
        SecurityCommands::Redos {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_redos(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::LogInjection {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_log_injection(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::HeaderInjection {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_header_injection(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::TemplateInjection {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_template_injection(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::Ssrf {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_ssrf(&path, lang, format, &min_severity, &min_confidence)?;
        }
        SecurityCommands::InputValidation {
            path,
            lang,
            format,
            min_severity,
            include_recommended,
            max_files,
        } => {
            cmd_input_validation(
                &path,
                lang,
                format,
                &min_severity,
                include_recommended,
                max_files,
            )?;
        }
        SecurityCommands::PrototypePollution {
            path,
            lang,
            format,
            min_severity,
            min_confidence,
        } => {
            cmd_prototype_pollution(&path, lang, format, &min_severity, &min_confidence)?;
        }
    }
    Ok(())
}

fn cmd_sql_injection(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
) -> Result<()> {
    use security::injection::sql::{Severity, SqlInjectionDetector};

    // Validate path exists
    require_exists(path)?;

    let detector = SqlInjectionDetector::new();
    let lang_str = lang.map(|l| l.to_string());

    let result = if path.is_file() {
        let findings = detector
            .scan_file(path.to_str().context("Invalid path")?)
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

        let mut severity_counts = rustc_hash::FxHashMap::default();
        for finding in &findings {
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        security::injection::sql::ScanResult {
            findings,
            files_scanned: 1,
            sinks_found: 0,
            severity_counts,
            language: lang_str.unwrap_or_else(|| "auto".to_string()),
        }
    } else {
        detector
            .scan_directory(path.to_str().context("Invalid path")?, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Filter by minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        _ => Severity::Low,
    };

    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| {
            let sev_val = match f.severity {
                Severity::Critical => 4,
                Severity::High => 3,
                Severity::Medium => 2,
                Severity::Low => 1,
            };
            let min_val = match min_sev {
                Severity::Critical => 4,
                Severity::High => 3,
                Severity::Medium => 2,
                Severity::Low => 1,
            };
            sev_val >= min_val
        })
        .collect();

    let filtered_result = security::injection::sql::ScanResult {
        findings: filtered_findings,
        files_scanned: result.files_scanned,
        sinks_found: result.sinks_found,
        severity_counts: result.severity_counts,
        language: result.language,
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&filtered_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("SQL Injection Scan Results");
            println!("==========================");
            println!();
            println!("Files scanned: {}", filtered_result.files_scanned);
            println!("Vulnerabilities found: {}", filtered_result.findings.len());
            println!();

            if filtered_result.findings.is_empty() {
                println!("No SQL injection vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_result.findings.iter().enumerate() {
                    println!(
                        "{}. [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Pattern: {}", finding.pattern);
                    println!("   Sink: {}", finding.sink_expression);
                    println!(
                        "   Code: {}",
                        finding.code_snippet.lines().next().unwrap_or("")
                    );
                    println!("   Description: {}", finding.description);
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &filtered_result.severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_command_injection(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::command::{
        scan_command_injection, scan_file_command_injection, Confidence, Severity,
    };

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for vulnerabilities
    let findings = if path.is_file() {
        scan_file_command_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    } else {
        scan_command_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
    }

    // Build result structure
    let result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": if path.is_file() { 1 } else {
            // Count scanned files (approximate from findings)
            filtered_findings.iter()
                .map(|f| &f.location.file)
                .collect::<std::collections::HashSet<_>>()
                .len()
                .max(1)
        },
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("Command Injection Scan Results");
            println!("==============================");
            println!();
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No command injection vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Sink: {}", finding.sink_function);
                    println!("   Type: {}", finding.kind);
                    println!("   Tainted Input: {}", finding.tainted_input);
                    if let Some(ref snippet) = finding.code_snippet {
                        let first_line = snippet.lines().next().unwrap_or("");
                        println!("   Code: {}", first_line);
                    }
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_xss(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::xss::{scan_xss, Confidence, Severity};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for XSS vulnerabilities
    let result =
        scan_xss(path, lang_str.as_deref()).map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
    }

    // Build result structure
    let output_result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "language": lang_str.unwrap_or_else(|| "javascript/typescript".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("XSS Vulnerability Scan Results");
            println!("==============================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No XSS vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Sink Type: {}", finding.sink_type);
                    println!("   Context: {}", finding.context);
                    println!(
                        "   Sink: {}",
                        finding.sink_expression.chars().take(80).collect::<String>()
                    );
                    if !finding.tainted_variables.is_empty() {
                        println!(
                            "   Tainted Variables: {}",
                            finding.tainted_variables.join(", ")
                        );
                    }
                    if let Some(ref snippet) = finding.code_snippet {
                        let first_line = snippet.lines().next().unwrap_or("");
                        println!("   Code: {}", first_line);
                    }
                    println!(
                        "   Description: {}",
                        finding.description.lines().next().unwrap_or("")
                    );
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_path_traversal(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::path_traversal::{
        scan_file_path_traversal, scan_path_traversal, Confidence, Severity,
    };

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for path traversal vulnerabilities
    let findings = if path.is_file() {
        scan_file_path_traversal(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    } else {
        scan_path_traversal(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
    }

    // Count files with vulnerabilities
    let files_with_vulns: std::collections::HashSet<_> =
        filtered_findings.iter().map(|f| &f.location.file).collect();

    // Build result structure
    let result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": if path.is_file() { 1 } else { files_with_vulns.len().max(1) },
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("Path Traversal Scan Results");
            println!("===========================");
            println!();
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No path traversal vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Sink: {}", finding.sink_function);
                    println!("   Operation: {}", finding.operation_type);
                    println!("   Pattern: {}", finding.pattern);
                    println!(
                        "   Path Expression: {}",
                        finding.path_expression.chars().take(60).collect::<String>()
                    );
                    if !finding.involved_variables.is_empty() {
                        println!("   Variables: {}", finding.involved_variables.join(", "));
                    }
                    if finding.symlink_risk {
                        println!("   Symlink Risk: Yes");
                    }
                    if let Some(ref snippet) = finding.code_snippet {
                        let first_line = snippet.lines().next().unwrap_or("");
                        println!("   Code: {}", first_line);
                    }
                    println!(
                        "   Description: {}",
                        finding.description.lines().next().unwrap_or("")
                    );
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }

                // Symlink warning
                let symlink_count = filtered_findings.iter().filter(|f| f.symlink_risk).count();
                if symlink_count > 0 {
                    println!();
                    println!(
                        "WARNING: {} findings may also be vulnerable to symlink attacks.",
                        symlink_count
                    );
                    println!("Consider using O_NOFOLLOW flag or equivalent protections.");
                }
            }
        }
    }

    Ok(())
}

fn cmd_secrets(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
    include_entropy: bool,
) -> Result<()> {
    use security::secrets::{Confidence, SecretsDetector, Severity};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Create detector with configuration
    let detector = SecretsDetector::new().include_entropy(include_entropy);

    // Scan for secrets
    let result = if path.is_file() {
        let findings = detector
            .scan_file(path.to_str().context("Invalid path")?)
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

        let mut type_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        let mut severity_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();

        for finding in &findings {
            *type_counts
                .entry(finding.secret_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        security::secrets::ScanResult {
            findings,
            files_scanned: 1,
            type_counts,
            severity_counts,
        }
    } else {
        detector
            .scan_directory(path.to_str().context("Invalid path")?, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Recalculate counts after filtering
    let mut type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *type_counts
            .entry(finding.secret_type.to_string())
            .or_insert(0) += 1;
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
    }

    let filtered_result = security::secrets::ScanResult {
        findings: filtered_findings.clone(),
        files_scanned: result.files_scanned,
        type_counts: type_counts.clone(),
        severity_counts: severity_counts.clone(),
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&filtered_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("Secrets Detection Scan Results");
            println!("==============================");
            println!();
            println!("Files scanned: {}", filtered_result.files_scanned);
            println!("Secrets found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No hardcoded secrets detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Type: {}", finding.secret_type);
                    println!("   Value: {}", finding.masked_value);
                    if let Some(ref var_name) = finding.variable_name {
                        println!("   Variable: {}", var_name);
                    }
                    if let Some(entropy) = finding.entropy {
                        println!("   Entropy: {:.2} bits/char", entropy);
                    }
                    if finding.is_test_file {
                        println!("   Test file: Yes (reduced severity)");
                    }
                    println!("   Description: {}", finding.description);
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by type
                println!("Summary by Type:");
                let mut type_vec: Vec<_> = type_counts.iter().collect();
                type_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (secret_type, count) in type_vec {
                    println!("  {}: {}", secret_type, count);
                }
                println!();

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }

                // Critical findings warning
                let critical_count = filtered_findings
                    .iter()
                    .filter(|f| f.severity == Severity::Critical)
                    .count();
                if critical_count > 0 {
                    println!();
                    println!(
                        "CRITICAL: {} secrets require immediate attention!",
                        critical_count
                    );
                    println!("Rotate credentials and remove from source control.");
                }
            }
        }
    }

    Ok(())
}

fn cmd_crypto(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
    include_safe: bool,
) -> Result<()> {
    use security::crypto::{Confidence, Severity, WeakCryptoDetector};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Create detector with configuration
    let detector = WeakCryptoDetector::new().include_safe_patterns(include_safe);

    // Scan for weak cryptography
    let result = if path.is_file() {
        let findings = detector
            .scan_file(path.to_str().context("Invalid path")?)
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

        let mut issue_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        let mut severity_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        let mut algorithm_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();

        for finding in &findings {
            *issue_counts
                .entry(finding.issue_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
            *algorithm_counts
                .entry(finding.algorithm.to_string())
                .or_insert(0) += 1;
        }

        security::crypto::ScanResult {
            findings,
            files_scanned: 1,
            issue_counts,
            severity_counts,
            algorithm_counts,
        }
    } else {
        detector
            .scan_directory(path.to_str().context("Invalid path")?, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Recalculate counts after filtering
    let mut issue_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut algorithm_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *issue_counts
            .entry(finding.issue_type.to_string())
            .or_insert(0) += 1;
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *algorithm_counts
            .entry(finding.algorithm.to_string())
            .or_insert(0) += 1;
    }

    let filtered_result = security::crypto::ScanResult {
        findings: filtered_findings.clone(),
        files_scanned: result.files_scanned,
        issue_counts: issue_counts.clone(),
        severity_counts: severity_counts.clone(),
        algorithm_counts: algorithm_counts.clone(),
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&filtered_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Text format output
            println!("Weak Cryptography Detection Scan Results");
            println!("=========================================");
            println!();
            println!("Files scanned: {}", filtered_result.files_scanned);
            println!("Issues found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No weak cryptography detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Issue: {}", finding.issue_type);
                    println!("   Algorithm: {}", finding.algorithm);
                    println!("   Context: {:?}", finding.context);
                    if finding.likely_safe {
                        println!("   Likely Safe: Yes (checksum/cache usage)");
                    }
                    if finding.is_test_file {
                        println!("   Test file: Yes (reduced severity)");
                    }
                    println!("   Description: {}", finding.description);
                    println!(
                        "   Remediation: {}",
                        finding.remediation.lines().next().unwrap_or("")
                    );
                    println!();
                }

                // Summary by issue type
                println!("Summary by Issue Type:");
                let mut issue_vec: Vec<_> = issue_counts.iter().collect();
                issue_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (issue_type, count) in issue_vec {
                    println!("  {}: {}", issue_type, count);
                }
                println!();

                // Summary by algorithm
                println!("Summary by Algorithm:");
                let mut algo_vec: Vec<_> = algorithm_counts.iter().collect();
                algo_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (algorithm, count) in algo_vec {
                    println!("  {}: {}", algorithm, count);
                }
                println!();

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }

                // Critical findings warning
                let critical_count = filtered_findings
                    .iter()
                    .filter(|f| f.severity == Severity::Critical)
                    .count();
                if critical_count > 0 {
                    println!();
                    println!(
                        "CRITICAL: {} cryptographic issues require immediate attention!",
                        critical_count
                    );
                    println!("Review hardcoded keys and weak algorithms.");
                }
            }
        }
    }

    Ok(())
}

fn cmd_deserialization(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
    include_safe: bool,
) -> Result<()> {
    use security::deserialization::{
        scan_deserialization, scan_file_deserialization, Confidence, Severity,
    };

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for deserialization vulnerabilities
    let findings = if path.is_file() {
        scan_file_deserialization(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    } else {
        scan_deserialization(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity, confidence, and safe patterns
    let filtered_findings: Vec<_> = findings
        .into_iter()
        .filter(|f| {
            f.severity >= min_sev && f.confidence >= min_conf && (include_safe || !f.possibly_safe)
        })
        .collect();

    // Count by severity and method
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut method_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut source_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *method_counts.entry(finding.method.to_string()).or_insert(0) += 1;
        *source_counts
            .entry(finding.input_source.to_string())
            .or_insert(0) += 1;
    }

    let files_scanned = if path.is_file() {
        1
    } else {
        filtered_findings
            .iter()
            .map(|f| &f.location.file)
            .collect::<std::collections::HashSet<_>>()
            .len()
            .max(1)
    };

    let result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "method_counts": method_counts,
        "source_counts": source_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Unsafe Deserialization Scan Results");
            println!("====================================");
            println!();
            println!("Files scanned: {}", files_scanned);
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No unsafe deserialization patterns detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Method: {}", finding.method);
                    println!("   Function: {}", finding.sink_function);
                    println!("   Input Source: {}", finding.input_source);
                    println!("   Data: {}", finding.deserialized_data);
                    if finding.possibly_safe {
                        println!("   Status: POSSIBLY SAFE (review recommended)");
                    }
                    println!("   Description: {}", finding.description);
                    println!();
                }

                // Summary
                println!("Summary by Method:");
                let mut method_vec: Vec<_> = method_counts.iter().collect();
                method_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (method, count) in method_vec {
                    println!("  {}: {}", method, count);
                }
                println!();

                println!("Summary by Input Source:");
                let mut source_vec: Vec<_> = source_counts.iter().collect();
                source_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (source, count) in source_vec {
                    println!("  {}: {}", source, count);
                }
                println!();

                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }

                // Critical findings warning
                let critical_count = filtered_findings
                    .iter()
                    .filter(|f| f.severity == Severity::Critical)
                    .count();
                if critical_count > 0 {
                    println!();
                    println!(
                        "CRITICAL: {} deserialization vulnerabilities allow RCE!",
                        critical_count
                    );
                    println!("These issues can execute arbitrary code without obvious sinks.");
                    println!("Review immediately and replace with safe alternatives.");
                }
            }
        }
    }

    Ok(())
}

/// Run all security analyzers and generate unified report.
fn cmd_security_scan(
    path: &PathBuf,
    lang: Option<Language>,
    format: SecurityOutputFormat,
    min_severity: &str,
    min_confidence: &str,
    categories: Option<&str>,
    fail_on: &str,
    include_suppressed: bool,
    max_files: usize,
) -> Result<i32> {
    use security::{scan_security, Confidence, SecurityConfig, Severity};

    // Validate path exists
    require_exists(path)?;

    // Build config
    let mut config = SecurityConfig::default();
    config.language = lang.map(|l| l.to_string());

    // Parse minimum severity
    config.min_severity = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    config.min_confidence = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Parse categories
    if let Some(cats) = categories {
        config.categories = Some(cats.split(',').map(|s| s.trim().to_lowercase()).collect());
    }

    config.include_suppressed = include_suppressed;
    config.max_files = max_files;
    config.deduplicate = true;

    // Run unified scan
    let report =
        scan_security(path, &config).map_err(|e| anyhow::anyhow!("Security scan failed: {}", e))?;

    // Output based on format
    match format {
        SecurityOutputFormat::Json => {
            println!(
                "{}",
                serde_json::to_string_pretty(&report).context("Failed to serialize output")?
            );
        }
        SecurityOutputFormat::Sarif => {
            let sarif_json = report
                .to_sarif_json()
                .map_err(|e| anyhow::anyhow!("Failed to generate SARIF: {}", e))?;
            println!("{}", sarif_json);
        }
        SecurityOutputFormat::Text => {
            println!("Security Scan Results");
            println!("=====================");
            println!();
            println!("Scan Duration: {}ms", report.summary.scan_duration_ms);
            println!("Files Scanned: {}", report.summary.files_scanned);
            println!("Total Findings: {}", report.summary.total_findings);
            println!("Duplicates Removed: {}", report.summary.duplicates_removed);
            println!();

            // Summary by severity
            println!("By Severity:");
            println!(
                "  Critical: {}",
                report.summary.by_severity.get("Critical").unwrap_or(&0)
            );
            println!(
                "  High: {}",
                report.summary.by_severity.get("High").unwrap_or(&0)
            );
            println!(
                "  Medium: {}",
                report.summary.by_severity.get("Medium").unwrap_or(&0)
            );
            println!(
                "  Low: {}",
                report.summary.by_severity.get("Low").unwrap_or(&0)
            );
            println!(
                "  Info: {}",
                report.summary.by_severity.get("Info").unwrap_or(&0)
            );
            println!();

            // Summary by category
            if !report.summary.by_category.is_empty() {
                println!("By Category:");
                for (category, count) in &report.summary.by_category {
                    println!("  {}: {}", category, count);
                }
                println!();
            }

            // List findings
            if report.findings.is_empty() {
                println!("No security vulnerabilities detected.");
            } else {
                println!("Findings:");
                println!("---------");
                for (i, finding) in report.findings.iter().enumerate() {
                    let suppressed_marker = if finding.suppressed {
                        " [SUPPRESSED]"
                    } else {
                        ""
                    };
                    println!(
                        "{}. [{}] [{}] {}{}",
                        i + 1,
                        finding.id,
                        finding.severity,
                        finding.title,
                        suppressed_marker
                    );
                    println!(
                        "   Location: {}:{}:{}",
                        finding.location.file,
                        finding.location.start_line,
                        finding.location.start_column
                    );
                    println!("   Category: {}", finding.category);
                    println!("   Confidence: {}", finding.confidence);
                    if let Some(cwe) = finding.cwe_id {
                        println!("   CWE: CWE-{}", cwe);
                    }
                    println!("   Description: {}", finding.description);
                    if !finding.remediation.is_empty() {
                        let first_line = finding.remediation.lines().next().unwrap_or("");
                        println!("   Remediation: {}", first_line);
                    }
                    if !finding.code_snippet.is_empty() {
                        let snippet = finding.code_snippet.lines().next().unwrap_or("");
                        if snippet.len() <= 80 {
                            println!("   Code: {}", snippet);
                        } else {
                            println!("   Code: {}...", &snippet[..77]);
                        }
                    }
                    println!();
                }
            }
        }
    }

    // Determine exit code based on fail_on threshold
    let fail_severity = match fail_on.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::High,
    };

    let has_severe_finding = report
        .findings
        .iter()
        .any(|f| !f.suppressed && f.severity >= fail_severity);

    Ok(if has_severe_finding { 1 } else { 0 })
}

fn cmd_redos(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::redos::{scan_redos, Confidence, Severity};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for ReDoS vulnerabilities
    let result = scan_redos(path.to_string_lossy().as_ref(), lang_str.as_deref())
        .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut vuln_type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *vuln_type_counts
            .entry(finding.vulnerability_type.to_string())
            .or_insert(0) += 1;
    }

    let output_result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "vulnerability_type_counts": vuln_type_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("ReDoS (Regular Expression Denial of Service) Scan Results");
            println!("==========================================================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No ReDoS vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Type: {}", finding.vulnerability_type);
                    println!("   Function: {}", finding.regex_function);
                    println!("   Pattern: {}", finding.regex_pattern);
                    println!("   Complexity: {}", finding.complexity);
                    if !finding.attack_string.is_empty() {
                        println!("   Attack String: {}", finding.attack_string);
                    }
                    println!("   Description: {}", finding.description);
                    println!();
                }

                // Summary
                println!("Summary by Vulnerability Type:");
                let mut vuln_vec: Vec<_> = vuln_type_counts.iter().collect();
                vuln_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (vuln_type, count) in vuln_vec {
                    println!("  {}: {}", vuln_type, count);
                }
                println!();

                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_log_injection(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::log_injection::{
        scan_file_log_injection, scan_log_injection, Confidence, Severity,
    };

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for log injection vulnerabilities
    let result = if path.is_file() {
        let findings = scan_file_log_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

        // Build type and severity counts
        let mut type_counts = rustc_hash::FxHashMap::default();
        let mut severity_counts = rustc_hash::FxHashMap::default();
        for finding in &findings {
            *type_counts
                .entry(finding.injection_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }

        security::injection::log_injection::ScanResult {
            findings,
            files_scanned: 1,
            type_counts,
            severity_counts,
        }
    } else {
        scan_log_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity and injection type
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *type_counts
            .entry(finding.injection_type.to_string())
            .or_insert(0) += 1;
    }

    let output_result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "injection_type_counts": type_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Log Injection Scan Results");
            println!("==========================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Vulnerabilities found: {}", filtered_findings.len());
            println!();

            if filtered_findings.is_empty() {
                println!("No log injection vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Type: {}", finding.injection_type);
                    println!("   Function: {}", finding.log_function);
                    println!("   Tainted Data: {}", finding.tainted_data);
                    println!("   CWE: CWE-{}", finding.cwe_id);
                    if finding.uses_structured_logging {
                        println!("   Note: Uses structured logging (safer pattern)");
                    }
                    if let Some(ref snippet) = finding.code_snippet {
                        println!("   Code:");
                        for line in snippet.lines() {
                            println!("     {}", line);
                        }
                    }
                    println!("   Remediation: {}", finding.remediation);
                    println!();
                }

                // Summary
                println!("Summary by Injection Type:");
                let mut type_vec: Vec<_> = type_counts.iter().collect();
                type_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (inj_type, count) in type_vec {
                    println!("  {}: {}", inj_type, count);
                }
                println!();

                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_header_injection(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::header_injection::{
        scan_file_header_injection, scan_header_injection, Confidence, Severity,
    };

    require_exists(path)?;
    let lang_str = lang.map(|l| l.to_string());

    let result = if path.is_file() {
        let findings = scan_file_header_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;
        let mut type_counts = rustc_hash::FxHashMap::default();
        let mut severity_counts = rustc_hash::FxHashMap::default();
        for finding in &findings {
            *type_counts
                .entry(finding.injection_type.to_string())
                .or_insert(0) += 1;
            *severity_counts
                .entry(finding.severity.to_string())
                .or_insert(0) += 1;
        }
        security::injection::header_injection::ScanResult {
            findings,
            files_scanned: 1,
            type_counts,
            severity_counts,
        }
    } else {
        scan_header_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *type_counts
            .entry(finding.injection_type.to_string())
            .or_insert(0) += 1;
    }

    let output_result = serde_json::json!({
        "findings": filtered_findings, "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts, "injection_type_counts": type_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result).context("Serialize failed")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Header Injection Scan Results\n==============================\n");
            println!(
                "Files scanned: {}\nVulnerabilities found: {}\n",
                result.files_scanned,
                filtered_findings.len()
            );
            if filtered_findings.is_empty() {
                println!("No header injection vulnerabilities detected.");
            } else {
                for (i, f) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        f.severity,
                        f.confidence,
                        f.location.file,
                        f.location.line
                    );
                    println!(
                        "   Type: {}\n   Header: {}\n   Sink: {}",
                        f.injection_type, f.header_name, f.sink_function
                    );
                    println!("   CWE: CWE-{}", f.cwe_id);
                    if f.framework_protected {
                        println!("   Note: Framework may auto-sanitize");
                    }
                    if let Some(ref s) = f.code_snippet {
                        println!("   Code:\n     {}", s.replace('\n', "\n     "));
                    }
                    println!("   Remediation: {}\n", f.remediation);
                }
            }
        }
    }
    Ok(())
}

fn cmd_template_injection(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::injection::template_injection::{
        scan_file_template_injection, scan_template_injection, Confidence, Severity,
    };

    require_exists(path)?;
    let lang_str = lang.map(|l| l.to_string());

    let result = if path.is_file() {
        scan_file_template_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    } else {
        scan_template_injection(path, lang_str.as_deref())
            .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?
    };

    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut engine_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *engine_counts
            .entry(finding.template_engine.to_string())
            .or_insert(0) += 1;
    }

    let output_result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "engine_counts": engine_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Template Injection (SSTI) Scan Results");
            println!("========================================\n");
            println!("Files scanned: {}", result.files_scanned);
            println!("Vulnerabilities found: {}\n", filtered_findings.len());

            if filtered_findings.is_empty() {
                println!("No template injection vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Engine: {}", finding.template_engine);
                    println!("   Type: {}", finding.injection_type);
                    println!("   Sink: {}", finding.sink_function);
                    println!("   CWE: CWE-{}", finding.cwe_id);
                    if let Some(ref snippet) = finding.code_snippet {
                        println!("   Code:");
                        for line in snippet.lines() {
                            println!("     {}", line);
                        }
                    }
                    println!("   Remediation: {}\n", finding.remediation);
                }

                println!("Summary by Template Engine:");
                for (engine, count) in &engine_counts {
                    println!("  {}: {}", engine, count);
                }
                println!("\nSummary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_ssrf(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::ssrf::{scan_ssrf, Confidence, Severity};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Scan for SSRF vulnerabilities
    let result = scan_ssrf(path.to_string_lossy().as_ref(), lang_str.as_deref())
        .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    // Parse minimum confidence
    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter by minimum severity and confidence
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Count by severity and SSRF type
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut ssrf_type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &filtered_findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *ssrf_type_counts
            .entry(finding.ssrf_type.to_string())
            .or_insert(0) += 1;
    }

    let output_result = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "vulnerabilities_found": filtered_findings.len(),
        "severity_counts": severity_counts,
        "ssrf_type_counts": ssrf_type_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
        "duration_ms": result.duration_ms,
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result)
                    .context("Failed to serialize output")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("SSRF (Server-Side Request Forgery) Scan Results");
            println!("================================================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Vulnerabilities found: {}", filtered_findings.len());
            if let Some(ms) = result.duration_ms {
                println!("Duration: {}ms", ms);
            }
            println!();

            if filtered_findings.is_empty() {
                println!("No SSRF vulnerabilities detected.");
            } else {
                for (i, finding) in filtered_findings.iter().enumerate() {
                    println!(
                        "{}. [{}] [{}] {}:{}",
                        i + 1,
                        finding.severity,
                        finding.confidence,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Type: {}", finding.ssrf_type);
                    println!("   Sink: {}", finding.sink_function);
                    println!("   Tainted URL: {}", finding.tainted_url);
                    if !finding.potential_targets.is_empty() {
                        println!(
                            "   Potential Targets: {}",
                            finding.potential_targets.join(", ")
                        );
                    }
                    println!("   Description: {}", finding.description);
                    if let Some(ref snippet) = finding.code_snippet {
                        println!("   Code:");
                        for line in snippet.lines() {
                            println!("      {}", line);
                        }
                    }
                    println!();
                }

                // Summary by SSRF type
                println!("Summary by SSRF Type:");
                let mut type_vec: Vec<_> = ssrf_type_counts.iter().collect();
                type_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (ssrf_type, count) in type_vec {
                    println!("  {}: {}", ssrf_type, count);
                }
                println!();

                // Summary by severity
                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

fn cmd_input_validation(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    include_recommended: bool,
    max_files: usize,
) -> Result<()> {
    use security::input_validation::{scan_input_validation, InputValidationConfig};
    use security::types::Severity;

    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    let config = InputValidationConfig {
        min_severity: min_sev,
        include_recommended,
        analyze_framework_validation: true,
        max_files,
        language: lang_str.clone(),
    };

    let result =
        scan_input_validation(path, config).map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut sink_type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut validation_type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for finding in &result.findings {
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        *sink_type_counts
            .entry(finding.sink_type.to_string())
            .or_insert(0) += 1;
        for val_type in &finding.missing_validation {
            *validation_type_counts
                .entry(val_type.to_string())
                .or_insert(0) += 1;
        }
    }

    let output_result = serde_json::json!({
        "findings": result.findings,
        "files_scanned": result.files_scanned,
        "files_with_findings": result.files_with_findings,
        "total_findings": result.findings.len(),
        "severity_counts": severity_counts,
        "sink_type_counts": sink_type_counts,
        "missing_validation_counts": validation_type_counts,
        "language": lang_str.unwrap_or_else(|| "all".to_string()),
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output_result).context("Failed to serialize")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Input Validation Analysis Results");
            println!("==================================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Files with findings: {}", result.files_with_findings);
            println!("Total findings: {}", result.findings.len());
            println!();

            if result.findings.is_empty() {
                println!("No input validation issues detected.");
            } else {
                for (i, finding) in result.findings.iter().enumerate() {
                    let marker = if finding.is_required {
                        "[REQUIRED]"
                    } else {
                        "[RECOMMENDED]"
                    };
                    println!(
                        "{}. [{}] {} {}:{}",
                        i + 1,
                        finding.severity,
                        marker,
                        finding.location.file,
                        finding.location.start_line
                    );
                    println!("   Input: {}", finding.input_source);
                    println!("   Sink: {} ({})", finding.sink, finding.sink_type);
                    println!("   Variable: {}", finding.variable);
                    println!("   Missing validations:");
                    for val_type in &finding.missing_validation {
                        println!("     - {}", val_type.description());
                    }
                    if !finding.applied_validation.is_empty() {
                        println!("   Applied validations:");
                        for val_type in &finding.applied_validation {
                            println!("     + {}", val_type.description());
                        }
                    }
                    if !finding.code_snippet.is_empty() {
                        println!("   Code: {}", finding.code_snippet);
                    }
                    println!("   Recommendation:");
                    for line in finding.recommendation.lines() {
                        println!("     {}", line);
                    }
                    println!();
                }

                println!("Summary by Sink Type:");
                let mut sink_vec: Vec<_> = sink_type_counts.iter().collect();
                sink_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (sink_type, count) in sink_vec {
                    println!("  {}: {}", sink_type, count);
                }
                println!();

                println!("Summary by Missing Validation:");
                let mut val_vec: Vec<_> = validation_type_counts.iter().collect();
                val_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (val_type, count) in val_vec {
                    println!("  {}: {}", val_type, count);
                }
                println!();

                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

/// Scan for JavaScript prototype pollution vulnerabilities.
fn cmd_prototype_pollution(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    min_confidence: &str,
) -> Result<()> {
    use security::prototype_pollution::{scan_prototype_pollution, Confidence, Severity};

    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let result = scan_prototype_pollution(path, lang_str.as_deref())
        .map_err(|e| anyhow::anyhow!("Scan failed: {}", e))?;

    // Parse severity/confidence filters
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => Severity::Critical,
        "high" => Severity::High,
        "medium" => Severity::Medium,
        "low" => Severity::Low,
        _ => Severity::Info,
    };

    let min_conf = match min_confidence.to_lowercase().as_str() {
        "high" => Confidence::High,
        "medium" => Confidence::Medium,
        _ => Confidence::Low,
    };

    // Filter findings
    let filtered_findings: Vec<_> = result
        .findings
        .into_iter()
        .filter(|f| f.severity >= min_sev && f.confidence >= min_conf)
        .collect();

    // Rebuild counts from filtered findings
    let mut type_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut severity_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();
    let mut rce_count = 0;

    for finding in &filtered_findings {
        *type_counts
            .entry(finding.pollution_type.to_string())
            .or_insert(0) += 1;
        *severity_counts
            .entry(finding.severity.to_string())
            .or_insert(0) += 1;
        if finding.potential_rce {
            rce_count += 1;
        }
    }

    let output = serde_json::json!({
        "findings": filtered_findings,
        "files_scanned": result.files_scanned,
        "total_findings": filtered_findings.len(),
        "type_counts": type_counts,
        "severity_counts": severity_counts,
        "rce_potential_count": rce_count,
    });

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize")?
            );
        }
        OutputFormat::Text | OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            println!("Prototype Pollution Scan Results");
            println!("=================================");
            println!();
            println!("Files scanned: {}", result.files_scanned);
            println!("Total findings: {}", filtered_findings.len());
            println!("RCE potential: {} findings", rce_count);
            println!();

            if filtered_findings.is_empty() {
                println!("No prototype pollution vulnerabilities detected.");
            } else {
                println!("Findings:");
                println!("---------");
                for (i, finding) in filtered_findings.iter().enumerate() {
                    let rce_marker = if finding.potential_rce {
                        " [RCE RISK]"
                    } else {
                        ""
                    };
                    println!(
                        "{}. [{}] [{}]{} - {}:{}",
                        i + 1,
                        finding.severity,
                        finding.pollution_type,
                        rce_marker,
                        finding.location.file,
                        finding.location.line
                    );
                    println!("   Sink: {}", finding.sink_function);
                    println!("   Path: {}", finding.tainted_path);
                    println!("   Confidence: {}", finding.confidence);
                    println!("   CWE: CWE-{}", finding.cwe_id);
                    println!("   Description: {}", finding.description);
                    if let Some(ref snippet) = finding.code_snippet {
                        println!("   Code:");
                        for line in snippet.lines() {
                            println!("     | {}", line);
                        }
                    }
                    println!("   Remediation: {}", finding.remediation);
                    if !finding.gadget_chains.is_empty() {
                        println!("   Gadget Chains:");
                        for gadget in &finding.gadget_chains {
                            println!("     - {}", gadget);
                        }
                    }
                    println!();
                }

                println!("Summary by Pollution Type:");
                let mut type_vec: Vec<_> = type_counts.iter().collect();
                type_vec.sort_by(|a, b| b.1.cmp(a.1));
                for (ptype, count) in type_vec {
                    println!("  {}: {}", ptype, count);
                }
                println!();

                println!("Summary by Severity:");
                for (severity, count) in &severity_counts {
                    println!("  {}: {}", severity, count);
                }
            }
        }
    }

    Ok(())
}

// =============================================================================
// METRICS COMMANDS
// =============================================================================

fn cmd_metrics(subcmd: MetricsCommands) -> Result<()> {
    match subcmd {
        MetricsCommands::Complexity {
            path,
            lang,
            format,
            threshold,
            sort,
            violations_only,
        } => {
            cmd_complexity(&path, lang, format, threshold, sort, violations_only)?;
        }
        MetricsCommands::Cognitive {
            path,
            lang,
            format,
            threshold,
            sort,
            violations_only,
            breakdown,
        } => {
            cmd_cognitive(
                &path,
                lang,
                format,
                threshold,
                sort,
                violations_only,
                breakdown,
            )?;
        }
        MetricsCommands::Halstead {
            path,
            lang,
            format,
            sort,
            sort_by_difficulty,
            show_tokens,
        } => {
            cmd_halstead(&path, lang, format, sort, sort_by_difficulty, show_tokens)?;
        }
        MetricsCommands::Maintainability {
            path,
            lang,
            format,
            threshold,
            sort,
            violations_only,
            include_comments,
        } => {
            cmd_maintainability(
                &path,
                lang,
                format,
                threshold,
                sort,
                violations_only,
                include_comments,
            )?;
        }
        MetricsCommands::Loc {
            path,
            lang,
            format,
            by_language,
            sort,
            function_threshold,
            violations_only,
            top,
        } => {
            cmd_loc(
                &path,
                lang,
                format,
                by_language,
                sort,
                function_threshold,
                violations_only,
                top,
            )?;
        }
        MetricsCommands::Nesting {
            path,
            lang,
            format,
            threshold,
            sort,
            violations_only,
            details,
        } => {
            cmd_nesting(
                &path,
                lang,
                format,
                threshold,
                sort,
                violations_only,
                details,
            )?;
        }
        MetricsCommands::Functions {
            path,
            lang,
            format,
            sort_by,
            violations_only,
            sloc_warn,
            sloc_critical,
            params_warn,
            params_critical,
            details,
        } => {
            cmd_function_size(
                &path,
                lang,
                format,
                sort_by,
                violations_only,
                sloc_warn,
                sloc_critical,
                params_warn,
                params_critical,
                details,
            )?;
        }
        MetricsCommands::Coupling {
            path,
            lang,
            format,
            level,
            sort,
            threshold,
            show_cycles,
            show_edges,
        } => {
            cmd_coupling(
                &path,
                lang,
                format,
                level,
                sort,
                threshold,
                show_cycles,
                show_edges,
            )?;
        }
        MetricsCommands::Cohesion {
            path,
            lang,
            format,
            threshold,
            sort,
            violations_only,
            show_components,
        } => {
            cmd_cohesion(
                &path,
                lang,
                format,
                threshold,
                sort,
                violations_only,
                show_components,
            )?;
        }
        MetricsCommands::Report {
            path,
            lang,
            format,
            thresholds,
            sort_by,
            issues_only,
            skip_coupling,
            fail_on,
            max_files,
            top,
            show_tokens,
        } => {
            let exit_code = cmd_metrics_report(
                &path,
                lang,
                format,
                &thresholds,
                sort_by,
                issues_only,
                skip_coupling,
                fail_on.as_deref(),
                max_files,
                top,
                show_tokens,
            )?;
            if exit_code != 0 {
                std::process::exit(exit_code);
            }
        }
    }
    Ok(())
}

fn cmd_complexity(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: Option<u32>,
    sort: bool,
    violations_only: bool,
) -> Result<()> {
    use metrics::{analyze_complexity, RiskLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_complexity(path, lang_str.as_deref(), threshold)
        .map_err(|e| anyhow::anyhow!("Complexity analysis failed: {}", e))?;

    // Sort by complexity if requested
    if sort {
        result
            .functions
            .sort_by(|a, b| b.complexity.cmp(&a.complexity));
        if let Some(ref mut violations) = result.violations {
            violations.sort_by(|a, b| b.complexity.cmp(&a.complexity));
        }
    }

    // Filter to violations only if requested
    let output = if violations_only && result.violations.is_some() {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "threshold": result.threshold,
            "violations": result.violations,
            "stats": result.stats,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Cyclomatic Complexity Analysis");
            println!("==============================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!(
                "  Average complexity: {:.2}",
                result.stats.average_complexity
            );
            println!("  Min complexity: {}", result.stats.min_complexity);
            println!("  Max complexity: {}", result.stats.max_complexity);
            println!("  Median complexity: {}", result.stats.median_complexity);
            println!();

            // Risk distribution
            println!("Risk Distribution:");
            for (risk, count) in &result.stats.risk_distribution {
                let level = match risk.as_str() {
                    "low" => RiskLevel::Low,
                    "medium" => RiskLevel::Medium,
                    "high" => RiskLevel::High,
                    "critical" => RiskLevel::Critical,
                    _ => RiskLevel::Low,
                };
                println!("  {}{}: {}\x1b[0m", level.color_code(), risk, count);
            }
            println!();

            // Functions or violations
            let functions_to_show = if violations_only && result.violations.is_some() {
                result.violations.as_ref().unwrap()
            } else {
                &result.functions
            };

            if !functions_to_show.is_empty() {
                let header = if violations_only {
                    format!("Violations (complexity > {}):", threshold.unwrap_or(0))
                } else {
                    "Functions:".to_string()
                };
                println!("{}", header);

                for func in functions_to_show {
                    let level = func.risk_level;
                    println!(
                        "  {}{}: {} ({}) - {}:{}\x1b[0m",
                        level.color_code(),
                        func.function_name,
                        func.complexity,
                        func.risk_level,
                        func.file.display(),
                        func.line
                    );
                }
            }

            // Histogram
            if !result.stats.histogram.is_empty() {
                println!();
                println!("Complexity Histogram:");
                let max_count = result
                    .stats
                    .histogram
                    .iter()
                    .map(|b| b.count)
                    .max()
                    .unwrap_or(1);
                for bucket in &result.stats.histogram {
                    if bucket.count > 0 {
                        let bar_len = (bucket.count as f64 / max_count as f64 * 40.0) as usize;
                        let bar = "#".repeat(bar_len.max(1));
                        println!("  {:>6}: {} ({})", bucket.label, bar, bucket.count);
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for complexity metrics
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print summary if threshold was set
    if let Some(t) = threshold {
        if let Some(ref violations) = result.violations {
            let count = violations.len();
            if count > 0 {
                eprintln!();
                eprintln!(
                    "WARNING: {} function(s) exceed complexity threshold of {}",
                    count, t
                );
            }
        }
    }

    Ok(())
}

fn cmd_cognitive(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: Option<u32>,
    sort: bool,
    violations_only: bool,
    show_breakdown: bool,
) -> Result<()> {
    use metrics::{analyze_cognitive_complexity, CognitiveRiskLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_cognitive_complexity(path, lang_str.as_deref(), threshold)
        .map_err(|e| anyhow::anyhow!("Cognitive complexity analysis failed: {}", e))?;

    // Sort by complexity if requested
    if sort {
        result
            .functions
            .sort_by(|a, b| b.complexity.cmp(&a.complexity));
        if let Some(ref mut violations) = result.violations {
            violations.sort_by(|a, b| b.complexity.cmp(&a.complexity));
        }
    }

    // Filter to violations only if requested
    let output = if violations_only && result.violations.is_some() {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "threshold": result.threshold,
            "violations": result.violations,
            "stats": result.stats,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Cognitive Complexity Analysis (SonarSource)");
            println!("============================================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!(
                "  Average complexity: {:.2}",
                result.stats.average_complexity
            );
            println!("  Min complexity: {}", result.stats.min_complexity);
            println!("  Max complexity: {}", result.stats.max_complexity);
            println!("  Median complexity: {}", result.stats.median_complexity);
            println!(
                "  Average max nesting: {:.2}",
                result.stats.average_max_nesting
            );
            println!(
                "  Functions with recursion: {}",
                result.stats.functions_with_recursion
            );
            println!();

            // Risk distribution
            println!("Risk Distribution:");
            for (risk, count) in &result.stats.risk_distribution {
                let level = match risk.as_str() {
                    "low" => CognitiveRiskLevel::Low,
                    "medium" => CognitiveRiskLevel::Medium,
                    "high" => CognitiveRiskLevel::High,
                    "critical" => CognitiveRiskLevel::Critical,
                    _ => CognitiveRiskLevel::Low,
                };
                println!("  {}{}: {}\x1b[0m", level.color_code(), risk, count);
            }
            println!();

            // Functions or violations
            let functions_to_show = if violations_only && result.violations.is_some() {
                result.violations.as_ref().unwrap()
            } else {
                &result.functions
            };

            if !functions_to_show.is_empty() {
                let header = if violations_only {
                    format!("Violations (complexity > {}):", threshold.unwrap_or(0))
                } else {
                    "Functions:".to_string()
                };
                println!("{}", header);

                for func in functions_to_show {
                    let level = func.risk_level;
                    println!(
                        "  {}{}: {} ({}) - {}:{} [max nesting: {}]\x1b[0m",
                        level.color_code(),
                        func.function_name,
                        func.complexity,
                        func.risk_level,
                        func.file.display(),
                        func.line,
                        func.max_nesting
                    );

                    // Show breakdown if requested and complexity is > 0
                    if show_breakdown && !func.breakdown.is_empty() {
                        for contrib in &func.breakdown {
                            let increment_desc = if contrib.nesting_increment > 0 {
                                format!(
                                    "+{} (base) +{} (nesting)",
                                    contrib.base_increment, contrib.nesting_increment
                                )
                            } else {
                                format!("+{}", contrib.base_increment)
                            };
                            println!(
                                "      L{}: {} {}",
                                contrib.line, contrib.construct, increment_desc
                            );
                        }
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for complexity metrics
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print summary if threshold was set
    if let Some(t) = threshold {
        if let Some(ref violations) = result.violations {
            let count = violations.len();
            if count > 0 {
                eprintln!();
                eprintln!(
                    "WARNING: {} function(s) exceed cognitive complexity threshold of {}",
                    count, t
                );
            }
        }
    }

    Ok(())
}

fn cmd_halstead(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    sort: bool,
    sort_by_difficulty: bool,
    show_tokens: bool,
) -> Result<()> {
    use metrics::{analyze_halstead, QualityLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_halstead(path, lang_str.as_deref(), show_tokens)
        .map_err(|e| anyhow::anyhow!("Halstead analysis failed: {}", e))?;

    // Sort by volume or difficulty if requested
    if sort || sort_by_difficulty {
        if sort_by_difficulty {
            result.functions.sort_by(|a, b| {
                b.metrics
                    .difficulty
                    .partial_cmp(&a.metrics.difficulty)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
        } else {
            result.functions.sort_by(|a, b| {
                b.metrics
                    .volume
                    .partial_cmp(&a.metrics.volume)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
        }
    }

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            let output = serde_json::to_value(&result).context("Failed to serialize result")?;
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Halstead Complexity Analysis");
            println!("============================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Aggregate statistics
            println!("Aggregate Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!("  Average volume: {:.1}", result.stats.avg_volume);
            println!("  Max volume: {:.1}", result.stats.max_volume);
            println!("  Average difficulty: {:.1}", result.stats.avg_difficulty);
            println!("  Max difficulty: {:.1}", result.stats.max_difficulty);
            println!("  Total estimated bugs: {:.2}", result.stats.total_bugs);
            println!(
                "  Total estimated time: {:.0}s ({:.1}h)",
                result.stats.total_time_seconds,
                result.stats.total_time_seconds / 3600.0
            );
            println!();

            // Function details
            if !result.functions.is_empty() {
                println!("Functions:");
                for func in &result.functions {
                    // Color based on volume level
                    let color = match func.quality.volume_level {
                        QualityLevel::Low => "\x1b[32m",      // Green
                        QualityLevel::Medium => "\x1b[33m",   // Yellow
                        QualityLevel::High => "\x1b[31m",     // Red
                        QualityLevel::VeryHigh => "\x1b[35m", // Magenta
                    };

                    println!(
                        "  {}{}: V={:.1}, D={:.1}, E={:.0}, T={:.0}s, B={:.3}\x1b[0m",
                        color,
                        func.function_name,
                        func.metrics.volume,
                        func.metrics.difficulty,
                        func.metrics.effort,
                        func.metrics.time_seconds,
                        func.metrics.bugs
                    );
                    println!(
                        "      n1={}, n2={}, N1={}, N2={} - {}:{}",
                        func.metrics.distinct_operators,
                        func.metrics.distinct_operands,
                        func.metrics.total_operators,
                        func.metrics.total_operands,
                        func.file.display(),
                        func.line
                    );

                    // Show tokens if requested
                    if show_tokens {
                        if let Some(ref operators) = func.operators {
                            let ops_preview: Vec<_> = operators.iter().take(10).collect();
                            let suffix = if operators.len() > 10 {
                                format!("... (+{} more)", operators.len() - 10)
                            } else {
                                String::new()
                            };
                            println!("      Operators: {:?}{}", ops_preview, suffix);
                        }
                        if let Some(ref operands) = func.operands {
                            let ops_preview: Vec<_> = operands.iter().take(10).collect();
                            let suffix = if operands.len() > 10 {
                                format!("... (+{} more)", operands.len() - 10)
                            } else {
                                String::new()
                            };
                            println!("      Operands: {:?}{}", ops_preview, suffix);
                        }
                    }
                }
            }

            // Errors
            if !result.errors.is_empty() {
                println!();
                println!("Errors ({}):", result.errors.len());
                for err in &result.errors {
                    println!("  {}: {}", err.file.display(), err.message);
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for Halstead metrics
            let output = serde_json::to_value(&result).context("Failed to serialize result")?;
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warning if there are high-complexity functions
    let high_complexity_count = result
        .functions
        .iter()
        .filter(|f| {
            matches!(
                f.quality.difficulty_level,
                QualityLevel::High | QualityLevel::VeryHigh
            )
        })
        .count();

    if high_complexity_count > 0 {
        eprintln!();
        eprintln!(
            "WARNING: {} function(s) have high difficulty (>15), consider refactoring",
            high_complexity_count
        );
    }

    Ok(())
}

fn cmd_maintainability(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: Option<f64>,
    sort: bool,
    violations_only: bool,
    include_comments: bool,
) -> Result<()> {
    use metrics::{analyze_maintainability, MaintainabilityRiskLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result =
        analyze_maintainability(path, lang_str.as_deref(), threshold, include_comments)
            .map_err(|e| anyhow::anyhow!("Maintainability analysis failed: {}", e))?;

    // Sort by MI score (lowest first - worst maintainability)
    if sort {
        result.functions.sort_by(|a, b| {
            a.index
                .score
                .partial_cmp(&b.index.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        if let Some(ref mut violations) = result.violations {
            violations.sort_by(|a, b| {
                a.index
                    .score
                    .partial_cmp(&b.index.score)
                    .unwrap_or(std::cmp::Ordering::Equal)
            });
        }
    }

    // Filter to violations only if requested
    let output = if violations_only && result.violations.is_some() {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "threshold": result.threshold,
            "violations": result.violations,
            "stats": result.stats,
            "includes_comments": result.includes_comments,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Maintainability Index Analysis");
            println!("===============================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            if result.includes_comments {
                println!("Formula: Extended (with comment bonus)");
            } else {
                println!("Formula: Standard (Visual Studio)");
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!("  Average MI: {:.1}", result.stats.average_mi);
            println!("  Min MI: {:.1}", result.stats.min_mi);
            println!("  Max MI: {:.1}", result.stats.max_mi);
            println!("  Median MI: {:.1}", result.stats.median_mi);
            println!("  Total SLOC: {}", result.stats.total_sloc);
            println!(
                "  Total comment lines: {}",
                result.stats.total_comment_lines
            );
            println!(
                "  Overall comment %: {:.1}%",
                result.stats.overall_comment_percentage
            );
            println!(
                "  Average Halstead Volume: {:.1}",
                result.stats.average_volume
            );
            println!(
                "  Average Cyclomatic Complexity: {:.1}",
                result.stats.average_cc
            );
            println!();

            // Risk distribution
            println!("Risk Distribution:");
            for (risk, count) in &result.stats.risk_distribution {
                let level = match risk.as_str() {
                    "low" => MaintainabilityRiskLevel::Low,
                    "medium" => MaintainabilityRiskLevel::Medium,
                    "high" => MaintainabilityRiskLevel::High,
                    "critical" => MaintainabilityRiskLevel::Critical,
                    _ => MaintainabilityRiskLevel::Medium,
                };
                println!("  {}{}: {}\x1b[0m", level.color_code(), risk, count);
            }
            println!();

            // Functions or violations
            let functions_to_show = if violations_only && result.violations.is_some() {
                result.violations.as_ref().unwrap()
            } else {
                &result.functions
            };

            if !functions_to_show.is_empty() {
                let header = if violations_only {
                    format!("Violations (MI < {}):", threshold.unwrap_or(0.0))
                } else {
                    "Functions:".to_string()
                };
                println!("{}", header);

                for func in functions_to_show {
                    let level = func.index.risk_level;
                    println!(
                        "  {}{}: MI={:.1} ({}) - {}:{}\x1b[0m",
                        level.color_code(),
                        func.function_name,
                        func.index.score,
                        func.index.risk_level,
                        func.file.display(),
                        func.line
                    );
                    println!(
                        "      V={:.1}, CC={}, SLOC={}, Comments={:.1}%",
                        func.index.halstead_volume,
                        func.index.cyclomatic_complexity,
                        func.index.lines_of_code.effective,
                        func.index.comment_percentage
                    );
                }
            }

            // Errors
            if !result.errors.is_empty() {
                println!();
                println!("Errors ({}):", result.errors.len());
                for err in &result.errors {
                    println!("  {}: {}", err.file.display(), err.message);
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for maintainability metrics - output JSON instead
            let output = serde_json::to_value(&result).context("Failed to serialize result")?;
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warning if there are low-maintainability functions
    if let Some(t) = threshold {
        if let Some(ref violations) = result.violations {
            let count = violations.len();
            if count > 0 {
                eprintln!();
                eprintln!(
                    "WARNING: {} function(s) have Maintainability Index below {} (hard to maintain)",
                    count, t
                );
            }
        }
    }

    // Always warn about critical functions
    let critical_count = result
        .functions
        .iter()
        .filter(|f| matches!(f.index.risk_level, MaintainabilityRiskLevel::Critical))
        .count();

    if critical_count > 0 {
        eprintln!();
        eprintln!(
            "CRITICAL: {} function(s) have MI < 10 (very hard to maintain, refactor immediately)",
            critical_count
        );
    }

    Ok(())
}

fn cmd_loc(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    by_language: bool,
    sort: bool,
    function_threshold: u32,
    violations_only: bool,
    top: usize,
) -> Result<()> {
    use metrics::analyze_loc;

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_loc(path, lang_str.as_deref(), Some(function_threshold))
        .map_err(|e| anyhow::anyhow!("LOC analysis failed: {}", e))?;

    // Sort files by SLOC if requested
    if sort {
        result
            .files
            .sort_by(|a, b| b.metrics.source.cmp(&a.metrics.source));
    }

    // Filter to violations only if requested
    let output = if violations_only {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "function_threshold": function_threshold,
            "oversized_functions": result.oversized_functions,
            "stats": {
                "total_functions": result.stats.total_functions,
                "oversized_function_count": result.stats.oversized_function_count,
            },
        })
    } else if by_language {
        serde_json::json!({
            "path": result.path,
            "by_language": result.by_language,
            "stats": result.stats,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Lines of Code Analysis");
            println!("======================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Distribution statistics
            println!("Statistics:");
            println!("  Total SLOC: {}", result.stats.total_sloc);
            println!("  Total physical lines: {}", result.stats.total_physical);
            println!("  Total logical lines: {}", result.stats.total_logical);
            println!("  Comment lines: {}", result.stats.total_comment);
            println!("  Blank lines: {}", result.stats.total_blank);
            println!(
                "  Code-to-comment ratio: {:.2}",
                result.stats.code_to_comment_ratio
            );
            println!("  Blank ratio: {:.1}%", result.stats.blank_ratio);
            println!("  Files analyzed: {}", result.files.len());
            println!("  Average SLOC/file: {:.1}", result.stats.avg_sloc_per_file);
            println!("  Max SLOC: {}", result.stats.max_sloc);
            println!("  Min SLOC: {}", result.stats.min_sloc);
            println!("  Median SLOC: {}", result.stats.median_sloc);
            println!();

            // Function statistics
            println!("Function Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!(
                "  Average function size: {:.1} SLOC",
                result.stats.avg_function_size
            );
            println!(
                "  Oversized functions (>{} SLOC): {}",
                function_threshold, result.stats.oversized_function_count
            );
            println!();

            // By language if requested
            if by_language && !result.by_language.is_empty() {
                println!("By Language:");
                for lang_stats in &result.by_language {
                    println!(
                        "  {}: {} files, {} SLOC, {:.1} avg SLOC/file",
                        lang_stats.language,
                        lang_stats.file_count,
                        lang_stats.metrics.source,
                        lang_stats.avg_sloc_per_file
                    );
                }
                println!();
            }

            // Largest files
            if !result.largest_files.is_empty() {
                println!(
                    "Largest Files (top {}):",
                    top.min(result.largest_files.len())
                );
                for (i, file) in result.largest_files.iter().take(top).enumerate() {
                    println!(
                        "  {}. {} - {} SLOC ({:.1}%)",
                        i + 1,
                        file.file.display(),
                        file.sloc,
                        file.percentage
                    );
                }
                println!();
            }

            // Oversized functions (violations)
            if !result.oversized_functions.is_empty() {
                println!("Oversized Functions (>{} SLOC):", function_threshold);
                for func in &result.oversized_functions {
                    println!(
                        "  \x1b[33m{}: {} SLOC - {}:{}\x1b[0m",
                        func.name,
                        func.sloc,
                        func.file.display(),
                        func.line
                    );
                }
            }

            // Errors
            if !result.errors.is_empty() {
                println!();
                println!("Errors ({}):", result.errors.len());
                for err in &result.errors {
                    println!("  {}: {}", err.file.display(), err.message);
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for LOC metrics - output JSON
            let output = serde_json::to_value(&result).context("Failed to serialize result")?;
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warning about oversized functions
    if result.stats.oversized_function_count > 0 {
        eprintln!();
        eprintln!(
            "WARNING: {} function(s) exceed {} SLOC threshold (consider splitting)",
            result.stats.oversized_function_count, function_threshold
        );
    }

    Ok(())
}

fn cmd_nesting(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: Option<u32>,
    sort: bool,
    violations_only: bool,
    details: bool,
) -> Result<()> {
    use metrics::{analyze_nesting, NestingDepthLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_nesting(path, lang_str.as_deref(), threshold)
        .map_err(|e| anyhow::anyhow!("Nesting analysis failed: {}", e))?;

    // Sort by depth if requested
    if sort {
        result
            .functions
            .sort_by(|a, b| b.max_depth.cmp(&a.max_depth));
        if let Some(ref mut violations) = result.violations {
            violations.sort_by(|a, b| b.max_depth.cmp(&a.max_depth));
        }
    }

    // Filter to violations only if requested
    let output = if violations_only && result.violations.is_some() {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "threshold": result.threshold,
            "violations": result.violations,
            "stats": result.stats,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Nesting Depth Analysis");
            println!("======================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            if let Some(t) = result.threshold {
                println!("Threshold: {}", t);
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!("  Average max depth: {:.2}", result.stats.average_max_depth);
            println!("  Global max depth: {}", result.stats.global_max_depth);
            println!("  Min max depth: {}", result.stats.min_max_depth);
            println!("  Median max depth: {}", result.stats.median_max_depth);
            println!(
                "  Functions over threshold: {}",
                result.stats.functions_over_threshold
            );
            println!();

            // Risk distribution
            println!("Risk Distribution:");
            for (risk, count) in &result.stats.risk_distribution {
                let level = match risk.as_str() {
                    "good" => NestingDepthLevel::Good,
                    "acceptable" => NestingDepthLevel::Acceptable,
                    "complex" => NestingDepthLevel::Complex,
                    "severe" => NestingDepthLevel::Severe,
                    _ => NestingDepthLevel::Good,
                };
                println!("  {}{}: {}\x1b[0m", level.color_code(), risk, count);
            }
            println!();

            // Functions or violations
            let functions_to_show = if violations_only && result.violations.is_some() {
                result.violations.as_ref().unwrap()
            } else {
                &result.functions
            };

            if !functions_to_show.is_empty() {
                let header = if violations_only {
                    format!("Violations (depth > {}):", threshold.unwrap_or(5))
                } else {
                    "Functions:".to_string()
                };
                println!("{}", header);

                for func in functions_to_show {
                    let level = func.risk_level;
                    println!(
                        "  {}{}: max_depth={} avg={:.1} ({}) - {}:{}\x1b[0m",
                        level.color_code(),
                        func.function_name,
                        func.max_depth,
                        func.average_depth,
                        func.risk_level,
                        func.file.display(),
                        func.line
                    );

                    // Show details if requested
                    if details {
                        if func.max_depth > 0 {
                            println!("    Deepest at line: {}", func.deepest_line);
                        }

                        // Show deep locations
                        if !func.deep_locations.is_empty() {
                            println!("    Deep nesting locations:");
                            for loc in &func.deep_locations {
                                println!(
                                    "      Line {}: depth {} [{}]",
                                    loc.line,
                                    loc.depth,
                                    loc.construct_stack.join(" > ")
                                );
                            }
                        }

                        // Show suggestions
                        if !func.suggestions.is_empty() {
                            println!("    Suggestions:");
                            for suggestion in &func.suggestions {
                                println!("      - {}", suggestion);
                            }
                        }

                        // Show depth distribution
                        if !func.depth_distribution.is_empty() {
                            let mut depths: Vec<_> = func.depth_distribution.iter().collect();
                            depths.sort_by_key(|&(d, _)| d);
                            print!("    Depth distribution: ");
                            for (depth, count) in depths {
                                print!("d{}={} ", depth, count);
                            }
                            println!();
                        }

                        println!();
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for nesting metrics - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warning if threshold was set and there are violations
    if let Some(t) = threshold {
        if let Some(ref violations) = result.violations {
            let count = violations.len();
            if count > 0 {
                eprintln!();
                eprintln!(
                    "WARNING: {} function(s) have nesting depth > {} (consider refactoring)",
                    count, t
                );
            }
        }
    }

    Ok(())
}

fn cmd_function_size(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    sort_by: Option<String>,
    violations_only: bool,
    sloc_warn: u32,
    sloc_critical: u32,
    params_warn: u32,
    params_critical: u32,
    details: bool,
) -> Result<()> {
    use metrics::{analyze_function_size, sort_size_functions, SizeSortBy, SizeThresholds};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Build custom thresholds from CLI args
    let thresholds = SizeThresholds {
        sloc_warning: sloc_warn,
        sloc_critical,
        params_warning: params_warn,
        params_critical,
        ..SizeThresholds::default()
    };

    let mut result = analyze_function_size(path, lang_str.as_deref(), Some(thresholds.clone()))
        .map_err(|e| anyhow::anyhow!("Function size analysis failed: {}", e))?;

    // Sort if requested
    if let Some(ref sort_field) = sort_by {
        let sort_option = sort_field.parse::<SizeSortBy>().unwrap_or(SizeSortBy::Sloc);
        sort_size_functions(&mut result.functions, sort_option, true); // descending
        sort_size_functions(&mut result.violations, sort_option, true);
    }

    // Filter to violations only if requested
    let output = if violations_only {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "violations": result.violations,
            "stats": result.stats,
            "thresholds": result.thresholds,
        })
    } else {
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Function Size Analysis");
            println!("======================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total functions: {}", result.stats.total_functions);
            println!(
                "  Functions with issues: {} ({:.1}%)",
                result.stats.functions_with_issues,
                if result.stats.total_functions > 0 {
                    result.stats.functions_with_issues as f64 / result.stats.total_functions as f64
                        * 100.0
                } else {
                    0.0
                }
            );
            println!("  Critical issues: {}", result.stats.critical_issues);
            println!("  Warning issues: {}", result.stats.warning_issues);
            println!("  Average SLOC: {:.1}", result.stats.avg_sloc);
            println!("  Max SLOC: {}", result.stats.max_sloc);
            println!("  Average parameters: {:.1}", result.stats.avg_parameters);
            println!("  Max parameters: {}", result.stats.max_parameters);
            println!();

            // Thresholds
            println!("Thresholds:");
            println!(
                "  SLOC: warning > {}, critical > {}",
                thresholds.sloc_warning, thresholds.sloc_critical
            );
            println!(
                "  Parameters: warning > {}, critical > {}",
                thresholds.params_warning, thresholds.params_critical
            );
            println!(
                "  Variables: warning > {}, critical > {}",
                thresholds.variables_warning, thresholds.variables_critical
            );
            println!("  Returns: warning > {}", thresholds.returns_warning);
            println!();

            // Issue counts
            if !result.stats.issue_counts.is_empty() {
                println!("Issue Breakdown:");
                for (issue_type, count) in &result.stats.issue_counts {
                    println!("  {}: {}", issue_type.replace('_', " "), count);
                }
                println!();
            }

            // Category distribution
            if !result.stats.category_distribution.is_empty() {
                println!("Function Categories:");
                for (category, count) in &result.stats.category_distribution {
                    println!("  {}: {}", category, count);
                }
                println!();
            }

            // Functions or violations
            let functions_to_show = if violations_only {
                &result.violations
            } else {
                &result.functions
            };

            if !functions_to_show.is_empty() {
                let header = if violations_only {
                    "Functions with Issues:".to_string()
                } else {
                    "All Functions:".to_string()
                };
                println!("{}", header);

                for func in functions_to_show {
                    let severity = func.max_severity();
                    let color = severity.map(|s| s.color_code()).unwrap_or("\x1b[32m"); // Green if no issues

                    let issue_indicator = if func.issues.is_empty() {
                        "OK".to_string()
                    } else {
                        format!("{} issue(s)", func.issues.len())
                    };

                    println!(
                        "  {}{}: sloc={} params={} vars={} returns={} branches={} [{}] - {}:{}\x1b[0m",
                        color,
                        func.name,
                        func.sloc,
                        func.parameters,
                        func.local_variables,
                        func.return_statements,
                        func.branches,
                        issue_indicator,
                        func.file.display(),
                        func.line
                    );

                    // Show details if requested
                    if details {
                        println!("    Category: {}", func.category);
                        println!("    Size score: {:.1}", func.size_score());

                        // Show issues
                        if !func.issues.is_empty() {
                            println!("    Issues:");
                            for issue in &func.issues {
                                let sev_color = issue.severity().color_code();
                                println!(
                                    "      {}{}: {}\x1b[0m",
                                    sev_color,
                                    issue.severity(),
                                    issue.description()
                                );
                            }
                        }

                        // Show suggestions
                        if !func.suggestions.is_empty() {
                            println!("    Suggestions:");
                            for suggestion in &func.suggestions {
                                println!("      - {}", suggestion);
                            }
                        }

                        println!();
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for function size metrics - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print summary warning if there are violations
    let total_issues = result.stats.critical_issues + result.stats.warning_issues;
    if total_issues > 0 {
        eprintln!();
        eprintln!(
            "WARNING: {} function(s) with {} issue(s) detected (consider refactoring)",
            result.stats.functions_with_issues, total_issues
        );
        if result.stats.critical_issues > 0 {
            eprintln!(
                "  {} critical issue(s) require immediate attention",
                result.stats.critical_issues
            );
        }
    }

    Ok(())
}

fn cmd_coupling(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    level: CouplingLevelArg,
    sort: bool,
    threshold: Option<f64>,
    show_cycles: bool,
    show_edges: bool,
) -> Result<()> {
    use metrics::{analyze_coupling, CouplingLevel, CouplingRisk};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());
    let coupling_level: CouplingLevel = level.into();

    let mut result = analyze_coupling(path, lang_str.as_deref(), coupling_level)
        .map_err(|e| anyhow::anyhow!("Coupling analysis failed: {}", e))?;

    // Sort by distance if requested (already sorted by default, but reverse if not)
    if !sort {
        // Default: sort by module name for stable output
        result.modules.sort_by(|a, b| a.module.cmp(&b.module));
    }

    // Filter by threshold if specified
    if let Some(t) = threshold {
        result.modules.retain(|m| m.distance >= t);
    }

    // Build output based on options
    let mut output = serde_json::to_value(&result).context("Failed to serialize result")?;

    // Remove edges if not requested
    if !show_edges {
        if let Some(obj) = output.as_object_mut() {
            obj.remove("edges");
        }
    }

    // Remove cycles if not requested
    if !show_cycles {
        if let Some(obj) = output.as_object_mut() {
            obj.remove("circular_dependencies");
        }
    }

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Coupling Analysis");
            println!("=================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!("Level: {}", result.level);
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total modules: {}", result.stats.total_modules);
            println!("  Total dependencies: {}", result.stats.total_dependencies);
            println!("  Average afferent (Ca): {:.2}", result.stats.avg_afferent);
            println!("  Average efferent (Ce): {:.2}", result.stats.avg_efferent);
            println!(
                "  Average instability (I): {:.2}",
                result.stats.avg_instability
            );
            println!("  Average distance (D): {:.2}", result.stats.avg_distance);
            println!();

            // Zone warnings
            if result.stats.zone_of_pain_count > 0 {
                println!(
                    "  \x1b[31mZone of Pain: {} module(s)\x1b[0m (stable, concrete - rigid)",
                    result.stats.zone_of_pain_count
                );
            }
            if result.stats.zone_of_uselessness_count > 0 {
                println!(
                    "  \x1b[33mZone of Uselessness: {} module(s)\x1b[0m (unstable, abstract)",
                    result.stats.zone_of_uselessness_count
                );
            }
            println!();

            // Risk distribution
            if !result.stats.risk_distribution.is_empty() {
                println!("Risk Distribution:");
                for (risk, count) in &result.stats.risk_distribution {
                    let risk_level = match risk.as_str() {
                        "low" => CouplingRisk::Low,
                        "medium" => CouplingRisk::Medium,
                        "high" => CouplingRisk::High,
                        "critical" => CouplingRisk::Critical,
                        _ => CouplingRisk::Low,
                    };
                    println!("  {}{}: {}\x1b[0m", risk_level.color_code(), risk, count);
                }
                println!();
            }

            // Most depended upon
            if !result.stats.most_depended.is_empty() {
                println!("Most Depended Upon (highest Ca):");
                for module in &result.stats.most_depended {
                    println!("  - {}", module);
                }
                println!();
            }

            // Most dependent
            if !result.stats.most_dependent.is_empty() {
                println!("Most Dependent (highest Ce):");
                for module in &result.stats.most_dependent {
                    println!("  - {}", module);
                }
                println!();
            }

            // Circular dependencies
            if show_cycles && !result.circular_dependencies.is_empty() {
                println!("\x1b[31mCircular Dependencies Detected:\x1b[0m");
                for (i, cycle) in result.circular_dependencies.iter().enumerate() {
                    println!(
                        "  {}. {} -> {}",
                        i + 1,
                        cycle.join(" -> "),
                        cycle.first().unwrap_or(&String::new())
                    );
                }
                println!();
            }

            // Module details
            println!("Modules (sorted by distance from main sequence):");
            println!("{:-<100}", "");
            println!(
                "{:<40} {:>4} {:>4} {:>6} {:>6} {:>6}  {}",
                "Module", "Ca", "Ce", "I", "A", "D", "Position"
            );
            println!("{:-<100}", "");

            for module in &result.modules {
                let risk = CouplingRisk::from_distance(module.distance);
                let position = module.position_description();

                println!(
                    "{}{:<40} {:>4} {:>4} {:>6.2} {:>6.2} {:>6.2}  {}\x1b[0m",
                    risk.color_code(),
                    if module.module.len() > 40 {
                        format!("{}...", &module.module[..37])
                    } else {
                        module.module.clone()
                    },
                    module.afferent,
                    module.efferent,
                    module.instability,
                    module.abstractness,
                    module.distance,
                    position
                );
            }

            // Show edges if requested
            if show_edges && !result.edges.is_empty() {
                println!();
                println!("Dependency Edges:");
                println!("{:-<80}", "");
                for edge in &result.edges {
                    println!(
                        "  {} -> {} [{}]{}",
                        edge.from,
                        edge.to,
                        edge.dependency_type,
                        if edge.items.is_empty() {
                            String::new()
                        } else {
                            format!(" ({})", edge.items.join(", "))
                        }
                    );
                }
            }
        }
        OutputFormat::Mermaid => {
            // Generate Mermaid flowchart of dependencies
            println!("flowchart TD");
            println!("    %% Coupling Analysis - {}", result.path.display());

            // Add nodes with styling based on risk
            for module in &result.modules {
                let risk = CouplingRisk::from_distance(module.distance);
                let style = match risk {
                    CouplingRisk::Low => "fill:#90EE90",      // Light green
                    CouplingRisk::Medium => "fill:#FFE4B5",   // Moccasin (yellow-ish)
                    CouplingRisk::High => "fill:#FFA07A",     // Light salmon
                    CouplingRisk::Critical => "fill:#FF6B6B", // Red
                };
                let node_id = module
                    .module
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                println!(
                    "    {}[\"{}<br/>Ca={} Ce={} I={:.2}\"]",
                    node_id, module.module, module.afferent, module.efferent, module.instability
                );
                println!("    style {} {}", node_id, style);
            }

            // Add edges
            for edge in &result.edges {
                let from_id = edge
                    .from
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                let to_id = edge
                    .to
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                println!("    {} --> {}", from_id, to_id);
            }
        }
        OutputFormat::Dot => {
            // Generate DOT graph
            println!("digraph coupling {{");
            println!("    rankdir=LR;");
            println!("    node [shape=box];");
            println!("    // Coupling Analysis - {}", result.path.display());
            println!();

            // Add nodes with colors based on risk
            for module in &result.modules {
                let risk = CouplingRisk::from_distance(module.distance);
                let color = match risk {
                    CouplingRisk::Low => "lightgreen",
                    CouplingRisk::Medium => "lightyellow",
                    CouplingRisk::High => "lightsalmon",
                    CouplingRisk::Critical => "lightcoral",
                };
                let node_id = module
                    .module
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                println!(
                    "    {} [label=\"{}\\nCa={} Ce={}\\nI={:.2} D={:.2}\" fillcolor={} style=filled];",
                    node_id,
                    module.module,
                    module.afferent,
                    module.efferent,
                    module.instability,
                    module.distance,
                    color
                );
            }

            println!();

            // Add edges
            for edge in &result.edges {
                let from_id = edge
                    .from
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                let to_id = edge
                    .to
                    .replace('.', "_")
                    .replace('/', "_")
                    .replace(':', "_");
                let style = match edge.dependency_type {
                    metrics::DependencyType::Import => "solid",
                    metrics::DependencyType::Call => "dashed",
                    metrics::DependencyType::Type => "dotted",
                    metrics::DependencyType::Inheritance => "bold",
                };
                println!("    {} -> {} [style={}];", from_id, to_id, style);
            }

            println!("}}");
        }
        OutputFormat::Csv => {
            // CSV not applicable for coupling analysis - fall back to JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warnings
    if result.stats.zone_of_pain_count > 0 || result.stats.zone_of_uselessness_count > 0 {
        eprintln!();
        if result.stats.zone_of_pain_count > 0 {
            eprintln!(
                "WARNING: {} module(s) in Zone of Pain (stable but concrete - hard to modify)",
                result.stats.zone_of_pain_count
            );
        }
        if result.stats.zone_of_uselessness_count > 0 {
            eprintln!(
                "WARNING: {} module(s) in Zone of Uselessness (abstract but unstable)",
                result.stats.zone_of_uselessness_count
            );
        }
    }

    if !result.circular_dependencies.is_empty() {
        eprintln!();
        eprintln!(
            "WARNING: {} circular dependency cycle(s) detected",
            result.circular_dependencies.len()
        );
    }

    Ok(())
}

fn cmd_cohesion(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: Option<u32>,
    sort: bool,
    violations_only: bool,
    show_components: bool,
) -> Result<()> {
    use metrics::{analyze_cohesion, CohesionLevel};

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    let mut result = analyze_cohesion(path, lang_str.as_deref(), threshold)
        .map_err(|e| anyhow::anyhow!("Cohesion analysis failed: {}", e))?;

    // Sort by LCOM4 if requested (highest first = worst cohesion)
    if sort {
        result.classes.sort_by(|a, b| b.lcom4.cmp(&a.lcom4));
        if let Some(ref mut violations) = result.violations {
            violations.sort_by(|a, b| b.lcom4.cmp(&a.lcom4));
        }
    }

    // Build output based on violations_only flag
    let output = if violations_only && result.violations.is_some() {
        serde_json::json!({
            "path": result.path,
            "language": result.language,
            "violations": result.violations,
            "stats": result.stats,
            "threshold": result.threshold,
        })
    } else {
        // Optionally strip components if not requested
        if !show_components {
            for class in &mut result.classes {
                class.components.clear();
            }
            if let Some(ref mut violations) = result.violations {
                for class in violations {
                    class.components.clear();
                }
            }
        }
        serde_json::to_value(&result).context("Failed to serialize result")?
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("Cohesion Analysis (LCOM)");
            println!("========================");
            println!("Path: {}", result.path.display());
            if let Some(ref lang) = result.language {
                println!("Language: {}", lang);
            }
            println!();

            // Statistics
            println!("Statistics:");
            println!("  Total classes: {}", result.stats.total_classes);
            println!("  Cohesive (LCOM3=1): {}", result.stats.cohesive_classes);
            println!(
                "  Low cohesion (LCOM3>1): {}",
                result.stats.low_cohesion_classes
            );
            println!("  Average LCOM3: {:.2}", result.stats.average_lcom3);
            println!("  Max LCOM3: {}", result.stats.max_lcom3);
            println!("  Average methods: {:.1}", result.stats.average_methods);
            println!(
                "  Average attributes: {:.1}",
                result.stats.average_attributes
            );
            println!();

            // Distribution
            if !result.stats.cohesion_distribution.is_empty() {
                println!("Cohesion Distribution:");
                for (level, count) in &result.stats.cohesion_distribution {
                    println!("  {}: {}", level, count);
                }
                println!();
            }

            // Classes
            let classes_to_show = if violations_only {
                result
                    .violations
                    .as_ref()
                    .map(|v| v.as_slice())
                    .unwrap_or(&[])
            } else {
                &result.classes
            };

            if classes_to_show.is_empty() {
                if violations_only {
                    println!("No classes with low cohesion found.");
                } else {
                    println!("No classes found.");
                }
            } else {
                println!("Classes ({}):", classes_to_show.len());
                for class in classes_to_show {
                    let level = CohesionLevel::from_lcom3(class.lcom3);
                    println!(
                        "  {}{}: LCOM1={} LCOM3={} LCOM4={} methods={} attrs={} ({})\x1b[0m - {}:{}",
                        level.color_code(),
                        class.class_name,
                        class.lcom1,
                        class.lcom3,
                        class.lcom4,
                        class.methods,
                        class.attributes,
                        class.cohesion_level,
                        class.file.display(),
                        class.line
                    );

                    if class.is_low_cohesion {
                        if let Some(ref suggestion) = class.suggestion {
                            println!("    Suggestion: {}", suggestion);
                        }
                    }

                    if show_components && !class.components.is_empty() {
                        println!("    Connected components:");
                        for (i, component) in class.components.iter().enumerate() {
                            println!("      {}: {:?}", i + 1, component);
                        }
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not directly applicable for cohesion - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print warning if there are low cohesion classes
    if result.stats.low_cohesion_classes > 0 {
        eprintln!();
        eprintln!(
            "WARNING: {} class(es) have low cohesion (LCOM3 > 1) - consider splitting",
            result.stats.low_cohesion_classes
        );
    }

    Ok(())
}

fn cmd_metrics_report(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold_preset: &str,
    sort_by: Option<String>,
    issues_only: bool,
    skip_coupling: bool,
    fail_on: Option<&str>,
    max_files: usize,
    top: usize,
    show_tokens: bool,
) -> Result<i32> {
    use metrics::{
        analyze_all_metrics, sort_unified_functions, FunctionSortBy, IssueSeverity,
        MetricThresholds, MetricsConfig, QualityGate,
    };

    // Validate path exists
    require_exists(path)?;

    let lang_str = lang.map(|l| l.to_string());

    // Build configuration based on threshold preset
    let thresholds = match threshold_preset.to_lowercase().as_str() {
        "strict" => MetricThresholds::strict(),
        "relaxed" => MetricThresholds::relaxed(),
        _ => MetricThresholds::default(),
    };

    let config = MetricsConfig {
        thresholds,
        include_halstead_tokens: show_tokens,
        include_cognitive_breakdown: false,
        include_cohesion_components: false,
        analyze_coupling: !skip_coupling,
        coupling_level: metrics::CouplingLevel::File,
        max_files,
        show_progress: false,
    };

    eprintln!("Analyzing metrics for: {}", path.display());
    let start = std::time::Instant::now();

    let mut report = analyze_all_metrics(path, lang_str.as_deref(), &config)
        .map_err(|e| anyhow::anyhow!("Metrics analysis failed: {}", e))?;

    // Sort functions if requested
    if let Some(ref sort_field) = sort_by {
        if let Ok(sort_by) = sort_field.parse::<FunctionSortBy>() {
            sort_unified_functions(&mut report.function_metrics, sort_by);
        }
    }

    // Filter to issues only if requested
    let functions_to_show = if issues_only {
        report
            .function_metrics
            .iter()
            .filter(|f| {
                !f.size_issues.is_empty()
                    || f.cyclomatic_risk == metrics::RiskLevel::High
                    || f.cyclomatic_risk == metrics::RiskLevel::Critical
                    || f.cognitive_risk == metrics::CognitiveRiskLevel::High
                    || f.cognitive_risk == metrics::CognitiveRiskLevel::Critical
                    || f.maintainability_risk == metrics::MaintainabilityRiskLevel::High
                    || f.maintainability_risk == metrics::MaintainabilityRiskLevel::Critical
            })
            .take(top)
            .cloned()
            .collect::<Vec<_>>()
    } else {
        report.function_metrics.iter().take(top).cloned().collect()
    };

    let elapsed = start.elapsed();
    eprintln!("Analysis completed in {:.2}s", elapsed.as_secs_f64());

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            // Build filtered output
            let output = if issues_only {
                serde_json::json!({
                    "path": report.path,
                    "language": report.language,
                    "analysis_duration_ms": report.analysis_duration_ms,
                    "project_summary": report.project_summary,
                    "issues": report.issues,
                    "issue_stats": report.issue_stats,
                    "functions": functions_to_show,
                })
            } else {
                serde_json::to_value(&report).context("Failed to serialize report")?
            };

            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!(
                "================================================================================"
            );
            println!("                      UNIFIED METRICS REPORT");
            println!(
                "================================================================================"
            );
            println!();
            println!("Path: {}", report.path.display());
            if let Some(ref lang) = report.language {
                println!("Language: {}", lang);
            }
            println!("Analysis duration: {}ms", report.analysis_duration_ms);
            println!("Threshold preset: {}", threshold_preset);
            println!();

            // Project Summary
            println!("PROJECT SUMMARY");
            println!("---------------");
            println!("  Files analyzed: {}", report.project_summary.total_files);
            println!("  Functions: {}", report.project_summary.total_functions);
            println!("  Classes: {}", report.project_summary.total_classes);
            println!();
            println!("  Lines of Code:");
            println!(
                "    Physical: {}",
                report.project_summary.total_loc.physical
            );
            println!(
                "    Source (SLOC): {}",
                report.project_summary.total_loc.source
            );
            println!("    Logical: {}", report.project_summary.total_loc.logical);
            println!("    Comment: {}", report.project_summary.total_loc.comment);
            println!();
            println!("  Averages:");
            println!(
                "    Cyclomatic complexity: {:.2}",
                report.project_summary.avg_cyclomatic
            );
            println!(
                "    Cognitive complexity: {:.2}",
                report.project_summary.avg_cognitive
            );
            println!(
                "    Maintainability Index: {:.2}",
                report.project_summary.avg_maintainability
            );
            println!(
                "    Nesting depth: {:.2}",
                report.project_summary.avg_nesting
            );
            println!(
                "    Function size (SLOC): {:.2}",
                report.project_summary.avg_function_size
            );
            println!();
            println!("  Halstead Estimates:");
            println!(
                "    Estimated bugs: {:.2}",
                report.project_summary.total_estimated_bugs
            );
            println!(
                "    Estimated hours: {:.1}",
                report.project_summary.total_estimated_hours
            );
            println!();
            println!("  Quality Indicators:");
            println!(
                "    Files with critical issues: {}",
                report.project_summary.files_with_critical_issues
            );
            println!(
                "    Complex functions: {}",
                report.project_summary.complex_functions
            );
            println!(
                "    Low cohesion classes: {}",
                report.project_summary.low_cohesion_classes
            );
            println!();

            // Issue Summary
            println!("ISSUE SUMMARY");
            println!("-------------");
            println!("  Total issues: {}", report.issue_stats.total);
            println!("  \x1b[36mInfo: {}\x1b[0m", report.issue_stats.info);
            println!("  \x1b[33mWarnings: {}\x1b[0m", report.issue_stats.warnings);
            println!("  \x1b[31mCritical: {}\x1b[0m", report.issue_stats.critical);
            println!();

            if !report.issue_stats.by_category.is_empty() {
                println!("  By category:");
                let mut categories: Vec<_> = report.issue_stats.by_category.iter().collect();
                categories.sort_by(|a, b| b.1.cmp(a.1));
                for (category, count) in categories {
                    println!("    {}: {}", category, count);
                }
                println!();
            }

            // Top Issues
            if !report.issues.is_empty() {
                let critical_issues: Vec<_> = report
                    .issues
                    .iter()
                    .filter(|i| i.severity == IssueSeverity::Critical)
                    .take(10)
                    .collect();

                if !critical_issues.is_empty() {
                    println!("TOP CRITICAL ISSUES");
                    println!("-------------------");
                    for issue in critical_issues {
                        println!(
                            "  \x1b[31m[CRITICAL]\x1b[0m {} - {}:{}",
                            issue.message,
                            issue.file.display(),
                            issue.line.map(|l| l.to_string()).unwrap_or_default()
                        );
                        if let Some(ref suggestion) = issue.suggestion {
                            println!("    Suggestion: {}", suggestion);
                        }
                    }
                    println!();
                }
            }

            // Top Functions
            if !functions_to_show.is_empty() {
                let header = if issues_only {
                    "FUNCTIONS WITH ISSUES"
                } else {
                    "FUNCTION METRICS"
                };
                println!("{} (showing {})", header, functions_to_show.len());
                println!("{}", "-".repeat(header.len() + 15));

                for func in &functions_to_show {
                    // Color code based on risk
                    let color = match func.cyclomatic_risk {
                        metrics::RiskLevel::Critical => "\x1b[35m",
                        metrics::RiskLevel::High => "\x1b[31m",
                        metrics::RiskLevel::Medium => "\x1b[33m",
                        metrics::RiskLevel::Low => "\x1b[32m",
                    };

                    println!(
                        "  {}{}\x1b[0m - {}:{}",
                        color,
                        func.name,
                        func.file.display(),
                        func.line
                    );
                    println!(
                        "    CC={} Cog={} MI={:.1} LOC={} Nest={} Params={}",
                        func.cyclomatic,
                        func.cognitive,
                        func.maintainability,
                        func.loc,
                        func.nesting,
                        func.params
                    );

                    if !func.size_issues.is_empty() {
                        for issue in &func.size_issues {
                            println!("    Issue: {}", issue);
                        }
                    }
                }
                println!();
            }

            // Class Cohesion (if analyzed)
            if !report.class_metrics.is_empty() {
                let low_cohesion: Vec<_> = report
                    .class_metrics
                    .iter()
                    .filter(|c| c.is_low_cohesion)
                    .take(10)
                    .collect();

                if !low_cohesion.is_empty() {
                    println!("CLASSES WITH LOW COHESION");
                    println!("-------------------------");
                    for class in low_cohesion {
                        println!(
                            "  {}: LCOM3={} LCOM4={} methods={} - {}:{}",
                            class.name,
                            class.lcom3,
                            class.lcom4,
                            class.method_count,
                            class.file.display(),
                            class.line
                        );
                        if let Some(ref suggestion) = class.suggestion {
                            println!("    {}", suggestion);
                        }
                    }
                    println!();
                }
            }

            println!(
                "================================================================================"
            );
        }
        OutputFormat::Csv => {
            // CSV output - function metrics by default
            // Output format selection based on what data is most useful:
            // --issues-only outputs issues CSV, otherwise function metrics
            if issues_only && !report.issues.is_empty() {
                print!("{}", metrics::format_issues_csv(&report.issues));
            } else {
                print!("{}", metrics::format_functions_csv(&functions_to_show));
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot => {
            // Not applicable for metrics report - output JSON
            let output = serde_json::to_value(&report).context("Failed to serialize report")?;
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Check quality gate if --fail-on is specified
    let exit_code = if let Some(fail_level) = fail_on {
        let gate = match fail_level.to_lowercase().as_str() {
            "warning" | "warnings" => QualityGate {
                fail_on_critical: true,
                max_critical_issues: 0,
                max_warning_issues: 0,
                min_maintainability: None,
                max_avg_cyclomatic: None,
            },
            "critical" => QualityGate::default(),
            _ => {
                eprintln!(
                    "Unknown fail-on level: {}. Use 'warning' or 'critical'",
                    fail_level
                );
                QualityGate::default()
            }
        };

        let result = gate.check(&report);
        if result.failed {
            eprintln!();
            eprintln!("QUALITY GATE FAILED");
            eprintln!("-------------------");
            for reason in &result.reasons {
                eprintln!("  - {}", reason);
            }
            1
        } else {
            eprintln!();
            eprintln!("Quality gate passed.");
            0
        }
    } else {
        0
    };

    Ok(exit_code)
}

// =============================================================================
// DATAFLOW COMMANDS
// =============================================================================

fn cmd_dataflow(subcmd: DataflowCommands) -> Result<()> {
    match subcmd {
        DataflowCommands::LiveVars {
            file,
            function,
            lang,
            format,
            interference,
            dead_stores_only,
        } => {
            cmd_live_vars(
                &file,
                &function,
                lang,
                format,
                interference,
                dead_stores_only,
            )?;
        }
        DataflowCommands::ReachingDefs {
            file,
            function,
            lang,
            format,
            chains,
        } => {
            cmd_reaching_defs(&file, &function, lang, format, chains)?;
        }
        DataflowCommands::Constants {
            file,
            function,
            lang,
            format,
            optimizations_only,
        } => {
            cmd_constants(&file, &function, lang, format, optimizations_only)?;
        }
        DataflowCommands::VeryBusy {
            file,
            function,
            lang,
            format,
            hoisting_only,
        } => {
            cmd_very_busy(&file, &function, lang, format, hoisting_only)?;
        }
        DataflowCommands::AvailableExprs {
            file,
            function,
            lang,
            format,
            cse_only,
        } => {
            cmd_available_exprs(&file, &function, lang, format, cse_only)?;
        }
    }
    Ok(())
}

fn cmd_live_vars(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    show_interference: bool,
    dead_stores_only: bool,
) -> Result<()> {
    use dataflow::live_variables;

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run live variable analysis
    let result =
        live_variables::analyze_file_with_language(file_str, function, lang_str.as_deref())
            .context("Failed to analyze live variables")?;

    // Output based on format and options
    if dead_stores_only {
        // Only show dead stores
        let dead_stores_output = serde_json::json!({
            "function_name": result.function_name,
            "dead_stores": result.dead_stores.iter().map(|ds| {
                serde_json::json!({
                    "variable": ds.variable,
                    "line": ds.location.line,
                    "reason": format!("{:?}", ds.reason),
                    "severity": format!("{:?}", ds.severity),
                    "suggestion": ds.suggestion,
                })
            }).collect::<Vec<_>>(),
            "unused_parameters": result.unused_parameters,
            "summary": {
                "dead_store_count": result.metrics.dead_store_count,
                "unused_param_count": result.metrics.unused_param_count,
            }
        });

        match format {
            OutputFormat::Text => {
                println!("Dead Stores in {}:", result.function_name);
                if result.dead_stores.is_empty() && result.unused_parameters.is_empty() {
                    println!("  No dead stores or unused parameters found.");
                } else {
                    for ds in &result.dead_stores {
                        println!(
                            "  Line {}: '{}' - {} [{:?}]",
                            ds.location.line, ds.variable, ds.reason, ds.severity
                        );
                        if let Some(ref suggestion) = ds.suggestion {
                            println!("    Suggestion: {}", suggestion);
                        }
                    }
                    for param in &result.unused_parameters {
                        println!("  Unused parameter: '{}'", param);
                    }
                }
            }
            _ => {
                println!("{}", serde_json::to_string_pretty(&dead_stores_output)?);
            }
        }
    } else if show_interference {
        // Show interference graph
        let interference = live_variables::compute_interference(&result);
        let output = serde_json::json!({
            "function_name": result.function_name,
            "interference": interference.iter().map(|(var, interferes)| {
                (var.clone(), interferes.iter().cloned().collect::<Vec<_>>())
            }).collect::<std::collections::HashMap<_, _>>(),
            "variable_count": interference.len(),
        });

        match format {
            OutputFormat::Text => {
                println!("Interference Graph for {}:", result.function_name);
                let mut vars: Vec<_> = interference.keys().collect();
                vars.sort();
                for var in vars {
                    if let Some(interferes) = interference.get(var) {
                        let mut ilist: Vec<_> = interferes.iter().collect();
                        ilist.sort();
                        println!("  {} interferes with: {:?}", var, ilist);
                    }
                }
            }
            _ => {
                println!("{}", serde_json::to_string_pretty(&output)?);
            }
        }
    } else {
        // Full output
        match format {
            OutputFormat::Text => {
                println!("{}", result.to_text());
            }
            _ => {
                println!("{}", serde_json::to_string_pretty(&result.to_json())?);
            }
        }
    }

    Ok(())
}

fn cmd_reaching_defs(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    show_chains: bool,
) -> Result<()> {
    use dataflow::reaching_definitions;

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run reaching definitions analysis
    let result = reaching_definitions::analyze_reaching_definitions_with_language(
        file_str,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to analyze reaching definitions")?;

    // Output based on format
    match format {
        OutputFormat::Text => {
            println!("Reaching Definitions Analysis: {}", result.function_name);
            println!("{}", "=".repeat(50));

            println!("\nDefinitions:");
            for def in &result.definitions {
                println!(
                    "  D{}: {} at line {} ({:?})",
                    def.def_id.0, def.variable, def.location.line, def.kind
                );
            }

            if show_chains {
                println!("\nDef-Use Chains:");
                for chain in &result.def_use_chains {
                    println!("  D{} -> lines {:?}", chain.definition.0, chain.uses);
                }
            }

            if !result.issues.is_empty() {
                println!("\nIssues:");
                for issue in &result.issues {
                    println!(
                        "  Line {}: {:?} - {}",
                        issue.location.line, issue.kind, issue.message
                    );
                }
            }

            println!(
                "\nMetrics: {} definitions, {} def-use chains, {} issues",
                result.definitions.len(),
                result.def_use_chains.len(),
                result.issues.len()
            );
        }
        _ => {
            let output = serde_json::json!({
                "function_name": result.function_name,
                "definitions": result.definitions.iter().map(|d| {
                    serde_json::json!({
                        "id": d.def_id.0,
                        "variable": d.variable,
                        "line": d.location.line,
                        "kind": format!("{:?}", d.kind),
                    })
                }).collect::<Vec<_>>(),
                "def_use_chains": if show_chains {
                    Some(result.def_use_chains.iter().map(|c| {
                        serde_json::json!({
                            "definition": c.definition.0,
                            "uses": c.uses,
                        })
                    }).collect::<Vec<_>>())
                } else {
                    None
                },
                "issues": result.issues.iter().map(|i| {
                    serde_json::json!({
                        "line": i.location.line,
                        "kind": format!("{:?}", i.kind),
                        "message": i.message,
                    })
                }).collect::<Vec<_>>(),
                "summary": {
                    "definition_count": result.definitions.len(),
                    "chain_count": result.def_use_chains.len(),
                    "issue_count": result.issues.len(),
                }
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

fn cmd_constants(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    optimizations_only: bool,
) -> Result<()> {
    use dataflow::constant_propagation;

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run constant propagation analysis
    let result = constant_propagation::analyze_constants_with_language(
        file_str,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to analyze constant propagation")?;

    // Output based on format
    match format {
        OutputFormat::Text => {
            println!("Constant Propagation Analysis: {}", result.function_name);
            println!("{}", "=".repeat(50));

            if !optimizations_only {
                println!("\nConstants at program points:");
                let mut points: Vec<_> = result.constants_at_point.iter().collect();
                points.sort_by_key(|(k, _)| *k);
                for ((block_id, stmt_idx), constants) in points {
                    if !constants.is_empty() {
                        let constants_str: Vec<_> = constants
                            .iter()
                            .map(|(var, val)| format!("{} = {}", var, val))
                            .collect();
                        println!(
                            "  Block {} stmt {}: {}",
                            block_id,
                            stmt_idx,
                            constants_str.join(", ")
                        );
                    }
                }
            }

            if !result.folded_expressions.is_empty() {
                println!("\nConstant Folding Opportunities:");
                for folded in &result.folded_expressions {
                    println!(
                        "  Line {}: {} can be folded to {}",
                        folded.location.line, folded.original, folded.folded_value
                    );
                }
            }

            if !result.dead_branches.is_empty() {
                println!("\nDead Branches:");
                for dead in &result.dead_branches {
                    println!(
                        "  Line {}: {} is always {}",
                        dead.location.line, dead.condition, dead.always_value
                    );
                    if !dead.unreachable_lines.is_empty() {
                        println!("    Unreachable lines: {:?}", dead.unreachable_lines);
                    }
                }
            }

            println!(
                "\nSummary: {} iterations, {} folding opportunities, {} dead branches",
                result.iterations,
                result.folded_expressions.len(),
                result.dead_branches.len()
            );
        }
        _ => {
            let output = if optimizations_only {
                serde_json::json!({
                    "function_name": result.function_name,
                    "folded_expressions": result.folded_expressions.iter().map(|f| {
                        serde_json::json!({
                            "line": f.location.line,
                            "original": f.original,
                            "folded_value": format!("{}", f.folded_value),
                        })
                    }).collect::<Vec<_>>(),
                    "dead_branches": result.dead_branches.iter().map(|d| {
                        serde_json::json!({
                            "line": d.location.line,
                            "condition": d.condition,
                            "always_value": d.always_value,
                            "unreachable_lines": d.unreachable_lines,
                        })
                    }).collect::<Vec<_>>(),
                    "summary": {
                        "iterations": result.iterations,
                        "converged": result.converged,
                        "folding_opportunities": result.folded_expressions.len(),
                        "dead_branches": result.dead_branches.len(),
                    }
                })
            } else {
                serde_json::json!({
                    "function_name": result.function_name,
                    "constants_at_point": result.constants_at_point.iter().map(|((block, stmt), constants)| {
                        serde_json::json!({
                            "block_id": block,
                            "stmt_index": stmt,
                            "constants": constants.iter().map(|(var, val)| {
                                serde_json::json!({
                                    "variable": var,
                                    "value": format!("{}", val),
                                })
                            }).collect::<Vec<_>>(),
                        })
                    }).collect::<Vec<_>>(),
                    "folded_expressions": result.folded_expressions.iter().map(|f| {
                        serde_json::json!({
                            "line": f.location.line,
                            "original": f.original,
                            "folded_value": format!("{}", f.folded_value),
                        })
                    }).collect::<Vec<_>>(),
                    "dead_branches": result.dead_branches.iter().map(|d| {
                        serde_json::json!({
                            "line": d.location.line,
                            "condition": d.condition,
                            "always_value": d.always_value,
                            "unreachable_lines": d.unreachable_lines,
                        })
                    }).collect::<Vec<_>>(),
                    "summary": {
                        "iterations": result.iterations,
                        "converged": result.converged,
                        "folding_opportunities": result.folded_expressions.len(),
                        "dead_branches": result.dead_branches.len(),
                    }
                })
            };
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

fn cmd_very_busy(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    hoisting_only: bool,
) -> Result<()> {
    use dataflow::very_busy_expressions;

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run very busy expressions analysis
    let result = very_busy_expressions::analyze_very_busy_expressions_with_language(
        file_str,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to analyze very busy expressions")?;

    // Output based on format
    match format {
        OutputFormat::Text => {
            if hoisting_only {
                println!("Hoisting Opportunities: {}", result.function_name);
                println!("{}", "=".repeat(50));

                if result.hoisting_opportunities.is_empty() {
                    println!("\nNo hoisting opportunities detected.");
                } else {
                    for opp in &result.hoisting_opportunities {
                        let current_lines: Vec<_> =
                            opp.current_locations.iter().map(|l| l.line).collect();
                        println!("\n  Expression: {}", opp.expression.to_string_repr());
                        println!("  Current locations: lines {:?}", current_lines);
                        println!("  Can hoist to: line {}", opp.hoist_to.line);
                        println!("  Benefit: {}", opp.benefit);
                        println!("  Occurrences saved: {}", opp.occurrences_saved);
                        for note in &opp.safety_notes {
                            println!("  Note: {}", note);
                        }
                    }
                }
                println!(
                    "\nSummary: {} hoisting opportunities found",
                    result.hoisting_opportunities.len()
                );
            } else {
                println!("{}", result.to_text());
            }
        }
        _ => {
            let output = if hoisting_only {
                serde_json::json!({
                    "function_name": result.function_name,
                    "hoisting_opportunities": result.hoisting_opportunities.iter().map(|opp| {
                        serde_json::json!({
                            "expression": opp.expression.to_string_repr(),
                            "current_locations": opp.current_locations.iter().map(|loc| {
                                serde_json::json!({
                                    "line": loc.line,
                                    "block": loc.block_id.0,
                                })
                            }).collect::<Vec<_>>(),
                            "hoist_to": {
                                "line": opp.hoist_to.line,
                                "block": opp.hoist_to.block_id.0,
                            },
                            "benefit": opp.benefit.to_string(),
                            "occurrences_saved": opp.occurrences_saved,
                            "safety_notes": opp.safety_notes,
                        })
                    }).collect::<Vec<_>>(),
                    "summary": {
                        "hoisting_count": result.hoisting_opportunities.len(),
                    }
                })
            } else {
                result.to_json()
            };
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

fn cmd_available_exprs(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    cse_only: bool,
) -> Result<()> {
    use dataflow::available_expressions;

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run available expressions analysis
    let result = available_expressions::analyze_available_expressions_with_language(
        file_str,
        function,
        lang_str.as_deref(),
    )
    .context("Failed to analyze available expressions")?;

    // Output based on format
    match format {
        OutputFormat::Text => {
            if cse_only {
                println!("CSE Opportunities: {}", result.function_name);
                println!("{}", "=".repeat(50));

                if result.cse_opportunities.is_empty() {
                    println!("\nNo CSE opportunities detected.");
                } else {
                    for cse in &result.cse_opportunities {
                        println!("\n  Expression: {}", cse.expression.text);
                        println!("    First computed at line {}", cse.first_computation.line);
                        for redundant in &cse.redundant_computations {
                            println!("    Redundant at line {} (can reuse)", redundant.line);
                        }
                        println!("    Suggested temp: {}", cse.suggested_temp_name);
                        println!(
                            "    Estimated savings: {} computation(s)",
                            cse.estimated_savings
                        );
                        let safety = if cse.is_safe { "safe" } else { "unsafe" };
                        println!("    Safety: {}", safety);
                    }
                }

                // Also show loop invariants
                if !result.loop_invariants.is_empty() {
                    println!("\nLoop Invariants (can be hoisted):");
                    for inv in &result.loop_invariants {
                        let safety = if inv.is_safe_to_hoist {
                            "safe"
                        } else {
                            "unsafe"
                        };
                        println!(
                            "  {} at loop {} ({})",
                            inv.expression.text, inv.loop_header.0, safety
                        );
                    }
                }

                println!(
                    "\nSummary: {} CSE opportunities, {} loop invariants",
                    result.cse_opportunities.len(),
                    result.loop_invariants.len()
                );
            } else {
                println!("{}", result.to_text());
            }
        }
        _ => {
            let output = if cse_only {
                serde_json::json!({
                    "function_name": result.function_name,
                    "cse_opportunities": result.cse_opportunities.iter().map(|cse| {
                        serde_json::json!({
                            "expression": cse.expression.text,
                            "first_computation": {
                                "line": cse.first_computation.line,
                                "block": cse.first_computation.block_id.0,
                            },
                            "redundant_computations": cse.redundant_computations.iter().map(|loc| {
                                serde_json::json!({
                                    "line": loc.line,
                                    "block": loc.block_id.0,
                                })
                            }).collect::<Vec<_>>(),
                            "suggested_temp_name": cse.suggested_temp_name,
                            "estimated_savings": cse.estimated_savings,
                            "is_safe": cse.is_safe,
                        })
                    }).collect::<Vec<_>>(),
                    "loop_invariants": result.loop_invariants.iter().map(|inv| {
                        serde_json::json!({
                            "expression": inv.expression.text,
                            "loop_header": inv.loop_header.0,
                            "is_safe_to_hoist": inv.is_safe_to_hoist,
                        })
                    }).collect::<Vec<_>>(),
                    "summary": {
                        "cse_count": result.cse_opportunities.len(),
                        "loop_invariant_count": result.loop_invariants.len(),
                        "estimated_savings": result.metrics.estimated_savings,
                    }
                })
            } else {
                result.to_json()
            };
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// =============================================================================
// QUALITY COMMANDS
// =============================================================================

mod patterns;
// Import quality from the library crate (brrr) rather than including it as a bin module.
// This avoids duplicate compilation and ensures crate:: references in quality files
// resolve correctly to the library crate's modules (embedding, semantic, etc.).
use brrr::quality;

fn cmd_quality(subcmd: QualityCommands) -> Result<()> {
    match subcmd {
        QualityCommands::Clones {
            path,
            min_lines,
            lang,
            format,
            include_licenses,
            include_tests,
            include_generated,
            max_file_size,
        } => {
            cmd_clones(
                &path,
                min_lines,
                lang,
                format,
                include_licenses,
                include_tests,
                include_generated,
                max_file_size,
            )?;
        }
        QualityCommands::StructuralClones {
            path,
            similarity,
            min_nodes,
            min_lines,
            lang,
            format,
            type2_only,
            type3_only,
            include_tests,
            include_accessors,
            include_interface_impls,
            show_filtered,
            max_file_size,
            max_comparisons,
        } => {
            cmd_structural_clones(
                &path,
                similarity,
                min_nodes,
                min_lines,
                lang,
                format,
                type2_only,
                type3_only,
                include_tests,
                include_accessors,
                include_interface_impls,
                show_filtered,
                max_file_size,
                max_comparisons,
            )?;
        }
        QualityCommands::GodClass {
            path,
            lang,
            format,
            threshold,
            method_threshold,
            attribute_threshold,
            line_threshold,
            lcom_threshold,
            include_tests,
            exclude_framework,
            include_generated,
            max_file_size,
            min_severity,
        } => {
            cmd_god_class(
                &path,
                lang,
                format,
                threshold,
                method_threshold,
                attribute_threshold,
                line_threshold,
                lcom_threshold,
                include_tests,
                exclude_framework,
                include_generated,
                max_file_size,
                &min_severity,
            )?;
        }
        QualityCommands::LongMethod {
            path,
            lang,
            format,
            max_lines,
            max_statements,
            max_variables,
            max_complexity,
            max_nesting,
            max_parameters,
            strict,
            lenient,
            no_context,
            show_suggestions,
            min_severity,
            sort,
        } => {
            cmd_long_method(
                &path,
                lang,
                format,
                max_lines,
                max_statements,
                max_variables,
                max_complexity,
                max_nesting,
                max_parameters,
                strict,
                lenient,
                no_context,
                show_suggestions,
                &min_severity,
                sort,
            )?;
        }
        QualityCommands::Circular {
            path,
            level,
            lang,
            format,
            min_severity,
            include_tests,
            exclude_intentional,
            max_cycles,
            max_suggestions,
        } => {
            cmd_circular(
                &path,
                level,
                lang,
                format,
                &min_severity,
                include_tests,
                exclude_intentional,
                max_cycles,
                max_suggestions,
            )?;
        }
        QualityCommands::Patterns {
            path,
            pattern,
            lang,
            format,
            min_confidence,
            include_tests,
            include_generated,
            no_modern,
            max_file_size,
        } => {
            cmd_patterns(
                &path,
                pattern.as_deref(),
                lang,
                format,
                min_confidence,
                include_tests,
                include_generated,
                no_modern,
                max_file_size,
            )?;
        }
        QualityCommands::TestQuality {
            path,
            lang,
            format,
            strict,
            lenient,
            min_density,
            flag_single_assertion,
            analyze_mocks,
            check_boundaries,
            estimate_mutations,
            weak_only,
            min_grade,
        } => {
            cmd_test_quality(
                &path,
                lang,
                format,
                strict,
                lenient,
                min_density,
                flag_single_assertion,
                analyze_mocks,
                check_boundaries,
                estimate_mutations,
                weak_only,
                min_grade,
            )?;
        }
        QualityCommands::DocCoverage {
            path,
            lang,
            format,
            public_only,
            min_quality,
            check_params,
            check_returns,
            check_exceptions,
            check_examples,
            flag_restatement,
            strict,
            lenient,
            min_lines,
        } => {
            cmd_doc_coverage(
                &path,
                lang,
                format,
                public_only,
                min_quality,
                check_params,
                check_returns,
                check_exceptions,
                check_examples,
                flag_restatement,
                strict,
                lenient,
                min_lines,
            )?;
        }
        QualityCommands::SemanticClones {
            path,
            threshold,
            min_lines,
            cross_file_only,
            include_tests,
            format,
            suggest_refactor,
            max_results,
            lang,
            tei_url,
        } => {
            cmd_semantic_clones(
                &path,
                threshold,
                min_lines,
                cross_file_only,
                include_tests,
                format,
                suggest_refactor,
                max_results,
                lang,
                &tei_url,
            )?;
        }
        QualityCommands::SimilarTo {
            location,
            k,
            path,
            threshold,
            format,
            lang,
            tei_url,
        } => {
            cmd_similar_to(&location, k, &path, threshold, format, lang, &tei_url)?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_test_quality(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    strict: bool,
    lenient: bool,
    min_density: f64,
    flag_single_assertion: bool,
    analyze_mocks: bool,
    check_boundaries: bool,
    estimate_mutations: bool,
    weak_only: bool,
    min_grade: Option<char>,
) -> Result<()> {
    use quality::test_quality::{
        analyze_test_quality, format_test_quality_report, TestQualityConfig,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration based on preset or custom values
    let config = if strict {
        TestQualityConfig::strict()
    } else if lenient {
        TestQualityConfig::lenient()
    } else {
        TestQualityConfig {
            min_assertion_density: min_density,
            flag_single_assertion,
            analyze_mocks,
            check_boundary_testing: check_boundaries,
            estimate_mutation_score: estimate_mutations,
            ..Default::default()
        }
    };

    // Parse language
    let language = lang.map(|l| l.to_string());

    // Run analysis
    let result = analyze_test_quality(path, language.as_deref(), Some(config))
        .map_err(|e| anyhow::anyhow!("Test quality analysis failed: {}", e))?;

    // Filter to weak tests only if requested
    let display_result = if weak_only {
        let mut filtered = result.clone();
        filtered.files = filtered
            .files
            .into_iter()
            .map(|mut f| {
                f.test_functions = f
                    .test_functions
                    .into_iter()
                    .filter(|t| t.grade == 'D' || t.grade == 'F' || !t.issues.is_empty())
                    .collect();
                f
            })
            .filter(|f| !f.test_functions.is_empty())
            .collect();
        filtered
    } else {
        result.clone()
    };

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&display_result)
                    .map_err(|e| anyhow::anyhow!("JSON serialization failed: {}", e))?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_test_quality_report(&display_result));
        }
        _ => {
            // For other formats (Mermaid, Dot, Csv), default to JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&display_result)
                    .map_err(|e| anyhow::anyhow!("JSON serialization failed: {}", e))?
            );
        }
    }

    // Check if minimum grade requirement is met
    if let Some(min) = min_grade {
        let grade_value = |g: char| match g {
            'A' => 4,
            'B' => 3,
            'C' => 2,
            'D' => 1,
            _ => 0,
        };
        let required = grade_value(min);
        let actual = grade_value(result.summary.overall_grade);

        if actual < required {
            eprintln!(
                "\x1b[31mTest quality grade {} does not meet minimum requirement {}\x1b[0m",
                result.summary.overall_grade, min
            );
            std::process::exit(1);
        }
    }

    // Print summary to stderr
    if matches!(format, OutputFormat::Json | OutputFormat::Jsonl) {
        eprintln!(
            "\x1b[32mAnalyzed {} test files, {} tests total\x1b[0m",
            result.summary.files_analyzed, result.summary.total_tests
        );
        eprintln!(
            "Overall grade: \x1b[{}m{}\x1b[0m",
            match result.summary.overall_grade {
                'A' => "32",
                'B' => "32",
                'C' => "33",
                'D' => "31",
                _ => "31",
            },
            result.summary.overall_grade
        );
        if result.summary.weak_test_count > 0 {
            eprintln!(
                "\x1b[33mWeak tests: {} ({:.1}%)\x1b[0m",
                result.summary.weak_test_count,
                if result.summary.total_tests > 0 {
                    f64::from(result.summary.weak_test_count)
                        / f64::from(result.summary.total_tests)
                        * 100.0
                } else {
                    0.0
                }
            );
        }
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_doc_coverage(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    public_only: bool,
    min_quality: u8,
    check_params: bool,
    check_returns: bool,
    check_exceptions: bool,
    check_examples: bool,
    flag_restatement: bool,
    strict: bool,
    lenient: bool,
    min_lines: u32,
) -> Result<()> {
    use quality::doc_coverage::{
        analyze_doc_coverage, format_doc_coverage_report, DocCoverageConfig,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration based on preset or custom values
    let config = if strict {
        DocCoverageConfig::strict()
    } else if lenient {
        DocCoverageConfig::lenient()
    } else {
        DocCoverageConfig {
            public_only,
            min_quality_score: min_quality,
            check_params,
            check_returns,
            check_exceptions,
            check_examples,
            flag_name_restatement: flag_restatement,
            min_lines_require_doc: min_lines,
            ..Default::default()
        }
    };

    // Parse language
    let language = lang.map(|l| l.to_string());

    // Run analysis
    let result = analyze_doc_coverage(path, language.as_deref(), Some(config))
        .map_err(|e| anyhow::anyhow!("Documentation coverage analysis failed: {}", e))?;

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result)
                    .map_err(|e| anyhow::anyhow!("JSON serialization failed: {}", e))?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_doc_coverage_report(&result));
        }
        _ => {
            // For other formats (Mermaid, Dot, Csv), default to JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result)
                    .map_err(|e| anyhow::anyhow!("JSON serialization failed: {}", e))?
            );
        }
    }

    // Print summary to stderr for JSON output
    if matches!(format, OutputFormat::Json | OutputFormat::Jsonl) {
        eprintln!(
            "\x1b[32mAnalyzed {} files, {} items\x1b[0m",
            result.metrics.files_analyzed, result.metrics.total_items
        );
        let coverage_pct = result.metrics.coverage_rate * 100.0;
        let coverage_color = if coverage_pct >= 80.0 {
            "32" // green
        } else if coverage_pct >= 50.0 {
            "33" // yellow
        } else {
            "31" // red
        };
        eprintln!(
            "Coverage: \x1b[{}m{:.1}%\x1b[0m ({}/{} documented)",
            coverage_color,
            coverage_pct,
            result.metrics.documented_items,
            result.metrics.total_items
        );
        eprintln!(
            "Quality Score: \x1b[{}m{:.1}/5\x1b[0m",
            if result.metrics.quality_score >= 3.0 {
                "32"
            } else if result.metrics.quality_score >= 2.0 {
                "33"
            } else {
                "31"
            },
            result.metrics.quality_score
        );
        if !result.missing_docs.is_empty() {
            eprintln!(
                "\x1b[33mMissing docs: {} items\x1b[0m",
                result.missing_docs.len()
            );
        }
    }

    Ok(())
}

fn cmd_clones(
    path: &PathBuf,
    min_lines: usize,
    lang: Option<Language>,
    format: OutputFormat,
    include_licenses: bool,
    include_tests: bool,
    include_generated: bool,
    max_file_size: u64,
) -> Result<()> {
    use quality::clones::{format_clone_summary, CloneConfig, TextualCloneDetector};

    // Validate path exists
    require_exists(path)?;

    // Build configuration
    let mut config = CloneConfig::default();
    config.min_lines = min_lines;
    config.max_file_size = max_file_size;
    config.exclude_license_headers = !include_licenses;
    config.exclude_test_fixtures = !include_tests;
    config.exclude_generated = !include_generated;

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Run detection
    let detector = TextualCloneDetector::new(config);
    let result = detector
        .detect(path)
        .map_err(|e| anyhow::anyhow!("Clone detection failed: {}", e))?;

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_clone_summary(&result));
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for clone detection - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary warning if there are clones
    if result.stats.clone_groups > 0 {
        eprintln!();
        eprintln!(
            "Detected {} clone group(s) with {} duplicated lines ({:.1}% duplication)",
            result.stats.clone_groups,
            result.stats.duplicated_lines,
            result.stats.duplication_percentage
        );
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_structural_clones(
    path: &PathBuf,
    similarity: f64,
    min_nodes: usize,
    min_lines: usize,
    lang: Option<Language>,
    format: OutputFormat,
    type2_only: bool,
    type3_only: bool,
    include_tests: bool,
    include_accessors: bool,
    include_interface_impls: bool,
    show_filtered: bool,
    max_file_size: u64,
    max_comparisons: usize,
) -> Result<()> {
    use quality::clones::{
        format_structural_clone_summary, StructuralCloneConfig, StructuralCloneDetector,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration
    let mut config = StructuralCloneConfig::default();
    config.similarity_threshold = similarity.clamp(0.0, 1.0);
    config.min_nodes = min_nodes;
    config.min_lines = min_lines;
    config.max_file_size = max_file_size;
    config.max_comparisons = max_comparisons;
    config.filter_tests = !include_tests;
    config.filter_accessors = !include_accessors;
    config.filter_interface_impls = !include_interface_impls;

    // Handle type-only flags
    if type2_only && type3_only {
        // Both specified - enable both (user probably made a mistake)
        config.detect_type2 = true;
        config.detect_type3 = true;
    } else if type2_only {
        config.detect_type2 = true;
        config.detect_type3 = false;
    } else if type3_only {
        config.detect_type2 = false;
        config.detect_type3 = true;
    }

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Run detection
    let detector = StructuralCloneDetector::new(config);
    let mut result = detector
        .detect(path)
        .map_err(|e| anyhow::anyhow!("Structural clone detection failed: {}", e))?;

    // Filter out filtered groups unless --show-filtered
    if !show_filtered {
        result.clone_groups.retain(|c| !c.filtered);
    }

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_structural_clone_summary(&result));
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for clone detection - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary
    let total_groups = result.stats.type2_groups + result.stats.type3_groups;
    if total_groups > 0 {
        eprintln!();
        eprintln!(
            "Detected {} structural clone group(s): {} Type-2, {} Type-3",
            total_groups, result.stats.type2_groups, result.stats.type3_groups
        );
        eprintln!(
            "  {} duplicated AST nodes across {} instances",
            result.stats.duplicated_nodes, result.stats.clone_instances
        );
        if result.stats.filtered_groups > 0 && !show_filtered {
            eprintln!(
                "  ({} potential false positive groups filtered, use --show-filtered to see them)",
                result.stats.filtered_groups
            );
        }
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_semantic_clones(
    path: &PathBuf,
    threshold: f32,
    min_lines: usize,
    cross_file_only: bool,
    include_tests: bool,
    format: OutputFormat,
    suggest_refactor: bool,
    max_results: usize,
    lang: Option<Language>,
    tei_url: &str,
) -> Result<()> {
    use indicatif::{ProgressBar, ProgressStyle};
    use quality::clones::{
        detect_semantic_clones, format_semantic_clone_summary, SemanticCloneConfig,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration
    let mut config = SemanticCloneConfig::default();
    config.low_similarity_threshold = threshold;
    config.min_lines = min_lines;
    config.cross_file_only = cross_file_only;
    config.ignore_tests = !include_tests;
    config.tei_url = tei_url.to_string();

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Create progress spinner
    let spinner = ProgressBar::new_spinner();
    spinner.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.cyan} {msg} [{elapsed_precise}]")
            .expect("Invalid spinner template")
            .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"),
    );
    spinner.set_message("Detecting semantic clones...");
    spinner.enable_steady_tick(std::time::Duration::from_millis(100));

    // Run detection
    let result = detect_semantic_clones(path, Some(config))
        .map_err(|e| anyhow::anyhow!("Semantic clone detection failed: {}", e))?;

    spinner.finish_with_message(format!(
        "Found {} clone pairs in {}ms",
        result.stats.pairs_found, result.stats.processing_time_ms
    ));

    // Limit results if needed
    let pairs_to_show: Vec<_> = result
        .clone_pairs
        .iter()
        .take(max_results)
        .cloned()
        .collect();

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            // Create output with limited pairs
            let output = serde_json::json!({
                "project_path": result.project_path,
                "clone_pairs": pairs_to_show,
                "clusters": result.clusters,
                "stats": result.stats,
                "config": {
                    "threshold": threshold,
                    "min_lines": min_lines,
                    "cross_file_only": cross_file_only,
                    "include_tests": include_tests,
                },
                "suggest_refactor": suggest_refactor,
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            // Human-readable summary
            println!("{}", format_semantic_clone_summary(&result));

            if suggest_refactor && !result.clone_pairs.is_empty() {
                println!("\n=== Refactoring Suggestions ===\n");
                for (i, pair) in result.pairs_by_similarity().iter().take(10).enumerate() {
                    let suggestion = match pair.clone_type {
                        quality::clones::SemanticCloneType::Identical => {
                            format!(
                                "Delete one of '{}' or '{}' and redirect callers to the other",
                                pair.name_a, pair.name_b
                            )
                        }
                        quality::clones::SemanticCloneType::HighSimilarity => {
                            format!(
                                "Extract common logic from '{}' and '{}' into a shared function",
                                pair.name_a, pair.name_b
                            )
                        }
                        quality::clones::SemanticCloneType::MediumSimilarity => {
                            format!(
                                "Review '{}' and '{}' for potential abstraction opportunities",
                                pair.name_a, pair.name_b
                            )
                        }
                        quality::clones::SemanticCloneType::LowSimilarity => {
                            format!(
                                "'{}' and '{}' share some patterns - consider if consolidation is appropriate",
                                pair.name_a, pair.name_b
                            )
                        }
                    };
                    println!(
                        "{}. [{:.1}%] {}\n   {}:{} <-> {}:{}",
                        i + 1,
                        pair.similarity * 100.0,
                        suggestion,
                        pair.file_a,
                        pair.line_a,
                        pair.file_b,
                        pair.line_b
                    );
                }
            }
        }
        OutputFormat::Dot => {
            // DOT graph format for visualization
            println!("digraph SemanticClones {{");
            println!("  rankdir=LR;");
            println!("  node [shape=box, style=filled];");
            println!();

            // Collect unique nodes
            let mut nodes: std::collections::HashSet<String> = std::collections::HashSet::new();
            for pair in &pairs_to_show {
                nodes.insert(pair.unit_a_id.clone());
                nodes.insert(pair.unit_b_id.clone());
            }

            // Output nodes with colors based on kind
            for node in &nodes {
                let label = node.replace("::", "\\n");
                println!("  \"{}\" [label=\"{}\", fillcolor=lightblue];", node, label);
            }

            println!();

            // Output edges with similarity as label
            for pair in &pairs_to_show {
                let color = match pair.clone_type {
                    quality::clones::SemanticCloneType::Identical => "red",
                    quality::clones::SemanticCloneType::HighSimilarity => "orange",
                    quality::clones::SemanticCloneType::MediumSimilarity => "yellow",
                    quality::clones::SemanticCloneType::LowSimilarity => "gray",
                };
                println!(
                    "  \"{}\" -> \"{}\" [label=\"{:.0}%\", color={}, penwidth=2];",
                    pair.unit_a_id,
                    pair.unit_b_id,
                    pair.similarity * 100.0,
                    color
                );
            }

            println!("}}");
        }
        OutputFormat::Mermaid | OutputFormat::Csv => {
            // Fall back to JSON for unsupported formats
            let output = serde_json::json!({
                "project_path": result.project_path,
                "clone_pairs": pairs_to_show,
                "stats": result.stats,
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    // Print summary to stderr
    if result.stats.pairs_found > 0 {
        eprintln!();
        eprintln!(
            "Detected {} semantic clone pairs:",
            result.stats.pairs_found
        );
        eprintln!(
            "  Identical (>=98%): {}",
            result.stats.identical_count
        );
        eprintln!(
            "  High similarity (>=90%): {}",
            result.stats.high_similarity_count
        );
        eprintln!(
            "  Medium similarity (>=80%): {}",
            result.stats.medium_similarity_count
        );
        eprintln!(
            "  Cross-file clones: {}",
            result.stats.cross_file_count
        );
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_similar_to(
    location: &str,
    k: usize,
    path: &PathBuf,
    threshold: f32,
    format: OutputFormat,
    lang: Option<Language>,
    tei_url: &str,
) -> Result<()> {
    use brrr::embedding::{IndexConfig, Metric, TeiClient, VectorIndex};
    use brrr::semantic::{build_embedding_text, extract_units, EmbeddingUnit};
    use indicatif::{ProgressBar, ProgressStyle};

    // Validate path exists
    require_exists(path)?;

    // Parse location: file:name or file:line
    let (file_path, target) = location
        .rsplit_once(':')
        .ok_or_else(|| anyhow::anyhow!("Invalid location format. Use file:function_name or file:line"))?;

    let file_path = PathBuf::from(file_path);
    if !file_path.exists() {
        anyhow::bail!("File not found: {}", file_path.display());
    }

    // Determine language
    let language = if let Some(l) = lang {
        l.to_string()
    } else {
        detect_project_language(path)
    };

    // Create progress spinner
    let spinner = ProgressBar::new_spinner();
    spinner.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.cyan} {msg} [{elapsed_precise}]")
            .expect("Invalid spinner template")
            .tick_chars("⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"),
    );
    spinner.set_message("Extracting code units...");
    spinner.enable_steady_tick(std::time::Duration::from_millis(100));

    // Extract units from the target file
    let file_units = extract_units(file_path.to_str().unwrap_or("."), &language)
        .map_err(|e| anyhow::anyhow!("Failed to extract units from file: {}", e))?;

    // Find the target unit
    let target_unit: Option<EmbeddingUnit> = if let Ok(line_num) = target.parse::<usize>() {
        // Find unit containing the line
        file_units.into_iter().find(|u| {
            u.start_line <= line_num && u.end_line >= line_num
        })
    } else {
        // Find unit by name (supports Class.method format)
        file_units.into_iter().find(|u| {
            u.name == target || u.id.ends_with(&format!("::{}", target))
        })
    };

    let target_unit = target_unit.ok_or_else(|| {
        anyhow::anyhow!("Could not find unit matching '{}' in {}", target, file_path.display())
    })?;

    spinner.set_message(format!("Found target: {} - extracting all units...", target_unit.name));

    // Extract all units from the search path
    let all_units = extract_units(path.to_str().unwrap_or("."), &language)
        .map_err(|e| anyhow::anyhow!("Failed to extract units: {}", e))?;

    if all_units.is_empty() {
        spinner.finish_with_message("No units found to compare");
        return Ok(());
    }

    spinner.set_message(format!("Generating embeddings for {} units...", all_units.len()));

    // Build embedding texts
    let target_text = build_embedding_text(&target_unit);
    let all_texts: Vec<String> = all_units.iter().map(|u| build_embedding_text(u)).collect();

    // Helper function to generate embeddings via TEI
    async fn generate_embeddings_async(
        tei_url: &str,
        target_text: &str,
        all_texts: &[String],
    ) -> Result<(Vec<f32>, Vec<Vec<f32>>)> {
        let client = TeiClient::new(tei_url).await?;

        // Generate target embedding
        let target_texts: Vec<&str> = vec![target_text];
        let target_embs = client.embed(&target_texts).await
            .map_err(|e| anyhow::anyhow!("Failed to embed target: {}", e))?;

        let target_emb = target_embs.into_iter().next()
            .ok_or_else(|| anyhow::anyhow!("No embedding returned for target"))?;

        // Generate all embeddings in batches
        let text_refs: Vec<&str> = all_texts.iter().map(String::as_str).collect();
        let embeddings = client.embed_batch(&text_refs, Some(64)).await
            .map_err(|e| anyhow::anyhow!("Failed to embed units: {}", e))?;

        Ok((target_emb, embeddings))
    }

    // Helper function to generate placeholder embeddings
    fn generate_placeholder_embeddings(target_idx: usize, num_units: usize) -> (Vec<f32>, Vec<Vec<f32>>) {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let dims = 1024;
        let gen_embedding = |seed: usize| -> Vec<f32> {
            let mut embedding = vec![0.0f32; dims];
            let mut hasher = DefaultHasher::new();
            seed.hash(&mut hasher);
            let base = hasher.finish();

            for (j, val) in embedding.iter_mut().enumerate() {
                let mut h = DefaultHasher::new();
                (base, j).hash(&mut h);
                *val = ((h.finish() as f64 / u64::MAX as f64) * 2.0 - 1.0) as f32;
            }

            let norm: f32 = embedding.iter().map(|x| x * x).sum::<f32>().sqrt();
            if norm > 0.0 {
                for val in &mut embedding {
                    *val /= norm;
                }
            }
            embedding
        };

        let target_emb = gen_embedding(target_idx);
        let embeddings: Vec<Vec<f32>> = (0..num_units).map(gen_embedding).collect();
        (target_emb, embeddings)
    }

    // Use block_in_place to handle nested runtime case
    let tei_url_owned = tei_url.to_string();
    let (target_embedding, all_embeddings): (Vec<f32>, Vec<Vec<f32>>) =
        if let Ok(handle) = tokio::runtime::Handle::try_current() {
            // Already inside a tokio runtime - use block_in_place
            let result: Result<(Vec<f32>, Vec<Vec<f32>>)> = tokio::task::block_in_place(|| {
                handle.block_on(async {
                    generate_embeddings_async(&tei_url_owned, &target_text, &all_texts).await
                })
            });

            match result {
                Ok(embeddings) => embeddings,
                Err(e) => {
                    eprintln!("Warning: Could not connect to TEI server at {}: {}", tei_url, e);
                    eprintln!("Using placeholder embeddings (results will be random)");
                    generate_placeholder_embeddings(0, all_units.len())
                }
            }
        } else {
            // Not in a runtime - create one
            let rt = tokio::runtime::Runtime::new()?;
            let result = rt.block_on(async {
                generate_embeddings_async(&tei_url_owned, &target_text, &all_texts).await
            });

            match result {
                Ok(embeddings) => embeddings,
                Err(e) => {
                    eprintln!("Warning: Could not connect to TEI server at {}: {}", tei_url, e);
                    eprintln!("Using placeholder embeddings (results will be random)");
                    generate_placeholder_embeddings(0, all_units.len())
                }
            }
        };

    spinner.set_message("Computing similarities...");

    // Build vector index and find similar
    let index_config = IndexConfig::new(target_embedding.len())
        .with_metric(Metric::InnerProduct);
    let index = VectorIndex::with_config(index_config)?;

    index.reserve(all_embeddings.len())?;
    for (i, embedding) in all_embeddings.iter().enumerate() {
        index.add(i as u64, embedding)?;
    }

    // Search for similar (k+1 because we might include the target itself)
    let neighbors = index.search(&target_embedding, k + 1)?;

    // Filter and convert results
    let mut results: Vec<(f32, &EmbeddingUnit)> = neighbors
        .into_iter()
        .filter_map(|(id, distance)| {
            let idx = id as usize;
            if idx >= all_units.len() {
                return None;
            }
            // Convert distance to similarity
            let similarity = 1.0 - distance;
            if similarity < threshold {
                return None;
            }
            // Skip if it's the same unit
            if all_units[idx].id == target_unit.id {
                return None;
            }
            Some((similarity, &all_units[idx]))
        })
        .take(k)
        .collect();

    results.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());

    spinner.finish_with_message(format!("Found {} similar units", results.len()));

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            let output = serde_json::json!({
                "query": {
                    "location": location,
                    "unit_id": target_unit.id,
                    "name": target_unit.name,
                    "file": target_unit.file,
                    "start_line": target_unit.start_line,
                    "end_line": target_unit.end_line,
                },
                "results": results.iter().map(|(sim, unit)| {
                    serde_json::json!({
                        "similarity": sim,
                        "unit_id": unit.id,
                        "name": unit.name,
                        "file": unit.file,
                        "start_line": unit.start_line,
                        "end_line": unit.end_line,
                        "kind": format!("{:?}", unit.kind),
                    })
                }).collect::<Vec<_>>(),
                "config": {
                    "k": k,
                    "threshold": threshold,
                    "search_path": path,
                }
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("=== Similar to: {} ===", target_unit.name);
            println!("File: {}:{}-{}", target_unit.file, target_unit.start_line, target_unit.end_line);
            println!();

            if results.is_empty() {
                println!("No similar code found above threshold {:.0}%", threshold * 100.0);
            } else {
                println!("Found {} similar units:\n", results.len());
                for (i, (sim, unit)) in results.iter().enumerate() {
                    println!(
                        "{}. {} ({:.1}% similar)",
                        i + 1,
                        unit.name,
                        sim * 100.0
                    );
                    println!(
                        "   {}:{}-{}",
                        unit.file, unit.start_line, unit.end_line
                    );
                    println!();
                }
            }
        }
        _ => {
            // Fall back to JSON
            let output = serde_json::json!({
                "query": target_unit.id,
                "results": results.iter().map(|(sim, unit)| {
                    serde_json::json!({
                        "similarity": sim,
                        "name": unit.name,
                        "file": unit.file,
                        "line": unit.start_line,
                    })
                }).collect::<Vec<_>>(),
            });
            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_god_class(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    threshold: f64,
    method_threshold: u32,
    attribute_threshold: u32,
    line_threshold: u32,
    lcom_threshold: u32,
    include_tests: bool,
    exclude_framework: bool,
    include_generated: bool,
    max_file_size: u64,
    min_severity: &str,
) -> Result<()> {
    use quality::smells::god_class::{
        detect_with_config, format_god_class_summary, GodClassConfig, GodClassSeverity,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration
    let mut config = GodClassConfig::default();
    config.score_threshold = threshold;
    config.method_threshold = method_threshold;
    config.attribute_threshold = attribute_threshold;
    config.line_threshold = line_threshold;
    config.lcom_threshold = lcom_threshold;
    config.exclude_tests = !include_tests;
    config.exclude_framework = exclude_framework;
    config.exclude_generated = !include_generated;
    config.max_file_size = max_file_size;

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "low" => GodClassSeverity::Low,
        "medium" => GodClassSeverity::Medium,
        "high" => GodClassSeverity::High,
        "critical" => GodClassSeverity::Critical,
        _ => GodClassSeverity::Low,
    };

    // Run detection
    let mut result = detect_with_config(path, config)
        .map_err(|e| anyhow::anyhow!("God class detection failed: {}", e))?;

    // Filter by minimum severity
    result.findings.retain(|f| f.severity >= min_sev);

    // Recalculate stats after filtering
    let filtered_count = result.findings.len();

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_god_class_summary(&result));
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for God class detection - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary
    if filtered_count > 0 {
        eprintln!();
        eprintln!(
            "Detected {} God class(es) with severity >= {}",
            filtered_count, min_severity
        );

        // Count by severity
        let mut critical = 0;
        let mut high = 0;
        let mut medium = 0;
        let mut low = 0;
        for finding in &result.findings {
            match finding.severity {
                GodClassSeverity::Critical => critical += 1,
                GodClassSeverity::High => high += 1,
                GodClassSeverity::Medium => medium += 1,
                GodClassSeverity::Low => low += 1,
            }
        }

        if critical > 0 {
            eprintln!("  \x1b[35mCritical: {}\x1b[0m", critical);
        }
        if high > 0 {
            eprintln!("  \x1b[31mHigh: {}\x1b[0m", high);
        }
        if medium > 0 {
            eprintln!("  \x1b[38;5;208mMedium: {}\x1b[0m", medium);
        }
        if low > 0 {
            eprintln!("  \x1b[33mLow: {}\x1b[0m", low);
        }

        eprintln!(
            "\nAnalyzed {} classes, {} excluded (tests/framework/generated)",
            result.stats.total_classes, result.stats.excluded_classes
        );
    } else {
        eprintln!();
        eprintln!("No God classes detected with severity >= {}", min_severity);
        eprintln!(
            "Analyzed {} classes, {} excluded",
            result.stats.total_classes, result.stats.excluded_classes
        );
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_long_method(
    path: &PathBuf,
    lang: Option<Language>,
    format: OutputFormat,
    max_lines: u32,
    max_statements: u32,
    max_variables: u32,
    max_complexity: u32,
    max_nesting: u32,
    max_parameters: u32,
    strict: bool,
    lenient: bool,
    no_context: bool,
    show_suggestions: bool,
    min_severity: &str,
    sort: bool,
) -> Result<()> {
    use quality::smells::long_method::{
        detect_long_methods, format_long_method_summary, LongMethodConfig, LongMethodSeverity,
    };

    // Validate path exists
    require_exists(path)?;

    // Build configuration based on preset or custom values
    let mut config = if strict {
        LongMethodConfig::strict()
    } else if lenient {
        LongMethodConfig::lenient()
    } else {
        LongMethodConfig {
            max_lines,
            max_statements,
            max_variables,
            max_complexity,
            max_nesting,
            max_parameters,
            min_lines_for_analysis: 5,
            context_aware: !no_context,
        }
    };

    // Override context-aware if explicitly disabled
    if no_context {
        config.context_aware = false;
    }

    // Parse language
    let language = lang.map(|l| l.to_string());

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "minor" => LongMethodSeverity::Minor,
        "moderate" => LongMethodSeverity::Moderate,
        "major" => LongMethodSeverity::Major,
        "critical" => LongMethodSeverity::Critical,
        _ => LongMethodSeverity::Minor,
    };

    // Run detection
    let mut result = detect_long_methods(path, language.as_deref(), Some(config))
        .map_err(|e| anyhow::anyhow!("Long method detection failed: {}", e))?;

    // Filter by minimum severity
    result.findings.retain(|f| f.severity >= min_sev);

    // Sort by score if requested
    if sort {
        result.findings.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
    }

    let filtered_count = result.findings.len();

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            // Optionally filter out suggestions if not requested
            if !show_suggestions {
                for finding in &mut result.findings {
                    finding.suggestions.clear();
                    finding.extraction_candidates.clear();
                }
            }
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            if show_suggestions {
                println!("{}", format_long_method_summary(&result));
            } else {
                // Simpler output without suggestions
                println!("=== Long Method Analysis ===\n");
                println!("Path: {}", result.path.display());
                if let Some(ref lang) = result.language {
                    println!("Language: {}", lang);
                }
                println!();

                println!("Statistics:");
                println!("  Total methods: {}", result.stats.total_methods);
                println!(
                    "  Long methods: {} ({:.1}%)",
                    result.stats.long_methods, result.stats.percentage_long
                );
                println!("  Average lines: {:.1}", result.stats.average_lines);
                println!("  Max lines: {}", result.stats.max_lines);
                println!();

                if result.findings.is_empty() {
                    println!("No long methods found.");
                } else {
                    println!("Long Methods ({}):\n", result.findings.len());
                    for finding in &result.findings {
                        println!(
                            "{}{}\x1b[0m at {}:{}-{}",
                            finding.severity.color_code(),
                            finding.function_name,
                            finding.file.display(),
                            finding.line,
                            finding.end_line
                        );
                        println!(
                            "  {} lines, {} statements, {} vars, complexity {}, nesting {}",
                            finding.length.lines,
                            finding.length.statements,
                            finding.length.variables,
                            finding.complexity.cyclomatic,
                            finding.complexity.max_nesting
                        );
                        println!(
                            "  Category: {}, Severity: {}",
                            finding.category, finding.severity
                        );

                        if !finding.violations.is_empty() {
                            for v in &finding.violations {
                                println!("    - {}", v);
                            }
                        }
                        println!();
                    }
                }
            }
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for long method detection - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary to stderr
    if filtered_count > 0 {
        eprintln!();
        eprintln!(
            "Detected {} long method(s) with severity >= {}",
            filtered_count, min_severity
        );

        // Count by severity
        let mut critical = 0;
        let mut major = 0;
        let mut moderate = 0;
        let mut minor = 0;
        for finding in &result.findings {
            match finding.severity {
                LongMethodSeverity::Critical => critical += 1,
                LongMethodSeverity::Major => major += 1,
                LongMethodSeverity::Moderate => moderate += 1,
                LongMethodSeverity::Minor => minor += 1,
            }
        }

        if critical > 0 {
            eprintln!("  \x1b[35mCritical: {}\x1b[0m", critical);
        }
        if major > 0 {
            eprintln!("  \x1b[31mMajor: {}\x1b[0m", major);
        }
        if moderate > 0 {
            eprintln!("  \x1b[91mModerate: {}\x1b[0m", moderate);
        }
        if minor > 0 {
            eprintln!("  \x1b[33mMinor: {}\x1b[0m", minor);
        }
    } else {
        eprintln!();
        eprintln!("No long methods detected with severity >= {}", min_severity);
    }

    eprintln!("Analyzed {} methods total", result.stats.total_methods);

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn cmd_circular(
    path: &PathBuf,
    level: CircularLevelArg,
    lang: Option<Language>,
    format: OutputFormat,
    min_severity: &str,
    include_tests: bool,
    exclude_intentional: bool,
    max_cycles: usize,
    max_suggestions: usize,
) -> Result<()> {
    use quality::circular::{
        detect_circular_dependencies, format_circular_report, CircularConfig,
        Severity as CircularSeverity,
    };

    // Validate path exists and is a directory
    require_directory(path)?;

    // Parse minimum severity
    let min_sev = match min_severity.to_lowercase().as_str() {
        "low" => CircularSeverity::Low,
        "medium" => CircularSeverity::Medium,
        "high" => CircularSeverity::High,
        "critical" => CircularSeverity::Critical,
        _ => CircularSeverity::Low,
    };

    // Build configuration
    let mut config = CircularConfig::default();
    config.level = level.into();
    config.min_severity = min_sev;
    config.include_tests = include_tests;
    config.exclude_intentional = exclude_intentional;
    config.max_cycles = max_cycles;
    config.max_suggestions = max_suggestions;

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Run detection
    let result = detect_circular_dependencies(path.to_str().unwrap_or("."), Some(config))
        .map_err(|e| anyhow::anyhow!("Circular dependency detection failed: {}", e))?;

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_circular_report(&result));
        }
        OutputFormat::Mermaid => {
            // Generate Mermaid diagram for cycles
            println!("graph LR");
            for cycle in &result.cycles {
                for (from, to) in &cycle.cycle_path {
                    // Sanitize names for Mermaid
                    let from_id = from.replace('.', "_").replace("::", "_");
                    let to_id = to.replace('.', "_").replace("::", "_");
                    println!("    {}[\"{}\"] --> {}[\"{}\"]", from_id, from, to_id, to);
                }
            }
        }
        OutputFormat::Dot => {
            // Generate DOT graph for cycles
            println!("digraph circular_deps {{");
            println!("    rankdir=LR;");
            println!("    node [shape=box];");
            for cycle in &result.cycles {
                for (from, to) in &cycle.cycle_path {
                    println!("    \"{}\" -> \"{}\";", from, to);
                }
            }
            println!("}}");
        }
        OutputFormat::Csv => {
            // CSV not applicable for circular dependencies - fall back to JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary to stderr
    if result.stats.cycle_count > 0 {
        eprintln!();
        eprintln!(
            "Detected {} circular dependency cycle(s) at {} level",
            result.stats.cycle_count, result.config.level
        );

        if result.stats.critical_count > 0 {
            eprintln!("  \x1b[35mCritical: {}\x1b[0m", result.stats.critical_count);
        }
        if result.stats.high_count > 0 {
            eprintln!("  \x1b[31mHigh: {}\x1b[0m", result.stats.high_count);
        }
        if result.stats.medium_count > 0 {
            eprintln!("  \x1b[91mMedium: {}\x1b[0m", result.stats.medium_count);
        }
        if result.stats.low_count > 0 {
            eprintln!("  \x1b[33mLow: {}\x1b[0m", result.stats.low_count);
        }

        eprintln!();
        eprintln!(
            "  {} participants in cycles, {} files involved",
            result.total_participants_in_cycles, result.total_files_in_cycles
        );

        if !result.suggestions.is_empty() {
            eprintln!();
            eprintln!(
                "  {} breaking suggestion(s) generated",
                result.suggestions.len()
            );
        }
    } else {
        eprintln!();
        eprintln!(
            "No circular dependencies detected at {} level",
            result.config.level
        );
    }

    eprintln!(
        "Analyzed {} nodes, {} edges in {}ms",
        result.stats.total_nodes, result.stats.total_edges, result.stats.analysis_time_ms
    );

    Ok(())
}

fn cmd_patterns(
    path: &PathBuf,
    pattern_filter: Option<&str>,
    lang: Option<Language>,
    format: OutputFormat,
    min_confidence: f64,
    include_tests: bool,
    include_generated: bool,
    no_modern: bool,
    max_file_size: u64,
) -> Result<()> {
    use patterns::{detect_patterns, format_pattern_summary, PatternConfig};

    // Validate path exists
    require_exists(path)?;

    // Build configuration
    let mut config = PatternConfig::default();
    config.min_confidence = min_confidence.clamp(0.0, 1.0);
    config.max_file_size = max_file_size;
    config.include_tests = include_tests;
    config.include_generated = include_generated;
    config.detect_modern_patterns = !no_modern;

    if let Some(l) = lang {
        config.language = Some(l.to_string());
    }

    // Run detection
    let result = detect_patterns(path, pattern_filter, Some(config))
        .map_err(|e| anyhow::anyhow!("Pattern detection failed: {}", e))?;

    match format {
        OutputFormat::Json | OutputFormat::Jsonl => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
        OutputFormat::Text => {
            println!("{}", format_pattern_summary(&result));
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not directly applicable - output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary to stderr
    if result.stats.patterns_detected > 0 {
        eprintln!();
        eprintln!(
            "Detected {} design pattern(s) in {} files",
            result.stats.patterns_detected, result.stats.files_with_patterns
        );

        if !result.stats.by_category.is_empty() {
            eprintln!("  By category:");
            for (category, count) in &result.stats.by_category {
                eprintln!("    {}: {}", category, count);
            }
        }

        eprintln!(
            "  Average confidence: {:.1}%",
            result.stats.average_confidence * 100.0
        );
    } else {
        eprintln!();
        eprintln!(
            "No design patterns detected with confidence >= {:.0}%",
            min_confidence * 100.0
        );
    }

    eprintln!(
        "Scanned {} files ({} skipped)",
        result.stats.files_scanned, result.stats.files_skipped
    );

    Ok(())
}

// =============================================================================
// ANALYZE COMMANDS
// =============================================================================

fn cmd_analyze(subcmd: AnalyzeCommands) -> Result<()> {
    match subcmd {
        AnalyzeCommands::ResourceFlow {
            file,
            function,
            lang,
            format,
            issues_only,
            min_severity,
        } => {
            cmd_resource_flow(&file, &function, lang, format, issues_only, &min_severity)?;
        }
        AnalyzeCommands::Invariants {
            file,
            function,
            lang,
            format,
            preconditions_only,
            postconditions_only,
            loop_invariants_only,
            suggestions,
            min_confidence,
        } => {
            cmd_invariants(
                &file,
                function.as_deref(),
                lang,
                format,
                preconditions_only,
                postconditions_only,
                loop_invariants_only,
                suggestions,
                min_confidence,
            )?;
        }
        AnalyzeCommands::StateMachine {
            file,
            scope,
            lang,
            format,
            var_pattern,
            min_confidence,
            validate,
        } => {
            cmd_state_machine(
                &file,
                scope.as_deref(),
                lang,
                format,
                var_pattern.as_deref(),
                min_confidence,
                validate,
            )?;
        }
    }

    Ok(())
}

/// Extract implicit state machines from code.
fn cmd_state_machine(
    file: &PathBuf,
    scope: Option<&str>,
    _lang: Option<Language>,
    format: OutputFormat,
    var_pattern: Option<&str>,
    _min_confidence: f64,
    validate: bool,
) -> Result<()> {
    use analysis::state_machine::{ExtractorConfig, StateMachineExtractor};

    // Validate file exists
    require_file(file)?;

    // Create extractor with optional configuration
    let config = if let Some(pattern) = var_pattern {
        let mut cfg = ExtractorConfig::new();
        cfg.state_variable_names = pattern.split(',').map(|s| s.trim().to_string()).collect();
        cfg
    } else {
        ExtractorConfig::new()
    };
    let extractor = StateMachineExtractor::with_config(config);

    // Extract state machines
    let machines = extractor
        .extract_from_file(file)
        .context("Failed to extract state machines")?;

    // Filter by scope if specified
    let filtered: Vec<_> = if let Some(scope_filter) = scope {
        machines
            .into_iter()
            .filter(|m| m.name.contains(scope_filter))
            .collect()
    } else {
        machines
    };

    // Output based on format
    match format {
        OutputFormat::Text => {
            if filtered.is_empty() {
                println!("No state machines found in {}", file.display());
            } else {
                for (i, machine) in filtered.iter().enumerate() {
                    if i > 0 {
                        println!();
                    }
                    println!("State Machine: {}", machine.name);
                    println!("  Variable: {}", machine.state_variable);
                    println!(
                        "  Location: {}:{}",
                        machine.location.file, machine.location.start_line
                    );
                    println!();

                    println!("  States ({}):", machine.states.len());
                    for state in &machine.states {
                        let marker = if state.id == machine.initial_state {
                            " (initial)"
                        } else if machine.final_states.contains(&state.id) {
                            " (final)"
                        } else {
                            ""
                        };
                        println!("    - {}{}", state.name, marker);
                    }
                    println!();

                    println!("  Transitions ({}):", machine.transitions.len());
                    for trans in &machine.transitions {
                        let from = machine
                            .get_state(trans.from)
                            .map(|s| s.name.as_str())
                            .unwrap_or("?");
                        let to = machine
                            .get_state(trans.to)
                            .map(|s| s.name.as_str())
                            .unwrap_or("?");
                        print!("    {} --[{}]--> {}", from, trans.trigger, to);
                        if let Some(ref guard) = trans.guard {
                            print!(" [{}]", guard);
                        }
                        println!();
                    }

                    if validate {
                        let validation = machine.validate();
                        if !validation.issues.is_empty() {
                            println!();
                            println!("  Validation Issues:");
                            for issue in &validation.issues {
                                println!("    - {:?}: {}", issue.severity, issue.message);
                            }
                        }
                    }
                }

                eprintln!();
                eprintln!("Found {} state machine(s)", filtered.len());
            }
        }
        OutputFormat::Mermaid => {
            for machine in &filtered {
                println!("{}", machine.to_mermaid());
            }
        }
        OutputFormat::Dot => {
            for machine in &filtered {
                println!("{}", machine.to_dot());
            }
        }
        OutputFormat::Json | OutputFormat::Jsonl | OutputFormat::Csv => {
            // Build JSON output with optional validation
            let output: Vec<_> = filtered
                .iter()
                .map(|m| {
                    let mut obj = serde_json::to_value(m).unwrap_or_default();
                    if validate {
                        let validation = m.validate();
                        if let serde_json::Value::Object(ref mut map) = obj {
                            map.insert(
                                "validation".to_string(),
                                serde_json::to_value(&validation).unwrap_or_default(),
                            );
                        }
                    }
                    obj
                })
                .collect();

            let result = serde_json::json!({
                "file": file.to_string_lossy(),
                "state_machines_count": output.len(),
                "state_machines": output,
            });

            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    Ok(())
}

/// Analyze resource flow in a function.
fn cmd_resource_flow(
    file: &PathBuf,
    function: &str,
    lang: Option<Language>,
    format: OutputFormat,
    issues_only: bool,
    min_severity: &str,
) -> Result<()> {
    use analysis::resource_flow::{analyze_resource_flow, format_resource_flow_text, LeakSeverity};

    // Validate file exists
    require_file(file)?;

    let lang_str = lang.map(|l| l.to_string());

    // Run resource flow analysis
    let result = analyze_resource_flow(file, function, lang_str.as_deref())
        .context("Failed to analyze resource flow")?;

    // Filter by severity if specified
    let min_sev = match min_severity.to_lowercase().as_str() {
        "critical" => LeakSeverity::Critical,
        "high" => LeakSeverity::High,
        "medium" => LeakSeverity::Medium,
        _ => LeakSeverity::Low,
    };

    // Filter leaks by severity
    let filtered_leaks: Vec<_> = result
        .leaks
        .iter()
        .filter(|l| l.severity.weight() >= min_sev.weight())
        .collect();

    // Build output based on format
    match format {
        OutputFormat::Text => {
            if issues_only {
                // Only show issues
                if filtered_leaks.is_empty()
                    && result.double_releases.is_empty()
                    && result.use_after_release.is_empty()
                {
                    println!("No resource flow issues detected.");
                } else {
                    println!("Resource Flow Issues: {}", result.function_name);
                    println!("{}", "=".repeat(60));

                    if !filtered_leaks.is_empty() {
                        println!("\nRESOURCE LEAKS:");
                        for leak in &filtered_leaks {
                            println!(
                                "  [{}] {} `{}`",
                                leak.severity.weight(),
                                leak.resource.resource_type,
                                leak.resource.variable
                            );
                            println!("    At: {}", leak.resource.acquire_location);
                            println!("    Fix: {}", leak.suggestion);
                        }
                    }

                    if !result.double_releases.is_empty() {
                        println!("\nDOUBLE-RELEASE BUGS:");
                        for dr in &result.double_releases {
                            println!("  {} `{}`", dr.resource.resource_type, dr.resource.variable);
                            println!("    First: {}", dr.first_release);
                            println!("    Second: {}", dr.second_release);
                        }
                    }

                    if !result.use_after_release.is_empty() {
                        println!("\nUSE-AFTER-RELEASE BUGS:");
                        for uar in &result.use_after_release {
                            println!(
                                "  {} `{}`",
                                uar.resource.resource_type, uar.resource.variable
                            );
                            println!("    Released at: {}", uar.release_location);
                            println!("    Used at: {}", uar.use_location);
                        }
                    }
                }
            } else {
                // Full text output
                println!("{}", format_resource_flow_text(&result));
            }
        }
        OutputFormat::Json | OutputFormat::Jsonl => {
            // Output full result as JSON
            let output = if issues_only {
                serde_json::json!({
                    "function": result.function_name,
                    "file": result.file,
                    "leaks": filtered_leaks,
                    "double_releases": result.double_releases,
                    "use_after_release": result.use_after_release,
                    "total_issues": filtered_leaks.len()
                        + result.double_releases.len()
                        + result.use_after_release.len()
                })
            } else {
                serde_json::to_value(&result)?
            };

            println!(
                "{}",
                serde_json::to_string_pretty(&output).context("Failed to serialize output")?
            );
        }
        OutputFormat::Mermaid | OutputFormat::Dot | OutputFormat::Csv => {
            // Not applicable for resource flow, output JSON
            println!(
                "{}",
                serde_json::to_string_pretty(&result).context("Failed to serialize output")?
            );
        }
    }

    // Print summary to stderr
    let total_issues =
        result.stats.leaked + result.stats.double_releases + result.stats.use_after_release;

    if total_issues > 0 {
        eprintln!();
        eprintln!(
            "\x1b[31mFound {} issue(s):\x1b[0m {} leak(s), {} double-release(s), {} use-after-release",
            total_issues,
            result.stats.leaked,
            result.stats.double_releases,
            result.stats.use_after_release
        );
    } else {
        eprintln!();
        eprintln!("\x1b[32mNo resource flow issues detected.\x1b[0m");
    }

    eprintln!(
        "Analyzed {} resources ({} safely managed)",
        result.stats.total_resources, result.stats.safely_managed
    );

    Ok(())
}

/// Analyze invariants in source code.
#[allow(clippy::too_many_arguments)]
fn cmd_invariants(
    file: &PathBuf,
    function: Option<&str>,
    lang: Option<Language>,
    format: OutputFormat,
    preconditions_only: bool,
    postconditions_only: bool,
    loop_invariants_only: bool,
    include_suggestions: bool,
    min_confidence: f64,
) -> Result<()> {
    use analysis::{
        analyze_invariants, analyze_invariants_function, format_invariant_function_json,
        format_invariant_json, format_invariant_text,
    };

    // Validate file exists
    require_file(file)?;

    let file_str = file.to_str().context("Invalid file path")?;
    let lang_str = lang.map(|l| l.to_string());

    // Run analysis based on whether a specific function is requested
    if let Some(func_name) = function {
        // Analyze specific function
        let mut result = analyze_invariants_function(file_str, func_name, lang_str.as_deref())
            .context("Failed to analyze function invariants")?;

        // Filter by confidence
        result
            .preconditions
            .retain(|i| i.confidence >= min_confidence);
        result
            .postconditions
            .retain(|i| i.confidence >= min_confidence);
        for invs in result.loop_invariants.values_mut() {
            invs.retain(|i| i.confidence >= min_confidence);
        }

        // Filter by type if requested
        if preconditions_only {
            result.postconditions.clear();
            result.loop_invariants.clear();
            result.loop_details.clear();
        } else if postconditions_only {
            result.preconditions.clear();
            result.loop_invariants.clear();
            result.loop_details.clear();
        } else if loop_invariants_only {
            result.preconditions.clear();
            result.postconditions.clear();
        }

        // Clear suggestions if not wanted
        if !include_suggestions {
            result.suggested_assertions.clear();
        }

        // Output
        match format {
            OutputFormat::Text => {
                println!("Invariant Analysis: {}", result.function);
                println!(
                    "File: {} (lines {}-{})",
                    result.file, result.start_line, result.end_line
                );
                println!("{}", "=".repeat(60));

                if !result.preconditions.is_empty() {
                    println!("\nPRECONDITIONS:");
                    for inv in &result.preconditions {
                        println!(
                            "  {} (confidence: {:.0}%{})",
                            inv.expression,
                            inv.confidence * 100.0,
                            if inv.is_explicit { ", explicit" } else { "" }
                        );
                        for ev in &inv.evidence {
                            println!("    Evidence: {} - {}", ev.kind, ev.description);
                        }
                    }
                }

                if !result.postconditions.is_empty() {
                    println!("\nPOSTCONDITIONS:");
                    for inv in &result.postconditions {
                        println!(
                            "  {} (confidence: {:.0}%{})",
                            inv.expression,
                            inv.confidence * 100.0,
                            if inv.is_explicit { ", explicit" } else { "" }
                        );
                    }
                }

                if !result.loop_invariants.is_empty() {
                    println!("\nLOOP INVARIANTS:");
                    for (line, invs) in &result.loop_invariants {
                        println!("  At line {}:", line);
                        for inv in invs {
                            println!(
                                "    {} (confidence: {:.0}%)",
                                inv.expression,
                                inv.confidence * 100.0
                            );
                        }
                        if let Some(details) = result.loop_details.get(line) {
                            if let Some(ref lv) = details.loop_variable {
                                println!("    Loop variable: {}", lv);
                            }
                            if let Some(ref bounds) = details.bounds {
                                if let (Some(ref lower), Some(ref upper)) =
                                    (&bounds.lower, &bounds.upper)
                                {
                                    let op = if bounds.inclusive { "..=" } else { ".." };
                                    println!("    Bounds: {}{}{}", lower, op, upper);
                                }
                            }
                            if !details.monotonic_variables.is_empty() {
                                for mv in &details.monotonic_variables {
                                    println!("    {} is {:?}", mv.name, mv.direction);
                                }
                            }
                        }
                    }
                }

                if !result.suggested_assertions.is_empty() {
                    println!("\nSUGGESTED ASSERTIONS:");
                    for sug in &result.suggested_assertions {
                        println!("  Line {}: {}", sug.location.line, sug.assertion);
                        println!(
                            "    Reason: {} (confidence: {:.0}%)",
                            sug.reason,
                            sug.confidence * 100.0
                        );
                    }
                }

                // Summary
                println!();
                println!("Summary:");
                println!(
                    "  Preconditions: {} ({} explicit, {} inferred)",
                    result.preconditions.len(),
                    result.metrics.explicit_assertions,
                    result.metrics.inferred_preconditions
                );
                println!("  Postconditions: {}", result.postconditions.len());
                println!(
                    "  Loop invariants: {}",
                    result.metrics.loop_invariants_count
                );
                if include_suggestions {
                    println!("  Suggestions: {}", result.suggested_assertions.len());
                }
            }
            OutputFormat::Json | OutputFormat::Jsonl => {
                println!(
                    "{}",
                    format_invariant_function_json(&result)
                        .context("Failed to serialize output")?
                );
            }
            _ => {
                // Default to JSON for other formats
                println!(
                    "{}",
                    format_invariant_function_json(&result)
                        .context("Failed to serialize output")?
                );
            }
        }

        // Summary to stderr
        let total = result.preconditions.len()
            + result.postconditions.len()
            + result
                .loop_invariants
                .values()
                .map(|v| v.len())
                .sum::<usize>();

        eprintln!();
        if total > 0 {
            eprintln!(
                "Found {} invariant(s) (avg confidence: {:.0}%)",
                total,
                result.metrics.average_confidence * 100.0
            );
        } else {
            eprintln!(
                "No invariants found with confidence >= {:.0}%",
                min_confidence * 100.0
            );
        }
    } else {
        // Analyze all functions in file
        let mut result = analyze_invariants(file_str, lang_str.as_deref())
            .context("Failed to analyze invariants")?;

        // Filter by confidence
        for func in &mut result.functions {
            func.preconditions
                .retain(|i| i.confidence >= min_confidence);
            func.postconditions
                .retain(|i| i.confidence >= min_confidence);
            for invs in func.loop_invariants.values_mut() {
                invs.retain(|i| i.confidence >= min_confidence);
            }

            // Filter by type if requested
            if preconditions_only {
                func.postconditions.clear();
                func.loop_invariants.clear();
                func.loop_details.clear();
            } else if postconditions_only {
                func.preconditions.clear();
                func.loop_invariants.clear();
                func.loop_details.clear();
            } else if loop_invariants_only {
                func.preconditions.clear();
                func.postconditions.clear();
            }

            // Clear suggestions if not wanted
            if !include_suggestions {
                func.suggested_assertions.clear();
            }
        }

        // Output
        match format {
            OutputFormat::Text => {
                println!("{}", format_invariant_text(&result));
            }
            OutputFormat::Json | OutputFormat::Jsonl => {
                println!(
                    "{}",
                    format_invariant_json(&result).context("Failed to serialize output")?
                );
            }
            _ => {
                println!(
                    "{}",
                    format_invariant_json(&result).context("Failed to serialize output")?
                );
            }
        }

        // Summary to stderr
        eprintln!();
        eprintln!(
            "Analyzed {} function(s), found {} invariant(s)",
            result.summary.functions_analyzed, result.summary.total_invariants
        );
        if result.summary.average_confidence > 0.0 {
            eprintln!(
                "Average confidence: {:.0}%",
                result.summary.average_confidence * 100.0
            );
        }
        if result.summary.total_suggestions > 0 && include_suggestions {
            eprintln!(
                "Generated {} suggestion(s)",
                result.summary.total_suggestions
            );
        }
    }

    Ok(())
}
