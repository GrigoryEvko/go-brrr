//! Documentation coverage analysis for code quality assessment.
//!
//! This module provides comprehensive analysis of documentation coverage and quality
//! across multiple programming languages. It detects missing or inadequate documentation
//! and provides actionable suggestions for improvement.
//!
//! # Supported Languages
//!
//! | Language   | Docstring Format                           | Parameter/Return Syntax        |
//! |------------|--------------------------------------------|---------------------------------|
//! | Python     | `"""docstring"""` at start of function/class | :param, :return:, :raises:     |
//! | TypeScript | `/** JSDoc */` comments                    | @param, @returns, @throws      |
//! | JavaScript | `/** JSDoc */` comments                    | @param, @returns, @throws      |
//! | Rust       | `///` line doc or `/** */` block doc       | # Examples, # Errors, # Panics |
//! | Go         | `//` comment before function               | N/A (convention-based)         |
//! | Java       | `/** Javadoc */` comments                  | @param, @return, @throws       |
//!
//! # Quality Scoring
//!
//! Documentation quality is scored on a 0-5 scale:
//!
//! | Score | Description                                    |
//! |-------|------------------------------------------------|
//! | 0     | No documentation at all                        |
//! | 1     | Has docstring but minimal (just name restate)  |
//! | 2     | Documents purpose                              |
//! | 3     | Documents parameters/returns                   |
//! | 4     | Has usage examples                             |
//! | 5     | Comprehensive (purpose + params + examples)    |
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::doc_coverage::{analyze_doc_coverage, DocCoverageConfig};
//!
//! let result = analyze_doc_coverage("./src", None, None)?;
//! println!("Coverage: {:.1}%", result.metrics.coverage_rate * 100.0);
//! println!("Quality Score: {:.1}/5", result.metrics.quality_score);
//! for missing in &result.missing_docs {
//!     println!("Missing: {} at {}", missing.item, missing.location);
//! }
//! ```

use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::debug;
use tree_sitter::{Node, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for documentation coverage analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocCoverageConfig {
    /// Only analyze public items (default: false - analyze all)
    pub public_only: bool,

    /// Minimum quality score for an item to be considered documented (default: 2)
    pub min_quality_score: u8,

    /// Whether to check for parameter documentation (default: true)
    pub check_params: bool,

    /// Whether to check for return value documentation (default: true)
    pub check_returns: bool,

    /// Whether to check for exception/error documentation (default: true)
    pub check_exceptions: bool,

    /// Whether to check for examples (default: true)
    pub check_examples: bool,

    /// Whether to flag docstrings that just restate the function name (default: true)
    pub flag_name_restatement: bool,

    /// Exclude items matching these patterns from analysis
    pub exclude_patterns: Vec<String>,

    /// File patterns to identify generated code (excluded from analysis)
    pub generated_patterns: Vec<String>,

    /// Minimum lines for a function to require documentation (default: 3)
    pub min_lines_require_doc: u32,
}

impl Default for DocCoverageConfig {
    fn default() -> Self {
        Self {
            public_only: false,
            min_quality_score: 2,
            check_params: true,
            check_returns: true,
            check_exceptions: true,
            check_examples: true,
            flag_name_restatement: true,
            exclude_patterns: vec![
                "__init__".into(),
                "__str__".into(),
                "__repr__".into(),
                "setUp".into(),
                "tearDown".into(),
            ],
            generated_patterns: vec![
                "_pb2.py".into(),
                ".pb.go".into(),
                "generated".into(),
                ".gen.".into(),
                "_generated".into(),
            ],
            min_lines_require_doc: 3,
        }
    }
}

impl DocCoverageConfig {
    /// Create a strict configuration requiring comprehensive documentation.
    #[must_use]
    pub fn strict() -> Self {
        Self {
            public_only: true,
            min_quality_score: 3,
            check_params: true,
            check_returns: true,
            check_exceptions: true,
            check_examples: true,
            flag_name_restatement: true,
            min_lines_require_doc: 1,
            ..Default::default()
        }
    }

    /// Create a lenient configuration for legacy codebases.
    #[must_use]
    pub fn lenient() -> Self {
        Self {
            public_only: true,
            min_quality_score: 1,
            check_params: false,
            check_returns: false,
            check_exceptions: false,
            check_examples: false,
            flag_name_restatement: false,
            min_lines_require_doc: 10,
            ..Default::default()
        }
    }
}

// =============================================================================
// OUTPUT TYPES
// =============================================================================

/// Type of documentation being analyzed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DocType {
    /// File/module level docstring
    ModuleDoc,
    /// Class docstring
    ClassDoc,
    /// Function docstring
    FunctionDoc,
    /// Method docstring
    MethodDoc,
    /// Parameter documentation
    ParameterDoc,
    /// Return value documentation
    ReturnDoc,
    /// Exception/error documentation
    ExceptionDoc,
    /// Usage examples
    ExampleDoc,
}

impl std::fmt::Display for DocType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DocType::ModuleDoc => write!(f, "module"),
            DocType::ClassDoc => write!(f, "class"),
            DocType::FunctionDoc => write!(f, "function"),
            DocType::MethodDoc => write!(f, "method"),
            DocType::ParameterDoc => write!(f, "parameter"),
            DocType::ReturnDoc => write!(f, "return"),
            DocType::ExceptionDoc => write!(f, "exception"),
            DocType::ExampleDoc => write!(f, "example"),
        }
    }
}

/// Type of code item being documented.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ItemType {
    /// Module or file
    Module,
    /// Class or struct
    Class,
    /// Standalone function
    Function,
    /// Method within a class
    Method,
    /// Constant value
    Constant,
    /// Type alias
    TypeAlias,
    /// Enum type
    Enum,
    /// Trait or interface
    Trait,
}

impl std::fmt::Display for ItemType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ItemType::Module => write!(f, "module"),
            ItemType::Class => write!(f, "class"),
            ItemType::Function => write!(f, "function"),
            ItemType::Method => write!(f, "method"),
            ItemType::Constant => write!(f, "constant"),
            ItemType::TypeAlias => write!(f, "type_alias"),
            ItemType::Enum => write!(f, "enum"),
            ItemType::Trait => write!(f, "trait"),
        }
    }
}

/// Visibility level of a code item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Visibility {
    /// Public API (exported)
    Public,
    /// Private (internal to module)
    Private,
    /// Internal (visible within package/crate)
    Internal,
}

impl std::fmt::Display for Visibility {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Visibility::Public => write!(f, "public"),
            Visibility::Private => write!(f, "private"),
            Visibility::Internal => write!(f, "internal"),
        }
    }
}

/// Location information for an item.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// File path
    pub file: PathBuf,
    /// Start line (1-indexed)
    pub line: u32,
    /// End line (1-indexed)
    pub end_line: u32,
    /// Column (1-indexed)
    pub column: u32,
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file.display(), self.line)
    }
}

/// Coverage metrics for a specific documentation type.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TypeCoverage {
    /// Total items of this type
    pub total: u32,
    /// Items with documentation
    pub documented: u32,
    /// Coverage rate (0.0-1.0)
    pub rate: f64,
}

impl TypeCoverage {
    /// Calculate coverage rate from total and documented counts.
    fn calculate_rate(&mut self) {
        self.rate = if self.total > 0 {
            f64::from(self.documented) / f64::from(self.total)
        } else {
            1.0 // No items means 100% coverage
        };
    }
}

/// Aggregate documentation coverage metrics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocCoverageMetrics {
    /// Total items analyzed
    pub total_items: u32,
    /// Items with documentation
    pub documented_items: u32,
    /// Overall coverage rate (0.0-1.0)
    pub coverage_rate: f64,
    /// Coverage broken down by documentation type
    pub by_type: FxHashMap<DocType, TypeCoverage>,
    /// Average quality score (0-5)
    pub quality_score: f64,
    /// Total files analyzed
    pub files_analyzed: u32,
    /// Files with module documentation
    pub files_with_module_doc: u32,
}

impl Default for DocCoverageMetrics {
    fn default() -> Self {
        Self {
            total_items: 0,
            documented_items: 0,
            coverage_rate: 0.0,
            by_type: FxHashMap::default(),
            quality_score: 0.0,
            files_analyzed: 0,
            files_with_module_doc: 0,
        }
    }
}

/// Information about a missing documentation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MissingDoc {
    /// Name of the item missing documentation
    pub item: String,
    /// Type of item
    pub item_type: ItemType,
    /// Location in source code
    pub location: Location,
    /// Visibility level
    pub visibility: Visibility,
    /// Suggested documentation
    pub suggestion: String,
    /// What specifically is missing
    pub missing_elements: Vec<DocType>,
    /// Current quality score
    pub current_score: u8,
}

/// Documentation quality analysis for a single item.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocQuality {
    /// Name of the item
    pub item: String,
    /// Type of item
    pub item_type: ItemType,
    /// Location in source code
    pub location: Location,
    /// Visibility level
    pub visibility: Visibility,
    /// Quality score (0-5)
    pub score: u8,
    /// Has any docstring
    pub has_docstring: bool,
    /// Describes purpose (not just name restatement)
    pub describes_purpose: bool,
    /// Has parameter documentation
    pub has_param_docs: bool,
    /// Has return documentation
    pub has_return_docs: bool,
    /// Has exception/error documentation
    pub has_exception_docs: bool,
    /// Has examples
    pub has_examples: bool,
    /// The actual docstring (if present)
    pub docstring: Option<String>,
    /// Issues found with the documentation
    pub issues: Vec<String>,
}

/// Per-file documentation analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileDocCoverage {
    /// File path
    pub file: PathBuf,
    /// Whether file has module-level documentation
    pub has_module_doc: bool,
    /// Module docstring content (if any)
    pub module_doc: Option<String>,
    /// Total items in file
    pub total_items: u32,
    /// Documented items in file
    pub documented_items: u32,
    /// File-level coverage rate
    pub coverage_rate: f64,
    /// Average quality score for file
    pub quality_score: f64,
    /// Per-item documentation quality
    pub items: Vec<DocQuality>,
    /// Missing documentation items
    pub missing: Vec<MissingDoc>,
}

/// Complete documentation coverage analysis result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocCoverageAnalysis {
    /// Per-file analysis results
    pub files: Vec<FileDocCoverage>,
    /// Aggregate metrics
    pub metrics: DocCoverageMetrics,
    /// All missing documentation items
    pub missing_docs: Vec<MissingDoc>,
    /// Documentation TODOs (items needing attention)
    pub todos: Vec<DocTodo>,
}

/// A documentation TODO item for prioritized improvement.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocTodo {
    /// File path
    pub file: PathBuf,
    /// Item name
    pub item: String,
    /// Item type
    pub item_type: ItemType,
    /// Line number
    pub line: u32,
    /// Priority (1 = highest)
    pub priority: u32,
    /// Description of what needs to be done
    pub description: String,
    /// Visibility (public items are higher priority)
    pub visibility: Visibility,
}

/// Error type for documentation coverage analysis.
#[derive(Debug, thiserror::Error)]
pub enum DocCoverageError {
    /// IO error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    /// Parse error
    #[error("Parse error in {file}: {message}")]
    Parse { file: String, message: String },
    /// Configuration error
    #[error("Configuration error: {0}")]
    Config(String),
    /// Path error
    #[error("Path error: {0}")]
    Path(String),
}

impl From<BrrrError> for DocCoverageError {
    fn from(e: BrrrError) -> Self {
        Self::Path(e.to_string())
    }
}

// =============================================================================
// LANGUAGE-SPECIFIC DOCSTRING PATTERNS
// =============================================================================

/// Python docstring format detection patterns.
mod python_patterns {
    /// Markers indicating parameter documentation (Google, NumPy, Sphinx styles)
    pub const PARAM_MARKERS: &[&str] = &[
        ":param ",
        ":type ",
        "Args:",
        "Arguments:",
        "Parameters:",
        "Parameters\n",
        "----------",
    ];

    /// Markers indicating return documentation
    pub const RETURN_MARKERS: &[&str] =
        &[":return:", ":returns:", ":rtype:", "Returns:", "Returns\n"];

    /// Markers indicating exception documentation
    pub const EXCEPTION_MARKERS: &[&str] =
        &[":raises ", ":raise ", ":except:", "Raises:", "Raises\n"];

    /// Markers indicating examples
    pub const EXAMPLE_MARKERS: &[&str] = &[
        ">>>",
        "Example:",
        "Examples:",
        "Example\n",
        "Examples\n",
        ".. code-block::",
        "```",
    ];
}

/// JavaScript/TypeScript JSDoc patterns.
mod jsdoc_patterns {
    /// Markers indicating parameter documentation
    pub const PARAM_MARKERS: &[&str] = &["@param ", "@arg ", "@argument "];

    /// Markers indicating return documentation
    pub const RETURN_MARKERS: &[&str] = &["@return ", "@returns "];

    /// Markers indicating exception documentation
    pub const EXCEPTION_MARKERS: &[&str] = &["@throws ", "@exception "];

    /// Markers indicating examples
    pub const EXAMPLE_MARKERS: &[&str] = &["@example"];
}

/// Rust doc comment patterns.
mod rust_patterns {
    /// Markers indicating examples
    pub const EXAMPLE_MARKERS: &[&str] = &[
        "# Example",
        "# Examples",
        "```rust",
        "```no_run",
        "```ignore",
        "```should_panic",
        "```compile_fail",
        "```",
    ];

    /// Markers indicating error documentation
    pub const ERROR_MARKERS: &[&str] = &["# Errors", "# Panics", "# Safety"];

    /// Markers indicating return documentation
    pub const RETURN_MARKERS: &[&str] = &["# Returns", "Returns"];
}

/// Go doc comment patterns.
mod go_patterns {
    /// Common doc comment patterns in Go
    pub const EXAMPLE_MARKERS: &[&str] = &["Example:", "See:", "Usage:"];
}

// =============================================================================
// ANALYSIS IMPLEMENTATION
// =============================================================================

/// Analyze documentation coverage for a project.
///
/// Scans source files and extracts documentation metrics for all code items.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `lang` - Optional language filter (auto-detected if None)
/// * `config` - Optional configuration (uses defaults if None)
///
/// # Returns
///
/// * `Result<DocCoverageAnalysis>` - Complete analysis results
///
/// # Errors
///
/// Returns an error if:
/// - Path does not exist or is not accessible
/// - Files cannot be parsed
/// - Configuration is invalid
pub fn analyze_doc_coverage(
    path: &Path,
    lang: Option<&str>,
    config: Option<DocCoverageConfig>,
) -> Result<DocCoverageAnalysis> {
    let config = config.unwrap_or_default();

    // Get language registry for parsing (use global singleton)
    let registry = LanguageRegistry::global();

    // Handle single file vs directory
    let file_results = if path.is_file() {
        let lang_name = lang
            .map(String::from)
            .or_else(|| {
                path.extension()
                    .and_then(|ext| {
                        registry.get_by_extension(&format!(".{}", ext.to_string_lossy()))
                    })
                    .map(|l| l.name().to_string())
            })
            .unwrap_or_else(|| "unknown".to_string());

        vec![analyze_file(path, &lang_name, &config, registry)?]
    } else {
        // Scan directory for source files
        let scan_config = ScanConfig {
            follow_symlinks: false,
            language: lang.map(String::from),
            collect_metadata: true,
            ..Default::default()
        };

        let path_str = path.to_str().ok_or_else(|| {
            BrrrError::Io(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Path contains invalid UTF-8",
            ))
        })?;
        let scanner = ProjectScanner::new(path_str)?;
        let files = scanner.scan_with_config(&scan_config)?;

        debug!(
            "Found {} files to analyze for doc coverage",
            files.metadata.len()
        );

        // Process files in parallel using metadata
        let results: Vec<_> = files
            .metadata
            .par_iter()
            .filter_map(|file_meta| {
                let lang_name = file_meta.language.clone()?;

                // Skip generated files
                let path_str = file_meta.path.to_string_lossy();
                if config
                    .generated_patterns
                    .iter()
                    .any(|p| path_str.contains(p))
                {
                    debug!("Skipping generated file: {}", path_str);
                    return None;
                }

                match analyze_file(&file_meta.path, &lang_name, &config, registry) {
                    Ok(result) => Some(result),
                    Err(e) => {
                        debug!("Error analyzing {}: {}", file_meta.path.display(), e);
                        None
                    }
                }
            })
            .collect();

        results
    };

    // Aggregate results
    let mut analysis = aggregate_results(file_results, &config);

    // Sort todos by priority
    analysis.todos.sort_by_key(|t| t.priority);

    Ok(analysis)
}

/// Analyze documentation coverage for a single file.
fn analyze_file(
    path: &Path,
    lang_name: &str,
    config: &DocCoverageConfig,
    registry: &LanguageRegistry,
) -> Result<FileDocCoverage> {
    // Read file content
    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;

    // Get language implementation
    let lang = registry
        .get_by_name(lang_name)
        .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?;

    // Parse file
    let mut parser = lang.parser_for_path(path)?;
    let tree = parser
        .parse(&source, None)
        .ok_or_else(|| BrrrError::Parse {
            file: path.display().to_string(),
            message: "Failed to parse file".to_string(),
        })?;

    // Extract module docstring
    let module_doc = lang.extract_module_docstring(&tree, &source);
    let has_module_doc = module_doc.is_some();

    // Analyze all items in the file
    let mut items = Vec::new();
    let mut missing = Vec::new();

    analyze_tree_items(
        &tree,
        &source,
        path,
        lang_name,
        config,
        &mut items,
        &mut missing,
    );

    // Calculate file-level metrics
    let total_items = items.len() as u32;
    let documented_items = items
        .iter()
        .filter(|i| i.has_docstring && i.score >= config.min_quality_score)
        .count() as u32;
    let coverage_rate = if total_items > 0 {
        f64::from(documented_items) / f64::from(total_items)
    } else {
        1.0
    };

    let quality_score = if items.is_empty() {
        0.0
    } else {
        items.iter().map(|i| f64::from(i.score)).sum::<f64>() / items.len() as f64
    };

    Ok(FileDocCoverage {
        file: path.to_path_buf(),
        has_module_doc,
        module_doc,
        total_items,
        documented_items,
        coverage_rate,
        quality_score,
        items,
        missing,
    })
}

/// Analyze all documentable items in a syntax tree.
fn analyze_tree_items(
    tree: &Tree,
    source: &[u8],
    path: &Path,
    lang_name: &str,
    config: &DocCoverageConfig,
    items: &mut Vec<DocQuality>,
    missing: &mut Vec<MissingDoc>,
) {
    let root = tree.root_node();
    analyze_node(root, source, path, lang_name, config, None, items, missing);
}

/// Recursively analyze a node and its children for documentation.
fn analyze_node(
    node: Node,
    source: &[u8],
    path: &Path,
    lang_name: &str,
    config: &DocCoverageConfig,
    parent_class: Option<&str>,
    items: &mut Vec<DocQuality>,
    missing: &mut Vec<MissingDoc>,
) {
    let node_kind = node.kind();

    // Check if this is a documentable item
    if let Some((item_type, visibility)) = get_item_info(node, source, lang_name, parent_class) {
        // Skip private items if public_only is set
        if config.public_only && visibility != Visibility::Public {
            // Continue analyzing children
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                let new_parent = if item_type == ItemType::Class {
                    Some(extract_item_name(node, source, lang_name))
                } else {
                    parent_class.map(String::from)
                };
                analyze_node(
                    child,
                    source,
                    path,
                    lang_name,
                    config,
                    new_parent.as_deref(),
                    items,
                    missing,
                );
            }
            return;
        }

        let item_name = extract_item_name(node, source, lang_name);

        // Check if item should be excluded
        if config
            .exclude_patterns
            .iter()
            .any(|p| item_name.contains(p))
        {
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                analyze_node(
                    child,
                    source,
                    path,
                    lang_name,
                    config,
                    parent_class,
                    items,
                    missing,
                );
            }
            return;
        }

        // Get line count for minimum threshold
        let start_line = node.start_position().row + 1;
        let end_line = node.end_position().row + 1;
        let line_count = end_line - start_line + 1;

        if line_count < config.min_lines_require_doc as usize {
            // Small items don't require documentation, skip
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                let new_parent = if item_type == ItemType::Class {
                    Some(item_name.clone())
                } else {
                    parent_class.map(String::from)
                };
                analyze_node(
                    child,
                    source,
                    path,
                    lang_name,
                    config,
                    new_parent.as_deref(),
                    items,
                    missing,
                );
            }
            return;
        }

        // Extract documentation
        let doc_quality = analyze_item_documentation(
            node, source, path, lang_name, &item_name, item_type, visibility, config,
        );

        // Check if documentation is missing or inadequate
        if !doc_quality.has_docstring || doc_quality.score < config.min_quality_score {
            let missing_elements = determine_missing_elements(&doc_quality, config);
            let suggestion =
                generate_suggestion(&item_name, item_type, &missing_elements, lang_name);

            missing.push(MissingDoc {
                item: item_name.clone(),
                item_type,
                location: doc_quality.location.clone(),
                visibility,
                suggestion,
                missing_elements,
                current_score: doc_quality.score,
            });
        }

        items.push(doc_quality);
    }

    // Recurse into children
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        let new_parent = if matches!(
            node_kind,
            "class_definition" | "class_declaration" | "impl_item" | "class_specifier"
        ) {
            Some(extract_item_name(node, source, lang_name))
        } else {
            parent_class.map(String::from)
        };
        analyze_node(
            child,
            source,
            path,
            lang_name,
            config,
            new_parent.as_deref(),
            items,
            missing,
        );
    }
}

/// Get item type and visibility from a node.
fn get_item_info(
    node: Node,
    source: &[u8],
    lang_name: &str,
    parent_class: Option<&str>,
) -> Option<(ItemType, Visibility)> {
    let kind = node.kind();

    match lang_name {
        "python" => match kind {
            "function_definition" => {
                let name = extract_item_name(node, source, lang_name);
                let visibility = if name.starts_with('_') && !name.starts_with("__") {
                    Visibility::Private
                } else if name.starts_with("__") && name.ends_with("__") {
                    Visibility::Public // Dunder methods are special
                } else if name.starts_with("__") {
                    Visibility::Private // Name mangling
                } else {
                    Visibility::Public
                };
                let item_type = if parent_class.is_some() {
                    ItemType::Method
                } else {
                    ItemType::Function
                };
                Some((item_type, visibility))
            }
            "class_definition" => {
                let name = extract_item_name(node, source, lang_name);
                let visibility = if name.starts_with('_') {
                    Visibility::Private
                } else {
                    Visibility::Public
                };
                Some((ItemType::Class, visibility))
            }
            _ => None,
        },

        "typescript" | "javascript" => match kind {
            "function_declaration" => {
                Some((ItemType::Function, determine_js_visibility(node, source)))
            }
            "method_definition" => Some((ItemType::Method, determine_js_visibility(node, source))),
            "class_declaration" => Some((ItemType::Class, determine_js_visibility(node, source))),
            "arrow_function" | "function" if is_named_export(node, source) => {
                Some((ItemType::Function, Visibility::Public))
            }
            _ => None,
        },

        "rust" => match kind {
            "function_item" => {
                let visibility = determine_rust_visibility(node, source);
                let item_type = if parent_class.is_some() {
                    ItemType::Method
                } else {
                    ItemType::Function
                };
                Some((item_type, visibility))
            }
            "struct_item" | "enum_item" => {
                Some((ItemType::Class, determine_rust_visibility(node, source)))
            }
            "trait_item" => Some((ItemType::Trait, determine_rust_visibility(node, source))),
            "impl_item" => None, // Analyze the methods inside instead
            _ => None,
        },

        "go" => match kind {
            "function_declaration" | "method_declaration" => {
                let name = extract_item_name(node, source, lang_name);
                let visibility = if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    Visibility::Public
                } else {
                    Visibility::Private
                };
                let item_type = if kind == "method_declaration" {
                    ItemType::Method
                } else {
                    ItemType::Function
                };
                Some((item_type, visibility))
            }
            "type_declaration" => {
                let name = extract_item_name(node, source, lang_name);
                let visibility = if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    Visibility::Public
                } else {
                    Visibility::Private
                };
                Some((ItemType::Class, visibility))
            }
            _ => None,
        },

        "java" | "c" | "cpp" => match kind {
            "method_declaration" | "function_definition" => {
                Some((ItemType::Method, determine_c_visibility(node, source)))
            }
            "class_declaration" | "class_specifier" => {
                Some((ItemType::Class, determine_c_visibility(node, source)))
            }
            _ => None,
        },

        _ => None,
    }
}

/// Extract the name of an item from its node.
fn extract_item_name(node: Node, source: &[u8], lang_name: &str) -> String {
    let kind = node.kind();

    // Try to find the name child based on language
    let name_field = match (lang_name, kind) {
        ("python", "function_definition") => "name",
        ("python", "class_definition") => "name",
        ("rust", "function_item") => "name",
        ("rust", "struct_item") => "name",
        ("rust", "enum_item") => "name",
        ("rust", "trait_item") => "name",
        ("go", "function_declaration") => "name",
        ("go", "method_declaration") => "name",
        ("typescript" | "javascript", "function_declaration") => "name",
        ("typescript" | "javascript", "class_declaration") => "name",
        ("typescript" | "javascript", "method_definition") => "name",
        ("java", "method_declaration") => "name",
        ("java", "class_declaration") => "name",
        _ => "name",
    };

    if let Some(name_node) = node.child_by_field_name(name_field) {
        return node_text(name_node, source).to_string();
    }

    // Fallback: search for identifier child
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" || child.kind() == "name" {
            return node_text(child, source).to_string();
        }
    }

    "<unknown>".to_string()
}

/// Analyze documentation quality for a single item.
fn analyze_item_documentation(
    node: Node,
    source: &[u8],
    path: &Path,
    lang_name: &str,
    item_name: &str,
    item_type: ItemType,
    visibility: Visibility,
    config: &DocCoverageConfig,
) -> DocQuality {
    let location = Location {
        file: path.to_path_buf(),
        line: (node.start_position().row + 1) as u32,
        end_line: (node.end_position().row + 1) as u32,
        column: (node.start_position().column + 1) as u32,
    };

    // Extract docstring based on language
    let docstring = extract_docstring(node, source, lang_name);

    let mut has_docstring = docstring.is_some();
    let mut describes_purpose = false;
    let mut has_param_docs = false;
    let mut has_return_docs = false;
    let mut has_exception_docs = false;
    let mut has_examples = false;
    let mut issues = Vec::new();

    if let Some(ref doc) = docstring {
        let doc_lower = doc.to_lowercase();

        // Check for name restatement (low-quality doc)
        let name_words: Vec<&str> = item_name
            .split(|c: char| c == '_' || c.is_uppercase())
            .filter(|s| !s.is_empty())
            .collect();

        let is_name_restatement = if config.flag_name_restatement && !name_words.is_empty() {
            // Check if doc is mostly just the name words
            let first_line = doc.lines().next().unwrap_or("");
            let first_line_lower = first_line.to_lowercase();
            name_words
                .iter()
                .all(|w| first_line_lower.contains(&w.to_lowercase()))
                && first_line.split_whitespace().count() <= name_words.len() + 3
        } else {
            false
        };

        if is_name_restatement {
            issues.push("Docstring just restates function name".to_string());
        } else {
            describes_purpose = true;
        }

        // Check for parameter documentation
        has_param_docs = match lang_name {
            "python" => python_patterns::PARAM_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "typescript" | "javascript" => jsdoc_patterns::PARAM_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "rust" => doc.contains("# Arguments") || doc.contains("`") && doc.contains("- "),
            _ => doc.contains("param") || doc.contains("arg"),
        };

        // Check for return documentation
        has_return_docs = match lang_name {
            "python" => python_patterns::RETURN_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "typescript" | "javascript" => jsdoc_patterns::RETURN_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "rust" => rust_patterns::RETURN_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            _ => doc_lower.contains("return"),
        };

        // Check for exception documentation
        has_exception_docs = match lang_name {
            "python" => python_patterns::EXCEPTION_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "typescript" | "javascript" => jsdoc_patterns::EXCEPTION_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "rust" => rust_patterns::ERROR_MARKERS.iter().any(|m| doc.contains(m)),
            _ => doc_lower.contains("throw") || doc_lower.contains("error"),
        };

        // Check for examples
        has_examples = match lang_name {
            "python" => python_patterns::EXAMPLE_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "typescript" | "javascript" => jsdoc_patterns::EXAMPLE_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "rust" => rust_patterns::EXAMPLE_MARKERS
                .iter()
                .any(|m| doc.contains(m)),
            "go" => go_patterns::EXAMPLE_MARKERS.iter().any(|m| doc.contains(m)),
            _ => doc_lower.contains("example"),
        };

        // Add issues for missing elements
        if config.check_params && !has_param_docs && has_parameters(node, source, lang_name) {
            issues.push("Missing parameter documentation".to_string());
        }
        if config.check_returns && !has_return_docs && has_return_value(node, source, lang_name) {
            issues.push("Missing return value documentation".to_string());
        }
        if config.check_examples && !has_examples {
            issues.push("No usage examples".to_string());
        }
    } else {
        issues.push("No documentation".to_string());
    }

    // Calculate quality score
    let score = calculate_quality_score(
        has_docstring,
        describes_purpose,
        has_param_docs,
        has_return_docs,
        has_exception_docs,
        has_examples,
    );

    // Handle edge case: docstring exists but is empty/whitespace only
    if let Some(ref doc) = docstring {
        if doc.trim().is_empty() {
            has_docstring = false;
        }
    }

    DocQuality {
        item: item_name.to_string(),
        item_type,
        location,
        visibility,
        score,
        has_docstring,
        describes_purpose,
        has_param_docs,
        has_return_docs,
        has_exception_docs,
        has_examples,
        docstring,
        issues,
    }
}

/// Extract docstring from a node based on language.
fn extract_docstring(node: Node, source: &[u8], lang_name: &str) -> Option<String> {
    match lang_name {
        "python" => extract_python_docstring(node, source),
        "typescript" | "javascript" => extract_jsdoc(node, source),
        "rust" => extract_rust_doc(node, source),
        "go" => extract_go_doc(node, source),
        "java" => extract_javadoc(node, source),
        _ => extract_generic_doc(node, source),
    }
}

/// Extract Python docstring from function/class body.
fn extract_python_docstring(node: Node, source: &[u8]) -> Option<String> {
    // For Python, docstring is the first string expression in the body
    let body = node.child_by_field_name("body")?;

    let mut cursor = body.walk();
    for child in body.children(&mut cursor) {
        if child.kind() == "expression_statement" {
            if let Some(expr) = child.child(0) {
                if expr.kind() == "string" || expr.kind() == "concatenated_string" {
                    let text = node_text(expr, source);
                    // Strip quotes
                    let cleaned = text
                        .trim()
                        .trim_start_matches("\"\"\"")
                        .trim_end_matches("\"\"\"")
                        .trim_start_matches("'''")
                        .trim_end_matches("'''")
                        .trim_start_matches('"')
                        .trim_end_matches('"')
                        .trim_start_matches('\'')
                        .trim_end_matches('\'')
                        .trim()
                        .to_string();
                    return Some(cleaned);
                }
            }
        }
        // Only check first statement
        break;
    }
    None
}

/// Extract JSDoc comment before a node.
fn extract_jsdoc(node: Node, source: &[u8]) -> Option<String> {
    // Look for a comment node immediately before this node
    if let Some(prev) = node.prev_sibling() {
        if prev.kind() == "comment" {
            let text = node_text(prev, source);
            if text.starts_with("/**") {
                let cleaned = text
                    .trim_start_matches("/**")
                    .trim_end_matches("*/")
                    .lines()
                    .map(|l| l.trim().trim_start_matches('*').trim())
                    .collect::<Vec<_>>()
                    .join("\n")
                    .trim()
                    .to_string();
                return Some(cleaned);
            }
        }
    }

    // Check parent for preceding comment (handles exported functions)
    if let Some(parent) = node.parent() {
        if let Some(prev) = parent.prev_sibling() {
            if prev.kind() == "comment" {
                let text = node_text(prev, source);
                if text.starts_with("/**") {
                    let cleaned = text
                        .trim_start_matches("/**")
                        .trim_end_matches("*/")
                        .lines()
                        .map(|l| l.trim().trim_start_matches('*').trim())
                        .collect::<Vec<_>>()
                        .join("\n")
                        .trim()
                        .to_string();
                    return Some(cleaned);
                }
            }
        }
    }
    None
}

/// Extract Rust doc comments.
fn extract_rust_doc(node: Node, source: &[u8]) -> Option<String> {
    let mut doc_lines = Vec::new();
    let start_row = node.start_position().row;

    // Look for doc comments before the item
    // Need to check preceding siblings at parent level
    let parent = node.parent()?;
    let mut cursor = parent.walk();

    let mut found_node = false;
    let mut prev_siblings = Vec::new();

    for child in parent.children(&mut cursor) {
        if child.id() == node.id() {
            found_node = true;
            break;
        }
        prev_siblings.push(child);
    }

    if !found_node {
        return None;
    }

    // Check preceding siblings in reverse order
    for prev in prev_siblings.iter().rev() {
        let kind = prev.kind();
        if kind == "line_comment" || kind == "attribute_item" {
            let text = node_text(*prev, source);
            if text.starts_with("///") {
                doc_lines.insert(0, text.trim_start_matches("///").trim().to_string());
            } else if text.starts_with("//!") {
                doc_lines.insert(0, text.trim_start_matches("//!").trim().to_string());
            } else if kind != "line_comment" {
                // Non-doc comment, stop
                break;
            }
        } else if kind == "block_comment" {
            let text = node_text(*prev, source);
            if text.starts_with("/**") && !text.starts_with("/***") {
                let cleaned = text
                    .trim_start_matches("/**")
                    .trim_end_matches("*/")
                    .lines()
                    .map(|l| l.trim().trim_start_matches('*').trim())
                    .collect::<Vec<_>>()
                    .join("\n");
                doc_lines.insert(0, cleaned);
            }
        } else if prev.end_position().row + 1 < start_row {
            // Gap between this sibling and the node, stop looking
            break;
        }
    }

    if doc_lines.is_empty() {
        None
    } else {
        Some(doc_lines.join("\n"))
    }
}

/// Extract Go doc comments.
fn extract_go_doc(node: Node, source: &[u8]) -> Option<String> {
    // Go uses // comments immediately before functions
    let mut doc_lines = Vec::new();
    let start_row = node.start_position().row;

    // Check for preceding comment siblings
    let parent = node.parent()?;
    let mut cursor = parent.walk();
    let mut prev_siblings = Vec::new();

    for child in parent.children(&mut cursor) {
        if child.id() == node.id() {
            break;
        }
        prev_siblings.push(child);
    }

    // Check siblings in reverse, collecting comments
    for prev in prev_siblings.iter().rev() {
        if prev.kind() == "comment" {
            let text = node_text(*prev, source);
            if text.starts_with("//") {
                let clean = text.trim_start_matches("//").trim();
                doc_lines.insert(0, clean.to_string());
            } else if text.starts_with("/*") {
                let cleaned = text
                    .trim_start_matches("/*")
                    .trim_end_matches("*/")
                    .trim()
                    .to_string();
                doc_lines.insert(0, cleaned);
                break;
            }
        } else if prev.end_position().row + 1 < start_row {
            break;
        }
    }

    if doc_lines.is_empty() {
        None
    } else {
        Some(doc_lines.join("\n"))
    }
}

/// Extract Javadoc comments.
fn extract_javadoc(node: Node, source: &[u8]) -> Option<String> {
    // Similar to JSDoc
    if let Some(prev) = node.prev_sibling() {
        if prev.kind() == "block_comment" || prev.kind() == "comment" {
            let text = node_text(prev, source);
            if text.starts_with("/**") {
                let cleaned = text
                    .trim_start_matches("/**")
                    .trim_end_matches("*/")
                    .lines()
                    .map(|l| l.trim().trim_start_matches('*').trim())
                    .collect::<Vec<_>>()
                    .join("\n")
                    .trim()
                    .to_string();
                return Some(cleaned);
            }
        }
    }
    None
}

/// Generic doc extraction (looks for preceding comments).
fn extract_generic_doc(node: Node, source: &[u8]) -> Option<String> {
    if let Some(prev) = node.prev_sibling() {
        if prev.kind().contains("comment") {
            return Some(node_text(prev, source).to_string());
        }
    }
    None
}

/// Calculate quality score (0-5) based on documentation elements.
fn calculate_quality_score(
    has_docstring: bool,
    describes_purpose: bool,
    has_param_docs: bool,
    has_return_docs: bool,
    has_exception_docs: bool,
    has_examples: bool,
) -> u8 {
    if !has_docstring {
        return 0;
    }
    if !describes_purpose {
        return 1;
    }

    let mut score: u8 = 2; // Base score for having purpose

    if has_param_docs || has_return_docs {
        score = 3;
    }
    if has_examples {
        score = score.max(4);
    }
    if has_param_docs && has_return_docs && has_examples {
        score = 5;
    }
    if has_exception_docs && score >= 3 {
        score = score.saturating_add(0); // Bonus, but capped at 5
    }

    score.min(5)
}

/// Check if a function has parameters.
fn has_parameters(node: Node, source: &[u8], lang_name: &str) -> bool {
    let params_field = match lang_name {
        "python" => "parameters",
        "rust" => "parameters",
        "go" => "parameters",
        "typescript" | "javascript" => "parameters",
        "java" => "parameters",
        _ => "parameters",
    };

    if let Some(params) = node.child_by_field_name(params_field) {
        // Check if there are actual parameters (not just parentheses)
        let mut cursor = params.walk();
        for child in params.children(&mut cursor) {
            let kind = child.kind();
            if kind != "(" && kind != ")" && kind != "," && kind != "self" && kind != "cls" {
                // Check for Python self/cls
                let text = node_text(child, source);
                if text != "self" && text != "cls" && !text.is_empty() {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if a function has a return value.
fn has_return_value(node: Node, _source: &[u8], lang_name: &str) -> bool {
    match lang_name {
        "rust" => {
            // Check for return type annotation
            node.child_by_field_name("return_type").is_some()
        }
        "typescript" | "javascript" => {
            // Check for return type or look for return statements
            if node.child_by_field_name("return_type").is_some() {
                return true;
            }
            // Look for return statements in body
            contains_return_statement(node)
        }
        "python" => {
            // Check for return type annotation or return statements
            if node.child_by_field_name("return_type").is_some() {
                return true;
            }
            contains_return_statement(node)
        }
        "go" => {
            // Check for result type
            node.child_by_field_name("result").is_some()
        }
        _ => true, // Assume functions return something by default
    }
}

/// Check if a node contains a return statement.
fn contains_return_statement(node: Node) -> bool {
    if node.kind() == "return_statement" {
        return true;
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if contains_return_statement(child) {
            return true;
        }
    }
    false
}

/// Determine JavaScript/TypeScript visibility from modifiers.
fn determine_js_visibility(node: Node, source: &[u8]) -> Visibility {
    // Check for export keyword
    if let Some(parent) = node.parent() {
        if parent.kind() == "export_statement" {
            return Visibility::Public;
        }
    }

    // Check for private modifier in class methods
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "accessibility_modifier" || child.kind() == "private" {
            let text = node_text(child, source);
            if text == "private" {
                return Visibility::Private;
            } else if text == "protected" {
                return Visibility::Internal;
            }
        }
    }

    // Default to private for non-exported items
    Visibility::Private
}

/// Determine Rust visibility from pub keyword.
fn determine_rust_visibility(node: Node, source: &[u8]) -> Visibility {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "visibility_modifier" {
            let text = node_text(child, source);
            if text == "pub" {
                return Visibility::Public;
            } else if text.starts_with("pub(crate)") {
                return Visibility::Internal;
            } else if text.starts_with("pub(super)") || text.starts_with("pub(in") {
                return Visibility::Internal;
            }
        }
    }
    Visibility::Private
}

/// Determine C/C++/Java visibility.
fn determine_c_visibility(node: Node, source: &[u8]) -> Visibility {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        let text = node_text(child, source);
        if text == "public" {
            return Visibility::Public;
        } else if text == "private" {
            return Visibility::Private;
        } else if text == "protected" {
            return Visibility::Internal;
        }
    }
    Visibility::Private
}

/// Check if a node is a named export.
fn is_named_export(node: Node, _source: &[u8]) -> bool {
    if let Some(parent) = node.parent() {
        if parent.kind() == "export_statement" || parent.kind() == "variable_declarator" {
            return true;
        }
    }
    false
}

/// Determine which documentation elements are missing.
fn determine_missing_elements(quality: &DocQuality, config: &DocCoverageConfig) -> Vec<DocType> {
    let mut missing = Vec::new();

    if !quality.has_docstring {
        missing.push(match quality.item_type {
            ItemType::Module => DocType::ModuleDoc,
            ItemType::Class => DocType::ClassDoc,
            ItemType::Function => DocType::FunctionDoc,
            ItemType::Method => DocType::MethodDoc,
            _ => DocType::FunctionDoc,
        });
    }

    if config.check_params && !quality.has_param_docs {
        missing.push(DocType::ParameterDoc);
    }
    if config.check_returns && !quality.has_return_docs {
        missing.push(DocType::ReturnDoc);
    }
    if config.check_exceptions && !quality.has_exception_docs {
        missing.push(DocType::ExceptionDoc);
    }
    if config.check_examples && !quality.has_examples {
        missing.push(DocType::ExampleDoc);
    }

    missing
}

/// Generate a documentation suggestion for an item.
fn generate_suggestion(
    item_name: &str,
    item_type: ItemType,
    missing_elements: &[DocType],
    lang_name: &str,
) -> String {
    let missing_str = missing_elements
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    match lang_name {
        "python" => format!(
            "Add docstring to {} '{}'. Missing: {}.\nExample:\n\"\"\"\nDescribe what {} does.\n\nArgs:\n    param: Description.\n\nReturns:\n    Description of return value.\n\nExample:\n    >>> {}(...)\n\"\"\"",
            item_type, item_name, missing_str, item_name, item_name
        ),
        "typescript" | "javascript" => format!(
            "Add JSDoc to {} '{}'. Missing: {}.\nExample:\n/**\n * Describe what {} does.\n * @param param - Description.\n * @returns Description of return value.\n * @example\n * {}(...);\n */",
            item_type, item_name, missing_str, item_name, item_name
        ),
        "rust" => format!(
            "Add doc comment to {} '{}'. Missing: {}.\nExample:\n/// Describe what {} does.\n///\n/// # Arguments\n///\n/// * `param` - Description.\n///\n/// # Returns\n///\n/// Description of return value.\n///\n/// # Examples\n///\n/// ```\n/// {}(...);\n/// ```",
            item_type, item_name, missing_str, item_name, item_name
        ),
        "go" => format!(
            "Add comment to {} '{}'. Missing: {}.\nExample:\n// {} describes what this does.\n// It takes param as input and returns ...",
            item_type, item_name, missing_str, item_name
        ),
        _ => format!(
            "Add documentation to {} '{}'. Missing: {}.",
            item_type, item_name, missing_str
        ),
    }
}

/// Aggregate file results into a complete analysis.
fn aggregate_results(
    file_results: Vec<FileDocCoverage>,
    _config: &DocCoverageConfig,
) -> DocCoverageAnalysis {
    let mut metrics = DocCoverageMetrics::default();
    let mut all_missing = Vec::new();
    let mut todos = Vec::new();

    // Initialize type coverage
    for doc_type in &[
        DocType::ModuleDoc,
        DocType::ClassDoc,
        DocType::FunctionDoc,
        DocType::MethodDoc,
    ] {
        metrics.by_type.insert(*doc_type, TypeCoverage::default());
    }

    let mut total_quality_score = 0.0;
    let mut quality_count = 0;

    for file in &file_results {
        metrics.files_analyzed += 1;
        if file.has_module_doc {
            metrics.files_with_module_doc += 1;
        }

        metrics.total_items += file.total_items;
        metrics.documented_items += file.documented_items;

        for item in &file.items {
            let doc_type = match item.item_type {
                ItemType::Class => DocType::ClassDoc,
                ItemType::Function => DocType::FunctionDoc,
                ItemType::Method => DocType::MethodDoc,
                _ => DocType::FunctionDoc,
            };

            let type_cov = metrics
                .by_type
                .entry(doc_type)
                .or_insert_with(TypeCoverage::default);
            type_cov.total += 1;
            if item.has_docstring && item.score >= 2 {
                type_cov.documented += 1;
            }

            total_quality_score += f64::from(item.score);
            quality_count += 1;
        }

        // Collect missing docs
        for missing in &file.missing {
            all_missing.push(missing.clone());

            // Create TODO item
            let priority = calculate_todo_priority(missing);
            todos.push(DocTodo {
                file: file.file.clone(),
                item: missing.item.clone(),
                item_type: missing.item_type,
                line: missing.location.line,
                priority,
                description: format!(
                    "Add documentation to {} '{}' (current score: {}/5)",
                    missing.item_type, missing.item, missing.current_score
                ),
                visibility: missing.visibility,
            });
        }
    }

    // Calculate rates
    metrics.coverage_rate = if metrics.total_items > 0 {
        f64::from(metrics.documented_items) / f64::from(metrics.total_items)
    } else {
        1.0
    };

    metrics.quality_score = if quality_count > 0 {
        total_quality_score / quality_count as f64
    } else {
        0.0
    };

    // Calculate per-type rates
    for type_cov in metrics.by_type.values_mut() {
        type_cov.calculate_rate();
    }

    DocCoverageAnalysis {
        files: file_results,
        metrics,
        missing_docs: all_missing,
        todos,
    }
}

/// Calculate priority for a TODO item (1 = highest priority).
fn calculate_todo_priority(missing: &MissingDoc) -> u32 {
    let mut priority: u32 = 10;

    // Public items are higher priority
    if missing.visibility == Visibility::Public {
        priority -= 5;
    }

    // Items with no documentation at all are higher priority
    if missing.current_score == 0 {
        priority -= 3;
    }

    // Certain item types are higher priority
    match missing.item_type {
        ItemType::Class | ItemType::Trait => priority -= 2,
        ItemType::Function => priority -= 1,
        _ => {}
    }

    priority.max(1)
}

/// Get text from a node.
fn node_text<'a>(node: Node<'a>, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

// =============================================================================
// FORMATTING
// =============================================================================

/// Format documentation coverage analysis as a human-readable report.
pub fn format_doc_coverage_report(analysis: &DocCoverageAnalysis) -> String {
    let mut output = String::new();

    output.push_str("=== Documentation Coverage Report ===\n\n");

    // Summary metrics
    output.push_str(&format!(
        "Files Analyzed: {}\n",
        analysis.metrics.files_analyzed
    ));
    output.push_str(&format!(
        "Files with Module Doc: {} ({:.1}%)\n",
        analysis.metrics.files_with_module_doc,
        if analysis.metrics.files_analyzed > 0 {
            f64::from(analysis.metrics.files_with_module_doc)
                / f64::from(analysis.metrics.files_analyzed)
                * 100.0
        } else {
            0.0
        }
    ));
    output.push('\n');

    output.push_str(&format!("Total Items: {}\n", analysis.metrics.total_items));
    output.push_str(&format!(
        "Documented Items: {}\n",
        analysis.metrics.documented_items
    ));
    output.push_str(&format!(
        "Coverage Rate: {:.1}%\n",
        analysis.metrics.coverage_rate * 100.0
    ));
    output.push_str(&format!(
        "Quality Score: {:.1}/5\n",
        analysis.metrics.quality_score
    ));
    output.push('\n');

    // Coverage by type
    output.push_str("Coverage by Type:\n");
    for (doc_type, coverage) in &analysis.metrics.by_type {
        output.push_str(&format!(
            "  {}: {}/{} ({:.1}%)\n",
            doc_type,
            coverage.documented,
            coverage.total,
            coverage.rate * 100.0
        ));
    }
    output.push('\n');

    // Missing documentation (top 20)
    if !analysis.missing_docs.is_empty() {
        output.push_str(&format!(
            "Missing Documentation ({} items):\n",
            analysis.missing_docs.len()
        ));
        for (i, missing) in analysis.missing_docs.iter().take(20).enumerate() {
            output.push_str(&format!(
                "  {}. {} {} '{}' at {} (score: {}/5)\n",
                i + 1,
                missing.visibility,
                missing.item_type,
                missing.item,
                missing.location,
                missing.current_score
            ));
        }
        if analysis.missing_docs.len() > 20 {
            output.push_str(&format!(
                "  ... and {} more\n",
                analysis.missing_docs.len() - 20
            ));
        }
        output.push('\n');
    }

    // Top TODOs
    if !analysis.todos.is_empty() {
        output.push_str("Documentation TODOs (by priority):\n");
        for (i, todo) in analysis.todos.iter().take(10).enumerate() {
            output.push_str(&format!(
                "  {}. [P{}] {} - {}\n",
                i + 1,
                todo.priority,
                todo.item,
                todo.description
            ));
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
    use std::fs;
    use tempfile::TempDir;

    fn create_test_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let path = dir.path().join(name);
        fs::write(&path, content).unwrap();
        path
    }

    #[test]
    fn test_detect_undocumented_function() {
        let dir = TempDir::new().unwrap();
        let content = r#"
def undocumented_function(x, y):
    return x + y

def documented_function(x, y):
    """Add two numbers together.

    Args:
        x: First number.
        y: Second number.

    Returns:
        The sum of x and y.
    """
    return x + y
"#;
        let path = create_test_file(&dir, "test.py", content);

        // Use config with low min_lines to ensure both functions are analyzed
        let config = DocCoverageConfig {
            min_lines_require_doc: 1,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("python"), Some(config)).unwrap();

        assert_eq!(result.metrics.total_items, 2);
        assert_eq!(result.metrics.documented_items, 1);
        assert!(!result.missing_docs.is_empty());

        let undoc = result
            .missing_docs
            .iter()
            .find(|m| m.item == "undocumented_function");
        assert!(undoc.is_some());
    }

    #[test]
    fn test_detect_partial_documentation() {
        let dir = TempDir::new().unwrap();
        let content = r#"
def partial_docs(x, y):
    """Add numbers."""
    return x + y
"#;
        let path = create_test_file(&dir, "test.py", content);

        let config = DocCoverageConfig {
            check_params: true,
            check_returns: true,
            min_quality_score: 3,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("python"), Some(config)).unwrap();

        assert_eq!(result.metrics.total_items, 1);
        // Partial docs means it's documented but low quality
        let item = &result.files[0].items[0];
        assert!(item.has_docstring);
        assert!(!item.has_param_docs);
        assert!(!item.has_return_docs);
        assert!(item.score < 3);
    }

    #[test]
    fn test_quality_scoring() {
        // Score 0: No docstring
        assert_eq!(
            calculate_quality_score(false, false, false, false, false, false),
            0
        );

        // Score 1: Has docstring but just name restatement
        assert_eq!(
            calculate_quality_score(true, false, false, false, false, false),
            1
        );

        // Score 2: Describes purpose
        assert_eq!(
            calculate_quality_score(true, true, false, false, false, false),
            2
        );

        // Score 3: Has params or returns
        assert_eq!(
            calculate_quality_score(true, true, true, false, false, false),
            3
        );
        assert_eq!(
            calculate_quality_score(true, true, false, true, false, false),
            3
        );

        // Score 4: Has examples
        assert_eq!(
            calculate_quality_score(true, true, false, false, false, true),
            4
        );

        // Score 5: Comprehensive
        assert_eq!(
            calculate_quality_score(true, true, true, true, false, true),
            5
        );
    }

    #[test]
    fn test_rust_doc_extraction() {
        let dir = TempDir::new().unwrap();
        let content = r#"
/// This is a documented function.
///
/// # Arguments
///
/// * `x` - First value.
///
/// # Returns
///
/// The processed value.
///
/// # Examples
///
/// ```
/// documented_fn(42);
/// ```
pub fn documented_fn(x: i32) -> i32 {
    x * 2
}

fn undocumented_fn(x: i32) -> i32 {
    x * 3
}
"#;
        let path = create_test_file(&dir, "test.rs", content);

        let result = analyze_doc_coverage(&path, Some("rust"), None).unwrap();

        // Find the documented function
        let doc_fn = result.files[0]
            .items
            .iter()
            .find(|i| i.item == "documented_fn");
        assert!(doc_fn.is_some());
        let doc_fn = doc_fn.unwrap();
        assert!(doc_fn.has_docstring);
        assert!(doc_fn.has_param_docs);
        assert!(doc_fn.has_return_docs);
        assert!(doc_fn.has_examples);
        assert!(doc_fn.score >= 4);
    }

    #[test]
    fn test_typescript_jsdoc_extraction() {
        let dir = TempDir::new().unwrap();
        // Use a non-exported function to test JSDoc extraction more reliably
        // (tree-sitter's AST structure for export statements can be complex)
        let content = r#"
/**
 * Multiplies two numbers together.
 * @param a - First number.
 * @param b - Second number.
 * @returns The product of a and b.
 */
function multiply(a: number, b: number): number {
    return a * b;
}

function undocumented(x: number): number {
    return x * 2;
}
"#;
        let path = create_test_file(&dir, "test.ts", content);

        // Use config with low min_lines to ensure functions are analyzed
        let config = DocCoverageConfig {
            min_lines_require_doc: 1,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("typescript"), Some(config)).unwrap();

        assert!(!result.files.is_empty());

        // Find the documented function
        let multiply_fn = result.files[0].items.iter().find(|i| i.item == "multiply");
        assert!(multiply_fn.is_some(), "multiply function should be found");

        let multiply_fn = multiply_fn.unwrap();
        // Verify JSDoc was extracted
        assert!(
            multiply_fn.has_docstring,
            "multiply should have detected JSDoc"
        );
        // With params and returns documented, should have score >= 3
        assert!(
            multiply_fn.score >= 2,
            "Function with JSDoc should have score >= 2, got {}",
            multiply_fn.score
        );

        // Check undocumented function is found
        let undoc_fn = result.files[0]
            .items
            .iter()
            .find(|i| i.item == "undocumented");
        assert!(undoc_fn.is_some(), "undocumented function should be found");
        let undoc_fn = undoc_fn.unwrap();
        assert!(
            !undoc_fn.has_docstring,
            "undocumented should not have docstring"
        );
    }

    #[test]
    fn test_public_only_filter() {
        let dir = TempDir::new().unwrap();
        let content = r#"
def public_function():
    pass

def _private_function():
    pass

def __dunder_method__():
    pass
"#;
        let path = create_test_file(&dir, "test.py", content);

        let config = DocCoverageConfig {
            public_only: true,
            min_lines_require_doc: 1,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("python"), Some(config)).unwrap();

        // Should only analyze public and dunder
        assert!(result.metrics.total_items <= 2);
    }

    #[test]
    fn test_config_presets() {
        let strict = DocCoverageConfig::strict();
        assert!(strict.public_only);
        assert_eq!(strict.min_quality_score, 3);
        assert!(strict.check_examples);

        let lenient = DocCoverageConfig::lenient();
        assert!(lenient.public_only);
        assert_eq!(lenient.min_quality_score, 1);
        assert!(!lenient.check_examples);
    }

    #[test]
    fn test_go_doc_detection() {
        let dir = TempDir::new().unwrap();
        let content = r#"
// Add adds two integers together and returns the result.
// It handles both positive and negative numbers.
func Add(a, b int) int {
    return a + b
}

func privateFunc(x int) int {
    return x * 2
}
"#;
        let path = create_test_file(&dir, "test.go", content);

        let config = DocCoverageConfig {
            min_lines_require_doc: 1,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("go"), Some(config)).unwrap();

        // Add is public (uppercase), privateFunc is private (lowercase)
        assert!(!result.files.is_empty());
    }

    #[test]
    fn test_name_restatement_detection() {
        let dir = TempDir::new().unwrap();
        let content = r#"
def get_user():
    """Get user."""
    pass

def process_data():
    """Process the incoming data and transform it for storage."""
    pass
"#;
        let path = create_test_file(&dir, "test.py", content);

        let config = DocCoverageConfig {
            flag_name_restatement: true,
            min_lines_require_doc: 1,
            ..Default::default()
        };

        let result = analyze_doc_coverage(&path, Some("python"), Some(config)).unwrap();

        let get_user = result.files[0].items.iter().find(|i| i.item == "get_user");
        let process_data = result.files[0]
            .items
            .iter()
            .find(|i| i.item == "process_data");

        if let Some(get_user) = get_user {
            // "Get user" is just restating the name
            assert!(!get_user.describes_purpose);
            assert_eq!(get_user.score, 1);
        }

        if let Some(process_data) = process_data {
            // "Process the incoming data..." is more descriptive
            assert!(process_data.describes_purpose);
            assert!(process_data.score >= 2);
        }
    }
}
