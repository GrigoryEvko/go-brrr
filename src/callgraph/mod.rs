//! Cross-file call graph analysis.
//!
//! Builds a project-wide call graph by scanning all source files,
//! indexing function definitions, and resolving call sites.
//!
//! # Components
//!
//! - [`scanner`] - Project file discovery with filtering and metadata
//! - [`indexer`] - Function definition indexing
//! - [`resolver`] - Call site resolution to build the graph
//! - [`impact`] - Reverse call graph analysis (who calls X?)
//! - [`dead`] - Dead code detection
//!
//! # Example: Impact Analysis
//!
//! ```ignore
//! use go_brrr::callgraph::{build, impact::{analyze_impact, ImpactConfig}};
//!
//! let graph = build("/path/to/project")?;
//! let config = ImpactConfig::new()
//!     .with_depth(5)
//!     .exclude_tests();
//!
//! let result = analyze_impact(&graph, "process_data", config);
//! println!("{}", result.to_llm_context());
//! ```

pub mod arch;
pub mod cache;
pub mod dead;
pub mod impact;
pub mod indexer;
pub mod resolver;
pub mod scanner;
pub mod types;

// Re-exports for the crate's public API (used by lib.rs)
#[allow(unused_imports)]
pub use arch::{analyze_architecture, ArchAnalysis, ArchStats, CycleDependency};
#[allow(unused_imports)]
pub use cache::{
    get_cache_dir, get_cache_file, get_or_build_graph_with_config, invalidate_cache,
    warm_cache_with_config, CachedCallGraph, CachedEdge,
};
#[allow(unused_imports)]
pub use dead::{
    analyze_dead_code, analyze_dead_code_with_config, classify_entry_point,
    detect_entry_points_with_config, DeadCodeConfig, DeadCodeResult, DeadCodeStats, DeadFunction,
    DeadReason, EntryPointKind,
};
#[allow(unused_imports)]
pub use impact::{analyze_impact, CallerInfo, ImpactConfig, ImpactResult};
#[allow(unused_imports)]
pub use indexer::{FunctionDef, FunctionIndex, IndexStats};
#[allow(unused_imports)]
pub use scanner::{
    ErrorHandling, FileMetadata, ProjectScanner, ScanConfig, ScanError, ScanErrorKind, ScanResult,
};
#[allow(unused_imports)]
pub use types::{CallEdge, CallGraph, FunctionRef};

use crate::error::Result;

/// Build call graph for a project.
///
/// # Arguments
///
/// * `path` - Path to the project root
///
/// # Returns
///
/// A call graph containing function definitions and call edges.
pub fn build(path: &str) -> Result<CallGraph> {
    build_with_config(path, None, false)
}

/// Build call graph for a project with configuration options.
///
/// # Arguments
///
/// * `path` - Path to the project root
/// * `lang` - Optional language filter (e.g., "python", "rust")
/// * `no_ignore` - Whether to ignore .gitignore/.brrrignore patterns
///
/// # Returns
///
/// A call graph containing function definitions and call edges.
pub fn build_with_config(path: &str, lang: Option<&str>, no_ignore: bool) -> Result<CallGraph> {
    let project_root = std::path::Path::new(path);
    let scanner = scanner::ProjectScanner::new(path)?;

    // Configure scanning with no_ignore and language filters
    let mut config = match lang {
        Some(l) if l != "all" => ScanConfig::for_language(l),
        _ => ScanConfig::default(),
    };
    config.no_ignore = no_ignore;

    let scan_result = scanner.scan_with_config(&config)?;
    let files = scan_result.files;
    let index = indexer::FunctionIndex::build(&files)?;
    let graph = resolver::resolve_calls(&files, &index, project_root)?;
    Ok(graph)
}

/// Build call graph with function index for detailed lookups.
///
/// Returns both the call graph and the function index, useful when
/// you need to look up function details after traversing the graph.
#[allow(dead_code)]
pub fn build_with_index(path: &str) -> Result<(CallGraph, FunctionIndex)> {
    let project_root = std::path::Path::new(path);
    let scanner = scanner::ProjectScanner::new(path)?;
    let files = scanner.scan_files()?;
    let index = indexer::FunctionIndex::build(&files)?;
    let graph = resolver::resolve_calls(&files, &index, project_root)?;
    Ok((graph, index))
}

/// Context information for a single function in the LLM context output.
#[derive(Debug, Clone, serde::Serialize)]
pub struct FunctionContextInfo {
    /// Function name
    pub name: String,
    /// File path containing the function
    pub file: String,
    /// Starting line number (1-indexed)
    pub line: usize,
    /// Function signature
    pub signature: String,
    /// Docstring if available
    pub docstring: Option<String>,
    /// Functions this function calls
    pub calls: Vec<String>,
}

/// Get LLM-ready context for an entry point with optional language filter.
///
/// This variant allows specifying a language to filter files.
///
/// # Arguments
///
/// * `project` - Project root path
/// * `entry_point` - Entry function name
/// * `depth` - Call graph depth
/// * `lang` - Optional language filter (e.g., "python", "rust")
pub fn get_context_with_lang(
    project: &str,
    entry_point: &str,
    depth: usize,
    lang: Option<&str>,
) -> Result<serde_json::Value> {
    use crate::ast::extractor::AstExtractor;
    use std::collections::{HashMap, HashSet};
    use std::path::Path;

    let project_root = std::path::Path::new(project);
    let scanner = scanner::ProjectScanner::new(project)?;

    // Use language-filtered scan if language is specified
    let files = match lang {
        Some(lang_str) => {
            let config = scanner::ScanConfig::for_language(lang_str);
            scanner.scan_with_config(&config)?.files
        }
        None => scanner.scan_files()?,
    };

    let index = indexer::FunctionIndex::build(&files)?;
    let mut graph = resolver::resolve_calls(&files, &index, project_root)?;
    graph.build_indexes();

    // Find the entry point function
    let entry_target = FunctionRef {
        file: String::new(),
        name: entry_point.to_string(),
        qualified_name: None,
    };

    // Get all callees up to depth
    let callees = graph.get_callees(&entry_target, depth);

    // Include entry point itself if found
    let mut all_funcs: Vec<FunctionRef> = Vec::new();

    // Find the entry point in the graph (uses cached all_functions)
    let entry_found = graph
        .all_functions()
        .iter()
        .find(|f| f.name == entry_point || f.qualified_name.as_deref() == Some(entry_point));

    if let Some(entry_func) = entry_found {
        all_funcs.push(entry_func.clone());
    }

    // Add callees (deduped)
    let mut seen: HashSet<String> = HashSet::new();
    for func in &all_funcs {
        seen.insert(func.name.clone());
    }
    for callee in callees {
        if seen.insert(callee.name.clone()) {
            all_funcs.push(callee);
        }
    }

    // Cache parsed modules to avoid re-parsing same files
    let mut module_cache: HashMap<String, crate::ast::types::ModuleInfo> = HashMap::new();

    // Build detailed function context for each function
    let mut function_contexts: Vec<FunctionContextInfo> = Vec::new();

    for func_ref in &all_funcs {
        // Skip functions with no file (unresolved references)
        if func_ref.file.is_empty() {
            function_contexts.push(FunctionContextInfo {
                name: func_ref
                    .qualified_name
                    .clone()
                    .unwrap_or_else(|| func_ref.name.clone()),
                file: "?".to_string(),
                line: 0,
                signature: format!("def {}(...)", func_ref.name),
                docstring: None,
                calls: graph
                    .callees
                    .get(func_ref)
                    .map(|c| c.iter().map(|f| f.name.clone()).collect())
                    .unwrap_or_default(),
            });
            continue;
        }

        // Parse the file if not cached
        let module_info = if let Some(cached) = module_cache.get(&func_ref.file) {
            cached.clone()
        } else {
            match AstExtractor::extract_file(Path::new(&func_ref.file)) {
                Ok(info) => {
                    module_cache.insert(func_ref.file.clone(), info.clone());
                    info
                }
                Err(_) => {
                    // File couldn't be parsed, use basic info
                    function_contexts.push(FunctionContextInfo {
                        name: func_ref
                            .qualified_name
                            .clone()
                            .unwrap_or_else(|| func_ref.name.clone()),
                        file: func_ref.file.clone(),
                        line: 0,
                        signature: format!("def {}(...)", func_ref.name),
                        docstring: None,
                        calls: graph
                            .callees
                            .get(func_ref)
                            .map(|c| c.iter().map(|f| f.name.clone()).collect())
                            .unwrap_or_default(),
                    });
                    continue;
                }
            }
        };

        // Find the function in the module (check both functions and class methods)
        let func_info: Option<&crate::ast::types::FunctionInfo> = module_info
            .functions
            .iter()
            .find(|f| f.name == func_ref.name)
            .or_else(|| {
                // Check class methods
                module_info.classes.iter().find_map(|c| {
                    c.methods.iter().find(|m| {
                        m.name == func_ref.name || func_ref.name == format!("{}.{}", c.name, m.name)
                    })
                })
            });

        let (signature, docstring, line) = if let Some(info) = func_info {
            (info.signature(), info.docstring.clone(), info.line_number)
        } else {
            // Try looking up in index for line number
            let line = index
                .get_definition(func_ref.qualified_name.as_deref().unwrap_or(&func_ref.name))
                .map(|d| d.line_number)
                .unwrap_or(0);
            (format!("def {}(...)", func_ref.name), None, line)
        };

        // Get calls from graph
        let calls: Vec<String> = graph
            .callees
            .get(func_ref)
            .map(|c| c.iter().map(|f| f.name.clone()).collect())
            .unwrap_or_default();

        function_contexts.push(FunctionContextInfo {
            name: func_ref
                .qualified_name
                .clone()
                .unwrap_or_else(|| func_ref.name.clone()),
            file: func_ref.file.clone(),
            line,
            signature,
            docstring,
            calls,
        });
    }

    // Build LLM-ready text (matching Python's to_llm_string format)
    let mut llm_context = String::new();
    llm_context.push_str(&format!(
        "## Code Context: {} (depth={})\n\n",
        entry_point, depth
    ));

    for (i, func) in function_contexts.iter().enumerate() {
        // Indentation based on call depth (approximate)
        let indent_level = i.min(depth);
        let indent = "  ".repeat(indent_level);

        // Function header with file:line
        let short_file = Path::new(&func.file)
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("?");
        llm_context.push_str(&format!(
            "{}* {} ({}:{})\n",
            indent, func.name, short_file, func.line
        ));
        llm_context.push_str(&format!("{}   {}\n", indent, func.signature));

        // Docstring (first line, truncated)
        if let Some(ref doc) = func.docstring {
            let first_line: &str = doc.lines().next().unwrap_or("");
            let truncated = if first_line.len() > 80 {
                &first_line[..77]
            } else {
                first_line
            };
            if !truncated.is_empty() {
                llm_context.push_str(&format!("{}   # {}\n", indent, truncated));
            }
        }

        // Calls (first 5, with overflow indicator)
        if !func.calls.is_empty() {
            let calls_str = if func.calls.len() > 5 {
                format!(
                    "{} (+{} more)",
                    func.calls[..5].join(", "),
                    func.calls.len() - 5
                )
            } else {
                func.calls.join(", ")
            };
            llm_context.push_str(&format!("{}   -> calls: {}\n", indent, calls_str));
        }

        llm_context.push('\n');
    }

    // Build JSON output with llm_context field
    Ok(serde_json::json!({
        "entry_point": entry_point,
        "project": project,
        "depth": depth,
        "function_count": function_contexts.len(),
        "functions": function_contexts.iter().map(|f| serde_json::json!({
            "name": f.name,
            "file": f.file,
            "line": f.line,
            "signature": f.signature,
            "docstring": f.docstring,
            "calls": f.calls,
        })).collect::<Vec<_>>(),
        "llm_context": llm_context,
    }))
}
