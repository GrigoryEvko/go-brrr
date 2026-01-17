//! Incremental call graph caching.
//!
//! Provides persistent caching of call graphs with incremental updates:
//! - Caches graphs to `.brrr/cache/call_graph.json` for fast repeated queries
//! - Detects dirty files by comparing content hashes
//! - Applies incremental patches instead of full rebuilds when possible
//!
//! This module mirrors the Python implementation's `_get_or_build_graph()`
//! function from `cli.py`, ensuring consistent behavior across both backends.
//!
//! # Cache Format
//!
//! The cache file is a JSON object with the following structure:
//! ```json
//! {
//!   "edges": [...],
//!   "file_hashes": {"path/to/file.py": 12345678901234567890, ...},
//!   "languages": ["python"],
//!   "timestamp": 1234567890.123
//! }
//! ```
//!
//! # Incremental Updates
//!
//! When files are modified:
//! 1. Detect dirty files by comparing content hashes
//! 2. Remove old edges involving dirty files
//! 3. Re-parse only the dirty files
//! 4. Merge new edges into the graph
//! 5. Update cache with new hashes

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use tracing::{debug, info, warn};

use crate::callgraph::indexer::FunctionIndex;
use crate::callgraph::resolver;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::callgraph::types::{CallEdge, CallGraph, FunctionRef};
use crate::error::{Result, BrrrError};

// =============================================================================
// Cache Types
// =============================================================================

/// Cached call graph with metadata for incremental updates.
///
/// Stores the serialized graph edges along with file content hashes
/// to detect modifications since the last build.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedCallGraph {
    /// Call graph edges in serializable format.
    pub edges: Vec<CachedEdge>,
    /// Map of file paths to their content hashes.
    /// Used to detect which files have changed since last cache.
    #[serde(default)]
    pub file_hashes: HashMap<String, u64>,
    /// Languages included in this cache.
    #[serde(default)]
    pub languages: Vec<String>,
    /// Unix timestamp when cache was created.
    #[serde(default)]
    pub timestamp: f64,
}

/// Serializable representation of a call edge.
///
/// Simplified structure that matches the Python cache format.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CachedEdge {
    pub from_file: String,
    pub from_func: String,
    pub to_file: String,
    pub to_func: String,
    #[serde(default)]
    pub call_line: usize,
}

impl CachedEdge {
    /// Convert from CallEdge to CachedEdge.
    pub fn from_edge(edge: &CallEdge) -> Self {
        Self {
            from_file: edge.caller.file.clone(),
            from_func: edge.caller.name.clone(),
            to_file: edge.callee.file.clone(),
            to_func: edge.callee.name.clone(),
            call_line: edge.call_line,
        }
    }

    /// Convert to CallEdge.
    pub fn to_edge(&self) -> CallEdge {
        CallEdge {
            caller: FunctionRef {
                file: self.from_file.clone(),
                name: self.from_func.clone(),
                qualified_name: None,
            },
            callee: FunctionRef {
                file: self.to_file.clone(),
                name: self.to_func.clone(),
                qualified_name: None,
            },
            call_line: self.call_line,
        }
    }
}

// =============================================================================
// Cache Operations
// =============================================================================

/// Get the cache directory for a project.
pub fn get_cache_dir(project: &Path) -> PathBuf {
    project.join(".brrr").join("cache")
}

/// Get the cache file path for a project.
pub fn get_cache_file(project: &Path) -> PathBuf {
    get_cache_dir(project).join("call_graph.json")
}

/// Load cached call graph from disk.
///
/// Returns `None` if cache doesn't exist or is invalid.
pub fn load_cached_graph(project: &Path) -> Option<CachedCallGraph> {
    let cache_file = get_cache_file(project);

    if !cache_file.exists() {
        debug!("Cache file not found: {}", cache_file.display());
        return None;
    }

    let content = match fs::read_to_string(&cache_file) {
        Ok(c) => c,
        Err(e) => {
            warn!("Failed to read cache file: {}", e);
            return None;
        }
    };

    match serde_json::from_str(&content) {
        Ok(cached) => Some(cached),
        Err(e) => {
            warn!("Failed to parse cache file: {}", e);
            None
        }
    }
}

/// Save cached call graph to disk.
///
/// Creates the cache directory if it doesn't exist.
pub fn save_cached_graph(project: &Path, cached: &CachedCallGraph) -> Result<()> {
    let cache_dir = get_cache_dir(project);
    let cache_file = get_cache_file(project);

    // Ensure cache directory exists
    if !cache_dir.exists() {
        fs::create_dir_all(&cache_dir).map_err(|e| {
            BrrrError::Cache(format!(
                "Failed to create cache directory {}: {}",
                cache_dir.display(),
                e
            ))
        })?;
    }

    // Serialize with pretty printing for human readability
    let content = serde_json::to_string_pretty(cached).map_err(|e| {
        BrrrError::Cache(format!("Failed to serialize cache: {}", e))
    })?;

    fs::write(&cache_file, content).map_err(|e| {
        BrrrError::Cache(format!(
            "Failed to write cache file {}: {}",
            cache_file.display(),
            e
        ))
    })?;

    debug!("Saved cache to: {}", cache_file.display());
    Ok(())
}

// =============================================================================
// Hash Computation
// =============================================================================

/// Compute a hash for file content.
///
/// Uses `DefaultHasher` which provides fast, deterministic hashing
/// suitable for change detection (not cryptographic security).
pub fn compute_content_hash(content: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    content.hash(&mut hasher);
    hasher.finish()
}

/// Compute hashes for a list of file paths.
pub fn compute_hashes_for_files(files: &[PathBuf]) -> HashMap<String, u64> {
    let mut hashes = HashMap::new();

    for file_path in files {
        if let Ok(content) = fs::read_to_string(file_path) {
            let hash = compute_content_hash(&content);
            if let Some(path_str) = file_path.to_str() {
                hashes.insert(path_str.to_string(), hash);
            }
        }
    }

    hashes
}

// =============================================================================
// Dirty File Detection
// =============================================================================

/// Find files that have changed since the cache was created.
///
/// Compares current file hashes against cached hashes to identify:
/// - Modified files (hash changed)
/// - New files (not in cache)
/// - Deleted files (in cache but no longer exist)
pub fn find_dirty_files(
    _project: &Path,
    cached_hashes: &HashMap<String, u64>,
    current_files: &[PathBuf],
) -> Vec<PathBuf> {
    let mut dirty = Vec::new();

    // Check each current file against cache
    for file_path in current_files {
        let path_str = match file_path.to_str() {
            Some(s) => s,
            None => continue,
        };

        // Read current content and compute hash
        let current_hash = match fs::read_to_string(file_path) {
            Ok(content) => compute_content_hash(&content),
            Err(_) => continue, // Skip unreadable files
        };

        // Compare against cached hash
        match cached_hashes.get(path_str) {
            Some(&cached_hash) if cached_hash == current_hash => {
                // File unchanged
            }
            _ => {
                // File is new or modified
                dirty.push(file_path.clone());
            }
        }
    }

    // Note: We don't need to explicitly track deleted files here
    // because their edges will be filtered out when we use the graph.
    // The incremental update will naturally exclude deleted file edges.

    dirty
}

// =============================================================================
// Incremental Updates
// =============================================================================

/// Apply incremental update to a graph for dirty files.
///
/// This function:
/// 1. Removes old edges involving dirty files
/// 2. Re-parses only the dirty files
/// 3. Merges new edges into the graph
///
/// # Arguments
///
/// * `graph` - The existing call graph to update
/// * `dirty_files` - Files that need to be re-parsed
/// * `project` - Project root directory
/// * `lang` - Optional language filter
///
/// # Returns
///
/// Updated call graph with new edges for dirty files.
pub fn apply_incremental_update(
    graph: &mut CallGraph,
    dirty_files: &[PathBuf],
    project: &Path,
) -> Result<()> {
    if dirty_files.is_empty() {
        return Ok(());
    }

    info!("Applying incremental update for {} dirty files", dirty_files.len());

    // Build set of dirty file paths for efficient lookup
    let dirty_set: HashSet<String> = dirty_files
        .iter()
        .filter_map(|p| p.to_str().map(String::from))
        .collect();

    // Remove old edges involving dirty files
    let original_count = graph.edges.len();
    graph.edges.retain(|edge| {
        !dirty_set.contains(&edge.caller.file) && !dirty_set.contains(&edge.callee.file)
    });
    let removed_count = original_count - graph.edges.len();
    debug!("Removed {} edges from dirty files", removed_count);

    // Build index from remaining files
    // We need to include all existing files to properly resolve cross-file calls
    let mut all_files: Vec<PathBuf> = graph.edges
        .iter()
        .flat_map(|e| {
            let mut files = Vec::new();
            if !e.caller.file.is_empty() {
                files.push(PathBuf::from(&e.caller.file));
            }
            if !e.callee.file.is_empty() {
                files.push(PathBuf::from(&e.callee.file));
            }
            files
        })
        .collect();

    // Add dirty files to the list
    all_files.extend(dirty_files.iter().cloned());

    // Deduplicate
    let unique_files: Vec<PathBuf> = all_files
        .into_iter()
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();

    // Build function index from all files
    let index = FunctionIndex::build(&unique_files)?;

    // Resolve calls for dirty files only
    let new_edges = resolver::resolve_calls(dirty_files, &index, project)?;

    // Merge new edges into graph
    let new_edge_count = new_edges.edges.len();
    graph.edges.extend(new_edges.edges);

    debug!("Added {} new edges from dirty files", new_edge_count);

    // Rebuild indexes for the updated graph
    graph.build_indexes();

    Ok(())
}

// =============================================================================
// Main API
// =============================================================================

/// Get or build a call graph with caching and configuration options.
///
/// # Arguments
///
/// * `project` - Path to the project root
/// * `lang` - Optional language filter (e.g., "python", "rust")
/// * `no_ignore` - Whether to ignore .gitignore/.brrrignore patterns
///
/// # Returns
///
/// A call graph, either loaded from cache or freshly built.
pub fn get_or_build_graph_with_config(
    project: &Path,
    lang: Option<&str>,
    no_ignore: bool,
) -> Result<CallGraph> {
    let project = project.canonicalize().unwrap_or_else(|_| project.to_path_buf());

    // When no_ignore is set, always do fresh build to ensure consistency
    // (cache was built with ignore patterns, but user now wants to include ignored files)
    if no_ignore {
        info!("no_ignore set, building fresh graph without cache");
        return build_and_cache_with_config(&project, lang, no_ignore);
    }

    // Try to load cached graph
    if let Some(cached) = load_cached_graph(&project) {
        // Validate cache language compatibility
        if let Some(requested_lang) = lang {
            if requested_lang != "all"
                && !cached.languages.is_empty()
                && !cached.languages.contains(&requested_lang.to_string())
            {
                info!("Cache language mismatch, rebuilding");
                return build_and_cache_with_config(&project, lang, no_ignore);
            }
        }

        // Scan current project files
        let scanner = ProjectScanner::new(project.to_str().unwrap_or("."))?;
        let mut scan_config = match lang {
            Some(l) if l != "all" => ScanConfig::for_language(l),
            _ => ScanConfig::default(),
        };
        scan_config.no_ignore = no_ignore;
        let scan_result = scanner.scan_with_config(&scan_config)?;

        // Find dirty files
        let dirty_files = find_dirty_files(&project, &cached.file_hashes, &scan_result.files);

        if dirty_files.is_empty() {
            // Cache is fresh, convert to CallGraph
            info!("Cache is fresh, loading {} edges", cached.edges.len());
            let edges: Vec<CallEdge> = cached.edges.iter().map(|e| e.to_edge()).collect();
            let mut graph = CallGraph::from_edges(edges);
            graph.build_indexes();
            return Ok(graph);
        }

        info!("Found {} dirty files, applying incremental update", dirty_files.len());

        // Convert cache to CallGraph
        let edges: Vec<CallEdge> = cached.edges.iter().map(|e| e.to_edge()).collect();
        let mut graph = CallGraph::from_edges(edges);

        // Apply incremental update
        apply_incremental_update(&mut graph, &dirty_files, &project)?;

        // Compute new hashes and update cache
        let new_hashes = compute_hashes_for_files(&scan_result.files);
        let new_cached = CachedCallGraph {
            edges: graph.edges.iter().map(CachedEdge::from_edge).collect(),
            file_hashes: new_hashes,
            languages: cached.languages.clone(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs_f64())
                .unwrap_or(0.0),
        };

        // Save updated cache (non-fatal if it fails)
        if let Err(e) = save_cached_graph(&project, &new_cached) {
            warn!("Failed to save updated cache: {}", e);
        }

        return Ok(graph);
    }

    // No cache or invalid cache - do fresh build
    build_and_cache_with_config(&project, lang, no_ignore)
}

/// Build a fresh call graph with configuration options and save to cache.
fn build_and_cache_with_config(
    project: &Path,
    lang: Option<&str>,
    no_ignore: bool,
) -> Result<CallGraph> {
    info!("Building fresh call graph for {}", project.display());

    // Use the build_with_config function that respects no_ignore
    let graph = crate::callgraph::build_with_config(
        project.to_str().unwrap_or("."),
        lang,
        no_ignore,
    )?;

    // Only save to cache if not in no_ignore mode
    // (cache built with no_ignore would be inconsistent with normal cached graphs)
    if !no_ignore {
        // Scan files to get hashes
        let scanner = ProjectScanner::new(project.to_str().unwrap_or("."))?;
        let mut scan_config = match lang {
            Some(l) if l != "all" => ScanConfig::for_language(l),
            _ => ScanConfig::default(),
        };
        scan_config.no_ignore = no_ignore;
        let scan_result = scanner.scan_with_config(&scan_config)?;
        let file_hashes = compute_hashes_for_files(&scan_result.files);

        // Create cache entry
        let cached = CachedCallGraph {
            edges: graph.edges.iter().map(CachedEdge::from_edge).collect(),
            file_hashes,
            languages: lang.map(|l| vec![l.to_string()]).unwrap_or_default(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs_f64())
                .unwrap_or(0.0),
        };

        // Save cache (non-fatal if it fails)
        if let Err(e) = save_cached_graph(project, &cached) {
            warn!("Failed to save cache: {}", e);
        }
    }

    info!("Built graph with {} edges", graph.edges.len());
    Ok(graph)
}

/// Warm the call graph cache with configuration options.
///
/// # Arguments
///
/// * `project` - Path to the project root
/// * `lang` - Optional language filter (e.g., "python", "rust")
/// * `no_ignore` - Whether to ignore .gitignore/.brrrignore patterns
pub fn warm_cache_with_config(project: &Path, lang: Option<&str>, no_ignore: bool) -> Result<()> {
    let _ = build_and_cache_with_config(project, lang, no_ignore)?;
    Ok(())
}

/// Invalidate the cache for a project.
///
/// Removes the cache file, forcing a fresh build on next query.
#[allow(dead_code)]
pub fn invalidate_cache(project: &Path) -> Result<()> {
    let cache_file = get_cache_file(project);

    if cache_file.exists() {
        fs::remove_file(&cache_file).map_err(|e| {
            BrrrError::Cache(format!(
                "Failed to remove cache file {}: {}",
                cache_file.display(),
                e
            ))
        })?;
        info!("Invalidated cache: {}", cache_file.display());
    }

    Ok(())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_compute_content_hash() {
        let hash1 = compute_content_hash("hello world");
        let hash2 = compute_content_hash("hello world");
        let hash3 = compute_content_hash("hello world!");

        assert_eq!(hash1, hash2);
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn test_cached_edge_conversion() {
        let edge = CallEdge {
            caller: FunctionRef {
                file: "src/main.py".to_string(),
                name: "main".to_string(),
                qualified_name: None,
            },
            callee: FunctionRef {
                file: "src/utils.py".to_string(),
                name: "helper".to_string(),
                qualified_name: None,
            },
            call_line: 10,
        };

        let cached = CachedEdge::from_edge(&edge);
        assert_eq!(cached.from_file, "src/main.py");
        assert_eq!(cached.from_func, "main");
        assert_eq!(cached.to_file, "src/utils.py");
        assert_eq!(cached.to_func, "helper");
        assert_eq!(cached.call_line, 10);

        let back = cached.to_edge();
        assert_eq!(back.caller.file, edge.caller.file);
        assert_eq!(back.caller.name, edge.caller.name);
        assert_eq!(back.callee.file, edge.callee.file);
        assert_eq!(back.callee.name, edge.callee.name);
        assert_eq!(back.call_line, edge.call_line);
    }

    #[test]
    fn test_find_dirty_files_empty_cache() {
        let temp_dir = TempDir::new().unwrap();
        let project = temp_dir.path();

        // Create a test file
        let test_file = project.join("test.py");
        fs::write(&test_file, "def foo(): pass").unwrap();

        // Empty cache hashes - all files should be dirty
        let cached_hashes = HashMap::new();
        let current_files = vec![test_file.clone()];

        let dirty = find_dirty_files(project, &cached_hashes, &current_files);
        assert_eq!(dirty.len(), 1);
        assert_eq!(dirty[0], test_file);
    }

    #[test]
    fn test_find_dirty_files_unchanged() {
        let temp_dir = TempDir::new().unwrap();
        let project = temp_dir.path();

        // Create a test file
        let test_file = project.join("test.py");
        let content = "def foo(): pass";
        fs::write(&test_file, content).unwrap();

        // Cache with matching hash
        let mut cached_hashes = HashMap::new();
        cached_hashes.insert(
            test_file.to_str().unwrap().to_string(),
            compute_content_hash(content),
        );
        let current_files = vec![test_file.clone()];

        let dirty = find_dirty_files(project, &cached_hashes, &current_files);
        assert!(dirty.is_empty());
    }

    #[test]
    fn test_find_dirty_files_modified() {
        let temp_dir = TempDir::new().unwrap();
        let project = temp_dir.path();

        // Create a test file
        let test_file = project.join("test.py");
        let old_content = "def foo(): pass";
        let new_content = "def foo(): return 42";
        fs::write(&test_file, new_content).unwrap();

        // Cache with old hash
        let mut cached_hashes = HashMap::new();
        cached_hashes.insert(
            test_file.to_str().unwrap().to_string(),
            compute_content_hash(old_content),
        );
        let current_files = vec![test_file.clone()];

        let dirty = find_dirty_files(project, &cached_hashes, &current_files);
        assert_eq!(dirty.len(), 1);
        assert_eq!(dirty[0], test_file);
    }

    #[test]
    fn test_cache_file_path() {
        let project = Path::new("/home/user/project");
        let cache_file = get_cache_file(project);
        assert_eq!(
            cache_file,
            PathBuf::from("/home/user/project/.brrr/cache/call_graph.json")
        );
    }
}
