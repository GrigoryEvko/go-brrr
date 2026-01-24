//! File tree generation with proper hierarchical structure.
//!
//! Generates a recursive tree structure from a directory, respecting
//! .gitignore and .brrrignore patterns via the `ignore` crate.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use ignore::WalkBuilder;
use tracing::warn;

use crate::ast::types::FileTreeEntry;
use crate::error::{validate_path_containment, BrrrError, Result};

/// Default maximum directory depth to prevent stack overflow.
/// This is a safety limit for deeply nested directory structures.
/// 100 levels deep should cover any reasonable project structure while
/// preventing stack overflow from malicious or accidental deeply nested dirs.
const DEFAULT_MAX_DEPTH: usize = 100;

/// Default directories to skip during traversal (matches Python DEFAULT_SKIP_DIRS).
const DEFAULT_SKIP_DIRS: &[&str] = &[
    "node_modules",
    "__pycache__",
    ".git",
    ".svn",
    ".hg",
    "dist",
    "build",
    ".next",
    ".nuxt",
    "coverage",
    ".tox",
    "venv",
    ".venv",
    "env",
    ".env",
    "vendor",
    ".cache",
    "target", // Rust build dir
];

/// Generate hierarchical file tree for a directory.
///
/// Respects .gitignore and .brrrignore files by default. Produces a proper nested
/// tree structure suitable for JSON serialization.
///
/// # Arguments
///
/// * `path` - Root directory path to scan
/// * `ext_filter` - Extension filters (e.g., &[".py", ".rs"]). Empty slice means no filter.
/// * `show_hidden` - If true, include hidden files/directories (those starting with '.')
/// * `no_ignore` - If true, bypass .gitignore and .brrrignore pattern matching
/// * `max_depth` - Maximum directory depth to traverse. None uses default (100).
///                 Prevents stack overflow from deeply nested directory structures.
///
/// # Returns
///
/// A `FileTreeEntry` representing the root directory with nested children.
/// Directories at the depth limit will have `depth_limited: true` set.
///
/// # Example Output
///
/// ```json
/// {
///   "name": "project",
///   "type": "dir",
///   "path": ".",
///   "children": [
///     {"name": "src", "type": "dir", "path": "src", "children": [...]},
///     {"name": "README.md", "type": "file", "path": "README.md"}
///   ]
/// }
/// ```
pub fn file_tree(
    path: &str,
    ext_filter: &[String],
    show_hidden: bool,
    no_ignore: bool,
    max_depth: Option<usize>,
) -> Result<FileTreeEntry> {
    let effective_max_depth = max_depth.unwrap_or(DEFAULT_MAX_DEPTH);

    let root_path = Path::new(path)
        .canonicalize()
        .map_err(|e| crate::error::BrrrError::Io(e))?;

    // Phase 1: Collect all paths using the walker.
    // Configure walker based on no_ignore and show_hidden flags.
    let mut walker_builder = WalkBuilder::new(&root_path);

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

    // Let walker handle hidden files when not showing them
    // We still do manual filtering for finer control over DEFAULT_SKIP_DIRS
    walker_builder.hidden(false);

    // BUG-015 FIX: Limit traversal depth to prevent stack overflow from deeply nested directories.
    // The ignore crate's WalkBuilder supports max_depth to limit filesystem traversal.
    // This protects Phase 1 (path collection) from malicious or accidental deep nesting.
    walker_builder.max_depth(Some(effective_max_depth));

    let walker = walker_builder.build();

    // Collect paths and build parent->children mapping in one pass
    let mut children_map: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
    let mut is_dir_set: HashSet<PathBuf> = HashSet::new();

    // BUG-014 FIX: Track visited canonical paths to detect symlink cycles.
    // A cycle like a -> b -> c -> a would cause infinite recursion without this check.
    // We track canonical paths because different symlink paths can resolve to the same directory.
    let mut visited_canonical: HashSet<PathBuf> = HashSet::new();

    // Pre-insert root's canonical path to handle cycles back to root
    visited_canonical.insert(root_path.clone());

    for result in walker {
        let entry = match result {
            Ok(e) => e,
            Err(_) => continue,
        };

        let entry_path = entry.path().to_path_buf();

        // Skip root itself (we'll handle it as the return value)
        if entry_path == root_path {
            is_dir_set.insert(entry_path);
            continue;
        }

        // SECURITY: Validate path containment to prevent path traversal attacks.
        // This is critical for symlinks that might point outside the root directory.
        // We use the canonical paths to catch symlink-based escapes.
        if entry_path.is_symlink() {
            // For symlinks, validate that the target is within the root
            match validate_path_containment(&root_path, &entry_path) {
                Ok(_) => {} // Symlink target is safely within root
                Err(BrrrError::PathTraversal { target, base }) => {
                    warn!(
                        symlink = %entry_path.display(),
                        target = %target,
                        base = %base,
                        "Skipping symlink that escapes project root (path traversal attempt)"
                    );
                    continue;
                }
                Err(BrrrError::Io(_)) => {
                    // Symlink target doesn't exist or can't be resolved - skip it
                    warn!(
                        symlink = %entry_path.display(),
                        "Skipping broken symlink"
                    );
                    continue;
                }
                Err(_) => continue,
            }
        }

        // BUG-014 FIX: Detect symlink cycles before processing.
        // Only symlinks can create cycles - regular directories cannot.
        // When a symlink points to a directory we've already seen, it's a cycle.
        // For regular directories, we track them to detect later symlinks pointing to them.
        let is_symlink = entry_path.is_symlink();
        let is_directory = entry_path.is_dir(); // Note: follows symlinks

        if is_directory {
            match entry_path.canonicalize() {
                Ok(canonical) => {
                    if !visited_canonical.insert(canonical.clone()) {
                        // This canonical path was already visited.
                        // Only skip if this is a SYMLINK creating the cycle.
                        // Regular directories should always be included (first encounter).
                        if is_symlink {
                            warn!(
                                path = %entry_path.display(),
                                canonical = %canonical.display(),
                                "Skipping symlink due to cycle (target already visited)"
                            );
                            continue;
                        }
                        // Regular directory with same canonical path - rare edge case
                        // (e.g., hard links to directories, though most filesystems don't allow this)
                        // We still skip to prevent duplicates
                    }
                }
                Err(e) => {
                    // Cannot canonicalize - likely broken symlink or permission issue
                    // Only warn and skip for symlinks; regular dirs should always canonicalize
                    if is_symlink {
                        warn!(
                            path = %entry_path.display(),
                            error = %e,
                            "Skipping symlink that cannot be resolved"
                        );
                        continue;
                    }
                    // For regular directories, this is unexpected - log but continue
                    warn!(
                        path = %entry_path.display(),
                        error = %e,
                        "Warning: directory could not be canonicalized"
                    );
                }
            }
        }

        // Get relative path for filtering
        let rel_path = match entry_path.strip_prefix(&root_path) {
            Ok(p) => p,
            Err(_) => continue,
        };

        // Skip default directories (always skip these regardless of flags)
        // BUG-012 FIX: Use to_string_lossy() to handle non-UTF8 paths gracefully
        // instead of silently converting to empty string which would never match.
        if rel_path.components().any(|c| {
            let component_str = c.as_os_str().to_string_lossy();
            DEFAULT_SKIP_DIRS.contains(&component_str.as_ref())
        }) {
            continue;
        }

        // Skip hidden files/directories unless show_hidden is true
        if !show_hidden {
            if rel_path.components().any(|c| {
                c.as_os_str()
                    .to_str()
                    .map(|s| s.starts_with('.'))
                    .unwrap_or(false)
            }) {
                continue;
            }
        }

        // For files, apply extension filter (match ANY of the provided extensions)
        // Note: is_directory was already computed above for cycle detection
        if !is_directory && !ext_filter.is_empty() {
            let file_ext = entry_path
                .extension()
                .and_then(|e| e.to_str())
                .map(|e| format!(".{}", e));

            let matches = file_ext
                .as_ref()
                .map(|fe| ext_filter.iter().any(|ef| ef == fe))
                .unwrap_or(false);

            if !matches {
                continue;
            }
        }

        // Track directory status
        if is_directory {
            is_dir_set.insert(entry_path.clone());
        }

        // Add to parent's children list
        if let Some(parent) = entry_path.parent() {
            children_map
                .entry(parent.to_path_buf())
                .or_default()
                .push(entry_path);
        }
    }

    // Phase 2: Build the tree recursively from the children map.
    // This handles the "prune empty directories" logic for extension filtering.
    // BUG-015 FIX: Pass max_depth and current depth (0 for root) to track depth during tree building.
    // This provides defense-in-depth against stack overflow and marks directories at the limit.
    let tree = build_tree_from_map(
        &root_path,
        &root_path,
        &mut children_map,
        &is_dir_set,
        !ext_filter.is_empty(),
        0,                   // current_depth starts at 0 for root
        effective_max_depth, // max_depth to limit recursion
    );

    match tree {
        Some(t) => Ok(t),
        None => {
            // Return empty root if nothing matches filter
            // Use "." for root path to match Python behavior (consistent relative paths)
            // BUG-012 FIX: Use to_string_lossy() for non-UTF8 path handling
            let name = root_path
                .file_name()
                .map(|n| {
                    let lossy = n.to_string_lossy();
                    if lossy.contains('\u{FFFD}') {
                        warn!(
                            path = %root_path.display(),
                            "Root directory name contains non-UTF8 characters, using lossy conversion"
                        );
                    }
                    lossy.into_owned()
                })
                .unwrap_or_else(|| ".".to_string());

            Ok(FileTreeEntry::new_dir(name, ".".to_string(), vec![]))
        }
    }
}

/// Recursively build tree from parent->children map.
///
/// When `has_filter` is true, directories without matching children
/// are pruned from the result (matching Python behavior).
///
/// BUG-015 FIX: Added `current_depth` and `max_depth` parameters to prevent stack overflow
/// from deeply nested directory structures. When `current_depth >= max_depth`, recursion
/// stops and directories are marked with `depth_limited: true`.
fn build_tree_from_map(
    path: &Path,
    root: &Path,
    children_map: &mut HashMap<PathBuf, Vec<PathBuf>>,
    is_dir_set: &HashSet<PathBuf>,
    has_filter: bool,
    current_depth: usize,
    max_depth: usize,
) -> Option<FileTreeEntry> {
    let is_directory = is_dir_set.contains(path);

    // For files, just return the entry
    if !is_directory {
        // BUG-012 FIX: Use to_string_lossy() to preserve as much information as possible
        // for non-UTF8 paths instead of silently converting to empty string.
        let name = path
            .file_name()
            .map(|n| {
                let lossy = n.to_string_lossy();
                if lossy.contains('\u{FFFD}') {
                    warn!(
                        path = %path.display(),
                        "File name contains non-UTF8 characters, using lossy conversion"
                    );
                }
                lossy.into_owned()
            })
            .unwrap_or_else(|| "<invalid>".to_string());

        let rel_path = path
            .strip_prefix(root)
            .map(|p| p.display().to_string())
            .unwrap_or_default();

        return Some(FileTreeEntry::new_file(name, rel_path));
    }

    // BUG-015 FIX: Check if we've reached the depth limit.
    // If so, return a depth-limited placeholder instead of recursing further.
    // This prevents stack overflow from deeply nested directory structures.
    if current_depth >= max_depth {
        return Some(FileTreeEntry::depth_limit_reached(path, root));
    }

    // For directories, recursively process children
    let child_paths = children_map.remove(path).unwrap_or_default();
    let mut children: Vec<FileTreeEntry> = Vec::with_capacity(child_paths.len());

    for child_path in child_paths {
        if let Some(child_entry) = build_tree_from_map(
            &child_path,
            root,
            children_map,
            is_dir_set,
            has_filter,
            current_depth + 1, // Increment depth for children
            max_depth,
        ) {
            children.push(child_entry);
        }
    }

    // Sort: directories first, then alphabetically by name (case-insensitive)
    children.sort_by(|a, b| match (a.is_dir(), b.is_dir()) {
        (true, false) => std::cmp::Ordering::Less,
        (false, true) => std::cmp::Ordering::Greater,
        _ => a.name.to_lowercase().cmp(&b.name.to_lowercase()),
    });

    // Prune empty directories when filter is active (matches Python behavior)
    if has_filter && children.is_empty() && path != root {
        return None;
    }

    // BUG-012 FIX: Use to_string_lossy() to preserve as much information as possible
    // for non-UTF8 paths instead of silently converting to fallback values.
    let name = path
        .file_name()
        .map(|n| {
            let lossy = n.to_string_lossy();
            if lossy.contains('\u{FFFD}') {
                warn!(
                    path = %path.display(),
                    "Directory name contains non-UTF8 characters, using lossy conversion"
                );
            }
            lossy.into_owned()
        })
        .unwrap_or_else(|| ".".to_string());

    // Use "." for root path to match Python behavior (consistent relative paths)
    let rel_path = if path == root {
        ".".to_string()
    } else {
        path.strip_prefix(root)
            .map(|p| p.display().to_string())
            .unwrap_or_default()
    };

    Some(FileTreeEntry::new_dir(name, rel_path, children))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use tempfile::TempDir;

    fn create_test_tree() -> TempDir {
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create directory structure:
        // root/
        //   src/
        //     main.py
        //     utils.py
        //   tests/
        //     test_main.py
        //   docs/
        //     README.md
        //   .hidden/
        //     secret.py
        //   node_modules/
        //     package/
        //       index.js

        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("tests")).unwrap();
        fs::create_dir_all(root.join("docs")).unwrap();
        fs::create_dir_all(root.join(".hidden")).unwrap();
        fs::create_dir_all(root.join("node_modules/package")).unwrap();

        File::create(root.join("src/main.py"))
            .unwrap()
            .write_all(b"print('hello')")
            .unwrap();
        File::create(root.join("src/utils.py"))
            .unwrap()
            .write_all(b"# utils")
            .unwrap();
        File::create(root.join("tests/test_main.py"))
            .unwrap()
            .write_all(b"# tests")
            .unwrap();
        File::create(root.join("docs/README.md"))
            .unwrap()
            .write_all(b"# README")
            .unwrap();
        File::create(root.join(".hidden/secret.py"))
            .unwrap()
            .write_all(b"# secret")
            .unwrap();
        File::create(root.join("node_modules/package/index.js"))
            .unwrap()
            .write_all(b"// index")
            .unwrap();

        temp_dir
    }

    #[test]
    fn test_file_tree_no_filter() {
        let temp_dir = create_test_tree();
        let tree = file_tree(temp_dir.path().to_str().unwrap(), &[], false, false, None).unwrap();

        assert!(tree.is_dir());
        assert!(!tree.children.is_empty());

        // Should have src, tests, docs but NOT .hidden or node_modules
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(child_names.contains(&"src"));
        assert!(child_names.contains(&"tests"));
        assert!(child_names.contains(&"docs"));
        assert!(!child_names.contains(&".hidden"));
        assert!(!child_names.contains(&"node_modules"));
    }

    #[test]
    fn test_file_tree_with_extension_filter() {
        let temp_dir = create_test_tree();
        let tree = file_tree(
            temp_dir.path().to_str().unwrap(),
            &[".py".to_string()],
            false,
            false,
            None,
        )
        .unwrap();

        assert!(tree.is_dir());

        // Should have src and tests (contain .py files) but NOT docs (only .md)
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(child_names.contains(&"src"));
        assert!(child_names.contains(&"tests"));
        assert!(!child_names.contains(&"docs")); // Pruned because no .py files
    }

    #[test]
    fn test_tree_structure_is_hierarchical() {
        let temp_dir = create_test_tree();
        let tree = file_tree(temp_dir.path().to_str().unwrap(), &[], false, false, None).unwrap();

        // Find src directory
        let src_dir = tree.children.iter().find(|c| c.name == "src").unwrap();
        assert!(src_dir.is_dir());
        assert!(!src_dir.children.is_empty());

        // src should contain main.py and utils.py
        let src_files: Vec<&str> = src_dir.children.iter().map(|c| c.name.as_str()).collect();
        assert!(src_files.contains(&"main.py"));
        assert!(src_files.contains(&"utils.py"));
    }

    #[test]
    fn test_sorting_dirs_first() {
        let temp_dir = create_test_tree();

        // Add a file at root level
        File::create(temp_dir.path().join("setup.py"))
            .unwrap()
            .write_all(b"# setup")
            .unwrap();

        let tree = file_tree(temp_dir.path().to_str().unwrap(), &[], false, false, None).unwrap();

        // Directories should come before files
        let first_file_idx = tree
            .children
            .iter()
            .position(|c| !c.is_dir())
            .unwrap_or(tree.children.len());
        let last_dir_idx = tree.children.iter().rposition(|c| c.is_dir()).unwrap_or(0);

        assert!(
            last_dir_idx < first_file_idx,
            "Directories should come before files"
        );
    }

    #[test]
    fn test_file_tree_with_multiple_extension_filter() {
        let temp_dir = create_test_tree();
        // Filter for both .py and .md files
        let tree = file_tree(
            temp_dir.path().to_str().unwrap(),
            &[".py".to_string(), ".md".to_string()],
            false,
            false,
            None,
        )
        .unwrap();

        assert!(tree.is_dir());

        // Should have src, tests (contain .py files) AND docs (contains .md files)
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(
            child_names.contains(&"src"),
            "src should be present (contains .py)"
        );
        assert!(
            child_names.contains(&"tests"),
            "tests should be present (contains .py)"
        );
        assert!(
            child_names.contains(&"docs"),
            "docs should be present (contains .md)"
        );
    }

    #[test]
    fn test_file_tree_show_hidden() {
        let temp_dir = create_test_tree();
        // With show_hidden=true, should include .hidden directory
        let tree = file_tree(temp_dir.path().to_str().unwrap(), &[], true, false, None).unwrap();

        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(
            child_names.contains(&".hidden"),
            ".hidden should be present when show_hidden=true"
        );
        // node_modules should still be excluded (it's in DEFAULT_SKIP_DIRS)
        assert!(
            !child_names.contains(&"node_modules"),
            "node_modules should still be excluded"
        );
    }

    // =========================================================================
    // SECURITY TESTS: Path Traversal Protection
    // =========================================================================

    #[cfg(unix)]
    #[test]
    fn test_symlink_outside_root_excluded() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a normal directory structure
        fs::create_dir_all(root.join("src")).unwrap();
        File::create(root.join("src/main.py"))
            .unwrap()
            .write_all(b"# main")
            .unwrap();

        // Create a symlink that points OUTSIDE the root (to /tmp)
        // This should be excluded from the tree for security
        let _ = symlink("/tmp", root.join("escape_link"));

        let tree = file_tree(root.to_str().unwrap(), &[], false, false, None).unwrap();

        // The symlink should NOT appear in the tree (security protection)
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();

        // Note: The symlink might not appear at all due to walker behavior,
        // OR it should be filtered out by our security validation.
        // Either way, we verify the tree only contains expected safe entries.
        assert!(child_names.contains(&"src"), "src should be present");

        // If escape_link IS present, it would be a security vulnerability
        // (though the walker might not yield it at all)
        for child in &tree.children {
            assert_ne!(
                child.name, "escape_link",
                "Symlink pointing outside root should be excluded"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_symlink_inside_root_included() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create directories
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("lib")).unwrap();
        File::create(root.join("lib/utils.py"))
            .unwrap()
            .write_all(b"# utils")
            .unwrap();

        // Create a symlink that points INSIDE the root (safe)
        let _ = symlink(root.join("lib"), root.join("src/lib_link"));

        let tree = file_tree(root.to_str().unwrap(), &[], false, false, None).unwrap();

        // src should be present
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(child_names.contains(&"src"), "src should be present");
        assert!(child_names.contains(&"lib"), "lib should be present");
    }

    // =========================================================================
    // BUG-014: Symlink Cycle Detection Tests
    // =========================================================================

    #[cfg(unix)]
    #[test]
    fn test_symlink_cycle_detected_and_skipped() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a directory structure with a symlink cycle:
        // root/
        //   dir_a/
        //     file.py
        //     link_to_b -> ../dir_b
        //   dir_b/
        //     link_to_a -> ../dir_a  (creates cycle: a -> b -> a)
        fs::create_dir_all(root.join("dir_a")).unwrap();
        fs::create_dir_all(root.join("dir_b")).unwrap();
        File::create(root.join("dir_a/file.py"))
            .unwrap()
            .write_all(b"# file in dir_a")
            .unwrap();

        // Create the cycle: dir_a/link_to_b -> dir_b, dir_b/link_to_a -> dir_a
        let _ = symlink(root.join("dir_b"), root.join("dir_a/link_to_b"));
        let _ = symlink(root.join("dir_a"), root.join("dir_b/link_to_a"));

        // This should NOT cause infinite recursion or stack overflow
        let result = file_tree(root.to_str().unwrap(), &[], false, false, None);

        // The function should complete successfully (no stack overflow)
        assert!(
            result.is_ok(),
            "file_tree should handle symlink cycles gracefully"
        );

        let tree = result.unwrap();

        // Verify basic structure is present
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(child_names.contains(&"dir_a"), "dir_a should be present");
        assert!(child_names.contains(&"dir_b"), "dir_b should be present");
    }

    #[cfg(unix)]
    #[test]
    fn test_symlink_self_cycle_detected() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a directory with a symlink pointing to itself (self-cycle)
        // root/
        //   data/
        //     self_link -> .  (points to same directory)
        fs::create_dir_all(root.join("data")).unwrap();
        File::create(root.join("data/file.py"))
            .unwrap()
            .write_all(b"# file")
            .unwrap();

        // Create self-referential symlink
        let _ = symlink(root.join("data"), root.join("data/self_link"));

        // This should NOT cause infinite recursion
        let result = file_tree(root.to_str().unwrap(), &[], false, false, None);
        assert!(
            result.is_ok(),
            "file_tree should handle self-referential symlinks"
        );

        let tree = result.unwrap();
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(
            child_names.contains(&"data"),
            "data directory should be present"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_symlink_to_root_cycle_detected() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a symlink that points back to the root directory
        // root/
        //   src/
        //     back_to_root -> ../..  (cycle back to root)
        fs::create_dir_all(root.join("src")).unwrap();
        File::create(root.join("src/main.py"))
            .unwrap()
            .write_all(b"# main")
            .unwrap();

        // Create symlink back to root
        let _ = symlink(root, root.join("src/back_to_root"));

        // This should NOT cause infinite recursion
        let result = file_tree(root.to_str().unwrap(), &[], false, false, None);
        assert!(
            result.is_ok(),
            "file_tree should handle symlinks pointing to root"
        );

        let tree = result.unwrap();
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(
            child_names.contains(&"src"),
            "src directory should be present"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_deep_symlink_chain_with_cycle() {
        use std::os::unix::fs::symlink;

        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a deeper cycle: a -> b -> c -> a
        // root/
        //   dir_a/
        //     link_to_b -> ../dir_b
        //   dir_b/
        //     link_to_c -> ../dir_c
        //   dir_c/
        //     link_to_a -> ../dir_a  (closes the cycle)
        fs::create_dir_all(root.join("dir_a")).unwrap();
        fs::create_dir_all(root.join("dir_b")).unwrap();
        fs::create_dir_all(root.join("dir_c")).unwrap();

        File::create(root.join("dir_a/a.py"))
            .unwrap()
            .write_all(b"# a")
            .unwrap();
        File::create(root.join("dir_b/b.py"))
            .unwrap()
            .write_all(b"# b")
            .unwrap();
        File::create(root.join("dir_c/c.py"))
            .unwrap()
            .write_all(b"# c")
            .unwrap();

        // Create the 3-way cycle
        let _ = symlink(root.join("dir_b"), root.join("dir_a/link_to_b"));
        let _ = symlink(root.join("dir_c"), root.join("dir_b/link_to_c"));
        let _ = symlink(root.join("dir_a"), root.join("dir_c/link_to_a"));

        // This should NOT cause infinite recursion or stack overflow
        let result = file_tree(root.to_str().unwrap(), &[], false, false, None);
        assert!(
            result.is_ok(),
            "file_tree should handle 3-way symlink cycles"
        );

        let tree = result.unwrap();
        let child_names: Vec<&str> = tree.children.iter().map(|c| c.name.as_str()).collect();
        assert!(child_names.contains(&"dir_a"), "dir_a should be present");
        assert!(child_names.contains(&"dir_b"), "dir_b should be present");
        assert!(child_names.contains(&"dir_c"), "dir_c should be present");
    }

    // =========================================================================
    // BUG-015: Max Depth Protection Tests
    // =========================================================================

    #[test]
    fn test_max_depth_limits_traversal() {
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a deeply nested structure: root/a/b/c/d/e/file.py
        fs::create_dir_all(root.join("a/b/c/d/e")).unwrap();
        File::create(root.join("a/b/c/d/e/file.py"))
            .unwrap()
            .write_all(b"# deep file")
            .unwrap();

        // With max_depth=2, should only see root and 2 levels of children
        let tree = file_tree(root.to_str().unwrap(), &[], false, false, Some(2)).unwrap();

        assert!(tree.is_dir());
        // Root (depth 0) should have 'a' (depth 1)
        let a_dir = tree.children.iter().find(|c| c.name == "a");
        assert!(
            a_dir.is_some(),
            "Directory 'a' should be present at depth 1"
        );

        let a_dir = a_dir.unwrap();
        // 'a' (depth 1) should have 'b' (depth 2)
        let b_dir = a_dir.children.iter().find(|c| c.name == "b");
        assert!(
            b_dir.is_some(),
            "Directory 'b' should be present at depth 2"
        );

        let b_dir = b_dir.unwrap();
        // 'b' at depth 2 should be depth_limited (can't recurse further)
        assert!(
            b_dir.depth_limited,
            "Directory 'b' at depth 2 should be marked as depth_limited"
        );
        assert!(
            b_dir.children.is_empty(),
            "Directory 'b' should have no children due to depth limit"
        );
    }

    #[test]
    fn test_default_max_depth_allows_reasonable_nesting() {
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create a structure 5 levels deep
        fs::create_dir_all(root.join("a/b/c/d/e")).unwrap();
        File::create(root.join("a/b/c/d/e/file.py"))
            .unwrap()
            .write_all(b"# deep file")
            .unwrap();

        // Default max_depth (None -> 100) should allow this
        let tree = file_tree(root.to_str().unwrap(), &[], false, false, None).unwrap();

        // Navigate to the deepest file
        let a = tree.children.iter().find(|c| c.name == "a").unwrap();
        let b = a.children.iter().find(|c| c.name == "b").unwrap();
        let c = b.children.iter().find(|c| c.name == "c").unwrap();
        let d = c.children.iter().find(|c| c.name == "d").unwrap();
        let e = d.children.iter().find(|c| c.name == "e").unwrap();

        // Should have the file at the deepest level
        let file = e.children.iter().find(|c| c.name == "file.py");
        assert!(file.is_some(), "file.py should be present at depth 5");

        // No directories should be depth_limited with default depth
        assert!(!a.depth_limited);
        assert!(!b.depth_limited);
        assert!(!c.depth_limited);
        assert!(!d.depth_limited);
        assert!(!e.depth_limited);
    }

    #[test]
    fn test_max_depth_zero_returns_only_root() {
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create some structure
        fs::create_dir_all(root.join("src")).unwrap();
        File::create(root.join("src/main.py"))
            .unwrap()
            .write_all(b"# main")
            .unwrap();

        // With max_depth=0, should only get the root directory
        let tree = file_tree(root.to_str().unwrap(), &[], false, false, Some(0)).unwrap();

        assert!(tree.is_dir());
        assert!(
            tree.depth_limited,
            "Root should be depth_limited when max_depth=0"
        );
        assert!(
            tree.children.is_empty(),
            "Root should have no children when max_depth=0"
        );
    }

    // =========================================================================
    // BUG-013: JSON Schema Compatibility Tests
    // =========================================================================

    #[test]
    fn test_file_tree_entry_json_schema_has_type_field() {
        // BUG-013 FIX: Verify JSON uses "type" field (matching Python) not "is_dir"
        let entry = FileTreeEntry::new_dir(
            "test".to_string(),
            "test".to_string(),
            vec![FileTreeEntry::new_file(
                "file.py".to_string(),
                "test/file.py".to_string(),
            )],
        );

        let json = serde_json::to_string(&entry).unwrap();

        // Must have "type" field, NOT "is_dir"
        assert!(
            json.contains(r#""type":"dir""#),
            "JSON should contain type:dir, got: {}",
            json
        );
        assert!(
            !json.contains(r#""is_dir""#),
            "JSON should NOT contain is_dir field, got: {}",
            json
        );

        // Children should also have "type" field
        assert!(
            json.contains(r#""type":"file""#),
            "Child JSON should contain type:file, got: {}",
            json
        );
    }

    #[test]
    fn test_file_tree_entry_json_roundtrip() {
        // Test that JSON can be deserialized back
        let original = FileTreeEntry::new_dir(
            "project".to_string(),
            ".".to_string(),
            vec![
                FileTreeEntry::new_dir("src".to_string(), "src".to_string(), vec![]),
                FileTreeEntry::new_file("main.py".to_string(), "main.py".to_string()),
            ],
        );

        let json = serde_json::to_string(&original).unwrap();
        let deserialized: FileTreeEntry = serde_json::from_str(&json).unwrap();

        assert_eq!(deserialized.name, "project");
        assert_eq!(deserialized.entry_type, "dir");
        assert!(deserialized.is_dir());
        assert_eq!(deserialized.children.len(), 2);

        // Verify children
        let src = deserialized
            .children
            .iter()
            .find(|c| c.name == "src")
            .unwrap();
        assert!(src.is_dir());
        assert_eq!(src.entry_type, "dir");

        let main = deserialized
            .children
            .iter()
            .find(|c| c.name == "main.py")
            .unwrap();
        assert!(!main.is_dir());
        assert_eq!(main.entry_type, "file");
    }

    #[test]
    fn test_file_tree_entry_python_compatible_json() {
        // Test exact JSON format matches Python implementation
        let entry = FileTreeEntry::new_file("test.py".to_string(), "src/test.py".to_string());
        let json = serde_json::to_string(&entry).unwrap();

        // Parse as generic JSON to verify structure
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed["name"], "test.py");
        assert_eq!(parsed["type"], "file");
        assert_eq!(parsed["path"], "src/test.py");
        // Files should not have children in output (skip_serializing_if = Vec::is_empty)
        assert!(
            parsed.get("children").is_none() || parsed["children"].as_array().unwrap().is_empty()
        );
    }
}
