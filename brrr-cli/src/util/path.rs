//! Path manipulation utilities.
//!
//! Provides functions for normalizing paths, detecting project roots,
//! detecting languages, and validating paths.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use once_cell::sync::Lazy;
use rustc_hash::FxHashSet;

use crate::lang::LanguageRegistry;

/// Normalize a path to its canonical form.
///
/// Resolves symlinks and relative components (., ..) to produce an absolute path.
/// Returns the original path if canonicalization fails (e.g., path doesn't exist).
///
/// # Arguments
///
/// * `path` - Path to normalize (can be relative or absolute)
///
/// # Returns
///
/// Canonical absolute path, or cleaned original path if canonicalization fails.
///
/// # Examples
///
/// ```
/// use std::path::Path;
/// use brrr::util::path::normalize_path;
///
/// let normalized = normalize_path(Path::new("./src/../src/main.rs"));
/// // Returns absolute path like "/home/user/project/src/main.rs"
/// ```
#[must_use]
pub fn normalize_path(path: &Path) -> PathBuf {
    // Try canonicalization first (resolves symlinks and relative components)
    if let Ok(canonical) = path.canonicalize() {
        return canonical;
    }

    // Fallback: manually clean the path without requiring existence
    let mut result = PathBuf::new();
    let is_absolute = path.is_absolute();

    for component in path.components() {
        match component {
            std::path::Component::CurDir => {
                // Skip "." components
            }
            std::path::Component::ParentDir => {
                // Pop last component for ".."
                result.pop();
            }
            _ => {
                result.push(component);
            }
        }
    }

    // Ensure absolute paths stay absolute
    if is_absolute && !result.is_absolute() {
        if let Ok(cwd) = std::env::current_dir() {
            return cwd.join(result);
        }
    }

    result
}

/// Marker files that indicate a project root directory.
const PROJECT_MARKERS: &[&str] = &[
    // Version control
    ".git",
    ".hg",
    ".svn",
    // Python
    "pyproject.toml",
    "setup.py",
    "setup.cfg",
    "requirements.txt",
    // Rust
    "Cargo.toml",
    // Node.js / JavaScript / TypeScript
    "package.json",
    "tsconfig.json",
    // Go
    "go.mod",
    "go.work",
    // Java / JVM
    "pom.xml",
    "build.gradle",
    "build.gradle.kts",
    "settings.gradle",
    // C/C++
    "CMakeLists.txt",
    "Makefile",
    "meson.build",
    // General
    ".brrrignore",
    ".editorconfig",
];

/// Find the project root directory containing a given path.
///
/// Walks up the directory tree looking for common project markers
/// (like `.git`, `Cargo.toml`, `package.json`, etc.).
///
/// # Arguments
///
/// * `path` - Starting path (file or directory)
///
/// # Returns
///
/// `Some(PathBuf)` of the project root, or `None` if no markers found.
///
/// # Examples
///
/// ```no_run
/// use std::path::Path;
/// use brrr::util::path::get_project_root;
///
/// let root = get_project_root(Path::new("/home/user/project/src/main.rs"));
/// // Returns Some("/home/user/project") if .git or Cargo.toml exists there
/// ```
#[must_use]
pub fn get_project_root(path: &Path) -> Option<PathBuf> {
    // Normalize the starting path
    let start = normalize_path(path);

    // If it's a file, start from its parent directory
    let mut current = if start.is_file() {
        start.parent()?.to_path_buf()
    } else {
        start
    };

    // Walk up the directory tree
    loop {
        // Check for any project marker
        for marker in PROJECT_MARKERS {
            if current.join(marker).exists() {
                return Some(current);
            }
        }

        // Move to parent directory
        match current.parent() {
            Some(parent) => {
                if parent == current {
                    // Reached root without finding markers
                    break;
                }
                current = parent.to_path_buf();
            }
            None => break,
        }
    }

    None
}

/// Get the detected language name for a source file.
///
/// Convenience function that returns the language name as a string
/// if the file is recognized as source code.
///
/// # Arguments
///
/// * `path` - Path to check
///
/// # Returns
///
/// Language name (e.g., "python", "rust") or `None`.
#[must_use]
#[allow(dead_code)]
pub fn detect_language(path: &Path) -> Option<&'static str> {
    let registry = LanguageRegistry::global();
    registry.detect_language(path).map(|lang| lang.name())
}

/// Extension to language mapping for project language detection.
///
/// Maps file extensions (without dot) to language names.
/// Used by `detect_project_language` to count files by language.
const EXTENSION_TO_LANG: &[(&str, &str)] = &[
    // Python
    ("py", "python"),
    ("pyi", "python"),
    // Rust
    ("rs", "rust"),
    // TypeScript/JavaScript
    ("ts", "typescript"),
    ("tsx", "typescript"),
    ("js", "javascript"),
    ("jsx", "javascript"),
    ("mjs", "javascript"),
    ("cjs", "javascript"),
    // Go
    ("go", "go"),
    // Java
    ("java", "java"),
    // C
    ("c", "c"),
    // C/C++ headers: mapped to "cpp" to match the language registry
    // (the registry resolves .h → cpp since cpp is registered after c)
    ("h", "cpp"),
    // C++
    ("cpp", "cpp"),
    ("cc", "cpp"),
    ("cxx", "cpp"),
    ("hpp", "cpp"),
    ("hh", "cpp"),
    // CUDA (C++ superset, parsed as cpp)
    ("cu", "cpp"),
    ("cuh", "cpp"),
    // Ruby
    ("rb", "ruby"),
    // PHP
    ("php", "php"),
    // Kotlin
    ("kt", "kotlin"),
    ("kts", "kotlin"),
    // Swift
    ("swift", "swift"),
    // C#
    ("cs", "csharp"),
    // Scala
    ("scala", "scala"),
    ("sc", "scala"),
    // Lua
    ("lua", "lua"),
    // Elixir
    ("ex", "elixir"),
    ("exs", "elixir"),
];

// =============================================================================
// Path Validation Utilities
// =============================================================================

/// Validate that a path exists.
///
/// Returns an error with a descriptive message if the path does not exist.
/// Use this for commands that accept both files and directories.
///
/// # Arguments
///
/// * `path` - Path to validate
///
/// # Returns
///
/// `Ok(())` if the path exists, or an error describing the issue.
///
/// # Examples
///
/// ```no_run
/// use std::path::Path;
/// use brrr::util::path::require_exists;
///
/// require_exists(Path::new("/path/to/target"))?;
/// ```
pub fn require_exists(path: &Path) -> Result<(), PathValidationError> {
    if !path.exists() {
        return Err(PathValidationError::NotFound(path.display().to_string()));
    }
    Ok(())
}

/// Validate that a path exists and is a file.
///
/// Returns an error with a descriptive message if the path does not exist
/// or is not a regular file.
///
/// # Arguments
///
/// * `path` - Path to validate
///
/// # Returns
///
/// `Ok(())` if the path exists and is a file, or an error describing the issue.
///
/// # Examples
///
/// ```no_run
/// use std::path::Path;
/// use brrr::util::path::require_file;
///
/// require_file(Path::new("/path/to/source.py"))?;
/// ```
pub fn require_file(path: &Path) -> Result<(), PathValidationError> {
    if !path.exists() {
        return Err(PathValidationError::FileNotFound(
            path.display().to_string(),
        ));
    }
    if !path.is_file() {
        return Err(PathValidationError::ExpectedFile(
            path.display().to_string(),
        ));
    }
    Ok(())
}

/// Validate that a path exists and is a directory.
///
/// Returns an error with a descriptive message if the path does not exist
/// or is not a directory.
///
/// # Arguments
///
/// * `path` - Path to validate
///
/// # Returns
///
/// `Ok(())` if the path exists and is a directory, or an error describing the issue.
///
/// # Examples
///
/// ```no_run
/// use std::path::Path;
/// use brrr::util::path::require_directory;
///
/// require_directory(Path::new("/path/to/project"))?;
/// ```
pub fn require_directory(path: &Path) -> Result<(), PathValidationError> {
    if !path.exists() {
        return Err(PathValidationError::DirectoryNotFound(
            path.display().to_string(),
        ));
    }
    if !path.is_dir() {
        return Err(PathValidationError::ExpectedDirectory(
            path.display().to_string(),
        ));
    }
    Ok(())
}

/// Error type for path validation operations.
///
/// Provides descriptive error messages matching the Python implementation's
/// `_validate_path()` behavior.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathValidationError {
    /// Path does not exist (generic)
    NotFound(String),
    /// File not found
    FileNotFound(String),
    /// Directory not found
    DirectoryNotFound(String),
    /// Expected a file but found a directory
    ExpectedFile(String),
    /// Expected a directory but found a file
    ExpectedDirectory(String),
}

impl std::fmt::Display for PathValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(path) => write!(f, "Path not found: {}", path),
            Self::FileNotFound(path) => write!(f, "File not found: {}", path),
            Self::DirectoryNotFound(path) => write!(f, "Directory not found: {}", path),
            Self::ExpectedFile(path) => write!(f, "Expected file but found directory: {}", path),
            Self::ExpectedDirectory(path) => {
                write!(f, "Expected directory but found file: {}", path)
            }
        }
    }
}

impl std::error::Error for PathValidationError {}

/// Directories to skip during project language scanning.
/// Uses FxHashSet for O(1) lookup instead of O(n) linear search.
static SKIP_DIRECTORIES: Lazy<FxHashSet<&'static str>> = Lazy::new(|| {
    [
        "node_modules",
        "__pycache__",
        ".pycache",
        "vendor",
        "dist",
        "build",
        "target",
        ".git",
        ".hg",
        ".svn",
        "venv",
        ".venv",
        "env",
        ".env",
    ]
    .into_iter()
    .collect()
});

/// Detect the primary programming language of a project.
///
/// Uses a two-phase detection strategy:
/// 1. **Cache check**: Reads `.brrr/cache/call_graph.json` for cached language info
/// 2. **File scanning**: Counts source files by extension and returns the most common
///
/// Prefers `src/` or `lib/` directories if they exist for scanning.
///
/// # Arguments
///
/// * `path` - Path to the project root directory
///
/// # Returns
///
/// The detected language name (e.g., "python", "rust"), or "python" as default
/// if detection fails.
///
/// # Examples
///
/// ```no_run
/// use std::path::Path;
/// use brrr::util::path::detect_project_language;
///
/// // Detects "rust" for a Cargo project
/// let lang = detect_project_language(Path::new("/path/to/rust-project"));
///
/// // Returns "python" as default if no source files found
/// let lang = detect_project_language(Path::new("/empty/dir"));
/// ```
#[must_use]
pub fn detect_project_language(path: &Path) -> String {
    let project = normalize_path(path);

    // Priority 1: Check cached call graph for language info
    let cache_file = project.join(".brrr").join("cache").join("call_graph.json");
    if cache_file.exists() {
        if let Ok(content) = std::fs::read_to_string(&cache_file) {
            if let Ok(json) = serde_json::from_str::<serde_json::Value>(&content) {
                // Check for "languages" array (primary format)
                if let Some(languages) = json.get("languages").and_then(|v| v.as_array()) {
                    if let Some(first) = languages.first().and_then(|v| v.as_str()) {
                        return first.to_string();
                    }
                }
                // Fallback: Check for "language" string (legacy format)
                if let Some(lang) = json.get("language").and_then(|v| v.as_str()) {
                    return lang.to_string();
                }
            }
        }
    }

    // Priority 2: Scan project files and count by extension
    let ext_to_lang: HashMap<&str, &str> = EXTENSION_TO_LANG.iter().copied().collect();
    let mut counts: HashMap<&str, usize> = HashMap::new();

    // Prefer src/ or lib/ directories if they exist
    let scan_dir = if project.join("src").is_dir() {
        project.join("src")
    } else if project.join("lib").is_dir() {
        project.join("lib")
    } else {
        project.clone()
    };

    // Use walkdir with depth limit to avoid slow scanning
    let walker = walkdir::WalkDir::new(&scan_dir)
        .max_depth(10)
        .into_iter()
        .filter_entry(|e| {
            // Skip hidden directories and common vendor directories
            let name = e.file_name().to_string_lossy();
            if name.starts_with('.') && e.file_type().is_dir() {
                return false;
            }
            if e.file_type().is_dir() && SKIP_DIRECTORIES.contains(name.as_ref()) {
                return false;
            }
            true
        });

    for entry in walker.filter_map(std::result::Result::ok) {
        if !entry.file_type().is_file() {
            continue;
        }

        if let Some(ext) = entry.path().extension().and_then(|e| e.to_str()) {
            let ext_lower = ext.to_lowercase();
            if let Some(&lang) = ext_to_lang.get(ext_lower.as_str()) {
                *counts.entry(lang).or_insert(0) += 1;
            }
        }
    }

    // Return language with most files
    if let Some((&lang, _)) = counts.iter().max_by_key(|(_, &count)| count) {
        return lang.to_string();
    }

    // Default fallback
    "python".to_string()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_normalize_path_relative() {
        let path = Path::new("./src/../src/main.rs");
        let normalized = normalize_path(path);
        // Should remove . and .. components
        assert!(!normalized.to_string_lossy().contains("./"));
        assert!(!normalized.to_string_lossy().contains(".."));
    }

    #[test]
    fn test_get_project_root_with_git() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("project");
        let src_dir = project_dir.join("src");
        fs::create_dir_all(&src_dir).unwrap();
        fs::create_dir(project_dir.join(".git")).unwrap();

        let file_path = src_dir.join("main.rs");
        fs::write(&file_path, "fn main() {}").unwrap();

        let root = get_project_root(&file_path);
        assert!(root.is_some());
        assert_eq!(root.unwrap().file_name().unwrap(), "project");
    }

    #[test]
    fn test_get_project_root_with_cargo() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("rust_project");
        fs::create_dir_all(&project_dir).unwrap();
        fs::write(project_dir.join("Cargo.toml"), "[package]\nname = \"test\"").unwrap();

        let root = get_project_root(&project_dir);
        assert!(root.is_some());
        assert_eq!(root.unwrap().file_name().unwrap(), "rust_project");
    }

    #[test]
    fn test_get_project_root_not_found() {
        let temp_dir = TempDir::new().unwrap();
        let orphan_dir = temp_dir.path().join("no_markers");
        fs::create_dir_all(&orphan_dir).unwrap();

        // Create a file but no project markers
        let file_path = orphan_dir.join("orphan.rs");
        fs::write(&file_path, "fn main() {}").unwrap();

        // Note: This might find markers in parent directories on real systems
        // For isolation, we test with the temp dir root
        let root = get_project_root(temp_dir.path());
        // Should be None since temp dir has no markers
        assert!(root.is_none() || root.as_ref().map(|p| p != temp_dir.path()).unwrap_or(true));
    }

    #[test]
    fn test_detect_language() {
        assert_eq!(detect_language(Path::new("main.py")), Some("python"));
        assert_eq!(detect_language(Path::new("app.ts")), Some("typescript"));
        assert_eq!(detect_language(Path::new("lib.rs")), Some("rust"));
        assert_eq!(detect_language(Path::new("main.go")), Some("go"));
        assert_eq!(detect_language(Path::new("Main.java")), Some("java"));
        assert_eq!(detect_language(Path::new("util.c")), Some("c"));

        assert_eq!(detect_language(Path::new("readme.md")), None);
        assert_eq!(detect_language(Path::new("config.json")), None);
    }

    #[test]
    fn test_detect_project_language_from_files() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("project");
        fs::create_dir_all(&project_dir).unwrap();

        // Create multiple Python files
        fs::write(project_dir.join("main.py"), "print('hello')").unwrap();
        fs::write(project_dir.join("util.py"), "def foo(): pass").unwrap();
        fs::write(project_dir.join("helper.py"), "class A: pass").unwrap();

        // Create one Rust file
        fs::write(project_dir.join("lib.rs"), "fn main() {}").unwrap();

        // Python should win (3 files vs 1)
        let detected = detect_project_language(&project_dir);
        assert_eq!(detected, "python");
    }

    #[test]
    fn test_detect_project_language_prefers_src_dir() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("project");
        let src_dir = project_dir.join("src");
        fs::create_dir_all(&src_dir).unwrap();

        // Root has Python files
        fs::write(project_dir.join("setup.py"), "from setuptools import setup").unwrap();
        fs::write(project_dir.join("config.py"), "DEBUG = True").unwrap();

        // src/ has Rust files (should be preferred)
        fs::write(src_dir.join("main.rs"), "fn main() {}").unwrap();
        fs::write(src_dir.join("lib.rs"), "pub mod utils;").unwrap();
        fs::write(src_dir.join("utils.rs"), "pub fn foo() {}").unwrap();

        // Rust should win because src/ is preferred
        let detected = detect_project_language(&project_dir);
        assert_eq!(detected, "rust");
    }

    #[test]
    fn test_detect_project_language_from_cache() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("project");
        let cache_dir = project_dir.join(".brrr").join("cache");
        fs::create_dir_all(&cache_dir).unwrap();

        // Create cache file with language info
        let cache_content = r#"{"languages": ["go", "python"], "edges": []}"#;
        fs::write(cache_dir.join("call_graph.json"), cache_content).unwrap();

        // Create conflicting source files (should be ignored due to cache)
        fs::write(project_dir.join("main.py"), "print('hello')").unwrap();

        // Go should win (from cache)
        let detected = detect_project_language(&project_dir);
        assert_eq!(detected, "go");
    }

    #[test]
    fn test_detect_project_language_skips_vendor_dirs() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("project");
        fs::create_dir_all(&project_dir).unwrap();

        // Create node_modules with many JS files (should be skipped)
        let node_modules = project_dir.join("node_modules").join("some_package");
        fs::create_dir_all(&node_modules).unwrap();
        for i in 0..10 {
            fs::write(
                node_modules.join(format!("file{i}.js")),
                "module.exports = {}",
            )
            .unwrap();
        }

        // Create one Python file in root
        fs::write(project_dir.join("main.py"), "print('hello')").unwrap();

        // Python should win (node_modules is skipped)
        let detected = detect_project_language(&project_dir);
        assert_eq!(detected, "python");
    }

    #[test]
    fn test_detect_project_language_default_fallback() {
        let temp_dir = TempDir::new().unwrap();
        let project_dir = temp_dir.path().join("empty_project");
        fs::create_dir_all(&project_dir).unwrap();

        // No source files at all
        fs::write(project_dir.join("README.md"), "# Empty").unwrap();
        fs::write(project_dir.join("config.json"), "{}").unwrap();

        // Default to Python
        let detected = detect_project_language(&project_dir);
        assert_eq!(detected, "python");
    }

    // =========================================================================
    // Path Validation Tests
    // =========================================================================

    #[test]
    fn test_require_exists_with_existing_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("existing.txt");
        fs::write(&file_path, "content").unwrap();

        assert!(require_exists(&file_path).is_ok());
    }

    #[test]
    fn test_require_exists_with_existing_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("existing_dir");
        fs::create_dir_all(&dir_path).unwrap();

        assert!(require_exists(&dir_path).is_ok());
    }

    #[test]
    fn test_require_exists_with_nonexistent_path() {
        let path = Path::new("/nonexistent/path/to/file.txt");
        let result = require_exists(path);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, PathValidationError::NotFound(_)));
        assert!(err.to_string().contains("Path not found"));
    }

    #[test]
    fn test_require_file_with_existing_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test_file.py");
        fs::write(&file_path, "print('hello')").unwrap();

        assert!(require_file(&file_path).is_ok());
    }

    #[test]
    fn test_require_file_with_nonexistent_file() {
        let path = Path::new("/nonexistent/file.py");
        let result = require_file(path);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, PathValidationError::FileNotFound(_)));
        assert!(err.to_string().contains("File not found"));
    }

    #[test]
    fn test_require_file_with_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("a_directory");
        fs::create_dir_all(&dir_path).unwrap();

        let result = require_file(&dir_path);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, PathValidationError::ExpectedFile(_)));
        assert!(err
            .to_string()
            .contains("Expected file but found directory"));
    }

    #[test]
    fn test_require_directory_with_existing_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("test_dir");
        fs::create_dir_all(&dir_path).unwrap();

        assert!(require_directory(&dir_path).is_ok());
    }

    #[test]
    fn test_require_directory_with_nonexistent_directory() {
        let path = Path::new("/nonexistent/directory");
        let result = require_directory(path);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, PathValidationError::DirectoryNotFound(_)));
        assert!(err.to_string().contains("Directory not found"));
    }

    #[test]
    fn test_require_directory_with_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("a_file.txt");
        fs::write(&file_path, "content").unwrap();

        let result = require_directory(&file_path);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, PathValidationError::ExpectedDirectory(_)));
        assert!(err
            .to_string()
            .contains("Expected directory but found file"));
    }

    #[test]
    fn test_path_validation_error_display() {
        // Test all error variants have correct messages
        assert_eq!(
            PathValidationError::NotFound("/some/path".to_string()).to_string(),
            "Path not found: /some/path"
        );
        assert_eq!(
            PathValidationError::FileNotFound("/some/file.txt".to_string()).to_string(),
            "File not found: /some/file.txt"
        );
        assert_eq!(
            PathValidationError::DirectoryNotFound("/some/dir".to_string()).to_string(),
            "Directory not found: /some/dir"
        );
        assert_eq!(
            PathValidationError::ExpectedFile("/some/dir".to_string()).to_string(),
            "Expected file but found directory: /some/dir"
        );
        assert_eq!(
            PathValidationError::ExpectedDirectory("/some/file.txt".to_string()).to_string(),
            "Expected directory but found file: /some/file.txt"
        );
    }
}
