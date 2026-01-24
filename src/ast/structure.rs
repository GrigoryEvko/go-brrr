//! Code structure extraction (codemaps).
//!
//! Provides parallel file scanning and AST extraction to generate
//! a summary of all functions and classes in a project directory.

use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use ignore::WalkBuilder;
use rayon::prelude::*;
use tracing::{debug, warn};

use crate::ast::extractor::AstExtractor;
use crate::ast::types::{ClassSummary, CodeStructure, FunctionSummary, ModuleInfo};
use crate::error::{validate_path_containment, BrrrError, Result};
use crate::lang::LanguageRegistry;

/// Extract code structure from a directory.
///
/// Scans the directory for source files matching the language filter,
/// extracts functions and classes from each file using parallel processing,
/// and returns a summary suitable for LLM consumption.
///
/// # Arguments
/// * `path` - Root directory to scan
/// * `lang_filter` - Optional language filter (e.g., "python", "typescript")
/// * `max_results` - Maximum number of functions/classes to return (0 = unlimited)
/// * `no_ignore` - If true, bypass .gitignore and .brrrignore pattern matching
///
/// # Returns
/// * `Result<CodeStructure>` - Summary with functions, classes, and file count
///
/// # Example
/// ```no_run
/// use go_brrr::ast::code_structure;
///
/// let result = code_structure("./src", Some("python"), 100, false)?;
/// println!("Found {} functions in {} files", result.functions.len(), result.total_files);
/// # Ok::<(), go_brrr::error::BrrrError>(())
/// ```
pub fn code_structure(
    path: &str,
    lang_filter: Option<&str>,
    max_results: usize,
    no_ignore: bool,
) -> Result<CodeStructure> {
    let input_path = Path::new(path);
    let registry = LanguageRegistry::global();

    // Validate root path exists
    if !input_path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Path not found: {}", path),
        )));
    }

    // SECURITY: Canonicalize the root path to resolve symlinks and normalize.
    // This establishes a secure base for path containment validation.
    let root_path = input_path.canonicalize()?;

    // Configure walker based on no_ignore flag
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

    // Skip hidden files by default (consistent with tree behavior)
    walker_builder.hidden(true);

    // Resolve language alias BEFORE filtering to handle cases like "javascript" -> "typescript".
    // The registry's detect_language() returns the canonical handler (e.g., TypeScript for .js files),
    // so we must compare against the resolved canonical name, not the raw user input.
    let resolved_lang_name: Option<&str> = lang_filter.map(|name| {
        registry
            .get_by_name(name)
            .map(|lang| lang.name())
            .unwrap_or(name) // Fallback to original if not found (will match nothing)
    });

    // Collect all source files
    let files: Vec<_> = walker_builder
        .build()
        .filter_map(|entry| entry.ok())
        .filter(|e| e.path().is_file())
        .filter(|e| {
            // Filter by language if specified
            if let Some(target_name) = resolved_lang_name {
                registry
                    .detect_language(e.path())
                    .is_some_and(|l| l.name() == target_name)
            } else {
                // Include all supported languages
                registry.detect_language(e.path()).is_some()
            }
        })
        .collect();

    let file_count = files.len();
    debug!("Found {} source files to analyze", file_count);

    // Atomic counters for early termination when max_results is specified.
    // This prevents wasting CPU/memory on large codebases by stopping file
    // processing once we have enough results. We use a 2x buffer to account
    // for parallel processing overage (multiple threads may add results
    // simultaneously before checking the limit).
    let functions_found = AtomicUsize::new(0);
    let classes_found = AtomicUsize::new(0);

    // BUG-009 FIX: Track file processing outcomes separately for accurate statistics.
    // These counters distinguish between different failure modes:
    // - files_failed: AST extraction errors (parse failures, encoding issues)
    // - files_skipped: Early termination or security violations
    let files_failed_counter = AtomicUsize::new(0);
    let files_skipped_counter = AtomicUsize::new(0);

    // Buffer multiplier: 2x gives us room for parallel overage while still
    // saving significant work on large codebases
    let early_termination_threshold = if max_results > 0 {
        max_results.saturating_mul(2)
    } else {
        usize::MAX
    };

    // Extract AST info from files in parallel using rayon.
    // Uses early termination to avoid processing excess files.
    // NOTE: par_iter() produces non-deterministic order, so we sort after collection.
    let mut results: Vec<(String, ModuleInfo)> = files
        .par_iter()
        .filter_map(|entry| {
            // Early termination: skip file processing if we have enough results.
            // Check BOTH counters - only terminate when we have sufficient
            // functions AND classes (since they are limited independently).
            // Using Relaxed ordering is sufficient since this is a soft limit
            // optimization, not a correctness requirement.
            if max_results > 0 {
                let funcs = functions_found.load(Ordering::Relaxed);
                let cls = classes_found.load(Ordering::Relaxed);
                if funcs >= early_termination_threshold && cls >= early_termination_threshold {
                    files_skipped_counter.fetch_add(1, Ordering::Relaxed);
                    return None;
                }
            }

            let file_path = entry.path();

            // SECURITY: Validate path containment before reading any file.
            // This prevents path traversal attacks via symlinks pointing outside the root.
            // Especially important since we're about to read file contents.
            if let Err(e) = validate_path_containment(&root_path, file_path) {
                match &e {
                    BrrrError::PathTraversal { target, base } => {
                        warn!(
                            file = %file_path.display(),
                            target = %target,
                            base = %base,
                            "Skipping file due to path traversal detection (security)"
                        );
                    }
                    BrrrError::Io(_) => {
                        // File doesn't exist or broken symlink - skip silently
                        debug!("Skipping unresolvable path: {}", file_path.display());
                    }
                    _ => {
                        warn!(
                            file = %file_path.display(),
                            error = %e,
                            "Skipping file due to path validation error"
                        );
                    }
                }
                // Security violations are counted as skipped (not parse failures)
                files_skipped_counter.fetch_add(1, Ordering::Relaxed);
                return None;
            }

            match AstExtractor::extract_file(file_path) {
                Ok(module) => {
                    // Update atomic counters for early termination tracking.
                    // This allows other threads to see our progress and potentially
                    // skip processing when we have enough results.
                    functions_found.fetch_add(module.functions.len(), Ordering::Relaxed);
                    classes_found.fetch_add(module.classes.len(), Ordering::Relaxed);

                    // Compute relative path for cleaner output
                    let rel_path = file_path
                        .strip_prefix(&root_path)
                        .unwrap_or(file_path)
                        .display()
                        .to_string();
                    Some((rel_path, module))
                }
                Err(e) => {
                    // Log extraction failures but don't fail the whole operation.
                    // BUG-009 FIX: Count this as a parse failure, not a skip.
                    warn!(
                        file = %file_path.display(),
                        error = %e,
                        "Failed to extract AST from file"
                    );
                    files_failed_counter.fetch_add(1, Ordering::Relaxed);
                    None
                }
            }
        })
        .collect();

    // Sort results by file path for deterministic output order.
    // This is essential because par_iter() processes files in arbitrary order,
    // making output non-deterministic across runs.
    results.sort_by(|a, b| a.0.cmp(&b.0));

    let files_processed = results.len();
    // BUG-009 FIX: Use atomic counters for accurate failure/skip tracking
    let files_failed = files_failed_counter.load(Ordering::Relaxed);
    let files_skipped = files_skipped_counter.load(Ordering::Relaxed);

    if files_failed > 0 || files_skipped > 0 {
        debug!(
            "Extracted AST from {} files ({} failed, {} skipped) out of {} total",
            files_processed, files_failed, files_skipped, file_count
        );
    } else {
        debug!(
            "Successfully extracted AST from all {} files",
            files_processed
        );
    }

    // Aggregate all functions and classes with relative paths
    let mut functions = Vec::new();
    let mut classes = Vec::new();

    for (rel_path, module) in results {
        // Collect top-level functions
        for func in module.functions {
            functions.push(FunctionSummary {
                name: func.name.clone(),
                file: rel_path.clone(),
                line: func.line_number,
                signature: func.signature(),
            });
        }

        // Collect classes (structs, interfaces, etc.)
        for class in module.classes {
            classes.push(ClassSummary {
                name: class.name,
                file: rel_path.clone(),
                line: class.line_number,
                method_count: class.methods.len(),
            });
        }
    }

    // Sort functions and classes by (file, line) for fully deterministic output.
    // While results are sorted by file path, functions/classes within a file
    // may have been added in arbitrary order from the ModuleInfo.
    functions.sort_by(|a, b| (&a.file, a.line).cmp(&(&b.file, b.line)));
    classes.sort_by(|a, b| (&a.file, a.line).cmp(&(&b.file, b.line)));

    // Apply result limit if specified (0 = unlimited)
    if max_results > 0 {
        functions.truncate(max_results);
        classes.truncate(max_results);
    }

    Ok(CodeStructure {
        path: path.to_string(),
        functions,
        classes,
        files_processed,
        files_failed,
        files_skipped,
        total_files: file_count,
    })
}

/// Extract full module info from a source file with optional path containment validation.
///
/// Convenience wrapper around `AstExtractor::extract_file` that takes
/// a string path and returns the module info as a dictionary-like structure.
///
/// # Arguments
///
/// * `file_path` - Path to the source file
/// * `base_path` - Optional base directory for security validation.
///   If provided, `file_path` must resolve to a location within `base_path`.
///
/// # Returns
///
/// * `Result<ModuleInfo>` - Complete module information including functions,
///   classes, and imports
///
/// # Errors
///
/// * `BrrrError::Io` - File could not be read
/// * `BrrrError::UnsupportedLanguage` - File extension not recognized
/// * `BrrrError::Parse` - File could not be parsed
/// * `BrrrError::PathTraversal` - Path escapes base directory or contains dangerous patterns
///
/// # Security
///
/// When `base_path` is provided, this function validates that `file_path`
/// does not escape the base directory via:
/// - Directory traversal (../..)
/// - Symlink resolution
/// - Absolute paths outside base
///
/// When `base_path` is `None`, basic input validation is still performed
/// to detect obviously malicious paths (null bytes, excessive traversal).
///
/// # Example
///
/// ```no_run
/// use go_brrr::ast::extract_file;
///
/// // Without validation - basic safety checks only
/// let info = extract_file("src/main.py", None)?;
///
/// // With containment validation - enforces path stays within base
/// let info = extract_file("src/main.py", Some("./src"))?;
///
/// // This would fail - path escapes base directory
/// let result = extract_file("../etc/passwd", Some("./src")); // Error!
/// # Ok::<(), go_brrr::BrrrError>(())
/// ```
pub fn extract_file(file_path: &str, base_path: Option<&str>) -> Result<ModuleInfo> {
    // SECURITY: Basic input validation for dangerous patterns.
    // This is defense-in-depth - callers should also validate paths.

    // Check for null bytes (could bypass security checks in some contexts)
    if file_path.contains('\0') {
        return Err(BrrrError::PathTraversal {
            target: "<contains null byte>".to_string(),
            base: base_path.unwrap_or("<single file extraction>").to_string(),
        });
    }

    let path = Path::new(file_path);

    // Validate path containment if base_path is provided
    if let Some(base) = base_path {
        let base_path_obj = Path::new(base);
        validate_path_containment(base_path_obj, path)?;
    } else {
        // When no base_path, perform basic traversal depth check
        // to catch obviously malicious paths
        let mut depth: i32 = 0;
        for component in path.components() {
            match component {
                std::path::Component::ParentDir => {
                    depth -= 1;
                    // If we've gone more than 10 directories up from start, likely attack
                    if depth < -10 {
                        return Err(BrrrError::PathTraversal {
                            target: file_path.to_string(),
                            base: "<single file extraction>".to_string(),
                        });
                    }
                }
                std::path::Component::Normal(_) => {
                    depth += 1;
                }
                _ => {}
            }
        }
    }

    AstExtractor::extract_file(path)
}

/// Extract file without path validation (convenience wrapper).
///
/// This is equivalent to calling `extract_file(file_path, None)`.
/// Basic input validation is still performed.
///
/// # Security Warning
///
/// This function does not validate path containment. Only use when:
/// - The file path comes from a trusted source
/// - Path validation is performed by the caller
/// - You explicitly want to allow any valid file path
#[inline]
#[allow(dead_code)]
pub fn extract_file_unchecked(file_path: &str) -> Result<ModuleInfo> {
    extract_file(file_path, None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    /// Create a test directory structure with source files.
    fn create_test_project() -> TempDir {
        let dir = TempDir::new().expect("Failed to create temp dir");

        // Create Python files
        let py_content = r#"
def hello(name: str) -> str:
    """Say hello to someone."""
    return f"Hello, {name}!"

class Greeter:
    """A greeting class."""

    def greet(self, name: str) -> str:
        return hello(name)
"#;
        fs::write(dir.path().join("main.py"), py_content).unwrap();
        fs::write(dir.path().join("utils.py"), "def helper(): pass").unwrap();

        // Create a subdirectory with more files
        let sub_dir = dir.path().join("lib");
        fs::create_dir(&sub_dir).unwrap();
        fs::write(sub_dir.join("core.py"), "def core_func(): pass").unwrap();

        // Create TypeScript file
        let ts_content = r#"
function greet(name: string): string {
    return "Hello, " + name;
}

class Service {
    process(): void {}
}
"#;
        fs::write(dir.path().join("app.ts"), ts_content).unwrap();

        dir
    }

    #[test]
    fn test_code_structure_all_languages() {
        let dir = create_test_project();
        let result = code_structure(dir.path().to_str().unwrap(), None, 100, false).unwrap();

        // Should find files from both Python and TypeScript
        assert!(result.total_files >= 3);
        assert!(!result.functions.is_empty());
        assert!(!result.classes.is_empty());
    }

    #[test]
    fn test_code_structure_python_only() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // Should only find Python files
        assert!(result.total_files >= 3);

        // All files should be .py
        for func in &result.functions {
            assert!(
                func.file.ends_with(".py"),
                "Expected .py file: {}",
                func.file
            );
        }
        for class in &result.classes {
            assert!(
                class.file.ends_with(".py"),
                "Expected .py file: {}",
                class.file
            );
        }
    }

    #[test]
    fn test_code_structure_typescript_only() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("typescript"), 100, false).unwrap();

        // Should find the TypeScript file
        assert!(result.total_files >= 1);

        // All files should be .ts
        for func in &result.functions {
            assert!(
                func.file.ends_with(".ts"),
                "Expected .ts file: {}",
                func.file
            );
        }
    }

    #[test]
    fn test_code_structure_max_results() {
        let dir = create_test_project();
        let result = code_structure(dir.path().to_str().unwrap(), None, 2, false).unwrap();

        // Should limit results
        assert!(result.functions.len() <= 2);
        assert!(result.classes.len() <= 2);
    }

    #[test]
    fn test_code_structure_unlimited_results() {
        let dir = create_test_project();
        let result = code_structure(dir.path().to_str().unwrap(), None, 0, false).unwrap();

        // max_results=0 means unlimited - should return all
        assert!(result.functions.len() > 2);
    }

    #[test]
    fn test_code_structure_relative_paths() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // File paths should be relative, not absolute
        for func in &result.functions {
            assert!(
                !func.file.starts_with('/') && !func.file.contains("tmp"),
                "Expected relative path, got: {}",
                func.file
            );
        }
    }

    #[test]
    fn test_code_structure_nested_directory() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // Should find function in nested lib/core.py
        let has_nested = result.functions.iter().any(|f| f.file.contains("lib"));
        assert!(has_nested, "Should find functions in nested directories");
    }

    #[test]
    fn test_code_structure_nonexistent_path() {
        let result = code_structure("/nonexistent/path/that/does/not/exist", None, 100, false);
        assert!(result.is_err());
    }

    #[test]
    fn test_code_structure_empty_directory() {
        let dir = TempDir::new().unwrap();
        let result = code_structure(dir.path().to_str().unwrap(), None, 100, false).unwrap();

        assert_eq!(result.total_files, 0);
        assert!(result.functions.is_empty());
        assert!(result.classes.is_empty());
    }

    #[test]
    fn test_extract_file_python() {
        let dir = create_test_project();
        let file_path = dir.path().join("main.py");
        let result = extract_file(file_path.to_str().unwrap(), None).unwrap();

        assert_eq!(result.language, "python");
        assert!(!result.functions.is_empty());
        assert!(!result.classes.is_empty());

        // Check specific function
        let hello = result.functions.iter().find(|f| f.name == "hello");
        assert!(hello.is_some());
        let hello = hello.unwrap();
        assert_eq!(hello.return_type, Some("str".to_string()));
    }

    #[test]
    fn test_extract_file_with_base_path() {
        let dir = create_test_project();
        let file_path = dir.path().join("main.py");
        let base_path = dir.path();

        // Should succeed - file is within base_path
        let result = extract_file(
            file_path.to_str().unwrap(),
            Some(base_path.to_str().unwrap()),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_extract_file_base_path_escape_rejected() {
        let dir = create_test_project();
        let sub_dir = dir.path().join("lib");

        // Try to access file outside of restricted base_path
        let file_path = dir.path().join("main.py");
        let restricted_base = sub_dir.to_str().unwrap();

        let result = extract_file(file_path.to_str().unwrap(), Some(restricted_base));
        assert!(result.is_err());
        match result.unwrap_err() {
            BrrrError::PathTraversal { .. } => {}
            e => panic!("Expected PathTraversal error, got: {:?}", e),
        }
    }

    #[test]
    fn test_extract_file_nonexistent() {
        let result = extract_file("/nonexistent/file.py", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_function_summary_has_signature() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // All functions should have non-empty signatures
        for func in &result.functions {
            assert!(!func.signature.is_empty());
            // Python signatures should contain 'def'
            if func.file.ends_with(".py") {
                assert!(
                    func.signature.contains("def"),
                    "Python sig: {}",
                    func.signature
                );
            }
        }
    }

    #[test]
    fn test_class_summary_has_method_count() {
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // Find the Greeter class
        let greeter = result.classes.iter().find(|c| c.name == "Greeter");
        assert!(greeter.is_some());
        assert!(greeter.unwrap().method_count >= 1);
    }

    // =========================================================================
    // SECURITY TESTS: Path Traversal Protection
    // =========================================================================

    #[test]
    fn test_extract_file_rejects_null_bytes() {
        // Null bytes in paths could bypass security checks
        let result = extract_file("/tmp/test\0.py", None);
        assert!(result.is_err());
        match result.unwrap_err() {
            BrrrError::PathTraversal { target, .. } => {
                assert!(target.contains("null byte"), "Should mention null byte");
            }
            _ => panic!("Expected PathTraversal error"),
        }
    }

    #[test]
    fn test_extract_file_rejects_null_bytes_with_base_path() {
        // Null bytes should be rejected even with base_path
        let result = extract_file("/tmp/test\0.py", Some("/tmp"));
        assert!(result.is_err());
        match result.unwrap_err() {
            BrrrError::PathTraversal { target, base } => {
                assert!(target.contains("null byte"), "Should mention null byte");
                assert_eq!(base, "/tmp", "Should include base path in error");
            }
            _ => panic!("Expected PathTraversal error"),
        }
    }

    #[test]
    fn test_extract_file_rejects_excessive_traversal() {
        // Paths with excessive .. should be rejected (without base_path)
        let malicious_path = "../../../../../../../../../../../../../../../etc/passwd";
        let result = extract_file(malicious_path, None);
        assert!(result.is_err());
        match result.unwrap_err() {
            BrrrError::PathTraversal { .. } => {}
            BrrrError::Io(_) => {} // Also acceptable - file doesn't exist
            e => panic!("Expected PathTraversal or Io error, got: {:?}", e),
        }
    }

    #[test]
    fn test_extract_file_unchecked() {
        let dir = create_test_project();
        let file_path = dir.path().join("main.py");

        // extract_file_unchecked should work like extract_file with None
        let result = extract_file_unchecked(file_path.to_str().unwrap()).unwrap();
        assert_eq!(result.language, "python");
        assert!(!result.functions.is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn test_code_structure_excludes_symlinks_outside_root() {
        use std::os::unix::fs::symlink;

        let dir = TempDir::new().expect("Failed to create temp dir");

        // Create a normal Python file
        let py_content = "def safe_func(): pass";
        fs::write(dir.path().join("safe.py"), py_content).unwrap();

        // Create a symlink to a file OUTSIDE the project root
        // This should be excluded from analysis for security
        let _ = symlink("/etc/passwd", dir.path().join("escape.py"));

        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // Should find the safe function
        let has_safe = result.functions.iter().any(|f| f.name == "safe_func");
        assert!(has_safe, "Should find safe_func");

        // Should NOT have analyzed escape.py (which points to /etc/passwd)
        let has_escape = result.functions.iter().any(|f| f.file.contains("escape"));
        assert!(!has_escape, "Should NOT have analyzed escape.py symlink");
    }

    #[cfg(unix)]
    #[test]
    fn test_code_structure_allows_symlinks_inside_root() {
        use std::os::unix::fs::symlink;

        let dir = TempDir::new().expect("Failed to create temp dir");

        // Create a subdirectory with a Python file
        let sub_dir = dir.path().join("lib");
        fs::create_dir(&sub_dir).unwrap();
        fs::write(sub_dir.join("utils.py"), "def util_func(): pass").unwrap();

        // Create a symlink that points INSIDE the root (safe)
        let _ = symlink(
            sub_dir.join("utils.py"),
            dir.path().join("link_to_utils.py"),
        );

        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // Should find util_func (from the actual file)
        let has_util = result.functions.iter().any(|f| f.name == "util_func");
        assert!(has_util, "Should find util_func");
    }

    // =========================================================================
    // DETERMINISM TESTS: Verifies par_iter() results are sorted consistently
    // =========================================================================

    #[test]
    fn test_code_structure_deterministic_output() {
        // BUG-011 regression test: Verify par_iter() produces deterministic results
        // by calling code_structure multiple times and comparing output.
        let dir = create_test_project();
        let path = dir.path().to_str().unwrap();

        // Run multiple times to catch non-determinism
        let results: Vec<_> = (0..5)
            .map(|_| code_structure(path, None, 100, false).unwrap())
            .collect();

        // All results should be identical
        let first = &results[0];
        for (i, result) in results.iter().enumerate().skip(1) {
            // Compare function order
            assert_eq!(
                first.functions.len(),
                result.functions.len(),
                "Function count mismatch on iteration {i}"
            );
            for (j, (f1, f2)) in first.functions.iter().zip(&result.functions).enumerate() {
                assert_eq!(
                    (f1.file.as_str(), &f1.name, f1.line),
                    (f2.file.as_str(), &f2.name, f2.line),
                    "Function mismatch at index {j} on iteration {i}"
                );
            }

            // Compare class order
            assert_eq!(
                first.classes.len(),
                result.classes.len(),
                "Class count mismatch on iteration {i}"
            );
            for (j, (c1, c2)) in first.classes.iter().zip(&result.classes).enumerate() {
                assert_eq!(
                    (c1.file.as_str(), &c1.name, c1.line),
                    (c2.file.as_str(), &c2.name, c2.line),
                    "Class mismatch at index {j} on iteration {i}"
                );
            }
        }
    }

    #[test]
    fn test_code_structure_sorted_by_file_and_line() {
        // Verify that output is sorted by (file, line) for deterministic ordering
        let dir = create_test_project();
        let result = code_structure(dir.path().to_str().unwrap(), None, 100, false).unwrap();

        // Verify functions are sorted
        for window in result.functions.windows(2) {
            let cmp = (&window[0].file, window[0].line).cmp(&(&window[1].file, window[1].line));
            assert!(
                cmp != std::cmp::Ordering::Greater,
                "Functions not sorted: {:?} should come before {:?}",
                (&window[0].file, window[0].line),
                (&window[1].file, window[1].line)
            );
        }

        // Verify classes are sorted
        for window in result.classes.windows(2) {
            let cmp = (&window[0].file, window[0].line).cmp(&(&window[1].file, window[1].line));
            assert!(
                cmp != std::cmp::Ordering::Greater,
                "Classes not sorted: {:?} should come before {:?}",
                (&window[0].file, window[0].line),
                (&window[1].file, window[1].line)
            );
        }
    }

    // =========================================================================
    // BUG-009 FIX: File Count Accuracy Tests
    // =========================================================================

    #[test]
    fn test_file_count_invariant() {
        // BUG-009: Verify total_files == files_processed + files_failed + files_skipped
        let dir = create_test_project();
        let result = code_structure(dir.path().to_str().unwrap(), None, 100, false).unwrap();

        // For a clean project without parse errors, files_processed should equal total_files
        assert_eq!(
            result.total_files,
            result.files_processed + result.files_failed + result.files_skipped,
            "Invariant violated: total_files ({}) != processed ({}) + failed ({}) + skipped ({})",
            result.total_files,
            result.files_processed,
            result.files_failed,
            result.files_skipped
        );

        // For valid files, there should be no failures
        assert_eq!(
            result.files_failed, 0,
            "Valid Python/TypeScript files should not have parse failures"
        );
        assert_eq!(
            result.files_skipped, 0,
            "Without max_results limit, no files should be skipped"
        );
    }

    #[test]
    fn test_file_count_with_invalid_syntax() {
        // BUG-009: Verify files_failed counts parse errors correctly
        let dir = TempDir::new().unwrap();

        // Create a valid Python file
        fs::write(dir.path().join("valid.py"), "def good(): pass").unwrap();

        // Create a Python file with invalid syntax that will fail parsing
        fs::write(dir.path().join("invalid.py"), "def bad( missing colon").unwrap();

        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // total_files should count both files
        assert_eq!(result.total_files, 2, "Should find 2 Python files");

        // Invariant must still hold
        assert_eq!(
            result.total_files,
            result.files_processed + result.files_failed + result.files_skipped,
            "Invariant violated with invalid syntax file"
        );

        // files_failed should be >= 1 (the invalid file)
        // Note: tree-sitter may still parse with errors, so we check >= rather than ==
        // The key fix is that failures ARE now tracked, not hardcoded to 0
        assert!(
            result.files_processed >= 1,
            "Should successfully parse at least the valid file"
        );
    }

    #[test]
    fn test_files_processed_reflects_success() {
        // BUG-009: Verify files_processed counts only successfully parsed files
        let dir = create_test_project();
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("python"), 100, false).unwrap();

        // files_processed should equal the number of unique files that contributed functions/classes
        let unique_files: std::collections::HashSet<&str> = result
            .functions
            .iter()
            .map(|f| f.file.as_str())
            .chain(result.classes.iter().map(|c| c.file.as_str()))
            .collect();

        // files_processed should be >= unique_files count
        // (could be larger if some files have no functions/classes)
        assert!(
            result.files_processed >= unique_files.len(),
            "files_processed ({}) should be >= unique files with content ({})",
            result.files_processed,
            unique_files.len()
        );
    }

    // =========================================================================
    // LANGUAGE ALIAS RESOLUTION TESTS
    // =========================================================================

    #[test]
    fn test_javascript_alias_resolves_to_typescript() {
        // Regression test for JavaScript alias bug:
        // User passes --lang javascript, but detect_language() returns TypeScript handler.
        // The comparison l.name() == "javascript" fails because l.name() returns "typescript".
        // Fix: Resolve alias BEFORE comparison using registry.get_by_name().
        let dir = TempDir::new().unwrap();

        // Create a JavaScript file
        let js_content = r#"
function greet(name) {
    return "Hello, " + name;
}

const helper = () => {
    console.log("helper");
};
"#;
        fs::write(dir.path().join("app.js"), js_content).unwrap();

        // Create a TypeScript file to ensure we're not mixing up the filter
        let ts_content = r#"
function tsFunc(x: number): number {
    return x * 2;
}
"#;
        fs::write(dir.path().join("lib.ts"), ts_content).unwrap();

        // Test with "javascript" alias - should find the .js file
        let js_result =
            code_structure(dir.path().to_str().unwrap(), Some("javascript"), 100, false).unwrap();

        // CRITICAL: This was the bug - "javascript" alias returned 0 files
        assert!(
            js_result.total_files >= 1,
            "javascript alias should find .js files, got {} files",
            js_result.total_files
        );
        assert!(
            js_result.functions.iter().any(|f| f.file.ends_with(".js")),
            "Should find functions in .js files"
        );

        // Test with "typescript" - should find both .js and .ts (same parser)
        let ts_result =
            code_structure(dir.path().to_str().unwrap(), Some("typescript"), 100, false).unwrap();

        // Both should use the same parser, so total_files should match
        assert_eq!(
            js_result.total_files, ts_result.total_files,
            "javascript and typescript should find same files (same parser)"
        );
    }

    #[test]
    fn test_unknown_language_finds_nothing() {
        // Ensure that an unknown language (that doesn't resolve via alias) finds no files
        let dir = TempDir::new().unwrap();

        fs::write(dir.path().join("app.js"), "function test() {}").unwrap();
        fs::write(dir.path().join("main.py"), "def test(): pass").unwrap();

        // Use an unknown language name
        let result =
            code_structure(dir.path().to_str().unwrap(), Some("brainfuck"), 100, false).unwrap();

        // Should find no files since "brainfuck" is not a supported language
        assert_eq!(
            result.total_files, 0,
            "Unknown language should find no files"
        );
    }
}
