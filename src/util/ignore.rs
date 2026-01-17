//! BRRR ignore file handling (.brrrignore).
//!
//! Provides gitignore-style pattern matching for excluding files from indexing.
//! Only loads `.brrrignore` patterns - `.gitignore` is handled separately by
//! `WalkBuilder` in scanner code for efficiency.
//!
//! Uses the `ignore` crate's gitignore implementation for pattern matching.
//!
//! # Design Note
//!
//! This module intentionally does NOT load `.gitignore` to avoid duplicate
//! processing. When using `ignore::WalkBuilder` (e.g., in scanner.rs),
//! gitignore is handled natively and efficiently. This separation ensures:
//! - No duplicate pattern matching overhead
//! - Consistent behavior with Python implementation (which only uses .brrrignore)
//! - Clear separation of concerns

use std::path::{Path, PathBuf};

use ignore::gitignore::{Gitignore, GitignoreBuilder};
use memchr::memchr_iter;
use once_cell::sync::Lazy;

use crate::error::BrrrError;

// =============================================================================
// SIMD-Accelerated Pattern Parsing
// =============================================================================

/// Pre-parsed default pattern boundaries (start, end indices into `DEFAULT_PATTERNS`).
///
/// Parsed once at first access using SIMD-accelerated newline finding via `memchr`.
/// Excludes comments and empty lines. Avoids re-parsing on every `BrrrIgnore::new()`.
static PARSED_DEFAULT_PATTERNS: Lazy<Vec<(usize, usize)>> = Lazy::new(|| {
    parse_pattern_bounds_simd(DEFAULT_PATTERNS.as_bytes())
});

/// Parse pattern boundaries from content using SIMD-accelerated newline finding.
///
/// Returns `(start, end)` byte offsets for each valid pattern (non-empty, non-comment).
/// Uses `memchr` which employs SIMD on x86_64 (SSE2/AVX2) and aarch64 (NEON).
///
/// # Performance
///
/// - O(n) single pass through content
/// - SIMD-accelerated newline search (processes 16-32 bytes per instruction)
/// - No heap allocations for intermediate strings
/// - Pre-sized vector to avoid reallocations
#[inline]
fn parse_pattern_bounds_simd(bytes: &[u8]) -> Vec<(usize, usize)> {
    // Pre-allocate for typical .brrrignore size (~50-100 patterns)
    let mut patterns = Vec::with_capacity(64);
    let mut line_start = 0;

    // SIMD-accelerated newline finding via memchr
    // On x86_64: uses SSE2/AVX2 to scan 16-32 bytes per cycle
    // On aarch64: uses NEON for similar throughput
    for newline_pos in memchr_iter(b'\n', bytes) {
        if let Some((ps, pe)) = find_pattern_bounds_in_line(&bytes[line_start..newline_pos]) {
            patterns.push((line_start + ps, line_start + pe));
        }
        line_start = newline_pos + 1;
    }

    // Handle final line without trailing newline
    if line_start < bytes.len() {
        if let Some((ps, pe)) = find_pattern_bounds_in_line(&bytes[line_start..]) {
            patterns.push((line_start + ps, line_start + pe));
        }
    }

    patterns
}

/// Find pattern boundaries within a single line (trimmed, non-comment).
///
/// Returns `None` for empty lines or comments, `Some((start, end))` for valid patterns.
/// All offsets are relative to the input slice.
#[inline]
fn find_pattern_bounds_in_line(line: &[u8]) -> Option<(usize, usize)> {
    // Find first non-whitespace byte (left trim)
    let start = line.iter().position(|&b| !b.is_ascii_whitespace())?;

    // Skip comment lines (# prefix)
    if line[start] == b'#' {
        return None;
    }

    // Find last non-whitespace byte (right trim)
    let end = line
        .iter()
        .rposition(|&b| !b.is_ascii_whitespace())
        .map_or(start, |i| i + 1);

    Some((start, end))
}

/// Default ignore patterns used when no `.brrrignore` exists.
///
/// Note: Used by library crate (semantic/extractor.rs), not by binary crate.
#[allow(dead_code)]
pub const DEFAULT_PATTERNS: &str = r#"# BRRR ignore patterns (gitignore syntax)
# Docs: https://git-scm.com/docs/gitignore

# ===================
# Dependencies
# ===================
node_modules/
.venv/
venv/
env/
__pycache__/
.tox/
.nox/
.pytest_cache/
.mypy_cache/
.ruff_cache/
vendor/
Pods/

# ===================
# Build outputs
# ===================
dist/
build/
out/
target/
*.egg-info/
*.whl
*.pyc
*.pyo

# ===================
# Binary/large files
# ===================
*.so
*.dylib
*.dll
*.exe
*.bin
*.o
*.a
*.lib

# ===================
# IDE/editors
# ===================
.idea/
.vscode/
*.swp
*.swo
*~

# ===================
# Security (always exclude)
# ===================
.env
.env.*
*.pem
*.key
*.p12
*.pfx
credentials.*
secrets.*

# ===================
# Version control
# ===================
.git/
.hg/
.svn/

# ===================
# OS files
# ===================
.DS_Store
Thumbs.db
"#;

/// Wrapper around `ignore::gitignore::Gitignore` for BRRR-specific ignore patterns.
///
/// Loads patterns from:
/// - `.brrrignore` (project-specific patterns)
/// - Built-in defaults (when no `.brrrignore` exists)
///
/// Note: `.gitignore` is NOT loaded here to avoid duplicate processing.
/// Use `ignore::WalkBuilder` (with `git_ignore(true)`) for gitignore support.
///
/// Note: Used by library crate (semantic/extractor.rs), not by binary crate.
#[allow(dead_code)]
#[derive(Debug)]
pub struct BrrrIgnore {
    /// The compiled gitignore matcher
    matcher: Gitignore,
    /// Project root directory (for relative path matching)
    root: PathBuf,
}

#[allow(dead_code)]
impl BrrrIgnore {
    /// Create a new BrrrIgnore from a project directory.
    ///
    /// Loads patterns from `.brrrignore` if it exists, otherwise falls back
    /// to built-in defaults. Does NOT load `.gitignore` - that is handled
    /// separately by `WalkBuilder` in scanner code.
    ///
    /// # Arguments
    ///
    /// * `project_dir` - Root directory of the project
    ///
    /// # Returns
    ///
    /// A `Result<BrrrIgnore, BrrrError>` with compiled patterns.
    ///
    /// # Errors
    ///
    /// Returns `BrrrError::Config` if the gitignore matcher cannot be built.
    ///
    /// # Design Note
    ///
    /// This method intentionally does NOT load `.gitignore` to:
    /// 1. Avoid duplicate processing when used with `WalkBuilder`
    /// 2. Match Python implementation behavior (which only uses .brrrignore)
    /// 3. Keep clear separation of concerns
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::util::ignore::BrrrIgnore;
    /// use std::path::Path;
    ///
    /// let ignore = BrrrIgnore::new(Path::new("./my_project")).unwrap();
    /// assert!(!ignore.is_ignored(Path::new("src/main.rs")));
    /// assert!(ignore.is_ignored(Path::new("node_modules/package/index.js")));
    /// ```
    pub fn new(project_dir: &Path) -> Result<Self, BrrrError> {
        let root = project_dir
            .canonicalize()
            .unwrap_or_else(|_| project_dir.to_path_buf());

        let brrrignore_path = root.join(".brrrignore");

        let mut builder = GitignoreBuilder::new(&root);

        // Load .brrrignore if it exists
        // NOTE: We intentionally do NOT load .gitignore here.
        // WalkBuilder handles gitignore natively and efficiently.
        let loaded_brrrignore = if brrrignore_path.exists() {
            if let Some(err) = builder.add(&brrrignore_path) {
                tracing::warn!("Error loading .brrrignore: {}", err);
                false
            } else {
                tracing::debug!("Loaded .brrrignore from {:?}", brrrignore_path);
                true
            }
        } else {
            false
        };

        // If no .brrrignore found, use pre-parsed defaults (SIMD-accelerated)
        if !loaded_brrrignore {
            // Use pre-computed pattern boundaries from lazy static
            // Patterns are parsed once using SIMD-accelerated newline finding
            for &(start, end) in PARSED_DEFAULT_PATTERNS.iter() {
                let pattern = &DEFAULT_PATTERNS[start..end];
                if let Err(e) = builder.add_line(None, pattern) {
                    tracing::warn!("Invalid pattern '{}': {}", pattern, e);
                }
            }
            tracing::debug!(
                "Using {} default ignore patterns (no .brrrignore found)",
                PARSED_DEFAULT_PATTERNS.len()
            );
        }

        // Try to build the matcher with patterns
        let matcher = match builder.build() {
            Ok(m) => m,
            Err(e) => {
                tracing::warn!("Failed to build gitignore matcher: {}, trying empty fallback", e);
                // Try empty matcher as fallback
                GitignoreBuilder::new(&root)
                    .build()
                    .map_err(|fallback_err| {
                        BrrrError::Config(format!(
                            "Failed to build gitignore matcher: {}; fallback also failed: {}",
                            e, fallback_err
                        ))
                    })?
            }
        };

        Ok(Self { matcher, root })
    }

    /// Check if a path should be ignored.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to check (can be absolute or relative to project root)
    ///
    /// # Returns
    ///
    /// `true` if the path matches any ignore pattern.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use go_brrr::util::ignore::BrrrIgnore;
    /// use std::path::Path;
    ///
    /// let ignore = BrrrIgnore::new(Path::new("./project")).unwrap();
    ///
    /// // Common patterns that should be ignored
    /// assert!(ignore.is_ignored(Path::new("node_modules/pkg/index.js")));
    /// assert!(ignore.is_ignored(Path::new("__pycache__/module.pyc")));
    /// assert!(ignore.is_ignored(Path::new(".git/config")));
    /// assert!(ignore.is_ignored(Path::new("target/debug/binary")));
    ///
    /// // Source files should not be ignored
    /// assert!(!ignore.is_ignored(Path::new("src/main.rs")));
    /// ```
    #[must_use]
    pub fn is_ignored(&self, path: &Path) -> bool {
        // Make path relative to root for matching
        let relative_path = if path.is_absolute() {
            path.strip_prefix(&self.root)
                .map(Path::to_path_buf)
                .unwrap_or_else(|_| path.to_path_buf())
        } else {
            path.to_path_buf()
        };

        // Check if path is a directory (gitignore treats dirs specially)
        let is_dir = path.is_dir()
            || relative_path.to_string_lossy().ends_with('/')
            || self.root.join(&relative_path).is_dir();

        // Use the matcher
        self.matcher
            .matched_path_or_any_parents(&relative_path, is_dir)
            .is_ignore()
    }

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
    fn test_brrr_ignore_default_patterns() {
        let temp_dir = TempDir::new().unwrap();
        let ignore = BrrrIgnore::new(temp_dir.path()).unwrap();

        // Should ignore common patterns
        assert!(ignore.is_ignored(Path::new("node_modules/pkg/index.js")));
        assert!(ignore.is_ignored(Path::new("__pycache__/module.pyc")));
        assert!(ignore.is_ignored(Path::new(".git/config")));
        assert!(ignore.is_ignored(Path::new("target/debug/binary")));
        assert!(ignore.is_ignored(Path::new(".venv/bin/python")));
    }

    #[test]
    fn test_brrr_ignore_allows_source_files() {
        let temp_dir = TempDir::new().unwrap();
        let ignore = BrrrIgnore::new(temp_dir.path()).unwrap();

        // Should NOT ignore source files
        assert!(!ignore.is_ignored(Path::new("src/main.rs")));
        assert!(!ignore.is_ignored(Path::new("lib/utils.py")));
        assert!(!ignore.is_ignored(Path::new("app.ts")));
    }

    #[test]
    fn test_brrr_ignore_custom_patterns() {
        let temp_dir = TempDir::new().unwrap();

        // Create custom .brrrignore
        fs::write(
            temp_dir.path().join(".brrrignore"),
            "custom_ignore/\n*.custom\n",
        )
        .unwrap();

        let ignore = BrrrIgnore::new(temp_dir.path()).unwrap();

        // Custom patterns should work
        assert!(ignore.is_ignored(Path::new("custom_ignore/file.txt")));
        assert!(ignore.is_ignored(Path::new("test.custom")));

        // Default patterns should still work (from gitignore if present)
        // Note: with custom .brrrignore, defaults may not be loaded
        // unless we also have .gitignore
    }

    #[test]
    fn test_gitignore_not_loaded_by_brrrignore() {
        // BrrrIgnore does NOT load .gitignore - that's handled by WalkBuilder.
        // This test verifies that behavior.
        let temp_dir = TempDir::new().unwrap();

        // Create .gitignore with custom pattern (should be ignored by BrrrIgnore)
        fs::write(temp_dir.path().join(".gitignore"), "*.log\nlogs/\n").unwrap();

        let ignore = BrrrIgnore::new(temp_dir.path()).unwrap();

        // gitignore patterns should NOT be loaded (defaults are used instead)
        // Default patterns don't include *.log
        assert!(!ignore.is_ignored(Path::new("debug.log")));
        assert!(!ignore.is_ignored(Path::new("logs/app.txt")));

        // Default patterns should still work
        assert!(ignore.is_ignored(Path::new("node_modules/pkg")));
        assert!(ignore.is_ignored(Path::new("__pycache__/module.pyc")));
    }

    #[test]
    fn test_brrrignore_only_no_gitignore() {
        // When both .brrrignore and .gitignore exist, only .brrrignore is loaded.
        // .gitignore is handled separately by WalkBuilder.
        let temp_dir = TempDir::new().unwrap();

        // Create both ignore files
        fs::write(temp_dir.path().join(".gitignore"), "*.txt\n").unwrap();
        fs::write(temp_dir.path().join(".brrrignore"), "*.custom\n").unwrap();

        let ignore = BrrrIgnore::new(temp_dir.path()).unwrap();

        // Only .brrrignore patterns should work
        assert!(ignore.is_ignored(Path::new("test.custom")));

        // .gitignore patterns should NOT be loaded
        // (WalkBuilder handles gitignore separately when scanning files)
        assert!(!ignore.is_ignored(Path::new("test.txt")));
    }

    #[test]
    fn test_simd_pattern_parsing_correctness() {
        // Verify SIMD-accelerated parsing produces correct results
        let test_content = b"# Comment line\n  \npattern1\n  pattern2  \n# Another comment\npattern3\n";
        let bounds = parse_pattern_bounds_simd(test_content);

        // Should extract exactly 3 patterns (comments and empty lines excluded)
        assert_eq!(bounds.len(), 3);

        // Verify each pattern is correctly extracted (trimmed)
        let pattern1 = std::str::from_utf8(&test_content[bounds[0].0..bounds[0].1]).unwrap();
        let pattern2 = std::str::from_utf8(&test_content[bounds[1].0..bounds[1].1]).unwrap();
        let pattern3 = std::str::from_utf8(&test_content[bounds[2].0..bounds[2].1]).unwrap();

        assert_eq!(pattern1, "pattern1");
        assert_eq!(pattern2, "pattern2");
        assert_eq!(pattern3, "pattern3");
    }

    #[test]
    fn test_simd_pattern_parsing_edge_cases() {
        // Empty content
        assert!(parse_pattern_bounds_simd(b"").is_empty());

        // Only comments
        assert!(parse_pattern_bounds_simd(b"# comment\n# another").is_empty());

        // Only whitespace
        assert!(parse_pattern_bounds_simd(b"   \n\t\n  ").is_empty());

        // No trailing newline
        let bounds = parse_pattern_bounds_simd(b"pattern_no_newline");
        assert_eq!(bounds.len(), 1);
        assert_eq!(&b"pattern_no_newline"[bounds[0].0..bounds[0].1], b"pattern_no_newline");

        // Mixed whitespace around pattern
        let bounds = parse_pattern_bounds_simd(b"\t  mixed_ws  \t\n");
        assert_eq!(bounds.len(), 1);
        assert_eq!(&b"\t  mixed_ws  \t\n"[bounds[0].0..bounds[0].1], b"mixed_ws");
    }

    #[test]
    fn test_default_patterns_lazy_static() {
        // Verify lazy static patterns are correctly parsed from DEFAULT_PATTERNS
        let patterns = &*PARSED_DEFAULT_PATTERNS;

        // Should have parsed multiple patterns
        assert!(!patterns.is_empty());

        // Verify some known patterns exist
        let pattern_strs: Vec<&str> = patterns
            .iter()
            .map(|&(s, e)| &DEFAULT_PATTERNS[s..e])
            .collect();

        assert!(pattern_strs.contains(&"node_modules/"));
        assert!(pattern_strs.contains(&"__pycache__/"));
        assert!(pattern_strs.contains(&".git/"));
        assert!(pattern_strs.contains(&"target/"));

        // Comments and empty lines should NOT be present
        assert!(!pattern_strs.iter().any(|p| p.starts_with('#')));
        assert!(!pattern_strs.iter().any(|p| p.is_empty()));
    }
}
