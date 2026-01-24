//! Project file scanner for call graph analysis.
//!
//! Provides efficient file discovery with:
//! - Parallel scanning using rayon for large projects
//! - Respect for .gitignore and .brrrignore patterns
//! - Language-based and extension-based filtering
//! - File metadata collection (size, modification time, detected language)
//! - Comprehensive error handling with visibility into skipped files
//!
//! # Performance
//!
//! Sequential scanning is used for projects with fewer than 15 files
//! (see `MIN_FILES_FOR_PARALLEL`) to avoid thread spawn overhead.
//! For larger projects, rayon's work-stealing parallelism provides significant
//! speedups on multi-core systems. This threshold matches the Python implementation
//! for consistent behavior across both backends.
//!
//! # Error Handling
//!
//! The scanner collects errors encountered during traversal rather than silently
//! dropping them. Errors include permission denied, broken symlinks, and I/O errors.
//! Users can choose to fail on errors or continue with warnings via `ScanConfig`.

use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use parking_lot::Mutex;
use rustc_hash::{FxHashMap, FxHashSet};

use ignore::overrides::OverrideBuilder;
use ignore::WalkBuilder;
use rayon::prelude::*;
use tracing::{debug, warn};

use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

/// Minimum number of files before parallel processing is enabled.
///
/// This threshold balances the overhead of thread spawning against
/// the benefits of parallel execution. For small projects, sequential
/// processing is often faster due to reduced synchronization overhead.
///
/// Value of 15 matches the Python implementation for consistent behavior
/// across both backends. Process spawn overhead in Python (~50-100ms per worker)
/// is similar to Rayon's thread pool initialization cost for small workloads.
///
/// # Performance Notes
///
/// - Below 15 files: Sequential is typically faster (thread spawn overhead dominates)
/// - 15-50 files: Parallel provides modest speedup on multi-core systems
/// - 50+ files: Parallel provides significant speedup (2-4x on 4+ cores)
const MIN_FILES_FOR_PARALLEL: usize = 15;

/// Category of scan error for programmatic handling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScanErrorKind {
    /// Permission denied when accessing file or directory.
    PermissionDenied,
    /// Broken symbolic link that could not be followed.
    BrokenSymlink,
    /// Generic I/O error during traversal.
    IoError,
    /// Directory loop detected (symlink cycle).
    DirectoryLoop,
    /// Other unclassified error.
    Other,
}

impl fmt::Display for ScanErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScanErrorKind::PermissionDenied => write!(f, "permission denied"),
            ScanErrorKind::BrokenSymlink => write!(f, "broken symlink"),
            ScanErrorKind::IoError => write!(f, "I/O error"),
            ScanErrorKind::DirectoryLoop => write!(f, "directory loop"),
            ScanErrorKind::Other => write!(f, "other error"),
        }
    }
}

/// Error encountered during file scanning.
///
/// Contains details about what went wrong and where, allowing users
/// to diagnose and potentially fix scanning issues.
#[derive(Debug, Clone)]
pub struct ScanError {
    /// Path where the error occurred (if available).
    pub path: Option<PathBuf>,
    /// Human-readable error message.
    pub message: String,
    /// Category of the error for programmatic handling.
    pub kind: ScanErrorKind,
}

impl ScanError {
    /// Create a new scan error from an ignore::Error.
    ///
    /// Extracts path information by pattern matching on the error
    /// variants, since `ignore::Error` doesn't provide direct accessor methods.
    fn from_ignore_error(err: &ignore::Error) -> Self {
        let message = err.to_string();

        // Extract path by pattern matching on error variants
        let path = Self::extract_path(err);

        // Classify the error kind
        let kind = if let Some(io_err) = err.io_error() {
            match io_err.kind() {
                std::io::ErrorKind::PermissionDenied => ScanErrorKind::PermissionDenied,
                std::io::ErrorKind::NotFound => ScanErrorKind::BrokenSymlink,
                _ => ScanErrorKind::IoError,
            }
        } else {
            Self::classify_from_message(&message)
        };

        Self {
            path,
            message,
            kind,
        }
    }

    /// Extract path from ignore::Error variants recursively.
    fn extract_path(err: &ignore::Error) -> Option<PathBuf> {
        match err {
            ignore::Error::WithPath { path, .. } => Some(path.clone()),
            ignore::Error::WithDepth { err: inner, .. } => Self::extract_path(inner),
            ignore::Error::Loop { child, .. } => Some(child.clone()),
            _ => None,
        }
    }

    /// Classify error kind from message content when io_error is unavailable.
    fn classify_from_message(message: &str) -> ScanErrorKind {
        let msg_lower = message.to_lowercase();
        if msg_lower.contains("loop") || msg_lower.contains("cycle") {
            ScanErrorKind::DirectoryLoop
        } else if msg_lower.contains("symlink") || msg_lower.contains("link") {
            ScanErrorKind::BrokenSymlink
        } else if msg_lower.contains("permission") {
            ScanErrorKind::PermissionDenied
        } else {
            ScanErrorKind::Other
        }
    }
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref path) = self.path {
            write!(f, "{}: {} ({})", path.display(), self.message, self.kind)
        } else {
            write!(f, "{} ({})", self.message, self.kind)
        }
    }
}

/// Behavior when scan errors are encountered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ErrorHandling {
    /// Continue scanning, collecting errors for later review.
    /// This is the default behavior for maximum file discovery.
    #[default]
    CollectAndContinue,
    /// Stop scanning immediately on first error.
    #[allow(dead_code)]
    FailFast,
    /// Log warnings but don't collect errors (legacy behavior).
    #[allow(dead_code)]
    LogOnly,
}

/// Metadata collected for each scanned file.
#[derive(Debug, Clone)]
pub struct FileMetadata {
    /// Absolute path to the file.
    pub path: PathBuf,
    /// File size in bytes.
    pub size: u64,
    /// Detected language name (e.g., "python", "typescript").
    pub language: Option<String>,
}

impl FileMetadata {
    /// Create metadata for a file path with pre-cached language detection.
    ///
    /// This avoids redundant language detection when the language was already
    /// determined during filtering. Reduces language detection calls from 2-3
    /// per file to exactly 1.
    fn from_path_with_language(path: PathBuf, cached_language: Option<String>) -> Option<Self> {
        let metadata = fs::metadata(&path).ok()?;

        // Skip directories (should not happen with WalkBuilder, but safety check)
        if !metadata.is_file() {
            return None;
        }

        Some(Self {
            path,
            size: metadata.len(),
            language: cached_language,
        })
    }
}

/// File entry with cached language detection result.
///
/// Used during scanning to avoid redundant language detection calls.
/// Language is detected exactly once when the file is first encountered,
/// then reused for filtering and metadata collection.
#[derive(Debug, Clone)]
struct ScannedFile {
    /// Path to the file.
    path: PathBuf,
    /// Cached language name (None if not a supported language).
    language: Option<&'static str>,
}

/// Configuration for project scanning.
#[derive(Debug, Clone, Default)]
pub struct ScanConfig {
    /// Filter by specific language (e.g., "python").
    pub language: Option<String>,
    /// Filter by file extensions (e.g., [".py", ".pyi"]).
    pub extensions: Vec<String>,
    /// Glob patterns to include (e.g., ["src/**/*.rs"]).
    pub include_patterns: Vec<String>,
    /// Glob patterns to exclude (e.g., ["**/test/**"]).
    pub exclude_patterns: Vec<String>,
    /// Whether to follow symbolic links (default: false).
    pub follow_symlinks: bool,
    /// Maximum directory depth (None for unlimited).
    pub max_depth: Option<usize>,
    /// Whether to collect file metadata (default: false for faster scanning).
    pub collect_metadata: bool,
    /// Whether to use parallel scanning (default: true for large projects).
    pub parallel: bool,
    /// Whether to disable default exclude patterns (node_modules, __pycache__, .git, etc.).
    /// Default: false (default excludes are applied).
    /// Set to true when you need to include files from typically-excluded directories
    /// like vendored dependencies in node_modules.
    pub disable_default_excludes: bool,
    /// How to handle errors encountered during scanning.
    /// Default: CollectAndContinue (collect errors but don't stop scanning).
    pub error_handling: ErrorHandling,
    /// Whether to ignore all ignore files (.gitignore, .brrrignore) and include all files.
    /// Default: false (respect ignore files).
    /// Set to true to bypass all ignore file processing (equivalent to --no-ignore flag).
    pub no_ignore: bool,
}

impl ScanConfig {
    /// Create a config for scanning a specific language.
    pub fn for_language(lang: &str) -> Self {
        Self {
            language: Some(lang.to_string()),
            ..Default::default()
        }
    }

    /// Create a config for scanning specific file extensions.
    #[allow(dead_code)]
    pub fn for_extensions(exts: &[&str]) -> Self {
        Self {
            extensions: exts.iter().map(|s| (*s).to_string()).collect(),
            ..Default::default()
        }
    }

    /// Add include patterns.
    #[allow(dead_code)]
    pub fn with_includes(mut self, patterns: &[&str]) -> Self {
        self.include_patterns = patterns.iter().map(|s| (*s).to_string()).collect();
        self
    }

    /// Add exclude patterns.
    #[allow(dead_code)]
    pub fn with_excludes(mut self, patterns: &[&str]) -> Self {
        self.exclude_patterns = patterns.iter().map(|s| (*s).to_string()).collect();
        self
    }

    /// Enable metadata collection.
    #[allow(dead_code)]
    pub fn with_metadata(mut self) -> Self {
        self.collect_metadata = true;
        self
    }

    /// Set maximum traversal depth.
    #[allow(dead_code)]
    pub fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = Some(depth);
        self
    }

    /// Disable default exclude patterns (node_modules, __pycache__, .git, etc.).
    ///
    /// Use this when you need to include files from typically-excluded directories,
    /// such as vendored dependencies in node_modules or build artifacts you want to analyze.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use go_brrr::callgraph::scanner::ScanConfig;
    ///
    /// // Include vendored dependencies from node_modules
    /// let config = ScanConfig::default()
    ///     .with_default_excludes_disabled()
    ///     .with_includes(&["**/node_modules/vendor/**"]);
    /// ```
    #[allow(dead_code)]
    pub fn with_default_excludes_disabled(mut self) -> Self {
        self.disable_default_excludes = true;
        self
    }

    /// Set how errors should be handled during scanning.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use go_brrr::callgraph::scanner::{ScanConfig, ErrorHandling};
    ///
    /// // Fail immediately on any error
    /// let strict_config = ScanConfig::default()
    ///     .with_error_handling(ErrorHandling::FailFast);
    ///
    /// // Collect errors but continue scanning (default)
    /// let permissive_config = ScanConfig::default()
    ///     .with_error_handling(ErrorHandling::CollectAndContinue);
    /// ```
    #[allow(dead_code)]
    pub fn with_error_handling(mut self, handling: ErrorHandling) -> Self {
        self.error_handling = handling;
        self
    }

    /// Configure to fail fast on any error.
    ///
    /// Shorthand for `.with_error_handling(ErrorHandling::FailFast)`.
    #[allow(dead_code)]
    pub fn fail_on_error(mut self) -> Self {
        self.error_handling = ErrorHandling::FailFast;
        self
    }

    /// Set whether to ignore all ignore files (.gitignore, .brrrignore).
    ///
    /// When set to true, all files will be included regardless of ignore patterns.
    /// This is equivalent to the `--no-ignore` CLI flag.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use go_brrr::callgraph::scanner::ScanConfig;
    ///
    /// // Include all files, ignoring .gitignore and .brrrignore
    /// let config = ScanConfig::default()
    ///     .with_no_ignore(true);
    /// ```
    #[allow(dead_code)]
    pub fn with_no_ignore(mut self, no_ignore: bool) -> Self {
        self.no_ignore = no_ignore;
        self
    }
}

/// Filter for matching file extensions during scanning.
///
/// Encapsulates the extension matching logic to enable single-pass filtering
/// during directory traversal, avoiding double-allocation of file vectors.
///
/// # Memory Efficiency
///
/// This struct is designed to be used inline during walker iteration,
/// allowing filters to be applied as files are discovered rather than
/// collecting all files first and then filtering.
struct ExtensionFilter {
    /// Set of allowed extensions (lowercase, without leading dot).
    /// None means accept all files (no extension filtering).
    extensions: Option<FxHashSet<String>>,
}

impl ExtensionFilter {
    /// Create a filter from a set of extensions.
    ///
    /// If the set is empty, filtering is disabled (all files pass).
    fn new(extensions: FxHashSet<String>) -> Self {
        Self {
            extensions: if extensions.is_empty() {
                None
            } else {
                Some(extensions)
            },
        }
    }

    /// Check if a path matches the extension filter.
    ///
    /// Returns true if:
    /// - No extension filter is set (accept all)
    /// - The file's extension (case-insensitive) is in the allowed set
    #[inline]
    fn matches(&self, path: &Path) -> bool {
        match &self.extensions {
            Some(exts) => path
                .extension()
                .and_then(|e| e.to_str())
                .map(|e| exts.contains(&e.to_lowercase()))
                .unwrap_or(false),
            None => true, // No filter, accept all
        }
    }

    /// Check if extension filtering is active.
    #[inline]
    fn is_filtering(&self) -> bool {
        self.extensions.is_some()
    }
}

/// Filter for matching files by language during scanning.
///
/// Uses the language registry to detect and match file languages,
/// enabling single-pass filtering during directory traversal.
struct LanguageFilter<'a> {
    /// Resolved target language name to match (after alias resolution).
    /// None means accept all supported languages.
    target_language: Option<&'a str>,
    /// Reference to the language registry for detection.
    registry: &'a LanguageRegistry,
}

/// Result of language filter matching, includes cached language for reuse.
struct LanguageMatchResult {
    /// Whether the file matches the filter criteria.
    matches: bool,
    /// Cached detected language name (None if not a supported language).
    /// This value can be reused for metadata collection to avoid re-detection.
    language: Option<&'static str>,
}

impl<'a> LanguageFilter<'a> {
    /// Create a filter for a specific language.
    ///
    /// The `resolved_name` should be the canonical language name after
    /// alias resolution (e.g., "typescript" for both "javascript" and "typescript").
    fn new(resolved_name: Option<&'a str>, registry: &'a LanguageRegistry) -> Self {
        Self {
            target_language: resolved_name,
            registry,
        }
    }

    /// Check if a path matches the language filter, returning cached language.
    ///
    /// This method detects language exactly once and returns both the match
    /// result and the detected language for caching. Use this when you need
    /// the language information later (e.g., for metadata collection).
    ///
    /// # Performance
    ///
    /// Language detection is O(1) per file (extension-based lookup), but still
    /// involves string operations and HashMap lookups. Caching the result
    /// eliminates redundant detection calls during metadata collection.
    #[inline]
    fn matches_with_cache(&self, path: &Path, ext_filter: &ExtensionFilter) -> LanguageMatchResult {
        // Detect language once and cache the result
        let detected = self.registry.detect_language(path);
        let language = detected.map(|l| l.name());

        let matches = match self.target_language {
            Some(target_name) => {
                // Language filter active: check if detected language matches target
                language.is_some_and(|l| l == target_name)
            }
            None => {
                // No language filter: accept if extension filter passes OR file is supported
                if ext_filter.is_filtering() {
                    true // Extension filter handles the filtering
                } else {
                    // No filters: only accept supported language files
                    language.is_some()
                }
            }
        };

        LanguageMatchResult { matches, language }
    }
}

/// Result of a project scan with optional metadata.
#[derive(Debug, Clone)]
pub struct ScanResult {
    /// All matching file paths.
    pub files: Vec<PathBuf>,
    /// File metadata (only populated if `collect_metadata` was true).
    pub metadata: Vec<FileMetadata>,
    /// Total bytes scanned.
    pub total_bytes: u64,
    /// Number of files by language.
    pub by_language: FxHashMap<String, usize>,
    /// Errors encountered during scanning.
    /// Contains details about files/directories that could not be accessed.
    pub errors: Vec<ScanError>,
    /// Warning messages for non-fatal issues.
    pub warnings: Vec<String>,
}

impl ScanResult {
    fn new() -> Self {
        Self {
            files: Vec::new(),
            metadata: Vec::new(),
            total_bytes: 0,
            by_language: FxHashMap::default(),
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    fn add_file(&mut self, path: PathBuf) {
        self.files.push(path);
    }

    fn add_metadata(&mut self, meta: FileMetadata) {
        self.total_bytes += meta.size;
        if let Some(ref lang) = meta.language {
            *self.by_language.entry(lang.clone()).or_insert(0) += 1;
        }
        self.metadata.push(meta);
    }

    fn add_error(&mut self, error: ScanError) {
        self.errors.push(error);
    }

    fn add_warning(&mut self, warning: String) {
        self.warnings.push(warning);
    }

    /// Check if the scan encountered any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the count of errors by kind.
    pub fn error_counts(&self) -> FxHashMap<ScanErrorKind, usize> {
        let mut counts = FxHashMap::default();
        for error in &self.errors {
            *counts.entry(error.kind).or_insert(0) += 1;
        }
        counts
    }

    /// Get a summary of scan errors for logging or display.
    pub fn error_summary(&self) -> String {
        if self.errors.is_empty() {
            return String::from("No errors");
        }

        let counts = self.error_counts();
        let parts: Vec<String> = counts
            .iter()
            .map(|(kind, count)| format!("{}: {}", kind, count))
            .collect();

        format!("{} total errors ({})", self.errors.len(), parts.join(", "))
    }
}

/// Scans a project directory for source files.
///
/// Respects .gitignore and .brrrignore patterns, supports filtering by
/// language and extension, and optionally collects file metadata.
///
/// # Example
///
/// ```no_run
/// use go_brrr::callgraph::scanner::{ProjectScanner, ScanConfig};
///
/// let scanner = ProjectScanner::new("/path/to/project").unwrap();
///
/// // Scan all supported files
/// let files = scanner.scan_files().unwrap();
///
/// // Scan only Python files
/// let py_files = scanner.scan_language("python").unwrap();
///
/// // Advanced scanning with config
/// let config = ScanConfig::for_language("rust")
///     .with_excludes(&["**/target/**"])
///     .with_metadata();
/// let result = scanner.scan_with_config(&config).unwrap();
/// ```
pub struct ProjectScanner {
    root: PathBuf,
}

impl ProjectScanner {
    /// Create a new scanner for the given project root.
    ///
    /// # Errors
    ///
    /// Returns an error if the path does not exist or is not a directory.
    pub fn new(path: &str) -> Result<Self> {
        let root = PathBuf::from(path);

        if !root.exists() {
            return Err(BrrrError::Io(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("Project root does not exist: {}", path),
            )));
        }

        if !root.is_dir() {
            return Err(BrrrError::Io(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("Project root is not a directory: {}", path),
            )));
        }

        Ok(Self { root })
    }

    /// Get the project root path.
    #[allow(dead_code)]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Scan for all supported source files.
    ///
    /// Returns file paths for all files with extensions recognized by
    /// the language registry. Respects .gitignore and .brrrignore.
    ///
    /// Note: This method logs warnings for errors but continues scanning.
    /// For full error details, use `scan_files_with_errors()` instead.
    pub fn scan_files(&self) -> Result<Vec<PathBuf>> {
        let result = self.scan_files_with_errors()?;

        // Log warning if errors were encountered
        if result.has_errors() {
            warn!(
                "File scan completed with errors: {}",
                result.error_summary()
            );
            for error in &result.errors {
                debug!("Scan error: {}", error);
            }
        }

        Ok(result.files)
    }

    /// Scan for all supported source files with full error reporting.
    ///
    /// Returns a `ScanResult` containing both the found files and any
    /// errors encountered during scanning (permission denied, broken
    /// symlinks, I/O errors, etc.).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use go_brrr::callgraph::scanner::ProjectScanner;
    ///
    /// let scanner = ProjectScanner::new("/path/to/project").unwrap();
    /// let result = scanner.scan_files_with_errors().unwrap();
    ///
    /// println!("Found {} files", result.files.len());
    /// if result.has_errors() {
    ///     eprintln!("Warning: {}", result.error_summary());
    ///     for error in &result.errors {
    ///         eprintln!("  - {}", error);
    ///     }
    /// }
    /// ```
    pub fn scan_files_with_errors(&self) -> Result<ScanResult> {
        let registry = LanguageRegistry::global();
        let mut result = ScanResult::new();

        for entry_result in self.build_walker(None)? {
            match entry_result {
                Ok(entry) => {
                    if entry.path().is_file() {
                        if registry.detect_language(entry.path()).is_some() {
                            result.add_file(entry.path().to_path_buf());
                        }
                    }
                }
                Err(e) => {
                    let scan_error = ScanError::from_ignore_error(&e);
                    warn!("Failed to scan entry: {}", scan_error);
                    debug!("Error details: {:?}", e);
                    result.add_error(scan_error);
                }
            }
        }

        Ok(result)
    }

    /// Scan for files of a specific language.
    ///
    /// # Arguments
    ///
    /// * `lang_name` - Language identifier (e.g., "python", "typescript", "rust")
    ///
    /// # Errors
    ///
    /// Returns `UnsupportedLanguage` error if the language is not recognized.
    ///
    /// Note: This method logs warnings for errors but continues scanning.
    /// For full error details, use `scan_language_with_errors()` instead.
    #[allow(dead_code)]
    pub fn scan_language(&self, lang_name: &str) -> Result<Vec<PathBuf>> {
        let result = self.scan_language_with_errors(lang_name)?;

        // Log warning if errors were encountered
        if result.has_errors() {
            warn!(
                "Language scan completed with errors: {}",
                result.error_summary()
            );
            for error in &result.errors {
                debug!("Scan error: {}", error);
            }
        }

        Ok(result.files)
    }

    /// Scan for files of a specific language with full error reporting.
    ///
    /// Returns a `ScanResult` containing both the found files and any
    /// errors encountered during scanning.
    ///
    /// # Arguments
    ///
    /// * `lang_name` - Language identifier (e.g., "python", "typescript", "rust")
    ///
    /// # Errors
    ///
    /// Returns `UnsupportedLanguage` error if the language is not recognized.
    #[allow(dead_code)]
    pub fn scan_language_with_errors(&self, lang_name: &str) -> Result<ScanResult> {
        let registry = LanguageRegistry::global();

        // Validate language exists and get the resolved language handler.
        // This handles aliases like "javascript" -> "typescript".
        let target_lang = registry
            .get_by_name(lang_name)
            .ok_or_else(|| BrrrError::UnsupportedLanguage(lang_name.to_string()))?;
        let target_name = target_lang.name();

        let mut result = ScanResult::new();

        for entry_result in self.build_walker(None)? {
            match entry_result {
                Ok(entry) => {
                    if entry.path().is_file() {
                        // Compare against resolved canonical name to handle aliases correctly.
                        // e.g., "javascript" resolves to "typescript", so we compare against "typescript"
                        if registry
                            .detect_language(entry.path())
                            .is_some_and(|l| l.name() == target_name)
                        {
                            result.add_file(entry.path().to_path_buf());
                        }
                    }
                }
                Err(e) => {
                    let scan_error = ScanError::from_ignore_error(&e);
                    warn!("Failed to scan entry: {}", scan_error);
                    debug!("Error details: {:?}", e);
                    result.add_error(scan_error);
                }
            }
        }

        Ok(result)
    }

    /// Scan for files matching specific extensions.
    ///
    /// # Arguments
    ///
    /// * `extensions` - File extensions to match (e.g., [".py", ".pyi"])
    ///
    /// Note: This method logs warnings for errors but continues scanning.
    /// For full error details, use `scan_extensions_with_errors()` instead.
    #[allow(dead_code)]
    pub fn scan_extensions(&self, extensions: &[&str]) -> Result<Vec<PathBuf>> {
        let result = self.scan_extensions_with_errors(extensions)?;

        // Log warning if errors were encountered
        if result.has_errors() {
            warn!(
                "Extension scan completed with errors: {}",
                result.error_summary()
            );
            for error in &result.errors {
                debug!("Scan error: {}", error);
            }
        }

        Ok(result.files)
    }

    /// Scan for files matching specific extensions with full error reporting.
    ///
    /// Returns a `ScanResult` containing both the found files and any
    /// errors encountered during scanning.
    ///
    /// # Arguments
    ///
    /// * `extensions` - File extensions to match (e.g., [".py", ".pyi"])
    #[allow(dead_code)]
    pub fn scan_extensions_with_errors(&self, extensions: &[&str]) -> Result<ScanResult> {
        // Normalize extensions to lowercase without leading dot for case-insensitive matching
        let ext_set: FxHashSet<String> = extensions
            .iter()
            .map(|e| e.trim_start_matches('.').to_lowercase())
            .collect();
        let mut result = ScanResult::new();

        for entry_result in self.build_walker(None)? {
            match entry_result {
                Ok(entry) => {
                    if entry.path().is_file() {
                        // Case-insensitive extension matching: .py, .PY, .Py all match
                        let matches = entry
                            .path()
                            .extension()
                            .and_then(|ext| ext.to_str())
                            .map(|ext| ext_set.contains(&ext.to_lowercase()))
                            .unwrap_or(false);

                        if matches {
                            result.add_file(entry.path().to_path_buf());
                        }
                    }
                }
                Err(e) => {
                    let scan_error = ScanError::from_ignore_error(&e);
                    warn!("Failed to scan entry: {}", scan_error);
                    debug!("Error details: {:?}", e);
                    result.add_error(scan_error);
                }
            }
        }

        Ok(result)
    }

    /// Scan with full configuration options.
    ///
    /// This is the most flexible scanning method, supporting:
    /// - Language and extension filtering
    /// - Include/exclude glob patterns
    /// - Metadata collection
    /// - Parallel processing for large projects
    /// - Configurable error handling (fail-fast, collect-and-continue, log-only)
    ///
    /// # Error Handling
    ///
    /// By default, errors are collected and scanning continues (`CollectAndContinue`).
    /// Use `config.error_handling` to change this behavior:
    /// - `FailFast`: Stop on first error
    /// - `CollectAndContinue`: Collect errors, continue scanning (default)
    /// - `LogOnly`: Log warnings, don't collect errors
    ///
    /// # Memory Efficiency
    ///
    /// This method uses single-pass filtering during directory traversal to avoid
    /// creating intermediate collections. For a 100K file project, this reduces
    /// memory usage by avoiding double-allocation of file entry vectors.
    pub fn scan_with_config(&self, config: &ScanConfig) -> Result<ScanResult> {
        let registry = LanguageRegistry::global();

        // Validate language if specified and get resolved name for alias support.
        // e.g., "javascript" -> "typescript"
        let resolved_lang_name: Option<&str> = match &config.language {
            Some(lang) => {
                let resolved = registry
                    .get_by_name(lang)
                    .ok_or_else(|| BrrrError::UnsupportedLanguage(lang.clone()))?;
                Some(resolved.name())
            }
            None => None,
        };

        // Build filters for single-pass filtering during traversal.
        // This avoids collecting all files first and then filtering (double allocation).
        let ext_filter = ExtensionFilter::new(
            config
                .extensions
                .iter()
                .map(|e| e.trim_start_matches('.').to_lowercase())
                .collect(),
        );
        let lang_filter = LanguageFilter::new(resolved_lang_name, registry);

        // Single-pass: iterate walker, apply filters inline, collect only matching files.
        // This eliminates the memory double-allocation bug where we previously:
        // 1. Collected all files into entries Vec
        // 2. Filtered and collected into filtered Vec
        //
        // PERFORMANCE: Cache language detection during filtering to avoid redundant calls.
        // Language is detected exactly once per file, then reused for metadata collection.
        let walker = self.build_walker_with_config(config)?;
        let mut result = ScanResult::new();
        let mut filtered: Vec<ScannedFile> = Vec::new();

        for entry_result in walker {
            match entry_result {
                Ok(entry) => {
                    let path = entry.path();
                    // Apply extension filter first (fast, no language detection needed)
                    if path.is_file() && ext_filter.matches(path) {
                        // Use matches_with_cache to detect language once and cache the result
                        let match_result = lang_filter.matches_with_cache(path, &ext_filter);
                        if match_result.matches {
                            filtered.push(ScannedFile {
                                path: path.to_path_buf(),
                                language: match_result.language,
                            });
                        }
                    }
                }
                Err(e) => {
                    let scan_error = ScanError::from_ignore_error(&e);

                    match config.error_handling {
                        ErrorHandling::FailFast => {
                            return Err(BrrrError::Io(std::io::Error::new(
                                std::io::ErrorKind::Other,
                                format!("Scan failed: {}", scan_error),
                            )));
                        }
                        ErrorHandling::CollectAndContinue => {
                            warn!("Failed to scan entry: {}", scan_error);
                            debug!("Error details: {:?}", e);
                            result.add_error(scan_error);
                        }
                        ErrorHandling::LogOnly => {
                            warn!("Failed to scan entry: {}", scan_error);
                            debug!("Error details: {:?}", e);
                        }
                    }
                }
            }
        }

        // Collect metadata if requested, using cached language from filtering
        if config.collect_metadata {
            let use_parallel = config.parallel && filtered.len() >= MIN_FILES_FOR_PARALLEL;

            if use_parallel {
                // Parallel metadata collection with thread-safe error collection
                // Uses cached language from filtering - no redundant detection
                let errors = Mutex::new(Vec::new());
                let metadata: Vec<_> = filtered
                    .par_iter()
                    .filter_map(|scanned| {
                        let cached_lang = scanned.language.map(|s| s.to_string());
                        match FileMetadata::from_path_with_language(
                            scanned.path.clone(),
                            cached_lang,
                        ) {
                            Some(meta) => Some(meta),
                            None => {
                                // Metadata collection failed (likely permission or I/O error)
                                let warning = format!(
                                    "Could not collect metadata for: {}",
                                    scanned.path.display()
                                );
                                warn!("{}", warning);
                                if matches!(
                                    config.error_handling,
                                    ErrorHandling::CollectAndContinue
                                ) {
                                    errors.lock().push(warning);
                                }
                                None
                            }
                        }
                    })
                    .collect();

                // Merge collected warnings
                for warning in errors.into_inner() {
                    result.add_warning(warning);
                }

                for meta in metadata {
                    result.add_file(meta.path.clone());
                    result.add_metadata(meta);
                }
            } else {
                // Sequential metadata collection using cached language
                for scanned in filtered {
                    let cached_lang = scanned.language.map(|s| s.to_string());
                    if let Some(meta) =
                        FileMetadata::from_path_with_language(scanned.path.clone(), cached_lang)
                    {
                        result.add_file(meta.path.clone());
                        result.add_metadata(meta);
                    } else {
                        let warning =
                            format!("Could not collect metadata for: {}", scanned.path.display());
                        warn!("{}", warning);
                        if matches!(config.error_handling, ErrorHandling::CollectAndContinue) {
                            result.add_warning(warning);
                        }
                        result.add_file(scanned.path);
                    }
                }
            }
        } else {
            // No metadata collection - extract paths from cached ScannedFile entries
            result.files = filtered.into_iter().map(|f| f.path).collect();
        }

        // Log summary if errors were encountered
        if result.has_errors() {
            warn!("Scan completed with errors: {}", result.error_summary());
        }

        Ok(result)
    }

    /// Scan and return detailed file metadata.
    ///
    /// This is a convenience method equivalent to:
    /// ```ignore
    /// scanner.scan_with_config(&ScanConfig::default().with_metadata())
    /// ```
    #[allow(dead_code)]
    pub fn scan_with_metadata(&self) -> Result<Vec<FileMetadata>> {
        let config = ScanConfig {
            collect_metadata: true,
            parallel: true,
            ..Default::default()
        };

        Ok(self.scan_with_config(&config)?.metadata)
    }

    /// Scan a specific language and return metadata.
    #[allow(dead_code)]
    pub fn scan_language_with_metadata(&self, lang_name: &str) -> Result<Vec<FileMetadata>> {
        let config = ScanConfig {
            language: Some(lang_name.to_string()),
            collect_metadata: true,
            parallel: true,
            ..Default::default()
        };

        Ok(self.scan_with_config(&config)?.metadata)
    }

    /// Build a WalkBuilder with default settings.
    ///
    /// # Ignore Handling Design
    ///
    /// WalkBuilder handles gitignore natively (efficient, integrated with walking).
    /// `.brrrignore` is added as a custom ignore file.
    ///
    /// Note: `BrrrIgnore` (in util/ignore.rs) intentionally does NOT load `.gitignore`
    /// to avoid duplicate processing. This scanner handles gitignore, while other code
    /// paths use `BrrrIgnore` for `.brrrignore` patterns only.
    fn build_walker(
        &self,
        max_depth: Option<usize>,
    ) -> Result<impl Iterator<Item = std::result::Result<ignore::DirEntry, ignore::Error>>> {
        let mut builder = WalkBuilder::new(&self.root);

        // gitignore handling: WalkBuilder handles this natively and efficiently.
        // BrrrIgnore does NOT load .gitignore to avoid duplicate processing.
        builder
            .hidden(true) // Skip hidden files/dirs
            .parents(true) // Respect .gitignore in parent dirs
            .git_ignore(true) // Respect .gitignore
            .git_global(true) // Respect global gitignore
            .git_exclude(true) // Respect .git/info/exclude
            .add_custom_ignore_filename(".brrrignore");

        if let Some(depth) = max_depth {
            builder.max_depth(Some(depth));
        }

        // Add common exclude patterns
        let mut overrides = OverrideBuilder::new(&self.root);
        // Standard directories to always skip
        let _ = overrides.add("!**/node_modules/**");
        let _ = overrides.add("!**/__pycache__/**");
        let _ = overrides.add("!**/.venv/**");
        let _ = overrides.add("!**/venv/**");
        let _ = overrides.add("!**/target/debug/**");
        let _ = overrides.add("!**/target/release/**");
        let _ = overrides.add("!**/.git/**");
        let _ = overrides.add("!**/dist/**");
        let _ = overrides.add("!**/build/**");
        let _ = overrides.add("!**/*.min.js");
        let _ = overrides.add("!**/*.min.css");

        if let Ok(built) = overrides.build() {
            builder.overrides(built);
        }

        Ok(builder.build())
    }

    /// Build a WalkBuilder with custom configuration.
    ///
    /// See `build_walker` for ignore handling design notes.
    fn build_walker_with_config(
        &self,
        config: &ScanConfig,
    ) -> Result<impl Iterator<Item = std::result::Result<ignore::DirEntry, ignore::Error>>> {
        let mut builder = WalkBuilder::new(&self.root);

        // Handle no_ignore flag: when set, disable all ignore file processing
        if config.no_ignore {
            // Disable all ignore file processing when --no-ignore is set
            builder
                .hidden(false) // Include hidden files
                .parents(false) // Don't look for ignore files in parent dirs
                .git_ignore(false) // Ignore .gitignore
                .git_global(false) // Ignore global gitignore
                .git_exclude(false) // Ignore .git/info/exclude
                .ignore(false) // Ignore .ignore files
                .follow_links(config.follow_symlinks);
            // Note: Do NOT add .brrrignore when no_ignore is set
        } else {
            // gitignore handling: WalkBuilder handles this natively and efficiently.
            // BrrrIgnore does NOT load .gitignore to avoid duplicate processing.
            builder
                .hidden(true)
                .parents(true)
                .git_ignore(true)
                .git_global(true)
                .git_exclude(true)
                .follow_links(config.follow_symlinks)
                .add_custom_ignore_filename(".brrrignore");
        }

        if let Some(depth) = config.max_depth {
            builder.max_depth(Some(depth));
        }

        // Build overrides from config patterns
        let mut overrides = OverrideBuilder::new(&self.root);

        // Standard excludes (only applied if not disabled by config and not no_ignore mode)
        // These can be disabled when users need to include files from typically-excluded
        // directories like vendored dependencies in node_modules.
        // When no_ignore is set, we also skip default excludes
        if !config.disable_default_excludes && !config.no_ignore {
            let _ = overrides.add("!**/node_modules/**");
            let _ = overrides.add("!**/__pycache__/**");
            let _ = overrides.add("!**/.venv/**");
            let _ = overrides.add("!**/venv/**");
            let _ = overrides.add("!**/target/debug/**");
            let _ = overrides.add("!**/target/release/**");
            let _ = overrides.add("!**/.git/**");
        }

        // User-specified excludes
        for pattern in &config.exclude_patterns {
            let exclude = if pattern.starts_with('!') {
                pattern.clone()
            } else {
                format!("!{}", pattern)
            };
            let _ = overrides.add(&exclude);
        }

        // User-specified includes (if any)
        for pattern in &config.include_patterns {
            let _ = overrides.add(pattern);
        }

        if let Ok(built) = overrides.build() {
            builder.overrides(built);
        }

        // Enable parallel directory traversal for large projects
        if config.parallel {
            builder.threads(0); // Use all available CPUs
        } else {
            builder.threads(1);
        }

        Ok(builder.build())
    }

    /// Get the count of supported source files in the project.
    ///
    /// Performs a full directory traversal to get an accurate count.
    /// Uses parallel walking for performance - on modern SSDs this completes
    /// in under 1 second for projects with up to 100K files.
    ///
    /// This count matches what `scan_files()` will return (filtered by
    /// supported languages, respecting .gitignore and .brrrignore).
    ///
    /// Useful for progress bars or deciding scan strategy.
    /// Note: Errors during counting are logged but do not affect the count.
    #[allow(dead_code)]
    pub fn estimate_file_count(&self) -> Result<usize> {
        let registry = LanguageRegistry::global();
        let mut error_count = 0;

        // Single-pass traversal counting only supported language files.
        // This is both simpler and more accurate than the previous heuristic
        // which did TWO traversals with an inaccurate multiplication formula.
        let count = self
            .build_walker(None)?
            .filter_map(|e| match e {
                Ok(entry) => Some(entry),
                Err(err) => {
                    debug!("Error during file count: {:?}", err);
                    error_count += 1;
                    None
                }
            })
            .filter(|e| e.path().is_file() && registry.detect_language(e.path()).is_some())
            .count();

        if error_count > 0 {
            warn!(
                "File count encountered {} errors (count may be incomplete)",
                error_count
            );
        }

        Ok(count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use tempfile::TempDir;

    fn create_test_project() -> TempDir {
        let dir = TempDir::new().unwrap();
        let root = dir.path();

        // Create some test files
        File::create(root.join("main.py")).unwrap();
        File::create(root.join("lib.py")).unwrap();
        File::create(root.join("utils.rs")).unwrap();
        File::create(root.join("app.ts")).unwrap();

        // Create subdirectory
        std::fs::create_dir(root.join("src")).unwrap();
        File::create(root.join("src/module.py")).unwrap();
        File::create(root.join("src/helper.rs")).unwrap();

        // Create ignored directory
        std::fs::create_dir(root.join("node_modules")).unwrap();
        File::create(root.join("node_modules/dep.js")).unwrap();

        dir
    }

    #[test]
    fn test_scan_files() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let files = scanner.scan_files().unwrap();

        // Should find Python, Rust, TypeScript files but not node_modules
        assert!(files.iter().any(|p| p.ends_with("main.py")));
        assert!(files.iter().any(|p| p.ends_with("utils.rs")));
        assert!(files.iter().any(|p| p.ends_with("app.ts")));
        assert!(!files
            .iter()
            .any(|p| p.to_str().unwrap().contains("node_modules")));
    }

    #[test]
    fn test_scan_language() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let py_files = scanner.scan_language("python").unwrap();

        assert_eq!(py_files.len(), 3); // main.py, lib.py, src/module.py
        assert!(py_files.iter().all(|p| p.extension().unwrap() == "py"));
    }

    #[test]
    fn test_scan_extensions() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let rs_files = scanner.scan_extensions(&[".rs"]).unwrap();

        assert_eq!(rs_files.len(), 2); // utils.rs, src/helper.rs
    }

    #[test]
    fn test_scan_with_metadata() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let metadata = scanner.scan_with_metadata().unwrap();

        assert!(!metadata.is_empty());
        // All files should have language detected
        assert!(metadata.iter().all(|m| m.language.is_some()));
    }

    #[test]
    fn test_scan_config() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let config = ScanConfig::for_language("python")
            .with_excludes(&["**/src/**"])
            .with_metadata();

        let result = scanner.scan_with_config(&config).unwrap();

        // Should only find root-level Python files
        assert_eq!(result.files.len(), 2); // main.py, lib.py
        assert!(result.by_language.contains_key("python"));
    }

    #[test]
    fn test_unsupported_language_error() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let result = scanner.scan_language("brainfuck");

        assert!(matches!(result, Err(BrrrError::UnsupportedLanguage(_))));
    }

    #[test]
    fn test_scan_language_javascript_alias() {
        // BUG FIX TEST: "javascript" should be a valid language name (alias for TypeScript)
        // Previously, scan_language("javascript") would return UnsupportedLanguage error
        let dir = TempDir::new().unwrap();
        let root = dir.path();

        // Create JavaScript files
        File::create(root.join("app.js")).unwrap();
        File::create(root.join("utils.mjs")).unwrap();
        File::create(root.join("config.cjs")).unwrap();
        std::fs::create_dir(root.join("src")).unwrap();
        File::create(root.join("src/helper.js")).unwrap();

        let scanner = ProjectScanner::new(root.to_str().unwrap()).unwrap();

        // This should NOT return UnsupportedLanguage error
        let js_files = scanner.scan_language("javascript");
        assert!(
            js_files.is_ok(),
            "scan_language('javascript') should work: {:?}",
            js_files.err()
        );

        // Files should be found via the TypeScript parser (which handles JS)
        let files = js_files.unwrap();
        assert_eq!(files.len(), 4, "Should find all 4 JS files");

        // Short aliases should also work
        assert!(
            scanner.scan_language("js").is_ok(),
            "scan_language('js') alias should work"
        );
    }

    #[test]
    fn test_nonexistent_path_error() {
        let result = ProjectScanner::new("/nonexistent/path/12345");

        assert!(matches!(result, Err(BrrrError::Io(_))));
    }

    #[test]
    fn test_disable_default_excludes() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        // By default, node_modules should be excluded
        let default_config = ScanConfig::default();
        let result = scanner.scan_with_config(&default_config).unwrap();
        assert!(
            !result
                .files
                .iter()
                .any(|p| p.to_str().unwrap().contains("node_modules")),
            "node_modules should be excluded by default"
        );

        // With disable_default_excludes, node_modules should be included
        let config_with_disabled = ScanConfig::default().with_default_excludes_disabled();
        let result = scanner.scan_with_config(&config_with_disabled).unwrap();
        assert!(
            result
                .files
                .iter()
                .any(|p| p.to_str().unwrap().contains("node_modules")),
            "node_modules should be included when default excludes are disabled"
        );
    }

    #[test]
    fn test_disable_default_excludes_with_include_pattern() {
        let dir = create_test_project();

        // Create a vendored file in node_modules
        std::fs::create_dir_all(dir.path().join("node_modules/vendor")).unwrap();
        File::create(dir.path().join("node_modules/vendor/lib.js")).unwrap();

        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        // With default excludes disabled and include pattern, should find vendored file
        let config = ScanConfig::default()
            .with_default_excludes_disabled()
            .with_includes(&["**/node_modules/vendor/**"]);

        let result = scanner.scan_with_config(&config).unwrap();
        assert!(
            result
                .files
                .iter()
                .any(|p| p.to_str().unwrap().contains("node_modules/vendor")),
            "should find vendored files in node_modules when default excludes are disabled"
        );
    }

    #[test]
    fn test_scan_files_with_errors_returns_scan_result() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let result = scanner.scan_files_with_errors().unwrap();

        // Should find files successfully
        assert!(!result.files.is_empty());
        // In a normal project, should have no errors
        assert!(!result.has_errors());
        assert_eq!(result.error_summary(), "No errors");
    }

    #[test]
    fn test_scan_language_with_errors_returns_scan_result() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let result = scanner.scan_language_with_errors("python").unwrap();

        assert_eq!(result.files.len(), 3); // main.py, lib.py, src/module.py
        assert!(!result.has_errors());
    }

    #[test]
    fn test_scan_extensions_with_errors_returns_scan_result() {
        let dir = create_test_project();
        let scanner = ProjectScanner::new(dir.path().to_str().unwrap()).unwrap();

        let result = scanner.scan_extensions_with_errors(&[".rs"]).unwrap();

        assert_eq!(result.files.len(), 2); // utils.rs, src/helper.rs
        assert!(!result.has_errors());
    }

    #[test]
    fn test_error_handling_config() {
        let config = ScanConfig::default().with_error_handling(ErrorHandling::FailFast);
        assert_eq!(config.error_handling, ErrorHandling::FailFast);

        let config = ScanConfig::default().fail_on_error();
        assert_eq!(config.error_handling, ErrorHandling::FailFast);

        let config = ScanConfig::default().with_error_handling(ErrorHandling::CollectAndContinue);
        assert_eq!(config.error_handling, ErrorHandling::CollectAndContinue);

        let config = ScanConfig::default().with_error_handling(ErrorHandling::LogOnly);
        assert_eq!(config.error_handling, ErrorHandling::LogOnly);
    }

    #[test]
    fn test_scan_error_kind_display() {
        assert_eq!(
            format!("{}", ScanErrorKind::PermissionDenied),
            "permission denied"
        );
        assert_eq!(
            format!("{}", ScanErrorKind::BrokenSymlink),
            "broken symlink"
        );
        assert_eq!(format!("{}", ScanErrorKind::IoError), "I/O error");
        assert_eq!(
            format!("{}", ScanErrorKind::DirectoryLoop),
            "directory loop"
        );
        assert_eq!(format!("{}", ScanErrorKind::Other), "other error");
    }

    #[test]
    fn test_scan_error_display() {
        let error_with_path = ScanError {
            path: Some(PathBuf::from("/test/file.txt")),
            message: "test error".to_string(),
            kind: ScanErrorKind::PermissionDenied,
        };
        assert!(format!("{}", error_with_path).contains("/test/file.txt"));
        assert!(format!("{}", error_with_path).contains("test error"));
        assert!(format!("{}", error_with_path).contains("permission denied"));

        let error_without_path = ScanError {
            path: None,
            message: "test error".to_string(),
            kind: ScanErrorKind::IoError,
        };
        assert!(format!("{}", error_without_path).contains("test error"));
        assert!(format!("{}", error_without_path).contains("I/O error"));
    }

    #[test]
    fn test_scan_result_error_counts() {
        let mut result = ScanResult::new();
        result.add_error(ScanError {
            path: Some(PathBuf::from("/a")),
            message: "error 1".to_string(),
            kind: ScanErrorKind::PermissionDenied,
        });
        result.add_error(ScanError {
            path: Some(PathBuf::from("/b")),
            message: "error 2".to_string(),
            kind: ScanErrorKind::PermissionDenied,
        });
        result.add_error(ScanError {
            path: Some(PathBuf::from("/c")),
            message: "error 3".to_string(),
            kind: ScanErrorKind::BrokenSymlink,
        });

        let counts = result.error_counts();
        assert_eq!(counts.get(&ScanErrorKind::PermissionDenied), Some(&2));
        assert_eq!(counts.get(&ScanErrorKind::BrokenSymlink), Some(&1));

        assert!(result.has_errors());
        let summary = result.error_summary();
        assert!(summary.contains("3 total errors"));
    }

    #[test]
    fn test_scan_result_warnings() {
        let mut result = ScanResult::new();
        result.add_warning("warning 1".to_string());
        result.add_warning("warning 2".to_string());

        assert_eq!(result.warnings.len(), 2);
        assert!(result.warnings.contains(&"warning 1".to_string()));
        assert!(result.warnings.contains(&"warning 2".to_string()));
    }

    #[test]
    fn test_scan_extensions_case_insensitive() {
        let dir = TempDir::new().unwrap();
        let root = dir.path();

        // Create files with various extension cases
        File::create(root.join("lowercase.py")).unwrap();
        File::create(root.join("uppercase.PY")).unwrap();
        File::create(root.join("mixed.Py")).unwrap();
        File::create(root.join("mixed2.pY")).unwrap();
        File::create(root.join("other.rs")).unwrap();

        let scanner = ProjectScanner::new(root.to_str().unwrap()).unwrap();

        // Test with lowercase extension in query
        let py_files = scanner.scan_extensions(&[".py"]).unwrap();
        assert_eq!(
            py_files.len(),
            4,
            "Should match all .py variants regardless of case"
        );

        // Test with uppercase extension in query
        let py_files_upper = scanner.scan_extensions(&[".PY"]).unwrap();
        assert_eq!(
            py_files_upper.len(),
            4,
            "Query with .PY should also match all variants"
        );

        // Test without leading dot
        let py_files_no_dot = scanner.scan_extensions(&["py"]).unwrap();
        assert_eq!(py_files_no_dot.len(), 4, "Query without dot should work");
    }

    #[test]
    fn test_scan_config_extensions_case_insensitive() {
        let dir = TempDir::new().unwrap();
        let root = dir.path();

        // Create files with various extension cases
        File::create(root.join("test1.rs")).unwrap();
        File::create(root.join("test2.RS")).unwrap();
        File::create(root.join("test3.Rs")).unwrap();

        let scanner = ProjectScanner::new(root.to_str().unwrap()).unwrap();

        let config = ScanConfig::for_extensions(&[".rs"]);
        let result = scanner.scan_with_config(&config).unwrap();

        assert_eq!(
            result.files.len(),
            3,
            "Should match all .rs variants regardless of case"
        );
    }

    #[test]
    fn test_estimate_file_count_accuracy() {
        // BUG FIX TEST: estimate_file_count should return accurate count
        // Previously, it used a broken heuristic: depth_1_files * total_dirs
        // which gave wildly inaccurate results (e.g., estimated 12, actual 101)
        let dir = TempDir::new().unwrap();
        let root = dir.path();

        // Create a nested structure that would expose the old bug
        // Old formula: 2 files at depth 1 * 4 dirs = 8
        // But actual count is 6 supported files
        File::create(root.join("root1.py")).unwrap();
        File::create(root.join("root2.py")).unwrap();

        std::fs::create_dir(root.join("subdir1")).unwrap();
        File::create(root.join("subdir1/file1.py")).unwrap();
        File::create(root.join("subdir1/file2.py")).unwrap();

        std::fs::create_dir(root.join("subdir2")).unwrap();
        std::fs::create_dir(root.join("subdir2/nested")).unwrap();
        File::create(root.join("subdir2/nested/deep.py")).unwrap();

        // Also create an unsupported file type (should not be counted)
        File::create(root.join("readme.txt")).unwrap();

        let scanner = ProjectScanner::new(root.to_str().unwrap()).unwrap();

        let estimate = scanner.estimate_file_count().unwrap();
        let actual_files = scanner.scan_files().unwrap();

        // Estimate should now exactly match actual count
        assert_eq!(
            estimate,
            actual_files.len(),
            "estimate_file_count() should match scan_files() count exactly.\n\
             Estimate: {}, Actual: {}",
            estimate,
            actual_files.len()
        );

        // Should have found exactly 5 Python files (not counting .txt)
        assert_eq!(actual_files.len(), 5);
    }
}
