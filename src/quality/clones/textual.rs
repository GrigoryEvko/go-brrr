//! Textual clone detection (Type-1 clones).
//!
//! Detects exact code duplicates by normalizing whitespace and stripping comments,
//! then using a rolling hash (Rabin fingerprint) algorithm to find matching code blocks.
//!
//! # Type-1 Clones
//!
//! Type-1 clones are exact copies of code that may differ only in:
//! - Whitespace (indentation, blank lines within blocks)
//! - Comments (inline, block, documentation)
//! - Formatting (line breaks, spacing)
//!
//! # Algorithm
//!
//! 1. **Preprocessing**: Normalize each source file by stripping comments and
//!    collapsing whitespace to produce a sequence of normalized lines.
//! 2. **Fingerprinting**: Compute a rolling hash (Rabin fingerprint) over sliding
//!    windows of N lines (configurable, default 6).
//! 3. **Indexing**: Build a hash map from fingerprint -> list of locations.
//! 4. **Grouping**: Report locations with identical fingerprints as clone groups.
//!
//! # Exclusions
//!
//! The detector automatically excludes:
//! - **License headers**: Common OSS license patterns (MIT, Apache, GPL, etc.)
//! - **Test fixtures**: Files in test directories with intentional duplication
//! - **Generated code**: Auto-generated files (protobuf, thrift, etc.)
//! - **Blank-heavy blocks**: Blocks that are mostly whitespace after normalization
//!
//! # Performance
//!
//! - Uses parallel file processing via rayon for large codebases
//! - Memory-efficient streaming: processes files incrementally
//! - Handles 10K+ files efficiently with O(n) line scanning per file
//! - Uses FxHash for fast, non-cryptographic hashing
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::clones::textual::{TextualCloneDetector, CloneConfig};
//!
//! let config = CloneConfig::default();
//! let detector = TextualCloneDetector::new(config);
//! let result = detector.detect("./src")?;
//!
//! println!("Found {} clone groups", result.clone_groups.len());
//! println!("Total duplicated lines: {}", result.stats.duplicated_lines);
//! println!("Duplication ratio: {:.1}%", result.stats.duplication_percentage);
//! ```

use std::path::{Path, PathBuf};
use std::sync::Mutex;

use aho_corasick::AhoCorasick;
use fxhash::{FxHashMap, FxHashSet};
use once_cell::sync::Lazy;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use tracing::{debug, trace};
use xxhash_rust::xxh3::xxh3_64;

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// TYPES
// =============================================================================

/// Type of code clone detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CloneType {
    /// Type-1: Exact copy (ignoring whitespace/comments)
    Type1,
    /// Type-2: Syntactically identical with renamed identifiers (future)
    #[allow(dead_code)]
    Type2,
    /// Type-3: Near-miss clones with small modifications (future)
    #[allow(dead_code)]
    Type3,
}

impl Default for CloneType {
    fn default() -> Self {
        Self::Type1
    }
}

impl std::fmt::Display for CloneType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Type1 => write!(f, "Type-1 (exact)"),
            Self::Type2 => write!(f, "Type-2 (renamed)"),
            Self::Type3 => write!(f, "Type-3 (near-miss)"),
        }
    }
}

/// A single instance of a code clone.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CloneInstance {
    /// File containing this clone instance.
    pub file: PathBuf,
    /// Starting line number (1-indexed).
    pub start_line: usize,
    /// Ending line number (1-indexed, inclusive).
    pub end_line: usize,
    /// Preview of the first line (for display).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub preview: Option<String>,
}

impl CloneInstance {
    /// Create a new clone instance.
    #[must_use]
    pub fn new(file: PathBuf, start_line: usize, end_line: usize) -> Self {
        Self {
            file,
            start_line,
            end_line,
            preview: None,
        }
    }

    /// Create a clone instance with a preview line.
    #[must_use]
    pub fn with_preview(
        file: PathBuf,
        start_line: usize,
        end_line: usize,
        preview: String,
    ) -> Self {
        Self {
            file,
            start_line,
            end_line,
            preview: Some(preview),
        }
    }

    /// Number of lines in this clone instance.
    #[must_use]
    pub fn line_count(&self) -> usize {
        self.end_line.saturating_sub(self.start_line) + 1
    }
}

/// A group of identical code clones.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Clone {
    /// Type of clone (Type1, Type2, Type3).
    pub clone_type: CloneType,
    /// All instances of this clone.
    pub instances: Vec<CloneInstance>,
    /// Number of lines in each instance.
    pub line_count: usize,
    /// Similarity score (1.0 for Type-1 exact clones).
    pub similarity: f64,
    /// Fingerprint hash (for debugging/identification).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fingerprint: Option<u64>,
}

impl Clone {
    /// Create a new Type-1 clone group.
    #[must_use]
    pub fn new_type1(instances: Vec<CloneInstance>, line_count: usize) -> Self {
        Self {
            clone_type: CloneType::Type1,
            instances,
            line_count,
            similarity: 1.0,
            fingerprint: None,
        }
    }

    /// Create a clone group with fingerprint for tracking.
    #[must_use]
    pub fn with_fingerprint(mut self, fingerprint: u64) -> Self {
        self.fingerprint = Some(fingerprint);
        self
    }

    /// Total duplicated lines across all instances (excluding the first).
    ///
    /// The first instance is considered the "original" - subsequent instances
    /// are the duplicates contributing to the duplication count.
    #[must_use]
    pub fn duplicated_lines(&self) -> usize {
        if self.instances.len() <= 1 {
            return 0;
        }
        self.line_count * (self.instances.len() - 1)
    }
}

/// Configuration for clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneConfig {
    /// Minimum number of lines for a clone to be reported.
    /// Default: 6 lines (matches common tool defaults like PMD, Simian).
    pub min_lines: usize,

    /// Minimum number of tokens for a clone to be reported.
    /// Filters out trivial clones like single-line repeated patterns.
    /// Default: 50 tokens.
    pub min_tokens: usize,

    /// Glob patterns for files to ignore.
    /// Supports gitignore-style patterns.
    pub ignore_patterns: Vec<String>,

    /// Whether to exclude license headers from clone detection.
    /// Default: true.
    pub exclude_license_headers: bool,

    /// Whether to exclude test fixtures (intentional test duplication).
    /// Default: true.
    pub exclude_test_fixtures: bool,

    /// Whether to exclude generated code files.
    /// Default: true.
    pub exclude_generated: bool,

    /// Maximum file size to process (in bytes).
    /// Files larger than this are skipped.
    /// Default: 1MB.
    pub max_file_size: u64,

    /// Language filter (e.g., "python", "rust").
    /// If None, detects from file extensions.
    pub language: Option<String>,
}

impl Default for CloneConfig {
    fn default() -> Self {
        Self {
            min_lines: 6,
            min_tokens: 50,
            ignore_patterns: Vec::new(),
            exclude_license_headers: true,
            exclude_test_fixtures: true,
            exclude_generated: true,
            max_file_size: 1024 * 1024, // 1MB
            language: None,
        }
    }
}

impl CloneConfig {
    /// Create a configuration for a specific minimum line count.
    #[must_use]
    pub fn with_min_lines(mut self, min_lines: usize) -> Self {
        self.min_lines = min_lines;
        self
    }

    /// Create a configuration with a language filter.
    #[must_use]
    pub fn with_language(mut self, lang: impl Into<String>) -> Self {
        self.language = Some(lang.into());
        self
    }

    /// Add ignore patterns.
    #[must_use]
    pub fn with_ignore_patterns(mut self, patterns: Vec<String>) -> Self {
        self.ignore_patterns = patterns;
        self
    }
}

/// Statistics about clone detection results.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CloneStats {
    /// Total files scanned.
    pub files_scanned: usize,
    /// Files with clones detected.
    pub files_with_clones: usize,
    /// Total clone groups found.
    pub clone_groups: usize,
    /// Total clone instances (across all groups).
    pub clone_instances: usize,
    /// Total lines that are duplicated.
    pub duplicated_lines: usize,
    /// Total source lines analyzed.
    pub total_lines: usize,
    /// Duplication percentage (duplicated_lines / total_lines * 100).
    pub duplication_percentage: f64,
    /// Number of files skipped due to size limits.
    pub files_skipped_size: usize,
    /// Number of files skipped due to exclusion patterns.
    pub files_skipped_excluded: usize,
}

impl CloneStats {
    /// Calculate duplication percentage from current counts.
    pub fn calculate_percentage(&mut self) {
        if self.total_lines > 0 {
            self.duplication_percentage =
                (self.duplicated_lines as f64 / self.total_lines as f64) * 100.0;
        }
    }
}

/// Error during clone detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneError {
    /// File where error occurred.
    pub file: PathBuf,
    /// Error message.
    pub message: String,
}

/// Result of clone detection analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneAnalysis {
    /// Path that was analyzed.
    pub path: PathBuf,
    /// Configuration used for analysis.
    pub config: CloneConfig,
    /// Clone groups detected.
    pub clone_groups: Vec<Clone>,
    /// Aggregate statistics.
    pub stats: CloneStats,
    /// Errors encountered during analysis.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub errors: Vec<CloneError>,
}

// =============================================================================
// RABIN FINGERPRINTING
// =============================================================================

/// Rabin fingerprint hasher for rolling hash computation.
///
/// Uses polynomial rolling hash with a prime base for efficient
/// sliding window hash computation.
struct RabinHasher {
    /// Hash accumulator.
    hash: u64,
    /// Base for polynomial hash (large prime).
    base: u64,
    /// Modulus for hash (large prime for collision resistance).
    modulus: u64,
    /// Precomputed base^(window_size-1) mod modulus for efficient removal.
    base_power: u64,
    /// Window size (number of lines).
    window_size: usize,
}

impl RabinHasher {
    /// Create a new Rabin hasher with specified window size.
    ///
    /// Uses well-known primes for good distribution:
    /// - Base: 31 (common choice for string hashing)
    /// - Modulus: Large prime near 2^63 for minimal collisions
    fn new(window_size: usize) -> Self {
        let base: u64 = 31;
        let modulus: u64 = (1u64 << 61) - 1; // Mersenne prime 2^61-1

        // Precompute base^(window_size-1) mod modulus
        let mut base_power = 1u64;
        for _ in 0..window_size.saturating_sub(1) {
            base_power = base_power.wrapping_mul(base) % modulus;
        }

        Self {
            hash: 0,
            base,
            modulus,
            base_power,
            window_size,
        }
    }

    /// Add a new line hash to the window.
    fn push(&mut self, line_hash: u64) {
        // Reduce line_hash to modulus range first to prevent overflow
        let reduced_hash = line_hash % self.modulus;
        // Use wrapping operations throughout to handle large intermediate values
        let shifted = (self.hash % self.modulus).wrapping_mul(self.base) % self.modulus;
        self.hash = shifted.wrapping_add(reduced_hash) % self.modulus;
    }

    /// Remove the oldest line hash from the window.
    fn pop(&mut self, old_line_hash: u64) {
        // Reduce to modulus range first
        let reduced_hash = old_line_hash % self.modulus;
        let remove = reduced_hash.wrapping_mul(self.base_power) % self.modulus;
        // Handle potential underflow using modular arithmetic
        if self.hash >= remove {
            self.hash = self.hash - remove;
        } else {
            self.hash = self.modulus - (remove - self.hash);
        }
    }

    /// Get current fingerprint.
    #[inline]
    fn fingerprint(&self) -> u64 {
        self.hash
    }

    /// Reset the hasher.
    fn reset(&mut self) {
        self.hash = 0;
    }
}

/// Compute a hash for a single normalized line.
///
/// Uses xxh3 which leverages SIMD instructions internally for high throughput.
#[inline]
fn hash_line(line: &str) -> u64 {
    xxh3_64(line.as_bytes())
}

// =============================================================================
// LINE NORMALIZATION
// =============================================================================

/// Normalizes source code for clone detection.
///
/// Operations performed:
/// 1. Strip single-line comments (//, #, --)
/// 2. Strip block comments (/* */, """ """, ''' ''')
/// 3. Collapse multiple whitespace to single space
/// 4. Trim leading/trailing whitespace
/// 5. Skip blank lines
struct LineNormalizer<'a> {
    /// Language-specific single-line comment markers.
    single_line_comments: &'a [&'a str],
    /// Whether we're inside a block comment.
    in_block_comment: bool,
    /// Block comment end marker we're looking for.
    block_end: Option<&'a str>,
}

impl<'a> LineNormalizer<'a> {
    /// Create a normalizer for a given language.
    fn for_language(lang: Option<&str>) -> Self {
        let single_line_comments = match lang {
            Some("python") => &["#"][..],
            Some("rust") => &["//"][..],
            Some("go") => &["//"][..],
            Some("java") | Some("c") | Some("cpp") | Some("csharp") | Some("kotlin") => &["//"][..],
            Some("typescript") | Some("javascript") => &["//"][..],
            Some("ruby") => &["#"][..],
            Some("php") => &["//", "#"][..],
            Some("lua") => &["--"][..],
            Some("sql") => &["--"][..],
            Some("shell") | Some("bash") => &["#"][..],
            _ => &["//", "#"][..], // Default: common markers
        };

        Self {
            single_line_comments,
            in_block_comment: false,
            block_end: None,
        }
    }

    /// Normalize a single line, returning None if the line should be skipped.
    fn normalize_line(&mut self, line: &str) -> Option<String> {
        let mut result = line.to_string();

        // Handle block comment continuation
        if self.in_block_comment {
            if let Some(end) = self.block_end {
                if let Some(pos) = result.find(end) {
                    // Block comment ends on this line
                    result = result[pos + end.len()..].to_string();
                    self.in_block_comment = false;
                    self.block_end = None;
                } else {
                    // Still inside block comment
                    return None;
                }
            }
        }

        // Strip block comments that start and end on this line
        result = self.strip_inline_block_comments(&result);

        // Check for block comment start
        result = self.handle_block_comment_start(&result);

        // Strip single-line comments
        for marker in self.single_line_comments {
            if let Some(pos) = result.find(marker) {
                // Check if inside a string literal (simplified check)
                if !self.is_in_string_literal(&result, pos) {
                    result = result[..pos].to_string();
                }
            }
        }

        // Normalize whitespace: collapse multiple spaces to one
        let normalized: String = result.split_whitespace().collect::<Vec<_>>().join(" ");

        // Skip empty lines
        if normalized.is_empty() {
            return None;
        }

        Some(normalized)
    }

    /// Strip inline block comments (start and end on same line).
    fn strip_inline_block_comments(&self, line: &str) -> String {
        let mut result = line.to_string();

        // Handle /* */ style comments
        while let Some(start) = result.find("/*") {
            if let Some(end) = result[start..].find("*/") {
                result = format!("{}{}", &result[..start], &result[start + end + 2..]);
            } else {
                break;
            }
        }

        // Handle Python triple-quoted comments (doc strings used as comments)
        // This is a simplified approach - we treat """ as block comment markers
        while let Some(start) = result.find("\"\"\"") {
            if let Some(end) = result[start + 3..].find("\"\"\"") {
                result = format!("{}{}", &result[..start], &result[start + end + 6..]);
            } else {
                break;
            }
        }

        result
    }

    /// Handle block comment that starts on this line.
    fn handle_block_comment_start(&mut self, line: &str) -> String {
        let mut result = line.to_string();

        // Check for /* ... without closing */
        if let Some(start) = result.find("/*") {
            if result[start..].find("*/").is_none() {
                self.in_block_comment = true;
                self.block_end = Some("*/");
                result = result[..start].to_string();
            }
        }

        // Check for Python """ starting multiline string/comment
        if let Some(start) = result.find("\"\"\"") {
            if result[start + 3..].find("\"\"\"").is_none() {
                self.in_block_comment = true;
                self.block_end = Some("\"\"\"");
                result = result[..start].to_string();
            }
        }

        result
    }

    /// Simple check if position is inside a string literal.
    ///
    /// Uses SIMD (u8x32) to count single and double quotes in one pass,
    /// then subtracts escaped quotes found via memchr.
    /// This is a heuristic - not a full parser. Works for common cases.
    #[allow(clippy::cast_possible_truncation)]
    fn is_in_string_literal(&self, line: &str, pos: usize) -> bool {
        use wide::{u8x32, CmpEq};

        let bytes = &line.as_bytes()[..pos];
        let len = bytes.len();

        if len == 0 {
            return false;
        }

        // SIMD comparison targets
        let single_quote_vec = u8x32::splat(b'\'');
        let double_quote_vec = u8x32::splat(b'"');

        let mut single_count: u32 = 0;
        let mut double_count: u32 = 0;

        // Process 32-byte chunks with SIMD
        let chunks = len / 32;
        for chunk_idx in 0..chunks {
            let offset = chunk_idx * 32;
            // SAFETY: chunks calculation guarantees offset + 32 <= len
            let chunk: [u8; 32] = bytes[offset..offset + 32]
                .try_into()
                .expect("chunk size is exactly 32");
            let vec = u8x32::from(chunk);

            // cmp_eq returns 0xFF for matches, 0 for non-matches
            let single_mask = vec.cmp_eq(single_quote_vec);
            let double_mask = vec.cmp_eq(double_quote_vec);

            // Each non-zero byte in mask represents one match
            for b in single_mask.to_array() {
                if b != 0 {
                    single_count += 1;
                }
            }
            for b in double_mask.to_array() {
                if b != 0 {
                    double_count += 1;
                }
            }
        }

        // Handle remainder with scalar code
        for &b in &bytes[chunks * 32..] {
            if b == b'\'' {
                single_count += 1;
            } else if b == b'"' {
                double_count += 1;
            }
        }

        // Count escaped quotes (\' and \") using SIMD-accelerated memchr
        let mut escaped_single: u32 = 0;
        let mut escaped_double: u32 = 0;

        for backslash_pos in memchr::memchr_iter(b'\\', bytes) {
            if let Some(&next_byte) = bytes.get(backslash_pos + 1) {
                match next_byte {
                    b'\'' => escaped_single += 1,
                    b'"' => escaped_double += 1,
                    _ => {}
                }
            }
        }

        let unescaped_single = single_count.saturating_sub(escaped_single);
        let unescaped_double = double_count.saturating_sub(escaped_double);

        // Odd count means we're inside a string
        (unescaped_single % 2 == 1) || (unescaped_double % 2 == 1)
    }
}

// =============================================================================
// LICENSE AND EXCLUSION DETECTION
// =============================================================================

/// Common license header patterns to exclude from clone detection.
const LICENSE_PATTERNS: &[&str] = &[
    "copyright",
    "licensed under",
    "license",
    "mit license",
    "apache license",
    "gnu general public",
    "gpl",
    "lgpl",
    "bsd license",
    "mozilla public license",
    "mpl",
    "permission is hereby granted",
    "this software is provided",
    "all rights reserved",
    "spdx-license-identifier",
];

/// Aho-Corasick automaton for O(n) multi-pattern license matching.
/// Uses case-insensitive matching to avoid per-call lowercase conversion.
static LICENSE_MATCHER: Lazy<AhoCorasick> = Lazy::new(|| {
    AhoCorasick::builder()
        .ascii_case_insensitive(true)
        .build(LICENSE_PATTERNS)
        .expect("LICENSE_PATTERNS are valid")
});

/// Patterns indicating generated code files.
const GENERATED_PATTERNS: &[&str] = &[
    "generated by",
    "auto-generated",
    "autogenerated",
    "do not edit",
    "do not modify",
    "generated from",
    "@generated",
    "this file is generated",
    "machine generated",
    "automatically generated",
];

/// Check if content appears to be a license header.
///
/// Uses Aho-Corasick automaton for O(n) multi-pattern matching,
/// replacing O(n*m) per-pattern iteration with `.contains()`.
#[inline]
fn is_license_content(content: &str) -> bool {
    LICENSE_MATCHER.is_match(content)
}

/// Check if a file appears to be generated code.
fn is_generated_file(path: &Path, first_lines: &[String]) -> bool {
    // Check file name patterns
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("")
        .to_lowercase();

    if file_name.contains("generated")
        || file_name.contains(".gen.")
        || file_name.ends_with(".pb.go")
        || file_name.ends_with("_pb2.py")
        || file_name.ends_with(".g.dart")
        || file_name.contains("_generated")
    {
        return true;
    }

    // Check first few lines for generation markers
    let header = first_lines
        .iter()
        .take(10)
        .map(|l| l.to_lowercase())
        .collect::<Vec<_>>()
        .join(" ");
    GENERATED_PATTERNS
        .iter()
        .any(|pattern| header.contains(pattern))
}

/// Check if a file is in a test fixtures directory.
fn is_test_fixture(path: &Path) -> bool {
    let path_str = path.to_string_lossy().to_lowercase();

    // Common test fixture directory patterns
    path_str.contains("/fixtures/")
        || path_str.contains("/testdata/")
        || path_str.contains("/test_data/")
        || path_str.contains("/__fixtures__/")
        || path_str.contains("/testfiles/")
        || path_str.contains("/samples/")
        || path_str.contains("/snapshots/")
        || path_str.contains("/__snapshots__/")
}

// =============================================================================
// CLONE DETECTOR
// =============================================================================

/// Minimum files for parallel processing.
const MIN_FILES_FOR_PARALLEL: usize = 10;

/// Textual clone detector using rolling hash algorithm.
pub struct TextualCloneDetector {
    /// Configuration for detection.
    config: CloneConfig,
}

impl TextualCloneDetector {
    /// Create a new detector with the given configuration.
    #[must_use]
    pub fn new(config: CloneConfig) -> Self {
        Self { config }
    }

    /// Create a detector with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(CloneConfig::default())
    }

    /// Detect clones in the given path (file or directory).
    pub fn detect(&self, path: impl AsRef<Path>) -> Result<CloneAnalysis> {
        let path = path.as_ref();
        debug!("Starting clone detection in {:?}", path);

        // Scan for source files
        let mut scan_config = if let Some(ref lang) = self.config.language {
            ScanConfig::for_language(lang)
        } else {
            ScanConfig::default()
        };
        scan_config.collect_metadata = true;

        let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;
        let scan_result = scanner.scan_with_config(&scan_config)?;

        // Use metadata if available for size filtering, otherwise use file list
        let files: Vec<PathBuf> = if !scan_result.metadata.is_empty() {
            scan_result
                .metadata
                .into_iter()
                .filter(|meta| meta.size <= self.config.max_file_size)
                .map(|meta| meta.path)
                .collect()
        } else {
            // Fallback: filter files by reading metadata individually
            scan_result
                .files
                .into_iter()
                .filter(|p| {
                    std::fs::metadata(p)
                        .map(|m| m.len() <= self.config.max_file_size)
                        .unwrap_or(false)
                })
                .collect()
        };

        debug!("Found {} files to analyze", files.len());

        self.detect_in_files(path.to_path_buf(), &files)
    }

    /// Detect clones in a specific list of files.
    pub fn detect_in_files(&self, base_path: PathBuf, files: &[PathBuf]) -> Result<CloneAnalysis> {
        let mut stats = CloneStats::default();
        stats.files_scanned = files.len();

        // Shared state for parallel processing
        let fingerprints: Mutex<FxHashMap<u64, Vec<CloneInstance>>> =
            Mutex::new(FxHashMap::default());
        let errors: Mutex<Vec<CloneError>> = Mutex::new(Vec::new());
        let total_lines: Mutex<usize> = Mutex::new(0);
        let files_excluded: Mutex<usize> = Mutex::new(0);

        let window_size = self.config.min_lines;

        // Process files
        let process_file = |file: &PathBuf| {
            match self.process_file(file, window_size) {
                Ok(Some((file_fingerprints, line_count))) => {
                    // Add fingerprints
                    let mut fp_guard = fingerprints.lock().unwrap_or_else(|e| e.into_inner());
                    for (hash, instance) in file_fingerprints {
                        fp_guard.entry(hash).or_default().push(instance);
                    }
                    drop(fp_guard);

                    // Update line count
                    *total_lines.lock().unwrap_or_else(|e| e.into_inner()) += line_count;
                }
                Ok(None) => {
                    // File was excluded
                    *files_excluded.lock().unwrap_or_else(|e| e.into_inner()) += 1;
                }
                Err(e) => {
                    errors
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .push(CloneError {
                            file: file.clone(),
                            message: e.to_string(),
                        });
                }
            }
        };

        // Choose parallel vs sequential based on file count
        if files.len() >= MIN_FILES_FOR_PARALLEL {
            files.par_iter().for_each(process_file);
        } else {
            files.iter().for_each(process_file);
        }

        // Extract results from mutex guards
        let fingerprints = fingerprints.into_inner().unwrap_or_else(|e| e.into_inner());
        let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
        stats.total_lines = *total_lines.lock().unwrap_or_else(|e| e.into_inner());
        stats.files_skipped_excluded = *files_excluded.lock().unwrap_or_else(|e| e.into_inner());

        // Build clone groups from fingerprints
        let mut clone_groups = Vec::new();
        let mut files_with_clones = FxHashSet::default();

        for (hash, instances) in fingerprints {
            if instances.len() >= 2 {
                // This is a clone group
                for inst in &instances {
                    files_with_clones.insert(inst.file.clone());
                }

                let line_count = instances
                    .first()
                    .map(|i| i.line_count())
                    .unwrap_or(window_size);
                let clone = Clone::new_type1(instances, line_count).with_fingerprint(hash);
                clone_groups.push(clone);
            }
        }

        // Sort clone groups by duplicated lines (descending)
        clone_groups.sort_by(|a, b| b.duplicated_lines().cmp(&a.duplicated_lines()));

        // Calculate statistics
        stats.clone_groups = clone_groups.len();
        stats.clone_instances = clone_groups.iter().map(|c| c.instances.len()).sum();
        stats.duplicated_lines = clone_groups.iter().map(|c| c.duplicated_lines()).sum();
        stats.files_with_clones = files_with_clones.len();
        stats.calculate_percentage();

        debug!(
            "Clone detection complete: {} groups, {} duplicated lines ({:.1}%)",
            stats.clone_groups, stats.duplicated_lines, stats.duplication_percentage
        );

        Ok(CloneAnalysis {
            path: base_path,
            config: self.config.clone(),
            clone_groups,
            stats,
            errors,
        })
    }

    /// Process a single file, returning fingerprints and line count.
    ///
    /// Returns `Ok(None)` if the file should be excluded.
    fn process_file(
        &self,
        path: &Path,
        window_size: usize,
    ) -> Result<Option<(Vec<(u64, CloneInstance)>, usize)>> {
        // Read file content
        let content =
            std::fs::read_to_string(path).map_err(|e| BrrrError::io_with_path(e, path))?;

        let original_lines: Vec<&str> = content.lines().collect();

        // Check for test fixtures
        if self.config.exclude_test_fixtures && is_test_fixture(path) {
            trace!("Skipping test fixture: {:?}", path);
            return Ok(None);
        }

        // Detect language for normalization
        let lang = self.config.language.as_deref().or_else(|| {
            LanguageRegistry::global()
                .detect_language(path)
                .map(|l| l.name())
        });

        // Normalize lines
        let mut normalizer = LineNormalizer::for_language(lang);
        let mut normalized_lines: Vec<(usize, String)> = Vec::new(); // (original_line_num, normalized)

        for (idx, line) in original_lines.iter().enumerate() {
            if let Some(normalized) = normalizer.normalize_line(line) {
                normalized_lines.push((idx + 1, normalized)); // 1-indexed line numbers
            }
        }

        // Check for generated code
        if self.config.exclude_generated {
            let first_lines: Vec<String> = original_lines
                .iter()
                .take(15)
                .map(|s| s.to_string())
                .collect();
            if is_generated_file(path, &first_lines) {
                trace!("Skipping generated file: {:?}", path);
                return Ok(None);
            }
        }

        // Check for license-heavy content (>50% license patterns in first 30 lines)
        if self.config.exclude_license_headers {
            let license_lines = normalized_lines
                .iter()
                .take(30)
                .filter(|(_, l)| is_license_content(l))
                .count();

            if license_lines > 15 {
                trace!("Skipping license-heavy file: {:?}", path);
                return Ok(None);
            }
        }

        // Not enough lines for clone detection
        if normalized_lines.len() < window_size {
            return Ok(Some((Vec::new(), original_lines.len())));
        }

        // Compute line hashes
        let line_hashes: Vec<u64> = normalized_lines.iter().map(|(_, l)| hash_line(l)).collect();

        // Build fingerprints using rolling hash
        let mut hasher = RabinHasher::new(window_size);
        let mut fingerprints: Vec<(u64, CloneInstance)> = Vec::new();

        // Initialize window
        for hash in line_hashes.iter().take(window_size) {
            hasher.push(*hash);
        }

        // Add first fingerprint
        let start_line = normalized_lines[0].0;
        let end_line = normalized_lines[window_size - 1].0;
        let preview = normalized_lines[0].1.chars().take(60).collect::<String>();

        // Skip if this block is mostly license content
        let block_is_license = self.config.exclude_license_headers
            && normalized_lines[..window_size]
                .iter()
                .filter(|(_, l)| is_license_content(l))
                .count()
                > window_size / 2;

        if !block_is_license {
            fingerprints.push((
                hasher.fingerprint(),
                CloneInstance::with_preview(path.to_path_buf(), start_line, end_line, preview),
            ));
        }

        // Slide window
        for i in window_size..normalized_lines.len() {
            // Remove oldest line hash
            hasher.pop(line_hashes[i - window_size]);
            // Add new line hash
            hasher.push(line_hashes[i]);

            let start_line = normalized_lines[i - window_size + 1].0;
            let end_line = normalized_lines[i].0;
            let preview = normalized_lines[i - window_size + 1]
                .1
                .chars()
                .take(60)
                .collect::<String>();

            // Skip if this block is mostly license content
            let block_is_license = self.config.exclude_license_headers
                && normalized_lines[i - window_size + 1..=i]
                    .iter()
                    .filter(|(_, l)| is_license_content(l))
                    .count()
                    > window_size / 2;

            if !block_is_license {
                fingerprints.push((
                    hasher.fingerprint(),
                    CloneInstance::with_preview(path.to_path_buf(), start_line, end_line, preview),
                ));
            }
        }

        Ok(Some((fingerprints, original_lines.len())))
    }
}

// =============================================================================
// PUBLIC API
// =============================================================================

/// Detect textual clones (Type-1) in a project.
///
/// This is the main entry point for clone detection.
///
/// # Arguments
///
/// * `path` - Path to file or directory to analyze
/// * `min_lines` - Minimum clone size in lines (default: 6)
/// * `language` - Optional language filter
///
/// # Returns
///
/// A `CloneAnalysis` containing detected clone groups and statistics.
///
/// # Example
///
/// ```ignore
/// let result = detect_clones("./src", Some(6), None)?;
/// println!("Found {} clone groups", result.clone_groups.len());
/// for clone in &result.clone_groups {
///     println!("Clone with {} instances ({} lines each):",
///         clone.instances.len(), clone.line_count);
///     for instance in &clone.instances {
///         println!("  {}:{}-{}", instance.file.display(),
///             instance.start_line, instance.end_line);
///     }
/// }
/// ```
pub fn detect_clones(
    path: impl AsRef<Path>,
    min_lines: Option<usize>,
    language: Option<&str>,
) -> Result<CloneAnalysis> {
    let mut config = CloneConfig::default();

    if let Some(min) = min_lines {
        config.min_lines = min;
    }

    if let Some(lang) = language {
        config.language = Some(lang.to_string());
    }

    let detector = TextualCloneDetector::new(config);
    detector.detect(path)
}

/// Analyze clone results and return a summary suitable for display.
///
/// # Arguments
///
/// * `analysis` - Clone analysis result
///
/// # Returns
///
/// A human-readable summary string.
pub fn format_clone_summary(analysis: &CloneAnalysis) -> String {
    let mut output = String::new();

    output.push_str(&format!(
        "Clone Detection Results for {}\n",
        analysis.path.display()
    ));
    output.push_str(&format!("{}\n\n", "=".repeat(60)));

    // Statistics
    output.push_str("Statistics:\n");
    output.push_str(&format!(
        "  Files scanned:     {}\n",
        analysis.stats.files_scanned
    ));
    output.push_str(&format!(
        "  Files with clones: {}\n",
        analysis.stats.files_with_clones
    ));
    output.push_str(&format!(
        "  Clone groups:      {}\n",
        analysis.stats.clone_groups
    ));
    output.push_str(&format!(
        "  Clone instances:   {}\n",
        analysis.stats.clone_instances
    ));
    output.push_str(&format!(
        "  Total lines:       {}\n",
        analysis.stats.total_lines
    ));
    output.push_str(&format!(
        "  Duplicated lines:  {}\n",
        analysis.stats.duplicated_lines
    ));
    output.push_str(&format!(
        "  Duplication:       {:.1}%\n\n",
        analysis.stats.duplication_percentage
    ));

    // Top clone groups
    if !analysis.clone_groups.is_empty() {
        output.push_str("Top Clone Groups:\n");
        for (i, clone) in analysis.clone_groups.iter().take(10).enumerate() {
            output.push_str(&format!(
                "\n{}. {} instances, {} lines each ({} duplicated lines)\n",
                i + 1,
                clone.instances.len(),
                clone.line_count,
                clone.duplicated_lines()
            ));

            for instance in &clone.instances {
                output.push_str(&format!(
                    "   {}:{}-{}\n",
                    instance.file.display(),
                    instance.start_line,
                    instance.end_line
                ));
                if let Some(ref preview) = instance.preview {
                    output.push_str(&format!("      > {}\n", preview));
                }
            }
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

    #[test]
    fn test_rabin_hasher_basic() {
        let mut hasher = RabinHasher::new(3);

        hasher.push(hash_line("line 1"));
        hasher.push(hash_line("line 2"));
        hasher.push(hash_line("line 3"));

        let fp1 = hasher.fingerprint();

        // Reset and add same lines
        hasher.reset();
        hasher.push(hash_line("line 1"));
        hasher.push(hash_line("line 2"));
        hasher.push(hash_line("line 3"));

        let fp2 = hasher.fingerprint();

        assert_eq!(fp1, fp2, "Same lines should produce same fingerprint");
    }

    #[test]
    fn test_rabin_hasher_sliding() {
        let mut hasher = RabinHasher::new(2);

        let h1 = hash_line("a");
        let h2 = hash_line("b");
        let h3 = hash_line("c");

        hasher.push(h1);
        hasher.push(h2);
        let fp_ab = hasher.fingerprint();

        hasher.pop(h1);
        hasher.push(h3);
        let fp_bc = hasher.fingerprint();

        // Reset and verify bc fingerprint
        hasher.reset();
        hasher.push(h2);
        hasher.push(h3);
        let fp_bc_direct = hasher.fingerprint();

        assert_ne!(
            fp_ab, fp_bc,
            "Different windows should have different fingerprints"
        );
        assert_eq!(fp_bc, fp_bc_direct, "Sliding and direct should match");
    }

    #[test]
    fn test_line_normalizer_comments() {
        let mut normalizer = LineNormalizer::for_language(Some("rust"));

        assert_eq!(
            normalizer.normalize_line("let x = 5; // this is a comment"),
            Some("let x = 5;".to_string())
        );

        assert_eq!(
            normalizer.normalize_line("  let   y   =   10;  "),
            Some("let y = 10;".to_string())
        );

        assert_eq!(normalizer.normalize_line("// just a comment"), None);
        assert_eq!(normalizer.normalize_line("   "), None);
    }

    #[test]
    fn test_line_normalizer_python() {
        let mut normalizer = LineNormalizer::for_language(Some("python"));

        assert_eq!(
            normalizer.normalize_line("x = 5  # assign x"),
            Some("x = 5".to_string())
        );

        assert_eq!(normalizer.normalize_line("# just a comment"), None);
    }

    #[test]
    fn test_line_normalizer_block_comments() {
        let mut normalizer = LineNormalizer::for_language(Some("rust"));

        // Inline block comment
        assert_eq!(
            normalizer.normalize_line("let x /* comment */ = 5;"),
            Some("let x = 5;".to_string())
        );
    }

    #[test]
    fn test_is_in_string_literal_simd() {
        let normalizer = LineNormalizer::for_language(Some("rust"));

        // Not in string - comment at end of code
        assert!(!normalizer.is_in_string_literal("let x = 5; // comment", 11));

        // Inside double-quoted string
        assert!(normalizer.is_in_string_literal(r#"let s = "hello // world";"#, 15));

        // Inside single-quoted char
        assert!(normalizer.is_in_string_literal("let c = '/' + other;", 10));

        // Escaped quote - not in string after escaped quote
        assert!(!normalizer.is_in_string_literal(r#"let s = "test\""; // comment"#, 20));

        // Empty position
        assert!(!normalizer.is_in_string_literal("let x = 5;", 0));

        // Long string to test SIMD 32-byte chunks
        let long_line = format!(
            r#"let long = "{}"; // comment at position 60"#,
            "a".repeat(40)
        );
        // Position after the closing quote (outside string)
        assert!(!normalizer.is_in_string_literal(&long_line, 56));
        // Position inside the string (inside quotes)
        assert!(normalizer.is_in_string_literal(&long_line, 20));
    }

    #[test]
    fn test_is_license_content() {
        assert!(is_license_content("Copyright 2024 Acme Inc"));
        assert!(is_license_content("Licensed under the MIT License"));
        assert!(is_license_content("SPDX-License-Identifier: Apache-2.0"));
        assert!(!is_license_content("fn main() {}"));
        assert!(!is_license_content("let x = 5;"));
    }

    #[test]
    fn test_is_test_fixture() {
        assert!(is_test_fixture(Path::new(
            "/project/tests/fixtures/data.json"
        )));
        assert!(is_test_fixture(Path::new("/project/__fixtures__/mock.js")));
        assert!(is_test_fixture(Path::new("/project/testdata/input.txt")));
        assert!(!is_test_fixture(Path::new("/project/src/main.rs")));
    }

    #[test]
    fn test_is_generated_file() {
        assert!(is_generated_file(
            Path::new("proto.pb.go"),
            &["// Code generated by protoc-gen-go. DO NOT EDIT.".to_string()]
        ));
        assert!(is_generated_file(Path::new("types_generated.rs"), &[]));
        assert!(!is_generated_file(
            Path::new("main.rs"),
            &["fn main() {}".to_string()]
        ));
    }

    #[test]
    fn test_detect_exact_clones() {
        let temp_dir = TempDir::new().unwrap();

        // Create two files with identical code blocks
        let code = r#"
fn process_data(data: &str) -> Result<String> {
    let trimmed = data.trim();
    let validated = validate(trimmed)?;
    let processed = transform(validated);
    let result = format(processed);
    Ok(result)
}

fn other_code() {
    println!("different");
}
"#;

        let file1 = temp_dir.path().join("file1.rs");
        let file2 = temp_dir.path().join("file2.rs");

        fs::write(&file1, code).unwrap();
        fs::write(&file2, code).unwrap();

        let config = CloneConfig::default().with_min_lines(4);
        let detector = TextualCloneDetector::new(config);
        let result = detector
            .detect_in_files(temp_dir.path().to_path_buf(), &[file1, file2])
            .unwrap();

        assert!(result.stats.clone_groups > 0, "Should detect clone groups");
        assert!(
            result.stats.duplicated_lines > 0,
            "Should have duplicated lines"
        );
    }

    #[test]
    fn test_detect_no_clones() {
        let temp_dir = TempDir::new().unwrap();

        let file1 = temp_dir.path().join("file1.rs");
        let file2 = temp_dir.path().join("file2.rs");

        fs::write(&file1, "fn foo() { println!(\"foo\"); }").unwrap();
        fs::write(&file2, "fn bar() { println!(\"bar\"); }").unwrap();

        let config = CloneConfig::default().with_min_lines(6);
        let detector = TextualCloneDetector::new(config);
        let result = detector
            .detect_in_files(temp_dir.path().to_path_buf(), &[file1, file2])
            .unwrap();

        assert_eq!(
            result.stats.clone_groups, 0,
            "Should not detect clones in different code"
        );
    }

    #[test]
    fn test_clone_instance_line_count() {
        let instance = CloneInstance::new(PathBuf::from("test.rs"), 10, 15);
        assert_eq!(instance.line_count(), 6);

        let instance2 = CloneInstance::new(PathBuf::from("test.rs"), 5, 5);
        assert_eq!(instance2.line_count(), 1);
    }

    #[test]
    fn test_clone_duplicated_lines() {
        let clone = Clone::new_type1(
            vec![
                CloneInstance::new(PathBuf::from("a.rs"), 1, 6),
                CloneInstance::new(PathBuf::from("b.rs"), 1, 6),
                CloneInstance::new(PathBuf::from("c.rs"), 1, 6),
            ],
            6,
        );

        // 3 instances, 6 lines each, first is "original" so 2 * 6 = 12 duplicated
        assert_eq!(clone.duplicated_lines(), 12);
    }

    #[test]
    fn test_clone_config_builder() {
        let config = CloneConfig::default()
            .with_min_lines(10)
            .with_language("python")
            .with_ignore_patterns(vec!["*.test.py".to_string()]);

        assert_eq!(config.min_lines, 10);
        assert_eq!(config.language, Some("python".to_string()));
        assert_eq!(config.ignore_patterns.len(), 1);
    }

    #[test]
    fn test_hash_line_consistency() {
        let line = "let x = foo(bar, baz);";
        let h1 = hash_line(line);
        let h2 = hash_line(line);
        assert_eq!(h1, h2, "Same line should produce same hash");

        let h3 = hash_line("let y = bar(foo);");
        assert_ne!(h1, h3, "Different lines should produce different hashes");
    }

    #[test]
    fn test_format_clone_summary() {
        let analysis = CloneAnalysis {
            path: PathBuf::from("./src"),
            config: CloneConfig::default(),
            clone_groups: vec![Clone::new_type1(
                vec![
                    CloneInstance::with_preview(
                        PathBuf::from("a.rs"),
                        1,
                        6,
                        "fn test()".to_string(),
                    ),
                    CloneInstance::with_preview(
                        PathBuf::from("b.rs"),
                        10,
                        15,
                        "fn test()".to_string(),
                    ),
                ],
                6,
            )],
            stats: CloneStats {
                files_scanned: 10,
                files_with_clones: 2,
                clone_groups: 1,
                clone_instances: 2,
                duplicated_lines: 6,
                total_lines: 100,
                duplication_percentage: 6.0,
                ..Default::default()
            },
            errors: Vec::new(),
        };

        let summary = format_clone_summary(&analysis);
        assert!(summary.contains("Clone Detection Results"));
        assert!(summary.contains("Files scanned:     10"));
        assert!(summary.contains("Duplication:       6.0%"));
    }
}
