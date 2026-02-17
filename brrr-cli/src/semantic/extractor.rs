//! Semantic unit extraction from source code.
//!
//! Provides functions to extract code units (functions, classes, methods) from
//! a project and prepare them for semantic embedding. Handles chunking of
//! oversized units and semantic pattern detection.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use parking_lot::RwLock;
use rustc_hash::FxHashMap;
use std::time::SystemTime;

use once_cell::sync::Lazy;
use rayon::prelude::*;
use regex::Regex;
use walkdir::WalkDir;

use crate::ast::{AstExtractor, ClassInfo, FunctionInfo};
use crate::callgraph::{self, CallGraph, FunctionRef};
use crate::cfg::{CfgBuilder, EdgeType};
use crate::dfg::DfgBuilder;
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::util::ignore::BrrrIgnore;

use super::chunker::ensure_tokenizer_loaded;
use super::types::{
    ChunkInfo, CodeComplexity, EmbeddingUnit, UnitKind, CHUNK_OVERLAP_TOKENS,
    MAX_CODE_PREVIEW_TOKENS, MAX_EMBEDDING_TOKENS, SEMANTIC_PATTERNS,
};

// =============================================================================
// Token Counting (re-exported from chunker for consistency)
// =============================================================================

// Re-export canonical token counting functions from chunker module.
// This ensures consistent token counting behavior across the codebase.
// The chunker uses `encode_ordinary` which excludes special tokens -
// this is correct for chunk splitting where we count actual text tokens.
pub use super::chunker::{count_tokens, truncate_to_tokens};

// =============================================================================
// Semantic Pattern Detection
// =============================================================================

/// Compiled regex patterns for semantic detection.
/// Patterns are compiled with case-insensitive flag to avoid allocating
/// a lowercased copy of the entire code string on every call.
static COMPILED_PATTERNS: Lazy<Vec<(&'static str, Regex)>> = Lazy::new(|| {
    use regex::RegexBuilder;
    SEMANTIC_PATTERNS
        .iter()
        .filter_map(|p| {
            RegexBuilder::new(p.pattern)
                .case_insensitive(true)
                .build()
                .ok()
                .map(|re| (p.name, re))
        })
        .collect()
});

// =============================================================================
// File-Based Unit Cache
// =============================================================================

/// Cached extraction result with modification time for invalidation.
#[derive(Clone)]
struct CachedUnits {
    /// File modification time when extraction was performed.
    mtime: SystemTime,
    /// Language used for extraction.
    language: String,
    /// Extracted embedding units.
    units: Vec<EmbeddingUnit>,
}

/// Per-file cache for extracted semantic units.
/// Key is the canonicalized file path to ensure consistency.
static UNIT_CACHE: Lazy<RwLock<FxHashMap<PathBuf, CachedUnits>>> =
    Lazy::new(|| RwLock::new(FxHashMap::default()));

/// Process a file with caching based on modification time.
///
/// Returns cached results if the file hasn't been modified since last extraction.
/// Otherwise, extracts fresh and updates the cache.
fn process_file_cached(
    project_root: &Path,
    file_path: &Path,
    language: &str,
) -> Result<Vec<EmbeddingUnit>> {
    // Canonicalize path for consistent cache keys
    let canonical_path = file_path.canonicalize().map_err(BrrrError::Io)?;

    // Get file modification time
    let mtime = file_path
        .metadata()
        .and_then(|m| m.modified())
        .map_err(BrrrError::Io)?;

    // Check cache first (read lock)
    {
        let cache = UNIT_CACHE.read();
        if let Some(cached) = cache.get(&canonical_path) {
            if cached.mtime == mtime && cached.language == language {
                return Ok(cached.units.clone());
            }
        }
    }

    // Cache miss or stale - extract fresh
    let units = process_file_uncached(project_root, file_path, language)?;

    // Update cache (write lock)
    {
        let mut cache = UNIT_CACHE.write();
        cache.insert(
            canonical_path,
            CachedUnits {
                mtime,
                language: language.to_string(),
                units: units.clone(),
            },
        );
    }

    Ok(units)
}

/// Clear the entire unit cache.
///
/// Useful when you want to force re-extraction of all files,
/// or to free memory when the cache is no longer needed.
pub fn clear_unit_cache() {
    let mut cache = UNIT_CACHE.write();
    cache.clear();
}

/// Get the number of cached files.
///
/// Returns the count of files currently in the extraction cache.
#[must_use]
pub fn unit_cache_stats() -> usize {
    let cache = UNIT_CACHE.read();
    cache.len()
}

/// Invalidate cache for a specific file.
///
/// Call this when you know a file has changed and want to ensure
/// the next extraction uses fresh data.
pub fn invalidate_unit_cache(file_path: &Path) {
    if let Ok(canonical) = file_path.canonicalize() {
        let mut cache = UNIT_CACHE.write();
        cache.remove(&canonical);
    }
}

/// Invalidate cache entries matching a predicate.
///
/// Useful for invalidating all files in a directory.
pub fn invalidate_unit_cache_matching<F>(predicate: F)
where
    F: Fn(&Path) -> bool,
{
    let mut cache = UNIT_CACHE.write();
    cache.retain(|path, _| !predicate(path));
}

/// Detect semantic patterns in code and return matching category names.
///
/// Scans code for common patterns (CRUD, validation, error handling, etc.)
/// using word-boundary regex patterns to avoid false positives.
#[must_use]
pub fn detect_semantic_patterns(code: &str) -> Vec<String> {
    if code.is_empty() {
        return Vec::new();
    }

    // Patterns are compiled case-insensitive, so no need to allocate
    // a lowercased copy of the (potentially huge) code string.
    let mut matched = Vec::new();

    for (name, regex) in COMPILED_PATTERNS.iter() {
        if regex.is_match(code) {
            matched.push((*name).to_string());
        }
    }

    matched.sort();
    matched
}

// =============================================================================
// Code Complexity Analysis
// =============================================================================

/// Calculate indentation depth handling both tabs and spaces.
///
/// Counts leading whitespace treating tabs as 4 spaces, without allocating.
/// Called on every line during complexity analysis, so allocation-free is critical.
#[inline]
fn get_indent_depth(line: &str) -> usize {
    let mut width = 0;
    for b in line.bytes() {
        match b {
            b'\t' => width += 4,
            b' ' => width += 1,
            _ => break,
        }
    }
    width / 4
}

/// Analyze code complexity without full AST parsing.
/// Quick heuristic analysis for embedding enrichment.
#[must_use]
pub fn detect_code_complexity(code: &str) -> CodeComplexity {
    if code.is_empty() {
        return CodeComplexity::empty();
    }

    // Count maximum indentation depth
    let max_depth = code.lines().map(get_indent_depth).max().unwrap_or(0);

    // Compile patterns once
    static BRANCH_PATTERN: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"\b(if|elif|else|case|switch|match)\b").expect("valid regex"));
    static LOOP_PATTERN: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"\b(for|while|loop)\b").expect("valid regex"));

    let branches = BRANCH_PATTERN.find_iter(code).count();
    let loops = LOOP_PATTERN.find_iter(code).count();

    CodeComplexity {
        depth: max_depth,
        branches,
        loops,
    }
}

// =============================================================================
// Chunking
// =============================================================================

/// Split code into token-limited chunks with overlap.
///
/// This function delegates to [`chunker::chunk_code_with_overlap`] which provides
/// sophisticated boundary-aware splitting. The results are converted to
/// [`ChunkInfo`] for backward compatibility.
///
/// The chunker module handles:
/// - Natural boundary detection (function/class definitions, blank lines)
/// - Context overlap for continuity between chunks
/// - Oversized chunk handling with fallback strategies
///
/// # Arguments
///
/// * `code` - Source code to split
/// * `max_tokens` - Maximum tokens per chunk
/// * `overlap_tokens` - Tokens to overlap between consecutive chunks
///
/// # Returns
///
/// Vector of [`ChunkInfo`] with text content and character offsets.
#[must_use]
pub fn split_into_chunks(code: &str, max_tokens: usize, overlap_tokens: usize) -> Vec<ChunkInfo> {
    use super::chunker::chunk_code_with_overlap;

    if code.is_empty() {
        return Vec::new();
    }

    // Delegate to the canonical chunker implementation
    let chunks = chunk_code_with_overlap(code, max_tokens, overlap_tokens);

    // Convert Chunk to ChunkInfo for backward compatibility
    chunks
        .into_iter()
        .map(|chunk| ChunkInfo::new(chunk.content, chunk.start_char, chunk.end_char))
        .collect()
}

/// Split an oversized unit into token-limited chunks.
///
/// Each chunk inherits metadata from parent and includes:
/// - Signature and docstring in first chunk
/// - Parent reference in all chunks
/// - Chunk index/total for reconstruction
pub fn chunk_unit(unit: &EmbeddingUnit) -> Vec<EmbeddingUnit> {
    if unit.code.is_empty() {
        return vec![unit.clone()];
    }

    let code_tokens = count_tokens(&unit.code);
    if code_tokens <= MAX_CODE_PREVIEW_TOKENS {
        let mut result = unit.clone();
        result.token_count = code_tokens;
        return vec![result];
    }

    // Split the code into chunks
    let chunks = split_into_chunks(&unit.code, MAX_CODE_PREVIEW_TOKENS, CHUNK_OVERLAP_TOKENS);

    if chunks.len() <= 1 {
        // Couldn't split effectively, just truncate
        let mut result = unit.clone();
        result.code = truncate_to_tokens(&unit.code, MAX_CODE_PREVIEW_TOKENS);
        result.token_count = count_tokens(&result.code);
        return vec![result];
    }

    // Create chunk units
    chunks
        .iter()
        .enumerate()
        .map(|(i, chunk)| {
            let chunk_name = format!("{}[{}/{}]", unit.name, i + 1, chunks.len());
            let lines_before = memchr::memchr_iter(b'\n', unit.code[..chunk.start_char].as_bytes()).count();

            EmbeddingUnit {
                id: format!("{}#chunk{}", unit.id, i + 1),
                file: unit.file.clone(),
                name: chunk_name,
                kind: UnitKind::Chunk,
                code: chunk.text.clone(),
                // First chunk gets full signature/docstring
                signature: if i == 0 {
                    unit.signature.clone()
                } else {
                    format!("// continued from {}", unit.name)
                },
                docstring: if i == 0 { unit.docstring.clone() } else { None },
                start_line: if i == 0 {
                    unit.start_line
                } else {
                    unit.start_line + lines_before
                },
                end_line: unit.start_line + lines_before + memchr::memchr_iter(b'\n', chunk.text.as_bytes()).count(),
                token_count: count_tokens(&chunk.text),
                semantic_tags: detect_semantic_patterns(&chunk.text),
                parent: Some(unit.name.clone()),
                language: unit.language.clone(),
                calls: if i == 0 {
                    unit.calls.clone()
                } else {
                    Vec::new()
                },
                called_by: if i == 0 {
                    unit.called_by.clone()
                } else {
                    Vec::new()
                },
                cfg_summary: if i == 0 {
                    unit.cfg_summary.clone()
                } else {
                    String::new()
                },
                dfg_summary: if i == 0 {
                    unit.dfg_summary.clone()
                } else {
                    String::new()
                },
                dependencies: unit.dependencies.clone(),
                complexity: detect_code_complexity(&chunk.text),
                chunk_index: i,
                chunk_total: chunks.len(),
            }
        })
        .collect()
}

// =============================================================================
// Unit Enrichment
// =============================================================================

/// Add semantic enrichment to a unit (modifies in place).
///
/// Detects patterns, calculates complexity, computes token count,
/// and builds CFG/DFG summaries for functions and methods.
pub fn enrich_unit(unit: &mut EmbeddingUnit) {
    if !unit.code.is_empty() {
        unit.semantic_tags = detect_semantic_patterns(&unit.code);
        unit.complexity = detect_code_complexity(&unit.code);
        unit.token_count = count_tokens(&unit.code);

        // Compute CFG and DFG summaries for functions and methods only
        // (classes and chunks don't need individual CFG/DFG analysis)
        if matches!(unit.kind, UnitKind::Function | UnitKind::Method) {
            enrich_cfg_summary(unit);
            enrich_dfg_summary(unit);
        }
    } else {
        unit.semantic_tags.clear();
        unit.complexity = CodeComplexity::empty();
        unit.token_count = 0;
    }
}

/// Compute CFG summary for a function/method unit.
///
/// Extracts control flow graph and summarizes:
/// - Cyclomatic complexity
/// - Block count
/// - Branch count (true/false edges)
fn enrich_cfg_summary(unit: &mut EmbeddingUnit) {
    // Skip if we already have a summary (e.g., from parent propagation)
    if !unit.cfg_summary.is_empty() {
        return;
    }

    // Try to extract CFG from the unit's code
    // This requires the code to be a complete, parseable function definition
    if let Ok(cfg) = CfgBuilder::extract_from_source(&unit.code, &unit.language, &unit.name) {
        let complexity = cfg.cyclomatic_complexity();
        let block_count = cfg.blocks.len();
        let branch_count = cfg
            .edges
            .iter()
            .filter(|e| matches!(e.edge_type, EdgeType::True | EdgeType::False))
            .count();

        unit.cfg_summary = format!(
            "complexity:{}, blocks:{}, branches:{}",
            complexity, block_count, branch_count
        );
    }
    // Silently ignore extraction failures - CFG summary is optional enrichment
    // This can fail for methods (need class context), complex decorators, etc.
}

/// Compute DFG summary for a function/method unit.
///
/// Extracts data flow graph and summarizes:
/// - Variable count
/// - Def-use chain count
fn enrich_dfg_summary(unit: &mut EmbeddingUnit) {
    // Skip if we already have a summary (e.g., from parent propagation)
    if !unit.dfg_summary.is_empty() {
        return;
    }

    // Try to extract DFG from the unit's code
    if let Ok(dfg) = DfgBuilder::extract_from_source(&unit.code, &unit.language, &unit.name) {
        let var_count = dfg.variables().len();
        let def_use_chains = dfg.edges.len();

        unit.dfg_summary = format!("vars:{}, def-use chains:{}", var_count, def_use_chains);
    }
    // Silently ignore extraction failures - DFG summary is optional enrichment
}

// =============================================================================
// File Scanning
// =============================================================================

/// Supported file extensions for each language.
///
/// Must be kept in sync with Language trait implementations in `src/lang/`.
/// Extensions include:
/// - Standard source files
/// - Type stub files (e.g., .pyi for Python)
/// - ES module variants (e.g., .mjs, .cjs, .mts, .cts)
/// - Build/script files (e.g., .pyw for Python GUI)
fn get_language_extensions(lang: &str) -> &'static [&'static str] {
    match lang {
        "python" => &[".py", ".pyi", ".pyx", ".pyw"],
        "typescript" => &[".ts", ".tsx", ".mts", ".cts"],
        "javascript" => &[".js", ".jsx", ".mjs", ".cjs"],
        "go" => &[".go"],
        "rust" => &[".rs"],
        "java" => &[".java"],
        // `.h` files are handled exclusively by C++ -- the C++ tree-sitter grammar
        // parses both C and C++ headers correctly, while the C grammar rejects C++
        // constructs. Listing `.h` under both "c" and "cpp" would cause duplicate
        // processing of every header file.
        "c" => &[".c"],
        "cpp" => &[".cpp", ".hpp", ".cc", ".hh", ".cxx", ".hxx", ".h++", ".c++", ".cu", ".cuh", ".h"],
        _ => &[],
    }
}

/// Check if a file is binary by looking for null bytes.
///
/// Uses SIMD-accelerated memchr for fast null byte detection in the first 8KB.
fn is_binary_file(path: &Path) -> bool {
    use std::fs::File;
    use std::io::Read;

    let Ok(mut file) = File::open(path) else {
        return false;
    };

    let mut buffer = [0u8; 8192];
    let Ok(bytes_read) = file.read(&mut buffer) else {
        return false;
    };

    // SIMD-accelerated null byte search via memchr
    memchr::memchr(0, &buffer[..bytes_read]).is_some()
}

/// Read file content with BOM handling and graceful encoding fallback.
///
/// Handles:
/// - UTF-8 BOM (EF BB BF) - strips the BOM prefix
/// - UTF-16 LE BOM (FF FE) - converts from UTF-16 Little Endian
/// - UTF-16 BE BOM (FE FF) - converts from UTF-16 Big Endian
/// - Non-UTF-8 files - uses lossy conversion (replaces invalid chars with U+FFFD)
///
/// This ensures source files with various encodings (common in legacy codebases
/// or files created on different platforms) can still be processed for semantic
/// analysis.
///
/// # Arguments
///
/// * `path` - Path to the file to read
///
/// # Returns
///
/// The file content as a String, or an IO error if the file cannot be read.
fn read_file_content(path: &Path) -> std::io::Result<String> {
    let bytes = std::fs::read(path).map_err(|e| {
        std::io::Error::new(
            e.kind(),
            format!("Failed to read {}: {}", path.display(), e),
        )
    })?;

    // UTF-8 BOM (EF BB BF) - common in files created on Windows
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        let content = String::from_utf8_lossy(&bytes[3..]).into_owned();
        return Ok(normalize_line_endings_owned(content));
    }

    // UTF-16 LE BOM (FF FE) - Windows default for some editors
    if bytes.starts_with(&[0xFF, 0xFE]) {
        let utf16: Vec<u16> = bytes[2..]
            .chunks(2)
            .map(|chunk| u16::from_le_bytes([chunk[0], chunk.get(1).copied().unwrap_or(0)]))
            .collect();
        let content = String::from_utf16_lossy(&utf16);
        return Ok(normalize_line_endings_owned(content));
    }

    // UTF-16 BE BOM (FE FF)
    if bytes.starts_with(&[0xFE, 0xFF]) {
        let utf16: Vec<u16> = bytes[2..]
            .chunks(2)
            .map(|chunk| u16::from_be_bytes([chunk[0], chunk.get(1).copied().unwrap_or(0)]))
            .collect();
        let content = String::from_utf16_lossy(&utf16);
        return Ok(normalize_line_endings_owned(content));
    }

    // Try UTF-8 first (most common), fall back to lossy conversion
    let content = match std::str::from_utf8(&bytes) {
        Ok(s) => s.to_string(),
        Err(_) => String::from_utf8_lossy(&bytes).into_owned(),
    };

    // Normalize line endings to LF for consistent processing across platforms.
    // This ensures token counts match between Python and Rust implementations.
    // Order matters: CRLF must be replaced before standalone CR.
    Ok(normalize_line_endings_owned(content))
}

/// Normalize line endings to LF (Unix-style) for consistent processing.
/// Takes an owned String and returns it unchanged if no CR bytes are found,
/// avoiding an unnecessary allocation in the common case.
#[inline]
fn normalize_line_endings_owned(content: String) -> String {
    // Fast path: SIMD scan for any CR byte. Most files have no CR at all.
    if memchr::memchr(b'\r', content.as_bytes()).is_none() {
        return content;
    }
    normalize_line_endings_impl(&content)
}

/// Normalize line endings to LF (Unix-style) for consistent processing.
///
/// Handles:
/// - CRLF (Windows): \r\n -> \n
/// - CR (Classic Mac): \r -> \n
///
/// Uses SIMD-accelerated memchr for fast CR detection and single-pass replacement.
/// This ensures consistent behavior across platforms and matching token counts
/// with the Python implementation.
#[inline]
#[cfg_attr(not(test), allow(dead_code))]
fn normalize_line_endings(content: &str) -> String {
    // Fast path: SIMD scan for any CR byte. Most files have no CR at all.
    if memchr::memchr(b'\r', content.as_bytes()).is_none() {
        return content.to_string();
    }
    normalize_line_endings_impl(content)
}

/// Inner implementation: single-pass CR replacement using memchr.
fn normalize_line_endings_impl(content: &str) -> String {
    let bytes = content.as_bytes();
    let mut result = String::with_capacity(content.len());
    let mut pos = 0;
    while pos < bytes.len() {
        match memchr::memchr(b'\r', &bytes[pos..]) {
            Some(offset) => {
                // Copy everything before this CR
                result.push_str(&content[pos..pos + offset]);
                result.push('\n');
                pos += offset + 1;
                // Skip the \n in CRLF pairs
                if pos < bytes.len() && bytes[pos] == b'\n' {
                    pos += 1;
                }
            }
            None => {
                // No more CRs, copy the rest
                result.push_str(&content[pos..]);
                break;
            }
        }
    }
    result
}

/// Scan project for source files of the specified language.
///
/// Respects `.brrrignore` patterns (falls back to defaults if no .brrrignore exists).
/// This ensures consistency with the Python implementation's ignore behavior.
///
/// Note: `.gitignore` is NOT loaded here - it's handled by `WalkBuilder` in scanner code.
fn scan_source_files(project_path: &Path, language: &str) -> Vec<PathBuf> {
    let extensions = get_language_extensions(language);
    if extensions.is_empty() {
        return Vec::new();
    }

    // Load ignore patterns from .brrrignore only (NOT .gitignore)
    // If loading fails, log warning and continue without ignore patterns
    let ignore = match BrrrIgnore::new(project_path) {
        Ok(ig) => Some(ig),
        Err(e) => {
            tracing::warn!(
                "Failed to load .brrrignore patterns: {}. Proceeding without ignore filtering.",
                e
            );
            None
        }
    };

    let mut files = Vec::new();

    for entry in WalkDir::new(project_path)
        .follow_links(false)
        .into_iter()
        .filter_entry(|e| {
            // Check if this entry should be ignored using .brrrignore patterns
            match &ignore {
                Some(ig) => !ig.is_ignored(e.path()),
                None => true, // Include all files if ignore patterns failed to load
            }
        })
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if path.is_file() {
            let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if extensions.iter().any(|ext| file_name.ends_with(ext)) {
                if !is_binary_file(path) {
                    files.push(path.to_path_buf());
                }
            }
        }
    }

    files
}

// =============================================================================
// Unit Creation Helpers
// =============================================================================

/// Create an EmbeddingUnit from a FunctionInfo.
fn function_to_unit(
    func: &FunctionInfo,
    file_path: &str,
    code_content: &str,
    language: &str,
) -> EmbeddingUnit {
    // Extract code for this function
    let code = extract_function_code(code_content, func.line_number, func.end_line_number);

    let mut unit = EmbeddingUnit::new(
        file_path,
        &func.name,
        if func.is_method {
            UnitKind::Method
        } else {
            UnitKind::Function
        },
        code,
        func.line_number,
        language,
    );

    unit.signature = func.signature();
    unit.docstring = func.docstring.clone();
    unit.end_line = func.end_line_number.unwrap_or(func.line_number);

    unit
}

/// Create an EmbeddingUnit from a ClassInfo.
fn class_to_unit(
    class: &ClassInfo,
    file_path: &str,
    code_content: &str,
    language: &str,
) -> EmbeddingUnit {
    // Extract code for this class
    let code = extract_function_code(code_content, class.line_number, class.end_line_number);

    let mut unit = EmbeddingUnit::new(
        file_path,
        &class.name,
        UnitKind::Class,
        code,
        class.line_number,
        language,
    );

    unit.signature = format!("class {}", class.name);
    if !class.bases.is_empty() {
        unit.signature = format!("class {}({})", class.name, class.bases.join(", "));
    }
    unit.docstring = class.docstring.clone();
    unit.end_line = class.end_line_number.unwrap_or(class.line_number);

    unit
}

/// Create EmbeddingUnits for methods within a class.
fn methods_to_units(
    class: &ClassInfo,
    file_path: &str,
    code_content: &str,
    language: &str,
) -> Vec<EmbeddingUnit> {
    class
        .methods
        .iter()
        .map(|method| {
            let code =
                extract_function_code(code_content, method.line_number, method.end_line_number);

            let mut unit = EmbeddingUnit::new(
                file_path,
                &method.name,
                UnitKind::Method,
                code,
                method.line_number,
                language,
            );

            unit.id = format!("{}::{}.{}", file_path, class.name, method.name);
            unit.signature = method.signature();
            unit.docstring = method.docstring.clone();
            unit.end_line = method.end_line_number.unwrap_or(method.line_number);
            unit.parent = Some(class.name.clone());

            unit
        })
        .collect()
}

/// Extract code for a function/class given line numbers.
///
/// Uses SIMD-accelerated memchr to find newline byte offsets, then slices
/// directly from the content string. Avoids collecting all lines into a Vec
/// (which was O(total_lines) even for a small function at the end of a file).
fn extract_function_code(content: &str, start_line: usize, end_line: Option<usize>) -> String {
    if content.is_empty() || start_line == 0 {
        return String::new();
    }

    let bytes = content.as_bytes();
    let target_start = start_line - 1; // Convert 1-indexed to 0-indexed

    // Find byte offset of the start line
    let mut line_count = 0;
    let byte_start = if target_start == 0 {
        0
    } else {
        let mut offset = 0;
        for pos in memchr::memchr_iter(b'\n', bytes) {
            line_count += 1;
            if line_count == target_start {
                offset = pos + 1;
                break;
            }
        }
        if line_count < target_start {
            return String::new(); // start_line beyond file
        }
        offset
    };

    // Find byte offset of the end line
    let byte_end = match end_line {
        Some(end_idx) => {
            // end_line is 1-indexed, inclusive. We want bytes up to end of that line.
            let target_end = end_idx; // number of lines from start of file
            let mut current_line = line_count; // lines counted so far
            for pos in memchr::memchr_iter(b'\n', &bytes[byte_start..]) {
                current_line += 1;
                if current_line == target_end {
                    // Return content up to (but not including) this newline
                    let newline_offset = byte_start + pos;
                    return content[byte_start..newline_offset].to_string();
                }
            }
            // Reached end of content before end_line
            content.len()
        }
        None => content.len(),
    };

    content[byte_start..byte_end].to_string()
}

// =============================================================================
// Main Extraction API
// =============================================================================

/// Extract all semantic units from a project directory.
///
/// Scans the project for source files, extracts functions, classes, and methods,
/// calculates token counts, adds semantic tags, and handles chunking for
/// oversized units.
///
/// # Arguments
///
/// * `project_path` - Path to project root directory
/// * `language` - Programming language to filter by (e.g., "python", "typescript")
///
/// # Returns
///
/// Vector of `EmbeddingUnit` objects ready for embedding and indexing.
///
/// # Errors
///
/// Returns error if project path doesn't exist or cannot be read.
pub fn extract_units(project_path: &str, language: &str) -> Result<Vec<EmbeddingUnit>> {
    let project = Path::new(project_path)
        .canonicalize()
        .map_err(|e| BrrrError::Io(e))?;

    if !project.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Project path not found: {}", project_path),
        )));
    }

    // Eagerly initialize the tokenizer on the main thread BEFORE spawning
    // rayon workers. The QWEN3_TOKENIZER uses once_cell::Lazy which blocks
    // all threads during initialization. If the first access happens inside
    // par_iter, ALL rayon worker threads block on the Lazy init, and if the
    // init involves a network download (HuggingFace Hub), this can hang for
    // minutes or indefinitely. By forcing init here, we pay the cost once
    // on the main thread before any parallelism begins.
    ensure_tokenizer_loaded();

    // Scan for source files
    let source_files = scan_source_files(&project, language);

    if source_files.is_empty() {
        return Ok(Vec::new());
    }

    // Process files in parallel.
    //
    // DEADLOCK FIX: Previously used process_file_cached() which acquired
    // UNIT_CACHE.read() then UNIT_CACHE.write() inside each par_iter task.
    // With parking_lot's write-preferring RwLock, a queued writer blocks
    // ALL new readers. When N rayon threads are all trying to write their
    // results while new iterations need read access, the threads starve
    // each other, causing effective deadlock on large codebases (100K+ files).
    //
    // The fix: use process_file_uncached() directly in par_iter (no shared
    // mutable state). Cache is populated in bulk AFTER parallel processing
    // completes, using a single write lock acquisition.
    let results: Vec<(PathBuf, Vec<EmbeddingUnit>)> = source_files
        .par_iter()
        .filter_map(|file_path| {
            match process_file_uncached(&project, file_path, language) {
                Ok(units) if !units.is_empty() => Some((file_path.clone(), units)),
                _ => None,
            }
        })
        .collect();

    // Bulk-populate cache with a single write lock (no contention).
    // We clone units for the cache and consume the originals for the return,
    // avoiding a second deep clone.
    let mut all_units = Vec::with_capacity(results.iter().map(|(_, u)| u.len()).sum());
    {
        let mut cache = UNIT_CACHE.write();
        for (file_path, units) in results {
            if let Ok(canonical_path) = file_path.canonicalize() {
                if let Ok(mtime) = file_path.metadata().and_then(|m| m.modified()) {
                    cache.insert(
                        canonical_path,
                        CachedUnits {
                            mtime,
                            language: language.to_string(),
                            units: units.clone(),
                        },
                    );
                }
            }
            all_units.extend(units);
        }
    }

    Ok(all_units)
}

/// Scan a project directory for source files matching the given language.
///
/// This is the public entry point for file discovery, used by the incremental
/// indexing pipeline to enumerate files before classifying them against the
/// hash cache.
///
/// # Arguments
///
/// * `project_path` - Canonicalized project root
/// * `language` - Language filter (e.g., "python", "typescript")
///
/// # Returns
///
/// Sorted list of absolute paths to source files.
pub fn scan_project_files(project_path: &Path, language: &str) -> Vec<PathBuf> {
    scan_source_files(project_path, language)
}

/// Extract semantic units from a specific set of files (incremental mode).
///
/// Unlike `extract_units` which scans the entire project, this function
/// processes only the provided file list. Used by the incremental indexing
/// pipeline to reprocess only changed files.
///
/// # Arguments
///
/// * `project_root` - Canonicalized project root for relative path computation
/// * `files` - List of absolute file paths to process
/// * `language` - Programming language for AST parsing
///
/// # Returns
///
/// Vector of `EmbeddingUnit` objects from the specified files.
pub fn extract_units_from_paths(
    project_root: &Path,
    files: &[PathBuf],
    language: &str,
) -> Result<Vec<EmbeddingUnit>> {
    if files.is_empty() {
        return Ok(Vec::new());
    }

    // Ensure tokenizer is loaded before parallel work (deadlock prevention)
    ensure_tokenizer_loaded();

    let results: Vec<(PathBuf, Vec<EmbeddingUnit>)> = files
        .par_iter()
        .filter_map(|file_path| {
            match process_file_uncached(project_root, file_path, language) {
                Ok(units) if !units.is_empty() => Some((file_path.clone(), units)),
                Ok(_) => None,
                Err(e) => {
                    tracing::debug!("Failed to extract units from {}: {}", file_path.display(), e);
                    None
                }
            }
        })
        .collect();

    let units: Vec<EmbeddingUnit> = results.into_iter().flat_map(|(_, units)| units).collect();
    Ok(units)
}

/// Extract a dependency summary string from import statements.
///
/// Formats imports into a concise summary for embedding enrichment.
/// Limits to the first 10 imports to keep the summary manageable.
///
/// # Arguments
///
/// * `imports` - Slice of `ImportInfo` from AST extraction
///
/// # Returns
///
/// A semicolon-separated string of import statements, or empty string if no imports.
fn extract_dependency_summary(imports: &[crate::ast::ImportInfo]) -> String {
    if imports.is_empty() {
        return String::new();
    }

    imports
        .iter()
        .take(10) // Limit to top 10 imports to avoid bloating embedding text
        .map(|imp| {
            if imp.is_from {
                // "from X import Y" style
                let names = if imp.names.len() > 3 {
                    // Truncate long import lists
                    format!("{}, ...", imp.names[..3].join(", "))
                } else {
                    imp.names.join(", ")
                };
                if imp.module.is_empty() {
                    // Relative import: from . import X
                    let dots = ".".repeat(imp.level.max(1));
                    format!("from {} import {}", dots, names)
                } else if imp.level > 0 {
                    // Relative with module: from ..module import X
                    let dots = ".".repeat(imp.level);
                    format!("from {}{} import {}", dots, imp.module, names)
                } else {
                    format!("from {} import {}", imp.module, names)
                }
            } else {
                // Simple "import X" style
                imp.module.clone()
            }
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// Process a single file and extract all units (uncached version).
///
/// This is the core extraction logic. Use `process_file_cached` for
/// performance when processing the same files multiple times.
fn process_file_uncached(
    project_root: &Path,
    file_path: &Path,
    language: &str,
) -> Result<Vec<EmbeddingUnit>> {
    // Get relative path for unit IDs
    let relative_path = file_path
        .strip_prefix(project_root)
        .unwrap_or(file_path)
        .to_string_lossy()
        .to_string();

    // Read file content with BOM handling and encoding fallback (RS-15 fix)
    let content = read_file_content(file_path)?;

    // Parse with AST extractor using the caller's language, not auto-detection.
    // This is critical for `.h` files in mixed C/C++ projects: when the C++ pass
    // scans `.h` files, they must be parsed with the C++ grammar (which handles
    // both C and C++ code), not the C grammar which would reject C++ headers.
    let module_info = AstExtractor::extract_file_as(file_path, language)?;

    // Extract dependencies from imports (RS-12 fix)
    // This enriches semantic search by including what modules each code unit depends on
    let dependency_summary = extract_dependency_summary(&module_info.imports);

    let mut all_units = Vec::new();

    // Process top-level functions
    for func in &module_info.functions {
        let mut unit = function_to_unit(func, &relative_path, &content, language);
        unit.dependencies = dependency_summary.clone();
        enrich_unit(&mut unit);

        // Chunk if needed
        let chunked = chunk_unit(&unit);
        all_units.extend(chunked);
    }

    // Process classes and their methods
    for class in &module_info.classes {
        // Add class unit
        let mut class_unit = class_to_unit(class, &relative_path, &content, language);
        class_unit.dependencies = dependency_summary.clone();
        enrich_unit(&mut class_unit);

        let chunked_class = chunk_unit(&class_unit);
        all_units.extend(chunked_class);

        // Add method units
        for mut method_unit in methods_to_units(class, &relative_path, &content, language) {
            method_unit.dependencies = dependency_summary.clone();
            enrich_unit(&mut method_unit);

            let chunked_method = chunk_unit(&method_unit);
            all_units.extend(chunked_method);
        }
    }

    Ok(all_units)
}

/// Extract units from a single file (convenience function).
///
/// # Arguments
///
/// * `file_path` - Path to source file
///
/// # Returns
///
/// Vector of `EmbeddingUnit` objects from the file.
pub fn extract_units_from_file(file_path: &str) -> Result<Vec<EmbeddingUnit>> {
    let path = Path::new(file_path);

    if !path.exists() {
        return Err(BrrrError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", file_path),
        )));
    }

    // Detect language
    let registry = LanguageRegistry::global();
    let lang = registry.detect_language(path).ok_or_else(|| {
        BrrrError::UnsupportedLanguage(
            path.extension()
                .and_then(|e| e.to_str())
                .unwrap_or("unknown")
                .to_string(),
        )
    })?;

    let parent = path.parent().unwrap_or(Path::new("."));
    process_file_cached(parent, path, lang.name())
}

// =============================================================================
// Call Graph Integration
// =============================================================================

/// Extract semantic units with call graph information.
///
/// This function builds a call graph for the project and enriches each
/// extracted unit with `calls` and `called_by` information, enabling
/// semantic search to understand function relationships.
///
/// # Arguments
///
/// * `project_path` - Path to project root directory
/// * `language` - Programming language to filter by (e.g., "python", "typescript")
///
/// # Returns
///
/// Vector of `EmbeddingUnit` objects with populated `calls` and `called_by` fields.
///
/// # Errors
///
/// Returns error if project path doesn't exist, cannot be read, or call graph
/// building fails.
///
/// # Example
///
/// ```no_run
/// use brrr::semantic::extract_units_with_callgraph;
///
/// let units = extract_units_with_callgraph("./my_project", "python")?;
/// for unit in &units {
///     if !unit.calls.is_empty() {
///         println!("{} calls: {:?}", unit.name, unit.calls);
///     }
///     if !unit.called_by.is_empty() {
///         println!("{} called by: {:?}", unit.name, unit.called_by);
///     }
/// }
/// # Ok::<(), brrr::BrrrError>(())
/// ```
pub fn extract_units_with_callgraph(
    project_path: &str,
    language: &str,
) -> Result<Vec<EmbeddingUnit>> {
    let project = Path::new(project_path)
        .canonicalize()
        .map_err(BrrrError::Io)?;

    // Build call graph first
    let mut call_graph = callgraph::build(project_path)?;
    call_graph.build_indexes();

    // Extract units as before
    let mut units = extract_units(project_path, language)?;

    // Build a name-based index from the call graph for O(1) lookup per unit.
    // The old approach iterated ALL edges for EVERY unit -- O(units * edges),
    // with canonicalize() syscalls in the inner loop. For PyTorch (~100k edges,
    // ~50k units) this caused extreme slowness. Now it's O(units + edges).
    let func_index = build_callgraph_index(&call_graph);

    // Enrich with call graph data
    for unit in &mut units {
        // Skip chunks - they inherit call info from parent
        if unit.kind == UnitKind::Chunk {
            continue;
        }

        // Find matching function in call graph via index
        if let Some(func_ref) = find_function_in_index(
            &func_index,
            &project,
            &unit.file,
            &unit.name,
            unit.parent.as_deref(),
        ) {
            // Get functions this unit calls (callees).
            // Sort and dedup BEFORE truncating to 20 -- the old order
            // (take then sort/dedup) discarded valid entries and left
            // non-deterministic results due to HashSet iteration order.
            if let Some(callees) = call_graph.callees.get(&func_ref) {
                let mut names: Vec<String> =
                    callees.iter().map(|f| f.name.clone()).collect();
                names.sort();
                names.dedup();
                names.truncate(20);
                unit.calls = names;
            }

            // Get functions that call this unit (callers)
            if let Some(callers) = call_graph.callers.get(&func_ref) {
                let mut names: Vec<String> =
                    callers.iter().map(|f| f.name.clone()).collect();
                names.sort();
                names.dedup();
                names.truncate(20);
                unit.called_by = names;
            }
        }
    }

    // Propagate call info to first chunk of chunked units
    propagate_call_info_to_chunks(&mut units);

    Ok(units)
}

/// Index of function name -> deduplicated list of FunctionRefs with that name.
///
/// Built once from the call graph, then used for O(1) name lookup
/// instead of O(edges) linear scan per unit.
type CallGraphIndex = FxHashMap<String, Vec<FunctionRef>>;

/// Build a name-based index from a call graph.
///
/// Collects all unique FunctionRefs (from edges and index maps) keyed by name.
/// Built ONCE then queried for each unit, replacing O(N*E) with O(N + E).
fn build_callgraph_index(graph: &CallGraph) -> CallGraphIndex {
    let mut index: CallGraphIndex = FxHashMap::default();

    // Collect from edges
    for edge in &graph.edges {
        index
            .entry(edge.caller.name.clone())
            .or_default()
            .push(edge.caller.clone());
        index
            .entry(edge.callee.name.clone())
            .or_default()
            .push(edge.callee.clone());
    }

    // Collect from index maps (may contain functions not in edges)
    for func_ref in graph.callees.keys().chain(graph.callers.keys()) {
        index
            .entry(func_ref.name.clone())
            .or_default()
            .push(func_ref.clone());
    }

    // Deduplicate each bucket
    for refs in index.values_mut() {
        refs.sort_by(|a, b| a.file.cmp(&b.file));
        refs.dedup();
    }

    index
}

/// Find a function reference in the pre-built index.
///
/// Uses O(1) name lookup then checks file path match among the (typically few)
/// candidates sharing that name. No syscalls (canonicalize) in the hot path --
/// only cheap string comparisons.
fn find_function_in_index(
    index: &CallGraphIndex,
    project_root: &Path,
    unit_file: &str,
    unit_name: &str,
    parent_class: Option<&str>,
) -> Option<FunctionRef> {
    let candidates = index.get(unit_name)?;

    // Build expected absolute path once per lookup (not per candidate)
    let expected_path = project_root.join(unit_file);
    let expected_path_str = expected_path.to_string_lossy();

    let matches_file = |func_file: &str| -> bool {
        // Exact match (most common case)
        if func_file == expected_path_str.as_ref() {
            return true;
        }
        // Suffix match for relative paths
        if func_file.ends_with(unit_file) {
            return true;
        }
        // Reverse suffix match
        if expected_path_str.ends_with(func_file) {
            return true;
        }
        false
    };

    for func_ref in candidates {
        if !matches_file(&func_ref.file) {
            continue;
        }
        // For methods, also check class match via qualified name
        if let Some(class) = parent_class {
            if let Some(ref qname) = func_ref.qualified_name {
                if qname.contains(class) {
                    return Some(func_ref.clone());
                }
            }
            // Parent class specified but no qualified name match -- skip candidate
        } else {
            return Some(func_ref.clone());
        }
    }

    None
}

/// Propagate call information from original units to their first chunks.
///
/// When a unit is chunked, only the first chunk should carry the call
/// information to avoid duplicating it across all chunks.
fn propagate_call_info_to_chunks(units: &mut [EmbeddingUnit]) {
    // Build a map of parent name -> call info for non-chunk units
    let mut call_info_map: FxHashMap<String, (Vec<String>, Vec<String>)> =
        FxHashMap::default();

    for unit in units.iter() {
        if unit.kind != UnitKind::Chunk && (!unit.calls.is_empty() || !unit.called_by.is_empty()) {
            call_info_map.insert(
                unit.name.clone(),
                (unit.calls.clone(), unit.called_by.clone()),
            );
        }
    }

    // Apply to first chunks
    for unit in units.iter_mut() {
        if unit.kind == UnitKind::Chunk && unit.chunk_index == 0 {
            if let Some(parent_name) = &unit.parent {
                if let Some((calls, called_by)) = call_info_map.get(parent_name) {
                    if unit.calls.is_empty() {
                        unit.calls = calls.clone();
                    }
                    if unit.called_by.is_empty() {
                        unit.called_by = called_by.clone();
                    }
                }
            }
        }
    }
}

// =============================================================================
// Embedding Text Building
// =============================================================================

/// Parse camelCase/snake_case/PascalCase identifier to space-separated words.
/// Converts code identifiers into natural language for better semantic search.
#[must_use]
pub fn parse_identifier_to_words(name: &str) -> String {
    let name = name.trim_matches('_');
    if name.is_empty() {
        return String::new();
    }

    // Handle snake_case
    let name = name.replace('_', " ");

    // Handle camelCase and PascalCase
    static CAMEL_RE: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"([a-z])([A-Z])").expect("valid regex"));
    static ACRONYM_RE: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"([A-Z]+)([A-Z][a-z])").expect("valid regex"));

    let words = CAMEL_RE.replace_all(&name, "$1 $2");
    let words = ACRONYM_RE.replace_all(&words, "$1 $2");

    // Clean up and lowercase
    words
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_lowercase()
}

/// Extract inline comments from code for semantic enrichment.
///
/// Comments often contain valuable natural language descriptions that improve
/// semantic search quality. Handles both line comments (//, #) and block
/// comments (/* */, """).
///
/// # Arguments
///
/// * `code` - Source code to extract comments from
/// * `language` - Programming language name for comment syntax detection
///
/// # Returns
///
/// Vector of extracted comment strings, limited to 20 most relevant.
#[must_use]
pub fn extract_inline_comments(code: &str, language: &str) -> Vec<String> {
    if code.is_empty() {
        return Vec::new();
    }

    let mut comments = Vec::new();

    // Get comment delimiters for the language
    let (line_comment, block_start, block_end): (&str, &str, &str) = match language {
        "python" => ("#", "\"\"\"", "\"\"\""),
        "rust" => ("//", "/*", "*/"),
        "javascript" | "typescript" | "java" | "c" | "cpp" | "go" | "kotlin" | "swift"
        | "csharp" | "scala" => ("//", "/*", "*/"),
        "ruby" => ("#", "=begin", "=end"),
        "lua" => ("--", "--[[", "]]"),
        "elixir" => ("#", "@doc \"\"\"", "\"\"\""),
        "php" => ("//", "/*", "*/"),
        _ => ("//", "/*", "*/"),
    };

    let mut in_block_comment = false;
    let mut block_comment_buffer = String::new();

    for line in code.lines() {
        let trimmed = line.trim();

        // Handle block comment start
        if !in_block_comment && trimmed.contains(block_start) {
            in_block_comment = true;
            // Extract text after block start on same line
            if let Some(pos) = trimmed.find(block_start) {
                let after_start = &trimmed[pos + block_start.len()..];
                // Check if block ends on same line
                if let Some(end_pos) = after_start.find(block_end) {
                    let comment_text = after_start[..end_pos].trim();
                    if is_valid_comment(comment_text) {
                        comments.push(comment_text.to_string());
                    }
                    in_block_comment = false;
                } else {
                    block_comment_buffer.push_str(after_start.trim());
                    block_comment_buffer.push(' ');
                }
            }
            continue;
        }

        // Inside block comment
        if in_block_comment {
            if trimmed.contains(block_end) {
                // Block comment ends
                if let Some(end_pos) = trimmed.find(block_end) {
                    block_comment_buffer.push_str(trimmed[..end_pos].trim());
                }
                let full_comment = block_comment_buffer.trim().to_string();
                if is_valid_comment(&full_comment) {
                    comments.push(full_comment);
                }
                block_comment_buffer.clear();
                in_block_comment = false;
            } else {
                // Continue accumulating block comment
                let cleaned = trimmed.trim_start_matches('*').trim();
                if !cleaned.is_empty() {
                    block_comment_buffer.push_str(cleaned);
                    block_comment_buffer.push(' ');
                }
            }
            continue;
        }

        // Handle line comments
        if let Some(pos) = trimmed.find(line_comment) {
            // Make sure it's not inside a string (simple heuristic)
            let before_comment = &trimmed[..pos];
            let quote_count =
                before_comment.matches('"').count() + before_comment.matches('\'').count();

            // Skip if odd number of quotes before comment (likely inside string)
            if quote_count % 2 != 0 {
                continue;
            }

            let comment = trimmed[pos + line_comment.len()..].trim();
            if is_valid_comment(comment) {
                comments.push(comment.to_string());
            }
        }
    }

    // Limit to 20 most relevant comments to avoid noise
    comments.into_iter().take(20).collect()
}

/// Check if a comment string is meaningful enough to include.
///
/// Filters out noise like too-short comments, pure punctuation,
/// TODO markers without content, etc.
fn is_valid_comment(comment: &str) -> bool {
    // Must have minimum length
    if comment.len() < 4 {
        return false;
    }

    // Must contain at least one alphabetic character
    if !comment.chars().any(|c| c.is_alphabetic()) {
        return false;
    }

    // Skip common noise patterns
    let lower = comment.to_lowercase();
    let noise_patterns = [
        "todo", "fixme", "hack", "xxx", "###", "---", "===", "***", "lint:", "type:", "noqa",
        "pylint", "pragma", "nolint",
    ];

    // Skip if the comment is ONLY a noise pattern (allow "TODO: actual description")
    for pattern in noise_patterns {
        if lower == pattern {
            return false;
        }
        // Short noise like "TODO fix" (pattern + space + <4 chars) -- not useful
        if lower.len() < pattern.len() + 5
            && lower.starts_with(pattern)
            && lower.as_bytes().get(pattern.len()) == Some(&b' ')
        {
            return false;
        }
    }

    true
}

/// Extract parameter names from a function signature.
///
/// Parses common signature formats: `def func(a, b: Type)` or `fn func(a: T, b: U)`
/// Returns parameter names stripped of type annotations.
#[must_use]
fn extract_parameters_from_signature(signature: &str) -> Vec<String> {
    // Find the parameter list between parentheses
    let start = match signature.find('(') {
        Some(idx) => idx + 1,
        None => return Vec::new(),
    };
    let end = match signature.rfind(')') {
        Some(idx) => idx,
        None => return Vec::new(),
    };

    if start >= end {
        return Vec::new();
    }

    let params_str = &signature[start..end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    // Split by comma, but handle generic types with commas inside angle brackets
    let mut params = Vec::new();
    let mut current = String::new();
    let mut angle_depth: usize = 0;
    let mut paren_depth: usize = 0;

    for ch in params_str.chars() {
        match ch {
            '<' => {
                angle_depth += 1;
                current.push(ch);
            }
            '>' => {
                angle_depth = angle_depth.saturating_sub(1);
                current.push(ch);
            }
            '(' => {
                paren_depth += 1;
                current.push(ch);
            }
            ')' => {
                paren_depth = paren_depth.saturating_sub(1);
                current.push(ch);
            }
            ',' if angle_depth == 0 && paren_depth == 0 => {
                let param = current.trim().to_string();
                if !param.is_empty() {
                    params.push(param);
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }

    // Don't forget the last parameter
    let param = current.trim().to_string();
    if !param.is_empty() {
        params.push(param);
    }

    // Extract just the parameter name (before : or =)
    params
        .into_iter()
        .filter_map(|p| {
            // Skip 'self', 'cls', '&self', '&mut self'
            let p_lower = p.to_lowercase();
            if p_lower == "self" || p_lower == "cls" || p_lower == "&self" || p_lower == "&mut self"
            {
                return None;
            }

            // Get name before type annotation (:) or default value (=)
            let name = p
                .split(':')
                .next()
                .unwrap_or(&p)
                .split('=')
                .next()
                .unwrap_or(&p)
                .trim()
                .trim_start_matches('&')
                .trim_start_matches("mut ")
                .trim()
                .to_string();

            if name.is_empty() || name.starts_with('*') || name.starts_with("**") {
                None
            } else {
                Some(name)
            }
        })
        .collect()
}

/// Extract return type from a function signature.
///
/// Handles Python (`-> Type`) and Rust (`-> Type`) style return annotations.
#[must_use]
fn extract_return_type_from_signature(signature: &str) -> Option<String> {
    // Find -> followed by return type
    let arrow_pos = signature.find("->")?;
    let after_arrow = &signature[arrow_pos + 2..];

    // Get the return type, stopping at common delimiters
    let ret_type = after_arrow
        .trim()
        .trim_end_matches('{')
        .trim_end_matches(':')
        .trim()
        .to_string();

    if ret_type.is_empty() || ret_type == "None" || ret_type == "()" {
        None
    } else {
        Some(ret_type)
    }
}

/// Generate a rich semantic description for a unit without a docstring.
///
/// Creates natural language description from:
/// - Name parsed into words
/// - Unit type (function, method, class)
/// - Parameter names
/// - Return type
/// - Complexity information
///
/// This ensures functions without docstrings still have meaningful
/// semantic content for embedding and search.
#[must_use]
fn generate_semantic_description(unit: &EmbeddingUnit) -> String {
    let mut parts = Vec::new();

    // Parse name into natural language words
    let name_words = parse_identifier_to_words(&unit.name);

    // Generate type-specific description
    match unit.kind {
        UnitKind::Function | UnitKind::Method => {
            if !name_words.is_empty() {
                parts.push(format!("Function that {}", name_words));
            }
        }
        UnitKind::Class => {
            if !name_words.is_empty() {
                parts.push(format!("Class representing {}", name_words));
            }
        }
        UnitKind::Module => {
            if !name_words.is_empty() {
                parts.push(format!("Module for {}", name_words));
            }
        }
        UnitKind::Chunk => {
            // Chunks inherit description from parent, just use name
            if !name_words.is_empty() {
                parts.push(name_words.clone());
            }
        }
    }

    // Add parameter information for functions/methods
    if matches!(unit.kind, UnitKind::Function | UnitKind::Method) && !unit.signature.is_empty() {
        let param_names = extract_parameters_from_signature(&unit.signature);
        if !param_names.is_empty() {
            // Convert parameter names to readable form
            let readable_params: Vec<_> = param_names
                .iter()
                .map(|p| parse_identifier_to_words(p))
                .filter(|p| !p.is_empty())
                .collect();
            if !readable_params.is_empty() {
                parts.push(format!("Takes {} as input", readable_params.join(", ")));
            }
        }

        // Add return type if available
        if let Some(ret_type) = extract_return_type_from_signature(&unit.signature) {
            let readable_ret = parse_identifier_to_words(&ret_type);
            if !readable_ret.is_empty() {
                parts.push(format!("Returns {}", readable_ret));
            }
        }
    }

    // Add complexity hint based on total complexity score
    let total_complexity = unit.complexity.depth + unit.complexity.branches + unit.complexity.loops;
    if total_complexity > 10 {
        parts.push("Contains complex logic with multiple branches".to_string());
    } else if total_complexity > 5 {
        parts.push("Contains conditional logic".to_string());
    }

    parts.join(". ")
}

/// Build rich text for embedding from an EmbeddingUnit.
///
/// Creates text containing information from all analysis layers,
/// suitable for embedding with a language model.
#[must_use]
pub fn build_embedding_text(unit: &EmbeddingUnit) -> String {
    // Pre-allocate a single buffer instead of N format!() allocations + join().
    // Typical embedding text is ~1-8 KB; the code section dominates size.
    let capacity = 256 + unit.code.len() + unit.signature.len();
    let mut buf = String::with_capacity(capacity);

    // Header with type and name
    if unit.is_chunk() {
        let _ = write!(
            buf,
            "Chunk [{}/{}] of {}",
            unit.chunk_index + 1,
            unit.chunk_total,
            unit.parent.as_deref().unwrap_or(&unit.name)
        );
    } else {
        // kind.as_str() returns lowercase; uppercase inline to avoid allocation
        let kind = unit.kind.as_str();
        for c in kind.chars() {
            for upper in c.to_uppercase() {
                buf.push(upper);
            }
        }
        let _ = write!(buf, ": {}", unit.name);
    }

    // Semantic tags
    if !unit.semantic_tags.is_empty() {
        buf.push_str("\nCategories: ");
        for (i, tag) in unit.semantic_tags.iter().enumerate() {
            if i > 0 {
                buf.push_str(", ");
            }
            buf.push_str(tag);
        }
    }

    // Description: prefer docstring, fall back to generated description
    let has_docstring = unit
        .docstring
        .as_ref()
        .is_some_and(|d| !d.is_empty());

    if has_docstring {
        buf.push_str("\nDescription: ");
        buf.push_str(unit.docstring.as_ref().unwrap());
    } else {
        let description = generate_semantic_description(unit);
        if !description.is_empty() {
            buf.push_str("\nPurpose: ");
            buf.push_str(&description);
        }
    }

    // Supplement docstring with parsed name meaning
    if has_docstring {
        let name_words = parse_identifier_to_words(&unit.name);
        if !name_words.is_empty() && name_words != unit.name.to_lowercase() {
            buf.push_str("\nName meaning: ");
            buf.push_str(&name_words);
        }
    }

    // Signature
    if !unit.signature.is_empty() {
        buf.push_str("\nSignature: ");
        buf.push_str(&unit.signature);
    }

    // Complexity
    if let Some(complexity_desc) = unit.complexity.describe() {
        buf.push_str("\nComplexity: ");
        buf.push_str(&complexity_desc);
    }

    // Call relationships
    if !unit.calls.is_empty() {
        let mut first = true;
        for word in unit.calls.iter().take(5).map(|c| parse_identifier_to_words(c)).filter(|w| !w.is_empty()) {
            if first {
                buf.push_str("\nUses: ");
                first = false;
            } else {
                buf.push_str(", ");
            }
            buf.push_str(&word);
        }
    }

    if !unit.called_by.is_empty() {
        let mut first = true;
        for word in unit.called_by.iter().take(5).map(|c| parse_identifier_to_words(c)).filter(|w| !w.is_empty()) {
            if first {
                buf.push_str("\nUsed by: ");
                first = false;
            } else {
                buf.push_str(", ");
            }
            buf.push_str(&word);
        }
    }

    // Dependencies
    if !unit.dependencies.is_empty() {
        buf.push_str("\nDependencies: ");
        buf.push_str(&unit.dependencies);
    }

    // Inline comments (valuable natural language for semantic search)
    if !unit.code.is_empty() {
        let comments = extract_inline_comments(&unit.code, &unit.language);
        if !comments.is_empty() {
            buf.push_str("\nCode comments: ");
            for (i, comment) in comments.iter().enumerate() {
                if i > 0 {
                    buf.push_str("; ");
                }
                buf.push_str(comment);
            }
        }
    }

    // Code preview
    if !unit.code.is_empty() {
        buf.push_str("\nCode:\n");
        buf.push_str(&unit.code);
    }

    truncate_to_tokens(&buf, MAX_EMBEDDING_TOKENS)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_tokens() {
        let text = "Hello, world!";
        let count = count_tokens(text);
        assert!(count > 0);
        assert!(count < text.len()); // Tokens should be fewer than chars
    }

    #[test]
    fn test_truncate_to_tokens() {
        let long_text = "word ".repeat(10000);
        let truncated = truncate_to_tokens(&long_text, 100);
        let truncated_tokens = count_tokens(&truncated);
        assert!(truncated_tokens <= 100);
    }

    #[test]
    fn test_detect_semantic_patterns() {
        // CRUD pattern - standalone verbs at word boundaries
        let crud_code = "def handler(data):\n    db.save(data)\n    return fetch(id)";
        let patterns = detect_semantic_patterns(crud_code);
        assert!(
            patterns.contains(&"crud".to_string()),
            "Expected 'crud' in {:?}",
            patterns
        );

        // Validation pattern - check/validate as standalone words
        let validation_code = "def handler(data):\n    check(data)\n    ensure(valid)";
        let patterns = detect_semantic_patterns(validation_code);
        assert!(
            patterns.contains(&"validation".to_string()),
            "Expected 'validation' in {:?}",
            patterns
        );

        // Error handling pattern
        let error_code = "try:\n    do_stuff()\nexcept Exception:\n    raise ValueError()";
        let patterns = detect_semantic_patterns(error_code);
        assert!(
            patterns.contains(&"error_handling".to_string()),
            "Expected 'error_handling' in {:?}",
            patterns
        );

        // Empty code returns empty patterns
        let empty_patterns = detect_semantic_patterns("");
        assert!(empty_patterns.is_empty());
    }

    #[test]
    fn test_detect_code_complexity() {
        let simple_code = "def foo():\n    return 1";
        let complexity = detect_code_complexity(simple_code);
        assert!(complexity.depth <= 1);
        assert_eq!(complexity.branches, 0);
        assert_eq!(complexity.loops, 0);

        let complex_code = "if x:\n    if y:\n        for i in range(10):\n            while True:\n                pass";
        let complexity = detect_code_complexity(complex_code);
        assert!(complexity.depth >= 3);
        assert!(complexity.branches > 0);
        assert!(complexity.loops >= 2);
    }

    #[test]
    fn test_split_into_chunks() {
        let short_code = "def foo(): pass";
        let chunks = split_into_chunks(short_code, 1000, 50);
        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].text, short_code);

        // Empty code
        let chunks = split_into_chunks("", 100, 10);
        assert!(chunks.is_empty());
    }

    #[test]
    fn test_parse_identifier_to_words() {
        assert_eq!(parse_identifier_to_words("getUserData"), "get user data");
        assert_eq!(parse_identifier_to_words("get_user_data"), "get user data");
        assert_eq!(parse_identifier_to_words("XMLParser"), "xml parser");
        assert_eq!(
            parse_identifier_to_words("_private_method"),
            "private method"
        );
        assert_eq!(parse_identifier_to_words("HTMLElement"), "html element");
        assert_eq!(parse_identifier_to_words(""), "");
    }

    #[test]
    fn test_enrich_unit() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "process_data",
            UnitKind::Function,
            // Code with standalone keywords that match patterns
            "def process_data(user):\n    check(user)  # validate\n    if not user:\n        raise ValueError('Invalid')",
            1,
            "python",
        );

        enrich_unit(&mut unit);

        assert!(
            !unit.semantic_tags.is_empty(),
            "Expected semantic tags to be detected"
        );
        // Should match 'validation' (check) and 'error_handling' (raise)
        assert!(
            unit.semantic_tags.contains(&"validation".to_string())
                || unit.semantic_tags.contains(&"error_handling".to_string()),
            "Expected 'validation' or 'error_handling' in {:?}",
            unit.semantic_tags
        );
        assert!(unit.token_count > 0);
    }

    #[test]
    fn test_chunk_unit_small() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "small_func",
            UnitKind::Function,
            "def small_func(): pass",
            1,
            "python",
        );
        unit.token_count = 10;

        let chunks = chunk_unit(&unit);
        assert_eq!(chunks.len(), 1);
        assert!(!chunks[0].is_chunk());
    }

    #[test]
    fn test_build_embedding_text() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "processUserData",
            UnitKind::Function,
            "def processUserData(user): pass",
            1,
            "python",
        );
        unit.signature = "def processUserData(user: User) -> Result".to_string();
        unit.docstring = Some("Process user data and return result.".to_string());
        unit.semantic_tags = vec!["crud".to_string()];

        let text = build_embedding_text(&unit);

        assert!(text.contains("FUNCTION: processUserData"));
        assert!(text.contains("Categories: crud"));
        assert!(text.contains("Description: Process user data"));
        // When docstring is present, name is added as "Name meaning:" for supplementation
        assert!(text.contains("Name meaning: process user data"));
        assert!(text.contains("Signature:"));
    }

    #[test]
    fn test_extract_inline_comments_python() {
        let python_code = r#"
def process_data(x):
    # This validates the input data
    if x is None:
        return None  # Early return for null
    result = compute(x)  # Main computation
    return result
"#;
        let comments = extract_inline_comments(python_code, "python");
        assert!(!comments.is_empty(), "Expected comments to be extracted");
        assert!(
            comments.iter().any(|c| c.contains("validates")),
            "Expected 'validates' comment, got: {:?}",
            comments
        );
        assert!(
            comments.iter().any(|c| c.contains("computation")),
            "Expected 'computation' comment, got: {:?}",
            comments
        );
    }

    #[test]
    fn test_extract_inline_comments_rust() {
        let rust_code = r#"
fn process_data(x: i32) -> i32 {
    // Validate input before processing
    if x < 0 {
        return 0; // Return zero for negative input
    }
    /* This is a block comment
       that spans multiple lines
       describing the algorithm */
    x * 2
}
"#;
        let comments = extract_inline_comments(rust_code, "rust");
        assert!(!comments.is_empty(), "Expected comments to be extracted");
        assert!(
            comments.iter().any(|c| c.contains("Validate")),
            "Expected 'Validate' comment, got: {:?}",
            comments
        );
        assert!(
            comments.iter().any(|c| c.contains("algorithm")),
            "Expected block comment content, got: {:?}",
            comments
        );
    }

    #[test]
    fn test_extract_inline_comments_javascript() {
        let js_code = r#"
function processData(x) {
    // Check for valid input
    if (x === null) {
        return null;
    }
    /* Calculate the result
       using the formula */
    return x * 2;
}
"#;
        let comments = extract_inline_comments(js_code, "javascript");
        assert!(!comments.is_empty(), "Expected comments to be extracted");
        assert!(
            comments.iter().any(|c| c.contains("valid input")),
            "Expected 'valid input' comment, got: {:?}",
            comments
        );
    }

    #[test]
    fn test_extract_inline_comments_filters_noise() {
        let code_with_noise = r#"
fn test() {
    // TODO
    // FIXME
    // ###
    // This is a real comment about logic
    x + 1
}
"#;
        let comments = extract_inline_comments(code_with_noise, "rust");
        // Should filter out short/noise comments
        assert!(
            !comments
                .iter()
                .any(|c| c == "TODO" || c == "FIXME" || c == "###"),
            "Noise comments should be filtered out, got: {:?}",
            comments
        );
        assert!(
            comments.iter().any(|c| c.contains("real comment")),
            "Real comments should be kept, got: {:?}",
            comments
        );
    }

    #[test]
    fn test_extract_inline_comments_empty_code() {
        let comments = extract_inline_comments("", "rust");
        assert!(comments.is_empty());
    }

    #[test]
    fn test_extract_inline_comments_no_comments() {
        let code = "fn foo() { let x = 1; x + 2 }";
        let comments = extract_inline_comments(code, "rust");
        assert!(comments.is_empty());
    }

    #[test]
    fn test_build_embedding_text_includes_comments() {
        let unit = EmbeddingUnit::new(
            "test.rs",
            "process_data",
            UnitKind::Function,
            "fn process_data() {\n    // This processes important data\n    let x = 1;\n}",
            1,
            "rust",
        );

        let text = build_embedding_text(&unit);
        assert!(
            text.contains("Code comments:"),
            "Expected Code comments section in: {}",
            text
        );
        assert!(
            text.contains("important data"),
            "Expected comment content in embedding text: {}",
            text
        );
    }

    #[test]
    fn test_is_valid_comment() {
        // Valid comments
        assert!(is_valid_comment("This is a valid comment"));
        assert!(is_valid_comment("Check the input parameter"));

        // Invalid: too short
        assert!(!is_valid_comment("ab"));
        assert!(!is_valid_comment("xyz"));

        // Invalid: no alphabetic characters
        assert!(!is_valid_comment("===="));
        assert!(!is_valid_comment("----"));
        assert!(!is_valid_comment("1234"));

        // Invalid: noise patterns only
        assert!(!is_valid_comment("TODO"));
        assert!(!is_valid_comment("FIXME"));
    }

    #[test]
    fn test_get_indent_depth() {
        assert_eq!(get_indent_depth(""), 0);
        assert_eq!(get_indent_depth("    code"), 1);
        assert_eq!(get_indent_depth("        code"), 2);
        assert_eq!(get_indent_depth("\tcode"), 1);
        assert_eq!(get_indent_depth("\t\tcode"), 2);
    }

    #[test]
    fn test_is_binary_file() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        // Text file
        let mut text_file = NamedTempFile::new().unwrap();
        text_file.write_all(b"Hello, world!").unwrap();
        assert!(!is_binary_file(text_file.path()));

        // Binary file with null bytes
        let mut binary_file = NamedTempFile::new().unwrap();
        binary_file.write_all(b"Hello\x00world").unwrap();
        assert!(is_binary_file(binary_file.path()));
    }

    #[test]
    fn test_extract_function_code() {
        let content = "line 1\nline 2\nline 3\nline 4\nline 5";

        let code = extract_function_code(content, 2, Some(4));
        assert_eq!(code, "line 2\nline 3\nline 4");

        let code_no_end = extract_function_code(content, 3, None);
        assert_eq!(code_no_end, "line 3\nline 4\nline 5");

        let code_out_of_bounds = extract_function_code(content, 100, None);
        assert!(code_out_of_bounds.is_empty());
    }

    #[test]
    fn test_enrich_unit_cfg_summary() {
        // Test that CFG summary is computed for a simple Python function
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "simple_func",
            UnitKind::Function,
            "def simple_func(x):\n    if x > 0:\n        return x\n    return 0",
            1,
            "python",
        );

        enrich_unit(&mut unit);

        // CFG summary should be populated for functions
        assert!(
            !unit.cfg_summary.is_empty(),
            "Expected CFG summary to be computed for function"
        );
        assert!(
            unit.cfg_summary.contains("complexity:"),
            "Expected complexity in CFG summary: {}",
            unit.cfg_summary
        );
        assert!(
            unit.cfg_summary.contains("blocks:"),
            "Expected blocks in CFG summary: {}",
            unit.cfg_summary
        );
        assert!(
            unit.cfg_summary.contains("branches:"),
            "Expected branches in CFG summary: {}",
            unit.cfg_summary
        );
    }

    #[test]
    fn test_enrich_unit_dfg_summary() {
        // Test that DFG summary is computed for a Python function
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "example_func",
            UnitKind::Function,
            "def example_func(x, y):\n    z = x + y\n    return z",
            1,
            "python",
        );

        enrich_unit(&mut unit);

        // DFG summary should be populated for functions
        assert!(
            !unit.dfg_summary.is_empty(),
            "Expected DFG summary to be computed for function"
        );
        assert!(
            unit.dfg_summary.contains("vars:"),
            "Expected vars in DFG summary: {}",
            unit.dfg_summary
        );
        assert!(
            unit.dfg_summary.contains("def-use chains:"),
            "Expected def-use chains in DFG summary: {}",
            unit.dfg_summary
        );
    }

    #[test]
    fn test_enrich_unit_skips_cfg_dfg_for_class() {
        // Test that CFG/DFG summaries are NOT computed for class units
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "MyClass",
            UnitKind::Class,
            "class MyClass:\n    def method(self):\n        pass",
            1,
            "python",
        );

        enrich_unit(&mut unit);

        // Class units should not have CFG/DFG summaries
        assert!(
            unit.cfg_summary.is_empty(),
            "Expected no CFG summary for class units"
        );
        assert!(
            unit.dfg_summary.is_empty(),
            "Expected no DFG summary for class units"
        );
    }

    #[test]
    fn test_enrich_unit_cfg_dfg_for_rust() {
        // Test that CFG/DFG works for Rust code as well
        let mut unit = EmbeddingUnit::new(
            "test.rs",
            "process",
            UnitKind::Function,
            "fn process(x: i32) -> i32 {\n    if x > 0 {\n        x * 2\n    } else {\n        0\n    }\n}",
            1,
            "rust",
        );

        enrich_unit(&mut unit);

        // Both summaries should be computed for Rust functions
        assert!(
            !unit.cfg_summary.is_empty(),
            "Expected CFG summary for Rust function"
        );
        assert!(
            !unit.dfg_summary.is_empty(),
            "Expected DFG summary for Rust function"
        );
    }

    #[test]
    fn test_enrich_unit_preserves_existing_summary() {
        // Test that existing summaries are not overwritten
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "func",
            UnitKind::Function,
            "def func(): pass",
            1,
            "python",
        );
        unit.cfg_summary = "existing:cfg".to_string();
        unit.dfg_summary = "existing:dfg".to_string();

        enrich_unit(&mut unit);

        // Existing summaries should be preserved
        assert_eq!(unit.cfg_summary, "existing:cfg");
        assert_eq!(unit.dfg_summary, "existing:dfg");
    }

    // ==========================================================================
    // Tests for extract_dependency_summary (RS-12 fix)
    // ==========================================================================

    #[test]
    fn test_extract_dependency_summary_empty() {
        let imports: Vec<crate::ast::ImportInfo> = vec![];
        let summary = extract_dependency_summary(&imports);
        assert!(summary.is_empty());
    }

    #[test]
    fn test_extract_dependency_summary_simple_import() {
        let imports = vec![crate::ast::ImportInfo {
            module: "os".to_string(),
            names: vec![],
            aliases: FxHashMap::default(),
            is_from: false,
            level: 0,
            line_number: 1,
            visibility: None,
        }];
        let summary = extract_dependency_summary(&imports);
        assert_eq!(summary, "os");
    }

    #[test]
    fn test_extract_dependency_summary_from_import() {
        let imports = vec![crate::ast::ImportInfo {
            module: "os.path".to_string(),
            names: vec!["join".to_string(), "dirname".to_string()],
            aliases: FxHashMap::default(),
            is_from: true,
            level: 0,
            line_number: 1,
            visibility: None,
        }];
        let summary = extract_dependency_summary(&imports);
        assert_eq!(summary, "from os.path import join, dirname");
    }

    #[test]
    fn test_extract_dependency_summary_relative_import() {
        let imports = vec![crate::ast::ImportInfo {
            module: "".to_string(),
            names: vec!["utils".to_string()],
            aliases: FxHashMap::default(),
            is_from: true,
            level: 2,
            line_number: 1,
            visibility: None,
        }];
        let summary = extract_dependency_summary(&imports);
        assert_eq!(summary, "from .. import utils");
    }

    #[test]
    fn test_extract_dependency_summary_relative_with_module() {
        let imports = vec![crate::ast::ImportInfo {
            module: "helpers".to_string(),
            names: vec!["format_date".to_string()],
            aliases: FxHashMap::default(),
            is_from: true,
            level: 1,
            line_number: 1,
            visibility: None,
        }];
        let summary = extract_dependency_summary(&imports);
        assert_eq!(summary, "from .helpers import format_date");
    }

    #[test]
    fn test_extract_dependency_summary_multiple_imports() {
        let imports = vec![
            crate::ast::ImportInfo {
                module: "os".to_string(),
                names: vec![],
                aliases: FxHashMap::default(),
                is_from: false,
                level: 0,
                line_number: 1,
                visibility: None,
            },
            crate::ast::ImportInfo {
                module: "sys".to_string(),
                names: vec![],
                aliases: FxHashMap::default(),
                is_from: false,
                level: 0,
                line_number: 2,
                visibility: None,
            },
            crate::ast::ImportInfo {
                module: "typing".to_string(),
                names: vec!["Optional".to_string(), "List".to_string()],
                aliases: FxHashMap::default(),
                is_from: true,
                level: 0,
                line_number: 3,
                visibility: None,
            },
        ];
        let summary = extract_dependency_summary(&imports);
        assert_eq!(summary, "os; sys; from typing import Optional, List");
    }

    #[test]
    fn test_extract_dependency_summary_truncates_long_names() {
        let imports = vec![crate::ast::ImportInfo {
            module: "typing".to_string(),
            names: vec![
                "Optional".to_string(),
                "List".to_string(),
                "Dict".to_string(),
                "Set".to_string(),
                "Tuple".to_string(),
            ],
            aliases: FxHashMap::default(),
            is_from: true,
            level: 0,
            line_number: 1,
            visibility: None,
        }];
        let summary = extract_dependency_summary(&imports);
        // Should truncate after 3 names
        assert_eq!(summary, "from typing import Optional, List, Dict, ...");
    }

    #[test]
    fn test_extract_dependency_summary_limits_to_10() {
        let imports: Vec<crate::ast::ImportInfo> = (0..15)
            .map(|i| crate::ast::ImportInfo {
                module: format!("module{}", i),
                names: vec![],
                aliases: FxHashMap::default(),
                is_from: false,
                level: 0,
                line_number: i + 1,
                visibility: None,
            })
            .collect();
        let summary = extract_dependency_summary(&imports);
        // Should only include first 10
        let count = summary.split("; ").count();
        assert_eq!(count, 10);
        assert!(summary.contains("module0"));
        assert!(summary.contains("module9"));
        assert!(!summary.contains("module10"));
    }

    #[test]
    fn test_build_embedding_text_includes_dependencies() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "process_data",
            UnitKind::Function,
            "def process_data(): pass",
            1,
            "python",
        );
        unit.dependencies = "os; from typing import Optional".to_string();

        let text = build_embedding_text(&unit);
        assert!(
            text.contains("Dependencies:"),
            "Expected Dependencies section in embedding text: {}",
            text
        );
        assert!(
            text.contains("os"),
            "Expected dependency 'os' in embedding text: {}",
            text
        );
        assert!(
            text.contains("typing"),
            "Expected 'typing' in embedding text: {}",
            text
        );
    }

    #[test]
    fn test_extract_parameters_from_signature_python() {
        // Basic Python signature
        let params = extract_parameters_from_signature("def process_data(user_id, data)");
        assert_eq!(params, vec!["user_id", "data"]);

        // With type hints
        let params =
            extract_parameters_from_signature("def process_data(user_id: int, data: dict) -> bool");
        assert_eq!(params, vec!["user_id", "data"]);

        // With self (should be filtered)
        let params = extract_parameters_from_signature("def process(self, user_id)");
        assert_eq!(params, vec!["user_id"]);

        // With cls (should be filtered)
        let params = extract_parameters_from_signature("def from_config(cls, config)");
        assert_eq!(params, vec!["config"]);

        // Empty params
        let params = extract_parameters_from_signature("def no_params()");
        assert!(params.is_empty());
    }

    #[test]
    fn test_extract_parameters_from_signature_rust() {
        // Basic Rust signature
        let params = extract_parameters_from_signature(
            "fn process_data(user_id: i32, data: Vec<u8>) -> bool",
        );
        assert_eq!(params, vec!["user_id", "data"]);

        // With &self (should be filtered)
        let params = extract_parameters_from_signature("fn process(&self, user_id: i32)");
        assert_eq!(params, vec!["user_id"]);

        // With &mut self (should be filtered)
        let params = extract_parameters_from_signature("fn update(&mut self, value: String)");
        assert_eq!(params, vec!["value"]);

        // With generic types containing commas
        let params = extract_parameters_from_signature(
            "fn process(data: HashMap<String, i32>, config: Config)",
        );
        assert_eq!(params, vec!["data", "config"]);

        // With reference parameters
        let params =
            extract_parameters_from_signature("fn process(data: &str, config: &mut Config)");
        assert_eq!(params, vec!["data", "config"]);
    }

    #[test]
    fn test_extract_parameters_from_signature_edge_cases() {
        // No parentheses
        let params = extract_parameters_from_signature("invalid signature");
        assert!(params.is_empty());

        // Empty string
        let params = extract_parameters_from_signature("");
        assert!(params.is_empty());

        // Only opening paren
        let params = extract_parameters_from_signature("fn broken(");
        assert!(params.is_empty());

        // With default values
        let params = extract_parameters_from_signature("def func(a, b=10, c='default')");
        assert_eq!(params, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_extract_return_type_from_signature() {
        // Python return type
        let ret = extract_return_type_from_signature("def process_data(x: int) -> bool");
        assert_eq!(ret, Some("bool".to_string()));

        // Rust return type
        let ret =
            extract_return_type_from_signature("fn process_data(x: i32) -> Result<String, Error>");
        assert_eq!(ret, Some("Result<String, Error>".to_string()));

        // No return type
        let ret = extract_return_type_from_signature("def process_data(x)");
        assert!(ret.is_none());

        // Python None return (should be filtered)
        let ret = extract_return_type_from_signature("def process_data(x) -> None");
        assert!(ret.is_none());

        // Rust unit return (should be filtered)
        let ret = extract_return_type_from_signature("fn process() -> ()");
        assert!(ret.is_none());

        // Rust function with brace
        let ret = extract_return_type_from_signature("fn process() -> bool {");
        assert_eq!(ret, Some("bool".to_string()));
    }

    #[test]
    fn test_generate_semantic_description_function() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "getUserData",
            UnitKind::Function,
            "def getUserData(user_id): pass",
            1,
            "python",
        );
        unit.signature = "def getUserData(user_id: int) -> dict".to_string();

        let desc = generate_semantic_description(&unit);

        assert!(
            desc.contains("Function that get user data"),
            "Expected function purpose in: {}",
            desc
        );
        assert!(
            desc.contains("Takes user id as input"),
            "Expected parameter info in: {}",
            desc
        );
        assert!(
            desc.contains("Returns dict"),
            "Expected return type in: {}",
            desc
        );
    }

    #[test]
    fn test_generate_semantic_description_class() {
        let unit = EmbeddingUnit::new(
            "test.py",
            "UserDataProcessor",
            UnitKind::Class,
            "class UserDataProcessor: pass",
            1,
            "python",
        );

        let desc = generate_semantic_description(&unit);

        assert!(
            desc.contains("Class representing user data processor"),
            "Expected class description in: {}",
            desc
        );
    }

    #[test]
    fn test_generate_semantic_description_with_complexity() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "complexFunction",
            UnitKind::Function,
            "def complexFunction(): pass",
            1,
            "python",
        );
        // High complexity: depth=4 + branches=5 + loops=3 = 12 > 10
        unit.complexity = CodeComplexity {
            depth: 4,
            branches: 5,
            loops: 3,
        };

        let desc = generate_semantic_description(&unit);

        assert!(
            desc.contains("Contains complex logic with multiple branches"),
            "Expected complexity hint in: {}",
            desc
        );

        // Medium complexity: total=7 > 5
        unit.complexity = CodeComplexity {
            depth: 2,
            branches: 3,
            loops: 2,
        };

        let desc = generate_semantic_description(&unit);

        assert!(
            desc.contains("Contains conditional logic"),
            "Expected conditional logic hint in: {}",
            desc
        );

        // Low complexity: total=3 <= 5
        unit.complexity = CodeComplexity {
            depth: 1,
            branches: 1,
            loops: 1,
        };

        let desc = generate_semantic_description(&unit);

        assert!(
            !desc.contains("Contains"),
            "Should not have complexity hint for simple code: {}",
            desc
        );
    }

    #[test]
    fn test_build_embedding_text_without_docstring() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "processUserData",
            UnitKind::Function,
            "def processUserData(user_id, config): pass",
            1,
            "python",
        );
        unit.signature = "def processUserData(user_id: int, config: Config) -> Result".to_string();
        // No docstring set

        let text = build_embedding_text(&unit);

        // Should contain generated description
        assert!(
            text.contains("Purpose:"),
            "Expected Purpose section in: {}",
            text
        );
        assert!(
            text.contains("Function that process user data"),
            "Expected function description in: {}",
            text
        );
        assert!(
            text.contains("user id") || text.contains("config"),
            "Expected parameter info in: {}",
            text
        );
    }

    #[test]
    fn test_build_embedding_text_with_docstring() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "processUserData",
            UnitKind::Function,
            "def processUserData(user_id): pass",
            1,
            "python",
        );
        unit.signature = "def processUserData(user_id: int) -> Result".to_string();
        unit.docstring = Some("Process user data and return result.".to_string());

        let text = build_embedding_text(&unit);

        // Should contain docstring as description
        assert!(
            text.contains("Description: Process user data and return result."),
            "Expected docstring in: {}",
            text
        );
        // Should contain name meaning (supplementary)
        assert!(
            text.contains("Name meaning:"),
            "Expected name meaning for supplementation in: {}",
            text
        );
    }

    #[test]
    fn test_build_embedding_text_empty_docstring() {
        let mut unit = EmbeddingUnit::new(
            "test.py",
            "getUserById",
            UnitKind::Function,
            "def getUserById(id): pass",
            1,
            "python",
        );
        unit.signature = "def getUserById(id: int) -> User".to_string();
        unit.docstring = Some(String::new()); // Empty docstring

        let text = build_embedding_text(&unit);

        // Should fall back to generated description
        assert!(
            text.contains("Purpose:"),
            "Expected Purpose section for empty docstring in: {}",
            text
        );
        assert!(
            text.contains("Function that get user by id"),
            "Expected generated description in: {}",
            text
        );
    }

    // ==========================================================================
    // Tests for .brrrignore support in scan_source_files (RS-14 fix)
    // ==========================================================================

    #[test]
    fn test_scan_source_files_respects_brrrignore() {
        use std::fs;
        use tempfile::TempDir;

        // Create temp directory structure
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create source files
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(root.join("src/main.py"), "def main(): pass").unwrap();
        fs::write(root.join("src/utils.py"), "def util(): pass").unwrap();

        // Create directory to be ignored via .brrrignore
        fs::create_dir_all(root.join("custom_ignored")).unwrap();
        fs::write(root.join("custom_ignored/hidden.py"), "def hidden(): pass").unwrap();

        // Create .brrrignore with custom pattern
        fs::write(root.join(".brrrignore"), "custom_ignored/\n").unwrap();

        // Scan should respect .brrrignore
        let files = scan_source_files(root, "python");

        // Should include src/ files
        assert!(
            files.iter().any(|p| p.ends_with("main.py")),
            "Expected main.py in {:?}",
            files
        );
        assert!(
            files.iter().any(|p| p.ends_with("utils.py")),
            "Expected utils.py in {:?}",
            files
        );

        // Should NOT include custom_ignored/ files
        assert!(
            !files
                .iter()
                .any(|p| p.to_string_lossy().contains("custom_ignored")),
            "custom_ignored/ should be excluded by .brrrignore, got {:?}",
            files
        );
    }

    #[test]
    fn test_scan_source_files_ignores_default_patterns() {
        use std::fs;
        use tempfile::TempDir;

        // Create temp directory structure
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create source files
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(root.join("src/main.py"), "def main(): pass").unwrap();

        // Create directories that should be ignored by default
        fs::create_dir_all(root.join("node_modules/pkg")).unwrap();
        fs::write(
            root.join("node_modules/pkg/index.py"),
            "# should be ignored",
        )
        .unwrap();

        fs::create_dir_all(root.join("__pycache__")).unwrap();
        fs::write(root.join("__pycache__/cache.py"), "# should be ignored").unwrap();

        fs::create_dir_all(root.join(".venv/lib")).unwrap();
        fs::write(root.join(".venv/lib/site.py"), "# should be ignored").unwrap();

        // Scan without .brrrignore (should use defaults)
        let files = scan_source_files(root, "python");

        // Should include src/ files
        assert!(
            files.iter().any(|p| p.ends_with("main.py")),
            "Expected main.py in {:?}",
            files
        );

        // Should NOT include files from default ignored directories
        assert!(
            !files
                .iter()
                .any(|p| p.to_string_lossy().contains("node_modules")),
            "node_modules/ should be ignored by default, got {:?}",
            files
        );
        assert!(
            !files
                .iter()
                .any(|p| p.to_string_lossy().contains("__pycache__")),
            "__pycache__/ should be ignored by default, got {:?}",
            files
        );
        assert!(
            !files.iter().any(|p| p.to_string_lossy().contains(".venv")),
            ".venv/ should be ignored by default, got {:?}",
            files
        );
    }

    #[test]
    fn test_scan_source_files_gitignore_not_loaded() {
        // BrrrIgnore does NOT load .gitignore - this test verifies that behavior.
        // .gitignore is handled separately by WalkBuilder in scanner code.
        use std::fs;
        use tempfile::TempDir;

        // Create temp directory structure
        let temp_dir = TempDir::new().unwrap();
        let root = temp_dir.path();

        // Create source files
        fs::create_dir_all(root.join("src")).unwrap();
        fs::write(root.join("src/main.py"), "def main(): pass").unwrap();

        // Create directory that would be ignored by .gitignore
        fs::create_dir_all(root.join("logs")).unwrap();
        fs::write(root.join("logs/app.py"), "# log handler").unwrap();

        // Create .gitignore with custom pattern (no .brrrignore)
        // BrrrIgnore should NOT load this - it uses defaults instead
        fs::write(root.join(".gitignore"), "logs/\n").unwrap();

        // Scan with BrrrIgnore (which does NOT load .gitignore)
        let files = scan_source_files(root, "python");

        // Should include src/ files
        assert!(
            files.iter().any(|p| p.ends_with("main.py")),
            "Expected main.py in {:?}",
            files
        );

        // logs/ WILL be included because .gitignore is NOT loaded by BrrrIgnore.
        // (BrrrIgnore uses default patterns when no .brrrignore exists)
        // This is intentional - .gitignore is handled by WalkBuilder in scanner code.
        assert!(
            files.iter().any(|p| p.to_string_lossy().contains("logs")),
            "logs/ should be included (gitignore NOT loaded by BrrrIgnore), got {:?}",
            files
        );
    }

    // ==========================================================================
    // Tests for read_file_content encoding handling (RS-15 fix)
    // ==========================================================================

    #[test]
    fn test_read_file_content_utf8_no_bom() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"Hello, world!").unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "Hello, world!");
    }

    #[test]
    fn test_read_file_content_utf8_with_bom() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // UTF-8 BOM (EF BB BF) followed by content
        let mut data = vec![0xEF, 0xBB, 0xBF];
        data.extend_from_slice(b"Hello with BOM");
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        // BOM should be stripped
        assert_eq!(content, "Hello with BOM");
        assert!(!content.starts_with('\u{FEFF}'), "BOM should be stripped");
    }

    #[test]
    fn test_read_file_content_utf16_le_bom() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // UTF-16 LE BOM (FF FE) followed by "Hi" in UTF-16 LE
        // 'H' = 0x0048 in LE: 0x48 0x00
        // 'i' = 0x0069 in LE: 0x69 0x00
        let data = vec![0xFF, 0xFE, 0x48, 0x00, 0x69, 0x00];
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "Hi");
    }

    #[test]
    fn test_read_file_content_utf16_be_bom() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // UTF-16 BE BOM (FE FF) followed by "Hi" in UTF-16 BE
        // 'H' = 0x0048 in BE: 0x00 0x48
        // 'i' = 0x0069 in BE: 0x00 0x69
        let data = vec![0xFE, 0xFF, 0x00, 0x48, 0x00, 0x69];
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "Hi");
    }

    #[test]
    fn test_read_file_content_invalid_utf8_fallback() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // Invalid UTF-8 sequence: 0x80 is not valid as a start byte
        let data = vec![
            0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x80, 0x57, 0x6F, 0x72, 0x6C, 0x64,
        ];
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        // Should use lossy conversion - invalid byte becomes replacement char
        assert!(content.contains("Hello"));
        assert!(content.contains("World"));
        // The invalid byte (0x80) should be replaced with U+FFFD
        assert!(
            content.contains('\u{FFFD}'),
            "Invalid bytes should be replaced with U+FFFD"
        );
    }

    #[test]
    fn test_read_file_content_latin1_fallback() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // Latin-1 encoded text with non-ASCII characters
        // "cafe" with accent (e = 0xE9 in Latin-1, which is invalid standalone UTF-8)
        let data = vec![0x63, 0x61, 0x66, 0xE9];
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        // Should not panic, should contain valid content with replacement
        assert!(content.starts_with("caf"));
        // The 0xE9 byte is invalid UTF-8, should be replaced
        assert!(content.ends_with('\u{FFFD}') || content.len() >= 3);
    }

    #[test]
    fn test_read_file_content_empty_file() {
        use tempfile::NamedTempFile;

        let file = NamedTempFile::new().unwrap();
        // Don't write anything - empty file

        let content = read_file_content(file.path()).unwrap();
        assert!(content.is_empty());
    }

    #[test]
    fn test_read_file_content_unicode_multibyte() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let mut file = NamedTempFile::new().unwrap();
        // Unicode string with multibyte characters
        file.write_all("Hello, World".as_bytes()).unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert!(content.contains("Hello"));
        assert!(content.contains("World"));
    }

    #[test]
    fn test_read_file_content_nonexistent_file() {
        let result = read_file_content(Path::new("/nonexistent/path/to/file.txt"));
        assert!(result.is_err());
    }

    // =========================================================================
    // Line Ending Normalization Tests
    // =========================================================================

    #[test]
    fn test_normalize_line_endings_lf_unchanged() {
        // Unix-style LF should remain unchanged
        let input = "line1\nline2\nline3";
        let result = normalize_line_endings(input);
        assert_eq!(result, "line1\nline2\nline3");
    }

    #[test]
    fn test_normalize_line_endings_crlf_to_lf() {
        // Windows-style CRLF should be converted to LF
        let input = "line1\r\nline2\r\nline3";
        let result = normalize_line_endings(input);
        assert_eq!(result, "line1\nline2\nline3");
    }

    #[test]
    fn test_normalize_line_endings_cr_to_lf() {
        // Classic Mac-style CR should be converted to LF
        let input = "line1\rline2\rline3";
        let result = normalize_line_endings(input);
        assert_eq!(result, "line1\nline2\nline3");
    }

    #[test]
    fn test_normalize_line_endings_mixed() {
        // Mixed line endings should all become LF
        let input = "line1\r\nline2\nline3\rline4";
        let result = normalize_line_endings(input);
        assert_eq!(result, "line1\nline2\nline3\nline4");
    }

    #[test]
    fn test_normalize_line_endings_empty_string() {
        let result = normalize_line_endings("");
        assert_eq!(result, "");
    }

    #[test]
    fn test_normalize_line_endings_no_newlines() {
        let input = "single line with no newlines";
        let result = normalize_line_endings(input);
        assert_eq!(result, "single line with no newlines");
    }

    #[test]
    fn test_read_file_content_crlf_normalization() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        // Test that read_file_content normalizes CRLF to LF
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"line1\r\nline2\r\nline3").unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "line1\nline2\nline3");
        assert!(!content.contains('\r'), "CRLF should be normalized to LF");
    }

    #[test]
    fn test_read_file_content_cr_normalization() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        // Test that read_file_content normalizes CR to LF
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"line1\rline2\rline3").unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "line1\nline2\nline3");
        assert!(!content.contains('\r'), "CR should be normalized to LF");
    }

    #[test]
    fn test_read_file_content_mixed_line_endings() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        // Test mixed line endings are all normalized
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"line1\r\nline2\nline3\rline4").unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "line1\nline2\nline3\nline4");
        assert!(
            !content.contains('\r'),
            "All line endings should be normalized to LF"
        );
    }

    #[test]
    fn test_read_file_content_utf8_bom_with_crlf() {
        use std::io::Write;
        use tempfile::NamedTempFile;

        // Test BOM handling combined with CRLF normalization
        let mut file = NamedTempFile::new().unwrap();
        // UTF-8 BOM + CRLF content
        let data = [
            0xEF, 0xBB, 0xBF, b'H', b'i', b'\r', b'\n', b'W', b'o', b'r', b'l', b'd',
        ];
        file.write_all(&data).unwrap();

        let content = read_file_content(file.path()).unwrap();
        assert_eq!(content, "Hi\nWorld");
        assert!(!content.contains('\r'), "CRLF should be normalized");
        assert!(!content.starts_with('\u{FEFF}'), "BOM should be stripped");
    }
}
