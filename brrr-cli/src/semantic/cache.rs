//! File-hash cache for incremental semantic indexing.
//!
//! Avoids reprocessing unchanged files on `brrr semantic index` re-runs.
//! Uses a two-level invalidation strategy:
//!
//! 1. **Fast path**: mtime + size unchanged => skip (covers 99.9% of cases)
//! 2. **Slow path**: mtime changed but size same => recompute xxh3 content hash
//!
//! The cache is stored as `.brrr_index/file_hashes.json` alongside the vector
//! index and metadata.

use std::fs;
use std::path::Path;
use std::time::UNIX_EPOCH;

use xxhash_rust::xxh3::xxh3_64;

use super::types::{FileHashEntry, HashCache};

/// Cache file name within the `.brrr_index/` directory.
const CACHE_FILENAME: &str = "file_hashes.json";

/// Load the file-hash cache from disk.
///
/// Returns `None` if the cache file doesn't exist, is corrupt, or has an
/// incompatible version/model. Callers should treat `None` as "full re-index
/// required".
///
/// # Arguments
///
/// * `index_dir` - Path to `.brrr_index/` directory
/// * `model` - Current embedding model name for compatibility check
pub fn load_cache(index_dir: &Path, model: &str) -> Option<HashCache> {
    let cache_path = index_dir.join(CACHE_FILENAME);

    let data = fs::read_to_string(&cache_path).ok()?;
    let cache: HashCache = serde_json::from_str(&data).ok()?;

    if !cache.is_compatible(model) {
        tracing::info!(
            "Cache model mismatch (cached={}, current={}), forcing full re-index",
            cache.model,
            model
        );
        return None;
    }

    tracing::debug!(
        "Loaded file hash cache with {} entries",
        cache.entries.len()
    );
    Some(cache)
}

/// Save the file-hash cache to disk.
///
/// Writes atomically by first writing to a temporary file then renaming,
/// so a crash mid-write never leaves a corrupt cache.
///
/// # Errors
///
/// Returns `Err` if the index directory doesn't exist or isn't writable.
pub fn save_cache(index_dir: &Path, cache: &HashCache) -> std::io::Result<()> {
    let cache_path = index_dir.join(CACHE_FILENAME);
    let tmp_path = index_dir.join(".file_hashes.json.tmp");

    let data = serde_json::to_string_pretty(cache).map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::Other, format!("JSON serialize: {}", e))
    })?;

    fs::write(&tmp_path, data)?;
    fs::rename(&tmp_path, &cache_path)?;

    tracing::debug!(
        "Saved file hash cache with {} entries",
        cache.entries.len()
    );
    Ok(())
}

/// Compute the xxh3 content hash of a file.
///
/// Uses xxh3-64 which is SIMD-accelerated and ~10x faster than SHA-256.
/// Reads the entire file into memory (source files are typically <1MB,
/// so this is fine for our use case).
///
/// Returns the hash as `"xxh3:<16-char-hex>"`.
///
/// # Errors
///
/// Returns `Err` on I/O failure (file not found, permission denied, etc.).
pub fn compute_file_hash(path: &Path) -> std::io::Result<String> {
    let bytes = fs::read(path)?;
    let hash = xxh3_64(&bytes);
    Ok(format!("xxh3:{:016x}", hash))
}

/// Get mtime (as nanoseconds since UNIX epoch) and size for a file.
///
/// Returns `None` if metadata can't be read (file deleted, permission denied).
pub fn file_mtime_and_size(path: &Path) -> Option<(u128, u64)> {
    let meta = fs::metadata(path).ok()?;
    let mtime = meta
        .modified()
        .ok()?
        .duration_since(UNIX_EPOCH)
        .ok()?
        .as_nanos();
    Some((mtime, meta.len()))
}

/// Check whether a file is unchanged relative to its cache entry.
///
/// Uses a two-level strategy:
/// 1. If mtime AND size match => unchanged (fast path)
/// 2. If size matches but mtime differs => compute content hash (slow path)
/// 3. If size differs => definitely changed
///
/// Returns `true` if the file can be skipped (unchanged).
pub fn is_file_unchanged(path: &Path, entry: &FileHashEntry) -> bool {
    let (mtime_ns, size) = match file_mtime_and_size(path) {
        Some(v) => v,
        None => return false, // Can't stat => treat as changed
    };

    // Fast path: mtime + size both match
    if mtime_ns == entry.mtime_ns && size == entry.size {
        return true;
    }

    // Size changed => definitely modified
    if size != entry.size {
        return false;
    }

    // Slow path: size same but mtime different (e.g., `touch`, or copied file).
    // Recompute content hash to be sure.
    match compute_file_hash(path) {
        Ok(hash) => hash == entry.content_hash,
        Err(_) => false,
    }
}

/// Determine which files need reprocessing given the current file list and cache.
///
/// Returns a struct with:
/// - `changed`: files that need extraction + embedding (new or modified)
/// - `unchanged`: files whose cached units can be reused
/// - `deleted`: cache entries for files that no longer exist
///
/// # Arguments
///
/// * `all_files` - Every source file discovered by the scanner (absolute paths)
/// * `project_root` - Project root for computing relative paths
/// * `cache` - Previous cache (or `None` for first run)
pub fn classify_files(
    all_files: &[std::path::PathBuf],
    project_root: &Path,
    cache: Option<&HashCache>,
) -> FileClassification {
    let cache = match cache {
        Some(c) => c,
        None => {
            // No cache: everything is new
            return FileClassification {
                changed: all_files.to_vec(),
                unchanged: Vec::new(),
                deleted_keys: Vec::new(),
            };
        }
    };

    let mut changed = Vec::new();
    let mut unchanged = Vec::new();
    let mut seen_keys = std::collections::HashSet::new();

    for file in all_files {
        let rel = file
            .strip_prefix(project_root)
            .unwrap_or(file)
            .to_string_lossy()
            .to_string();

        seen_keys.insert(rel.clone());

        match cache.entries.get(&rel) {
            Some(entry) if is_file_unchanged(file, entry) => {
                unchanged.push((file.clone(), rel));
            }
            _ => {
                changed.push(file.clone());
            }
        }
    }

    // Find deleted files (in cache but not on disk)
    let deleted_keys: Vec<String> = cache
        .entries
        .keys()
        .filter(|k| !seen_keys.contains(*k))
        .cloned()
        .collect();

    FileClassification {
        changed,
        unchanged,
        deleted_keys,
    }
}

/// Result of classifying files against the cache.
pub struct FileClassification {
    /// Files that need fresh extraction and embedding (new or modified).
    pub changed: Vec<std::path::PathBuf>,
    /// Files whose cached units can be reused: (absolute_path, relative_key).
    pub unchanged: Vec<(std::path::PathBuf, String)>,
    /// Cache keys for files that were deleted from disk.
    pub deleted_keys: Vec<String>,
}

/// Build a new `FileHashEntry` for a file that was just processed.
///
/// # Arguments
///
/// * `path` - Absolute path to the source file
/// * `unit_count` - Number of units extracted from this file
/// * `unit_ids` - Global indices of this file's units in the combined array
pub fn build_entry(
    path: &Path,
    unit_count: usize,
    unit_ids: Vec<usize>,
) -> std::io::Result<FileHashEntry> {
    let (mtime_ns, size) = file_mtime_and_size(path)
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::NotFound, "cannot stat file"))?;

    let content_hash = compute_file_hash(path)?;

    Ok(FileHashEntry {
        content_hash,
        mtime_ns,
        size,
        unit_count,
        unit_ids,
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_compute_file_hash_deterministic() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");
        fs::write(&file, b"def hello(): pass").unwrap();

        let h1 = compute_file_hash(&file).unwrap();
        let h2 = compute_file_hash(&file).unwrap();
        assert_eq!(h1, h2);
        assert!(h1.starts_with("xxh3:"));
    }

    #[test]
    fn test_compute_file_hash_changes_on_content() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");

        fs::write(&file, b"version 1").unwrap();
        let h1 = compute_file_hash(&file).unwrap();

        fs::write(&file, b"version 2").unwrap();
        let h2 = compute_file_hash(&file).unwrap();

        assert_ne!(h1, h2);
    }

    #[test]
    fn test_is_file_unchanged_fast_path() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");
        fs::write(&file, b"content").unwrap();

        let (mtime_ns, size) = file_mtime_and_size(&file).unwrap();
        let hash = compute_file_hash(&file).unwrap();

        let entry = FileHashEntry {
            content_hash: hash,
            mtime_ns,
            size,
            unit_count: 1,
            unit_ids: vec![0],
        };

        // Same file, nothing changed => unchanged
        assert!(is_file_unchanged(&file, &entry));
    }

    #[test]
    fn test_is_file_unchanged_content_modified() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");
        fs::write(&file, b"original").unwrap();

        let (mtime_ns, size) = file_mtime_and_size(&file).unwrap();
        let hash = compute_file_hash(&file).unwrap();

        let entry = FileHashEntry {
            content_hash: hash,
            mtime_ns,
            size,
            unit_count: 1,
            unit_ids: vec![0],
        };

        // Modify content with different size
        fs::write(&file, b"modified content that is longer").unwrap();
        assert!(!is_file_unchanged(&file, &entry));
    }

    #[test]
    fn test_is_file_unchanged_slow_path_same_content() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");
        fs::write(&file, b"content").unwrap();

        let hash = compute_file_hash(&file).unwrap();
        let size = fs::metadata(&file).unwrap().len();

        // Create entry with a different mtime but same hash and size
        let entry = FileHashEntry {
            content_hash: hash,
            mtime_ns: 0, // Wrong mtime forces slow path
            size,
            unit_count: 1,
            unit_ids: vec![0],
        };

        // Should detect as unchanged via hash comparison
        assert!(is_file_unchanged(&file, &entry));
    }

    #[test]
    fn test_is_file_unchanged_deleted_file() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("deleted.py");

        let entry = FileHashEntry {
            content_hash: "xxh3:0000000000000000".to_string(),
            mtime_ns: 0,
            size: 100,
            unit_count: 1,
            unit_ids: vec![0],
        };

        // File doesn't exist => treat as changed
        assert!(!is_file_unchanged(&file, &entry));
    }

    #[test]
    fn test_cache_roundtrip() {
        let dir = TempDir::new().unwrap();

        let mut cache = HashCache::new("bge-large-en-v1.5");
        cache.entries.insert(
            "src/main.py".to_string(),
            FileHashEntry {
                content_hash: "xxh3:abcdef0123456789".to_string(),
                mtime_ns: 1234567890,
                size: 4096,
                unit_count: 5,
                unit_ids: vec![0, 1, 2, 3, 4],
            },
        );

        save_cache(dir.path(), &cache).unwrap();
        let loaded = load_cache(dir.path(), "bge-large-en-v1.5").unwrap();

        assert_eq!(loaded.version, "1.0");
        assert_eq!(loaded.model, "bge-large-en-v1.5");
        assert_eq!(loaded.entries.len(), 1);
        assert_eq!(
            loaded.entries["src/main.py"].content_hash,
            "xxh3:abcdef0123456789"
        );
    }

    #[test]
    fn test_cache_model_mismatch() {
        let dir = TempDir::new().unwrap();

        let cache = HashCache::new("model-a");
        save_cache(dir.path(), &cache).unwrap();

        // Loading with different model returns None
        assert!(load_cache(dir.path(), "model-b").is_none());
    }

    #[test]
    fn test_classify_files_no_cache() {
        let dir = TempDir::new().unwrap();
        let f1 = dir.path().join("a.py");
        let f2 = dir.path().join("b.py");
        fs::write(&f1, b"a").unwrap();
        fs::write(&f2, b"b").unwrap();

        let files = vec![f1, f2];
        let result = classify_files(&files, dir.path(), None);

        assert_eq!(result.changed.len(), 2);
        assert!(result.unchanged.is_empty());
        assert!(result.deleted_keys.is_empty());
    }

    #[test]
    fn test_classify_files_with_cache() {
        let dir = TempDir::new().unwrap();
        let f1 = dir.path().join("unchanged.py");
        let f2 = dir.path().join("new.py");
        fs::write(&f1, b"stable content").unwrap();
        fs::write(&f2, b"new file").unwrap();

        let (mtime, size) = file_mtime_and_size(&f1).unwrap();
        let hash = compute_file_hash(&f1).unwrap();

        let mut cache = HashCache::new("test-model");
        cache.entries.insert(
            "unchanged.py".to_string(),
            FileHashEntry {
                content_hash: hash,
                mtime_ns: mtime,
                size,
                unit_count: 2,
                unit_ids: vec![0, 1],
            },
        );
        // Old file that was deleted
        cache.entries.insert(
            "deleted.py".to_string(),
            FileHashEntry {
                content_hash: "xxh3:0".to_string(),
                mtime_ns: 0,
                size: 0,
                unit_count: 1,
                unit_ids: vec![2],
            },
        );

        let files = vec![f1, f2];
        let result = classify_files(&files, dir.path(), Some(&cache));

        assert_eq!(result.changed.len(), 1); // new.py
        assert_eq!(result.unchanged.len(), 1); // unchanged.py
        assert_eq!(result.deleted_keys.len(), 1); // deleted.py
        assert_eq!(result.deleted_keys[0], "deleted.py");
    }

    #[test]
    fn test_build_entry() {
        let dir = TempDir::new().unwrap();
        let file = dir.path().join("test.py");
        fs::write(&file, b"def foo(): pass").unwrap();

        let entry = build_entry(&file, 3, vec![10, 11, 12]).unwrap();

        assert!(entry.content_hash.starts_with("xxh3:"));
        assert_eq!(entry.size, 15); // len("def foo(): pass")
        assert_eq!(entry.unit_count, 3);
        assert_eq!(entry.unit_ids, vec![10, 11, 12]);
        assert!(entry.mtime_ns > 0);
    }
}
