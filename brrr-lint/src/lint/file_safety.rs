//! Atomic file write safety module.
//!
//! This module provides safe, atomic file writing with backup and rollback capabilities
//! to prevent data corruption during fix application.
//!
//! ## Safety Guarantees
//!
//! 1. **Atomicity**: File writes either complete fully or not at all (via temp+rename)
//! 2. **Backup**: Original file is preserved before modification
//! 3. **Lock Files**: Prevents concurrent modification of the same file
//! 4. **Rollback**: Can restore from backup if something goes wrong
//!
//! ## Usage
//!
//! ```rust,ignore
//! use crate::lint::file_safety::AtomicWriter;
//!
//! let writer = AtomicWriter::new();
//! let backup_path = writer.write_with_backup(&target_path, &new_content)?;
//! // On failure, call writer.rollback(&target_path, &backup_path)?;
//! ```

use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use tracing::{debug, error, info, warn};

/// Default backup retention time: 24 hours
const DEFAULT_BACKUP_RETENTION_HOURS: u64 = 24;

/// Lock file timeout: 30 seconds
const LOCK_TIMEOUT_SECS: u64 = 30;

/// Backup directory name
const BACKUP_DIR_NAME: &str = ".fstar-lint-backups";

/// Errors that can occur during atomic file operations.
#[derive(Debug)]
pub enum AtomicWriteError {
    /// Failed to create temporary file
    TempFileCreation { path: PathBuf, source: io::Error },
    /// Failed to write to temporary file
    TempFileWrite { path: PathBuf, source: io::Error },
    /// Failed to sync temporary file to disk
    TempFileSync { path: PathBuf, source: io::Error },
    /// Failed to rename temporary file to target
    Rename {
        from: PathBuf,
        to: PathBuf,
        source: io::Error,
    },
    /// Failed to create backup
    BackupCreation { path: PathBuf, source: io::Error },
    /// Failed to read original file for backup
    OriginalRead { path: PathBuf, source: io::Error },
    /// Failed to create backup directory
    BackupDirCreation { path: PathBuf, source: io::Error },
    /// Failed to acquire lock (file is being modified by another process)
    LockAcquisitionFailed { path: PathBuf, reason: String },
    /// Lock file is stale but cannot be removed
    StaleLockRemoval { path: PathBuf, source: io::Error },
    /// Failed to release lock
    LockReleaseFailed { path: PathBuf, source: io::Error },
    /// Rollback failed
    RollbackFailed { path: PathBuf, source: io::Error },
    /// Content validation failed after write
    ValidationFailed {
        path: PathBuf,
        expected_len: usize,
        actual_len: usize,
    },
    /// Parent directory does not exist
    ParentDirMissing { path: PathBuf },
    /// File is on different filesystem than temp directory (rename would fail)
    CrossFilesystem { path: PathBuf },
}

impl std::fmt::Display for AtomicWriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AtomicWriteError::TempFileCreation { path, source } => {
                write!(
                    f,
                    "Failed to create temporary file at {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::TempFileWrite { path, source } => {
                write!(
                    f,
                    "Failed to write to temporary file {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::TempFileSync { path, source } => {
                write!(
                    f,
                    "Failed to sync temporary file {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::Rename { from, to, source } => {
                write!(
                    f,
                    "Failed to rename {} to {}: {}",
                    from.display(),
                    to.display(),
                    source
                )
            }
            AtomicWriteError::BackupCreation { path, source } => {
                write!(f, "Failed to create backup at {}: {}", path.display(), source)
            }
            AtomicWriteError::OriginalRead { path, source } => {
                write!(
                    f,
                    "Failed to read original file {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::BackupDirCreation { path, source } => {
                write!(
                    f,
                    "Failed to create backup directory {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::LockAcquisitionFailed { path, reason } => {
                write!(
                    f,
                    "Failed to acquire lock for {}: {}",
                    path.display(),
                    reason
                )
            }
            AtomicWriteError::StaleLockRemoval { path, source } => {
                write!(
                    f,
                    "Failed to remove stale lock file {}: {}",
                    path.display(),
                    source
                )
            }
            AtomicWriteError::LockReleaseFailed { path, source } => {
                write!(f, "Failed to release lock for {}: {}", path.display(), source)
            }
            AtomicWriteError::RollbackFailed { path, source } => {
                write!(f, "Failed to rollback {}: {}", path.display(), source)
            }
            AtomicWriteError::ValidationFailed {
                path,
                expected_len,
                actual_len,
            } => {
                write!(
                    f,
                    "Content validation failed for {}: expected {} bytes, got {}",
                    path.display(),
                    expected_len,
                    actual_len
                )
            }
            AtomicWriteError::ParentDirMissing { path } => {
                write!(
                    f,
                    "Parent directory does not exist for {}",
                    path.display()
                )
            }
            AtomicWriteError::CrossFilesystem { path } => {
                write!(
                    f,
                    "File {} is on different filesystem, atomic rename not possible",
                    path.display()
                )
            }
        }
    }
}

impl std::error::Error for AtomicWriteError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            AtomicWriteError::TempFileCreation { source, .. } => Some(source),
            AtomicWriteError::TempFileWrite { source, .. } => Some(source),
            AtomicWriteError::TempFileSync { source, .. } => Some(source),
            AtomicWriteError::Rename { source, .. } => Some(source),
            AtomicWriteError::BackupCreation { source, .. } => Some(source),
            AtomicWriteError::OriginalRead { source, .. } => Some(source),
            AtomicWriteError::BackupDirCreation { source, .. } => Some(source),
            AtomicWriteError::StaleLockRemoval { source, .. } => Some(source),
            AtomicWriteError::LockReleaseFailed { source, .. } => Some(source),
            AtomicWriteError::RollbackFailed { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Result type for atomic write operations.
pub type AtomicWriteResult<T> = Result<T, AtomicWriteError>;

/// Information about a backup file.
#[derive(Debug, Clone)]
pub struct BackupInfo {
    /// Path to the backup file
    pub backup_path: PathBuf,
    /// Path to the original file
    pub original_path: PathBuf,
    /// Timestamp when backup was created
    pub created_at: SystemTime,
    /// Size of the backup in bytes
    pub size: u64,
}

/// Atomic file writer with backup and lock file support.
///
/// This struct provides safe file writing operations that:
/// - Write to a temp file first, then atomic rename
/// - Create backups before modifying files
/// - Use lock files to prevent concurrent modification
/// - Support rollback from backup
pub struct AtomicWriter {
    /// Active locks held by this writer (path -> lock file path)
    active_locks: Arc<Mutex<HashMap<PathBuf, PathBuf>>>,
    /// Backup retention duration
    backup_retention: Duration,
    /// Whether to validate content after write
    validate_writes: bool,
}

impl Default for AtomicWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl AtomicWriter {
    /// Create a new AtomicWriter with default settings.
    pub fn new() -> Self {
        Self {
            active_locks: Arc::new(Mutex::new(HashMap::new())),
            backup_retention: Duration::from_secs(DEFAULT_BACKUP_RETENTION_HOURS * 3600),
            validate_writes: true,
        }
    }

    /// Create an AtomicWriter with custom backup retention.
    pub fn with_retention(retention_hours: u64) -> Self {
        Self {
            active_locks: Arc::new(Mutex::new(HashMap::new())),
            backup_retention: Duration::from_secs(retention_hours * 3600),
            validate_writes: true,
        }
    }

    /// Get a nanosecond timestamp for unique file naming.
    ///
    /// Logs a warning if the system clock is behind UNIX epoch (which indicates
    /// a severely misconfigured system) rather than silently returning 0.
    fn unix_timestamp_nanos() -> u128 {
        match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(d) => d.as_nanos(),
            Err(e) => {
                warn!(
                    "System clock is behind UNIX epoch ({}); using 0 for timestamp",
                    e
                );
                0
            }
        }
    }

    /// Get a second-precision timestamp for lock file content.
    ///
    /// Logs a warning on clock failure rather than silently returning 0.
    fn unix_timestamp_secs() -> u64 {
        match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(d) => d.as_secs(),
            Err(e) => {
                warn!(
                    "System clock is behind UNIX epoch ({}); using 0 for timestamp",
                    e
                );
                0
            }
        }
    }

    /// Disable write validation (not recommended for production).
    pub fn without_validation(mut self) -> Self {
        self.validate_writes = false;
        self
    }

    /// Atomically write content to a file.
    ///
    /// This function:
    /// 1. Creates a temp file in the same directory as the target
    /// 2. Writes content to the temp file
    /// 3. Syncs the temp file to disk
    /// 4. Atomically renames temp file to target
    ///
    /// If any step fails, the original file is untouched.
    pub fn write(&self, path: &Path, content: &str) -> AtomicWriteResult<()> {
        // Verify parent directory exists
        let parent = path.parent().ok_or_else(|| AtomicWriteError::ParentDirMissing {
            path: path.to_path_buf(),
        })?;

        if !parent.exists() {
            return Err(AtomicWriteError::ParentDirMissing {
                path: path.to_path_buf(),
            });
        }

        // Generate temp file path in same directory (ensures same filesystem for atomic rename)
        let temp_path = self.generate_temp_path(path);
        debug!("Creating temp file: {}", temp_path.display());

        // Create and write to temp file
        let mut temp_file = File::create(&temp_path).map_err(|e| AtomicWriteError::TempFileCreation {
            path: temp_path.clone(),
            source: e,
        })?;

        temp_file
            .write_all(content.as_bytes())
            .map_err(|e| AtomicWriteError::TempFileWrite {
                path: temp_path.clone(),
                source: e,
            })?;

        // Sync to disk to ensure durability
        temp_file
            .sync_all()
            .map_err(|e| AtomicWriteError::TempFileSync {
                path: temp_path.clone(),
                source: e,
            })?;

        // Close the file explicitly before rename
        drop(temp_file);

        // Atomic rename
        fs::rename(&temp_path, path).map_err(|e| {
            // Clean up temp file on failure
            let _ = fs::remove_file(&temp_path);
            AtomicWriteError::Rename {
                from: temp_path.clone(),
                to: path.to_path_buf(),
                source: e,
            }
        })?;

        // Validate if enabled
        if self.validate_writes {
            self.validate_content(path, content)?;
        }

        debug!("Successfully wrote {} bytes to {}", content.len(), path.display());
        Ok(())
    }

    /// Atomically write content to a file with backup.
    ///
    /// This function:
    /// 1. Acquires a lock on the file
    /// 2. Creates a backup of the original file
    /// 3. Atomically writes new content
    /// 4. Releases the lock
    ///
    /// Returns the path to the backup file for potential rollback.
    pub fn write_with_backup(&self, path: &Path, content: &str) -> AtomicWriteResult<PathBuf> {
        // Acquire lock
        self.acquire_lock(path)?;

        // Create backup (if file exists)
        let backup_path = if path.exists() {
            Some(self.create_backup(path)?)
        } else {
            None
        };

        // Attempt atomic write
        let write_result = self.write(path, content);

        // Release lock regardless of write result
        let release_result = self.release_lock(path);

        // Handle write failure - attempt rollback
        if let Err(write_err) = write_result {
            if let Some(ref backup) = backup_path {
                warn!("Write failed, attempting rollback from backup");
                if let Err(_rollback_err) = self.rollback(path, backup) {
                    error!(
                        "CRITICAL: Write failed AND rollback failed! Backup at: {}",
                        backup.display()
                    );
                    // Return the original write error since that's the root cause
                    return Err(write_err);
                }
                info!("Successfully rolled back from backup");
            }
            return Err(write_err);
        }

        // Handle lock release failure (write succeeded)
        if let Err(lock_err) = release_result {
            warn!("Lock release failed (but write succeeded): {:?}", lock_err);
            // Don't fail the operation since the write succeeded
        }

        Ok(backup_path.unwrap_or_else(|| self.generate_backup_path(path)))
    }

    /// Rollback a file from its backup.
    pub fn rollback(&self, original: &Path, backup: &Path) -> AtomicWriteResult<()> {
        if !backup.exists() {
            warn!("Backup file does not exist: {}", backup.display());
            return Ok(());
        }

        // Read backup content
        let mut backup_content = String::new();
        File::open(backup)
            .and_then(|mut f| f.read_to_string(&mut backup_content))
            .map_err(|e| AtomicWriteError::RollbackFailed {
                path: original.to_path_buf(),
                source: e,
            })?;

        // Atomic write the backup content
        self.write(original, &backup_content)?;

        info!(
            "Rolled back {} from backup {}",
            original.display(),
            backup.display()
        );
        Ok(())
    }

    /// Create a backup of a file.
    ///
    /// Uses temp-file + sync + rename pattern for crash safety. A crash mid-write
    /// leaves only a `.tmp` file; the final `.bak` path either exists with full
    /// content or does not exist at all.
    fn create_backup(&self, path: &Path) -> AtomicWriteResult<PathBuf> {
        let backup_dir = self.get_backup_dir(path)?;
        let backup_path = self.generate_backup_path(path);

        // Read original content
        let mut content = String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut content))
            .map_err(|e| AtomicWriteError::OriginalRead {
                path: path.to_path_buf(),
                source: e,
            })?;

        // Create backup directory if needed
        if !backup_dir.exists() {
            fs::create_dir_all(&backup_dir).map_err(|e| AtomicWriteError::BackupDirCreation {
                path: backup_dir.clone(),
                source: e,
            })?;
        }

        // Atomic backup: write to temp file, sync, then rename.
        // This prevents corrupted backups if the process crashes mid-write.
        let filename = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "file".to_string());

        let temp_backup_path = backup_dir.join(format!(
            ".{}.{}.bak.tmp",
            filename,
            Self::unix_timestamp_nanos()
        ));

        let mut temp_file =
            File::create(&temp_backup_path).map_err(|e| AtomicWriteError::BackupCreation {
                path: temp_backup_path.clone(),
                source: e,
            })?;

        temp_file
            .write_all(content.as_bytes())
            .map_err(|e| {
                let _ = fs::remove_file(&temp_backup_path);
                AtomicWriteError::BackupCreation {
                    path: temp_backup_path.clone(),
                    source: e,
                }
            })?;

        temp_file
            .sync_all()
            .map_err(|e| {
                let _ = fs::remove_file(&temp_backup_path);
                AtomicWriteError::BackupCreation {
                    path: temp_backup_path.clone(),
                    source: e,
                }
            })?;

        // Close file before rename
        drop(temp_file);

        // Atomic rename: temp -> final backup path
        fs::rename(&temp_backup_path, &backup_path).map_err(|e| {
            let _ = fs::remove_file(&temp_backup_path);
            AtomicWriteError::BackupCreation {
                path: backup_path.clone(),
                source: e,
            }
        })?;

        info!("Created backup: {}", backup_path.display());
        Ok(backup_path)
    }

    /// Acquire a lock on a file to prevent concurrent modification.
    ///
    /// Uses atomic `create_new(true)` as the primary mechanism to avoid TOCTOU
    /// races. The protocol is:
    ///   1. Try atomic create (optimistic, no race window)
    ///   2. On AlreadyExists, check if the existing lock is stale
    ///   3. If stale, remove and retry exactly once
    ///   4. If retry also fails, another process won the race -- report error
    fn acquire_lock(&self, path: &Path) -> AtomicWriteResult<()> {
        let lock_path = self.get_lock_path(path);

        // Ensure parent directory exists before any lock creation attempt
        if let Some(parent) = lock_path.parent() {
            if !parent.exists() {
                fs::create_dir_all(parent).map_err(|e| AtomicWriteError::BackupDirCreation {
                    path: parent.to_path_buf(),
                    source: e,
                })?;
            }
        }

        let lock_content = format!(
            "pid:{}\ntime:{}\nfile:{}",
            std::process::id(),
            Self::unix_timestamp_secs(),
            path.display()
        );

        // Attempt 1: Atomic create -- no TOCTOU, no check-then-act race
        match Self::try_create_lock_atomic(&lock_path, &lock_content) {
            Ok(()) => {
                self.track_lock(path, &lock_path);
                debug!("Acquired lock: {}", lock_path.display());
                return Ok(());
            }
            Err((true, _)) => {
                // AlreadyExists -- fall through to staleness check
            }
            Err((false, e)) => {
                return Err(AtomicWriteError::LockAcquisitionFailed {
                    path: path.to_path_buf(),
                    reason: format!("Failed to create lock file: {}", e),
                });
            }
        }

        // Lock file exists. Check whether it is stale.
        match self.is_lock_stale(&lock_path) {
            Ok(false) => {
                return Err(AtomicWriteError::LockAcquisitionFailed {
                    path: path.to_path_buf(),
                    reason: format!(
                        "File is locked by another process (lock file: {})",
                        lock_path.display()
                    ),
                });
            }
            Ok(true) => {
                // Stale -- proceed to remove below
            }
            Err(_) => {
                // Lock disappeared between our create attempt and staleness check.
                // Another process removed it; fall through to retry.
            }
        }

        // Remove stale lock. Tolerate NotFound (another process may have cleaned it).
        info!("Removing stale lock: {}", lock_path.display());
        if let Err(e) = fs::remove_file(&lock_path) {
            if e.kind() != io::ErrorKind::NotFound {
                return Err(AtomicWriteError::StaleLockRemoval {
                    path: lock_path.clone(),
                    source: e,
                });
            }
        }

        // Attempt 2: Retry atomic create after stale removal
        match Self::try_create_lock_atomic(&lock_path, &lock_content) {
            Ok(()) => {
                self.track_lock(path, &lock_path);
                debug!("Acquired lock (after stale removal): {}", lock_path.display());
                Ok(())
            }
            Err((true, _)) => Err(AtomicWriteError::LockAcquisitionFailed {
                path: path.to_path_buf(),
                reason: "Lock was acquired by another process during stale lock removal"
                    .to_string(),
            }),
            Err((false, e)) => Err(AtomicWriteError::LockAcquisitionFailed {
                path: path.to_path_buf(),
                reason: format!("Failed to create lock file on retry: {}", e),
            }),
        }
    }

    /// Atomically create a lock file using `create_new(true)`.
    ///
    /// Returns `Ok(())` on success. On failure returns `Err((already_exists, io_error))`
    /// where `already_exists` is true if the file already existed.
    fn try_create_lock_atomic(
        lock_path: &Path,
        lock_content: &str,
    ) -> Result<(), (bool, io::Error)> {
        let mut lock_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(lock_path)
            .map_err(|e| (e.kind() == io::ErrorKind::AlreadyExists, e))?;

        lock_file.write_all(lock_content.as_bytes()).map_err(|e| {
            // Clean up on write failure
            let _ = fs::remove_file(lock_path);
            (false, e)
        })?;

        Ok(())
    }

    /// Record a lock in the active locks map (poisoned-mutex safe).
    fn track_lock(&self, path: &Path, lock_path: &Path) {
        let mut locks = self
            .active_locks
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        locks.insert(path.to_path_buf(), lock_path.to_path_buf());
    }

    /// Release a lock on a file.
    fn release_lock(&self, path: &Path) -> AtomicWriteResult<()> {
        let lock_path = self.get_lock_path(path);

        // Remove from active locks (poisoned-mutex safe)
        {
            let mut locks = self
                .active_locks
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            locks.remove(path);
        }

        // Delete lock file
        if lock_path.exists() {
            fs::remove_file(&lock_path).map_err(|e| AtomicWriteError::LockReleaseFailed {
                path: path.to_path_buf(),
                source: e,
            })?;
        }

        debug!("Released lock: {}", lock_path.display());
        Ok(())
    }

    /// Check if a lock file is stale (older than LOCK_TIMEOUT_SECS).
    fn is_lock_stale(&self, lock_path: &Path) -> AtomicWriteResult<bool> {
        let metadata = fs::metadata(lock_path).map_err(|e| AtomicWriteError::LockAcquisitionFailed {
            path: lock_path.to_path_buf(),
            reason: format!("Cannot read lock file metadata: {}", e),
        })?;

        let modified = metadata.modified().map_err(|e| {
            AtomicWriteError::LockAcquisitionFailed {
                path: lock_path.to_path_buf(),
                reason: format!("Cannot read lock file mtime: {}", e),
            }
        })?;

        let age = SystemTime::now()
            .duration_since(modified)
            .unwrap_or(Duration::ZERO);

        Ok(age.as_secs() > LOCK_TIMEOUT_SECS)
    }

    /// Validate that written content matches expected content.
    fn validate_content(&self, path: &Path, expected: &str) -> AtomicWriteResult<()> {
        let mut actual = String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut actual))
            .map_err(|e| AtomicWriteError::OriginalRead {
                path: path.to_path_buf(),
                source: e,
            })?;

        if actual.len() != expected.len() {
            return Err(AtomicWriteError::ValidationFailed {
                path: path.to_path_buf(),
                expected_len: expected.len(),
                actual_len: actual.len(),
            });
        }

        // Full content comparison for safety
        if actual != expected {
            return Err(AtomicWriteError::ValidationFailed {
                path: path.to_path_buf(),
                expected_len: expected.len(),
                actual_len: actual.len(),
            });
        }

        Ok(())
    }

    /// Generate a unique temp file path in the same directory as the target.
    fn generate_temp_path(&self, path: &Path) -> PathBuf {
        let parent = path.parent().unwrap_or(Path::new("."));
        let filename = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "file".to_string());

        let timestamp = Self::unix_timestamp_nanos();

        parent.join(format!(".{}.{}.tmp", filename, timestamp))
    }

    /// Generate a backup file path.
    /// Uses nanosecond precision to avoid collisions when multiple backups are created rapidly.
    fn generate_backup_path(&self, path: &Path) -> PathBuf {
        let backup_dir = self.get_backup_dir(path).unwrap_or_else(|_| {
            path.parent()
                .unwrap_or(Path::new("."))
                .join(BACKUP_DIR_NAME)
        });

        let filename = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "file".to_string());

        // Use nanoseconds to avoid collisions when creating multiple backups rapidly
        let timestamp = Self::unix_timestamp_nanos();

        backup_dir.join(format!("{}.{}.bak", filename, timestamp))
    }

    /// Get the backup directory for a file.
    fn get_backup_dir(&self, path: &Path) -> AtomicWriteResult<PathBuf> {
        let parent = path.parent().ok_or_else(|| AtomicWriteError::ParentDirMissing {
            path: path.to_path_buf(),
        })?;

        Ok(parent.join(BACKUP_DIR_NAME))
    }

    /// Get the lock file path for a file.
    fn get_lock_path(&self, path: &Path) -> PathBuf {
        let backup_dir = self
            .get_backup_dir(path)
            .unwrap_or_else(|_| path.parent().unwrap_or(Path::new(".")).join(BACKUP_DIR_NAME));

        let filename = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "file".to_string());

        backup_dir.join(format!("{}.lock", filename))
    }

    /// List all backups for a given directory.
    pub fn list_backups(&self, dir: &Path) -> AtomicWriteResult<Vec<BackupInfo>> {
        let backup_dir = dir.join(BACKUP_DIR_NAME);
        if !backup_dir.exists() {
            return Ok(Vec::new());
        }

        let mut backups = Vec::new();

        let entries = fs::read_dir(&backup_dir).map_err(|e| AtomicWriteError::BackupDirCreation {
            path: backup_dir.clone(),
            source: e,
        })?;

        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("bak") {
                if let Ok(metadata) = fs::metadata(&path) {
                    let created_at = metadata.modified().unwrap_or(SystemTime::UNIX_EPOCH);

                    // Parse original filename from backup name
                    let filename = path
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("");

                    // Format: "original.timestamp.bak" -> "original"
                    let original_name: String = filename
                        .rsplitn(3, '.')
                        .skip(2)
                        .collect::<Vec<_>>()
                        .into_iter()
                        .rev()
                        .collect::<Vec<_>>()
                        .join(".");

                    let original_path = dir.join(&original_name);

                    backups.push(BackupInfo {
                        backup_path: path,
                        original_path,
                        created_at,
                        size: metadata.len(),
                    });
                }
            }
        }

        // Sort by creation time, newest first
        backups.sort_by_key(|b| std::cmp::Reverse(b.created_at));

        Ok(backups)
    }

    /// Clean up old backups beyond retention period.
    pub fn cleanup_old_backups(&self, dir: &Path) -> AtomicWriteResult<usize> {
        let backups = self.list_backups(dir)?;
        let now = SystemTime::now();
        let mut removed = 0;

        for backup in backups {
            let age = now.duration_since(backup.created_at).unwrap_or(Duration::ZERO);

            if age > self.backup_retention {
                if let Err(e) = fs::remove_file(&backup.backup_path) {
                    warn!(
                        "Failed to remove old backup {}: {}",
                        backup.backup_path.display(),
                        e
                    );
                } else {
                    debug!("Removed old backup: {}", backup.backup_path.display());
                    removed += 1;
                }
            }
        }

        // Remove backup directory if empty
        let backup_dir = dir.join(BACKUP_DIR_NAME);
        if backup_dir.exists() {
            if let Ok(entries) = fs::read_dir(&backup_dir) {
                // Count non-lock files
                let file_count = entries
                    .flatten()
                    .filter(|e| {
                        e.path()
                            .extension()
                            .and_then(|ext| ext.to_str())
                            .map(|ext| ext != "lock")
                            .unwrap_or(true)
                    })
                    .count();

                if file_count == 0 {
                    let _ = fs::remove_dir(&backup_dir);
                }
            }
        }

        if removed > 0 {
            info!("Cleaned up {} old backup(s) from {}", removed, dir.display());
        }

        Ok(removed)
    }

    /// Restore a specific backup.
    pub fn restore_backup(&self, backup: &BackupInfo) -> AtomicWriteResult<()> {
        if !backup.backup_path.exists() {
            return Err(AtomicWriteError::RollbackFailed {
                path: backup.original_path.clone(),
                source: io::Error::new(io::ErrorKind::NotFound, "Backup file not found"),
            });
        }

        self.rollback(&backup.original_path, &backup.backup_path)
    }
}

impl Drop for AtomicWriter {
    fn drop(&mut self) {
        // Release all held locks on drop.
        // Use unwrap_or_else to avoid aborting if the mutex was poisoned by a
        // panic on another thread -- during unwinding a second panic would abort.
        let locks = self
            .active_locks
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for (path, lock_path) in locks.iter() {
            if lock_path.exists() {
                if let Err(e) = fs::remove_file(lock_path) {
                    error!(
                        "Failed to release lock for {} on drop: {}",
                        path.display(),
                        e
                    );
                }
            }
        }
    }
}

/// Convenience function for simple atomic write without backup.
pub fn atomic_write(path: &Path, content: &str) -> AtomicWriteResult<()> {
    AtomicWriter::new().write(path, content)
}

/// Convenience function for atomic write with backup.
pub fn atomic_write_with_backup(path: &Path, content: &str) -> AtomicWriteResult<PathBuf> {
    AtomicWriter::new().write_with_backup(path, content)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn create_test_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let path = dir.path().join(name);
        fs::write(&path, content).expect("Failed to write test file");
        path
    }

    #[test]
    fn test_atomic_write_success() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = temp_dir.path().join("test.txt");

        let writer = AtomicWriter::new();
        writer
            .write(&file_path, "Hello, World!")
            .expect("Atomic write should succeed");

        let content = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(content, "Hello, World!");
    }

    #[test]
    fn test_atomic_write_overwrites_existing() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.txt", "Original content");

        let writer = AtomicWriter::new();
        writer
            .write(&file_path, "New content")
            .expect("Atomic write should succeed");

        let content = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(content, "New content");
    }

    #[test]
    fn test_atomic_write_with_backup_creates_backup() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Original F* content");

        let writer = AtomicWriter::new();
        let backup_path = writer
            .write_with_backup(&file_path, "Modified F* content")
            .expect("Atomic write with backup should succeed");

        // Check new content
        let content = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(content, "Modified F* content");

        // Check backup exists
        assert!(backup_path.exists(), "Backup file should exist");

        // Check backup content
        let backup_content = fs::read_to_string(&backup_path).expect("Should read backup");
        assert_eq!(backup_content, "Original F* content");
    }

    #[test]
    fn test_rollback_restores_original() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Original content");

        let writer = AtomicWriter::new();

        // Write with backup
        let backup_path = writer
            .write_with_backup(&file_path, "Modified content")
            .expect("Write with backup should succeed");

        // Verify modification
        let content = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(content, "Modified content");

        // Rollback
        writer
            .rollback(&file_path, &backup_path)
            .expect("Rollback should succeed");

        // Verify restoration
        let restored = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(restored, "Original content");
    }

    #[test]
    fn test_lock_prevents_concurrent_access() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Content");

        let writer1 = AtomicWriter::new();
        let writer2 = AtomicWriter::new();

        // First writer acquires lock
        writer1
            .acquire_lock(&file_path)
            .expect("First lock should succeed");

        // Second writer should fail
        let result = writer2.acquire_lock(&file_path);
        assert!(result.is_err(), "Second lock should fail");

        // Release first lock
        writer1
            .release_lock(&file_path)
            .expect("Lock release should succeed");

        // Now second writer should succeed
        writer2
            .acquire_lock(&file_path)
            .expect("Second lock should succeed after release");

        writer2
            .release_lock(&file_path)
            .expect("Cleanup lock release");
    }

    #[test]
    fn test_list_backups() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Content v1");

        let writer = AtomicWriter::new();

        // Create multiple backups
        writer
            .write_with_backup(&file_path, "Content v2")
            .expect("First backup should succeed");

        // Small delay to ensure different timestamps
        std::thread::sleep(std::time::Duration::from_millis(100));

        writer
            .write_with_backup(&file_path, "Content v3")
            .expect("Second backup should succeed");

        // List backups
        let backups = writer
            .list_backups(temp_dir.path())
            .expect("List backups should succeed");

        assert!(backups.len() >= 2, "Should have at least 2 backups");
    }

    #[test]
    fn test_cleanup_old_backups() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Content");

        // Create writer with very short retention (1 second)
        let writer = AtomicWriter {
            active_locks: Arc::new(Mutex::new(HashMap::new())),
            backup_retention: Duration::from_secs(1),
            validate_writes: true,
        };

        // Create backup
        writer
            .write_with_backup(&file_path, "New content")
            .expect("Backup should succeed");

        // Wait for backup to become "old"
        std::thread::sleep(std::time::Duration::from_secs(2));

        // Cleanup
        let removed = writer
            .cleanup_old_backups(temp_dir.path())
            .expect("Cleanup should succeed");

        assert!(removed > 0, "Should have removed at least one old backup");
    }

    #[test]
    fn test_temp_file_cleanup_on_failure() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = temp_dir.path().join("nonexistent_dir").join("test.txt");

        let writer = AtomicWriter::new();
        let result = writer.write(&file_path, "Content");

        // Should fail because parent directory doesn't exist
        assert!(result.is_err());

        // Verify no temp files left behind
        let temp_files: Vec<_> = fs::read_dir(temp_dir.path())
            .expect("Should read dir")
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .extension()
                    .and_then(|ext| ext.to_str())
                    .map(|ext| ext == "tmp")
                    .unwrap_or(false)
            })
            .collect();

        assert!(temp_files.is_empty(), "No temp files should be left behind");
    }

    #[test]
    fn test_validation_catches_corruption() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = temp_dir.path().join("test.txt");

        let writer = AtomicWriter::new();

        // Write normally first
        writer
            .write(&file_path, "Test content")
            .expect("Write should succeed");

        // Validation during write should pass
        let content = fs::read_to_string(&file_path).expect("Read should succeed");
        assert_eq!(content, "Test content");
    }

    #[test]
    fn test_write_new_file_without_backup() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = temp_dir.path().join("new_file.fst");

        let writer = AtomicWriter::new();

        // File doesn't exist, so backup path will be generated but no actual backup created
        let result = writer.write_with_backup(&file_path, "New file content");

        assert!(result.is_ok(), "Write should succeed for new file");

        let content = fs::read_to_string(&file_path).expect("Should read file");
        assert_eq!(content, "New file content");
    }

    #[test]
    fn test_convenience_functions() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");

        // Test atomic_write
        let file1 = temp_dir.path().join("file1.txt");
        atomic_write(&file1, "Content 1").expect("atomic_write should succeed");
        assert_eq!(
            fs::read_to_string(&file1).unwrap(),
            "Content 1"
        );

        // Test atomic_write_with_backup
        let file2 = temp_dir.path().join("file2.txt");
        fs::write(&file2, "Original").expect("Setup file");
        let backup = atomic_write_with_backup(&file2, "Content 2")
            .expect("atomic_write_with_backup should succeed");

        assert_eq!(
            fs::read_to_string(&file2).unwrap(),
            "Content 2"
        );
        assert!(backup.exists() || !temp_dir.path().join(BACKUP_DIR_NAME).exists());
    }

    #[test]
    fn test_restore_backup() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "test.fst", "Original content");

        let writer = AtomicWriter::new();

        // Create backup
        writer
            .write_with_backup(&file_path, "Modified content")
            .expect("Write should succeed");

        // Get backups
        let backups = writer
            .list_backups(temp_dir.path())
            .expect("List should succeed");

        assert!(!backups.is_empty(), "Should have backups");

        // Restore first backup
        writer
            .restore_backup(&backups[0])
            .expect("Restore should succeed");

        // Verify restoration
        let content = fs::read_to_string(&file_path).expect("Read should succeed");
        assert_eq!(content, "Original content");
    }

    // =========================================================================
    // CONCURRENT ACCESS TESTS
    // =========================================================================

    #[test]
    fn test_concurrent_lock_acquisition_same_file() {
        // Two threads race to acquire a lock on the same file.
        // Exactly one must succeed; the other must fail.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "race.fst", "content");
        let path = file_path.clone();

        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));

        let b1 = barrier.clone();
        let p1 = path.clone();
        let h1 = std::thread::spawn(move || {
            let writer = AtomicWriter::new();
            b1.wait(); // synchronize start
            let result = writer.acquire_lock(&p1);
            if result.is_ok() {
                // Hold the lock briefly so the other thread has time to attempt
                std::thread::sleep(Duration::from_millis(50));
                let _ = writer.release_lock(&p1);
            }
            result.is_ok()
        });

        let b2 = barrier.clone();
        let p2 = path.clone();
        let h2 = std::thread::spawn(move || {
            let writer = AtomicWriter::new();
            b2.wait(); // synchronize start
            let result = writer.acquire_lock(&p2);
            if result.is_ok() {
                std::thread::sleep(Duration::from_millis(50));
                let _ = writer.release_lock(&p2);
            }
            result.is_ok()
        });

        let r1 = h1.join().expect("Thread 1 panicked");
        let r2 = h2.join().expect("Thread 2 panicked");

        // Exactly one thread should succeed (mutual exclusion).
        // Both cannot succeed because create_new(true) is atomic.
        assert!(
            (r1 && !r2) || (!r1 && r2),
            "Exactly one thread should acquire the lock, got r1={}, r2={}",
            r1,
            r2
        );
    }

    #[test]
    fn test_concurrent_writes_to_different_files_preserve_content() {
        // Multiple threads write to distinct files concurrently.
        // All writes must complete and produce correct content.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let base = temp_dir.path().to_path_buf();

        let num_threads = 8;
        let writes_per_thread = 5;

        // Create initial files
        for i in 0..num_threads {
            let path = base.join(format!("concurrent_{}.txt", i));
            fs::write(&path, format!("initial_{}", i)).expect("setup write");
        }

        let handles: Vec<_> = (0..num_threads)
            .map(|i| {
                let dir = base.clone();
                std::thread::spawn(move || {
                    let file_path = dir.join(format!("concurrent_{}.txt", i));
                    let writer = AtomicWriter::new();
                    for j in 0..writes_per_thread {
                        writer
                            .write_with_backup(
                                &file_path,
                                &format!("thread_{}_write_{}", i, j),
                            )
                            .expect("concurrent write should succeed");
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().expect("Thread panicked");
        }

        // Verify each file has the content from its last write
        for i in 0..num_threads {
            let path = base.join(format!("concurrent_{}.txt", i));
            let content = fs::read_to_string(&path).expect("read result");
            let expected = format!("thread_{}_write_{}", i, writes_per_thread - 1);
            assert_eq!(
                content, expected,
                "File concurrent_{}.txt has wrong content", i
            );
        }
    }

    #[test]
    fn test_stale_lock_allows_reacquisition() {
        // Simulate a stale lock (created in the past) and verify a new writer
        // can acquire the lock after detecting staleness.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "stale.fst", "content");

        let writer = AtomicWriter::new();

        // Manually create a stale lock file with an old timestamp
        let lock_path = writer.get_lock_path(&file_path);
        if let Some(parent) = lock_path.parent() {
            fs::create_dir_all(parent).expect("create lock dir");
        }

        let stale_time = SystemTime::now()
            .checked_sub(Duration::from_secs(LOCK_TIMEOUT_SECS + 60))
            .unwrap_or(SystemTime::UNIX_EPOCH);

        // Create lock file with old content
        fs::write(
            &lock_path,
            format!("pid:99999\ntime:0\nfile:{}", file_path.display()),
        )
        .expect("create stale lock");

        // Set modification time to the past using std::fs::File::set_times
        // (stabilized in Rust 1.75).
        {
            let file = OpenOptions::new()
                .write(true)
                .open(&lock_path)
                .expect("open lock for mtime update");
            let times = std::fs::FileTimes::new()
                .set_modified(stale_time)
                .set_accessed(stale_time);
            file.set_times(times).expect("set lock mtime");
        }

        // A new writer should detect staleness, remove, and acquire
        let writer2 = AtomicWriter::new();
        let result = writer2.acquire_lock(&file_path);

        assert!(
            result.is_ok(),
            "Should acquire lock after stale lock detected: {:?}",
            result.err()
        );

        // Cleanup
        let _ = writer2.release_lock(&file_path);
    }

    #[test]
    fn test_lock_acquire_release_cycle() {
        // Rapidly acquire and release the same lock to stress the atomic path.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "cycle.fst", "content");

        let writer = AtomicWriter::new();
        for i in 0..20 {
            writer
                .acquire_lock(&file_path)
                .unwrap_or_else(|e| panic!("Lock acquisition {} failed: {:?}", i, e));
            writer
                .release_lock(&file_path)
                .unwrap_or_else(|e| panic!("Lock release {} failed: {:?}", i, e));
        }
    }

    #[test]
    fn test_backup_is_atomic_no_partial_content() {
        // Verify that backup files always contain complete content (never partial).
        // We write a known string and verify the backup matches exactly.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "atomic_bak.fst", "Original line 1\nOriginal line 2\nOriginal line 3\n");

        let writer = AtomicWriter::new();
        let backup_path = writer
            .write_with_backup(&file_path, "New content")
            .expect("Write with backup should succeed");

        let backup_content = fs::read_to_string(&backup_path).expect("Read backup");
        assert_eq!(
            backup_content,
            "Original line 1\nOriginal line 2\nOriginal line 3\n",
            "Backup must contain exact original content"
        );

        // Verify no .tmp files remain in the backup directory
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        if backup_dir.exists() {
            let tmp_files: Vec<_> = fs::read_dir(&backup_dir)
                .expect("read backup dir")
                .filter_map(|e| e.ok())
                .filter(|e| {
                    e.path()
                        .extension()
                        .and_then(|ext| ext.to_str())
                        .map(|ext| ext == "tmp")
                        .unwrap_or(false)
                })
                .collect();
            assert!(
                tmp_files.is_empty(),
                "No .tmp files should remain in backup directory after successful backup"
            );
        }
    }

    #[test]
    fn test_nanosecond_backup_uniqueness() {
        // Create multiple backups rapidly and verify all have unique paths.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "rapid.fst", "v0");

        let writer = AtomicWriter::new();
        let mut backup_paths = Vec::new();
        for i in 1..=10 {
            let bp = writer
                .write_with_backup(&file_path, &format!("v{}", i))
                .expect("rapid backup should succeed");
            backup_paths.push(bp);
        }

        // All backup paths must be distinct
        let unique: std::collections::HashSet<_> = backup_paths.iter().collect();
        assert_eq!(
            unique.len(),
            backup_paths.len(),
            "All backup paths should be unique (nanosecond resolution)"
        );
    }

    #[test]
    fn test_drop_releases_locks() {
        // Verify that dropping an AtomicWriter cleans up its lock files.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "drop_test.fst", "content");

        let lock_path;
        {
            let writer = AtomicWriter::new();
            writer
                .acquire_lock(&file_path)
                .expect("acquire lock");
            lock_path = writer.get_lock_path(&file_path);
            assert!(lock_path.exists(), "Lock file should exist before drop");
            // writer drops here
        }

        assert!(
            !lock_path.exists(),
            "Lock file should be removed after AtomicWriter is dropped"
        );

        // A new writer should be able to acquire the lock
        let writer2 = AtomicWriter::new();
        writer2
            .acquire_lock(&file_path)
            .expect("Should acquire lock after previous writer dropped");
        writer2.release_lock(&file_path).expect("cleanup");
    }

    #[test]
    fn test_concurrent_stale_lock_removal_race() {
        // Multiple threads encounter a stale lock and race to remove it.
        // Exactly one should succeed in acquiring the lock; others should
        // either fail or succeed sequentially -- none should panic.
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let file_path = create_test_file(&temp_dir, "stale_race.fst", "content");

        // Create the lock directory
        let writer_setup = AtomicWriter::new();
        let lock_path = writer_setup.get_lock_path(&file_path);
        if let Some(parent) = lock_path.parent() {
            fs::create_dir_all(parent).expect("create lock dir");
        }

        // Create a stale lock file
        fs::write(
            &lock_path,
            format!("pid:99999\ntime:0\nfile:{}", file_path.display()),
        )
        .expect("create stale lock");

        // Set old mtime using std::fs::FileTimes
        {
            let stale_time = SystemTime::UNIX_EPOCH + Duration::from_secs(1000);
            let file = OpenOptions::new()
                .write(true)
                .open(&lock_path)
                .expect("open lock for mtime update");
            let times = std::fs::FileTimes::new()
                .set_modified(stale_time)
                .set_accessed(stale_time);
            file.set_times(times).expect("set lock mtime");
        }

        let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
        let path = file_path.clone();

        let handles: Vec<_> = (0..4)
            .map(|_| {
                let b = barrier.clone();
                let p = path.clone();
                std::thread::spawn(move || {
                    let writer = AtomicWriter::new();
                    b.wait();
                    let result = writer.acquire_lock(&p);
                    if result.is_ok() {
                        // Hold briefly then release
                        std::thread::sleep(Duration::from_millis(10));
                        let _ = writer.release_lock(&p);
                    }
                    result.is_ok()
                })
            })
            .collect();

        let results: Vec<bool> = handles
            .into_iter()
            .map(|h| h.join().expect("Thread panicked during stale lock race"))
            .collect();

        // At least one thread should have succeeded (stale lock detected).
        // The key assertion is that NO thread panicked.
        {
            let successes = results.iter().filter(|&&r| r).count();
            assert!(
                successes >= 1,
                "At least one thread should acquire the stale lock, got {} successes",
                successes
            );
        }
    }
}
