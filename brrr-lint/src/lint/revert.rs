//! Backup revert functionality for brrr-lint.
//!
//! This module provides the ability to revert files to their backed-up versions.
//! Backups are created automatically when fixes are applied with the `fix --apply` command.
//!
//! # Backup Format
//!
//! Backups are stored in `.fstar-lint-backups/` directories with the format:
//! `filename.timestamp.bak` where timestamp is milliseconds since Unix epoch.
//!
//! # Features
//!
//! - **Atomic revert**: All-or-nothing semantics -- if any file fails, all changes are rolled back
//! - **Modification detection**: Warns when original files have been modified since backup
//! - **Timestamp grouping**: Groups backups by timestamp with configurable tolerance (default 100ms)
//! - **Duplicate handling**: When multiple backups exist for the same file, keeps the newest
//!
//! # Usage
//!
//! ```bash
//! # List all available backup timestamps
//! brrr-lint revert --list
//!
//! # Revert to a specific timestamp
//! brrr-lint revert --timestamp 1706123456789
//!
//! # Revert to the most recent backup
//! brrr-lint revert --latest
//!
//! # Best-effort revert to closest timestamp (within 100ms tolerance)
//! brrr-lint revert --best-effort 1706123456789
//!
//! # Force revert even if files were modified since backup
//! brrr-lint revert --latest --force
//!
//! # Preview what would be reverted (dry-run)
//! brrr-lint revert --latest --dry-run
//!
//! # Filter by path
//! brrr-lint revert --latest src/core/
//! ```

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use tracing::{debug, error, info, warn};

/// The name of the backup directory created by file_safety module.
const BACKUP_DIR_NAME: &str = ".fstar-lint-backups";

/// Validation result: `(valid_with_content, skipped, warnings, hard_failures)`.
type ValidationResult<'a> = (
    Vec<(&'a BackupEntry, String)>,
    Vec<(PathBuf, String)>,
    Vec<(PathBuf, String)>,
    Vec<(PathBuf, String)>,
);

/// Default timestamp tolerance for grouping/matching backups (100 milliseconds).
const DEFAULT_TIMESTAMP_TOLERANCE_MS: u64 = 100;

// =============================================================================
// ERROR TYPES
// =============================================================================

/// Error types for revert operations.
#[derive(Debug)]
pub enum RevertError {
    /// No backups found at the specified path or timestamp.
    NoBackupsFound { path: PathBuf, reason: String },
    /// Timestamp not found in available backups.
    TimestampNotFound { timestamp: u64, available: Vec<u64> },
    /// Failed to read backup file.
    BackupReadFailed { path: PathBuf, source: io::Error },
    /// Failed to write restored file.
    RestoreFailed { path: PathBuf, source: io::Error },
    /// Failed to read directory.
    DirectoryReadFailed { path: PathBuf, source: io::Error },
    /// Invalid backup filename format.
    InvalidBackupFormat { filename: String },
    /// Multiple errors during batch revert (validation failures in atomic mode).
    BatchErrors { errors: Vec<(PathBuf, String)> },
    /// Backup file no longer exists.
    BackupFileMissing {
        backup_path: PathBuf,
        original_path: PathBuf,
    },
    /// Original file was modified since backup was created.
    FileModifiedSinceBackup {
        file: PathBuf,
        backup_time: u64,
        file_modified: u64,
    },
    /// Multiple backups exist for the same file at the same timestamp.
    DuplicateBackups {
        file: PathBuf,
        timestamp: u64,
        count: usize,
    },
    /// Atomic revert failed -- some files were reverted before the failure, then rolled back.
    AtomicRevertFailed {
        reason: String,
        reverted_before_failure: Vec<PathBuf>,
        failed_file: PathBuf,
        error: String,
    },
    /// Rollback during atomic revert also failed (critical, manual intervention needed).
    RollbackFailed {
        original_error: String,
        rollback_failures: Vec<(PathBuf, String)>,
    },
}

impl std::fmt::Display for RevertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RevertError::NoBackupsFound { path, reason } => {
                write!(f, "No backups found at {}: {}", path.display(), reason)
            }
            RevertError::TimestampNotFound {
                timestamp,
                available,
            } => {
                write!(
                    f,
                    "Timestamp {} not found. Available timestamps: {:?}",
                    timestamp, available
                )
            }
            RevertError::BackupReadFailed { path, source } => {
                write!(f, "Failed to read backup {}: {}", path.display(), source)
            }
            RevertError::RestoreFailed { path, source } => {
                write!(f, "Failed to restore {}: {}", path.display(), source)
            }
            RevertError::DirectoryReadFailed { path, source } => {
                write!(
                    f,
                    "Failed to read directory {}: {}",
                    path.display(),
                    source
                )
            }
            RevertError::InvalidBackupFormat { filename } => {
                write!(f, "Invalid backup filename format: {}", filename)
            }
            RevertError::BatchErrors { errors } => {
                writeln!(f, "Multiple errors during revert:")?;
                for (path, err) in errors {
                    writeln!(f, "  - {}: {}", path.display(), err)?;
                }
                Ok(())
            }
            RevertError::BackupFileMissing {
                backup_path,
                original_path,
            } => {
                write!(
                    f,
                    "Backup file no longer exists: {} (for {})",
                    backup_path.display(),
                    original_path.display()
                )
            }
            RevertError::FileModifiedSinceBackup {
                file,
                backup_time,
                file_modified,
            } => {
                write!(
                    f,
                    "File {} was modified after backup (backup: {}, file: {}). Use --force to override.",
                    file.display(),
                    backup_time,
                    file_modified
                )
            }
            RevertError::DuplicateBackups {
                file,
                timestamp,
                count,
            } => {
                write!(
                    f,
                    "Found {} duplicate backups for {} at timestamp {}",
                    count,
                    file.display(),
                    timestamp
                )
            }
            RevertError::AtomicRevertFailed {
                reason,
                reverted_before_failure,
                failed_file,
                error,
            } => {
                write!(
                    f,
                    "Atomic revert failed at {}: {}. {} file(s) were already reverted (rollback attempted).",
                    failed_file.display(),
                    error,
                    reverted_before_failure.len()
                )?;
                if !reason.is_empty() {
                    write!(f, " Reason: {}", reason)?;
                }
                Ok(())
            }
            RevertError::RollbackFailed {
                original_error,
                rollback_failures,
            } => {
                write!(
                    f,
                    "CRITICAL: Revert failed ({}) and rollback also failed for {} file(s). Manual intervention required.",
                    original_error,
                    rollback_failures.len()
                )
            }
        }
    }
}

impl std::error::Error for RevertError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            RevertError::BackupReadFailed { source, .. }
            | RevertError::RestoreFailed { source, .. }
            | RevertError::DirectoryReadFailed { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Result type for revert operations.
pub type RevertResult<T> = Result<T, RevertError>;

// =============================================================================
// DATA TYPES
// =============================================================================

/// Information about a single backup file.
#[derive(Debug, Clone)]
pub struct BackupEntry {
    /// Path to the backup file.
    pub backup_path: PathBuf,
    /// Path to the original file (reconstructed from backup directory + name).
    pub original_path: PathBuf,
    /// Timestamp when backup was created (milliseconds since Unix epoch).
    pub timestamp: u64,
    /// Human-readable timestamp string.
    pub timestamp_str: String,
    /// Size of the backup file in bytes.
    pub size: u64,
}

impl BackupEntry {
    /// Check if the backup file still exists on disk.
    pub fn backup_exists(&self) -> bool {
        self.backup_path.exists()
    }

    /// Check if the original file has been modified since the backup was created.
    ///
    /// Returns `None` if the original file does not exist or its modification time
    /// cannot be determined.  Returns `Some(true)` if the file was modified after
    /// the backup timestamp (with a 1-second tolerance for filesystem precision).
    pub fn is_original_modified_since_backup(&self) -> Option<bool> {
        let metadata = fs::metadata(&self.original_path).ok()?;
        let modified = metadata.modified().ok()?;
        let modified_ms = modified.duration_since(UNIX_EPOCH).ok()?.as_millis() as u64;
        // 1-second tolerance for filesystem timestamp granularity
        Some(modified_ms > self.timestamp + 1000)
    }

    /// Get the modification time of the original file in milliseconds since epoch.
    pub fn get_original_modified_time(&self) -> Option<u64> {
        let metadata = fs::metadata(&self.original_path).ok()?;
        let modified = metadata.modified().ok()?;
        Some(modified.duration_since(UNIX_EPOCH).ok()?.as_millis() as u64)
    }

    /// Read the content of the backup file.
    pub fn read_backup_content(&self) -> io::Result<String> {
        fs::read_to_string(&self.backup_path)
    }

    /// Read the current content of the original file.
    pub fn read_original_content(&self) -> io::Result<String> {
        fs::read_to_string(&self.original_path)
    }
}

/// Summary of backups grouped by timestamp.
#[derive(Debug, Clone)]
pub struct TimestampSummary {
    /// The representative timestamp (milliseconds since Unix epoch).
    pub timestamp: u64,
    /// Human-readable timestamp string.
    pub timestamp_str: String,
    /// Number of files backed up at this timestamp.
    pub file_count: usize,
    /// Total size of all backups at this timestamp.
    pub total_size: u64,
    /// List of original file paths.
    pub files: Vec<PathBuf>,
}

/// Result of a revert operation.
#[derive(Debug, Clone)]
pub struct RevertResult_ {
    /// Files successfully reverted.
    pub reverted: Vec<PathBuf>,
    /// Files that failed to revert with error messages.
    pub failed: Vec<(PathBuf, String)>,
    /// Files that were skipped (e.g., backup missing, modified without --force).
    pub skipped: Vec<(PathBuf, String)>,
    /// Warnings (e.g., force-reverting a modified file).
    pub warnings: Vec<(PathBuf, String)>,
    /// Total bytes restored.
    pub bytes_restored: u64,
}

impl RevertResult_ {
    fn new() -> Self {
        Self {
            reverted: Vec::new(),
            failed: Vec::new(),
            skipped: Vec::new(),
            warnings: Vec::new(),
            bytes_restored: 0,
        }
    }

    /// Returns true if all operations succeeded (no failures).
    pub fn is_success(&self) -> bool {
        self.failed.is_empty()
    }

    /// Returns true if succeeded but produced warnings.
    pub fn is_success_with_warnings(&self) -> bool {
        self.failed.is_empty() && !self.warnings.is_empty()
    }

    /// Returns the total number of files processed.
    pub fn total_processed(&self) -> usize {
        self.reverted.len() + self.failed.len() + self.skipped.len()
    }
}

// =============================================================================
// CONFIGURATION
// =============================================================================

/// Configuration for revert operations.
#[derive(Debug, Clone)]
pub struct RevertConfig {
    /// Run in dry-run mode (no actual changes).
    pub dry_run: bool,
    /// Force revert even if files were modified since backup.
    pub force: bool,
    /// Timestamp tolerance for grouping/matching (milliseconds).
    pub timestamp_tolerance_ms: u64,
    /// Enable atomic mode (all-or-nothing revert with rollback).
    pub atomic: bool,
    /// Delete backup files after successful revert.
    pub delete_backups: bool,
}

impl Default for RevertConfig {
    fn default() -> Self {
        Self {
            dry_run: false,
            force: false,
            timestamp_tolerance_ms: DEFAULT_TIMESTAMP_TOLERANCE_MS,
            atomic: true,
            delete_backups: false,
        }
    }
}

impl RevertConfig {
    /// Create a dry-run configuration.
    pub fn dry_run() -> Self {
        Self {
            dry_run: true,
            ..Default::default()
        }
    }

    /// Create a forced-revert configuration.
    pub fn forced() -> Self {
        Self {
            force: true,
            ..Default::default()
        }
    }

    pub fn with_dry_run(mut self, v: bool) -> Self {
        self.dry_run = v;
        self
    }
    pub fn with_force(mut self, v: bool) -> Self {
        self.force = v;
        self
    }
    pub fn with_tolerance(mut self, ms: u64) -> Self {
        self.timestamp_tolerance_ms = ms;
        self
    }
    pub fn with_atomic(mut self, v: bool) -> Self {
        self.atomic = v;
        self
    }
    pub fn with_delete_backups(mut self, v: bool) -> Self {
        self.delete_backups = v;
        self
    }
}

// =============================================================================
// REVERT ENGINE
// =============================================================================

/// The main revert engine for managing backup restoration.
///
/// Supports atomic revert (all-or-nothing with rollback), modification detection,
/// timestamp tolerance grouping, and duplicate backup handling.
pub struct RevertEngine {
    /// Root paths to search for backups.
    search_paths: Vec<PathBuf>,
    /// Optional path filter (only revert files matching this prefix).
    path_filter: Option<PathBuf>,
    /// Revert configuration.
    config: RevertConfig,
}

impl RevertEngine {
    /// Create a new engine with the given search paths and default configuration.
    pub fn new(search_paths: Vec<PathBuf>) -> Self {
        Self {
            search_paths,
            path_filter: None,
            config: RevertConfig::default(),
        }
    }

    /// Create a new engine with explicit configuration.
    pub fn with_config(search_paths: Vec<PathBuf>, config: RevertConfig) -> Self {
        Self {
            search_paths,
            path_filter: None,
            config,
        }
    }

    /// Set a path filter to only revert files matching this prefix.
    pub fn with_path_filter(mut self, filter: PathBuf) -> Self {
        self.path_filter = Some(filter);
        self
    }

    // =========================================================================
    // DIRECTORY SCANNING
    // =========================================================================

    /// Find all `.fstar-lint-backups/` directories recursively under search paths.
    fn find_backup_dirs(&self) -> RevertResult<Vec<PathBuf>> {
        let mut backup_dirs = Vec::new();
        for search_path in &self.search_paths {
            self.find_backup_dirs_recursive(search_path, &mut backup_dirs)?;
        }
        Ok(backup_dirs)
    }

    fn find_backup_dirs_recursive(
        &self,
        dir: &Path,
        result: &mut Vec<PathBuf>,
    ) -> RevertResult<()> {
        if !dir.exists() || !dir.is_dir() {
            return Ok(());
        }

        let entries = fs::read_dir(dir).map_err(|e| RevertError::DirectoryReadFailed {
            path: dir.to_path_buf(),
            source: e,
        })?;

        for entry in entries.flatten() {
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }
            let name = match path.file_name().and_then(|n| n.to_str()) {
                Some(n) => n,
                None => continue,
            };
            if name == BACKUP_DIR_NAME {
                result.push(path);
            } else if !name.starts_with('.') && name != "target" && name != "node_modules" {
                self.find_backup_dirs_recursive(&path, result)?;
            }
        }

        Ok(())
    }

    // =========================================================================
    // FILENAME PARSING
    // =========================================================================

    /// Parse `{original_name}.{timestamp_ms}.bak` -> `(original_name, timestamp_ms)`.
    ///
    /// The original name may contain dots (e.g. `My.Module.fst`).
    fn parse_backup_filename(backup_path: &Path) -> RevertResult<(String, u64)> {
        let filename = backup_path
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or_else(|| RevertError::InvalidBackupFormat {
                filename: backup_path.display().to_string(),
            })?;

        if !filename.ends_with(".bak") {
            return Err(RevertError::InvalidBackupFormat {
                filename: filename.to_string(),
            });
        }

        let without_bak = &filename[..filename.len() - 4];
        let last_dot =
            without_bak
                .rfind('.')
                .ok_or_else(|| RevertError::InvalidBackupFormat {
                    filename: filename.to_string(),
                })?;

        let original_name = &without_bak[..last_dot];
        let timestamp_str = &without_bak[last_dot + 1..];

        if original_name.is_empty() {
            return Err(RevertError::InvalidBackupFormat {
                filename: filename.to_string(),
            });
        }

        let timestamp: u64 =
            timestamp_str
                .parse()
                .map_err(|_| RevertError::InvalidBackupFormat {
                    filename: filename.to_string(),
                })?;

        Ok((original_name.to_string(), timestamp))
    }

    // =========================================================================
    // TIMESTAMP FORMATTING
    // =========================================================================

    fn format_timestamp(timestamp_ms: u64) -> String {
        let duration = Duration::from_millis(timestamp_ms);
        let system_time = UNIX_EPOCH + duration;

        match system_time.duration_since(UNIX_EPOCH) {
            Ok(d) => {
                let secs = d.as_secs();
                let millis = d.subsec_millis();
                let days_since_epoch = secs / 86400;
                let secs_today = secs % 86400;
                let hours = secs_today / 3600;
                let minutes = (secs_today % 3600) / 60;
                let seconds = secs_today % 60;

                let mut year: u64 = 1970;
                let mut remaining_days = days_since_epoch;
                loop {
                    let days_in_year = if is_leap_year(year) { 366 } else { 365 };
                    if remaining_days < days_in_year {
                        break;
                    }
                    remaining_days -= days_in_year;
                    year += 1;
                }
                let (month, day) = days_to_month_day(remaining_days as u32, is_leap_year(year));

                format!(
                    "{:04}-{:02}-{:02} {:02}:{:02}:{:02}.{:03} UTC",
                    year, month, day, hours, minutes, seconds, millis
                )
            }
            Err(_) => format!("{}ms", timestamp_ms),
        }
    }

    // =========================================================================
    // BACKUP SCANNING
    // =========================================================================

    /// Scan all backup directories and collect backup entries, sorted newest-first.
    pub fn scan_backups(&self) -> RevertResult<Vec<BackupEntry>> {
        let backup_dirs = self.find_backup_dirs()?;
        let mut entries = Vec::new();

        for backup_dir in backup_dirs {
            let parent_dir = backup_dir.parent().unwrap_or(Path::new("."));

            let dir_entries = fs::read_dir(&backup_dir).map_err(|e| {
                RevertError::DirectoryReadFailed {
                    path: backup_dir.clone(),
                    source: e,
                }
            })?;

            for entry in dir_entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) != Some("bak") {
                    continue;
                }

                match Self::parse_backup_filename(&path) {
                    Ok((original_name, timestamp)) => {
                        let original_path = parent_dir.join(&original_name);

                        if let Some(ref filter) = self.path_filter {
                            if !original_path.starts_with(filter) {
                                continue;
                            }
                        }

                        let size = fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
                        entries.push(BackupEntry {
                            backup_path: path,
                            original_path,
                            timestamp,
                            timestamp_str: Self::format_timestamp(timestamp),
                            size,
                        });
                    }
                    Err(e) => {
                        debug!("Skipping invalid backup file: {:?}", e);
                    }
                }
            }
        }

        entries.sort_by_key(|b| std::cmp::Reverse(b.timestamp));
        Ok(entries)
    }

    // =========================================================================
    // TIMESTAMP GROUPING
    // =========================================================================

    /// Group entries by timestamp, collapsing entries within `tolerance_ms` of
    /// each other into a single group (chain tolerance).
    ///
    /// Returns groups sorted descending by representative timestamp (= minimum
    /// timestamp in the group).
    pub fn group_by_timestamp(
        entries: &[BackupEntry],
        tolerance_ms: u64,
    ) -> Vec<(u64, Vec<&BackupEntry>)> {
        if entries.is_empty() {
            return Vec::new();
        }

        let mut timestamps: Vec<u64> = entries.iter().map(|e| e.timestamp).collect();
        timestamps.sort_unstable();
        timestamps.dedup();

        // Greedy chain grouping: a new group starts when a timestamp is more
        // than `tolerance_ms` away from the previous timestamp.
        let mut ts_to_group: HashMap<u64, u64> = HashMap::new();
        let mut current_group_min: u64 = timestamps[0];
        let mut current_group_max: u64 = timestamps[0];
        ts_to_group.insert(timestamps[0], current_group_min);

        for &ts in timestamps.iter().skip(1) {
            if ts.saturating_sub(current_group_max) <= tolerance_ms {
                ts_to_group.insert(ts, current_group_min);
                current_group_max = ts;
            } else {
                current_group_min = ts;
                current_group_max = ts;
                ts_to_group.insert(ts, current_group_min);
            }
        }

        let mut result_map: BTreeMap<u64, Vec<&BackupEntry>> = BTreeMap::new();
        for entry in entries {
            let group_ts = ts_to_group
                .get(&entry.timestamp)
                .copied()
                .unwrap_or(entry.timestamp);
            result_map.entry(group_ts).or_default().push(entry);
        }

        let mut result: Vec<(u64, Vec<&BackupEntry>)> = result_map.into_iter().collect();
        result.sort_by_key(|b| std::cmp::Reverse(b.0));
        result
    }

    /// List unique timestamp groups with their summaries.
    pub fn list_timestamps(&self) -> RevertResult<Vec<TimestampSummary>> {
        let entries = self.scan_backups()?;
        let groups = Self::group_by_timestamp(&entries, self.config.timestamp_tolerance_ms);

        let summaries: Vec<TimestampSummary> = groups
            .into_iter()
            .map(|(timestamp, group)| {
                let total_size: u64 = group.iter().map(|e| e.size).sum();
                let files: Vec<PathBuf> = group.iter().map(|e| e.original_path.clone()).collect();
                TimestampSummary {
                    timestamp,
                    timestamp_str: Self::format_timestamp(timestamp),
                    file_count: group.len(),
                    total_size,
                    files,
                }
            })
            .collect();

        Ok(summaries)
    }

    /// Get the most recent timestamp.
    pub fn get_latest_timestamp(&self) -> RevertResult<Option<u64>> {
        let entries = self.scan_backups()?;
        Ok(entries.first().map(|e| e.timestamp))
    }

    /// Find the closest timestamp group to the given target.
    pub fn find_closest_timestamp(&self, target: u64) -> RevertResult<Option<u64>> {
        let summaries = self.list_timestamps()?;
        if summaries.is_empty() {
            return Ok(None);
        }
        let closest = summaries
            .iter()
            .min_by_key(|s| (s.timestamp as i128 - target as i128).unsigned_abs());
        Ok(closest.map(|s| s.timestamp))
    }

    // =========================================================================
    // DUPLICATE DETECTION
    // =========================================================================

    /// Deduplicate: when multiple backups exist for the same original file,
    /// keep only the one with the newest (largest) individual timestamp.
    fn deduplicate_entries<'a>(entries: &[&'a BackupEntry]) -> Vec<&'a BackupEntry> {
        let mut best: HashMap<&Path, &'a BackupEntry> = HashMap::new();
        let mut counts: HashMap<&Path, usize> = HashMap::new();

        for &entry in entries {
            let p = entry.original_path.as_path();
            *counts.entry(p).or_insert(0) += 1;
            match best.get(p) {
                Some(existing) if existing.timestamp >= entry.timestamp => {}
                _ => {
                    best.insert(p, entry);
                }
            }
        }

        for (path, count) in &counts {
            if *count > 1 {
                warn!(
                    "Found {} backups for {} in timestamp group, using newest",
                    count,
                    path.display()
                );
            }
        }

        let mut result: Vec<&'a BackupEntry> = best.into_values().collect();
        result.sort_by(|a, b| a.original_path.cmp(&b.original_path));
        result
    }

    // =========================================================================
    // VALIDATION
    // =========================================================================

    /// Validate entries before revert.  Returns:
    /// `(valid_with_content, skipped, warnings, hard_failures)`.
    ///
    /// In atomic mode, a missing backup or a modified-without-force file
    /// becomes a hard failure (blocks the entire revert).  In non-atomic mode
    /// it becomes a skip.
    fn validate_entries<'a>(
        &self,
        entries: &[&'a BackupEntry],
    ) -> ValidationResult<'a> {
        let mut valid = Vec::new();
        let mut skipped = Vec::new();
        let mut warnings = Vec::new();
        let mut failures = Vec::new();

        for &entry in entries {
            // Edge case: backup file no longer on disk
            if !entry.backup_exists() {
                let msg = format!("Backup file missing: {}", entry.backup_path.display());
                if self.config.atomic {
                    failures.push((entry.original_path.clone(), msg));
                } else {
                    skipped.push((entry.original_path.clone(), msg));
                }
                continue;
            }

            // Edge case: original file modified since backup
            if let Some(true) = entry.is_original_modified_since_backup() {
                if !self.config.force {
                    let file_mtime = entry.get_original_modified_time().unwrap_or(0);
                    let msg = format!(
                        "Modified since backup (backup={}, file={}). Use --force to override.",
                        entry.timestamp, file_mtime
                    );
                    if self.config.atomic {
                        failures.push((entry.original_path.clone(), msg));
                    } else {
                        skipped.push((entry.original_path.clone(), msg));
                    }
                    continue;
                }
                let file_mtime = entry.get_original_modified_time().unwrap_or(0);
                warnings.push((
                    entry.original_path.clone(),
                    format!(
                        "Force-reverting modified file (backup={}, file={})",
                        entry.timestamp, file_mtime
                    ),
                ));
            }

            // Read backup content
            match entry.read_backup_content() {
                Ok(content) => valid.push((entry, content)),
                Err(e) => {
                    let msg = format!("Failed to read backup: {}", e);
                    if self.config.atomic {
                        failures.push((entry.original_path.clone(), msg));
                    } else {
                        skipped.push((entry.original_path.clone(), msg));
                    }
                }
            }
        }

        (valid, skipped, warnings, failures)
    }

    // =========================================================================
    // CORE REVERT (ATOMIC / NON-ATOMIC)
    // =========================================================================

    /// Collect entries matching a timestamp (exact or within tolerance).
    fn collect_matching_entries<'a>(
        &self,
        all_entries: &'a [BackupEntry],
        timestamp: u64,
    ) -> RevertResult<Vec<&'a BackupEntry>> {
        let tolerance = self.config.timestamp_tolerance_ms;
        let groups = Self::group_by_timestamp(all_entries, tolerance);

        let matching = groups.into_iter().find(|(group_ts, _)| {
            let diff = if *group_ts > timestamp {
                group_ts - timestamp
            } else {
                timestamp - *group_ts
            };
            diff <= tolerance
        });

        match matching {
            Some((_, group)) => Ok(group),
            None => {
                let available: Vec<u64> = all_entries
                    .iter()
                    .map(|e| e.timestamp)
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                Err(RevertError::TimestampNotFound {
                    timestamp,
                    available,
                })
            }
        }
    }

    /// Execute the revert for a set of entries.
    ///
    /// In **atomic** mode (default):
    ///   1. Validate every entry.  Any validation failure aborts immediately.
    ///   2. Snapshot each original file's current content (for rollback).
    ///   3. Apply writes.  On the first write failure, roll back every file
    ///      that was already written.
    ///
    /// In **non-atomic** mode: each file is independent; failures are recorded
    /// but do not block other files.
    fn execute_revert(&self, entries: &[&BackupEntry]) -> RevertResult<RevertResult_> {
        let mut result = RevertResult_::new();
        let deduped = Self::deduplicate_entries(entries);

        // --- DRY-RUN ---
        if self.config.dry_run {
            for &entry in &deduped {
                if !entry.backup_exists() {
                    result.skipped.push((
                        entry.original_path.clone(),
                        format!("Backup file missing: {}", entry.backup_path.display()),
                    ));
                    continue;
                }
                if let Some(true) = entry.is_original_modified_since_backup() {
                    if !self.config.force {
                        result.skipped.push((
                            entry.original_path.clone(),
                            "Modified since backup (use --force)".to_string(),
                        ));
                        continue;
                    }
                    result.warnings.push((
                        entry.original_path.clone(),
                        "Would force-revert modified file".to_string(),
                    ));
                }
                result.reverted.push(entry.original_path.clone());
                result.bytes_restored += entry.size;
            }
            return Ok(result);
        }

        // --- VALIDATION ---
        let (valid, skipped, warnings, failures) = self.validate_entries(&deduped);
        result.skipped = skipped;
        result.warnings = warnings;

        if self.config.atomic && !failures.is_empty() {
            return Err(RevertError::BatchErrors { errors: failures });
        }
        if !failures.is_empty() {
            result.failed.extend(failures);
        }
        if valid.is_empty() {
            return Ok(result);
        }

        // --- SNAPSHOT (for atomic rollback) ---
        let snapshots: Vec<(PathBuf, Option<String>)> = if self.config.atomic {
            valid
                .iter()
                .map(|(entry, _)| {
                    let current = entry.read_original_content().ok();
                    (entry.original_path.clone(), current)
                })
                .collect()
        } else {
            Vec::new()
        };

        // --- APPLY WRITES ---
        let mut reverted_paths: Vec<PathBuf> = Vec::new();
        let mut apply_error: Option<(PathBuf, String)> = None;

        for (entry, content) in &valid {
            match atomic_write(&entry.original_path, content) {
                Ok(()) => {
                    info!("Reverted: {}", entry.original_path.display());
                    reverted_paths.push(entry.original_path.clone());
                    result.bytes_restored += entry.size;
                }
                Err(e) => {
                    let msg = e.to_string();
                    error!(
                        "Failed to revert {}: {}",
                        entry.original_path.display(),
                        msg
                    );
                    if self.config.atomic {
                        apply_error = Some((entry.original_path.clone(), msg));
                        break;
                    }
                    result.failed.push((entry.original_path.clone(), msg));
                }
            }
        }

        // --- ATOMIC ROLLBACK on failure ---
        if let Some((failed_path, err_msg)) = apply_error {
            warn!(
                "Atomic revert failed at {}; rolling back {} file(s)",
                failed_path.display(),
                reverted_paths.len()
            );

            let mut rollback_failures: Vec<(PathBuf, String)> = Vec::new();
            for (path, snapshot) in &snapshots {
                if !reverted_paths.contains(path) {
                    continue;
                }
                let rb = match snapshot {
                    Some(content) => atomic_write(path, content),
                    None => fs::remove_file(path),
                };
                if let Err(re) = rb {
                    rollback_failures.push((path.clone(), re.to_string()));
                } else {
                    debug!("Rolled back: {}", path.display());
                }
            }

            if !rollback_failures.is_empty() {
                return Err(RevertError::RollbackFailed {
                    original_error: err_msg,
                    rollback_failures,
                });
            }

            return Err(RevertError::AtomicRevertFailed {
                reason: "Write failed during atomic revert".to_string(),
                reverted_before_failure: reverted_paths,
                failed_file: failed_path,
                error: err_msg,
            });
        }

        result.reverted = reverted_paths;

        // --- DELETE BACKUPS (optional, post-success) ---
        if self.config.delete_backups {
            for (entry, _) in &valid {
                if result.reverted.contains(&entry.original_path) {
                    if let Err(e) = fs::remove_file(&entry.backup_path) {
                        warn!(
                            "Failed to delete backup {}: {}",
                            entry.backup_path.display(),
                            e
                        );
                    } else {
                        debug!("Deleted backup: {}", entry.backup_path.display());
                    }
                }
            }
        }

        Ok(result)
    }

    // =========================================================================
    // PUBLIC API
    // =========================================================================

    /// Revert files to a specific timestamp.
    ///
    /// `dry_run` is OR-ed with `config.dry_run` for backward compatibility.
    pub fn revert_to_timestamp(
        &self,
        timestamp: u64,
        dry_run: bool,
    ) -> RevertResult<RevertResult_> {
        let effective = RevertEngine {
            search_paths: self.search_paths.clone(),
            path_filter: self.path_filter.clone(),
            config: RevertConfig {
                dry_run: dry_run || self.config.dry_run,
                ..self.config.clone()
            },
        };
        let entries = effective.scan_backups()?;
        let matching = effective.collect_matching_entries(&entries, timestamp)?;
        effective.execute_revert(&matching)
    }

    /// Revert to the most recent backup.
    pub fn revert_to_latest(&self, dry_run: bool) -> RevertResult<RevertResult_> {
        let latest = self.get_latest_timestamp()?;
        match latest {
            Some(ts) => self.revert_to_timestamp(ts, dry_run),
            None => Err(RevertError::NoBackupsFound {
                path: self.search_paths.first().cloned().unwrap_or_default(),
                reason: "No backup files found".to_string(),
            }),
        }
    }

    /// Best-effort revert: find the closest timestamp to `target` and revert.
    ///
    /// Returns `(actual_timestamp_used, result)`.
    pub fn revert_best_effort(
        &self,
        target: u64,
        dry_run: bool,
    ) -> RevertResult<(u64, RevertResult_)> {
        let closest = self.find_closest_timestamp(target)?;
        match closest {
            Some(ts) => {
                let result = self.revert_to_timestamp(ts, dry_run)?;
                Ok((ts, result))
            }
            None => Err(RevertError::NoBackupsFound {
                path: self.search_paths.first().cloned().unwrap_or_default(),
                reason: "No backup files found".to_string(),
            }),
        }
    }
}

// =============================================================================
// ATOMIC WRITE HELPER
// =============================================================================

/// Write content to a temp file then rename (atomic on POSIX).
fn atomic_write(path: &Path, content: &str) -> io::Result<()> {
    let parent = path.parent().unwrap_or(Path::new("."));
    if !parent.exists() {
        fs::create_dir_all(parent)?;
    }

    let temp_path = parent.join(format!(
        ".{}.{}.tmp",
        path.file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("file"),
        std::process::id()
    ));

    {
        let mut file = fs::File::create(&temp_path)?;
        file.write_all(content.as_bytes())?;
        file.sync_all()?;
    }

    fs::rename(&temp_path, path)?;
    Ok(())
}

// =============================================================================
// DATE HELPERS
// =============================================================================

fn is_leap_year(year: u64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

fn days_to_month_day(day_of_year: u32, leap: bool) -> (u32, u32) {
    let days_in_months: [u32; 12] = if leap {
        [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    } else {
        [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    };

    let mut remaining = day_of_year;
    for (i, &days) in days_in_months.iter().enumerate() {
        if remaining < days {
            return ((i + 1) as u32, remaining + 1);
        }
        remaining -= days;
    }
    (12, 31)
}

/// Format file size in human-readable form.
pub fn format_size(bytes: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = KB * 1024;
    const GB: u64 = MB * 1024;

    if bytes >= GB {
        format!("{:.2} GB", bytes as f64 / GB as f64)
    } else if bytes >= MB {
        format!("{:.2} MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.2} KB", bytes as f64 / KB as f64)
    } else {
        format!("{} B", bytes)
    }
}

// =============================================================================
// BACKUP METADATA (serde-serialised alongside backups)
// =============================================================================

const METADATA_FILE_NAME: &str = ".metadata.json";

/// Metadata about a single backup operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BackupMetadata {
    pub id: String,
    pub timestamp_ms: u64,
    pub timestamp_human: String,
    pub files: HashMap<String, String>,
    pub command: String,
    pub git_commit: Option<String>,
    pub git_branch: Option<String>,
    pub name: Option<String>,
    pub total_size_bytes: u64,
}

impl BackupMetadata {
    pub fn new(command: &str) -> Self {
        let now_ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64;

        Self {
            id: format!("backup_{}", now_ms),
            timestamp_ms: now_ms,
            timestamp_human: RevertEngine::format_timestamp(now_ms),
            files: HashMap::new(),
            command: command.to_string(),
            git_commit: get_git_info("rev-parse", &["HEAD"]),
            git_branch: get_git_info("rev-parse", &["--abbrev-ref", "HEAD"]),
            name: None,
            total_size_bytes: 0,
        }
    }

    pub fn add_file(&mut self, original: &Path, backup: &Path, size: u64) {
        self.files.insert(
            original.display().to_string(),
            backup.display().to_string(),
        );
        self.total_size_bytes += size;
    }

    pub fn with_name(mut self, name: &str) -> Self {
        self.name = Some(name.to_string());
        self
    }

    pub fn age(&self) -> Duration {
        let now_ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64;
        Duration::from_millis(now_ms.saturating_sub(self.timestamp_ms))
    }

    pub fn age_string(&self) -> String {
        format_duration_short(self.age())
    }
}

/// Named revert point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevertPoint {
    pub name: String,
    pub description: Option<String>,
    pub created_at_ms: u64,
    pub backup_id: String,
    pub files: Vec<String>,
}

/// Root metadata stored in `.fstar-lint-backups/.metadata.json`.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BackupDirectoryMetadata {
    pub version: u32,
    pub backups: Vec<BackupMetadata>,
    pub revert_points: Vec<RevertPoint>,
}

impl BackupDirectoryMetadata {
    pub const CURRENT_VERSION: u32 = 1;

    pub fn new() -> Self {
        Self {
            version: Self::CURRENT_VERSION,
            backups: Vec::new(),
            revert_points: Vec::new(),
        }
    }

    /// Record a backup, coalescing with the previous entry if the same command
    /// was run within 5 seconds.
    pub fn record_backup(&mut self, mut meta: BackupMetadata) {
        let coalesce_window_ms = 5_000;
        let should_merge = self.backups.last().is_some_and(|last| {
            meta.timestamp_ms.saturating_sub(last.timestamp_ms) < coalesce_window_ms
                && last.command == meta.command
        });

        if should_merge {
            if let Some(last) = self.backups.last_mut() {
                for (k, v) in meta.files.drain() {
                    last.files.insert(k, v);
                }
                last.total_size_bytes += meta.total_size_bytes;
            }
        } else {
            self.backups.push(meta);
        }
    }

    pub fn find_revert_point(&self, name: &str) -> Option<&RevertPoint> {
        self.revert_points.iter().find(|p| p.name == name)
    }

    pub fn find_backup_for_point(&self, point: &RevertPoint) -> Option<&BackupMetadata> {
        self.backups.iter().find(|b| b.id == point.backup_id)
    }

    pub fn add_revert_point(&mut self, point: RevertPoint) {
        self.revert_points.retain(|p| p.name != point.name);
        self.revert_points.push(point);
    }

    pub fn prune_older_than(
        &mut self,
        max_age: Duration,
        include_named: bool,
    ) -> Vec<BackupMetadata> {
        let cutoff_ms = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64
            - max_age.as_millis() as u64;

        let (old, recent): (Vec<_>, Vec<_>) = self.backups.drain(..).partition(|b| {
            b.timestamp_ms < cutoff_ms && (include_named || b.name.is_none())
        });

        let old_ids: HashSet<String> = old.iter().map(|b| b.id.clone()).collect();
        self.backups = recent;
        self.revert_points
            .retain(|p| !old_ids.contains(&p.backup_id));
        old
    }
}

// =============================================================================
// METADATA I/O
// =============================================================================

pub fn load_metadata(dir: &Path) -> Result<BackupDirectoryMetadata, String> {
    let metadata_path = dir.join(BACKUP_DIR_NAME).join(METADATA_FILE_NAME);
    if !metadata_path.exists() {
        return Ok(BackupDirectoryMetadata::new());
    }
    let content = fs::read_to_string(&metadata_path)
        .map_err(|e| format!("read {}: {}", metadata_path.display(), e))?;
    serde_json::from_str(&content)
        .map_err(|e| format!("parse {}: {}", metadata_path.display(), e))
}

pub fn save_metadata(dir: &Path, metadata: &BackupDirectoryMetadata) -> Result<(), String> {
    let backup_dir = dir.join(BACKUP_DIR_NAME);
    if !backup_dir.exists() {
        fs::create_dir_all(&backup_dir)
            .map_err(|e| format!("mkdir {}: {}", backup_dir.display(), e))?;
    }
    let metadata_path = backup_dir.join(METADATA_FILE_NAME);
    let json = serde_json::to_string_pretty(metadata)
        .map_err(|e| format!("serialize metadata: {}", e))?;
    fs::write(&metadata_path, json)
        .map_err(|e| format!("write {}: {}", metadata_path.display(), e))
}

pub fn record_backup_in_metadata(
    dir: &Path,
    original: &Path,
    backup: &Path,
    command: &str,
) -> Result<(), String> {
    let mut metadata = load_metadata(dir).unwrap_or_else(|_| BackupDirectoryMetadata::new());
    let size = fs::metadata(backup).map(|m| m.len()).unwrap_or(0);
    let mut entry = BackupMetadata::new(command);
    entry.add_file(original, backup, size);
    metadata.record_backup(entry);
    save_metadata(dir, &metadata)
}

// =============================================================================
// NAMED REVERT POINTS
// =============================================================================

impl RevertEngine {
    /// Create a named revert point from the latest backup of each file.
    pub fn create_revert_point(
        &self,
        name: &str,
        description: Option<&str>,
    ) -> RevertResult<RevertPoint> {
        let entries = self.scan_backups()?;
        let root = self.search_paths.first().cloned().unwrap_or_default();
        let mut metadata =
            load_metadata(&root).unwrap_or_else(|_| BackupDirectoryMetadata::new());

        let mut latest_by_file: HashMap<PathBuf, &BackupEntry> = HashMap::new();
        for entry in &entries {
            latest_by_file
                .entry(entry.original_path.clone())
                .and_modify(|e| {
                    if entry.timestamp > e.timestamp {
                        *e = entry;
                    }
                })
                .or_insert(entry);
        }

        let mut backup_meta =
            BackupMetadata::new(&format!("revert-point:{}", name)).with_name(name);

        for (original, entry) in &latest_by_file {
            backup_meta.add_file(original, &entry.backup_path, entry.size);
        }

        let point = RevertPoint {
            name: name.to_string(),
            description: description.map(|s| s.to_string()),
            created_at_ms: backup_meta.timestamp_ms,
            backup_id: backup_meta.id.clone(),
            files: latest_by_file
                .keys()
                .map(|p| p.display().to_string())
                .collect(),
        };

        metadata.record_backup(backup_meta);
        metadata.add_revert_point(point.clone());

        save_metadata(&root, &metadata).map_err(|e| RevertError::NoBackupsFound {
            path: root,
            reason: e,
        })?;

        info!(
            "Created revert point '{}' with {} files",
            name,
            latest_by_file.len()
        );
        Ok(point)
    }

    /// Revert to a named revert point.
    pub fn revert_to_point(
        &self,
        point_name: &str,
        dry_run: bool,
    ) -> RevertResult<RevertResult_> {
        let root = self.search_paths.first().cloned().unwrap_or_default();
        let metadata = load_metadata(&root).map_err(|e| RevertError::NoBackupsFound {
            path: root.clone(),
            reason: e,
        })?;

        let point =
            metadata
                .find_revert_point(point_name)
                .ok_or_else(|| RevertError::NoBackupsFound {
                    path: root.clone(),
                    reason: format!("Revert point '{}' not found", point_name),
                })?;

        let backup =
            metadata
                .find_backup_for_point(point)
                .ok_or_else(|| RevertError::NoBackupsFound {
                    path: root.clone(),
                    reason: format!(
                        "Backup data for point '{}' (id: {}) not found",
                        point_name, point.backup_id
                    ),
                })?;

        let mut result = RevertResult_::new();

        for (original_str, backup_str) in &backup.files {
            let original_path = PathBuf::from(original_str);
            let backup_path = PathBuf::from(backup_str);

            if !backup_path.exists() {
                result
                    .failed
                    .push((original_path, "backup file missing".to_string()));
                continue;
            }

            if dry_run {
                result.reverted.push(original_path);
                continue;
            }

            match fs::read_to_string(&backup_path) {
                Ok(content) => {
                    let size = content.len() as u64;
                    match atomic_write(&original_path, &content) {
                        Ok(()) => {
                            info!(
                                "Reverted {} from point '{}'",
                                original_str, point_name
                            );
                            result.reverted.push(original_path);
                            result.bytes_restored += size;
                        }
                        Err(e) => {
                            result.failed.push((original_path, e.to_string()));
                        }
                    }
                }
                Err(e) => {
                    result.failed.push((original_path, e.to_string()));
                }
            }
        }

        Ok(result)
    }

    /// Interactive revert -- prompt per file.
    pub fn revert_interactive(&self, timestamp: u64) -> RevertResult<RevertResult_> {
        let entries = self.scan_backups()?;
        let matching: Vec<&BackupEntry> =
            entries.iter().filter(|e| e.timestamp == timestamp).collect();

        if matching.is_empty() {
            let available: Vec<u64> = entries
                .iter()
                .map(|e| e.timestamp)
                .collect::<HashSet<_>>()
                .into_iter()
                .collect();
            return Err(RevertError::TimestampNotFound {
                timestamp,
                available,
            });
        }

        let mut result = RevertResult_::new();

        println!();
        println!(
            "Interactive revert for timestamp {}",
            RevertEngine::format_timestamp(timestamp)
        );
        println!("{}", "-".repeat(60));
        println!("For each file, enter: y=revert, n=skip, q=quit");
        println!();

        for entry in &matching {
            let modified_indicator = match entry.is_original_modified_since_backup() {
                Some(true) => " [MODIFIED since backup]",
                _ => "",
            };

            print!(
                "  {} ({}){} -> [y/n/q]: ",
                entry.original_path.display(),
                format_size(entry.size),
                modified_indicator,
            );
            io::stdout().flush().unwrap_or(());

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                result
                    .skipped
                    .push((entry.original_path.clone(), "stdin error".to_string()));
                continue;
            }

            match input.trim().to_lowercase().as_str() {
                "y" | "yes" => match fs::read_to_string(&entry.backup_path) {
                    Ok(content) => {
                        let size = content.len() as u64;
                        match atomic_write(&entry.original_path, &content) {
                            Ok(()) => {
                                result.reverted.push(entry.original_path.clone());
                                result.bytes_restored += size;
                                info!("Reverted: {}", entry.original_path.display());
                            }
                            Err(e) => {
                                result
                                    .failed
                                    .push((entry.original_path.clone(), e.to_string()));
                            }
                        }
                    }
                    Err(e) => {
                        result.failed.push((
                            entry.original_path.clone(),
                            format!("Failed to read backup: {}", e),
                        ));
                    }
                },
                "q" | "quit" => {
                    info!("User aborted interactive revert");
                    break;
                }
                _ => {
                    result
                        .skipped
                        .push((entry.original_path.clone(), "user skipped".to_string()));
                }
            }
        }

        Ok(result)
    }
}

// =============================================================================
// CLEANUP
// =============================================================================

/// Summary of a cleanup operation.
#[derive(Debug, Default)]
pub struct CleanupSummary {
    pub removed: usize,
    pub would_remove: usize,
    pub freed_bytes: u64,
    pub would_free_bytes: u64,
    pub failed: usize,
}

/// Parse a human-readable duration string like "7d", "24h", "30m", "60s".
pub fn parse_duration_str(s: &str) -> Result<Duration, String> {
    let s = s.trim();
    if s.is_empty() {
        return Err("empty duration string".to_string());
    }
    let (num_str, unit) = s.split_at(s.len() - 1);
    let num: u64 =
        num_str
            .parse()
            .map_err(|_| format!("invalid number in duration: '{}'", s))?;
    let secs = match unit {
        "s" => num,
        "m" => num * 60,
        "h" => num * 3600,
        "d" => num * 86400,
        "w" => num * 86400 * 7,
        _ => return Err(format!("unknown duration unit '{}'. Use s/m/h/d/w", unit)),
    };
    Ok(Duration::from_secs(secs))
}

/// Cleanup old backups across all discovered backup directories.
pub fn cleanup_old_backups(
    search_paths: &[PathBuf],
    max_age: Duration,
    dry_run: bool,
) -> RevertResult<CleanupSummary> {
    let engine = RevertEngine::new(search_paths.to_vec());
    let entries = engine.scan_backups()?;

    let cutoff_ms = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
        - max_age.as_millis() as u64;

    let mut summary = CleanupSummary::default();
    let mut affected_dirs: HashSet<PathBuf> = HashSet::new();

    for entry in &entries {
        if entry.timestamp >= cutoff_ms {
            continue;
        }
        if dry_run {
            summary.would_remove += 1;
            summary.would_free_bytes += entry.size;
        } else {
            match fs::remove_file(&entry.backup_path) {
                Ok(()) => {
                    debug!("Removed old backup: {}", entry.backup_path.display());
                    summary.removed += 1;
                    summary.freed_bytes += entry.size;
                    if let Some(parent) = entry.backup_path.parent() {
                        if let Some(dir) = parent.parent() {
                            affected_dirs.insert(dir.to_path_buf());
                        }
                    }
                }
                Err(e) => {
                    warn!("Failed to remove {}: {}", entry.backup_path.display(), e);
                    summary.failed += 1;
                }
            }
        }
    }

    if !dry_run {
        for dir in &affected_dirs {
            if let Ok(mut metadata) = load_metadata(dir) {
                metadata.prune_older_than(max_age, false);
                let _ = save_metadata(dir, &metadata);
            }
        }
    }

    Ok(summary)
}

/// Print cleanup summary.
pub fn print_cleanup_summary(summary: &CleanupSummary, dry_run: bool) {
    println!();
    if dry_run {
        println!("Cleanup Preview (DRY RUN)");
        println!("{}", "=".repeat(60));
        println!(
            "Would remove {} backup(s), freeing {}",
            summary.would_remove,
            format_size(summary.would_free_bytes)
        );
    } else if summary.removed > 0 {
        println!("Cleanup Complete");
        println!("{}", "=".repeat(60));
        println!(
            "Removed {} backup(s), freed {}",
            summary.removed,
            format_size(summary.freed_bytes)
        );
    } else {
        println!("No old backups to remove.");
    }
    if summary.failed > 0 {
        println!("Failed to remove {} backup(s)", summary.failed);
    }
    println!();
}

// =============================================================================
// BACKUP SUMMARY INFO
// =============================================================================

/// Summary about available backups.
#[derive(Debug, Default)]
pub struct BackupSummaryInfo {
    pub total_backups: usize,
    pub unique_files: usize,
    pub total_bytes: u64,
    pub revert_point_count: usize,
    pub revert_point_names: Vec<String>,
}

pub fn gather_backup_summary(search_paths: &[PathBuf]) -> BackupSummaryInfo {
    let engine = RevertEngine::new(search_paths.to_vec());
    let entries = match engine.scan_backups() {
        Ok(e) => e,
        Err(_) => return BackupSummaryInfo::default(),
    };

    let unique_files: HashSet<_> = entries.iter().map(|e| &e.original_path).collect();
    let total_bytes: u64 = entries.iter().map(|e| e.size).sum();

    let root = search_paths.first().cloned().unwrap_or_default();
    let metadata = load_metadata(&root).unwrap_or_default();

    BackupSummaryInfo {
        total_backups: entries.len(),
        unique_files: unique_files.len(),
        total_bytes,
        revert_point_count: metadata.revert_points.len(),
        revert_point_names: metadata
            .revert_points
            .iter()
            .map(|p| p.name.clone())
            .collect(),
    }
}

pub fn print_backup_summary_line(info: &BackupSummaryInfo) {
    if info.total_backups == 0 {
        return;
    }
    print!(
        "Backups: {} file(s), {} total",
        info.unique_files,
        format_size(info.total_bytes)
    );
    if info.revert_point_count > 0 {
        print!(", {} revert point(s)", info.revert_point_count);
    }
    println!(". Use `brrr-lint revert --list` to view.");
}

// =============================================================================
// HELPERS
// =============================================================================

fn get_git_info(subcommand: &str, args: &[&str]) -> Option<String> {
    let mut cmd = std::process::Command::new("git");
    cmd.arg(subcommand);
    for a in args {
        cmd.arg(a);
    }
    cmd.output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

fn format_duration_short(d: Duration) -> String {
    let secs = d.as_secs();
    if secs < 60 {
        format!("{}s ago", secs)
    } else if secs < 3600 {
        format!("{}m ago", secs / 60)
    } else if secs < 86400 {
        format!("{}h ago", secs / 3600)
    } else {
        format!("{}d ago", secs / 86400)
    }
}

// =============================================================================
// DISPLAY / PRINT HELPERS
// =============================================================================

pub fn print_timestamp_list(summaries: &[TimestampSummary]) {
    if summaries.is_empty() {
        println!("No backups found.");
        return;
    }

    println!();
    println!("Available backup timestamps:");
    println!("{}", "=".repeat(80));
    println!(
        "{:<20} {:>10} {:>12}   DATETIME (UTC)",
        "TIMESTAMP (ms)", "FILES", "SIZE"
    );
    println!("{}", "-".repeat(80));

    for summary in summaries {
        println!(
            "{:<20} {:>10} {:>12}   {}",
            summary.timestamp,
            summary.file_count,
            format_size(summary.total_size),
            summary.timestamp_str
        );
    }

    println!("{}", "-".repeat(80));
    println!("Total: {} timestamps", summaries.len());
    println!();
    println!("To revert to a timestamp, run:");
    println!("  brrr-lint revert --timestamp <TIMESTAMP>");
    println!();
}

pub fn print_timestamp_list_with_points(
    summaries: &[TimestampSummary],
    search_paths: &[PathBuf],
) {
    print_timestamp_list(summaries);

    let root = search_paths.first().cloned().unwrap_or_default();
    if let Ok(metadata) = load_metadata(&root) {
        if !metadata.revert_points.is_empty() {
            println!("Named Revert Points:");
            println!("{}", "=".repeat(60));
            for point in &metadata.revert_points {
                let age_ms = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_millis() as u64
                    - point.created_at_ms;
                let age = format_duration_short(Duration::from_millis(age_ms));
                println!(
                    "  {:20} {} ({} files)",
                    point.name,
                    age,
                    point.files.len()
                );
                if let Some(ref desc) = point.description {
                    println!("                       {}", desc);
                }
            }
            println!();
            println!("To revert to a named point:");
            println!("  brrr-lint revert --to-point <NAME>");
            println!();
        }

        if let Some(last) = metadata.backups.last() {
            println!("Last backup:");
            println!("  Command: {}", last.command);
            println!("  Time:    {}", last.timestamp_human);
            if let Some(ref hash) = last.git_commit {
                println!("  Commit:  {}", &hash[..hash.len().min(12)]);
            }
            if let Some(ref branch) = last.git_branch {
                println!("  Branch:  {}", branch);
            }
            println!();
        }
    }
}

pub fn print_revert_result(result: &RevertResult_, dry_run: bool) {
    let mode_str = if dry_run { " (DRY RUN)" } else { "" };

    println!();
    if dry_run {
        println!("Revert Preview{}", mode_str);
        println!("{}", "=".repeat(60));
        println!("The following files WOULD be reverted:");
    } else {
        println!("Revert Complete{}", mode_str);
        println!("{}", "=".repeat(60));
    }

    if !result.reverted.is_empty() {
        println!();
        if dry_run {
            println!("Would revert {} file(s):", result.reverted.len());
        } else {
            println!("Successfully reverted {} file(s):", result.reverted.len());
        }
        for path in &result.reverted {
            println!("  - {}", path.display());
        }
    }

    if !result.warnings.is_empty() {
        println!();
        println!("Warnings ({}):", result.warnings.len());
        for (path, msg) in &result.warnings {
            println!("  - {}: {}", path.display(), msg);
        }
    }

    if !result.skipped.is_empty() {
        println!();
        println!("Skipped {} file(s):", result.skipped.len());
        for (path, reason) in &result.skipped {
            println!("  - {}: {}", path.display(), reason);
        }
    }

    if !result.failed.is_empty() {
        println!();
        println!("Failed to revert {} file(s):", result.failed.len());
        for (path, error) in &result.failed {
            println!("  - {}: {}", path.display(), error);
        }
    }

    if result.bytes_restored > 0 {
        println!();
        println!("Total bytes restored: {}", format_size(result.bytes_restored));
    }

    println!();
    if dry_run {
        println!("To actually revert, run without --dry-run");
    }
}

pub fn print_backup_details(entries: &[BackupEntry], timestamp: u64) {
    let matching: Vec<&BackupEntry> = entries.iter().filter(|e| e.timestamp == timestamp).collect();

    if matching.is_empty() {
        println!("No backups found for timestamp {}", timestamp);
        return;
    }

    let Some(first) = matching.first() else { return };
    println!();
    println!("Backup details for timestamp {}", timestamp);
    println!("Created: {}", first.timestamp_str);
    println!("{}", "=".repeat(60));
    println!("{:<50} {:>10}", "FILE", "SIZE");
    println!("{}", "-".repeat(60));

    let total_size: u64 = matching.iter().map(|e| e.size).sum();
    for entry in &matching {
        println!(
            "{:<50} {:>10}",
            entry.original_path.display(),
            format_size(entry.size)
        );
    }

    println!("{}", "-".repeat(60));
    println!(
        "Total: {} file(s), {}",
        matching.len(),
        format_size(total_size)
    );
    println!();
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    /// Create a standard backup structure for tests.
    ///
    /// Layout:
    ///   <temp>/src/.fstar-lint-backups/test.fst.1706000000000.bak
    ///   <temp>/src/.fstar-lint-backups/test.fst.1706000001000.bak
    ///   <temp>/src/.fstar-lint-backups/other.fsti.1706000001000.bak
    fn create_backup_structure(temp_dir: &TempDir) -> PathBuf {
        let src_dir = temp_dir.path().join("src");
        let backup_dir = src_dir.join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        fs::write(
            backup_dir.join("test.fst.1706000000000.bak"),
            "backup content 1",
        )
        .unwrap();
        fs::write(
            backup_dir.join("test.fst.1706000001000.bak"),
            "backup content 2",
        )
        .unwrap();
        fs::write(
            backup_dir.join("other.fsti.1706000001000.bak"),
            "other backup",
        )
        .unwrap();

        src_dir
    }

    // =====================================================================
    // FILENAME PARSING
    // =====================================================================

    #[test]
    fn test_parse_backup_filename() {
        let path = PathBuf::from("/some/path/.fstar-lint-backups/test.fst.1706123456789.bak");
        let (name, ts) = RevertEngine::parse_backup_filename(&path).unwrap();
        assert_eq!(name, "test.fst");
        assert_eq!(ts, 1706123456789);
    }

    #[test]
    fn test_parse_backup_filename_with_dots() {
        let path =
            PathBuf::from("/path/.fstar-lint-backups/my.module.name.fst.1706123456789.bak");
        let (name, ts) = RevertEngine::parse_backup_filename(&path).unwrap();
        assert_eq!(name, "my.module.name.fst");
        assert_eq!(ts, 1706123456789);
    }

    #[test]
    fn test_parse_backup_filename_invalid_no_bak() {
        let path = PathBuf::from("/path/.fstar-lint-backups/file.fst.123.txt");
        assert!(RevertEngine::parse_backup_filename(&path).is_err());
    }

    #[test]
    fn test_parse_backup_filename_invalid_no_dot() {
        let path = PathBuf::from("/path/.fstar-lint-backups/invalid.bak");
        assert!(RevertEngine::parse_backup_filename(&path).is_err());
    }

    #[test]
    fn test_parse_backup_filename_invalid_empty_name() {
        let path = PathBuf::from("/path/.fstar-lint-backups/.123.bak");
        assert!(RevertEngine::parse_backup_filename(&path).is_err());
    }

    #[test]
    fn test_parse_backup_filename_invalid_non_numeric_ts() {
        let path = PathBuf::from("/path/.fstar-lint-backups/file.fst.abc.bak");
        assert!(RevertEngine::parse_backup_filename(&path).is_err());
    }

    // =====================================================================
    // SCANNING
    // =====================================================================

    #[test]
    fn test_scan_backups() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        let engine = RevertEngine::new(vec![src_dir]);
        let entries = engine.scan_backups().unwrap();

        assert_eq!(entries.len(), 3);
        // Newest first
        assert!(entries[0].timestamp >= entries[1].timestamp);
    }

    #[test]
    fn test_scan_backups_nested() {
        let temp_dir = TempDir::new().unwrap();
        let deep = temp_dir
            .path()
            .join("a")
            .join("b")
            .join("c")
            .join(BACKUP_DIR_NAME);
        fs::create_dir_all(&deep).unwrap();
        fs::write(deep.join("deep.fst.1234.bak"), "deep").unwrap();

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let entries = engine.scan_backups().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].timestamp, 1234);
    }

    #[test]
    fn test_scan_backups_empty_dir() {
        let temp_dir = TempDir::new().unwrap();
        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let entries = engine.scan_backups().unwrap();
        assert!(entries.is_empty());
    }

    // =====================================================================
    // TIMESTAMP GROUPING
    // =====================================================================

    #[test]
    fn test_group_by_timestamp_exact() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);
        let engine = RevertEngine::new(vec![src_dir]);
        let entries = engine.scan_backups().unwrap();

        // With 0 tolerance, exact match only
        let groups = RevertEngine::group_by_timestamp(&entries, 0);
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_group_by_timestamp_within_tolerance() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Three files within 90ms of each other
        fs::write(backup_dir.join("a.fst.1000.bak"), "a").unwrap();
        fs::write(backup_dir.join("b.fst.1050.bak"), "b").unwrap();
        fs::write(backup_dir.join("c.fst.1090.bak"), "c").unwrap();
        // One file 1 second later
        fs::write(backup_dir.join("d.fst.2100.bak"), "d").unwrap();

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let entries = engine.scan_backups().unwrap();

        let groups = RevertEngine::group_by_timestamp(&entries, 100);
        assert_eq!(groups.len(), 2, "should produce 2 groups");

        // Newest group (2100) has 1 entry
        assert_eq!(groups[0].1.len(), 1);
        // Older group (1000-1090) has 3 entries
        assert_eq!(groups[1].1.len(), 3);
    }

    #[test]
    fn test_group_by_timestamp_chain_tolerance() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Chain: 1000, 1050, 1100, 1150 -- each within 100ms of previous
        fs::write(backup_dir.join("a.fst.1000.bak"), "a").unwrap();
        fs::write(backup_dir.join("b.fst.1050.bak"), "b").unwrap();
        fs::write(backup_dir.join("c.fst.1100.bak"), "c").unwrap();
        fs::write(backup_dir.join("d.fst.1150.bak"), "d").unwrap();

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let entries = engine.scan_backups().unwrap();

        let groups = RevertEngine::group_by_timestamp(&entries, 100);
        assert_eq!(groups.len(), 1, "all within chain tolerance -> 1 group");
        assert_eq!(groups[0].1.len(), 4);
    }

    #[test]
    fn test_group_by_timestamp_empty() {
        let groups = RevertEngine::group_by_timestamp(&[], 100);
        assert!(groups.is_empty());
    }

    // =====================================================================
    // DUPLICATE DETECTION
    // =====================================================================

    #[test]
    fn test_deduplicate_entries() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Two backups for same file -- older and newer
        fs::write(backup_dir.join("file.fst.1000.bak"), "old").unwrap();
        fs::write(backup_dir.join("file.fst.2000.bak"), "new").unwrap();
        fs::write(backup_dir.join("other.fst.1500.bak"), "other").unwrap();

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let entries = engine.scan_backups().unwrap();
        let refs: Vec<&BackupEntry> = entries.iter().collect();

        let deduped = RevertEngine::deduplicate_entries(&refs);
        assert_eq!(deduped.len(), 2, "should keep 1 per unique original file");

        // The file.fst entry should have the newer timestamp
        let file_entry = deduped
            .iter()
            .find(|e| e.original_path.ends_with("file.fst"))
            .unwrap();
        assert_eq!(file_entry.timestamp, 2000);
    }

    // =====================================================================
    // REVERT: DRY-RUN
    // =====================================================================

    #[test]
    fn test_revert_dry_run() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        let engine = RevertEngine::new(vec![src_dir.clone()]);
        let result = engine.revert_to_timestamp(1706000001000, true).unwrap();

        assert_eq!(result.reverted.len(), 2);
        assert!(result.failed.is_empty());
        // No files actually created
        assert!(!src_dir.join("test.fst").exists());
        assert!(!src_dir.join("other.fsti").exists());
    }

    #[test]
    fn test_revert_dry_run_via_config() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        let config = RevertConfig::dry_run();
        let engine = RevertEngine::with_config(vec![src_dir.clone()], config);
        let result = engine.revert_to_timestamp(1706000001000, false).unwrap();

        assert_eq!(result.reverted.len(), 2);
        assert!(!src_dir.join("test.fst").exists());
    }

    // =====================================================================
    // REVERT: ACTUAL
    // =====================================================================

    #[test]
    fn test_revert_actual() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        fs::write(src_dir.join("test.fst"), "current content").unwrap();
        fs::write(src_dir.join("other.fsti"), "current other").unwrap();

        // Force needed because original files have current mtime > backup timestamp
        let config = RevertConfig::forced();
        let engine = RevertEngine::with_config(vec![src_dir.clone()], config);
        let result = engine.revert_to_timestamp(1706000001000, false).unwrap();

        assert_eq!(result.reverted.len(), 2);
        assert!(result.failed.is_empty());

        assert_eq!(
            fs::read_to_string(src_dir.join("test.fst")).unwrap(),
            "backup content 2"
        );
        assert_eq!(
            fs::read_to_string(src_dir.join("other.fsti")).unwrap(),
            "other backup"
        );
    }

    #[test]
    fn test_revert_latest() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);
        fs::write(src_dir.join("test.fst"), "current").unwrap();
        fs::write(src_dir.join("other.fsti"), "current").unwrap();

        let config = RevertConfig::forced();
        let engine = RevertEngine::with_config(vec![src_dir.clone()], config);
        let result = engine.revert_to_latest(false).unwrap();

        assert_eq!(result.reverted.len(), 2);
        assert_eq!(
            fs::read_to_string(src_dir.join("test.fst")).unwrap(),
            "backup content 2"
        );
    }

    // =====================================================================
    // REVERT: TIMESTAMP NOT FOUND
    // =====================================================================

    #[test]
    fn test_revert_timestamp_not_found() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        let engine = RevertEngine::new(vec![src_dir]);
        let result = engine.revert_to_timestamp(9999999999999, false);

        assert!(matches!(
            result,
            Err(RevertError::TimestampNotFound { .. })
        ));
    }

    #[test]
    fn test_revert_no_backups() {
        let temp_dir = TempDir::new().unwrap();
        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        let result = engine.revert_to_latest(false);
        assert!(matches!(result, Err(RevertError::NoBackupsFound { .. })));
    }

    // =====================================================================
    // REVERT: BEST EFFORT
    // =====================================================================

    #[test]
    fn test_revert_best_effort() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);
        // Don't create original file -- dry_run doesn't need it, and it avoids
        // the modification-since-backup check firing due to current mtime.

        let engine = RevertEngine::new(vec![src_dir.clone()]);
        // Target close to 1706000000000
        let (actual_ts, result) = engine.revert_best_effort(1706000000100, true).unwrap();

        assert_eq!(actual_ts, 1706000000000);
        assert_eq!(result.reverted.len(), 1); // only test.fst at ts 0
    }

    // =====================================================================
    // EDGE CASE: BACKUP FILE MISSING
    // =====================================================================

    #[test]
    fn test_revert_backup_file_missing_atomic() {
        // Test: a BackupEntry references a backup file that no longer exists.
        // In atomic mode, validation should produce a hard failure.
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Create one real backup
        let real_bak = backup_dir.join("real.fst.1000.bak");
        fs::write(&real_bak, "real content").unwrap();

        // Construct a BackupEntry pointing to a non-existent file (simulates
        // the file disappearing between scan and validation)
        let missing_entry = BackupEntry {
            backup_path: backup_dir.join("gone.fst.1000.bak"), // does not exist
            original_path: temp_dir.path().join("gone.fst"),
            timestamp: 1000,
            timestamp_str: "1000".to_string(),
            size: 0,
        };
        let real_entry = BackupEntry {
            backup_path: real_bak,
            original_path: temp_dir.path().join("real.fst"),
            timestamp: 1000,
            timestamp_str: "1000".to_string(),
            size: 12,
        };

        let refs: Vec<&BackupEntry> = vec![&missing_entry, &real_entry];
        let config = RevertConfig::default().with_force(true); // atomic=true
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.execute_revert(&refs);
        assert!(
            matches!(result, Err(RevertError::BatchErrors { .. })),
            "atomic mode should fail when any backup file is missing"
        );
    }

    #[test]
    fn test_revert_backup_file_missing_non_atomic() {
        // Test: in non-atomic mode, a missing backup is skipped while the
        // other file is still reverted.
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Create one real backup
        let real_bak = backup_dir.join("real.fst.1000.bak");
        fs::write(&real_bak, "real content").unwrap();

        let missing_entry = BackupEntry {
            backup_path: backup_dir.join("gone.fst.1000.bak"),
            original_path: temp_dir.path().join("gone.fst"),
            timestamp: 1000,
            timestamp_str: "1000".to_string(),
            size: 0,
        };
        let real_entry = BackupEntry {
            backup_path: real_bak,
            original_path: temp_dir.path().join("real.fst"),
            timestamp: 1000,
            timestamp_str: "1000".to_string(),
            size: 12,
        };

        let refs: Vec<&BackupEntry> = vec![&missing_entry, &real_entry];
        let config = RevertConfig::default().with_atomic(false).with_force(true);
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.execute_revert(&refs).unwrap();
        assert_eq!(result.skipped.len(), 1, "missing backup should be skipped");
        assert_eq!(
            result.reverted.len(),
            1,
            "real file should still be reverted"
        );
    }

    // =====================================================================
    // EDGE CASE: MODIFIED SINCE BACKUP
    // =====================================================================

    #[test]
    fn test_revert_modified_file_blocked_atomic() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // Backup with very old timestamp
        fs::write(backup_dir.join("file.fst.1000.bak"), "original").unwrap();

        // Original file exists with a recent mtime
        let file_path = temp_dir.path().join("file.fst");
        fs::write(&file_path, "modified").unwrap();

        let config = RevertConfig::default(); // atomic=true, force=false
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.revert_to_timestamp(1000, false);
        assert!(
            matches!(result, Err(RevertError::BatchErrors { .. })),
            "atomic mode should fail when file is modified"
        );

        // File should be unchanged
        assert_eq!(fs::read_to_string(&file_path).unwrap(), "modified");
    }

    #[test]
    fn test_revert_modified_file_force() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        fs::write(backup_dir.join("file.fst.1000.bak"), "original").unwrap();

        let file_path = temp_dir.path().join("file.fst");
        fs::write(&file_path, "modified").unwrap();

        let config = RevertConfig::forced(); // force=true
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.revert_to_timestamp(1000, false).unwrap();
        assert_eq!(result.reverted.len(), 1);
        assert!(!result.warnings.is_empty(), "should produce a warning");
        assert_eq!(fs::read_to_string(&file_path).unwrap(), "original");
    }

    // =====================================================================
    // EDGE CASE: TIMESTAMP TOLERANCE MATCHING
    // =====================================================================

    #[test]
    fn test_revert_with_tolerance_matching() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        fs::write(backup_dir.join("a.fst.1000.bak"), "a-content").unwrap();
        fs::write(backup_dir.join("b.fst.1050.bak"), "b-content").unwrap();

        let file_a = temp_dir.path().join("a.fst");
        let file_b = temp_dir.path().join("b.fst");
        fs::write(&file_a, "current-a").unwrap();
        fs::write(&file_b, "current-b").unwrap();

        // Force to bypass modification check (backup timestamps are ancient)
        let config = RevertConfig::default().with_tolerance(100).with_force(true);
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.revert_to_timestamp(1050, false).unwrap();
        assert_eq!(result.reverted.len(), 2);
    }

    #[test]
    fn test_revert_tolerance_does_not_match_distant() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        fs::write(backup_dir.join("a.fst.1000.bak"), "a").unwrap();
        fs::write(backup_dir.join("b.fst.5000.bak"), "b").unwrap();

        let config = RevertConfig::default().with_tolerance(100);
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        // Timestamp 3000 is >100ms from both groups
        let result = engine.revert_to_timestamp(3000, false);
        assert!(matches!(
            result,
            Err(RevertError::TimestampNotFound { .. })
        ));
    }

    // =====================================================================
    // ATOMIC REVERT WITH DELETE BACKUPS
    // =====================================================================

    #[test]
    fn test_revert_delete_backups_after() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        let bak_path = backup_dir.join("file.fst.1000.bak");
        fs::write(&bak_path, "original").unwrap();
        fs::write(temp_dir.path().join("file.fst"), "current").unwrap();

        let config = RevertConfig::default()
            .with_delete_backups(true)
            .with_force(true);
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let result = engine.revert_to_timestamp(1000, false).unwrap();
        assert_eq!(result.reverted.len(), 1);
        assert!(!bak_path.exists(), "backup should be deleted after revert");
    }

    // =====================================================================
    // LIST TIMESTAMPS (with tolerance grouping)
    // =====================================================================

    #[test]
    fn test_list_timestamps() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);

        let engine = RevertEngine::new(vec![src_dir]);
        let summaries = engine.list_timestamps().unwrap();

        assert_eq!(summaries.len(), 2); // Two distinct timestamp groups
        assert_eq!(summaries[0].file_count, 2); // ts 1706000001000 has 2 files
        assert_eq!(summaries[1].file_count, 1); // ts 1706000000000 has 1 file
    }

    #[test]
    fn test_list_timestamps_with_tolerance() {
        let temp_dir = TempDir::new().unwrap();
        let backup_dir = temp_dir.path().join(BACKUP_DIR_NAME);
        fs::create_dir_all(&backup_dir).unwrap();

        // All within 100ms
        fs::write(backup_dir.join("a.fst.1000.bak"), "a").unwrap();
        fs::write(backup_dir.join("b.fst.1050.bak"), "b").unwrap();
        fs::write(backup_dir.join("c.fst.1099.bak"), "c").unwrap();

        let config = RevertConfig::default().with_tolerance(100);
        let engine = RevertEngine::with_config(vec![temp_dir.path().to_path_buf()], config);

        let summaries = engine.list_timestamps().unwrap();
        assert_eq!(summaries.len(), 1, "all within tolerance -> 1 group");
        assert_eq!(summaries[0].file_count, 3);
    }

    // =====================================================================
    // CLOSEST TIMESTAMP
    // =====================================================================

    #[test]
    fn test_find_closest_timestamp() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);
        let engine = RevertEngine::new(vec![src_dir]);

        assert_eq!(
            engine.find_closest_timestamp(1706000001000).unwrap(),
            Some(1706000001000)
        );
        assert_eq!(
            engine.find_closest_timestamp(1706000000100).unwrap(),
            Some(1706000000000)
        );
        assert_eq!(
            engine.find_closest_timestamp(1706000000900).unwrap(),
            Some(1706000001000)
        );
    }

    // =====================================================================
    // PATH FILTER
    // =====================================================================

    #[test]
    fn test_path_filter() {
        let temp_dir = TempDir::new().unwrap();

        let core_dir = temp_dir.path().join("src").join("core");
        let core_backup = core_dir.join(BACKUP_DIR_NAME);
        fs::create_dir_all(&core_backup).unwrap();
        fs::write(core_backup.join("core.fst.1000.bak"), "core").unwrap();

        let util_dir = temp_dir.path().join("src").join("util");
        let util_backup = util_dir.join(BACKUP_DIR_NAME);
        fs::create_dir_all(&util_backup).unwrap();
        fs::write(util_backup.join("util.fst.1000.bak"), "util").unwrap();

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()]);
        assert_eq!(engine.scan_backups().unwrap().len(), 2);

        let engine = RevertEngine::new(vec![temp_dir.path().to_path_buf()])
            .with_path_filter(core_dir.clone());
        let entries = engine.scan_backups().unwrap();
        assert_eq!(entries.len(), 1);
        assert!(entries[0].original_path.starts_with(&core_dir));
    }

    // =====================================================================
    // RESULT HELPERS
    // =====================================================================

    #[test]
    fn test_revert_result_helpers() {
        let mut r = RevertResult_::new();
        assert!(r.is_success());
        assert_eq!(r.total_processed(), 0);

        r.reverted.push(PathBuf::from("/a.fst"));
        r.skipped
            .push((PathBuf::from("/b.fst"), "reason".to_string()));
        assert!(r.is_success());
        assert_eq!(r.total_processed(), 2);

        r.failed
            .push((PathBuf::from("/c.fst"), "error".to_string()));
        assert!(!r.is_success());
        assert_eq!(r.total_processed(), 3);
    }

    #[test]
    fn test_success_with_warnings() {
        let mut r = RevertResult_::new();
        r.reverted.push(PathBuf::from("/a.fst"));
        r.warnings
            .push((PathBuf::from("/a.fst"), "force-reverted".to_string()));
        assert!(r.is_success_with_warnings());
    }

    // =====================================================================
    // FORMAT HELPERS
    // =====================================================================

    #[test]
    fn test_format_timestamp() {
        let ts = 1706097600123u64;
        let formatted = RevertEngine::format_timestamp(ts);
        assert!(formatted.contains("2024"));
        assert!(formatted.contains("UTC"));
        assert!(formatted.contains(".123"));
    }

    #[test]
    fn test_format_size() {
        assert_eq!(format_size(100), "100 B");
        assert_eq!(format_size(1024), "1.00 KB");
        assert_eq!(format_size(1536), "1.50 KB");
        assert_eq!(format_size(1048576), "1.00 MB");
        assert_eq!(format_size(1073741824), "1.00 GB");
    }

    // =====================================================================
    // METADATA
    // =====================================================================

    #[test]
    fn test_backup_metadata_new() {
        let meta = BackupMetadata::new("fix src/ --apply");
        assert!(!meta.id.is_empty());
        assert!(meta.timestamp_ms > 0);
        assert_eq!(meta.command, "fix src/ --apply");
        assert!(meta.files.is_empty());
        assert_eq!(meta.total_size_bytes, 0);
    }

    #[test]
    fn test_backup_metadata_add_file() {
        let mut meta = BackupMetadata::new("test");
        meta.add_file(
            Path::new("/src/test.fst"),
            Path::new("/src/.fstar-lint-backups/test.fst.123.bak"),
            1024,
        );
        assert_eq!(meta.files.len(), 1);
        assert_eq!(meta.total_size_bytes, 1024);
    }

    #[test]
    fn test_directory_metadata_roundtrip() {
        let temp_dir = TempDir::new().unwrap();
        let mut metadata = BackupDirectoryMetadata::new();

        let mut entry = BackupMetadata::new("test command");
        entry.add_file(
            Path::new("/test/file.fst"),
            Path::new("/test/.fstar-lint-backups/file.fst.123.bak"),
            500,
        );
        metadata.record_backup(entry);

        save_metadata(temp_dir.path(), &metadata).unwrap();
        let loaded = load_metadata(temp_dir.path()).unwrap();

        assert_eq!(loaded.backups.len(), 1);
        assert_eq!(loaded.backups[0].command, "test command");
        assert_eq!(loaded.backups[0].total_size_bytes, 500);
        assert_eq!(loaded.version, BackupDirectoryMetadata::CURRENT_VERSION);
    }

    #[test]
    fn test_metadata_coalescing() {
        let mut metadata = BackupDirectoryMetadata::new();
        let entry1 = BackupMetadata::new("fix --apply");
        let mut entry2 = BackupMetadata::new("fix --apply");
        entry2.timestamp_ms = entry1.timestamp_ms + 1;

        metadata.record_backup(entry1);
        metadata.record_backup(entry2);
        assert_eq!(metadata.backups.len(), 1);
    }

    #[test]
    fn test_revert_point_add_and_find() {
        let mut metadata = BackupDirectoryMetadata::new();
        let point = RevertPoint {
            name: "before-refactor".to_string(),
            description: Some("Before big refactor".to_string()),
            created_at_ms: 1706000000000,
            backup_id: "backup_123".to_string(),
            files: vec!["/src/test.fst".to_string()],
        };
        metadata.add_revert_point(point);
        assert!(metadata.find_revert_point("before-refactor").is_some());
        assert!(metadata.find_revert_point("nonexistent").is_none());
    }

    #[test]
    fn test_revert_point_replace_same_name() {
        let mut metadata = BackupDirectoryMetadata::new();
        metadata.add_revert_point(RevertPoint {
            name: "checkpoint".to_string(),
            description: Some("First".to_string()),
            created_at_ms: 100,
            backup_id: "id1".to_string(),
            files: vec![],
        });
        metadata.add_revert_point(RevertPoint {
            name: "checkpoint".to_string(),
            description: Some("Second".to_string()),
            created_at_ms: 200,
            backup_id: "id2".to_string(),
            files: vec![],
        });
        assert_eq!(metadata.revert_points.len(), 1);
        assert_eq!(
            metadata
                .find_revert_point("checkpoint")
                .unwrap()
                .description
                .as_deref(),
            Some("Second")
        );
    }

    // =====================================================================
    // PARSE DURATION
    // =====================================================================

    #[test]
    fn test_parse_duration_str() {
        assert_eq!(parse_duration_str("30s").unwrap(), Duration::from_secs(30));
        assert_eq!(parse_duration_str("5m").unwrap(), Duration::from_secs(300));
        assert_eq!(parse_duration_str("2h").unwrap(), Duration::from_secs(7200));
        assert_eq!(
            parse_duration_str("7d").unwrap(),
            Duration::from_secs(604800)
        );
        assert_eq!(
            parse_duration_str("1w").unwrap(),
            Duration::from_secs(604800)
        );
        assert!(parse_duration_str("").is_err());
        assert!(parse_duration_str("abc").is_err());
        assert!(parse_duration_str("7x").is_err());
    }

    // =====================================================================
    // BACKUP SUMMARY
    // =====================================================================

    #[test]
    fn test_gather_backup_summary_empty() {
        let temp_dir = TempDir::new().unwrap();
        let info = gather_backup_summary(&[temp_dir.path().to_path_buf()]);
        assert_eq!(info.total_backups, 0);
        assert_eq!(info.unique_files, 0);
    }

    #[test]
    fn test_gather_backup_summary_with_data() {
        let temp_dir = TempDir::new().unwrap();
        let src_dir = create_backup_structure(&temp_dir);
        let info = gather_backup_summary(&[src_dir]);
        assert_eq!(info.total_backups, 3);
        assert_eq!(info.unique_files, 2);
        assert!(info.total_bytes > 0);
    }

    // =====================================================================
    // CLEANUP
    // =====================================================================

    #[test]
    fn test_cleanup_dry_run() {
        let temp_dir = TempDir::new().unwrap();
        let _src_dir = create_backup_structure(&temp_dir);
        let summary = cleanup_old_backups(
            &[temp_dir.path().join("src")],
            Duration::from_secs(1),
            true,
        )
        .unwrap();

        assert!(summary.would_remove > 0);
        assert_eq!(summary.removed, 0);
    }
}
