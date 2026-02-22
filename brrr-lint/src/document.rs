//! Document state management.

use crate::config::{FstarConfig, LspSettings};
use crate::connection::FstarConnection;
use crate::error::{FstarError, Result};
use crate::protocol::*;
use std::path::PathBuf;
use tokio::sync::{mpsc, Mutex, RwLock};
use tokio::time::Instant;
use tower_lsp::lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, NumberOrString,
    Position, Range, TextDocumentContentChangeEvent, Url,
};
use tracing::{debug, warn};

/// Verification status of a code fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FragmentStatus {
    Ok,
    LaxOk,
    // InProgress removed - using Started instead
    Started,
    Failed,
}

/// A verified code fragment.
#[derive(Debug, Clone)]
pub struct Fragment {
    pub range: Range,
    pub status: FragmentStatus,
    /// True if the fragment was invalidated by an edit (stale result).
    pub stale: bool,
    /// Hash of the fragment's source code, sent by F* for cache-based invalidation.
    /// If a fragment's digest matches a previously verified fragment, its verification
    /// result can potentially be reused without re-checking.
    pub code_digest: Option<String>,
}

/// Document verification results.
#[derive(Debug, Default)]
pub struct VerificationResults {
    pub fragments: Vec<Fragment>,
    /// Diagnostics from the full (non-lax) F* process.
    pub full_diagnostics: Vec<Diagnostic>,
    /// Diagnostics from the lax (flycheck) F* process.
    pub lax_diagnostics: Vec<Diagnostic>,
    pub proof_states: Vec<IdeProofState>,
    pub invalid_after: Option<Position>,
}

impl VerificationResults {
    pub fn clear(&mut self) {
        self.fragments.clear();
        self.full_diagnostics.clear();
        self.lax_diagnostics.clear();
        self.proof_states.clear();
        self.invalid_after = None;
    }

    /// Returns merged diagnostics for the LSP client.
    ///
    /// Implements diagnostic merging to avoid duplicates between full and lax F* processes:
    /// - Full process diagnostics are shown as-is
    /// - Lax process diagnostics are filtered to only show those AFTER the last verified fragment
    /// - This prevents duplicate errors in the already-verified region
    /// - Lax diagnostics are labeled "fstar (flycheck)" for distinction
    ///
    /// This matches the TypeScript implementation in documentState.ts lines 163-182.
    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        // Find the end position of the last fully verified (non-lax, non-stale) fragment.
        let last_verified_pos = self
            .fragments
            .iter()
            .rfind(|f| f.status == FragmentStatus::Ok && !f.stale)
            .map(|f| f.range.end);

        // Start with all full diagnostics
        let mut merged = self.full_diagnostics.clone();

        if let Some(verified_end) = last_verified_pos {
            // Only include lax diagnostics that start after the verified region.
            for diag in &self.lax_diagnostics {
                let after_verified = diag.range.start.line > verified_end.line
                    || (diag.range.start.line == verified_end.line
                        && diag.range.start.character >= verified_end.character);

                if after_verified {
                    let mut lax_diag = diag.clone();
                    lax_diag.source = Some("fstar (flycheck)".to_string());
                    merged.push(lax_diag);
                }
            }
        } else {
            // No verified region yet - show all lax diagnostics labeled as flycheck.
            for diag in &self.lax_diagnostics {
                let mut lax_diag = diag.clone();
                lax_diag.source = Some("fstar (flycheck)".to_string());
                merged.push(lax_diag);
            }
        }

        merged
    }

    pub fn invalidate_after(&mut self, pos: Position) {
        // FIX M6: Keep the earlier invalidation point.
        // If we already have an invalidation point that is earlier than or equal to
        // the new position, don't overwrite it. This prevents losing track of earlier
        // edits when multiple edits occur (e.g., edit at line 5, then at line 10 -
        // we must keep line 5 as the invalidation point).
        if let Some(existing) = self.invalid_after {
            if existing.line < pos.line
                || (existing.line == pos.line && existing.character <= pos.character)
            {
                // Existing invalidation point is earlier or equal; keep it.
                // Still need to mark additional fragments as stale below.
            } else {
                // New position is earlier; update the invalidation point.
                self.invalid_after = Some(pos);
            }
        } else {
            self.invalid_after = Some(pos);
        }

        // FIX H2: Mark fragments whose END is at or after the edit position as stale.
        // Previously compared fragment START, which missed fragments that contain
        // the edit. If you edit inside a fragment, its start is before the edit
        // but the fragment is still affected and must be re-verified.
        for frag in &mut self.fragments {
            let affected = frag.range.end.line > pos.line
                || (frag.range.end.line == pos.line && frag.range.end.character > pos.character);
            if affected {
                frag.stale = true;
            }
        }

        // Remove diagnostics that start at or after the edit position.
        let retain_diag = |d: &Diagnostic| {
            d.range.start.line < pos.line
                || (d.range.start.line == pos.line && d.range.start.character < pos.character)
        };
        self.full_diagnostics.retain(retain_diag);
        self.lax_diagnostics.retain(retain_diag);
    }
}

/// Document state for a single F* file.
pub struct DocumentState {
    pub uri: Url,
    pub file_path: PathBuf,
    text: RwLock<String>,
    version: RwLock<i32>,
    config: FstarConfig,
    fstar: Mutex<Option<FstarConnection>>,
    fstar_lax: Mutex<Option<FstarConnection>>,
    results: RwLock<VerificationResults>,
    /// Buffer for new results during FBQ. F* replays cached results before processing
    /// new fragments. We buffer these in new_results to avoid data loss when the main
    /// results vector is empty. The buffers are swapped on the first real fragment-started.
    new_results: RwLock<Option<VerificationResults>>,
    settings: LspSettings,
    disposed: RwLock<bool>,
    status_tx: mpsc::Sender<StatusUpdate>,
    last_edit: RwLock<Instant>,
    /// Flag indicating restart is in progress. During restart, vfs_add calls in update()
    /// are skipped since the connections are being recreated. After initialize() completes,
    /// the current text is re-synced to the new F* processes.
    restarting: RwLock<bool>,
}

/// Status update message.
#[derive(Debug, Clone)]
pub struct StatusUpdate {
    pub uri: Url,
    pub fragments: Vec<Fragment>,
    pub diagnostics: Vec<Diagnostic>,
}

impl DocumentState {
    pub async fn new(
        uri: Url,
        text: String,
        version: i32,
        config: FstarConfig,
        settings: LspSettings,
        status_tx: mpsc::Sender<StatusUpdate>,
    ) -> Result<Self> {
        let file_path = uri
            .to_file_path()
            .map_err(|_| FstarError::Config("Invalid file URI".to_string()))?;

        Ok(Self {
            uri,
            file_path,
            text: RwLock::new(text),
            version: RwLock::new(version),
            config,
            fstar: Mutex::new(None),
            fstar_lax: Mutex::new(None),
            results: RwLock::new(VerificationResults::default()),
            new_results: RwLock::new(None),
            settings,
            disposed: RwLock::new(false),
            status_tx,
            last_edit: RwLock::new(Instant::now()),
            restarting: RwLock::new(false),
        })
    }

    pub async fn initialize(&self) -> Result<()> {
        let fstar = FstarConnection::spawn(
            &self.config,
            &self.file_path,
            false,
            self.settings.timeout_ms,
            self.settings.debug,
        )
        .await?;

        let text = self.text.read().await.clone();
        fstar
            .vfs_add(Some(&self.file_path.to_string_lossy()), &text)
            .await?;

        *self.fstar.lock().await = Some(fstar);

        if self.settings.fly_check {
            match FstarConnection::spawn(
                &self.config,
                &self.file_path,
                true,
                self.settings.timeout_ms,
                self.settings.debug,
            )
            .await
            {
                Ok(fstar_lax) => {
                    fstar_lax
                        .vfs_add(Some(&self.file_path.to_string_lossy()), &text)
                        .await?;
                    *self.fstar_lax.lock().await = Some(fstar_lax);
                }
                Err(e) => {
                    warn!("Failed to spawn lax F* process: {}", e);
                }
            }
        }

        Ok(())
    }

    pub async fn update(&self, changes: Vec<TextDocumentContentChangeEvent>, version: i32) {
        let mut text = self.text.write().await;

        // Track the earliest change position for cancel-on-edit
        let mut earliest_change = Position {
            line: u32::MAX,
            character: u32::MAX,
        };

        for change in &changes {
            if let Some(range) = change.range {
                if range.start.line < earliest_change.line
                    || (range.start.line == earliest_change.line
                        && range.start.character < earliest_change.character)
                {
                    earliest_change = range.start;
                }

                let start_offset = self.position_to_offset(&text, range.start);
                let end_offset = self.position_to_offset(&text, range.end);

                if let (Ok(start), Ok(end)) = (start_offset, end_offset) {
                    text.replace_range(start..end, &change.text);
                }
            } else {
                earliest_change = Position {
                    line: 0,
                    character: 0,
                };
                *text = change.text.clone();
            }
        }

        *self.version.write().await = version;
        *self.last_edit.write().await = Instant::now();

        // Invalidate both results buffers to maintain consistency during double-buffering.
        // This matches the TypeScript behavior where invalidateResults is called on both
        // this.results and this.newResults (see documentState.ts lines 328-329).
        self.results.write().await.invalidate_after(earliest_change);
        if let Some(ref mut new_res) = *self.new_results.write().await {
            new_res.invalidate_after(earliest_change);
        }

        let text_clone = text.clone();
        drop(text);

        // Skip vfs_add if restart is in progress. During restart, connections are being
        // recreated and vfs_add would either fail or be sent to dead processes. The text
        // is still updated above in self.text, and restart() will re-sync after initialize().
        if *self.restarting.read().await {
            return;
        }

        // Cancel in-progress verification at the edit position
        let fstar_pos = lsp_to_fstar_pos(earliest_change);
        if let Some(fstar) = self.fstar.lock().await.as_ref() {
            let _ = fstar.cancel_fbq(fstar_pos).await;
            let _ = fstar
                .vfs_add(Some(&self.file_path.to_string_lossy()), &text_clone)
                .await;
        }

        if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            let _ = fstar_lax.cancel_fbq(fstar_pos).await;
            let _ = fstar_lax
                .vfs_add(Some(&self.file_path.to_string_lossy()), &text_clone)
                .await;
        }
    }

    /// Converts an LSP Position to a byte offset within the text.
    ///
    /// Handles three critical issues:
    /// 1. CRLF line endings: Windows files use `\r\n` (2 bytes) not `\n` (1 byte)
    /// 2. Out-of-bounds: Returns Err(InvalidPosition) if position is past line/file end
    /// 3. UTF-16 encoding: LSP character offsets are UTF-16 code units, not bytes
    fn position_to_offset(
        &self,
        text: &str,
        pos: Position,
    ) -> std::result::Result<usize, FstarError> {
        let mut offset = 0;
        let bytes = text.as_bytes();
        let line_num = pos.line as usize;

        for (i, line) in text.lines().enumerate() {
            if i == line_num {
                // Convert UTF-16 column offset to byte offset within the line
                let char_byte_offset = utf16_to_byte_offset(line, pos.character, pos.line)?;
                return Ok(offset + char_byte_offset);
            }
            offset += line.len();
            // Skip actual line ending bytes (handles both \r\n and \n)
            if bytes.get(offset) == Some(&b'\r') {
                offset += 1;
            }
            if bytes.get(offset) == Some(&b'\n') {
                offset += 1;
            }
        }

        // Position is at or past the last line - only valid for inserting at end
        let line_count = text.lines().count();
        // Handle edge case: empty file or file ending with newline
        // In these cases, line_count might equal line_num for valid end-of-file position
        if line_num == line_count && pos.character == 0 {
            Ok(text.len())
        } else {
            Err(FstarError::InvalidPosition {
                line: pos.line,
                column: pos.character,
            })
        }
    }

    pub async fn verify_full(&self) -> Result<()> {
        self.do_verify(FullBufferKind::Full, None, false).await
    }

    pub async fn verify_lax(&self) -> Result<()> {
        self.do_verify(FullBufferKind::Lax, None, true).await
    }

    /// Send a cache query to the main (non-lax) checker.
    ///
    /// This tells F* to report which prefix of the buffer is still verified from cache,
    /// without re-checking. This enables incremental checking: F* compares the new buffer
    /// against its cached verification state and only re-verifies changed portions when
    /// `verify_full()` is later called.
    pub async fn verify_cache(&self) -> Result<()> {
        self.do_verify(FullBufferKind::Cache, None, false).await
    }

    pub async fn verify_to_position(&self, position: Position, lax: bool) -> Result<()> {
        let kind = if lax {
            FullBufferKind::LaxToPosition
        } else {
            FullBufferKind::VerifyToPosition
        };
        let fstar_pos = lsp_to_fstar_pos(position);
        self.do_verify(kind, Some(fstar_pos), lax).await
    }

    async fn do_verify(
        &self,
        kind: FullBufferKind,
        to_position: Option<FstarPosition>,
        use_lax: bool,
    ) -> Result<()> {
        if *self.disposed.read().await {
            return Ok(());
        }

        // Start the FBQ on the appropriate connection, then immediately drop the lock
        // so other operations (vfs_add, cancel) aren't blocked during verification.
        let text = self.text.read().await.clone();
        let rx = if use_lax {
            let guard = self.fstar_lax.lock().await;
            if let Some(fstar) = guard.as_ref() {
                let rx = fstar.full_buffer_query(&text, kind, to_position).await?;
                drop(guard);
                rx
            } else {
                drop(guard);
                // Fall back to main connection
                let guard = self.fstar.lock().await;
                let fstar = guard
                    .as_ref()
                    .ok_or_else(|| FstarError::Process("F* not running".to_string()))?;
                let rx = fstar.full_buffer_query(&text, kind, to_position).await?;
                drop(guard);
                rx
            }
        } else {
            let guard = self.fstar.lock().await;
            let fstar = guard
                .as_ref()
                .ok_or_else(|| FstarError::Process("F* not running".to_string()))?;
            let rx = fstar.full_buffer_query(&text, kind, to_position).await?;
            drop(guard);
            rx
        };

        let mut rx = rx;
        let mut received_done = false;
        let mut was_cancelled = false;

        while let Some(response) = rx.recv().await {
            if *self.disposed.read().await {
                break;
            }

            self.handle_fbq_response(&response, use_lax).await;

            if response.is_done() {
                received_done = true;
                // Check if this is a cancellation response (response kind with null body).
                // When F* receives a cancel request, it sends back a "response" message
                // with null response field to indicate the query was cancelled.
                if response.kind == "response" && response.response.is_none() {
                    was_cancelled = true;
                }
                break;
            }
        }

        self.send_status_update().await;

        // If the channel closed without receiving a done message (and not due to disposal),
        // the query was cancelled (e.g., connection lost during FBQ, or sender dropped).
        if !received_done && !*self.disposed.read().await {
            return Err(FstarError::Cancelled);
        }

        // If we received an explicit cancellation response, return Cancelled error.
        // This allows callers to distinguish between normal completion and cancellation.
        if was_cancelled {
            return Err(FstarError::Cancelled);
        }

        Ok(())
    }

    async fn handle_fbq_response(&self, response: &Response, is_lax: bool) {
        if response.is_progress() {
            if let Some(contents) = &response.contents {
                if let Ok(progress) = serde_json::from_value::<IdeProgress>(contents.clone()) {
                    self.handle_progress(&progress, is_lax).await;
                }
            }
        }

        if response.kind == "message" {
            // Check if this is a proof-state message
            if response.level.as_deref() == Some("proof-state") {
                if let Some(contents) = &response.contents {
                    if let Ok(ps) = serde_json::from_value::<IdeProofState>(contents.clone()) {
                        self.results.write().await.proof_states.push(ps);
                    }
                }
                return;
            }

            if let Some(contents) = &response.contents {
                if let Ok(diags) = serde_json::from_value::<Vec<IdeDiagnostic>>(contents.clone()) {
                    self.handle_diagnostics(&diags, is_lax).await;
                }
            }
        } else if response.kind == "response" {
            // F* sends structured diagnostics in "response" messages with the diagnostics
            // array in the `response` field (not `contents`). This is the primary way
            // errors, warnings, and other diagnostics are delivered after verification.
            match &response.response {
                None => {
                    // Query was cancelled (e.g., by user edit during verification)
                    tracing::debug!("Query {} cancelled", response.query_id);
                }
                Some(resp) if resp.is_array() => {
                    if let Ok(diags) = serde_json::from_value::<Vec<IdeDiagnostic>>(resp.clone()) {
                        self.handle_diagnostics(&diags, is_lax).await;
                    }
                }
                Some(_) => {
                    // Non-array response (e.g., null or object), nothing to do
                }
            }
        }
    }

    /// Handles progress messages during a Full Buffer Query (FBQ).
    ///
    /// Implements double-buffering to correctly handle F*'s cached result replay:
    /// - When F* starts an FBQ, it first replays cached results (fragment-ok without fragment-started)
    /// - These are buffered in `new_results` until the first real fragment-started
    /// - On first fragment-started, buffers are swapped, preserving proof states from the verified prefix
    /// - On FBQ finish, `invalid_after` is cleared since the document is now consistent
    ///
    /// This matches the TypeScript implementation in documentState.ts lines 439-535.
    async fn handle_progress(&self, progress: &IdeProgress, is_lax: bool) {
        let mut results = self.results.write().await;
        let mut new_results_guard = self.new_results.write().await;

        match progress.stage {
            ProgressStage::FullBufferStarted => {
                // Create a fresh buffer for incoming results. F* will first replay cached
                // results (fragment-ok without fragment-started), which go into this buffer.
                *new_results_guard = Some(VerificationResults::default());
            }

            ProgressStage::FullBufferFragmentStarted => {
                // This is the first fragment F* actually processes (not from cache).
                // Swap the buffers now, preserving proof states from the verified prefix.
                if let Some(mut new_res) = new_results_guard.take() {
                    if let Some(range) = &progress.ranges {
                        let rng = range.to_lsp_range();
                        // Preserve proof states from before this fragment's range
                        new_res.proof_states = results
                            .proof_states
                            .iter()
                            .filter(|ps| {
                                ps.location.as_ref().is_some_and(|loc| {
                                    let ps_end = loc.to_lsp_range().end;
                                    ps_end.line < rng.start.line
                                        || (ps_end.line == rng.start.line
                                            && ps_end.character <= rng.start.character)
                                })
                            })
                            .cloned()
                            .collect();
                    }
                    *results = new_res;
                }

                // Now add the new in-progress fragment
                if let Some(range) = &progress.ranges {
                    let lsp_range = range.to_lsp_range();
                    let stale = results.invalid_after.is_some_and(|inv_pos| {
                        lsp_range.end.line > inv_pos.line
                            || (lsp_range.end.line == inv_pos.line
                                && lsp_range.end.character > inv_pos.character)
                    });
                    results.fragments.push(Fragment {
                        range: lsp_range,
                        status: FragmentStatus::Started,
                        stale,
                        // code_digest is not available at fragment-started; it arrives with fragment-ok
                        code_digest: None,
                    });
                }
            }

            ProgressStage::FullBufferFragmentOk | ProgressStage::FullBufferFragmentLaxOk => {
                let status = if progress.stage == ProgressStage::FullBufferFragmentOk {
                    FragmentStatus::Ok
                } else if is_lax {
                    FragmentStatus::LaxOk
                } else {
                    FragmentStatus::Ok
                };

                if let Some(new_res) = new_results_guard.as_mut() {
                    // This is a cached result (no preceding fragment-started).
                    // Buffer it in new_results to avoid losing it when results is empty.
                    if let Some(range) = &progress.ranges {
                        let lsp_range = range.to_lsp_range();
                        let stale = new_res.invalid_after.is_some_and(|inv_pos| {
                            lsp_range.end.line > inv_pos.line
                                || (lsp_range.end.line == inv_pos.line
                                    && lsp_range.end.character > inv_pos.character)
                        });
                        // Log cached result with code digest for debugging
                        if let Some(cf) = &progress.code_fragment {
                            debug!(
                                "Cached fragment result: digest={}, range=({},{})-({},{})",
                                cf.code_digest,
                                lsp_range.start.line,
                                lsp_range.start.character,
                                lsp_range.end.line,
                                lsp_range.end.character
                            );
                        }
                        new_res.fragments.push(Fragment {
                            range: lsp_range,
                            status,
                            stale,
                            code_digest: progress
                                .code_fragment
                                .as_ref()
                                .map(|cf| cf.code_digest.clone()),
                        });
                    }
                } else {
                    // Normal case: update the last fragment's status
                    // Read invalid_after before taking mutable borrow of fragments
                    let inv_pos = results.invalid_after;
                    if let Some(frag) = results.fragments.last_mut() {
                        frag.status = status;
                        // Store the code digest for potential cache-based invalidation
                        if let Some(cf) = &progress.code_fragment {
                            frag.code_digest = Some(cf.code_digest.clone());
                            debug!(
                                "Fragment verified: digest={}, range=({},{})-({},{})",
                                cf.code_digest,
                                frag.range.start.line,
                                frag.range.start.character,
                                frag.range.end.line,
                                frag.range.end.character
                            );
                        }
                        // Update stale flag based on current invalid_after
                        if let Some(inv_pos) = inv_pos {
                            frag.stale = frag.range.end.line > inv_pos.line
                                || (frag.range.end.line == inv_pos.line
                                    && frag.range.end.character > inv_pos.character);
                        }
                    }
                }
            }

            ProgressStage::FullBufferFragmentFailed => {
                if new_results_guard.is_some() {
                    // This shouldn't happen for cached results - log a warning
                    warn!("full-buffer-fragment-failed without preceding fragment-started");
                } else if let Some(frag) = results.fragments.last_mut() {
                    frag.status = FragmentStatus::Failed;
                }
            }

            ProgressStage::FullBufferFinished => {
                if let Some(mut new_res) = new_results_guard.take() {
                    // No fragments were actually processed (all from cache).
                    // Preserve proof states from previous results.
                    new_res.proof_states = std::mem::take(&mut results.proof_states);
                    *results = new_res;
                } else {
                    // When cancelling an FBQ, F* may send fragment-started without fragment-ok.
                    // Remove any incomplete (started but not finished) fragment.
                    if let Some(last_frag) = results.fragments.last() {
                        if last_frag.status == FragmentStatus::Started {
                            results.fragments.pop();
                        }
                    }
                }

                // Clear invalid_after since the document state is now consistent with
                // verification results. This fixes the accumulation bug (H3).
                results.invalid_after = None;
            }
        }
    }

    /// Handles diagnostics from F*, converting them to LSP Diagnostic format.
    ///
    /// Uses the first valid range as the main diagnostic location, with additional
    /// ranges as `relatedInformation`. This matches the TypeScript implementation
    /// (documentState.ts lines 537-573) and provides better UX - users see one
    /// diagnostic with "related locations" instead of multiple duplicate diagnostics.
    async fn handle_diagnostics(&self, diags: &[IdeDiagnostic], is_lax: bool) {
        let mut results = self.results.write().await;

        for diag in diags {
            // Filter out dummy ranges (line 0, character 0 placeholders from F*)
            let valid_ranges: Vec<_> = diag.ranges.iter().filter(|r| !r.is_dummy()).collect();

            if valid_ranges.is_empty() {
                continue;
            }

            let severity = match diag.level {
                DiagnosticLevel::Error => {
                    if is_lax {
                        DiagnosticSeverity::WARNING
                    } else {
                        DiagnosticSeverity::ERROR
                    }
                }
                DiagnosticLevel::Warning => DiagnosticSeverity::WARNING,
                DiagnosticLevel::Info => DiagnosticSeverity::INFORMATION,
                DiagnosticLevel::NotImplemented => DiagnosticSeverity::ERROR,
            };

            // First range is the main diagnostic location
            let main_range = valid_ranges[0].to_lsp_range();

            // Remaining ranges become related information, providing context
            // about other locations relevant to this diagnostic
            let related_information: Option<Vec<DiagnosticRelatedInformation>> =
                if valid_ranges.len() > 1 {
                    Some(
                        valid_ranges[1..]
                            .iter()
                            .map(|r| DiagnosticRelatedInformation {
                                location: Location {
                                    uri: Url::from_file_path(&r.fname)
                                        .unwrap_or_else(|_| self.uri.clone()),
                                    range: r.to_lsp_range(),
                                },
                                message: "Related location".to_string(),
                            })
                            .collect(),
                    )
                } else {
                    None
                };

            let diagnostic = Diagnostic {
                range: main_range,
                severity: Some(severity),
                code: diag.number.map(NumberOrString::Number),
                source: Some("fstar".to_string()),
                message: diag.message.clone(),
                related_information,
                ..Default::default()
            };

            // Route to appropriate diagnostic list based on source process.
            if is_lax {
                results.lax_diagnostics.push(diagnostic);
            } else {
                results.full_diagnostics.push(diagnostic);
            }
        }
    }

    async fn send_status_update(&self) {
        let results = self.results.read().await;
        let update = StatusUpdate {
            uri: self.uri.clone(),
            fragments: results.fragments.clone(),
            diagnostics: results.diagnostics(),
        };
        let _ = self.status_tx.send(update).await;
    }

    pub async fn get_diagnostics(&self) -> Vec<Diagnostic> {
        self.results.read().await.diagnostics()
    }

    pub async fn get_fragments(&self) -> Vec<Fragment> {
        self.results.read().await.fragments.clone()
    }

    /// Returns a clone of the full document text.
    pub async fn text(&self) -> String {
        self.text.read().await.clone()
    }

    /// Returns the number of lines in the document text.
    pub async fn line_count(&self) -> u32 {
        let text = self.text.read().await;
        text.lines().count() as u32
    }

    /// Returns hover content for the given position, along with an optional range
    /// to highlight in the editor.
    ///
    /// The range is derived from the `symbol_range` field when available from F*
    /// symbol lookups, allowing the editor to highlight the exact symbol.
    pub async fn hover(&self, position: Position) -> Option<(String, Option<Range>)> {
        let results = self.results.read().await;
        // L4: Find proof state with highest urgency matching the line.
        // When multiple proof states exist for the same location (from nested tactic dumps
        // or multiple verification runs), higher urgency indicates more important state.
        let matching_ps = results
            .proof_states
            .iter()
            .filter(|ps| {
                ps.location
                    .as_ref()
                    .map(|loc| loc.to_lsp_range().start.line == position.line)
                    .unwrap_or(false)
            })
            .max_by_key(|ps| ps.urgency);

        if let Some(ps) = matching_ps {
            return Some((format_proof_state(ps), None));
        }
        drop(results);

        let word = self
            .get_word_at_position(position)
            .await
            .ok()
            .filter(|w| !w.is_empty())?;
        let fstar_pos = lsp_to_fstar_pos(position);

        if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            if let Ok(Some(response)) = fstar_lax.lookup(&word, &self.file_path, fstar_pos).await {
                let range = extract_symbol_range(&response);
                return Some((format_lookup_response(&response), range));
            }
        }

        if let Some(fstar) = self.fstar.lock().await.as_ref() {
            if let Ok(Some(response)) = fstar.lookup(&word, &self.file_path, fstar_pos).await {
                let range = extract_symbol_range(&response);
                return Some((format_lookup_response(&response), range));
            }
        }

        None
    }

    /// Extracts the word at the given LSP position.
    ///
    /// Properly handles UTF-16 character offsets by converting to character indices.
    /// Returns `Err(InvalidPosition)` if the position is outside document bounds.
    /// Returns `Ok(empty string)` if the position is valid but not on a word.
    async fn get_word_at_position(
        &self,
        position: Position,
    ) -> std::result::Result<String, FstarError> {
        let text = self.text.read().await;
        let lines: Vec<&str> = text.lines().collect();
        let line = lines
            .get(position.line as usize)
            .ok_or(FstarError::InvalidPosition {
                line: position.line,
                column: position.character,
            })?;

        // Convert UTF-16 column offset to character index
        // This handles characters outside BMP (emoji, etc.) which use surrogate pairs
        let col = utf16_to_char_index(line, position.character, position.line)?;

        let chars: Vec<char> = line.chars().collect();

        // Bounds check: col can be at most chars.len() (end of line)
        if col > chars.len() {
            return Err(FstarError::InvalidPosition {
                line: position.line,
                column: position.character,
            });
        }

        let mut start = col;
        let mut end = col;

        while start > 0 && is_word_char(chars[start - 1]) {
            start -= 1;
        }

        while end < chars.len() && is_word_char(chars[end]) {
            end += 1;
        }

        if start == end {
            return Ok(String::new());
        }

        Ok(chars[start..end].iter().collect())
    }

    pub async fn definition(&self, position: Position) -> Option<tower_lsp::lsp_types::Location> {
        let word = self
            .get_word_at_position(position)
            .await
            .ok()
            .filter(|w| !w.is_empty())?;
        let fstar_pos = lsp_to_fstar_pos(position);

        // Try lax connection first (faster), fall back to full
        let lookup_result = if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            fstar_lax
                .lookup(&word, &self.file_path, fstar_pos)
                .await
                .ok()
                .flatten()
        } else {
            None
        };

        let lookup_result = match lookup_result {
            Some(r) => Some(r),
            None => {
                if let Some(fstar) = self.fstar.lock().await.as_ref() {
                    fstar
                        .lookup(&word, &self.file_path, fstar_pos)
                        .await
                        .ok()
                        .flatten()
                } else {
                    None
                }
            }
        };

        match lookup_result {
            Some(LookupResponse::Symbol(sym)) => {
                if let Some(defined_at) = sym.defined_at {
                    if !defined_at.is_dummy() {
                        // Resolve symlinks so go-to-definition lands on the real file
                        let path = std::path::Path::new(&defined_at.fname);
                        let resolved = tokio::fs::canonicalize(path).await.ok();
                        let uri = resolved
                            .as_deref()
                            .unwrap_or(path)
                            .to_str()
                            .and_then(|s| Url::from_file_path(s).ok())?;

                        return Some(tower_lsp::lsp_types::Location {
                            uri,
                            range: defined_at.to_lsp_range(),
                        });
                    }
                }
                None
            }
            Some(LookupResponse::Module(module)) => {
                // Navigate to the module file at line 0 (beginning of file)
                let path = std::path::Path::new(&module.path);
                let resolved = tokio::fs::canonicalize(path).await.ok();
                let uri = resolved
                    .as_deref()
                    .unwrap_or(path)
                    .to_str()
                    .and_then(|s| Url::from_file_path(s).ok())?;

                Some(tower_lsp::lsp_types::Location {
                    uri,
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: 0,
                            character: 0,
                        },
                    },
                })
            }
            None => None,
        }
    }

    pub async fn completions(
        &self,
        position: Position,
    ) -> Vec<tower_lsp::lsp_types::CompletionItem> {
        let word = self
            .get_word_at_position(position)
            .await
            .unwrap_or_default();

        // M13: Minimum word length guard to avoid slow queries returning thousands of results
        if word.len() < 2 {
            return vec![];
        }

        // H7: Try lax connection first (faster), fall back to main connection
        let candidates = if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            fstar_lax.autocomplete(&word).await.ok()
        } else {
            None
        };

        let candidates = match candidates {
            Some(c) if !c.is_empty() => c,
            _ => {
                // Fallback to main connection when lax unavailable or returned empty/error
                if let Some(fstar) = self.fstar.lock().await.as_ref() {
                    fstar.autocomplete(&word).await.unwrap_or_default()
                } else {
                    return vec![];
                }
            }
        };

        candidates
            .into_iter()
            .map(|c| {
                // Strip qualified prefix to prevent duplicate prefixes when completing.
                // E.g., "FStar.List.length" -> "length" so accepting completion on
                // "FStar.List.le" produces "FStar.List.length" not "FStar.List.FStar.List.length"
                let label = if let Some(dot_pos) = c.candidate.rfind('.') {
                    c.candidate[dot_pos + 1..].to_string()
                } else {
                    c.candidate.clone()
                };

                // Use match_length as sort priority (higher match_length = better match = lower sort_text).
                // LSP clients sort by sort_text ascending, so better matches appear first.
                // Format with 5 digits for consistent lexicographic ordering up to 99999.
                let sort_text = format!("{:05}", 99999_u32.saturating_sub(c.match_length));

                tower_lsp::lsp_types::CompletionItem {
                    label,
                    detail: Some(c.annotation),
                    // M12: Set CompletionItemKind for proper icon display in editors
                    kind: Some(tower_lsp::lsp_types::CompletionItemKind::FUNCTION),
                    sort_text: Some(sort_text),
                    ..Default::default()
                }
            })
            .collect()
    }

    pub async fn format(&self) -> Option<String> {
        let text = self.text.read().await.clone();

        // Try lax connection first (usually not running long FBQs).
        // Format requests through the main connection get BUFFERED during
        // full-buffer queries, causing hangs until verification completes or timeout.
        if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            if let Ok(formatted) = fstar_lax.format(&text).await {
                if formatted.is_some() {
                    return formatted;
                }
            }
        }

        // Fallback to main connection
        if let Some(fstar) = self.fstar.lock().await.as_ref() {
            if let Ok(formatted) = fstar.format(&text).await {
                return formatted;
            }
        }

        None
    }

    /// Extracts text within the given LSP range from the document.
    ///
    /// Converts LSP positions (UTF-16 code units) to byte offsets and returns
    /// the substring between them. Returns None if the range is invalid.
    pub async fn get_text_in_range(&self, range: Range) -> Option<String> {
        let text = self.text.read().await;
        let start_offset = self.position_to_offset(&text, range.start).ok()?;
        let end_offset = self.position_to_offset(&text, range.end).ok()?;

        if start_offset <= end_offset && end_offset <= text.len() {
            Some(text[start_offset..end_offset].to_string())
        } else {
            None
        }
    }

    /// Formats the given text using the F* formatter.
    ///
    /// Tries the lax connection first (faster response and not blocked by FBQs),
    /// falling back to the main connection if lax is unavailable.
    pub async fn format_text(&self, text: &str) -> Option<String> {
        // Try lax connection first (usually not running long FBQs).
        // Format requests through the main connection get BUFFERED during
        // full-buffer queries, causing hangs until verification completes or timeout.
        if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
            if let Ok(Some(formatted)) = fstar_lax.format(text).await {
                return Some(formatted);
            }
        }

        // Fall back to main connection
        if let Some(fstar) = self.fstar.lock().await.as_ref() {
            if let Ok(formatted) = fstar.format(text).await {
                return formatted;
            }
        }

        None
    }

    pub async fn restart(&self) -> Result<()> {
        // Set restarting flag to prevent update() from sending vfs_add to dead connections.
        // The flag ensures that edits during restart are still applied to self.text,
        // and we re-sync after initialize() to avoid stale file content.
        *self.restarting.write().await = true;

        if let Some(mut fstar) = self.fstar.lock().await.take() {
            fstar.kill().await;
        }
        if let Some(mut fstar_lax) = self.fstar_lax.lock().await.take() {
            fstar_lax.kill().await;
        }

        self.results.write().await.clear();
        let result = self.initialize().await;

        // Clear restarting flag after connections are re-established
        *self.restarting.write().await = false;

        // Re-sync text content to the new F* processes. This handles any edits
        // that occurred during the restart window (after take() but before initialize()).
        // The initialize() method syncs text at that moment, but edits during the
        // window would be lost without this explicit re-sync.
        if result.is_ok() {
            let text = self.text.read().await.clone();
            if let Some(fstar) = self.fstar.lock().await.as_ref() {
                let _ = fstar
                    .vfs_add(Some(&self.file_path.to_string_lossy()), &text)
                    .await;
            }
            if let Some(fstar_lax) = self.fstar_lax.lock().await.as_ref() {
                let _ = fstar_lax
                    .vfs_add(Some(&self.file_path.to_string_lossy()), &text)
                    .await;
            }
        }

        result
    }

    pub async fn restart_solver(&self) -> Result<()> {
        if let Some(fstar) = self.fstar.lock().await.as_ref() {
            fstar.restart_solver().await?;
        }
        Ok(())
    }

    pub async fn dispose(&self) {
        *self.disposed.write().await = true;

        if let Some(mut fstar) = self.fstar.lock().await.take() {
            fstar.kill().await;
        }
        if let Some(mut fstar_lax) = self.fstar_lax.lock().await.take() {
            fstar_lax.kill().await;
        }

        // Clear UI by sending empty status update.
        // This removes stale fragment indicators and diagnostics from the editor
        // when the document is closed, matching the TypeScript implementation.
        let _ = self
            .status_tx
            .send(StatusUpdate {
                uri: self.uri.clone(),
                fragments: vec![],
                diagnostics: vec![],
            })
            .await;
    }
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '.'
}

/// Converts a UTF-16 column offset to a byte offset within a line.
///
/// LSP `Position.character` is specified in UTF-16 code units, not bytes.
/// This function handles the conversion properly for all Unicode characters,
/// including those outside the BMP (like emoji) which use surrogate pairs.
///
/// Returns `Err(InvalidPosition)` if the UTF-16 offset is invalid (points past
/// end of line or into the middle of a surrogate pair).
fn utf16_to_byte_offset(
    line: &str,
    utf16_col: u32,
    line_num: u32,
) -> std::result::Result<usize, FstarError> {
    let mut utf16_offset = 0u32;
    for (byte_idx, ch) in line.char_indices() {
        if utf16_offset == utf16_col {
            return Ok(byte_idx);
        }
        utf16_offset += ch.len_utf16() as u32;
    }
    // Check if pointing to end of line
    if utf16_offset == utf16_col {
        Ok(line.len())
    } else {
        Err(FstarError::InvalidPosition {
            line: line_num,
            column: utf16_col,
        })
    }
}

/// Converts a UTF-16 column offset to a character index within a line.
///
/// Similar to `utf16_to_byte_offset`, but returns an index suitable for
/// indexing into a `Vec<char>` rather than byte slicing.
///
/// Returns `Err(InvalidPosition)` if the UTF-16 offset is invalid.
fn utf16_to_char_index(
    line: &str,
    utf16_col: u32,
    line_num: u32,
) -> std::result::Result<usize, FstarError> {
    let mut utf16_offset = 0u32;
    for (char_idx, ch) in line.chars().enumerate() {
        if utf16_offset == utf16_col {
            return Ok(char_idx);
        }
        utf16_offset += ch.len_utf16() as u32;
    }
    // Check if pointing to end of line
    if utf16_offset == utf16_col {
        Ok(line.chars().count())
    } else {
        Err(FstarError::InvalidPosition {
            line: line_num,
            column: utf16_col,
        })
    }
}

fn format_proof_state(ps: &IdeProofState) -> String {
    let mut result = String::new();
    // L3: Apply depth-based indentation to show nesting of tactic dump calls.
    // Depth represents how deeply nested the dump call is within tactic execution.
    let indent = "  ".repeat(ps.depth.max(0) as usize);

    if !ps.label.is_empty() {
        result.push_str(&format!("{}**{}**\n\n", indent, ps.label));
    }

    for (i, goal) in ps.goals.iter().enumerate() {
        result.push_str(&format!(
            "{}**Goal {}**\n{}```fstar\n",
            indent,
            i + 1,
            indent
        ));

        for hyp in &goal.hyps {
            result.push_str(&format!("{}{} : {}\n", indent, hyp.name, hyp.typ));
        }

        // L5: Show goal label on separator line if present.
        let separator = if !goal.goal.label.is_empty() {
            format!("{}──────────── ({})\n", indent, goal.goal.label)
        } else {
            format!("{}────────────────────\n", indent)
        };
        result.push_str(&separator);
        result.push_str(&format!(
            "{}{} : {}\n{}```\n\n",
            indent, goal.goal.witness, goal.goal.typ, indent
        ));
    }

    if !ps.smt_goals.is_empty() {
        result.push_str(&format!(
            "{}\n{}**SMT Goals:** {}\n",
            indent,
            indent,
            ps.smt_goals.len()
        ));
    }

    result
}

fn format_lookup_response(response: &LookupResponse) -> String {
    match response {
        LookupResponse::Symbol(sym) => {
            let mut result = String::new();

            // Show both the queried symbol and resolved name when they differ.
            // This helps users understand name resolution: "length" -> "FStar.List.Tot.Base.length"
            if let Some(queried) = &sym.symbol {
                if queried != &sym.name {
                    tracing::debug!("Lookup '{}' resolved to '{}'", queried, sym.name);
                    result.push_str(&format!("**{}** -> `{}`\n\n", queried, sym.name));
                } else {
                    result.push_str(&format!("**{}**\n\n", sym.name));
                }
            } else {
                result.push_str(&format!("**{}**\n\n", sym.name));
            }

            if let Some(typ) = &sym.typ {
                result.push_str(&format!("```fstar\n{}\n```\n\n", typ));
            }

            if let Some(def) = &sym.definition {
                if !def.is_empty() {
                    result.push_str(&format!("**Definition:**\n```fstar\n{}\n```\n\n", def));
                }
            }

            if let Some(doc) = &sym.documentation {
                if !doc.is_empty() {
                    result.push_str(&format!("{}\n", doc));
                }
            }

            result
        }
        LookupResponse::Module(module) => {
            format!(
                "**Module:** {}\n\nPath: {}\nLoaded: {}",
                module.name, module.path, module.loaded
            )
        }
    }
}

/// Extracts the symbol_range from a lookup response for use as hover highlight range.
///
/// Returns the LSP range if the lookup response contains a symbol with a valid
/// (non-dummy) symbol_range, which allows the editor to highlight the exact symbol.
fn extract_symbol_range(response: &LookupResponse) -> Option<Range> {
    match response {
        LookupResponse::Symbol(sym) => sym
            .symbol_range
            .as_ref()
            .filter(|r| !r.is_dummy())
            .map(|r| r.to_lsp_range()),
        LookupResponse::Module(_) => None,
    }
}
