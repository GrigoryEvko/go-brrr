//! F* process connection handling via JSONL protocol.

use crate::config::FstarConfig;
use crate::error::{FstarError, Result};
use crate::protocol::*;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};
use tokio::sync::{mpsc, oneshot, Mutex};
use tokio::time::{timeout, Duration};
use tracing::{debug, error, info, warn};

/// Maximum buffer size for JSONL input (100MB).
const MAX_BUFFER_SIZE: usize = 100 * 1024 * 1024;

/// Query ID counter.
static QUERY_ID: AtomicU64 = AtomicU64::new(1);

fn next_query_id() -> String {
    QUERY_ID.fetch_add(1, Ordering::SeqCst).to_string()
}

/// Pending response handler.
struct PendingQuery {
    tx: oneshot::Sender<Result<Response>>,
}

/// A buffered request waiting for FBQ to complete.
struct BufferedRequest {
    json: String,
    query_id: String,
    tx: oneshot::Sender<Result<Response>>,
}

/// Full buffer query state.
struct FullBufferState {
    query_id: String,
    response_tx: mpsc::Sender<Response>,
}

/// Connection to a single F* process.
pub struct FstarConnection {
    /// Process handle.
    child: Child,

    /// Stdin for sending queries.
    stdin: Arc<Mutex<ChildStdin>>,

    /// Pending query responses.
    pending: Arc<Mutex<HashMap<String, PendingQuery>>>,

    /// Current full-buffer query state.
    fbq_state: Arc<Mutex<Option<FullBufferState>>>,

    /// Requests buffered during an in-progress FBQ, replayed when FBQ finishes.
    buffered_requests: Arc<Mutex<Vec<BufferedRequest>>>,

    /// Protocol info from F*.
    protocol_info: Arc<Mutex<Option<ProtocolInfo>>>,

    /// Whether this is a lax-mode connection.
    #[allow(dead_code)]
    pub is_lax: bool,

    /// Debug mode.
    debug: bool,

    /// File path this connection is for.
    pub file_path: PathBuf,

    /// Timeout for queries in milliseconds.
    timeout_ms: u64,
}

impl FstarConnection {
    /// Spawn a new F* process and create a connection.
    pub async fn spawn(
        config: &FstarConfig,
        file_path: &Path,
        lax: bool,
        timeout_ms: u64,
        debug: bool,
    ) -> Result<Self> {
        let fstar_exe = config.resolve_fstar_exe()?;
        let cwd = config.get_cwd(file_path);
        let args = config.build_args(lax);

        info!(
            "Spawning F*: {} {:?} (lax: {}, cwd: {})",
            fstar_exe.display(),
            args,
            lax,
            cwd.display()
        );

        let mut child = Command::new(&fstar_exe)
            .args(&args)
            .arg(file_path)
            .current_dir(&cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true)
            .spawn()
            .map_err(|e| FstarError::Process(format!("Failed to spawn F*: {}", e)))?;

        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| FstarError::Process("Failed to get stdin handle".to_string()))?;

        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| FstarError::Process("Failed to get stdout handle".to_string()))?;

        let stderr = child.stderr.take();

        let conn = Self {
            child,
            stdin: Arc::new(Mutex::new(stdin)),
            pending: Arc::new(Mutex::new(HashMap::new())),
            fbq_state: Arc::new(Mutex::new(None)),
            buffered_requests: Arc::new(Mutex::new(Vec::new())),
            protocol_info: Arc::new(Mutex::new(None)),
            is_lax: lax,
            debug,
            file_path: file_path.to_path_buf(),
            timeout_ms,
        };

        // Start stdout reader task
        conn.spawn_reader(stdout);

        // Start stderr reader task
        if let Some(stderr) = stderr {
            conn.spawn_stderr_reader(stderr);
        }

        Ok(conn)
    }

    /// Spawn the stdout reader task.
    fn spawn_reader(&self, stdout: ChildStdout) {
        let pending = Arc::clone(&self.pending);
        let fbq_state = Arc::clone(&self.fbq_state);
        let buffered_requests = Arc::clone(&self.buffered_requests);
        let stdin = Arc::clone(&self.stdin);
        let protocol_info = Arc::clone(&self.protocol_info);
        let debug = self.debug;

        tokio::spawn(async move {
            let mut reader = BufReader::new(stdout);
            let mut line = String::new();

            loop {
                line.clear();
                match reader.read_line(&mut line).await {
                    Ok(0) => {
                        debug!("F* stdout closed");
                        break;
                    }
                    Ok(_) => {
                        if line.trim().is_empty() {
                            continue;
                        }

                        if debug {
                            debug!("F* -> {}", line.trim());
                        }

                        match serde_json::from_str::<serde_json::Value>(&line) {
                            Ok(value) => {
                                Self::handle_message(
                                    value,
                                    &pending,
                                    &fbq_state,
                                    &buffered_requests,
                                    &stdin,
                                    &protocol_info,
                                    debug,
                                )
                                .await;
                            }
                            Err(e) => {
                                error!("Failed to parse F* message: {} - {}", e, line.trim());
                            }
                        }
                    }
                    Err(e) => {
                        error!("Error reading F* stdout: {}", e);
                        break;
                    }
                }

                if line.len() > MAX_BUFFER_SIZE {
                    error!("F* output line too large, dropping");
                    line.clear();
                }
            }

            // Reject all pending queries on connection close
            let mut pending = pending.lock().await;
            for (_, pq) in pending.drain() {
                let _ = pq.tx.send(Err(FstarError::ConnectionClosed));
            }

            // Reject all buffered requests
            let mut buffered = buffered_requests.lock().await;
            for br in buffered.drain(..) {
                let _ = br.tx.send(Err(FstarError::ConnectionClosed));
            }
        });
    }

    /// Spawn stderr reader task.
    fn spawn_stderr_reader(&self, stderr: tokio::process::ChildStderr) {
        let debug = self.debug;
        tokio::spawn(async move {
            let mut reader = BufReader::new(stderr);
            let mut line = String::new();

            loop {
                line.clear();
                match reader.read_line(&mut line).await {
                    Ok(0) => break,
                    Ok(_) => {
                        if debug {
                            debug!("F* stderr: {}", line.trim());
                        }
                    }
                    Err(e) => {
                        error!("Error reading F* stderr: {}", e);
                        break;
                    }
                }
            }
        });
    }

    /// Handle a message from F*.
    async fn handle_message(
        value: serde_json::Value,
        pending: &Mutex<HashMap<String, PendingQuery>>,
        fbq_state: &Mutex<Option<FullBufferState>>,
        buffered_requests: &Mutex<Vec<BufferedRequest>>,
        stdin: &Mutex<ChildStdin>,
        protocol_info: &Mutex<Option<ProtocolInfo>>,
        debug_mode: bool,
    ) {
        // Check for protocol-info message
        if value.get("kind").and_then(|k| k.as_str()) == Some("protocol-info") {
            match serde_json::from_value::<ProtocolInfo>(value) {
                Ok(info) => {
                    debug!(
                        "F* protocol version: {}, features: {:?}",
                        info.version, info.features
                    );
                    *protocol_info.lock().await = Some(info);
                }
                Err(e) => {
                    error!("Failed to parse protocol-info message: {}", e);
                }
            }
            return;
        }

        // Parse as response
        let response: Response = match serde_json::from_value(value.clone()) {
            Ok(r) => r,
            Err(e) => {
                // Try to extract query-id to notify the pending query of the protocol error
                if let Some(qid) = value.get("query-id").and_then(|q| q.as_str()) {
                    let base_qid = qid.split('.').next().unwrap_or(qid).to_string();
                    if let Some(pq) = pending.lock().await.remove(&base_qid) {
                        let _ = pq.tx.send(Err(FstarError::Protocol(format!(
                            "Invalid response format: {}",
                            e
                        ))));
                    }
                }
                error!("Failed to parse F* response: {} - {:?}", e, value);
                return;
            }
        };

        // Extract base query ID (before any dot)
        let base_qid = response
            .query_id
            .split('.')
            .next()
            .unwrap_or(&response.query_id)
            .to_string();

        // Check if this is a full-buffer query response
        let is_fbq = {
            let state = fbq_state.lock().await;
            state
                .as_ref()
                .map(|s| s.query_id == base_qid)
                .unwrap_or(false)
        };

        if is_fbq {
            let is_done = response.is_done();

            // Forward to FBQ handler
            if let Some(state) = fbq_state.lock().await.as_ref() {
                let _ = state.response_tx.send(response).await;
            }

            // Clear FBQ state and replay buffered requests
            if is_done {
                *fbq_state.lock().await = None;

                let buffered: Vec<BufferedRequest> =
                    buffered_requests.lock().await.drain(..).collect();
                if !buffered.is_empty() {
                    debug!("Replaying {} buffered requests after FBQ", buffered.len());
                    let mut writer = stdin.lock().await;
                    for br in buffered {
                        if debug_mode {
                            debug!("-> F* (replay): {}", br.json);
                        }
                        match writer.write_all(br.json.as_bytes()).await {
                            Ok(()) => {
                                let _ = writer.write_all(b"\n").await;
                                let _ = writer.flush().await;
                                pending
                                    .lock()
                                    .await
                                    .insert(br.query_id, PendingQuery { tx: br.tx });
                            }
                            Err(e) => {
                                error!("Failed to replay buffered request: {}", e);
                                let _ = br.tx.send(Err(FstarError::ConnectionClosed));
                            }
                        }
                    }
                }
            }
        } else {
            // Regular query response
            if let Some(pq) = pending.lock().await.remove(&base_qid) {
                // Convert protocol-violation responses to Protocol errors
                if response.is_protocol_violation() {
                    let msg = response
                        .protocol_violation_message()
                        .unwrap_or_else(|| "Protocol violation".to_string());
                    let _ = pq.tx.send(Err(FstarError::Protocol(msg)));
                } else {
                    let _ = pq.tx.send(Ok(response));
                }
            }
        }
    }

    /// Send a query and wait for response.
    /// If a full-buffer query is in progress, the request is buffered and replayed
    /// when the FBQ completes. VFS-add requests bypass buffering since they're
    /// needed to keep the F* process in sync.
    pub async fn request<A: serde::Serialize>(&self, query: &str, args: A) -> Result<Response> {
        if !self.is_alive() {
            return Err(FstarError::ConnectionClosed);
        }

        let qid = next_query_id();
        let msg = Query {
            query_id: qid.clone(),
            query: query.to_string(),
            args,
        };

        // Buffer non-vfs requests during FBQ.
        // FIX C1: Hold fbq_state lock through the check AND the buffering decision
        // to prevent TOCTOU race where FBQ finishes and drains buffer between check and push.
        if query != "vfs-add" && query != "cancel" {
            let fbq_guard = self.fbq_state.lock().await;
            if fbq_guard.is_some() {
                let json = serde_json::to_string(&msg)?;
                let (tx, rx) = oneshot::channel();
                debug!("Buffering request '{}' (qid={}) during FBQ", query, qid);
                self.buffered_requests.lock().await.push(BufferedRequest {
                    json,
                    query_id: qid.clone(),
                    tx,
                });
                // Release lock after buffering is complete
                drop(fbq_guard);

                return match timeout(Duration::from_millis(self.timeout_ms), rx).await {
                    Ok(Ok(result)) => result,
                    Ok(Err(_)) => Err(FstarError::ConnectionClosed),
                    Err(_) => Err(FstarError::Timeout(self.timeout_ms)),
                };
            }
            // fbq_guard dropped here if FBQ not active
        }

        let (tx, rx) = oneshot::channel();
        self.pending
            .lock()
            .await
            .insert(qid.clone(), PendingQuery { tx });

        self.send_raw(&msg).await?;

        match timeout(Duration::from_millis(self.timeout_ms), rx).await {
            Ok(Ok(result)) => result,
            Ok(Err(_)) => Err(FstarError::ConnectionClosed),
            Err(_) => {
                self.pending.lock().await.remove(&qid);
                Err(FstarError::Timeout(self.timeout_ms))
            }
        }
    }

    /// Send a raw message to F*.
    async fn send_raw<T: serde::Serialize>(&self, msg: &T) -> Result<()> {
        let json = serde_json::to_string(msg)?;
        if self.debug {
            debug!("-> F*: {}", json);
        }

        let mut stdin = self.stdin.lock().await;
        stdin.write_all(json.as_bytes()).await?;
        stdin.write_all(b"\n").await?;
        stdin.flush().await?;
        Ok(())
    }

    /// Start a full-buffer query, returning a channel for streaming responses.
    /// Returns an error if the F* process does not support full-buffer queries.
    pub async fn full_buffer_query(
        &self,
        code: &str,
        kind: FullBufferKind,
        to_position: Option<(u32, u32)>,
    ) -> Result<mpsc::Receiver<Response>> {
        // Check if process is alive before any state changes
        if !self.is_alive() {
            return Err(FstarError::ConnectionClosed);
        }

        // Check if F* supports full-buffer queries before attempting
        if !self.supports_full_buffer().await {
            return Err(FstarError::Protocol(
                "F* process does not support full-buffer queries".to_string(),
            ));
        }

        let qid = next_query_id();

        let args = FullBufferArgs {
            kind,
            with_symbols: false,
            code: code.to_string(),
            line: 1,
            column: 0,
            to_position: to_position.map(|(line, col)| ToPosition { line, column: col }),
        };

        let msg = Query {
            query_id: qid.clone(),
            query: "full-buffer".to_string(),
            args,
        };

        // Create response channel
        let (tx, rx) = mpsc::channel(100);

        // FIX C2: Check for active FBQ before setting new state.
        // If an FBQ is already in progress, reject this request to prevent
        // orphaning the previous FBQ's response channel.
        let mut fbq_guard = self.fbq_state.lock().await;
        if fbq_guard.is_some() {
            return Err(FstarError::Process(
                "Full buffer query already in progress".to_string(),
            ));
        }

        // Set FBQ state while holding the lock
        *fbq_guard = Some(FullBufferState {
            query_id: qid,
            response_tx: tx,
        });

        // Send query - FIX C3: Roll back fbq_state if send fails
        if let Err(e) = self.send_raw(&msg).await {
            *fbq_guard = None;
            return Err(e);
        }

        // Release lock after successful send
        drop(fbq_guard);

        Ok(rx)
    }

    /// Cancel current full-buffer query.
    pub async fn cancel_fbq(&self, position: (u32, u32)) -> Result<()> {
        // Check if process is alive before attempting cancel
        if !self.is_alive() {
            return Err(FstarError::ConnectionClosed);
        }

        if self.fbq_state.lock().await.is_none() {
            return Ok(());
        }

        let args = CancelArgs {
            cancel_line: position.0,
            cancel_column: position.1,
        };

        let msg = Query {
            query_id: next_query_id(),
            query: "cancel".to_string(),
            args,
        };

        self.send_raw(&msg).await
    }

    /// Request symbol lookup.
    /// For F* IDE protocol version < 3, the filename is mapped to "<input>".
    pub async fn lookup(
        &self,
        symbol: &str,
        file_path: &Path,
        position: (u32, u32),
    ) -> Result<Option<LookupResponse>> {
        // Map filename for compatibility with older F* IDE protocol versions
        let filename = self.map_input_filename(&file_path.to_string_lossy()).await;

        let args = LookupArgs {
            context: "code".to_string(),
            symbol: symbol.to_string(),
            requested_info: vec![
                "type".to_string(),
                "documentation".to_string(),
                "defined-at".to_string(),
            ],
            location: LookupLocation {
                filename,
                line: position.0,
                column: position.1,
            },
            symbol_range: None,
        };

        let response = self.request("lookup", args).await?;

        if response.is_success() {
            if let Some(resp) = response.response {
                return Ok(serde_json::from_value(resp).ok());
            }
        }

        Ok(None)
    }

    /// Request autocomplete.
    pub async fn autocomplete(&self, partial: &str) -> Result<Vec<AutocompleteCandidate>> {
        let args = AutocompleteArgs {
            partial_symbol: partial.to_string(),
            context: "code".to_string(),
        };

        let response = self.request("autocomplete", args).await?;

        if response.is_success() {
            if let Some(resp) = response.response {
                return Ok(serde_json::from_value(resp).unwrap_or_default());
            }
        }

        Ok(vec![])
    }

    /// Request code formatting.
    pub async fn format(&self, code: &str) -> Result<Option<String>> {
        let args = FormatArgs {
            code: code.to_string(),
        };

        let response = self.request("format", args).await?;

        if response.is_success() {
            if let Some(resp) = response.response {
                if let Ok(fr) = serde_json::from_value::<FormatResponse>(resp) {
                    return Ok(fr.formatted_code);
                }
            }
        }

        Ok(None)
    }

    /// Add file to virtual file system.
    pub async fn vfs_add(&self, filename: Option<&str>, contents: &str) -> Result<()> {
        let args = VfsAddArgs {
            filename: filename.map(String::from),
            contents: contents.to_string(),
        };

        let _ = self.request("vfs-add", args).await?;
        Ok(())
    }

    /// Restart the Z3 solver.
    /// Includes a 1s delay after killing Z3 to allow processes to fully terminate.
    pub async fn restart_solver(&self) -> Result<()> {
        // Check if process is alive before attempting restart
        if !self.is_alive() {
            return Err(FstarError::ConnectionClosed);
        }

        self.kill_z3_subprocesses().await;

        // Wait for Z3 processes to fully terminate before restarting
        tokio::time::sleep(Duration::from_secs(1)).await;

        let msg = Query {
            query_id: next_query_id(),
            query: "restart-solver".to_string(),
            args: serde_json::Value::Object(serde_json::Map::new()),
        };

        self.send_raw(&msg).await
    }

    /// Kill Z3 subprocesses.
    async fn kill_z3_subprocesses(&self) {
        if let Some(pid) = self.child.id() {
            // Use pkill to kill Z3 children
            let _ = Command::new("pkill")
                .args(["-P", &pid.to_string(), "z3"])
                .output()
                .await;
        }
    }

    /// Check if the process is still running.
    pub fn is_alive(&self) -> bool {
        self.child.id().is_some()
    }

    /// Kill the F* process.
    pub async fn kill(&mut self) {
        self.kill_z3_subprocesses().await;
        let _ = self.child.kill().await;
    }

    /// Get protocol info.
    #[allow(dead_code)] // Internal method for future use
    pub async fn protocol_info(&self) -> Option<ProtocolInfo> {
        self.protocol_info.lock().await.clone()
    }

    /// Wait for protocol info to be received (with timeout).
    /// F* sends protocol-info immediately on connection, so this should resolve quickly.
    /// Returns None if protocol info is not received within the timeout.
    async fn wait_for_protocol_info(&self, timeout_ms: u64) -> Option<ProtocolInfo> {
        let deadline = tokio::time::Instant::now() + Duration::from_millis(timeout_ms);
        let poll_interval = Duration::from_millis(10);

        while tokio::time::Instant::now() < deadline {
            if let Some(info) = self.protocol_info.lock().await.clone() {
                return Some(info);
            }
            tokio::time::sleep(poll_interval).await;
        }

        None
    }

    /// Check if the F* process supports full-buffer queries.
    /// Waits briefly for protocol info if not yet received.
    /// Returns false if protocol info indicates no support or times out.
    pub async fn supports_full_buffer(&self) -> bool {
        // Check if we already have protocol info
        if let Some(info) = self.protocol_info.lock().await.as_ref() {
            return info.features.iter().any(|f| f == "full-buffer");
        }

        // Wait briefly for protocol info (F* sends it immediately on startup)
        if let Some(info) = self.wait_for_protocol_info(1000).await {
            return info.features.iter().any(|f| f == "full-buffer");
        }

        // Default to false if we can't determine support (safer)
        warn!("Protocol info not received within timeout; assuming no full-buffer support");
        false
    }

    /// Get the IDE protocol version from protocol info.
    /// Waits briefly for protocol info if not yet received.
    /// Returns 3 as default (latest version behavior) if protocol info unavailable.
    async fn ide_version(&self) -> u32 {
        // Check if we already have protocol info
        if let Some(info) = self.protocol_info.lock().await.as_ref() {
            return info.version;
        }

        // Wait briefly for protocol info
        if let Some(info) = self.wait_for_protocol_info(1000).await {
            return info.version;
        }

        // Default to version 3 (modern behavior)
        3
    }

    /// Map a filename for use in F* queries.
    /// For IDE protocol version < 3, F* expects "<input>" instead of the actual filename.
    /// This matches the TypeScript implementation's mapInputFileHack().
    pub async fn map_input_filename(&self, filename: &str) -> String {
        let version = self.ide_version().await;
        if version < 3 {
            "<input>".to_string()
        } else {
            filename.to_string()
        }
    }
}

impl Drop for FstarConnection {
    fn drop(&mut self) {
        // Process will be killed due to kill_on_drop(true)
        debug!("Dropping F* connection for {}", self.file_path.display());
    }
}
