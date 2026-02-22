//! LSP server implementation.

use crate::config::{FstarConfig, LspSettings};
use crate::document::{DocumentState, FragmentStatus, StatusUpdate};
use crate::error::Result;
use crate::lint::lsp::{self as lint_lsp, LintBackend, LintSettings};
use crate::lint::Diagnostic as LintDiagnostic;
use dashmap::DashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use tower_lsp::jsonrpc::Result as RpcResult;
use tower_lsp::lsp_types::{
    self, CodeActionOrCommand, CodeActionParams, CodeActionProviderCapability, CodeActionResponse,
    CompletionOptions, CompletionParams, CompletionResponse, DidChangeConfigurationParams,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, DocumentFormattingParams, DocumentRangeFormattingParams,
    GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverContents, HoverParams,
    HoverProviderCapability, InitializeParams, InitializeResult, InitializedParams, MarkupContent,
    MarkupKind, MessageType, NumberOrString, OneOf, Position, ProgressParams, ProgressParamsValue,
    Range, SaveOptions, ServerCapabilities, ServerInfo, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, TextDocumentSyncSaveOptions, TextEdit, Url,
    WorkDoneProgress, WorkDoneProgressCreateParams, WorkspaceFolder,
};
use tower_lsp::{Client, LanguageServer};
use tracing::{debug, error, info};

/// Custom LSP requests for F*.
///
/// These requests allow clients to query the current verification state
/// without relying on notifications. Useful for custom UI, debugging tools,
/// or integration with other extensions.
pub mod requests {
    use serde::{Deserialize, Serialize};
    use tower_lsp::lsp_types::{Range, TextDocumentIdentifier};

    /// Parameters for getDiagnostics request.
    pub type GetDiagnosticsParams = TextDocumentIdentifier;

    /// Parameters for getFragments request.
    pub type GetFragmentsParams = TextDocumentIdentifier;

    /// Information about a verified code fragment.
    ///
    /// Provides the verification status and range of each fragment
    /// in the document, enabling clients to display custom verification
    /// progress indicators.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct FragmentInfo {
        /// The range of the fragment in the document.
        pub range: Range,
        /// Verification status: "ok", "lax-ok", "in-progress", "started", or "failed".
        pub status: String,
        /// True if the fragment was invalidated by an edit (stale result).
        #[serde(skip_serializing_if = "std::ops::Not::not")]
        pub stale: bool,
    }
}

/// Custom LSP notifications for F*.
pub mod notifications {
    use serde::{Deserialize, Serialize};
    use tower_lsp::lsp_types::notification::Notification;

    /// Status notification: server -> client.
    #[derive(Debug)]
    pub enum StatusNotification {}

    impl Notification for StatusNotification {
        type Params = StatusParams;
        const METHOD: &'static str = "$/fstar/status";
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct StatusParams {
        pub uri: String,
        pub fragments: Vec<FragmentStatus>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct FragmentStatus {
        pub kind: String,
        pub range: tower_lsp::lsp_types::Range,
        #[serde(skip_serializing_if = "std::ops::Not::not")]
        pub stale: bool,
    }

    /// Verify to position: client -> server.
    ///
    /// The enum type is never directly referenced - handlers are registered
    /// with string method names. However, this enum defines the protocol
    /// contract (METHOD constant and Params type) for documentation and
    /// type safety when tower-lsp deserializes incoming notifications.
    #[allow(dead_code)]
    #[derive(Debug)]
    pub enum VerifyToPosition {}

    impl Notification for VerifyToPosition {
        type Params = VerifyToPositionParams;
        const METHOD: &'static str = "$/fstar/verifyToPosition";
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct VerifyToPositionParams {
        pub uri: String,
        pub position: tower_lsp::lsp_types::Position,
        pub lax: bool,
    }

    /// Restart: client -> server.
    ///
    /// Protocol marker enum - see VerifyToPosition for explanation.
    #[allow(dead_code)]
    #[derive(Debug)]
    pub enum Restart {}

    impl Notification for Restart {
        type Params = RestartParams;
        const METHOD: &'static str = "$/fstar/restart";
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct RestartParams {
        pub uri: String,
    }

    /// Kill and restart solver: client -> server.
    ///
    /// Protocol marker enum - see VerifyToPosition for explanation.
    #[allow(dead_code)]
    #[derive(Debug)]
    pub enum KillAndRestartSolver {}

    impl Notification for KillAndRestartSolver {
        type Params = KillAndRestartSolverParams;
        const METHOD: &'static str = "$/fstar/killAndRestartSolver";
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct KillAndRestartSolverParams {
        pub uri: String,
    }

    /// Kill all: client -> server.
    ///
    /// Protocol marker enum - see VerifyToPosition for explanation.
    #[allow(dead_code)]
    #[derive(Debug)]
    pub enum KillAll {}

    impl Notification for KillAll {
        type Params = KillAllParams;
        const METHOD: &'static str = "$/fstar/killAll";
    }

    /// Parameters for kill all notification (empty object).
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct KillAllParams {}

    /// Get translated F* position (C2Pulse): client -> server request.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct GetTranslatedFstParams {
        pub uri: String,
        pub position: tower_lsp::lsp_types::Position,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct GetTranslatedFstResponse {
        pub uri: String,
        pub position: tower_lsp::lsp_types::Position,
    }
}

/// F* Language Server.
pub struct FstarServer {
    /// LSP client for sending notifications.
    client: Client,

    /// Document states indexed by URI.
    documents: DashMap<String, Arc<DocumentState>>,

    /// LSP settings.
    settings: RwLock<LspSettings>,

    /// Status update sender.
    status_tx: mpsc::Sender<StatusUpdate>,

    /// Workspace folders.
    workspace_folders: RwLock<Vec<WorkspaceFolder>>,

    /// Per-document flycheck debounce handles.
    /// Stores an abort handle that cancels the previous flycheck task.
    flycheck_handles: DashMap<String, tokio::task::AbortHandle>,

    // ---- Lint integration ------------------------------------------------

    /// Lint backend (thread-safe, shared with background tasks).
    ///
    /// Wrapped in `std::sync::RwLock` so that `did_change_configuration` can
    /// hot-swap the backend when the client sends new lint settings (select/ignore).
    /// Readers (lint_document, did_change) briefly read-lock to clone the `Arc`.
    lint_backend: std::sync::RwLock<Arc<LintBackend>>,

    /// Per-document lint LSP diagnostics for merging with F* diagnostics.
    lint_lsp_diagnostics: Arc<DashMap<String, Vec<lsp_types::Diagnostic>>>,

    /// Per-document raw lint diagnostics (carry `Fix` payloads for code actions).
    lint_raw_diagnostics: DashMap<String, Vec<LintDiagnostic>>,

    /// Per-document lint debounce handles (separate from flycheck).
    lint_handles: DashMap<String, tokio::task::AbortHandle>,

    /// Lint settings from workspace configuration.
    lint_settings: RwLock<LintSettings>,

    /// Whether the client supports `window/workDoneProgress`.
    supports_progress: std::sync::atomic::AtomicBool,
}

impl FstarServer {
    /// Create a new F* server with CLI-derived settings.
    pub fn new(client: Client, cli_settings: LspSettings) -> Self {
        let (status_tx, status_rx) = mpsc::channel(100);

        let lint_lsp_diagnostics = Arc::new(DashMap::new());
        let lint_backend = std::sync::RwLock::new(Arc::new(LintBackend::default_backend()));

        let server = Self {
            client: client.clone(),
            documents: DashMap::new(),
            settings: RwLock::new(cli_settings),
            status_tx,
            workspace_folders: RwLock::new(Vec::new()),
            flycheck_handles: DashMap::new(),
            lint_backend,
            lint_lsp_diagnostics: Arc::clone(&lint_lsp_diagnostics),
            lint_raw_diagnostics: DashMap::new(),
            lint_handles: DashMap::new(),
            lint_settings: RwLock::new(LintSettings::default()),
            supports_progress: std::sync::atomic::AtomicBool::new(false),
        };

        // Spawn status update handler (receives F* diagnostics and merges with lint).
        tokio::spawn(Self::status_update_handler(
            client,
            status_rx,
            lint_lsp_diagnostics,
        ));

        server
    }

    /// Handle status updates from F* and forward merged diagnostics to the client.
    ///
    /// Merges F* verification diagnostics with cached lint diagnostics so that
    /// a `publishDiagnostics` call never accidentally clobbers lint results.
    async fn status_update_handler(
        client: Client,
        mut rx: mpsc::Receiver<StatusUpdate>,
        lint_diags: Arc<DashMap<String, Vec<lsp_types::Diagnostic>>>,
    ) {
        while let Some(update) = rx.recv().await {
            let params = notifications::StatusParams {
                uri: update.uri.to_string(),
                fragments: update
                    .fragments
                    .iter()
                    .map(|f| notifications::FragmentStatus {
                        kind: match f.status {
                            FragmentStatus::Ok => "ok",
                            FragmentStatus::LaxOk => "lax-ok",
                            FragmentStatus::Started => "started",
                            FragmentStatus::Failed => "failed",
                        }
                        .to_string(),
                        range: f.range,
                        stale: f.stale,
                    })
                    .collect(),
            };

            client
                .send_notification::<notifications::StatusNotification>(params)
                .await;

            // Merge F* diagnostics with lint diagnostics before publishing.
            let mut merged = update.diagnostics;
            if let Some(entry) = lint_diags.get(&update.uri.to_string()) {
                merged.extend(entry.value().clone());
            }

            client
                .publish_diagnostics(update.uri, merged, None)
                .await;
        }
    }

    /// Get or create document state.
    async fn get_or_create_document(
        &self,
        uri: &Url,
        text: Option<String>,
        version: i32,
    ) -> Result<Arc<DocumentState>> {
        let key = uri.to_string();

        if let Some(doc) = self.documents.get(&key) {
            return Ok(Arc::clone(&doc));
        }

        // Find config for this file
        let file_path = uri
            .to_file_path()
            .map_err(|_| crate::error::FstarError::Config("Invalid URI".to_string()))?;

        // Collect workspace folder paths for config boundary check
        let ws_folders: Vec<std::path::PathBuf> = self
            .workspace_folders
            .read()
            .await
            .iter()
            .filter_map(|f| Url::parse(f.uri.as_ref()).ok()?.to_file_path().ok())
            .collect();

        let mut config = match FstarConfig::find_and_load(&file_path, &ws_folders).await? {
            Some((config, _)) => config,
            None => FstarConfig::default(),
        };

        // Apply CLI fstar_exe override if config doesn't specify one
        let settings = self.settings.read().await;
        if config.fstar_exe.is_none() {
            if let Some(ref exe) = settings.fstar_exe {
                config.fstar_exe = Some(exe.clone());
            }
        }
        drop(settings);

        let settings = self.settings.read().await.clone();
        let doc = Arc::new(
            DocumentState::new(
                uri.clone(),
                text.unwrap_or_default(),
                version,
                config,
                settings,
                self.status_tx.clone(),
            )
            .await?,
        );

        // Initialize F* connections - if this fails, don't store the broken document
        if let Err(e) = doc.initialize().await {
            error!("Failed to initialize F* for {}: {}", uri, e);
            self.client
                .show_message(MessageType::ERROR, format!("Failed to start F*: {}", e))
                .await;
            return Err(e);
        }

        self.documents.insert(key, Arc::clone(&doc));
        Ok(doc)
    }

    /// Get document state.
    fn get_document(&self, uri: &Url) -> Option<Arc<DocumentState>> {
        self.documents.get(&uri.to_string()).map(|r| Arc::clone(&r))
    }

    /// Remove document state.
    async fn remove_document(&self, uri: &Url) {
        if let Some((_, doc)) = self.documents.remove(&uri.to_string()) {
            doc.dispose().await;
        }
    }

}

#[tower_lsp::async_trait]
impl LanguageServer for FstarServer {
    async fn initialize(&self, params: InitializeParams) -> RpcResult<InitializeResult> {
        info!("F* LSP server initializing");

        // Store workspace folders
        if let Some(folders) = params.workspace_folders {
            *self.workspace_folders.write().await = folders;
        }

        // Check if client supports workDoneProgress for lint progress reporting.
        if let Some(ref general) = params.capabilities.window {
            if let Some(true) = general.work_done_progress {
                self.supports_progress
                    .store(true, std::sync::atomic::Ordering::Relaxed);
            }
        }

        // Parse initialization options if provided, merging with CLI settings.
        // CLI settings (fstar_exe, debug) take precedence over client settings.
        if let Some(ref options) = params.initialization_options {
            if let Ok(client_settings) =
                serde_json::from_value::<LspSettings>(options.clone())
            {
                let mut settings = self.settings.write().await;

                // Preserve CLI fstar_exe if set, otherwise use client value
                let cli_fstar_exe = settings.fstar_exe.clone();

                // Merge client settings
                settings.verify_on_open = client_settings.verify_on_open;
                settings.verify_on_save = client_settings.verify_on_save;
                settings.fly_check = client_settings.fly_check;
                settings.timeout_ms = client_settings.timeout_ms;
                settings.max_processes = client_settings.max_processes;

                // CLI --debug wins (OR with client setting)
                settings.debug = settings.debug || client_settings.debug;

                // CLI fstar_exe takes precedence over client setting
                if cli_fstar_exe.is_some() {
                    settings.fstar_exe = cli_fstar_exe;
                } else {
                    settings.fstar_exe = client_settings.fstar_exe;
                }
            }

            // Parse lint-specific settings from initializationOptions.lint
            if let Some(lint_opts) = options.get("lint") {
                if let Ok(ls) = serde_json::from_value::<LintSettings>(lint_opts.clone()) {
                    *self.lint_settings.write().await = ls;
                }
            }
        }

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(false),
                        })),
                        ..Default::default()
                    },
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                document_range_formatting_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "fstar-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        info!("F* LSP server initialized");
    }

    async fn shutdown(&self) -> RpcResult<()> {
        info!("F* LSP server shutting down");

        // Collect all documents first to release DashMap locks before awaiting.
        // DashMap::iter() holds shard read locks - calling .await while holding
        // these locks would cause deadlocks if other tasks try to access documents.
        let docs: Vec<Arc<DocumentState>> = self
            .documents
            .iter()
            .map(|entry| Arc::clone(entry.value()))
            .collect();

        // Now dispose without holding any DashMap locks
        for doc in docs {
            doc.dispose().await;
        }
        self.documents.clear();

        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        debug!("Document opened: {}", uri);

        // Run lint immediately (works without F* installed).
        {
            let ls = self.lint_settings.read().await;
            if ls.enabled && ls.lint_on_open {
                drop(ls);
                self.lint_document(&uri, &text).await;
            }
        }

        match self
            .get_or_create_document(&uri, Some(text), version)
            .await
        {
            Ok(doc) => {
                let settings = self.settings.read().await;
                if settings.verify_on_open {
                    drop(settings);
                    if let Err(e) = doc.verify_full().await {
                        error!("Verification failed: {}", e);
                    }
                } else if settings.fly_check {
                    drop(settings);
                    if let Err(e) = doc.verify_lax().await {
                        error!("Lax check failed: {}", e);
                    }
                }
            }
            Err(e) => {
                error!("Failed to open document: {}", e);
            }
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let key = uri.to_string();

        if let Some(doc) = self.get_document(&uri) {
            doc.update(params.content_changes, version).await;

            // Trigger flycheck after debounce, cancelling any previous pending flycheck
            let settings = self.settings.read().await;
            if settings.fly_check {
                drop(settings);

                // Cancel previous flycheck for this document
                if let Some((_, prev)) = self.flycheck_handles.remove(&key) {
                    prev.abort();
                }

                let doc_clone = Arc::clone(&doc);
                let handle_key = key.clone();
                let handles = self.flycheck_handles.clone();
                let task = tokio::spawn(async move {
                    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
                    let _ = doc_clone.verify_lax().await;
                    let _ = doc_clone.verify_cache().await;
                    handles.remove(&handle_key);
                });

                self.flycheck_handles.insert(key.clone(), task.abort_handle());
            }

            // Debounced re-lint on change (independent of F* flycheck).
            let ls = self.lint_settings.read().await;
            if ls.enabled && ls.lint_on_change {
                let debounce_ms = ls.debounce_ms;
                drop(ls);

                // Cancel previous pending lint for this document.
                if let Some((_, prev)) = self.lint_handles.remove(&key) {
                    prev.abort();
                }

                // Grab text after incremental update for the lint pass.
                let text = doc.text().await;
                let lint_uri = uri.clone();
                let backend = Arc::clone(&self.lint_backend.read().unwrap());
                let lint_lsp_diags = Arc::clone(&self.lint_lsp_diagnostics);
                let lint_raw = self.lint_raw_diagnostics.clone();
                let client = self.client.clone();
                let lint_key = key.clone();
                let lint_handles = self.lint_handles.clone();

                let task = tokio::spawn(async move {
                    tokio::time::sleep(tokio::time::Duration::from_millis(debounce_ms)).await;

                    let file_path = lint_uri.to_file_path().unwrap_or_default();
                    let (lsp_diags, raw_diags) = tokio::task::spawn_blocking(move || {
                        backend.lint_full(&file_path, &text)
                    })
                    .await
                    .unwrap_or_default();

                    let k = lint_uri.to_string();
                    lint_lsp_diags.insert(k.clone(), lsp_diags.clone());
                    lint_raw.insert(k, raw_diags);

                    // Publish lint diagnostics (F* status handler will include them on next update).
                    client
                        .publish_diagnostics(lint_uri, lsp_diags, None)
                        .await;

                    lint_handles.remove(&lint_key);
                });

                self.lint_handles.insert(key, task.abort_handle());
            }
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;

        if let Some(doc) = self.get_document(&uri) {
            let settings = self.settings.read().await;
            if settings.verify_on_save {
                drop(settings);
                if let Err(e) = doc.verify_full().await {
                    error!("Verification on save failed: {}", e);
                }
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        let key = uri.to_string();
        debug!("Document closed: {}", uri);

        // Abort pending flycheck and lint tasks.
        if let Some((_, handle)) = self.flycheck_handles.remove(&key) {
            handle.abort();
        }
        if let Some((_, handle)) = self.lint_handles.remove(&key) {
            handle.abort();
        }

        // Clean up lint state for this document.
        self.lint_lsp_diagnostics.remove(&key);
        self.lint_raw_diagnostics.remove(&key);

        self.remove_document(&uri).await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        // Try to parse as a JSON object that may contain both server and lint settings.
        let settings_val = &params.settings;

        if let Ok(client_settings) = serde_json::from_value::<LspSettings>(settings_val.clone()) {
            info!("Configuration updated");
            let mut settings = self.settings.write().await;

            let cli_fstar_exe = settings.fstar_exe.clone();

            settings.verify_on_open = client_settings.verify_on_open;
            settings.verify_on_save = client_settings.verify_on_save;
            settings.fly_check = client_settings.fly_check;
            settings.timeout_ms = client_settings.timeout_ms;
            settings.max_processes = client_settings.max_processes;
            settings.debug = settings.debug || client_settings.debug;

            if cli_fstar_exe.is_some() {
                settings.fstar_exe = cli_fstar_exe;
            } else {
                settings.fstar_exe = client_settings.fstar_exe;
            }
        }

        // Parse lint-specific settings from the `lint` key.
        if let Some(lint_val) = settings_val.get("lint") {
            if let Ok(ls) = serde_json::from_value::<LintSettings>(lint_val.clone()) {
                info!("Lint configuration updated");
                let new_backend = Arc::new(LintBackend::with_settings(&ls));

                // Hot-swap the backend. Readers (lint_document, did_change) that
                // already cloned the old Arc will finish with the old config;
                // subsequent reads will pick up the new backend.
                *self.lint_backend.write().unwrap() = new_backend;

                // Store the new settings for enabled/debounce checks.
                *self.lint_settings.write().await = ls;

                // Force a re-lint of all open documents with the new settings.
                let doc_keys: Vec<String> =
                    self.documents.iter().map(|e| e.key().clone()).collect();
                for key in doc_keys {
                    if let Some(doc) = self.documents.get(&key) {
                        let text = doc.text().await;
                        if let Ok(uri) = Url::parse(&key) {
                            self.lint_document(&uri, &text).await;
                        }
                    }
                }
            }
        }
    }

    async fn code_action(&self, params: CodeActionParams) -> RpcResult<Option<CodeActionResponse>> {
        let uri = params.text_document.uri;
        let key = uri.to_string();
        let range = params.range;

        // Look up stored raw lint diagnostics for this document.
        if let Some(entry) = self.lint_raw_diagnostics.get(&key) {
            let raw = entry.value();
            let backend = self.lint_backend.read().unwrap();
            let actions = backend.code_actions(&uri, range, raw);
            if !actions.is_empty() {
                let response: Vec<CodeActionOrCommand> = actions
                    .into_iter()
                    .map(CodeActionOrCommand::CodeAction)
                    .collect();
                return Ok(Some(response));
            }
        }

        Ok(None)
    }

    async fn hover(&self, params: HoverParams) -> RpcResult<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.get_document(&uri) {
            if let Some((contents, range)) = doc.hover(position).await {
                return Ok(Some(Hover {
                    contents: HoverContents::Markup(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: contents,
                    }),
                    range,
                }));
            }
        }

        Ok(None)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> RpcResult<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.get_document(&uri) {
            if let Some(location) = doc.definition(position).await {
                return Ok(Some(GotoDefinitionResponse::Scalar(location)));
            }
        }

        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> RpcResult<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        if let Some(doc) = self.get_document(&uri) {
            let items = doc.completions(position).await;
            if !items.is_empty() {
                return Ok(Some(CompletionResponse::Array(items)));
            }
        }

        Ok(None)
    }

    async fn formatting(
        &self,
        params: DocumentFormattingParams,
    ) -> RpcResult<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri;

        if let Some(doc) = self.get_document(&uri) {
            if let Some(formatted) = doc.format().await {
                let end_line = doc.line_count().await;

                return Ok(Some(vec![TextEdit {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: end_line,
                            character: 0,
                        },
                    },
                    new_text: formatted,
                }]));
            }
        }

        Ok(None)
    }

    async fn range_formatting(
        &self,
        params: DocumentRangeFormattingParams,
    ) -> RpcResult<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri;
        let range = params.range;

        // FIX: Extract just the selected text and format that portion.
        // The previous implementation formatted the entire document and then extracted
        // lines using the original document's line numbers. This was broken because
        // if formatting changes the number of lines (adding/removing blank lines,
        // reformatting multi-line expressions), the extracted range would correspond
        // to wrong lines, producing mangled text.
        if let Some(doc) = self.get_document(&uri) {
            // Extract the text within the requested range
            if let Some(selected_text) = doc.get_text_in_range(range).await {
                // Format just the selected text
                if let Some(formatted) = doc.format_text(&selected_text).await {
                    return Ok(Some(vec![TextEdit {
                        range,
                        new_text: formatted,
                    }]));
                }
            }
        }

        Ok(None)
    }
}

/// Lint integration helpers.
impl FstarServer {
    /// Run lint on `text`, store results, and publish merged diagnostics.
    ///
    /// Progress reporting uses `$/progress` when the client supports it.
    async fn lint_document(&self, uri: &Url, text: &str) {
        let file_path = match uri.to_file_path() {
            Ok(p) => p,
            Err(_) => return,
        };
        let file_name = file_path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("file")
            .to_string();

        let supports_progress = self
            .supports_progress
            .load(std::sync::atomic::Ordering::Relaxed);

        // Send progress begin.
        let token = NumberOrString::String(lint_lsp::LINT_PROGRESS_TOKEN.to_string());
        if supports_progress {
            let _ = self
                .client
                .send_request::<lsp_types::request::WorkDoneProgressCreate>(
                    WorkDoneProgressCreateParams {
                        token: token.clone(),
                    },
                )
                .await;
            self.client
                .send_notification::<lsp_types::notification::Progress>(ProgressParams {
                    token: token.clone(),
                    value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                        lint_lsp::progress_begin(&file_name),
                    )),
                })
                .await;
        }

        let backend = Arc::clone(&self.lint_backend.read().unwrap());
        let text_owned = text.to_string();
        let result = tokio::task::spawn_blocking(move || backend.lint_full(&file_path, &text_owned))
            .await;

        let (lsp_diags, raw_diags) = result.unwrap_or_default();

        // Store results.
        let key = uri.to_string();
        let diag_count = lsp_diags.len();
        self.lint_lsp_diagnostics
            .insert(key.clone(), lsp_diags.clone());
        self.lint_raw_diagnostics.insert(key, raw_diags);

        // Merge with F* diagnostics and publish.
        let mut merged = if let Some(doc) = self.get_document(uri) {
            doc.get_diagnostics().await
        } else {
            vec![]
        };
        merged.extend(lsp_diags);

        self.client
            .publish_diagnostics(uri.clone(), merged, None)
            .await;

        // Send progress end.
        if supports_progress {
            self.client
                .send_notification::<lsp_types::notification::Progress>(ProgressParams {
                    token,
                    value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                        lint_lsp::progress_end(diag_count),
                    )),
                })
                .await;
        }
    }
}

/// Custom notification handlers wired via LspService::build().custom_method().
impl FstarServer {
    /// Handle verify to position notification.
    pub async fn handle_verify_to_position(&self, params: notifications::VerifyToPositionParams) {
        if let Ok(uri) = Url::parse(&params.uri) {
            if let Some(doc) = self.get_document(&uri) {
                if let Err(e) = doc.verify_to_position(params.position, params.lax).await {
                    error!("Verify to position failed: {}", e);
                }
            }
        }
    }

    /// Handle restart notification.
    pub async fn handle_restart(&self, params: notifications::RestartParams) {
        if let Ok(uri) = Url::parse(&params.uri) {
            if let Some(doc) = self.get_document(&uri) {
                if let Err(e) = doc.restart().await {
                    error!("Restart failed: {}", e);
                    self.client
                        .show_message(MessageType::ERROR, format!("Failed to restart F*: {}", e))
                        .await;
                }
            }
        }
    }

    /// Handle kill and restart solver notification.
    pub async fn handle_kill_and_restart_solver(
        &self,
        params: notifications::KillAndRestartSolverParams,
    ) {
        if let Ok(uri) = Url::parse(&params.uri) {
            if let Some(doc) = self.get_document(&uri) {
                if let Err(e) = doc.restart_solver().await {
                    error!("Restart solver failed: {}", e);
                }
            }
        }
    }

    /// Handle kill all notification.
    pub async fn handle_kill_all(&self, _params: notifications::KillAllParams) {
        // Collect all documents first to release DashMap locks before awaiting.
        // DashMap::iter() holds shard read locks - calling .await while holding
        // these locks would cause deadlocks if other tasks try to access documents.
        let docs: Vec<Arc<DocumentState>> = self
            .documents
            .iter()
            .map(|entry| Arc::clone(entry.value()))
            .collect();

        // Now dispose without holding any DashMap locks
        for doc in docs {
            doc.dispose().await;
        }
        self.documents.clear();
    }

    /// Handle getTranslatedFst request (C2Pulse feature).
    /// Returns None for F* files — only meaningful for C files with source maps.
    pub async fn handle_get_translated_fst(
        &self,
        _params: notifications::GetTranslatedFstParams,
    ) -> tower_lsp::jsonrpc::Result<Option<notifications::GetTranslatedFstResponse>> {
        Ok(None)
    }

    /// Handle getDiagnostics request.
    ///
    /// Returns the current diagnostics for the specified document, merging
    /// full verification diagnostics with flycheck (lax) diagnostics.
    /// Flycheck diagnostics are filtered to only show those after the last
    /// verified fragment to avoid duplicates.
    pub async fn handle_get_diagnostics(
        &self,
        params: requests::GetDiagnosticsParams,
    ) -> RpcResult<Vec<tower_lsp::lsp_types::Diagnostic>> {
        if let Some(doc) = self.get_document(&params.uri) {
            Ok(doc.get_diagnostics().await)
        } else {
            Ok(vec![])
        }
    }

    /// Handle getFragments request.
    ///
    /// Returns information about all verified code fragments in the document,
    /// including their ranges, verification status, and staleness.
    /// Useful for custom UI that shows verification progress.
    pub async fn handle_get_fragments(
        &self,
        params: requests::GetFragmentsParams,
    ) -> RpcResult<Vec<requests::FragmentInfo>> {
        if let Some(doc) = self.get_document(&params.uri) {
            let fragments = doc.get_fragments().await;
            Ok(fragments
                .into_iter()
                .map(|f| requests::FragmentInfo {
                    range: f.range,
                    status: fragment_status_to_string(f.status),
                    stale: f.stale,
                })
                .collect())
        } else {
            Ok(vec![])
        }
    }
}

/// Converts a FragmentStatus enum to its string representation for the LSP response.
fn fragment_status_to_string(status: FragmentStatus) -> String {
    match status {
        FragmentStatus::Ok => "ok",
        FragmentStatus::LaxOk => "lax-ok",
        FragmentStatus::Started => "started",
        FragmentStatus::Failed => "failed",
    }
    .to_string()
}
