//! F* IDE protocol message types.
//!
//! This module defines the JSON message types used to communicate with F* in IDE mode.
//! The protocol uses JSON Lines (one JSON object per line) over stdin/stdout.

use serde::{Deserialize, Serialize};

/// F* position: [line, column] where line is 1-based, column is 0-based.
pub type FstarPosition = (u32, u32);

/// F* range with filename and positions.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct FstarRange {
    pub fname: String,
    pub beg: FstarPosition,
    pub end: FstarPosition,
}

impl FstarRange {
    /// Check if this is a dummy/invalid range.
    pub fn is_dummy(&self) -> bool {
        self.fname == "dummy" || self.fname == "<input>" || self.beg.0 == 0
    }
}

// ============================================================================
// Protocol Info
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)] // kind consumed by serde
pub struct ProtocolInfo {
    pub kind: String, // "protocol-info"
    pub version: u32,
    pub features: Vec<String>,
}

// ============================================================================
// Queries (Client -> F*)
// ============================================================================

#[derive(Debug, Clone, Serialize)]
pub struct Query<A> {
    #[serde(rename = "query-id")]
    pub query_id: String,
    pub query: String,
    pub args: A,
}

/// Full buffer query kinds.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum FullBufferKind {
    Full,
    Lax,
    Cache,
    ReloadDeps,
    VerifyToPosition,
    LaxToPosition,
}

/// Full buffer query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct FullBufferArgs {
    pub kind: FullBufferKind,
    #[serde(rename = "with-symbols")]
    pub with_symbols: bool,
    pub code: String,
    pub line: u32,
    pub column: u32,
    #[serde(rename = "to-position", skip_serializing_if = "Option::is_none")]
    pub to_position: Option<ToPosition>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ToPosition {
    pub line: u32,
    pub column: u32,
}

/// Lookup query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct LookupArgs {
    pub context: String,
    pub symbol: String,
    #[serde(rename = "requested-info")]
    pub requested_info: Vec<String>,
    pub location: LookupLocation,
    #[serde(rename = "symbol-range", skip_serializing_if = "Option::is_none")]
    pub symbol_range: Option<FstarRange>,
}

#[derive(Debug, Clone, Serialize)]
pub struct LookupLocation {
    pub filename: String,
    pub line: u32,
    pub column: u32,
}

/// Autocomplete query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct AutocompleteArgs {
    #[serde(rename = "partial-symbol")]
    pub partial_symbol: String,
    pub context: String,
}

/// Cancel query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct CancelArgs {
    #[serde(rename = "cancel-line")]
    pub cancel_line: u32,
    #[serde(rename = "cancel-column")]
    pub cancel_column: u32,
}

/// Format query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct FormatArgs {
    pub code: String,
}

/// VFS add query arguments.
#[derive(Debug, Clone, Serialize)]
pub struct VfsAddArgs {
    pub filename: Option<String>,
    pub contents: String,
}

// ============================================================================
// Responses (F* -> Client)
// ============================================================================

/// Base response structure.
#[derive(Debug, Clone, Deserialize)]
pub struct Response {
    #[serde(rename = "query-id")]
    pub query_id: String,
    pub kind: String,
    pub status: Option<String>,
    pub level: Option<String>,
    pub contents: Option<serde_json::Value>,
    pub response: Option<serde_json::Value>,
}

impl Response {
    pub fn is_success(&self) -> bool {
        self.status.as_deref() == Some("success")
    }

    pub fn is_progress(&self) -> bool {
        self.kind == "message" && self.level.as_deref() == Some("progress")
    }

    /// Check if this response indicates a protocol violation from F*.
    pub fn is_protocol_violation(&self) -> bool {
        self.status.as_deref() == Some("protocol-violation")
    }

    /// Get the protocol violation message if this is a protocol-violation response.
    pub fn protocol_violation_message(&self) -> Option<String> {
        if !self.is_protocol_violation() {
            return None;
        }

        // Try to extract message from contents or response field
        if let Some(contents) = &self.contents {
            if let Some(msg) = contents.as_str() {
                return Some(msg.to_string());
            }
            if let Some(msg) = contents.get("message").and_then(|m| m.as_str()) {
                return Some(msg.to_string());
            }
        }
        if let Some(response) = &self.response {
            if let Some(msg) = response.as_str() {
                return Some(msg.to_string());
            }
        }

        Some("Protocol violation".to_string())
    }

    /// Check if this response indicates FBQ completion.
    ///
    /// Returns true when:
    /// 1. Progress message with `stage: "full-buffer-finished"` (normal completion)
    /// 2. Response kind message (FBQ completion or cancellation)
    ///
    /// This matches the TypeScript behavior in `fstar_connection.ts` line 307.
    pub fn is_done(&self) -> bool {
        // Check for explicit progress message with full-buffer-finished
        if self.is_progress() {
            if let Some(contents) = &self.contents {
                if contents.get("stage").and_then(|s| s.as_str()) == Some("full-buffer-finished") {
                    return true;
                }
            }
        }

        // Also check for "response" kind (FBQ completion/cancellation)
        if self.kind == "response" {
            return true;
        }

        false
    }
}

// ============================================================================
// Diagnostics
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct IdeDiagnostic {
    pub message: String,
    #[serde(default)]
    pub number: Option<i32>,
    pub level: DiagnosticLevel,
    pub ranges: Vec<FstarRange>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Info,
    NotImplemented,
}

// ============================================================================
// Symbol/Lookup Response
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct IdeSymbol {
    pub name: String,
    #[serde(rename = "type")]
    pub typ: Option<String>,
    pub documentation: Option<String>,
    pub definition: Option<String>,
    #[serde(rename = "defined-at")]
    pub defined_at: Option<FstarRange>,
    #[serde(rename = "symbol-range")]
    pub symbol_range: Option<FstarRange>,
    pub symbol: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdeModule {
    pub name: String,
    pub path: String,
    pub loaded: bool,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub enum LookupResponse {
    #[serde(rename = "symbol")]
    Symbol(IdeSymbol),
    #[serde(rename = "module")]
    Module(IdeModule),
}

// ============================================================================
// Autocomplete Response
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct AutocompleteCandidate {
    #[serde(rename = "match-length")]
    pub match_length: u32,
    pub annotation: String,
    pub candidate: String,
}

// ============================================================================
// Proof State
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct IdeProofState {
    pub label: String,
    pub depth: i32,
    pub urgency: i32,
    pub goals: Vec<IdeGoal>,
    #[serde(rename = "smt-goals")]
    pub smt_goals: Vec<IdeGoal>,
    pub location: Option<FstarRange>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdeGoal {
    pub hyps: Vec<IdeHypothesis>,
    pub goal: IdeGoalType,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdeHypothesis {
    pub name: String,
    #[serde(rename = "type")]
    pub typ: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdeGoalType {
    pub witness: String,
    #[serde(rename = "type")]
    pub typ: String,
    pub label: String,
}

// ============================================================================
// Progress Messages
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct IdeProgress {
    pub stage: ProgressStage,
    #[serde(default)]
    pub ranges: Option<FstarRange>,
    #[serde(rename = "code-fragment")]
    pub code_fragment: Option<IdeCodeFragment>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum ProgressStage {
    FullBufferStarted,
    FullBufferFinished,
    FullBufferFragmentStarted,
    FullBufferFragmentOk,
    FullBufferFragmentLaxOk,
    FullBufferFragmentFailed,
}

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)] // range for future cache comparison
pub struct IdeCodeFragment {
    #[serde(rename = "code-digest")]
    pub code_digest: String,
    pub range: FstarRange,
}

// ============================================================================
// Format Response
// ============================================================================

#[derive(Debug, Clone, Deserialize)]
pub struct FormatResponse {
    #[serde(rename = "formatted-code")]
    pub formatted_code: Option<String>,
}

// ============================================================================
// Position Conversion
// ============================================================================

impl FstarRange {
    /// Convert F* range to LSP range. F* uses 1-based lines, LSP uses 0-based.
    pub fn to_lsp_range(&self) -> tower_lsp::lsp_types::Range {
        tower_lsp::lsp_types::Range {
            start: tower_lsp::lsp_types::Position {
                line: self.beg.0.saturating_sub(1),
                character: self.beg.1,
            },
            end: tower_lsp::lsp_types::Position {
                line: self.end.0.saturating_sub(1),
                character: self.end.1,
            },
        }
    }
}

/// Convert LSP position to F* position.
pub fn lsp_to_fstar_pos(pos: tower_lsp::lsp_types::Position) -> FstarPosition {
    (pos.line + 1, pos.character)
}
