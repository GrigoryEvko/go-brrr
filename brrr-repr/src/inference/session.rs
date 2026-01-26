//! Session type checking for channel operations
//!
//! Implements protocol verification following F* SessionTypes.fsti patterns.
//!
//! # Overview
//!
//! Session type checking verifies that channel operations follow the specified
//! protocol. Each channel has a session type that describes the expected
//! sequence of send/receive operations.
//!
//! # Checking Operations
//!
//! - `check_send` - Verify send operation matches expected !T.S
//! - `check_recv` - Verify receive operation matches expected ?T.S
//! - `check_select` - Verify internal choice matches +{...}
//! - `check_branch` - Verify external choice matches &{...}
//! - `check_new_channel` - Create dual channel endpoints
//! - `check_close` - Verify session has ended before closing
//!
//! # Error Handling
//!
//! Session errors provide detailed information about protocol violations:
//! - Expected vs actual session state
//! - Type mismatches in payloads
//! - Missing or invalid branch labels
//! - Duality violations

use serde::{Deserialize, Serialize};

use crate::effects::ChanId;
use crate::expr::Range;
use crate::session::{Label, SessionCtx, SessionType};
use crate::types::BrrrType;

// ============================================================================
// Session Errors
// ============================================================================

/// Session type checking errors
///
/// Maps to F* SessionTypes.fsti check_result error cases with additional
/// context for better diagnostics.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SessionError {
    /// Channel not found in session context
    ///
    /// Occurs when trying to use a channel that hasn't been created or
    /// has already been closed.
    ChannelNotFound {
        /// The channel that was not found
        chan: ChanId,
        /// Source location of the operation
        span: Range,
    },

    /// Unexpected send operation
    ///
    /// Occurs when trying to send on a channel that expects a different
    /// operation (e.g., receive, choice, or end).
    UnexpectedSend {
        /// The channel involved
        chan: ChanId,
        /// The expected session type (not a Send)
        expected: SessionType,
        /// Source location of the operation
        span: Range,
    },

    /// Unexpected receive operation
    ///
    /// Occurs when trying to receive on a channel that expects a different
    /// operation (e.g., send, choice, or end).
    UnexpectedRecv {
        /// The channel involved
        chan: ChanId,
        /// The expected session type (not a Recv)
        expected: SessionType,
        /// Source location of the operation
        span: Range,
    },

    /// Payload type mismatch
    ///
    /// Occurs when the type of a sent/received value doesn't match
    /// the type specified in the session type.
    TypeMismatch {
        /// The channel involved
        chan: ChanId,
        /// The expected payload type from session type
        expected: BrrrType,
        /// The actual payload type
        found: BrrrType,
        /// Source location of the operation
        span: Range,
    },

    /// Session not ended before close
    ///
    /// Occurs when trying to close a channel that still has remaining
    /// protocol operations.
    SessionNotEnded {
        /// The channel being closed
        chan: ChanId,
        /// The remaining session type
        remaining: SessionType,
        /// Source location of the close operation
        span: Range,
    },

    /// Branch label mismatch
    ///
    /// Occurs when selecting a label that doesn't exist in the session
    /// type's branch options.
    BranchMismatch {
        /// The channel involved
        chan: ChanId,
        /// The label that was not found
        label: Label,
        /// Source location of the operation
        span: Range,
    },

    /// Duality violation
    ///
    /// Occurs when creating channel endpoints with session types that
    /// are not duals of each other.
    DualityViolation {
        /// First channel endpoint
        chan1: ChanId,
        /// Second channel endpoint
        chan2: ChanId,
        /// Source location of the channel creation
        span: Range,
    },

    /// Unexpected select operation
    ///
    /// Occurs when trying to select on a channel that doesn't expect
    /// an internal choice.
    UnexpectedSelect {
        /// The channel involved
        chan: ChanId,
        /// The expected session type (not a Select)
        expected: SessionType,
        /// Source location of the operation
        span: Range,
    },

    /// Unexpected branch operation
    ///
    /// Occurs when trying to branch on a channel that doesn't expect
    /// an external choice.
    UnexpectedBranch {
        /// The channel involved
        chan: ChanId,
        /// The expected session type (not a Branch)
        expected: SessionType,
        /// Source location of the operation
        span: Range,
    },

    /// Channel already exists
    ///
    /// Occurs when trying to create a channel with an ID that's already
    /// in use.
    ChannelAlreadyExists {
        /// The channel that already exists
        chan: ChanId,
        /// Source location of the creation attempt
        span: Range,
    },

    /// Session type not well-formed
    ///
    /// Occurs when a session type is not closed or not contractive.
    MalformedSessionType {
        /// Description of the problem
        reason: String,
        /// Source location
        span: Range,
    },
}

impl SessionError {
    /// Get the source span for this error
    #[must_use]
    pub const fn span(&self) -> Range {
        match self {
            Self::ChannelNotFound { span, .. }
            | Self::UnexpectedSend { span, .. }
            | Self::UnexpectedRecv { span, .. }
            | Self::TypeMismatch { span, .. }
            | Self::SessionNotEnded { span, .. }
            | Self::BranchMismatch { span, .. }
            | Self::DualityViolation { span, .. }
            | Self::UnexpectedSelect { span, .. }
            | Self::UnexpectedBranch { span, .. }
            | Self::ChannelAlreadyExists { span, .. }
            | Self::MalformedSessionType { span, .. } => *span,
        }
    }

    /// Get a human-readable error kind name
    #[must_use]
    pub const fn kind_name(&self) -> &'static str {
        match self {
            Self::ChannelNotFound { .. } => "channel not found",
            Self::UnexpectedSend { .. } => "unexpected send",
            Self::UnexpectedRecv { .. } => "unexpected receive",
            Self::TypeMismatch { .. } => "type mismatch",
            Self::SessionNotEnded { .. } => "session not ended",
            Self::BranchMismatch { .. } => "branch mismatch",
            Self::DualityViolation { .. } => "duality violation",
            Self::UnexpectedSelect { .. } => "unexpected select",
            Self::UnexpectedBranch { .. } => "unexpected branch",
            Self::ChannelAlreadyExists { .. } => "channel already exists",
            Self::MalformedSessionType { .. } => "malformed session type",
        }
    }

    /// Get the channel involved in this error, if any
    #[must_use]
    pub const fn channel(&self) -> Option<ChanId> {
        match self {
            Self::ChannelNotFound { chan, .. }
            | Self::UnexpectedSend { chan, .. }
            | Self::UnexpectedRecv { chan, .. }
            | Self::TypeMismatch { chan, .. }
            | Self::SessionNotEnded { chan, .. }
            | Self::BranchMismatch { chan, .. }
            | Self::UnexpectedSelect { chan, .. }
            | Self::UnexpectedBranch { chan, .. }
            | Self::ChannelAlreadyExists { chan, .. } => Some(*chan),
            Self::DualityViolation { chan1, .. } => Some(*chan1),
            Self::MalformedSessionType { .. } => None,
        }
    }
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ChannelNotFound { chan, .. } => {
                write!(f, "Channel {} not found in session context", chan)
            }
            Self::UnexpectedSend { chan, expected, .. } => {
                write!(
                    f,
                    "Unexpected send on channel {}: expected {:?}",
                    chan, expected
                )
            }
            Self::UnexpectedRecv { chan, expected, .. } => {
                write!(
                    f,
                    "Unexpected receive on channel {}: expected {:?}",
                    chan, expected
                )
            }
            Self::TypeMismatch {
                chan,
                expected,
                found,
                ..
            } => {
                write!(
                    f,
                    "Type mismatch on channel {}: expected {:?}, found {:?}",
                    chan, expected, found
                )
            }
            Self::SessionNotEnded {
                chan, remaining, ..
            } => {
                write!(
                    f,
                    "Cannot close channel {}: session has remaining operations {:?}",
                    chan, remaining
                )
            }
            Self::BranchMismatch { chan, .. } => {
                write!(f, "Branch label not found in channel {} session type", chan)
            }
            Self::DualityViolation { chan1, chan2, .. } => {
                write!(
                    f,
                    "Session types for channels {} and {} are not duals",
                    chan1, chan2
                )
            }
            Self::UnexpectedSelect { chan, expected, .. } => {
                write!(
                    f,
                    "Unexpected select on channel {}: expected {:?}",
                    chan, expected
                )
            }
            Self::UnexpectedBranch { chan, expected, .. } => {
                write!(
                    f,
                    "Unexpected branch on channel {}: expected {:?}",
                    chan, expected
                )
            }
            Self::ChannelAlreadyExists { chan, .. } => {
                write!(f, "Channel {} already exists in session context", chan)
            }
            Self::MalformedSessionType { reason, .. } => {
                write!(f, "Malformed session type: {}", reason)
            }
        }
    }
}

impl std::error::Error for SessionError {}

// ============================================================================
// Session Check State
// ============================================================================

/// State maintained during session type checking
///
/// Maps to F* SessionTypes.fsti session_ctx with additional error tracking.
///
/// # Usage
///
/// ```ignore
/// let mut state = SessionCheckState::new();
///
/// // Create a new channel pair
/// let (c1, c2) = check_new_channel(session_type, &mut state, span)?;
///
/// // Perform operations
/// check_send(c1, &payload_type, &mut state, span)?;
/// let recv_ty = check_recv(c2, &mut state, span)?;
///
/// // Close channels
/// check_close(c1, &mut state, span)?;
/// check_close(c2, &mut state, span)?;
///
/// // Verify all sessions ended
/// let remaining_errors = verify_all_sessions_ended(&state);
/// ```
#[derive(Debug, Clone, Default)]
pub struct SessionCheckState {
    /// Active channel sessions
    ///
    /// Maps channel IDs to their current session types.
    /// Updated after each operation to reflect protocol progress.
    pub ctx: SessionCtx,

    /// Accumulated session errors
    ///
    /// Errors are collected rather than immediately failing to allow
    /// multiple errors to be reported in a single pass.
    pub errors: Vec<SessionError>,

    /// Counter for generating fresh channel IDs
    channel_counter: u32,
}

impl SessionCheckState {
    /// Create a new empty session check state
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: SessionCtx::empty(),
            errors: Vec::new(),
            channel_counter: 0,
        }
    }

    /// Create a session check state with an existing context
    #[must_use]
    pub fn with_ctx(ctx: SessionCtx) -> Self {
        Self {
            ctx,
            errors: Vec::new(),
            channel_counter: 0,
        }
    }

    /// Generate a fresh channel ID
    pub fn fresh_channel_id(&mut self) -> ChanId {
        let id = self.channel_counter;
        self.channel_counter += 1;
        id
    }

    /// Record a session error
    pub fn add_error(&mut self, error: SessionError) {
        self.errors.push(error);
    }

    /// Check if any errors have been recorded
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Get the number of active channels
    #[must_use]
    pub fn channel_count(&self) -> usize {
        self.ctx.len()
    }

    /// Check if all channels have ended
    #[must_use]
    pub fn all_ended(&self) -> bool {
        self.ctx.all_ended()
    }

    /// Lookup a channel's current session type
    #[must_use]
    pub fn lookup_channel(&self, chan: ChanId) -> Option<&SessionType> {
        self.ctx.lookup_channel(chan)
    }

    /// Check if a channel exists in the context
    #[must_use]
    pub fn has_channel(&self, chan: ChanId) -> bool {
        self.ctx.has_channel(chan)
    }
}

// ============================================================================
// Core Checking Functions
// ============================================================================

/// Check a send operation
///
/// Verifies that the channel's session type is `!T.S` where T matches
/// the payload type. Advances the session to S.
///
/// # Arguments
///
/// * `chan` - Channel to send on
/// * `payload_ty` - Type of the value being sent
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(())` if the send is valid
/// - `Err(SessionError)` if the channel is not found, not in send state,
///   or the payload type doesn't match
///
/// # F* Reference
///
/// Maps to `check_send : channel_name -> brrr_type -> session_ctx -> check_result`
pub fn check_send(
    chan: ChanId,
    payload_ty: &BrrrType,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<(), SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types by unfolding
    let session = unfold_if_needed(&session);

    // Check that we're in a send state
    match &session {
        SessionType::Send {
            payload,
            continuation,
        } => {
            // Verify payload type matches
            if payload != payload_ty {
                let err = SessionError::TypeMismatch {
                    chan,
                    expected: payload.clone(),
                    found: payload_ty.clone(),
                    span,
                };
                state.add_error(err.clone());
                return Err(err);
            }

            // Advance session to continuation
            state.ctx = state.ctx.update_channel(chan, (**continuation).clone());
            Ok(())
        }
        _ => {
            let err = SessionError::UnexpectedSend {
                chan,
                expected: session.clone(),
                span,
            };
            state.add_error(err.clone());
            Err(err)
        }
    }
}

/// Check a receive operation
///
/// Verifies that the channel's session type is `?T.S`. Advances the
/// session to S and returns the expected payload type T.
///
/// # Arguments
///
/// * `chan` - Channel to receive on
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(BrrrType)` - The expected payload type if the receive is valid
/// - `Err(SessionError)` - If the channel is not found or not in receive state
///
/// # F* Reference
///
/// Maps to `check_recv : channel_name -> session_ctx -> check_result`
pub fn check_recv(
    chan: ChanId,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<BrrrType, SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types by unfolding
    let session = unfold_if_needed(&session);

    // Check that we're in a receive state
    match &session {
        SessionType::Recv {
            payload,
            continuation,
        } => {
            // Advance session to continuation
            state.ctx = state.ctx.update_channel(chan, (**continuation).clone());
            Ok(payload.clone())
        }
        _ => {
            let err = SessionError::UnexpectedRecv {
                chan,
                expected: session.clone(),
                span,
            };
            state.add_error(err.clone());
            Err(err)
        }
    }
}

/// Check an internal choice (select) operation
///
/// Verifies that the channel's session type is `+{l1: S1, l2: S2, ...}`
/// and the selected label exists. Advances the session to the corresponding Si.
///
/// # Arguments
///
/// * `chan` - Channel to select on
/// * `label` - Label being selected
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(())` if the select is valid
/// - `Err(SessionError)` if the channel is not found, not in select state,
///   or the label doesn't exist
///
/// # F* Reference
///
/// Maps to `check_select : channel_name -> label -> session_ctx -> check_result`
pub fn check_select(
    chan: ChanId,
    label: Label,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<(), SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types by unfolding
    let session = unfold_if_needed(&session);

    // Check that we're in a select state
    match &session {
        SessionType::Select(branches) => {
            // Find the branch for the selected label
            match branches.iter().find(|(l, _)| *l == label) {
                Some((_, continuation)) => {
                    // Advance session to the selected branch
                    state.ctx = state.ctx.update_channel(chan, continuation.clone());
                    Ok(())
                }
                None => {
                    let err = SessionError::BranchMismatch { chan, label, span };
                    state.add_error(err.clone());
                    Err(err)
                }
            }
        }
        _ => {
            let err = SessionError::UnexpectedSelect {
                chan,
                expected: session.clone(),
                span,
            };
            state.add_error(err.clone());
            Err(err)
        }
    }
}

/// Check an external choice (branch) operation
///
/// Verifies that the channel's session type is `&{l1: S1, l2: S2, ...}`.
/// Returns the available branches for pattern matching.
///
/// Note: Unlike select, branch doesn't immediately advance the session.
/// The caller must handle each branch and call `advance_branch` with
/// the received label.
///
/// # Arguments
///
/// * `chan` - Channel to branch on
/// * `state` - Session check state
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(Vec<(Label, SessionType)>)` - Available branches if valid
/// - `Err(SessionError)` - If the channel is not found or not in branch state
///
/// # F* Reference
///
/// Maps to `check_branch : channel_name -> label -> session_ctx -> check_result`
pub fn check_branch(
    chan: ChanId,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<Vec<(Label, SessionType)>, SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types by unfolding
    let session = unfold_if_needed(&session);

    // Check that we're in a branch state
    match &session {
        SessionType::Branch(branches) => Ok(branches.clone()),
        _ => {
            let err = SessionError::UnexpectedBranch {
                chan,
                expected: session.clone(),
                span,
            };
            state.add_error(err.clone());
            Err(err)
        }
    }
}

/// Advance a channel after receiving a branch label
///
/// Used after `check_branch` to update the session to the selected branch.
///
/// # Arguments
///
/// * `chan` - Channel that received the branch
/// * `label` - Label that was received
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(SessionType)` - The continuation session type for this branch
/// - `Err(SessionError)` - If the label doesn't exist in the branch
pub fn advance_branch(
    chan: ChanId,
    label: Label,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<SessionType, SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types by unfolding
    let session = unfold_if_needed(&session);

    // Check that we're in a branch state and find the label
    match &session {
        SessionType::Branch(branches) => match branches.iter().find(|(l, _)| *l == label) {
            Some((_, continuation)) => {
                state.ctx = state.ctx.update_channel(chan, continuation.clone());
                Ok(continuation.clone())
            }
            None => {
                let err = SessionError::BranchMismatch { chan, label, span };
                state.add_error(err.clone());
                Err(err)
            }
        },
        _ => {
            let err = SessionError::UnexpectedBranch {
                chan,
                expected: session.clone(),
                span,
            };
            state.add_error(err.clone());
            Err(err)
        }
    }
}

/// Create a new channel pair with dual session types
///
/// Creates two channel endpoints with session types that are duals of
/// each other, ensuring type-safe bidirectional communication.
///
/// # Arguments
///
/// * `session` - Session type for the first endpoint (second gets dual)
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok((ChanId, ChanId))` - The two channel endpoint IDs
/// - `Err(SessionError)` - If the session type is malformed
///
/// # Invariant
///
/// For the returned (c1, c2): `session_of(c1).is_dual_of(session_of(c2))`
///
/// # F* Reference
///
/// Maps to `check_new : channel_name -> channel_name -> session_type -> session_ctx -> check_result`
pub fn check_new_channel(
    session: SessionType,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<(ChanId, ChanId), SessionError> {
    // Verify session type is well-formed
    if !session.is_wellformed() {
        let err = SessionError::MalformedSessionType {
            reason: if !session.is_closed() {
                "session type has free variables".to_string()
            } else {
                "session type is not contractive".to_string()
            },
            span,
        };
        state.add_error(err.clone());
        return Err(err);
    }

    // Generate fresh channel IDs
    let chan1 = state.fresh_channel_id();
    let chan2 = state.fresh_channel_id();

    // Compute dual session type
    let dual_session = session.dual();

    // Add both channels to context
    state.ctx = state.ctx.update_channel(chan1, session);
    state.ctx = state.ctx.update_channel(chan2, dual_session);

    Ok((chan1, chan2))
}

/// Create a channel with explicit dual endpoint
///
/// Like `check_new_channel` but allows specifying both channel IDs
/// explicitly. Verifies that the session types are duals.
///
/// # Arguments
///
/// * `chan1` - First channel ID
/// * `chan2` - Second channel ID
/// * `session1` - Session type for first channel
/// * `session2` - Session type for second channel
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(())` if the channels are created successfully
/// - `Err(SessionError)` if duality is violated or IDs exist
pub fn check_new_channel_explicit(
    chan1: ChanId,
    chan2: ChanId,
    session1: SessionType,
    session2: SessionType,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<(), SessionError> {
    // Check channels don't already exist
    if state.has_channel(chan1) {
        let err = SessionError::ChannelAlreadyExists { chan: chan1, span };
        state.add_error(err.clone());
        return Err(err);
    }
    if state.has_channel(chan2) {
        let err = SessionError::ChannelAlreadyExists { chan: chan2, span };
        state.add_error(err.clone());
        return Err(err);
    }

    // Verify duality
    if !verify_duality(&session1, &session2) {
        let err = SessionError::DualityViolation { chan1, chan2, span };
        state.add_error(err.clone());
        return Err(err);
    }

    // Verify well-formedness
    if !session1.is_wellformed() {
        let err = SessionError::MalformedSessionType {
            reason: "first session type is not well-formed".to_string(),
            span,
        };
        state.add_error(err.clone());
        return Err(err);
    }

    // Add channels to context
    state.ctx = state.ctx.update_channel(chan1, session1);
    state.ctx = state.ctx.update_channel(chan2, session2);

    Ok(())
}

/// Close a channel
///
/// Verifies that the channel's session type is `end` before removing
/// it from the context.
///
/// # Arguments
///
/// * `chan` - Channel to close
/// * `state` - Session check state to update
/// * `span` - Source location for error reporting
///
/// # Returns
///
/// - `Ok(())` if the channel is successfully closed
/// - `Err(SessionError)` if the channel is not found or hasn't ended
///
/// # F* Reference
///
/// Maps to checking that session is End before removal
pub fn check_close(
    chan: ChanId,
    state: &mut SessionCheckState,
    span: Range,
) -> Result<(), SessionError> {
    // Look up the channel's current session type
    let session = match state.ctx.lookup_channel(chan) {
        Some(s) => s.clone(),
        None => {
            let err = SessionError::ChannelNotFound { chan, span };
            state.add_error(err.clone());
            return Err(err);
        }
    };

    // Handle recursive types that unfold to End
    let session = unfold_if_needed(&session);

    // Check that the session has ended
    if !session.is_end() {
        let err = SessionError::SessionNotEnded {
            chan,
            remaining: session,
            span,
        };
        state.add_error(err.clone());
        return Err(err);
    }

    // Remove channel from context
    state.ctx = state.ctx.remove_channel(chan);
    Ok(())
}

// ============================================================================
// Duality and Well-formedness
// ============================================================================

/// Verify that two session types are duals of each other
///
/// Duality ensures type-safe communication: when one party sends,
/// the other must receive, and vice versa.
///
/// # Arguments
///
/// * `s1` - First session type
/// * `s2` - Second session type
///
/// # Returns
///
/// `true` if `s1` is the dual of `s2`
pub fn verify_duality(s1: &SessionType, s2: &SessionType) -> bool {
    s1.is_dual_of(s2)
}

/// Verify that all sessions in the state have ended
///
/// Returns a list of errors for channels that haven't ended.
/// Should be called at scope boundaries to ensure all protocols complete.
///
/// # Arguments
///
/// * `state` - Session check state to verify
///
/// # Returns
///
/// A vector of `SessionNotEnded` errors for each channel that hasn't
/// completed its protocol.
pub fn verify_all_sessions_ended(state: &SessionCheckState) -> Vec<SessionError> {
    let mut errors = Vec::new();

    for (chan, session) in state.ctx.iter() {
        // Unfold to check if it ends
        let unfolded = unfold_if_needed(session);
        if !unfolded.is_end() {
            errors.push(SessionError::SessionNotEnded {
                chan: *chan,
                remaining: session.clone(),
                span: Range::SYNTHETIC,
            });
        }
    }

    errors
}

/// Verify all sessions ended with a specific span for errors
///
/// Like `verify_all_sessions_ended` but uses the provided span for
/// error locations.
pub fn verify_all_sessions_ended_at(state: &SessionCheckState, span: Range) -> Vec<SessionError> {
    let mut errors = Vec::new();

    for (chan, session) in state.ctx.iter() {
        let unfolded = unfold_if_needed(session);
        if !unfolded.is_end() {
            errors.push(SessionError::SessionNotEnded {
                chan: *chan,
                remaining: session.clone(),
                span,
            });
        }
    }

    errors
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Unfold a session type if it's a recursive type
///
/// Applies one level of unfolding for recursive types to expose
/// the underlying structure.
fn unfold_if_needed(session: &SessionType) -> SessionType {
    match session {
        SessionType::Rec { .. } => session.unfold(),
        _ => session.clone(),
    }
}

/// Check if a session type has finished (is End or unfolds to End)
pub fn is_session_ended(session: &SessionType) -> bool {
    let unfolded = unfold_if_needed(session);
    unfolded.is_end()
}

// ============================================================================
// Expression-level Session Checking
// ============================================================================

/// Result of session checking an expression
#[derive(Debug, Clone)]
pub struct SessionCheckResult {
    /// Whether the check succeeded
    pub success: bool,
    /// Type returned by receive operations (if applicable)
    pub recv_type: Option<BrrrType>,
    /// Created channels (if applicable)
    pub created_channels: Vec<(ChanId, ChanId)>,
    /// Errors encountered
    pub errors: Vec<SessionError>,
}

impl SessionCheckResult {
    /// Create a successful result with no additional data
    #[must_use]
    pub fn ok() -> Self {
        Self {
            success: true,
            recv_type: None,
            created_channels: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Create a successful result with a receive type
    #[must_use]
    pub fn with_recv_type(ty: BrrrType) -> Self {
        Self {
            success: true,
            recv_type: Some(ty),
            created_channels: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Create a successful result with created channels
    #[must_use]
    pub fn with_channels(channels: Vec<(ChanId, ChanId)>) -> Self {
        Self {
            success: true,
            recv_type: None,
            created_channels: channels,
            errors: Vec::new(),
        }
    }

    /// Create a failed result with an error
    #[must_use]
    pub fn err(error: SessionError) -> Self {
        Self {
            success: false,
            recv_type: None,
            created_channels: Vec::new(),
            errors: vec![error],
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{IntType, NumericType, PrimKind};

    fn bool_type() -> BrrrType {
        BrrrType::Prim(PrimKind::Bool)
    }

    fn int_type() -> BrrrType {
        BrrrType::Numeric(NumericType::Int(IntType::I32))
    }

    #[test]
    fn test_check_send_success() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_send(0, &bool_type(), &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        assert!(state.lookup_channel(0).unwrap().is_end());
    }

    #[test]
    fn test_check_send_wrong_type() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_send(0, &int_type(), &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        match result.unwrap_err() {
            SessionError::TypeMismatch {
                expected, found, ..
            } => {
                assert_eq!(expected, bool_type());
                assert_eq!(found, int_type());
            }
            _ => panic!("Expected TypeMismatch error"),
        }
    }

    #[test]
    fn test_check_send_unexpected() {
        let session = SessionType::recv(bool_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_send(0, &bool_type(), &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::UnexpectedSend { .. }
        ));
    }

    #[test]
    fn test_check_send_channel_not_found() {
        let mut state = SessionCheckState::new();

        let result = check_send(0, &bool_type(), &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::ChannelNotFound { .. }
        ));
    }

    #[test]
    fn test_check_recv_success() {
        let session = SessionType::recv(int_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_recv(0, &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), int_type());
        assert!(state.lookup_channel(0).unwrap().is_end());
    }

    #[test]
    fn test_check_recv_unexpected() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_recv(0, &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::UnexpectedRecv { .. }
        ));
    }

    #[test]
    fn test_check_new_channel() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let mut state = SessionCheckState::new();

        let result = check_new_channel(session.clone(), &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        let (c1, c2) = result.unwrap();
        assert!(state.has_channel(c1));
        assert!(state.has_channel(c2));

        // Verify duality
        let s1 = state.lookup_channel(c1).unwrap();
        let s2 = state.lookup_channel(c2).unwrap();
        assert!(s1.is_dual_of(s2));
    }

    #[test]
    fn test_check_new_channel_malformed() {
        use crate::session::SessionVar;

        // rec X.X is not contractive (infinite loop without communication)
        let var = SessionVar::new(0);
        let session = SessionType::rec(var, SessionType::var(var));
        let mut state = SessionCheckState::new();

        let result = check_new_channel(session, &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::MalformedSessionType { .. }
        ));
    }

    #[test]
    fn test_check_close_success() {
        let ctx = SessionCtx::singleton(0, SessionType::End);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_close(0, &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        assert!(!state.has_channel(0));
    }

    #[test]
    fn test_check_close_not_ended() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_close(0, &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::SessionNotEnded { .. }
        ));
    }

    #[test]
    fn test_verify_all_sessions_ended() {
        let session = SessionType::send(bool_type(), SessionType::End);
        let ctx = SessionCtx::from_iter(vec![(0, SessionType::End), (1, session)]);
        let state = SessionCheckState::with_ctx(ctx);

        let errors = verify_all_sessions_ended(&state);

        assert_eq!(errors.len(), 1);
        assert!(matches!(
            &errors[0],
            SessionError::SessionNotEnded { chan: 1, .. }
        ));
    }

    #[test]
    fn test_check_select_success() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let session = SessionType::select(vec![
            (label_ok, SessionType::End),
            (label_err, SessionType::send(bool_type(), SessionType::End)),
        ]);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_select(0, label_ok, &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        assert!(state.lookup_channel(0).unwrap().is_end());
    }

    #[test]
    fn test_check_select_branch_not_found() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let label_ok = rodeo.get_or_intern("ok");
        let label_bad = rodeo.get_or_intern("bad");

        let session = SessionType::select(vec![(label_ok, SessionType::End)]);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_select(0, label_bad, &mut state, Range::SYNTHETIC);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SessionError::BranchMismatch { .. }
        ));
    }

    #[test]
    fn test_check_branch_success() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let label_ok = rodeo.get_or_intern("ok");
        let label_err = rodeo.get_or_intern("err");

        let session = SessionType::branch(vec![
            (label_ok, SessionType::End),
            (label_err, SessionType::send(bool_type(), SessionType::End)),
        ]);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        let result = check_branch(0, &mut state, Range::SYNTHETIC);

        assert!(result.is_ok());
        let branches = result.unwrap();
        assert_eq!(branches.len(), 2);
    }

    #[test]
    fn test_verify_duality() {
        let send = SessionType::send(bool_type(), SessionType::End);
        let recv = SessionType::recv(bool_type(), SessionType::End);

        assert!(verify_duality(&send, &recv));
        assert!(verify_duality(&recv, &send));
        assert!(!verify_duality(&send, &send));
    }

    #[test]
    fn test_full_protocol() {
        // Request-response protocol
        // Client: !Bool.?Int.end
        // Server: ?Bool.!Int.end

        let client_session =
            SessionType::send(bool_type(), SessionType::recv(int_type(), SessionType::End));

        let mut state = SessionCheckState::new();

        // Create channel pair
        let (client, server) =
            check_new_channel(client_session, &mut state, Range::SYNTHETIC).unwrap();

        // Client sends
        check_send(client, &bool_type(), &mut state, Range::SYNTHETIC).unwrap();

        // Server receives
        let recv_ty = check_recv(server, &mut state, Range::SYNTHETIC).unwrap();
        assert_eq!(recv_ty, bool_type());

        // Server sends
        check_send(server, &int_type(), &mut state, Range::SYNTHETIC).unwrap();

        // Client receives
        let recv_ty = check_recv(client, &mut state, Range::SYNTHETIC).unwrap();
        assert_eq!(recv_ty, int_type());

        // Close both
        check_close(client, &mut state, Range::SYNTHETIC).unwrap();
        check_close(server, &mut state, Range::SYNTHETIC).unwrap();

        // Verify all ended
        assert!(state.ctx.is_empty());
        assert!(verify_all_sessions_ended(&state).is_empty());
    }

    #[test]
    fn test_recursive_session() {
        use crate::session::SessionVar;

        // rec X.!Bool.X - infinite send loop
        let var = SessionVar::new(0);
        let session = SessionType::rec(var, SessionType::send(bool_type(), SessionType::var(var)));

        let mut state = SessionCheckState::new();
        let (c1, _c2) = check_new_channel(session, &mut state, Range::SYNTHETIC).unwrap();

        // Can send multiple times
        check_send(c1, &bool_type(), &mut state, Range::SYNTHETIC).unwrap();
        check_send(c1, &bool_type(), &mut state, Range::SYNTHETIC).unwrap();
        check_send(c1, &bool_type(), &mut state, Range::SYNTHETIC).unwrap();

        // Session type should still be recursive send
        let current = state.lookup_channel(c1).unwrap();
        assert!(current.is_recursive());
    }

    #[test]
    fn test_error_accumulation() {
        let mut state = SessionCheckState::new();

        // Multiple errors on non-existent channels
        let _ = check_send(0, &bool_type(), &mut state, Range::SYNTHETIC);
        let _ = check_recv(1, &mut state, Range::SYNTHETIC);
        let _ = check_close(2, &mut state, Range::SYNTHETIC);

        assert_eq!(state.error_count(), 3);
        assert!(state.has_errors());
    }

    #[test]
    fn test_advance_branch() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let label_ok = rodeo.get_or_intern("ok");

        let session = SessionType::branch(vec![(
            label_ok,
            SessionType::send(bool_type(), SessionType::End),
        )]);
        let ctx = SessionCtx::singleton(0, session);
        let mut state = SessionCheckState::with_ctx(ctx);

        // Get branches
        let _ = check_branch(0, &mut state, Range::SYNTHETIC).unwrap();

        // Advance to selected branch
        let cont = advance_branch(0, label_ok, &mut state, Range::SYNTHETIC).unwrap();

        assert!(cont.is_send());
    }
}
