//! TEI (Text Embeddings Inference) gRPC client implementation.
//!
//! High-performance async client with:
//! - Connection pooling (via tonic channel)
//! - Retry with exponential backoff
//! - Token-budget batching for optimal throughput
//! - Comprehensive error handling
//! - Cross-encoder reranking support

use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use futures::stream;
use rand::Rng;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::sync::{OnceCell, RwLock, Semaphore};
use tonic::transport::{Channel, Endpoint};

// Generated protobuf types
pub mod tei_proto {
    tonic::include_proto!("tei.v1");
}

use tei_proto::{
    embed_client::EmbedClient, info_client::InfoClient, rerank_client::RerankClient,
    tokenize_client::TokenizeClient, DecodeRequest, EmbedRequest, EncodeRequest, InfoRequest,
    RerankRequest, TruncationDirection,
};

// =============================================================================
// Error Types
// =============================================================================

/// TEI client error type.
#[derive(Error, Debug)]
pub enum TeiError {
    /// Connection failed to TEI server.
    #[error("Connection failed: {0}")]
    Connection(String),

    /// gRPC call failed.
    #[error("gRPC error: {0}")]
    Grpc(#[from] tonic::Status),

    /// Transport error.
    #[error("Transport error: {0}")]
    Transport(#[from] tonic::transport::Error),

    /// Server returned empty response.
    #[error("Empty response from server")]
    EmptyResponse,

    /// Retry exhausted.
    #[error("All retry attempts failed: {0}")]
    RetryExhausted(String),

    /// Invalid configuration.
    #[error("Invalid configuration: {0}")]
    Config(String),

    /// Server returned fewer responses than requests (stream truncated).
    ///
    /// This indicates a server-side issue where the stream was terminated
    /// before all responses were delivered. Callers should not attempt to
    /// use partial results as index alignment cannot be guaranteed.
    #[error("Partial response: expected {expected} results, received {received}")]
    PartialResponse {
        /// Number of items requested.
        expected: usize,
        /// Number of items actually received.
        received: usize,
    },

    /// Server returned an empty embedding for a specific input.
    ///
    /// This indicates the model produced no embedding vector for the given
    /// text, which may indicate invalid input or a server-side error.
    #[error("Empty embedding received for text at index {index}")]
    EmptyEmbedding {
        /// Index of the text that produced an empty embedding.
        index: usize,
    },

    /// Server returned embeddings with inconsistent dimensions.
    ///
    /// All embeddings in a batch must have the same dimensionality.
    /// This error indicates the server returned an embedding with a
    /// different dimension than previously observed embeddings.
    #[error("Dimension mismatch at index {index}: expected {expected}, got {actual}")]
    DimensionMismatch {
        /// Expected embedding dimension (from first embedding in batch).
        expected: usize,
        /// Actual embedding dimension received.
        actual: usize,
        /// Index of the text that produced the mismatched embedding.
        index: usize,
    },

    /// Client has been explicitly closed.
    ///
    /// After calling `close()`, all operations will return this error.
    /// This allows for graceful shutdown with connection draining before
    /// the client is dropped.
    #[error("Client has been closed")]
    ClientClosed,
}

/// Result type for TEI operations.
pub type Result<T> = std::result::Result<T, TeiError>;

// =============================================================================
// Retry Error Classification
// =============================================================================

/// Classification of how to handle errors during retry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RetryAction {
    /// Error should be returned immediately, no retry.
    FailImmediately,
    /// Error is retryable without reconnection.
    Retry,
    /// Error warrants channel reconnection before retry.
    ReconnectAndRetry,
}

/// Classify a gRPC status code to determine retry behavior.
///
/// This centralizes the error classification logic used by all retry functions.
#[inline]
fn classify_grpc_code(code: tonic::Code) -> RetryAction {
    match code {
        // Non-retryable errors: client-side issues that won't change on retry
        tonic::Code::InvalidArgument
        | tonic::Code::NotFound
        | tonic::Code::AlreadyExists
        | tonic::Code::PermissionDenied
        | tonic::Code::Unauthenticated => RetryAction::FailImmediately,

        // Channel errors: warrant reconnection before retry
        tonic::Code::Unavailable
        | tonic::Code::Unknown
        | tonic::Code::Internal
        | tonic::Code::Aborted
        | tonic::Code::ResourceExhausted => RetryAction::ReconnectAndRetry,

        // Other errors: retryable without reconnection
        _ => RetryAction::Retry,
    }
}

// =============================================================================
// Data Types
// =============================================================================

/// Server information returned by the Info endpoint.
///
/// Contains comprehensive details about the TEI server configuration,
/// loaded model, and batching limits.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerInfo {
    /// TEI server version (e.g., "1.2.3").
    pub version: String,

    /// Git SHA of the server build (optional).
    pub sha: Option<String>,

    /// Docker image label (optional).
    pub docker_label: Option<String>,

    /// Model identifier (e.g., "BAAI/bge-large-en-v1.5").
    pub model_id: String,

    /// Git SHA of the model (optional).
    pub model_sha: Option<String>,

    /// Model data type (e.g., "float16", "float32").
    pub model_dtype: String,

    /// Type of model (embedding, classifier, reranker).
    pub model_type: ModelType,

    /// Maximum concurrent requests the server can handle.
    pub max_concurrent_requests: u32,

    /// Maximum input length in tokens.
    pub max_input_length: u32,

    /// Maximum tokens per batch.
    pub max_batch_tokens: u32,

    /// Maximum requests per batch (optional).
    pub max_batch_requests: Option<u32>,

    /// Maximum client batch size.
    pub max_client_batch_size: u32,

    /// Number of tokenization workers.
    pub tokenization_workers: u32,
}

impl ServerInfo {
    /// Check if the server is using FP16 (half-precision) inference.
    ///
    /// Returns true if the model dtype is float16/fp16/half,
    /// but NOT bfloat16 (which is a different format).
    #[must_use]
    pub fn is_fp16(&self) -> bool {
        let dtype = self.model_dtype.to_lowercase();
        // Check for float16/fp16/half but exclude bfloat16
        (dtype.contains("float16") || dtype.contains("fp16") || dtype.contains("half"))
            && !dtype.contains("bfloat")
    }

    /// Check if the server is using BF16 (bfloat16) inference.
    #[must_use]
    pub fn is_bf16(&self) -> bool {
        self.model_dtype.to_lowercase().contains("bf16")
            || self.model_dtype.to_lowercase().contains("bfloat")
    }

    /// Get a short description of the server configuration.
    ///
    /// Format: "model_id v{version} ({dtype}, {type})"
    #[must_use]
    pub fn description(&self) -> String {
        format!(
            "{} v{} ({}, {})",
            self.model_id, self.version, self.model_dtype, self.model_type
        )
    }

    /// Get effective batch size considering all limits.
    ///
    /// Returns the minimum of max_client_batch_size and max_batch_requests
    /// (if set), representing the practical limit for client batching.
    #[must_use]
    pub fn effective_batch_size(&self) -> u32 {
        match self.max_batch_requests {
            Some(max_requests) => self.max_client_batch_size.min(max_requests),
            None => self.max_client_batch_size,
        }
    }
}

/// Model type classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModelType {
    /// Dense embedding model (e.g., BGE, MiniLM).
    Embedding,
    /// Classification model.
    Classifier,
    /// Cross-encoder reranking model.
    Reranker,
    /// Unknown or unrecognized model type.
    Unknown,
}

impl From<i32> for ModelType {
    fn from(val: i32) -> Self {
        match val {
            0 => Self::Embedding,
            1 => Self::Classifier,
            2 => Self::Reranker,
            _ => Self::Unknown,
        }
    }
}

impl fmt::Display for ModelType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Embedding => write!(f, "embedding"),
            Self::Classifier => write!(f, "classifier"),
            Self::Reranker => write!(f, "reranker"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Token from tokenization endpoint.
#[derive(Debug, Clone)]
pub struct Token {
    pub id: u32,
    pub text: String,
    pub special: bool,
    pub start: Option<u32>,
    pub stop: Option<u32>,
}

/// Result from reranking operation.
///
/// Contains the original index, relevance score, and optionally the text.
#[derive(Debug, Clone)]
pub struct RerankResult {
    /// Original index in the input texts array.
    pub index: usize,
    /// Relevance score (higher = more relevant to query).
    pub score: f32,
    /// Original text (only populated if `return_text` was true).
    pub text: Option<String>,
}

/// Sparse embedding value (index-value pair for SPLADE-style embeddings).
///
/// Sparse embeddings represent text as a sparse vector where only non-zero
/// dimensions have values. Each `SparseValue` represents one non-zero entry:
/// - `index`: The dimension/token ID in the vocabulary
/// - `value`: The weight/importance of that token for this text
///
/// SPLADE models typically produce sparse vectors with 50-300 non-zero entries
/// out of a vocabulary of 30,000+ tokens.
#[derive(Debug, Clone, PartialEq)]
pub struct SparseValue {
    /// Vocabulary index (token ID) for this non-zero dimension.
    pub index: u32,
    /// Weight/importance value for this dimension.
    pub value: f32,
}

/// Sparse embedding result containing all non-zero values.
///
/// Used for lexical matching combined with dense semantic search (hybrid retrieval).
/// Sparse embeddings capture exact term matches while dense embeddings capture
/// semantic similarity.
///
/// # Hybrid Search
///
/// A typical hybrid retrieval pipeline:
/// 1. Generate both sparse and dense embeddings for documents
/// 2. At query time, generate sparse and dense query embeddings
/// 3. Retrieve candidates using sparse (BM25-like) scoring
/// 4. Re-rank or combine with dense similarity scores
#[derive(Debug, Clone)]
pub struct SparseEmbedding {
    /// Non-zero values in the sparse vector.
    ///
    /// Typically sorted by index for efficient operations, but ordering
    /// depends on the TEI server implementation.
    pub values: Vec<SparseValue>,
}

impl SparseEmbedding {
    /// Returns the number of non-zero dimensions in this sparse embedding.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns true if the sparse embedding has no non-zero values.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Compute the dot product between two sparse embeddings.
    ///
    /// This is useful for computing similarity between sparse vectors
    /// without expanding to dense representation.
    ///
    /// # Performance
    ///
    /// O(n + m) where n and m are the number of non-zero values in each
    /// embedding, assuming both are sorted by index.
    pub fn dot(&self, other: &SparseEmbedding) -> f32 {
        // Use merge-join algorithm for sorted sparse vectors
        let mut i = 0;
        let mut j = 0;
        let mut result = 0.0f32;

        while i < self.values.len() && j < other.values.len() {
            match self.values[i].index.cmp(&other.values[j].index) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => {
                    result += self.values[i].value * other.values[j].value;
                    i += 1;
                    j += 1;
                }
            }
        }

        result
    }

    /// Sort the sparse values by index for efficient operations.
    ///
    /// Call this if you need to perform operations that assume sorted order
    /// (like `dot()`) and are unsure whether the values are sorted.
    pub fn sort_by_index(&mut self) {
        self.values.sort_unstable_by_key(|v| v.index);
    }
}

/// Metadata from embedding request.
///
/// Contains performance timing information useful for debugging
/// and optimization. All time values are in nanoseconds.
#[derive(Debug, Clone, Default)]
pub struct EmbedMetadata {
    /// Number of characters processed.
    pub compute_chars: u32,
    /// Number of tokens processed.
    pub compute_tokens: u32,
    /// Total request time in nanoseconds.
    pub total_time_ns: u64,
    /// Time spent tokenizing in nanoseconds.
    pub tokenization_time_ns: u64,
    /// Time spent waiting in queue in nanoseconds.
    pub queue_time_ns: u64,
    /// Time spent on model inference in nanoseconds.
    pub inference_time_ns: u64,
}

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the TEI client.
#[derive(Debug, Clone)]
pub struct TeiClientConfig {
    /// Server endpoint (e.g., "http://localhost:18080")
    pub endpoint: String,

    /// Request timeout in seconds.
    pub timeout_secs: u64,

    /// Maximum number of attempts for each request.
    ///
    /// This includes the initial attempt plus any retries on failure.
    /// - 1 = no retries (try once, fail immediately on error)
    /// - 2 = 1 retry (try up to twice)
    /// - 3 = 2 retries (try up to three times, the default)
    ///
    /// Set to 0 to disable requests entirely (not recommended).
    ///
    /// Default: 3
    pub max_attempts: u32,

    /// Base delay for exponential backoff (milliseconds).
    pub retry_base_delay_ms: u64,

    /// Maximum delay for exponential backoff (milliseconds).
    pub retry_max_delay_ms: u64,

    /// Token budget per batch (for batching optimization).
    /// TEI batches by total tokens, not by request count.
    pub batch_token_budget: usize,

    /// Keep-alive interval in seconds.
    pub keepalive_secs: u64,
}

impl Default for TeiClientConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:18080".to_string(),
            timeout_secs: 120,
            max_attempts: 3,
            retry_base_delay_ms: 100,
            retry_max_delay_ms: 5000,
            batch_token_budget: 65536,
            keepalive_secs: 30,
        }
    }
}

impl TeiClientConfig {
    /// Create config from environment variables with fallbacks.
    ///
    /// Environment variables:
    /// - `BRRR_TEI_HOST`: Server host (default: localhost)
    /// - `BRRR_TEI_PORT`: Server port (default: 18080)
    pub fn from_env() -> Self {
        let host = std::env::var("BRRR_TEI_HOST").unwrap_or_else(|_| "localhost".to_string());
        let port = std::env::var("BRRR_TEI_PORT")
            .ok()
            .and_then(|p| p.parse().ok())
            .unwrap_or(18080u16);

        Self {
            endpoint: format!("http://{host}:{port}"),
            ..Default::default()
        }
    }

    /// Returns the number of retries (attempts after the initial one).
    ///
    /// This is a convenience method that derives retry count from `max_attempts`.
    /// Since `max_attempts` includes the initial attempt, the actual number of
    /// retries is always one less.
    ///
    /// # Examples
    ///
    /// ```
    /// use brrr::embedding::TeiClientConfig;
    ///
    /// let config = TeiClientConfig::default();
    /// assert_eq!(config.max_attempts, 3);
    /// assert_eq!(config.retry_count(), 2); // 2 retries after initial attempt
    ///
    /// let no_retry = TeiClientConfig { max_attempts: 1, ..Default::default() };
    /// assert_eq!(no_retry.retry_count(), 0); // No retries, just initial attempt
    /// ```
    #[must_use]
    pub const fn retry_count(&self) -> u32 {
        self.max_attempts.saturating_sub(1)
    }
}

// =============================================================================
// Backoff Utilities
// =============================================================================

/// Calculate exponential backoff duration with random jitter.
///
/// Uses true random jitter (0-25% of backoff delay) to prevent the thundering
/// herd problem where all clients retry simultaneously after a failure.
///
/// # Arguments
///
/// * `base_delay_ms` - Base delay in milliseconds
/// * `max_delay_ms` - Maximum delay cap in milliseconds
/// * `attempt` - Current retry attempt number (1-indexed)
///
/// # Returns
///
/// Duration with exponential backoff and random jitter applied.
fn calculate_backoff_with_jitter(base_delay_ms: u64, max_delay_ms: u64, attempt: u32) -> Duration {
    // Exponential backoff: base * 2^attempt, capped at 2^6 = 64x to prevent overflow
    let backoff_ms = base_delay_ms.saturating_mul(1 << attempt.min(6));

    // Cap at maximum delay
    let capped_delay_ms = backoff_ms.min(max_delay_ms);

    // Random jitter: 0 to 25% of the capped delay
    // This ensures different clients retry at different times
    let max_jitter_ms = capped_delay_ms / 4;
    let jitter_ms = if max_jitter_ms > 0 {
        rand::thread_rng().gen_range(0..=max_jitter_ms)
    } else {
        0
    };

    Duration::from_millis(capped_delay_ms + jitter_ms)
}

/// Estimate token count from character count using heuristic.
///
/// Most embedding models (BGE, Qwen, etc.) use subword tokenization where
/// average tokens per character is approximately 0.25-0.33 for English text.
/// We use 0.30 as a conservative estimate (slightly over-estimates tokens).
///
/// This avoids a server round-trip for token counting, which was causing
/// double tokenization overhead: once for batching, once for embedding.
///
/// # Arguments
///
/// * `char_count` - Number of characters in the text
///
/// # Returns
///
/// Estimated token count (conservative, tends to slightly over-estimate).
#[inline]
fn estimate_tokens_from_chars(char_count: usize) -> usize {
    // ~3.3 chars per token on average, use 3 to be conservative
    // This means we slightly over-estimate tokens, leading to smaller batches
    // which is safer than under-estimating and hitting server limits
    (char_count + 2) / 3
}

// =============================================================================
// Client Implementation
// =============================================================================

/// High-level client for TEI gRPC server.
///
/// Provides async interface for:
/// - `embed()`: Dense embeddings (streaming RPC)
/// - `embed_single()`: Single embedding with metadata (unary RPC)
/// - `embed_batch()`: Batched embeddings with token-budget optimization
/// - `tokenize()`: Get tokens with offsets
/// - `count_tokens()`: Fast token counting
/// - `decode()`: Convert token IDs back to text
/// - `decode_batch()`: Batch decode multiple token sequences
/// - `rerank()`: Cross-encoder reranking of texts against a query
/// - `info()`: Server information
///
/// # Reconnection Behavior
///
/// The client automatically reconnects when channel errors are detected
/// (connection failures, transport errors, unavailable server). This provides
/// resilience against:
/// - Server restarts
/// - Network interruptions
/// - Connection timeouts
/// - Load balancer failovers
///
/// # Graceful Shutdown
///
/// While Rust's Drop trait handles cleanup automatically, explicit shutdown
/// can be performed via `close()` for controlled connection draining:
///
/// ```no_run
/// use brrr::embedding::TeiClient;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let client = TeiClient::new("http://localhost:18080").await?;
///     // ... use client ...
///     client.close().await?;  // Graceful shutdown
///     // client.embed(...) would now return ClientClosed error
///     Ok(())
/// }
/// ```
pub struct TeiClient {
    config: TeiClientConfig,
    /// gRPC channel wrapped in RwLock for automatic reconnection on failure.
    channel: RwLock<Channel>,
    /// Cached server info for batching decisions.
    ///
    /// Uses `OnceCell` for exactly-once initialization semantics, preventing
    /// redundant `info()` calls under high concurrency. Server info is static
    /// metadata that doesn't change during runtime, so we don't need to
    /// invalidate this cache on reconnection.
    server_info: OnceCell<ServerInfo>,
    /// Semaphore for limiting concurrent requests to the server.
    ///
    /// Initialized lazily based on `server_info.max_concurrent_requests` to
    /// prevent overwhelming the TEI server with too many parallel requests.
    /// This is critical for avoiding server-side queue overflow and timeouts.
    request_semaphore: OnceCell<Semaphore>,
    /// Tracks whether the client has been explicitly closed.
    ///
    /// Uses `AtomicBool` with `SeqCst` ordering for thread-safe access without
    /// requiring a lock. Once set to `true`, all operations return `ClientClosed`.
    closed: AtomicBool,
}

impl TeiClient {
    /// Create a new TEI client with the given endpoint.
    ///
    /// # Arguments
    ///
    /// * `endpoint` - Server endpoint (e.g., "http://localhost:18080")
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let embeddings = client.embed(&["hello world"]).await?;
    ///     Ok(())
    /// }
    /// ```
    pub async fn new(endpoint: &str) -> Result<Self> {
        let config = TeiClientConfig {
            endpoint: endpoint.to_string(),
            ..Default::default()
        };
        Self::with_config(config).await
    }

    /// Create a new TEI client with custom configuration.
    pub async fn with_config(config: TeiClientConfig) -> Result<Self> {
        let channel = Self::create_channel(&config).await?;

        Ok(Self {
            config,
            channel: RwLock::new(channel),
            server_info: OnceCell::const_new(),
            request_semaphore: OnceCell::const_new(),
            closed: AtomicBool::new(false),
        })
    }

    /// Create a new TEI client from environment variables.
    ///
    /// Uses `BRRR_TEI_HOST` and `BRRR_TEI_PORT` environment variables.
    pub async fn from_env() -> Result<Self> {
        Self::with_config(TeiClientConfig::from_env()).await
    }

    // =========================================================================
    // Lifecycle Management
    // =========================================================================

    /// Close the client explicitly for graceful shutdown.
    ///
    /// After calling `close()`, all methods will return `TeiError::ClientClosed`.
    /// This allows for graceful shutdown with connection draining before the
    /// client is dropped.
    ///
    /// This method is idempotent - calling it multiple times has no additional
    /// effect after the first call.
    ///
    /// # Thread Safety
    ///
    /// The close operation uses atomic compare-and-swap to ensure only one
    /// thread performs the actual close. The write lock on the channel ensures
    /// no new operations can acquire the channel during the close sequence.
    ///
    /// # In-Flight Request Behavior
    ///
    /// Requests that have already acquired a channel reference before `close()`
    /// is called may continue to completion. Retry loops check the closed state
    /// at the start of each attempt, so in-flight requests will return
    /// `ClientClosed` on their next retry attempt if `close()` is called during
    /// a retry backoff.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     // ... use client ...
    ///     client.close().await?;  // Graceful shutdown
    ///     assert!(client.is_closed());
    ///     // client.embed(...) would now return ClientClosed error
    ///     Ok(())
    /// }
    /// ```
    pub async fn close(&self) -> Result<()> {
        // Atomically mark as closed; if already closed, return immediately
        if self.closed.swap(true, Ordering::SeqCst) {
            return Ok(());
        }

        // Acquire write lock to ensure no in-flight operations use the channel
        // This provides a synchronization point for graceful connection draining
        let mut channel = self.channel.write().await;

        // Replace channel with a lazy-connecting dummy endpoint
        // This invalidates any cached channel references and prevents new connections
        // The dummy endpoint points to localhost:1 which will fail to connect if used
        *channel = Channel::from_static("http://[::1]:1").connect_lazy();

        Ok(())
    }

    /// Check if the client has been explicitly closed.
    ///
    /// Returns `true` if `close()` has been called on this client.
    ///
    /// # Thread Safety
    ///
    /// This method uses atomic load with `SeqCst` ordering, providing a
    /// consistent view of the closed state across all threads.
    #[inline]
    pub fn is_closed(&self) -> bool {
        self.closed.load(Ordering::SeqCst)
    }

    /// Ensure the client has not been closed before performing operations.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    #[inline]
    fn ensure_not_closed(&self) -> Result<()> {
        if self.is_closed() {
            return Err(TeiError::ClientClosed);
        }
        Ok(())
    }

    // =========================================================================
    // Channel Management
    // =========================================================================

    /// Create the gRPC channel with optimized settings.
    ///
    /// Wraps the tonic connect in a hard tokio timeout as a safety net —
    /// tonic's connect_timeout can silently hang on some systems/configurations.
    async fn create_channel(config: &TeiClientConfig) -> Result<Channel> {
        let endpoint = Endpoint::from_shared(config.endpoint.clone())
            .map_err(|e| TeiError::Config(e.to_string()))?
            .timeout(Duration::from_secs(config.timeout_secs))
            .tcp_keepalive(Some(Duration::from_secs(config.keepalive_secs)))
            .http2_keep_alive_interval(Duration::from_secs(config.keepalive_secs))
            .keep_alive_timeout(Duration::from_secs(10))
            .connect_timeout(Duration::from_secs(5));

        // Hard 10s outer timeout — tonic's connect_timeout is unreliable on
        // some platforms (e.g. when nothing listens but connection isn't refused).
        match tokio::time::timeout(Duration::from_secs(10), endpoint.connect()).await {
            Ok(Ok(channel)) => Ok(channel),
            Ok(Err(e)) => Err(TeiError::Connection(e.to_string())),
            Err(_elapsed) => Err(TeiError::Connection(format!(
                "connection to {} timed out after 10s — is the TEI server running?",
                config.endpoint
            ))),
        }
    }

    /// Get a clone of the current channel.
    ///
    /// This method acquires a read lock on the channel and returns a clone.
    /// The clone can be used for gRPC operations without holding the lock.
    async fn get_channel(&self) -> Channel {
        self.channel.read().await.clone()
    }

    /// Reconnect the channel after a failure.
    ///
    /// This method creates a new channel and replaces the existing one.
    /// It acquires a write lock BEFORE creating the channel to prevent race
    /// conditions where multiple threads could create different channels and
    /// one would overwrite the other.
    ///
    /// Note: Server info cache is NOT cleared on reconnection because it contains
    /// static metadata (model ID, max lengths, etc.) that doesn't change unless
    /// the server is replaced entirely. For load balancer failover to a different
    /// backend with different configuration, create a new `TeiClient` instance.
    ///
    /// # Returns
    ///
    /// The newly created channel on success, or an error if reconnection fails.
    ///
    /// # Thread Safety
    ///
    /// The write lock is held during channel creation to ensure only one thread
    /// performs reconnection at a time. While this means readers will block during
    /// reconnection, this is acceptable because:
    /// 1. Reconnection is a rare event (only on channel failures)
    /// 2. Readers using a stale channel would fail anyway
    /// 3. Tokio's async RwLock doesn't block the runtime
    async fn reconnect(&self) -> Result<Channel> {
        // Acquire write lock FIRST to prevent race condition where multiple
        // threads create different channels and one overwrites the other
        let mut channel = self.channel.write().await;

        // Create new channel while holding the lock
        let new_channel = Self::create_channel(&self.config).await?;
        *channel = new_channel.clone();

        Ok(new_channel)
    }

    /// Check if an error indicates a channel/connection problem that warrants reconnection.
    ///
    /// Returns `true` for errors that suggest the channel is broken or overloaded:
    /// - Connection errors (server unreachable, connection reset)
    /// - Transport errors (HTTP/2 errors, stream failures)
    /// - gRPC status codes indicating server unavailability or overload:
    ///   - `Unavailable`: Server is not reachable
    ///   - `Unknown`: Unknown error (often transport-level)
    ///   - `Internal`: Server-side error
    ///   - `Aborted`: Operation aborted
    ///   - `ResourceExhausted`: Server is overloaded (may benefit from reconnection
    ///     to a different backend via load balancer)
    fn is_channel_error(&self, error: &TeiError) -> bool {
        match error {
            TeiError::Connection(_) | TeiError::Transport(_) => true,
            TeiError::Grpc(status) => matches!(
                status.code(),
                tonic::Code::Unavailable
                    | tonic::Code::Unknown
                    | tonic::Code::Internal
                    | tonic::Code::Aborted
                    | tonic::Code::ResourceExhausted
            ),
            _ => false,
        }
    }

    /// Get server information.
    ///
    /// Retrieves metadata about the TEI server including model ID, type,
    /// and batching limits. Uses retry logic with exponential backoff
    /// for resilience against transient failures.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn info(&self) -> Result<ServerInfo> {
        self.ensure_not_closed()?;

        let info = self
            .with_retry_reconnect(|channel| async move {
                let mut client = InfoClient::new(channel);
                let response = client.info(InfoRequest {}).await?;
                Ok(response.into_inner())
            })
            .await?;

        // Convert optional string fields: empty strings become None
        let to_option = |s: String| if s.is_empty() { None } else { Some(s) };

        Ok(ServerInfo {
            version: info.version,
            sha: info.sha.and_then(|s| to_option(s)),
            docker_label: info.docker_label.and_then(|s| to_option(s)),
            model_id: info.model_id,
            model_sha: info.model_sha.and_then(|s| to_option(s)),
            model_dtype: info.model_dtype,
            model_type: ModelType::from(info.model_type),
            max_concurrent_requests: info.max_concurrent_requests,
            max_input_length: info.max_input_length,
            max_batch_tokens: info.max_batch_tokens,
            max_batch_requests: info.max_batch_requests,
            max_client_batch_size: info.max_client_batch_size,
            tokenization_workers: info.tokenization_workers,
        })
    }

    /// Embed texts to dense vectors.
    ///
    /// # Arguments
    ///
    /// * `texts` - Slice of texts to embed
    ///
    /// # Returns
    ///
    /// Vector of embedding vectors (one per input text).
    pub async fn embed(&self, texts: &[&str]) -> Result<Vec<Vec<f32>>> {
        self.embed_with_options(texts, true, true, None).await
    }

    /// Embed texts with custom options.
    ///
    /// # Arguments
    ///
    /// * `texts` - Texts to embed
    /// * `normalize` - L2-normalize embeddings
    /// * `truncate` - Truncate texts exceeding max length
    /// * `dimensions` - Output dimensions for MRL (Matryoshka). None = full.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn embed_with_options(
        &self,
        texts: &[&str],
        normalize: bool,
        truncate: bool,
        dimensions: Option<u32>,
    ) -> Result<Vec<Vec<f32>>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        // Use streaming for multiple texts with retry logic at batch level
        self.embed_stream_with_retry(texts, normalize, truncate, dimensions)
            .await
    }

    /// Embed a single text with full metadata.
    ///
    /// Unlike `embed()` which uses streaming RPC, this method uses the unary
    /// `Embed` RPC and returns detailed performance metadata including timing
    /// information.
    ///
    /// # Arguments
    ///
    /// * `text` - Text to embed
    /// * `normalize` - L2-normalize the embedding
    /// * `truncate` - Truncate text exceeding max length
    /// * `dimensions` - Output dimensions for MRL (Matryoshka). None = full.
    ///
    /// # Returns
    ///
    /// Tuple of (embedding vector, metadata with timing info).
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let (embedding, meta) = client.embed_single("hello world", true, true, None).await?;
    ///     println!("Embedding dim: {}", embedding.len());
    ///     println!("Tokens processed: {}", meta.compute_tokens);
    ///     println!("Inference time: {} ns", meta.inference_time_ns);
    ///     Ok(())
    /// }
    /// ```
    pub async fn embed_single(
        &self,
        text: &str,
        normalize: bool,
        truncate: bool,
        dimensions: Option<u32>,
    ) -> Result<(Vec<f32>, EmbedMetadata)> {
        self.ensure_not_closed()?;

        let request = EmbedRequest {
            inputs: text.to_string(),
            truncate,
            normalize,
            truncation_direction: TruncationDirection::Right.into(),
            prompt_name: None,
            dimensions,
        };

        // Use with_retry_reconnect to get fresh channel on each attempt.
        // This ensures reconnected channels are used after channel errors.
        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = EmbedClient::new(channel);
                    client.embed(req).await
                }
            })
            .await?;

        let inner = response.into_inner();

        let metadata = inner
            .metadata
            .map(|m| EmbedMetadata {
                compute_chars: m.compute_chars,
                compute_tokens: m.compute_tokens,
                total_time_ns: m.total_time_ns,
                tokenization_time_ns: m.tokenization_time_ns,
                queue_time_ns: m.queue_time_ns,
                inference_time_ns: m.inference_time_ns,
            })
            .unwrap_or_default();

        Ok((inner.embeddings, metadata))
    }

    /// Internal streaming embed with retry and reconnection support.
    ///
    /// Retries are handled at the full request level since streams cannot be cloned.
    /// On channel errors, triggers reconnection before the next retry.
    async fn embed_stream_with_retry(
        &self,
        texts: &[&str],
        normalize: bool,
        truncate: bool,
        dimensions: Option<u32>,
    ) -> Result<Vec<Vec<f32>>> {
        let mut attempt = 0;
        // Store status directly to avoid repeated .to_string() calls
        let mut last_grpc_error: Option<tonic::Status> = None;
        let mut last_other_error: Option<String> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Check closed state at start of each attempt to handle race with close()
            if self.is_closed() {
                return Err(TeiError::ClientClosed);
            }

            // Reconnect if previous attempt detected a channel error
            if should_reconnect {
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            match self
                .embed_stream_once(texts, normalize, truncate, dimensions)
                .await
            {
                Ok(results) => return Ok(results),
                Err(TeiError::Grpc(status)) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_grpc_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_grpc_error = Some(status);
                        }
                    }
                }
                Err(e) => {
                    // Non-gRPC errors (connection, transport) also warrant reconnection
                    if self.is_channel_error(&e) {
                        should_reconnect = true;
                    }
                    last_other_error = Some(e.to_string());
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_grpc_error
            .map(|s| s.to_string())
            .or(last_other_error)
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }

    /// Single attempt at streaming embed.
    ///
    /// Validates that:
    /// 1. The server returns exactly as many responses as requests sent
    /// 2. Each embedding vector is non-empty
    /// 3. All embedding vectors have consistent dimensions
    async fn embed_stream_once(
        &self,
        texts: &[&str],
        normalize: bool,
        truncate: bool,
        dimensions: Option<u32>,
    ) -> Result<Vec<Vec<f32>>> {
        let mut client = EmbedClient::new(self.get_channel().await);
        let expected_count = texts.len();

        // BUG FIX: Lazy EmbedRequest creation to reduce memory allocation.
        //
        // Previously, all EmbedRequest objects were eagerly collected into a Vec
        // before streaming. For 100K texts, this allocated ~5-10MB of EmbedRequest
        // structs upfront.
        //
        // Now we:
        // 1. Clone strings to Vec<String> (required for 'static gRPC lifetime)
        // 2. Lazily create EmbedRequest as the stream is consumed
        //
        // This halves memory overhead by avoiding the intermediate Vec<EmbedRequest>.
        // For truly large batches, users should use embed_batch() which chunks the input.
        let owned_texts: Vec<String> = texts.iter().map(|t| (*t).to_string()).collect();
        let request_stream = tokio_stream::iter(owned_texts.into_iter().map(move |text| {
            EmbedRequest {
                inputs: text,
                truncate,
                normalize,
                truncation_direction: TruncationDirection::Right.into(),
                prompt_name: None,
                dimensions,
            }
        }));
        let response = client.embed_stream(request_stream).await?;

        let mut results = Vec::with_capacity(expected_count);
        let mut stream = response.into_inner();

        // Track expected dimension from first embedding for consistency validation
        let mut expected_dims: Option<usize> = None;

        // BUG FIX: Per-item timeout to detect stalled streams (30s per item).
        let per_item_timeout = Duration::from_secs(30);

        use tokio_stream::StreamExt as TokioStreamExt;
        let mut index = 0usize;
        loop {
            // Apply per-item timeout to detect stalled streams
            let next_item =
                tokio::time::timeout(per_item_timeout, TokioStreamExt::next(&mut stream)).await;
            let resp = match next_item {
                Ok(Some(r)) => r?,
                Ok(None) => break, // Stream ended normally
                Err(_) => {
                    return Err(TeiError::RetryExhausted(format!(
                        "Stream stalled: no response for item {} after {}s",
                        index,
                        per_item_timeout.as_secs()
                    )));
                }
            };

            // Validate embedding is not empty
            if resp.embeddings.is_empty() {
                return Err(TeiError::EmptyEmbedding { index });
            }

            // Validate embedding dimensions are consistent across the batch
            let actual_dims = resp.embeddings.len();
            match expected_dims {
                None => {
                    // First embedding establishes the expected dimension
                    expected_dims = Some(actual_dims);
                }
                Some(expected) if actual_dims != expected => {
                    return Err(TeiError::DimensionMismatch {
                        expected,
                        actual: actual_dims,
                        index,
                    });
                }
                Some(_) => {
                    // Dimensions match, continue
                }
            }

            results.push(resp.embeddings);
            index += 1;
        }

        // Validate we received all expected responses
        if results.len() != expected_count {
            return Err(TeiError::PartialResponse {
                expected: expected_count,
                received: results.len(),
            });
        }

        Ok(results)
    }

    /// Embed texts in batches optimized for token budget.
    ///
    /// Uses character-based token estimation to avoid double tokenization overhead.
    /// Previously, this method called `count_tokens_batch()` (round-trip 1) followed
    /// by `embed()` (round-trip 2). Now it estimates tokens from character counts.
    ///
    /// # Arguments
    ///
    /// * `texts` - Texts to embed
    /// * `batch_size` - Maximum texts per batch (overrides token-based batching)
    ///
    /// # Returns
    ///
    /// Vector of embedding vectors (one per input text).
    ///
    /// # Performance
    ///
    /// - Uses character-based token estimation (avoids server round-trip)
    /// - Processes batches in parallel with concurrency control
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn embed_batch(
        &self,
        texts: &[&str],
        batch_size: Option<usize>,
    ) -> Result<Vec<Vec<f32>>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        // Get or fetch server info for batching decisions
        let server_info = self.get_cached_server_info().await?;
        let max_batch = batch_size
            .unwrap_or(server_info.max_client_batch_size as usize)
            .min(server_info.max_client_batch_size as usize);

        // BUG FIX: Use character-based token estimation instead of server round-trip.
        // Previously: count_tokens_batch() made a server call THEN embed() made another.
        // Now: Estimate tokens from char count (~3 chars/token for subword tokenizers).
        let token_counts: Vec<usize> = texts
            .iter()
            .map(|t| estimate_tokens_from_chars(t.len()))
            .collect();

        // Respect both client config and server's max_batch_tokens limit
        let token_budget = self
            .config
            .batch_token_budget
            .min(server_info.max_batch_tokens as usize);

        // Build batches based on token budget
        let batches = Self::build_token_batches(texts, &token_counts, token_budget, max_batch);

        // Get semaphore for concurrency control (reference to self.request_semaphore)
        // Semaphore limits concurrent requests to server's max_concurrent_requests
        let semaphore = self.get_request_semaphore().await?;

        // BUG FIX: Process batches in parallel instead of sequentially.
        // Previously: for batch in batches { embed(&batch).await? }
        // Now: Use buffer_unordered for concurrent batch processing.
        use futures::StreamExt as FuturesStreamExt;

        // Use server's max_concurrent_requests as the concurrency limit.
        // Cap at 32 for client-side resource management (memory for in-flight requests).
        // The semaphore provides the actual rate limiting based on server capacity.
        let max_concurrent = (server_info.max_concurrent_requests as usize).clamp(1, 32);

        let batch_futures = batches.into_iter().enumerate().map(|(batch_idx, batch)| {
            async move {
                // Acquire permit before making request
                let _permit = semaphore.acquire().await.map_err(|_| {
                    TeiError::Connection("Request semaphore closed unexpectedly".to_string())
                })?;

                let batch_results = self.embed(&batch).await?;
                Ok::<_, TeiError>((batch_idx, batch_results))
            }
        });

        // Execute batches concurrently with bounded parallelism
        let results: Vec<_> = stream::iter(batch_futures)
            .buffer_unordered(max_concurrent)
            .collect()
            .await;

        // Sort by batch index and flatten, checking for errors
        let mut indexed_results: Vec<(usize, Vec<Vec<f32>>)> = Vec::with_capacity(results.len());
        for result in results {
            indexed_results.push(result?);
        }
        indexed_results.sort_by_key(|(idx, _)| *idx);

        let all_results: Vec<Vec<f32>> = indexed_results
            .into_iter()
            .flat_map(|(_, batch_results)| batch_results)
            .collect();

        Ok(all_results)
    }

    /// Build batches based on token budget.
    ///
    /// Greedy algorithm: add texts to current batch until token budget
    /// would be exceeded, then start new batch.
    fn build_token_batches<'a>(
        texts: &[&'a str],
        token_counts: &[usize],
        token_budget: usize,
        max_batch: usize,
    ) -> Vec<Vec<&'a str>> {
        let mut batches = Vec::new();
        let mut current_batch = Vec::new();
        let mut current_tokens = 0usize;

        for (text, &count) in texts.iter().zip(token_counts.iter()) {
            // Start new batch if adding this text would exceed budget
            // or if we've hit the max batch size
            if !current_batch.is_empty()
                && (current_tokens + count > token_budget || current_batch.len() >= max_batch)
            {
                batches.push(std::mem::take(&mut current_batch));
                current_tokens = 0;
            }

            current_batch.push(*text);
            current_tokens += count;
        }

        // Don't forget the last batch
        if !current_batch.is_empty() {
            batches.push(current_batch);
        }

        batches
    }

    // =========================================================================
    // Sparse Embedding Methods (SPLADE-style)
    // =========================================================================

    /// Generate a sparse embedding for a single text (SPLADE-style).
    ///
    /// Sparse embeddings are useful for lexical matching combined with
    /// dense semantic search (hybrid retrieval). They capture exact term
    /// matches while dense embeddings capture semantic similarity.
    ///
    /// # Arguments
    ///
    /// * `text` - Text to embed
    ///
    /// # Returns
    ///
    /// Sparse embedding containing non-zero dimension values.
    ///
    /// # Errors
    ///
    /// * `TeiError::EmptyResponse` - If the server returns no results
    /// * `TeiError::Grpc` - If the gRPC call fails
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let sparse = client.embed_sparse("hello world").await?;
    ///     println!("Non-zero dimensions: {}", sparse.len());
    ///     for sv in &sparse.values[..5.min(sparse.len())] {
    ///         println!("  token {}: {:.4}", sv.index, sv.value);
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub async fn embed_sparse(&self, text: &str) -> Result<SparseEmbedding> {
        let results = self.embed_sparse_batch(&[text]).await?;
        results.into_iter().next().ok_or(TeiError::EmptyResponse)
    }

    /// Generate a sparse embedding with metadata for a single text.
    ///
    /// Unlike `embed_sparse()` which uses streaming RPC, this method uses
    /// the unary `EmbedSparse` RPC and returns detailed performance metadata.
    ///
    /// # Arguments
    ///
    /// * `text` - Text to embed
    /// * `truncate` - Whether to truncate text exceeding max length
    ///
    /// # Returns
    ///
    /// Tuple of (sparse embedding, metadata with timing info).
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn embed_sparse_single(
        &self,
        text: &str,
        truncate: bool,
    ) -> Result<(SparseEmbedding, EmbedMetadata)> {
        self.ensure_not_closed()?;

        let request = tei_proto::EmbedSparseRequest {
            inputs: text.to_string(),
            truncate,
            truncation_direction: TruncationDirection::Right.into(),
            prompt_name: None,
        };

        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = EmbedClient::new(channel);
                    client.embed_sparse(req).await
                }
            })
            .await?;

        let inner = response.into_inner();

        let values: Vec<SparseValue> = inner
            .sparse_embeddings
            .into_iter()
            .map(|sv| SparseValue {
                index: sv.index,
                value: sv.value,
            })
            .collect();

        let metadata = inner
            .metadata
            .map(|m| EmbedMetadata {
                compute_chars: m.compute_chars,
                compute_tokens: m.compute_tokens,
                total_time_ns: m.total_time_ns,
                tokenization_time_ns: m.tokenization_time_ns,
                queue_time_ns: m.queue_time_ns,
                inference_time_ns: m.inference_time_ns,
            })
            .unwrap_or_default();

        Ok((SparseEmbedding { values }, metadata))
    }

    /// Generate sparse embeddings for multiple texts using streaming.
    ///
    /// More efficient than calling `embed_sparse()` multiple times when
    /// processing many texts.
    ///
    /// # Arguments
    ///
    /// * `texts` - Texts to embed
    ///
    /// # Returns
    ///
    /// Vector of sparse embeddings (one per input text).
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let texts = &["first document", "second document", "third document"];
    ///     let embeddings = client.embed_sparse_batch(texts).await?;
    ///     for (i, emb) in embeddings.iter().enumerate() {
    ///         println!("Text {}: {} non-zero values", i, emb.len());
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub async fn embed_sparse_batch(&self, texts: &[&str]) -> Result<Vec<SparseEmbedding>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        self.embed_sparse_stream_with_retry(texts, true).await
    }

    /// Generate sparse embeddings with custom options.
    ///
    /// # Arguments
    ///
    /// * `texts` - Texts to embed
    /// * `truncate` - Whether to truncate texts exceeding max length
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn embed_sparse_with_options(
        &self,
        texts: &[&str],
        truncate: bool,
    ) -> Result<Vec<SparseEmbedding>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        self.embed_sparse_stream_with_retry(texts, truncate).await
    }

    /// Internal streaming sparse embed with retry and reconnection support.
    async fn embed_sparse_stream_with_retry(
        &self,
        texts: &[&str],
        truncate: bool,
    ) -> Result<Vec<SparseEmbedding>> {
        let mut attempt = 0;
        // Store status directly to avoid repeated .to_string() calls
        let mut last_grpc_error: Option<tonic::Status> = None;
        let mut last_other_error: Option<String> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Check closed state at start of each attempt to handle race with close()
            if self.is_closed() {
                return Err(TeiError::ClientClosed);
            }

            // Reconnect if previous attempt detected a channel error
            if should_reconnect {
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            match self.embed_sparse_stream_once(texts, truncate).await {
                Ok(results) => return Ok(results),
                Err(TeiError::Grpc(status)) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_grpc_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_grpc_error = Some(status);
                        }
                    }
                }
                Err(e) => {
                    // Non-gRPC errors (connection, transport) also warrant reconnection
                    if self.is_channel_error(&e) {
                        should_reconnect = true;
                    }
                    last_other_error = Some(e.to_string());
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_grpc_error
            .map(|s| s.to_string())
            .or(last_other_error)
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }

    /// Single attempt at streaming sparse embed.
    ///
    /// Validates that the server returns exactly as many responses as requests sent.
    async fn embed_sparse_stream_once(
        &self,
        texts: &[&str],
        truncate: bool,
    ) -> Result<Vec<SparseEmbedding>> {
        let mut client = EmbedClient::new(self.get_channel().await);
        let expected_count = texts.len();

        // Lazy EmbedSparseRequest creation - clone strings for 'static lifetime,
        // then create request objects on-demand as the stream is consumed.
        let owned_texts: Vec<String> = texts.iter().map(|t| (*t).to_string()).collect();
        let request_stream =
            tokio_stream::iter(owned_texts.into_iter().map(move |text| {
                tei_proto::EmbedSparseRequest {
                    inputs: text,
                    truncate,
                    truncation_direction: TruncationDirection::Right.into(),
                    prompt_name: None,
                }
            }));
        let response = client.embed_sparse_stream(request_stream).await?;

        let mut results = Vec::with_capacity(expected_count);
        let mut stream = response.into_inner();

        use tokio_stream::StreamExt as TokioStreamExt;
        while let Some(resp) = TokioStreamExt::next(&mut stream).await {
            let resp = resp?;
            let values: Vec<SparseValue> = resp
                .sparse_embeddings
                .into_iter()
                .map(|sv| SparseValue {
                    index: sv.index,
                    value: sv.value,
                })
                .collect();
            results.push(SparseEmbedding { values });
        }

        // Validate we received all expected responses
        if results.len() != expected_count {
            return Err(TeiError::PartialResponse {
                expected: expected_count,
                received: results.len(),
            });
        }

        Ok(results)
    }

    // =========================================================================
    // Tokenization Methods
    // =========================================================================

    /// Tokenize a single text.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn tokenize(&self, text: &str, add_special_tokens: bool) -> Result<Vec<Token>> {
        self.ensure_not_closed()?;

        let request = EncodeRequest {
            inputs: text.to_string(),
            add_special_tokens,
            prompt_name: None,
        };

        // Use with_retry_reconnect to get fresh channel on each attempt.
        // This ensures reconnected channels are used after channel errors.
        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = TokenizeClient::new(channel);
                    client.tokenize(req).await
                }
            })
            .await?;

        let tokens = response
            .into_inner()
            .tokens
            .into_iter()
            .map(|t| Token {
                id: t.id,
                text: t.text,
                special: t.special,
                start: t.start,
                stop: t.stop,
            })
            .collect();

        Ok(tokens)
    }

    /// Count tokens for a single text.
    pub async fn count_tokens(&self, text: &str) -> Result<usize> {
        let tokens = self.tokenize(text, false).await?;
        Ok(tokens.len())
    }

    /// Count tokens for multiple texts efficiently using streaming.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn count_tokens_batch(&self, texts: &[&str]) -> Result<Vec<usize>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        self.count_tokens_batch_with_retry(texts).await
    }

    /// Internal streaming tokenize with retry and reconnection support.
    async fn count_tokens_batch_with_retry(&self, texts: &[&str]) -> Result<Vec<usize>> {
        let mut attempt = 0;
        // Store status directly to avoid repeated .to_string() calls
        let mut last_grpc_error: Option<tonic::Status> = None;
        let mut last_other_error: Option<String> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Check closed state at start of each attempt to handle race with close()
            if self.is_closed() {
                return Err(TeiError::ClientClosed);
            }

            if should_reconnect {
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            match self.count_tokens_batch_once(texts).await {
                Ok(counts) => return Ok(counts),
                Err(TeiError::Grpc(status)) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_grpc_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_grpc_error = Some(status);
                        }
                    }
                }
                Err(e) => {
                    if self.is_channel_error(&e) {
                        should_reconnect = true;
                    }
                    last_other_error = Some(e.to_string());
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_grpc_error
            .map(|s| s.to_string())
            .or(last_other_error)
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }

    /// Single attempt at streaming tokenize count.
    ///
    /// Validates that the server returns exactly as many responses as requests sent.
    async fn count_tokens_batch_once(&self, texts: &[&str]) -> Result<Vec<usize>> {
        let mut client = TokenizeClient::new(self.get_channel().await);
        let expected_count = texts.len();

        // Lazy EncodeRequest creation - clone strings for 'static lifetime,
        // then create request objects on-demand as the stream is consumed.
        let owned_texts: Vec<String> = texts.iter().map(|t| (*t).to_string()).collect();
        let request_stream = tokio_stream::iter(owned_texts.into_iter().map(|text| {
            EncodeRequest {
                inputs: text,
                add_special_tokens: false,
                prompt_name: None,
            }
        }));
        let response = client.tokenize_stream(request_stream).await?;

        let mut counts = Vec::with_capacity(expected_count);
        let mut stream = response.into_inner();

        use tokio_stream::StreamExt as TokioStreamExt;
        while let Some(resp) = TokioStreamExt::next(&mut stream).await {
            let resp = resp?;
            counts.push(resp.tokens.len());
        }

        // Validate we received all expected responses
        if counts.len() != expected_count {
            return Err(TeiError::PartialResponse {
                expected: expected_count,
                received: counts.len(),
            });
        }

        Ok(counts)
    }

    /// Decode token IDs back to text.
    ///
    /// This is the inverse of tokenization - converts a sequence of token IDs
    /// back into the original text representation.
    ///
    /// # Arguments
    ///
    /// * `token_ids` - Slice of token IDs to decode
    ///
    /// # Returns
    ///
    /// The decoded text string.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let tokens = client.tokenize("hello world", true).await?;
    ///     let ids: Vec<u32> = tokens.iter().map(|t| t.id).collect();
    ///     let text = client.decode(&ids).await?;
    ///     Ok(())
    /// }
    /// ```
    pub async fn decode(&self, token_ids: &[u32]) -> Result<String> {
        self.decode_with_options(token_ids, false).await
    }

    /// Decode token IDs back to text with options.
    ///
    /// # Arguments
    ///
    /// * `token_ids` - Slice of token IDs to decode
    /// * `skip_special_tokens` - If true, special tokens (e.g., [CLS], [SEP]) are
    ///   omitted from the output text
    ///
    /// # Returns
    ///
    /// The decoded text string.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn decode_with_options(
        &self,
        token_ids: &[u32],
        skip_special_tokens: bool,
    ) -> Result<String> {
        self.ensure_not_closed()?;

        let request = DecodeRequest {
            ids: token_ids.to_vec(),
            skip_special_tokens,
        };

        // Use with_retry_reconnect to get fresh channel on each attempt.
        // This ensures reconnected channels are used after channel errors.
        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = TokenizeClient::new(channel);
                    client.decode(req).await
                }
            })
            .await?;

        Ok(response.into_inner().text)
    }

    /// Decode multiple token ID sequences in batch using streaming.
    ///
    /// More efficient than calling `decode()` multiple times when decoding
    /// many sequences.
    ///
    /// # Arguments
    ///
    /// * `token_id_batches` - Slice of token ID sequences to decode
    /// * `skip_special_tokens` - If true, special tokens are omitted from output
    ///
    /// # Returns
    ///
    /// Vector of decoded text strings (one per input sequence).
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn decode_batch(
        &self,
        token_id_batches: &[&[u32]],
        skip_special_tokens: bool,
    ) -> Result<Vec<String>> {
        self.ensure_not_closed()?;

        if token_id_batches.is_empty() {
            return Ok(Vec::new());
        }

        self.decode_batch_with_retry(token_id_batches, skip_special_tokens)
            .await
    }

    /// Internal streaming decode with retry and reconnection support.
    async fn decode_batch_with_retry(
        &self,
        token_id_batches: &[&[u32]],
        skip_special_tokens: bool,
    ) -> Result<Vec<String>> {
        let mut attempt = 0;
        // Store status directly to avoid repeated .to_string() calls
        let mut last_grpc_error: Option<tonic::Status> = None;
        let mut last_other_error: Option<String> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Check closed state at start of each attempt to handle race with close()
            if self.is_closed() {
                return Err(TeiError::ClientClosed);
            }

            if should_reconnect {
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            match self
                .decode_batch_once(token_id_batches, skip_special_tokens)
                .await
            {
                Ok(results) => return Ok(results),
                Err(TeiError::Grpc(status)) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_grpc_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_grpc_error = Some(status);
                        }
                    }
                }
                Err(e) => {
                    if self.is_channel_error(&e) {
                        should_reconnect = true;
                    }
                    last_other_error = Some(e.to_string());
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_grpc_error
            .map(|s| s.to_string())
            .or(last_other_error)
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }

    /// Single attempt at streaming decode.
    ///
    /// Validates that the server returns exactly as many responses as requests sent.
    async fn decode_batch_once(
        &self,
        token_id_batches: &[&[u32]],
        skip_special_tokens: bool,
    ) -> Result<Vec<String>> {
        let mut client = TokenizeClient::new(self.get_channel().await);
        let expected_count = token_id_batches.len();

        // Lazy DecodeRequest creation - clone token IDs for 'static lifetime,
        // then create request objects on-demand as the stream is consumed.
        let owned_ids: Vec<Vec<u32>> = token_id_batches.iter().map(|ids| ids.to_vec()).collect();
        let request_stream = tokio_stream::iter(owned_ids.into_iter().map(move |ids| {
            DecodeRequest {
                ids,
                skip_special_tokens,
            }
        }));
        let response = client.decode_stream(request_stream).await?;

        let mut results = Vec::with_capacity(expected_count);
        let mut stream = response.into_inner();

        use tokio_stream::StreamExt as TokioStreamExt;
        while let Some(resp) = TokioStreamExt::next(&mut stream).await {
            let resp = resp?;
            results.push(resp.text);
        }

        // Validate we received all expected responses
        if results.len() != expected_count {
            return Err(TeiError::PartialResponse {
                expected: expected_count,
                received: results.len(),
            });
        }

        Ok(results)
    }

    /// Rerank texts based on relevance to a query.
    ///
    /// Uses a cross-encoder reranker model to score how relevant each text is
    /// to the query. Results are returned sorted by score (highest first).
    ///
    /// # Arguments
    ///
    /// * `query` - The query text to compare against.
    /// * `texts` - Slice of texts to rerank.
    /// * `truncate` - Whether to truncate texts exceeding max length.
    /// * `return_text` - Whether to include the original text in results.
    ///
    /// # Returns
    ///
    /// Vector of `RerankResult` sorted by score descending.
    ///
    /// # Errors
    ///
    /// * `TeiError::ClientClosed` - If `close()` has been called.
    /// * `TeiError::Config` - If query is empty.
    /// * `TeiError::Grpc` - If the gRPC call fails.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use brrr::embedding::TeiClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///     let client = TeiClient::new("http://localhost:18080").await?;
    ///     let texts = vec![
    ///         "Rust is a systems programming language".to_string(),
    ///         "Python is great for machine learning".to_string(),
    ///         "The weather is nice today".to_string(),
    ///     ];
    ///     let results = client.rerank("programming languages", &texts, true, false).await?;
    ///     for result in results {
    ///         println!("Index: {}, Score: {:.4}", result.index, result.score);
    ///     }
    ///     Ok(())
    /// }
    /// ```
    pub async fn rerank(
        &self,
        query: &str,
        texts: &[String],
        truncate: bool,
        return_text: bool,
    ) -> Result<Vec<RerankResult>> {
        self.ensure_not_closed()?;

        // Handle empty inputs
        if texts.is_empty() {
            return Ok(Vec::new());
        }

        // Validate query
        if query.is_empty() {
            return Err(TeiError::Config("query cannot be empty".to_string()));
        }

        let request = RerankRequest {
            query: query.to_string(),
            texts: texts.to_vec(),
            truncate,
            raw_scores: false, // Return normalized scores by default
            return_text,
            truncation_direction: TruncationDirection::Right.into(),
        };

        // Use with_retry_reconnect to get fresh channel on each attempt.
        // This ensures reconnected channels are used after channel errors.
        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = RerankClient::new(channel);
                    client.rerank(req).await
                }
            })
            .await?;

        let inner = response.into_inner();

        // Map ranks to RerankResult, preserving order from server (should be sorted by score desc)
        let results: Vec<RerankResult> = inner
            .ranks
            .into_iter()
            .map(|rank| RerankResult {
                index: rank.index as usize,
                score: rank.score,
                text: rank.text,
            })
            .collect();

        Ok(results)
    }

    /// Rerank texts with custom options.
    ///
    /// Extended version with full control over reranking behavior.
    ///
    /// # Arguments
    ///
    /// * `query` - The query text to compare against.
    /// * `texts` - Slice of texts to rerank.
    /// * `truncate` - Whether to truncate texts exceeding max length.
    /// * `return_text` - Whether to include the original text in results.
    /// * `raw_scores` - If true, return raw logits instead of normalized probabilities.
    ///
    /// # Returns
    ///
    /// Vector of `RerankResult` sorted by score descending.
    ///
    /// # Errors
    ///
    /// Returns `TeiError::ClientClosed` if `close()` has been called.
    pub async fn rerank_with_options(
        &self,
        query: &str,
        texts: &[String],
        truncate: bool,
        return_text: bool,
        raw_scores: bool,
    ) -> Result<Vec<RerankResult>> {
        self.ensure_not_closed()?;

        if texts.is_empty() {
            return Ok(Vec::new());
        }

        if query.is_empty() {
            return Err(TeiError::Config("query cannot be empty".to_string()));
        }

        let request = RerankRequest {
            query: query.to_string(),
            texts: texts.to_vec(),
            truncate,
            raw_scores,
            return_text,
            truncation_direction: TruncationDirection::Right.into(),
        };

        // Use with_retry_reconnect to get fresh channel on each attempt.
        // This ensures reconnected channels are used after channel errors.
        let response = self
            .with_retry_reconnect(|channel| {
                let req = request.clone();
                async move {
                    let mut client = RerankClient::new(channel);
                    client.rerank(req).await
                }
            })
            .await?;

        let inner = response.into_inner();

        let results: Vec<RerankResult> = inner
            .ranks
            .into_iter()
            .map(|rank| RerankResult {
                index: rank.index as usize,
                score: rank.score,
                text: rank.text,
            })
            .collect();

        Ok(results)
    }

    /// Check if the TEI server is available.
    pub async fn is_available(&self) -> bool {
        self.info().await.is_ok()
    }

    /// Get cached server info, fetching if not cached.
    ///
    /// Uses `OnceCell` for exactly-once initialization, ensuring that even under
    /// high concurrency (multiple concurrent `embed_batch()` calls), only one
    /// `info()` request is made to the server. Other callers will await the
    /// result of that single request.
    async fn get_cached_server_info(&self) -> Result<ServerInfo> {
        self.server_info
            .get_or_try_init(|| self.info())
            .await
            .cloned()
    }

    /// Get or initialize the request semaphore based on server's max_concurrent_requests.
    ///
    /// The semaphore is initialized lazily because we need to know the server's
    /// concurrency limit, which requires an info() call. This ensures we don't
    /// overwhelm the TEI server with too many parallel requests.
    async fn get_request_semaphore(&self) -> Result<&Semaphore> {
        // First ensure server_info is cached
        let server_info = self.get_cached_server_info().await?;

        // Initialize semaphore based on server's max_concurrent_requests
        // Use a reasonable default if the server reports 0
        let permits = (server_info.max_concurrent_requests as usize).max(1);

        self.request_semaphore
            .get_or_init(|| async { Semaphore::new(permits) })
            .await;

        // Safe to unwrap because we just initialized it
        Ok(self.request_semaphore.get().unwrap())
    }

    /// Execute an async operation with exponential backoff retry and reconnection.
    ///
    /// On channel errors (Unavailable, Unknown, Internal, Aborted), triggers
    /// a reconnection before the next retry attempt.
    async fn with_retry<F, Fut, T>(&self, operation: F) -> Result<T>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = std::result::Result<T, tonic::Status>>,
    {
        let mut attempt = 0;
        let mut last_error: Option<tonic::Status> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Reconnect if previous attempt detected a channel error
            if should_reconnect {
                // Attempt reconnection; if it fails, still try the operation
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            match operation().await {
                Ok(result) => return Ok(result),
                Err(status) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_error = Some(status);
                        }
                    }
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_error
            .map(|s| s.to_string())
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }

    /// Execute an async operation with retry and automatic channel reconnection.
    ///
    /// Unlike `with_retry`, this method creates a fresh gRPC client from the
    /// current channel on each attempt. This ensures reconnected channels are
    /// used after channel errors.
    ///
    /// # Type Parameters
    ///
    /// * `F` - Factory function that takes a Channel and returns a Future
    /// * `T` - Return type of the operation
    async fn with_retry_reconnect<F, Fut, T>(&self, operation: F) -> Result<T>
    where
        F: Fn(Channel) -> Fut,
        Fut: std::future::Future<Output = std::result::Result<T, tonic::Status>>,
    {
        let mut attempt = 0;
        let mut last_error: Option<tonic::Status> = None;
        let mut should_reconnect = false;

        while attempt < self.config.max_attempts {
            // Check closed state at start of each attempt to handle race with close()
            if self.is_closed() {
                return Err(TeiError::ClientClosed);
            }

            // Reconnect if previous attempt detected a channel error
            if should_reconnect {
                let _ = self.reconnect().await;
                should_reconnect = false;
            }

            // Get fresh channel for each attempt (may be newly reconnected)
            let channel = self.get_channel().await;

            match operation(channel).await {
                Ok(result) => return Ok(result),
                Err(status) => {
                    match classify_grpc_code(status.code()) {
                        RetryAction::FailImmediately => {
                            return Err(TeiError::Grpc(status));
                        }
                        RetryAction::ReconnectAndRetry => {
                            should_reconnect = true;
                            last_error = Some(status);
                        }
                        RetryAction::Retry => {
                            last_error = Some(status);
                        }
                    }
                }
            }

            attempt += 1;

            if attempt < self.config.max_attempts {
                let backoff = calculate_backoff_with_jitter(
                    self.config.retry_base_delay_ms,
                    self.config.retry_max_delay_ms,
                    attempt,
                );
                tokio::time::sleep(backoff).await;
            }
        }

        // Convert to string only once at the end
        let error_msg = last_error
            .map(|s| s.to_string())
            .unwrap_or_else(|| "Unknown error".into());
        Err(TeiError::RetryExhausted(error_msg))
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_default() {
        let config = TeiClientConfig::default();
        assert_eq!(config.endpoint, "http://localhost:18080");
        assert_eq!(config.timeout_secs, 120);
        assert_eq!(config.max_attempts, 3);
    }

    #[test]
    fn test_max_attempts_semantics() {
        // Verify that max_attempts means total attempts, not retries after initial.
        // This test documents the intended behavior.
        let config = TeiClientConfig {
            max_attempts: 3,
            ..Default::default()
        };

        // max_attempts: 3 means:
        // - Attempt 0: initial try
        // - Attempt 1: first retry (if initial failed)
        // - Attempt 2: second retry (if first retry failed)
        // Total: 3 attempts maximum, which equals 2 retries after initial failure
        assert_eq!(config.max_attempts, 3);

        // Verify retry_count() helper method returns correct value
        assert_eq!(config.retry_count(), 2);

        // Edge case: max_attempts = 1 means no retries
        let no_retry_config = TeiClientConfig {
            max_attempts: 1,
            ..Default::default()
        };
        assert_eq!(no_retry_config.retry_count(), 0);

        // Edge case: max_attempts = 0 means no attempts at all (disabled)
        let disabled_config = TeiClientConfig {
            max_attempts: 0,
            ..Default::default()
        };
        assert_eq!(disabled_config.retry_count(), 0);
    }

    #[test]
    fn test_model_type_from_i32() {
        assert_eq!(ModelType::from(0), ModelType::Embedding);
        assert_eq!(ModelType::from(1), ModelType::Classifier);
        assert_eq!(ModelType::from(2), ModelType::Reranker);
        assert_eq!(ModelType::from(99), ModelType::Unknown);
    }

    #[test]
    fn test_model_type_display() {
        assert_eq!(ModelType::Embedding.to_string(), "embedding");
        assert_eq!(ModelType::Classifier.to_string(), "classifier");
        assert_eq!(ModelType::Reranker.to_string(), "reranker");
        assert_eq!(ModelType::Unknown.to_string(), "unknown");
    }

    #[test]
    fn test_server_info_is_fp16() {
        let info = ServerInfo {
            version: "1.0.0".to_string(),
            sha: None,
            docker_label: None,
            model_id: "test-model".to_string(),
            model_sha: None,
            model_dtype: "float16".to_string(),
            model_type: ModelType::Embedding,
            max_concurrent_requests: 100,
            max_input_length: 512,
            max_batch_tokens: 16384,
            max_batch_requests: Some(32),
            max_client_batch_size: 32,
            tokenization_workers: 4,
        };
        assert!(info.is_fp16());
        assert!(!info.is_bf16());

        let info_f32 = ServerInfo {
            model_dtype: "float32".to_string(),
            ..info.clone()
        };
        assert!(!info_f32.is_fp16());

        let info_half = ServerInfo {
            model_dtype: "half".to_string(),
            ..info.clone()
        };
        assert!(info_half.is_fp16());
    }

    #[test]
    fn test_server_info_is_bf16() {
        let info = ServerInfo {
            version: "1.0.0".to_string(),
            sha: None,
            docker_label: None,
            model_id: "test-model".to_string(),
            model_sha: None,
            model_dtype: "bfloat16".to_string(),
            model_type: ModelType::Embedding,
            max_concurrent_requests: 100,
            max_input_length: 512,
            max_batch_tokens: 16384,
            max_batch_requests: None,
            max_client_batch_size: 32,
            tokenization_workers: 4,
        };
        assert!(info.is_bf16());
        assert!(!info.is_fp16());
    }

    #[test]
    fn test_server_info_description() {
        let info = ServerInfo {
            version: "1.2.3".to_string(),
            sha: Some("abc123".to_string()),
            docker_label: None,
            model_id: "BAAI/bge-large-en-v1.5".to_string(),
            model_sha: None,
            model_dtype: "float16".to_string(),
            model_type: ModelType::Embedding,
            max_concurrent_requests: 100,
            max_input_length: 512,
            max_batch_tokens: 16384,
            max_batch_requests: Some(32),
            max_client_batch_size: 32,
            tokenization_workers: 4,
        };
        let desc = info.description();
        assert!(desc.contains("BAAI/bge-large-en-v1.5"));
        assert!(desc.contains("1.2.3"));
        assert!(desc.contains("float16"));
        assert!(desc.contains("embedding"));
    }

    #[test]
    fn test_server_info_effective_batch_size() {
        // With max_batch_requests set
        let info = ServerInfo {
            version: "1.0.0".to_string(),
            sha: None,
            docker_label: None,
            model_id: "test".to_string(),
            model_sha: None,
            model_dtype: "float32".to_string(),
            model_type: ModelType::Embedding,
            max_concurrent_requests: 100,
            max_input_length: 512,
            max_batch_tokens: 16384,
            max_batch_requests: Some(16),
            max_client_batch_size: 32,
            tokenization_workers: 4,
        };
        assert_eq!(info.effective_batch_size(), 16); // min(32, 16)

        // Without max_batch_requests
        let info_no_limit = ServerInfo {
            max_batch_requests: None,
            ..info.clone()
        };
        assert_eq!(info_no_limit.effective_batch_size(), 32); // just max_client_batch_size
    }

    #[test]
    fn test_server_info_serde() {
        let info = ServerInfo {
            version: "1.0.0".to_string(),
            sha: Some("abc123".to_string()),
            docker_label: None,
            model_id: "test-model".to_string(),
            model_sha: Some("def456".to_string()),
            model_dtype: "float16".to_string(),
            model_type: ModelType::Embedding,
            max_concurrent_requests: 100,
            max_input_length: 512,
            max_batch_tokens: 16384,
            max_batch_requests: Some(32),
            max_client_batch_size: 32,
            tokenization_workers: 4,
        };

        // Test serialization roundtrip
        let json = serde_json::to_string(&info).expect("serialize");
        let deserialized: ServerInfo = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.version, info.version);
        assert_eq!(deserialized.sha, info.sha);
        assert_eq!(deserialized.model_id, info.model_id);
        assert_eq!(deserialized.model_dtype, info.model_dtype);
        assert_eq!(deserialized.model_type, info.model_type);
        assert_eq!(
            deserialized.max_concurrent_requests,
            info.max_concurrent_requests
        );
    }

    #[test]
    fn test_build_token_batches_simple() {
        let texts = vec!["a", "b", "c", "d"];
        let token_counts = vec![100, 100, 100, 100];

        // With budget of 250, should get batches of 2
        let batches = TeiClient::build_token_batches(&texts, &token_counts, 250, 100);
        assert_eq!(batches.len(), 2);
        assert_eq!(batches[0], vec!["a", "b"]);
        assert_eq!(batches[1], vec!["c", "d"]);
    }

    #[test]
    fn test_build_token_batches_max_size() {
        let texts = vec!["a", "b", "c", "d", "e"];
        let token_counts = vec![10, 10, 10, 10, 10];

        // With large budget but max_batch of 2
        let batches = TeiClient::build_token_batches(&texts, &token_counts, 10000, 2);
        assert_eq!(batches.len(), 3);
        assert_eq!(batches[0], vec!["a", "b"]);
        assert_eq!(batches[1], vec!["c", "d"]);
        assert_eq!(batches[2], vec!["e"]);
    }

    #[test]
    fn test_build_token_batches_empty() {
        let texts: Vec<&str> = vec![];
        let token_counts: Vec<usize> = vec![];

        let batches = TeiClient::build_token_batches(&texts, &token_counts, 1000, 10);
        assert!(batches.is_empty());
    }

    #[test]
    fn test_build_token_batches_single_large() {
        let texts = vec!["large"];
        let token_counts = vec![5000];

        // Single text exceeding budget should still be in its own batch
        let batches = TeiClient::build_token_batches(&texts, &token_counts, 1000, 10);
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0], vec!["large"]);
    }

    // Note: decode() tests require a running TEI server, so they are marked as integration tests.
    // The following tests verify the request construction logic without network calls.

    #[test]
    fn test_decode_request_construction() {
        // Verify DecodeRequest can be constructed correctly
        let token_ids: Vec<u32> = vec![101, 7592, 2088, 102];
        let request = super::tei_proto::DecodeRequest {
            ids: token_ids.clone(),
            skip_special_tokens: false,
        };
        assert_eq!(request.ids, token_ids);
        assert!(!request.skip_special_tokens);

        let request_with_skip = super::tei_proto::DecodeRequest {
            ids: token_ids.clone(),
            skip_special_tokens: true,
        };
        assert!(request_with_skip.skip_special_tokens);
    }

    #[test]
    fn test_decode_request_empty_ids() {
        // Verify empty token IDs are handled
        let request = super::tei_proto::DecodeRequest {
            ids: Vec::new(),
            skip_special_tokens: false,
        };
        assert!(request.ids.is_empty());
    }

    // Note: rerank() tests require a running TEI reranker server.
    // The following tests verify the request construction logic without network calls.

    #[test]
    fn test_rerank_request_construction() {
        // Verify RerankRequest can be constructed correctly
        let query = "programming languages".to_string();
        let texts = vec!["Rust is fast".to_string(), "Python is easy".to_string()];

        let request = super::tei_proto::RerankRequest {
            query: query.clone(),
            texts: texts.clone(),
            truncate: true,
            raw_scores: false,
            return_text: true,
            truncation_direction: TruncationDirection::Right.into(),
        };

        assert_eq!(request.query, query);
        assert_eq!(request.texts, texts);
        assert!(request.truncate);
        assert!(!request.raw_scores);
        assert!(request.return_text);
    }

    #[test]
    fn test_rerank_request_with_raw_scores() {
        let request = super::tei_proto::RerankRequest {
            query: "test query".to_string(),
            texts: vec!["text1".to_string()],
            truncate: false,
            raw_scores: true,
            return_text: false,
            truncation_direction: TruncationDirection::Left.into(),
        };

        assert!(!request.truncate);
        assert!(request.raw_scores);
        assert!(!request.return_text);
    }

    #[test]
    fn test_rerank_result_struct() {
        // Verify RerankResult can be constructed and accessed
        let result = RerankResult {
            index: 5,
            score: 0.95,
            text: Some("sample text".to_string()),
        };

        assert_eq!(result.index, 5);
        assert!((result.score - 0.95).abs() < f32::EPSILON);
        assert_eq!(result.text, Some("sample text".to_string()));

        // Test without text
        let result_no_text = RerankResult {
            index: 0,
            score: 0.5,
            text: None,
        };
        assert!(result_no_text.text.is_none());
    }

    #[test]
    fn test_rerank_result_clone() {
        let original = RerankResult {
            index: 10,
            score: 0.8,
            text: Some("cloneable".to_string()),
        };

        let cloned = original.clone();
        assert_eq!(cloned.index, original.index);
        assert_eq!(cloned.score, original.score);
        assert_eq!(cloned.text, original.text);
    }

    // Note: embed_single() tests require a running TEI server.
    // The following tests verify the EmbedMetadata struct without network calls.

    #[test]
    fn test_embed_metadata_default() {
        // Verify EmbedMetadata can be default-constructed
        let meta = EmbedMetadata::default();
        assert_eq!(meta.compute_chars, 0);
        assert_eq!(meta.compute_tokens, 0);
        assert_eq!(meta.total_time_ns, 0);
        assert_eq!(meta.tokenization_time_ns, 0);
        assert_eq!(meta.queue_time_ns, 0);
        assert_eq!(meta.inference_time_ns, 0);
    }

    #[test]
    fn test_embed_metadata_construction() {
        // Verify EmbedMetadata can be constructed with values
        let meta = EmbedMetadata {
            compute_chars: 100,
            compute_tokens: 25,
            total_time_ns: 50_000_000,
            tokenization_time_ns: 5_000_000,
            queue_time_ns: 1_000_000,
            inference_time_ns: 44_000_000,
        };

        assert_eq!(meta.compute_chars, 100);
        assert_eq!(meta.compute_tokens, 25);
        assert_eq!(meta.total_time_ns, 50_000_000);
        assert_eq!(meta.tokenization_time_ns, 5_000_000);
        assert_eq!(meta.queue_time_ns, 1_000_000);
        assert_eq!(meta.inference_time_ns, 44_000_000);
    }

    #[test]
    fn test_embed_metadata_clone() {
        let original = EmbedMetadata {
            compute_chars: 42,
            compute_tokens: 10,
            total_time_ns: 100_000,
            tokenization_time_ns: 10_000,
            queue_time_ns: 5_000,
            inference_time_ns: 85_000,
        };

        let cloned = original.clone();
        assert_eq!(cloned.compute_chars, original.compute_chars);
        assert_eq!(cloned.compute_tokens, original.compute_tokens);
        assert_eq!(cloned.total_time_ns, original.total_time_ns);
        assert_eq!(cloned.tokenization_time_ns, original.tokenization_time_ns);
        assert_eq!(cloned.queue_time_ns, original.queue_time_ns);
        assert_eq!(cloned.inference_time_ns, original.inference_time_ns);
    }

    // Tests for stream response validation error types

    #[test]
    fn test_partial_response_error_construction() {
        let err = TeiError::PartialResponse {
            expected: 10,
            received: 7,
        };

        let msg = err.to_string();
        assert!(msg.contains("10"));
        assert!(msg.contains("7"));
        assert!(msg.contains("expected"));
        assert!(msg.contains("received"));
    }

    #[test]
    fn test_partial_response_error_debug() {
        let err = TeiError::PartialResponse {
            expected: 100,
            received: 0,
        };

        let debug = format!("{:?}", err);
        assert!(debug.contains("PartialResponse"));
        assert!(debug.contains("100"));
        assert!(debug.contains("0"));
    }

    #[test]
    fn test_empty_embedding_error_construction() {
        let err = TeiError::EmptyEmbedding { index: 5 };

        let msg = err.to_string();
        assert!(msg.contains("5"));
        // Error message uses "Empty" (capitalized) at the start
        assert!(msg.to_lowercase().contains("empty"));
        assert!(msg.contains("index"));
    }

    #[test]
    fn test_empty_embedding_error_debug() {
        let err = TeiError::EmptyEmbedding { index: 42 };

        let debug = format!("{:?}", err);
        assert!(debug.contains("EmptyEmbedding"));
        assert!(debug.contains("42"));
    }

    #[test]
    fn test_dimension_mismatch_error_construction() {
        let err = TeiError::DimensionMismatch {
            expected: 768,
            actual: 512,
            index: 3,
        };

        let msg = err.to_string();
        assert!(msg.contains("768"), "Should contain expected dimension");
        assert!(msg.contains("512"), "Should contain actual dimension");
        assert!(msg.contains("3"), "Should contain index");
        assert!(
            msg.to_lowercase().contains("mismatch"),
            "Should indicate mismatch"
        );
    }

    #[test]
    fn test_dimension_mismatch_error_debug() {
        let err = TeiError::DimensionMismatch {
            expected: 1024,
            actual: 256,
            index: 7,
        };

        let debug = format!("{:?}", err);
        assert!(debug.contains("DimensionMismatch"));
        assert!(debug.contains("1024"));
        assert!(debug.contains("256"));
        assert!(debug.contains("7"));
    }

    #[test]
    fn test_dimension_mismatch_error_clone() {
        let original = TeiError::DimensionMismatch {
            expected: 384,
            actual: 768,
            index: 0,
        };

        // Verify Debug trait is implemented (required for error types)
        let debug = format!("{:?}", original);
        assert!(debug.contains("DimensionMismatch"));
    }

    #[test]
    fn test_error_is_send_sync() {
        // Ensure TeiError can be sent across threads (important for async code)
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}

        assert_send::<TeiError>();
        assert_sync::<TeiError>();
    }

    #[test]
    fn test_backoff_with_jitter_produces_random_values() {
        // Verify that jitter is truly random by checking that multiple calls
        // produce different values (statistically very likely with random jitter)
        let base_delay = 100u64;
        let max_delay = 5000u64;
        let attempt = 2u32;

        let mut results: Vec<Duration> = Vec::new();
        for _ in 0..10 {
            results.push(calculate_backoff_with_jitter(
                base_delay, max_delay, attempt,
            ));
        }

        // With true random jitter, we expect at least some variation
        // The probability of all 10 being identical is essentially zero
        let first = results[0];
        let has_variation = results.iter().any(|d| *d != first);

        // Even if by extreme chance all are the same, the test should pass
        // as long as values are within expected range
        let expected_base = base_delay * (1 << attempt); // 100 * 4 = 400ms
        let max_with_jitter = expected_base + (expected_base / 4); // 400 + 100 = 500ms

        for duration in &results {
            let ms = duration.as_millis() as u64;
            assert!(
                ms >= expected_base,
                "Backoff should be at least {expected_base}ms, got {ms}ms"
            );
            assert!(
                ms <= max_with_jitter,
                "Backoff should be at most {max_with_jitter}ms, got {ms}ms"
            );
        }

        // Log whether variation was found (for debugging, not a hard failure)
        if !has_variation {
            eprintln!("Warning: No variation found in 10 jitter samples - extremely unlikely but possible");
        }
    }

    #[test]
    fn test_backoff_exponential_growth() {
        let base_delay = 100u64;
        let max_delay = 10000u64;

        // Test exponential growth pattern
        let backoff_1 = calculate_backoff_with_jitter(base_delay, max_delay, 1);
        let backoff_2 = calculate_backoff_with_jitter(base_delay, max_delay, 2);
        let backoff_3 = calculate_backoff_with_jitter(base_delay, max_delay, 3);

        // Attempt 1: base * 2^1 = 200ms (+ 0-50ms jitter)
        // Attempt 2: base * 2^2 = 400ms (+ 0-100ms jitter)
        // Attempt 3: base * 2^3 = 800ms (+ 0-200ms jitter)
        assert!(backoff_1.as_millis() >= 200, "Attempt 1 should be >= 200ms");
        assert!(backoff_1.as_millis() <= 250, "Attempt 1 should be <= 250ms");

        assert!(backoff_2.as_millis() >= 400, "Attempt 2 should be >= 400ms");
        assert!(backoff_2.as_millis() <= 500, "Attempt 2 should be <= 500ms");

        assert!(backoff_3.as_millis() >= 800, "Attempt 3 should be >= 800ms");
        assert!(
            backoff_3.as_millis() <= 1000,
            "Attempt 3 should be <= 1000ms"
        );
    }

    #[test]
    fn test_backoff_respects_max_delay() {
        let base_delay = 1000u64;
        let max_delay = 2000u64;

        // High attempt number should be capped at max_delay
        let backoff = calculate_backoff_with_jitter(base_delay, max_delay, 10);

        // Should be capped at max_delay (2000ms) + 25% jitter (500ms) = 2500ms max
        assert!(
            backoff.as_millis() <= 2500,
            "Backoff should be capped at max_delay + jitter"
        );
        assert!(
            backoff.as_millis() >= 2000,
            "Backoff should be at least max_delay"
        );
    }

    #[test]
    fn test_backoff_handles_zero_base_delay() {
        let backoff = calculate_backoff_with_jitter(0, 5000, 5);

        // With 0 base delay, result should be 0
        assert_eq!(backoff.as_millis(), 0);
    }

    // =========================================================================
    // Sparse Embedding Tests
    // =========================================================================

    #[test]
    fn test_sparse_value_construction() {
        let sv = SparseValue {
            index: 1234,
            value: 0.567,
        };
        assert_eq!(sv.index, 1234);
        assert!((sv.value - 0.567).abs() < f32::EPSILON);
    }

    #[test]
    fn test_sparse_value_equality() {
        let sv1 = SparseValue {
            index: 100,
            value: 0.5,
        };
        let sv2 = SparseValue {
            index: 100,
            value: 0.5,
        };
        let sv3 = SparseValue {
            index: 101,
            value: 0.5,
        };
        let sv4 = SparseValue {
            index: 100,
            value: 0.6,
        };

        assert_eq!(sv1, sv2);
        assert_ne!(sv1, sv3);
        assert_ne!(sv1, sv4);
    }

    #[test]
    fn test_sparse_value_clone() {
        let original = SparseValue {
            index: 42,
            value: 0.99,
        };
        let cloned = original.clone();
        assert_eq!(original, cloned);
    }

    #[test]
    fn test_sparse_embedding_empty() {
        let emb = SparseEmbedding { values: vec![] };
        assert!(emb.is_empty());
        assert_eq!(emb.len(), 0);
    }

    #[test]
    fn test_sparse_embedding_with_values() {
        let emb = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 1,
                    value: 0.5,
                },
                SparseValue {
                    index: 5,
                    value: 0.3,
                },
                SparseValue {
                    index: 10,
                    value: 0.8,
                },
            ],
        };
        assert!(!emb.is_empty());
        assert_eq!(emb.len(), 3);
    }

    #[test]
    fn test_sparse_embedding_dot_product_identical() {
        let emb = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 1,
                    value: 2.0,
                },
                SparseValue {
                    index: 3,
                    value: 3.0,
                },
                SparseValue {
                    index: 5,
                    value: 4.0,
                },
            ],
        };

        // Dot product with itself: 2^2 + 3^2 + 4^2 = 4 + 9 + 16 = 29
        let dot = emb.dot(&emb);
        assert!((dot - 29.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_sparse_embedding_dot_product_orthogonal() {
        // Two vectors with no overlapping indices
        let emb1 = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 1,
                    value: 1.0,
                },
                SparseValue {
                    index: 3,
                    value: 1.0,
                },
            ],
        };
        let emb2 = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 2,
                    value: 1.0,
                },
                SparseValue {
                    index: 4,
                    value: 1.0,
                },
            ],
        };

        // No overlap = 0 dot product
        let dot = emb1.dot(&emb2);
        assert!((dot - 0.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_sparse_embedding_dot_product_partial_overlap() {
        let emb1 = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 1,
                    value: 2.0,
                },
                SparseValue {
                    index: 3,
                    value: 3.0,
                },
                SparseValue {
                    index: 5,
                    value: 4.0,
                },
            ],
        };
        let emb2 = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 2,
                    value: 1.0,
                },
                SparseValue {
                    index: 3,
                    value: 2.0,
                },
                SparseValue {
                    index: 5,
                    value: 1.5,
                },
            ],
        };

        // Only indices 3 and 5 overlap: 3*2 + 4*1.5 = 6 + 6 = 12
        let dot = emb1.dot(&emb2);
        assert!((dot - 12.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_sparse_embedding_dot_product_empty() {
        let emb1 = SparseEmbedding { values: vec![] };
        let emb2 = SparseEmbedding {
            values: vec![SparseValue {
                index: 1,
                value: 1.0,
            }],
        };

        assert!((emb1.dot(&emb2) - 0.0).abs() < f32::EPSILON);
        assert!((emb2.dot(&emb1) - 0.0).abs() < f32::EPSILON);
    }

    #[test]
    fn test_sparse_embedding_sort_by_index() {
        let mut emb = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 10,
                    value: 0.1,
                },
                SparseValue {
                    index: 2,
                    value: 0.2,
                },
                SparseValue {
                    index: 5,
                    value: 0.5,
                },
            ],
        };

        emb.sort_by_index();

        assert_eq!(emb.values[0].index, 2);
        assert_eq!(emb.values[1].index, 5);
        assert_eq!(emb.values[2].index, 10);
    }

    #[test]
    fn test_sparse_embedding_clone() {
        let original = SparseEmbedding {
            values: vec![
                SparseValue {
                    index: 1,
                    value: 0.5,
                },
                SparseValue {
                    index: 2,
                    value: 0.7,
                },
            ],
        };
        let cloned = original.clone();

        assert_eq!(original.len(), cloned.len());
        for (orig, cln) in original.values.iter().zip(cloned.values.iter()) {
            assert_eq!(orig, cln);
        }
    }

    #[test]
    fn test_embed_sparse_request_construction() {
        // Verify EmbedSparseRequest can be constructed correctly
        let request = super::tei_proto::EmbedSparseRequest {
            inputs: "test input".to_string(),
            truncate: true,
            truncation_direction: TruncationDirection::Right.into(),
            prompt_name: None,
        };

        assert_eq!(request.inputs, "test input");
        assert!(request.truncate);
        assert!(request.prompt_name.is_none());
    }

    #[test]
    fn test_embed_sparse_request_with_prompt_name() {
        let request = super::tei_proto::EmbedSparseRequest {
            inputs: "document text".to_string(),
            truncate: false,
            truncation_direction: TruncationDirection::Left.into(),
            prompt_name: Some("passage".to_string()),
        };

        assert_eq!(request.inputs, "document text");
        assert!(!request.truncate);
        assert_eq!(request.prompt_name, Some("passage".to_string()));
    }

    #[test]
    fn test_sparse_embedding_is_send_sync() {
        // Ensure SparseEmbedding can be sent across threads
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}

        assert_send::<SparseEmbedding>();
        assert_sync::<SparseEmbedding>();
        assert_send::<SparseValue>();
        assert_sync::<SparseValue>();
    }

    #[test]
    fn test_sparse_embedding_debug() {
        let emb = SparseEmbedding {
            values: vec![SparseValue {
                index: 42,
                value: 0.123,
            }],
        };

        let debug = format!("{:?}", emb);
        assert!(debug.contains("SparseEmbedding"));
        assert!(debug.contains("42"));
    }

    // =========================================================================
    // Client Lifecycle Tests
    // =========================================================================

    #[test]
    fn test_client_closed_error_construction() {
        let err = TeiError::ClientClosed;
        let msg = err.to_string();
        assert!(msg.to_lowercase().contains("closed"));
    }

    #[test]
    fn test_client_closed_error_debug() {
        let err = TeiError::ClientClosed;
        let debug = format!("{:?}", err);
        assert!(debug.contains("ClientClosed"));
    }

    #[tokio::test]
    async fn test_client_is_closed_initially_false() {
        // Create client with a dummy endpoint (won't connect since we use connect_lazy semantics)
        let config = TeiClientConfig {
            endpoint: "http://localhost:1".to_string(),
            ..Default::default()
        };

        // Create a lazy channel that doesn't require an actual server
        let channel = Channel::from_static("http://[::1]:1").connect_lazy();

        let client = TeiClient {
            config,
            channel: RwLock::new(channel),
            server_info: OnceCell::const_new(),
            request_semaphore: OnceCell::const_new(),
            closed: AtomicBool::new(false),
        };

        assert!(!client.is_closed());
    }

    #[tokio::test]
    async fn test_client_close_sets_closed_flag() {
        let config = TeiClientConfig {
            endpoint: "http://localhost:1".to_string(),
            ..Default::default()
        };

        let channel = Channel::from_static("http://[::1]:1").connect_lazy();

        let client = TeiClient {
            config,
            channel: RwLock::new(channel),
            server_info: OnceCell::const_new(),
            request_semaphore: OnceCell::const_new(),
            closed: AtomicBool::new(false),
        };

        assert!(!client.is_closed());

        // Close the client
        let result = client.close().await;
        assert!(result.is_ok());
        assert!(client.is_closed());
    }

    #[tokio::test]
    async fn test_client_close_is_idempotent() {
        let config = TeiClientConfig {
            endpoint: "http://localhost:1".to_string(),
            ..Default::default()
        };

        let channel = Channel::from_static("http://[::1]:1").connect_lazy();

        let client = TeiClient {
            config,
            channel: RwLock::new(channel),
            server_info: OnceCell::const_new(),
            request_semaphore: OnceCell::const_new(),
            closed: AtomicBool::new(false),
        };

        // Close multiple times
        let result1 = client.close().await;
        let result2 = client.close().await;
        let result3 = client.close().await;

        // All should succeed
        assert!(result1.is_ok());
        assert!(result2.is_ok());
        assert!(result3.is_ok());
        assert!(client.is_closed());
    }

    #[tokio::test]
    async fn test_ensure_not_closed_returns_error_when_closed() {
        let config = TeiClientConfig {
            endpoint: "http://localhost:1".to_string(),
            ..Default::default()
        };

        let channel = Channel::from_static("http://[::1]:1").connect_lazy();

        let client = TeiClient {
            config,
            channel: RwLock::new(channel),
            server_info: OnceCell::const_new(),
            request_semaphore: OnceCell::const_new(),
            closed: AtomicBool::new(false),
        };

        // Before close, should be Ok
        assert!(client.ensure_not_closed().is_ok());

        // Close the client
        client.close().await.unwrap();

        // After close, should return ClientClosed error
        let result = client.ensure_not_closed();
        assert!(matches!(result, Err(TeiError::ClientClosed)));
    }

    #[test]
    fn test_tei_client_is_send_sync() {
        // Ensure TeiClient can be sent across threads and shared
        fn assert_send<T: Send>() {}
        fn assert_sync<T: Sync>() {}

        assert_send::<TeiClient>();
        assert_sync::<TeiClient>();
    }
}
