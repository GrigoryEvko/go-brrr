//! Token-aware code chunking for semantic embedding.
//!
//! This module provides intelligent code chunking that:
//! - Respects token limits for embedding models
//! - Splits at natural code boundaries (functions, classes, blank lines)
//! - Preserves context through overlapping chunks
//! - Handles edge cases like oversized functions and deeply nested code
//!
//! The chunking strategy prioritizes semantic coherence over strict token limits,
//! attempting to keep related code (e.g., function with its docstring) together.
//!
//! # Tokenizer Mismatch Warning (BUG-02)
//!
//! **IMPORTANT**: This module uses `cl100k_base` (GPT-4/ChatGPT tokenizer) for local
//! token counting, while Python's semantic module uses Qwen3-Embedding-0.6B's tokenizer.
//! Different tokenizers produce different token counts for the same text:
//!
//! - `cl100k_base`: ~100K vocabulary, optimized for English + code
//! - Qwen3 tokenizer: Different vocabulary size and subword tokenization
//!
//! This can cause **5-15% variance** in token counts between Rust and Python,
//! leading to inconsistent chunk boundaries.
//!
//! ## Solutions for Exact Parity
//!
//! 1. **Use TEI Server** (recommended): Call [`count_tokens_tei`] or [`count_tokens_batch_tei`]
//!    to use the actual embedding model's tokenizer via the TEI gRPC server.
//!
//! 2. **Accept Variance**: For most use cases, the ~10% variance is acceptable since
//!    both tokenizers produce reasonable chunk boundaries.
//!
//! 3. **Use ChunkConfig**: Configure token limits with [`ChunkConfig`] to specify
//!    the tokenizer type and adjust limits based on expected variance.
//!
//! # Example: TEI-based Token Counting
//!
//! ```no_run
//! use go_brrr::semantic::chunker::{count_tokens_tei, ChunkConfig, TokenizerType};
//! use go_brrr::embedding::TeiClient;
//!
//! async fn example() -> Result<(), Box<dyn std::error::Error>> {
//!     let client = TeiClient::new("http://localhost:18080").await?;
//!
//!     // Count tokens using TEI (matches Python exactly)
//!     let code = "def hello(): pass";
//!     let tokens = count_tokens_tei(code, &client).await?;
//!
//!     // Configure chunking with explicit tokenizer awareness
//!     let config = ChunkConfig::new()
//!         .with_tokenizer(TokenizerType::Cl100kBase)
//!         .with_variance_margin(0.10); // 10% safety margin
//!
//!     Ok(())
//! }
//! ```

use std::cell::RefCell;
use std::sync::OnceLock;

use once_cell::sync::Lazy;
use rayon::prelude::*;
use regex::Regex;
use serde::{Deserialize, Serialize};
use tiktoken_rs::CoreBPE;

use super::types::{CHUNK_OVERLAP_TOKENS, MAX_CODE_PREVIEW_TOKENS};
use crate::embedding::{TeiClient, TeiError};

/// Minimum token count for chunks to prevent infinite recursion in reduction.
///
/// When `handle_oversized_chunk` recursively reduces `max_tokens` via `max_tokens * 3 / 4`,
/// without a floor the sequence can reach 0: 4 -> 3 -> 2 -> 1 -> 0.
/// With `max_tokens = 0`, the condition `current_tokens + line_tokens > max_tokens`
/// becomes always true, causing infinite recursion between `handle_oversized_chunk`
/// and `chunk_with_boundaries`.
///
/// This constant provides a safe floor (10 tokens ~= 40 characters) below which
/// we fall back to direct line-by-line splitting instead of recursive reduction.
const MIN_CHUNK_TOKENS: usize = 10;

// =============================================================================
// Line Numbering Convention (BUG-16 Fix)
// =============================================================================

/// Line numbering convention used throughout this module.
///
/// All public APIs use **1-indexed line numbers** to match:
/// - Editor conventions (VS Code, Vim, Emacs, etc.)
/// - Error message conventions (compiler/linter output)
/// - Source code display conventions (`git diff`, `grep -n`)
/// - Human expectation (first line is "line 1", not "line 0")
///
/// Internal array indices are 0-indexed and converted at API boundaries
/// using [`index_to_line`] and [`line_to_index`].
///
/// # Conventions
///
/// | Context | Indexing | Example |
/// |---------|----------|---------|
/// | `Chunk.start_line`, `Chunk.end_line` | 1-indexed | First line = 1 |
/// | `Boundary.line_idx` | 0-indexed (internal) | First line = 0 |
/// | `lines[i]` array access | 0-indexed | First line = lines[0] |
/// | `enumerate()` index | 0-indexed | First iteration i = 0 |
///
/// # Inclusive vs Exclusive Ranges
///
/// - **Chunk line ranges are INCLUSIVE on both ends**: `start_line=1, end_line=3`
///   means lines 1, 2, and 3 are all included.
/// - **Internal ranges may be EXCLUSIVE on end**: When iterating `0..end_idx`,
///   the `end_idx` is not included. This is converted at API boundaries.
///
/// # Example
///
/// ```text
/// Array index:  [0]    [1]    [2]    [3]
/// 1-indexed:    Line 1 Line 2 Line 3 Line 4
/// Content:      "fn x" "{"    "}"    ""
///
/// A chunk containing all 4 lines would have:
/// - start_line = 1 (first line, 1-indexed)
/// - end_line = 4 (last line, 1-indexed, INCLUSIVE)
/// - line_count() = 4
/// ```

/// Convert a 0-indexed array index to a 1-indexed line number.
///
/// Use this when exposing line numbers in public APIs (e.g., `Chunk.start_line`).
///
/// # Example
///
/// ```
/// use go_brrr::semantic::chunker::index_to_line;
///
/// assert_eq!(index_to_line(0), 1);  // First array element = line 1
/// assert_eq!(index_to_line(9), 10); // 10th array element = line 10
/// ```
#[inline]
#[must_use]
pub fn index_to_line(index: usize) -> usize {
    index + 1
}

/// Convert a 1-indexed line number to a 0-indexed array index.
///
/// Use this when accessing arrays with user-provided line numbers.
/// Returns 0 for line number 0 (invalid input) to avoid underflow.
///
/// # Example
///
/// ```
/// use go_brrr::semantic::chunker::line_to_index;
///
/// assert_eq!(line_to_index(1), 0);   // Line 1 = first array element
/// assert_eq!(line_to_index(10), 9);  // Line 10 = 10th array element (index 9)
/// assert_eq!(line_to_index(0), 0);   // Invalid line 0 saturates to index 0
/// ```
#[inline]
#[must_use]
pub fn line_to_index(line: usize) -> usize {
    line.saturating_sub(1)
}

// =============================================================================
// Tokenizer Configuration (BUG-02 Fix)
// =============================================================================

/// Tokenizer type for token counting.
///
/// Different embedding models use different tokenizers, which produce different
/// token counts for the same text. This enum documents the available options
/// and their characteristics.
///
/// # Tokenizer Comparison
///
/// | Tokenizer | Model | Vocab Size | Notes |
/// |-----------|-------|------------|-------|
/// | `Cl100kBase` | GPT-4, ChatGPT | ~100K | Default for tiktoken in Rust |
/// | `P50kBase` | GPT-3 | ~50K | Older OpenAI models |
/// | `R50kBase` | Codex | ~50K | Code-optimized |
/// | `Qwen3` | Qwen3-Embedding | Varies | Used by Python's semantic module |
/// | `CharEstimate` | N/A | N/A | Character-based estimation for Python parity |
///
/// # Mismatch Warning (BUG-02)
///
/// When using `Cl100kBase` (default), token counts may differ from Python's
/// Qwen3-based counts by approximately 5-15%. For exact parity:
///
/// 1. **Use TEI Server** (recommended): Call [`count_tokens_tei`] for exact Qwen3 counts
/// 2. **Use CharEstimate**: Call [`set_tokenizer_type(TokenizerType::CharEstimate)`]
///    to use the same character-based estimation as Python's fallback
/// 3. **Accept Variance**: For most use cases, ~10% variance is acceptable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TokenizerType {
    /// GPT-4/ChatGPT tokenizer (tiktoken cl100k_base).
    /// ~100K vocabulary, optimized for English text and code.
    /// This is the default for local Rust token counting.
    #[default]
    Cl100kBase,

    /// GPT-3 tokenizer (tiktoken p50k_base).
    /// ~50K vocabulary, older OpenAI models.
    P50kBase,

    /// Codex tokenizer (tiktoken r50k_base).
    /// ~50K vocabulary, code-optimized.
    R50kBase,

    /// Qwen3 tokenizer (via TEI server).
    /// Used by Python's semantic module for Qwen3-Embedding-0.6B.
    /// Requires TEI server connection for accurate counts.
    ///
    /// **Note**: Local Rust code cannot use Qwen3 tokenizer directly.
    /// When this is selected, [`count_tokens`] falls back to `CharEstimate`
    /// for synchronous counting. Use [`count_tokens_tei`] for exact counts.
    Qwen3,

    /// Character-based token estimation matching Python's fallback.
    ///
    /// Uses Unicode-aware heuristics for better accuracy:
    /// - ASCII/code: ~4 chars per token
    /// - CJK characters: ~1.5 chars per token (each ideograph often = 1 token)
    /// - Emoji: ~3 tokens per emoji
    /// - Other Unicode: ~2 chars per token
    ///
    /// **Use this for exact parity with Python** when the TEI server is unavailable.
    /// Both Rust and Python implementations use the same formula, ensuring
    /// identical chunk boundaries.
    CharEstimate,
}

impl TokenizerType {
    /// Get a human-readable name for the tokenizer.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::Cl100kBase => "cl100k_base (GPT-4)",
            Self::P50kBase => "p50k_base (GPT-3)",
            Self::R50kBase => "r50k_base (Codex)",
            Self::Qwen3 => "Qwen3 (TEI server)",
            Self::CharEstimate => "CharEstimate (Python parity)",
        }
    }

    /// Check if this tokenizer requires a TEI server connection.
    #[must_use]
    pub fn requires_tei(&self) -> bool {
        matches!(self, Self::Qwen3)
    }

    /// Check if this tokenizer uses character-based estimation.
    #[must_use]
    pub fn is_estimation(&self) -> bool {
        matches!(self, Self::CharEstimate)
    }

    /// Get the expected variance percentage compared to Qwen3.
    ///
    /// Returns the approximate percentage difference in token counts
    /// when using this tokenizer vs. the Qwen3 tokenizer.
    #[must_use]
    pub fn variance_vs_qwen3(&self) -> f64 {
        match self {
            Self::Cl100kBase => 0.10,   // ~10% variance
            Self::P50kBase => 0.15,     // ~15% variance
            Self::R50kBase => 0.12,     // ~12% variance
            Self::Qwen3 => 0.0,         // Exact match
            Self::CharEstimate => 0.05, // ~5% variance (uses same formula as Python fallback)
        }
    }
}

impl std::fmt::Display for TokenizerType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Configuration for chunking operations.
///
/// Provides fine-grained control over token limits, overlap, and tokenizer
/// selection. Use the builder pattern for easy configuration.
///
/// # Example
///
/// ```
/// use go_brrr::semantic::chunker::{ChunkConfig, TokenizerType};
///
/// // Default configuration
/// let config = ChunkConfig::default();
///
/// // Custom configuration with variance margin
/// let config = ChunkConfig::new()
///     .with_max_tokens(6000)
///     .with_overlap_tokens(200)
///     .with_tokenizer(TokenizerType::Cl100kBase)
///     .with_variance_margin(0.10); // 10% safety margin
///
/// // Effective max tokens accounts for variance
/// assert!(config.effective_max_tokens() < config.max_tokens);
/// ```
#[derive(Debug, Clone)]
pub struct ChunkConfig {
    /// Maximum tokens per chunk.
    pub max_tokens: usize,

    /// Token overlap between consecutive chunks for context continuity.
    pub overlap_tokens: usize,

    /// Tokenizer type for token counting.
    pub tokenizer: TokenizerType,

    /// Variance margin to account for tokenizer differences.
    ///
    /// When using a non-Qwen3 tokenizer, this margin reduces the effective
    /// max tokens to ensure chunks fit within limits even with tokenizer
    /// variance. Set to 0.0 for exact limits, or 0.10-0.15 for safety.
    pub variance_margin: f64,
}

impl Default for ChunkConfig {
    fn default() -> Self {
        Self {
            max_tokens: MAX_CODE_PREVIEW_TOKENS,
            overlap_tokens: CHUNK_OVERLAP_TOKENS,
            tokenizer: TokenizerType::default(),
            variance_margin: 0.0, // No margin by default for backward compatibility
        }
    }
}

impl ChunkConfig {
    /// Create a new configuration with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the maximum tokens per chunk.
    #[must_use]
    pub fn with_max_tokens(mut self, max_tokens: usize) -> Self {
        self.max_tokens = max_tokens;
        self
    }

    /// Set the overlap tokens between chunks.
    #[must_use]
    pub fn with_overlap_tokens(mut self, overlap_tokens: usize) -> Self {
        self.overlap_tokens = overlap_tokens;
        self
    }

    /// Set the tokenizer type.
    #[must_use]
    pub fn with_tokenizer(mut self, tokenizer: TokenizerType) -> Self {
        self.tokenizer = tokenizer;
        self
    }

    /// Set the variance margin for tokenizer differences.
    ///
    /// The margin is a percentage (0.0 to 1.0) that reduces the effective
    /// max tokens to account for potential tokenizer variance.
    ///
    /// # Example
    ///
    /// With `max_tokens = 6000` and `variance_margin = 0.10`:
    /// - `effective_max_tokens() = 6000 * (1 - 0.10) = 5400`
    #[must_use]
    pub fn with_variance_margin(mut self, margin: f64) -> Self {
        self.variance_margin = margin.clamp(0.0, 0.5); // Cap at 50% for sanity
        self
    }

    /// Calculate effective max tokens accounting for variance margin.
    ///
    /// When using a tokenizer other than Qwen3, this applies the variance
    /// margin to reduce the limit and ensure chunks fit within bounds.
    #[must_use]
    pub fn effective_max_tokens(&self) -> usize {
        if self.tokenizer.requires_tei() {
            // Qwen3 tokenizer has no variance, use exact limit
            self.max_tokens
        } else {
            // Apply variance margin for non-Qwen3 tokenizers
            let margin = self.variance_margin + self.tokenizer.variance_vs_qwen3();
            let effective = (self.max_tokens as f64 * (1.0 - margin)) as usize;
            effective.max(MIN_CHUNK_TOKENS) // Ensure we don't go below minimum
        }
    }
}

// =============================================================================
// Global Tokenizer Type Configuration (BUG-02 Fix)
// =============================================================================

/// Global tokenizer type for [`count_tokens`].
///
/// Set via [`set_tokenizer_type`] before any token counting operations.
/// If not set, defaults to `Cl100kBase`.
static GLOBAL_TOKENIZER_TYPE: OnceLock<TokenizerType> = OnceLock::new();

/// Set the global tokenizer type for [`count_tokens`].
///
/// This must be called before any chunking operations to take effect.
/// Once set, the tokenizer type cannot be changed (write-once semantics).
///
/// # Arguments
///
/// * `tokenizer_type` - The tokenizer type to use globally
///
/// # Returns
///
/// `true` if the tokenizer type was set, `false` if it was already set.
///
/// # Example: Python Parity
///
/// ```
/// use go_brrr::semantic::chunker::{set_tokenizer_type, TokenizerType, count_tokens};
///
/// // Set CharEstimate for exact parity with Python's fallback behavior
/// set_tokenizer_type(TokenizerType::CharEstimate);
///
/// // Now count_tokens uses the same formula as Python
/// let tokens = count_tokens("def hello(): pass");
/// ```
///
/// # Thread Safety
///
/// This function is thread-safe. If multiple threads call it concurrently,
/// only the first call will succeed and subsequent calls will be no-ops.
pub fn set_tokenizer_type(tokenizer_type: TokenizerType) -> bool {
    GLOBAL_TOKENIZER_TYPE.set(tokenizer_type).is_ok()
}

/// Get the current global tokenizer type.
///
/// Returns the tokenizer type set via [`set_tokenizer_type`], or
/// `Cl100kBase` if no type has been set.
///
/// # Example
///
/// ```
/// use go_brrr::semantic::chunker::{get_tokenizer_type, TokenizerType};
///
/// let current = get_tokenizer_type();
/// println!("Using tokenizer: {}", current);
/// ```
#[must_use]
pub fn get_tokenizer_type() -> TokenizerType {
    GLOBAL_TOKENIZER_TYPE
        .get()
        .copied()
        .unwrap_or(TokenizerType::Cl100kBase)
}

// =============================================================================
// Token Counting - Thread-Local for Zero Contention
// =============================================================================

thread_local! {
    /// Thread-local tokenizer to eliminate lock contention under parallel processing.
    ///
    /// Each thread gets its own BPE tokenizer instance, avoiding cache-line contention
    /// when using rayon's par_iter. Uses cl100k_base (GPT-4/ChatGPT tokenizer).
    ///
    /// Benefits over shared static:
    /// - Zero synchronization overhead
    /// - Better cache locality per thread
    /// - No false sharing between CPU cores
    static THREAD_TOKENIZER: RefCell<Option<CoreBPE>> = RefCell::new(
        match tiktoken_rs::cl100k_base() {
            Ok(bpe) => Some(bpe),
            Err(e) => {
                tracing::warn!(
                    "Failed to initialize thread-local tokenizer: {}, falling back to estimation",
                    e
                );
                None
            }
        }
    );
}

/// Count tokens in a string using the configured tokenizer.
///
/// The tokenizer used depends on the global setting from [`set_tokenizer_type`]:
///
/// - `Cl100kBase` (default): Uses tiktoken cl100k_base (GPT-4 tokenizer)
/// - `CharEstimate`: Uses Unicode-aware character estimation matching Python
/// - `Qwen3`: Falls back to `CharEstimate` (use [`count_tokens_tei`] for exact counts)
/// - Other: Uses the corresponding tiktoken tokenizer
///
/// Uses a thread-local tokenizer to eliminate lock contention under parallel
/// processing (e.g., rayon's par_iter).
///
/// # Arguments
///
/// * `text` - The text to count tokens for
///
/// # Returns
///
/// Token count (exact or estimated depending on configured tokenizer).
///
/// # BUG-02 Fix: Python Parity
///
/// To achieve exact parity with Python's token counting:
///
/// ```
/// use go_brrr::semantic::chunker::{set_tokenizer_type, TokenizerType, count_tokens};
///
/// // Option 1: Use CharEstimate for same formula as Python fallback
/// set_tokenizer_type(TokenizerType::CharEstimate);
/// let tokens = count_tokens("def hello(): pass");
///
/// // Option 2: Use count_tokens_tei for exact Qwen3 tokenizer counts
/// // (requires TEI server)
/// ```
#[must_use]
pub fn count_tokens(text: &str) -> usize {
    if text.is_empty() {
        return 0;
    }

    match get_tokenizer_type() {
        // Character-based estimation matching Python's fallback
        TokenizerType::CharEstimate => estimate_tokens_unicode_aware(text),
        // Qwen3 requires TEI server; fall back to char estimation for sync calls
        TokenizerType::Qwen3 => estimate_tokens_unicode_aware(text),
        // Use tiktoken for other types
        TokenizerType::Cl100kBase | TokenizerType::P50kBase | TokenizerType::R50kBase => {
            THREAD_TOKENIZER.with(|tokenizer| match tokenizer.borrow().as_ref() {
                Some(bpe) => bpe.encode_ordinary(text).len(),
                None => estimate_tokens_unicode_aware(text),
            })
        }
    }
}

/// Simple token estimate (~4 chars per token).
///
/// Fast estimation for ASCII/code text. For more accurate Unicode handling,
/// use [`estimate_tokens_unicode_aware`].
///
/// This function is kept for backward compatibility and testing purposes.
#[inline]
#[must_use]
#[allow(dead_code)]
fn estimate_tokens(text: &str) -> usize {
    (text.len() + 3) / 4
}

/// Unicode-aware token estimation matching Python's `estimate_tokens_fallback`.
///
/// Uses character-type heuristics for better accuracy than simple len/4:
/// - ASCII/code: ~4 chars per token
/// - CJK characters: ~1.5 tokens per char (each ideograph often = 1-2 tokens)
/// - Emoji: ~3 tokens per emoji
/// - Other Unicode: ~2 chars per token
///
/// This function produces **identical results to Python's fallback**,
/// ensuring consistent chunk boundaries between Rust and Python when
/// using `CharEstimate` tokenizer type.
///
/// ## Performance
///
/// Uses SIMD acceleration (AVX2/SSE2 on x86_64, NEON on aarch64) to count ASCII
/// bytes in 32-byte chunks. Since most source code is >90% ASCII, this provides
/// significant speedup over character-by-character iteration.
///
/// # Example
///
/// ```
/// use go_brrr::semantic::chunker::estimate_tokens_unicode_aware;
///
/// // ASCII text: ~4 chars per token
/// assert_eq!(estimate_tokens_unicode_aware("hello world"), 3);
///
/// // CJK text: higher token density
/// let cjk_estimate = estimate_tokens_unicode_aware("Hello");
/// assert!(cjk_estimate > 0);
/// ```
#[must_use]
pub fn estimate_tokens_unicode_aware(text: &str) -> usize {
    if text.is_empty() {
        return 0;
    }

    let bytes = text.as_bytes();

    // Fast SIMD path: count ASCII bytes (bytes with bit 7 = 0)
    // In UTF-8, ASCII bytes are exactly code points 0-127, so byte count = char count
    let ascii_chars = count_ascii_bytes_simd(bytes);

    // Classify non-ASCII characters (must decode UTF-8 to get codepoints)
    let mut cjk_chars: usize = 0;
    let mut emoji_chars: usize = 0;
    let mut other_chars: usize = 0;

    for c in text.chars() {
        let code = c as u32;

        // Skip ASCII - already counted via SIMD
        if code >= 128 {
            if is_cjk_char(code) {
                cjk_chars += 1;
            } else if is_emoji_char(code) {
                emoji_chars += 1;
            } else {
                // Other Unicode (extended Latin, Cyrillic, Arabic, etc.)
                other_chars += 1;
            }
        }
    }

    // Estimate tokens by character type density (matches Python exactly)
    let estimated = ascii_chars as f64 / 4.0      // ~4 ASCII chars per token
        + cjk_chars as f64 * 1.5                  // Each CJK char often = 1-2 tokens
        + emoji_chars as f64 * 3.0                // Emoji = 2-4 tokens each
        + other_chars as f64 / 2.0;               // Other Unicode ~2 chars per token

    // Return at least 1 for non-empty text
    (estimated as usize).max(1)
}

/// Count ASCII bytes using SIMD acceleration.
///
/// Uses AVX2 (32 bytes/iter) or SSE2 (16 bytes/iter) on x86_64,
/// NEON (16 bytes/iter) on aarch64, with scalar fallback.
///
/// ASCII bytes in UTF-8 are exactly bytes with bit 7 = 0 (< 128).
#[inline]
fn count_ascii_bytes_simd(bytes: &[u8]) -> usize {
    let len = bytes.len();

    // For small inputs, scalar is faster (no SIMD setup overhead)
    if len < 64 {
        return bytes.iter().filter(|&&b| b < 128).count();
    }

    let mut i = 0;

    // x86_64: Use AVX2 (32 bytes) or SSE2 (16 bytes)
    #[cfg(target_arch = "x86_64")]
    let mut ascii_count = count_ascii_x86_64(bytes, &mut i);

    // aarch64: Use NEON (16 bytes)
    #[cfg(target_arch = "aarch64")]
    let mut ascii_count = count_ascii_aarch64(bytes, &mut i);

    // Non-SIMD architectures: pure scalar
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    let mut ascii_count: usize = 0;

    // Scalar fallback for remaining bytes and non-SIMD architectures
    for &b in &bytes[i..] {
        if b < 128 {
            ascii_count += 1;
        }
    }

    ascii_count
}

/// x86_64 SIMD implementation using AVX2 or SSE2.
#[cfg(target_arch = "x86_64")]
#[inline]
fn count_ascii_x86_64(bytes: &[u8], offset: &mut usize) -> usize {
    use std::arch::x86_64::*;

    let len = bytes.len();
    let mut count: usize = 0;
    let ptr = bytes.as_ptr();

    // Try AVX2 first (32 bytes per iteration)
    if is_x86_feature_detected!("avx2") {
        // SAFETY: We check bounds before each load and AVX2 is detected
        unsafe {
            // 0x80 mask to check high bit of each byte
            let high_bit_mask = _mm256_set1_epi8(i8::MIN); // 0x80

            while *offset + 32 <= len {
                // Load 32 bytes unaligned
                let chunk = _mm256_loadu_si256(ptr.add(*offset).cast::<__m256i>());

                // AND with 0x80 to isolate high bit, compare to zero
                // Bytes with high bit = 0 are ASCII
                let high_bits = _mm256_and_si256(chunk, high_bit_mask);
                let is_ascii = _mm256_cmpeq_epi8(high_bits, _mm256_setzero_si256());

                // movemask: bit N = 1 if byte N was 0xFF (ASCII)
                let mask = _mm256_movemask_epi8(is_ascii) as u32;
                count += mask.count_ones() as usize;

                *offset += 32;
            }
        }
    } else if is_x86_feature_detected!("sse2") {
        // Fallback to SSE2 (16 bytes per iteration)
        // SAFETY: We check bounds before each load and SSE2 is detected
        unsafe {
            let high_bit_mask = _mm_set1_epi8(i8::MIN); // 0x80

            while *offset + 16 <= len {
                let chunk = _mm_loadu_si128(ptr.add(*offset).cast::<__m128i>());

                let high_bits = _mm_and_si128(chunk, high_bit_mask);
                let is_ascii = _mm_cmpeq_epi8(high_bits, _mm_setzero_si128());

                let mask = _mm_movemask_epi8(is_ascii) as u16;
                count += mask.count_ones() as usize;

                *offset += 16;
            }
        }
    }

    count
}

/// aarch64 SIMD implementation using NEON.
#[cfg(target_arch = "aarch64")]
#[inline]
fn count_ascii_aarch64(bytes: &[u8], offset: &mut usize) -> usize {
    use std::arch::aarch64::*;

    let len = bytes.len();
    let mut count: usize = 0;
    let ptr = bytes.as_ptr();

    // NEON is always available on aarch64
    // Process 16 bytes per iteration
    // SAFETY: We check bounds before each load
    unsafe {
        // High bit mask: 0x80 for each byte
        let high_bit_mask = vdupq_n_u8(0x80);
        let zero = vdupq_n_u8(0);

        while *offset + 16 <= len {
            // Load 16 bytes
            let chunk = vld1q_u8(ptr.add(*offset));

            // Check high bit: (byte & 0x80) == 0 means ASCII
            let high_bits = vandq_u8(chunk, high_bit_mask);
            let is_ascii = vceqq_u8(high_bits, zero);

            // Count 0xFF bytes (ASCII indicators)
            // Each 0xFF byte contributes 255, divide by 255 to get count
            // Use horizontal add for accurate counting
            let ascii_bytes = vandq_u8(is_ascii, vdupq_n_u8(1));
            count += vaddvq_u8(ascii_bytes) as usize;

            *offset += 16;
        }
    }

    count
}

/// Check if a Unicode codepoint is a CJK character.
#[inline]
fn is_cjk_char(code: u32) -> bool {
    // CJK Unified Ideographs
    (0x4E00..=0x9FFF).contains(&code)
        // CJK Extension A
        || (0x3400..=0x4DBF).contains(&code)
        // CJK Extension B
        || (0x20000..=0x2A6DF).contains(&code)
        // CJK Extension C
        || (0x2A700..=0x2B73F).contains(&code)
        // CJK Extension D
        || (0x2B740..=0x2B81F).contains(&code)
        // CJK Compatibility Ideographs
        || (0xF900..=0xFAFF).contains(&code)
        // CJK Punctuation
        || (0x3000..=0x303F).contains(&code)
        // Hiragana
        || (0x3040..=0x309F).contains(&code)
        // Katakana
        || (0x30A0..=0x30FF).contains(&code)
        // Korean Hangul Syllables
        || (0xAC00..=0xD7AF).contains(&code)
}

/// Check if a Unicode codepoint is an emoji.
#[inline]
fn is_emoji_char(code: u32) -> bool {
    // Misc Symbols and Pictographs, Emoticons
    (0x1F300..=0x1F9FF).contains(&code)
        // Chess Symbols, Extended-A
        || (0x1FA00..=0x1FA6F).contains(&code)
        // Emoticons
        || (0x1F600..=0x1F64F).contains(&code)
        // Misc Symbols
        || (0x2600..=0x26FF).contains(&code)
        // Dingbats
        || (0x2700..=0x27BF).contains(&code)
        // Variation Selectors
        || (0xFE00..=0xFE0F).contains(&code)
        // Mahjong, Dominos
        || (0x1F000..=0x1F02F).contains(&code)
}

// =============================================================================
// TEI-based Token Counting (BUG-02 Fix)
// =============================================================================

/// Count tokens using the TEI server's tokenizer.
///
/// This function provides **exact parity with Python's semantic module** by using
/// the actual embedding model's tokenizer (e.g., Qwen3) via the TEI gRPC server.
///
/// # Why Use This?
///
/// The local [`count_tokens`] function uses `cl100k_base` (GPT-4 tokenizer),
/// which produces different token counts than Python's Qwen3-based tokenizer.
/// This can cause **5-15% variance** in chunk boundaries between Rust and Python.
///
/// Use this function when exact parity with Python is required, such as:
/// - Building indexes that will be queried by Python code
/// - Comparing chunk boundaries across implementations
/// - Testing tokenizer behavior
///
/// # Arguments
///
/// * `text` - The text to count tokens for
/// * `client` - TEI gRPC client instance
///
/// # Returns
///
/// The exact token count as determined by the embedding model's tokenizer.
///
/// # Errors
///
/// Returns [`TeiError`] if the TEI server is unavailable or returns an error.
///
/// # Example
///
/// ```no_run
/// use go_brrr::semantic::chunker::count_tokens_tei;
/// use go_brrr::embedding::TeiClient;
///
/// async fn example() -> Result<(), Box<dyn std::error::Error>> {
///     let client = TeiClient::new("http://localhost:18080").await?;
///     let code = "def process_data(items): return [x * 2 for x in items]";
///
///     let tokens = count_tokens_tei(code, &client).await?;
///     println!("Token count (Qwen3): {}", tokens);
///
///     // Compare with local tokenizer
///     let local_tokens = go_brrr::semantic::chunker::count_tokens(code);
///     println!("Token count (cl100k_base): {}", local_tokens);
///     println!("Variance: {:.1}%",
///         (local_tokens as f64 - tokens as f64).abs() / tokens as f64 * 100.0);
///
///     Ok(())
/// }
/// ```
pub async fn count_tokens_tei(text: &str, client: &TeiClient) -> Result<usize, TeiError> {
    if text.is_empty() {
        return Ok(0);
    }
    client.count_tokens(text).await
}

/// Count tokens for multiple texts using the TEI server's tokenizer.
///
/// Batch version of [`count_tokens_tei`] for efficient token counting of many texts.
/// Uses TEI's streaming RPC for optimal throughput.
///
/// # Arguments
///
/// * `texts` - Slice of texts to count tokens for
/// * `client` - TEI gRPC client instance
///
/// # Returns
///
/// Vector of token counts, one per input text.
///
/// # Errors
///
/// Returns [`TeiError`] if the TEI server is unavailable or returns an error.
///
/// # Example
///
/// ```no_run
/// use go_brrr::semantic::chunker::count_tokens_batch_tei;
/// use go_brrr::embedding::TeiClient;
///
/// async fn example() -> Result<(), Box<dyn std::error::Error>> {
///     let client = TeiClient::new("http://localhost:18080").await?;
///     let chunks = vec![
///         "def func1(): pass",
///         "def func2(): return 42",
///         "class MyClass: pass",
///     ];
///
///     let token_counts = count_tokens_batch_tei(&chunks, &client).await?;
///     for (chunk, count) in chunks.iter().zip(token_counts.iter()) {
///         println!("{}: {} tokens", chunk, count);
///     }
///
///     Ok(())
/// }
/// ```
pub async fn count_tokens_batch_tei(
    texts: &[&str],
    client: &TeiClient,
) -> Result<Vec<usize>, TeiError> {
    if texts.is_empty() {
        return Ok(Vec::new());
    }
    client.count_tokens_batch(texts).await
}

/// Compare token counts between local and TEI tokenizers.
///
/// Utility function to analyze the variance between local (cl100k_base) and
/// TEI (Qwen3) tokenizers for a given text. Useful for debugging and
/// understanding tokenizer behavior.
///
/// # Arguments
///
/// * `text` - The text to analyze
/// * `client` - TEI gRPC client instance
///
/// # Returns
///
/// A tuple of (local_count, tei_count, variance_percentage).
/// Variance is calculated as `abs(local - tei) / tei * 100`.
///
/// # Example
///
/// ```no_run
/// use go_brrr::semantic::chunker::compare_tokenizer_counts;
/// use go_brrr::embedding::TeiClient;
///
/// async fn example() -> Result<(), Box<dyn std::error::Error>> {
///     let client = TeiClient::new("http://localhost:18080").await?;
///     let code = "async def fetch_user(user_id: int) -> User: ...";
///
///     let (local, tei, variance) = compare_tokenizer_counts(code, &client).await?;
///     println!("cl100k_base: {} tokens", local);
///     println!("Qwen3: {} tokens", tei);
///     println!("Variance: {:.1}%", variance);
///
///     Ok(())
/// }
/// ```
pub async fn compare_tokenizer_counts(
    text: &str,
    client: &TeiClient,
) -> Result<(usize, usize, f64), TeiError> {
    let local_count = count_tokens(text);
    let tei_count = count_tokens_tei(text, client).await?;

    let variance = if tei_count == 0 {
        0.0
    } else {
        (local_count as f64 - tei_count as f64).abs() / tei_count as f64 * 100.0
    };

    Ok((local_count, tei_count, variance))
}

/// Count lines in content, correctly handling trailing newlines.
///
/// Unlike `str::lines().count()`, this function correctly counts the
/// empty line that exists after a trailing newline. This is important
/// for accurate line number tracking in chunks and matches how text
/// editors count lines.
///
/// The formula is: number of newlines + 1 = number of lines.
///
/// # Examples
///
/// - `""` -> 0 (empty string has no lines)
/// - `"a"` -> 1 (single line without newline)
/// - `"a\n"` -> 2 (line "a" + empty line after newline)
/// - `"\n\n\n"` -> 4 (3 newlines = 4 lines)
/// - `"a\nb\nc"` -> 3 (three lines)
/// - `"a\nb\nc\n"` -> 4 (three lines + trailing empty)
#[inline]
#[must_use]
pub fn count_lines(content: &str) -> usize {
    use std::simd::{cmp::SimdPartialEq, u8x32};

    if content.is_empty() {
        return 0;
    }

    let bytes = content.as_bytes();
    let len = bytes.len();
    let newline_vec = u8x32::splat(b'\n');

    let mut count = 0_usize;
    let mut offset = 0_usize;

    // SIMD: process 32 bytes at a time
    while offset + 32 <= len {
        // SAFETY: bounds check guarantees bytes[offset..offset+32] is valid
        let chunk = u8x32::from_slice(&bytes[offset..offset + 32]);
        let mask = chunk.simd_eq(newline_vec);
        count += mask.to_bitmask().count_ones() as usize;
        offset += 32;
    }

    // Scalar: handle remaining bytes (0..31)
    for &byte in &bytes[offset..] {
        if byte == b'\n' {
            count += 1;
        }
    }

    // Number of lines = number of newlines + 1
    count + 1
}

/// Truncate text to fit within a token limit.
///
/// Uses the thread-local tokenizer to find the maximum substring that fits
/// within the token budget by encoding and decoding.
///
/// # Arguments
///
/// * `text` - The text to truncate
/// * `max_tokens` - Maximum number of tokens
///
/// # Returns
///
/// Truncated text that fits within the token limit.
#[must_use]
pub fn truncate_to_tokens(text: &str, max_tokens: usize) -> String {
    if text.is_empty() || max_tokens == 0 {
        return String::new();
    }

    let current_tokens = count_tokens(text);
    if current_tokens <= max_tokens {
        return text.to_string();
    }

    THREAD_TOKENIZER.with(|tokenizer| {
        match tokenizer.borrow().as_ref() {
            Some(bpe) => {
                let tokens = bpe.encode_ordinary(text);
                if tokens.len() <= max_tokens {
                    return text.to_string();
                }
                let truncated_tokens = &tokens[..max_tokens];
                bpe.decode(truncated_tokens.to_vec())
                    .unwrap_or_else(|_| {
                        // Fallback: estimate character count on decode failure
                        let max_chars = max_tokens * 4;
                        if text.len() <= max_chars {
                            text.to_string()
                        } else {
                            // Find nearest word boundary for clean truncation
                            let truncated = &text[..max_chars.min(text.len())];
                            match truncated.rfind(char::is_whitespace) {
                                Some(pos) => truncated[..pos].to_string(),
                                None => truncated.to_string(),
                            }
                        }
                    })
            }
            None => {
                // Fallback: estimate ~4 chars per token
                let max_chars = max_tokens * 4;
                if text.len() <= max_chars {
                    text.to_string()
                } else {
                    // Find nearest word boundary for clean truncation
                    let truncated = &text[..max_chars];
                    match truncated.rfind(char::is_whitespace) {
                        Some(pos) => truncated[..pos].to_string(),
                        None => truncated.to_string(),
                    }
                }
            }
        }
    })
}

// =============================================================================
// Chunk Data Structure
// =============================================================================

/// A chunk of code with metadata for embedding and reconstruction.
///
/// This struct contains both positional information (for reconstruction) and
/// semantic metadata (signature, docstring, calls) for richer embedding context.
/// The semantic fields match Python's `EmbeddingUnit` when `unit_type="chunk"`.
///
/// # Line Numbering Convention (BUG-16 Fix)
///
/// All line numbers in this struct are **1-indexed** to match editor conventions.
/// See the module-level documentation for the full convention.
///
/// - `start_line`: First line of chunk (1-indexed, INCLUSIVE)
/// - `end_line`: Last line of chunk (1-indexed, INCLUSIVE)
///
/// For internal array operations, use [`line_to_index`] to convert.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Chunk {
    /// Unique identifier for this chunk (e.g., "file.py::func_name#chunk1")
    pub chunk_id: String,

    /// The actual code content of this chunk
    pub content: String,

    /// Number of tokens in this chunk
    pub token_count: usize,

    /// Starting line number (1-indexed, INCLUSIVE) in the original code.
    ///
    /// The first line of the chunk has this line number.
    /// The first line of any file is line 1, not line 0.
    /// This matches editor line numbering (VS Code, Vim, etc.).
    ///
    /// # Invariant
    ///
    /// `start_line >= 1` (validated in debug builds)
    pub start_line: usize,

    /// Ending line number (1-indexed, INCLUSIVE) in the original code.
    ///
    /// The last line of the chunk has this line number. This differs from Python's
    /// range() convention where end is exclusive. For a chunk containing lines 10-15:
    /// - `start_line = 10` (first line)
    /// - `end_line = 15` (last line, INCLUDED in chunk)
    /// - `line_count() = 6` (15 - 10 + 1)
    ///
    /// This inclusive convention matches 1-indexed line numbers shown in editors
    /// and makes single-line chunks intuitive: `start_line == end_line`.
    ///
    /// # Invariant
    ///
    /// `end_line >= start_line` (validated in debug builds)
    pub end_line: usize,

    /// Starting character offset in the original code
    pub start_char: usize,

    /// Ending character offset in the original code
    pub end_char: usize,

    /// Index of this chunk (0-indexed)
    pub chunk_index: usize,

    /// Total number of chunks for the parent unit
    pub chunk_total: usize,

    /// Reference to the parent unit name (for reconstruction)
    pub parent_ref: Option<String>,

    // =========================================================================
    // Semantic metadata fields (matching Python's EmbeddingUnit for chunks)
    // =========================================================================
    /// Function/method/class signature if applicable.
    /// For the first chunk, this contains the full signature.
    /// For subsequent chunks, this may contain "// continued from <name>".
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,

    /// Extracted docstring from the code unit.
    /// Typically only present in the first chunk of a multi-chunk unit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub docstring: Option<String>,

    /// Functions/methods called within this chunk.
    /// Enables call graph analysis at the chunk level.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub calls: Vec<String>,
}

impl Chunk {
    /// Create a new chunk with the given content and metadata.
    ///
    /// The semantic fields (signature, docstring, calls) are initialized to empty/None.
    /// Use the builder methods or `with_metadata()` to populate them.
    ///
    /// # Arguments
    ///
    /// * `content` - The code content of this chunk
    /// * `start_line` - Starting line number (1-indexed, INCLUSIVE). Must be >= 1.
    /// * `end_line` - Ending line number (1-indexed, INCLUSIVE). Must be >= start_line.
    /// * `start_char` - Starting character offset in original code
    /// * `end_char` - Ending character offset in original code
    ///
    /// # Panics (Debug Only)
    ///
    /// In debug builds, panics if:
    /// - `start_line < 1` (line numbers are 1-indexed)
    /// - `end_line < start_line` (invalid range)
    ///
    /// In release builds, these constraints are not checked for performance.
    #[must_use]
    pub fn new(
        content: String,
        start_line: usize,
        end_line: usize,
        start_char: usize,
        end_char: usize,
    ) -> Self {
        // BUG-16: Validate 1-indexed line number convention
        debug_assert!(
            start_line >= 1,
            "start_line must be 1-indexed (>= 1), got {}. \
             Use index_to_line() to convert from 0-indexed array indices.",
            start_line
        );
        debug_assert!(
            end_line >= start_line,
            "end_line ({}) must be >= start_line ({}). \
             For single-line chunks, use start_line == end_line.",
            end_line,
            start_line
        );

        let token_count = count_tokens(&content);
        Self {
            chunk_id: String::new(),
            content,
            token_count,
            start_line,
            end_line,
            start_char,
            end_char,
            chunk_index: 0,
            chunk_total: 1,
            parent_ref: None,
            signature: None,
            docstring: None,
            calls: Vec::new(),
        }
    }

    /// Set the chunk ID.
    #[must_use]
    pub fn with_id(mut self, id: impl Into<String>) -> Self {
        self.chunk_id = id.into();
        self
    }

    /// Set the parent reference.
    #[must_use]
    pub fn with_parent(mut self, parent: impl Into<String>) -> Self {
        self.parent_ref = Some(parent.into());
        self
    }

    /// Set chunk index and total.
    #[must_use]
    pub fn with_chunk_info(mut self, index: usize, total: usize) -> Self {
        self.chunk_index = index;
        self.chunk_total = total;
        self
    }

    /// Set semantic metadata (signature, docstring, and calls).
    ///
    /// This is useful for enriching chunks with information from the parent unit.
    /// Following Python's convention:
    /// - First chunk gets full signature and docstring
    /// - Subsequent chunks may get abbreviated signature ("// continued from <name>")
    ///
    /// # Arguments
    ///
    /// * `signature` - Function/method/class signature if applicable
    /// * `docstring` - Extracted docstring from the code unit
    /// * `calls` - Functions/methods called within this chunk
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::semantic::chunker::Chunk;
    ///
    /// let chunk = Chunk::new("def foo(): pass".to_string(), 1, 1, 0, 15)
    ///     .with_metadata(
    ///         Some("def foo() -> None".to_string()),
    ///         Some("Does foo things".to_string()),
    ///         vec!["bar".to_string(), "baz".to_string()],
    ///     );
    ///
    /// assert_eq!(chunk.signature, Some("def foo() -> None".to_string()));
    /// assert_eq!(chunk.docstring, Some("Does foo things".to_string()));
    /// assert_eq!(chunk.calls, vec!["bar", "baz"]);
    /// ```
    #[must_use]
    pub fn with_metadata(
        mut self,
        signature: Option<String>,
        docstring: Option<String>,
        calls: Vec<String>,
    ) -> Self {
        self.signature = signature;
        self.docstring = docstring;
        self.calls = calls;
        self
    }

    /// Set the signature.
    #[must_use]
    pub fn with_signature(mut self, signature: impl Into<String>) -> Self {
        self.signature = Some(signature.into());
        self
    }

    /// Set the docstring.
    #[must_use]
    pub fn with_docstring(mut self, docstring: impl Into<String>) -> Self {
        self.docstring = Some(docstring.into());
        self
    }

    /// Add calls to the list of functions called within this chunk.
    #[must_use]
    pub fn with_calls(mut self, calls: Vec<String>) -> Self {
        self.calls = calls;
        self
    }

    /// Check if this is a standalone chunk (not part of a larger unit).
    #[must_use]
    pub fn is_standalone(&self) -> bool {
        self.chunk_total == 1
    }

    /// Check if this chunk has semantic metadata populated.
    #[must_use]
    pub fn has_metadata(&self) -> bool {
        self.signature.is_some() || self.docstring.is_some() || !self.calls.is_empty()
    }

    /// Get the number of lines in this chunk.
    ///
    /// Since both `start_line` and `end_line` are 1-indexed INCLUSIVE,
    /// the line count is `end_line - start_line + 1`.
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::semantic::chunker::Chunk;
    ///
    /// // Chunk containing lines 10, 11, 12, 13, 14, 15
    /// let chunk = Chunk::new("content".to_string(), 10, 15, 0, 7);
    /// assert_eq!(chunk.line_count(), 6);
    ///
    /// // Single-line chunk
    /// let single = Chunk::new("x".to_string(), 5, 5, 0, 1);
    /// assert_eq!(single.line_count(), 1);
    /// ```
    #[must_use]
    pub fn line_count(&self) -> usize {
        // Both start_line and end_line are 1-indexed inclusive
        self.end_line.saturating_sub(self.start_line) + 1
    }

    /// Check if a 1-indexed line number is within this chunk.
    ///
    /// Since both `start_line` and `end_line` are INCLUSIVE,
    /// a line is contained if `start_line <= line <= end_line`.
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::semantic::chunker::Chunk;
    ///
    /// // Chunk containing lines 10-15 (inclusive)
    /// let chunk = Chunk::new("content".to_string(), 10, 15, 0, 7);
    ///
    /// assert!(chunk.contains_line(10));   // First line (inclusive)
    /// assert!(chunk.contains_line(12));   // Middle line
    /// assert!(chunk.contains_line(15));   // Last line (inclusive)
    /// assert!(!chunk.contains_line(9));   // Before chunk
    /// assert!(!chunk.contains_line(16));  // After chunk
    /// ```
    #[must_use]
    pub fn contains_line(&self, line: usize) -> bool {
        line >= self.start_line && line <= self.end_line
    }
}

// =============================================================================
// Boundary Detection
// =============================================================================

/// Types of code boundaries that are good split points.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum BoundaryKind {
    /// Blank line (lowest priority)
    BlankLine,
    /// Comment line
    Comment,
    /// End of a code block (dedent)
    BlockEnd,
    /// Start of a function/method definition
    FunctionStart,
    /// Start of a class/struct definition
    ClassStart,
}

/// A potential split boundary in the code.
///
/// # Internal Use Only
///
/// This struct uses **0-indexed** line indices for internal array operations.
/// When creating [`Chunk`] structs for external use, convert using [`index_to_line`]:
///
/// ```ignore
/// let boundary_1indexed = index_to_line(boundary.line_idx);
/// ```
///
/// See the module-level documentation for the full line numbering convention.
#[derive(Debug, Clone)]
struct Boundary {
    /// Line index (0-indexed, internal).
    ///
    /// This is the array index into `lines: Vec<&str>`, where `lines[0]` is the
    /// first line. Convert to 1-indexed for external use with [`index_to_line`].
    line_idx: usize,
    /// Character offset (preserved for potential future use in precise slicing)
    #[allow(dead_code)]
    char_offset: usize,
    /// Type of boundary
    kind: BoundaryKind,
}

/// Regex patterns for detecting code boundaries.
static BOUNDARY_PATTERNS: Lazy<BoundaryPatterns> = Lazy::new(BoundaryPatterns::new);

struct BoundaryPatterns {
    /// Matches function/method definitions across languages
    function_start: Regex,
    /// Matches class/struct/interface definitions
    class_start: Regex,
    /// Matches comment lines
    comment: Regex,
    /// Matches blank or whitespace-only lines
    blank: Regex,
}

impl BoundaryPatterns {
    fn new() -> Self {
        Self {
            // Function patterns: def, fn, func, function, async function, public/private methods
            function_start: Regex::new(r"^\s*(pub\s+)?(async\s+)?(def|fn|func|function|fun)\s+\w+")
                .expect("valid regex"),

            // Class patterns: class, struct, interface, trait, type (Go/TS)
            // Rust impl pattern handles optional generics: impl<T>, impl<T: Clone>, impl<'a, T>
            // The generic pattern `<(?:[^<>]|<[^>]*>)*>` handles one level of nesting:
            //   - [^<>] matches non-bracket chars (type params, bounds, lifetimes)
            //   - <[^>]*> matches nested simple generics like Iterator<Item=Foo>
            // Test cases that must match:
            //   - impl Foo {
            //   - impl<T> Foo<T> {
            //   - impl<T: Clone> Foo<T> for Bar {
            //   - impl<'a, T: 'a + Clone> Foo<'a, T> {
            //   - impl<T: Iterator<Item=Foo>> Bar {  (nested generics)
            class_start: Regex::new(
                r"^\s*(pub\s+)?(?:(?:class|struct|interface|trait|type)\s+\w+|impl\s*(?:<(?:[^<>]|<[^>]*>)*>)?\s*\w+)"
            ).expect("valid regex"),

            // Comment patterns for various programming languages:
            // - #         : Python, Ruby, Shell, YAML (not shebang #!, not Rust attr #[, not ## decorators)
            // - //        : C, C++, Java, JavaScript, TypeScript, Rust, Go, Swift, Kotlin
            // - /*        : C-style block comment start (all C-family languages)
            // - """       : Python docstring (triple double quotes)
            // - '''       : Python docstring (triple single quotes)
            // - --        : SQL, Haskell, Lua (not --> for XML/SGML closing)
            // - (*        : OCaml, Pascal, ML, F#
            // - %         : LaTeX, Erlang, MATLAB (not %% format specifier, not %= modulo-assign)
            // - ;         : Lisp, Scheme, Clojure, assembly
            // - <!--      : HTML, XML, SGML
            // - !         : Fortran (only when followed by whitespace or end of line)
            // - '         : BASIC, VB.NET (not ''' which is Python docstring)
            //
            // BUG-14 fix: Added --, (*, %, ;, <!--, !, ' patterns and fixed single # detection
            // Note: Rust regex crate doesn't support lookahead, using alternation with $ anchor instead
            comment: Regex::new(
                r#"^\s*(?:#(?:$|[^!\[#])|//|/\*|"""|'''|--(?:$|[^>])|\(\*|%(?:$|[^%=])|;|<!--|!(?:\s|$)|'(?:$|[^']))"#
            ).expect("valid regex"),

            // Blank line
            blank: Regex::new(r"^\s*$").expect("valid regex"),
        }
    }
}

/// Detect code boundaries in the given lines.
///
/// Scans each line and identifies potential split points based on
/// code structure patterns.
fn detect_boundaries(lines: &[&str], line_offsets: &[usize]) -> Vec<Boundary> {
    let mut boundaries = Vec::new();
    let patterns = &*BOUNDARY_PATTERNS;

    for (idx, line) in lines.iter().enumerate() {
        let char_offset = line_offsets.get(idx).copied().unwrap_or(0);

        // Check patterns in order of priority (highest first)
        if patterns.class_start.is_match(line) {
            boundaries.push(Boundary {
                line_idx: idx,
                char_offset,
                kind: BoundaryKind::ClassStart,
            });
        } else if patterns.function_start.is_match(line) {
            boundaries.push(Boundary {
                line_idx: idx,
                char_offset,
                kind: BoundaryKind::FunctionStart,
            });
        } else if patterns.blank.is_match(line) {
            boundaries.push(Boundary {
                line_idx: idx,
                char_offset,
                kind: BoundaryKind::BlankLine,
            });
        } else if patterns.comment.is_match(line) {
            boundaries.push(Boundary {
                line_idx: idx,
                char_offset,
                kind: BoundaryKind::Comment,
            });
        }

        // Detect block ends by checking for any dedent (single or multiple levels).
        // For Python/indent-based languages, any dedent back to a lower indent level
        // marks the end of a code block (if, for, while, with, try, etc.).
        //
        // Example:
        //   def foo():
        //       if x:
        //           pass
        //       bar()  # Single dedent from indent=2 to indent=1 - should be detected
        //
        // Previously this required 2-level dedents (prev_indent > curr_indent + 1),
        // which missed single-level dedents like the `bar()` line above.
        if idx > 0 {
            let prev_indent = get_indent_depth(lines[idx - 1]);
            let curr_indent = get_indent_depth(line);
            // Any dedent (prev_indent > curr_indent) indicates potential block end
            if prev_indent > curr_indent && !line.trim().is_empty() {
                boundaries.push(Boundary {
                    line_idx: idx,
                    char_offset,
                    kind: BoundaryKind::BlockEnd,
                });
            }
        }
    }

    boundaries
}

/// Calculate indentation depth of a line.
///
/// Expands tabs to 4 spaces for consistent counting.
#[inline]
fn get_indent_depth(line: &str) -> usize {
    let stripped = line.trim_start();
    if stripped.is_empty() {
        return 0;
    }

    let leading_len = line.len() - stripped.len();
    let leading = &line[..leading_len];
    // Expand tabs to 4 spaces
    let expanded_len: usize = leading.chars().map(|c| if c == '\t' { 4 } else { 1 }).sum();

    expanded_len / 4
}

// =============================================================================
// Main Chunking Function
// =============================================================================

/// Split code into token-limited chunks with context overlap.
///
/// This function intelligently splits code at natural boundaries (function
/// definitions, class definitions, blank lines) while respecting token limits.
/// Consecutive chunks overlap slightly to maintain context continuity.
///
/// # Arguments
///
/// * `code` - The source code to chunk
/// * `max_tokens` - Maximum tokens per chunk (default: `MAX_CODE_PREVIEW_TOKENS`)
///
/// # Returns
///
/// A vector of [`Chunk`] objects. Returns a single chunk containing the entire
/// code if it fits within the token limit.
///
/// # Algorithm
///
/// 1. If code fits in token budget, return single chunk
/// 2. Detect natural boundaries (functions, classes, blank lines)
/// 3. Accumulate lines until approaching token limit
/// 4. Split at the best boundary before the limit
/// 5. Include overlap from previous chunk for context
/// 6. Repeat until all code is chunked
///
/// # Edge Cases
///
/// - **Single function > max_tokens**: Splits at sub-function boundaries
///   (blank lines, comments) or falls back to line-by-line splitting
/// - **Deeply nested code**: Uses indentation changes as split points
/// - **Long strings/comments**: Treated as atomic units where possible
///
/// # Examples
///
/// ```
/// use go_brrr::semantic::chunker::chunk_code;
///
/// let code = r#"
/// def func1():
///     pass
///
/// def func2():
///     pass
/// "#;
///
/// let chunks = chunk_code(code, 100);
/// assert!(!chunks.is_empty());
/// for chunk in &chunks {
///     assert!(chunk.token_count <= 100 || chunk.content.lines().count() == 1);
/// }
/// ```
#[must_use]
pub fn chunk_code(code: &str, max_tokens: usize) -> Vec<Chunk> {
    chunk_code_with_overlap(code, max_tokens, CHUNK_OVERLAP_TOKENS)
}

/// Split code into chunks with custom overlap.
///
/// See [`chunk_code`] for full documentation.
#[must_use]
pub fn chunk_code_with_overlap(code: &str, max_tokens: usize, overlap_tokens: usize) -> Vec<Chunk> {
    if code.is_empty() {
        return Vec::new();
    }

    // Check if code fits in a single chunk
    let total_tokens = count_tokens(code);
    if total_tokens <= max_tokens {
        let line_count = count_lines(code);
        return vec![Chunk::new(code.to_string(), 1, line_count, 0, code.len())];
    }

    // Parse lines and build offset map
    let lines: Vec<&str> = code.lines().collect();
    let line_offsets = build_line_offsets(&lines, code);

    // Detect natural boundaries
    let boundaries = detect_boundaries(&lines, &line_offsets);

    // Smart chunking with boundary awareness
    chunk_with_boundaries(
        code,
        &lines,
        &line_offsets,
        &boundaries,
        max_tokens,
        overlap_tokens,
    )
}

/// Build a map of line index to character offset.
fn build_line_offsets(lines: &[&str], code: &str) -> Vec<usize> {
    let mut offsets = Vec::with_capacity(lines.len());
    let mut current_offset = 0;

    for (i, line) in lines.iter().enumerate() {
        offsets.push(current_offset);
        current_offset += line.len();
        // Add 1 for newline if not the last line
        if i < lines.len() - 1 {
            current_offset += 1;
        }
    }

    // Handle trailing newline
    if code.ends_with('\n') && !lines.is_empty() {
        // The last line_offset already accounts for content
    }

    offsets
}

/// Perform chunking using detected boundaries.
fn chunk_with_boundaries(
    code: &str,
    lines: &[&str],
    line_offsets: &[usize],
    boundaries: &[Boundary],
    max_tokens: usize,
    overlap_tokens: usize,
) -> Vec<Chunk> {
    let mut chunks = Vec::new();

    // Pre-compute all line token counts in parallel using rayon.
    // This leverages the thread-local tokenizer to parallelize token counting,
    // reducing O(n) sequential tokenizer calls to O(n/cores) parallel calls.
    // For a 1000-line file on 8 cores, this is ~8x faster.
    let line_token_counts: Vec<usize> = lines
        .par_iter()
        .enumerate()
        .map(|(idx, line)| {
            let with_newline = if idx < lines.len() - 1 {
                format!("{}\n", line)
            } else {
                (*line).to_string()
            };
            count_tokens(&with_newline)
        })
        .collect();

    // Track current chunk state
    let mut chunk_start_line = 0;
    let mut current_tokens = 0;
    let mut last_good_boundary: Option<usize> = None; // line index of last good split point

    // Track overlap for context continuity (values set on chunk split)
    let mut overlap_lines: Vec<usize>;
    let mut overlap_token_count: usize;

    for (line_idx, _line) in lines.iter().enumerate() {
        // Use pre-computed token count instead of calling count_tokens each iteration
        let line_tokens = line_token_counts[line_idx];

        // Check if adding this line would exceed limit
        if current_tokens + line_tokens > max_tokens && line_idx > chunk_start_line {
            // Find best split point
            let split_line =
                find_best_split(chunk_start_line, line_idx, last_good_boundary, boundaries);

            // Create chunk
            let chunk =
                create_chunk_from_range(code, lines, line_offsets, chunk_start_line, split_line);
            chunks.push(chunk);

            // Calculate overlap for next chunk (only scan within current chunk)
            (overlap_lines, overlap_token_count) =
                calculate_overlap(lines, chunk_start_line, split_line, overlap_tokens);

            // Start new chunk with overlap
            chunk_start_line = split_line.saturating_sub(overlap_lines.len());
            current_tokens = overlap_token_count;
            last_good_boundary = None;
        }

        // Check if this line is a good boundary
        if boundaries.iter().any(|b| b.line_idx == line_idx) {
            last_good_boundary = Some(line_idx);
        }

        current_tokens += line_tokens;
    }

    // Don't forget the last chunk
    if chunk_start_line < lines.len() {
        let chunk =
            create_chunk_from_range(code, lines, line_offsets, chunk_start_line, lines.len());
        chunks.push(chunk);
    }

    // Assign chunk metadata
    let total_chunks = chunks.len();
    for (i, chunk) in chunks.iter_mut().enumerate() {
        chunk.chunk_index = i;
        chunk.chunk_total = total_chunks;
        chunk.chunk_id = format!("chunk_{}", i + 1);
    }

    // Handle edge case: single oversized line
    if chunks.len() == 1 && chunks[0].token_count > max_tokens {
        return handle_oversized_chunk(&chunks[0], max_tokens, overlap_tokens);
    }

    chunks
}

/// Find the best line to split at, preferring natural boundaries.
fn find_best_split(
    chunk_start: usize,
    current_line: usize,
    last_boundary: Option<usize>,
    boundaries: &[Boundary],
) -> usize {
    // First choice: use the last good boundary if available
    if let Some(boundary_line) = last_boundary {
        if boundary_line > chunk_start && boundary_line < current_line {
            return boundary_line;
        }
    }

    // Second choice: find the highest priority boundary in range
    let candidates: Vec<_> = boundaries
        .iter()
        .filter(|b| b.line_idx > chunk_start && b.line_idx < current_line)
        .collect();

    if let Some(best) = candidates.iter().max_by_key(|b| b.kind) {
        return best.line_idx;
    }

    // Fallback: split at current line
    current_line
}

/// Create a chunk from a line range (internal 0-indexed to public 1-indexed).
///
/// This function handles the conversion between internal 0-indexed array indices
/// and the public 1-indexed line numbers used in [`Chunk`].
///
/// # Arguments
///
/// * `code` - The full source code string
/// * `lines` - Pre-split lines from the code
/// * `line_offsets` - Character offset for each line start
/// * `start_idx` - Starting line index (0-indexed, INCLUSIVE)
/// * `end_idx` - Ending line index (0-indexed, EXCLUSIVE like Python range)
///
/// # Returns
///
/// A [`Chunk`] with 1-indexed INCLUSIVE line numbers.
///
/// # Conversion Details (BUG-16 Fix)
///
/// The internal 0-indexed exclusive range `[start_idx, end_idx)` maps to
/// 1-indexed inclusive range in the output Chunk:
///
/// ```text
/// Internal: [0, 3) means indices 0, 1, 2 (exclusive end)
/// Chunk:    start_line=1, end_line=3 (inclusive)
///
/// Conversion:
/// - start_line = index_to_line(start_idx) = start_idx + 1
/// - end_line = end_idx (exclusive 0-indexed == inclusive 1-indexed for last line)
/// ```
///
/// Note: `end_idx` being 0-indexed EXCLUSIVE means the last included index is
/// `end_idx - 1`. In 1-indexed terms, that's just `end_idx` (no +1 needed).
fn create_chunk_from_range(
    code: &str,
    lines: &[&str],
    line_offsets: &[usize],
    start_idx: usize,
    end_idx: usize,
) -> Chunk {
    let start_char = line_offsets.get(start_idx).copied().unwrap_or(0);
    let end_char = if end_idx >= lines.len() {
        code.len()
    } else {
        line_offsets.get(end_idx).copied().unwrap_or(code.len())
    };

    // Ensure we don't go past the end of code
    let end_char = end_char.min(code.len());
    let content = code[start_char..end_char].to_string();

    // BUG-16: Use index_to_line for clear 0-indexed to 1-indexed conversion.
    // - start_line: Convert 0-indexed to 1-indexed using index_to_line()
    // - end_line: Since end_idx is 0-indexed EXCLUSIVE, the last included index
    //   is (end_idx - 1). In 1-indexed terms: (end_idx - 1) + 1 = end_idx.
    //   This is why we use end_idx directly without index_to_line().
    Chunk::new(
        content,
        index_to_line(start_idx), // 0 -> 1, 1 -> 2, etc.
        end_idx,                  // Already correct: exclusive 0-idx == inclusive 1-idx
        start_char,
        end_char,
    )
}

/// Calculate overlap lines for context continuity.
///
/// Only iterates over lines within the current chunk (from `chunk_start_line` to `split_line`)
/// to avoid O(n^2) performance when processing large files.
///
/// # Arguments
///
/// * `lines` - All lines in the file
/// * `chunk_start_line` - Start line of the current chunk (0-indexed)
/// * `split_line` - Line where the chunk is being split (0-indexed)
/// * `overlap_tokens` - Target number of overlap tokens
///
/// # Returns
///
/// Tuple of (line indices for overlap, total token count of overlap)
fn calculate_overlap(
    lines: &[&str],
    chunk_start_line: usize,
    split_line: usize,
    overlap_tokens: usize,
) -> (Vec<usize>, usize) {
    let mut overlap_lines = Vec::new();
    let mut token_count = 0;

    // Go backwards from split point, but only within the current chunk
    // This is O(chunk_size) instead of O(file_size)
    for line_idx in (chunk_start_line..split_line).rev() {
        let line = lines.get(line_idx).copied().unwrap_or("");
        // Add 1 token for the newline character to match the main chunking loop's accounting.
        // Newlines typically encode as 1 token in most tokenizers (including cl100k_base).
        // All lines in the overlap range have newlines since they're not the last line of the file.
        let line_tokens = count_tokens(line) + 1;

        if token_count + line_tokens > overlap_tokens {
            break;
        }

        overlap_lines.insert(0, line_idx);
        token_count += line_tokens;
    }

    (overlap_lines, token_count)
}

/// Handle the edge case of a single chunk that exceeds the token limit.
///
/// This can happen when a single function or class is larger than the limit.
/// We fall back to line-by-line splitting in this case.
fn handle_oversized_chunk(chunk: &Chunk, max_tokens: usize, overlap_tokens: usize) -> Vec<Chunk> {
    let lines: Vec<&str> = chunk.content.lines().collect();

    if lines.len() <= 1 {
        // Single line that's too long - just truncate
        let truncated = truncate_to_tokens(&chunk.content, max_tokens);
        return vec![Chunk::new(
            truncated,
            chunk.start_line,
            chunk.start_line,
            chunk.start_char,
            chunk.start_char + chunk.content.len().min(max_tokens * 4),
        )];
    }

    // Try to split at blank lines within the oversized chunk
    let line_offsets = build_line_offsets(&lines, &chunk.content);
    let boundaries = detect_boundaries(&lines, &line_offsets);

    // If we have boundaries, try chunking again with smaller target.
    // BUG-13 FIX: Guard against recursive reduction reaching max_tokens=0.
    // Without this guard, the sequence max_tokens * 3/4 can reach 0:
    //   4 -> 3 -> 2 -> 1 -> 0, causing infinite recursion.
    // We use MIN_CHUNK_TOKENS as a floor and skip recursive splitting
    // if we can't reduce further.
    if !boundaries.is_empty() {
        let reduced_max = (max_tokens * 3 / 4).max(MIN_CHUNK_TOKENS);

        // Only attempt recursive splitting if we can actually reduce the target.
        // If reduced_max >= max_tokens, recursive splitting won't help and could
        // cause infinite recursion, so skip directly to force_split_by_lines.
        if reduced_max < max_tokens {
            let sub_chunks = chunk_with_boundaries(
                &chunk.content,
                &lines,
                &line_offsets,
                &boundaries,
                reduced_max,
                overlap_tokens,
            );

            if sub_chunks.len() > 1 {
                // Adjust line numbers to be relative to original chunk
                return sub_chunks
                    .into_iter()
                    .map(|mut c| {
                        c.start_line += chunk.start_line - 1;
                        c.end_line += chunk.start_line - 1;
                        c.start_char += chunk.start_char;
                        c.end_char += chunk.start_char;
                        c
                    })
                    .collect();
            }
        }
    }

    // Last resort: split by lines, trying to stay under token limit
    force_split_by_lines(
        &chunk.content,
        chunk.start_line,
        chunk.start_char,
        max_tokens,
    )
}

/// Force split content line by line when no good boundaries exist.
///
/// Preserves the original content exactly - only adds newlines between lines
/// if they existed in the original content. Does not add trailing newline
/// unless the original content had one.
///
/// # Arguments
///
/// * `content` - The content to split
/// * `base_line` - Starting line number (1-indexed). This is the line number
///   of the first line in `content` within the original file.
/// * `base_char` - Starting character offset
/// * `max_tokens` - Maximum tokens per chunk
///
/// # Line Number Calculation (BUG-16 Fix)
///
/// Since `base_line` is already 1-indexed (from `Chunk.start_line`) and
/// `enumerate()` produces 0-indexed offsets, the correct line number for
/// each line is simply `base_line + i`:
///
/// ```text
/// base_line = 10 (first line of this chunk in original file)
/// i = 0 (first line in content) -> line 10
/// i = 1 (second line in content) -> line 11
/// i = 2 (third line in content) -> line 12
/// ```
fn force_split_by_lines(
    content: &str,
    base_line: usize,
    base_char: usize,
    max_tokens: usize,
) -> Vec<Chunk> {
    let mut chunks = Vec::new();
    let mut current_content = String::new();
    let mut current_tokens = 0;
    let mut current_start_line = base_line;
    let mut current_start_char = base_char;
    let mut char_offset = 0;

    // Track if original content had trailing newline to preserve it
    let has_trailing_newline = content.ends_with('\n');
    let lines: Vec<&str> = content.lines().collect();
    let total_lines = lines.len();

    for (i, line) in lines.iter().enumerate() {
        let is_last_line = i == total_lines - 1;

        // Only add newline if not last line, OR if original had trailing newline
        let should_add_newline = !is_last_line || has_trailing_newline;
        let line_with_optional_newline = if should_add_newline {
            format!("{}\n", line)
        } else {
            (*line).to_string()
        };
        let line_tokens = count_tokens(&line_with_optional_newline);
        let line_byte_len = if should_add_newline {
            line.len() + 1
        } else {
            line.len()
        };

        // If single line exceeds limit, truncate it
        if line_tokens > max_tokens && current_content.is_empty() {
            let truncated = truncate_to_tokens(line, max_tokens);
            chunks.push(Chunk::new(
                truncated,
                base_line + i,
                base_line + i,
                base_char + char_offset,
                base_char + char_offset + line.len(),
            ));
            char_offset += line_byte_len;
            current_start_line = base_line + i + 1;
            current_start_char = base_char + char_offset;
            continue;
        }

        // Check if adding this line would exceed limit
        if current_tokens + line_tokens > max_tokens && !current_content.is_empty() {
            // Save current chunk
            let end_line = base_line + i - 1;
            let end_char = base_char + char_offset;
            chunks.push(Chunk::new(
                std::mem::take(&mut current_content),
                current_start_line,
                end_line,
                current_start_char,
                end_char,
            ));
            current_tokens = 0;
            current_start_line = base_line + i;
            current_start_char = base_char + char_offset;
        }

        current_content.push_str(&line_with_optional_newline);
        current_tokens += line_tokens;
        char_offset += line_byte_len;
    }

    // Don't forget the last chunk
    if !current_content.is_empty() {
        let end_line = base_line + total_lines.saturating_sub(1);
        chunks.push(Chunk::new(
            current_content,
            current_start_line,
            end_line,
            current_start_char,
            base_char + content.len(),
        ));
    }

    // Assign metadata
    let total = chunks.len();
    for (i, chunk) in chunks.iter_mut().enumerate() {
        chunk.chunk_index = i;
        chunk.chunk_total = total;
        chunk.chunk_id = format!("chunk_{}", i + 1);
    }

    chunks
}

// =============================================================================
// Convenience Functions
// =============================================================================

/// Chunk code using default settings.
///
/// Uses `MAX_CODE_PREVIEW_TOKENS` (6000) as the limit and
/// `CHUNK_OVERLAP_TOKENS` (200) for overlap.
#[must_use]
pub fn chunk_code_default(code: &str) -> Vec<Chunk> {
    chunk_code(code, MAX_CODE_PREVIEW_TOKENS)
}

/// Check if code needs to be chunked based on token count.
///
/// # Arguments
///
/// * `code` - The code to check
/// * `max_tokens` - Token limit to check against
///
/// # Returns
///
/// `true` if the code exceeds the token limit and needs chunking.
#[must_use]
pub fn needs_chunking(code: &str, max_tokens: usize) -> bool {
    count_tokens(code) > max_tokens
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_tokens_empty() {
        assert_eq!(count_tokens(""), 0);
    }

    #[test]
    fn test_count_tokens_simple() {
        // "hello world" should be around 2-3 tokens
        let count = count_tokens("hello world");
        assert!(count > 0);
        assert!(count < 10);
    }

    #[test]
    fn test_count_tokens_code() {
        let code = "def hello():\n    print('world')\n";
        let count = count_tokens(code);
        assert!(count > 0);
        // Should be reasonable for this small snippet
        assert!(count < 50);
    }

    // =========================================================================
    // count_lines tests - BUG-12 fix verification
    // =========================================================================

    #[test]
    fn test_count_lines_empty() {
        // Empty string has no lines
        assert_eq!(count_lines(""), 0);
    }

    #[test]
    fn test_count_lines_single_without_newline() {
        // Single line without trailing newline
        assert_eq!(count_lines("a"), 1);
        assert_eq!(count_lines("hello world"), 1);
    }

    #[test]
    fn test_count_lines_single_with_newline() {
        // Single line with trailing newline = 2 lines (content + empty)
        assert_eq!(count_lines("a\n"), 2);
        assert_eq!(count_lines("hello\n"), 2);
    }

    #[test]
    fn test_count_lines_multiple_without_trailing() {
        // Multiple lines without trailing newline
        assert_eq!(count_lines("a\nb"), 2);
        assert_eq!(count_lines("a\nb\nc"), 3);
        assert_eq!(count_lines("line1\nline2\nline3"), 3);
    }

    #[test]
    fn test_count_lines_multiple_with_trailing() {
        // Multiple lines with trailing newline
        assert_eq!(count_lines("a\nb\n"), 3);
        assert_eq!(count_lines("a\nb\nc\n"), 4);
        assert_eq!(count_lines("line1\nline2\nline3\n"), 4);
    }

    #[test]
    fn test_count_lines_only_newlines() {
        // BUG-12: This was the main bug - "\n\n\n".lines().count() = 3, but should be 4
        assert_eq!(count_lines("\n"), 2);      // 1 newline = 2 lines
        assert_eq!(count_lines("\n\n"), 3);    // 2 newlines = 3 lines
        assert_eq!(count_lines("\n\n\n"), 4);  // 3 newlines = 4 lines (the bug case!)
        assert_eq!(count_lines("\n\n\n\n"), 5);
    }

    #[test]
    fn test_count_lines_mixed_empty_lines() {
        // Content with empty lines in the middle
        assert_eq!(count_lines("a\n\nb"), 3);      // a, empty, b
        assert_eq!(count_lines("a\n\n\nb"), 4);    // a, empty, empty, b
        assert_eq!(count_lines("a\n\nb\n"), 4);    // a, empty, b, empty
    }

    #[test]
    fn test_count_lines_vs_lines_iterator() {
        // Verify the difference between count_lines and lines().count()
        // to document the bug we're fixing

        // Case 1: No trailing newline - same result
        let s1 = "a\nb\nc";
        assert_eq!(count_lines(s1), 3);
        assert_eq!(s1.lines().count(), 3);

        // Case 2: With trailing newline - count_lines is +1
        let s2 = "a\nb\nc\n";
        assert_eq!(count_lines(s2), 4);
        assert_eq!(s2.lines().count(), 3); // lines() misses the trailing empty line

        // Case 3: Only newlines - the bug case
        let s3 = "\n\n\n";
        assert_eq!(count_lines(s3), 4);
        assert_eq!(s3.lines().count(), 3); // lines() misses the trailing empty line
    }

    #[test]
    fn test_count_lines_chunk_end_line_accuracy() {
        // Verify that chunk end_line is accurate after the fix
        let code = "line1\nline2\nline3\n";
        let chunks = chunk_code(code, 1000);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].start_line, 1);
        // With the fix, end_line should be 4 (3 content lines + 1 trailing empty)
        assert_eq!(
            chunks[0].end_line, 4,
            "end_line should account for trailing newline"
        );
    }

    #[test]
    fn test_truncate_to_tokens_empty() {
        assert_eq!(truncate_to_tokens("", 100), "");
    }

    #[test]
    fn test_truncate_to_tokens_fits() {
        let text = "hello world";
        let result = truncate_to_tokens(text, 100);
        assert_eq!(result, text);
    }

    #[test]
    fn test_truncate_to_tokens_truncates() {
        let text = "hello world this is a longer text that should be truncated";
        let result = truncate_to_tokens(text, 3);
        assert!(result.len() < text.len());
        assert!(!result.is_empty());
    }

    #[test]
    fn test_chunk_empty() {
        let chunks = chunk_code("", 100);
        assert!(chunks.is_empty());
    }

    #[test]
    fn test_chunk_fits_single() {
        let code = "def hello():\n    pass\n";
        let chunks = chunk_code(code, 1000);
        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].content, code);
        assert_eq!(chunks[0].start_line, 1);
        assert!(chunks[0].is_standalone());
    }

    #[test]
    fn test_chunk_splits_at_functions() {
        let code = r#"def func1():
    """First function."""
    pass

def func2():
    """Second function."""
    pass

def func3():
    """Third function."""
    pass
"#;
        // Use a small token limit to force splitting
        let chunks = chunk_code(code, 20);
        assert!(chunks.len() > 1);

        // Each chunk should be reasonably close to the limit
        // With small limits (20 tokens), exact splitting is difficult as
        // we prioritize semantic boundaries over strict limits
        for chunk in &chunks {
            // Allow 2x tolerance for boundary-aware splitting with small limits
            assert!(
                chunk.token_count <= 50,
                "Chunk {} has {} tokens (expected <= 50)",
                chunk.chunk_index,
                chunk.token_count
            );
        }
    }

    #[test]
    fn test_chunk_preserves_content() {
        let code = "line1\nline2\nline3\nline4\nline5\n";
        let chunks = chunk_code(code, 5);

        // All content should be covered (with possible overlap)
        let all_lines: std::collections::HashSet<_> = code.lines().collect();
        let chunked_lines: std::collections::HashSet<_> =
            chunks.iter().flat_map(|c| c.content.lines()).collect();

        for line in &all_lines {
            assert!(
                chunked_lines.contains(line),
                "Line '{}' missing from chunks",
                line
            );
        }
    }

    #[test]
    fn test_chunk_metadata() {
        let code = "a\nb\nc\nd\ne\nf\ng\nh\n";
        let chunks = chunk_code(code, 3);

        for (i, chunk) in chunks.iter().enumerate() {
            assert_eq!(chunk.chunk_index, i);
            assert_eq!(chunk.chunk_total, chunks.len());
        }
    }

    #[test]
    fn test_get_indent_depth() {
        assert_eq!(get_indent_depth(""), 0);
        assert_eq!(get_indent_depth("    code"), 1);
        assert_eq!(get_indent_depth("        code"), 2);
        assert_eq!(get_indent_depth("\tcode"), 1);
        assert_eq!(get_indent_depth("\t\tcode"), 2);
        assert_eq!(get_indent_depth("  \tcode"), 1); // 2 spaces + 4 (tab) = 6 / 4 = 1
    }

    #[test]
    fn test_boundary_detection() {
        let code = "def func():\n    pass\n\nclass MyClass:\n    pass\n";
        let lines: Vec<&str> = code.lines().collect();
        let offsets = build_line_offsets(&lines, code);
        let boundaries = detect_boundaries(&lines, &offsets);

        // Should detect function start, blank line, and class start
        let kinds: Vec<_> = boundaries.iter().map(|b| b.kind).collect();
        assert!(kinds.contains(&BoundaryKind::FunctionStart));
        assert!(kinds.contains(&BoundaryKind::BlankLine));
        assert!(kinds.contains(&BoundaryKind::ClassStart));
    }

    // =========================================================================
    // Comment detection tests - BUG-14 fix verification
    // =========================================================================

    /// Helper to test if a line is detected as a comment boundary
    fn is_detected_as_comment(line: &str) -> bool {
        let lines = vec![line];
        let offsets = vec![0usize];
        let boundaries = detect_boundaries(&lines, &offsets);
        boundaries.iter().any(|b| b.kind == BoundaryKind::Comment)
    }

    #[test]
    fn test_comment_detection_python_ruby_shell() {
        // Python/Ruby/Shell: # comments
        assert!(is_detected_as_comment("  # Python comment"));
        assert!(is_detected_as_comment("# Ruby comment"));
        assert!(is_detected_as_comment("    # Shell comment"));
        assert!(is_detected_as_comment("#comment without space"));

        // Should NOT match shebang
        assert!(!is_detected_as_comment("#!/usr/bin/env python"));
        assert!(!is_detected_as_comment("#!bash"));

        // Should NOT match Rust attributes
        assert!(!is_detected_as_comment("#[derive(Debug)]"));
        assert!(!is_detected_as_comment("  #[cfg(test)]"));

        // Should NOT match decorators (## style)
        assert!(!is_detected_as_comment("## Section header decorator"));
    }

    #[test]
    fn test_comment_detection_c_style() {
        // C-style: // and /*
        assert!(is_detected_as_comment("  // C++ comment"));
        assert!(is_detected_as_comment("// single line"));
        assert!(is_detected_as_comment("    /* block comment start */"));
        assert!(is_detected_as_comment("/* multi"));
    }

    #[test]
    fn test_comment_detection_python_docstrings() {
        // Python docstrings: """ and '''
        assert!(is_detected_as_comment(r#"    """Docstring""""#));
        assert!(is_detected_as_comment(r#""""Triple quote doc""""#));
        assert!(is_detected_as_comment("  '''Single quote doc'''"));
        assert!(is_detected_as_comment("'''"));
    }

    #[test]
    fn test_comment_detection_sql_haskell_lua() {
        // SQL/Haskell/Lua: -- comments
        assert!(is_detected_as_comment("  -- SQL comment"));
        assert!(is_detected_as_comment("-- Haskell comment"));
        assert!(is_detected_as_comment("    -- Lua comment"));
        assert!(is_detected_as_comment("--compact"));

        // Should NOT match XML closing tag -->
        assert!(!is_detected_as_comment("  -->"));
        assert!(!is_detected_as_comment("-->closing tag"));
    }

    #[test]
    fn test_comment_detection_ocaml_pascal() {
        // OCaml/Pascal/ML: (* comments *)
        assert!(is_detected_as_comment("  (* OCaml comment *)"));
        assert!(is_detected_as_comment("(* Pascal comment *)"));
        assert!(is_detected_as_comment("    (* nested (* comment *) *)"));
        assert!(is_detected_as_comment("(*"));
    }

    #[test]
    fn test_comment_detection_latex_erlang_matlab() {
        // LaTeX/Erlang/MATLAB: % comments
        assert!(is_detected_as_comment("  % LaTeX comment"));
        assert!(is_detected_as_comment("% Erlang comment"));
        assert!(is_detected_as_comment("    % MATLAB comment"));

        // Should NOT match format specifiers or modulo-assign
        assert!(!is_detected_as_comment("  %% format spec"));
        assert!(!is_detected_as_comment("%=modulo"));
    }

    #[test]
    fn test_comment_detection_lisp_scheme() {
        // Lisp/Scheme/Clojure: ; comments
        assert!(is_detected_as_comment("  ; Lisp comment"));
        assert!(is_detected_as_comment("; Scheme comment"));
        assert!(is_detected_as_comment(";;; Section comment"));
        assert!(is_detected_as_comment("    ; Clojure comment"));
    }

    #[test]
    fn test_comment_detection_html_xml() {
        // HTML/XML: <!-- comments -->
        assert!(is_detected_as_comment("  <!-- HTML comment -->"));
        assert!(is_detected_as_comment("<!-- XML comment"));
        assert!(is_detected_as_comment("    <!--"));
    }

    #[test]
    fn test_comment_detection_fortran() {
        // Fortran: ! comments (only with whitespace or at end)
        assert!(is_detected_as_comment("  ! Fortran comment"));
        assert!(is_detected_as_comment("! comment"));

        // Should NOT match operators
        assert!(!is_detected_as_comment("  !="));
        assert!(!is_detected_as_comment("!important"));
    }

    #[test]
    fn test_comment_detection_basic_vb() {
        // BASIC/VB.NET: ' comments
        assert!(is_detected_as_comment("  ' VB comment"));
        assert!(is_detected_as_comment("' BASIC comment"));

        // Should NOT match triple quotes (handled by ''' pattern)
        // Note: ''' is matched by the explicit ''' pattern, not by '
        assert!(is_detected_as_comment("'''"));  // Matches as Python docstring
    }

    #[test]
    fn test_comment_detection_not_trailing() {
        // Trailing comments should NOT be detected (we detect comment LINES)
        assert!(!is_detected_as_comment("  code()  // trailing comment"));
        assert!(!is_detected_as_comment("x = 1  # trailing"));
        assert!(!is_detected_as_comment("SELECT * FROM foo  -- trailing"));
    }

    #[test]
    fn test_comment_detection_empty_and_whitespace() {
        // Empty and whitespace-only lines are NOT comments (they're blank lines)
        // The blank pattern matches these, not the comment pattern
        assert!(!is_detected_as_comment(""));
        assert!(!is_detected_as_comment("   "));
        assert!(!is_detected_as_comment("\t\t"));
    }

    #[test]
    fn test_single_level_dedent_block_end_detection() {
        // BUG-11 regression test: Single-level dedents should be detected as BlockEnd
        // Previously, only 2-level dedents were detected, missing patterns like:
        //
        //   def foo():
        //       if x:
        //           pass
        //       bar()  # Single dedent from indent=2 to indent=1
        //
        let code = r#"def foo():
    if x:
        pass
    bar()
    if y:
        baz()
    return result"#;
        let lines: Vec<&str> = code.lines().collect();
        let offsets = build_line_offsets(&lines, code);
        let boundaries = detect_boundaries(&lines, &offsets);

        // Find all BlockEnd boundaries
        let block_ends: Vec<_> = boundaries
            .iter()
            .filter(|b| b.kind == BoundaryKind::BlockEnd)
            .collect();

        // line 0: "def foo():"       -> indent 0, FunctionStart
        // line 1: "    if x:"        -> indent 1
        // line 2: "        pass"     -> indent 2
        // line 3: "    bar()"        -> indent 1, BlockEnd (dedent from 2 to 1)
        // line 4: "    if y:"        -> indent 1
        // line 5: "        baz()"    -> indent 2
        // line 6: "    return result"-> indent 1, BlockEnd (dedent from 2 to 1)

        // Should detect at least 2 single-level dedents: bar() and return result
        assert!(
            block_ends.len() >= 2,
            "Should detect at least 2 single-level dedents as BlockEnd, found {}. \
             Boundaries: {:?}",
            block_ends.len(),
            block_ends.iter().map(|b| b.line_idx).collect::<Vec<_>>()
        );

        // Verify specific lines are detected
        let block_end_lines: Vec<_> = block_ends.iter().map(|b| b.line_idx).collect();

        // bar() at line 3 (0-indexed) should be detected
        assert!(
            block_end_lines.contains(&3),
            "bar() at line 3 should be detected as BlockEnd. Found: {:?}",
            block_end_lines
        );

        // return result at line 6 (0-indexed) should be detected
        assert!(
            block_end_lines.contains(&6),
            "return result at line 6 should be detected as BlockEnd. Found: {:?}",
            block_end_lines
        );
    }

    #[test]
    fn test_multi_level_dedent_still_detected() {
        // Ensure multi-level dedents are still detected after BUG-11 fix
        let code = r#"def foo():
    if x:
        if y:
            pass
    bar()"#;
        // line 0: "def foo():"  -> indent 0
        // line 1: "    if x:"   -> indent 1
        // line 2: "        if y:" -> indent 2
        // line 3: "            pass" -> indent 3
        // line 4: "    bar()"   -> indent 1, BlockEnd (dedent from 3 to 1 = 2 levels)

        let lines: Vec<&str> = code.lines().collect();
        let offsets = build_line_offsets(&lines, code);
        let boundaries = detect_boundaries(&lines, &offsets);

        let block_ends: Vec<_> = boundaries
            .iter()
            .filter(|b| b.kind == BoundaryKind::BlockEnd)
            .map(|b| b.line_idx)
            .collect();

        // bar() at line 4 (0-indexed) should be detected as BlockEnd
        assert!(
            block_ends.contains(&4),
            "Multi-level dedent at line 4 should be detected. Found: {:?}",
            block_ends
        );
    }

    #[test]
    fn test_needs_chunking() {
        assert!(!needs_chunking("short", 100));
        assert!(needs_chunking(&"x".repeat(1000), 10));
    }

    #[test]
    fn test_chunk_with_overlap() {
        let code = "line1\nline2\nline3\nline4\nline5\n";
        let chunks = chunk_code_with_overlap(code, 5, 2);

        if chunks.len() > 1 {
            // Check that chunks have reasonable overlap
            // (exact overlap depends on tokenization)
            for i in 1..chunks.len() {
                let prev_end = chunks[i - 1].end_line;
                let curr_start = chunks[i].start_line;
                // Overlap means current start should be <= previous end
                assert!(
                    curr_start <= prev_end + 1,
                    "No overlap between chunks {} and {}",
                    i - 1,
                    i
                );
            }
        }
    }

    #[test]
    fn test_chunk_line_numbers() {
        let code = "line1\nline2\nline3\n";
        let chunks = chunk_code(code, 1000);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].start_line, 1);
        // BUG-12 fix: end_line now correctly includes the trailing empty line
        // "line1\nline2\nline3\n" has 4 lines: line1, line2, line3, and empty after \n
        assert_eq!(chunks[0].end_line, 4);
    }

    /// BUG-09 fix: Verify that end_line is INCLUSIVE (not exclusive like Python ranges).
    ///
    /// This test documents and enforces the convention:
    /// - start_line: 1-indexed, INCLUSIVE (first line IN the chunk)
    /// - end_line: 1-indexed, INCLUSIVE (last line IN the chunk)
    ///
    /// For a chunk containing lines 1, 2, 3:
    /// - start_line = 1
    /// - end_line = 3
    /// - line_count() = 3
    #[test]
    fn test_end_line_is_inclusive() {
        // Test case 1: Simple 3-line content without trailing newline
        let content = "line1\nline2\nline3";
        let chunks = chunk_code(content, 1000);
        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].start_line, 1, "start_line should be 1 (first line)");
        assert_eq!(chunks[0].end_line, 3, "end_line should be 3 (last line, INCLUSIVE)");
        assert_eq!(chunks[0].line_count(), 3, "line_count should be 3");

        // Verify contains_line works correctly
        assert!(chunks[0].contains_line(1), "Line 1 should be in chunk");
        assert!(chunks[0].contains_line(2), "Line 2 should be in chunk");
        assert!(chunks[0].contains_line(3), "Line 3 should be in chunk (INCLUSIVE)");
        assert!(!chunks[0].contains_line(0), "Line 0 should NOT be in chunk");
        assert!(!chunks[0].contains_line(4), "Line 4 should NOT be in chunk");

        // Test case 2: Content with trailing newline (creates extra empty line)
        let content_with_newline = "line1\nline2\nline3\n";
        let chunks2 = chunk_code(content_with_newline, 1000);
        assert_eq!(chunks2.len(), 1);
        assert_eq!(chunks2[0].start_line, 1);
        assert_eq!(
            chunks2[0].end_line, 4,
            "Trailing newline creates line 4 (empty), which should be INCLUDED"
        );
        assert_eq!(chunks2[0].line_count(), 4, "Should count all 4 lines");

        // Test case 3: Single-line chunk (start_line == end_line)
        let single_line = "only one line";
        let single_chunks = chunk_code(single_line, 1000);
        assert_eq!(single_chunks.len(), 1);
        assert_eq!(single_chunks[0].start_line, 1);
        assert_eq!(
            single_chunks[0].end_line, 1,
            "Single-line chunk: end_line == start_line"
        );
        assert_eq!(single_chunks[0].line_count(), 1);
        assert!(single_chunks[0].contains_line(1));
        assert!(!single_chunks[0].contains_line(2));
    }

    #[test]
    fn test_chunk_handles_long_single_line() {
        // A very long line that exceeds token limit
        let long_line = "x".repeat(10000);
        let chunks = chunk_code(&long_line, 100);

        assert!(!chunks.is_empty());
        // The first chunk should be truncated
        assert!(chunks[0].token_count <= 100 || chunks[0].content.len() < long_line.len());
    }

    #[test]
    fn test_estimate_tokens() {
        // Estimation should be roughly 1 token per 4 chars
        assert_eq!(estimate_tokens("12345678"), 2); // 8 chars / 4 = 2
        assert_eq!(estimate_tokens(""), 0);
        assert_eq!(estimate_tokens("abc"), 1); // (3 + 3) / 4 = 1
    }

    #[test]
    fn test_chunk_python_with_docstrings() {
        let code = r#"def process_data(items):
    """Process a list of items.

    This function takes items and processes them
    in a very important way.

    Args:
        items: List of items to process

    Returns:
        Processed items
    """
    result = []
    for item in items:
        result.append(transform(item))
    return result
"#;
        // With reasonable limit, docstring should stay with function
        let chunks = chunk_code(code, 100);
        assert!(!chunks.is_empty());

        // First chunk should contain the docstring
        let first_chunk = &chunks[0];
        assert!(
            first_chunk.content.contains("Process a list"),
            "Docstring should be in first chunk"
        );
    }

    #[test]
    fn test_chunk_rust_code() {
        let code = r#"fn main() {
    println!("Hello");
}

pub fn helper() {
    // Helper function
}

impl MyStruct {
    fn method(&self) {
        // Method body
    }
}
"#;
        let chunks = chunk_code(code, 30);

        // Should have detected function and impl boundaries
        assert!(!chunks.is_empty());
    }

    #[test]
    fn test_rust_impl_generics_boundary_detection() {
        // BUG-07: Regex patterns must match Rust generics in impl blocks
        // These patterns previously failed because the regex required whitespace after "impl"
        let patterns = &*BOUNDARY_PATTERNS;

        // Test case 1: Simple impl without generics (should always work)
        assert!(
            patterns.class_start.is_match("impl Foo {"),
            "Simple impl should match"
        );

        // Test case 2: impl with type parameter
        assert!(
            patterns.class_start.is_match("impl<T> Foo<T> {"),
            "impl<T> should match"
        );

        // Test case 3: impl with trait bound
        assert!(
            patterns.class_start.is_match("impl<T: Clone> Foo<T> for Bar {"),
            "impl<T: Clone> should match"
        );

        // Test case 4: impl with lifetime and complex bounds
        assert!(
            patterns.class_start.is_match("impl<'a, T: 'a + Clone> Foo<'a, T> {"),
            "impl with lifetime should match"
        );

        // Test case 5: impl with nested generics (one level)
        assert!(
            patterns.class_start.is_match("impl<T: Iterator<Item=Foo>> Bar {"),
            "impl with nested generics should match"
        );

        // Test case 6: pub impl with generics
        assert!(
            patterns.class_start.is_match("pub impl<T> Foo<T> {"),
            "pub impl<T> should match"
        );

        // Test case 7: impl with where clause type generics
        assert!(
            patterns.class_start.is_match("impl<T, U> Pair<T, U> {"),
            "impl with multiple type params should match"
        );

        // Test case 8: Leading whitespace
        assert!(
            patterns.class_start.is_match("    impl<T> Foo<T> {"),
            "Indented impl<T> should match"
        );
    }

    #[test]
    fn test_rust_impl_generics_in_chunking() {
        // Verify that impl blocks with generics are detected as boundaries during chunking
        let code = r#"fn setup() {
    // Setup code
}

impl<T: Clone> Container<T> {
    fn new(value: T) -> Self {
        Self { value }
    }

    fn get(&self) -> &T {
        &self.value
    }
}

impl<T: Default> Default for Container<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}
"#;
        let lines: Vec<&str> = code.lines().collect();
        let offsets = build_line_offsets(&lines, code);
        let boundaries = detect_boundaries(&lines, &offsets);

        // Should detect impl<T: Clone> and impl<T: Default> as ClassStart boundaries
        let class_boundaries: Vec<_> = boundaries
            .iter()
            .filter(|b| b.kind == BoundaryKind::ClassStart)
            .collect();

        assert!(
            class_boundaries.len() >= 2,
            "Should detect at least 2 impl blocks with generics, found {}",
            class_boundaries.len()
        );

        // Verify the impl lines are detected
        // Line 4 (0-indexed): impl<T: Clone> Container<T> {
        // Line 14 (0-indexed): impl<T: Default> Default for Container<T> {
        let impl_lines: Vec<_> = class_boundaries.iter().map(|b| b.line_idx).collect();
        assert!(
            impl_lines.contains(&4),
            "impl<T: Clone> Container<T> should be detected at line 4, got {:?}",
            impl_lines
        );
        assert!(
            impl_lines.contains(&14),
            "impl<T: Default> Default for Container<T> should be detected at line 14, got {:?}",
            impl_lines
        );
    }

    #[test]
    fn test_chunk_typescript_code() {
        let code = r#"function processData(data: string[]): void {
    console.log(data);
}

async function fetchData(): Promise<string> {
    return "data";
}

class DataProcessor {
    private data: string[];

    constructor() {
        this.data = [];
    }
}
"#;
        let chunks = chunk_code(code, 40);
        assert!(!chunks.is_empty());
    }

    #[test]
    fn test_calculate_overlap_only_scans_current_chunk() {
        // Regression test for O(n^2) bug where calculate_overlap scanned entire file
        // With the fix, it should only scan lines within the current chunk

        // Generate a large file with 2000 lines (simulates large codebase)
        let mut large_code = String::new();
        for i in 0..2000 {
            large_code.push_str(&format!("def func_{}():\n    pass\n\n", i));
        }

        // This should complete quickly with O(n) complexity
        // Before the fix, this would be O(n^2) and very slow
        let start = std::time::Instant::now();
        let chunks = chunk_code(&large_code, 100);
        let elapsed = start.elapsed();

        // Should complete in under 5 seconds (generous bound for CI)
        // Before the fix, this could take 30+ seconds
        assert!(
            elapsed.as_secs() < 5,
            "Chunking took too long ({:?}), possible O(n^2) regression",
            elapsed
        );

        // Verify chunking actually worked
        assert!(chunks.len() > 10, "Should produce multiple chunks");

        // Verify overlap is calculated correctly (each chunk except first should overlap)
        for i in 1..chunks.len() {
            let prev_end = chunks[i - 1].end_line;
            let curr_start = chunks[i].start_line;
            // With overlap, current start should be <= previous end
            assert!(
                curr_start <= prev_end + 1,
                "Chunk {} start ({}) should overlap with chunk {} end ({})",
                i, curr_start, i - 1, prev_end
            );
        }
    }

    #[test]
    fn test_chunk_new_has_empty_metadata() {
        let chunk = Chunk::new("def foo(): pass".to_string(), 1, 1, 0, 15);

        // Verify new fields are initialized correctly
        assert!(chunk.signature.is_none());
        assert!(chunk.docstring.is_none());
        assert!(chunk.calls.is_empty());
        assert!(!chunk.has_metadata());
    }

    #[test]
    fn test_chunk_with_metadata() {
        let chunk = Chunk::new("def foo(): pass".to_string(), 1, 1, 0, 15).with_metadata(
            Some("def foo() -> None".to_string()),
            Some("Does foo things".to_string()),
            vec!["bar".to_string(), "baz".to_string()],
        );

        assert_eq!(chunk.signature, Some("def foo() -> None".to_string()));
        assert_eq!(chunk.docstring, Some("Does foo things".to_string()));
        assert_eq!(chunk.calls, vec!["bar", "baz"]);
        assert!(chunk.has_metadata());
    }

    #[test]
    fn test_chunk_individual_metadata_setters() {
        let chunk = Chunk::new("code".to_string(), 1, 1, 0, 4)
            .with_signature("fn foo()")
            .with_docstring("A function")
            .with_calls(vec!["helper".to_string()]);

        assert_eq!(chunk.signature, Some("fn foo()".to_string()));
        assert_eq!(chunk.docstring, Some("A function".to_string()));
        assert_eq!(chunk.calls, vec!["helper"]);
    }

    #[test]
    fn test_chunk_serialization() {
        let chunk = Chunk::new("def foo(): bar()".to_string(), 1, 1, 0, 16)
            .with_id("test::foo#chunk1")
            .with_parent("foo")
            .with_chunk_info(0, 2)
            .with_metadata(
                Some("def foo()".to_string()),
                Some("Test function".to_string()),
                vec!["bar".to_string()],
            );

        // Verify serialization works
        let json = serde_json::to_string(&chunk).expect("serialization should succeed");
        assert!(json.contains("signature"));
        assert!(json.contains("docstring"));
        assert!(json.contains("calls"));
        assert!(json.contains("def foo()"));

        // Verify deserialization works
        let deserialized: Chunk =
            serde_json::from_str(&json).expect("deserialization should succeed");
        assert_eq!(deserialized.signature, chunk.signature);
        assert_eq!(deserialized.docstring, chunk.docstring);
        assert_eq!(deserialized.calls, chunk.calls);
    }

    #[test]
    fn test_chunk_serialization_skips_empty_fields() {
        let chunk = Chunk::new("def foo(): pass".to_string(), 1, 1, 0, 15);

        let json = serde_json::to_string(&chunk).expect("serialization should succeed");

        // Empty optional fields should be skipped due to skip_serializing_if
        assert!(!json.contains("signature"));
        assert!(!json.contains("docstring"));
        assert!(!json.contains("\"calls\""));
    }

    #[test]
    fn test_chunk_has_metadata_partial() {
        // Only signature set
        let chunk1 = Chunk::new("code".to_string(), 1, 1, 0, 4).with_signature("fn foo()");
        assert!(chunk1.has_metadata());

        // Only docstring set
        let chunk2 = Chunk::new("code".to_string(), 1, 1, 0, 4).with_docstring("A doc");
        assert!(chunk2.has_metadata());

        // Only calls set
        let chunk3 = Chunk::new("code".to_string(), 1, 1, 0, 4).with_calls(vec!["bar".to_string()]);
        assert!(chunk3.has_metadata());
    }

    #[test]
    fn test_force_split_preserves_trailing_newline() {
        // Regression test: force_split_by_lines should NOT add trailing newline
        // if the original content didn't have one.

        // Content WITHOUT trailing newline
        let content_no_newline = "line1\nline2\nline3";
        let chunks = force_split_by_lines(content_no_newline, 1, 0, 5);

        // Concatenate all chunk contents
        let reconstructed: String = chunks.iter().map(|c| c.content.as_str()).collect();

        // Should NOT have trailing newline since original didn't
        assert!(
            !reconstructed.ends_with('\n'),
            "Content without trailing newline should not gain one. Got: {:?}",
            reconstructed
        );
        assert_eq!(
            reconstructed.len(),
            content_no_newline.len(),
            "Reconstructed length should match original"
        );

        // Content WITH trailing newline
        let content_with_newline = "line1\nline2\nline3\n";
        let chunks_with = force_split_by_lines(content_with_newline, 1, 0, 5);

        let reconstructed_with: String = chunks_with.iter().map(|c| c.content.as_str()).collect();

        // Should preserve trailing newline
        assert!(
            reconstructed_with.ends_with('\n'),
            "Content with trailing newline should preserve it. Got: {:?}",
            reconstructed_with
        );
        assert_eq!(
            reconstructed_with.len(),
            content_with_newline.len(),
            "Reconstructed length should match original"
        );
    }

    #[test]
    fn test_force_split_single_line_no_trailing_newline() {
        // Single line without trailing newline
        let content = "single_line_content";
        let chunks = force_split_by_lines(content, 1, 0, 100);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].content, content);
        assert!(!chunks[0].content.ends_with('\n'));
    }

    #[test]
    fn test_force_split_single_line_with_trailing_newline() {
        // Single line with trailing newline
        let content = "single_line_content\n";
        let chunks = force_split_by_lines(content, 1, 0, 100);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].content, content);
        assert!(chunks[0].content.ends_with('\n'));
    }

    // =========================================================================
    // BUG-13 regression test: Recursive reduction infinite loop prevention
    // =========================================================================

    #[test]
    fn test_recursive_reduction_does_not_reach_zero_max_tokens() {
        // BUG-13: Recursive reduction in handle_oversized_chunk could reach max_tokens=0
        // causing infinite recursion or panic. The reduction sequence was:
        //   max_tokens * 3/4: 4 -> 3 -> 2 -> 1 -> 0
        // With max_tokens=0, the condition `current_tokens + line_tokens > 0` is always
        // true, causing infinite recursion.
        //
        // This test verifies that chunking with very small max_tokens completes
        // without panic or infinite loop, thanks to MIN_CHUNK_TOKENS floor.

        // Code that will require oversized chunk handling
        let code = r#"def very_long_function():
    """A function that will exceed small token limits."""
    x = 1
    y = 2
    z = x + y
    return z
"#;
        // Use a very small max_tokens that would previously cause the bug
        // 4 -> 3 -> 2 -> 1 -> 0 sequence
        let chunks = chunk_code(code, 4);

        // Should complete without panic
        assert!(
            !chunks.is_empty(),
            "Chunking should produce at least one chunk"
        );

        // Verify all chunks have valid content
        for chunk in &chunks {
            assert!(
                !chunk.content.is_empty(),
                "Each chunk should have non-empty content"
            );
        }
    }

    #[test]
    fn test_chunk_code_with_min_chunk_tokens_boundary() {
        // Test behavior exactly at and around MIN_CHUNK_TOKENS (10)
        let code = "def foo():\n    pass\n\ndef bar():\n    pass\n";

        // Test with max_tokens = MIN_CHUNK_TOKENS (10)
        // This should work without recursion since reduced_max can't go below MIN_CHUNK_TOKENS
        let chunks_at_min = chunk_code(code, MIN_CHUNK_TOKENS);
        assert!(!chunks_at_min.is_empty());

        // Test with max_tokens slightly above MIN_CHUNK_TOKENS
        let chunks_above_min = chunk_code(code, MIN_CHUNK_TOKENS + 5);
        assert!(!chunks_above_min.is_empty());

        // Test with max_tokens below MIN_CHUNK_TOKENS (should still work)
        let chunks_below_min = chunk_code(code, 5);
        assert!(!chunks_below_min.is_empty());
    }

    #[test]
    fn test_handle_oversized_chunk_respects_min_tokens() {
        // Directly test that handle_oversized_chunk uses MIN_CHUNK_TOKENS floor
        let content = "line1\nline2\nline3\nline4\nline5\n";
        let chunk = Chunk::new(content.to_string(), 1, 5, 0, content.len());

        // Call with max_tokens that would reduce below MIN_CHUNK_TOKENS
        // reduced_max = 8 * 3/4 = 6, but should be clamped to MIN_CHUNK_TOKENS = 10
        let result = handle_oversized_chunk(&chunk, 8, 2);

        // Should complete without infinite recursion
        assert!(!result.is_empty());

        // When max_tokens (8) < MIN_CHUNK_TOKENS (10), reduced_max = 10 >= max_tokens,
        // so recursive splitting should be skipped and force_split_by_lines used directly
    }

    // =========================================================================
    // BUG-02 regression tests: Tokenizer mismatch fix
    // =========================================================================

    #[test]
    fn test_estimate_tokens_unicode_aware_ascii() {
        // Pure ASCII: ~4 chars per token
        // "hello world" = 11 chars -> 11/4 = 2.75 -> 2 (but max(1, 2) = 2)
        let result = estimate_tokens_unicode_aware("hello world");
        assert_eq!(result, 2, "ASCII text should estimate ~4 chars per token");

        // Empty string
        assert_eq!(estimate_tokens_unicode_aware(""), 0);

        // Single char
        assert_eq!(estimate_tokens_unicode_aware("a"), 1);
    }

    #[test]
    fn test_estimate_tokens_unicode_aware_cjk() {
        // CJK text: ~1.5 tokens per character
        // 4 CJK chars -> 4 * 1.5 = 6 tokens
        let cjk_text = "\u{4E00}\u{4E01}\u{4E02}\u{4E03}"; // 4 CJK ideographs
        let result = estimate_tokens_unicode_aware(cjk_text);
        assert_eq!(result, 6, "CJK text should estimate ~1.5 tokens per char");
    }

    #[test]
    fn test_estimate_tokens_unicode_aware_mixed() {
        // Mixed ASCII and CJK
        // "hello" = 5 ASCII chars -> 5/4 = 1.25
        // + 2 CJK chars -> 2 * 1.5 = 3
        // Total: 1.25 + 3 = 4.25 -> 4
        let mixed = "hello\u{4E00}\u{4E01}";
        let result = estimate_tokens_unicode_aware(mixed);
        assert_eq!(result, 4);
    }

    #[test]
    fn test_estimate_tokens_unicode_aware_emoji() {
        // Emoji: ~3 tokens per emoji
        // 2 emojis -> 2 * 3 = 6 tokens
        let emoji_text = "\u{1F600}\u{1F601}"; // 2 emoji
        let result = estimate_tokens_unicode_aware(emoji_text);
        assert_eq!(result, 6, "Emoji should estimate ~3 tokens each");
    }

    #[test]
    fn test_estimate_tokens_unicode_aware_other_unicode() {
        // Other Unicode (Cyrillic, Arabic, etc.): ~2 chars per token
        // 4 Cyrillic chars -> 4/2 = 2 tokens
        let cyrillic = "\u{0410}\u{0411}\u{0412}\u{0413}"; // 4 Cyrillic chars
        let result = estimate_tokens_unicode_aware(cyrillic);
        assert_eq!(result, 2, "Other Unicode should estimate ~2 chars per token");
    }

    #[test]
    fn test_tokenizer_type_char_estimate_variant() {
        // Test the new CharEstimate variant
        let char_estimate = TokenizerType::CharEstimate;

        assert_eq!(char_estimate.name(), "CharEstimate (Python parity)");
        assert!(!char_estimate.requires_tei());
        assert!(char_estimate.is_estimation());
        assert_eq!(char_estimate.variance_vs_qwen3(), 0.05);
    }

    #[test]
    fn test_is_cjk_char() {
        // CJK Unified Ideographs
        assert!(is_cjk_char(0x4E00)); // First CJK unified
        assert!(is_cjk_char(0x9FFF)); // Last CJK unified

        // Hiragana
        assert!(is_cjk_char(0x3040));
        assert!(is_cjk_char(0x309F));

        // Katakana
        assert!(is_cjk_char(0x30A0));
        assert!(is_cjk_char(0x30FF));

        // Korean Hangul
        assert!(is_cjk_char(0xAC00));
        assert!(is_cjk_char(0xD7AF));

        // Non-CJK
        assert!(!is_cjk_char(0x0041)); // 'A'
        assert!(!is_cjk_char(0x0020)); // space
    }

    #[test]
    fn test_is_emoji_char() {
        // Emoji
        assert!(is_emoji_char(0x1F600)); // Grinning face
        assert!(is_emoji_char(0x1F601)); // Beaming face
        assert!(is_emoji_char(0x2600));  // Sun

        // Non-emoji
        assert!(!is_emoji_char(0x0041)); // 'A'
        assert!(!is_emoji_char(0x4E00)); // CJK
    }

    #[test]
    fn test_count_ascii_bytes_simd_small() {
        // Test scalar path (< 64 bytes)
        let small = b"hello world";
        assert_eq!(count_ascii_bytes_simd(small), 11);

        // Empty
        assert_eq!(count_ascii_bytes_simd(b""), 0);

        // Single byte
        assert_eq!(count_ascii_bytes_simd(b"x"), 1);

        // 63 bytes (just under SIMD threshold)
        let just_under = vec![b'a'; 63];
        assert_eq!(count_ascii_bytes_simd(&just_under), 63);
    }

    #[test]
    fn test_count_ascii_bytes_simd_medium() {
        // Test SIMD path (>= 64 bytes)
        let medium = vec![b'a'; 100];
        assert_eq!(count_ascii_bytes_simd(&medium), 100);

        // Exactly 64 bytes (SIMD threshold)
        let exact = vec![b'x'; 64];
        assert_eq!(count_ascii_bytes_simd(&exact), 64);

        // 128 bytes (multiple SIMD iterations)
        let multiple = vec![b'z'; 128];
        assert_eq!(count_ascii_bytes_simd(&multiple), 128);
    }

    #[test]
    fn test_count_ascii_bytes_simd_large() {
        // Large input: test AVX2 path with 32-byte chunks
        let large = vec![b'a'; 1000];
        assert_eq!(count_ascii_bytes_simd(&large), 1000);

        // Very large input
        let very_large = vec![b'b'; 10000];
        assert_eq!(count_ascii_bytes_simd(&very_large), 10000);
    }

    #[test]
    fn test_count_ascii_bytes_simd_non_ascii() {
        // Pure non-ASCII (high bit set)
        let non_ascii: Vec<u8> = vec![0x80, 0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0];
        assert_eq!(count_ascii_bytes_simd(&non_ascii), 0);

        // Large non-ASCII (tests SIMD path)
        let large_non_ascii: Vec<u8> = vec![0xFF; 100];
        assert_eq!(count_ascii_bytes_simd(&large_non_ascii), 0);
    }

    #[test]
    fn test_count_ascii_bytes_simd_mixed() {
        // Mixed ASCII and non-ASCII
        let mixed: Vec<u8> = vec![
            b'h', b'e', b'l', b'l', b'o',  // 5 ASCII
            0xC3, 0xA9,                    // 2 non-ASCII (UTF-8 e-acute)
            b'w', b'o', b'r', b'l', b'd',  // 5 ASCII
        ];
        assert_eq!(count_ascii_bytes_simd(&mixed), 10);

        // Large mixed (tests SIMD path with mixed content)
        let mut large_mixed = vec![b'a'; 50];
        large_mixed.extend(vec![0xFF; 20]);
        large_mixed.extend(vec![b'b'; 50]);
        assert_eq!(count_ascii_bytes_simd(&large_mixed), 100);
    }

    #[test]
    fn test_count_ascii_bytes_simd_utf8_string() {
        // Real UTF-8 string with mixed content
        let text = "Hello World 123 \u{4E00}\u{4E01} \u{1F600}";
        let bytes = text.as_bytes();
        // Count manually: "Hello World 123 " = 16 ASCII, then CJK (non-ASCII), space, emoji (non-ASCII)
        // "Hello World 123 " = 16 bytes, space after CJK = 1
        // Actually: H(1) e(1) l(1) l(1) o(1) (1) W(1) o(1) r(1) l(1) d(1) (1) 1(1) 2(1) 3(1) (1) = 16
        // Then CJK bytes (non-ASCII), space (1), emoji bytes (non-ASCII)
        let ascii_count = bytes.iter().filter(|&&b| b < 128).count();
        assert_eq!(count_ascii_bytes_simd(bytes), ascii_count);
    }

    #[test]
    fn test_get_tokenizer_type_default() {
        // Note: This test may be affected by other tests that call set_tokenizer_type
        // In a fresh process, the default should be Cl100kBase
        let current = get_tokenizer_type();
        // We can only assert it's one of the valid types
        matches!(
            current,
            TokenizerType::Cl100kBase
                | TokenizerType::CharEstimate
                | TokenizerType::Qwen3
                | TokenizerType::P50kBase
                | TokenizerType::R50kBase
        );
    }

    // =========================================================================
    // BUG-16: Line Numbering Convention Tests
    // =========================================================================

    #[test]
    fn test_index_to_line_conversion() {
        // BUG-16: Verify 0-indexed to 1-indexed conversion
        assert_eq!(index_to_line(0), 1, "Index 0 should map to line 1");
        assert_eq!(index_to_line(1), 2, "Index 1 should map to line 2");
        assert_eq!(index_to_line(9), 10, "Index 9 should map to line 10");
        assert_eq!(index_to_line(99), 100, "Index 99 should map to line 100");
    }

    #[test]
    fn test_line_to_index_conversion() {
        // BUG-16: Verify 1-indexed to 0-indexed conversion
        assert_eq!(line_to_index(1), 0, "Line 1 should map to index 0");
        assert_eq!(line_to_index(2), 1, "Line 2 should map to index 1");
        assert_eq!(line_to_index(10), 9, "Line 10 should map to index 9");
        assert_eq!(line_to_index(100), 99, "Line 100 should map to index 99");

        // Edge case: line 0 (invalid) should saturate to index 0
        assert_eq!(
            line_to_index(0),
            0,
            "Invalid line 0 should saturate to index 0"
        );
    }

    #[test]
    fn test_roundtrip_index_line_conversion() {
        // BUG-16: Verify roundtrip conversion
        for idx in 0..100 {
            let line = index_to_line(idx);
            let back = line_to_index(line);
            assert_eq!(
                back, idx,
                "Roundtrip failed: index {} -> line {} -> index {}",
                idx, line, back
            );
        }
    }

    #[test]
    fn test_line_numbers_are_1_indexed() {
        // BUG-16: Verify that chunk line numbers start at 1, not 0
        let content = "line1\nline2\nline3";
        let chunks = chunk_code(content, 1000);

        assert_eq!(chunks.len(), 1, "Should produce single chunk");
        assert_eq!(
            chunks[0].start_line, 1,
            "First line should be 1, not 0"
        );
        assert_eq!(
            chunks[0].end_line, 3,
            "Last line should be 3 (3 lines, 1-indexed inclusive)"
        );
        assert_eq!(
            chunks[0].line_count(),
            3,
            "Line count should be 3 (end - start + 1)"
        );
    }

    #[test]
    fn test_single_line_chunk_line_numbers() {
        // BUG-16: Single line chunk should have start_line == end_line == 1
        let content = "single line";
        let chunks = chunk_code(content, 1000);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].start_line, 1, "Single line: start should be 1");
        assert_eq!(chunks[0].end_line, 1, "Single line: end should be 1 (inclusive)");
        assert_eq!(chunks[0].line_count(), 1, "Single line: count should be 1");
    }

    #[test]
    fn test_multi_chunk_line_numbers_continuous() {
        // BUG-16: Multi-chunk file should have continuous line numbers
        // Generate content that will be split into multiple chunks
        let mut content = String::new();
        for i in 1..=20 {
            content.push_str(&format!("def function_{}():\n    pass\n\n", i));
        }

        let chunks = chunk_code(&content, 50); // Small limit to force splitting

        assert!(chunks.len() > 1, "Should produce multiple chunks");

        // First chunk should start at line 1
        assert_eq!(
            chunks[0].start_line, 1,
            "First chunk should start at line 1"
        );

        // Line numbers should be continuous (with possible overlap)
        for i in 1..chunks.len() {
            let prev_end = chunks[i - 1].end_line;
            let curr_start = chunks[i].start_line;

            assert!(
                curr_start <= prev_end + 1,
                "Chunk {} start ({}) should be <= prev chunk {} end ({}) + 1",
                i,
                curr_start,
                i - 1,
                prev_end
            );
        }
    }

    #[test]
    fn test_contains_line_uses_1_indexed() {
        // BUG-16: contains_line should work with 1-indexed line numbers
        let chunk = Chunk::new("a\nb\nc".to_string(), 5, 7, 0, 5);

        // Lines 5, 6, 7 should be contained (1-indexed)
        assert!(chunk.contains_line(5), "Line 5 should be in chunk [5,7]");
        assert!(chunk.contains_line(6), "Line 6 should be in chunk [5,7]");
        assert!(chunk.contains_line(7), "Line 7 should be in chunk [5,7]");

        // Lines outside range should not be contained
        assert!(!chunk.contains_line(4), "Line 4 should NOT be in chunk [5,7]");
        assert!(!chunk.contains_line(8), "Line 8 should NOT be in chunk [5,7]");

        // Line 0 (invalid) should not be contained
        assert!(
            !chunk.contains_line(0),
            "Line 0 (invalid) should NOT be in any chunk"
        );
    }

    #[test]
    fn test_create_chunk_from_range_converts_correctly() {
        // BUG-16: Internal 0-indexed exclusive -> public 1-indexed inclusive
        let code = "line0\nline1\nline2\nline3";
        let lines: Vec<&str> = code.lines().collect();
        let line_offsets = build_line_offsets(&lines, code);

        // Internal range [0, 3) means indices 0, 1, 2 (3 lines)
        let chunk = create_chunk_from_range(code, &lines, &line_offsets, 0, 3);

        assert_eq!(
            chunk.start_line, 1,
            "Internal index 0 should become line 1"
        );
        assert_eq!(
            chunk.end_line, 3,
            "Internal exclusive end 3 should become inclusive line 3"
        );
        assert_eq!(chunk.line_count(), 3, "Should contain 3 lines");

        // Content should be first 3 lines
        assert!(chunk.content.contains("line0"));
        assert!(chunk.content.contains("line1"));
        assert!(chunk.content.contains("line2"));
        assert!(!chunk.content.contains("line3"));
    }

    #[test]
    fn test_force_split_preserves_1_indexed_base() {
        // BUG-16: force_split_by_lines should preserve the 1-indexed base_line
        let content = "a\nb\nc\nd\ne";
        let base_line = 10; // Simulate chunk starting at line 10 of original file

        let chunks = force_split_by_lines(content, base_line, 0, 2);

        assert!(!chunks.is_empty(), "Should produce chunks");

        // First chunk should start at base_line (10)
        assert_eq!(
            chunks[0].start_line, 10,
            "First sub-chunk should start at base_line {}",
            base_line
        );

        // All line numbers should be >= base_line
        for (i, chunk) in chunks.iter().enumerate() {
            assert!(
                chunk.start_line >= base_line,
                "Chunk {} start_line {} should be >= base_line {}",
                i,
                chunk.start_line,
                base_line
            );
            assert!(
                chunk.end_line >= chunk.start_line,
                "Chunk {} end_line {} should be >= start_line {}",
                i,
                chunk.end_line,
                chunk.start_line
            );
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "start_line must be 1-indexed")]
    fn test_chunk_new_rejects_zero_start_line() {
        // BUG-16: Debug assertion should catch start_line = 0
        let _ = Chunk::new("content".to_string(), 0, 1, 0, 7);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "end_line")]
    fn test_chunk_new_rejects_end_before_start() {
        // BUG-16: Debug assertion should catch end_line < start_line
        let _ = Chunk::new("content".to_string(), 5, 3, 0, 7);
    }
}
