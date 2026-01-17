//! Semantic search and embedding support.
//!
//! This module provides vector-based semantic code search using embeddings.
//! It extracts code units (functions, classes, methods) from source files,
//! enriches them with semantic metadata, and prepares them for embedding.
//!
//! # Architecture
//!
//! The semantic module mirrors the Python implementation in `brrr/semantic.py`:
//!
//! - **Types** ([`types`]): Core data structures for embedding units and search results
//! - **Extractor** ([`extractor`]): Code extraction, pattern detection, and chunking
//!
//! # Quick Start
//!
//! ```no_run
//! use go_brrr::semantic::{extract_units, EmbeddingUnit, UnitKind};
//!
//! // Extract all units from a Python project
//! let units = extract_units("./my_project", "python")?;
//!
//! for unit in &units {
//!     println!("{}: {} ({} tokens)",
//!         unit.kind,
//!         unit.name,
//!         unit.token_count
//!     );
//! }
//! # Ok::<(), go_brrr::BrrrError>(())
//! ```
//!
//! # Chunking Oversized Units
//!
//! Units larger than 8K tokens are automatically split into chunks:
//!
//! ```no_run
//! use go_brrr::semantic::{extract_units, MAX_EMBEDDING_TOKENS};
//!
//! let units = extract_units("./large_project", "typescript")?;
//!
//! for unit in units.iter().filter(|u| u.is_chunk()) {
//!     println!("Chunk {}/{} of {}",
//!         unit.chunk_index + 1,
//!         unit.chunk_total,
//!         unit.parent.as_deref().unwrap_or("unknown")
//!     );
//! }
//! # Ok::<(), go_brrr::BrrrError>(())
//! ```
//!
//! # Semantic Pattern Detection
//!
//! Code is automatically tagged with semantic patterns:
//!
//! ```no_run
//! use go_brrr::semantic::{detect_semantic_patterns, build_embedding_text};
//!
//! let code = "def validate_user(user): assert user is not None";
//! let patterns = detect_semantic_patterns(code);
//! // patterns contains ["validation"]
//! ```
//!
//! # Token Counting
//!
//! Uses tiktoken (cl100k_base) for accurate token counting:
//!
//! ```
//! use go_brrr::semantic::{count_tokens, truncate_to_tokens};
//!
//! let text = "Some code to embed";
//! let tokens = count_tokens(text);
//!
//! // Truncate to fit embedding limit
//! let truncated = truncate_to_tokens(text, 1000);
//! ```

pub mod chunker;
pub mod extractor;
pub mod types;

// =============================================================================
// Type Re-exports
// =============================================================================

// Core types
pub use types::{
    ChunkInfo, CodeComplexity, CodeLocation, ContentHashedIndex, EmbeddingUnit, SearchResult,
    SemanticPattern, UnitKind,
};

// Constants
pub use types::{
    CHUNK_OVERLAP_TOKENS, MAX_CODE_PREVIEW_TOKENS, MAX_EMBEDDING_TOKENS, SEMANTIC_PATTERNS,
};

// =============================================================================
// Function Re-exports
// =============================================================================

// Main extraction API
pub use extractor::{extract_units, extract_units_from_file, extract_units_with_callgraph};

// Unit cache management
pub use extractor::{
    clear_unit_cache, invalidate_unit_cache, invalidate_unit_cache_matching, unit_cache_stats,
};

// Token operations
pub use extractor::{count_tokens, truncate_to_tokens};

// Semantic analysis
pub use extractor::{detect_code_complexity, detect_semantic_patterns};

// Chunking
pub use extractor::{chunk_unit, split_into_chunks};

// Unit enrichment
pub use extractor::enrich_unit;

// Embedding text building
pub use extractor::{build_embedding_text, parse_identifier_to_words};

// Advanced chunking (boundary-aware splitting)
pub use chunker::{chunk_code, chunk_code_default, chunk_code_with_overlap, needs_chunking, Chunk};

// Tokenizer configuration and TEI-based token counting (BUG-02 fix)
pub use chunker::{
    compare_tokenizer_counts, count_tokens_batch_tei, count_tokens_tei,
    estimate_tokens_unicode_aware, get_tokenizer_type, set_tokenizer_type,
    ChunkConfig, TokenizerType,
};

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_public_types_exported() {
        // Verify all public types are accessible
        fn _assert_types() {
            let _: Option<EmbeddingUnit> = None;
            let _: Option<SearchResult> = None;
            let _: Option<UnitKind> = None;
            let _: Option<CodeComplexity> = None;
            let _: Option<ChunkInfo> = None;
            let _: Option<SemanticPattern> = None;
            let _: Option<ContentHashedIndex> = None;
            let _: Option<CodeLocation> = None;
        }
    }

    #[test]
    fn test_constants_exported() {
        assert!(MAX_EMBEDDING_TOKENS > 0);
        assert!(MAX_CODE_PREVIEW_TOKENS > 0);
        assert!(CHUNK_OVERLAP_TOKENS > 0);
        assert!(!SEMANTIC_PATTERNS.is_empty());
    }

    #[test]
    fn test_functions_exported() {
        // Verify all public functions are callable
        fn _assert_functions() {
            let _ = extract_units as fn(&str, &str) -> crate::error::Result<Vec<EmbeddingUnit>>;
            let _ = extract_units_from_file as fn(&str) -> crate::error::Result<Vec<EmbeddingUnit>>;
            let _ = count_tokens as fn(&str) -> usize;
            let _ = truncate_to_tokens as fn(&str, usize) -> String;
            let _ = detect_semantic_patterns as fn(&str) -> Vec<String>;
            let _ = detect_code_complexity as fn(&str) -> CodeComplexity;
            let _ = split_into_chunks as fn(&str, usize, usize) -> Vec<ChunkInfo>;
            let _ = chunk_unit as fn(&EmbeddingUnit) -> Vec<EmbeddingUnit>;
            let _ = enrich_unit as fn(&mut EmbeddingUnit);
            let _ = build_embedding_text as fn(&EmbeddingUnit) -> String;
            let _ = parse_identifier_to_words as fn(&str) -> String;
        }
    }

    #[test]
    fn test_cache_functions_exported() {
        // Verify cache management functions are callable
        fn _assert_cache_functions() {
            let _ = clear_unit_cache as fn();
            let _ = unit_cache_stats as fn() -> usize;
            let _ = invalidate_unit_cache as fn(&std::path::Path);
        }
    }

    #[test]
    fn test_chunker_functions_exported() {
        // Verify chunker functions are callable
        fn _assert_chunker() {
            let _ = chunk_code as fn(&str, usize) -> Vec<Chunk>;
            let _ = chunk_code_default as fn(&str) -> Vec<Chunk>;
            let _ = chunk_code_with_overlap as fn(&str, usize, usize) -> Vec<Chunk>;
            let _ = needs_chunking as fn(&str, usize) -> bool;
        }
    }

    #[test]
    fn test_chunk_type_exported() {
        // Verify Chunk type is accessible
        fn _assert_chunk_type() {
            let _: Option<Chunk> = None;
        }
    }
}
