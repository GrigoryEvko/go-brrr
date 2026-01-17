//! Embedding and vector index support for semantic search.
//!
//! This module provides:
//!
//! - **TEI Client** ([`tei_client`]): High-performance gRPC client for
//!   text-embeddings-inference with connection pooling and batching
//! - **Vector Index** ([`index`]): HNSW-based approximate nearest neighbor
//!   search using usearch
//!
//! # Integration with Semantic Search
//!
//! The typical workflow is:
//!
//! 1. Extract code units using [`semantic::extract_units`](crate::semantic::extract_units)
//! 2. Generate embeddings using [`TeiClient`]
//! 3. Store embeddings in [`VectorIndex`] with unit indices as keys
//! 4. Store metadata (units) in a separate JSON file
//! 5. Search returns keys which map back to units
//!
//! # Example
//!
//! ```no_run
//! use go_brrr::embedding::{VectorIndex, IndexConfig, Metric};
//!
//! // Create index matching your embedding model dimensions
//! let config = IndexConfig::new(768)  // MiniLM dimensions
//!     .with_metric(Metric::InnerProduct);
//!
//! let index = VectorIndex::with_config(config)?;
//!
//! // Reserve capacity for performance
//! index.reserve(10000)?;
//!
//! // Add embeddings (keys correspond to EmbeddingUnit indices)
//! for (i, embedding) in embeddings.iter().enumerate() {
//!     index.add(i as u64, embedding)?;
//! }
//!
//! // Search
//! let results = index.search(&query_embedding, 10)?;
//! for (key, distance) in results {
//!     let score = 1.0 - distance;  // Convert to similarity
//!     println!("Unit {}: score {:.3}", key, score);
//! }
//!
//! // Persist
//! index.save("./index.usearch")?;
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! # Metric Selection
//!
//! - Use [`Metric::InnerProduct`] for pre-normalized embeddings (most models)
//! - Use [`Metric::Cosine`] if your embeddings aren't normalized
//! - Use [`Metric::L2Squared`] for absolute distance comparisons

pub mod index;
mod tei_client;

// =============================================================================
// TEI Client Re-exports
// =============================================================================

pub use tei_client::{
    EmbedMetadata, ModelType, RerankResult, ServerInfo, SparseEmbedding, SparseValue, TeiClient,
    TeiClientConfig, TeiError, Token,
};

// =============================================================================
// Vector Index Re-exports
// =============================================================================

pub use index::{
    clear_query_cache, distances_to_scores, distances_to_scores_for_metric,
    get_cached_query_embedding, get_cached_query_embedding_async, is_normalized, is_valid_vector,
    normalize_vector, normalize_vector_or_original, query_cache_stats, query_in_cache, IndexConfig,
    IndexView, Metric, Quantization, SaveInfo, VectorIndex,
};

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_index_types_exported() {
        // Verify public types are accessible
        fn _assert_types() {
            let _: Option<VectorIndex> = None;
            let _: Option<IndexConfig> = None;
            let _: Option<IndexView> = None;
            let _: Metric = Metric::InnerProduct;
            let _: Quantization = Quantization::F32;
        }
    }

    #[test]
    fn test_utility_functions_exported() {
        // Verify public functions are accessible
        fn _assert_functions() {
            let _ = distances_to_scores as fn(&[f32]) -> Vec<f32>;
            let _ = distances_to_scores_for_metric as fn(&[f32], Metric) -> Vec<f32>;
            let _ = normalize_vector as fn(&[f32]) -> Option<Vec<f32>>;
            let _ = normalize_vector_or_original as fn(Vec<f32>) -> Vec<f32>;
            let _ = is_valid_vector as fn(&[f32]) -> bool;
            let _ = is_normalized as fn(&[f32], f32) -> bool;
        }
    }
}
