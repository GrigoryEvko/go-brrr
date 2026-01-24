//! Clustering for semantic clone detection.
//!
//! Provides transitive closure clustering using union-find to group similar code
//! fragments into clone clusters based on embedding similarity.
//!
//! # Algorithm
//!
//! 1. Start with pairwise similarity pairs from `similarity.rs`
//! 2. Use union-find to compute transitive closure (if A~B and B~C, then A~C)
//! 3. Extract connected components as clone clusters
//! 4. Compute cluster centroids as mean embeddings
//!
//! # Performance
//!
//! - Union-find: O(n * alpha(n)) where alpha is inverse Ackermann (~O(n))
//! - Centroid computation: O(k * d) per cluster (k members, d dimensions)
//! - Memory: O(n) for union-find structure
//!
//! # Example
//!
//! ```ignore
//! use go_brrr::quality::clones::cluster::{cluster_clones, CloneCluster};
//! use go_brrr::quality::clones::similarity::SimilarityPair;
//!
//! let pairs = vec![
//!     SimilarityPair::new(0, 1, 0.95),
//!     SimilarityPair::new(1, 2, 0.90),  // Transitively connects 0, 1, 2
//!     SimilarityPair::new(3, 4, 0.88),  // Separate cluster
//! ];
//! let embeddings = vec![...];
//!
//! let clusters = cluster_clones(&pairs, &embeddings, 0.85);
//! // Returns 2 clusters: {0, 1, 2} and {3, 4}
//! ```

use std::path::PathBuf;

use anyhow::Result;
use fixedbitset::FixedBitSet;
use fxhash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use super::similarity::SimilarityPair;
use crate::embedding::VectorIndex;

// =============================================================================
// UNION-FIND DATA STRUCTURE
// =============================================================================

/// Disjoint-set (union-find) data structure with path compression and union by rank.
///
/// Provides near-constant time operations for finding set representatives
/// and merging sets.
struct UnionFind {
    /// Parent pointers. parent[i] = i means i is a root.
    parent: Vec<usize>,
    /// Rank (tree depth upper bound) for union by rank.
    rank: Vec<usize>,
}

impl UnionFind {
    /// Create a new union-find structure with n elements.
    ///
    /// Initially, each element is its own set.
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    /// Find the representative (root) of the set containing x.
    ///
    /// Uses path compression for amortized O(alpha(n)) complexity.
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            // Path compression: make all nodes point directly to root
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    /// Merge the sets containing x and y.
    ///
    /// Uses union by rank to keep trees balanced.
    /// Returns true if sets were actually merged (were different).
    fn union(&mut self, x: usize, y: usize) -> bool {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x == root_y {
            return false; // Already in same set
        }

        // Union by rank: attach smaller tree under larger tree
        match self.rank[root_x].cmp(&self.rank[root_y]) {
            std::cmp::Ordering::Less => {
                self.parent[root_x] = root_y;
            }
            std::cmp::Ordering::Greater => {
                self.parent[root_y] = root_x;
            }
            std::cmp::Ordering::Equal => {
                self.parent[root_y] = root_x;
                self.rank[root_x] += 1;
            }
        }

        true
    }

    /// Check if x and y are in the same set.
    fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    /// Extract all sets (connected components) as vectors of indices.
    fn extract_sets(&mut self) -> Vec<Vec<usize>> {
        let n = self.parent.len();
        let mut sets: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

        for i in 0..n {
            let root = self.find(i);
            sets.entry(root).or_default().push(i);
        }

        // Return only sets with more than one element (actual clusters)
        sets.into_values().filter(|s| s.len() > 1).collect()
    }
}

// =============================================================================
// CLONE CLUSTER
// =============================================================================

/// A cluster of semantically similar code fragments.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneCluster {
    /// Indices of cluster members (into the original embedding list).
    pub members: Vec<usize>,

    /// Centroid embedding (mean of all member embeddings).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub centroid: Option<Vec<f32>>,

    /// Average pairwise similarity within the cluster.
    pub cohesion: f32,

    /// Minimum pairwise similarity in the cluster.
    pub min_similarity: f32,

    /// Maximum pairwise similarity in the cluster.
    pub max_similarity: f32,

    /// Optional metadata about cluster members.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub member_info: Vec<ClusterMemberInfo>,
}

/// Information about a cluster member.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterMemberInfo {
    /// Index in the original embedding list.
    pub index: usize,
    /// Optional file path.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file: Option<PathBuf>,
    /// Optional function/method name.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Optional line range.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_range: Option<(usize, usize)>,
}

impl CloneCluster {
    /// Create a new cluster with the given members.
    #[must_use]
    pub fn new(members: Vec<usize>) -> Self {
        Self {
            members,
            centroid: None,
            cohesion: 0.0,
            min_similarity: 0.0,
            max_similarity: 0.0,
            member_info: Vec::new(),
        }
    }

    /// Number of members in this cluster.
    #[must_use]
    pub fn size(&self) -> usize {
        self.members.len()
    }

    /// Check if cluster is non-trivial (has at least 2 members).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.members.len() >= 2
    }

    /// Compute and set the centroid from embeddings.
    pub fn compute_centroid(&mut self, embeddings: &[Vec<f32>]) {
        if self.members.is_empty() {
            return;
        }

        let dim = embeddings
            .get(self.members[0])
            .map(|e| e.len())
            .unwrap_or(0);

        if dim == 0 {
            return;
        }

        // Sum all member embeddings
        let mut centroid = vec![0.0f32; dim];
        let mut count = 0;

        for &idx in &self.members {
            if let Some(emb) = embeddings.get(idx) {
                if emb.len() == dim {
                    for (c, &e) in centroid.iter_mut().zip(emb.iter()) {
                        *c += e;
                    }
                    count += 1;
                }
            }
        }

        // Compute mean
        if count > 0 {
            for c in &mut centroid {
                *c /= count as f32;
            }
        }

        self.centroid = Some(centroid);
    }

    /// Compute cohesion statistics from pairwise similarities.
    pub fn compute_cohesion(&mut self, pairs: &[SimilarityPair]) {
        if self.members.is_empty() {
            return;
        }
        let max_idx = self.members.iter().copied().max().unwrap_or(0);
        let mut member_set = FixedBitSet::with_capacity(max_idx + 1);
        for &idx in &self.members {
            member_set.insert(idx);
        }

        let relevant_pairs: Vec<f32> = pairs
            .iter()
            .filter(|p| {
                p.i < member_set.len()
                    && p.j < member_set.len()
                    && member_set.contains(p.i)
                    && member_set.contains(p.j)
            })
            .map(|p| p.similarity)
            .collect();

        if relevant_pairs.is_empty() {
            return;
        }

        self.cohesion = relevant_pairs.iter().sum::<f32>() / relevant_pairs.len() as f32;
        self.min_similarity = relevant_pairs
            .iter()
            .copied()
            .fold(f32::INFINITY, f32::min);
        self.max_similarity = relevant_pairs
            .iter()
            .copied()
            .fold(f32::NEG_INFINITY, f32::max);
    }
}

// =============================================================================
// CLUSTERING
// =============================================================================

/// Cluster similar code fragments using transitive closure.
///
/// Uses union-find to efficiently compute connected components from pairwise
/// similarity relationships.
///
/// # Arguments
///
/// * `pairs` - Pairwise similarity pairs (typically from `compute_pairwise_similarities`)
/// * `embeddings` - Embedding vectors for all code fragments
/// * `threshold` - Minimum similarity to consider (pairs below this are ignored)
///
/// # Returns
///
/// Vector of `CloneCluster`, each containing indices of similar code fragments.
/// Clusters are sorted by size descending.
///
/// # Example
///
/// ```ignore
/// use go_brrr::quality::clones::cluster::cluster_clones;
/// use go_brrr::quality::clones::similarity::{compute_pairwise_similarities, SimilarityPair};
///
/// let embeddings: Vec<Vec<f32>> = vec![...];
/// let pairs = compute_pairwise_similarities(&embeddings, 0.8);
/// let clusters = cluster_clones(&pairs, &embeddings, 0.8);
///
/// for cluster in &clusters {
///     println!("Cluster with {} members, cohesion: {:.2}",
///         cluster.size(), cluster.cohesion);
/// }
/// ```
pub fn cluster_clones(
    pairs: &[SimilarityPair],
    embeddings: &[Vec<f32>],
    threshold: f32,
) -> Vec<CloneCluster> {
    if embeddings.is_empty() {
        return Vec::new();
    }

    let n = embeddings.len();
    let mut uf = UnionFind::new(n);

    // Union all pairs above threshold
    for pair in pairs {
        if pair.similarity >= threshold && pair.i < n && pair.j < n {
            uf.union(pair.i, pair.j);
        }
    }

    // Extract clusters
    let sets = uf.extract_sets();

    // Build CloneCluster for each set
    let mut clusters: Vec<CloneCluster> = sets
        .into_iter()
        .map(|members| {
            let mut cluster = CloneCluster::new(members);
            cluster.compute_centroid(embeddings);
            cluster.compute_cohesion(pairs);
            cluster
        })
        .filter(|c| c.is_valid())
        .collect();

    // Sort by size descending
    clusters.sort_by(|a, b| b.size().cmp(&a.size()));

    clusters
}

/// Cluster with pre-computed union-find (for incremental updates).
///
/// Useful when you want to add more pairs incrementally without recomputing.
pub fn cluster_with_union_find(
    uf: &mut UnionFind,
    embeddings: &[Vec<f32>],
    pairs: &[SimilarityPair],
) -> Vec<CloneCluster> {
    let sets = uf.extract_sets();

    let mut clusters: Vec<CloneCluster> = sets
        .into_iter()
        .map(|members| {
            let mut cluster = CloneCluster::new(members);
            cluster.compute_centroid(embeddings);
            cluster.compute_cohesion(pairs);
            cluster
        })
        .filter(|c| c.is_valid())
        .collect();

    clusters.sort_by(|a, b| b.size().cmp(&a.size()));
    clusters
}

// =============================================================================
// APPROXIMATE NEAREST NEIGHBOR
// =============================================================================

/// Find similar code fragments using approximate nearest neighbor search.
///
/// Uses usearch HNSW index for O(log n) lookup instead of O(n) brute force.
/// Essential for large codebases where pairwise comparison is prohibitive.
///
/// # Arguments
///
/// * `query` - Query embedding vector
/// * `index` - Pre-built vector index (from `VectorIndex`)
/// * `k` - Maximum number of neighbors to retrieve
/// * `threshold` - Minimum similarity to include (filters results)
///
/// # Returns
///
/// Vector of `(index, similarity)` pairs, sorted by similarity descending.
///
/// # Performance
///
/// - Time: O(log n * ef_search) where n = index size
/// - For 1M vectors: ~1ms per query vs ~1s for brute force
///
/// # Example
///
/// ```ignore
/// use go_brrr::quality::clones::cluster::find_similar_approximate;
/// use go_brrr::embedding::{VectorIndex, Metric};
///
/// let index = VectorIndex::load("./embeddings.usearch")?;
/// let query = vec![0.1, 0.2, 0.3, ...];
///
/// let similar = find_similar_approximate(&query, &index, 10, 0.8)?;
/// for (idx, sim) in &similar {
///     println!("Index {}: similarity {:.3}", idx, sim);
/// }
/// ```
pub fn find_similar_approximate(
    query: &[f32],
    index: &VectorIndex,
    k: usize,
    threshold: f32,
) -> Result<Vec<(usize, f32)>> {
    // Search returns (key, distance) pairs
    // For InnerProduct/Cosine, distance = 1 - similarity
    let results = index.search(query, k)?;

    // Convert distance to similarity and filter by threshold
    let filtered: Vec<(usize, f32)> = results
        .into_iter()
        .map(|(key, distance)| {
            // usearch InnerProduct returns distance = 1 - similarity
            let similarity = 1.0 - distance;
            (key as usize, similarity)
        })
        .filter(|(_, sim)| *sim >= threshold)
        .collect();

    Ok(filtered)
}

/// Find all similar pairs using HNSW index (approximate all-pairs).
///
/// For each embedding, query the index for k nearest neighbors and collect
/// pairs above threshold. Much faster than exact pairwise for large n.
///
/// # Arguments
///
/// * `embeddings` - All embedding vectors
/// * `index` - Pre-built index containing all embeddings
/// * `k` - Number of neighbors to search per query
/// * `threshold` - Minimum similarity to include
///
/// # Returns
///
/// Vector of similarity pairs (deduplicated, i < j).
///
/// # Performance
///
/// - Time: O(n * k * log n) vs O(n^2) for exact pairwise
/// - For n=10000, k=20: ~200ms vs ~minutes
///
/// # Note
///
/// May miss some pairs that exact computation would find (approximate).
/// Increase k for higher recall at cost of speed.
pub fn find_all_similar_approximate(
    embeddings: &[Vec<f32>],
    index: &VectorIndex,
    k: usize,
    threshold: f32,
) -> Result<Vec<SimilarityPair>> {
    use rayon::prelude::*;

    let n = embeddings.len();
    if n < 2 {
        return Ok(Vec::new());
    }

    // Parallel search for each embedding
    let all_results: Vec<Vec<(usize, f32)>> = embeddings
        .par_iter()
        .enumerate()
        .map(|(i, emb)| {
            match find_similar_approximate(emb, index, k + 1, threshold) {
                // +1 to exclude self
                Ok(results) => results.into_iter().filter(|(j, _)| *j != i).collect(),
                Err(_) => Vec::new(),
            }
        })
        .collect();

    // Deduplicate pairs (ensure i < j)
    let mut seen: FxHashSet<(usize, usize)> = FxHashSet::default();
    let mut pairs = Vec::new();

    for (i, results) in all_results.into_iter().enumerate() {
        for (j, sim) in results {
            let (a, b) = if i < j { (i, j) } else { (j, i) };
            if seen.insert((a, b)) {
                pairs.push(SimilarityPair::new(a, b, sim));
            }
        }
    }

    // Sort by similarity descending
    pairs.sort_by(|a, b| {
        b.similarity
            .partial_cmp(&a.similarity)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    Ok(pairs)
}

/// Build clone clusters using approximate nearest neighbor search.
///
/// Convenience function that combines ANN search with clustering.
///
/// # Arguments
///
/// * `embeddings` - All embedding vectors
/// * `index` - Pre-built index containing all embeddings
/// * `k` - Number of neighbors to search per query
/// * `threshold` - Minimum similarity for clustering
///
/// # Returns
///
/// Vector of `CloneCluster`, sorted by size descending.
pub fn cluster_clones_approximate(
    embeddings: &[Vec<f32>],
    index: &VectorIndex,
    k: usize,
    threshold: f32,
) -> Result<Vec<CloneCluster>> {
    let pairs = find_all_similar_approximate(embeddings, index, k, threshold)?;
    Ok(cluster_clones(&pairs, embeddings, threshold))
}

// =============================================================================
// TESTS
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_find_basic() {
        let mut uf = UnionFind::new(5);

        assert!(!uf.connected(0, 1));

        uf.union(0, 1);
        assert!(uf.connected(0, 1));
        assert!(!uf.connected(0, 2));

        uf.union(1, 2);
        assert!(uf.connected(0, 2)); // Transitive
    }

    #[test]
    fn test_union_find_extract_sets() {
        let mut uf = UnionFind::new(6);

        // Create two clusters: {0, 1, 2} and {3, 4}
        // 5 remains singleton (not included in output)
        uf.union(0, 1);
        uf.union(1, 2);
        uf.union(3, 4);

        let sets = uf.extract_sets();

        assert_eq!(sets.len(), 2);

        let sizes: Vec<usize> = sets.iter().map(|s| s.len()).collect();
        assert!(sizes.contains(&3)); // {0, 1, 2}
        assert!(sizes.contains(&2)); // {3, 4}
    }

    #[test]
    fn test_cluster_clones_simple() {
        let embeddings = vec![
            vec![1.0, 0.0],
            vec![0.99, 0.01],
            vec![0.98, 0.02],
            vec![0.0, 1.0],
            vec![0.01, 0.99],
        ];

        let pairs = vec![
            SimilarityPair::new(0, 1, 0.99),
            SimilarityPair::new(0, 2, 0.98),
            SimilarityPair::new(1, 2, 0.97),
            SimilarityPair::new(3, 4, 0.99),
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.9);

        assert_eq!(clusters.len(), 2);
        assert_eq!(clusters[0].size(), 3); // Larger cluster first
        assert_eq!(clusters[1].size(), 2);
    }

    #[test]
    fn test_cluster_empty() {
        let embeddings: Vec<Vec<f32>> = vec![];
        let pairs: Vec<SimilarityPair> = vec![];
        let clusters = cluster_clones(&pairs, &embeddings, 0.5);
        assert!(clusters.is_empty());
    }

    #[test]
    fn test_cluster_no_pairs() {
        let embeddings = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
        let pairs: Vec<SimilarityPair> = vec![];
        let clusters = cluster_clones(&pairs, &embeddings, 0.5);
        assert!(clusters.is_empty()); // No pairs above threshold
    }

    #[test]
    fn test_cluster_transitive() {
        let embeddings = vec![vec![1.0, 0.0], vec![0.5, 0.5], vec![0.0, 1.0]];

        // 0-1 and 1-2 connected, but 0-2 not directly connected
        let pairs = vec![
            SimilarityPair::new(0, 1, 0.9),
            SimilarityPair::new(1, 2, 0.9),
            // No direct 0-2 pair
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.8);

        // Should still form one cluster due to transitivity
        assert_eq!(clusters.len(), 1);
        assert_eq!(clusters[0].size(), 3);
    }

    #[test]
    fn test_cluster_centroid() {
        let embeddings = vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]];

        let pairs = vec![
            SimilarityPair::new(0, 1, 0.9),
            SimilarityPair::new(0, 2, 0.9),
            SimilarityPair::new(1, 2, 0.9),
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.8);

        assert_eq!(clusters.len(), 1);
        let centroid = clusters[0].centroid.as_ref().unwrap();

        // Centroid should be mean: (1+0+0.5)/3, (0+1+0.5)/3 = (0.5, 0.5)
        assert!((centroid[0] - 0.5).abs() < 1e-5);
        assert!((centroid[1] - 0.5).abs() < 1e-5);
    }

    #[test]
    fn test_cluster_cohesion() {
        let embeddings = vec![vec![1.0, 0.0], vec![0.99, 0.01], vec![0.98, 0.02]];

        let pairs = vec![
            SimilarityPair::new(0, 1, 0.99),
            SimilarityPair::new(0, 2, 0.98),
            SimilarityPair::new(1, 2, 0.97),
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.9);

        assert_eq!(clusters.len(), 1);

        // Cohesion should be average: (0.99 + 0.98 + 0.97) / 3
        let expected_cohesion = (0.99 + 0.98 + 0.97) / 3.0;
        assert!((clusters[0].cohesion - expected_cohesion).abs() < 1e-5);
        assert!((clusters[0].min_similarity - 0.97).abs() < 1e-5);
        assert!((clusters[0].max_similarity - 0.99).abs() < 1e-5);
    }

    #[test]
    fn test_clone_cluster_struct() {
        let mut cluster = CloneCluster::new(vec![0, 1, 2]);

        assert_eq!(cluster.size(), 3);
        assert!(cluster.is_valid());
        assert!(cluster.centroid.is_none());

        let embeddings = vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![0.5, 0.5]];

        cluster.compute_centroid(&embeddings);
        assert!(cluster.centroid.is_some());
    }

    #[test]
    fn test_cluster_single_element_not_valid() {
        let cluster = CloneCluster::new(vec![0]);
        assert!(!cluster.is_valid());
    }

    #[test]
    fn test_cluster_threshold_filtering() {
        let embeddings = vec![vec![1.0, 0.0], vec![0.5, 0.5], vec![0.0, 1.0]];

        let pairs = vec![
            SimilarityPair::new(0, 1, 0.7), // Below threshold
            SimilarityPair::new(1, 2, 0.7), // Below threshold
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.8);

        // No clusters because all pairs are below threshold
        assert!(clusters.is_empty());
    }

    #[test]
    fn test_union_find_path_compression() {
        let mut uf = UnionFind::new(5);

        // Build a chain: 0 -> 1 -> 2 -> 3 -> 4
        uf.union(0, 1);
        uf.union(1, 2);
        uf.union(2, 3);
        uf.union(3, 4);

        // Find should compress the path
        let root = uf.find(0);
        assert_eq!(uf.find(4), root);

        // After compression, direct parent should be root
        // (path compression makes all point to root)
        let _ = uf.find(0);
        assert_eq!(uf.parent[0], root);
    }

    #[test]
    fn test_cluster_sorted_by_size() {
        let embeddings = vec![
            vec![1.0, 0.0],
            vec![0.99, 0.01],
            vec![0.0, 1.0],
            vec![0.01, 0.99],
            vec![0.02, 0.98],
        ];

        let pairs = vec![
            SimilarityPair::new(0, 1, 0.99),    // 2-member cluster
            SimilarityPair::new(2, 3, 0.99),    // 3-member cluster
            SimilarityPair::new(2, 4, 0.98),    //
            SimilarityPair::new(3, 4, 0.97),    //
        ];

        let clusters = cluster_clones(&pairs, &embeddings, 0.9);

        assert_eq!(clusters.len(), 2);
        assert!(
            clusters[0].size() >= clusters[1].size(),
            "Clusters should be sorted by size descending"
        );
    }
}
