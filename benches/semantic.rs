//! Comprehensive benchmarks for semantic search and embedding operations.
//!
//! Measures performance of:
//! - Code chunking (boundary-aware, overlap calculation)
//! - Embedding unit extraction (multi-language)
//! - Vector index operations (HNSW search, batch operations)
//! - Tokenization (exact vs estimated)
//! - Text processing (identifier parsing, pattern detection)

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use rand::prelude::*;
use std::io::Write;
use tempfile::NamedTempFile;

use go_brrr::embedding::{Metric, VectorIndex};
use go_brrr::semantic::{
    build_embedding_text, chunk_code, chunk_code_with_overlap, count_tokens,
    detect_code_complexity, detect_semantic_patterns, needs_chunking, parse_identifier_to_words,
    split_into_chunks, truncate_to_tokens, EmbeddingUnit, UnitKind, CHUNK_OVERLAP_TOKENS,
    MAX_CODE_PREVIEW_TOKENS,
};
use go_brrr::util::tokenizer::{estimate_tokens, fits_in_tokens, split_at_tokens};

// =============================================================================
// Test Data Generation
// =============================================================================

/// Generate a small Python function (typical unit test size).
fn generate_small_python_function() -> String {
    r#"def calculate_sum(numbers: list[int]) -> int:
    """Calculate the sum of a list of numbers."""
    total = 0
    for num in numbers:
        total += num
    return total
"#
    .to_string()
}

/// Generate a medium Python class with methods.
fn generate_medium_python_class() -> String {
    r#"class DataProcessor:
    """Process and transform data with validation."""

    def __init__(self, config: dict) -> None:
        """Initialize processor with configuration."""
        self.config = config
        self.cache = {}
        self.errors = []

    def validate(self, data: dict) -> bool:
        """Validate input data against schema."""
        if not isinstance(data, dict):
            self.errors.append("Data must be a dictionary")
            return False
        required_fields = self.config.get("required", [])
        for field in required_fields:
            if field not in data:
                self.errors.append(f"Missing required field: {field}")
                return False
        return True

    def transform(self, data: dict) -> dict:
        """Apply transformations to the data."""
        result = data.copy()
        for key, value in result.items():
            if isinstance(value, str):
                result[key] = value.strip().lower()
            elif isinstance(value, (int, float)):
                result[key] = round(value, 2)
        return result

    def process(self, data: dict) -> dict | None:
        """Process data: validate and transform."""
        if not self.validate(data):
            return None
        return self.transform(data)

    def get_errors(self) -> list[str]:
        """Return accumulated errors."""
        return self.errors.copy()

    def clear_errors(self) -> None:
        """Clear all accumulated errors."""
        self.errors.clear()
"#
    .to_string()
}

/// Generate a large Python file with multiple classes and functions.
fn generate_large_python_file() -> String {
    let mut code = String::with_capacity(50_000);

    // Add imports
    code.push_str(
        r#"import os
import json
import logging
from typing import Any, Dict, List, Optional
from dataclasses import dataclass
from abc import ABC, abstractmethod

logger = logging.getLogger(__name__)

"#,
    );

    // Generate multiple classes
    for i in 0..10 {
        code.push_str(&format!(
            r#"
class Handler{i}(ABC):
    """Handler for processing type {i} data."""

    def __init__(self, config: Dict[str, Any]) -> None:
        self.config = config
        self.processed_count = 0
        self.error_count = 0

    @abstractmethod
    def process(self, data: Any) -> Any:
        """Process the input data."""
        pass

    def validate(self, data: Any) -> bool:
        """Validate input data."""
        if data is None:
            logger.error("Data cannot be None")
            return False
        return True

    def log_metrics(self) -> None:
        """Log processing metrics."""
        logger.info(f"Processed: {{self.processed_count}}, Errors: {{self.error_count}}")


class ConcreteHandler{i}(Handler{i}):
    """Concrete implementation for type {i}."""

    def process(self, data: Any) -> Any:
        if not self.validate(data):
            self.error_count += 1
            return None
        try:
            result = self._transform(data)
            self.processed_count += 1
            return result
        except Exception as e:
            logger.exception(f"Processing failed: {{e}}")
            self.error_count += 1
            return None

    def _transform(self, data: Any) -> Any:
        """Internal transformation logic."""
        if isinstance(data, dict):
            return {{k: v for k, v in data.items() if v is not None}}
        return data

"#
        ));
    }

    // Add utility functions
    for i in 0..20 {
        code.push_str(&format!(
            r#"
def utility_function_{i}(arg1: int, arg2: str, arg3: Optional[List[int]] = None) -> Dict[str, Any]:
    """Utility function number {i} for various operations."""
    result = {{"index": {i}, "arg1": arg1, "arg2": arg2}}
    if arg3:
        result["sum"] = sum(arg3)
        result["count"] = len(arg3)
    for j in range(min(arg1, 10)):
        if j % 2 == 0:
            result[f"even_{{j}}"] = j * 2
        else:
            result[f"odd_{{j}}"] = j * 3
    return result

"#
        ));
    }

    code
}

/// Generate TypeScript code of varying sizes.
fn generate_typescript_function() -> String {
    r#"interface User {
    id: number;
    name: string;
    email: string;
    roles: string[];
}

async function fetchUserData(userId: number): Promise<User | null> {
    try {
        const response = await fetch(`/api/users/${userId}`);
        if (!response.ok) {
            console.error(`Failed to fetch user: ${response.status}`);
            return null;
        }
        const data: User = await response.json();
        return data;
    } catch (error) {
        console.error('Error fetching user:', error);
        return null;
    }
}

function validateUser(user: User): boolean {
    if (!user.name || user.name.length < 2) {
        return false;
    }
    if (!user.email || !user.email.includes('@')) {
        return false;
    }
    return true;
}
"#
    .to_string()
}

/// Generate Rust code for testing.
fn generate_rust_function() -> String {
    r#"use std::collections::HashMap;
use std::error::Error;

/// Configuration for the processor
#[derive(Debug, Clone)]
pub struct ProcessorConfig {
    pub max_items: usize,
    pub timeout_ms: u64,
    pub cache_enabled: bool,
}

impl Default for ProcessorConfig {
    fn default() -> Self {
        Self {
            max_items: 1000,
            timeout_ms: 5000,
            cache_enabled: true,
        }
    }
}

/// Process items with the given configuration
pub fn process_items<T: Clone>(
    items: &[T],
    config: &ProcessorConfig,
    transform: impl Fn(&T) -> T,
) -> Result<Vec<T>, Box<dyn Error>> {
    if items.len() > config.max_items {
        return Err("Too many items".into());
    }

    let results: Vec<T> = items
        .iter()
        .map(|item| transform(item))
        .collect();

    Ok(results)
}

/// Cache implementation with LRU eviction
pub struct LruCache<K, V> {
    capacity: usize,
    items: HashMap<K, V>,
    order: Vec<K>,
}

impl<K: Eq + std::hash::Hash + Clone, V> LruCache<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            items: HashMap::with_capacity(capacity),
            order: Vec::with_capacity(capacity),
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.items.contains_key(key) {
            self.order.retain(|k| k != key);
            self.order.push(key.clone());
            self.items.get(key)
        } else {
            None
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        if self.items.len() >= self.capacity && !self.items.contains_key(&key) {
            if let Some(oldest) = self.order.first().cloned() {
                self.items.remove(&oldest);
                self.order.remove(0);
            }
        }
        self.items.insert(key.clone(), value);
        self.order.retain(|k| k != &key);
        self.order.push(key);
    }
}
"#
    .to_string()
}

/// Generate random embedding vector.
fn generate_random_vector(dims: usize, rng: &mut impl Rng) -> Vec<f32> {
    let mut vec: Vec<f32> = (0..dims).map(|_| rng.gen_range(-1.0..1.0)).collect();
    // Normalize
    let norm: f32 = vec.iter().map(|x| x * x).sum::<f32>().sqrt();
    if norm > f32::EPSILON {
        for v in &mut vec {
            *v /= norm;
        }
    }
    vec
}

/// Create a test EmbeddingUnit with the given code.
fn create_test_unit(name: &str, code: &str) -> EmbeddingUnit {
    let mut unit = EmbeddingUnit::new("test.py", name, UnitKind::Function, code, 1, "python");
    unit.signature = format!("def {}()", name);
    unit.docstring = Some("Test function docstring.".to_string());
    unit.semantic_tags = vec!["crud".to_string(), "validation".to_string()];
    unit.calls = vec!["helper_func".to_string(), "util_func".to_string()];
    unit
}

/// Create a temporary file with the given content.
fn create_temp_file(content: &str, extension: &str) -> NamedTempFile {
    let mut file = tempfile::Builder::new()
        .suffix(extension)
        .tempfile()
        .expect("Failed to create temp file");
    file.write_all(content.as_bytes())
        .expect("Failed to write to temp file");
    file.flush().expect("Failed to flush temp file");
    file
}

// =============================================================================
// Code Chunking Benchmarks
// =============================================================================

fn bench_chunk_small_function(c: &mut Criterion) {
    let code = generate_small_python_function();

    c.bench_function("chunk_small_function", |b| {
        b.iter(|| chunk_code(black_box(&code), MAX_CODE_PREVIEW_TOKENS))
    });
}

fn bench_chunk_medium_class(c: &mut Criterion) {
    let code = generate_medium_python_class();

    c.bench_function("chunk_medium_class", |b| {
        b.iter(|| chunk_code(black_box(&code), MAX_CODE_PREVIEW_TOKENS))
    });
}

fn bench_chunk_large_file(c: &mut Criterion) {
    let code = generate_large_python_file();

    c.bench_function("chunk_large_file", |b| {
        b.iter(|| chunk_code(black_box(&code), MAX_CODE_PREVIEW_TOKENS))
    });
}

fn bench_chunk_with_overlap_calculation(c: &mut Criterion) {
    let code = generate_large_python_file();

    let mut group = c.benchmark_group("chunk_with_overlap");

    for overlap in [50, 100, 200, 400] {
        group.bench_with_input(
            BenchmarkId::new("overlap", overlap),
            &overlap,
            |b, &overlap| b.iter(|| chunk_code_with_overlap(black_box(&code), 1000, overlap)),
        );
    }

    group.finish();
}

fn bench_needs_chunking(c: &mut Criterion) {
    let small = generate_small_python_function();
    let large = generate_large_python_file();

    let mut group = c.benchmark_group("needs_chunking");

    group.bench_function("small_code", |b| {
        b.iter(|| needs_chunking(black_box(&small), MAX_CODE_PREVIEW_TOKENS))
    });

    group.bench_function("large_code", |b| {
        b.iter(|| needs_chunking(black_box(&large), MAX_CODE_PREVIEW_TOKENS))
    });

    group.finish();
}

fn bench_split_into_chunks_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("split_into_chunks_scaling");
    group.sample_size(50);

    // Generate code of increasing sizes
    for size_multiplier in [1, 2, 5, 10] {
        let code = generate_large_python_file().repeat(size_multiplier);
        let code_len = code.len();

        group.throughput(Throughput::Bytes(code_len as u64));
        group.bench_with_input(
            BenchmarkId::new("size_kb", code_len / 1024),
            &code,
            |b, code| b.iter(|| split_into_chunks(black_box(code), 2000, CHUNK_OVERLAP_TOKENS)),
        );
    }

    group.finish();
}

// =============================================================================
// Tokenization Benchmarks
// =============================================================================

fn bench_count_tokens(c: &mut Criterion) {
    let mut group = c.benchmark_group("count_tokens");

    // Various text sizes
    let small_text = "Hello, world! This is a simple test.";
    let medium_text = generate_small_python_function();
    let large_text = generate_large_python_file();

    group.bench_function("small_text_37_chars", |b| {
        b.iter(|| count_tokens(black_box(small_text)))
    });

    group.throughput(Throughput::Bytes(medium_text.len() as u64));
    group.bench_function("medium_code_function", |b| {
        b.iter(|| count_tokens(black_box(&medium_text)))
    });

    group.throughput(Throughput::Bytes(large_text.len() as u64));
    group.bench_function("large_code_file", |b| {
        b.iter(|| count_tokens(black_box(&large_text)))
    });

    group.finish();
}

fn bench_truncate_to_tokens(c: &mut Criterion) {
    let mut group = c.benchmark_group("truncate_to_tokens");

    let text = generate_large_python_file();

    for max_tokens in [100, 500, 1000, 2000] {
        group.bench_with_input(
            BenchmarkId::new("max_tokens", max_tokens),
            &max_tokens,
            |b, &max_tokens| b.iter(|| truncate_to_tokens(black_box(&text), max_tokens)),
        );
    }

    group.finish();
}

fn bench_split_at_tokens(c: &mut Criterion) {
    let mut group = c.benchmark_group("split_at_tokens");

    let text = generate_large_python_file();

    for chunk_size in [100, 500, 1000, 2000] {
        group.bench_with_input(
            BenchmarkId::new("chunk_size", chunk_size),
            &chunk_size,
            |b, &chunk_size| b.iter(|| split_at_tokens(black_box(&text), chunk_size)),
        );
    }

    group.finish();
}

fn bench_estimate_vs_exact_tokens(c: &mut Criterion) {
    let mut group = c.benchmark_group("token_estimation_vs_exact");

    let text = generate_medium_python_class();

    group.bench_function("estimate_tokens", |b| {
        b.iter(|| estimate_tokens(black_box(&text)))
    });

    group.bench_function("exact_count_tokens", |b| {
        b.iter(|| count_tokens(black_box(&text)))
    });

    group.finish();
}

fn bench_fits_in_tokens(c: &mut Criterion) {
    let mut group = c.benchmark_group("fits_in_tokens");

    let small = generate_small_python_function();
    let large = generate_large_python_file();

    group.bench_function("small_fits", |b| {
        b.iter(|| fits_in_tokens(black_box(&small), 10000))
    });

    group.bench_function("small_doesnt_fit", |b| {
        b.iter(|| fits_in_tokens(black_box(&small), 5))
    });

    group.bench_function("large_borderline", |b| {
        b.iter(|| fits_in_tokens(black_box(&large), 5000))
    });

    group.finish();
}

// =============================================================================
// Text Processing Benchmarks
// =============================================================================

fn bench_build_embedding_text(c: &mut Criterion) {
    let mut group = c.benchmark_group("build_embedding_text");

    // Simple unit
    let simple_unit = create_test_unit("simple_func", &generate_small_python_function());

    // Complex unit with more metadata
    let mut complex_unit = create_test_unit("complex_func", &generate_medium_python_class());
    complex_unit.semantic_tags = vec![
        "crud".to_string(),
        "validation".to_string(),
        "transform".to_string(),
        "error_handling".to_string(),
    ];
    complex_unit.calls = (0..20).map(|i| format!("func_{}", i)).collect();
    complex_unit.called_by = (0..10).map(|i| format!("caller_{}", i)).collect();
    complex_unit.cfg_summary = "blocks: 15, edges: 20, complexity: 8".to_string();
    complex_unit.dfg_summary = "variables: 12, def-use chains: 25".to_string();
    complex_unit.dependencies = "os, json, logging, typing".to_string();

    group.bench_function("simple_unit", |b| {
        b.iter(|| build_embedding_text(black_box(&simple_unit)))
    });

    group.bench_function("complex_unit", |b| {
        b.iter(|| build_embedding_text(black_box(&complex_unit)))
    });

    group.finish();
}

fn bench_parse_identifier_to_words(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_identifier_to_words");

    let identifiers = [
        "getUserDataFromDatabase",
        "get_user_data_from_database",
        "XMLHttpRequest",
        "HTMLElement",
        "parseJSONResponse",
        "API_KEY_PREFIX",
        "__private_method__",
        "calculateTotalSumOfAllItems",
    ];

    for id in identifiers {
        group.bench_with_input(BenchmarkId::new("identifier", id), &id, |b, id| {
            b.iter(|| parse_identifier_to_words(black_box(id)))
        });
    }

    group.finish();
}

fn bench_detect_code_complexity(c: &mut Criterion) {
    let mut group = c.benchmark_group("detect_code_complexity");

    let simple_code = generate_small_python_function();
    let complex_code = generate_medium_python_class();
    let large_code = generate_large_python_file();

    group.bench_function("simple_function", |b| {
        b.iter(|| detect_code_complexity(black_box(&simple_code)))
    });

    group.bench_function("medium_class", |b| {
        b.iter(|| detect_code_complexity(black_box(&complex_code)))
    });

    group.bench_function("large_file", |b| {
        b.iter(|| detect_code_complexity(black_box(&large_code)))
    });

    group.finish();
}

fn bench_detect_semantic_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("detect_semantic_patterns");

    // Code with various patterns
    let crud_code = r#"
def save_user(user):
    db.insert(user)
    cache.store(user.id, user)
    return fetch_user(user.id)
"#;

    let validation_code = r#"
def validate_input(data):
    check(data)
    verify(data.schema)
    assert data is not None
    ensure(len(data) > 0)
"#;

    let async_code = r#"
async def fetch_data():
    try:
        result = await api.get()
        return result
    except Exception as e:
        raise ValueError(str(e))
"#;

    let mixed_code = generate_large_python_file();

    group.bench_function("crud_patterns", |b| {
        b.iter(|| detect_semantic_patterns(black_box(crud_code)))
    });

    group.bench_function("validation_patterns", |b| {
        b.iter(|| detect_semantic_patterns(black_box(validation_code)))
    });

    group.bench_function("async_error_patterns", |b| {
        b.iter(|| detect_semantic_patterns(black_box(async_code)))
    });

    group.bench_function("large_mixed_code", |b| {
        b.iter(|| detect_semantic_patterns(black_box(&mixed_code)))
    });

    group.finish();
}

// =============================================================================
// Vector Index Benchmarks
// =============================================================================

fn bench_vector_index_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_creation");

    for dims in [384, 768, 1024, 1536] {
        group.bench_with_input(BenchmarkId::new("dimensions", dims), &dims, |b, &dims| {
            b.iter(|| VectorIndex::new(dims, Metric::InnerProduct).expect("index creation"))
        });
    }

    group.finish();
}

fn bench_vector_index_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_add");
    let dims = 768;
    let mut rng = rand::thread_rng();

    group.bench_function("single_add", |b| {
        let index = VectorIndex::new(dims, Metric::InnerProduct).expect("index creation");
        index.reserve(1000).expect("reserve");
        let mut key = 0u64;

        b.iter_batched(
            || {
                let vec = generate_random_vector(dims, &mut rng);
                key += 1;
                (key, vec)
            },
            |(key, vec)| {
                index.add(key, &vec).expect("add");
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_vector_index_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_search");
    let dims = 768;
    let mut rng = rand::thread_rng();

    // Create and populate index with N vectors
    for n_vectors in [100, 1000, 10000] {
        let index = VectorIndex::new(dims, Metric::InnerProduct).expect("index creation");
        index.reserve(n_vectors).expect("reserve");

        for i in 0..n_vectors {
            let vec = generate_random_vector(dims, &mut rng);
            index.add(i as u64, &vec).expect("add");
        }

        for k in [5, 10, 50] {
            if k <= n_vectors {
                let query = generate_random_vector(dims, &mut rng);

                group.bench_with_input(
                    BenchmarkId::new(format!("n{}_k{}", n_vectors, k), k),
                    &(&index, &query, k),
                    |b, (index, query, k)| b.iter(|| index.search(black_box(query), *k)),
                );
            }
        }
    }

    group.finish();
}

fn bench_vector_index_filtered_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_filtered_search");
    let dims = 768;
    let n_vectors = 1000;
    let mut rng = rand::thread_rng();

    let index = VectorIndex::new(dims, Metric::InnerProduct).expect("index creation");
    index.reserve(n_vectors).expect("reserve");

    for i in 0..n_vectors {
        let vec = generate_random_vector(dims, &mut rng);
        index.add(i as u64, &vec).expect("add");
    }

    let query = generate_random_vector(dims, &mut rng);

    // Filter that accepts 50% of vectors
    group.bench_function("filter_50_percent", |b| {
        b.iter(|| {
            index
                .search_filtered(black_box(&query), 10, |key| key % 2 == 0)
                .expect("search")
        })
    });

    // Filter that accepts 10% of vectors
    group.bench_function("filter_10_percent", |b| {
        b.iter(|| {
            index
                .search_filtered(black_box(&query), 10, |key| key % 10 == 0)
                .expect("search")
        })
    });

    // Filter that accepts 1% of vectors
    group.bench_function("filter_1_percent", |b| {
        b.iter(|| {
            index
                .search_filtered(black_box(&query), 10, |key| key % 100 == 0)
                .expect("search")
        })
    });

    group.finish();
}

fn bench_vector_index_batch_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_batch_add");
    group.sample_size(30);
    let dims = 768;
    let mut rng = rand::thread_rng();

    for batch_size in [10, 50, 100, 500] {
        group.bench_with_input(
            BenchmarkId::new("batch_size", batch_size),
            &batch_size,
            |b, &batch_size| {
                b.iter_batched(
                    || {
                        let index =
                            VectorIndex::new(dims, Metric::InnerProduct).expect("index creation");
                        index.reserve(batch_size).expect("reserve");
                        let keys: Vec<u64> = (0..batch_size as u64).collect();
                        let vectors: Vec<Vec<f32>> = (0..batch_size)
                            .map(|_| generate_random_vector(dims, &mut rng))
                            .collect();
                        (index, keys, vectors)
                    },
                    |(index, keys, vectors)| {
                        index.add_batch(&keys, &vectors).expect("batch add");
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

fn bench_vector_index_batch_add_flat(c: &mut Criterion) {
    let mut group = c.benchmark_group("vector_index_batch_add_flat");
    group.sample_size(30);
    let dims = 768;
    let mut rng = rand::thread_rng();

    for batch_size in [10, 50, 100, 500] {
        group.bench_with_input(
            BenchmarkId::new("batch_size", batch_size),
            &batch_size,
            |b, &batch_size| {
                b.iter_batched(
                    || {
                        let index =
                            VectorIndex::new(dims, Metric::InnerProduct).expect("index creation");
                        index.reserve(batch_size).expect("reserve");
                        let keys: Vec<u64> = (0..batch_size as u64).collect();
                        let vectors_flat: Vec<f32> = (0..batch_size)
                            .flat_map(|_| generate_random_vector(dims, &mut rng))
                            .collect();
                        (index, keys, vectors_flat)
                    },
                    |(index, keys, vectors_flat)| {
                        index
                            .add_batch_flat(&keys, &vectors_flat)
                            .expect("batch add flat");
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

// =============================================================================
// Embedding Unit Extraction Benchmarks
// =============================================================================

fn bench_extract_units_python(c: &mut Criterion) {
    let mut group = c.benchmark_group("extract_units_python");

    let python_code = generate_medium_python_class();
    let temp_file = create_temp_file(&python_code, ".py");
    let path = temp_file.path().to_string_lossy().to_string();

    group.bench_function("medium_class", |b| {
        b.iter(|| go_brrr::extract_file_units(black_box(&path)))
    });

    // Large file
    let large_python = generate_large_python_file();
    let temp_large = create_temp_file(&large_python, ".py");
    let large_path = temp_large.path().to_string_lossy().to_string();

    group.bench_function("large_file", |b| {
        b.iter(|| go_brrr::extract_file_units(black_box(&large_path)))
    });

    group.finish();
}

fn bench_extract_units_typescript(c: &mut Criterion) {
    let mut group = c.benchmark_group("extract_units_typescript");

    let ts_code = generate_typescript_function();
    let temp_file = create_temp_file(&ts_code, ".ts");
    let path = temp_file.path().to_string_lossy().to_string();

    group.bench_function("interface_and_functions", |b| {
        b.iter(|| go_brrr::extract_file_units(black_box(&path)))
    });

    group.finish();
}

fn bench_extract_units_rust(c: &mut Criterion) {
    let mut group = c.benchmark_group("extract_units_rust");

    let rust_code = generate_rust_function();
    let temp_file = create_temp_file(&rust_code, ".rs");
    let path = temp_file.path().to_string_lossy().to_string();

    group.bench_function("structs_and_impls", |b| {
        b.iter(|| go_brrr::extract_file_units(black_box(&path)))
    });

    group.finish();
}

// =============================================================================
// Combined/Integration Benchmarks
// =============================================================================

fn bench_full_embedding_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_embedding_pipeline");
    group.sample_size(30);

    let python_code = generate_medium_python_class();
    let temp_file = create_temp_file(&python_code, ".py");
    let path = temp_file.path().to_string_lossy().to_string();

    // Full pipeline: extract units -> build embedding text -> count tokens
    group.bench_function("extract_build_count", |b| {
        b.iter(|| {
            let units = go_brrr::extract_file_units(black_box(&path)).unwrap_or_default();
            for unit in &units {
                let text = build_embedding_text(unit);
                let _tokens = count_tokens(&text);
            }
            units.len()
        })
    });

    group.finish();
}

fn bench_chunking_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("chunking_pipeline");

    let large_code = generate_large_python_file();

    // Full chunking pipeline
    group.bench_function("detect_and_chunk", |b| {
        b.iter(|| {
            if needs_chunking(black_box(&large_code), MAX_CODE_PREVIEW_TOKENS) {
                let chunks = chunk_code(&large_code, MAX_CODE_PREVIEW_TOKENS);
                chunks.len()
            } else {
                1
            }
        })
    });

    group.finish();
}

// =============================================================================
// Criterion Groups and Main
// =============================================================================

criterion_group!(
    name = chunking_benches;
    config = Criterion::default();
    targets =
        bench_chunk_small_function,
        bench_chunk_medium_class,
        bench_chunk_large_file,
        bench_chunk_with_overlap_calculation,
        bench_needs_chunking,
        bench_split_into_chunks_scaling
);

criterion_group!(
    name = tokenization_benches;
    config = Criterion::default();
    targets =
        bench_count_tokens,
        bench_truncate_to_tokens,
        bench_split_at_tokens,
        bench_estimate_vs_exact_tokens,
        bench_fits_in_tokens
);

criterion_group!(
    name = text_processing_benches;
    config = Criterion::default();
    targets =
        bench_build_embedding_text,
        bench_parse_identifier_to_words,
        bench_detect_code_complexity,
        bench_detect_semantic_patterns
);

criterion_group!(
    name = vector_index_benches;
    config = Criterion::default().sample_size(50);
    targets =
        bench_vector_index_creation,
        bench_vector_index_add,
        bench_vector_index_search,
        bench_vector_index_filtered_search,
        bench_vector_index_batch_add,
        bench_vector_index_batch_add_flat
);

criterion_group!(
    name = extraction_benches;
    config = Criterion::default().sample_size(30);
    targets =
        bench_extract_units_python,
        bench_extract_units_typescript,
        bench_extract_units_rust
);

criterion_group!(
    name = integration_benches;
    config = Criterion::default().sample_size(30);
    targets =
        bench_full_embedding_pipeline,
        bench_chunking_pipeline
);

criterion_main!(
    chunking_benches,
    tokenization_benches,
    text_processing_benches,
    vector_index_benches,
    extraction_benches,
    integration_benches
);
