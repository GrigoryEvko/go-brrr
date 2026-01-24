//! End-to-end benchmarks for go-brrr operations.
//!
//! Measures real-world performance of complete analysis pipelines including:
//! - Full file analysis (parse + extract)
//! - Project scanning with ignore patterns
//! - Multi-language file processing
//! - Batch processing scenarios
//!
//! Run with: `cargo bench --bench e2e`

use criterion::{
    black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput,
};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use tempfile::TempDir;

use go_brrr::{
    ast::{self, AstExtractor},
    get_structure, get_tree,
    lang::LanguageRegistry,
    util::ignore::{is_default_ignored, BrrrIgnore},
};

// =============================================================================
// Test Fixtures (embedded as string constants)
// =============================================================================

/// Small Python module (~200 lines)
const SMALL_PYTHON: &str = include_str!("fixtures/small_python.py");

/// Medium TypeScript file (~500 lines)
const MEDIUM_TYPESCRIPT: &str = include_str!("fixtures/medium_typescript.ts");

/// Large Rust file (~1000 lines)
const LARGE_RUST: &str = include_str!("fixtures/large_rust.rs");

/// Sample Go file
const SAMPLE_GO: &str = include_str!("fixtures/sample_go.go");

/// Sample Java file
const SAMPLE_JAVA: &str = include_str!("fixtures/sample_java.java");

/// Sample C file
const SAMPLE_C: &str = include_str!("fixtures/sample_c.c");

/// Sample C++ file
const SAMPLE_CPP: &str = include_str!("fixtures/sample_cpp.cpp");

// =============================================================================
// Helper Functions
// =============================================================================

/// Create a temporary file with the given content and extension.
fn create_temp_file(dir: &Path, name: &str, content: &str) -> PathBuf {
    let path = dir.join(name);
    let mut file = fs::File::create(&path).expect("Failed to create temp file");
    file.write_all(content.as_bytes())
        .expect("Failed to write temp file");
    path
}

/// Create a test project directory with multiple files.
fn create_test_project() -> TempDir {
    let dir = TempDir::new().expect("Failed to create temp dir");
    let root = dir.path();

    // Create directory structure
    fs::create_dir_all(root.join("src/lib")).expect("mkdir failed");
    fs::create_dir_all(root.join("src/utils")).expect("mkdir failed");
    fs::create_dir_all(root.join("tests")).expect("mkdir failed");

    // Python files
    create_temp_file(root, "src/main.py", SMALL_PYTHON);
    create_temp_file(root, "src/lib/core.py", SMALL_PYTHON);
    create_temp_file(root, "src/utils/helpers.py", SMALL_PYTHON);
    create_temp_file(root, "tests/test_main.py", SMALL_PYTHON);

    // TypeScript files
    create_temp_file(root, "src/app.ts", MEDIUM_TYPESCRIPT);
    create_temp_file(root, "src/lib/service.ts", MEDIUM_TYPESCRIPT);

    // Rust files
    create_temp_file(root, "src/lib.rs", LARGE_RUST);
    create_temp_file(root, "src/utils/mod.rs", LARGE_RUST);

    // Other languages
    create_temp_file(root, "src/handler.go", SAMPLE_GO);
    create_temp_file(root, "src/Main.java", SAMPLE_JAVA);

    dir
}

/// Create a large test project with many files.
fn create_large_test_project(file_count: usize) -> TempDir {
    let dir = TempDir::new().expect("Failed to create temp dir");
    let root = dir.path();

    // Create directory structure
    for i in 0..5 {
        fs::create_dir_all(root.join(format!("module_{}/sub", i))).expect("mkdir failed");
    }

    // Create files distributed across directories
    for i in 0..file_count {
        let module = i % 5;
        let subdir = if i % 2 == 0 { "" } else { "sub/" };
        let ext = match i % 4 {
            0 => "py",
            1 => "ts",
            2 => "rs",
            _ => "go",
        };
        let content = match ext {
            "py" => SMALL_PYTHON,
            "ts" => MEDIUM_TYPESCRIPT,
            "rs" => LARGE_RUST,
            _ => SAMPLE_GO,
        };
        let filename = format!("module_{}/{}file_{}.{}", module, subdir, i, ext);
        create_temp_file(root, &filename, content);
    }

    dir
}

// =============================================================================
// Full File Analysis Pipeline Benchmarks
// =============================================================================

fn bench_full_file_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_file_analysis");

    // Benchmark Python file analysis
    let py_dir = TempDir::new().unwrap();
    let py_path = create_temp_file(py_dir.path(), "module.py", SMALL_PYTHON);

    group.throughput(Throughput::Bytes(SMALL_PYTHON.len() as u64));
    group.bench_function("python_small_200_lines", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_file(black_box(&py_path));
            black_box(result)
        })
    });

    // Benchmark TypeScript file analysis
    let ts_dir = TempDir::new().unwrap();
    let ts_path = create_temp_file(ts_dir.path(), "module.ts", MEDIUM_TYPESCRIPT);

    group.throughput(Throughput::Bytes(MEDIUM_TYPESCRIPT.len() as u64));
    group.bench_function("typescript_medium_500_lines", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_file(black_box(&ts_path));
            black_box(result)
        })
    });

    // Benchmark Rust file analysis
    let rs_dir = TempDir::new().unwrap();
    let rs_path = create_temp_file(rs_dir.path(), "module.rs", LARGE_RUST);

    group.throughput(Throughput::Bytes(LARGE_RUST.len() as u64));
    group.bench_function("rust_large_1000_lines", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_file(black_box(&rs_path));
            black_box(result)
        })
    });

    group.finish();
}

fn bench_code_structure_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("code_structure_extraction");

    // Setup: Create test files for each language
    let py_dir = TempDir::new().unwrap();
    let py_path = create_temp_file(py_dir.path(), "module.py", SMALL_PYTHON);

    let ts_dir = TempDir::new().unwrap();
    let ts_path = create_temp_file(ts_dir.path(), "module.ts", MEDIUM_TYPESCRIPT);

    let rs_dir = TempDir::new().unwrap();
    let rs_path = create_temp_file(rs_dir.path(), "module.rs", LARGE_RUST);

    // Benchmark extraction with full ModuleInfo
    group.bench_function("python_module_info", |b| {
        b.iter(|| {
            let module = ast::extract_file(black_box(py_path.to_str().unwrap())).unwrap();
            black_box((
                module.functions.len(),
                module.classes.len(),
                module.imports.len(),
            ))
        })
    });

    group.bench_function("typescript_module_info", |b| {
        b.iter(|| {
            let module = ast::extract_file(black_box(ts_path.to_str().unwrap())).unwrap();
            black_box((
                module.functions.len(),
                module.classes.len(),
                module.imports.len(),
            ))
        })
    });

    group.bench_function("rust_module_info", |b| {
        b.iter(|| {
            let module = ast::extract_file(black_box(rs_path.to_str().unwrap())).unwrap();
            black_box((
                module.functions.len(),
                module.classes.len(),
                module.imports.len(),
            ))
        })
    });

    group.finish();
}

// =============================================================================
// Project Scanning Benchmarks
// =============================================================================

fn bench_project_scanning(c: &mut Criterion) {
    let mut group = c.benchmark_group("project_scanning");

    // Small project (10 files)
    let small_project = create_test_project();
    group.bench_function("file_tree_small_project", |b| {
        b.iter(|| {
            let tree = get_tree(black_box(small_project.path().to_str().unwrap()), None);
            black_box(tree)
        })
    });

    // File tree with extension filter
    group.bench_function("file_tree_python_filter", |b| {
        b.iter(|| {
            let tree = get_tree(
                black_box(small_project.path().to_str().unwrap()),
                Some(".py"),
            );
            black_box(tree)
        })
    });

    // Code structure extraction for project
    group.bench_function("code_structure_all_languages", |b| {
        b.iter(|| {
            let structure =
                get_structure(black_box(small_project.path().to_str().unwrap()), None, 0);
            black_box(structure)
        })
    });

    group.bench_function("code_structure_python_only", |b| {
        b.iter(|| {
            let structure = get_structure(
                black_box(small_project.path().to_str().unwrap()),
                Some("python"),
                0,
            );
            black_box(structure)
        })
    });

    group.finish();
}

fn bench_ignore_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("ignore_patterns");

    // Create test project with ignore files
    let project_dir = TempDir::new().unwrap();
    let root = project_dir.path();

    // Create .brrrignore
    fs::write(
        root.join(".brrrignore"),
        "*.log\n__pycache__/\nnode_modules/\n*.pyc\n",
    )
    .unwrap();

    // Create test paths
    let test_paths: Vec<PathBuf> = vec![
        PathBuf::from("src/main.py"),
        PathBuf::from("src/utils.py"),
        PathBuf::from("node_modules/package/index.js"),
        PathBuf::from("__pycache__/module.pyc"),
        PathBuf::from("debug.log"),
        PathBuf::from("app.ts"),
        PathBuf::from("lib/helper.rs"),
    ];

    // Benchmark BrrrIgnore loading
    group.bench_function("load_ignore_patterns", |b| {
        b.iter(|| {
            let ignore = BrrrIgnore::new(black_box(root)).expect("BrrrIgnore::new failed");
            black_box(ignore)
        })
    });

    // Benchmark ignore checking
    let ignore = BrrrIgnore::new(root).expect("BrrrIgnore::new failed");
    group.bench_function("check_ignore_single", |b| {
        b.iter(|| {
            for path in &test_paths {
                black_box(ignore.is_ignored(path));
            }
        })
    });

    // Benchmark filter_paths
    let paths_refs: Vec<&Path> = test_paths.iter().map(|p| p.as_path()).collect();
    group.bench_function("filter_paths_batch", |b| {
        b.iter(|| {
            let filtered = ignore.filter_paths(black_box(paths_refs.clone()));
            black_box(filtered)
        })
    });

    // Benchmark default ignore check (fast path)
    group.bench_function("is_default_ignored", |b| {
        b.iter(|| {
            for path in &test_paths {
                black_box(is_default_ignored(path));
            }
        })
    });

    group.finish();
}

// =============================================================================
// Language Detection Benchmarks
// =============================================================================

fn bench_language_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("language_detection");

    let registry = LanguageRegistry::global();

    let test_paths = [
        PathBuf::from("src/main.py"),
        PathBuf::from("src/app.ts"),
        PathBuf::from("src/lib.rs"),
        PathBuf::from("src/handler.go"),
        PathBuf::from("src/Main.java"),
        PathBuf::from("src/util.c"),
        PathBuf::from("src/util.cpp"),
        PathBuf::from("src/unknown.xyz"),
    ];

    group.bench_function("detect_language_by_extension", |b| {
        b.iter(|| {
            for path in &test_paths {
                black_box(registry.detect_language(path));
            }
        })
    });

    group.bench_function("get_by_name", |b| {
        let names = ["python", "typescript", "rust", "go", "java", "c", "cpp"];
        b.iter(|| {
            for name in &names {
                black_box(registry.get_by_name(name));
            }
        })
    });

    group.finish();
}

// =============================================================================
// Multi-Language File Processing Benchmarks
// =============================================================================

fn bench_multi_language_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("multi_language_processing");

    // Create temp files for each language
    let temp_dir = TempDir::new().unwrap();
    let root = temp_dir.path();

    let py_path = create_temp_file(root, "module.py", SMALL_PYTHON);
    let ts_path = create_temp_file(root, "module.ts", MEDIUM_TYPESCRIPT);
    let rs_path = create_temp_file(root, "module.rs", LARGE_RUST);
    let go_path = create_temp_file(root, "module.go", SAMPLE_GO);
    let java_path = create_temp_file(root, "Module.java", SAMPLE_JAVA);
    let c_path = create_temp_file(root, "module.c", SAMPLE_C);
    let cpp_path = create_temp_file(root, "module.cpp", SAMPLE_CPP);

    // Individual language benchmarks
    group.bench_function("python_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&py_path)))
    });

    group.bench_function("typescript_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&ts_path)))
    });

    group.bench_function("rust_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&rs_path)))
    });

    group.bench_function("go_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&go_path)))
    });

    group.bench_function("java_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&java_path)))
    });

    group.bench_function("c_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&c_path)))
    });

    group.bench_function("cpp_e2e", |b| {
        b.iter(|| black_box(AstExtractor::extract_file(&cpp_path)))
    });

    group.finish();
}

// =============================================================================
// Batch Processing Benchmarks
// =============================================================================

fn bench_batch_processing(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_processing");

    // Create test files
    let temp_dir = TempDir::new().unwrap();
    let root = temp_dir.path();

    // Create 10 Python files
    let python_files: Vec<PathBuf> = (0..10)
        .map(|i| create_temp_file(root, &format!("module_{}.py", i), SMALL_PYTHON))
        .collect();

    // Create 10 TypeScript files
    let ts_files: Vec<PathBuf> = (0..10)
        .map(|i| create_temp_file(root, &format!("module_{}.ts", i), MEDIUM_TYPESCRIPT))
        .collect();

    // Create mixed language files
    let mixed_files: Vec<PathBuf> = (0..10)
        .map(|i| {
            let (name, content) = match i % 4 {
                0 => (format!("file_{}.py", i), SMALL_PYTHON),
                1 => (format!("file_{}.ts", i), MEDIUM_TYPESCRIPT),
                2 => (format!("file_{}.rs", i), LARGE_RUST),
                _ => (format!("file_{}.go", i), SAMPLE_GO),
            };
            create_temp_file(root, &name, content)
        })
        .collect();

    // Benchmark sequential processing of 10 Python files
    group.throughput(Throughput::Elements(10));
    group.bench_function("sequential_10_python_files", |b| {
        b.iter(|| {
            let mut results = Vec::with_capacity(10);
            for path in &python_files {
                results.push(AstExtractor::extract_file(path));
            }
            black_box(results)
        })
    });

    // Benchmark sequential processing of 10 TypeScript files
    group.bench_function("sequential_10_typescript_files", |b| {
        b.iter(|| {
            let mut results = Vec::with_capacity(10);
            for path in &ts_files {
                results.push(AstExtractor::extract_file(path));
            }
            black_box(results)
        })
    });

    // Benchmark sequential processing of mixed language files
    group.bench_function("sequential_10_mixed_files", |b| {
        b.iter(|| {
            let mut results = Vec::with_capacity(10);
            for path in &mixed_files {
                results.push(AstExtractor::extract_file(path));
            }
            black_box(results)
        })
    });

    group.finish();
}

// =============================================================================
// Project Scale Benchmarks
// =============================================================================

fn bench_project_scale(c: &mut Criterion) {
    let mut group = c.benchmark_group("project_scale");
    group.sample_size(20); // Reduce sample size for expensive operations

    // Benchmark different project sizes
    for size in [10, 25, 50].iter() {
        let project = create_large_test_project(*size);

        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(
            BenchmarkId::new("file_tree", size),
            &project,
            |b, project| {
                b.iter(|| {
                    let tree = get_tree(black_box(project.path().to_str().unwrap()), None);
                    black_box(tree)
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("code_structure", size),
            &project,
            |b, project| {
                b.iter(|| {
                    let structure =
                        get_structure(black_box(project.path().to_str().unwrap()), None, 0);
                    black_box(structure)
                })
            },
        );
    }

    group.finish();
}

// =============================================================================
// Memory Efficiency Benchmarks
// =============================================================================

fn bench_memory_efficiency(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_efficiency");

    // Create test files
    let temp_dir = TempDir::new().unwrap();
    let root = temp_dir.path();

    let large_py_path = create_temp_file(root, "large.py", SMALL_PYTHON);
    let large_ts_path = create_temp_file(root, "large.ts", MEDIUM_TYPESCRIPT);
    let large_rs_path = create_temp_file(root, "large.rs", LARGE_RUST);

    // Benchmark repeated extraction (tests memory cleanup)
    group.bench_function("repeated_python_extraction", |b| {
        b.iter_batched(
            || large_py_path.clone(),
            |path| {
                for _ in 0..5 {
                    let _ = black_box(AstExtractor::extract_file(&path));
                }
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("repeated_typescript_extraction", |b| {
        b.iter_batched(
            || large_ts_path.clone(),
            |path| {
                for _ in 0..5 {
                    let _ = black_box(AstExtractor::extract_file(&path));
                }
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("repeated_rust_extraction", |b| {
        b.iter_batched(
            || large_rs_path.clone(),
            |path| {
                for _ in 0..5 {
                    let _ = black_box(AstExtractor::extract_file(&path));
                }
            },
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

// =============================================================================
// Source Parsing Benchmarks
// =============================================================================

fn bench_source_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("source_parsing");

    // Benchmark parsing from source string directly
    group.bench_function("parse_python_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(SMALL_PYTHON), "python");
            black_box(result)
        })
    });

    group.bench_function("parse_typescript_from_source", |b| {
        b.iter(|| {
            let result =
                AstExtractor::extract_from_source(black_box(MEDIUM_TYPESCRIPT), "typescript");
            black_box(result)
        })
    });

    group.bench_function("parse_rust_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(LARGE_RUST), "rust");
            black_box(result)
        })
    });

    group.bench_function("parse_go_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(SAMPLE_GO), "go");
            black_box(result)
        })
    });

    group.bench_function("parse_java_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(SAMPLE_JAVA), "java");
            black_box(result)
        })
    });

    group.bench_function("parse_c_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(SAMPLE_C), "c");
            black_box(result)
        })
    });

    group.bench_function("parse_cpp_from_source", |b| {
        b.iter(|| {
            let result = AstExtractor::extract_from_source(black_box(SAMPLE_CPP), "cpp");
            black_box(result)
        })
    });

    group.finish();
}

// =============================================================================
// Criterion Group Configuration
// =============================================================================

criterion_group!(
    name = e2e_benches;
    config = Criterion::default()
        .significance_level(0.05)
        .measurement_time(std::time::Duration::from_secs(10));
    targets =
        bench_full_file_analysis,
        bench_code_structure_extraction,
        bench_project_scanning,
        bench_ignore_patterns,
        bench_language_detection,
        bench_multi_language_processing,
        bench_batch_processing,
        bench_project_scale,
        bench_memory_efficiency,
        bench_source_parsing,
);

criterion_main!(e2e_benches);
