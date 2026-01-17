# go-brrr

Token-efficient code analysis for LLMs - High-performance Rust implementation.

```
 ____  ____  ____  ____
| __ )|  _ \|  _ \|  _ \
|  _ \| |_) | |_) | |_) |
| |_) |  _ <|  _ <|  _ <
|____/|_| \_\_| \_\_| \_\
```

[![Rust](https://img.shields.io/badge/rust-1.70+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A blazing-fast CLI tool for extracting structured code information optimized for feeding context to Large Language Models. Achieves up to 95% token savings compared to raw source code by providing structured summaries, call graphs, and semantic search capabilities.

## Features

### AST Analysis
- **File Tree** - JSON-structured directory traversal with extension filtering
- **Code Structure** - Extract functions, classes, methods, and docstrings
- **Full Extraction** - Complete AST analysis with type information and decorators

### Control Flow Analysis
- **CFG** - Control flow graph generation with Mermaid/DOT export
- **DFG** - Data flow graph showing variable dependencies
- **Program Slicing** - Backward/forward slicing to find affected code paths
- **PDG** - Program Dependence Graph combining CFG and DFG

### Call Graph Analysis
- **Cross-file Call Graph** - Build project-wide function call relationships
- **Impact Analysis** - Find all callers of a function (transitive)
- **Dead Code Detection** - Identify unreachable functions
- **Architectural Layers** - Detect entry/middle/leaf layer patterns
- **Import Analysis** - Parse and trace module imports

### Semantic Search
- **Embedding-based Search** - Natural language code search using vector similarity
- **TEI Integration** - gRPC client for text-embeddings-inference server
- **HNSW Index** - Fast approximate nearest neighbor search via usearch
- **Multi-language Index** - Unified index across all supported languages

### Security Scanning
- **SQL Injection** (CWE-89) - Detect unsafe query construction
- **Command Injection** (CWE-78) - Find shell execution vulnerabilities
- **XSS** (CWE-79) - Cross-site scripting detection for JS/TS
- **Path Traversal** (CWE-22) - Directory traversal vulnerabilities
- **Secrets Detection** (CWE-798) - Hardcoded credentials and API keys
- **Weak Cryptography** (CWE-327) - Insecure algorithm usage
- **Unsafe Deserialization** (CWE-502) - Pickle, YAML, ObjectInputStream
- **ReDoS** (CWE-1333) - Regular expression denial of service
- **Taint Analysis** - Track data flow from sources to sinks
- **SARIF Output** - GitHub/GitLab security tab integration

### Code Metrics
- **Cyclomatic Complexity** - Branch and loop complexity measurement
- **Cognitive Complexity** - SonarSource methodology for understandability
- **Halstead Metrics** - Vocabulary, volume, difficulty, effort, bugs estimate
- **Maintainability Index** - Combined metric with comment bonus
- **Lines of Code** - Physical, logical, source, and comment LOC
- **Nesting Depth** - Deep nesting detection with suggestions
- **Function Size** - SLOC, parameters, variables, return points
- **Coupling** - Afferent/efferent coupling and instability metrics
- **Cohesion** - LCOM variants for class quality

### Code Quality
- **Clone Detection** - Textual (Type-1) and structural (Type-2/3) duplicates
- **God Class Detection** - SRP violations with weighted scoring
- **Long Method Detection** - Oversized functions with extraction suggestions
- **Circular Dependencies** - Package/module/class/function level cycles
- **Design Pattern Detection** - Singleton, Factory, Builder, Observer, etc.

### Performance Optimizations
- **jemalloc** - High-performance memory allocator
- **SIMD Operations** - portable_simd for vectorized computations
- **Parallel Processing** - Rayon for multi-threaded file analysis
- **Aho-Corasick** - Multi-pattern string matching
- **PHF** - Compile-time perfect hash functions for O(1) keyword lookups
- **FxHash** - Fast non-cryptographic hashing
- **xxHash** - SIMD-accelerated hashing (xxh3)

## Installation

### From Source

```bash
# Clone the repository
git clone https://github.com/GrigoryEvko/go-brrr
cd go-brrr

# Build with release optimizations
cargo build --release

# Install to ~/.cargo/bin
cargo install --path .
```

### Requirements

- Rust 1.70+ (nightly required for `portable_simd` feature)
- For semantic search: TEI server or local embedding model

```bash
# Set nightly toolchain (required for SIMD)
rustup override set nightly
```

## Quick Start

```bash
# Show file tree
brrr tree ./src --ext .rs

# Extract code structure
brrr structure . --lang rust

# Full file analysis
brrr extract src/main.rs

# Build call graph
brrr calls ./src

# Find dead code
brrr dead ./src

# Control flow graph
brrr cfg src/main.rs main

# Security scan
brrr security scan ./src

# Code metrics report
brrr metrics report ./src

# Semantic search (requires index)
brrr semantic index .
brrr semantic search "authentication handler" .
```

## Commands Reference

### File Operations

#### tree
Display directory structure in JSON format.

```bash
brrr tree ./src                     # Default tree
brrr tree ./src --ext .rs .toml     # Filter by extensions
brrr tree ./src --show-hidden       # Include dotfiles
brrr tree ./src --max-depth 3       # Limit depth
```

#### structure
Extract functions, classes, and methods from source files.

```bash
brrr structure .                    # Current directory
brrr structure ./src --lang python  # Specific language
brrr structure ./src --limit 100    # Limit files analyzed
```

#### extract
Full AST extraction from a single file.

```bash
brrr extract src/main.py
brrr extract src/api.py --class UserController
brrr extract src/api.py --function process_data
brrr extract src/api.py --method UserController.get_user
```

#### search
Regex pattern search with context lines.

```bash
brrr search "def process" ./src
brrr search "async fn" ./src --ext .rs
brrr search "TODO" . -C 2 --max 50
```

### Flow Analysis

#### cfg
Generate control flow graph for a function.

```bash
brrr cfg src/main.py process_data
brrr cfg src/main.rs handle_request --format mermaid
brrr cfg src/main.go Process --format dot
```

Output formats: `json` (default), `mermaid`, `dot`

#### dfg
Generate data flow graph showing variable dependencies.

```bash
brrr dfg src/processor.py process_data
brrr dfg src/handler.rs handle --lang rust
```

#### slice
Compute program slice - find lines affecting or affected by a target line.

```bash
# Backward slice: what affects line 42?
brrr slice src/main.py process 42

# Forward slice: what does line 10 affect?
brrr slice src/main.py process 10 --direction forward

# Track specific variable
brrr slice src/main.py process 42 --var result

# Extended output with metrics
brrr slice src/main.py process 42 --extended
```

### Call Graph Analysis

#### calls
Build cross-file call graph.

```bash
brrr calls ./src
brrr calls ./src --lang python
brrr calls ./src --extended      # Include call line numbers
```

#### impact
Find all callers of a function (reverse call graph).

```bash
brrr impact process_data ./src
brrr impact get_user ./src --depth 5
brrr impact critical_func ./src --file api
```

#### dead
Find unreachable (dead) code.

```bash
brrr dead ./src
brrr dead ./src --entry main cli   # Additional entry points
brrr dead ./src --lang python
```

#### arch
Detect architectural layers from call patterns.

```bash
brrr arch ./src
brrr arch ./src --lang typescript
```

### Import Analysis

#### imports
Parse import statements from a source file.

```bash
brrr imports src/main.py
brrr imports src/index.ts --lang typescript
```

#### importers
Find all files that import a module.

```bash
brrr importers json ./src
brrr importers UserController ./src --lang python
```

#### change-impact
Find tests affected by changed files.

```bash
brrr change-impact src/api.py           # Specific files
brrr change-impact --git                 # Use git diff
brrr change-impact --session             # Use session-modified files
brrr change-impact --run                 # Actually run affected tests
```

### Semantic Search

#### semantic index
Build semantic index for a project.

```bash
brrr semantic index .
brrr semantic index ./src --lang python
brrr semantic index . --model all-MiniLM-L6-v2   # Smaller model (80MB)
brrr semantic index . --backend tei              # Use TEI server
```

#### semantic search
Search code using natural language queries.

```bash
brrr semantic search "authentication logic" .
brrr semantic search "database connection" ./src --k 10
brrr semantic search "error handling" . --expand   # Include call graph
brrr semantic search "user validation" . --task code_retrieval
```

#### semantic cache
Manage the semantic index cache.

```bash
brrr semantic cache stats       # Show cache statistics
brrr semantic cache clear       # Clear all cached indexes
brrr semantic cache invalidate  # Invalidate specific project
```

#### semantic device
Show compute device and backend info.

```bash
brrr semantic device
```

### Security Scanning

#### security scan
Run all security analyzers.

```bash
brrr security scan ./src
brrr security scan ./src --severity high      # Only high/critical
brrr security scan ./src --format sarif       # SARIF output for CI
brrr security scan ./src --category injection # Only injection issues
brrr security scan ./src --fail-on high       # Exit 1 if high+ found
```

#### Individual Scanners

```bash
brrr security sql-injection ./src
brrr security command-injection ./src
brrr security xss ./src
brrr security path-traversal ./src
brrr security secrets ./src
brrr security crypto ./src
brrr security deserialization ./src
brrr security redos ./src
```

### Code Metrics

#### metrics report
Generate comprehensive metrics report.

```bash
brrr metrics report ./src
brrr metrics ./src                           # Shorthand
brrr metrics ./src --format text
brrr metrics ./src --fail-on critical        # CI quality gate
brrr metrics ./src --thresholds strict       # Stricter thresholds
```

#### metrics complexity
Calculate cyclomatic complexity.

```bash
brrr metrics complexity ./src
brrr metrics complexity ./src --threshold 10 --sort
brrr metrics complexity ./src --violations-only
```

#### metrics cognitive
Calculate cognitive complexity (SonarSource methodology).

```bash
brrr metrics cognitive ./src
brrr metrics cognitive ./src --breakdown     # Detailed contributions
```

#### metrics halstead
Calculate Halstead complexity metrics.

```bash
brrr metrics halstead ./src
brrr metrics halstead ./src --sort-by-difficulty
brrr metrics halstead ./src --show-tokens
```

#### metrics maintainability
Calculate Maintainability Index.

```bash
brrr metrics maintainability ./src
brrr metrics maintainability ./src --threshold 50 --sort
brrr metrics maintainability ./src --include-comments
```

#### metrics loc
Calculate lines of code metrics.

```bash
brrr metrics loc ./src
brrr metrics loc ./src --by-language
brrr metrics loc ./src --function-threshold 50 --violations-only
```

#### metrics nesting
Calculate nesting depth metrics.

```bash
brrr metrics nesting ./src
brrr metrics nesting ./src --threshold 5 --details
```

#### metrics functions
Calculate function size metrics.

```bash
brrr metrics functions ./src
brrr metrics functions ./src --sort-by sloc --violations-only
brrr metrics functions ./src --sloc-warn 30 --sloc-critical 60
```

#### metrics coupling
Calculate coupling metrics for modules.

```bash
brrr metrics coupling ./src
brrr metrics coupling ./src --level module
brrr metrics coupling ./src --show-cycles --show-edges
```

#### metrics cohesion
Calculate class cohesion metrics (LCOM variants).

```bash
brrr metrics cohesion ./src
brrr metrics cohesion ./src --threshold 2 --show-components
```

### Code Quality

#### quality clones
Detect code clones (duplicate code).

```bash
brrr quality clones ./src
brrr quality clones ./src --min-lines 10
brrr quality clones ./src --include-tests
```

#### quality structural-clones
Detect structural code clones (Type-2/Type-3).

```bash
brrr quality structural-clones ./src
brrr quality structural-clones ./src --similarity 0.8
brrr quality structural-clones ./src --type2-only
```

#### quality god-class
Detect God classes violating SRP.

```bash
brrr quality god-class ./src
brrr quality god-class ./src --threshold 15
brrr quality god-class ./src --method-threshold 20 --attribute-threshold 15
```

#### quality long-method
Detect long methods with extraction suggestions.

```bash
brrr quality long-method ./src
brrr quality long-method ./src --max-lines 30 --max-complexity 10
brrr quality long-method ./src --show-suggestions
brrr quality long-method ./src --strict   # Stricter thresholds
```

#### quality circular
Detect circular dependencies.

```bash
brrr quality circular ./src
brrr quality circular ./src --level function
brrr quality circular ./src --max-suggestions 20
```

#### quality patterns
Detect design patterns.

```bash
brrr quality patterns ./src
brrr quality patterns ./src --pattern singleton
brrr quality patterns ./src --min-confidence 0.7
```

### Diagnostics

#### diagnostics
Run type checker and linter.

```bash
brrr diagnostics src/main.py
brrr diagnostics ./src --project
brrr diagnostics ./src --no-lint    # Type checker only
```

#### doctor
Check and install diagnostic tools.

```bash
brrr doctor                   # Check all tools
brrr doctor --json            # JSON output
brrr doctor --install python  # Install Python tools
```

### Daemon Management

#### daemon start
Start background daemon for faster queries.

```bash
brrr daemon start
brrr daemon start -p /path/to/project
```

#### daemon stop
Stop the daemon gracefully.

```bash
brrr daemon stop
```

#### daemon status
Check daemon status.

```bash
brrr daemon status
```

#### daemon notify
Notify daemon of file changes.

```bash
brrr daemon notify src/changed_file.py
```

### Cache Management

#### warm
Pre-build call graph cache.

```bash
brrr warm ./src --lang python
brrr warm ./src --lang all --background
```

## Configuration

### .brrrignore

Create a `.brrrignore` file in your project root to exclude files from analysis. Uses gitignore syntax.

```gitignore
# Dependencies
node_modules/
.venv/
vendor/
target/

# Build outputs
dist/
build/
*.pyc

# IDE files
.idea/
.vscode/

# Security - always exclude
.env
*.pem
*.key
credentials.*

# Custom patterns
large_test_fixtures/
```

### .brrr/config.toml

Project-specific configuration (optional).

```toml
[general]
default_language = "python"

[metrics]
cyclomatic_threshold = 10
cognitive_threshold = 15
maintainability_threshold = 50

[security]
fail_on_severity = "high"
include_suppressed = false

[semantic]
model = "bge-large-en-v1.5"
backend = "auto"
```

## Supported Languages

| Language | Tree-sitter | Call Graph | Metrics | Security |
|----------|-------------|------------|---------|----------|
| Python | Yes | Yes | Yes | Full |
| TypeScript | Yes | Yes | Yes | Full |
| JavaScript | Yes | Yes | Yes | Full |
| Go | Yes | Yes | Yes | Full |
| Rust | Yes | Yes | Yes | Full |
| Java | Yes | Yes | Yes | Full |
| C | Yes | Yes | Yes | Partial |
| C++ | Yes | Yes | Yes | Partial |

Additional languages supported for structure extraction only:
Ruby, PHP, Kotlin, Swift, C#, Scala, Lua, Elixir

## Architecture

### Core Components

```
src/
|-- ast/          # AST extraction, file tree, code structure
|-- callgraph/    # Cross-file call graph, impact analysis, dead code
|-- cfg/          # Control flow graph builder and rendering
|-- dfg/          # Data flow graph and program slicing
|-- pdg/          # Program Dependence Graph (CFG + DFG)
|-- embedding/    # Vector index (usearch) and TEI gRPC client
|-- semantic/     # Semantic search, code chunking, unit extraction
|-- lang/         # Language-specific tree-sitter configurations
|-- metrics/      # All complexity and quality metrics
|-- security/     # Vulnerability scanners and taint analysis
|-- quality/      # Code smells, clones, patterns
|-- simd.rs       # SIMD-accelerated operations
|-- util/         # Path validation, ignore patterns, helpers
```

### Tree-sitter Integration

All parsing is done through tree-sitter for consistent, fast, and accurate AST extraction across languages. Language grammars are included as dependencies:

- `tree-sitter` 0.26
- `tree-sitter-python` 0.25
- `tree-sitter-typescript` 0.23
- `tree-sitter-go` 0.25
- `tree-sitter-rust` 0.24
- `tree-sitter-java` 0.23
- `tree-sitter-c` 0.24
- `tree-sitter-cpp` 0.23

### Embedding Pipeline

1. Extract code units (functions, classes) via AST
2. Generate embeddings via TEI server or local model
3. Build HNSW index using usearch
4. Store metadata in JSON sidecar file
5. Search returns keys mapping back to units

### SIMD Optimizations

The `src/simd.rs` module provides portable SIMD operations:

- `sum_f32` / `dot_product` - 8x speedup for embedding similarity
- `count_byte` / `find_newlines` - 32x speedup for line counting
- `all_equal` - Fast duplicate detection
- `cosine_similarity` - Vectorized similarity computation
- `find_matching_u32` - Fast edge filtering in dataflow analysis

Targets: x86_64 (SSE2/AVX2/AVX-512), aarch64 (NEON)

## Performance

### Key Optimizations

| Optimization | Impact | Use Case |
|--------------|--------|----------|
| jemalloc | 10-20% faster allocation | Heavy object creation |
| SIMD dot product | 8x throughput | Embedding similarity |
| SIMD byte search | 32x throughput | Line counting |
| Rayon parallelism | Linear scaling | Multi-file analysis |
| FxHash | 2x faster hashing | Hash maps |
| PHF | O(1) keyword lookup | Language detection |
| Aho-Corasick | Multi-pattern matching | Pattern detection |
| usearch HNSW | Sub-linear search | Semantic search |
| LRU cache | Avoid recomputation | Query embeddings |

### Benchmarks

Run benchmarks with:

```bash
cargo bench
```

Available benchmarks:
- `ast_parsing` - Tree-sitter parse performance
- `ast_extraction` - Full file extraction
- `flow_analysis` - CFG/DFG construction
- `semantic` - Embedding and search
- `callgraph` - Call graph building
- `e2e` - End-to-end scenarios

## Output Formats

Most commands support multiple output formats:

- **json** (default) - Structured JSON for programmatic use
- **text** - Human-readable text output
- **mermaid** - Mermaid diagram syntax (CFG)
- **dot** - Graphviz DOT format (CFG)
- **sarif** - SARIF v2.1 for security findings (CI/CD integration)
- **csv** - CSV format for metrics export

## Global Options

```bash
--no-ignore     # Ignore .brrrignore patterns
-v, -vv, -vvv   # Verbosity levels (info, debug, trace)
--format        # Output format (json, text, mermaid, dot, csv)
```

## Exit Codes

- `0` - Success
- `1` - Error or findings above fail threshold
- `2` - Invalid arguments

## Environment Variables

```bash
BRRR_LOG=debug          # Set log level
BRRR_TEI_URL=...        # TEI server URL for semantic search
RUST_BACKTRACE=1        # Enable backtraces for debugging
```

## Suppressing Security Findings

Add inline comments to suppress specific findings:

```python
# brrr-ignore: SQLI-001
cursor.execute(query)  # Known safe

# Also supports:
# nosec
# noqa
# security-ignore
```

## License

Apache-2.0

## Contributing

Contributions are welcome. Please ensure:

1. Code passes `cargo clippy` without warnings
2. All tests pass: `cargo test`
3. New features include tests
4. Documentation is updated

## Related Projects

- [tree-sitter](https://tree-sitter.github.io/tree-sitter/) - Incremental parsing
- [usearch](https://github.com/unum-cloud/usearch) - Vector search
- [text-embeddings-inference](https://github.com/huggingface/text-embeddings-inference) - Embedding server
