# go-brrr

Token-efficient code analysis for LLMs with formally verified foundations.

```
 ____  ____  ____  ____
| __ )|  _ \|  _ \|  _ \
|  _ \| |_) | |_) | |_) |
| |_) |  _ <|  _ <|  _ <
|____/|_| \_\_| \_\_| \_\
```

[![Crates.io](https://img.shields.io/crates/v/go-brrr.svg)](https://crates.io/crates/go-brrr)
[![Rust](https://img.shields.io/badge/rust-1.70+-orange.svg)](https://www.rust-lang.org/)
[![F*](https://img.shields.io/badge/F*-verified-green.svg)](https://www.fstar-lang.org/)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A high-performance code analysis toolkit that extracts structured information from source code, optimized for feeding context to Large Language Models. Achieves up to **95% token savings** compared to raw source code.

The project combines a practical Rust CLI with formally verified analysis algorithms specified in F*, ensuring both performance and correctness.

## Architecture

```
go-brrr/
+-- brrr-cli/         Rust CLI - practical code analysis tool
+-- brrr-repr/        Rust library - IR types, expressions, effects
+-- brrr-lang/        F* specification - formal type system
+-- brrr-machine/     F* framework - verified static analysis
```

```
                      Formal Verification Layer
          +-------------------------------------------+
          |                                           |
          |  brrr-lang (F*)        brrr-machine (F*)  |
          |  Type System           IFDS, Taint, CPG   |
          |  Specification         Analysis Proofs    |
          |                                           |
          +-------------------------------------------+
                              |
                              | Verified Interface
                              v
          +-------------------------------------------+
          |                                           |
          |  brrr-repr (Rust)      brrr-cli (Rust)   |
          |  IR Data Structures    CLI Tool          |
          |  Encodings             tree-sitter       |
          |                                           |
          +-------------------------------------------+
```

## Quick Start

```bash
# Install from crates.io
cargo install go-brrr

# Or build from source
git clone https://github.com/GrigoryEvko/go-brrr
cd go-brrr
cargo install --path brrr-cli
```

```bash
# File tree (JSON)
brrr tree ./src --ext .rs

# Extract code structure
brrr structure . --lang rust

# Build call graph
brrr calls ./src

# Control flow graph
brrr cfg src/main.rs main --format mermaid

# Security scan
brrr security scan ./src

# Code metrics
brrr metrics report ./src

# Semantic search
brrr semantic index .
brrr semantic search "authentication handler" .
```

## Components

### brrr-cli

Rust CLI for practical code analysis with tree-sitter.

| Feature | Description |
|---------|-------------|
| **AST Analysis** | File tree, code structure, full extraction |
| **Control Flow** | CFG, DFG, program slicing, PDG |
| **Call Graph** | Cross-file analysis, impact analysis, dead code |
| **Semantic Search** | Embedding-based natural language code search |
| **Security Scanning** | SQL injection, XSS, command injection, secrets |
| **Code Metrics** | Cyclomatic, cognitive, Halstead, maintainability |
| **Code Quality** | Clone detection, god class, circular dependencies |

### brrr-repr

Rust library for the intermediate representation.

| Module | Description |
|--------|-------------|
| `types` | 12 type constructors: primitives, functions, structs, enums |
| `expr` | 53 expression variants covering all language constructs |
| `effects` | Row-polymorphic effect system with handlers |
| `modes` | Linear, affine, and relevant type tracking |
| `session` | Binary and multiparty session types |
| `verification` | Contracts, formulas, VC generation |
| `encoding` | Binary (`.brrr`) and text (`.brrrx`) formats |

### brrr-lang

F* formal specification for the type system.

| Module | Description |
|--------|-------------|
| `BrrrTypes.fst` | Main type system (12 constructors) |
| `Effects.fst` | Effect algebra and row types |
| `Modes.fst` | Ownership modes (owned, borrowed, shared) |
| `BorrowChecker.fst` | Borrow checking specification |
| `SessionTypes.fst` | Binary session types |
| `TypeChecker.fst` | Bidirectional type checking |

### brrr-machine

F* verified static analysis framework.

| Module | Lines | Description |
|--------|-------|-------------|
| `IFDS.fst` | 2,166 | Context-sensitive interprocedural analysis |
| `IFDSTaint.fst` | 3,328 | Taint analysis on IFDS |
| `GaloisConnection.fst` | 1,786 | Abstract interpretation foundations |
| `CPG.fst` | 1,264 | Unified Code Property Graph |
| `Traversal.fst` | 1,137 | Graph traversal and queries |

**Verification Status**: 14,711 lines of F* code, 0 admits.

## Features

### AST Analysis

```bash
brrr tree ./src --ext .rs .toml    # File tree with filtering
brrr structure . --lang python      # Functions, classes, methods
brrr extract src/main.py            # Full AST extraction
brrr search "async fn" ./src        # Regex search
```

### Control Flow

```bash
brrr cfg src/main.py process        # Control flow graph
brrr dfg src/handler.rs handle      # Data flow graph
brrr slice src/main.py func 42      # Program slice at line 42
```

### Call Graph

```bash
brrr calls ./src                    # Cross-file call graph
brrr impact process_data ./src      # Find all callers
brrr dead ./src                     # Dead code detection
brrr arch ./src                     # Architectural layers
```

### Security Scanning

```bash
brrr security scan ./src                    # All scanners
brrr security scan ./src --format sarif    # SARIF output for CI
brrr security sql-injection ./src          # Individual scanner
brrr security secrets ./src                # Hardcoded credentials
```

Detects: SQL injection (CWE-89), command injection (CWE-78), XSS (CWE-79), path traversal (CWE-22), secrets (CWE-798), weak crypto (CWE-327), unsafe deserialization (CWE-502), ReDoS (CWE-1333).

### Code Metrics

```bash
brrr metrics report ./src           # Full report
brrr metrics complexity ./src       # Cyclomatic complexity
brrr metrics cognitive ./src        # Cognitive complexity
brrr metrics halstead ./src         # Halstead metrics
brrr metrics maintainability ./src  # Maintainability index
```

### Semantic Search

```bash
brrr semantic index .                           # Build index
brrr semantic search "error handling" ./src     # Natural language
brrr semantic search "user auth" . --expand    # Include call graph
```

## Supported Languages

| Language | Tree-sitter | Call Graph | Metrics | Security |
|----------|:-----------:|:----------:|:-------:|:--------:|
| Python | Yes | Yes | Yes | Full |
| TypeScript | Yes | Yes | Yes | Full |
| JavaScript | Yes | Yes | Yes | Full |
| Go | Yes | Yes | Yes | Full |
| Rust | Yes | Yes | Yes | Full |
| Java | Yes | Yes | Yes | Full |
| C/C++ | Yes | Yes | Yes | Partial |

Additional structure extraction: Ruby, PHP, Kotlin, Swift, C#, Scala, Lua, Elixir.

## Performance

| Optimization | Impact |
|--------------|--------|
| jemalloc | 10-20% faster allocation |
| SIMD dot product | 8x embedding similarity |
| Rayon parallelism | Linear multi-core scaling |
| PHF | O(1) keyword lookup |
| usearch HNSW | Sub-linear semantic search |

## Configuration

### .brrrignore

```gitignore
node_modules/
.venv/
target/
*.pyc
.env
```

### .brrr/config.toml

```toml
[general]
default_language = "python"

[metrics]
cyclomatic_threshold = 10
cognitive_threshold = 15

[security]
fail_on_severity = "high"
```

## Building from Source

### Rust Components (brrr-cli, brrr-repr)

```bash
# Requires Rust 1.70+ (nightly for SIMD)
rustup override set nightly

cargo build --release
cargo test
cargo install --path brrr-cli
```

### F* Components (brrr-lang, brrr-machine)

```bash
# Requires F* 2024.01.13+ and Z3 4.8.5+
opam install fstar

cd brrr-lang && make verify
cd brrr-machine/src && make verify
```

## Theoretical Foundations

The F* verification layer is based on foundational work:

- **IFDS**: Reps, Horwitz, Sagiv 1995 - Interprocedural dataflow via graph reachability
- **Abstract Interpretation**: Cousot & Cousot 1977 - Galois connections
- **CPG**: Yamaguchi 2014 - Code Property Graphs for vulnerability discovery
- **Session Types**: Honda 1993 - Protocol verification

## Related Projects

- [tree-sitter](https://tree-sitter.github.io/tree-sitter/) - Incremental parsing
- [usearch](https://github.com/unum-cloud/usearch) - Vector search
- [F*](https://www.fstar-lang.org/) - Proof-oriented programming
- [text-embeddings-inference](https://github.com/huggingface/text-embeddings-inference) - Embedding server

## License

Apache-2.0

## Author

Grigory Evko <grigory@evko.io>

---

[GitHub](https://github.com/GrigoryEvko/go-brrr) | [Issues](https://github.com/GrigoryEvko/go-brrr/issues)
