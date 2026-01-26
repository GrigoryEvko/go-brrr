# go-brrr

Token-efficient code analysis for LLMs - High-performance Rust implementation.

```
 ____  ____  ____  ____
| __ )|  _ \|  _ \|  _ \
|  _ \| |_) | |_) | |_) |
| |_) |  _ <|  _ <|  _ <
|____/|_| \_\_| \_\_| \_\
```

[![Crates.io](https://img.shields.io/crates/v/go-brrr.svg)](https://crates.io/crates/go-brrr)
[![Rust](https://img.shields.io/badge/rust-1.70+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A blazing-fast CLI tool for extracting structured code information optimized for feeding context to Large Language Models. Achieves up to 95% token savings compared to raw source code by providing structured summaries, call graphs, and semantic search capabilities.

## Installation

```bash
cargo install go-brrr
```

Or from source:

```bash
git clone https://github.com/GrigoryEvko/go-brrr
cd go-brrr
cargo install --path brrr-cli
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

## Features

- **AST Analysis** - File tree, code structure, full extraction with tree-sitter
- **Control Flow** - CFG, DFG, program slicing, PDG generation
- **Call Graph** - Cross-file analysis, impact analysis, dead code detection
- **Semantic Search** - Embedding-based natural language code search
- **Security Scanning** - SQL injection, XSS, command injection, secrets, and more
- **Code Metrics** - Cyclomatic/cognitive complexity, Halstead, maintainability index
- **Code Quality** - Clone detection, god class, long method, circular dependencies

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

## Documentation

For full documentation, see the [GitHub repository](https://github.com/GrigoryEvko/go-brrr).

## License

Apache-2.0
