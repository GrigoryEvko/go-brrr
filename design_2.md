# TLDR: Universal Code Intelligence Platform

## Design Document v2.0

---

# Table of Contents

1. [Vision & Goals](#1-vision--goals)
2. [Architecture Overview](#2-architecture-overview)
3. [Core Abstractions](#3-core-abstractions)
4. [Layer 1: Parse](#4-layer-1-parse)
5. [Layer 2: Graph](#5-layer-2-graph)
6. [Layer 3: Index](#6-layer-3-index)
7. [Layer 4: Analysis](#7-layer-4-analysis)
8. [Layer 5: Correlation](#8-layer-5-correlation)
9. [Layer 6: Query](#9-layer-6-query)
10. [Layer 7: Output](#10-layer-7-output)
11. [Analysis Domains](#11-analysis-domains) (15 domains including Bundle Diff)
12. [Multi-Language Strategy](#12-multi-language-strategy)
13. [Performance Architecture](#13-performance-architecture)
14. [Extension System](#14-extension-system)
15. [RAG System Architecture](#15-rag-system-architecture)
16. [Daemon Mode](#16-daemon-mode)
17. [Special Cases](#17-special-cases) (Generated Code, Polyglot, Monorepo, Offline)
18. [Implementation Roadmap](#18-implementation-roadmap)

---

# 1. Vision & Goals

## 1.1 Vision

Build the most comprehensive code intelligence platform that understands code at every level—from individual expressions to entire systems, from static structure to runtime behavior, from current state to historical evolution.

## 1.2 Core Principles

1. **Complete Coverage** - No aspect of code analysis left uncovered
2. **Language Agnostic** - Unified abstractions that work across all languages
3. **Static + Dynamic** - Combine compile-time analysis with runtime data
4. **Incremental** - Fast updates on code changes
5. **Queryable** - Answer any question about the codebase
6. **LLM-Ready** - Output optimized for AI consumption

## 1.3 What We Analyze

| Dimension | Question Answered |
|-----------|-------------------|
| **Structure** | What IS the code? |
| **Behavior** | What does the code DO? |
| **Quality** | How GOOD is the code? |
| **Security** | Is the code SAFE? |
| **Performance** | Is the code FAST? |
| **Evolution** | How has the code CHANGED? |
| **Boundaries** | How do pieces CONNECT? |
| **Semantics** | What does the code MEAN? |
| **Prediction** | What MIGHT go wrong? |
| **Runtime** | What ACTUALLY happens? |

---

# 2. Architecture Overview

## 2.1 Layer Stack

```
┌─────────────────────────────────────────────────────────────────┐
│                      QUERY INTERFACE                             │
│         (CLI, LSP, API, LLM Context Builder)                    │
├─────────────────────────────────────────────────────────────────┤
│                      OUTPUT LAYER                                │
│         (JSON, Text, HTML, Graphs, LLM-Optimized)               │
├─────────────────────────────────────────────────────────────────┤
│                    ANALYSIS LAYER                                │
│  ┌──────────┬──────────┬──────────┬──────────┬──────────┐      │
│  │Structure │Behavior  │Quality   │Security  │Performance│      │
│  ├──────────┼──────────┼──────────┼──────────┼──────────┤      │
│  │Evolution │Boundaries│Semantics │Prediction│ Runtime  │      │
│  └──────────┴──────────┴──────────┴──────────┴──────────┘      │
├─────────────────────────────────────────────────────────────────┤
│                   CORRELATION LAYER                              │
│         (Static ↔ Dynamic, Cross-Language Links)                │
├─────────────────────────────────────────────────────────────────┤
│                      INDEX LAYER                                 │
│         (Symbol Index, Semantic Index, Graph Index)             │
├─────────────────────────────────────────────────────────────────┤
│                      GRAPH LAYER                                 │
│  ┌─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┐            │
│  │ AST │ CFG │ DFG │ PDG │Call │Type │Dep  │Bind │            │
│  └─────┴─────┴─────┴─────┴─────┴─────┴─────┴─────┘            │
├─────────────────────────────────────────────────────────────────┤
│                      PARSE LAYER                                 │
│         (Tree-sitter, Language Plugins, Normalization)          │
├─────────────────────────────────────────────────────────────────┤
│                      SOURCE LAYER                                │
│         (Files, VCS, Remote, Virtual)                           │
└─────────────────────────────────────────────────────────────────┘
```

## 2.2 Data Flow

```
Source Code ──► Parse ──► Graphs ──► Index ──► Analysis ──► Output
                 │          │          │           │
                 ▼          ▼          ▼           ▼
              Cache      Cache      Cache      Results
                 │          │          │           │
                 └──────────┴──────────┴───────────┘
                              │
                    Incremental Update
```

## 2.3 Cross-Cutting Concerns

- **Parallelism**: Rayon-based parallel processing at every layer
- **Caching**: Multi-level cache (memory → mmap → disk)
- **Incremental**: Dependency tracking for minimal recomputation
- **Streaming**: Handle files larger than memory
- **Extensibility**: Plugin points at each layer

---

# 3. Core Abstractions

## 3.1 Universal Code Unit

The fundamental unit of analysis, language-agnostic:

| Concept | Description | Examples |
|---------|-------------|----------|
| **Module** | Compilation unit | File, package, crate |
| **Container** | Grouping construct | Class, struct, module, namespace |
| **Callable** | Executable unit | Function, method, closure, lambda |
| **Binding** | Name-value association | Variable, constant, parameter |
| **Reference** | Usage of a binding | Read, write, call |
| **Type** | Data shape | Primitive, composite, generic |

## 3.2 Universal Graph Node

Every graph node has:
- **Identity**: Unique within project
- **Location**: File, line, column, byte range
- **Kind**: Node type in the graph
- **Attributes**: Language-specific metadata
- **Relations**: Edges to other nodes

## 3.3 Universal Edge

Every edge has:
- **Source** and **Target** nodes
- **Kind**: Relationship type
- **Direction**: Forward, backward, bidirectional
- **Attributes**: Context-specific data

## 3.4 Analysis Result

Every analysis produces:
- **Findings**: What was discovered
- **Confidence**: How certain we are
- **Location**: Where it applies
- **Severity**: How important it is
- **Suggestions**: What to do about it

---

# 4. Layer 1: Parse

## 4.1 Responsibilities

- Convert source text to structured representation
- Normalize across languages where possible
- Handle syntax errors gracefully
- Support incremental re-parsing

## 4.2 Components

| Component | Purpose | Integration |
|-----------|---------|-------------|
| **Lexer Pool** | Reusable tokenizers per language | `src/lang/mod.rs` - ThreadLocal parser instances per language, already implemented with tree-sitter |
| **Parser Pool** | Reusable parsers (tree-sitter) | `src/ast/parser.rs` - Extend existing `get_parser()` with pool management and LRU eviction |
| **AST Normalizer** | Language-specific → universal | `src/ast/normalize.rs` (new) - Convert tree-sitter nodes to universal `CodeUnit` enum |
| **Error Recovery** | Partial parse on syntax errors | `src/ast/recovery.rs` (new) - Use tree-sitter ERROR nodes to build partial AST |
| **Preprocessor** | Handle macros, includes, conditionals | `src/lang/{c,cpp,rust}.rs` - Language-specific macro expansion before CFG/DFG |

## 4.3 Language Support Matrix

| Capability | Tier 1 | Tier 2 | Tier 3 |
|------------|--------|--------|--------|
| **Languages** | Python, TypeScript, Rust, Go | Java, C, C++ | Ruby, PHP, Swift, Kotlin |
| **Full AST** | ✓ | ✓ | ✓ |
| **Type Info** | ✓ | ✓ | Partial |
| **Incremental** | ✓ | ✓ | ✓ |
| **Error Recovery** | ✓ | ✓ | ✓ |

---

# 5. Layer 2: Graph

## 5.1 Graph Types

### 5.1.1 Abstract Syntax Tree (AST)
- **Purpose**: Syntactic structure
- **Nodes**: Expressions, statements, declarations
- **Edges**: Parent-child, sibling
- **Use**: Refactoring, formatting, linting
- **Integration**: `src/ast/` - Already implemented. `types.rs` defines `FunctionInfo`, `ClassInfo`, `ModuleInfo`. Extraction in `src/lang/*.rs` per language.

### 5.1.2 Control Flow Graph (CFG)
- **Purpose**: Execution paths
- **Nodes**: Basic blocks
- **Edges**: Branches, loops, exceptions
- **Use**: Dead code, reachability, complexity
- **Integration**: `src/cfg/` - Already implemented. `builder.rs` constructs CFG, `types.rs` has `CFGInfo`, `BlockType`, `EdgeType`. 38+ edge types supported.

### 5.1.3 Data Flow Graph (DFG)
- **Purpose**: Value movement
- **Nodes**: Definitions, uses
- **Edges**: Def-use chains
- **Use**: Slicing, taint, constants
- **Integration**: `src/dfg/` - Already implemented. `builder.rs` builds DFG, `types.rs` has `DFGInfo`, `DataflowKind`. Lazy adjacency caching via `OnceLock`.

### 5.1.4 Program Dependence Graph (PDG)
- **Purpose**: Combined control + data dependencies
- **Nodes**: Statements
- **Edges**: Control deps, data deps
- **Use**: Slicing, impact analysis
- **Integration**: `src/pdg/` - Already implemented. Combines CFG + DFG. `builder.rs` merges graphs, `types.rs` defines `PDGInfo` with control dependency edges.

### 5.1.5 Call Graph
- **Purpose**: Function relationships
- **Nodes**: Callables
- **Edges**: Calls (direct, indirect, virtual)
- **Use**: Impact, dead code, architecture
- **Integration**: `src/callgraph/` - Already implemented. `builder.rs` builds project-wide graph, `cache.rs` handles incremental updates in `.tldr/cache/`.

### 5.1.6 Type Graph
- **Purpose**: Type relationships
- **Nodes**: Types
- **Edges**: Subtype, implements, contains
- **Use**: Type checking, API analysis
- **Integration**: `src/typegraph/` (new) - Extract type hierarchies from AST. Link to external type checkers (pyright, tsc) for inference.

### 5.1.7 Dependency Graph
- **Purpose**: Module relationships
- **Nodes**: Modules/packages
- **Edges**: Imports, exports
- **Use**: Build order, cycles, architecture
- **Integration**: `src/callgraph/imports.rs` - Partially implemented. Extend to build full module graph with `resolve_import()` for each language.

### 5.1.8 Binding Graph
- **Purpose**: Cross-language connections
- **Nodes**: FFI boundaries
- **Edges**: Binding calls
- **Use**: Cross-language tracing
- **Integration**: `src/bindings/` (new) - Parse pybind11/PyO3/N-API/ctypes definitions, link Python AST nodes to C++ AST nodes.

## 5.2 Graph Operations

| Operation | Description |
|-----------|-------------|
| **Build** | Construct graph from source |
| **Query** | Find nodes/edges matching criteria |
| **Traverse** | Walk graph in various orders |
| **Slice** | Extract subgraph affecting/affected by node |
| **Diff** | Compare two versions of graph |
| **Merge** | Combine graphs from multiple sources |
| **Project** | Extract specific aspect of graph |

---

# 6. Layer 3: Index

## 6.1 Index Types

### 6.1.1 Symbol Index
- **Purpose**: Fast name lookup
- **Structure**: Trie + inverted index
- **Queries**: By name, by kind, by scope
- **Features**: Fuzzy matching, prefix search
- **Integration**: `src/index/symbol.rs` (new) - Build from `FunctionInfo`/`ClassInfo`. Use `fst` crate for trie, store in `.tldr/index/symbols.fst`.

### 6.1.2 Semantic Index
- **Purpose**: Meaning-based search
- **Structure**: Vector embeddings + HNSW
- **Queries**: Natural language, similarity
- **Features**: Multi-modal (code + docs)
- **Integration**: `src/semantic/` + `src/embedding/` - Already implemented. `chunker.rs` creates `EmbeddingUnit`, `index.rs` uses usearch HNSW.

### 6.1.3 Graph Index
- **Purpose**: Relationship queries
- **Structure**: Adjacency lists + bloom filters
- **Queries**: Reachability, paths, patterns
- **Features**: Bidirectional, transitive closure
- **Integration**: `src/callgraph/index.rs` - Extend existing `FunctionIndex`. Add bloom filters for fast negative lookup on reachability queries.

### 6.1.4 Location Index
- **Purpose**: Position-based lookup
- **Structure**: Interval trees
- **Queries**: What's at line:col, range queries
- **Features**: Byte and line addressing
- **Integration**: `src/index/location.rs` (new) - Use `intervaltree` crate. Build from AST spans. Essential for LSP hover/goto.

### 6.1.5 History Index
- **Purpose**: Temporal queries
- **Structure**: Commit-keyed storage
- **Queries**: State at time T, changes between T1-T2
- **Features**: Blame, evolution tracking
- **Integration**: `src/history/index.rs` (new) - Parse git with `gix` crate. Store commit→file→analysis mappings in `.tldr/history/`.

## 6.2 Index Properties

| Property | Requirement |
|----------|-------------|
| **Incremental** | Update without full rebuild |
| **Persistent** | Survive process restart |
| **Concurrent** | Safe parallel access |
| **Compressed** | Minimal disk/memory footprint |
| **Versioned** | Multiple versions coexist |

---

# 7. Layer 4: Analysis

See [Section 11: Analysis Domains](#11-analysis-domains) for complete breakdown.

---

# 8. Layer 5: Correlation

## 8.1 Purpose

Link static analysis artifacts to dynamic runtime data and cross-language boundaries.

## 8.2 Static ↔ Dynamic Correlation

| Static Artifact | Runtime Data | Correlation |
|-----------------|--------------|-------------|
| CFG node | Execution count | Hot path detection |
| DFG edge | Actual values | Value range inference |
| Call edge | Call frequency | Optimization targets |
| Memory estimate | Actual allocation | Model calibration |
| Time estimate | Wall clock time | Model calibration |

**Integration**: `src/correlation/` (new) - `static_dynamic.rs` links `CFGInfo` nodes to trace data. `calibrator.rs` adjusts cost models based on observed vs predicted.

## 8.3 Cross-Language Correlation

| Source Language | Target Language | Binding Type |
|-----------------|-----------------|--------------|
| Python | C/C++ | CPython API, pybind11, Cython, ctypes |
| Python | Rust | PyO3, maturin |
| JavaScript | C++ | N-API, node-addon-api |
| JavaScript | Rust | neon, wasm-bindgen |
| Rust | C | FFI |
| Java | C | JNI |
| Go | C | cgo |
| Any | Any | WASM |

**Integration**: `src/bindings/` (new) - Each binding type gets a parser: `pybind11.rs`, `pyo3.rs`, `napi.rs`, `ctypes.rs`. Produces `CrossLanguageLink` structs linking AST nodes.

## 8.4 Correlation Operations

- **Link**: Connect static node to runtime observation
- **Propagate**: Spread runtime info through static graph
- **Validate**: Check static prediction against runtime
- **Calibrate**: Adjust static models based on runtime

---

# 9. Layer 6: Query

## 9.1 Query Types

### 9.1.1 Point Queries
- What is at this location?
- What does this symbol refer to?
- What type is this expression?

### 9.1.2 Relational Queries
- Who calls this function?
- What does this function call?
- What depends on this module?

### 9.1.3 Path Queries
- How does data flow from A to B?
- What's the call chain from A to B?
- What execution paths reach this line?

### 9.1.4 Pattern Queries
- Find all instances of pattern X
- Find code similar to snippet Y
- Find violations of rule Z

### 9.1.5 Aggregate Queries
- What's the complexity distribution?
- Which files have most issues?
- What's the test coverage?

### 9.1.6 Temporal Queries
- When did this change?
- Who changed this most?
- How has complexity evolved?

### 9.1.7 Predictive Queries
- What's likely to break?
- What needs refactoring most?
- What's the security risk?

## 9.2 Query Interface

- **CLI**: Command-line queries
- **LSP**: IDE integration
- **API**: Programmatic access
- **Natural Language**: LLM-mediated queries

---

# 10. Layer 7: Output

## 10.1 Output Formats

| Format | Use Case |
|--------|----------|
| **JSON** | Machine consumption, tooling |
| **Text** | Human readable, CLI |
| **HTML** | Interactive reports |
| **Markdown** | Documentation integration |
| **Graph (DOT/Mermaid)** | Visualization |
| **SARIF** | Security tool interchange |
| **LLM-Optimized** | AI consumption |

## 10.2 LLM-Optimized Output

### 10.2.1 Compression Strategies
- **Signature-only**: Just declarations, no bodies
- **Summary**: Natural language description
- **Diff-only**: Only what changed
- **Relevant-only**: Filtered by query context

### 10.2.2 Context Assembly
- **Token budgeting**: Fit within context window
- **Priority ranking**: Most relevant first
- **Dependency inclusion**: Pull in needed context
- **Deduplication**: No repeated information

---

# 11. Analysis Domains

## 11.1 Structural Analysis

**Question: What IS the code?**

| Analysis | Output |
|----------|--------|
| **AST Extraction** | Functions, classes, imports, structure |
| **Type Extraction** | Types, generics, constraints |
| **API Surface** | Public interface, exports |
| **Module Structure** | Package hierarchy, namespaces |
| **Dependency Mapping** | Internal and external deps |
| **Documentation** | Docstrings, comments, annotations |

**Integration**: `src/ast/` (existing) + `src/structure/` (new). AST extraction done. Add `api_surface.rs` to extract public exports, `module_graph.rs` for package hierarchy. Use `src/lang/*.rs` `extract_*` functions.

## 11.2 Behavioral Analysis

**Question: What does the code DO?**

| Analysis | Output |
|----------|--------|
| **Control Flow** | Execution paths, branches, loops |
| **Data Flow** | Value definitions, uses, transformations |
| **Side Effects** | I/O, mutation, global state |
| **Exception Flow** | Throw sites, catch sites, propagation |
| **Async Flow** | Await points, task graphs, cancellation |
| **Resource Flow** | Acquire/release, lifecycle |
| **Concurrency** | Shared state, synchronization, memory ordering |
| **Symbolic Execution** | Path exploration, constraint-based analysis |
| **State Machines** | Implicit FSM extraction, state coverage |
| **Invariant Inference** | Likely preconditions, postconditions, loop invariants |

**Integration**: `src/cfg/`, `src/dfg/`, `src/pdg/` (existing). Add `src/analysis/behavior/` - `exception_flow.rs` extends CFG with throw/catch edges, `async_flow.rs` models await points, `concurrency.rs` detects shared state. `symbolic.rs` uses Z3 via `z3` crate for constraint solving.

## 11.3 Quality Analysis

**Question: How GOOD is the code?**

| Analysis | Output |
|----------|--------|
| **Complexity Metrics** | Cyclomatic, cognitive, Halstead |
| **Maintainability** | Maintainability index, readability |
| **Coupling/Cohesion** | Module dependencies, class cohesion |
| **Duplication** | Clone detection (textual, structural, semantic) |
| **Code Smells** | Anti-patterns, bad practices |
| **Test Coverage** | Line, branch, path coverage mapping |
| **Test Quality** | Mutation score, assertion density |
| **Documentation Coverage** | Missing docs, doc quality |

**Integration**: `src/metrics/` (new) - `complexity.rs` computes cyclomatic (from CFG), cognitive, Halstead. `coupling.rs` analyzes call graph for afferent/efferent coupling. `duplication.rs` uses AST hashing for clone detection. `coverage.rs` parses lcov/coverage.json and maps to CFG paths.

## 11.4 Security Analysis

**Question: Is the code SAFE?**

| Analysis | Output |
|----------|--------|
| **Taint Analysis** | Untrusted data flow |
| **Injection Detection** | SQL, command, XSS, path traversal |
| **Secret Detection** | Hardcoded credentials, API keys |
| **Input Validation** | Missing or weak validation |
| **Cryptography Audit** | Weak algorithms, misuse |
| **Dependency Audit** | Known vulnerabilities (CVE) |
| **Access Control** | Authorization checks |
| **ReDoS Detection** | Catastrophic regex backtracking |
| **Serialization Safety** | Unsafe deserialization patterns |

**Integration**: `src/security/` (new) - `taint.rs` extends DFG with taint labels, propagates through call graph. `injection.rs` pattern-matches sink calls (SQL, shell, eval). `secrets.rs` regex + entropy detection. `redos.rs` analyzes regex AST for catastrophic backtracking patterns.

## 11.5 Performance Analysis

**Question: Is the code FAST?**

| Analysis | Output |
|----------|--------|
| **Time Complexity** | Algorithmic complexity estimation |
| **Memory Pressure** | Allocation patterns, peak usage |
| **Escape Analysis** | Stack vs heap, object lifetime |
| **I/O Patterns** | Blocking calls, batching opportunities |
| **Hot Path Detection** | Critical execution paths |
| **Optimization Blockers** | Patterns preventing optimization |
| **Cache Locality** | Memory access patterns, data layout |
| **Resource Efficiency** | CPU, memory, network usage patterns |
| **Parallelization Potential** | What can be parallelized |

### 11.5.1 Performance Models

For each supported runtime, maintain cost models:

| Runtime | Model Components |
|---------|-----------------|
| **CPython** | Bytecode costs, C extension calls, GIL impact |
| **V8** | Optimization tiers, deopt triggers, hidden classes |
| **Bun/JSC** | JIT characteristics, startup time |
| **Rust/LLVM** | Inlining, vectorization, allocation |
| **JVM** | JIT warmup, GC pressure, escape analysis |
| **Go** | Goroutine overhead, GC characteristics |

**Integration**: `src/perf/` (new) - `memory.rs` estimates allocations from AST patterns (list comprehensions, object creation). `cost_model.rs` has per-runtime cost tables. `hotpath.rs` combines CFG with call frequency. Runtime models loaded from `data/cost_models/*.json`.

## 11.6 Evolution Analysis

**Question: How has the code CHANGED?**

| Analysis | Output |
|----------|--------|
| **Change History** | What changed, when, by whom |
| **Hotspot Detection** | Frequently changed areas |
| **Churn Analysis** | Change rate vs complexity |
| **Author Expertise** | Who knows what code best |
| **Change Coupling** | What changes together |
| **API Evolution** | Breaking changes, deprecations |
| **Trend Analysis** | Quality/complexity over time |
| **Bug Correlation** | Changes that introduced bugs |

### 11.6.1 VCS Integration

| Source | Data Extracted |
|--------|---------------|
| **Git log** | Commits, authors, timestamps, messages |
| **Git blame** | Line-level authorship |
| **Git diff** | Change content between versions |
| **PR/MR metadata** | Review comments, approval, CI status |
| **Issue tracking** | Bug reports, feature requests |

**Integration**: `src/history/` (new) - `git.rs` uses `gix` crate to parse commits, blame, diffs. `hotspots.rs` computes change frequency × complexity. `coupling.rs` finds co-changed files via commit analysis. `expertise.rs` maps authors to code areas via blame aggregation.

## 11.7 Cross-Boundary Analysis

**Question: How do pieces CONNECT?**

| Analysis | Output |
|----------|--------|
| **FFI Mapping** | Cross-language call relationships |
| **Type Marshaling** | Type conversions at boundaries |
| **Ownership Transfer** | Memory ownership across boundaries |
| **Service Boundaries** | Microservice communication |
| **Database Queries** | SQL/ORM to schema mapping |
| **API Contracts** | REST/GraphQL/gRPC schema extraction |
| **Configuration Impact** | Config → code behavior mapping |

### 11.7.1 Deep Tracing (ML/Native)

For complex library ecosystems with native bindings:

| Layer | What We Track |
|-------|---------------|
| **High-level Language** | User code, library calls |
| **Framework Layer** | High-level APIs, abstractions |
| **Binding Layer** | pybind11, PyO3, N-API, cgo bindings |
| **Native Core** | C/C++ libraries, runtime internals |
| **Accelerator Kernels** | GPU/TPU kernel launches, dispatches |

**Integration**: `src/bindings/` (new) - Parsers per binding type. `src/trace/` (new) - `deep_trace.rs` instruments Python to capture native call stacks. Correlates Python line → binding call → native function via debug symbols when available.

## 11.8 Semantic Analysis

**Question: What does the code MEAN?**

| Analysis | Output |
|----------|--------|
| **Intent Extraction** | What is this code trying to do |
| **Pattern Recognition** | Design patterns, idioms |
| **Similarity Detection** | Semantically similar code |
| **Concept Mapping** | Code ↔ domain concepts |
| **Documentation Generation** | Auto-generated explanations |
| **Natural Language Search** | Find code by description |

**Integration**: `src/semantic/` (existing) - Already has `chunker.rs`, `search.rs`. Add `patterns.rs` for design pattern detection via AST templates. `similarity.rs` uses embedding cosine distance. NL search via existing `embedding/tei_client.rs` for query encoding.

## 11.9 Predictive Analysis

**Question: What MIGHT go wrong?**

| Analysis | Output |
|----------|--------|
| **Bug Prediction** | Likely buggy areas |
| **Regression Risk** | Changes likely to cause issues |
| **Security Risk Score** | Vulnerability likelihood |
| **Refactoring Priority** | What to fix first |
| **Test Suggestions** | What tests are missing |
| **Review Focus** | Where reviewers should look |

### 11.9.1 Prediction Models

Combine multiple signals:

| Signal | Weight Factor |
|--------|--------------|
| Complexity | Higher complexity → higher risk |
| Churn | More changes → higher risk |
| Author count | More authors → higher risk |
| Age | Very old or very new → higher risk |
| Test coverage | Less coverage → higher risk |
| Previous bugs | History of bugs → higher risk |
| Dependency count | More deps → higher risk |

**Integration**: `src/predict/` (new) - `model.rs` combines signals from metrics, history, coverage into weighted risk score. `suggest.rs` generates actionable recommendations. Uses `src/history/` hotspot data + `src/metrics/` complexity + `src/callgraph/` for dependency analysis.

## 11.10 Runtime Analysis

**Question: What ACTUALLY happens?**

| Analysis | Output |
|----------|--------|
| **Trace Collection** | Execution traces from running code |
| **Profile Integration** | CPU/memory profiler data |
| **Coverage Collection** | Actual execution coverage |
| **Value Observation** | Real values at runtime |
| **Allocation Tracking** | Actual memory allocations |
| **Call Frequency** | Actual call counts |
| **Latency Measurement** | Actual timing data |

### 11.10.1 Instrumentation Approaches

| Language | Approach |
|----------|----------|
| **Python** | sys.settrace, sys.monitoring (3.12+), ast.NodeTransformer |
| **JavaScript** | V8 inspector, Bun profiler, source transforms |
| **Rust** | tracing crate, proc macros |
| **Go** | runtime/trace, pprof |
| **Java** | JVMTI, bytecode instrumentation |
| **C/C++** | Compiler instrumentation, binary rewriting |

**Integration**: `src/trace/` (new) - Language-specific tracers: `python_trace.rs` uses `sys.monitoring`, `js_trace.rs` uses V8 inspector protocol. `collector.rs` normalizes trace format. Links to static graphs via `src/correlation/static_dynamic.rs`.

## 11.11 Architecture Analysis

**Question: Is the code WELL-STRUCTURED?**

| Analysis | Output |
|----------|--------|
| **Layer Violations** | Cross-layer dependencies, architecture drift |
| **Circular Dependencies** | Module cycles, dependency tangles |
| **Boundary Enforcement** | Module interface compliance |
| **Component Cohesion** | Related code grouped together |
| **Abstraction Levels** | Consistent abstraction within modules |

**Integration**: `src/arch/` (new) - `layers.rs` detects layer violations using call graph direction analysis. `cycles.rs` finds circular deps via Tarjan's SCC on module graph. `boundaries.rs` enforces module interface rules defined in `.tldr/arch.toml`.

## 11.12 Build & Artifacts

**Question: How does the code become DELIVERABLE?**

| Analysis | Output |
|----------|--------|
| **Build Graph** | Build dependencies, parallelization |
| **Build Time** | Slow builds, incremental opportunities |
| **Artifact Size** | Binary bloat, tree-shaking opportunities |
| **Unused Dependencies** | Deps declared but not used |
| **Version Conflicts** | Dependency version mismatches |

**Integration**: `src/build/` (new) - `manifest.rs` parses Cargo.toml/package.json/pyproject.toml. `unused.rs` compares declared deps vs actually imported. `size.rs` analyzes binary/bundle size with tree-shaking simulation. Uses existing `src/callgraph/` for dead code.

## 11.13 Compliance

**Question: Does the code meet REQUIREMENTS?**

| Analysis | Output |
|----------|--------|
| **License Compatibility** | License conflicts in dependency tree |
| **SBOM Generation** | Software bill of materials |
| **Policy Violations** | Custom rule enforcement |
| **Deprecation Tracking** | Usage of deprecated APIs |

**Integration**: `src/compliance/` (new) - `license.rs` parses SPDX expressions from manifests, checks compatibility matrix. `sbom.rs` generates CycloneDX/SPDX format. `policy.rs` loads custom rules from `.tldr/policies/*.yaml` and runs pattern matching.

## 11.14 Process & Social

**Question: How does the TEAM work with this code?**

| Analysis | Output |
|----------|--------|
| **Knowledge Distribution** | Bus factor, expertise silos |
| **Review Patterns** | Review coverage, reviewer load |
| **Contribution Patterns** | Who contributes where |
| **Issue Correlation** | Code areas linked to bugs/issues |

**Integration**: `src/social/` (new) - Extends `src/history/` git analysis. `bus_factor.rs` computes knowledge concentration per module. `reviews.rs` parses GitHub/GitLab MR data via API. `issues.rs` correlates issue labels to code paths via commit message parsing.

## 11.15 Bundle/Minified Code Analysis

**Question: What CHANGED between bundled releases?**

Specialized analysis for comparing minified, mangled JavaScript/TypeScript bundles (e.g., 20MB Claude Code releases).

### 11.15.1 The Challenge

Bundlers destroy semantic information:
- **Identifiers mangled**: `authenticateUser` → `a`
- **Modules merged**: All code in single file
- **Whitespace removed**: No formatting hints
- **Dead code eliminated**: Different between builds

### 11.15.2 What Survives Mangling

| Invariant | Example | Use |
|-----------|---------|-----|
| **String literals** | Error messages, URLs, API paths | Anchor matching |
| **Property names** | `obj.userId`, `config.timeout` | Structure matching |
| **Numbers/constants** | `3600000`, `Math.PI` | Fingerprinting |
| **AST structure** | If/else shape, loop patterns | Structural matching |
| **CFG topology** | Branch/loop graph shape | Behavioral matching |
| **Call patterns** | Number of calls, argument counts | Signature matching |

### 11.15.3 Multi-Dimensional Fingerprinting

Each function gets multiple independent fingerprints:

| Fingerprint | What It Captures |
|-------------|------------------|
| **Structural** | AST node histogram, tree shape hash |
| **CFG** | Control flow graph topology, edge types |
| **Anchor** | Unique strings, numbers, property names |
| **Call Pattern** | Call count, argument patterns, call sites |
| **Size** | Statement count, expression count, byte size |

### 11.15.4 Matching Algorithm (6 Phases)

| Phase | Strategy | Confidence |
|-------|----------|------------|
| 1. **Exact** | Identical fingerprints | 100% |
| 2. **Anchor** | Same unique strings/constants | 95% |
| 3. **Structural** | Similar AST + CFG shape | 85% |
| 4. **Context** | Same callers/callees matched | 80% |
| 5. **Semantic** | Embedding similarity | 70% |
| 6. **Fuzzy** | Best remaining candidates | 50% |

### 11.15.5 Diff Output

| Change Type | Description |
|-------------|-------------|
| **Added** | Function in new, not in old |
| **Removed** | Function in old, not in new |
| **Modified** | Matched but different (with diff) |
| **Moved** | Same function, different location |
| **Split** | One function became multiple |
| **Merged** | Multiple functions became one |

**Integration**: `src/bundle/` (new) - `extract.rs` parses minified JS into function units. `fingerprint.rs` computes multi-dimensional fingerprints. `matcher.rs` implements 6-phase matching with Bloom filters for fast negative lookup. `diff.rs` generates semantic diffs. Uses `src/cfg/` for topology, `src/semantic/` for embedding similarity. CLI: `tldr bundle-diff old.js new.js`.

---

# 12. Multi-Language Strategy

## 12.1 Abstraction Layers

```
┌─────────────────────────────────────────────┐
│           Unified Analysis APIs             │
│  (Language-agnostic queries and results)    │
├─────────────────────────────────────────────┤
│         Normalized Intermediate Rep         │
│  (Universal AST, CFG, DFG abstractions)     │
├─────────────────────────────────────────────┤
│         Language-Specific Adapters          │
│  (Python, TypeScript, Rust, Go, ...)        │
├─────────────────────────────────────────────┤
│         Parser Infrastructure               │
│  (Tree-sitter grammars per language)        │
└─────────────────────────────────────────────┘
```

## 12.2 Language Plugin Interface

Each language implementation provides:

| Component | Purpose |
|-----------|---------|
| **Grammar** | Tree-sitter grammar for parsing |
| **Normalizer** | Convert AST to universal form |
| **CFG Builder** | Build control flow graph |
| **DFG Builder** | Build data flow graph |
| **Type Extractor** | Extract type information |
| **Pattern Library** | Language-specific patterns |
| **Cost Model** | Performance characteristics |
| **Tracer** | Runtime instrumentation |

## 12.3 Cross-Language Features

| Feature | How It Works |
|---------|--------------|
| **Unified search** | Same query syntax, any language |
| **Cross-lang call graph** | FFI/binding aware |
| **Polyglot projects** | Single project, multiple languages |
| **Language comparison** | Same metrics across languages |

---

# 13. Performance Architecture

## 13.1 Parallelism Strategy

| Level | Parallelism Approach |
|-------|---------------------|
| **File** | Process files in parallel (rayon) |
| **Function** | Analyze functions in parallel |
| **Graph** | Build graph components in parallel |
| **Query** | Execute independent queries in parallel |
| **Index** | Parallel index construction |

## 13.2 Caching Architecture

```
┌─────────────────┐
│   L1: Memory    │  LRU, sub-millisecond, hot data
│   (64-128 MB)   │
├─────────────────┤
│   L2: Mmap      │  Memory-mapped, fast reload
│   (256-512 MB)  │
├─────────────────┤
│   L3: Disk      │  Persistent, content-addressed
│   (Unlimited)   │
└─────────────────┘
```

## 13.3 Incremental Processing

| Change Type | Recomputation |
|-------------|---------------|
| **Single line** | Reparse function, recompute local analysis |
| **Function body** | Reparse function, propagate to callers |
| **Function signature** | Reparse + recompute call graph locally |
| **File structure** | Reparse file, update module graph |
| **New file** | Parse file, integrate into project graph |
| **Deleted file** | Remove from graphs, update dependents |

## 13.4 Streaming for Large Files

For files > threshold (e.g., 10MB):
- Parse incrementally by top-level declarations
- Process one function at a time
- Aggregate results without full AST in memory
- Essential for bundle analysis (20MB+ files)

## 13.5 Performance Targets

| Operation | Target |
|-----------|--------|
| Single file parse | < 50ms |
| Single file full analysis | < 200ms |
| Project index (10K files) | < 60s |
| Incremental update | < 100ms |
| Symbol lookup | < 1ms |
| Semantic search | < 200ms |
| Memory (10K file project) | < 500MB |

---

# 14. Extension System

## 14.1 Extension Points

| Extension Point | What Can Be Extended |
|-----------------|---------------------|
| **Language** | Add new language support |
| **Analysis** | Add new analysis types |
| **Output** | Add new output formats |
| **Query** | Add new query types |
| **Pattern** | Add detection patterns |
| **Integration** | Connect to external tools |

## 14.2 Plugin Architecture

```
┌──────────────────────────────────────────┐
│              Plugin Manager              │
├──────────────────────────────────────────┤
│  ┌────────────┐  ┌────────────┐         │
│  │  Language  │  │  Analysis  │  ...    │
│  │  Plugins   │  │  Plugins   │         │
│  └────────────┘  └────────────┘         │
├──────────────────────────────────────────┤
│              Plugin API                  │
│  (Stable interface, versioned)           │
└──────────────────────────────────────────┘
```

## 14.3 Future: WASM Plugins

- Language-agnostic plugin format
- Sandboxed execution
- Hot-reload capability
- Community ecosystem

---

# 15. RAG System Architecture

## 15.1 Multi-Index Search

Combine multiple indexes for hybrid retrieval:

| Index | Purpose | Weight (Code Search) |
|-------|---------|---------------------|
| **Semantic** | Meaning similarity via embeddings | 0.4 |
| **Symbol** | Exact name/identifier matching | 0.3 |
| **Structural** | AST pattern matching | 0.2 |
| **Graph** | Call/dependency relationships | 0.1 |

**Integration**: `src/rag/` (new) - `multi_index.rs` wraps all indexes. `fusion.rs` implements Reciprocal Rank Fusion for combining results. `router.rs` detects query intent (find code vs explain vs debug) and adjusts weights.

## 15.2 Query Understanding

| Component | Purpose |
|-----------|---------|
| **Intent Classification** | Detect: FindCode, Explain, Debug, Refactor |
| **Entity Extraction** | Pull out function names, file paths, line numbers |
| **Query Expansion** | Add synonyms, naming conventions (camelCase ↔ snake_case) |

**Integration**: `src/rag/query.rs` - Regex + heuristics for entity extraction. Optional LLM call for complex query understanding. Expands `getUserData` to also search `get_user_data`, `fetchUserData`.

## 15.3 Context Assembly

Build LLM-ready context within token budget:

| Step | Action |
|------|--------|
| 1. **Retrieve** | Get top-K candidates from each index |
| 2. **Fuse** | Combine and deduplicate results |
| 3. **Expand** | Add callers/callees, imports, types |
| 4. **Rank** | Sort by relevance to query |
| 5. **Budget** | Fit within token limit with smart truncation |
| 6. **Format** | Output as structured context |

**Integration**: `src/rag/context.rs` - `assemble()` takes query + budget, returns `ContextBundle`. Uses `src/callgraph/` for expansion. `truncate.rs` removes function bodies before signatures when over budget.

## 15.4 LLM Output Formats

| Format | Tokens | Use Case |
|--------|--------|----------|
| **Full** | ~4000 | Deep understanding needed |
| **Signatures** | ~500 | API overview |
| **Summary** | ~200 | Quick context |
| **Diff** | Variable | Change-focused queries |

**Integration**: `src/output/llm.rs` - Formatters per token budget. `compact.rs` removes docstrings, inlines simple functions. `hierarchy.rs` builds nested file→class→method structure.

---

# 16. Daemon Mode

## 16.1 Purpose

Persistent background process for fast repeated queries. Avoids cold-start parsing/indexing on every CLI invocation.

## 16.2 Architecture

```
┌─────────────────┐     ┌─────────────────────────────────────┐
│   CLI Client    │────►│           Daemon Process            │
│  (tldr ...)     │◄────│                                     │
└─────────────────┘     │  ┌─────────────────────────────┐   │
        │               │  │     In-Memory Caches         │   │
        │ Unix Socket   │  │  - Parsed ASTs               │   │
        │               │  │  - CFG/DFG/PDG graphs        │   │
        │               │  │  - Call graph                │   │
┌─────────────────┐     │  │  - Semantic index            │   │
│   File Watcher  │────►│  └─────────────────────────────┘   │
│   (notify-rs)   │     │                                     │
└─────────────────┘     │  ┌─────────────────────────────┐   │
                        │  │     Background Tasks         │   │
                        │  │  - Incremental reindex       │   │
                        │  │  - Index optimization        │   │
                        │  │  - Cache eviction            │   │
                        │  └─────────────────────────────┘   │
                        └─────────────────────────────────────┘
```

## 16.3 Features

| Feature | Description |
|---------|-------------|
| **File Watching** | Auto-reindex on file changes via `notify` crate |
| **Incremental Updates** | Only reparse changed files, propagate to graphs |
| **Background Indexing** | Build semantic index during idle time |
| **Memory Limits** | Configurable cache size, LRU eviction |
| **Auto-Shutdown** | Exit after idle timeout (default 30 min) |
| **Health Checks** | Expose /health endpoint for monitoring |

## 16.4 Protocol

JSON-RPC over Unix socket at `/tmp/tldr-{project-hash}.sock`:

```
--> {"method": "search", "params": {"query": "auth"}}
<-- {"result": [{"file": "src/auth.rs", "line": 42, ...}]}

--> {"method": "analyze", "params": {"file": "src/main.rs"}}
<-- {"result": {"complexity": 15, "issues": [...]}}
```

**Integration**: `src/daemon/` (existing structure) - `server.rs` handles socket. `handler.rs` dispatches methods. `watcher.rs` uses `notify` for file events. `cache.rs` manages LRU caches. Socket path from `src/util/path.rs` project hash.

---

# 17. Special Cases

## 17.1 Generated Code Detection

Automatically detect and optionally exclude generated code from analysis.

| Indicator | Example |
|-----------|---------|
| **Header comments** | `// Code generated by protoc`, `# Auto-generated` |
| **File patterns** | `*.pb.go`, `*.generated.ts`, `*_gen.rs` |
| **Directory patterns** | `generated/`, `__generated__/`, `node_modules/` |
| **Content patterns** | High repetition, no comments, unusual structure |

**Integration**: `src/util/generated.rs` (new) - `is_generated()` checks file. Configurable via `.tldrignore` patterns and `.tldr/config.toml` rules. Default: exclude from metrics, include in call graph.

## 17.2 Polyglot Files

Handle files with multiple embedded languages.

| File Type | Languages | Approach |
|-----------|-----------|----------|
| **HTML** | HTML + JS + CSS | Extract `<script>`, `<style>` blocks |
| **Markdown** | MD + code blocks | Parse fenced blocks by language tag |
| **Jupyter** | JSON + Python + Markdown | Parse cell array, analyze code cells |
| **Vue/Svelte** | HTML + JS + CSS | Component-aware extraction |
| **JSX/TSX** | JS + HTML-like | Already handled by tree-sitter |

**Integration**: `src/polyglot/` (new) - `splitter.rs` extracts language regions with byte offsets. Creates virtual files for each region. `reassemble.rs` maps findings back to original file locations.

## 17.3 Monorepo Scale (100K+ files)

Strategies for very large codebases:

| Strategy | Description |
|----------|-------------|
| **Workspace Partitioning** | Analyze each package/crate independently, merge graphs |
| **Lazy Loading** | Only parse files when accessed, evict LRU |
| **Sharded Indexes** | Split indexes by directory, parallel query |
| **Sparse Checkout** | Analyze only configured paths |
| **Distributed** | Split work across multiple daemon instances |

**Integration**: `src/workspace/` (new) - `partition.rs` detects workspace roots (Cargo.toml, package.json). `shard.rs` splits index by subtree. `merge.rs` combines cross-package call graphs. Config via `.tldr/workspace.toml`.

## 17.4 Offline Mode

Work without network access (no embedding API calls).

| Feature | Offline Behavior |
|---------|------------------|
| **Semantic Search** | Use local model (MiniLM) or skip |
| **CVE Database** | Cache locally, update when online |
| **Git Remote** | Skip PR/issue correlation |

**Integration**: `src/config.rs` - `offline_mode` flag. `src/embedding/` falls back to local `candle` inference. CVE data cached in `.tldr/cve_cache/`.

---

# 18. Implementation Roadmap

## Phase 1: Foundation (Current)
- [x] Multi-language parsing (7 languages)
- [x] AST extraction
- [x] CFG construction
- [x] DFG construction
- [x] PDG construction
- [x] Call graph building
- [x] Semantic search (embeddings)
- [x] Basic CLI

## Phase 2: Analysis Expansion
- [ ] Enhanced control flow (exceptions, async, generators)
- [ ] Advanced data flow (taint, constants, reaching defs)
- [ ] Security analysis suite
- [ ] Complexity metrics suite
- [ ] Pattern detection

## Phase 3: Evolution & History
- [ ] Git integration
- [ ] Hotspot detection
- [ ] Change coupling
- [ ] API evolution tracking
- [ ] Bug prediction models

## Phase 4: Performance Intelligence
- [ ] Memory pressure estimation
- [ ] CPU cost modeling (per runtime)
- [ ] Bottleneck detection
- [ ] Optimization suggestions

## Phase 5: Runtime Correlation
- [ ] Python tracer
- [ ] JavaScript tracer
- [ ] Rust tracer
- [ ] Static ↔ dynamic linking
- [ ] Model calibration

## Phase 6: Cross-Boundary
- [ ] FFI binding parsers
- [ ] Cross-language call graphs
- [ ] Deep ML framework tracing
- [ ] Service boundary detection

## Phase 7: Advanced Intelligence
- [ ] Predictive models
- [ ] LLM-guided analysis
- [ ] Natural language queries
- [ ] Auto-refactoring suggestions

## Phase 8: Ecosystem
- [ ] LSP server
- [ ] IDE plugins
- [ ] CI/CD integration
- [ ] WASM plugin system
- [ ] Community patterns

---

# Appendix A: Analysis Coverage Matrix

| Domain | Analysis | Languages | Static | Dynamic |
|--------|----------|-----------|--------|---------|
| Structure | AST | All | ✓ | - |
| Structure | Types | All | ✓ | ✓ |
| Structure | API Surface | All | ✓ | - |
| Behavior | CFG | All | ✓ | - |
| Behavior | DFG | All | ✓ | ✓ |
| Behavior | Exceptions | All | ✓ | ✓ |
| Behavior | Async | JS, Py, Rust | ✓ | ✓ |
| Behavior | Concurrency | All | ✓ | ✓ |
| Behavior | Symbolic Exec | All | ✓ | - |
| Behavior | Invariants | All | ✓ | ✓ |
| Quality | Complexity | All | ✓ | - |
| Quality | Duplication | All | ✓ | - |
| Quality | Coverage | All | - | ✓ |
| Quality | Test Quality | All | ✓ | ✓ |
| Security | Taint | All | ✓ | ✓ |
| Security | Injection | All | ✓ | - |
| Security | Secrets | All | ✓ | - |
| Security | ReDoS | All | ✓ | - |
| Performance | Memory | All | ✓ | ✓ |
| Performance | CPU | All | ✓ | ✓ |
| Performance | I/O | All | ✓ | ✓ |
| Performance | Escape | All | ✓ | - |
| Evolution | History | All | ✓ | - |
| Evolution | Churn | All | ✓ | - |
| Architecture | Layers | All | ✓ | - |
| Architecture | Cycles | All | ✓ | - |
| Build | Graph | All | ✓ | - |
| Build | Artifacts | All | ✓ | - |
| Compliance | License | All | ✓ | - |
| Process | Knowledge | All | ✓ | - |
| Boundaries | FFI | Py, Rust, JS | ✓ | ✓ |
| Boundaries | ML Deep | Python | ✓ | ✓ |
| Bundle | Diff | JS/TS | ✓ | - |
| Bundle | Fingerprint | JS/TS | ✓ | - |
| Semantics | Search | All | ✓ | - |
| Semantics | Similarity | All | ✓ | - |
| Prediction | Bugs | All | ✓ | - |
| Prediction | Risk | All | ✓ | - |

---

# Appendix B: Query Examples

```
# Structural
tldr find "class * extends Component"
tldr api-surface ./src

# Behavioral
tldr cfg src/auth.py authenticate
tldr taint --source "request.form" --sink "execute"

# Quality
tldr complexity --threshold 15
tldr duplicates --min-lines 10

# Security
tldr security scan ./src
tldr secrets detect

# Performance
tldr perf estimate src/process.py
tldr memory-pressure --function process_batch

# Evolution
tldr hotspots --days 90
tldr breaking-changes v1.0..v2.0

# Cross-boundary
tldr trace-bindings torch.nn.Linear
tldr ffi-map ./native

# Predictive
tldr risk-score ./src
tldr suggest-tests --uncovered

# Architecture
tldr layers ./src --check
tldr cycles --module-level

# Build
tldr build-graph
tldr unused-deps

# Compliance
tldr licenses --check-compat
tldr sbom generate
```

---

# Appendix C: Output Examples

## LLM-Optimized Context

```
<context budget="4000" relevance="high">
  <file path="src/auth.py" summary="Authentication module">
    <function name="authenticate" complexity="12" calls="3" callers="7">
      <signature>def authenticate(user: str, token: str) -> bool</signature>
      <doc>Validates user credentials against the auth service.</doc>
      <security-note>Taint flow from token to SQL query at line 45</security-note>
    </function>
    <function name="validate_token" complexity="5" calls="1" callers="1">
      <signature>def validate_token(token: str) -> dict</signature>
    </function>
  </file>
  <dependencies>
    <module name="auth_service" functions_used="2"/>
  </dependencies>
</context>
```

---

*End of Design Document v2.0*
