# TLDR-RS: High-Performance Code Intelligence Platform

## Design Document v2.0

A comprehensive code analysis platform providing static analysis, runtime instrumentation, cross-language tracing, and LLM-optimized representations for every supported language.

---

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [Core Analysis Engine](#2-core-analysis-engine)
3. [Advanced Static Analysis](#3-advanced-static-analysis)
4. [Security Analysis](#4-security-analysis)
5. [Performance Prediction](#5-performance-prediction)
6. [Git History Intelligence](#6-git-history-intelligence)
7. [Runtime Instrumentation](#7-runtime-instrumentation)
8. [Cross-Language Binding Analysis](#8-cross-language-binding-analysis)
9. [ML Framework Deep Tracing](#9-ml-framework-deep-tracing)
10. [Bundle Diff Engine](#10-bundle-diff-engine)
11. [LLM Integration & RAG](#11-llm-integration--rag)
12. [High-Performance Architecture](#12-high-performance-architecture)
13. [CLI & API Design](#13-cli--api-design)
14. [Implementation Roadmap](#14-implementation-roadmap)

---

## 1. Architecture Overview

### 1.1 System Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           TLDR-RS Platform                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐        │
│  │   Source    │  │    Git      │  │   Runtime   │  │  External   │        │
│  │   Files     │  │   History   │  │   Traces    │  │   Data      │        │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘        │
│         │                │                │                │                │
│         ▼                ▼                ▼                ▼                │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      INPUT LAYER                                  │      │
│  │  • File Scanner  • Git Parser  • Trace Collector  • API Client   │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                    │                                        │
│                                    ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      PARSE LAYER (Parallel)                       │      │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐    │      │
│  │  │ Python  │ │   TS    │ │   Go    │ │  Rust   │ │  C/C++  │    │      │
│  │  │ Parser  │ │ Parser  │ │ Parser  │ │ Parser  │ │ Parser  │    │      │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘    │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                    │                                        │
│                                    ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      ANALYSIS LAYER                               │      │
│  │  ┌─────────────────────────────────────────────────────────┐     │      │
│  │  │  Graph Construction (Parallel per file)                  │     │      │
│  │  │  • AST  • CFG  • DFG  • PDG  • Call Graph               │     │      │
│  │  └─────────────────────────────────────────────────────────┘     │      │
│  │  ┌─────────────────────────────────────────────────────────┐     │      │
│  │  │  Advanced Analysis (Parallel per function)               │     │      │
│  │  │  • Taint  • Security  • Complexity  • Patterns          │     │      │
│  │  └─────────────────────────────────────────────────────────┘     │      │
│  │  ┌─────────────────────────────────────────────────────────┐     │      │
│  │  │  Performance Analysis                                    │     │      │
│  │  │  • Memory Prediction  • CPU Estimation  • Runtime Corr  │     │      │
│  │  └─────────────────────────────────────────────────────────┘     │      │
│  │  ┌─────────────────────────────────────────────────────────┐     │      │
│  │  │  Cross-Language Analysis                                 │     │      │
│  │  │  • Binding Parser  • FFI Tracker  • ML Deep Trace       │     │      │
│  │  └─────────────────────────────────────────────────────────┘     │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                    │                                        │
│                                    ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      INDEX LAYER                                  │      │
│  │  • Semantic Index (Embeddings)  • Symbol Index  • Graph Index    │      │
│  │  • History Index  • Runtime Index  • Binding Index               │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                    │                                        │
│                                    ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      QUERY LAYER                                  │      │
│  │  • Search  • RAG  • Diff  • Impact  • Slice  • Predict          │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                    │                                        │
│                                    ▼                                        │
│  ┌──────────────────────────────────────────────────────────────────┐      │
│  │                      OUTPUT LAYER                                 │      │
│  │  • JSON  • Text  • HTML  • LLM-Optimized  • Graph Viz           │      │
│  └──────────────────────────────────────────────────────────────────┘      │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.2 Module Hierarchy

```
src/
├── lib.rs                    # Public API (50+ functions)
├── main.rs                   # CLI entry point
├── error.rs                  # Error types
│
├── lang/                     # Language implementations
│   ├── mod.rs
│   ├── traits.rs             # Language trait definition
│   ├── registry.rs           # Language registry
│   ├── python.rs             # Python (4500+ lines)
│   ├── typescript.rs         # TypeScript/JavaScript
│   ├── go.rs                 # Go
│   ├── rust_lang.rs          # Rust
│   ├── c.rs                  # C
│   ├── cpp.rs                # C++
│   └── java.rs               # Java
│
├── ast/                      # AST extraction
│   ├── mod.rs
│   ├── extractor.rs          # Main extractor
│   ├── structure.rs          # Code structure
│   └── types.rs              # FunctionInfo, ClassInfo, ModuleInfo
│
├── cfg/                      # Control Flow Graphs
│   ├── mod.rs
│   ├── builder.rs            # CFG construction
│   ├── types.rs              # CFGInfo, BlockId, EdgeType
│   ├── render.rs             # Mermaid, DOT, ASCII, JSON
│   ├── exception_flow.rs     # Exception path tracking
│   ├── async_flow.rs         # Async/await modeling
│   └── loop_analysis.rs      # Loop invariants, bounds
│
├── dfg/                      # Data Flow Graphs
│   ├── mod.rs
│   ├── builder.rs            # DFG construction
│   ├── types.rs              # DFGInfo, DataflowEdge
│   └── slice.rs              # Program slicing
│
├── pdg/                      # Program Dependence Graphs
│   ├── mod.rs
│   ├── builder.rs            # PDG = CFG + DFG
│   └── types.rs              # Control dependencies
│
├── callgraph/                # Cross-file call analysis
│   ├── mod.rs
│   ├── scanner.rs            # Project scanner
│   ├── indexer.rs            # FunctionIndex (arena-based)
│   ├── resolver.rs           # Call resolution
│   ├── types.rs              # CallGraph, FunctionRef
│   ├── cache.rs              # Incremental caching
│   ├── impact.rs             # Impact analysis
│   ├── dead.rs               # Dead code detection
│   └── arch.rs               # Architecture layers
│
├── dataflow/                 # Advanced data flow [NEW]
│   ├── mod.rs
│   ├── taint.rs              # Taint analysis
│   ├── constant_prop.rs      # Constant propagation
│   ├── reaching_defs.rs      # Reaching definitions
│   ├── live_vars.rs          # Live variable analysis
│   └── alias.rs              # Alias/points-to analysis
│
├── security/                 # Security analysis [NEW]
│   ├── mod.rs
│   ├── sql_injection.rs
│   ├── xss.rs
│   ├── command_injection.rs
│   ├── path_traversal.rs
│   └── secrets.rs
│
├── metrics/                  # Complexity metrics [NEW]
│   ├── mod.rs
│   ├── cognitive.rs          # Cognitive complexity
│   ├── halstead.rs           # Halstead metrics
│   ├── maintainability.rs    # Maintainability index
│   └── coupling.rs           # Coupling/cohesion
│
├── patterns/                 # Pattern detection [NEW]
│   ├── mod.rs
│   ├── design_patterns.rs    # GoF patterns
│   ├── anti_patterns.rs      # Code smells
│   └── duplication.rs        # Clone detection
│
├── perf/                     # Performance prediction [NEW]
│   ├── mod.rs
│   ├── memory/
│   │   ├── mod.rs
│   │   ├── python.rs         # Python memory model
│   │   ├── javascript.rs     # V8/Bun memory model
│   │   ├── rust.rs           # Rust ownership tracking
│   │   └── estimator.rs      # Unified estimator
│   ├── cpu/
│   │   ├── mod.rs
│   │   ├── cost_model.rs     # Abstract cost units
│   │   ├── python_bytecode.rs
│   │   ├── v8_cost.rs
│   │   ├── bun_cost.rs
│   │   └── llvm_cost.rs
│   └── scorer.rs             # Performance scoring
│
├── history/                  # Git history analysis [NEW]
│   ├── mod.rs
│   ├── parser.rs             # Git log/blame parsing
│   ├── hotspots.rs           # Change frequency
│   ├── churn.rs              # Churn × complexity
│   ├── coupling.rs           # Change coupling
│   ├── expertise.rs          # Author mapping
│   └── prediction.rs         # Bug prediction
│
├── instrument/               # Runtime instrumentation [NEW]
│   ├── mod.rs
│   ├── python_tracer.rs      # sys.monitoring (3.12+)
│   ├── js_tracer.rs          # V8 inspector / Bun profiler
│   ├── rust_tracer.rs        # tracing crate integration
│   ├── collector.rs          # Unified trace format
│   └── correlator.rs         # Static ↔ dynamic mapping
│
├── bindings/                 # Cross-language analysis [NEW]
│   ├── mod.rs
│   ├── parser/
│   │   ├── pybind11.rs
│   │   ├── pyo3.rs
│   │   ├── cython.rs
│   │   ├── ctypes.rs
│   │   ├── cffi.rs
│   │   ├── napi.rs
│   │   └── wasm.rs
│   ├── linker.rs             # Cross-AST linking
│   └── types.rs              # CrossLanguageLink
│
├── ml_trace/                 # ML framework tracing [NEW]
│   ├── mod.rs
│   ├── pytorch/
│   │   ├── tensor_tracker.rs
│   │   ├── autograd_graph.rs
│   │   ├── cuda_correlation.rs
│   │   └── memory_timeline.rs
│   └── diffusers/
│       ├── pipeline_trace.rs
│       └── attention_map.rs
│
├── bundle_diff/              # Mangled JS comparison [NEW]
│   ├── mod.rs
│   ├── extractor.rs          # Function extraction
│   ├── fingerprint.rs        # Multi-dimensional fingerprints
│   ├── matcher.rs            # 6-phase matching
│   ├── differ.rs             # Diff generation
│   └── types.rs              # FunctionUnit, MatchResult
│
├── semantic/                 # Semantic search
│   ├── mod.rs
│   ├── chunker.rs            # Code chunking
│   ├── extractor.rs          # Unit extraction
│   └── types.rs              # EmbeddingUnit
│
├── embedding/                # Vector operations
│   ├── mod.rs
│   ├── index.rs              # HNSW index (usearch)
│   └── tei_client.rs         # TEI gRPC client
│
├── rag/                      # RAG system [NEW]
│   ├── mod.rs
│   ├── multi_index.rs        # Semantic + structural + symbol
│   ├── query_router.rs       # Intent classification
│   ├── context_builder.rs    # Token-optimized assembly
│   └── hybrid_search.rs      # Reciprocal rank fusion
│
├── output/                   # Output formatters [NEW]
│   ├── mod.rs
│   ├── llm_format.rs         # Token-efficient formats
│   ├── compact_ast.rs        # Compressed AST
│   └── signature_view.rs     # Declarations only
│
└── util/
    ├── mod.rs
    ├── path.rs               # Path utilities
    └── ignore.rs             # .tldrignore handling
```

### 1.3 Supported Languages

| Language | AST | CFG | DFG | Call Graph | Memory | CPU | Bindings |
|----------|-----|-----|-----|------------|--------|-----|----------|
| Python | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (C/C++) |
| TypeScript | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (WASM) |
| JavaScript | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (WASM) |
| Go | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (CGo) |
| Rust | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (C/FFI) |
| C | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | N/A |
| C++ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | N/A |
| Java | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (JNI) |

---

## 2. Core Analysis Engine

### 2.1 AST Extraction

```rust
/// Core code unit information
#[derive(Debug, Clone, Serialize)]
pub struct FunctionInfo {
    pub name: String,
    pub qualified_name: String,
    pub start_line: usize,
    pub end_line: usize,
    pub params: Vec<ParamInfo>,
    pub return_type: Option<String>,
    pub docstring: Option<String>,
    pub decorators: Vec<String>,
    pub is_async: bool,
    pub is_generator: bool,
    pub complexity: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct ClassInfo {
    pub name: String,
    pub bases: Vec<String>,
    pub methods: Vec<FunctionInfo>,
    pub class_variables: Vec<String>,
    pub instance_variables: Vec<String>,
    pub decorators: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModuleInfo {
    pub path: String,
    pub language: String,
    pub functions: Vec<FunctionInfo>,
    pub classes: Vec<ClassInfo>,
    pub imports: Vec<ImportInfo>,
    pub exports: Vec<String>,
    pub module_docstring: Option<String>,
}
```

### 2.2 Control Flow Graph

```rust
/// CFG block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub usize);

/// CFG block types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockType {
    Entry,
    Exit,
    Body,
    Branch,
    LoopHeader,
    LoopBody,
    Return,
    Exception,
    Finally,
    Yield,
    Await,
}

/// CFG edge types (38 variants for full precision)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeType {
    Unconditional,
    True,
    False,
    BackEdge,
    Break,
    Continue,
    Exception,
    Finally,
    Return,
    Yield,
    YieldFrom,
    Await,
    // ... 26 more for language-specific constructs
}

/// Complete CFG information
#[derive(Debug, Clone)]
pub struct CFGInfo {
    pub function_name: String,
    pub blocks: HashMap<BlockId, CFGBlock>,
    pub edges: Vec<CFGEdge>,
    pub entry: BlockId,
    pub exit: BlockId,
    pub complexity: usize,
    pub back_edges: Vec<(BlockId, BlockId)>,
    // Lazy-computed analysis results
    dominators: OnceLock<DominatorTree>,
    post_dominators: OnceLock<DominatorTree>,
    loops: OnceLock<Vec<LoopInfo>>,
}
```

### 2.3 Data Flow Graph

```rust
/// Data flow edge kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataflowKind {
    Definition,
    Use,
    Mutation,
    Return,
    Param,
    Yield,
    ClosureCapture,
    GlobalRead,
    GlobalWrite,
    AttributeRead,
    AttributeWrite,
}

/// Data flow edge
#[derive(Debug, Clone)]
pub struct DataflowEdge {
    pub from_line: usize,
    pub to_line: usize,
    pub variable: String,
    pub kind: DataflowKind,
}

/// Complete DFG with cached adjacency for O(1) lookups
#[derive(Debug, Clone)]
pub struct DFGInfo {
    pub function_name: String,
    pub edges: Vec<DataflowEdge>,
    pub definitions: HashMap<String, Vec<usize>>,
    pub uses: HashMap<String, Vec<usize>>,
    // 15900x speedup via lazy adjacency caching
    adjacency_cache: OnceLock<AdjacencyCache>,
}
```

### 2.4 Call Graph

```rust
/// Arena-indexed function reference
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionRef {
    pub file: Arc<str>,
    pub name: Arc<str>,
    pub qualified_name: Arc<str>,
    pub line: usize,
}

/// Project-wide call graph
#[derive(Debug)]
pub struct CallGraph {
    /// Edges: caller -> callees
    edges: HashMap<FunctionRef, HashSet<FunctionRef>>,
    /// Reverse edges: callee -> callers
    reverse_edges: HashMap<FunctionRef, HashSet<FunctionRef>>,
    /// All functions (cached)
    all_functions_cache: OnceLock<HashSet<FunctionRef>>,
}

/// High-performance function index
#[derive(Debug)]
pub struct FunctionIndex {
    /// Arena storage for function definitions
    functions: Vec<FunctionDef>,
    /// Name -> indices (for call resolution)
    by_name: HashMap<Arc<str>, Vec<usize>>,
    /// Qualified name -> index
    by_qualified: HashMap<Arc<str>, usize>,
    /// File -> indices
    by_file: HashMap<Arc<str>, Vec<usize>>,
}
```

---

## 3. Advanced Static Analysis

### 3.1 Taint Analysis

Track data from untrusted sources to security-sensitive sinks.

```rust
/// Taint source kinds
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TaintSourceKind {
    UserInput,        // request.form, input(), sys.argv
    Environment,      // os.environ, process.env
    FileRead,         // open().read(), fs.readFile
    NetworkData,      // socket.recv, fetch response
    DatabaseResult,   // cursor.fetchall()
    Deserialization,  // pickle.load, JSON.parse (external)
    Custom(String),
}

/// Taint sink kinds
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TaintSinkKind {
    SqlQuery,         // cursor.execute
    ShellCommand,     // os.system, subprocess
    FilePath,         // open(user_input)
    HtmlOutput,       // response.write
    CodeEval,         // eval, exec
    Deserialization,  // pickle.loads with untrusted
    LdapQuery,
    XmlParsing,       // XXE risk
    Custom(String),
}

/// A detected taint flow
#[derive(Debug, Clone)]
pub struct TaintFlow {
    pub source: TaintSource,
    pub sink: TaintSink,
    pub path: Vec<TaintPathStep>,
    pub sanitized: bool,
    pub sanitizer: Option<String>,
    pub confidence: f32,
}

/// Taint analyzer with configurable patterns
pub struct TaintAnalyzer<'a> {
    dfg: &'a DFGInfo,
    call_graph: Option<&'a CallGraph>,
    config: TaintConfig,
}

impl<'a> TaintAnalyzer<'a> {
    /// Analyze using forward data flow from sources
    pub fn analyze(&self) -> TaintAnalysisResult {
        // 1. Identify all taint sources
        let sources = self.find_sources();

        // 2. Propagate taint through DFG (parallel per source)
        let tainted: Vec<_> = sources.par_iter()
            .map(|src| self.propagate_taint(src))
            .collect();

        // 3. Check if taint reaches sinks
        let flows = self.find_flows_to_sinks(&tainted);

        // 4. Filter through sanitizers
        self.filter_sanitized(flows)
    }
}
```

### 3.2 Constant Propagation

```rust
/// Constant value lattice
#[derive(Debug, Clone, PartialEq)]
pub enum ConstantValue {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Null,
    Unknown,  // Known type, unknown value
    Varying,  // Multiple possible values (phi node)
}

/// Constant propagation using abstract interpretation
pub struct ConstantPropagator<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
}

impl<'a> ConstantPropagator<'a> {
    /// Worklist algorithm with meet semilattice
    pub fn analyze(&self) -> ConstantPropResult {
        let mut values: HashMap<usize, HashMap<String, ConstantValue>> = HashMap::new();
        let mut worklist: VecDeque<BlockId> = VecDeque::new();

        // Initialize entry with Unknown for all params
        worklist.push_back(self.cfg.entry);

        while let Some(block) = worklist.pop_front() {
            let in_state = self.compute_meet(&values, block);
            let out_state = self.transfer(block, &in_state);

            if self.state_changed(block, &out_state, &values) {
                values.insert(block.0, out_state);
                for succ in self.cfg.successors(block) {
                    worklist.push_back(succ);
                }
            }
        }

        self.extract_results(&values)
    }

    /// Meet operation: same → keep, different → Varying
    fn meet(a: &ConstantValue, b: &ConstantValue) -> ConstantValue {
        match (a, b) {
            (x, y) if x == y => x.clone(),
            (ConstantValue::Unknown, x) | (x, ConstantValue::Unknown) => x.clone(),
            _ => ConstantValue::Varying,
        }
    }
}
```

### 3.3 Live Variable Analysis

```rust
/// Live variable analysis (backward data flow)
pub struct LiveVarsAnalyzer<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
}

impl<'a> LiveVarsAnalyzer<'a> {
    pub fn analyze(&self) -> LiveVarsResult {
        // Backward analysis: IN[B] = USE[B] ∪ (OUT[B] - DEF[B])
        let mut live_in: HashMap<BlockId, HashSet<String>> = HashMap::new();
        let mut live_out: HashMap<BlockId, HashSet<String>> = HashMap::new();
        let mut changed = true;

        while changed {
            changed = false;
            for block in self.cfg.blocks_reverse_postorder() {
                // OUT[B] = ∪ IN[S] for all successors S
                let out: HashSet<String> = self.cfg.successors(block)
                    .flat_map(|s| live_in.get(&s).cloned().unwrap_or_default())
                    .collect();

                // IN[B] = USE[B] ∪ (OUT[B] - DEF[B])
                let use_set = self.use_set(block);
                let def_set = self.def_set(block);
                let new_in: HashSet<String> = use_set
                    .union(&out.difference(&def_set).cloned().collect())
                    .cloned()
                    .collect();

                if live_in.get(&block) != Some(&new_in) {
                    live_in.insert(block, new_in);
                    changed = true;
                }
                live_out.insert(block, out);
            }
        }

        self.find_dead_assignments(&live_in, &live_out)
    }
}
```

### 3.4 Alias Analysis

```rust
/// Abstract memory location
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemoryLocation {
    Variable(String),
    HeapAlloc(usize),  // Allocation site
    Field(Box<MemoryLocation>, String),
    Element(Box<MemoryLocation>, Option<i64>),
    Global(String),
    Unknown,
}

/// Points-to set
#[derive(Debug, Clone, Default)]
pub struct PointsToSet {
    pub locations: HashSet<MemoryLocation>,
    pub may_be_unknown: bool,
}

/// Alias relation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasRelation {
    MustAlias,
    MayAlias,
    NoAlias,
}

/// Andersen's inclusion-based alias analysis
pub struct AliasAnalyzer<'a> {
    dfg: &'a DFGInfo,
    call_graph: Option<&'a CallGraph>,
}

impl<'a> AliasAnalyzer<'a> {
    pub fn analyze(&self) -> AliasAnalysisResult {
        // Build constraint graph from assignments
        let constraints = self.build_constraints();

        // Propagate points-to sets using wave propagation
        let points_to = self.solve_constraints(constraints);

        // Cache alias queries
        AliasAnalysisResult { points_to }
    }

    pub fn query(&self, a: &str, b: &str) -> AliasRelation {
        let pts_a = self.points_to.get(a);
        let pts_b = self.points_to.get(b);

        match (pts_a, pts_b) {
            (Some(a), Some(b)) if a.locations.len() == 1
                && b.locations.len() == 1
                && a.locations == b.locations => AliasRelation::MustAlias,
            (Some(a), Some(b)) if a.locations.is_disjoint(&b.locations)
                && !a.may_be_unknown && !b.may_be_unknown => AliasRelation::NoAlias,
            _ => AliasRelation::MayAlias,
        }
    }
}
```

---

## 4. Security Analysis

### 4.1 SQL Injection Detection

```rust
/// SQL injection finding
#[derive(Debug, Clone)]
pub struct SqlInjectionFinding {
    pub line: usize,
    pub sql_expr: String,
    pub tainted_var: String,
    pub taint_source: TaintSource,
    pub severity: Severity,
    pub pattern: SqlInjectionPattern,
    pub suggestion: String,
}

#[derive(Debug, Clone)]
pub enum SqlInjectionPattern {
    FStringFormat,       // f"SELECT * FROM {table}"
    PercentFormat,       // "SELECT * FROM %s" % table
    ConcatFormat,        // "SELECT * FROM " + table
    FormatMethod,        // "SELECT * FROM {}".format(table)
}

pub struct SqlInjectionDetector<'a> {
    dfg: &'a DFGInfo,
    taint_result: &'a TaintAnalysisResult,
}

impl<'a> SqlInjectionDetector<'a> {
    pub fn detect(&self) -> Vec<SqlInjectionFinding> {
        self.taint_result.flows.par_iter()
            .filter(|flow| flow.sink.kind == TaintSinkKind::SqlQuery)
            .filter(|flow| !flow.sanitized)
            .map(|flow| self.create_finding(flow))
            .collect()
    }
}
```

### 4.2 Command Injection Detection

```rust
#[derive(Debug, Clone)]
pub struct CommandInjectionFinding {
    pub line: usize,
    pub command_expr: String,
    pub tainted_var: String,
    pub uses_shell: bool,  // shell=True is extra dangerous
    pub severity: Severity,
}

// Patterns detected:
// - os.system(user_input)
// - subprocess.run(user_input, shell=True)
// - subprocess.Popen(f"cmd {user_input}", shell=True)
// - child_process.exec(user_input)
```

### 4.3 Secrets Detection

```rust
/// Detected secret
#[derive(Debug, Clone)]
pub struct SecretFinding {
    pub line: usize,
    pub value_snippet: String,  // Redacted
    pub secret_type: SecretType,
    pub confidence: f32,
    pub variable: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SecretType {
    AwsAccessKey,
    AwsSecretKey,
    GitHubToken,
    PrivateKey,
    ApiKey,
    JwtSecret,
    DatabasePassword,
    HighEntropy,  // Entropy > 4.5 bits/char
}

pub struct SecretDetector {
    patterns: Vec<SecretPattern>,
    entropy_threshold: f64,
}

impl SecretDetector {
    pub fn detect(&self, source: &[u8]) -> Vec<SecretFinding> {
        let mut findings = Vec::new();

        // Pattern matching (parallel per pattern)
        let pattern_matches: Vec<_> = self.patterns.par_iter()
            .flat_map(|p| self.match_pattern(p, source))
            .collect();
        findings.extend(pattern_matches);

        // Entropy analysis for string literals
        for string_literal in self.extract_strings(source) {
            if Self::entropy(&string_literal.value) > self.entropy_threshold {
                findings.push(SecretFinding {
                    secret_type: SecretType::HighEntropy,
                    confidence: 0.6,
                    ..
                });
            }
        }

        findings
    }

    fn entropy(s: &str) -> f64 {
        let mut freq: HashMap<char, usize> = HashMap::new();
        for c in s.chars() {
            *freq.entry(c).or_insert(0) += 1;
        }
        let len = s.len() as f64;
        -freq.values()
            .map(|&count| {
                let p = count as f64 / len;
                p * p.log2()
            })
            .sum::<f64>()
    }
}

// Default patterns
impl Default for SecretDetector {
    fn default() -> Self {
        Self {
            patterns: vec![
                SecretPattern::new("AWS Access Key", r"AKIA[0-9A-Z]{16}", SecretType::AwsAccessKey, 0.95),
                SecretPattern::new("GitHub Token", r"ghp_[0-9a-zA-Z]{36}", SecretType::GitHubToken, 0.95),
                SecretPattern::new("Private Key", r"-----BEGIN (RSA |EC )?PRIVATE KEY-----", SecretType::PrivateKey, 0.99),
                SecretPattern::new("JWT", r"eyJ[a-zA-Z0-9_-]*\.eyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]*", SecretType::JwtSecret, 0.8),
            ],
            entropy_threshold: 4.5,
        }
    }
}
```

---

## 5. Performance Prediction

### 5.1 Memory Prediction

```rust
/// Memory estimate for a code block
#[derive(Debug, Clone)]
pub struct MemoryEstimate {
    /// Heap allocation range [min, max] bytes
    pub heap_bytes: Range<usize>,
    /// Stack usage estimate
    pub stack_bytes: usize,
    /// Number of allocations
    pub allocation_count: usize,
    /// Detected memory patterns
    pub patterns: Vec<MemoryPattern>,
    /// Per-line breakdown
    pub line_estimates: HashMap<usize, LineMemoryEstimate>,
    /// Confidence (0.0 - 1.0)
    pub confidence: f32,
}

#[derive(Debug, Clone)]
pub enum MemoryPattern {
    /// Large list/array creation in loop
    LargeCollectionInLoop { variable: String, estimated_elements: usize },
    /// Unbounded growth (append in loop without clear)
    UnboundedGrowth { variable: String, loop_line: usize },
    /// String concatenation in loop (O(n²) memory)
    StringConcatInLoop { variable: String },
    /// Large tensor allocation
    TensorAllocation { shape: Vec<i64>, dtype: String, bytes: usize },
    /// DataFrame creation
    DataFrameLoad { estimated_rows: Option<usize>, columns: usize },
    /// Closure capturing large data
    LargeClosureCapture { captured_vars: Vec<String>, estimated_bytes: usize },
    /// Recursive call with large stack frames
    DeepRecursion { function: String, max_depth: Option<usize> },
}

/// Python-specific memory model
pub struct PythonMemoryEstimator;

impl PythonMemoryEstimator {
    // Python object sizes (CPython 3.11+)
    const PYOBJECT_OVERHEAD: usize = 16;  // refcount + type pointer
    const INT_SMALL: usize = 28;          // Small int (-5 to 256, interned)
    const INT_LARGE: usize = 32;          // Arbitrary precision
    const FLOAT: usize = 24;
    const STR_OVERHEAD: usize = 49;       // + len * char_size
    const LIST_OVERHEAD: usize = 56;      // + len * 8 (pointers)
    const DICT_OVERHEAD: usize = 232;     // + entries
    const TUPLE_OVERHEAD: usize = 40;     // + len * 8

    pub fn estimate_expression(&self, expr: &str, context: &MemoryContext) -> usize {
        // Parse expression and estimate based on type inference
        match self.infer_type(expr, context) {
            InferredType::List(elem_type) => {
                let elem_size = self.estimate_type_size(&elem_type);
                Self::LIST_OVERHEAD + context.estimated_length * (8 + elem_size)
            }
            InferredType::Dict(k, v) => {
                Self::DICT_OVERHEAD + context.estimated_length *
                    (self.estimate_type_size(&k) + self.estimate_type_size(&v) + 24)
            }
            InferredType::String => {
                Self::STR_OVERHEAD + context.estimated_str_len
            }
            // ... more types
        }
    }
}

/// JavaScript/V8 memory model
pub struct V8MemoryEstimator;

impl V8MemoryEstimator {
    // V8 object sizes
    const SMI_SIZE: usize = 0;            // Small integer (tagged pointer)
    const HEAP_NUMBER: usize = 16;        // Boxed number
    const STRING_OVERHEAD: usize = 24;    // + length
    const ARRAY_OVERHEAD: usize = 32;     // + length * 8 (or packed)
    const OBJECT_OVERHEAD: usize = 40;    // + properties

    pub fn estimate(&self, ast: &JsAst) -> MemoryEstimate {
        // Track hidden class transitions (affect memory layout)
        // Detect holey arrays (sparse = more memory)
        // Track closure captured variables
    }
}

/// Rust memory model (ownership-aware)
pub struct RustMemoryEstimator;

impl RustMemoryEstimator {
    pub fn estimate(&self, ast: &RustAst) -> MemoryEstimate {
        // Track Box/Vec/Arc allocations
        // Ownership = clear allocation/deallocation points
        // Can give precise estimates due to ownership rules
    }
}
```

### 5.2 CPU Cycle Estimation

```rust
/// CPU performance estimate
#[derive(Debug, Clone)]
pub struct CpuEstimate {
    /// Relative cost units (not actual cycles)
    pub cost_units: u64,
    /// Breakdown by category
    pub breakdown: CpuBreakdown,
    /// Performance issues detected
    pub issues: Vec<PerfIssue>,
    /// Per-line costs
    pub line_costs: HashMap<usize, u64>,
    /// Hotness score (0-100)
    pub hotness: u8,
}

#[derive(Debug, Clone, Default)]
pub struct CpuBreakdown {
    pub allocations: u64,      // Heap allocations are expensive
    pub syscalls: u64,         // I/O operations
    pub locks: u64,            // Mutex/semaphore operations
    pub polymorphic: u64,      // Virtual dispatch overhead
    pub branches: u64,         // Unpredictable branches
    pub memory_access: u64,    // Cache-unfriendly access
    pub compute: u64,          // Pure computation
}

#[derive(Debug, Clone)]
pub enum PerfIssue {
    /// Allocation in hot loop
    HotLoopAllocation { line: usize, count_estimate: u64 },
    /// O(n²) string concatenation
    QuadraticStringConcat { line: usize },
    /// Synchronous I/O
    SynchronousIO { line: usize, operation: String },
    /// Megamorphic call site (V8 deopt trigger)
    MegamorphicCall { line: usize },
    /// Unvectorized numeric loop
    UnvectorizedLoop { line: usize },
    /// Branch in hot path with poor prediction
    UnpredictableBranch { line: usize },
    /// Dictionary access in tight loop (Python)
    DictAccessInLoop { line: usize, variable: String },
    /// Global variable access in loop (Python)
    GlobalInLoop { line: usize, variable: String },
}

/// Python bytecode cost model
pub struct PythonCostModel;

impl PythonCostModel {
    // Approximate cost units per bytecode (CPython 3.11+)
    const LOAD_FAST: u64 = 1;
    const LOAD_GLOBAL: u64 = 10;      // Dict lookup
    const LOAD_ATTR: u64 = 15;        // Attribute lookup
    const CALL_FUNCTION: u64 = 30;    // Function call overhead
    const BUILD_LIST: u64 = 50;       // + n * 2
    const BUILD_DICT: u64 = 100;      // + n * 5
    const BINARY_OP: u64 = 5;
    const COMPARE_OP: u64 = 5;
    const FOR_ITER: u64 = 10;         // Iterator overhead per iteration

    pub fn estimate_function(&self, cfg: &CFGInfo, source: &[u8]) -> CpuEstimate {
        let mut total_cost = 0u64;
        let mut breakdown = CpuBreakdown::default();
        let mut issues = Vec::new();

        for block in cfg.blocks.values() {
            let loop_multiplier = self.estimate_loop_iterations(block, cfg);

            for line in block.lines() {
                let (cost, category) = self.estimate_line(line, source);
                let adjusted_cost = cost * loop_multiplier;
                total_cost += adjusted_cost;

                // Track issues
                if loop_multiplier > 100 && cost > 50 {
                    issues.push(PerfIssue::HotLoopAllocation { line, count_estimate: loop_multiplier });
                }
            }
        }

        CpuEstimate { cost_units: total_cost, breakdown, issues, .. }
    }
}

/// V8 JavaScript cost model
pub struct V8CostModel;

impl V8CostModel {
    // V8 has multiple tiers: interpreter -> Sparkplug -> Maglev -> Turbofan
    // Costs vary wildly based on optimization level

    pub fn estimate(&self, cfg: &CFGInfo) -> CpuEstimate {
        // Key factors:
        // 1. Monomorphic vs polymorphic call sites
        // 2. Hidden class stability
        // 3. Array element kinds (packed vs holey)
        // 4. Hot function detection

        // For each call site, track how many different types it sees
        // >4 types = megamorphic = deopt
    }
}

/// Bun/JSC cost model (different from V8)
pub struct BunCostModel;

impl BunCostModel {
    // Bun uses JavaScriptCore with different optimization strategies
    // Generally faster startup, different hot-path behavior
}

/// LLVM cost model for Rust
pub struct LlvmCostModel;

impl LlvmCostModel {
    // Use LLVM's own cost model where possible
    // Track: bounds checks, panic paths, monomorphization
}
```

### 5.3 Performance Scorer

```rust
/// Unified performance score
#[derive(Debug, Clone)]
pub struct PerformanceScore {
    /// Overall score 0-100 (higher = faster)
    pub score: u8,
    /// Memory score 0-100
    pub memory_score: u8,
    /// CPU score 0-100
    pub cpu_score: u8,
    /// Detailed breakdown
    pub memory: MemoryEstimate,
    pub cpu: CpuEstimate,
    /// Actionable recommendations
    pub recommendations: Vec<PerfRecommendation>,
}

#[derive(Debug, Clone)]
pub struct PerfRecommendation {
    pub line: usize,
    pub severity: Severity,
    pub issue: String,
    pub suggestion: String,
    pub estimated_improvement: String,
}

/// Performance scorer combining memory + CPU
pub struct PerformanceScorer<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
    language: &'a str,
}

impl<'a> PerformanceScorer<'a> {
    pub fn score(&self) -> PerformanceScore {
        let memory = self.estimate_memory();
        let cpu = self.estimate_cpu();

        // Normalize scores
        let memory_score = self.normalize_memory_score(&memory);
        let cpu_score = self.normalize_cpu_score(&cpu);

        // Combined score (weighted)
        let score = (memory_score as u16 * 40 + cpu_score as u16 * 60) / 100;

        let recommendations = self.generate_recommendations(&memory, &cpu);

        PerformanceScore {
            score: score as u8,
            memory_score,
            cpu_score,
            memory,
            cpu,
            recommendations,
        }
    }
}
```

---

## 6. Git History Intelligence

### 6.1 Data Structures

```rust
/// Git commit information
#[derive(Debug, Clone)]
pub struct Commit {
    pub hash: String,
    pub author: Author,
    pub timestamp: DateTime<Utc>,
    pub message: String,
    pub files_changed: Vec<FileChange>,
}

#[derive(Debug, Clone)]
pub struct FileChange {
    pub path: PathBuf,
    pub additions: usize,
    pub deletions: usize,
    pub change_type: ChangeType,
}

#[derive(Debug, Clone)]
pub enum ChangeType {
    Added,
    Modified,
    Deleted,
    Renamed { from: PathBuf },
}

/// Hotspot analysis result
#[derive(Debug, Clone)]
pub struct HotspotAnalysis {
    /// Files ranked by change frequency
    pub hotspots: Vec<Hotspot>,
    /// Time period analyzed
    pub period: DateRange,
    /// Total commits analyzed
    pub commit_count: usize,
}

#[derive(Debug, Clone)]
pub struct Hotspot {
    pub file: PathBuf,
    pub change_count: usize,
    pub total_churn: usize,  // additions + deletions
    pub unique_authors: usize,
    pub avg_change_size: f32,
    pub last_changed: DateTime<Utc>,
    /// Complexity at last analysis
    pub complexity: Option<usize>,
    /// Churn × Complexity score (bug predictor)
    pub risk_score: f32,
}

/// Change coupling (files that change together)
#[derive(Debug, Clone)]
pub struct ChangeCoupling {
    pub file_a: PathBuf,
    pub file_b: PathBuf,
    /// Times changed together
    pub coupling_count: usize,
    /// Total changes to either file
    pub total_changes: usize,
    /// Coupling strength (0.0 - 1.0)
    pub strength: f32,
}

/// Author expertise mapping
#[derive(Debug, Clone)]
pub struct AuthorExpertise {
    pub author: Author,
    /// Files this author knows best (by ownership %)
    pub expertise_areas: Vec<(PathBuf, f32)>,
    /// Total commits
    pub commit_count: usize,
    /// Total lines touched
    pub lines_touched: usize,
    /// Active time period
    pub active_period: DateRange,
}
```

### 6.2 Algorithms

```rust
/// Git history analyzer
pub struct HistoryAnalyzer {
    repo_path: PathBuf,
}

impl HistoryAnalyzer {
    /// Parse git log efficiently
    pub fn parse_history(&self, since: Option<DateTime<Utc>>) -> Vec<Commit> {
        // Use git2 crate or shell out to git log
        // git log --numstat --format="%H|%an|%ae|%at|%s" --since=...

        let output = Command::new("git")
            .args(&["log", "--numstat", "--format=%H|%an|%ae|%at|%s", "--since=..."])
            .current_dir(&self.repo_path)
            .output()?;

        self.parse_log_output(&output.stdout)
    }

    /// Find hotspots (parallel aggregation)
    pub fn find_hotspots(&self, commits: &[Commit]) -> HotspotAnalysis {
        // Group changes by file
        let file_changes: HashMap<PathBuf, Vec<&FileChange>> = commits
            .par_iter()
            .flat_map(|c| c.files_changed.iter().map(move |f| (f.path.clone(), f)))
            .fold(HashMap::new, |mut acc, (path, change)| {
                acc.entry(path).or_default().push(change);
                acc
            })
            .reduce(HashMap::new, |mut a, b| {
                for (k, v) in b {
                    a.entry(k).or_default().extend(v);
                }
                a
            });

        // Compute hotspot scores (parallel per file)
        let hotspots: Vec<Hotspot> = file_changes.par_iter()
            .map(|(path, changes)| self.compute_hotspot(path, changes))
            .collect();

        HotspotAnalysis { hotspots, .. }
    }

    /// Compute churn × complexity score
    fn compute_risk_score(&self, hotspot: &Hotspot) -> f32 {
        // High churn + high complexity = high bug risk
        // Normalized: churn_percentile * complexity_percentile
        let churn_factor = (hotspot.total_churn as f32).ln_1p();
        let complexity_factor = hotspot.complexity.map(|c| (c as f32).ln_1p()).unwrap_or(1.0);
        churn_factor * complexity_factor
    }

    /// Find change coupling
    pub fn find_coupling(&self, commits: &[Commit], threshold: f32) -> Vec<ChangeCoupling> {
        // Build co-change matrix
        let mut co_changes: HashMap<(PathBuf, PathBuf), usize> = HashMap::new();
        let mut file_changes: HashMap<PathBuf, usize> = HashMap::new();

        for commit in commits {
            let files: Vec<_> = commit.files_changed.iter().map(|f| &f.path).collect();

            // Count individual file changes
            for file in &files {
                *file_changes.entry((*file).clone()).or_default() += 1;
            }

            // Count co-changes (all pairs)
            for i in 0..files.len() {
                for j in (i+1)..files.len() {
                    let pair = if files[i] < files[j] {
                        (files[i].clone(), files[j].clone())
                    } else {
                        (files[j].clone(), files[i].clone())
                    };
                    *co_changes.entry(pair).or_default() += 1;
                }
            }
        }

        // Filter by threshold
        co_changes.into_iter()
            .filter_map(|((a, b), count)| {
                let total = file_changes[&a] + file_changes[&b];
                let strength = count as f32 * 2.0 / total as f32;
                if strength >= threshold {
                    Some(ChangeCoupling { file_a: a, file_b: b, coupling_count: count, total_changes: total, strength })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Map author expertise
    pub fn map_expertise(&self, commits: &[Commit]) -> Vec<AuthorExpertise> {
        // Group by author, then by file
        let author_files: HashMap<Author, HashMap<PathBuf, usize>> = ...;

        // Calculate ownership percentage per file
        // Author owns file if they wrote >50% of current lines (git blame)
    }

    /// Predict bug-prone areas
    pub fn predict_bugs(&self, hotspots: &[Hotspot], coupling: &[ChangeCoupling]) -> Vec<BugPrediction> {
        // Factors:
        // 1. High churn × complexity score
        // 2. Many authors (knowledge fragmentation)
        // 3. Recent rapid changes
        // 4. High coupling to other hot files
        // 5. Low test coverage (if available)
    }
}
```

---

## 7. Runtime Instrumentation

### 7.1 Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Runtime Instrumentation                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────────┐    ┌──────────────────┐                   │
│  │  Static Analysis │    │  Runtime Tracer  │                   │
│  │  (CFG/DFG/CG)    │    │  (per language)  │                   │
│  └────────┬─────────┘    └────────┬─────────┘                   │
│           │                       │                              │
│           │    ┌──────────────────┘                              │
│           │    │                                                 │
│           ▼    ▼                                                 │
│  ┌──────────────────────────────────────────┐                   │
│  │              Correlator                   │                   │
│  │  • Map trace events to static nodes      │                   │
│  │  • Aggregate statistics                   │                   │
│  │  • Detect discrepancies                   │                   │
│  └──────────────────────────────────────────┘                   │
│                       │                                          │
│                       ▼                                          │
│  ┌──────────────────────────────────────────┐                   │
│  │           Annotated Graph                 │                   │
│  │  • Static structure + runtime values     │                   │
│  │  • Actual call counts                     │                   │
│  │  • Measured memory/time                   │                   │
│  │  • Observed types                         │                   │
│  └──────────────────────────────────────────┘                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 7.2 Trace Format

```rust
/// Unified trace event
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceEvent {
    /// Event type
    pub kind: TraceEventKind,
    /// Source location
    pub location: CodeLocation,
    /// Timestamp (nanoseconds from trace start)
    pub timestamp_ns: u64,
    /// Thread/task ID
    pub thread_id: u64,
    /// Event-specific data
    pub data: TraceEventData,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraceEventKind {
    FunctionEnter,
    FunctionExit,
    LineExecute,
    Allocation,
    Deallocation,
    CallSite,
    Exception,
    AwaitStart,
    AwaitEnd,
    TensorCreate,
    TensorDelete,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraceEventData {
    FunctionEnter {
        args: Vec<TracedValue>,
    },
    FunctionExit {
        return_value: Option<TracedValue>,
        duration_ns: u64,
    },
    Allocation {
        address: u64,
        size: usize,
        type_name: Option<String>,
    },
    TensorCreate {
        shape: Vec<i64>,
        dtype: String,
        device: String,
        bytes: usize,
    },
    // ... more variants
}

/// Traced value (with type information)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracedValue {
    pub type_name: String,
    pub repr: String,  // String representation (truncated)
    pub size_bytes: Option<usize>,
}
```

### 7.3 Python Tracer

```rust
/// Python tracer using sys.monitoring (Python 3.12+)
pub struct PythonTracer {
    /// Output file for traces
    output_path: PathBuf,
    /// Tracing configuration
    config: PythonTracerConfig,
}

#[derive(Debug, Clone)]
pub struct PythonTracerConfig {
    /// Trace function calls
    pub trace_calls: bool,
    /// Trace line execution
    pub trace_lines: bool,
    /// Trace memory allocations
    pub trace_memory: bool,
    /// Trace tensor operations
    pub trace_tensors: bool,
    /// Maximum trace size (bytes)
    pub max_trace_size: usize,
    /// Sampling rate for high-frequency events
    pub sample_rate: f32,
}

impl PythonTracer {
    /// Generate Python code to inject tracing
    pub fn generate_tracer_code(&self) -> String {
        r#"
import sys
import json
import time
import threading

_trace_file = open("{output_path}", "w")
_trace_start = time.perf_counter_ns()
_trace_lock = threading.Lock()

def _emit(event):
    event["timestamp_ns"] = time.perf_counter_ns() - _trace_start
    event["thread_id"] = threading.get_ident()
    with _trace_lock:
        _trace_file.write(json.dumps(event) + "\n")

if sys.version_info >= (3, 12):
    # Use sys.monitoring (PEP 669)
    def _call_handler(code, instruction_offset, callable, arg0):
        _emit({
            "kind": "FunctionEnter",
            "location": {"file": code.co_filename, "line": code.co_firstlineno},
            "data": {"function": code.co_qualname}
        })

    sys.monitoring.use_tool_id(sys.monitoring.PROFILER_ID, "tldr")
    sys.monitoring.set_events(sys.monitoring.PROFILER_ID, sys.monitoring.events.CALL)
    sys.monitoring.register_callback(sys.monitoring.PROFILER_ID, sys.monitoring.events.CALL, _call_handler)
else:
    # Fall back to sys.settrace
    def _trace(frame, event, arg):
        if event == "call":
            _emit({
                "kind": "FunctionEnter",
                "location": {"file": frame.f_code.co_filename, "line": frame.f_lineno},
                "data": {"function": frame.f_code.co_qualname}
            })
        return _trace

    sys.settrace(_trace)
"#
    }

    /// Parse trace file and correlate with static analysis
    pub fn correlate(&self, trace_path: &Path, static_graph: &CallGraph) -> AnnotatedGraph {
        let events = self.parse_trace(trace_path);

        // Group by function
        let call_counts: HashMap<FunctionRef, u64> = events.iter()
            .filter(|e| e.kind == TraceEventKind::FunctionEnter)
            .map(|e| self.resolve_function(&e.location, static_graph))
            .flatten()
            .fold(HashMap::new(), |mut acc, f| {
                *acc.entry(f).or_default() += 1;
                acc
            });

        // Aggregate timing
        let timing = self.aggregate_timing(&events);

        // Aggregate memory
        let memory = self.aggregate_memory(&events);

        AnnotatedGraph { call_counts, timing, memory, .. }
    }
}
```

### 7.4 JavaScript Tracer

```rust
/// JavaScript tracer using V8 inspector protocol
pub struct JsTracer {
    output_path: PathBuf,
    config: JsTracerConfig,
}

impl JsTracer {
    /// Generate tracing code for Node.js
    pub fn generate_node_tracer(&self) -> String {
        // Use inspector module for V8 profiling
        // Or async_hooks for async tracking
    }

    /// Generate tracing code for Bun
    pub fn generate_bun_tracer(&self) -> String {
        // Bun has different profiler API
    }

    /// Generate tracing code for browser
    pub fn generate_browser_tracer(&self) -> String {
        // Performance.mark/measure API
        // PerformanceObserver
    }
}
```

### 7.5 Correlator

```rust
/// Correlates runtime traces with static analysis
pub struct TraceCorrelator<'a> {
    call_graph: &'a CallGraph,
    cfg_map: &'a HashMap<String, CFGInfo>,
    dfg_map: &'a HashMap<String, DFGInfo>,
}

/// Graph annotated with runtime data
#[derive(Debug, Clone)]
pub struct AnnotatedGraph {
    /// Function -> actual call count
    pub call_counts: HashMap<FunctionRef, u64>,
    /// Function -> total execution time (ns)
    pub total_time: HashMap<FunctionRef, u64>,
    /// Function -> self time (excluding callees)
    pub self_time: HashMap<FunctionRef, u64>,
    /// Function -> memory allocated
    pub memory_allocated: HashMap<FunctionRef, usize>,
    /// Line -> execution count
    pub line_counts: HashMap<CodeLocation, u64>,
    /// Edge -> actual traversal count
    pub edge_counts: HashMap<(FunctionRef, FunctionRef), u64>,
    /// Observed types at call sites
    pub observed_types: HashMap<CodeLocation, Vec<String>>,
    /// Discrepancies (static vs dynamic)
    pub discrepancies: Vec<Discrepancy>,
}

#[derive(Debug, Clone)]
pub struct Discrepancy {
    pub location: CodeLocation,
    pub kind: DiscrepancyKind,
    pub static_prediction: String,
    pub runtime_observation: String,
}

#[derive(Debug, Clone)]
pub enum DiscrepancyKind {
    /// Static analysis predicted dead code, but it ran
    DeadCodeExecuted,
    /// Static analysis missed a call edge
    MissedCallEdge,
    /// Type inference was wrong
    TypeMismatch,
    /// Memory estimate was way off
    MemoryEstimateOff { factor: f32 },
}

impl<'a> TraceCorrelator<'a> {
    pub fn correlate(&self, events: &[TraceEvent]) -> AnnotatedGraph {
        // Build runtime call graph
        let runtime_cg = self.build_runtime_call_graph(events);

        // Compare with static call graph
        let discrepancies = self.find_discrepancies(&runtime_cg);

        // Aggregate statistics
        AnnotatedGraph {
            call_counts: self.count_calls(events),
            total_time: self.measure_time(events),
            self_time: self.measure_self_time(events),
            memory_allocated: self.measure_memory(events),
            line_counts: self.count_lines(events),
            edge_counts: self.count_edges(events),
            observed_types: self.collect_types(events),
            discrepancies,
        }
    }
}
```

---

## 8. Cross-Language Binding Analysis

### 8.1 Binding Types

```rust
/// Supported binding mechanisms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingType {
    /// pybind11 (C++ -> Python)
    Pybind11,
    /// PyO3 (Rust -> Python)
    PyO3,
    /// Cython (.pyx files)
    Cython,
    /// ctypes (Python -> C via FFI)
    Ctypes,
    /// cffi (Python -> C)
    Cffi,
    /// Node N-API (C/C++ -> JavaScript)
    Napi,
    /// WebAssembly (any -> JS/any)
    Wasm,
    /// JNI (C/C++ -> Java)
    Jni,
    /// CGo (Go -> C)
    CGo,
    /// UniFFI (Rust -> multiple)
    UniFFI,
}

/// Cross-language function link
#[derive(Debug, Clone)]
pub struct CrossLanguageLink {
    /// High-level side (Python, JS, etc.)
    pub caller: CodeLocation,
    pub caller_language: Language,

    /// Low-level side (C, C++, Rust)
    pub callee: CodeLocation,
    pub callee_language: Language,

    /// Binding mechanism
    pub binding_type: BindingType,

    /// Parameter type mappings
    pub param_mappings: Vec<TypeMapping>,

    /// Return type mapping
    pub return_mapping: TypeMapping,

    /// Memory ownership semantics
    pub ownership: OwnershipTransfer,
}

#[derive(Debug, Clone)]
pub struct TypeMapping {
    pub high_level_type: String,
    pub low_level_type: String,
    pub conversion: ConversionKind,
}

#[derive(Debug, Clone)]
pub enum ConversionKind {
    /// Zero-cost view (e.g., numpy array -> raw pointer)
    ZeroCopy,
    /// Copy into managed memory
    Copy,
    /// Move ownership
    Move,
    /// Shared reference counting
    SharedRef,
    /// Custom conversion function
    Custom(String),
}

#[derive(Debug, Clone)]
pub enum OwnershipTransfer {
    /// Callee borrows, caller keeps ownership
    BorrowedByCallee,
    /// Ownership moves to callee
    MovedToCallee,
    /// Data is copied
    Copied,
    /// Callee returns new owned value
    ReturnedOwnership,
    /// Shared via reference counting
    SharedRefCount,
}
```

### 8.2 Binding Parsers

```rust
/// pybind11 binding parser
pub struct Pybind11Parser;

impl Pybind11Parser {
    /// Parse PYBIND11_MODULE macro and extract bindings
    pub fn parse(&self, cpp_source: &str) -> Vec<CrossLanguageLink> {
        // Look for patterns like:
        // PYBIND11_MODULE(module_name, m) {
        //     m.def("func_name", &cpp_func, "docstring");
        //     py::class_<CppClass>(m, "PyClassName")
        //         .def("method", &CppClass::method);
        // }

        let module_regex = regex!(r"PYBIND11_MODULE\s*\(\s*(\w+)\s*,\s*(\w+)\s*\)");
        let def_regex = regex!(r#"(\w+)\.def\s*\(\s*"(\w+)"\s*,\s*&(\w+(?:::\w+)?)"#);

        // Parse and extract
    }
}

/// PyO3 binding parser
pub struct PyO3Parser;

impl PyO3Parser {
    /// Parse #[pyfunction] and #[pymethods] attributes
    pub fn parse(&self, rust_source: &str) -> Vec<CrossLanguageLink> {
        // Look for:
        // #[pyfunction]
        // fn my_function(py: Python, arg: PyObject) -> PyResult<PyObject>
        //
        // #[pymethods]
        // impl MyClass {
        //     fn method(&self) -> PyResult<i32>
        // }
    }
}

/// ctypes binding parser
pub struct CtypesParser;

impl CtypesParser {
    /// Parse ctypes.CDLL usage
    pub fn parse(&self, python_source: &str) -> Vec<CrossLanguageLink> {
        // Look for:
        // lib = ctypes.CDLL("libfoo.so")
        // lib.func_name.argtypes = [ctypes.c_int, ctypes.c_char_p]
        // lib.func_name.restype = ctypes.c_double
    }
}

/// Cross-language linker
pub struct CrossLanguageLinker {
    parsers: HashMap<BindingType, Box<dyn BindingParser>>,
}

impl CrossLanguageLinker {
    /// Build unified cross-language call graph
    pub fn link(&self, project: &ProjectFiles) -> CrossLanguageGraph {
        let mut links = Vec::new();

        // Find all binding definitions (parallel per file)
        for (path, source) in project.files.par_iter() {
            if let Some(binding_type) = self.detect_binding_type(path, source) {
                let parser = &self.parsers[&binding_type];
                links.extend(parser.parse(source));
            }
        }

        // Build graph
        CrossLanguageGraph { links }
    }

    /// Trace a call from high-level to low-level
    pub fn trace_call(&self, call_site: &CodeLocation, graph: &CrossLanguageGraph) -> Vec<BindingFrame> {
        // Follow the call through binding layers
    }
}
```

---

## 9. ML Framework Deep Tracing

### 9.1 PyTorch Tensor Tracking

```rust
/// Tracked tensor allocation
#[derive(Debug, Clone)]
pub struct TensorAllocation {
    /// Python source location that triggered this
    pub python_location: CodeLocation,
    /// C++ ATen location (if available)
    pub cpp_location: Option<String>,
    /// CUDA kernel (if GPU)
    pub cuda_kernel: Option<String>,
    /// Tensor properties
    pub shape: Vec<i64>,
    pub dtype: TensorDtype,
    pub device: TensorDevice,
    pub bytes: usize,
    pub requires_grad: bool,
    /// Full stack through binding layers
    pub binding_stack: Vec<BindingFrame>,
    /// Timestamp
    pub timestamp_ns: u64,
    /// Allocation ID (for tracking deallocation)
    pub alloc_id: u64,
}

#[derive(Debug, Clone)]
pub struct BindingFrame {
    pub layer: BindingLayer,
    pub function: String,
    pub file: Option<String>,
    pub line: Option<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingLayer {
    PythonUserCode,      // User's Python code
    PythonFramework,     // torch.nn, diffusers, transformers
    PythonTorchCore,     // torch.Tensor methods
    CppDispatcher,       // ATen dispatcher
    CppATen,             // ATen operations
    CppC10,              // Core tensor library
    CudaRuntime,         // CUDA API calls
    CudaKernel,          // Actual GPU kernels
}

/// PyTorch tensor tracker
pub struct TensorTracker {
    config: TensorTrackerConfig,
}

impl TensorTracker {
    /// Generate Python code to track tensor allocations
    pub fn generate_tracker_code(&self) -> String {
        r#"
import torch
import weakref
import traceback

_allocations = {}
_alloc_id = 0
_trace_file = open("{output_path}", "w")

# Hook into tensor creation
_original_tensor_new = torch.Tensor.__new__

def _tracked_tensor_new(cls, *args, **kwargs):
    global _alloc_id
    tensor = _original_tensor_new(cls)

    _alloc_id += 1
    alloc_info = {
        "alloc_id": _alloc_id,
        "shape": list(tensor.shape) if hasattr(tensor, 'shape') else [],
        "dtype": str(tensor.dtype) if hasattr(tensor, 'dtype') else "unknown",
        "device": str(tensor.device) if hasattr(tensor, 'device') else "cpu",
        "bytes": tensor.element_size() * tensor.nelement() if hasattr(tensor, 'element_size') else 0,
        "stack": traceback.format_stack(),
        "timestamp_ns": time.perf_counter_ns(),
    }

    _allocations[_alloc_id] = alloc_info
    _trace_file.write(json.dumps({"kind": "TensorCreate", "data": alloc_info}) + "\n")

    # Track deallocation
    weakref.finalize(tensor, _on_tensor_delete, _alloc_id)

    return tensor

torch.Tensor.__new__ = _tracked_tensor_new

# Also hook torch.empty, torch.zeros, torch.randn, etc.
"#
    }

    /// Parse tensor trace and correlate with source
    pub fn analyze_trace(&self, trace_path: &Path) -> TensorAnalysis {
        let events = self.parse_trace(trace_path);

        TensorAnalysis {
            allocations: self.extract_allocations(&events),
            memory_timeline: self.build_memory_timeline(&events),
            peak_memory: self.find_peak_memory(&events),
            hotspots: self.find_allocation_hotspots(&events),
            leak_candidates: self.find_leak_candidates(&events),
        }
    }
}

/// Tensor memory analysis result
#[derive(Debug, Clone)]
pub struct TensorAnalysis {
    /// All tensor allocations
    pub allocations: Vec<TensorAllocation>,
    /// Memory usage over time
    pub memory_timeline: Vec<(u64, usize)>,  // (timestamp, bytes)
    /// Peak memory usage
    pub peak_memory: PeakMemory,
    /// Functions that allocate the most
    pub hotspots: Vec<TensorHotspot>,
    /// Potential memory leaks
    pub leak_candidates: Vec<LeakCandidate>,
}

#[derive(Debug, Clone)]
pub struct TensorHotspot {
    pub location: CodeLocation,
    pub total_bytes: usize,
    pub allocation_count: usize,
    pub avg_tensor_size: usize,
    /// Stack trace to this location
    pub typical_stack: Vec<BindingFrame>,
}
```

### 9.2 Diffusers Pipeline Tracing

```rust
/// Diffusers pipeline trace
#[derive(Debug, Clone)]
pub struct DiffusersPipelineTrace {
    /// Pipeline type
    pub pipeline_type: String,
    /// Component memory breakdown
    pub components: Vec<ComponentMemory>,
    /// Memory by pipeline stage
    pub stage_memory: Vec<StageMemory>,
    /// Attention memory
    pub attention_memory: AttentionMemory,
    /// Peak GPU memory
    pub peak_gpu_memory: usize,
    /// Recommendations
    pub recommendations: Vec<DiffusersRecommendation>,
}

#[derive(Debug, Clone)]
pub struct ComponentMemory {
    pub name: String,  // "unet", "vae", "text_encoder"
    pub parameters_bytes: usize,
    pub buffers_bytes: usize,
    pub peak_activation_bytes: usize,
}

#[derive(Debug, Clone)]
pub struct StageMemory {
    pub stage: PipelineStage,
    pub entry_memory: usize,
    pub peak_memory: usize,
    pub exit_memory: usize,
    pub tensor_count: usize,
}

#[derive(Debug, Clone)]
pub enum PipelineStage {
    TextEncoding,
    UNetInference,
    VaeDecoding,
    SafetyCheck,
}

#[derive(Debug, Clone)]
pub struct AttentionMemory {
    /// Attention type detected
    pub attention_type: AttentionType,
    /// Memory per attention layer
    pub per_layer_bytes: Vec<usize>,
    /// Total attention memory
    pub total_bytes: usize,
    /// Recommendations for memory reduction
    pub optimization_suggestions: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum AttentionType {
    Vanilla,           // O(n²) memory
    FlashAttention,    // O(n) memory
    XFormers,          // Memory efficient
    SlicedAttention,   // Chunked processing
}

/// Diffusers pipeline tracer
pub struct DiffusersTracer;

impl DiffusersTracer {
    pub fn generate_tracer_code(&self) -> String {
        r#"
import torch
from diffusers import StableDiffusionPipeline

# Patch forward methods to track memory
_stage_memory = []

def _track_stage(name):
    def decorator(fn):
        def wrapper(*args, **kwargs):
            torch.cuda.reset_peak_memory_stats()
            entry_mem = torch.cuda.memory_allocated()
            result = fn(*args, **kwargs)
            peak_mem = torch.cuda.max_memory_allocated()
            exit_mem = torch.cuda.memory_allocated()
            _stage_memory.append({
                "stage": name,
                "entry": entry_mem,
                "peak": peak_mem,
                "exit": exit_mem,
            })
            return result
        return wrapper
    return decorator

# Patch UNet
original_unet_forward = StableDiffusionPipeline.unet.forward
StableDiffusionPipeline.unet.forward = _track_stage("unet")(original_unet_forward)

# Similar for VAE, text encoder...
"#
    }
}
```

---

## 10. Bundle Diff Engine

### 10.1 Overview

Compare two versions of bundled, minified, mangled JavaScript files (e.g., Claude Code releases).

**Challenge**: Identifiers are mangled (`authenticateUser` → `a`), but we need to match functions across versions.

**Solution**: Multi-dimensional fingerprinting using invariants that survive mangling.

### 10.2 What Survives Mangling

| Preserved | Example | Use |
|-----------|---------|-----|
| String literals | `"Authentication failed"` | Anchor matching |
| Property names | `obj.userId` | Anchor matching |
| Numbers | `3600000` | Anchor matching |
| AST structure | `if-else-return` | Structural fingerprint |
| CFG topology | Loop with 3 branches | CFG fingerprint |
| Call patterns | 5 calls, args [2,1,3] | Call fingerprint |

### 10.3 Data Structures

```rust
/// Function extracted from bundled JS
#[derive(Debug, Clone)]
pub struct FunctionUnit {
    pub id: u32,
    pub byte_range: (usize, usize),
    pub line_range: (usize, usize),
    pub mangled_name: String,
    pub param_count: usize,
    pub is_async: bool,
    pub is_generator: bool,
    pub is_arrow: bool,
    pub cfg: CFGTopology,
    pub anchors: AnchorSet,
    pub call_sites: Vec<CallSite>,
    pub fingerprints: FingerprintSet,
}

/// Multi-dimensional fingerprint for matching
#[derive(Debug, Clone, Default)]
pub struct FingerprintSet {
    /// AST shape hash (ignoring identifiers)
    pub structural: StructuralFingerprint,
    /// CFG topology hash
    pub cfg: CFGFingerprint,
    /// Anchor-based fingerprint (strings, numbers)
    pub anchor: AnchorFingerprint,
    /// Call pattern fingerprint
    pub call_pattern: CallPatternFingerprint,
    /// Size-based fingerprint
    pub size: SizeFingerprint,
    /// Optional semantic embedding
    pub semantic: Option<Vec<f32>>,
}

/// Anchors that survive mangling
#[derive(Debug, Clone, Default)]
pub struct AnchorSet {
    pub strings: Vec<StringAnchor>,
    pub numbers: Vec<NumberAnchor>,
    pub regexes: Vec<String>,
    pub properties: Vec<String>,
    pub imports: Vec<String>,
    pub exports: Vec<String>,
}
```

### 10.4 Matching Algorithm

```rust
/// 6-phase matching algorithm
pub struct BundleMatcher {
    threshold: f32,
    semantic_enabled: bool,
}

impl BundleMatcher {
    pub fn match_functions(
        &self,
        old: &[FunctionUnit],
        new: &[FunctionUnit],
    ) -> Vec<MatchResult> {
        let mut matches = Vec::new();
        let mut matched_old: HashSet<u32> = HashSet::new();
        let mut matched_new: HashSet<u32> = HashSet::new();

        // Build index for fast candidate lookup
        let new_index = MatchIndex::build(new);

        // Phase 1: Exact matches (all fingerprints identical)
        for old_fn in old {
            if let Some(new_fn) = self.find_exact_match(old_fn, new, &new_index) {
                matches.push(MatchResult::exact(old_fn.id, new_fn.id));
                matched_old.insert(old_fn.id);
                matched_new.insert(new_fn.id);
            }
        }

        // Phase 2: Anchor-based matching (unique strings)
        for old_fn in old.iter().filter(|f| !matched_old.contains(&f.id)) {
            if let Some(m) = self.match_by_anchors(old_fn, new, &matched_new) {
                matches.push(m);
                matched_old.insert(old_fn.id);
                matched_new.insert(m.new_id);
            }
        }

        // Phase 3: Structural + CFG matching
        let structural_matches = self.match_structural(
            old.iter().filter(|f| !matched_old.contains(&f.id)),
            new.iter().filter(|f| !matched_new.contains(&f.id)),
            &new_index,
        );
        // ... update matched sets

        // Phase 4: Context propagation (use call graph)
        loop {
            let new_matches = self.propagate_context(&matches, old, new, &matched_old, &matched_new);
            if new_matches.is_empty() { break; }
            // ... update matched sets
        }

        // Phase 5: Semantic matching (embedding similarity)
        if self.semantic_enabled {
            let semantic_matches = self.match_semantic(
                old.iter().filter(|f| !matched_old.contains(&f.id)),
                new.iter().filter(|f| !matched_new.contains(&f.id)),
            );
            matches.extend(semantic_matches);
        }

        // Phase 6: Fuzzy matching for remaining
        let fuzzy_matches = self.match_fuzzy(
            old.iter().filter(|f| !matched_old.contains(&f.id)),
            new.iter().filter(|f| !matched_new.contains(&f.id)),
        );
        matches.extend(fuzzy_matches);

        matches
    }

    /// Compute similarity score
    fn compute_score(&self, old: &FunctionUnit, new: &FunctionUnit) -> f32 {
        let structural = structural_similarity(&old.fingerprints.structural, &new.fingerprints.structural);
        let cfg = cfg_similarity(&old.fingerprints.cfg, &new.fingerprints.cfg);
        let anchor = anchor_similarity(&old.fingerprints.anchor, &new.fingerprints.anchor);
        let call = call_pattern_similarity(&old.fingerprints.call_pattern, &new.fingerprints.call_pattern);
        let size = size_similarity(&old.fingerprints.size, &new.fingerprints.size);

        // Weighted combination
        structural * 0.25 + cfg * 0.20 + anchor * 0.25 + call * 0.15 + size * 0.15
    }
}
```

### 10.5 Performance

```rust
/// Index for O(1) candidate lookup
pub struct MatchIndex {
    structural_exact: HashMap<u64, Vec<u32>>,
    complexity_bucket: HashMap<u8, Vec<u32>>,
    unique_string_index: HashMap<u64, Vec<u32>>,
    error_hash_index: HashMap<u64, Vec<u32>>,
    structural_lsh: LSHIndex,
    anchor_lsh: LSHIndex,
}

/// Parallel fingerprint computation
pub fn compute_fingerprints_parallel(functions: &mut [FunctionUnit], stats: &GlobalStats) {
    functions.par_iter_mut().for_each(|func| {
        func.fingerprints = FingerprintSet {
            structural: compute_structural(&func),
            cfg: compute_cfg(&func.cfg),
            anchor: compute_anchor(&func.anchors, stats),
            call_pattern: compute_call_pattern(&func.call_sites),
            size: compute_size(&func),
            semantic: None,
        };
    });
}

/// Parallel matching with work stealing
pub fn match_parallel(old: &[FunctionUnit], new: &[FunctionUnit]) -> Vec<MatchResult> {
    let new_index = MatchIndex::build(new);

    old.par_iter()
        .filter_map(|old_fn| {
            let candidates = new_index.find_candidates(old_fn);
            find_best_match(old_fn, &candidates, new)
        })
        .collect()
}
```

---

## 11. LLM Integration & RAG

### 11.1 Token-Efficient Representations

```rust
/// Compressed AST representation (~70-80% token savings)
#[derive(Debug, Clone, Serialize)]
pub struct CompactAst {
    /// Function/class signatures only
    pub signatures: Vec<String>,
    /// Condensed structure
    pub structure: String,
    /// Key identifiers
    pub identifiers: Vec<String>,
    /// Estimated tokens
    pub token_count: usize,
}

/// Signature-only view (~90% token savings)
#[derive(Debug, Clone, Serialize)]
pub struct SignatureView {
    pub functions: Vec<FunctionSignature>,
    pub classes: Vec<ClassSignature>,
    pub exports: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionSignature {
    pub name: String,
    pub params: String,  // "(a: int, b: str) -> bool"
    pub docstring_summary: Option<String>,  // First line only
}

/// Call graph summary format
#[derive(Debug, Clone, Serialize)]
pub struct CallGraphSummary {
    /// Entry points
    pub entry_points: Vec<String>,
    /// Hot functions (high fan-in)
    pub hot_functions: Vec<(String, usize)>,
    /// Module-level summary
    pub modules: Vec<ModuleSummary>,
}

/// LLM-optimized code formatter
pub struct LlmFormatter {
    max_tokens: usize,
    format: OutputFormat,
}

impl LlmFormatter {
    pub fn format(&self, module: &ModuleInfo) -> String {
        match self.format {
            OutputFormat::Full => self.format_full(module),
            OutputFormat::Compact => self.format_compact(module),
            OutputFormat::SignaturesOnly => self.format_signatures(module),
            OutputFormat::ContextWindow(budget) => self.format_with_budget(module, budget),
        }
    }

    /// Smart truncation that preserves semantics
    fn truncate_to_budget(&self, content: &str, budget: usize) -> String {
        // Priority: signatures > docstrings > important functions > details
    }
}
```

### 11.2 Multi-Index RAG

```rust
/// RAG system with multiple index types
pub struct RagSystem {
    /// Semantic index (embeddings)
    semantic: SemanticIndex,
    /// Structural index (AST patterns)
    structural: StructuralIndex,
    /// Symbol index (BM25)
    symbol: SymbolIndex,
    /// Call graph index
    callgraph: CallGraphIndex,
}

impl RagSystem {
    /// Hybrid search across all indexes
    pub fn search(&self, query: &str, k: usize) -> Vec<SearchResult> {
        // 1. Classify query intent
        let intent = self.classify_intent(query);

        // 2. Route to appropriate indexes
        let weights = self.get_index_weights(intent);

        // 3. Search each index in parallel
        let (semantic_results, structural_results, symbol_results, cg_results) = rayon::join(
            || self.semantic.search(query, k * 2),
            || self.structural.search(query, k * 2),
            || self.symbol.search(query, k * 2),
            || self.callgraph.search(query, k * 2),
        );

        // 4. Reciprocal rank fusion
        self.fuse_results(
            &[semantic_results, structural_results, symbol_results, cg_results],
            &weights,
            k,
        )
    }

    /// Build context for LLM
    pub fn build_context(&self, query: &str, budget: usize) -> LlmContext {
        let results = self.search(query, 20);

        // Expand with dependencies
        let expanded = self.expand_with_deps(&results);

        // Deduplicate and rank
        let ranked = self.rank_for_context(&expanded, query);

        // Fit to token budget
        self.assemble_context(&ranked, budget)
    }
}

/// Query intent classification
#[derive(Debug, Clone, Copy)]
pub enum QueryIntent {
    FindCode,      // "where is X implemented"
    Understand,    // "how does X work"
    Debug,         // "why is X failing"
    Refactor,      // "how to improve X"
    FindSimilar,   // "code like X"
}

impl RagSystem {
    fn get_index_weights(&self, intent: QueryIntent) -> IndexWeights {
        match intent {
            QueryIntent::FindCode => IndexWeights { semantic: 0.3, structural: 0.3, symbol: 0.3, callgraph: 0.1 },
            QueryIntent::Understand => IndexWeights { semantic: 0.4, structural: 0.2, symbol: 0.1, callgraph: 0.3 },
            QueryIntent::Debug => IndexWeights { semantic: 0.2, structural: 0.2, symbol: 0.2, callgraph: 0.4 },
            QueryIntent::Refactor => IndexWeights { semantic: 0.3, structural: 0.4, symbol: 0.1, callgraph: 0.2 },
            QueryIntent::FindSimilar => IndexWeights { semantic: 0.5, structural: 0.3, symbol: 0.1, callgraph: 0.1 },
        }
    }
}
```

---

## 12. High-Performance Architecture

### 12.1 Parallelism Strategy

```rust
use rayon::prelude::*;

/// Parallel file processing
pub fn analyze_project(files: &[PathBuf]) -> ProjectAnalysis {
    // Level 1: File-level parallelism
    let file_results: Vec<FileAnalysis> = files.par_iter()
        .map(|file| analyze_file(file))
        .collect();

    // Level 2: Cross-file analysis (needs all files)
    let call_graph = build_call_graph(&file_results);

    // Level 3: Parallel per-function analysis
    let function_analyses: Vec<_> = file_results.par_iter()
        .flat_map(|f| f.functions.par_iter())
        .map(|func| analyze_function_deep(func, &call_graph))
        .collect();

    ProjectAnalysis { file_results, call_graph, function_analyses }
}

/// Parallel graph construction
pub fn build_graphs_parallel(source: &[u8], language: &str) -> (CFGInfo, DFGInfo) {
    // CFG and DFG can be built in parallel (independent)
    let (cfg, dfg) = rayon::join(
        || CfgBuilder::build(source, language),
        || DfgBuilder::build(source, language),
    );
    (cfg, dfg)
}
```

### 12.2 Caching Strategy

```rust
/// Three-tier cache hierarchy
pub struct CacheHierarchy {
    /// L1: In-memory LRU (hot data)
    l1: LruCache<CacheKey, Arc<dyn Any>>,
    /// L2: Memory-mapped files (warm data)
    l2: MmapCache,
    /// L3: Disk cache (cold data)
    l3: DiskCache,
}

impl CacheHierarchy {
    pub fn get<T: 'static>(&self, key: &CacheKey) -> Option<Arc<T>> {
        // Try L1
        if let Some(value) = self.l1.get(key) {
            return value.downcast_ref::<Arc<T>>().cloned();
        }

        // Try L2
        if let Some(value) = self.l2.get(key) {
            self.l1.put(key.clone(), value.clone());  // Promote
            return value.downcast_ref::<Arc<T>>().cloned();
        }

        // Try L3
        if let Some(value) = self.l3.get(key) {
            self.l2.put(key.clone(), value.clone());  // Promote
            self.l1.put(key.clone(), value.clone());
            return value.downcast_ref::<Arc<T>>().cloned();
        }

        None
    }
}

/// Lazy computation with OnceLock
pub struct LazyAnalysis<T> {
    computed: OnceLock<T>,
    compute_fn: Box<dyn Fn() -> T + Send + Sync>,
}

impl<T> LazyAnalysis<T> {
    pub fn get(&self) -> &T {
        self.computed.get_or_init(|| (self.compute_fn)())
    }
}
```

### 12.3 Memory Management

```rust
/// Arena allocator for AST nodes
pub struct AstArena {
    chunks: Vec<Vec<u8>>,
    current_offset: usize,
}

impl AstArena {
    pub fn alloc<T>(&mut self, value: T) -> &mut T {
        // Allocate from arena, avoiding individual heap allocations
    }
}

/// Streaming parser for large files
pub struct StreamingParser {
    chunk_size: usize,
}

impl StreamingParser {
    /// Parse 20MB+ files without loading entirely into memory
    pub fn parse_streaming<'a>(&self, source: &'a [u8]) -> impl Iterator<Item = FunctionUnit> + 'a {
        // Find function boundaries first (lightweight scan)
        let boundaries = find_function_boundaries(source);

        // Parse each function independently
        boundaries.into_iter().map(move |(start, end)| {
            parse_single_function(&source[start..end], start)
        })
    }
}

/// Memory-bounded LRU cache
pub struct BoundedCache<K, V> {
    cache: LinkedHashMap<K, V>,
    max_memory: usize,
    current_memory: usize,
    size_fn: Box<dyn Fn(&V) -> usize>,
}

impl<K: Hash + Eq, V> BoundedCache<K, V> {
    pub fn insert(&mut self, key: K, value: V) {
        let value_size = (self.size_fn)(&value);

        // Evict until we have space
        while self.current_memory + value_size > self.max_memory {
            if let Some((_, evicted)) = self.cache.pop_front() {
                self.current_memory -= (self.size_fn)(&evicted);
            } else {
                break;
            }
        }

        self.cache.insert(key, value);
        self.current_memory += value_size;
    }
}
```

### 12.4 Performance Targets

| Operation | Target | Notes |
|-----------|--------|-------|
| Single file parse | <50ms | Most files |
| CFG construction | <20ms | Per function |
| DFG construction | <30ms | Per function |
| Semantic search | <200ms | P95 |
| Call graph (10K files) | <30s | Cold cache |
| Call graph (warm) | <100ms | Incremental |
| Bundle diff (20MB) | <60s | Full comparison |
| Memory (daemon) | <500MB | 10K file project |

---

## 13. CLI & API Design

### 13.1 CLI Commands

```bash
# Core analysis
tldr tree <path>                    # File tree
tldr structure <path>               # Code structure
tldr extract <file>                 # Full AST extraction
tldr cfg <file> <function>          # Control flow graph
tldr dfg <file> <function>          # Data flow graph
tldr slice <file> <function> <line> # Program slice
tldr calls <path>                   # Build call graph
tldr impact <function>              # Impact analysis
tldr dead <path>                    # Dead code detection

# Security analysis
tldr security <path>                # Full security scan
tldr taint <file> <function>        # Taint analysis
tldr secrets <path>                 # Secret detection

# Performance analysis
tldr perf <file>                    # Performance scoring
tldr memory <file> <function>       # Memory estimation
tldr cpu <file> <function>          # CPU cost estimation

# Git history
tldr hotspots <path>                # Change hotspots
tldr churn <path>                   # Churn analysis
tldr coupling <path>                # Change coupling
tldr expertise <path>               # Author expertise

# Runtime instrumentation
tldr trace <command>                # Trace execution
tldr correlate <trace> <path>       # Correlate with static

# ML tracing
tldr tensor-trace <command>         # Trace tensor allocations
tldr diffusers-trace <command>      # Trace diffusers pipeline

# Bundle diff
tldr bundle-diff <old> <new>        # Compare bundles

# Semantic search
tldr semantic index <path>          # Build index
tldr semantic search <query>        # Search
tldr rag <query>                    # RAG context

# Daemon
tldr daemon start                   # Start daemon
tldr daemon stop                    # Stop daemon
```

### 13.2 Library API

```rust
// Core analysis
pub fn extract_file(path: &str) -> Result<ModuleInfo>;
pub fn get_cfg(file: &str, function: &str) -> Result<CFGInfo>;
pub fn get_dfg(file: &str, function: &str) -> Result<DFGInfo>;
pub fn get_slice(file: &str, function: &str, line: usize) -> Result<Vec<usize>>;
pub fn build_call_graph(path: &str) -> Result<CallGraph>;

// Security
pub fn analyze_security(path: &str) -> Result<SecurityReport>;
pub fn analyze_taint(file: &str, function: &str) -> Result<TaintAnalysisResult>;
pub fn detect_secrets(path: &str) -> Result<Vec<SecretFinding>>;

// Performance
pub fn estimate_performance(file: &str, function: &str) -> Result<PerformanceScore>;
pub fn estimate_memory(file: &str, function: &str) -> Result<MemoryEstimate>;
pub fn estimate_cpu(file: &str, function: &str) -> Result<CpuEstimate>;

// Git history
pub fn analyze_hotspots(path: &str) -> Result<HotspotAnalysis>;
pub fn analyze_coupling(path: &str) -> Result<Vec<ChangeCoupling>>;
pub fn map_expertise(path: &str) -> Result<Vec<AuthorExpertise>>;

// Runtime
pub fn generate_tracer(language: &str, config: TracerConfig) -> Result<String>;
pub fn correlate_trace(trace_path: &str, project_path: &str) -> Result<AnnotatedGraph>;

// Bundle diff
pub fn bundle_diff(old: &[u8], new: &[u8]) -> Result<BundleDiff>;

// RAG
pub fn build_rag_index(path: &str) -> Result<RagIndex>;
pub fn rag_search(query: &str, index: &RagIndex) -> Result<Vec<SearchResult>>;
pub fn build_llm_context(query: &str, index: &RagIndex, budget: usize) -> Result<LlmContext>;
```

---

## 14. Implementation Roadmap

### Phase 1: Foundation (Current)
- [x] AST extraction (7 languages)
- [x] CFG construction
- [x] DFG construction
- [x] PDG construction
- [x] Call graph analysis
- [x] Semantic search
- [x] Basic CLI

### Phase 2: Advanced Static Analysis
- [ ] Taint analysis
- [ ] Constant propagation
- [ ] Live variable analysis
- [ ] Security detectors (SQL injection, XSS, etc.)
- [ ] Secret detection

### Phase 3: Performance Prediction
- [ ] Python memory model
- [ ] JavaScript memory model
- [ ] CPU cost models
- [ ] Performance scorer
- [ ] Recommendations engine

### Phase 4: Git History Intelligence
- [ ] Git log parser
- [ ] Hotspot detection
- [ ] Churn analysis
- [ ] Change coupling
- [ ] Author expertise mapping

### Phase 5: Runtime Instrumentation
- [ ] Python tracer (sys.monitoring)
- [ ] JavaScript tracer (V8 inspector)
- [ ] Trace format and collector
- [ ] Static-dynamic correlator

### Phase 6: Cross-Language Analysis
- [ ] pybind11 parser
- [ ] PyO3 parser
- [ ] ctypes/cffi parser
- [ ] Cross-language linker

### Phase 7: ML Framework Tracing
- [ ] PyTorch tensor tracker
- [ ] Diffusers pipeline trace
- [ ] CUDA correlation
- [ ] Memory timeline

### Phase 8: Bundle Diff
- [ ] Minified JS parser
- [ ] Multi-dimensional fingerprinting
- [ ] 6-phase matching algorithm
- [ ] Diff generation

### Phase 9: LLM Integration
- [ ] Token-efficient formatters
- [ ] Multi-index RAG
- [ ] Query intent classification
- [ ] Context assembly

### Phase 10: Polish
- [ ] Comprehensive documentation
- [ ] Performance benchmarks
- [ ] Integration tests
- [ ] IDE plugins

---

## Appendix A: File Size Estimates

| Module | Estimated Lines | Complexity |
|--------|-----------------|------------|
| lang/ | 15,000 | High |
| ast/ | 2,000 | Medium |
| cfg/ | 3,000 | High |
| dfg/ | 2,500 | High |
| pdg/ | 1,000 | Medium |
| callgraph/ | 4,000 | High |
| dataflow/ | 3,000 | Very High |
| security/ | 2,000 | Medium |
| metrics/ | 1,500 | Medium |
| patterns/ | 2,000 | Medium |
| perf/ | 4,000 | Very High |
| history/ | 2,000 | Medium |
| instrument/ | 3,000 | High |
| bindings/ | 3,000 | Very High |
| ml_trace/ | 2,500 | High |
| bundle_diff/ | 3,500 | Very High |
| semantic/ | 2,000 | Medium |
| embedding/ | 1,000 | Medium |
| rag/ | 2,000 | High |
| output/ | 1,000 | Low |
| **Total** | **~55,000** | |

---

## Appendix B: Dependencies

```toml
[dependencies]
# Core
tree-sitter = "0.20"
tree-sitter-python = "0.20"
tree-sitter-typescript = "0.20"
# ... more language grammars

# Parallelism
rayon = "1.8"
tokio = { version = "1", features = ["full"] }

# Data structures
hashbrown = "0.14"
smallvec = "1.11"
parking_lot = "0.12"

# Serialization
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# Git
git2 = "0.18"

# Embedding
usearch = "2"
tonic = "0.10"  # gRPC for TEI

# CLI
clap = { version = "4", features = ["derive"] }

# Regex
regex = "1"

# Caching
lru = "0.12"
memmap2 = "0.9"
```

---

## Appendix C: References

1. Data Flow Analysis - Aho, Lam, Sethi, Ullman (Dragon Book)
2. Static Analysis (SPA) - Møller, Schwartzbach
3. Taint Analysis - Tripp et al., TAJ
4. Cognitive Complexity - SonarSource
5. Halstead Metrics - Software Science
6. Code Clone Detection - Roy, Cordy, Koschke
7. Git Mining - Bird et al., Mining Version Archives
8. V8 Optimization - https://v8.dev/docs
9. PyTorch Internals - https://pytorch.org/docs/stable/notes/extending.html
