# Advanced Static Analysis Features - Design Document

## Executive Summary

This document outlines the design for advanced static analysis capabilities to be added to the llm-tldr-rs codebase. The current implementation provides solid foundations with CFG, DFG, PDG, and call graph analysis. These new features will build upon that foundation to provide:

1. Enhanced Control Flow Analysis (exception tracking, async/await, generators)
2. Advanced Data Flow Analysis (taint analysis, constant propagation, alias analysis)
3. Security Analysis (injection detection, credential scanning)
4. Type Flow Analysis (for dynamic languages)
5. Complexity Metrics (cognitive complexity, coupling/cohesion)
6. Pattern Detection (code smells, anti-patterns, semantic duplication)

---

## 1. Enhanced Control Flow Analysis

### 1.1 Exception Flow Tracking

**Current State**: CFG has `Exception` and `Finally` edge types, but exception propagation across function boundaries is not tracked.

**Design**:

```rust
// src/cfg/exception_flow.rs

use std::collections::{HashMap, HashSet};

/// Types of exceptions that can be thrown/caught.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExceptionType {
    /// Named exception type (e.g., "ValueError", "std::runtime_error")
    Named(String),
    /// Generic/unknown exception
    Generic,
    /// Base exception type (catches all)
    BaseException,
}

/// Information about an exception throw site.
#[derive(Debug, Clone)]
pub struct ThrowSite {
    /// Line number where exception is thrown
    pub line: usize,
    /// Type of exception thrown
    pub exception_type: ExceptionType,
    /// Whether this is explicit (raise/throw) or implicit (function call)
    pub is_explicit: bool,
    /// For implicit throws, the called function
    pub called_function: Option<String>,
}

/// Information about an exception catch site.
#[derive(Debug, Clone)]
pub struct CatchSite {
    /// Line number of catch/except clause
    pub line: usize,
    /// Types of exceptions caught (empty = catch all)
    pub caught_types: Vec<ExceptionType>,
    /// Variable binding for the exception (if any)
    pub binding: Option<String>,
    /// Block ID in CFG
    pub block_id: BlockId,
}

/// Exception flow information for a function.
#[derive(Debug, Clone)]
pub struct ExceptionFlowInfo {
    /// All throw sites in the function
    pub throw_sites: Vec<ThrowSite>,
    /// All catch sites in the function
    pub catch_sites: Vec<CatchSite>,
    /// Mapping: throw site -> reachable catch sites
    pub throw_catch_edges: HashMap<usize, Vec<usize>>,
    /// Exceptions that can escape the function (uncaught)
    pub escaping_exceptions: Vec<ExceptionType>,
    /// Try-finally associations for resource cleanup tracking
    pub finally_blocks: Vec<FinallyBlock>,
}

#[derive(Debug, Clone)]
pub struct FinallyBlock {
    pub try_start_line: usize,
    pub finally_start_line: usize,
    pub finally_end_line: usize,
    /// Resources acquired in try that must be released
    pub managed_resources: Vec<String>,
}

/// Builder for exception flow analysis.
pub struct ExceptionFlowBuilder<'a> {
    cfg: &'a CFGInfo,
    source: &'a [u8],
    language: &'a str,
}

impl<'a> ExceptionFlowBuilder<'a> {
    /// Build exception flow graph.
    ///
    /// Algorithm:
    /// 1. Identify all throw sites (explicit raises + calls to throwing functions)
    /// 2. Identify all catch sites with their exception filters
    /// 3. Compute throw->catch edges using CFG dominator analysis
    /// 4. Identify escaping exceptions (thrown but not caught)
    pub fn build(&self) -> ExceptionFlowInfo {
        // Implementation
        todo!()
    }

    /// Compute which catch sites can handle a given throw site.
    /// Uses reverse dominator tree to find enclosing try blocks.
    fn compute_handlers(&self, throw_line: usize) -> Vec<usize> {
        // Walk up the dominator tree from throw site
        // Find catch blocks that dominate the merge point
        todo!()
    }
}
```

**Integration Points**:
- Extends `CFGInfo` with `exception_flow: Option<ExceptionFlowInfo>`
- Language trait method: `fn analyze_exception_flow(&self, cfg: &CFGInfo, source: &[u8]) -> ExceptionFlowInfo`

### 1.2 Async/Await Flow Modeling

**Current State**: Basic async function detection exists, but await points and cancellation are not modeled.

**Design**:

```rust
// src/cfg/async_flow.rs

/// Types of async operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncOpKind {
    /// await expression
    Await,
    /// async for/async with
    AsyncIteration,
    /// Task spawn (asyncio.create_task, tokio::spawn)
    TaskSpawn,
    /// Task join/gather
    TaskJoin,
    /// Cancellation point
    CancellationPoint,
    /// Select/race between multiple futures
    Select,
}

/// An async operation in the control flow.
#[derive(Debug, Clone)]
pub struct AsyncOp {
    pub kind: AsyncOpKind,
    pub line: usize,
    /// The awaited expression (for Await ops)
    pub awaited_expr: Option<String>,
    /// Spawned task name (for TaskSpawn)
    pub task_name: Option<String>,
}

/// Async control flow information.
#[derive(Debug, Clone)]
pub struct AsyncFlowInfo {
    /// Whether the function is async
    pub is_async: bool,
    /// All async operations
    pub async_ops: Vec<AsyncOp>,
    /// Await point -> possible resume points (after cancellation)
    pub cancellation_edges: HashMap<usize, Vec<usize>>,
    /// Spawned tasks and their join points
    pub task_graph: TaskGraph,
}

/// Graph of spawned tasks and their dependencies.
#[derive(Debug, Clone, Default)]
pub struct TaskGraph {
    /// task_id -> (spawn_line, join_lines)
    pub tasks: HashMap<String, (usize, Vec<usize>)>,
    /// Dependencies between tasks
    pub dependencies: Vec<(String, String)>,
}

/// Edge type for async control flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncEdgeType {
    /// Normal await resume
    Resume,
    /// Cancellation path
    Cancelled,
    /// Timeout path
    Timeout,
    /// Error propagation
    Error,
}
```

**Algorithm**:
1. Identify async function entry points
2. Mark all await expressions as suspension points
3. Build task spawn/join graph for structured concurrency
4. Model cancellation paths (task.cancel() -> await points)
5. Detect potential deadlocks in task dependencies

### 1.3 Generator/Iterator Flow

**Design**:

```rust
// src/cfg/generator_flow.rs

/// Yield point in a generator.
#[derive(Debug, Clone)]
pub struct YieldPoint {
    pub line: usize,
    /// Value yielded (expression)
    pub yielded_value: Option<String>,
    /// For yield from, the delegated iterator
    pub delegate: Option<String>,
    /// Whether this is yield from (Python) or similar
    pub is_delegating: bool,
}

/// Generator state machine representation.
#[derive(Debug, Clone)]
pub struct GeneratorStateMachine {
    /// States corresponding to yield points
    pub states: Vec<GeneratorState>,
    /// Transitions between states
    pub transitions: Vec<StateTransition>,
    /// Initial state (before first yield)
    pub initial: usize,
    /// Final states (return or end of function)
    pub finals: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct GeneratorState {
    pub id: usize,
    /// Lines of code in this state (between yields)
    pub lines: Vec<usize>,
    /// The yield point that ends this state (None for final)
    pub yield_point: Option<YieldPoint>,
}

#[derive(Debug, Clone)]
pub struct StateTransition {
    pub from_state: usize,
    pub to_state: usize,
    /// Condition for this transition (for generator.send())
    pub sent_value: Option<String>,
}
```

### 1.4 Loop Invariant Detection

**Design**:

```rust
// src/cfg/loop_analysis.rs

/// Information about a loop.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// Header block ID
    pub header: BlockId,
    /// Back edge source blocks
    pub back_edges: Vec<BlockId>,
    /// All blocks in the loop body
    pub body_blocks: HashSet<BlockId>,
    /// Exit blocks (targets of break or normal exit)
    pub exits: Vec<BlockId>,
    /// Nesting depth (0 = outermost)
    pub depth: usize,
    /// Parent loop (if nested)
    pub parent: Option<BlockId>,
}

/// Loop invariant computation result.
#[derive(Debug, Clone)]
pub struct LoopInvariant {
    pub loop_header: BlockId,
    /// Lines that are loop-invariant (can be hoisted)
    pub invariant_lines: Vec<usize>,
    /// Variables that are loop-invariant
    pub invariant_vars: HashSet<String>,
    /// Induction variables (change predictably each iteration)
    pub induction_vars: Vec<InductionVariable>,
}

#[derive(Debug, Clone)]
pub struct InductionVariable {
    pub name: String,
    /// Initial value expression
    pub init: String,
    /// Step expression (e.g., "+1", "*2")
    pub step: String,
    /// Bound expression (if determinable)
    pub bound: Option<String>,
}

impl LoopInvariant {
    /// Compute loop invariants using reaching definitions.
    ///
    /// Algorithm:
    /// 1. Compute reaching definitions at loop header
    /// 2. For each statement S in loop body:
    ///    - S is loop-invariant if all its operands are:
    ///      a) Constants, or
    ///      b) Defined outside the loop, or
    ///      c) Defined by loop-invariant statements
    /// 3. Iterate until fixed point
    pub fn compute(cfg: &CFGInfo, dfg: &DFGInfo, loop_info: &LoopInfo) -> Self {
        todo!()
    }
}
```

### 1.5 Dead Branch Detection

**Design**:

```rust
// src/cfg/dead_branch.rs

/// A branch that is statically determinable to be dead.
#[derive(Debug, Clone)]
pub struct DeadBranch {
    /// Block ID of the branch point
    pub branch_block: BlockId,
    /// The dead edge
    pub dead_edge: EdgeType,
    /// Reason the branch is dead
    pub reason: DeadBranchReason,
    /// Line number
    pub line: usize,
}

#[derive(Debug, Clone)]
pub enum DeadBranchReason {
    /// Condition is constant True
    ConstantTrue,
    /// Condition is constant False
    ConstantFalse,
    /// Type narrowing eliminates branch (isinstance checks)
    TypeNarrowing { narrowed_type: String },
    /// Previous return/raise makes branch unreachable
    PreviousTerminator,
    /// Loop never enters (empty range, etc.)
    EmptyIteration,
    /// Pattern match exhaustiveness
    ExhaustiveMatch,
}

/// Dead branch detector.
pub struct DeadBranchDetector<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
    /// Known constant values from constant propagation
    constants: HashMap<String, ConstantValue>,
}

impl<'a> DeadBranchDetector<'a> {
    /// Detect all dead branches.
    ///
    /// Uses:
    /// 1. Constant propagation results
    /// 2. Type flow analysis (for isinstance)
    /// 3. Dominator analysis (for previous terminators)
    pub fn detect(&self) -> Vec<DeadBranch> {
        todo!()
    }
}
```

---

## 2. Advanced Data Flow Analysis

### 2.1 Taint Analysis

**Purpose**: Track data from untrusted sources (sources) to security-sensitive operations (sinks).

**Design**:

```rust
// src/dataflow/taint.rs

use std::collections::{HashMap, HashSet};

/// Source of tainted data.
#[derive(Debug, Clone)]
pub struct TaintSource {
    pub line: usize,
    pub variable: String,
    pub source_kind: TaintSourceKind,
    /// Confidence level (high for explicit sources, lower for inferred)
    pub confidence: f32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TaintSourceKind {
    /// User input (request.form, input(), sys.argv)
    UserInput,
    /// Environment variables
    Environment,
    /// File contents
    FileRead,
    /// Network data
    NetworkData,
    /// Database query result
    DatabaseResult,
    /// Deserialization (pickle.load, json.loads with external data)
    Deserialization,
    /// Custom source pattern
    Custom(String),
}

/// Sink where tainted data is dangerous.
#[derive(Debug, Clone)]
pub struct TaintSink {
    pub line: usize,
    pub variable: String,
    pub sink_kind: TaintSinkKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TaintSinkKind {
    /// SQL query execution
    SqlQuery,
    /// Shell command execution
    ShellCommand,
    /// File path operations
    FilePath,
    /// HTML output (XSS)
    HtmlOutput,
    /// Code evaluation (eval, exec)
    CodeEval,
    /// Deserialization with untrusted data
    Deserialization,
    /// LDAP query
    LdapQuery,
    /// XML parsing (XXE)
    XmlParsing,
    /// Custom sink pattern
    Custom(String),
}

/// A detected taint flow from source to sink.
#[derive(Debug, Clone)]
pub struct TaintFlow {
    pub source: TaintSource,
    pub sink: TaintSink,
    /// Path of variable transformations
    pub path: Vec<TaintPathStep>,
    /// Whether the flow passes through a sanitizer
    pub sanitized: bool,
    /// Sanitizer function if applicable
    pub sanitizer: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TaintPathStep {
    pub line: usize,
    pub variable: String,
    /// Operation that propagates or transforms taint
    pub operation: String,
}

/// Sanitizer that removes taint.
#[derive(Debug, Clone)]
pub struct Sanitizer {
    /// Function/method name pattern
    pub pattern: String,
    /// Which parameter is sanitized
    pub sanitized_param: usize,
    /// Which sink types this sanitizer protects against
    pub protects_against: Vec<TaintSinkKind>,
}

/// Taint analysis configuration.
#[derive(Debug, Clone)]
pub struct TaintConfig {
    /// Source patterns by language
    pub sources: HashMap<String, Vec<SourcePattern>>,
    /// Sink patterns by language
    pub sinks: HashMap<String, Vec<SinkPattern>>,
    /// Sanitizer patterns by language
    pub sanitizers: HashMap<String, Vec<Sanitizer>>,
}

#[derive(Debug, Clone)]
pub struct SourcePattern {
    pub kind: TaintSourceKind,
    /// Function/method name regex
    pub function_pattern: String,
    /// Which return value or parameter is tainted
    pub tainted_output: TaintedOutput,
}

#[derive(Debug, Clone)]
pub enum TaintedOutput {
    ReturnValue,
    Parameter(usize),
    AllParameters,
}

#[derive(Debug, Clone)]
pub struct SinkPattern {
    pub kind: TaintSinkKind,
    /// Function/method name regex
    pub function_pattern: String,
    /// Which parameter is sensitive
    pub sensitive_param: usize,
}

/// Taint analyzer.
pub struct TaintAnalyzer<'a> {
    dfg: &'a DFGInfo,
    call_graph: Option<&'a CallGraph>,
    config: &'a TaintConfig,
}

impl<'a> TaintAnalyzer<'a> {
    /// Perform taint analysis.
    ///
    /// Algorithm:
    /// 1. Identify all taint sources in the DFG
    /// 2. Propagate taint through data flow edges
    /// 3. Mark sanitized flows (taint passing through sanitizers)
    /// 4. Check if taint reaches any sinks
    /// 5. For inter-procedural: follow call graph edges
    pub fn analyze(&self) -> TaintAnalysisResult {
        todo!()
    }

    /// Propagate taint from a source using forward data flow.
    fn propagate_taint(&self, source: &TaintSource) -> HashSet<(usize, String)> {
        // Use cached adjacency for efficient propagation
        let mut tainted: HashSet<(usize, String)> = HashSet::new();
        let mut worklist: Vec<(usize, String)> = vec![(source.line, source.variable.clone())];

        while let Some((line, var)) = worklist.pop() {
            if !tainted.insert((line, var.clone())) {
                continue;
            }

            // Follow data flow edges
            if let Some(outgoing) = self.dfg.get_var_outgoing(&var, line) {
                for &target_line in outgoing {
                    worklist.push((target_line, var.clone()));
                }
            }
        }

        tainted
    }
}

#[derive(Debug)]
pub struct TaintAnalysisResult {
    pub flows: Vec<TaintFlow>,
    /// Flows that are definitely vulnerable (reach sink without sanitization)
    pub vulnerabilities: Vec<TaintFlow>,
    /// Flows that might be vulnerable (partial sanitization)
    pub warnings: Vec<TaintFlow>,
}
```

**Default Source/Sink Patterns**:

```rust
impl Default for TaintConfig {
    fn default() -> Self {
        let mut config = TaintConfig {
            sources: HashMap::new(),
            sinks: HashMap::new(),
            sanitizers: HashMap::new(),
        };

        // Python sources
        config.sources.insert("python".into(), vec![
            SourcePattern {
                kind: TaintSourceKind::UserInput,
                function_pattern: r"(input|raw_input|request\.(form|args|data|json|files|values|cookies|headers)|sys\.argv|os\.environ)".into(),
                tainted_output: TaintedOutput::ReturnValue,
            },
            SourcePattern {
                kind: TaintSourceKind::FileRead,
                function_pattern: r"(open\(.*\)\.read|\.read\(\)|\.readlines?\()".into(),
                tainted_output: TaintedOutput::ReturnValue,
            },
        ]);

        // Python sinks
        config.sinks.insert("python".into(), vec![
            SinkPattern {
                kind: TaintSinkKind::SqlQuery,
                function_pattern: r"(cursor\.execute|\.execute\(|\.raw\(|connection\.execute)".into(),
                sensitive_param: 0,
            },
            SinkPattern {
                kind: TaintSinkKind::ShellCommand,
                function_pattern: r"(os\.system|os\.popen|subprocess\.(run|call|Popen)|eval|exec)".into(),
                sensitive_param: 0,
            },
        ]);

        // Python sanitizers
        config.sanitizers.insert("python".into(), vec![
            Sanitizer {
                pattern: r"(escape|quote|sanitize|clean|bleach\.|markupsafe\.|parameterized|prepared_statement)".into(),
                sanitized_param: 0,
                protects_against: vec![TaintSinkKind::SqlQuery, TaintSinkKind::HtmlOutput],
            },
        ]);

        config
    }
}
```

### 2.2 Constant Propagation

**Design**:

```rust
// src/dataflow/constant_prop.rs

/// A constant value tracked during analysis.
#[derive(Debug, Clone, PartialEq)]
pub enum ConstantValue {
    /// Integer constant
    Int(i64),
    /// Float constant
    Float(f64),
    /// String constant
    String(String),
    /// Boolean constant
    Bool(bool),
    /// None/null
    Null,
    /// Known type but unknown value
    Unknown,
    /// Value depends on control flow (phi node)
    Varying,
}

/// Constant propagation result for a function.
#[derive(Debug, Clone)]
pub struct ConstantPropResult {
    /// Variable -> value at each program point
    pub values: HashMap<usize, HashMap<String, ConstantValue>>,
    /// Expressions that can be folded (line, expression, result)
    pub foldable_expressions: Vec<(usize, String, ConstantValue)>,
    /// Conditions that are constant (for dead branch detection)
    pub constant_conditions: Vec<(usize, bool)>,
}

/// Constant propagation analyzer using abstract interpretation.
pub struct ConstantPropagator<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
    source: &'a [u8],
}

impl<'a> ConstantPropagator<'a> {
    /// Perform constant propagation using worklist algorithm.
    ///
    /// Algorithm (forward data flow):
    /// 1. Initialize all variables to Top (unknown)
    /// 2. Process entry block: set parameters to Unknown
    /// 3. For each block in topological order:
    ///    a. Compute meet of predecessor values
    ///    b. Apply transfer function for each statement
    ///    c. If any value changed, add successors to worklist
    /// 4. Iterate until fixed point
    pub fn analyze(&self) -> ConstantPropResult {
        todo!()
    }

    /// Transfer function for a statement.
    fn transfer(
        &self,
        stmt_line: usize,
        in_state: &HashMap<String, ConstantValue>,
    ) -> HashMap<String, ConstantValue> {
        todo!()
    }

    /// Meet operation for lattice (Constant analysis uses meet semilattice).
    fn meet(a: &ConstantValue, b: &ConstantValue) -> ConstantValue {
        match (a, b) {
            // Same value -> keep it
            (x, y) if x == y => x.clone(),
            // Unknown meets anything -> that thing
            (ConstantValue::Unknown, x) | (x, ConstantValue::Unknown) => x.clone(),
            // Different constants -> Varying
            _ => ConstantValue::Varying,
        }
    }
}
```

### 2.3 Reaching Definitions

**Design**:

```rust
// src/dataflow/reaching_defs.rs

/// A definition that can reach a program point.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Definition {
    pub variable: String,
    pub line: usize,
    pub block: BlockId,
    /// Whether this is a "may define" (conditional) or "must define" (unconditional)
    pub is_definite: bool,
}

/// Reaching definitions analysis result.
#[derive(Debug)]
pub struct ReachingDefsResult {
    /// For each program point, which definitions reach it
    pub reaching_in: HashMap<usize, HashSet<Definition>>,
    /// Definitions that are live OUT of each line
    pub reaching_out: HashMap<usize, HashSet<Definition>>,
    /// Use-def chains: (use_line, var) -> definitions
    pub use_def_chains: HashMap<(usize, String), HashSet<Definition>>,
    /// Def-use chains: definition -> (use_line, var)
    pub def_use_chains: HashMap<Definition, HashSet<(usize, String)>>,
}

/// Reaching definitions analyzer.
pub struct ReachingDefsAnalyzer<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
}

impl<'a> ReachingDefsAnalyzer<'a> {
    /// Compute reaching definitions.
    ///
    /// Algorithm (forward data flow):
    /// GEN[B] = definitions in block B that reach end of B
    /// KILL[B] = definitions killed by definitions in B
    /// OUT[B] = GEN[B] union (IN[B] - KILL[B])
    /// IN[B] = union of OUT[P] for all predecessors P
    pub fn analyze(&self) -> ReachingDefsResult {
        todo!()
    }
}
```

### 2.4 Live Variable Analysis

**Design**:

```rust
// src/dataflow/live_vars.rs

/// Live variable analysis result.
#[derive(Debug)]
pub struct LiveVarsResult {
    /// Variables live at entry to each line
    pub live_in: HashMap<usize, HashSet<String>>,
    /// Variables live at exit of each line
    pub live_out: HashMap<usize, HashSet<String>>,
    /// Dead assignments (assignments to variables never used afterward)
    pub dead_assignments: Vec<DeadAssignment>,
    /// Variables that are never read (but defined)
    pub unused_variables: Vec<(String, usize)>,
}

#[derive(Debug, Clone)]
pub struct DeadAssignment {
    pub variable: String,
    pub line: usize,
    /// Whether another assignment overwrites before any use
    pub overwritten: bool,
}

/// Live variable analyzer (backward data flow).
pub struct LiveVarsAnalyzer<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
}

impl<'a> LiveVarsAnalyzer<'a> {
    /// Compute live variables.
    ///
    /// Algorithm (backward data flow):
    /// USE[B] = variables used in B before any definition
    /// DEF[B] = variables defined in B
    /// IN[B] = USE[B] union (OUT[B] - DEF[B])
    /// OUT[B] = union of IN[S] for all successors S
    pub fn analyze(&self) -> LiveVarsResult {
        todo!()
    }
}
```

### 2.5 Alias Analysis

**Purpose**: Track which variables may refer to the same memory location.

**Design**:

```rust
// src/dataflow/alias.rs

/// An abstract memory location.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemoryLocation {
    /// Stack variable
    Variable(String),
    /// Heap allocation site (line number)
    HeapAlloc(usize),
    /// Field access (base, field_name)
    Field(Box<MemoryLocation>, String),
    /// Array/list element (base, index if known)
    Element(Box<MemoryLocation>, Option<i64>),
    /// Global variable
    Global(String),
    /// Unknown location
    Unknown,
}

/// Points-to set for a variable.
#[derive(Debug, Clone)]
pub struct PointsToSet {
    /// Locations this variable may point to
    pub locations: HashSet<MemoryLocation>,
    /// Whether the set may include unknown locations
    pub may_be_unknown: bool,
}

/// Alias analysis result.
#[derive(Debug)]
pub struct AliasAnalysisResult {
    /// Points-to information at each program point
    pub points_to: HashMap<usize, HashMap<String, PointsToSet>>,
    /// Alias queries: (var1, var2) -> MayAlias | MustAlias | NoAlias
    pub alias_pairs: HashMap<(String, String), AliasRelation>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasRelation {
    /// Definitely alias (same location)
    MustAlias,
    /// May or may not alias
    MayAlias,
    /// Definitely don't alias
    NoAlias,
}

/// Alias analyzer using Andersen's analysis (flow-insensitive).
pub struct AliasAnalyzer<'a> {
    dfg: &'a DFGInfo,
    call_graph: Option<&'a CallGraph>,
}

impl<'a> AliasAnalyzer<'a> {
    /// Perform points-to analysis.
    ///
    /// Uses Andersen's inclusion-based algorithm:
    /// 1. Build constraint graph from assignments
    /// 2. Propagate points-to sets through constraints
    /// 3. Resolve alias queries using computed sets
    pub fn analyze(&self) -> AliasAnalysisResult {
        todo!()
    }
}
```

---

## 3. Security Analysis

### 3.1 SQL Injection Detection

**Design**:

```rust
// src/security/sql_injection.rs

/// SQL injection vulnerability finding.
#[derive(Debug, Clone)]
pub struct SqlInjectionFinding {
    pub line: usize,
    /// The unsafe SQL construction
    pub sql_expr: String,
    /// User input variable that reaches the query
    pub tainted_var: String,
    /// Source of the taint
    pub taint_source: TaintSource,
    /// Severity based on context
    pub severity: Severity,
    /// Suggested fix
    pub suggestion: String,
}

/// SQL injection detector.
pub struct SqlInjectionDetector<'a> {
    dfg: &'a DFGInfo,
    source: &'a [u8],
    language: &'a str,
}

impl<'a> SqlInjectionDetector<'a> {
    /// Detect SQL injection vulnerabilities.
    ///
    /// Patterns detected:
    /// 1. String formatting in SQL: f"SELECT * FROM {var}"
    /// 2. String concatenation: "SELECT * FROM " + var
    /// 3. % formatting: "SELECT * FROM %s" % var
    /// 4. .format(): "SELECT * FROM {}".format(var)
    pub fn detect(&self) -> Vec<SqlInjectionFinding> {
        todo!()
    }
}
```

### 3.2 XSS Detection

**Design**:

```rust
// src/security/xss.rs

/// XSS vulnerability finding.
#[derive(Debug, Clone)]
pub struct XssFinding {
    pub line: usize,
    /// The unsafe output expression
    pub output_expr: String,
    /// User input variable
    pub tainted_var: String,
    /// Context (HTML attribute, JavaScript, etc.)
    pub context: XssContext,
    pub severity: Severity,
    pub suggestion: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum XssContext {
    /// Inside HTML body
    HtmlBody,
    /// Inside HTML attribute
    HtmlAttribute,
    /// Inside JavaScript
    JavaScript,
    /// Inside URL
    Url,
    /// Inside CSS
    Css,
}

/// XSS detector.
pub struct XssDetector<'a> {
    dfg: &'a DFGInfo,
    source: &'a [u8],
    taint_result: &'a TaintAnalysisResult,
}
```

### 3.3 Path Traversal Detection

```rust
// src/security/path_traversal.rs

/// Path traversal vulnerability finding.
#[derive(Debug, Clone)]
pub struct PathTraversalFinding {
    pub line: usize,
    /// The file operation
    pub file_op: String,
    /// User input reaching file path
    pub tainted_var: String,
    /// Whether ../ sequences are checked
    pub has_traversal_check: bool,
    pub severity: Severity,
}
```

### 3.4 Command Injection Detection

```rust
// src/security/command_injection.rs

/// Command injection vulnerability finding.
#[derive(Debug, Clone)]
pub struct CommandInjectionFinding {
    pub line: usize,
    /// The command execution call
    pub command_expr: String,
    /// Tainted variable in command
    pub tainted_var: String,
    /// Whether shell=True or equivalent
    pub uses_shell: bool,
    pub severity: Severity,
}
```

### 3.5 Secrets/Credentials Detection

**Design**:

```rust
// src/security/secrets.rs

/// A detected secret or credential.
#[derive(Debug, Clone)]
pub struct SecretFinding {
    pub line: usize,
    /// The suspicious string/value
    pub value_snippet: String,
    /// Type of secret
    pub secret_type: SecretType,
    /// Confidence (pattern match vs entropy)
    pub confidence: f32,
    /// Variable name if assigned
    pub variable: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SecretType {
    /// AWS access key
    AwsAccessKey,
    /// AWS secret key
    AwsSecretKey,
    /// GitHub token
    GitHubToken,
    /// Private key (RSA, etc.)
    PrivateKey,
    /// API key (generic)
    ApiKey,
    /// Database password
    DatabasePassword,
    /// JWT secret
    JwtSecret,
    /// High entropy string
    HighEntropy,
    /// Custom pattern
    Custom(String),
}

/// Secret detector using pattern matching and entropy analysis.
pub struct SecretDetector {
    patterns: Vec<SecretPattern>,
    entropy_threshold: f64,
}

#[derive(Debug, Clone)]
pub struct SecretPattern {
    pub name: String,
    pub regex: String,
    pub secret_type: SecretType,
    pub confidence: f32,
}

impl SecretDetector {
    /// Scan source for secrets.
    pub fn detect(&self, source: &[u8]) -> Vec<SecretFinding> {
        todo!()
    }

    /// Calculate Shannon entropy of a string.
    fn entropy(s: &str) -> f64 {
        let mut freq = HashMap::new();
        for c in s.chars() {
            *freq.entry(c).or_insert(0) += 1;
        }
        let len = s.len() as f64;
        -freq.values().map(|&count| {
            let p = count as f64 / len;
            p * p.log2()
        }).sum::<f64>()
    }
}

impl Default for SecretDetector {
    fn default() -> Self {
        Self {
            patterns: vec![
                SecretPattern {
                    name: "AWS Access Key".into(),
                    regex: r"AKIA[0-9A-Z]{16}".into(),
                    secret_type: SecretType::AwsAccessKey,
                    confidence: 0.95,
                },
                SecretPattern {
                    name: "GitHub Token".into(),
                    regex: r"ghp_[0-9a-zA-Z]{36}|github_pat_[0-9a-zA-Z]{22}_[0-9a-zA-Z]{59}".into(),
                    secret_type: SecretType::GitHubToken,
                    confidence: 0.95,
                },
                SecretPattern {
                    name: "Private Key".into(),
                    regex: r"-----BEGIN (RSA |EC |OPENSSH )?PRIVATE KEY-----".into(),
                    secret_type: SecretType::PrivateKey,
                    confidence: 0.99,
                },
                SecretPattern {
                    name: "Generic API Key".into(),
                    regex: r#"(?i)(api[_-]?key|apikey)['":\s]+=?\s*['"]?([a-zA-Z0-9]{20,})"#.into(),
                    secret_type: SecretType::ApiKey,
                    confidence: 0.7,
                },
            ],
            entropy_threshold: 4.5, // bits per character
        }
    }
}
```

---

## 4. Type Flow Analysis (Dynamic Languages)

**Purpose**: Infer and track types through dynamic language code where static types are not declared.

**Design**:

```rust
// src/typeflow/mod.rs

use std::collections::{HashMap, HashSet};

/// An inferred type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InferredType {
    /// Primitive types
    Int,
    Float,
    String,
    Bool,
    None,
    /// Collection types
    List(Box<InferredType>),
    Dict(Box<InferredType>, Box<InferredType>),
    Set(Box<InferredType>),
    Tuple(Vec<InferredType>),
    /// Class instance
    Instance(String),
    /// Callable with signature
    Callable {
        params: Vec<InferredType>,
        returns: Box<InferredType>,
    },
    /// Union of possible types
    Union(Vec<InferredType>),
    /// Optional (Union with None)
    Optional(Box<InferredType>),
    /// Any type (unknown)
    Any,
    /// Never type (unreachable)
    Never,
    /// Type variable (generics)
    TypeVar(String),
}

/// Type narrowing from a guard.
#[derive(Debug, Clone)]
pub struct TypeNarrowing {
    pub line: usize,
    pub variable: String,
    pub original_type: InferredType,
    pub narrowed_type: InferredType,
    /// The guard expression that narrows
    pub guard: String,
    /// Which branch gets the narrowed type
    pub branch: bool,
}

/// Type flow analysis result.
#[derive(Debug)]
pub struct TypeFlowResult {
    /// Inferred type at each program point
    pub types: HashMap<usize, HashMap<String, InferredType>>,
    /// Type narrowings from guards
    pub narrowings: Vec<TypeNarrowing>,
    /// Type errors (incompatible operations)
    pub type_errors: Vec<TypeError>,
    /// Widened types from joins
    pub widenings: Vec<TypeWidening>,
}

#[derive(Debug, Clone)]
pub struct TypeError {
    pub line: usize,
    pub message: String,
    pub expected: InferredType,
    pub actual: InferredType,
}

#[derive(Debug, Clone)]
pub struct TypeWidening {
    pub line: usize,
    pub variable: String,
    pub from_types: Vec<InferredType>,
    pub to_type: InferredType,
}

/// Type flow analyzer using abstract interpretation.
pub struct TypeFlowAnalyzer<'a> {
    cfg: &'a CFGInfo,
    dfg: &'a DFGInfo,
    source: &'a [u8],
    /// External type information (stubs, annotations)
    type_hints: &'a TypeHints,
}

/// External type hints from annotations or stub files.
#[derive(Debug, Default)]
pub struct TypeHints {
    /// Function signatures: func_name -> (param_types, return_type)
    pub functions: HashMap<String, (Vec<InferredType>, InferredType)>,
    /// Class fields: class.field -> type
    pub fields: HashMap<String, InferredType>,
    /// Variable annotations: var -> type
    pub variables: HashMap<String, InferredType>,
}

impl<'a> TypeFlowAnalyzer<'a> {
    /// Perform type inference and flow analysis.
    ///
    /// Algorithm:
    /// 1. Collect type hints from annotations
    /// 2. Infer types from literals and known functions
    /// 3. Propagate types through data flow
    /// 4. Handle type guards (isinstance, is None, etc.)
    /// 5. Join types at merge points (unions)
    /// 6. Report type errors
    pub fn analyze(&self) -> TypeFlowResult {
        todo!()
    }

    /// Infer type from an expression node.
    fn infer_expr_type(&self, line: usize, expr: &str) -> InferredType {
        // Pattern matching for literal types
        // Function call return types
        // Attribute access types
        todo!()
    }

    /// Handle type guard (isinstance, is None, etc.)
    fn handle_guard(&self, guard_line: usize, var: &str, current_type: &InferredType) -> (InferredType, InferredType) {
        // Returns (true_branch_type, false_branch_type)
        todo!()
    }

    /// Join types at merge point.
    fn join_types(types: &[InferredType]) -> InferredType {
        if types.is_empty() {
            return InferredType::Never;
        }
        if types.len() == 1 {
            return types[0].clone();
        }

        // Filter out Never types
        let non_never: Vec<_> = types.iter()
            .filter(|t| **t != InferredType::Never)
            .collect();

        if non_never.is_empty() {
            return InferredType::Never;
        }
        if non_never.len() == 1 {
            return non_never[0].clone();
        }

        // Check if all same type
        if non_never.iter().all(|t| *t == non_never[0]) {
            return non_never[0].clone();
        }

        // Create union (deduplicated)
        let unique: HashSet<_> = non_never.into_iter().cloned().collect();
        InferredType::Union(unique.into_iter().collect())
    }
}
```

---

## 5. Complexity Metrics

### 5.1 Cognitive Complexity

**Purpose**: Measure how hard code is to understand (vs cyclomatic which measures testability).

**Design**:

```rust
// src/metrics/cognitive.rs

/// Cognitive complexity result.
#[derive(Debug, Clone)]
pub struct CognitiveComplexityResult {
    /// Total cognitive complexity score
    pub score: usize,
    /// Breakdown by construct type
    pub breakdown: CognitiveBreakdown,
    /// Individual contributions by line
    pub contributions: Vec<ComplexityContribution>,
    /// Rating (simple, moderate, complex, very_complex)
    pub rating: ComplexityRating,
}

#[derive(Debug, Clone, Default)]
pub struct CognitiveBreakdown {
    pub conditions: usize,      // if, elif, switch case
    pub loops: usize,           // for, while
    pub nesting_penalties: usize, // nested structures
    pub logical_operators: usize, // && ||
    pub recursion: usize,
    pub early_returns: usize,   // break, continue, return from nested
    pub exception_handling: usize,
}

#[derive(Debug, Clone)]
pub struct ComplexityContribution {
    pub line: usize,
    pub score: usize,
    pub reason: String,
    pub nesting_level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComplexityRating {
    Simple,      // 0-5
    Moderate,    // 6-10
    Complex,     // 11-20
    VeryComplex, // 21+
}

/// Cognitive complexity calculator.
pub struct CognitiveComplexityCalculator<'a> {
    cfg: &'a CFGInfo,
    source: &'a [u8],
}

impl<'a> CognitiveComplexityCalculator<'a> {
    /// Calculate cognitive complexity.
    ///
    /// Rules (Sonar model):
    /// 1. +1 for each break in linear flow (if, for, while, switch, catch)
    /// 2. +1 for each nesting level when inside nested structures
    /// 3. +1 for each logical operator sequence (a && b && c = +2)
    /// 4. +1 for recursion
    /// 5. +1 for each break/continue/early return
    pub fn calculate(&self) -> CognitiveComplexityResult {
        todo!()
    }
}
```

### 5.2 Halstead Metrics

**Design**:

```rust
// src/metrics/halstead.rs

/// Halstead complexity metrics.
#[derive(Debug, Clone)]
pub struct HalsteadMetrics {
    /// Number of distinct operators
    pub n1: usize,
    /// Number of distinct operands
    pub n2: usize,
    /// Total number of operators
    pub N1: usize,
    /// Total number of operands
    pub N2: usize,
    /// Program vocabulary: n = n1 + n2
    pub vocabulary: usize,
    /// Program length: N = N1 + N2
    pub length: usize,
    /// Calculated length: N^ = n1 * log2(n1) + n2 * log2(n2)
    pub calculated_length: f64,
    /// Volume: V = N * log2(n)
    pub volume: f64,
    /// Difficulty: D = (n1 / 2) * (N2 / n2)
    pub difficulty: f64,
    /// Effort: E = D * V
    pub effort: f64,
    /// Time to program: T = E / 18 seconds
    pub time: f64,
    /// Estimated bugs: B = V / 3000
    pub bugs: f64,
}

/// Halstead metrics calculator.
pub struct HalsteadCalculator<'a> {
    source: &'a [u8],
    language: &'a str,
}

impl<'a> HalsteadCalculator<'a> {
    /// Calculate Halstead metrics.
    ///
    /// Operators include: +, -, *, /, =, ==, !=, <, >, etc.
    /// Operands include: identifiers, literals, constants
    pub fn calculate(&self) -> HalsteadMetrics {
        todo!()
    }
}
```

### 5.3 Maintainability Index

**Design**:

```rust
// src/metrics/maintainability.rs

/// Maintainability index result.
#[derive(Debug, Clone)]
pub struct MaintainabilityIndex {
    /// Original MI (0-171 scale, higher is better)
    pub mi: f64,
    /// Normalized MI (0-100 scale)
    pub mi_normalized: f64,
    /// Component metrics
    pub halstead_volume: f64,
    pub cyclomatic_complexity: usize,
    pub lines_of_code: usize,
    pub percent_comments: f64,
    /// Rating
    pub rating: MaintainabilityRating,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MaintainabilityRating {
    HighlyMaintainable, // MI >= 85 or normalized >= 20
    ModeratelyMaintainable, // MI 65-84 or normalized 10-19
    DifficultToMaintain, // MI < 65 or normalized < 10
}

impl MaintainabilityIndex {
    /// Calculate maintainability index.
    ///
    /// Formula (Microsoft variant):
    /// MI = max(0, (171 - 5.2 * ln(V) - 0.23 * CC - 16.2 * ln(LOC)) * 100 / 171)
    ///
    /// Where:
    /// - V = Halstead Volume
    /// - CC = Cyclomatic Complexity
    /// - LOC = Lines of Code
    pub fn calculate(
        halstead: &HalsteadMetrics,
        cyclomatic: usize,
        loc: usize,
        comment_lines: usize,
    ) -> Self {
        let v = halstead.volume.max(1.0);
        let cc = cyclomatic as f64;
        let loc_f = loc.max(1) as f64;

        let mi = 171.0 - 5.2 * v.ln() - 0.23 * cc - 16.2 * loc_f.ln();
        let mi = mi.max(0.0);

        // Normalized to 0-100
        let mi_normalized = mi * 100.0 / 171.0;

        let percent_comments = if loc > 0 {
            comment_lines as f64 / loc as f64 * 100.0
        } else {
            0.0
        };

        let rating = if mi_normalized >= 20.0 {
            MaintainabilityRating::HighlyMaintainable
        } else if mi_normalized >= 10.0 {
            MaintainabilityRating::ModeratelyMaintainable
        } else {
            MaintainabilityRating::DifficultToMaintain
        };

        Self {
            mi,
            mi_normalized,
            halstead_volume: halstead.volume,
            cyclomatic_complexity: cyclomatic,
            lines_of_code: loc,
            percent_comments,
            rating,
        }
    }
}
```

### 5.4 Coupling and Cohesion Metrics

**Design**:

```rust
// src/metrics/coupling.rs

/// Coupling metrics for a module/file.
#[derive(Debug, Clone)]
pub struct CouplingMetrics {
    /// Afferent coupling (incoming dependencies)
    pub ca: usize,
    /// Efferent coupling (outgoing dependencies)
    pub ce: usize,
    /// Instability: I = Ce / (Ca + Ce)
    pub instability: f64,
    /// Abstractness: A = abstract_types / total_types
    pub abstractness: f64,
    /// Distance from main sequence: D = |A + I - 1|
    pub distance: f64,
    /// Specific dependencies
    pub incoming: Vec<String>,
    pub outgoing: Vec<String>,
}

/// Cohesion metrics for a class.
#[derive(Debug, Clone)]
pub struct CohesionMetrics {
    /// Lack of Cohesion of Methods (LCOM)
    pub lcom: usize,
    /// LCOM normalized (0-1, lower is better)
    pub lcom_normalized: f64,
    /// Methods that share instance variables
    pub method_connectivity: f64,
    /// Rating
    pub rating: CohesionRating,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CohesionRating {
    HighCohesion,    // LCOM = 0
    ModerateCohesion, // LCOM 1-5
    LowCohesion,     // LCOM > 5
}

impl CohesionMetrics {
    /// Calculate LCOM (Lack of Cohesion of Methods).
    ///
    /// LCOM = number of method pairs that don't share instance variables
    ///      - number of method pairs that do share instance variables
    ///
    /// Lower is better (0 = perfect cohesion)
    pub fn calculate(
        methods: &[String],
        instance_vars_used: &HashMap<String, HashSet<String>>,
    ) -> Self {
        let mut share = 0;
        let mut no_share = 0;

        for i in 0..methods.len() {
            for j in (i + 1)..methods.len() {
                let vars_i = instance_vars_used.get(&methods[i]);
                let vars_j = instance_vars_used.get(&methods[j]);

                match (vars_i, vars_j) {
                    (Some(vi), Some(vj)) if !vi.is_disjoint(vj) => share += 1,
                    _ => no_share += 1,
                }
            }
        }

        let lcom = no_share.saturating_sub(share);
        let total_pairs = methods.len() * (methods.len().saturating_sub(1)) / 2;
        let lcom_normalized = if total_pairs > 0 {
            lcom as f64 / total_pairs as f64
        } else {
            0.0
        };

        let method_connectivity = if total_pairs > 0 {
            share as f64 / total_pairs as f64
        } else {
            1.0
        };

        let rating = match lcom {
            0 => CohesionRating::HighCohesion,
            1..=5 => CohesionRating::ModerateCohesion,
            _ => CohesionRating::LowCohesion,
        };

        Self {
            lcom,
            lcom_normalized,
            method_connectivity,
            rating,
        }
    }
}
```

---

## 6. Pattern Detection

### 6.1 Design Pattern Recognition

**Design**:

```rust
// src/patterns/design_patterns.rs

/// A detected design pattern.
#[derive(Debug, Clone)]
pub struct PatternMatch {
    pub pattern: DesignPattern,
    /// Classes/functions involved
    pub participants: Vec<PatternParticipant>,
    /// Confidence (0.0 - 1.0)
    pub confidence: f64,
    /// Notes about the match
    pub notes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DesignPattern {
    // Creational
    Singleton,
    Factory,
    AbstractFactory,
    Builder,
    Prototype,
    // Structural
    Adapter,
    Bridge,
    Composite,
    Decorator,
    Facade,
    Flyweight,
    Proxy,
    // Behavioral
    ChainOfResponsibility,
    Command,
    Iterator,
    Mediator,
    Memento,
    Observer,
    State,
    Strategy,
    TemplateMethod,
    Visitor,
}

#[derive(Debug, Clone)]
pub struct PatternParticipant {
    pub role: String,
    pub name: String,
    pub file: String,
    pub line: usize,
}

/// Pattern detector.
pub struct PatternDetector<'a> {
    call_graph: &'a CallGraph,
    function_index: &'a FunctionIndex,
    class_info: &'a HashMap<String, ClassInfo>,
}

impl<'a> PatternDetector<'a> {
    /// Detect design patterns in the codebase.
    pub fn detect(&self) -> Vec<PatternMatch> {
        let mut matches = Vec::new();

        matches.extend(self.detect_singleton());
        matches.extend(self.detect_factory());
        matches.extend(self.detect_observer());
        matches.extend(self.detect_strategy());
        matches.extend(self.detect_decorator());
        // ... more patterns

        matches
    }

    /// Detect Singleton pattern.
    ///
    /// Indicators:
    /// - Private/protected constructor
    /// - Static instance field
    /// - Static getInstance() method
    fn detect_singleton(&self) -> Vec<PatternMatch> {
        todo!()
    }

    /// Detect Factory pattern.
    ///
    /// Indicators:
    /// - Method returns interface/base class
    /// - Method creates subclass instances based on input
    fn detect_factory(&self) -> Vec<PatternMatch> {
        todo!()
    }
}
```

### 6.2 Anti-Pattern Detection

**Design**:

```rust
// src/patterns/anti_patterns.rs

/// A detected anti-pattern or code smell.
#[derive(Debug, Clone)]
pub struct AntiPatternFinding {
    pub pattern: AntiPattern,
    pub location: Location,
    pub severity: Severity,
    pub description: String,
    pub suggestion: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AntiPattern {
    // Object-Oriented Anti-Patterns
    GodClass,
    GodMethod,
    FeatureEnvy,
    DataClass,
    RefusedBequest,
    InappropriateIntimacy,
    MessageChain,
    MiddleMan,

    // Code Smells
    LongMethod,
    LongParameterList,
    DuplicatedCode,
    DeadCode,
    SpeculativeGenerality,
    SwitchStatements,
    ParallelInheritance,

    // Architectural Anti-Patterns
    CircularDependency,
    LayerViolation,
    SpaghettCode,

    // Concurrency Anti-Patterns
    DoubleCheckedLocking,
    RaceCondition,
    Deadlock,

    // Error Handling Anti-Patterns
    ExceptionSwallowing,
    EmptyCatch,
    GenericException,

    // Custom
    Custom(String),
}

/// Anti-pattern detector configuration.
#[derive(Debug, Clone)]
pub struct AntiPatternConfig {
    /// Lines threshold for long method
    pub long_method_lines: usize,
    /// Parameter count threshold
    pub long_param_count: usize,
    /// Methods threshold for god class
    pub god_class_methods: usize,
    /// Cyclomatic complexity threshold for god method
    pub god_method_complexity: usize,
}

impl Default for AntiPatternConfig {
    fn default() -> Self {
        Self {
            long_method_lines: 50,
            long_param_count: 5,
            god_class_methods: 20,
            god_method_complexity: 15,
        }
    }
}

/// Anti-pattern detector.
pub struct AntiPatternDetector<'a> {
    cfg_map: &'a HashMap<String, CFGInfo>,
    dfg_map: &'a HashMap<String, DFGInfo>,
    call_graph: &'a CallGraph,
    metrics: &'a HashMap<String, CognitiveComplexityResult>,
    config: AntiPatternConfig,
}

impl<'a> AntiPatternDetector<'a> {
    /// Detect all anti-patterns.
    pub fn detect(&self) -> Vec<AntiPatternFinding> {
        let mut findings = Vec::new();

        findings.extend(self.detect_god_class());
        findings.extend(self.detect_long_method());
        findings.extend(self.detect_feature_envy());
        findings.extend(self.detect_circular_deps());
        findings.extend(self.detect_exception_swallowing());

        findings
    }

    /// Detect God Class (class that does too much).
    ///
    /// Indicators:
    /// - Very high number of methods
    /// - Very high number of instance variables
    /// - Low cohesion (LCOM)
    /// - High coupling to other classes
    fn detect_god_class(&self) -> Vec<AntiPatternFinding> {
        todo!()
    }

    /// Detect Feature Envy (method uses more from another class).
    ///
    /// Method calls more methods on other objects than on self.
    fn detect_feature_envy(&self) -> Vec<AntiPatternFinding> {
        todo!()
    }
}
```

### 6.3 Semantic Code Duplication Detection

**Design**:

```rust
// src/patterns/duplication.rs

/// A detected code clone.
#[derive(Debug, Clone)]
pub struct CodeClone {
    pub clone_type: CloneType,
    /// First instance
    pub instance1: CloneInstance,
    /// Second instance
    pub instance2: CloneInstance,
    /// Similarity score (0.0 - 1.0)
    pub similarity: f64,
    /// Suggested abstraction
    pub abstraction_hint: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloneType {
    /// Exact copy (Type I)
    ExactCopy,
    /// Renamed identifiers (Type II)
    RenamedCopy,
    /// Modified statements (Type III)
    ModifiedCopy,
    /// Semantically equivalent (Type IV)
    SemanticClone,
}

#[derive(Debug, Clone)]
pub struct CloneInstance {
    pub file: String,
    pub start_line: usize,
    pub end_line: usize,
    pub function: Option<String>,
}

/// Code duplication detector.
pub struct DuplicationDetector<'a> {
    /// Parsed ASTs for comparison
    asts: &'a HashMap<String, tree_sitter::Tree>,
    source_map: &'a HashMap<String, Vec<u8>>,
    /// Minimum lines to consider as duplicate
    min_lines: usize,
    /// Similarity threshold
    similarity_threshold: f64,
}

impl<'a> DuplicationDetector<'a> {
    /// Detect code clones.
    ///
    /// Algorithm:
    /// 1. Extract normalized AST subtrees for each function
    /// 2. Hash subtrees for quick comparison (suffix tree approach)
    /// 3. Compare similar-hash subtrees for actual similarity
    /// 4. Classify clone type based on differences
    pub fn detect(&self) -> Vec<CodeClone> {
        todo!()
    }

    /// Compute AST similarity using tree edit distance.
    fn ast_similarity(&self, tree1: &tree_sitter::Tree, tree2: &tree_sitter::Tree) -> f64 {
        todo!()
    }

    /// Normalize AST for semantic comparison.
    /// - Rename all identifiers to canonical forms
    /// - Remove comments
    /// - Normalize whitespace
    fn normalize_ast(&self, tree: &tree_sitter::Tree, source: &[u8]) -> NormalizedAst {
        todo!()
    }
}

#[derive(Debug)]
struct NormalizedAst {
    /// Hash for quick comparison
    hash: u64,
    /// Normalized node kinds and structure
    nodes: Vec<(String, usize)>, // (kind, depth)
}
```

---

## 7. Performance Considerations

### 7.1 Caching Strategy

All analyzers should use lazy caching similar to the existing DFG adjacency cache:

```rust
/// Analysis cache using interior mutability.
pub struct AnalysisCache {
    taint: OnceLock<TaintAnalysisResult>,
    constant_prop: OnceLock<ConstantPropResult>,
    live_vars: OnceLock<LiveVarsResult>,
    reaching_defs: OnceLock<ReachingDefsResult>,
    type_flow: OnceLock<TypeFlowResult>,
}
```

### 7.2 Incremental Analysis

For IDE integration, support incremental updates:

```rust
/// Incremental analysis support.
pub trait IncrementalAnalysis {
    /// Update analysis after a local change.
    fn update(&mut self, changed_lines: &[usize], new_source: &[u8]);

    /// Check if full reanalysis is needed.
    fn requires_full_reanalysis(&self, change_scope: ChangeScope) -> bool;
}

pub enum ChangeScope {
    /// Single statement changed
    Statement(usize),
    /// Function body changed
    FunctionBody(String),
    /// Function signature changed
    FunctionSignature(String),
    /// Class structure changed
    ClassStructure(String),
    /// File added/removed
    FileChange,
}
```

### 7.3 Parallel Analysis

Use rayon for parallel analysis of independent modules:

```rust
/// Parallel analyzer for project-wide analysis.
pub struct ParallelAnalyzer<'a> {
    files: &'a [PathBuf],
    language: &'a str,
}

impl<'a> ParallelAnalyzer<'a> {
    /// Run analysis in parallel.
    pub fn analyze_all(&self) -> HashMap<PathBuf, AnalysisResult> {
        use rayon::prelude::*;

        self.files
            .par_iter()
            .filter_map(|path| {
                let result = self.analyze_file(path).ok()?;
                Some((path.clone(), result))
            })
            .collect()
    }
}
```

---

## 8. Integration with Existing Code

### 8.1 Language Trait Extension

Extend the Language trait with new analysis methods:

```rust
pub trait LanguageExtended: Language {
    /// Build exception flow graph.
    fn build_exception_flow(&self, cfg: &CFGInfo, source: &[u8]) -> ExceptionFlowInfo {
        // Default implementation
        ExceptionFlowInfo::default()
    }

    /// Get taint configuration for this language.
    fn taint_config(&self) -> TaintConfig {
        TaintConfig::default()
    }

    /// Get secret patterns for this language.
    fn secret_patterns(&self) -> Vec<SecretPattern> {
        Vec::new()
    }
}
```

### 8.2 CLI Integration

New commands for the CLI:

```
tldr security <path>           # Run security analysis
tldr taint <file> <function>   # Taint analysis for function
tldr complexity <file>         # Complexity metrics
tldr patterns <path>           # Design pattern detection
tldr smells <path>             # Anti-pattern detection
tldr types <file> <function>   # Type flow analysis
```

### 8.3 Output Format

JSON output for all analyses:

```rust
#[derive(Serialize)]
pub struct AnalysisReport {
    pub file: String,
    pub timestamp: String,
    pub security: Option<SecurityReport>,
    pub complexity: Option<ComplexityReport>,
    pub patterns: Option<PatternReport>,
    pub smells: Option<SmellReport>,
}
```

---

## 9. Implementation Priority

### Phase 1: Security (High Value, Medium Effort)
1. Taint Analysis
2. SQL Injection Detection
3. Command Injection Detection
4. Secret Detection

### Phase 2: Data Flow (Foundation for Others)
1. Constant Propagation
2. Reaching Definitions
3. Live Variable Analysis

### Phase 3: Complexity Metrics (Quick Wins)
1. Cognitive Complexity
2. Maintainability Index
3. Coupling/Cohesion

### Phase 4: Advanced Flow (High Effort)
1. Exception Flow Tracking
2. Async/Await Modeling
3. Type Flow Analysis

### Phase 5: Pattern Detection (Lower Priority)
1. Anti-Pattern Detection
2. Design Pattern Recognition
3. Semantic Duplication

---

## 10. Testing Strategy

### Unit Tests
- Each analyzer has isolated tests with synthetic code snippets
- Edge cases for each language construct

### Integration Tests
- Real-world code samples from open source projects
- Cross-language consistency tests

### Regression Tests
- Known vulnerability patterns (OWASP examples)
- False positive reduction tests

### Performance Tests
- Benchmark on large codebases (Linux kernel, CPython)
- Memory usage profiling

---

## Appendix A: File Structure

```
src/
  dataflow/
    mod.rs
    taint.rs
    constant_prop.rs
    reaching_defs.rs
    live_vars.rs
    alias.rs
  security/
    mod.rs
    sql_injection.rs
    xss.rs
    command_injection.rs
    path_traversal.rs
    secrets.rs
  typeflow/
    mod.rs
    inference.rs
    narrowing.rs
  metrics/
    mod.rs
    cognitive.rs
    halstead.rs
    maintainability.rs
    coupling.rs
  patterns/
    mod.rs
    design_patterns.rs
    anti_patterns.rs
    duplication.rs
  cfg/
    exception_flow.rs
    async_flow.rs
    generator_flow.rs
    loop_analysis.rs
    dead_branch.rs
```

---

## Appendix B: References

1. Sonar Cognitive Complexity - https://www.sonarsource.com/docs/CognitiveComplexity.pdf
2. Halstead Metrics - https://en.wikipedia.org/wiki/Halstead_complexity_measures
3. Andersen's Analysis - https://cs.au.dk/~amoeller/spa/
4. OWASP Code Review - https://owasp.org/www-project-code-review-guide/
5. Design Patterns (GoF) - Gamma et al.
6. Refactoring (Fowler) - Code Smells catalogue
