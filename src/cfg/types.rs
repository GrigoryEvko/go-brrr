//! CFG type definitions.

use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

/// Cached adjacency lists for O(1) successor/predecessor lookups.
///
/// Built lazily on first access to avoid overhead when not needed.
/// Uses separate HashMaps for outgoing (successors) and incoming (predecessors) edges.
/// NOTE: This type is public for `CFGInfo.adjacency_cache` but is an internal implementation detail.
#[derive(Debug)]
pub struct AdjacencyCache {
    /// BlockId -> list of successor BlockIds (outgoing edges)
    successors: HashMap<BlockId, Vec<BlockId>>,
    /// BlockId -> list of predecessor BlockIds (incoming edges)
    predecessors: HashMap<BlockId, Vec<BlockId>>,
}

/// Errors that can occur during CFG validation.
///
/// These errors indicate structural inconsistencies in the control flow graph
/// that would cause issues during analysis or rendering.
#[derive(Debug, thiserror::Error)]
#[allow(dead_code)]
pub enum CFGError {
    /// Entry block ID does not exist in the blocks map.
    #[error("Entry block {0:?} not found in blocks")]
    InvalidEntry(BlockId),

    /// An exit block ID does not exist in the blocks map.
    #[error("Exit block {0:?} not found in blocks")]
    InvalidExit(BlockId),

    /// Duplicate block ID was inserted (would silently overwrite).
    #[error("Duplicate block ID {0:?}")]
    DuplicateBlockId(BlockId),

    /// An edge references a block that does not exist.
    #[error("Edge references non-existent block {0:?}")]
    InvalidEdgeBlock(BlockId),
}

/// Unique identifier for a basic block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BlockId(pub usize);

/// Type of a basic block in the control flow graph.
///
/// Categorizes blocks by their role in the control flow:
/// - Entry/Exit: Function boundaries
/// - Branch: Conditional decision points
/// - LoopHeader/LoopBody: Loop constructs
/// - Return: Explicit return statements
/// - Body: Regular sequential code
/// - Exception/Finally: Error handling constructs
/// - TryOperator/ErrorReturn/PanicSite: Rust Result/Option handling
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum BlockType {
    /// Function entry point
    Entry,
    /// Function exit point
    Exit,
    /// Conditional branch (if, elif, match case)
    Branch,
    /// Loop header (condition evaluation)
    LoopHeader,
    /// Loop body
    LoopBody,
    /// Return statement block
    Return,
    /// Regular code block (default)
    #[default]
    Body,
    /// Exception handler (except, catch)
    Exception,
    /// Finally block
    Finally,
    /// Rust ? operator - may propagate error/none (Result/Option)
    TryOperator,
    /// Rust early return from ? operator on Err/None
    ErrorReturn,
    /// Potential panic site (.unwrap(), .expect(), panic!(), unreachable!(), todo!())
    PanicSite,
    /// Pattern match block (if let, while let, match arm)
    PatternMatch,
    /// Closure body (separate control flow context)
    Closure,
    // =========================================================================
    // Go-specific block types for defer/panic/recover flow
    // =========================================================================
    /// Go: Deferred function call (executes on function exit in LIFO order)
    DeferredCall,
    /// Go: Recover call site (recover() in deferred function)
    RecoverCall,
    /// Go: Error check pattern (if err != nil { return err })
    ErrorCheck,
    /// Go: Panic site (explicit panic() or potential runtime panic)
    GoPanicSite,
    // =========================================================================
    // Go-specific block types for concurrency (goroutines, channels, sync)
    // =========================================================================
    /// Go: Goroutine spawn (go func() {...} or go existingFunc())
    GoroutineSpawn,
    /// Go: Channel send operation (ch <- value) - may block
    ChannelSend,
    /// Go: Channel receive operation (val := <-ch or <-ch) - may block
    ChannelReceive,
    /// Go: Select statement block (multi-way channel operation)
    SelectBlock,
    /// Go: Select case (case <-ch: or case ch <-:)
    SelectCase,
    /// Go: Mutex lock operation (mu.Lock() or mu.RLock())
    MutexLock,
    /// Go: Mutex unlock operation (mu.Unlock() or mu.RUnlock())
    MutexUnlock,
    /// Go: WaitGroup wait operation (wg.Wait()) - synchronization point
    WaitGroupWait,
    /// Go: WaitGroup add/done operation (wg.Add(), wg.Done())
    WaitGroupOp,
    /// Go: sync.Once.Do() call - one-time initialization
    OnceCall,
    /// Go: Channel make/creation (make(chan T) or make(chan T, size))
    ChannelMake,
    /// Go: Channel close operation (close(ch))
    ChannelClose,
    /// Go: Context cancellation check (ctx.Done(), ctx.Err())
    ContextCheck,
    // =========================================================================
    // Python async/await block types
    // =========================================================================
    /// Python: Await expression - suspension point where execution yields to event loop
    AwaitPoint,
    /// Python: Async for loop header
    AsyncForLoop,
    /// Python: Async with block (async context manager)
    AsyncWithBlock,
    /// Python: Task spawn point (asyncio.create_task, asyncio.gather, etc.)
    TaskSpawn,
    // =========================================================================
    // JavaScript/TypeScript async/await and Promise block types
    // =========================================================================
    /// JS/TS: Promise.then() callback block - executes on promise resolution
    PromiseThen,
    /// JS/TS: Promise.catch() callback block - executes on promise rejection
    PromiseCatch,
    /// JS/TS: Promise.finally() callback block - executes regardless of outcome
    PromiseFinally,
    /// JS/TS: Promise.all() - parallel execution, waits for all promises
    PromiseAll,
    /// JS/TS: Promise.race() - parallel execution, resolves with first settled
    PromiseRace,
    /// JS/TS: Promise.allSettled() - parallel execution, waits for all to settle
    PromiseAllSettled,
    /// JS/TS: Promise.any() - parallel execution, resolves with first fulfilled
    PromiseAny,
    /// JS/TS: Async generator yield point (yield* in async generator)
    AsyncGeneratorYield,
    /// JS/TS: for await...of loop header (async iteration)
    ForAwaitOf,
    // =========================================================================
    // Rust async/await block types
    // =========================================================================
    /// Rust: Await expression (.await) - suspension point where Future yields
    /// Critical for tracking async state machine transitions and cancellation safety.
    RustAwaitPoint,
    /// Rust: Task spawn point (tokio::spawn, async_std::spawn, etc.)
    /// Creates a concurrent task that runs independently.
    RustTaskSpawn,
    /// Rust: tokio::join! - concurrent execution, waits for all futures
    /// All branches run concurrently, function continues when all complete.
    RustJoin,
    /// Rust: tokio::select! - concurrent execution, first completion wins
    /// All branches race, first to complete is taken, others are cancelled.
    RustSelect,
    /// Rust: select! branch (individual arm in select!)
    RustSelectBranch,
    /// Rust: Blocking call in async context (std::thread::sleep, blocking I/O)
    /// ANTI-PATTERN: Blocks the executor thread, starving other tasks.
    RustBlockingCall,
    /// Rust: Lock held across await (MutexGuard, RwLockGuard across .await)
    /// ANTI-PATTERN: Causes deadlocks and breaks Send bounds.
    RustLockAcrossAwait,
    /// Rust: Async block (async { ... }) - creates anonymous Future
    RustAsyncBlock,
}

/// A basic block in the control flow graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CFGBlock {
    /// Unique block identifier
    pub id: BlockId,
    /// Human-readable label
    pub label: String,
    /// Type of block (entry, exit, branch, loop, etc.)
    #[serde(default)]
    pub block_type: BlockType,
    /// Statements in this block
    pub statements: Vec<String>,
    /// Functions called within this block
    #[serde(default)]
    pub func_calls: Vec<String>,
    /// Starting line number
    pub start_line: usize,
    /// Ending line number
    pub end_line: usize,
}

/// Semantic type of a CFG edge.
///
/// This enum represents the control flow semantics, while `condition`
/// provides human-readable display text (e.g., "x > 0").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EdgeType {
    /// Unconditional edge (fallthrough, sequential)
    Unconditional,
    /// True branch of a conditional
    True,
    /// False branch of a conditional
    False,
    /// Back edge in a loop
    BackEdge,
    /// Break statement exiting a loop
    Break,
    /// Continue statement restarting loop iteration
    Continue,
    /// Exception handling path
    Exception,
    /// Finally block execution
    Finally,
    /// Loop iteration edge
    Iterate,
    /// Return from function
    Return,
    /// Loop entry edge
    Enter,
    /// Loop exit edge (done/exit)
    Exit,
    /// Switch/match case
    Case,
    /// Pattern match in match statement
    PatternMatch,
    /// Goto statement (C/C++)
    Goto,
    /// Goroutine spawn (Go)
    Spawn,
    /// Deferred execution (Go)
    Defer,
    /// Channel send (Go)
    Send,
    /// Resource acquire (Java try-with-resources)
    Acquire,
    /// Successful completion
    Success,
    /// Resource close (Java try-with-resources)
    Close,
    /// Else branch
    Else,
    /// Result/Option Ok/Some variant (Rust)
    OkSome,
    /// Result/Option Err/None variant (Rust)
    ErrNone,
    /// Loop next iteration
    Next,
    /// Match expression dispatch
    Match,
    /// Loop continuation (back to condition)
    Loop,
    /// Assert pass (condition true)
    Pass,
    /// Assert fail (condition false, raises AssertionError)
    Fail,
    /// Loop exhausted (iteration complete)
    Exhausted,
    /// No exception occurred (try/else)
    NoException,
    /// Exception group handling (except*)
    ExceptionGroup,
    /// Context manager enter success
    EnterSuccess,
    /// Context manager enter exception
    EnterException,
    /// Cleanup path
    Cleanup,
    /// Exception propagation
    Propagate,
    /// Re-raise current exception (bare `raise` statement)
    Reraise,
    /// Typed exception edge (edge to specific exception handler)
    TypedException,
    // =========================================================================
    // Go-specific edge types for defer/panic/recover flow
    // =========================================================================
    /// Go: Panic propagation (control flow on panic)
    Panic,
    /// Go: Recover success (panic caught by recover())
    Recover,
    /// Go: Deferred execution chain (between deferred calls)
    DeferChain,
    /// Go: Error return path (err != nil -> return)
    ErrorPath,
    /// Go: Success path (err == nil -> continue)
    SuccessPath,
    // =========================================================================
    // Go-specific edge types for concurrency (goroutines, channels, sync)
    // =========================================================================
    /// Go: Channel receive operation edge
    Receive,
    /// Go: Select case branch (case <-ch: or case ch <- val:)
    SelectCase,
    /// Go: Select default branch (non-blocking)
    SelectDefault,
    /// Go: Mutex lock acquisition
    Lock,
    /// Go: Mutex unlock release
    Unlock,
    /// Go: WaitGroup synchronization
    WaitSync,
    /// Go: Channel close operation
    ChannelClose,
    /// Go: Context cancellation path (ctx.Done() triggered)
    ContextCancel,
    /// Go: Context continue path (ctx not cancelled)
    ContextContinue,
    // =========================================================================
    // Python async/await edge types
    // =========================================================================
    /// Python: Await suspension point - execution yields to event loop
    Await,
    /// Python: Async for iteration (like Iterate but async)
    AsyncIterate,
    /// Python: Async for exhausted (like Exhausted but async)
    AsyncExhausted,
    /// Python: Async with enter success
    AsyncEnterSuccess,
    /// Python: Async with enter exception
    AsyncEnterException,
    /// Python: Task spawn (concurrent execution begins)
    TaskSpawn,
    /// Python: Task join (await on task result)
    TaskJoin,
    // =========================================================================
    // JavaScript/TypeScript async/await and Promise edge types
    // =========================================================================
    /// JS/TS: Promise resolved - .then() callback path
    PromiseResolved,
    /// JS/TS: Promise rejected - .catch() callback path
    PromiseRejected,
    /// JS/TS: Promise settled - .finally() callback path (always executes)
    PromiseSettled,
    /// JS/TS: Promise.all parallel branch - edge to each task
    PromiseAllBranch,
    /// JS/TS: Promise.all join - all tasks completed
    PromiseAllJoin,
    /// JS/TS: Promise.race branch - edge to each racing task
    PromiseRaceBranch,
    /// JS/TS: Promise.race winner - first settled wins
    PromiseRaceWinner,
    /// JS/TS: for await...of iteration edge
    ForAwaitIterate,
    /// JS/TS: for await...of exhausted edge
    ForAwaitExhausted,
    /// JS/TS: Async generator yield edge
    AsyncYield,
    /// JS/TS: Async generator resume edge (after yield)
    AsyncResume,
    // =========================================================================
    // Rust async/await edge types
    // =========================================================================
    /// Rust: .await suspension point - Future yields to executor
    RustAwait,
    /// Rust: .await resumption - Future resumes after poll returns Ready
    RustResume,
    /// Rust: tokio::spawn - new task spawned (concurrent execution)
    RustSpawn,
    /// Rust: JoinHandle.await - waiting for spawned task result
    RustJoinTask,
    /// Rust: join! branch - edge to each concurrent future
    RustJoinBranch,
    /// Rust: join! complete - all futures completed
    RustJoinComplete,
    /// Rust: select! branch - edge to each racing future
    RustSelectBranch,
    /// Rust: select! winner - first future to complete
    RustSelectWinner,
    /// Rust: select! cancelled - future cancelled (not selected)
    RustSelectCancelled,
    /// Rust: Blocking operation in async context (anti-pattern)
    RustBlocking,
    /// Rust: Lock acquisition in async context (potential issue)
    RustLockAcquire,
    /// Rust: Await while holding lock (anti-pattern)
    RustAwaitWithLock,
}

impl EdgeType {
    /// Get the default display label for this edge type.
    pub fn default_label(&self) -> &'static str {
        match self {
            EdgeType::Unconditional => "",
            EdgeType::True => "true",
            EdgeType::False => "false",
            EdgeType::BackEdge => "back_edge",
            EdgeType::Break => "break",
            EdgeType::Continue => "continue",
            EdgeType::Exception => "exception",
            EdgeType::Finally => "finally",
            EdgeType::Iterate => "iterate",
            EdgeType::Return => "return",
            EdgeType::Enter => "enter",
            EdgeType::Exit => "exit",
            EdgeType::Case => "case",
            EdgeType::PatternMatch => "pattern_match",
            EdgeType::Goto => "goto",
            EdgeType::Spawn => "spawn",
            EdgeType::Defer => "defer",
            EdgeType::Send => "send",
            EdgeType::Acquire => "acquire",
            EdgeType::Success => "success",
            EdgeType::Close => "close",
            EdgeType::Else => "else",
            EdgeType::OkSome => "Ok/Some",
            EdgeType::ErrNone => "Err/None",
            EdgeType::Next => "next",
            EdgeType::Match => "match",
            EdgeType::Loop => "loop",
            EdgeType::Pass => "pass",
            EdgeType::Fail => "fail",
            EdgeType::Exhausted => "exhausted",
            EdgeType::NoException => "no_exception",
            EdgeType::ExceptionGroup => "exception_group",
            EdgeType::EnterSuccess => "enter_success",
            EdgeType::EnterException => "enter_exception",
            EdgeType::Cleanup => "cleanup",
            EdgeType::Propagate => "propagate",
            EdgeType::Reraise => "reraise",
            EdgeType::TypedException => "typed_exception",
            // Go-specific edge labels
            EdgeType::Panic => "panic",
            EdgeType::Recover => "recover",
            EdgeType::DeferChain => "defer_chain",
            EdgeType::ErrorPath => "err != nil",
            EdgeType::SuccessPath => "err == nil",
            // Go concurrency edge labels
            EdgeType::Receive => "receive",
            EdgeType::SelectCase => "select_case",
            EdgeType::SelectDefault => "select_default",
            EdgeType::Lock => "lock",
            EdgeType::Unlock => "unlock",
            EdgeType::WaitSync => "wait",
            EdgeType::ChannelClose => "close_chan",
            EdgeType::ContextCancel => "ctx_cancel",
            EdgeType::ContextContinue => "ctx_continue",
            // Python async/await edge labels
            EdgeType::Await => "await",
            EdgeType::AsyncIterate => "async_iterate",
            EdgeType::AsyncExhausted => "async_exhausted",
            EdgeType::AsyncEnterSuccess => "async_enter_success",
            EdgeType::AsyncEnterException => "async_enter_exception",
            EdgeType::TaskSpawn => "spawn_task",
            EdgeType::TaskJoin => "join_task",
            // JavaScript/TypeScript async/await edge labels
            EdgeType::PromiseResolved => "resolved",
            EdgeType::PromiseRejected => "rejected",
            EdgeType::PromiseSettled => "settled",
            EdgeType::PromiseAllBranch => "all_branch",
            EdgeType::PromiseAllJoin => "all_join",
            EdgeType::PromiseRaceBranch => "race_branch",
            EdgeType::PromiseRaceWinner => "race_winner",
            EdgeType::ForAwaitIterate => "for_await_iterate",
            EdgeType::ForAwaitExhausted => "for_await_exhausted",
            EdgeType::AsyncYield => "async_yield",
            EdgeType::AsyncResume => "async_resume",
            // Rust async/await edge labels
            EdgeType::RustAwait => ".await",
            EdgeType::RustResume => "resume",
            EdgeType::RustSpawn => "rust_spawn",
            EdgeType::RustJoinTask => "join_task",
            EdgeType::RustJoinBranch => "join_branch",
            EdgeType::RustJoinComplete => "join_complete",
            EdgeType::RustSelectBranch => "select_branch",
            EdgeType::RustSelectWinner => "select_winner",
            EdgeType::RustSelectCancelled => "select_cancel",
            EdgeType::RustBlocking => "blocking",
            EdgeType::RustLockAcquire => "lock_acquire",
            EdgeType::RustAwaitWithLock => "await_with_lock",
        }
    }
}

/// An edge in the control flow graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CFGEdge {
    /// Source block
    #[serde(rename = "source_id")]
    pub from: BlockId,
    /// Target block
    #[serde(rename = "target_id")]
    pub to: BlockId,
    /// Semantic edge type
    #[serde(rename = "type")]
    pub edge_type: EdgeType,
    /// Human-readable condition (e.g., "x > 0")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<String>,
}

impl CFGEdge {
    /// Create a new unconditional edge.
    pub fn unconditional(from: BlockId, to: BlockId) -> Self {
        Self {
            from,
            to,
            edge_type: EdgeType::Unconditional,
            condition: None,
        }
    }

    /// Create a new edge with a specific type.
    pub fn new(from: BlockId, to: BlockId, edge_type: EdgeType) -> Self {
        Self {
            from,
            to,
            edge_type,
            condition: None,
        }
    }

    /// Create a new edge with type and condition.
    pub fn with_condition(from: BlockId, to: BlockId, edge_type: EdgeType, condition: String) -> Self {
        Self {
            from,
            to,
            edge_type,
            condition: Some(condition),
        }
    }

    /// Create edge from legacy label format (backward compatibility).
    ///
    /// This method allows gradual migration from the old `label: Option<String>`
    /// format to the new `edge_type` + `condition` format.
    pub fn from_label(from: BlockId, to: BlockId, label: Option<String>) -> Self {
        match label.as_deref() {
            None => Self::unconditional(from, to),
            Some("true") => Self::new(from, to, EdgeType::True),
            Some("false") => Self::new(from, to, EdgeType::False),
            Some("break") => Self::new(from, to, EdgeType::Break),
            Some("continue") => Self::new(from, to, EdgeType::Continue),
            Some("exception") => Self::new(from, to, EdgeType::Exception),
            Some("finally") => Self::new(from, to, EdgeType::Finally),
            Some("iterate") => Self::new(from, to, EdgeType::Iterate),
            Some("return") => Self::new(from, to, EdgeType::Return),
            Some("enter") => Self::new(from, to, EdgeType::Enter),
            Some("exit") => Self::new(from, to, EdgeType::Exit),
            Some("case") => Self::new(from, to, EdgeType::Case),
            Some("pattern_match") => Self::new(from, to, EdgeType::PatternMatch),
            Some("spawn") => Self::new(from, to, EdgeType::Spawn),
            Some("defer") => Self::new(from, to, EdgeType::Defer),
            Some("send") => Self::new(from, to, EdgeType::Send),
            Some("acquire") => Self::new(from, to, EdgeType::Acquire),
            Some("success") => Self::new(from, to, EdgeType::Success),
            Some("close") => Self::new(from, to, EdgeType::Close),
            Some("else") => Self::new(from, to, EdgeType::Else),
            Some("Ok/Some") => Self::new(from, to, EdgeType::OkSome),
            Some("Err/None") => Self::new(from, to, EdgeType::ErrNone),
            Some("next") => Self::new(from, to, EdgeType::Next),
            Some("match") => Self::new(from, to, EdgeType::Match),
            Some("loop") => Self::new(from, to, EdgeType::Loop),
            Some("back_edge") => Self::new(from, to, EdgeType::BackEdge),
            Some("done") => Self::new(from, to, EdgeType::Exit),
            Some("reraise") => Self::new(from, to, EdgeType::Reraise),
            Some("typed_exception") => Self::new(from, to, EdgeType::TypedException),
            Some("propagate") => Self::new(from, to, EdgeType::Propagate),
            Some("cleanup") => Self::new(from, to, EdgeType::Cleanup),
            Some("no_exception") => Self::new(from, to, EdgeType::NoException),
            Some("enter_success") => Self::new(from, to, EdgeType::EnterSuccess),
            Some("enter_exception") => Self::new(from, to, EdgeType::EnterException),
            // Go-specific edge labels
            Some("panic") => Self::new(from, to, EdgeType::Panic),
            Some("recover") => Self::new(from, to, EdgeType::Recover),
            Some("defer_chain") => Self::new(from, to, EdgeType::DeferChain),
            Some("err != nil") => Self::new(from, to, EdgeType::ErrorPath),
            Some("err == nil") => Self::new(from, to, EdgeType::SuccessPath),
            // Go concurrency edge labels
            Some("receive") => Self::new(from, to, EdgeType::Receive),
            Some("select_case") => Self::new(from, to, EdgeType::SelectCase),
            Some("select_default") => Self::new(from, to, EdgeType::SelectDefault),
            Some("lock") => Self::new(from, to, EdgeType::Lock),
            Some("unlock") => Self::new(from, to, EdgeType::Unlock),
            Some("wait") => Self::new(from, to, EdgeType::WaitSync),
            Some("close_chan") => Self::new(from, to, EdgeType::ChannelClose),
            Some("ctx_cancel") => Self::new(from, to, EdgeType::ContextCancel),
            Some("ctx_continue") => Self::new(from, to, EdgeType::ContextContinue),
            // Python async/await edge labels
            Some("await") => Self::new(from, to, EdgeType::Await),
            Some("async_iterate") => Self::new(from, to, EdgeType::AsyncIterate),
            Some("async_exhausted") => Self::new(from, to, EdgeType::AsyncExhausted),
            Some("async_enter_success") => Self::new(from, to, EdgeType::AsyncEnterSuccess),
            Some("async_enter_exception") => Self::new(from, to, EdgeType::AsyncEnterException),
            Some("spawn_task") => Self::new(from, to, EdgeType::TaskSpawn),
            Some("join_task") => Self::new(from, to, EdgeType::TaskJoin),
            // JavaScript/TypeScript async/await edge labels
            Some("resolved") => Self::new(from, to, EdgeType::PromiseResolved),
            Some("rejected") => Self::new(from, to, EdgeType::PromiseRejected),
            Some("settled") => Self::new(from, to, EdgeType::PromiseSettled),
            Some("all_branch") => Self::new(from, to, EdgeType::PromiseAllBranch),
            Some("all_join") => Self::new(from, to, EdgeType::PromiseAllJoin),
            Some("race_branch") => Self::new(from, to, EdgeType::PromiseRaceBranch),
            Some("race_winner") => Self::new(from, to, EdgeType::PromiseRaceWinner),
            Some("for_await_iterate") => Self::new(from, to, EdgeType::ForAwaitIterate),
            Some("for_await_exhausted") => Self::new(from, to, EdgeType::ForAwaitExhausted),
            Some("async_yield") => Self::new(from, to, EdgeType::AsyncYield),
            Some("async_resume") => Self::new(from, to, EdgeType::AsyncResume),
            // Rust async/await edge labels
            Some(".await") => Self::new(from, to, EdgeType::RustAwait),
            Some("resume") => Self::new(from, to, EdgeType::RustResume),
            Some("rust_spawn") => Self::new(from, to, EdgeType::RustSpawn),
            Some("rust_join_task") => Self::new(from, to, EdgeType::RustJoinTask),
            Some("join_branch") => Self::new(from, to, EdgeType::RustJoinBranch),
            Some("join_complete") => Self::new(from, to, EdgeType::RustJoinComplete),
            Some("select_branch") => Self::new(from, to, EdgeType::RustSelectBranch),
            Some("select_winner") => Self::new(from, to, EdgeType::RustSelectWinner),
            Some("select_cancel") => Self::new(from, to, EdgeType::RustSelectCancelled),
            Some("blocking") => Self::new(from, to, EdgeType::RustBlocking),
            Some("lock_acquire") => Self::new(from, to, EdgeType::RustLockAcquire),
            Some("await_with_lock") => Self::new(from, to, EdgeType::RustAwaitWithLock),
            Some(s) if s.starts_with("goto ") => {
                Self::with_condition(from, to, EdgeType::Goto, s.to_string())
            }
            Some(other) => {
                // Unknown label: store as condition with Unconditional type
                Self::with_condition(from, to, EdgeType::Unconditional, other.to_string())
            }
        }
    }

    /// Get the display label for this edge.
    ///
    /// Returns the condition if present, otherwise the default label for the edge type.
    pub fn label(&self) -> String {
        self.condition.clone().unwrap_or_else(|| {
            self.edge_type.default_label().to_string()
        })
    }
}

/// Complete control flow graph for a function.
#[derive(Debug, Serialize, Deserialize)]
pub struct CFGInfo {
    /// Function name
    pub function_name: String,
    /// All blocks indexed by ID
    pub blocks: HashMap<BlockId, CFGBlock>,
    /// All edges
    pub edges: Vec<CFGEdge>,
    /// Entry block
    pub entry: BlockId,
    /// Exit blocks
    pub exits: Vec<BlockId>,
    /// Total decision points in the function.
    ///
    /// Tracks all control flow decisions:
    /// - if statements (+1)
    /// - elif clauses (+1 each)
    /// - while loops (+1)
    /// - for loops (+1)
    /// - except handlers (+1 each)
    /// - assert statements (+1)
    /// - match cases (+1 each)
    /// - match guards (+1 each)
    /// - comprehension if clauses (+1 each)
    ///
    /// Used for accurate cyclomatic complexity: decision_points + 1
    #[serde(default)]
    pub decision_points: usize,
    /// Extra decision points from comprehensions (if_clause, for_in_clause).
    /// These affect cyclomatic complexity but don't create separate CFG blocks
    /// since comprehensions are expressions with internal iteration/filtering.
    /// NOTE: Kept for backward compatibility, but now included in decision_points.
    #[serde(default)]
    pub comprehension_decision_points: usize,
    /// Nested function/closure CFGs (name -> CFG).
    ///
    /// Stores control flow graphs for inner functions and closures defined
    /// within this function. Maps the nested function name to its CFGInfo.
    /// This matches Python's `nested_cfgs: dict[str, CFGInfo]` field.
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub nested_cfgs: HashMap<String, Box<CFGInfo>>,
    // =========================================================================
    // Python async/await tracking
    // =========================================================================
    /// Whether this is an async function (async def in Python).
    /// Important for async flow analysis and detecting blocking calls.
    #[serde(default)]
    pub is_async: bool,
    /// Number of await suspension points in this function.
    /// Each await creates a point where execution yields to the event loop.
    /// Higher counts indicate more complex async interleaving potential.
    #[serde(default)]
    pub await_points: usize,
    /// Detected blocking calls in async context (e.g., time.sleep in async def).
    /// These are potential bugs that block the event loop.
    /// Format: Vec<(function_name, line_number)>
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blocking_calls: Vec<(String, usize)>,
    // =========================================================================
    // Performance optimization: Lazy adjacency list cache
    // =========================================================================
    /// Lazily-built adjacency cache for O(1) successor/predecessor lookups.
    ///
    /// Built on first call to `successors()` or `predecessors()`.
    /// Amortizes O(E) edge scan across all subsequent lookups.
    /// Skipped during serialization; rebuilt on demand after deserialization.
    /// NOTE: This field is public for struct literal construction but should
    /// be treated as internal. Use `OnceCell::new()` when constructing.
    #[serde(skip)]
    pub adjacency_cache: OnceCell<AdjacencyCache>,
}

impl Clone for CFGInfo {
    fn clone(&self) -> Self {
        Self {
            function_name: self.function_name.clone(),
            blocks: self.blocks.clone(),
            edges: self.edges.clone(),
            entry: self.entry,
            exits: self.exits.clone(),
            decision_points: self.decision_points,
            comprehension_decision_points: self.comprehension_decision_points,
            nested_cfgs: self.nested_cfgs.clone(),
            is_async: self.is_async,
            await_points: self.await_points,
            blocking_calls: self.blocking_calls.clone(),
            // Reset cache on clone - will be rebuilt lazily if needed
            adjacency_cache: OnceCell::new(),
        }
    }
}

impl Default for CFGInfo {
    fn default() -> Self {
        Self {
            function_name: String::new(),
            blocks: HashMap::new(),
            edges: Vec::new(),
            entry: BlockId(0),
            exits: Vec::new(),
            decision_points: 0,
            comprehension_decision_points: 0,
            nested_cfgs: HashMap::new(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            adjacency_cache: OnceCell::new(),
        }
    }
}

impl CFGInfo {
    /// Create a new CFGInfo with the essential fields.
    ///
    /// This constructor handles the internal adjacency cache initialization.
    /// Use this instead of struct literal syntax.
    ///
    /// # Arguments
    /// * `function_name` - Name of the function this CFG represents
    /// * `blocks` - Map of block IDs to blocks
    /// * `edges` - List of edges connecting blocks
    /// * `entry` - Entry block ID
    /// * `exits` - List of exit block IDs
    #[must_use]
    pub fn new(
        function_name: String,
        blocks: HashMap<BlockId, CFGBlock>,
        edges: Vec<CFGEdge>,
        entry: BlockId,
        exits: Vec<BlockId>,
    ) -> Self {
        Self {
            function_name,
            blocks,
            edges,
            entry,
            exits,
            decision_points: 0,
            comprehension_decision_points: 0,
            nested_cfgs: HashMap::new(),
            is_async: false,
            await_points: 0,
            blocking_calls: Vec::new(),
            adjacency_cache: OnceCell::new(),
        }
    }

    /// Create a CFGInfo with all fields specified.
    ///
    /// Use this when you need to set decision points, async info, etc.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn with_details(
        function_name: String,
        blocks: HashMap<BlockId, CFGBlock>,
        edges: Vec<CFGEdge>,
        entry: BlockId,
        exits: Vec<BlockId>,
        decision_points: usize,
        comprehension_decision_points: usize,
        is_async: bool,
        await_points: usize,
        blocking_calls: Vec<(String, usize)>,
    ) -> Self {
        Self {
            function_name,
            blocks,
            edges,
            entry,
            exits,
            decision_points,
            comprehension_decision_points,
            nested_cfgs: HashMap::new(),
            is_async,
            await_points,
            blocking_calls,
            adjacency_cache: OnceCell::new(),
        }
    }
}

impl CFGInfo {
    /// Calculate cyclomatic complexity using decision points.
    ///
    /// Uses the formula: M = decision_points + 1
    ///
    /// This matches Python's implementation and accurately counts:
    /// - if statements (+1)
    /// - elif clauses (+1 each)
    /// - while loops (+1)
    /// - for loops (+1)
    /// - except handlers (+1 each)
    /// - assert statements (+1)
    /// - match cases (+1 each)
    /// - match guards (+1 each)
    /// - comprehension if clauses (+1 each)
    ///
    /// Higher values indicate more complex control flow.
    /// General guidelines:
    /// - 1-10: Simple, low risk
    /// - 11-20: Moderate complexity
    /// - 21-50: Complex, higher risk
    /// - 50+: Very high risk, consider refactoring
    pub fn cyclomatic_complexity(&self) -> usize {
        self.decision_points + 1
    }

    /// Calculate cyclomatic complexity using graph formula.
    ///
    /// Uses the classic formula: M = E - N + 2P + C where:
    /// - E = number of edges
    /// - N = number of nodes (blocks)
    /// - P = number of connected components (always 1 for a single function)
    /// - C = comprehension decision points (for internal comprehension control flow)
    ///
    /// NOTE: This formula may give different results than `cyclomatic_complexity()`
    /// due to unreachable blocks (after return/raise) and graph structure variations.
    /// The decision-point-based method is recommended for consistency with Python.
    #[allow(dead_code)]
    pub fn cyclomatic_complexity_graph(&self) -> usize {
        let edges = self.edges.len();
        let nodes = self.blocks.len();
        edges.saturating_sub(nodes) + 2 + self.comprehension_decision_points
    }

    /// Build adjacency cache from edges (called once, lazily).
    ///
    /// Scans all edges once to build both successor and predecessor maps.
    /// Time: O(E) where E = number of edges
    /// Space: O(E) for storing all edge endpoints
    fn build_adjacency(&self) -> AdjacencyCache {
        let mut successors: HashMap<BlockId, Vec<BlockId>> =
            HashMap::with_capacity(self.blocks.len());
        let mut predecessors: HashMap<BlockId, Vec<BlockId>> =
            HashMap::with_capacity(self.blocks.len());

        for edge in &self.edges {
            successors.entry(edge.from).or_default().push(edge.to);
            predecessors.entry(edge.to).or_default().push(edge.from);
        }

        AdjacencyCache {
            successors,
            predecessors,
        }
    }

    /// Get the adjacency cache, building it if necessary.
    ///
    /// Thread-safe: uses `OnceCell` for lazy initialization.
    /// First call: O(E) to build cache
    /// Subsequent calls: O(1)
    #[inline]
    fn adjacency(&self) -> &AdjacencyCache {
        self.adjacency_cache.get_or_init(|| self.build_adjacency())
    }

    /// Get successors of a block (outgoing edges).
    ///
    /// Returns a slice of successor block IDs for O(1) lookup after cache is built.
    /// First call triggers O(E) cache construction; subsequent calls are O(1).
    ///
    /// # Arguments
    /// * `block_id` - The block to get successors for
    ///
    /// # Returns
    /// Slice of successor BlockIds (empty if block has no outgoing edges)
    #[allow(dead_code)]
    pub fn successors(&self, block_id: BlockId) -> &[BlockId] {
        self.adjacency()
            .successors
            .get(&block_id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Get predecessors of a block (incoming edges).
    ///
    /// Returns a slice of predecessor block IDs for O(1) lookup after cache is built.
    /// First call triggers O(E) cache construction; subsequent calls are O(1).
    ///
    /// # Arguments
    /// * `block_id` - The block to get predecessors for
    ///
    /// # Returns
    /// Slice of predecessor BlockIds (empty if block has no incoming edges)
    #[allow(dead_code)]
    pub fn predecessors(&self, block_id: BlockId) -> &[BlockId] {
        self.adjacency()
            .predecessors
            .get(&block_id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Invalidate the adjacency cache (call after modifying edges).
    ///
    /// This method is useful if edges are modified after CFG construction.
    /// The cache will be rebuilt on the next call to `successors()` or `predecessors()`.
    ///
    /// Note: This requires mutable access. If the CFG is shared immutably,
    /// prefer creating a new CFGInfo instead of modifying edges.
    #[allow(dead_code)]
    pub fn invalidate_adjacency_cache(&mut self) {
        self.adjacency_cache = OnceCell::new();
    }

    /// Add a nested CFG for an inner function or closure.
    ///
    /// # Arguments
    /// * `name` - The name of the nested function/closure
    /// * `cfg` - The control flow graph for the nested function
    #[allow(dead_code)]
    pub fn add_nested(&mut self, name: String, cfg: CFGInfo) {
        self.nested_cfgs.insert(name, Box::new(cfg));
    }

    /// Get nested CFG by name.
    ///
    /// # Arguments
    /// * `name` - The name of the nested function to retrieve
    ///
    /// # Returns
    /// Reference to the nested CFGInfo if found, None otherwise
    #[allow(dead_code)]
    pub fn get_nested(&self, name: &str) -> Option<&CFGInfo> {
        self.nested_cfgs.get(name).map(|boxed| boxed.as_ref())
    }

    /// Get mutable reference to nested CFG by name.
    ///
    /// # Arguments
    /// * `name` - The name of the nested function to retrieve
    ///
    /// # Returns
    /// Mutable reference to the nested CFGInfo if found, None otherwise
    #[allow(dead_code)]
    pub fn get_nested_mut(&mut self, name: &str) -> Option<&mut CFGInfo> {
        self.nested_cfgs.get_mut(name).map(|boxed| boxed.as_mut())
    }

    /// Iterate over all nested CFGs.
    ///
    /// # Returns
    /// Iterator yielding (name, cfg) pairs for all nested functions
    #[allow(dead_code)]
    pub fn nested_iter(&self) -> impl Iterator<Item = (&String, &CFGInfo)> {
        self.nested_cfgs.iter().map(|(k, v)| (k, v.as_ref()))
    }

    /// Check if this CFG has any nested functions/closures.
    #[allow(dead_code)]
    pub fn has_nested(&self) -> bool {
        !self.nested_cfgs.is_empty()
    }

    /// Get the count of nested CFGs.
    #[allow(dead_code)]
    pub fn nested_count(&self) -> usize {
        self.nested_cfgs.len()
    }

    /// Validate CFG structural invariants.
    ///
    /// Checks that:
    /// - Entry block exists in the blocks map
    /// - All exit blocks exist in the blocks map
    /// - All edge source and target blocks exist in the blocks map
    ///
    /// # Errors
    ///
    /// Returns `CFGError` if any invariant is violated:
    /// - `InvalidEntry` if entry block is not in blocks
    /// - `InvalidExit` if any exit block is not in blocks
    /// - `InvalidEdgeBlock` if any edge references a non-existent block
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::cfg::types::{CFGInfo, CFGBlock, BlockId, BlockType};
    /// use std::collections::HashMap;
    ///
    /// let entry_id = BlockId(0);
    /// let mut blocks = HashMap::new();
    /// blocks.insert(entry_id, CFGBlock {
    ///     id: entry_id,
    ///     label: "entry".to_string(),
    ///     block_type: BlockType::Entry,
    ///     statements: vec![],
    ///     func_calls: vec![],
    ///     start_line: 1,
    ///     end_line: 1,
    /// });
    ///
    /// let cfg = CFGInfo::new(
    ///     "test".to_string(),
    ///     blocks,
    ///     vec![],
    ///     entry_id,
    ///     vec![entry_id],
    /// );
    ///
    /// assert!(cfg.validate().is_ok());
    /// ```
    #[allow(dead_code)]
    pub fn validate(&self) -> Result<(), CFGError> {
        // Check entry block exists
        if !self.blocks.contains_key(&self.entry) {
            return Err(CFGError::InvalidEntry(self.entry));
        }

        // Check all exit blocks exist
        for exit in &self.exits {
            if !self.blocks.contains_key(exit) {
                return Err(CFGError::InvalidExit(*exit));
            }
        }

        // Check all edge endpoints exist
        for edge in &self.edges {
            if !self.blocks.contains_key(&edge.from) {
                return Err(CFGError::InvalidEdgeBlock(edge.from));
            }
            if !self.blocks.contains_key(&edge.to) {
                return Err(CFGError::InvalidEdgeBlock(edge.to));
            }
        }

        Ok(())
    }

    /// Insert a block with duplicate detection.
    ///
    /// Unlike direct `blocks.insert()`, this method returns an error if
    /// a block with the same ID already exists, preventing silent overwrites.
    ///
    /// # Errors
    ///
    /// Returns `CFGError::DuplicateBlockId` if a block with the same ID
    /// already exists in the blocks map.
    ///
    /// # Example
    ///
    /// ```
    /// use go_brrr::cfg::types::{CFGInfo, CFGBlock, BlockId, BlockType};
    /// use std::collections::HashMap;
    ///
    /// let mut cfg = CFGInfo::new(
    ///     "test".to_string(),
    ///     HashMap::new(),
    ///     vec![],
    ///     BlockId(0),
    ///     vec![],
    /// );
    ///
    /// let block = CFGBlock {
    ///     id: BlockId(0),
    ///     label: "entry".to_string(),
    ///     block_type: BlockType::Entry,
    ///     statements: vec![],
    ///     func_calls: vec![],
    ///     start_line: 1,
    ///     end_line: 1,
    /// };
    ///
    /// // First insert succeeds
    /// assert!(cfg.insert_block(block.clone()).is_ok());
    ///
    /// // Duplicate insert fails
    /// assert!(cfg.insert_block(block).is_err());
    /// ```
    #[allow(dead_code)]
    pub fn insert_block(&mut self, block: CFGBlock) -> Result<(), CFGError> {
        if self.blocks.contains_key(&block.id) {
            return Err(CFGError::DuplicateBlockId(block.id));
        }
        self.blocks.insert(block.id, block);
        Ok(())
    }

    /// Safe getter for a block by ID.
    ///
    /// Returns a reference to the block if it exists, None otherwise.
    /// Prefer this over direct `blocks.get()` for API consistency.
    ///
    /// # Arguments
    /// * `id` - The block ID to look up
    ///
    /// # Returns
    /// `Some(&CFGBlock)` if found, `None` otherwise
    #[allow(dead_code)]
    pub fn get_block(&self, id: BlockId) -> Option<&CFGBlock> {
        self.blocks.get(&id)
    }

    /// Check if a block is the entry block.
    ///
    /// # Arguments
    /// * `id` - The block ID to check
    ///
    /// # Returns
    /// `true` if the block is the entry point, `false` otherwise
    #[allow(dead_code)]
    pub fn is_entry(&self, id: BlockId) -> bool {
        self.entry == id
    }

    /// Check if a block is an exit block.
    ///
    /// # Arguments
    /// * `id` - The block ID to check
    ///
    /// # Returns
    /// `true` if the block is in the exits list, `false` otherwise
    #[allow(dead_code)]
    pub fn is_exit(&self, id: BlockId) -> bool {
        self.exits.contains(&id)
    }

    /// Detect if the CFG has any back edges (indicating loops).
    ///
    /// A back edge is an edge from a node to one of its ancestors in the
    /// DFS tree, which indicates a cycle (loop) in the control flow.
    ///
    /// # Returns
    /// `true` if the CFG contains at least one back edge (loop), `false` otherwise
    ///
    /// # Algorithm
    /// Uses depth-first search with a recursion stack to detect cycles.
    /// An edge to a node currently in the recursion stack is a back edge.
    #[allow(dead_code)]
    pub fn has_back_edge(&self) -> bool {
        let mut visited = HashSet::new();
        let mut stack = HashSet::new();
        self.has_back_edge_dfs(self.entry, &mut visited, &mut stack)
    }

    /// Internal DFS helper for back edge detection.
    ///
    /// Traverses the graph maintaining both visited set and current recursion stack.
    /// A back edge is detected when we encounter a successor already in the stack.
    #[allow(dead_code)]
    fn has_back_edge_dfs(
        &self,
        node: BlockId,
        visited: &mut HashSet<BlockId>,
        stack: &mut HashSet<BlockId>,
    ) -> bool {
        visited.insert(node);
        stack.insert(node);

        for &succ in self.successors(node) {
            if !visited.contains(&succ) {
                if self.has_back_edge_dfs(succ, visited, stack) {
                    return true;
                }
            } else if stack.contains(&succ) {
                // Found a back edge: edge to ancestor in DFS tree
                return true;
            }
        }

        stack.remove(&node);
        false
    }

    /// Check if the graph is connected from the entry block.
    ///
    /// A CFG is considered connected if all blocks are reachable from the entry.
    /// Unreachable blocks indicate dead code or a malformed graph.
    ///
    /// # Returns
    /// `true` if all blocks are reachable from entry, `false` otherwise
    #[allow(dead_code)]
    pub fn is_connected(&self) -> bool {
        let reachable = self.reachable_from(self.entry);
        reachable.len() == self.blocks.len()
    }

    /// Compute the set of blocks reachable from a given start block.
    ///
    /// Uses breadth-first traversal to find all blocks reachable via
    /// forward edges from the start block.
    ///
    /// # Arguments
    /// * `start` - The block ID to start traversal from
    ///
    /// # Returns
    /// Set of all reachable block IDs (includes the start block)
    #[allow(dead_code)]
    pub fn reachable_from(&self, start: BlockId) -> HashSet<BlockId> {
        let mut reachable = HashSet::new();
        let mut queue = vec![start];

        while let Some(node) = queue.pop() {
            if reachable.insert(node) {
                queue.extend(self.successors(node).iter().copied());
            }
        }

        reachable
    }

    /// Compute a topological ordering of blocks for dataflow analysis.
    ///
    /// Uses Kahn's algorithm to produce an ordering where each block appears
    /// after all its predecessors (excluding back edges). This is essential
    /// for correct dataflow analysis where we need to process definitions
    /// before their uses.
    ///
    /// # Returns
    /// Vector of BlockIds in topological order. For cyclic graphs (loops),
    /// back edges are ignored to produce a valid ordering.
    ///
    /// # Algorithm
    /// 1. Build in-degree map (counting non-back-edge predecessors)
    /// 2. Start with blocks that have zero in-degree
    /// 3. Process each block, decrementing in-degree of successors
    /// 4. Add successors to queue when their in-degree reaches zero
    pub fn topological_order(&self) -> Vec<BlockId> {
        use std::collections::VecDeque;

        // Identify back edges using DFS
        let back_edges = self.find_back_edges();

        // Build in-degree map (excluding back edges)
        let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
        for block_id in self.blocks.keys() {
            in_degree.insert(*block_id, 0);
        }

        for edge in &self.edges {
            if !back_edges.contains(&(edge.from, edge.to)) {
                *in_degree.entry(edge.to).or_insert(0) += 1;
            }
        }

        // Start with zero in-degree blocks (should include entry)
        let mut queue: VecDeque<BlockId> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(&id, _)| id)
            .collect();

        // Ensure entry is processed first if it has zero in-degree
        if let Some(pos) = queue.iter().position(|&id| id == self.entry) {
            queue.swap(0, pos);
        }

        let mut result = Vec::with_capacity(self.blocks.len());

        while let Some(block_id) = queue.pop_front() {
            result.push(block_id);

            // Process successors (excluding back edges)
            for edge in &self.edges {
                if edge.from == block_id && !back_edges.contains(&(edge.from, edge.to)) {
                    if let Some(deg) = in_degree.get_mut(&edge.to) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            queue.push_back(edge.to);
                        }
                    }
                }
            }
        }

        result
    }

    /// Find all back edges in the CFG using DFS.
    ///
    /// A back edge is an edge from a node to one of its ancestors in the
    /// DFS tree. These indicate loops in the control flow.
    ///
    /// # Returns
    /// Set of (from, to) block ID pairs representing back edges.
    fn find_back_edges(&self) -> HashSet<(BlockId, BlockId)> {
        let mut back_edges = HashSet::new();
        let mut visited = HashSet::new();
        let mut stack = HashSet::new();
        self.find_back_edges_dfs(self.entry, &mut visited, &mut stack, &mut back_edges);
        back_edges
    }

    /// Internal DFS helper for finding back edges.
    fn find_back_edges_dfs(
        &self,
        node: BlockId,
        visited: &mut HashSet<BlockId>,
        stack: &mut HashSet<BlockId>,
        back_edges: &mut HashSet<(BlockId, BlockId)>,
    ) {
        visited.insert(node);
        stack.insert(node);

        for &succ in self.successors(node) {
            if !visited.contains(&succ) {
                self.find_back_edges_dfs(succ, visited, stack, back_edges);
            } else if stack.contains(&succ) {
                // Found a back edge
                back_edges.insert((node, succ));
            }
        }

        stack.remove(&node);
    }

    /// Get the block containing a specific line number.
    ///
    /// Searches through all blocks to find which block contains the given line.
    /// When multiple blocks contain the same line (overlapping ranges), prefers:
    /// 1. The block with the smallest range (most specific)
    /// 2. If equal range, the block that ends at the line (definitions belong to ending block)
    ///
    /// This is important for CFG-aware DFG analysis where variable definitions
    /// at boundary lines need to be assigned to the correct block.
    ///
    /// # Arguments
    /// * `line` - The line number to look up (1-indexed)
    ///
    /// # Returns
    /// The BlockId of the block containing the line, or None if not found.
    pub fn block_for_line(&self, line: usize) -> Option<BlockId> {
        // Find all blocks that contain this line
        let mut candidates: Vec<(BlockId, &CFGBlock)> = self
            .blocks
            .iter()
            .filter(|(_, block)| line >= block.start_line && line <= block.end_line)
            .map(|(id, block)| (*id, block))
            .collect();

        if candidates.is_empty() {
            // Fallback: find the closest block that starts at or before the line
            let mut best_match: Option<(BlockId, usize)> = None;
            for (id, block) in &self.blocks {
                if block.start_line <= line {
                    match best_match {
                        None => best_match = Some((*id, block.start_line)),
                        Some((_, best_start)) if block.start_line > best_start => {
                            best_match = Some((*id, block.start_line));
                        }
                        _ => {}
                    }
                }
            }
            return best_match.map(|(id, _)| id);
        }

        if candidates.len() == 1 {
            return Some(candidates[0].0);
        }

        // Multiple blocks contain this line - need to pick the most appropriate one
        // For DFG analysis, we want definitions at a line to belong to the block
        // where they're executed, not merge/join blocks which are conceptual points.
        //
        // Priority:
        // 1. Prefer blocks that end at this line (the definition belongs there)
        // 2. Prefer blocks with later start_line (more specific to this location)
        // 3. Prefer larger ranges (actual code blocks over phantom merge points)
        candidates.sort_by(|(_, a), (_, b)| {
            // First priority: prefer block that ends at this line (definitions belong to ending block)
            let ends_at_line_a = a.end_line == line;
            let ends_at_line_b = b.end_line == line;
            let starts_at_line_a = a.start_line == line;
            let starts_at_line_b = b.start_line == line;

            // If one block only starts at this line while another ends at it,
            // prefer the one that ends (the definition is in the ending block)
            match (ends_at_line_a && !starts_at_line_a, ends_at_line_b && !starts_at_line_b) {
                (true, false) => return std::cmp::Ordering::Less,
                (false, true) => return std::cmp::Ordering::Greater,
                _ => {}
            }

            let range_a = a.end_line.saturating_sub(a.start_line);
            let range_b = b.end_line.saturating_sub(b.start_line);

            // Prefer larger range (actual code blocks over single-line merge points)
            match range_b.cmp(&range_a) {
                std::cmp::Ordering::Equal => {
                    // If same range, prefer block with later start
                    b.start_line.cmp(&a.start_line)
                }
                other => other,
            }
        });

        Some(candidates[0].0)
    }
}
