//! Go language support.
//!
//! Implements full extraction for Go code including:
//! - Functions (function_declaration)
//! - Methods (method_declaration with receivers)
//! - Structs (type_declaration with struct_type)
//! - Imports (import_declaration, single and grouped)
//!
//! Go-specific patterns handled:
//! - Receiver types (pointer and value)
//! - Multiple return values
//! - Named return values
//! - Doc comments (// style preceding declarations)

use std::sync::LazyLock;

use rustc_hash::FxHashMap;

use tree_sitter::{Node, Parser, Tree};

use aho_corasick::AhoCorasick;
use phf::phf_map;

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{BrrrError, Result};
use crate::lang::traits::Language;

// =========================================================================
// Compile-time optimized pattern matchers
// =========================================================================

/// Aho-Corasick automaton for context.WithCancel/WithTimeout/WithDeadline patterns.
/// Returns ContextOp::WithCancel for any match.
static CONTEXT_WITH_CANCEL_AC: LazyLock<AhoCorasick> = LazyLock::new(|| {
    AhoCorasick::new([
        "context.WithCancel",
        "context.WithTimeout",
        "context.WithDeadline",
    ])
    .expect("valid patterns")
});

/// Aho-Corasick automaton for context.Background/TODO patterns.
/// Returns ContextOp::Background for any match.
static CONTEXT_BACKGROUND_AC: LazyLock<AhoCorasick> = LazyLock::new(|| {
    AhoCorasick::new(["context.Background", "context.TODO"]).expect("valid patterns")
});

/// Aho-Corasick automaton for Go error check patterns.
/// Used to detect `if err != nil` style error handling.
static ERROR_CHECK_AC: LazyLock<AhoCorasick> = LazyLock::new(|| {
    AhoCorasick::new(["err != nil", "err == nil", "error != nil", "e != nil"])
        .expect("valid patterns")
});

/// PHF map for sync primitive method name to operation type.
/// O(1) lookup for Lock, Unlock, RLock, RUnlock, Add, Done, Wait, Do, Get, Put.
static SYNC_PRIMITIVE_MAP: phf::Map<&'static str, SyncPrimitiveOp> = phf_map! {
    "Lock" => SyncPrimitiveOp::MutexLock,
    "Unlock" => SyncPrimitiveOp::MutexUnlock,
    "RLock" => SyncPrimitiveOp::MutexRLock,
    "RUnlock" => SyncPrimitiveOp::MutexRUnlock,
    "Add" => SyncPrimitiveOp::WaitGroupAdd,
    "Done" => SyncPrimitiveOp::WaitGroupDone,
    "Wait" => SyncPrimitiveOp::WaitGroupWait,
    "Do" => SyncPrimitiveOp::OnceDo,
    "Get" => SyncPrimitiveOp::PoolGet,
    "Put" => SyncPrimitiveOp::PoolPut,
};

/// PHF map for context method name to operation type.
/// O(1) lookup for Done, Err, Value, Deadline.
static CONTEXT_METHOD_MAP: phf::Map<&'static str, ContextOp> = phf_map! {
    "Done" => ContextOp::Done,
    "Err" => ContextOp::Err,
    "Value" => ContextOp::Value,
    "Deadline" => ContextOp::Deadline,
};

// =========================================================================
// Go concurrency helper types
// =========================================================================

/// Sync primitive operations detected in Go code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncPrimitiveOp {
    /// sync.Mutex.Lock() or sync.RWMutex.Lock()
    MutexLock,
    /// sync.Mutex.Unlock() or sync.RWMutex.Unlock()
    MutexUnlock,
    /// sync.RWMutex.RLock() - read lock
    MutexRLock,
    /// sync.RWMutex.RUnlock() - read unlock
    MutexRUnlock,
    /// sync.WaitGroup.Add(n)
    WaitGroupAdd,
    /// sync.WaitGroup.Done()
    WaitGroupDone,
    /// sync.WaitGroup.Wait()
    WaitGroupWait,
    /// sync.Once.Do(f)
    OnceDo,
    /// sync.Pool.Get()
    PoolGet,
    /// sync.Pool.Put(x)
    PoolPut,
}

/// Context operations detected in Go code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContextOp {
    /// context.Background() or context.TODO()
    Background,
    /// context.WithCancel(), WithTimeout(), WithDeadline()
    WithCancel,
    /// context.WithValue()
    WithValue,
    /// ctx.Done() - returns channel for cancellation
    Done,
    /// ctx.Err() - returns cancellation error
    Err,
    /// ctx.Value(key) - retrieves value from context
    Value,
    /// ctx.Deadline() - returns deadline if set
    Deadline,
}

/// Channel direction in Go.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelDirection {
    /// chan T - bidirectional
    Bidirectional,
    /// chan<- T - send-only
    SendOnly,
    /// <-chan T - receive-only
    ReceiveOnly,
}

/// Information about a Go channel.
#[derive(Debug, Clone)]
pub struct ChannelInfo {
    /// Whether the channel is buffered (has capacity > 0)
    pub is_buffered: bool,
    /// Channel direction constraint
    pub direction: ChannelDirection,
}

/// Kind of concurrency issue detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrencyIssueKind {
    /// Goroutine that might not terminate (no coordination)
    GoroutineLeak,
    /// Channel created but never closed
    ChannelNeverClosed,
    /// Potential deadlock pattern detected
    PotentialDeadlock,
    /// Mutex lock without corresponding unlock
    MutexLockWithoutUnlock,
    /// WaitGroup misuse (Wait without Add)
    WaitGroupMisuse,
    /// Potential data race (shared variable without sync)
    DataRace,
    /// Infinite blocking operation (empty select {})
    InfiniteBlock,
}

/// Severity of concurrency issue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IssueSeverity {
    /// Informational - might be intentional
    Info,
    /// Warning - probably a bug but could be intentional
    Warning,
    /// Error - likely a serious bug
    Error,
}

/// A detected concurrency issue.
#[derive(Debug, Clone)]
pub struct ConcurrencyIssue {
    /// Kind of issue
    pub kind: ConcurrencyIssueKind,
    /// Block where issue was detected
    pub block_id: BlockId,
    /// Human-readable description
    pub description: String,
    /// Severity level
    pub severity: IssueSeverity,
}

/// Go language implementation.
pub struct Go;

impl Go {
    /// Safely decode bytes to UTF-8 string, replacing invalid sequences.
    #[inline]
    fn decode_text<'a>(&self, source: &'a [u8], node: Node) -> &'a str {
        let bytes = &source[node.start_byte()..node.end_byte()];
        std::str::from_utf8(bytes).unwrap_or("")
    }

    /// Extract text from a node, owned version.
    fn node_text(&self, source: &[u8], node: Node) -> String {
        self.decode_text(source, node).to_string()
    }

    /// Find a child node by field name.
    fn child_by_field<'a>(&self, node: Node<'a>, field: &str) -> Option<Node<'a>> {
        node.child_by_field_name(field)
    }

    /// Check if a defer block contains recover() call.
    ///
    /// In Go, recover() catches panics only when called from a deferred function.
    fn contains_recover(&self, node: Node, source: &[u8]) -> bool {
        let text = self.node_text(source, node);
        text.contains("recover()")
    }

    /// Check if a call expression is a panic() call.
    ///
    /// Handles both call_expression directly and expression_statement wrapping a call_expression.
    fn is_panic_call(&self, node: Node, source: &[u8]) -> bool {
        match node.kind() {
            "call_expression" => {
                if let Some(func) = self.child_by_field(node, "function") {
                    let func_name = self.node_text(source, func);
                    return func_name == "panic";
                }
            }
            "expression_statement" => {
                // Check if the expression is a panic call
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "call_expression" {
                        if let Some(func) = self.child_by_field(child, "function") {
                            let func_name = self.node_text(source, func);
                            if func_name == "panic" {
                                return true;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        false
    }

    /// Check if a node contains potential runtime panics.
    ///
    /// This includes:
    /// - Explicit panic() calls
    /// - Array/slice index operations (potential out of bounds)
    /// - Map access (potential nil map)
    /// - Pointer dereference (potential nil pointer)
    fn has_potential_panic(&self, node: Node, source: &[u8]) -> bool {
        // Check for explicit panic call
        if self.is_panic_call(node, source) {
            return true;
        }

        let text = self.node_text(source, node);

        // Check for panic() in text
        if text.contains("panic(") {
            return true;
        }

        // Could add more sophisticated checks for:
        // - Array/slice indexing without bounds check
        // - Map access without ok check
        // - Pointer dereference
        // For now, keep it simple

        false
    }

    /// Get preceding comment as doc comment.
    /// Go uses // comments directly before declarations.
    /// Doc comments must be immediately adjacent (no blank lines).
    fn get_doc_comment(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut comments = Vec::new();
        // Track the row we expect the next comment to end on.
        // Initially, this is the row immediately before the declaration.
        let mut expected_end_row = node.start_position().row;

        // Walk backwards through siblings to find adjacent comments
        if let Some(parent) = node.parent() {
            let mut found_self = false;
            let child_count = parent.child_count();

            for i in (0..child_count).rev() {
                if let Some(sibling) = parent.child(i as u32) {
                    if sibling.id() == node.id() {
                        found_self = true;
                        continue;
                    }

                    if found_self && sibling.kind() == "comment" {
                        let comment_end_row = sibling.end_position().row;
                        // Comment must end on the line immediately before expected_end_row
                        // (i.e., no blank lines between comment and declaration/previous comment)
                        if comment_end_row + 1 == expected_end_row {
                            let text = self.decode_text(source, sibling);
                            // Remove // prefix
                            let cleaned = text.strip_prefix("//").unwrap_or(text).trim();
                            comments.push(cleaned.to_string());
                            // Update: next comment must end right before this one starts
                            expected_end_row = sibling.start_position().row;
                        } else {
                            break;
                        }
                    } else if found_self && sibling.kind() != "comment" {
                        break;
                    }
                }
            }
        }

        if comments.is_empty() {
            None
        } else {
            comments.reverse();
            Some(comments.join("\n"))
        }
    }

    /// Extract Go parameter list from parameter_list node.
    /// Handles both regular params and receiver params.
    fn extract_param_list(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                let param_text = self.extract_parameter_declaration(child, source);
                if !param_text.is_empty() {
                    params.push(param_text);
                }
            }
        }

        params
    }

    /// Extract a single parameter declaration.
    /// Handles: `name type`, `name1, name2 type`, and unnamed `type`.
    fn extract_parameter_declaration(&self, node: Node, source: &[u8]) -> String {
        let mut names = Vec::new();
        let mut type_str = String::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" | "field_identifier" => {
                    names.push(self.node_text(source, child));
                }
                // Type nodes - extract the full type text
                "type_identifier" | "pointer_type" | "array_type" | "slice_type" | "map_type"
                | "channel_type" | "function_type" | "interface_type" | "struct_type"
                | "qualified_type" | "generic_type" => {
                    type_str = self.node_text(source, child);
                }
                "variadic_parameter_declaration" => {
                    // Handle ...type
                    return self.node_text(source, child);
                }
                _ => {}
            }
        }

        if names.is_empty() {
            // Unnamed parameter, just type
            type_str
        } else {
            // Named parameter(s)
            format!("{} {}", names.join(", "), type_str)
        }
    }

    /// Extract return type from result node.
    /// Handles single type, multiple returns, and named returns.
    fn extract_return_type(&self, node: Node, source: &[u8]) -> Option<String> {
        match node.kind() {
            "type_identifier" | "pointer_type" | "array_type" | "slice_type" | "map_type"
            | "channel_type" | "function_type" | "interface_type" | "struct_type"
            | "qualified_type" | "generic_type" => Some(self.node_text(source, node)),
            "parameter_list" => {
                // Multiple or named returns: (int, error) or (result string, err error)
                let params = self.extract_param_list(node, source);
                if params.is_empty() {
                    None
                } else {
                    Some(format!("({})", params.join(", ")))
                }
            }
            _ => None,
        }
    }

    /// Extract receiver information from method.
    /// Returns (receiver_name, receiver_type) tuple.
    fn extract_receiver(&self, node: Node, source: &[u8]) -> Option<(String, String)> {
        let receiver_list = self.child_by_field(node, "receiver")?;
        let mut cursor = receiver_list.walk();

        for child in receiver_list.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                let mut name = String::new();
                let mut type_str = String::new();
                let mut inner_cursor = child.walk();

                for inner_child in child.children(&mut inner_cursor) {
                    match inner_child.kind() {
                        "identifier" => {
                            name = self.node_text(source, inner_child);
                        }
                        "pointer_type" | "type_identifier" | "generic_type" => {
                            type_str = self.node_text(source, inner_child);
                        }
                        _ => {}
                    }
                }

                if !type_str.is_empty() {
                    return Some((name, type_str));
                }
            }
        }

        None
    }

    /// Build CFG for Go function body with proper defer/panic/recover flow.
    ///
    /// Go defer semantics:
    /// - defer statements are pushed onto a stack
    /// - On function exit (return/panic), deferred calls execute in LIFO order
    /// - recover() only works inside a deferred function
    /// - Named return values can be modified by deferred functions
    fn build_go_cfg(&self, node: Node, source: &[u8], func_name: &str) -> CFGInfo {
        let mut blocks = FxHashMap::default();
        let mut edges = Vec::new();
        let mut block_id = 0;
        let mut exits = Vec::new();
        let mut decision_points = 0;

        // Track deferred calls in order of appearance (will execute in reverse)
        let mut defer_stack: Vec<BlockId> = Vec::new();

        // Track panic sites for connecting to deferred calls
        let mut panic_sites: Vec<BlockId> = Vec::new();

        // Entry block
        let entry = BlockId(block_id);
        blocks.insert(
            entry,
            CFGBlock {
                id: entry,
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );
        block_id += 1;

        // Collect return blocks for later wiring to deferred calls
        let mut return_blocks: Vec<BlockId> = Vec::new();

        // Find body block
        if let Some(body) = self.child_by_field(node, "body") {
            self.process_cfg_block_with_defer(
                body,
                source,
                &mut blocks,
                &mut edges,
                &mut block_id,
                entry,
                &mut exits,
                &mut defer_stack,
                &mut panic_sites,
                &mut return_blocks,
                &mut decision_points,
            );
        }

        // Wire deferred calls in LIFO order for all exit paths
        // Each return/exit should flow through deferred calls before actual exit
        if !defer_stack.is_empty() {
            // Create exit block for final function exit
            let exit_block = BlockId(block_id);
            block_id += 1;
            blocks.insert(
                exit_block,
                CFGBlock {
                    id: exit_block,
                    label: "exit".to_string(),
                    block_type: BlockType::Exit,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: node.end_position().row + 1,
                    end_line: node.end_position().row + 1,
                },
            );

            // Wire deferred calls in reverse order (LIFO)
            let mut prev_defer: Option<BlockId> = None;
            for &defer_block in defer_stack.iter().rev() {
                if let Some(prev) = prev_defer {
                    edges.push(CFGEdge::new(prev, defer_block, EdgeType::DeferChain));
                }
                prev_defer = Some(defer_block);
            }

            // Connect last deferred call to exit
            if let Some(last_defer) = prev_defer {
                edges.push(CFGEdge::new(
                    last_defer,
                    exit_block,
                    EdgeType::Unconditional,
                ));
            }

            // Connect return blocks to first deferred call (which is last in stack - LIFO)
            if let Some(&first_to_execute) = defer_stack.last() {
                for &ret_block in &return_blocks {
                    // Remove any existing edges from ret_block
                    edges.retain(|e| e.from != ret_block);
                    edges.push(CFGEdge::new(ret_block, first_to_execute, EdgeType::Defer));
                }
            }

            // Connect panic sites to deferred calls (panic unwinds through defers)
            if let Some(&first_to_execute) = defer_stack.last() {
                for &panic_block in &panic_sites {
                    edges.push(CFGEdge::new(panic_block, first_to_execute, EdgeType::Panic));
                }
            }

            exits = vec![exit_block];
        } else if exits.is_empty() {
            // No defers and no explicit exits - entry is exit
            exits.push(entry);
        }

        CFGInfo {
            function_name: func_name.to_string(),
            blocks,
            edges,
            entry,
            exits,
            decision_points,
            comprehension_decision_points: 0, // Go doesn't have Python-style comprehensions
            nested_cfgs: FxHashMap::default(), // TODO: Handle Go closures/anonymous functions as nested CFGs
            is_async: false,             // Go uses goroutines, not async/await
            await_points: 0,             // Go doesn't have await
            blocking_calls: Vec::new(),  // Go doesn't have async context blocking detection
            ..Default::default()
        }
    }

    /// Recursively process a block for CFG construction with defer/panic/recover tracking.
    ///
    /// This enhanced version tracks:
    /// - Defer statements (added to defer_stack in order)
    /// - Panic sites (explicit panic(), potential runtime panics)
    /// - Return blocks (for wiring to deferred calls)
    /// - Error check patterns (if err != nil)
    fn process_cfg_block_with_defer(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        defer_stack: &mut Vec<BlockId>,
        panic_sites: &mut Vec<BlockId>,
        return_blocks: &mut Vec<BlockId>,
        decision_points: &mut usize,
    ) -> BlockId {
        let mut last_block = current_block;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "return_statement" => {
                    // Create return block
                    *block_id += 1;
                    let ret_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        ret_block,
                        CFGBlock {
                            id: ret_block,
                            label: format!("return: {}", stmt.trim()),
                            block_type: BlockType::Return,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::unconditional(last_block, ret_block));
                    return_blocks.push(ret_block);
                    exits.push(ret_block);
                    last_block = ret_block;
                }
                "if_statement" => {
                    // Check for error check pattern: if err != nil
                    if self.is_error_check_pattern(child, source) {
                        last_block = self.process_error_check_cfg(
                            child,
                            source,
                            blocks,
                            edges,
                            block_id,
                            last_block,
                            exits,
                            defer_stack,
                            panic_sites,
                            return_blocks,
                            decision_points,
                        );
                    } else {
                        *decision_points += 1;
                        // Process if statement with panic tracking
                        last_block = self.process_if_cfg_tracking_panic(
                            child,
                            source,
                            blocks,
                            edges,
                            block_id,
                            last_block,
                            exits,
                            defer_stack,
                            panic_sites,
                            return_blocks,
                            decision_points,
                        );
                    }
                }
                "for_statement" => {
                    *decision_points += 1;
                    // Process for loop without defer tracking (defer handled at function level)
                    last_block = self
                        .process_for_cfg(child, source, blocks, edges, block_id, last_block, exits);
                }
                "expression_switch_statement" | "type_switch_statement" => {
                    // Switch statements without defer tracking (defer handled at function level)
                    last_block = self.process_switch_cfg(
                        child, source, blocks, edges, block_id, last_block, exits,
                    );
                }
                "statement_list" | "block" => {
                    last_block = self.process_cfg_block_with_defer(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        defer_stack,
                        panic_sites,
                        return_blocks,
                        decision_points,
                    );
                }
                // Goroutine statement - create dedicated block for concurrency analysis
                "go_statement" => {
                    *block_id += 1;
                    let go_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        go_block,
                        CFGBlock {
                            id: go_block,
                            label: format!("goroutine: {}", stmt.trim()),
                            block_type: BlockType::GoroutineSpawn,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::new(last_block, go_block, EdgeType::Spawn));
                    last_block = go_block;
                }
                // Select statement - multi-way channel operation
                "select_statement" => {
                    *decision_points += 1;
                    last_block = self.process_select_cfg(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        last_block,
                        exits,
                        decision_points,
                    );
                }
                // Defer statement - add to defer stack with proper block type
                "defer_statement" => {
                    *block_id += 1;
                    let defer_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    // Check if this defer contains a recover() call
                    let has_recover = self.contains_recover(child, source);
                    let block_type = if has_recover {
                        BlockType::RecoverCall
                    } else {
                        BlockType::DeferredCall
                    };

                    blocks.insert(
                        defer_block,
                        CFGBlock {
                            id: defer_block,
                            label: format!("defer: {}", stmt.trim()),
                            block_type,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    // Don't add edge here - defer executes at function exit
                    // Just record in stack (LIFO order)
                    defer_stack.push(defer_block);
                    // Control flow continues past defer registration
                    // Add edge to show defer was encountered
                    edges.push(CFGEdge::new(last_block, defer_block, EdgeType::Defer));
                    last_block = defer_block;
                }
                // Channel send statement - track for concurrency analysis
                "send_statement" => {
                    *block_id += 1;
                    let send_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        send_block,
                        CFGBlock {
                            id: send_block,
                            label: format!("chan<-: {}", stmt.trim()),
                            block_type: BlockType::ChannelSend,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::new(last_block, send_block, EdgeType::Send));
                    last_block = send_block;
                }
                // Expression statement - check for panic(), sync primitives, and context calls
                "expression_statement" => {
                    // Find call_expression inside expression_statement
                    let call_expr = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "call_expression");

                    if self.is_panic_call(child, source) {
                        *block_id += 1;
                        let panic_block = BlockId(*block_id);
                        let stmt = self.node_text(source, child);

                        blocks.insert(
                            panic_block,
                            CFGBlock {
                                id: panic_block,
                                label: format!("panic: {}", stmt.trim()),
                                block_type: BlockType::GoPanicSite,
                                statements: vec![stmt],
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::new(last_block, panic_block, EdgeType::Panic));
                        panic_sites.push(panic_block);
                        last_block = panic_block;
                    } else if let Some(call) = call_expr {
                        // Check for channel close
                        if self.is_channel_close(call, source) {
                            *block_id += 1;
                            let close_block = BlockId(*block_id);
                            let stmt = self.node_text(source, child);

                            blocks.insert(
                                close_block,
                                CFGBlock {
                                    id: close_block,
                                    label: format!("close: {}", stmt.trim()),
                                    block_type: BlockType::ChannelClose,
                                    statements: vec![stmt],
                                    func_calls: Vec::new(),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(
                                last_block,
                                close_block,
                                EdgeType::ChannelClose,
                            ));
                            last_block = close_block;
                        // Check for sync primitive operations
                        } else if let Some(sync_op) = self.is_sync_primitive_call(call, source) {
                            *block_id += 1;
                            let sync_block = BlockId(*block_id);
                            let stmt = self.node_text(source, child);

                            let (block_type, edge_type, label_prefix) = match sync_op {
                                SyncPrimitiveOp::MutexLock | SyncPrimitiveOp::MutexRLock => {
                                    (BlockType::MutexLock, EdgeType::Lock, "lock")
                                }
                                SyncPrimitiveOp::MutexUnlock | SyncPrimitiveOp::MutexRUnlock => {
                                    (BlockType::MutexUnlock, EdgeType::Unlock, "unlock")
                                }
                                SyncPrimitiveOp::WaitGroupAdd | SyncPrimitiveOp::WaitGroupDone => {
                                    (BlockType::WaitGroupOp, EdgeType::Unconditional, "wg_op")
                                }
                                SyncPrimitiveOp::WaitGroupWait => {
                                    (BlockType::WaitGroupWait, EdgeType::WaitSync, "wg_wait")
                                }
                                SyncPrimitiveOp::OnceDo => {
                                    (BlockType::OnceCall, EdgeType::Unconditional, "once_do")
                                }
                                SyncPrimitiveOp::PoolGet | SyncPrimitiveOp::PoolPut => {
                                    (BlockType::Body, EdgeType::Unconditional, "pool")
                                }
                            };

                            blocks.insert(
                                sync_block,
                                CFGBlock {
                                    id: sync_block,
                                    label: format!("{}: {}", label_prefix, stmt.trim()),
                                    block_type,
                                    statements: vec![stmt],
                                    func_calls: Vec::new(),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(last_block, sync_block, edge_type));
                            last_block = sync_block;
                        // Check for context operations
                        } else if let Some(ctx_op) = self.is_context_call(call, source) {
                            if matches!(ctx_op, ContextOp::Done) {
                                // ctx.Done() is special - creates a channel receive pattern
                                *block_id += 1;
                                let ctx_block = BlockId(*block_id);
                                let stmt = self.node_text(source, child);

                                blocks.insert(
                                    ctx_block,
                                    CFGBlock {
                                        id: ctx_block,
                                        label: format!("ctx_done: {}", stmt.trim()),
                                        block_type: BlockType::ContextCheck,
                                        statements: vec![stmt],
                                        func_calls: Vec::new(),
                                        start_line: child.start_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );

                                edges.push(CFGEdge::unconditional(last_block, ctx_block));
                                last_block = ctx_block;
                            } else if let Some(block) = blocks.get_mut(&last_block) {
                                let stmt = self.node_text(source, child);
                                block.statements.push(stmt);
                                block.end_line = child.end_position().row + 1;
                            }
                        } else if let Some(block) = blocks.get_mut(&last_block) {
                            let stmt = self.node_text(source, child);
                            block.statements.push(stmt);
                            block.end_line = child.end_position().row + 1;
                        }
                    } else if let Some(block) = blocks.get_mut(&last_block) {
                        let stmt = self.node_text(source, child);
                        block.statements.push(stmt);
                        block.end_line = child.end_position().row + 1;
                    }
                }
                // Regular statements - add to current block
                "short_var_declaration" | "assignment_statement" | "call_expression" => {
                    // Find call expressions in the RHS
                    let call_in_rhs = self.find_call_in_node(child);
                    let stmt = self.node_text(source, child);

                    // Check for channel make: ch := make(chan int)
                    if let Some(call) = call_in_rhs {
                        if self.is_channel_make(call, source).is_some() {
                            *block_id += 1;
                            let make_block = BlockId(*block_id);

                            blocks.insert(
                                make_block,
                                CFGBlock {
                                    id: make_block,
                                    label: format!("make_chan: {}", stmt.trim()),
                                    block_type: BlockType::ChannelMake,
                                    statements: vec![stmt],
                                    func_calls: Vec::new(),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::unconditional(last_block, make_block));
                            last_block = make_block;
                            continue;
                        }
                    }

                    // Check for channel receive in assignment: val := <-ch
                    if self.is_channel_receive_in_node(child, source) {
                        *block_id += 1;
                        let recv_block = BlockId(*block_id);

                        blocks.insert(
                            recv_block,
                            CFGBlock {
                                id: recv_block,
                                label: format!("<-chan: {}", stmt.trim()),
                                block_type: BlockType::ChannelReceive,
                                statements: vec![stmt.clone()],
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::new(last_block, recv_block, EdgeType::Receive));
                        last_block = recv_block;
                    // Check for panic potential in index expressions
                    } else if self.has_potential_panic(child, source) {
                        *block_id += 1;
                        let potential_panic = BlockId(*block_id);

                        blocks.insert(
                            potential_panic,
                            CFGBlock {
                                id: potential_panic,
                                label: format!("potential_panic: {}", stmt.trim()),
                                block_type: BlockType::GoPanicSite,
                                statements: vec![stmt],
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::unconditional(last_block, potential_panic));
                        panic_sites.push(potential_panic);
                        last_block = potential_panic;
                    } else if let Some(block) = blocks.get_mut(&last_block) {
                        block.statements.push(stmt);
                        block.end_line = child.end_position().row + 1;
                    }
                }
                _ => {}
            }
        }

        last_block
    }

    /// Recursively process a block for CFG construction (legacy version without defer tracking).
    fn process_cfg_block(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
    ) -> BlockId {
        let mut last_block = current_block;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "return_statement" => {
                    // Create return block
                    *block_id += 1;
                    let ret_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        ret_block,
                        CFGBlock {
                            id: ret_block,
                            label: format!("return: {}", stmt.trim()),
                            block_type: BlockType::Return,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(last_block, ret_block, None));

                    exits.push(ret_block);
                    last_block = ret_block;
                }
                "if_statement" => {
                    last_block = self
                        .process_if_cfg(child, source, blocks, edges, block_id, last_block, exits);
                }
                "for_statement" => {
                    last_block = self
                        .process_for_cfg(child, source, blocks, edges, block_id, last_block, exits);
                }
                "expression_switch_statement" | "type_switch_statement" => {
                    last_block = self.process_switch_cfg(
                        child, source, blocks, edges, block_id, last_block, exits,
                    );
                }
                "statement_list" | "block" => {
                    last_block = self.process_cfg_block(
                        child, source, blocks, edges, block_id, last_block, exits,
                    );
                }
                // Goroutine statement - create dedicated block for concurrency analysis
                "go_statement" => {
                    *block_id += 1;
                    let go_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        go_block,
                        CFGBlock {
                            id: go_block,
                            label: format!("goroutine: {}", stmt.trim()),
                            block_type: BlockType::Body,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(
                        last_block,
                        go_block,
                        Some("spawn".to_string()),
                    ));

                    // Goroutine runs concurrently, so control continues
                    // The goroutine block is a "detached" concurrent path
                    last_block = go_block;
                }
                // Defer statement - track separately for cleanup analysis
                "defer_statement" => {
                    *block_id += 1;
                    let defer_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        defer_block,
                        CFGBlock {
                            id: defer_block,
                            label: format!("defer: {}", stmt.trim()),
                            block_type: BlockType::Body,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(
                        last_block,
                        defer_block,
                        Some("defer".to_string()),
                    ));

                    last_block = defer_block;
                }
                // Channel send statement - track for concurrency analysis
                "send_statement" => {
                    *block_id += 1;
                    let send_block = BlockId(*block_id);
                    let stmt = self.node_text(source, child);

                    blocks.insert(
                        send_block,
                        CFGBlock {
                            id: send_block,
                            label: format!("chan<-: {}", stmt.trim()),
                            block_type: BlockType::Body,
                            statements: vec![stmt],
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(
                        last_block,
                        send_block,
                        Some("send".to_string()),
                    ));

                    last_block = send_block;
                }
                // Regular statements - add to current block
                "short_var_declaration"
                | "assignment_statement"
                | "expression_statement"
                | "call_expression" => {
                    if let Some(block) = blocks.get_mut(&last_block) {
                        let stmt = self.node_text(source, child);
                        block.statements.push(stmt);
                        block.end_line = child.end_position().row + 1;
                    }
                }
                _ => {}
            }
        }

        last_block
    }

    /// Process if statement for CFG.
    fn process_if_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
    ) -> BlockId {
        // Condition block
        *block_id += 1;
        let cond_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(source, n))
            .unwrap_or_else(|| "condition".to_string());

        blocks.insert(
            cond_block,
            CFGBlock {
                id: cond_block,
                label: format!("if {}", condition),
                block_type: BlockType::Branch,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, cond_block, None));

        // True branch
        *block_id += 1;
        let true_block = BlockId(*block_id);
        blocks.insert(
            true_block,
            CFGBlock {
                id: true_block,
                label: "then".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(
            cond_block,
            true_block,
            Some("true".to_string()),
        ));

        let true_end = if let Some(consequence) = self.child_by_field(node, "consequence") {
            self.process_cfg_block(
                consequence,
                source,
                blocks,
                edges,
                block_id,
                true_block,
                exits,
            )
        } else {
            true_block
        };

        // False/else branch
        let false_end = if let Some(alternative) = self.child_by_field(node, "alternative") {
            *block_id += 1;
            let false_block = BlockId(*block_id);
            blocks.insert(
                false_block,
                CFGBlock {
                    id: false_block,
                    label: "else".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: alternative.start_position().row + 1,
                    end_line: alternative.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::from_label(
                cond_block,
                false_block,
                Some("false".to_string()),
            ));

            self.process_cfg_block(
                alternative,
                source,
                blocks,
                edges,
                block_id,
                false_block,
                exits,
            )
        } else {
            cond_block
        };

        // Merge block
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "endif".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(true_end, merge_block, None));
        edges.push(CFGEdge::from_label(false_end, merge_block, None));

        merge_block
    }

    /// Process for statement for CFG.
    fn process_for_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
    ) -> BlockId {
        // Loop header
        *block_id += 1;
        let header_block = BlockId(*block_id);
        let header_text = self
            .node_text(source, node)
            .lines()
            .next()
            .unwrap_or("for")
            .to_string();

        blocks.insert(
            header_block,
            CFGBlock {
                id: header_block,
                label: header_text,
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, header_block, None));

        // Loop body
        *block_id += 1;
        let body_block = BlockId(*block_id);
        blocks.insert(
            body_block,
            CFGBlock {
                id: body_block,
                label: "loop body".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(
            header_block,
            body_block,
            Some("iterate".to_string()),
        ));

        let body_end = if let Some(body) = self.child_by_field(node, "body") {
            self.process_cfg_block(body, source, blocks, edges, block_id, body_block, exits)
        } else {
            body_block
        };

        // Back edge
        edges.push(CFGEdge::from_label(
            body_end,
            header_block,
            Some("continue".to_string()),
        ));

        // Exit block
        *block_id += 1;
        let exit_block = BlockId(*block_id);
        blocks.insert(
            exit_block,
            CFGBlock {
                id: exit_block,
                label: "endfor".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(
            header_block,
            exit_block,
            Some("done".to_string()),
        ));

        exit_block
    }

    /// Process switch statement for CFG.
    fn process_switch_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
    ) -> BlockId {
        // Switch header
        *block_id += 1;
        let switch_block = BlockId(*block_id);
        let switch_text = self
            .node_text(source, node)
            .lines()
            .next()
            .unwrap_or("switch")
            .to_string();

        blocks.insert(
            switch_block,
            CFGBlock {
                id: switch_block,
                label: switch_text,
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::from_label(current_block, switch_block, None));

        // Merge block for after switch
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "endswitch".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // Process cases
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "expression_case"
                || child.kind() == "default_case"
                || child.kind() == "type_case"
            {
                *block_id += 1;
                let case_block = BlockId(*block_id);
                let case_text = self
                    .node_text(source, child)
                    .lines()
                    .next()
                    .unwrap_or("case")
                    .to_string();

                blocks.insert(
                    case_block,
                    CFGBlock {
                        id: case_block,
                        label: case_text,
                        block_type: BlockType::Body,
                        statements: Vec::new(),
                        func_calls: Vec::new(),
                        start_line: child.start_position().row + 1,
                        end_line: child.end_position().row + 1,
                    },
                );

                edges.push(CFGEdge::from_label(switch_block, case_block, None));

                let case_end = self
                    .process_cfg_block(child, source, blocks, edges, block_id, case_block, exits);

                edges.push(CFGEdge::from_label(case_end, merge_block, None));
            }
        }

        merge_block
    }

    /// Process select statement for CFG.
    ///
    /// Go select statements implement multi-way channel operations:
    /// - `case <-ch:` - receive from channel
    /// - `case ch <- val:` - send to channel
    /// - `case val := <-ch:` - receive with assignment
    /// - `case val, ok := <-ch:` - receive with ok check
    /// - `default:` - non-blocking fallback
    ///
    /// All cases are evaluated simultaneously; the first ready case executes.
    /// If no case is ready and there's no default, select blocks.
    fn process_select_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        decision_points: &mut usize,
    ) -> BlockId {
        // Select block header
        *block_id += 1;
        let select_block = BlockId(*block_id);
        let select_text = self
            .node_text(source, node)
            .lines()
            .next()
            .unwrap_or("select")
            .to_string();

        blocks.insert(
            select_block,
            CFGBlock {
                id: select_block,
                label: select_text,
                block_type: BlockType::SelectBlock,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(current_block, select_block));

        // Merge block for after select
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "endselect".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // Track if we have a default case (makes select non-blocking)
        let mut has_default = false;
        let mut case_count = 0;

        // Process communication_case and default_case
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "communication_case" => {
                    case_count += 1;
                    *decision_points += 1;

                    *block_id += 1;
                    let case_block = BlockId(*block_id);

                    // Determine if this is a send or receive case
                    let (case_text, block_type) = self.analyze_communication_case(child, source);

                    blocks.insert(
                        case_block,
                        CFGBlock {
                            id: case_block,
                            label: case_text,
                            block_type,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::new(select_block, case_block, EdgeType::SelectCase));

                    // Process case body
                    let case_end = self.process_select_case_body(
                        child, source, blocks, edges, block_id, case_block, exits,
                    );

                    edges.push(CFGEdge::unconditional(case_end, merge_block));
                }
                "default_case" => {
                    has_default = true;
                    *decision_points += 1;

                    *block_id += 1;
                    let default_block = BlockId(*block_id);
                    let default_text = self
                        .node_text(source, child)
                        .lines()
                        .next()
                        .unwrap_or("default")
                        .to_string();

                    blocks.insert(
                        default_block,
                        CFGBlock {
                            id: default_block,
                            label: default_text,
                            block_type: BlockType::SelectCase,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::new(
                        select_block,
                        default_block,
                        EdgeType::SelectDefault,
                    ));

                    // Process default body
                    let default_end = self.process_select_case_body(
                        child,
                        source,
                        blocks,
                        edges,
                        block_id,
                        default_block,
                        exits,
                    );

                    edges.push(CFGEdge::unconditional(default_end, merge_block));
                }
                _ => {}
            }
        }

        // If no default and no cases, select blocks forever (deadlock)
        // Add annotation for potential deadlock detection
        if case_count == 0 && !has_default {
            // Empty select {} - blocks forever
            if let Some(block) = blocks.get_mut(&select_block) {
                block.label = "select {} [BLOCKS FOREVER]".to_string();
            }
        }

        merge_block
    }

    /// Analyze a communication_case to determine its type (send or receive).
    fn analyze_communication_case(&self, node: Node, source: &[u8]) -> (String, BlockType) {
        let mut cursor = node.walk();
        let case_text = self
            .node_text(source, node)
            .lines()
            .next()
            .unwrap_or("case")
            .to_string();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "send_statement" => {
                    return (case_text, BlockType::ChannelSend);
                }
                "receive_statement" => {
                    return (case_text, BlockType::ChannelReceive);
                }
                _ => {}
            }
        }

        // Default to SelectCase if we can't determine
        (case_text, BlockType::SelectCase)
    }

    /// Process the body of a select case.
    fn process_select_case_body(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
    ) -> BlockId {
        let mut last_block = current_block;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            // Skip the communication operation itself (already captured in case block)
            if child.kind() == "send_statement"
                || child.kind() == "receive_statement"
                || child.kind() == "case"
                || child.kind() == "default"
                || child.kind() == ":"
            {
                continue;
            }

            // Process statements in the case body
            last_block =
                self.process_cfg_block(child, source, blocks, edges, block_id, last_block, exits);
        }

        last_block
    }

    // =========================================================================
    // Sync primitive detection helpers
    // =========================================================================

    /// Check if a call expression is a sync primitive operation.
    ///
    /// Detects:
    /// - sync.Mutex: Lock(), Unlock(), RLock(), RUnlock()
    /// - sync.WaitGroup: Add(), Done(), Wait()
    /// - sync.Once: Do()
    /// - sync.Pool: Get(), Put()
    ///
    /// Uses PHF map for O(1) method name lookup.
    fn is_sync_primitive_call(&self, node: Node, source: &[u8]) -> Option<SyncPrimitiveOp> {
        if node.kind() != "call_expression" {
            return None;
        }

        let func = self.child_by_field(node, "function")?;
        if func.kind() != "selector_expression" {
            return None;
        }

        let field = self.child_by_field(func, "field")?;
        let method_name = self.node_text(source, field);

        // O(1) PHF lookup instead of sequential match
        SYNC_PRIMITIVE_MAP.get(method_name.as_str()).copied()
    }

    /// Check if a call expression is a context operation.
    ///
    /// Detects:
    /// - ctx.Done()
    /// - ctx.Err()
    /// - ctx.Value()
    /// - ctx.Deadline()
    /// - context.WithCancel(), WithTimeout(), WithDeadline(), WithValue()
    ///
    /// Uses Aho-Corasick for multi-pattern matching on context package functions,
    /// and PHF map for O(1) method name lookup.
    fn is_context_call(&self, node: Node, source: &[u8]) -> Option<ContextOp> {
        if node.kind() != "call_expression" {
            return None;
        }

        let text = self.node_text(source, node);

        // Use Aho-Corasick for efficient multi-pattern matching
        // Check for context.WithCancel/WithTimeout/WithDeadline in single pass
        if CONTEXT_WITH_CANCEL_AC.is_match(&text) {
            return Some(ContextOp::WithCancel);
        }
        // Check for context.WithValue (single pattern, use direct contains)
        if text.contains("context.WithValue") {
            return Some(ContextOp::WithValue);
        }
        // Check for context.Background/TODO in single pass
        if CONTEXT_BACKGROUND_AC.is_match(&text) {
            return Some(ContextOp::Background);
        }

        // Check for method calls on context using PHF map
        let func = self.child_by_field(node, "function")?;
        if func.kind() != "selector_expression" {
            return None;
        }

        let field = self.child_by_field(func, "field")?;
        let method_name = self.node_text(source, field);

        // O(1) PHF lookup instead of sequential match
        CONTEXT_METHOD_MAP.get(method_name.as_str()).copied()
    }

    /// Check if a call expression is make(chan ...) for channel creation.
    fn is_channel_make(&self, node: Node, source: &[u8]) -> Option<ChannelInfo> {
        if node.kind() != "call_expression" {
            return None;
        }

        if let Some(func) = self.child_by_field(node, "function") {
            let func_name = self.node_text(source, func);
            if func_name == "make" {
                if let Some(args) = self.child_by_field(node, "arguments") {
                    let args_text = self.node_text(source, args);
                    if args_text.contains("chan") {
                        // Determine if buffered or unbuffered
                        // make(chan int) - unbuffered
                        // make(chan int, 10) - buffered with size 10
                        let is_buffered = args_text.matches(',').count() >= 1;
                        return Some(ChannelInfo {
                            is_buffered,
                            direction: ChannelDirection::Bidirectional,
                        });
                    }
                }
            }
        }

        None
    }

    /// Check if a call expression is close(ch) for channel close.
    fn is_channel_close(&self, node: Node, source: &[u8]) -> bool {
        if node.kind() != "call_expression" {
            return false;
        }

        if let Some(func) = self.child_by_field(node, "function") {
            let func_name = self.node_text(source, func);
            return func_name == "close";
        }

        false
    }

    /// Find a call_expression in a node tree (recursive).
    fn find_call_in_node<'a>(&self, node: Node<'a>) -> Option<Node<'a>> {
        if node.kind() == "call_expression" {
            return Some(node);
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if let Some(call) = self.find_call_in_node(child) {
                return Some(call);
            }
        }

        None
    }

    /// Check if a node contains a channel receive operation (<-ch).
    ///
    /// Uses AST traversal to find unary_expression nodes with <- operator.
    /// This is more accurate than text-based heuristics.
    fn is_channel_receive_in_node(&self, node: Node, _source: &[u8]) -> bool {
        // Look for unary_expression with receive operator via AST traversal
        fn find_receive(n: Node) -> bool {
            if n.kind() == "unary_expression" {
                // Check for <- operator
                let mut cursor = n.walk();
                for child in n.children(&mut cursor) {
                    if child.kind() == "<-" {
                        return true;
                    }
                }
            }

            let mut cursor = n.walk();
            for child in n.children(&mut cursor) {
                if find_receive(child) {
                    return true;
                }
            }
            false
        }

        find_receive(node)
    }

    // =========================================================================
    // Concurrency issue detection
    // =========================================================================

    /// Analyze CFG for potential concurrency issues.
    ///
    /// Returns a list of detected issues:
    /// - Goroutine leaks (goroutine that might not terminate)
    /// - Channel never closed
    /// - Potential deadlock patterns
    /// - Data race potential (shared variable access without sync)
    #[allow(dead_code)]
    pub fn detect_concurrency_issues(&self, cfg: &CFGInfo) -> Vec<ConcurrencyIssue> {
        let mut issues = Vec::new();

        // Track channel operations
        let mut channel_makes: Vec<(BlockId, String)> = Vec::new();
        let mut channel_closes: Vec<(BlockId, String)> = Vec::new();
        let mut channel_sends: Vec<(BlockId, String)> = Vec::new();
        let mut channel_receives: Vec<(BlockId, String)> = Vec::new();

        // Track sync operations
        let mut mutex_locks: Vec<(BlockId, String)> = Vec::new();
        let mut mutex_unlocks: Vec<(BlockId, String)> = Vec::new();
        let mut wg_adds: Vec<(BlockId, String)> = Vec::new();
        let mut wg_dones: Vec<(BlockId, String)> = Vec::new();
        let mut wg_waits: Vec<(BlockId, String)> = Vec::new();

        // Track goroutine spawns
        let mut goroutine_spawns: Vec<BlockId> = Vec::new();

        // Collect operations from CFG blocks
        for (block_id, block) in &cfg.blocks {
            match block.block_type {
                BlockType::ChannelMake => {
                    channel_makes.push((*block_id, block.label.clone()));
                }
                BlockType::ChannelClose => {
                    channel_closes.push((*block_id, block.label.clone()));
                }
                BlockType::ChannelSend => {
                    channel_sends.push((*block_id, block.label.clone()));
                }
                BlockType::ChannelReceive => {
                    channel_receives.push((*block_id, block.label.clone()));
                }
                BlockType::GoroutineSpawn => {
                    goroutine_spawns.push(*block_id);
                }
                BlockType::MutexLock => {
                    mutex_locks.push((*block_id, block.label.clone()));
                }
                BlockType::MutexUnlock => {
                    mutex_unlocks.push((*block_id, block.label.clone()));
                }
                BlockType::WaitGroupOp => {
                    if block.label.contains("Add") {
                        wg_adds.push((*block_id, block.label.clone()));
                    } else if block.label.contains("Done") {
                        wg_dones.push((*block_id, block.label.clone()));
                    }
                }
                BlockType::WaitGroupWait => {
                    wg_waits.push((*block_id, block.label.clone()));
                }
                _ => {}
            }
        }

        // Issue 1: Channels created but never closed
        // This is a heuristic - some channels don't need to be closed
        if !channel_makes.is_empty() && channel_closes.is_empty() {
            for (block_id, label) in &channel_makes {
                issues.push(ConcurrencyIssue {
                    kind: ConcurrencyIssueKind::ChannelNeverClosed,
                    block_id: *block_id,
                    description: format!(
                        "Channel created at '{}' is never closed. This may leak goroutines waiting on receive.",
                        label
                    ),
                    severity: IssueSeverity::Warning,
                });
            }
        }

        // Issue 2: Unbuffered channel send without receiver in scope
        // This is a deadlock pattern if send is on main goroutine
        if goroutine_spawns.is_empty() && !channel_sends.is_empty() && channel_receives.is_empty() {
            for (block_id, label) in &channel_sends {
                issues.push(ConcurrencyIssue {
                    kind: ConcurrencyIssueKind::PotentialDeadlock,
                    block_id: *block_id,
                    description: format!(
                        "Channel send at '{}' without receiver - potential deadlock on unbuffered channel.",
                        label
                    ),
                    severity: IssueSeverity::Error,
                });
            }
        }

        // Issue 3: Mutex lock without unlock (potential deadlock or leak)
        if mutex_locks.len() > mutex_unlocks.len() {
            let diff = mutex_locks.len() - mutex_unlocks.len();
            issues.push(ConcurrencyIssue {
                kind: ConcurrencyIssueKind::MutexLockWithoutUnlock,
                block_id: mutex_locks.first().map(|(id, _)| *id).unwrap_or(BlockId(0)),
                description: format!(
                    "{} mutex Lock() calls without matching Unlock() - potential deadlock or resource leak.",
                    diff
                ),
                severity: IssueSeverity::Error,
            });
        }

        // Issue 4: WaitGroup.Wait() without Add() (no-op)
        if !wg_waits.is_empty() && wg_adds.is_empty() {
            for (block_id, label) in &wg_waits {
                issues.push(ConcurrencyIssue {
                    kind: ConcurrencyIssueKind::WaitGroupMisuse,
                    block_id: *block_id,
                    description: format!(
                        "WaitGroup.Wait() at '{}' without prior Add() - Wait() will return immediately.",
                        label
                    ),
                    severity: IssueSeverity::Warning,
                });
            }
        }

        // Issue 5: Goroutine spawned without coordination
        // This is very heuristic - not all goroutines need explicit coordination
        if !goroutine_spawns.is_empty() && wg_waits.is_empty() && channel_receives.is_empty() {
            issues.push(ConcurrencyIssue {
                kind: ConcurrencyIssueKind::GoroutineLeak,
                block_id: goroutine_spawns[0],
                description: "Goroutine spawned without WaitGroup or channel coordination - may cause goroutine leak.".to_string(),
                severity: IssueSeverity::Info,
            });
        }

        // Issue 6: Empty select {} (blocks forever)
        for (block_id, block) in &cfg.blocks {
            if block.block_type == BlockType::SelectBlock && block.label.contains("BLOCKS FOREVER")
            {
                issues.push(ConcurrencyIssue {
                    kind: ConcurrencyIssueKind::InfiniteBlock,
                    block_id: *block_id,
                    description:
                        "Empty select {} statement blocks forever - intentional infinite wait."
                            .to_string(),
                    severity: IssueSeverity::Info,
                });
            }
        }

        issues
    }

    /// Build DFG for Go function.
    fn build_go_dfg(&self, node: Node, source: &[u8], func_name: &str) -> DFGInfo {
        let mut edges = Vec::new();
        let mut definitions: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut uses: FxHashMap<String, Vec<usize>> = FxHashMap::default();

        // Extract parameters as definitions
        if let Some(params) = self.child_by_field(node, "parameters") {
            let line = params.start_position().row + 1;
            let mut cursor = params.walk();

            for child in params.children(&mut cursor) {
                if child.kind() == "parameter_declaration" {
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "identifier" {
                            let name = self.node_text(source, inner_child);
                            definitions.entry(name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Param,
                            });
                        }
                    }
                }
            }
        }

        // Process body
        if let Some(body) = self.child_by_field(node, "body") {
            self.extract_dfg_from_block(body, source, &mut edges, &mut definitions, &mut uses);
        }

        DFGInfo::new(func_name.to_string(), edges, definitions, uses)
    }

    /// Extract data flow from a block.
    fn extract_dfg_from_block(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            let line = child.start_position().row + 1;

            match child.kind() {
                "short_var_declaration" => {
                    // x := value or x, y := values (handles multiple return with blanks)
                    if let Some(left) = self.child_by_field(child, "left") {
                        self.extract_definitions_with_blanks(
                            left,
                            source,
                            line,
                            edges,
                            definitions,
                        );
                    }
                    if let Some(right) = self.child_by_field(child, "right") {
                        self.extract_uses(right, source, line, edges, definitions, uses);
                    }
                }
                "assignment_statement" => {
                    // x = value or x += value etc.
                    if let Some(left) = self.child_by_field(child, "left") {
                        self.extract_definitions_with_blanks(
                            left,
                            source,
                            line,
                            edges,
                            definitions,
                        );
                    }
                    if let Some(right) = self.child_by_field(child, "right") {
                        self.extract_uses(right, source, line, edges, definitions, uses);
                    }
                }
                "var_declaration" => {
                    // var x type = value
                    self.extract_var_declaration(child, source, line, edges, definitions, uses);
                }
                "return_statement" => {
                    // Extract uses from return value
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "expression_list" {
                            self.extract_uses(inner_child, source, line, edges, definitions, uses);
                        }
                    }
                }
                // FEATURE 1: Goroutine detection
                "go_statement" => {
                    self.extract_goroutine_dfg(child, source, line, edges, definitions, uses);
                }
                // FEATURE 2: Channel send operation
                "send_statement" => {
                    self.extract_channel_send_dfg(child, source, line, edges, definitions, uses);
                }
                // FEATURE 3: Defer statement
                "defer_statement" => {
                    self.extract_defer_dfg(child, source, line, edges, definitions, uses);
                }
                "for_statement" => {
                    // Handle range clause to extract loop variables as definitions
                    // This fixes the bug where for-range variables (i, v in "for i, v := range items")
                    // were not tracked, causing uses inside the loop to have no matching definitions
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "range_clause" {
                            let range_line = inner_child.start_position().row + 1;

                            // Extract loop variables from left side of range clause
                            // Handles: for i := range, for i, v := range, for _, v := range
                            if let Some(left) = self.child_by_field(inner_child, "left") {
                                self.extract_definitions_with_blanks(
                                    left,
                                    source,
                                    range_line,
                                    edges,
                                    definitions,
                                );
                            }

                            // Extract uses from the range expression (the iterable)
                            if let Some(right) = self.child_by_field(inner_child, "right") {
                                self.extract_uses(
                                    right,
                                    source,
                                    range_line,
                                    edges,
                                    definitions,
                                    uses,
                                );
                            }
                        }
                    }
                    // Process loop body and any nested control flow
                    self.extract_dfg_from_block(child, source, edges, definitions, uses);
                }
                "if_statement"
                | "expression_switch_statement"
                | "type_switch_statement"
                | "select_statement" => {
                    self.extract_dfg_from_block(child, source, edges, definitions, uses);
                }
                "block" | "statement_list" => {
                    self.extract_dfg_from_block(child, source, edges, definitions, uses);
                }
                "expression_statement" | "call_expression" => {
                    self.extract_uses(child, source, line, edges, definitions, uses);
                }
                _ => {}
            }
        }
    }

    /// Extract variable definitions.
    fn extract_definitions(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(source, node);
                if !name.is_empty() && name != "_" {
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Definition,
                    });
                }
            }
            "expression_list" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.extract_definitions(child, source, line, edges, definitions);
                }
            }
            _ => {}
        }
    }

    /// Extract variable uses and create flow edges.
    fn extract_uses(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(source, node);
                if !name.is_empty() && name != "_" {
                    uses.entry(name.clone()).or_default().push(line);

                    // Create edge from most recent definition
                    if let Some(def_lines) = definitions.get(&name) {
                        if let Some(&def_line) = def_lines.last() {
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: def_line,
                                to_line: line,
                                kind: DataflowKind::Use,
                            });
                        }
                    }
                }
            }
            // FEATURE 2: Channel receive expression (<-ch)
            "unary_expression" => {
                // Check if this is a channel receive operation
                let text = self.node_text(source, node);
                if text.starts_with("<-") {
                    self.extract_channel_receive_dfg(node, source, line, edges, definitions, uses);
                } else {
                    // Regular unary expression - process operand
                    let mut cursor = node.walk();
                    for child in node.children(&mut cursor) {
                        self.extract_uses(child, source, line, edges, definitions, uses);
                    }
                }
            }
            // FEATURE 4: Type assertion (x.(Type))
            "type_assertion_expression" => {
                self.extract_type_assertion_dfg(node, source, line, edges, definitions, uses);
            }
            _ => {
                // Recursively process children
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.extract_uses(child, source, line, edges, definitions, uses);
                }
            }
        }
    }

    /// Extract var declaration.
    fn extract_var_declaration(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "var_spec" {
                // Extract name(s)
                if let Some(name_node) = self.child_by_field(child, "name") {
                    self.extract_definitions(name_node, source, line, edges, definitions);
                }
                // Extract value uses
                if let Some(value_node) = self.child_by_field(child, "value") {
                    self.extract_uses(value_node, source, line, edges, definitions, uses);
                }
            }
        }
    }

    // =========================================================================
    // FEATURE 5: Blank identifier handling for multiple return values
    // =========================================================================

    /// Extract variable definitions with proper blank identifier handling.
    /// Handles: x, _ := f() or _, y, _ := g()
    fn extract_definitions_with_blanks(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(source, node);
                // Skip blank identifier - it intentionally discards value
                if !name.is_empty() && name != "_" {
                    definitions.entry(name.clone()).or_default().push(line);
                    edges.push(DataflowEdge {
                        variable: name,
                        from_line: line,
                        to_line: line,
                        kind: DataflowKind::Definition,
                    });
                }
                // Note: blank identifier "_" is intentionally not tracked
            }
            "blank_identifier" => {
                // Explicitly handle blank identifier node type - do nothing
                // The blank identifier discards the value at this position
            }
            "expression_list" => {
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.extract_definitions_with_blanks(child, source, line, edges, definitions);
                }
            }
            _ => {}
        }
    }

    // =========================================================================
    // FEATURE 1: Goroutine detection
    // =========================================================================

    /// Extract DFG for goroutine statement (go func() { ... }).
    /// Tracks variables captured/used by the goroutine.
    fn extract_goroutine_dfg(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            // go func() { body } or go existingFunc(args)
            if child.kind() == "call_expression" {
                // Extract variables used in goroutine - mark them as captured
                self.extract_goroutine_captures(child, source, line, edges, definitions, uses);
            }
        }
    }

    /// Extract variables captured by a goroutine.
    fn extract_goroutine_captures(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "identifier" => {
                let name = self.node_text(source, node);
                if !name.is_empty() && name != "_" {
                    uses.entry(name.clone()).or_default().push(line);

                    // Create edge from most recent definition, marked as goroutine capture
                    if let Some(def_lines) = definitions.get(&name) {
                        if let Some(&def_line) = def_lines.last() {
                            edges.push(DataflowEdge {
                                variable: name,
                                from_line: def_line,
                                to_line: line,
                                kind: DataflowKind::Goroutine,
                            });
                        }
                    }
                }
            }
            "func_literal" => {
                // For anonymous functions: go func() { body }
                // Process the function body for captured variables
                if let Some(body) = self.child_by_field(node, "body") {
                    self.extract_goroutine_captures(body, source, line, edges, definitions, uses);
                }
            }
            _ => {
                // Recursively process children
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    self.extract_goroutine_captures(child, source, line, edges, definitions, uses);
                }
            }
        }
    }

    // =========================================================================
    // FEATURE 2: Channel operations
    // =========================================================================

    /// Extract DFG for channel send statement (ch <- val).
    fn extract_channel_send_dfg(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // send_statement: channel <- value
        if let Some(channel) = self.child_by_field(node, "channel") {
            let ch_name = self.node_text(source, channel);
            if !ch_name.is_empty() && ch_name != "_" {
                uses.entry(ch_name.clone()).or_default().push(line);

                // Track channel send operation
                if let Some(def_lines) = definitions.get(&ch_name) {
                    if let Some(&def_line) = def_lines.last() {
                        edges.push(DataflowEdge {
                            variable: ch_name,
                            from_line: def_line,
                            to_line: line,
                            kind: DataflowKind::ChannelSend,
                        });
                    }
                }
            }
        }

        // Extract uses from the value being sent
        if let Some(value) = self.child_by_field(node, "value") {
            self.extract_uses(value, source, line, edges, definitions, uses);
        }
    }

    /// Extract DFG for channel receive expression (<-ch).
    /// Called from extract_uses when encountering unary_expression with <- operator.
    fn extract_channel_receive_dfg(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // unary_expression with <- operator: <-ch
        if let Some(operand) = self.child_by_field(node, "operand") {
            let ch_name = self.node_text(source, operand);
            if !ch_name.is_empty() && ch_name != "_" {
                uses.entry(ch_name.clone()).or_default().push(line);

                if let Some(def_lines) = definitions.get(&ch_name) {
                    if let Some(&def_line) = def_lines.last() {
                        edges.push(DataflowEdge {
                            variable: ch_name,
                            from_line: def_line,
                            to_line: line,
                            kind: DataflowKind::ChannelReceive,
                        });
                    }
                }
            }
        }
    }

    // =========================================================================
    // FEATURE 3: Defer statement tracking
    // =========================================================================

    /// Extract DFG for defer statement (defer f()).
    /// Important for resource cleanup analysis.
    fn extract_defer_dfg(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // defer statement contains a call expression
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "call_expression" {
                // Extract function name and arguments
                self.extract_defer_call(child, source, line, edges, definitions, uses);
            }
        }
    }

    /// Extract deferred call details.
    fn extract_defer_call(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // Extract function being deferred
        if let Some(func) = self.child_by_field(node, "function") {
            let func_name = self.node_text(source, func);
            if !func_name.is_empty() {
                // Track the deferred function/method
                edges.push(DataflowEdge {
                    variable: func_name,
                    from_line: line,
                    to_line: line,
                    kind: DataflowKind::Defer,
                });
            }
        }

        // Extract arguments - these are captured at defer time
        if let Some(args) = self.child_by_field(node, "arguments") {
            let mut cursor = args.walk();
            for child in args.children(&mut cursor) {
                self.extract_uses(child, source, line, edges, definitions, uses);
            }
        }
    }

    // =========================================================================
    // FEATURE 4: Type assertion handling
    // =========================================================================

    /// Extract DFG for type assertion (x.(Type)).
    fn extract_type_assertion_dfg(
        &self,
        node: Node,
        source: &[u8],
        line: usize,
        edges: &mut Vec<DataflowEdge>,
        definitions: &FxHashMap<String, Vec<usize>>,
        uses: &mut FxHashMap<String, Vec<usize>>,
    ) {
        // type_assertion_expression: operand.(type)
        if let Some(operand) = self.child_by_field(node, "operand") {
            let var_name = self.node_text(source, operand);
            if !var_name.is_empty() && var_name != "_" {
                uses.entry(var_name.clone()).or_default().push(line);

                if let Some(def_lines) = definitions.get(&var_name) {
                    if let Some(&def_line) = def_lines.last() {
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: def_line,
                            to_line: line,
                            kind: DataflowKind::TypeAssertion,
                        });
                    }
                }
            }
        }
    }

    // =========================================================================
    // CFG Helper Methods for error check patterns
    // =========================================================================

    /// Check if an if statement is a Go error check pattern: if err != nil
    ///
    /// Common patterns:
    /// - if err != nil { return err }
    /// - if err != nil { return fmt.Errorf("...") }
    /// - if err == nil { ... } else { ... }
    ///
    /// Uses Aho-Corasick for efficient multi-pattern matching in single pass.
    fn is_error_check_pattern(&self, node: Node, source: &[u8]) -> bool {
        if node.kind() != "if_statement" {
            return false;
        }

        if let Some(condition) = self.child_by_field(node, "condition") {
            let cond_text = self.node_text(source, condition);
            // Aho-Corasick matches all 4 patterns in single pass
            ERROR_CHECK_AC.is_match(&cond_text)
        } else {
            false
        }
    }

    /// Process error check pattern: if err != nil { return ... }
    ///
    /// Creates a dedicated ErrorCheck block with ErrorPath and SuccessPath edges.
    fn process_error_check_cfg(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        defer_stack: &mut Vec<BlockId>,
        panic_sites: &mut Vec<BlockId>,
        return_blocks: &mut Vec<BlockId>,
        decision_points: &mut usize,
    ) -> BlockId {
        *decision_points += 1;

        // Error check condition block
        *block_id += 1;
        let check_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(source, n))
            .unwrap_or_else(|| "err != nil".to_string());

        blocks.insert(
            check_block,
            CFGBlock {
                id: check_block,
                label: format!("error_check: {}", condition),
                block_type: BlockType::ErrorCheck,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(current_block, check_block));

        // Error path (err != nil -> true branch)
        *block_id += 1;
        let error_block = BlockId(*block_id);
        blocks.insert(
            error_block,
            CFGBlock {
                id: error_block,
                label: "error_path".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::new(check_block, error_block, EdgeType::ErrorPath));

        let error_end = if let Some(consequence) = self.child_by_field(node, "consequence") {
            self.process_cfg_block_with_defer(
                consequence,
                source,
                blocks,
                edges,
                block_id,
                error_block,
                exits,
                defer_stack,
                panic_sites,
                return_blocks,
                decision_points,
            )
        } else {
            error_block
        };

        // Success path (err == nil -> false branch / continue)
        let success_end = if let Some(alternative) = self.child_by_field(node, "alternative") {
            *block_id += 1;
            let success_block = BlockId(*block_id);
            blocks.insert(
                success_block,
                CFGBlock {
                    id: success_block,
                    label: "success_path".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: alternative.start_position().row + 1,
                    end_line: alternative.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::new(
                check_block,
                success_block,
                EdgeType::SuccessPath,
            ));

            self.process_cfg_block_with_defer(
                alternative,
                source,
                blocks,
                edges,
                block_id,
                success_block,
                exits,
                defer_stack,
                panic_sites,
                return_blocks,
                decision_points,
            )
        } else {
            // No else - success path continues (implicit)
            check_block
        };

        // Merge block
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "error_merge".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(error_end, merge_block));
        if success_end != check_block {
            edges.push(CFGEdge::unconditional(success_end, merge_block));
        } else {
            // No else branch - connect check directly to merge for success path
            edges.push(CFGEdge::new(
                check_block,
                merge_block,
                EdgeType::SuccessPath,
            ));
        }

        merge_block
    }

    /// Process if statement with panic tracking.
    ///
    /// This version properly tracks panic sites inside if branches.
    fn process_if_cfg_tracking_panic(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut FxHashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        block_id: &mut usize,
        current_block: BlockId,
        exits: &mut Vec<BlockId>,
        defer_stack: &mut Vec<BlockId>,
        panic_sites: &mut Vec<BlockId>,
        return_blocks: &mut Vec<BlockId>,
        decision_points: &mut usize,
    ) -> BlockId {
        // Condition block
        *block_id += 1;
        let cond_block = BlockId(*block_id);
        let condition = self
            .child_by_field(node, "condition")
            .map(|n| self.node_text(source, n))
            .unwrap_or_else(|| "condition".to_string());

        blocks.insert(
            cond_block,
            CFGBlock {
                id: cond_block,
                label: format!("if {}", condition),
                block_type: BlockType::Branch,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(current_block, cond_block));

        // True branch
        *block_id += 1;
        let true_block = BlockId(*block_id);
        blocks.insert(
            true_block,
            CFGBlock {
                id: true_block,
                label: "then".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::new(cond_block, true_block, EdgeType::True));

        let true_end = if let Some(consequence) = self.child_by_field(node, "consequence") {
            self.process_cfg_block_with_defer(
                consequence,
                source,
                blocks,
                edges,
                block_id,
                true_block,
                exits,
                defer_stack,
                panic_sites,
                return_blocks,
                decision_points,
            )
        } else {
            true_block
        };

        // False/else branch
        let false_end = if let Some(alternative) = self.child_by_field(node, "alternative") {
            *block_id += 1;
            let false_block = BlockId(*block_id);
            blocks.insert(
                false_block,
                CFGBlock {
                    id: false_block,
                    label: "else".to_string(),
                    block_type: BlockType::Body,
                    statements: Vec::new(),
                    func_calls: Vec::new(),
                    start_line: alternative.start_position().row + 1,
                    end_line: alternative.end_position().row + 1,
                },
            );

            edges.push(CFGEdge::new(cond_block, false_block, EdgeType::False));

            self.process_cfg_block_with_defer(
                alternative,
                source,
                blocks,
                edges,
                block_id,
                false_block,
                exits,
                defer_stack,
                panic_sites,
                return_blocks,
                decision_points,
            )
        } else {
            cond_block
        };

        // Merge block
        *block_id += 1;
        let merge_block = BlockId(*block_id);
        blocks.insert(
            merge_block,
            CFGBlock {
                id: merge_block,
                label: "endif".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        edges.push(CFGEdge::unconditional(true_end, merge_block));
        edges.push(CFGEdge::unconditional(false_end, merge_block));

        merge_block
    }
}

impl Language for Go {
    fn name(&self) -> &'static str {
        "go"
    }

    fn extensions(&self) -> &[&'static str] {
        &[".go"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_go::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        match node.kind() {
            "function_declaration" => {
                // func Name(params) ReturnType
                let name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(source, n))?;

                let params = self
                    .child_by_field(node, "parameters")
                    .map(|n| self.extract_param_list(n, source))
                    .unwrap_or_default();

                let return_type = self
                    .child_by_field(node, "result")
                    .and_then(|n| self.extract_return_type(n, source));

                let docstring = self.get_doc_comment(node, source);

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: false,
                    is_async: false,        // Go doesn't have async keyword
                    decorators: Vec::new(), // Go doesn't have decorators
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "go".to_string(),
                })
            }
            "method_declaration" => {
                // func (receiver Type) Name(params) ReturnType
                let name = self
                    .child_by_field(node, "name")
                    .map(|n| self.node_text(source, n))?;

                // Get parameters (second parameter_list, not receiver)
                let params = self
                    .child_by_field(node, "parameters")
                    .map(|n| self.extract_param_list(n, source))
                    .unwrap_or_default();

                let return_type = self
                    .child_by_field(node, "result")
                    .and_then(|n| self.extract_return_type(n, source));

                let docstring = self.get_doc_comment(node, source);

                // Extract receiver info for decorators (to preserve receiver type info)
                let mut decorators = Vec::new();
                if let Some((recv_name, recv_type)) = self.extract_receiver(node, source) {
                    let recv_str = if recv_name.is_empty() {
                        recv_type
                    } else {
                        format!("{} {}", recv_name, recv_type)
                    };
                    decorators.push(format!("receiver:{}", recv_str));
                }

                Some(FunctionInfo {
                    name,
                    params,
                    return_type,
                    docstring,
                    is_method: true,
                    is_async: false,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "go".to_string(),
                })
            }
            _ => None,
        }
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        // Go uses struct types - extract from type_declaration
        if node.kind() != "type_declaration" {
            return None;
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "type_spec" {
                let name = self
                    .child_by_field(child, "name")
                    .map(|n| self.node_text(source, n))?;

                // Check if it's a struct type
                let type_node = self.child_by_field(child, "type")?;
                if type_node.kind() != "struct_type" && type_node.kind() != "interface_type" {
                    return None;
                }

                let docstring = self.get_doc_comment(node, source);

                // Extract interface methods if it's an interface type
                let methods = if type_node.kind() == "interface_type" {
                    self.extract_interface_methods(type_node, source)
                } else {
                    Vec::new()
                };

                // Extract embedded types as bases (works for both interfaces and structs)
                let bases = match type_node.kind() {
                    "interface_type" => self.extract_embedded_interfaces(type_node, source),
                    "struct_type" => self.extract_struct_embedded_types(type_node, source),
                    _ => Vec::new(),
                };

                return Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods,
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators: Vec::new(),
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "go".to_string(),
                });
            }
        }

        None
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "import_declaration" {
                self.extract_import_declaration(child, source, &mut imports);
            }
        }

        imports
    }

    fn function_query(&self) -> &'static str {
        r#"[
            (function_declaration name: (identifier) @name) @function
            (method_declaration name: (field_identifier) @name) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        // Match both struct and interface type declarations
        r#"[
            (type_declaration (type_spec name: (type_identifier) @name type: (struct_type))) @struct
            (type_declaration (type_spec name: (type_identifier) @name type: (interface_type))) @interface
        ]"#
    }

    fn call_query(&self) -> &'static str {
        r#"[
            (call_expression function: (identifier) @callee) @call
            (call_expression function: (selector_expression field: (field_identifier) @callee)) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        let func_name = match node.kind() {
            "function_declaration" => self
                .child_by_field(node, "name")
                .map(|n| self.node_text(source, n))
                .unwrap_or_else(|| "anonymous".to_string()),
            "method_declaration" => self
                .child_by_field(node, "name")
                .map(|n| self.node_text(source, n))
                .unwrap_or_else(|| "anonymous".to_string()),
            _ => {
                return Err(BrrrError::UnsupportedLanguage(
                    "Node is not a function or method".to_string(),
                ))
            }
        };

        Ok(self.build_go_cfg(node, source, &func_name))
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        let func_name = match node.kind() {
            "function_declaration" => self
                .child_by_field(node, "name")
                .map(|n| self.node_text(source, n))
                .unwrap_or_else(|| "anonymous".to_string()),
            "method_declaration" => self
                .child_by_field(node, "name")
                .map(|n| self.node_text(source, n))
                .unwrap_or_else(|| "anonymous".to_string()),
            _ => {
                return Err(BrrrError::UnsupportedLanguage(
                    "Node is not a function or method".to_string(),
                ))
            }
        };

        Ok(self.build_go_dfg(node, source, &func_name))
    }
}

impl Go {
    /// Extract methods from interface type.
    fn extract_interface_methods(&self, node: Node, source: &[u8]) -> Vec<FunctionInfo> {
        let mut methods = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            // In Go interface, methods are defined as method_elem (tree-sitter-go)
            if child.kind() == "method_elem" {
                if let Some(method) = self.extract_interface_method(child, source) {
                    methods.push(method);
                }
            }
        }

        methods
    }

    /// Extract a single interface method.
    fn extract_interface_method(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let name = self
            .child_by_field(node, "name")
            .map(|n| self.node_text(source, n))?;

        let params = self
            .child_by_field(node, "parameters")
            .map(|n| self.extract_param_list(n, source))
            .unwrap_or_default();

        let return_type = self
            .child_by_field(node, "result")
            .and_then(|n| self.extract_return_type(n, source));

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring: None,
            is_method: true,
            is_async: false,
            decorators: Vec::new(),
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "go".to_string(),
        })
    }

    /// Extract embedded interfaces (for interface composition).
    /// Tree-sitter-go wraps embedded types in type_elem nodes.
    fn extract_embedded_interfaces(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut embedded = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                // Tree-sitter-go wraps embedded interfaces in type_elem nodes
                "type_elem" => {
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "type_identifier"
                            || inner_child.kind() == "qualified_type"
                        {
                            embedded.push(self.node_text(source, inner_child));
                        }
                    }
                }
                // Direct type references (fallback for older tree-sitter versions)
                "type_identifier" | "qualified_type" => {
                    embedded.push(self.node_text(source, child));
                }
                _ => {}
            }
        }

        embedded
    }

    /// Extract embedded types from struct (for struct composition).
    /// In Go, embedded fields in structs are fields without explicit names.
    fn extract_struct_embedded_types(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut embedded = Vec::new();
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            if child.kind() == "field_declaration_list" {
                let mut inner_cursor = child.walk();
                for field in child.children(&mut inner_cursor) {
                    if field.kind() == "field_declaration" {
                        // Embedded fields have no name, only a type
                        // Check if this is an embedded field (no identifier children)
                        let has_name = field
                            .children(&mut field.walk())
                            .any(|c| c.kind() == "field_identifier");

                        if !has_name {
                            // This is an embedded type - extract the type
                            let mut field_cursor = field.walk();
                            for field_child in field.children(&mut field_cursor) {
                                match field_child.kind() {
                                    "type_identifier" | "qualified_type" | "pointer_type" => {
                                        embedded.push(self.node_text(source, field_child));
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
        }

        embedded
    }

    /// Extract import declarations.
    fn extract_import_declaration(&self, node: Node, source: &[u8], imports: &mut Vec<ImportInfo>) {
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "import_spec" => {
                    if let Some(import) = self.extract_import_spec(child, source) {
                        imports.push(import);
                    }
                }
                "import_spec_list" => {
                    // Grouped imports: import ( ... )
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "import_spec" {
                            if let Some(import) = self.extract_import_spec(inner_child, source) {
                                imports.push(import);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Extract a single import spec.
    fn extract_import_spec(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        let mut alias_name: Option<String> = None;
        let mut path: Option<String> = None;
        let mut cursor = node.walk();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "package_identifier" => {
                    // Alias: import alias "path"
                    alias_name = Some(self.node_text(source, child));
                }
                "interpreted_string_literal" => {
                    // Path: "github.com/user/pkg"
                    let text = self.node_text(source, child);
                    // Remove quotes
                    path = Some(text.trim_matches('"').to_string());
                }
                "blank_identifier" => {
                    // Blank import: import _ "path"
                    alias_name = Some("_".to_string());
                }
                "dot" => {
                    // Dot import: import . "path"
                    alias_name = Some(".".to_string());
                }
                _ => {}
            }
        }

        let module = path?;
        let mut aliases = FxHashMap::default();

        if let Some(alias) = alias_name {
            aliases.insert(module.clone(), alias);
        }

        Some(ImportInfo {
            module,
            names: Vec::new(), // Go imports whole packages
            aliases,
            is_from: false, // Go doesn't have "from X import Y" syntax
            level: 0,       // Go doesn't have relative imports
            line_number: node.start_position().row + 1,
            visibility: None, // Go doesn't have visibility modifiers on imports
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_go(source: &str) -> (Tree, Vec<u8>) {
        let go = Go;
        let mut parser = go.parser().unwrap();
        let source_bytes = source.as_bytes().to_vec();
        let tree = parser.parse(&source_bytes, None).unwrap();
        (tree, source_bytes)
    }

    #[test]
    fn test_extract_simple_function() {
        let source = r#"
package main

// SayHello greets someone
func SayHello(name string) string {
    return "Hello, " + name
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        // Find function_declaration
        let mut found = false;
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let func = go.extract_function(child, &source_bytes);
                assert!(func.is_some());
                let func = func.unwrap();
                assert_eq!(func.name, "SayHello");
                assert_eq!(func.params, vec!["name string"]);
                assert_eq!(func.return_type, Some("string".to_string()));
                assert!(!func.is_method);
                assert_eq!(func.language, "go");
                found = true;
            }
        }
        assert!(found, "Function declaration not found");
    }

    #[test]
    fn test_extract_method() {
        let source = r#"
package main

func (p *Person) Greet() string {
    return "Hi, I'm " + p.Name
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "method_declaration" {
                let func = go.extract_function(child, &source_bytes);
                assert!(func.is_some());
                let func = func.unwrap();
                assert_eq!(func.name, "Greet");
                assert!(func.is_method);
                assert!(func.decorators.iter().any(|d| d.starts_with("receiver:")));
                assert_eq!(func.return_type, Some("string".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_multiple_returns() {
        let source = r#"
package main

func MultiReturn() (int, error) {
    return 42, nil
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let func = go.extract_function(child, &source_bytes);
                assert!(func.is_some());
                let func = func.unwrap();
                assert_eq!(func.name, "MultiReturn");
                assert_eq!(func.return_type, Some("(int, error)".to_string()));
            }
        }
    }

    #[test]
    fn test_extract_named_returns() {
        let source = r#"
package main

func NamedReturn() (result string, err error) {
    result = "hello"
    return
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let func = go.extract_function(child, &source_bytes);
                assert!(func.is_some());
                let func = func.unwrap();
                assert_eq!(func.name, "NamedReturn");
                assert_eq!(
                    func.return_type,
                    Some("(result string, err error)".to_string())
                );
            }
        }
    }

    #[test]
    fn test_extract_struct() {
        let source = r#"
package main

// Person represents a human
type Person struct {
    Name string
    Age  int
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let cls = go.extract_class(child, &source_bytes);
                assert!(cls.is_some());
                let cls = cls.unwrap();
                assert_eq!(cls.name, "Person");
                assert_eq!(cls.language, "go");
            }
        }
    }

    #[test]
    fn test_extract_imports() {
        let source = r#"
package main

import (
    "fmt"
    "os"
)

import "strings"
import alias "io"
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let imports = go.extract_imports(&tree, &source_bytes);

        assert_eq!(imports.len(), 4);

        // Check grouped imports
        assert!(imports.iter().any(|i| i.module == "fmt"));
        assert!(imports.iter().any(|i| i.module == "os"));

        // Check single import
        assert!(imports.iter().any(|i| i.module == "strings"));

        // Check aliased import
        let alias_import = imports.iter().find(|i| i.module == "io").unwrap();
        assert_eq!(alias_import.aliases.get("io"), Some(&"alias".to_string()));
    }

    #[test]
    fn test_function_signature() {
        let func = FunctionInfo {
            name: "Process".to_string(),
            params: vec!["ctx context.Context".to_string(), "data []byte".to_string()],
            return_type: Some("(int, error)".to_string()),
            docstring: None,
            is_method: false,
            is_async: false,
            decorators: Vec::new(),
            line_number: 1,
            end_line_number: Some(5),
            language: "go".to_string(),
        };

        assert_eq!(
            func.signature(),
            "func Process(ctx context.Context, data []byte) (int, error)"
        );
    }

    // =========================================================================
    // FEATURE 1: Goroutine detection tests
    // =========================================================================

    #[test]
    fn test_goroutine_cfg() {
        let source = r#"
package main

func worker() {
    go func() {
        process()
    }()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                // Check for goroutine block label
                let has_goroutine_block = cfg
                    .blocks
                    .values()
                    .any(|b| b.label.starts_with("goroutine:"));
                assert!(has_goroutine_block, "CFG should contain goroutine block");

                // Check for spawn edge
                let has_spawn_edge = cfg.edges.iter().any(|e| e.label() == "spawn");
                assert!(has_spawn_edge, "CFG should have spawn edge for goroutine");
            }
        }
    }

    #[test]
    fn test_goroutine_dfg_captures() {
        let source = r#"
package main

func worker() {
    x := 10
    go func() {
        println(x)
    }()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();
                // Check that x is captured by goroutine
                let has_goroutine_capture = dfg
                    .edges
                    .iter()
                    .any(|e| e.variable == "x" && e.kind == DataflowKind::Goroutine);
                assert!(
                    has_goroutine_capture,
                    "DFG should mark x as goroutine capture"
                );
            }
        }
    }

    // =========================================================================
    // FEATURE 2: Channel operations tests
    // =========================================================================

    #[test]
    fn test_channel_send_cfg() {
        let source = r#"
package main

func sender(ch chan int) {
    ch <- 42
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                // Check for channel send block
                let has_send_block = cfg.blocks.values().any(|b| b.label.starts_with("chan<-:"));
                assert!(has_send_block, "CFG should contain channel send block");

                // Check for send edge
                let has_send_edge = cfg.edges.iter().any(|e| e.label() == "send");
                assert!(has_send_edge, "CFG should have send edge");
            }
        }
    }

    #[test]
    fn test_channel_send_dfg() {
        let source = r#"
package main

func sender() {
    ch := make(chan int)
    val := 42
    ch <- val
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();
                // Check for channel send tracking
                let has_channel_send = dfg
                    .edges
                    .iter()
                    .any(|e| e.variable == "ch" && e.kind == DataflowKind::ChannelSend);
                assert!(has_channel_send, "DFG should track channel send");

                // val should be used in the send
                let has_val_use = dfg.edges.iter().any(|e| e.variable == "val");
                assert!(has_val_use, "DFG should track value used in send");
            }
        }
    }

    #[test]
    fn test_channel_receive_dfg() {
        let source = r#"
package main

func receiver() {
    ch := make(chan int)
    x := <-ch
    println(x)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();
                // Check for channel receive tracking
                let has_channel_receive = dfg
                    .edges
                    .iter()
                    .any(|e| e.variable == "ch" && e.kind == DataflowKind::ChannelReceive);
                assert!(has_channel_receive, "DFG should track channel receive");
            }
        }
    }

    // =========================================================================
    // FEATURE 3: Defer statement tests
    // =========================================================================

    #[test]
    fn test_defer_cfg() {
        let source = r#"
package main

func cleanup() {
    defer closeFile()
    process()
    return
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                // Check for defer block - now uses BlockType
                let has_defer_block = cfg.blocks.values().any(|b| {
                    b.block_type == BlockType::DeferredCall || b.label.starts_with("defer:")
                });
                assert!(has_defer_block, "CFG should contain defer block");

                // Check for defer edge
                let has_defer_edge = cfg.edges.iter().any(|e| e.edge_type == EdgeType::Defer);
                assert!(has_defer_edge, "CFG should have defer edge");
            }
        }
    }

    #[test]
    fn test_defer_dfg() {
        let source = r#"
package main

func cleanup() {
    f := openFile()
    defer f.Close()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();
                // Check for defer tracking
                let has_defer = dfg.edges.iter().any(|e| e.kind == DataflowKind::Defer);
                assert!(has_defer, "DFG should track defer calls");
            }
        }
    }

    // =========================================================================
    // FEATURE 4: Type assertion tests
    // =========================================================================

    #[test]
    fn test_type_assertion_dfg() {
        let source = r#"
package main

func typeAssert(v interface{}) {
    s := v.(string)
    println(s)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();
                // Check for type assertion tracking
                let has_type_assertion = dfg
                    .edges
                    .iter()
                    .any(|e| e.variable == "v" && e.kind == DataflowKind::TypeAssertion);
                assert!(has_type_assertion, "DFG should track type assertion");
            }
        }
    }

    #[test]
    fn test_type_switch_cfg() {
        let source = r#"
package main

func typeSwitch(v interface{}) {
    switch x := v.(type) {
    case int:
        println(x)
    case string:
        println(x)
    default:
        println("unknown")
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                // Type switch should create multiple case blocks
                let case_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.label.starts_with("case") || b.label.starts_with("default"))
                    .collect();
                assert!(
                    case_blocks.len() >= 2,
                    "Type switch should have multiple case blocks"
                );
            }
        }
    }

    // =========================================================================
    // FEATURE 5: Blank identifier handling tests
    // =========================================================================

    #[test]
    fn test_blank_identifier_multiple_return() {
        let source = r#"
package main

func multiReturn() (int, string, error) {
    return 1, "test", nil
}

func useBlank() {
    x, _, err := multiReturn()
    println(x, err)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let name_node = go.child_by_field(child, "name");
                if let Some(n) = name_node {
                    let name = go.node_text(&source_bytes, n);
                    if name == "useBlank" {
                        let dfg = go.build_dfg(child, &source_bytes).unwrap();

                        // x should be defined
                        assert!(dfg.definitions.contains_key("x"), "x should be defined");

                        // err should be defined
                        assert!(dfg.definitions.contains_key("err"), "err should be defined");

                        // Blank identifier should NOT be tracked
                        assert!(
                            !dfg.definitions.contains_key("_"),
                            "Blank identifier should not be tracked"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_blank_identifier_for_range() {
        let source = r#"
package main

func rangeWithBlank() {
    items := []int{1, 2, 3}
    for _, v := range items {
        println(v)
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();

                // Blank identifier should NOT be tracked as a definition
                assert!(
                    !dfg.definitions.contains_key("_"),
                    "Blank identifier should not be tracked in range"
                );

                // But v SHOULD be tracked as a definition (this was the bug)
                assert!(
                    dfg.definitions.contains_key("v"),
                    "Loop variable v should be tracked as definition"
                );
            }
        }
    }

    // =========================================================================
    // For-range loop variable tracking tests (bug fix verification)
    // =========================================================================

    #[test]
    fn test_for_range_single_variable() {
        // Test: for i := range slice {}
        let source = r#"
package main

func singleVar() {
    items := []int{1, 2, 3}
    for i := range items {
        println(i)
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();

                // i should be tracked as a definition
                assert!(
                    dfg.definitions.contains_key("i"),
                    "Single loop variable i should be tracked as definition"
                );

                // items should be tracked as a use in the range expression
                assert!(
                    dfg.uses.contains_key("items"),
                    "Range expression 'items' should be tracked as use"
                );
            }
        }
    }

    #[test]
    fn test_for_range_dual_variables() {
        // Test: for i, v := range slice {}
        let source = r#"
package main

func dualVar() {
    items := []int{1, 2, 3}
    for i, v := range items {
        println(i, v)
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();

                // Both i and v should be tracked as definitions
                assert!(
                    dfg.definitions.contains_key("i"),
                    "Loop variable i should be tracked as definition"
                );
                assert!(
                    dfg.definitions.contains_key("v"),
                    "Loop variable v should be tracked as definition"
                );

                // items should be tracked as a use
                assert!(
                    dfg.uses.contains_key("items"),
                    "Range expression 'items' should be tracked as use"
                );

                // i and v should have dataflow edges from their definitions to uses in println
                let i_use_edges: Vec<_> = dfg
                    .edges
                    .iter()
                    .filter(|e| e.variable == "i" && e.kind == DataflowKind::Use)
                    .collect();
                assert!(
                    !i_use_edges.is_empty(),
                    "Should have use edge for i inside loop body"
                );

                let v_use_edges: Vec<_> = dfg
                    .edges
                    .iter()
                    .filter(|e| e.variable == "v" && e.kind == DataflowKind::Use)
                    .collect();
                assert!(
                    !v_use_edges.is_empty(),
                    "Should have use edge for v inside loop body"
                );
            }
        }
    }

    #[test]
    fn test_for_range_map_iteration() {
        // Test: for k, v := range mapVar {}
        let source = r#"
package main

func mapRange() {
    m := make(map[string]int)
    for k, v := range m {
        println(k, v)
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();

                // Both k and v should be tracked as definitions
                assert!(
                    dfg.definitions.contains_key("k"),
                    "Map key variable k should be tracked as definition"
                );
                assert!(
                    dfg.definitions.contains_key("v"),
                    "Map value variable v should be tracked as definition"
                );

                // m should be tracked as a use
                assert!(
                    dfg.uses.contains_key("m"),
                    "Range expression 'm' should be tracked as use"
                );
            }
        }
    }

    #[test]
    fn test_for_range_nested_loops() {
        // Test nested for-range loops
        let source = r#"
package main

func nestedRange() {
    matrix := [][]int{{1, 2}, {3, 4}}
    for i, row := range matrix {
        for j, val := range row {
            println(i, j, val)
        }
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let dfg = go.build_dfg(child, &source_bytes).unwrap();

                // All loop variables should be tracked
                assert!(
                    dfg.definitions.contains_key("i"),
                    "Outer loop variable i should be tracked"
                );
                assert!(
                    dfg.definitions.contains_key("row"),
                    "Outer loop variable row should be tracked"
                );
                assert!(
                    dfg.definitions.contains_key("j"),
                    "Inner loop variable j should be tracked"
                );
                assert!(
                    dfg.definitions.contains_key("val"),
                    "Inner loop variable val should be tracked"
                );

                // row should be used in the inner range expression
                assert!(
                    dfg.uses.contains_key("row"),
                    "row should be tracked as use in inner range"
                );
            }
        }
    }

    // =========================================================================
    // DEFER/PANIC/RECOVER CFG TESTS
    // =========================================================================

    #[test]
    fn test_defer_basic_cfg() {
        // Test basic defer with LIFO execution order
        let source = r#"
package main

func foo() {
    defer cleanup1()
    defer cleanup2()
    doWork()
    return
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have deferred call blocks
                let defer_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::DeferredCall)
                    .collect();

                assert!(
                    !defer_blocks.is_empty(),
                    "Should have DeferredCall blocks for defer statements"
                );

                // Should have Defer edges
                let defer_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Defer)
                    .collect();

                assert!(
                    !defer_edges.is_empty(),
                    "Should have Defer edges connecting to deferred calls"
                );

                // Should have DeferChain edges for LIFO execution
                let chain_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::DeferChain)
                    .collect();

                assert!(
                    !chain_edges.is_empty(),
                    "Should have DeferChain edges for LIFO execution order"
                );
            }
        }
    }

    #[test]
    fn test_panic_site_detection() {
        // Test panic() detection
        let source = r#"
package main

func riskyOperation() {
    data := getData()
    if data == nil {
        panic("data is nil")
    }
    process(data)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have panic site blocks
                let panic_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::GoPanicSite)
                    .collect();

                assert!(
                    !panic_blocks.is_empty(),
                    "Should detect panic() as GoPanicSite block"
                );

                // Should have Panic edges
                let panic_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Panic)
                    .collect();

                assert!(
                    !panic_edges.is_empty(),
                    "Should have Panic edges from panic sites"
                );
            }
        }
    }

    #[test]
    fn test_recover_in_defer() {
        // Test recover() detection in deferred function
        let source = r#"
package main

func safe() (err error) {
    defer func() {
        if r := recover(); r != nil {
            err = fmt.Errorf("recovered: %v", r)
        }
    }()
    riskyOperation()
    return nil
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have RecoverCall blocks for defer with recover()
                let recover_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::RecoverCall)
                    .collect();

                assert!(
                    !recover_blocks.is_empty(),
                    "Should detect recover() in defer as RecoverCall block"
                );
            }
        }
    }

    #[test]
    fn test_error_check_pattern() {
        // Test if err != nil pattern detection
        let source = r#"
package main

func processFile(path string) error {
    file, err := os.Open(path)
    if err != nil {
        return fmt.Errorf("failed to open file: %w", err)
    }
    defer file.Close()

    data, err := io.ReadAll(file)
    if err != nil {
        return err
    }

    return process(data)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have ErrorCheck blocks
                let error_check_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ErrorCheck)
                    .collect();

                assert!(
                    !error_check_blocks.is_empty(),
                    "Should detect 'if err != nil' as ErrorCheck block"
                );

                // Should have ErrorPath edges
                let error_path_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::ErrorPath)
                    .collect();

                assert!(
                    !error_path_edges.is_empty(),
                    "Should have ErrorPath edges from error check"
                );

                // Should have SuccessPath edges
                let success_path_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::SuccessPath)
                    .collect();

                assert!(
                    !success_path_edges.is_empty(),
                    "Should have SuccessPath edges from error check"
                );
            }
        }
    }

    #[test]
    fn test_defer_lifo_order() {
        // Test that defers execute in LIFO order
        // defer A(); defer B(); return  ->  B executes first, then A
        let source = r#"
package main

func multiDefer() {
    defer func() { println("first registered, last executed") }()
    defer func() { println("second registered, second executed") }()
    defer func() { println("third registered, first executed") }()
    doWork()
    return
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have 3 defer blocks
                let defer_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::DeferredCall)
                    .collect();

                assert_eq!(defer_blocks.len(), 3, "Should have 3 DeferredCall blocks");

                // Should have DeferChain edges connecting them
                let chain_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::DeferChain)
                    .collect();

                // With 3 defers, we should have 2 chain edges (3 -> 2 -> 1)
                assert!(
                    chain_edges.len() >= 2,
                    "Should have at least 2 DeferChain edges for LIFO order"
                );
            }
        }
    }

    #[test]
    fn test_defer_with_return_value() {
        // Test defer with named return value modification
        let source = r#"
package main

func namedReturn() (result int) {
    defer func() {
        result = result * 2
    }()
    result = 21
    return
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have a deferred call block
                let defer_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::DeferredCall)
                    .collect();

                assert!(!defer_blocks.is_empty(), "Should have DeferredCall block");

                // The defer should contain the result modification
                let has_result_mod = defer_blocks.iter().any(|b| b.label.contains("result"));

                assert!(has_result_mod, "Defer should reference named return value");
            }
        }
    }

    #[test]
    fn test_mu_unlock_defer() {
        // Test common mutex unlock pattern
        let source = r#"
package main

import "sync"

func (s *Server) Get(key string) (string, bool) {
    s.mu.RLock()
    defer s.mu.RUnlock()
    val, ok := s.data[key]
    return val, ok
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "method_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should detect defer for mutex unlock
                let defer_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::DeferredCall)
                    .collect();

                assert!(
                    !defer_blocks.is_empty(),
                    "Should detect defer for mutex unlock"
                );

                // Should have the unlock in the defer
                let has_unlock = defer_blocks
                    .iter()
                    .any(|b| b.label.contains("Unlock") || b.label.contains("RUnlock"));

                assert!(has_unlock, "Defer should contain unlock call");
            }
        }
    }

    #[test]
    fn test_file_close_defer() {
        // Test common file close pattern
        let source = r#"
package main

import "os"

func readFile(path string) ([]byte, error) {
    f, err := os.Open(path)
    if err != nil {
        return nil, err
    }
    defer f.Close()

    return io.ReadAll(f)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have error check block
                let error_checks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ErrorCheck)
                    .collect();

                assert!(
                    !error_checks.is_empty(),
                    "Should detect error check pattern"
                );

                // Should have defer for file close
                let defer_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::DeferredCall)
                    .collect();

                assert!(
                    !defer_blocks.is_empty(),
                    "Should detect defer for file close"
                );

                let has_close = defer_blocks.iter().any(|b| b.label.contains("Close"));

                assert!(has_close, "Defer should contain Close call");
            }
        }
    }

    #[test]
    fn test_gin_recovery_pattern() {
        // Test gin-style recovery middleware pattern
        let source = r#"
package gin

func Recovery() HandlerFunc {
    return func(c *Context) {
        defer func() {
            if err := recover(); err != nil {
                c.AbortWithStatus(500)
            }
        }()
        c.Next()
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        // Find the outer function
        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // The CFG should exist
                assert!(cfg.blocks.len() > 0, "CFG should have blocks");
            }
        }
    }

    // =========================================================================
    // CONCURRENCY CFG TESTS - Goroutines, Channels, Select, Sync primitives
    // =========================================================================

    #[test]
    fn test_select_statement_cfg() {
        // Test select with multiple cases
        let source = r#"
package main

func selectExample() {
    ch1 := make(chan int)
    ch2 := make(chan string)

    select {
    case v := <-ch1:
        handle1(v)
    case ch2 <- "hello":
        handle2()
    default:
        handleDefault()
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have SelectBlock
                let select_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::SelectBlock)
                    .collect();

                assert!(
                    !select_blocks.is_empty(),
                    "CFG should contain SelectBlock for select statement"
                );

                // Should have SelectCase edges
                let select_case_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::SelectCase)
                    .collect();

                assert!(
                    !select_case_edges.is_empty(),
                    "CFG should have SelectCase edges"
                );

                // Should have SelectDefault edge
                let select_default_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::SelectDefault)
                    .collect();

                assert!(
                    !select_default_edges.is_empty(),
                    "CFG should have SelectDefault edge for default case"
                );
            }
        }
    }

    #[test]
    fn test_channel_make_cfg() {
        // Test channel creation detection
        let source = r#"
package main

func channelMake() {
    unbuffered := make(chan int)
    buffered := make(chan string, 10)
    _ = unbuffered
    _ = buffered
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have ChannelMake blocks
                let channel_make_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ChannelMake)
                    .collect();

                assert_eq!(
                    channel_make_blocks.len(),
                    2,
                    "CFG should contain 2 ChannelMake blocks"
                );
            }
        }
    }

    #[test]
    fn test_channel_close_cfg() {
        // Test channel close detection
        let source = r#"
package main

func channelClose() {
    ch := make(chan int)
    close(ch)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have ChannelClose block
                let close_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ChannelClose)
                    .collect();

                assert!(
                    !close_blocks.is_empty(),
                    "CFG should contain ChannelClose block"
                );

                // Should have ChannelClose edge
                let close_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::ChannelClose)
                    .collect();

                assert!(!close_edges.is_empty(), "CFG should have ChannelClose edge");
            }
        }
    }

    #[test]
    fn test_mutex_lock_unlock_cfg() {
        // Test mutex lock/unlock detection
        let source = r#"
package main

import "sync"

func mutexExample() {
    var mu sync.Mutex
    mu.Lock()
    doWork()
    mu.Unlock()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have MutexLock block
                let lock_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::MutexLock)
                    .collect();

                assert!(
                    !lock_blocks.is_empty(),
                    "CFG should contain MutexLock block"
                );

                // Should have MutexUnlock block
                let unlock_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::MutexUnlock)
                    .collect();

                assert!(
                    !unlock_blocks.is_empty(),
                    "CFG should contain MutexUnlock block"
                );

                // Should have Lock edge
                let lock_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Lock)
                    .collect();

                assert!(!lock_edges.is_empty(), "CFG should have Lock edge");

                // Should have Unlock edge
                let unlock_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Unlock)
                    .collect();

                assert!(!unlock_edges.is_empty(), "CFG should have Unlock edge");
            }
        }
    }

    #[test]
    fn test_waitgroup_cfg() {
        // Test WaitGroup detection
        let source = r#"
package main

import "sync"

func waitgroupExample() {
    var wg sync.WaitGroup
    wg.Add(1)
    go func() {
        defer wg.Done()
        doWork()
    }()
    wg.Wait()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have WaitGroupWait block
                let wait_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::WaitGroupWait)
                    .collect();

                assert!(
                    !wait_blocks.is_empty(),
                    "CFG should contain WaitGroupWait block"
                );

                // Should have GoroutineSpawn block
                let spawn_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::GoroutineSpawn)
                    .collect();

                assert!(
                    !spawn_blocks.is_empty(),
                    "CFG should contain GoroutineSpawn block"
                );

                // Should have WaitSync edge
                let wait_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::WaitSync)
                    .collect();

                assert!(!wait_edges.is_empty(), "CFG should have WaitSync edge");
            }
        }
    }

    #[test]
    fn test_goroutine_spawn_block_type() {
        // Test that goroutine uses proper block type
        let source = r#"
package main

func spawnGoroutine() {
    go func() {
        doWork()
    }()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have GoroutineSpawn block
                let spawn_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::GoroutineSpawn)
                    .collect();

                assert!(
                    !spawn_blocks.is_empty(),
                    "CFG should contain GoroutineSpawn block"
                );

                // Should have Spawn edge
                let spawn_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Spawn)
                    .collect();

                assert!(
                    !spawn_edges.is_empty(),
                    "CFG should have Spawn edge for goroutine"
                );
            }
        }
    }

    #[test]
    fn test_channel_send_block_type() {
        // Test that channel send uses proper block type
        let source = r#"
package main

func sendToChannel(ch chan int) {
    ch <- 42
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have ChannelSend block
                let send_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ChannelSend)
                    .collect();

                assert!(
                    !send_blocks.is_empty(),
                    "CFG should contain ChannelSend block"
                );

                // Should have Send edge
                let send_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Send)
                    .collect();

                assert!(
                    !send_edges.is_empty(),
                    "CFG should have Send edge for channel send"
                );
            }
        }
    }

    #[test]
    fn test_channel_receive_cfg() {
        // Test channel receive detection in assignment
        let source = r#"
package main

func receiveFromChannel(ch chan int) {
    val := <-ch
    process(val)
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have ChannelReceive block
                let recv_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ChannelReceive)
                    .collect();

                assert!(
                    !recv_blocks.is_empty(),
                    "CFG should contain ChannelReceive block"
                );

                // Should have Receive edge
                let recv_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::Receive)
                    .collect();

                assert!(
                    !recv_edges.is_empty(),
                    "CFG should have Receive edge for channel receive"
                );
            }
        }
    }

    #[test]
    fn test_empty_select_blocks_forever() {
        // Test empty select {} detection
        let source = r#"
package main

func blockForever() {
    select {}
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have SelectBlock with BLOCKS FOREVER annotation
                let select_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::SelectBlock)
                    .collect();

                assert!(!select_blocks.is_empty(), "CFG should contain SelectBlock");

                let has_blocks_forever = select_blocks
                    .iter()
                    .any(|b| b.label.contains("BLOCKS FOREVER"));

                assert!(
                    has_blocks_forever,
                    "Empty select {{}} should be annotated with BLOCKS FOREVER"
                );
            }
        }
    }

    #[test]
    fn test_gin_concurrent_handler() {
        // Test concurrent gin-style handler pattern
        let source = r#"
package main

import "sync"

func handleRequest(c *gin.Context) {
    var wg sync.WaitGroup
    results := make(chan int, 3)

    wg.Add(3)
    go func() {
        defer wg.Done()
        results <- fetchFromDB()
    }()
    go func() {
        defer wg.Done()
        results <- fetchFromCache()
    }()
    go func() {
        defer wg.Done()
        results <- fetchFromAPI()
    }()

    wg.Wait()
    close(results)

    c.JSON(200, collectResults(results))
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have multiple GoroutineSpawn blocks
                let spawn_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::GoroutineSpawn)
                    .collect();

                assert_eq!(
                    spawn_blocks.len(),
                    3,
                    "CFG should contain 3 GoroutineSpawn blocks"
                );

                // Should have WaitGroupWait block
                let wait_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::WaitGroupWait)
                    .collect();

                assert!(
                    !wait_blocks.is_empty(),
                    "CFG should contain WaitGroupWait block"
                );

                // Should have ChannelClose block
                let close_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::ChannelClose)
                    .collect();

                assert!(
                    !close_blocks.is_empty(),
                    "CFG should contain ChannelClose block"
                );
            }
        }
    }

    #[test]
    fn test_context_cancellation_pattern() {
        // Test context cancellation pattern with select
        let source = r#"
package main

import "context"

func withTimeout(ctx context.Context, ch chan int) {
    select {
    case <-ctx.Done():
        handleCancel()
    case val := <-ch:
        handleValue(val)
    }
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();

                // Should have SelectBlock
                let select_blocks: Vec<_> = cfg
                    .blocks
                    .values()
                    .filter(|b| b.block_type == BlockType::SelectBlock)
                    .collect();

                assert!(!select_blocks.is_empty(), "CFG should contain SelectBlock");

                // Should have SelectCase edges (at least 2)
                let case_edges: Vec<_> = cfg
                    .edges
                    .iter()
                    .filter(|e| e.edge_type == EdgeType::SelectCase)
                    .collect();

                assert!(
                    case_edges.len() >= 2,
                    "CFG should have at least 2 SelectCase edges"
                );
            }
        }
    }

    #[test]
    fn test_concurrency_issue_detection() {
        // Test concurrency issue detection
        let source = r#"
package main

func potentialIssues() {
    ch := make(chan int)
    ch <- 42  // Potential deadlock: send without receiver
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                let issues = go.detect_concurrency_issues(&cfg);

                // Should detect potential deadlock
                let has_deadlock_issue = issues
                    .iter()
                    .any(|i| i.kind == ConcurrencyIssueKind::PotentialDeadlock);

                assert!(
                    has_deadlock_issue,
                    "Should detect potential deadlock pattern"
                );
            }
        }
    }

    #[test]
    fn test_mutex_lock_without_unlock_detection() {
        // Test mutex lock without unlock detection
        let source = r#"
package main

import "sync"

func lockWithoutUnlock() {
    var mu sync.Mutex
    mu.Lock()
    doWork()
    // Missing mu.Unlock()
}
"#;

        let (tree, source_bytes) = parse_go(source);
        let go = Go;
        let root = tree.root_node();

        let mut cursor = root.walk();
        for child in root.children(&mut cursor) {
            if child.kind() == "function_declaration" {
                let cfg = go.build_cfg(child, &source_bytes).unwrap();
                let issues = go.detect_concurrency_issues(&cfg);

                // Should detect mutex lock without unlock
                let has_lock_issue = issues
                    .iter()
                    .any(|i| i.kind == ConcurrencyIssueKind::MutexLockWithoutUnlock);

                assert!(has_lock_issue, "Should detect mutex lock without unlock");
            }
        }
    }
}
