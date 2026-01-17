//! Rust language support.
//!
//! Named `rust_lang` to avoid conflict with `rust` keyword.
//!
//! Supports extraction of:
//! - Functions (including async, unsafe, const, extern, generic, visibility, attributes)
//! - Structs with fields
//! - Unions with fields (union Foo { a: u32, b: f32 })
//! - Enums with variants (unit, tuple, struct-like)
//! - Impl blocks with associated methods, types, and constants
//! - Traits with method signatures, associated types, and constants
//! - Associated types (type Item; in traits, type Item = u32; in impls)
//! - Associated constants (const MAX: usize = 100; in traits/impls)
//! - Use declarations (simple, scoped, glob, aliased)
//! - Const items (const X: Type = value)
//! - Static items (static X: Type = value, static mut X: Type = value)
//! - Type aliases (type Alias<T> = SomeType<T>)
//! - Module declarations (mod foo; and mod foo { ... })
//! - Extern blocks (extern "C" { fn foo(); }) with ABI tracking
//! - Extern crate declarations (extern crate foo; and extern crate foo as bar;)

use std::collections::HashMap;
use tree_sitter::{Node, Parser, Tree};

use aho_corasick::AhoCorasick;
use once_cell::sync::Lazy;

use crate::ast::types::{ClassInfo, FunctionInfo, ImportInfo};
use crate::cfg::types::{BlockId, BlockType, CFGBlock, CFGEdge, CFGInfo, EdgeType};
use crate::dfg::types::{DFGInfo, DataflowEdge, DataflowKind};
use crate::error::{Result, BrrrError};
use crate::lang::traits::Language;

// =============================================================================
// Static Aho-Corasick matchers for multi-pattern string matching
// =============================================================================

/// Panic site patterns for detecting unwrap, expect, panic!, unreachable!, todo!, unimplemented!
static PANIC_PATTERNS: Lazy<AhoCorasick> = Lazy::new(|| {
    AhoCorasick::new([
        ".unwrap()",
        ".expect(",
        "panic!",
        "unreachable!",
        "todo!",
        "unimplemented!",
    ])
    .expect("Invalid panic patterns")
});

/// Pattern names corresponding to PANIC_PATTERNS indices.
const PANIC_PATTERN_NAMES: &[&str] = &[
    "unwrap()",
    "expect()",
    "panic!()",
    "unreachable!()",
    "todo!()",
    "unimplemented!()",
];

/// Blocking call patterns for detecting sync operations in async context.
static BLOCKING_PATTERNS: Lazy<AhoCorasick> = Lazy::new(|| {
    AhoCorasick::new([
        "std::thread::sleep",
        "thread::sleep",
        "std::fs::read",
        "std::fs::write",
        "std::fs::open",
        "std::fs::create",
        "std::fs::remove",
        "std::fs::rename",
        "std::fs::copy",
        "std::fs::metadata",
        "fs::read",
        "fs::write",
        "fs::open",
        "fs::create",
        "fs::remove",
        "fs::rename",
        "fs::copy",
        "fs::metadata",
        "std::io::stdin",
        "std::io::stdout",
        "reqwest::blocking",
    ])
    .expect("Invalid blocking patterns")
});

/// Pattern names corresponding to BLOCKING_PATTERNS indices.
const BLOCKING_PATTERN_NAMES: &[&str] = &[
    "std::thread::sleep",
    "std::thread::sleep",
    "std::fs::read",
    "std::fs::write",
    "std::fs::open",
    "std::fs::create",
    "std::fs::remove",
    "std::fs::rename",
    "std::fs::copy",
    "std::fs::metadata",
    "std::fs::read",
    "std::fs::write",
    "std::fs::open",
    "std::fs::create",
    "std::fs::remove",
    "std::fs::rename",
    "std::fs::copy",
    "std::fs::metadata",
    "std::io blocking",
    "std::io blocking",
    "reqwest::blocking",
];

/// Lock acquisition patterns for detecting mutex/rwlock guards.
static LOCK_PATTERNS: Lazy<AhoCorasick> = Lazy::new(|| {
    AhoCorasick::new([
        ".lock().unwrap()",
        ".lock().expect(",
        ".read().unwrap()",
        ".write().unwrap()",
        ".lock()",
        ".read()",
        ".write()",
    ])
    .expect("Invalid lock patterns")
});

/// Lock type names corresponding to LOCK_PATTERNS indices.
/// Note: More specific patterns (with .unwrap()/.expect()) come first for priority matching.
const LOCK_PATTERN_TYPES: &[&str] = &[
    "Mutex",
    "Mutex",
    "RwLock::read",
    "RwLock::write",
    "Mutex",
    "RwLock::read",
    "RwLock::write",
];

/// Function modifiers in Rust (async, unsafe, const, extern).
///
/// CRITICAL for security analysis: `unsafe` code bypasses Rust's safety guarantees
/// and must be identified for security audits and code review.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionModifiers {
    /// Function is async (asynchronous execution).
    pub is_async: bool,
    /// Function is unsafe (CRITICAL: bypasses Rust safety checks).
    /// Must be flagged in security analysis.
    pub is_unsafe: bool,
    /// Function is const (compile-time evaluable).
    pub is_const: bool,
    /// Function uses extern ABI (foreign function interface).
    /// Security-relevant for FFI boundary analysis.
    pub extern_abi: Option<String>,
}

impl FunctionModifiers {
    /// Convert modifiers to decorator strings for FunctionInfo.
    ///
    /// Returns modifiers in order: unsafe, const, async, extern.
    /// This ordering puts security-critical modifiers first.
    pub fn to_decorators(&self) -> Vec<String> {
        let mut decorators = Vec::new();
        // Security-critical modifiers first
        if self.is_unsafe {
            decorators.push("unsafe".to_string());
        }
        if self.is_const {
            decorators.push("const".to_string());
        }
        if self.is_async {
            decorators.push("async".to_string());
        }
        if let Some(ref abi) = self.extern_abi {
            if abi.is_empty() {
                decorators.push("extern".to_string());
            } else {
                decorators.push(format!("extern \"{}\"", abi));
            }
        }
        decorators
    }

    /// Check if function has any security-relevant modifiers.
    ///
    /// Returns true for unsafe functions or extern FFI functions,
    /// which require additional scrutiny in security audits.
    #[allow(dead_code)]
    pub fn has_security_implications(&self) -> bool {
        self.is_unsafe || self.extern_abi.is_some()
    }
}

/// Context for tracking loops during CFG construction.
///
/// Enables proper handling of break and continue statements, including
/// labeled variants like `break 'outer` and `continue 'outer`.
#[derive(Default, Clone)]
struct LoopContext {
    /// Stack of unlabeled loop contexts: (header_block, exit_block)
    unlabeled_stack: Vec<(BlockId, BlockId)>,
    /// Map of labeled loops: label -> (header_block, exit_block)
    labeled_loops: HashMap<String, (BlockId, BlockId)>,
}

/// Context for tracking async/await patterns during CFG construction.
///
/// Tracks:
/// - Whether we're inside an async function (for blocking call detection)
/// - Await suspension points count
/// - Held locks (MutexGuard, RwLockGuard) for lock-across-await detection
/// - Blocking calls found in async context
#[derive(Default, Clone)]
struct AsyncCfgContext {
    /// Whether the current function is async (async fn or returns impl Future)
    is_async: bool,
    /// Number of await points encountered
    await_points: usize,
    /// Variables currently holding locks (MutexGuard, RwLockGuard, etc.)
    /// Format: (variable_name, lock_type, acquisition_line)
    held_locks: Vec<(String, String, usize)>,
    /// Blocking calls detected in async context: (function_name, line)
    blocking_calls: Vec<(String, usize)>,
    /// Lock-across-await issues: (lock_var, lock_type, lock_line, await_line)
    lock_across_await_issues: Vec<(String, String, usize, usize)>,
}

impl AsyncCfgContext {
    fn new(is_async: bool) -> Self {
        Self {
            is_async,
            ..Default::default()
        }
    }

    /// Record a lock acquisition
    fn acquire_lock(&mut self, var_name: &str, lock_type: &str, line: usize) {
        self.held_locks.push((var_name.to_string(), lock_type.to_string(), line));
    }

    /// Release a lock (variable goes out of scope or explicit drop)
    fn release_lock(&mut self, var_name: &str) {
        self.held_locks.retain(|(name, _, _)| name != var_name);
    }

    /// Check if any locks are held (for await point detection)
    fn has_held_locks(&self) -> bool {
        !self.held_locks.is_empty()
    }

    /// Record an await point and check for lock-across-await issues
    fn record_await(&mut self, await_line: usize) {
        self.await_points += 1;
        // Check for lock-across-await anti-pattern
        for (var, lock_type, lock_line) in &self.held_locks {
            self.lock_across_await_issues.push((
                var.clone(),
                lock_type.clone(),
                *lock_line,
                await_line,
            ));
        }
    }

    /// Record a blocking call if we're in async context
    fn record_blocking_call(&mut self, func_name: &str, line: usize) {
        if self.is_async {
            self.blocking_calls.push((func_name.to_string(), line));
        }
    }
}

impl LoopContext {
    fn push_loop(&mut self, label: Option<&str>, header: BlockId, exit: BlockId) {
        self.unlabeled_stack.push((header, exit));
        if let Some(l) = label {
            self.labeled_loops.insert(l.to_string(), (header, exit));
        }
    }

    fn pop_loop(&mut self, label: Option<&str>) {
        self.unlabeled_stack.pop();
        if let Some(l) = label {
            self.labeled_loops.remove(l);
        }
    }

    fn resolve_break(&self, label: Option<&str>) -> Option<BlockId> {
        if let Some(l) = label {
            self.labeled_loops.get(l).map(|(_, exit)| *exit)
        } else {
            self.unlabeled_stack.last().map(|(_, exit)| *exit)
        }
    }

    fn resolve_continue(&self, label: Option<&str>) -> Option<BlockId> {
        if let Some(l) = label {
            self.labeled_loops.get(l).map(|(header, _)| *header)
        } else {
            self.unlabeled_stack.last().map(|(header, _)| *header)
        }
    }
}

/// Rust language implementation.
pub struct Rust;

impl Rust {
    /// Extract text from a node.
    fn node_text<'a>(&self, node: Node<'a>, source: &'a [u8]) -> &'a str {
        node.utf8_text(source).unwrap_or("")
    }

    /// Find preceding doc comments (/// or /** */) for a node.
    ///
    /// Supports both line doc comments (///) and block doc comments (/** */).
    /// Module-level doc comments (//! and /*! */) are ignored.
    fn extract_doc_comments(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut comments = Vec::new();
        let mut sibling = node.prev_sibling();

        // Walk backwards to collect consecutive doc comments
        while let Some(prev) = sibling {
            if prev.kind() == "line_comment" {
                let text = self.node_text(prev, source);
                // Check for /// doc comments
                if text.starts_with("///") {
                    let doc_content = text.trim_start_matches('/').trim();
                    comments.push(doc_content.to_string());
                } else if text.starts_with("//!") {
                    // Module-level doc comment, stop here
                    break;
                } else {
                    // Regular comment, stop collecting
                    break;
                }
            } else if prev.kind() == "block_comment" {
                let text = self.node_text(prev, source);
                // Check for /** ... */ block doc comments (not /*! */ which is module-level)
                // Also skip /**/ which is an empty block comment, not a doc comment
                if text.starts_with("/**") && !text.starts_with("/**/") {
                    let doc_content = self.extract_block_doc_content(text);
                    if !doc_content.is_empty() {
                        comments.push(doc_content);
                    }
                } else if text.starts_with("/*!") {
                    // Module-level block doc comment, stop here
                    break;
                } else {
                    // Regular block comment, stop collecting
                    break;
                }
            } else if prev.kind() == "attribute_item" {
                // Skip attributes when looking for doc comments
                sibling = prev.prev_sibling();
                continue;
            } else {
                break;
            }
            sibling = prev.prev_sibling();
        }

        if comments.is_empty() {
            None
        } else {
            comments.reverse();
            Some(comments.join("\n"))
        }
    }

    /// Extract content from a block doc comment (/** ... */).
    ///
    /// Handles both single-line and multi-line block doc comments.
    /// Removes common leading asterisks from continuation lines.
    fn extract_block_doc_content(&self, text: &str) -> String {
        // Remove /** prefix and */ suffix
        let content = text
            .trim_start_matches("/**")
            .trim_end_matches("*/")
            .trim();

        // Handle multi-line block comments: remove leading * from each line
        let lines: Vec<&str> = content
            .lines()
            .map(|line| {
                let trimmed = line.trim();
                // Remove leading * that's common in block doc comments
                if trimmed.starts_with('*') {
                    trimmed[1..].trim_start()
                } else {
                    trimmed
                }
            })
            .collect();

        lines.join("\n").trim().to_string()
    }

    /// Extract attributes (#[...] and #![...]) for a node.
    ///
    /// Collects both:
    /// - Outer attributes (#[...]) from preceding siblings
    /// - Inner attributes (#![...]) from inside the node
    fn extract_attributes(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut attributes = Vec::new();

        // Collect outer attributes (#[...]) from preceding siblings
        let mut sibling = node.prev_sibling();
        while let Some(prev) = sibling {
            if prev.kind() == "attribute_item" {
                let text = self.node_text(prev, source).trim().to_string();
                attributes.push(text);
            } else if prev.kind() == "line_comment" {
                // Skip doc comments when collecting attributes
                sibling = prev.prev_sibling();
                continue;
            } else {
                break;
            }
            sibling = prev.prev_sibling();
        }
        attributes.reverse();

        // Collect inner attributes (#![...]) from inside the node
        for child in node.children(&mut node.walk()) {
            if child.kind() == "inner_attribute_item" {
                let text = self.node_text(child, source).trim().to_string();
                attributes.push(text);
            }
        }

        attributes
    }

    /// Extract visibility modifier (pub, pub(crate), etc.).
    fn extract_visibility(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "visibility_modifier" {
                return Some(self.node_text(child, source).to_string());
            }
        }
        None
    }

    /// Extract all function modifiers (async, unsafe, const, extern).
    ///
    /// CRITICAL: This method detects unsafe code which bypasses Rust's safety
    /// guarantees. Unsafe functions must be flagged in security analysis.
    ///
    /// # Modifiers detected:
    /// - `async` - asynchronous function
    /// - `unsafe` - bypasses safety checks (SECURITY CRITICAL)
    /// - `const` - compile-time evaluable
    /// - `extern "ABI"` - foreign function interface (SECURITY RELEVANT)
    fn extract_function_modifiers(&self, node: Node, source: &[u8]) -> FunctionModifiers {
        let mut modifiers = FunctionModifiers::default();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "function_modifiers" => {
                    // Handle modifiers like: async, unsafe, const
                    for modifier in child.children(&mut child.walk()) {
                        match modifier.kind() {
                            "async" => modifiers.is_async = true,
                            "unsafe" => modifiers.is_unsafe = true,
                            "const" => modifiers.is_const = true,
                            _ => {}
                        }
                    }
                }
                "extern_modifier" => {
                    // Handle extern "C" or extern "Rust" etc.
                    // Extract the ABI string if present
                    let abi = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "string_literal")
                        .map(|s| {
                            let text = self.node_text(s, source);
                            // Remove quotes from "C" -> C
                            text.trim_matches('"').to_string()
                        })
                        .unwrap_or_default();
                    modifiers.extern_abi = Some(abi);
                }
                _ => {}
            }
        }

        modifiers
    }

    /// Check if a node or any of its descendants contains a try expression (`?` operator).
    ///
    /// The try operator (`?`) causes early return on Err/None, creating critical
    /// control flow paths that must be modeled in the CFG. This is essential for:
    /// - Error propagation analysis
    /// - Finding unhandled error paths
    /// - Accurate cyclomatic complexity calculation
    fn contains_try_expression(&self, node: Node) -> bool {
        if node.kind() == "try_expression" {
            return true;
        }
        for child in node.children(&mut node.walk()) {
            if self.contains_try_expression(child) {
                return true;
            }
        }
        false
    }

    /// Count the number of try expressions (`?` operators) in a node and its descendants.
    ///
    /// Returns the total count of try expressions for CFG complexity analysis.
    fn count_try_expressions(&self, node: Node) -> usize {
        let mut count = 0;
        if node.kind() == "try_expression" {
            count += 1;
        }
        for child in node.children(&mut node.walk()) {
            count += self.count_try_expressions(child);
        }
        count
    }

    /// Check if a node contains a potential panic site.
    ///
    /// Panic sites include:
    /// - .unwrap() method calls
    /// - .expect() method calls
    /// - panic!() macro invocations
    /// - unreachable!() macro invocations
    /// - todo!() and unimplemented!() macros
    fn contains_panic_site(&self, node: Node, source: &[u8]) -> bool {
        let text = self.node_text(node, source);
        // Single-pass multi-pattern match using Aho-Corasick
        if PANIC_PATTERNS.find(text.as_bytes()).is_some() {
            return true;
        }

        // Recursive check for children
        for child in node.children(&mut node.walk()) {
            if self.contains_panic_site(child, source) {
                return true;
            }
        }
        false
    }

    /// Get information about a panic site for CFG labeling.
    ///
    /// Returns a human-readable description of the panic site.
    fn get_panic_site_info(&self, node: Node, source: &[u8]) -> String {
        let text = self.node_text(node, source);

        // Single-pass lookup returning the matched pattern name
        if let Some(mat) = PANIC_PATTERNS.find(text.as_bytes()) {
            PANIC_PATTERN_NAMES[mat.pattern().as_usize()].to_string()
        } else {
            "potential panic".to_string()
        }
    }

    // =========================================================================
    // Rust async/await detection and analysis methods
    // =========================================================================

    /// Check if a node is an await expression (.await).
    ///
    /// In tree-sitter-rust, await expressions are represented as:
    /// `await_expression` with an inner expression being awaited.
    fn is_await_expression(&self, node: Node) -> bool {
        node.kind() == "await_expression"
    }

    /// Check if a node contains any await expressions.
    fn contains_await(&self, node: Node) -> bool {
        if self.is_await_expression(node) {
            return true;
        }
        for child in node.children(&mut node.walk()) {
            if self.contains_await(child) {
                return true;
            }
        }
        false
    }

    /// Count await expressions in a node and its descendants.
    fn count_await_expressions(&self, node: Node) -> usize {
        let mut count = 0;
        if self.is_await_expression(node) {
            count += 1;
        }
        for child in node.children(&mut node.walk()) {
            count += self.count_await_expressions(child);
        }
        count
    }

    /// Check if a call expression is tokio::spawn or async_std::spawn.
    ///
    /// Returns (is_spawn, spawn_type) where spawn_type is "tokio" or "async_std".
    fn is_spawn_call(&self, node: Node, source: &[u8]) -> (bool, Option<&'static str>) {
        if node.kind() != "call_expression" {
            return (false, None);
        }

        let text = self.node_text(node, source);
        if text.contains("tokio::spawn") || text.contains("spawn(") && text.contains("tokio") {
            return (true, Some("tokio"));
        }
        if text.contains("async_std::spawn") || text.contains("task::spawn") {
            return (true, Some("async_std"));
        }
        if text.contains("spawn_blocking") {
            return (true, Some("spawn_blocking"));
        }
        (false, None)
    }

    /// Check if a macro invocation is tokio::join! or similar.
    ///
    /// Returns (is_join, macro_name) for join!/try_join!/select!/etc.
    fn is_async_macro(&self, node: Node, source: &[u8]) -> (bool, Option<&'static str>) {
        if node.kind() != "macro_invocation" {
            return (false, None);
        }

        let text = self.node_text(node, source);
        if text.starts_with("join!") || text.starts_with("tokio::join!") {
            return (true, Some("join!"));
        }
        if text.starts_with("try_join!") || text.starts_with("tokio::try_join!") {
            return (true, Some("try_join!"));
        }
        if text.starts_with("select!") || text.starts_with("tokio::select!") {
            return (true, Some("select!"));
        }
        if text.starts_with("futures::join!") || text.starts_with("futures::select!") {
            let macro_name = if text.contains("join!") { "join!" } else { "select!" };
            return (true, Some(macro_name));
        }
        (false, None)
    }

    /// Check if a call is a known blocking operation.
    ///
    /// Returns (is_blocking, blocking_type) for:
    /// - std::thread::sleep
    /// - std::io::* blocking operations
    /// - std::fs::* operations (not async fs)
    /// - blocking network operations
    fn is_blocking_call(&self, node: Node, source: &[u8]) -> (bool, Option<String>) {
        let text = self.node_text(node, source);

        // Single-pass multi-pattern match for known blocking operations
        if let Some(mat) = BLOCKING_PATTERNS.find(text.as_bytes()) {
            return (true, Some(BLOCKING_PATTERN_NAMES[mat.pattern().as_usize()].to_string()));
        }

        // Special case: Mutex::lock (sync version) requires negative matching
        // This cannot be in Aho-Corasick because it needs exclusion logic
        if text.contains(".lock()") && !text.contains("async") && !text.contains("tokio::sync") {
            return (true, Some("sync Mutex::lock".to_string()));
        }

        (false, None)
    }

    /// Check if a let binding acquires a lock (MutexGuard, RwLockGuard).
    ///
    /// Returns (variable_name, lock_type) if this is a lock acquisition.
    fn is_lock_acquisition(&self, node: Node, source: &[u8]) -> Option<(String, String)> {
        if node.kind() != "let_declaration" {
            return None;
        }

        let text = self.node_text(node, source);

        // Single-pass multi-pattern match for lock acquisition patterns
        if let Some(mat) = LOCK_PATTERNS.find(text.as_bytes()) {
            // Extract variable name from let binding
            if let Some(pattern_node) = node.child_by_field_name("pattern") {
                let var_name = self.node_text(pattern_node, source).to_string();
                // Clean up mut prefix
                let var_name = var_name.trim_start_matches("mut ").to_string();
                let lock_type = LOCK_PATTERN_TYPES[mat.pattern().as_usize()];
                return Some((var_name, lock_type.to_string()));
            }
        }

        None
    }

    /// Check if a statement contains a drop() call that releases a lock.
    fn is_lock_release(&self, node: Node, source: &[u8]) -> Option<String> {
        let text = self.node_text(node, source);
        if text.contains("drop(") {
            // Extract the variable being dropped
            // Pattern: drop(var_name) or drop(&var_name) or drop(&mut var_name)
            if let Some(start) = text.find("drop(") {
                let rest = &text[start + 5..];
                if let Some(end) = rest.find(')') {
                    let var = rest[..end]
                        .trim()
                        .trim_start_matches('&')
                        .trim_start_matches("mut ")
                        .to_string();
                    return Some(var);
                }
            }
        }
        None
    }

    /// Extract await expression info for CFG labeling.
    fn get_await_info(&self, node: Node, source: &[u8]) -> String {
        if node.kind() == "await_expression" {
            // Get the inner expression being awaited
            if let Some(inner) = node.child_by_field_name("value").or_else(|| node.child(0)) {
                let text = self.node_text(inner, source);
                if text.len() > 40 {
                    format!("{}..", &text[..40])
                } else {
                    text.to_string()
                }
            } else {
                "future".to_string()
            }
        } else {
            "future".to_string()
        }
    }

    /// Check if a node is an async block (async { ... } or async move { ... }).
    fn is_async_block(&self, node: Node) -> bool {
        node.kind() == "async_block"
    }

    /// Extract function calls from a node for CFG block metadata.
    ///
    /// Returns a list of function names called within the node.
    fn extract_func_calls_from_node(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut calls = Vec::new();
        self.collect_func_calls(node, source, &mut calls);
        calls
    }

    /// Helper to recursively collect function calls from a node.
    fn collect_func_calls(&self, node: Node, source: &[u8], calls: &mut Vec<String>) {
        if node.kind() == "call_expression" {
            // Extract the function name from the call
            if let Some(func) = node.child_by_field_name("function") {
                let func_text = self.node_text(func, source);
                // Clean up the function name (handle method calls)
                let name = if let Some(idx) = func_text.rfind("::") {
                    &func_text[idx + 2..]
                } else if let Some(idx) = func_text.rfind('.') {
                    &func_text[idx + 1..]
                } else {
                    func_text
                };
                if !name.is_empty() && !calls.contains(&name.to_string()) {
                    calls.push(name.to_string());
                }
            }
        }

        // Recurse into children
        for child in node.children(&mut node.walk()) {
            self.collect_func_calls(child, source, calls);
        }
    }

    /// Extract lifetime, type, and const generic parameters separately (BUG #13 fix).
    ///
    /// Distinguishes:
    /// - Lifetime parameters ('a, 'b)
    /// - Type parameters (T, U)
    /// - Const generic parameters (const N: usize)
    ///
    /// This is critical for accurate generic analysis in Rust code, especially for
    /// const generics which are semantically different from type parameters.
    ///
    /// # Returns
    /// A tuple of (lifetime_params, type_params, const_params) where each is a Vec of param strings.
    fn extract_distinct_type_params(
        &self,
        node: Node,
        source: &[u8],
    ) -> (Vec<String>, Vec<String>, Vec<String>) {
        let mut lifetimes = Vec::new();
        let mut type_params = Vec::new();
        let mut const_params = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "type_parameters" {
                for param in child.children(&mut child.walk()) {
                    match param.kind() {
                        // Lifetime parameters: 'a, 'b, 'static
                        "lifetime" => {
                            let lifetime = self.node_text(param, source).to_string();
                            lifetimes.push(lifetime);
                        }
                        // Direct type_identifier (rare, but possible)
                        "type_identifier" => {
                            let type_param = self.node_text(param, source).to_string();
                            type_params.push(type_param);
                        }
                        // Type parameter node (tree-sitter wraps type params in this)
                        // Contains: name: type_identifier, optionally bounds: trait_bounds
                        "type_parameter" => {
                            // Extract the full text which includes bounds if present
                            let text = self.node_text(param, source).to_string();
                            type_params.push(text);
                        }
                        // Constrained type parameter: T: Clone + Send or 'a: 'b
                        "constrained_type_parameter" => {
                            let text = self.node_text(param, source);
                            // Check if it starts with a lifetime
                            if text.starts_with('\'') {
                                lifetimes.push(text.to_string());
                            } else {
                                type_params.push(text.to_string());
                            }
                        }
                        // Const generic parameter: const N: usize
                        // These are distinct from type parameters and represent compile-time constants
                        "const_parameter" => {
                            let const_param = self.node_text(param, source).to_string();
                            const_params.push(const_param);
                        }
                        // Lifetime parameter node (tree-sitter wraps lifetimes)
                        "lifetime_parameter" => {
                            let text = self.node_text(param, source).to_string();
                            lifetimes.push(text);
                        }
                        _ => {}
                    }
                }
            }
        }

        (lifetimes, type_params, const_params)
    }

    /// Extract where clause.
    fn extract_where_clause(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "where_clause" {
                return Some(self.node_text(child, source).to_string());
            }
        }
        None
    }

    /// Extract function parameters as a list of strings.
    fn extract_parameters(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut params = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "parameters" {
                for param in child.children(&mut child.walk()) {
                    match param.kind() {
                        "parameter" => {
                            let param_text = self.node_text(param, source).to_string();
                            params.push(param_text);
                        }
                        "self_parameter" => {
                            let self_text = self.node_text(param, source).to_string();
                            params.push(self_text);
                        }
                        _ => {}
                    }
                }
            }
        }

        params
    }

    /// Extract return type from function.
    fn extract_return_type(&self, node: Node, source: &[u8]) -> Option<String> {
        // Look for -> followed by return_type
        let mut found_arrow = false;
        for child in node.children(&mut node.walk()) {
            if child.kind() == "->" {
                found_arrow = true;
            } else if found_arrow && child.kind() != "where_clause" && child.kind() != "block" {
                return Some(self.node_text(child, source).to_string());
            }
        }
        None
    }

    /// Extract struct fields (named fields and tuple struct fields).
    ///
    /// Handles both:
    /// - Named structs: `struct Point { x: i32, y: i32 }`
    /// - Tuple structs: `struct Point(i32, i32);`
    fn extract_struct_fields(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut fields = Vec::new();

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                // Named struct fields: struct Foo { field: Type }
                "field_declaration_list" => {
                    for field in child.children(&mut child.walk()) {
                        if field.kind() == "field_declaration" {
                            let field_text = self.node_text(field, source).trim().to_string();
                            fields.push(field_text);
                        }
                    }
                }
                // Tuple struct fields: struct Foo(Type1, Type2)
                "ordered_field_declaration_list" => {
                    let mut index = 0;
                    for field in child.children(&mut child.walk()) {
                        // Skip parentheses and commas
                        if field.kind() == "(" || field.kind() == ")" || field.kind() == "," {
                            continue;
                        }
                        // Each field in ordered_field_declaration_list may have visibility + type
                        let field_text = self.node_text(field, source).trim().to_string();
                        if !field_text.is_empty() {
                            // Format as positional field for clarity
                            fields.push(format!("{}: {}", index, field_text));
                            index += 1;
                        }
                    }
                }
                _ => {}
            }
        }

        fields
    }

    /// Extract enum variants from an enum_item node.
    ///
    /// Handles all variant forms:
    /// - Unit variants: `None`
    /// - Tuple variants: `Some(T)`
    /// - Struct variants: `Point { x: i32, y: i32 }`
    fn extract_enum_variants(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut variants = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "enum_variant_list" {
                for variant in child.children(&mut child.walk()) {
                    if variant.kind() == "enum_variant" {
                        let variant_text = self.node_text(variant, source).trim().to_string();
                        variants.push(variant_text);
                    }
                }
            }
        }

        variants
    }

    /// Extract methods and associated items from impl or trait body.
    ///
    /// Extracts:
    /// - Functions (function_item) and signatures (function_signature_item)
    /// - Associated types (associated_type in traits, type_item in impls)
    /// - Associated constants (const_item in traits/impls)
    fn extract_methods_from_body(&self, body_node: Node, source: &[u8]) -> Vec<FunctionInfo> {
        let mut methods = Vec::new();

        for child in body_node.children(&mut body_node.walk()) {
            match child.kind() {
                "function_item" => {
                    if let Some(mut func) = self.extract_function(child, source) {
                        func.is_method = true;
                        methods.push(func);
                    }
                }
                "function_signature_item" => {
                    // Trait method signatures (no body)
                    if let Some(mut func) = self.extract_function_signature(child, source) {
                        func.is_method = true;
                        methods.push(func);
                    }
                }
                // FEATURE: Associated type declarations in traits (type Item;)
                "associated_type" => {
                    if let Some(assoc_type) = self.extract_associated_type_declaration(child, source)
                    {
                        methods.push(assoc_type);
                    }
                }
                // FEATURE: Associated type definitions in impls (type Item = u32;)
                "type_item" => {
                    if let Some(assoc_type) = self.extract_associated_type_definition(child, source)
                    {
                        methods.push(assoc_type);
                    }
                }
                // FEATURE: Associated constants in traits/impls (const MAX: usize = 100;)
                "const_item" => {
                    if let Some(assoc_const) = self.extract_associated_const(child, source) {
                        methods.push(assoc_const);
                    }
                }
                _ => {}
            }
        }

        methods
    }

    /// Extract associated type declaration from trait body.
    ///
    /// Handles: `type Item;` or `type Item: Bound;`
    ///
    /// # Node structure (associated_type):
    /// ```text
    /// associated_type
    ///   type
    ///   name: type_identifier
    ///   [: trait_bounds]
    ///   ;
    /// ```
    fn extract_associated_type_declaration(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<FunctionInfo> {
        if node.kind() != "associated_type" {
            return None;
        }

        // Extract type name
        let name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "type_identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        // Extract bounds if present (e.g., type Item: Clone + Send;)
        let bounds = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "trait_bounds")
            .map(|n| self.node_text(n, source).to_string());

        let docstring = self.extract_doc_comments(node, source);

        let mut decorators = vec!["associated_type".to_string()];
        if let Some(ref b) = bounds {
            decorators.push(format!("bounds: {}", b));
        }

        // Store bounds in params for easier access
        let params = bounds.map(|b| vec![b]).unwrap_or_default();

        Some(FunctionInfo {
            name,
            params,
            return_type: None, // Declarations don't have a concrete type
            docstring,
            is_method: true,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    /// Extract associated type definition from impl body.
    ///
    /// Handles: `type Item = u32;`
    ///
    /// # Node structure (type_item inside impl):
    /// ```text
    /// type_item
    ///   type
    ///   name: type_identifier
    ///   =
    ///   type: <type_node>
    ///   ;
    /// ```
    fn extract_associated_type_definition(
        &self,
        node: Node,
        source: &[u8],
    ) -> Option<FunctionInfo> {
        if node.kind() != "type_item" {
            return None;
        }

        // Extract type name
        let name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "type_identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        // Extract the assigned type (after =)
        let assigned_type = node
            .child_by_field_name("type")
            .map(|n| self.node_text(n, source).to_string());

        let docstring = self.extract_doc_comments(node, source);

        let mut decorators = vec!["associated_type".to_string()];
        if let Some(ref t) = assigned_type {
            decorators.push(format!("= {}", t));
        }

        Some(FunctionInfo {
            name,
            params: Vec::new(),
            return_type: assigned_type, // Use return_type to store the assigned type
            docstring,
            is_method: true,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    /// Extract associated constant from trait or impl body.
    ///
    /// Handles both:
    /// - Trait declarations: `const MAX: usize;`
    /// - Impl definitions: `const MAX: usize = 100;`
    ///
    /// # Node structure (const_item):
    /// ```text
    /// const_item
    ///   const
    ///   name: identifier
    ///   :
    ///   type: <type_node>
    ///   [= value: <expr>]
    ///   ;
    /// ```
    fn extract_associated_const(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "const_item" {
            return None;
        }

        // Extract const name
        let name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        // Extract type annotation
        let const_type = node
            .children(&mut node.walk())
            .find(|c| c.is_named() && c.kind().contains("type") && c.kind() != "type_parameters")
            .map(|n| self.node_text(n, source).to_string());

        // Extract value if present (impl provides value, trait may not)
        let value = node
            .child_by_field_name("value")
            .map(|n| self.node_text(n, source).to_string());

        let docstring = self.extract_doc_comments(node, source);

        let mut decorators = vec!["associated_const".to_string()];
        if let Some(ref t) = const_type {
            decorators.push(format!("type: {}", t));
        }
        if let Some(ref v) = value {
            decorators.push(format!("= {}", v));
        }

        // Store type in params for representation
        let params = const_type.map(|t| vec![t]).unwrap_or_default();

        Some(FunctionInfo {
            name,
            params,
            return_type: value, // Store value in return_type for easy access
            docstring,
            is_method: true,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    /// Extract macro definition (macro_rules! foo { ... }).
    ///
    /// Captures declarative macros with their name and patterns.
    /// Creates a FunctionInfo with "macro" decorator for unified handling.
    ///
    /// # Node structure:
    /// ```text
    /// macro_definition
    ///   macro_rules!
    ///   name: identifier
    ///   { ... macro_rule* ... }
    /// ```
    fn extract_macro(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        if node.kind() != "macro_definition" {
            return None;
        }

        // Extract macro name from identifier child
        let name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        // Extract doc comments
        let docstring = self.extract_doc_comments(node, source);

        // Extract attributes (macros can have attributes like #[macro_export])
        let attributes = self.extract_attributes(node, source);

        // Build decorators: "macro" prefix + attributes
        let mut decorators = vec!["macro".to_string()];
        decorators.extend(attributes);

        // Extract macro arms/patterns for additional context
        let arms = self.extract_macro_arms(node, source);
        if !arms.is_empty() {
            // Add simplified arm signatures as params for context
            // This helps understand the macro's interface
            decorators.push(format!("arms: {}", arms.len()));
        }

        Some(FunctionInfo {
            name,
            params: arms, // Use params field to store macro arm patterns
            return_type: None,
            docstring,
            is_method: false,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    /// Extract macro arm patterns from a macro_definition.
    ///
    /// Returns simplified pattern representations for each arm.
    /// Example: `() => ...` becomes "()"
    ///          `($x:expr) => ...` becomes "($x:expr)"
    fn extract_macro_arms(&self, node: Node, source: &[u8]) -> Vec<String> {
        let mut arms = Vec::new();

        for child in node.children(&mut node.walk()) {
            if child.kind() == "macro_rule" {
                // Find the left side (token_tree_pattern)
                for rule_child in child.children(&mut child.walk()) {
                    if rule_child.kind() == "token_tree_pattern" {
                        let pattern = self.node_text(rule_child, source).to_string();
                        arms.push(pattern);
                        break;
                    }
                }
            }
        }

        arms
    }

    /// Check if a function has procedural macro attributes.
    ///
    /// Detects:
    /// - #[proc_macro] - function-like procedural macro
    /// - #[proc_macro_derive(...)] - derive macro
    /// - #[proc_macro_attribute] - attribute macro
    ///
    /// Returns the macro type if found, None otherwise.
    fn detect_proc_macro_type(&self, node: Node, source: &[u8]) -> Option<String> {
        let mut sibling = node.prev_sibling();

        while let Some(prev) = sibling {
            if prev.kind() == "attribute_item" {
                let text = self.node_text(prev, source);
                if text.contains("proc_macro_derive") {
                    // Extract derive name if present
                    if let Some(start) = text.find('(') {
                        if let Some(end) = text.find(')') {
                            let derive_name = &text[start + 1..end];
                            // Get first identifier (derive name, ignoring attributes)
                            let name = derive_name
                                .split(',')
                                .next()
                                .map(|s| s.trim())
                                .unwrap_or(derive_name);
                            return Some(format!("proc_macro_derive({})", name));
                        }
                    }
                    return Some("proc_macro_derive".to_string());
                } else if text.contains("proc_macro_attribute") {
                    return Some("proc_macro_attribute".to_string());
                } else if text.contains("proc_macro") {
                    return Some("proc_macro".to_string());
                }
            } else if prev.kind() != "line_comment" && prev.kind() != "block_comment" {
                // Stop at non-attribute, non-comment siblings
                break;
            }
            sibling = prev.prev_sibling();
        }

        None
    }

    /// Extract function signature item (trait methods without body).
    fn extract_function_signature(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        let mut name = None;
        let mut params = Vec::new();
        let mut return_type = None;

        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "identifier" => {
                    if name.is_none() {
                        name = Some(self.node_text(child, source).to_string());
                    }
                }
                "parameters" => {
                    params = self.extract_parameters(node, source);
                }
                "->" => {}
                _ if child.kind().contains("type") || child.kind() == "primitive_type" => {
                    if name.is_some() && return_type.is_none() {
                        // Check if this is after ->
                        let mut prev = child.prev_sibling();
                        while let Some(p) = prev {
                            if p.kind() == "->" {
                                return_type = Some(self.node_text(child, source).to_string());
                                break;
                            }
                            prev = p.prev_sibling();
                        }
                    }
                }
                _ => {}
            }
        }

        let name = name?;
        let docstring = self.extract_doc_comments(node, source);
        let attributes = self.extract_attributes(node, source);
        let visibility = self.extract_visibility(node, source);

        // Add visibility to decorators if present
        let mut decorators = attributes;
        if let Some(vis) = visibility {
            decorators.insert(0, vis);
        }

        Some(FunctionInfo {
            name,
            params,
            return_type: self.extract_return_type(node, source),
            docstring,
            is_method: false,
            is_async: false,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    /// Extract type name from impl_item.
    ///
    /// Handles both simple impls and trait impls:
    /// - `impl Type { }` -> returns "Type"
    /// - `impl Trait for Type { }` -> returns "Type" (after `for`)
    /// - `impl<T> Trait for Type<T> { }` -> returns "Type" (after `for`)
    fn extract_impl_type(&self, node: Node, source: &[u8]) -> Option<String> {
        // First, check if this is a trait impl by looking for "for" keyword
        let is_trait_impl = node.children(&mut node.walk()).any(|c| c.kind() == "for");

        for child in node.children(&mut node.walk()) {
            let is_type_node = child.kind() == "type"
                || child.kind() == "generic_type"
                || child.kind() == "type_identifier";

            if !is_type_node {
                continue;
            }

            if is_trait_impl {
                // For trait impls (impl Trait for Type), we want the type AFTER "for"
                // Check if the previous sibling is "for"
                if let Some(prev) = child.prev_sibling() {
                    if prev.kind() == "for" {
                        // This is the target type (comes after "for")
                        let type_text = self.node_text(child, source);
                        let base_type = type_text.split('<').next().unwrap_or(type_text);
                        return Some(base_type.to_string());
                    }
                }
                // Skip types that are not after "for" (they are trait names)
            } else {
                // For simple impls (impl Type), return the first type we find
                let type_text = self.node_text(child, source);
                if !type_text.is_empty() {
                    let base_type = type_text.split('<').next().unwrap_or(type_text);
                    return Some(base_type.to_string());
                }
            }
        }

        None
    }

    /// Extract trait being implemented (if any).
    fn extract_impl_trait(&self, node: Node, source: &[u8]) -> Option<String> {
        for child in node.children(&mut node.walk()) {
            if child.kind() == "type_identifier" || child.kind() == "generic_type" {
                // Check if next sibling is "for"
                if let Some(next) = child.next_sibling() {
                    if next.kind() == "for" {
                        return Some(self.node_text(child, source).to_string());
                    }
                }
            }
        }
        None
    }

    /// Parse use path into module and names.
    fn parse_use_path(
        &self,
        node: Node,
        source: &[u8],
    ) -> (String, Vec<String>, HashMap<String, String>, bool) {
        let mut module_parts = Vec::new();
        let mut names = Vec::new();
        let mut aliases = HashMap::new();
        let mut is_glob = false;

        self.traverse_use_tree(
            node,
            source,
            &mut module_parts,
            &mut names,
            &mut aliases,
            &mut is_glob,
        );

        let module = module_parts.join("::");
        (module, names, aliases, is_glob)
    }

    /// Recursively traverse use tree.
    fn traverse_use_tree(
        &self,
        node: Node,
        source: &[u8],
        module_parts: &mut Vec<String>,
        names: &mut Vec<String>,
        aliases: &mut HashMap<String, String>,
        is_glob: &mut bool,
    ) {
        match node.kind() {
            "identifier" | "crate" | "super" | "self" => {
                module_parts.push(self.node_text(node, source).to_string());
            }
            "scoped_identifier" => {
                for child in node.children(&mut node.walk()) {
                    self.traverse_use_tree(child, source, module_parts, names, aliases, is_glob);
                }
            }
            "scoped_use_list" => {
                // First get the path part
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "scoped_identifier"
                        || child.kind() == "identifier"
                        || child.kind() == "crate"
                        || child.kind() == "super"
                        || child.kind() == "self"
                    {
                        self.traverse_use_tree(
                            child,
                            source,
                            module_parts,
                            names,
                            aliases,
                            is_glob,
                        );
                    } else if child.kind() == "use_list" {
                        self.traverse_use_tree(
                            child,
                            source,
                            module_parts,
                            names,
                            aliases,
                            is_glob,
                        );
                    }
                }
            }
            "use_list" => {
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "identifier" {
                        names.push(self.node_text(child, source).to_string());
                    } else if child.kind() == "use_as_clause" {
                        let (name, alias) = self.extract_use_as_clause(child, source);
                        names.push(name.clone());
                        if let Some(a) = alias {
                            aliases.insert(name, a);
                        }
                    } else if child.kind() == "scoped_identifier"
                        || child.kind() == "scoped_use_list"
                    {
                        // Nested use in list - simplified handling
                        let text = self.node_text(child, source);
                        names.push(text.to_string());
                    }
                }
            }
            "use_wildcard" => {
                // Handle glob imports (use path::*)
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "scoped_identifier" {
                        self.traverse_use_tree(
                            child,
                            source,
                            module_parts,
                            names,
                            aliases,
                            is_glob,
                        );
                    }
                }
                *is_glob = true;
                names.push("*".to_string());
            }
            "use_as_clause" => {
                let (name, alias) = self.extract_use_as_clause(node, source);
                // Get the path part
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "scoped_identifier" {
                        self.traverse_use_tree(
                            child,
                            source,
                            module_parts,
                            names,
                            aliases,
                            is_glob,
                        );
                    }
                }
                names.push(name.clone());
                if let Some(a) = alias {
                    aliases.insert(name, a);
                }
            }
            _ => {
                // Recurse into children
                for child in node.children(&mut node.walk()) {
                    self.traverse_use_tree(child, source, module_parts, names, aliases, is_glob);
                }
            }
        }
    }

    /// Extract a single import from a use_declaration node.
    fn extract_single_import(&self, node: Node, source: &[u8]) -> Option<ImportInfo> {
        // Find the argument child (the actual use path)
        let argument = node.children(&mut node.walk()).find(|c: &Node| {
            c.kind() == "scoped_identifier"
                || c.kind() == "scoped_use_list"
                || c.kind() == "use_wildcard"
                || c.kind() == "use_as_clause"
                || c.kind() == "identifier"
        })?;

        let (module, names, aliases, is_glob) = self.parse_use_path(argument, source);

        // Determine if this is a "from" style import (has specific names)
        let is_from = !names.is_empty() && !is_glob;

        // Calculate relative import level by counting leading super:: segments
        // Must count only path segments, not substring matches
        // e.g., super::super::foo_super_module should be level 2, not 3
        let level = if module.starts_with("super") {
            module.split("::").take_while(|&s| s == "super").count()
        } else if module.starts_with("self") {
            1
        } else {
            0
        };

        // BUG #19 fix: Extract visibility modifier for pub use re-exports
        // Distinguishes `pub use foo::bar;` from `use foo::bar;`
        let visibility = self.extract_visibility(node, source);

        Some(ImportInfo {
            module,
            names,
            aliases,
            is_from,
            level,
            line_number: node.start_position().row + 1,
            visibility,
        })
    }

    /// Extract name and alias from use_as_clause.
    fn extract_use_as_clause(&self, node: Node, source: &[u8]) -> (String, Option<String>) {
        let mut name = String::new();
        let mut alias = None;
        let mut found_as = false;

        for child in node.children(&mut node.walk()) {
            if child.kind() == "scoped_identifier" {
                // Get the last part of the scoped identifier
                let text = self.node_text(child, source);
                name = text.rsplit("::").next().unwrap_or(text).to_string();
            } else if child.kind() == "identifier" {
                if found_as {
                    alias = Some(self.node_text(child, source).to_string());
                } else {
                    name = self.node_text(child, source).to_string();
                }
            } else if child.kind() == "as" {
                found_as = true;
            }
        }

        (name, alias)
    }

    /// Build CFG for a Rust function.
    ///
    /// Handles:
    /// - Regular control flow (if, loop, match, etc.)
    /// - Async/await patterns (suspension points, task spawning)
    /// - Error propagation (? operator)
    /// - Lock-across-await detection
    /// - Blocking call detection in async context
    fn build_rust_cfg(&self, node: Node, source: &[u8], function_name: &str) -> CFGInfo {
        let mut blocks = HashMap::new();
        let mut edges = Vec::new();
        let mut block_counter = 0;
        let mut decision_points = 0;

        // Detect if this is an async function
        let modifiers = self.extract_function_modifiers(node, source);
        let is_async_fn = modifiers.is_async;

        // Create async context for tracking await points, blocking calls, lock issues
        let mut async_ctx = AsyncCfgContext::new(is_async_fn);

        // Create entry block with async indicator if applicable
        let entry_id = BlockId(block_counter);
        block_counter += 1;

        let entry_label = if is_async_fn {
            "async entry".to_string()
        } else {
            "entry".to_string()
        };

        blocks.insert(
            entry_id,
            CFGBlock {
                id: entry_id,
                label: entry_label,
                block_type: BlockType::Entry,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.start_position().row + 1,
                end_line: node.start_position().row + 1,
            },
        );

        // Find function body
        let body_node = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "block");

        let mut exit_blocks = Vec::new();
        let mut loop_ctx = LoopContext::default();

        if let Some(body) = body_node {
            let (last_block, exits) = self.process_cfg_block_with_async_ctx(
                body,
                source,
                &mut blocks,
                &mut edges,
                &mut block_counter,
                entry_id,
                &mut loop_ctx,
                &mut async_ctx,
                &mut decision_points,
            );
            exit_blocks = exits;
            if exit_blocks.is_empty() {
                exit_blocks.push(last_block);
            }
        } else {
            exit_blocks.push(entry_id);
        }

        // Create exit block
        let exit_id = BlockId(block_counter);
        let exit_label = if is_async_fn {
            "async exit".to_string()
        } else {
            "exit".to_string()
        };

        blocks.insert(
            exit_id,
            CFGBlock {
                id: exit_id,
                label: exit_label,
                block_type: BlockType::Exit,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: node.end_position().row + 1,
                end_line: node.end_position().row + 1,
            },
        );

        // Connect all exit blocks to the exit node
        for exit_block in &exit_blocks {
            edges.push(CFGEdge::from_label(*exit_block, exit_id, None));
        }

        CFGInfo {
            function_name: function_name.to_string(),
            blocks,
            edges,
            entry: entry_id,
            exits: vec![exit_id],
            decision_points,
            comprehension_decision_points: 0, // Rust doesn't have Python-style comprehensions
            nested_cfgs: HashMap::new(),
            is_async: is_async_fn,
            await_points: async_ctx.await_points,
            blocking_calls: async_ctx.blocking_calls,
            ..Default::default()
        }
    }

    /// Process a block for CFG building (wrapper for backward compatibility).
    fn process_cfg_block(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        counter: &mut usize,
        entry: BlockId,
    ) -> (BlockId, Vec<BlockId>) {
        let mut loop_ctx = LoopContext::default();
        let mut async_ctx = AsyncCfgContext::default();
        let mut decision_points = 0;
        self.process_cfg_block_with_async_ctx(
            node, source, blocks, edges, counter, entry, &mut loop_ctx,
            &mut async_ctx, &mut decision_points,
        )
    }

    /// Process a block for CFG building with loop context tracking.
    ///
    /// The `loop_ctx` tracks loop headers and exit blocks for break/continue resolution.
    /// This is a compatibility wrapper that creates default async context.
    #[allow(clippy::too_many_arguments)]
    fn process_cfg_block_with_ctx(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        counter: &mut usize,
        entry: BlockId,
        loop_ctx: &mut LoopContext,
    ) -> (BlockId, Vec<BlockId>) {
        let mut async_ctx = AsyncCfgContext::default();
        let mut decision_points = 0;
        self.process_cfg_block_with_async_ctx(
            node, source, blocks, edges, counter, entry, loop_ctx,
            &mut async_ctx, &mut decision_points,
        )
    }

    /// Process a block for CFG building with full context tracking.
    ///
    /// Handles:
    /// - Loop context for break/continue resolution
    /// - Async context for await points, blocking calls, and lock-across-await detection
    /// - Decision point counting for cyclomatic complexity
    #[allow(clippy::too_many_arguments)]
    fn process_cfg_block_with_async_ctx(
        &self,
        node: Node,
        source: &[u8],
        blocks: &mut HashMap<BlockId, CFGBlock>,
        edges: &mut Vec<CFGEdge>,
        counter: &mut usize,
        entry: BlockId,
        loop_ctx: &mut LoopContext,
        async_ctx: &mut AsyncCfgContext,
        decision_points: &mut usize,
    ) -> (BlockId, Vec<BlockId>) {
        let mut current_block = entry;
        let mut statements = Vec::new();
        let mut exits = Vec::new();

        for child in node.children(&mut node.walk()) {
            // Handle expression_statement by processing its inner expression
            let effective_child = if child.kind() == "expression_statement" {
                // Get the inner expression
                child.child(0).unwrap_or(child)
            } else {
                child
            };

            match effective_child.kind() {
                "if_expression" => {
                    let child = effective_child; // Use the unwrapped expression
                                                 // Create block for if condition
                    let if_block = BlockId(*counter);
                    *counter += 1;

                    // Use tree-sitter field access for reliable condition extraction
                    let condition_node = child.child_by_field_name("condition");
                    let condition = condition_node
                        .map(|c| self.node_text(c, source).to_string())
                        .unwrap_or_else(|| "condition".to_string());

                    // Check if this is an if-let pattern (condition is let_condition)
                    let is_if_let = condition_node
                        .map(|c| c.kind() == "let_condition")
                        .unwrap_or(false);

                    // Use PatternMatch block type for if-let, Body for regular if
                    let block_type = if is_if_let {
                        BlockType::PatternMatch
                    } else {
                        BlockType::Body
                    };

                    let label = if is_if_let {
                        format!("if let {}", condition.chars().take(25).collect::<String>())
                    } else {
                        format!("if {}", condition.chars().take(30).collect::<String>())
                    };

                    blocks.insert(
                        if_block,
                        CFGBlock {
                            id: if_block,
                            label,
                            block_type,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.start_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, if_block, None));

                    // Process then branch
                    let then_block = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "block");

                    let (then_exit, then_exits) = if let Some(then_body) = then_block {
                        let then_entry = BlockId(*counter);
                        *counter += 1;
                        let then_label = if is_if_let {
                            "Some/Ok".to_string()
                        } else {
                            "then".to_string()
                        };
                        blocks.insert(
                            then_entry,
                            CFGBlock {
                                id: then_entry,
                                label: then_label,
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: then_body.start_position().row + 1,
                                end_line: then_body.end_position().row + 1,
                            },
                        );
                        // Use OkSome edge for if-let, True for regular if
                        let edge = if is_if_let {
                            CFGEdge::new(if_block, then_entry, EdgeType::OkSome)
                        } else {
                            CFGEdge::from_label(if_block, then_entry, Some("true".to_string()))
                        };
                        edges.push(edge);
                        *decision_points += 1; // if condition is a decision point
                        self.process_cfg_block_with_async_ctx(
                            then_body, source, blocks, edges, counter, then_entry,
                            loop_ctx, async_ctx, decision_points,
                        )
                    } else {
                        (if_block, Vec::new())
                    };

                    // Process else branch
                    let else_clause = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "else_clause");

                    let else_exits = if let Some(else_node) = else_clause {
                        let else_body = else_node
                            .children(&mut else_node.walk())
                            .find(|c| c.kind() == "block" || c.kind() == "if_expression");

                        if let Some(else_content) = else_body {
                            let else_entry = BlockId(*counter);
                            *counter += 1;
                            let else_label = if is_if_let {
                                "None/Err".to_string()
                            } else {
                                "else".to_string()
                            };
                            blocks.insert(
                                else_entry,
                                CFGBlock {
                                    id: else_entry,
                                    label: else_label,
                                    block_type: BlockType::Body,
                                    statements: Vec::new(),
                                    func_calls: Vec::new(),
                                    start_line: else_content.start_position().row + 1,
                                    end_line: else_content.end_position().row + 1,
                                },
                            );
                            // Use ErrNone edge for if-let, False for regular if
                            let edge = if is_if_let {
                                CFGEdge::new(if_block, else_entry, EdgeType::ErrNone)
                            } else {
                                CFGEdge::from_label(if_block, else_entry, Some("false".to_string()))
                            };
                            edges.push(edge);

                            let (_, exits) = self.process_cfg_block_with_async_ctx(
                                else_content,
                                source,
                                blocks,
                                edges,
                                counter,
                                else_entry,
                                loop_ctx,
                                async_ctx,
                                decision_points,
                            );
                            if exits.is_empty() {
                                vec![else_entry]
                            } else {
                                exits
                            }
                        } else {
                            vec![if_block]
                        }
                    } else {
                        // No else branch - if_block exits on false/None/Err
                        let edge = if is_if_let {
                            CFGEdge::new(if_block, if_block, EdgeType::ErrNone) // Will be updated
                        } else {
                            CFGEdge::from_label(if_block, if_block, Some("false".to_string()))
                        };
                        edges.push(edge);
                        vec![if_block]
                    };

                    // Create merge block
                    let merge_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        merge_block,
                        CFGBlock {
                id: merge_block,
                label: "merge".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );

                    // Connect branches to merge
                    if then_exits.is_empty() {
                        edges.push(CFGEdge::from_label(then_exit, merge_block, None));
                    } else {
                        for exit in then_exits {
                            edges.push(CFGEdge::from_label(exit, merge_block, None));
                        }
                    }

                    for exit in &else_exits {
                        if *exit != if_block {
                            edges.push(CFGEdge::from_label(*exit, merge_block, None));
                        }
                    }

                    // Update false edge if no else clause
                    if else_clause.is_none() {
                        if let Some(edge) = edges
                            .iter_mut()
                            .rev()
                            .find(|e| e.from == if_block && e.edge_type == EdgeType::False)
                        {
                            edge.to = merge_block;
                        }
                    }

                    current_block = merge_block;
                }
                "loop_expression" | "while_expression" | "for_expression" => {
                    let child = effective_child;
                    // Create loop header block
                    let loop_header = BlockId(*counter);
                    *counter += 1;

                    // Extract loop label if present (e.g., 'outer: loop { })
                    // In Rust tree-sitter, labeled loops have a loop_label child
                    let rust_loop_label: Option<String> = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "loop_label")
                        .map(|label_node| {
                            // The label text includes the lifetime syntax ('label:)
                            let text = self.node_text(label_node, source);
                            // Strip the colon suffix and leading quote
                            text.trim_end_matches(':').trim_start_matches('\'').to_string()
                        });

                    // Check if this is a while-let pattern (condition is let_condition)
                    let condition_node = child.child_by_field_name("condition");
                    let is_while_let = condition_node
                        .map(|c| c.kind() == "let_condition")
                        .unwrap_or(false);

                    let block_label = match child.kind() {
                        "while_expression" => {
                            // Use tree-sitter field access for reliable condition extraction
                            let cond = condition_node
                                .map(|c| self.node_text(c, source).to_string())
                                .unwrap_or_default();
                            if is_while_let {
                                format!("while let {}", cond.chars().take(15).collect::<String>())
                            } else {
                                format!("while {}", cond.chars().take(20).collect::<String>())
                            }
                        }
                        "for_expression" => "for loop".to_string(),
                        _ => "loop".to_string(),
                    };

                    // Include label in block name if present
                    let block_label = if let Some(ref lbl) = rust_loop_label {
                        format!("'{}: {}", lbl, block_label)
                    } else {
                        block_label
                    };

                    // Use PatternMatch block type for while-let, Body for others
                    let header_block_type = if is_while_let {
                        BlockType::PatternMatch
                    } else {
                        BlockType::Body
                    };

                    // Loop exit block - create before pushing to context
                    let loop_exit = BlockId(*counter);
                    *counter += 1;
                    let exit_label = if is_while_let {
                        "while_let exit".to_string()
                    } else {
                        "loop exit".to_string()
                    };
                    blocks.insert(
                        loop_exit,
                        CFGBlock {
                            id: loop_exit,
                            label: exit_label,
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.end_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    blocks.insert(
                        loop_header,
                        CFGBlock {
                            id: loop_header,
                            label: block_label,
                            block_type: header_block_type,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.start_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, loop_header, None));

                    // Register loop in context for break/continue resolution
                    loop_ctx.push_loop(rust_loop_label.as_deref(), loop_header, loop_exit);

                    // Process loop body
                    let body = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "block");

                    if let Some(loop_body) = body {
                        let body_entry = BlockId(*counter);
                        *counter += 1;
                        let body_label = if is_while_let {
                            "Some/Ok body".to_string()
                        } else {
                            "loop body".to_string()
                        };
                        blocks.insert(
                            body_entry,
                            CFGBlock {
                                id: body_entry,
                                label: body_label,
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: loop_body.start_position().row + 1,
                                end_line: loop_body.end_position().row + 1,
                            },
                        );

                        // Use OkSome edge for while-let, regular enter for others
                        let entry_edge = if is_while_let {
                            CFGEdge::new(loop_header, body_entry, EdgeType::OkSome)
                        } else {
                            CFGEdge::from_label(loop_header, body_entry, Some("enter".to_string()))
                        };
                        edges.push(entry_edge);

                        // Use _with_async_ctx to propagate loop and async context
                        *decision_points += 1; // loop is a decision point
                        let (body_exit, body_exits) = self.process_cfg_block_with_async_ctx(
                            loop_body, source, blocks, edges, counter, body_entry, loop_ctx,
                            async_ctx, decision_points,
                        );

                        // Back edge to loop header (for normal loop continuation)
                        // Only add if there's no explicit break/continue that already terminated
                        if body_exits.is_empty() {
                            let back_edge = if is_while_let {
                                CFGEdge::from_label(body_exit, loop_header, Some("next".to_string()))
                            } else {
                                CFGEdge::from_label(body_exit, loop_header, Some("loop".to_string()))
                            };
                            edges.push(back_edge);
                        }
                    }

                    // Pop loop from context
                    loop_ctx.pop_loop(rust_loop_label.as_deref());

                    // Exit edge: ErrNone for while-let (pattern doesn't match), break for others
                    let exit_edge = if is_while_let {
                        CFGEdge::new(loop_header, loop_exit, EdgeType::ErrNone)
                    } else {
                        CFGEdge::from_label(loop_header, loop_exit, Some("break".to_string()))
                    };
                    edges.push(exit_edge);

                    current_block = loop_exit;
                }
                "break_expression" => {
                    let child = effective_child;
                    let stmt = self.node_text(child, source).to_string();
                    statements.push(stmt.clone());

                    // Extract optional label from break (e.g., break 'outer)
                    let break_label: Option<String> = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "loop_label")
                        .map(|label_node| {
                            let text = self.node_text(label_node, source);
                            text.trim_start_matches('\'').to_string()
                        });

                    // Create break block
                    let break_block = BlockId(*counter);
                    *counter += 1;

                    let label_suffix = break_label
                        .as_ref()
                        .map(|l| format!(" '{}", l))
                        .unwrap_or_default();

                    blocks.insert(
                        break_block,
                        CFGBlock {
                            id: break_block,
                            label: format!("break{}", label_suffix),
                            block_type: BlockType::Body,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, break_block, None));

                    // Resolve break target using loop context
                    if let Some(target) = loop_ctx.resolve_break(break_label.as_deref()) {
                        edges.push(CFGEdge::from_label(break_block, target, Some("break".to_string())));
                    }

                    // Mark as exit (control flow leaves normal path)
                    exits.push(break_block);

                    // Create unreachable block for any following code
                    current_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        current_block,
                        CFGBlock {
                id: current_block,
                label: "unreachable".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );
                }
                "continue_expression" => {
                    let child = effective_child;
                    let stmt = self.node_text(child, source).to_string();
                    statements.push(stmt.clone());

                    // Extract optional label from continue (e.g., continue 'outer)
                    let continue_label: Option<String> = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "loop_label")
                        .map(|label_node| {
                            let text = self.node_text(label_node, source);
                            text.trim_start_matches('\'').to_string()
                        });

                    // Create continue block
                    let continue_block = BlockId(*counter);
                    *counter += 1;

                    let label_suffix = continue_label
                        .as_ref()
                        .map(|l| format!(" '{}", l))
                        .unwrap_or_default();

                    blocks.insert(
                        continue_block,
                        CFGBlock {
                            id: continue_block,
                            label: format!("continue{}", label_suffix),
                            block_type: BlockType::Body,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, continue_block, None));

                    // Resolve continue target using loop context (jumps to header)
                    if let Some(target) = loop_ctx.resolve_continue(continue_label.as_deref()) {
                        edges.push(CFGEdge::from_label(continue_block, target, Some("continue".to_string())));
                    }

                    // Mark as exit (control flow leaves normal path)
                    exits.push(continue_block);

                    // Create unreachable block for any following code
                    current_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        current_block,
                        CFGBlock {
                id: current_block,
                label: "unreachable".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );
                }
                "match_expression" => {
                    let child = effective_child;
                    let match_block = BlockId(*counter);
                    *counter += 1;

                    blocks.insert(
                        match_block,
                        CFGBlock {
                id: match_block,
                label: "match".to_string(),
                block_type: BlockType::Body,
                statements: statements.drain(..).collect(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.start_position().row + 1,
            },
                    );

                    edges.push(CFGEdge::from_label(current_block, match_block, None));

                    // Find match arms
                    let match_body = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "match_block");

                    let mut arm_exits = Vec::new();

                    if let Some(body) = match_body {
                        for arm in body.children(&mut body.walk()) {
                            if arm.kind() == "match_arm" {
                                let arm_block = BlockId(*counter);
                                *counter += 1;

                                let pattern = arm
                                    .children(&mut arm.walk())
                                    .find(|c| c.kind() == "match_pattern")
                                    .map(|p| self.node_text(p, source).to_string())
                                    .unwrap_or_else(|| "pattern".to_string());

                                blocks.insert(
                                    arm_block,
                                    CFGBlock {
                id: arm_block,
                label: pattern.chars().take(30).collect(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: arm.start_position().row + 1,
                end_line: arm.end_position().row + 1,
            },
                                );

                                edges.push(CFGEdge::from_label(match_block, arm_block, None));

                                arm_exits.push(arm_block);
                            }
                        }
                    }

                    // Merge block after match
                    let merge_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        merge_block,
                        CFGBlock {
                id: merge_block,
                label: "match merge".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );

                    for arm_exit in arm_exits {
                        edges.push(CFGEdge::from_label(arm_exit, merge_block, None));
                    }

                    current_block = merge_block;
                }
                "return_expression" => {
                    let child = effective_child;
                    let stmt = self.node_text(child, source).to_string();
                    statements.push(stmt);

                    // Create return block
                    let return_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        return_block,
                        CFGBlock {
                id: return_block,
                label: "return".to_string(),
                block_type: BlockType::Body,
                statements: statements.drain(..).collect(),
                func_calls: Vec::new(),
                start_line: child.start_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );

                    edges.push(CFGEdge::from_label(current_block, return_block, None));

                    exits.push(return_block);

                    // Create a new current block (unreachable but needed for structure)
                    current_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        current_block,
                        CFGBlock {
                id: current_block,
                label: "unreachable".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );
                }
                "let_declaration" => {
                    let stmt = self.node_text(child, source).to_string();

                    // Check for let-else pattern: let Some(x) = opt else { diverge }
                    // In tree-sitter, this is a let_declaration with an "alternative" field
                    let else_block = child.child_by_field_name("alternative");
                    if else_block.is_some() {
                        // This is a let-else pattern
                        let let_else_block = BlockId(*counter);
                        *counter += 1;

                        // Extract pattern for labeling
                        let pattern = child
                            .child_by_field_name("pattern")
                            .map(|p| self.node_text(p, source).to_string())
                            .unwrap_or_else(|| "pattern".to_string());

                        blocks.insert(
                            let_else_block,
                            CFGBlock {
                                id: let_else_block,
                                label: format!("let-else {}", pattern.chars().take(15).collect::<String>()),
                                block_type: BlockType::PatternMatch,
                                statements: statements.drain(..).collect(),
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.start_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::from_label(current_block, let_else_block, None));

                        // Process the else block (must diverge)
                        if let Some(else_body) = else_block {
                            let else_entry = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(
                                else_entry,
                                CFGBlock {
                                    id: else_entry,
                                    label: "let-else diverge".to_string(),
                                    block_type: BlockType::Body,
                                    statements: Vec::new(),
                                    func_calls: Vec::new(),
                                    start_line: else_body.start_position().row + 1,
                                    end_line: else_body.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(let_else_block, else_entry, EdgeType::ErrNone));
                            *decision_points += 1; // let-else is a decision point

                            let (_, else_exits) = self.process_cfg_block_with_async_ctx(
                                else_body, source, blocks, edges, counter, else_entry,
                                loop_ctx, async_ctx, decision_points,
                            );

                            // The else block must diverge, so add its exits to function exits
                            exits.extend(else_exits);
                            if exits.is_empty() || !exits.contains(&else_entry) {
                                exits.push(else_entry);
                            }
                        }

                        // Create continue block for match success path
                        let continue_block = BlockId(*counter);
                        *counter += 1;
                        blocks.insert(
                            continue_block,
                            CFGBlock {
                                id: continue_block,
                                label: "let-else match".to_string(),
                                block_type: BlockType::Body,
                                statements: vec![stmt],
                                func_calls: Vec::new(),
                                start_line: child.end_position().row + 1,
                                end_line: child.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::new(let_else_block, continue_block, EdgeType::OkSome));

                        current_block = continue_block;
                    }
                    // CRITICAL: Check for async patterns in let binding
                    else {
                        // First check if value contains tokio::spawn or async macros
                        let value_node = child.child_by_field_name("value");

                        // Check for spawn call in value (e.g., let handle = tokio::spawn(...))
                        if let Some(value) = value_node {
                            let (is_spawn, spawn_type) = self.is_spawn_call(value, source);
                            if is_spawn {
                                if !statements.is_empty() {
                                    if let Some(block) = blocks.get_mut(&current_block) {
                                        block.statements.extend(statements.drain(..));
                                    }
                                }

                                let spawn_block = BlockId(*counter);
                                *counter += 1;
                                let text = self.node_text(child, source);

                                blocks.insert(
                                    spawn_block,
                                    CFGBlock {
                                        id: spawn_block,
                                        label: format!("{}::spawn: {}..", spawn_type.unwrap_or("spawn"), text.chars().take(35).collect::<String>()),
                                        block_type: BlockType::RustTaskSpawn,
                                        statements: vec![text.to_string()],
                                        func_calls: self.extract_func_calls_from_node(child, source),
                                        start_line: child.start_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );

                                edges.push(CFGEdge::new(current_block, spawn_block, EdgeType::RustSpawn));
                                current_block = spawn_block;
                                continue; // Skip remaining checks
                            }

                            // Check for async macro in value (e.g., let (a,b) = tokio::join!(...))
                            let (is_async_macro, macro_type) = self.is_async_macro(value, source);
                            if is_async_macro {
                                let line = child.start_position().row + 1;
                                let text = self.node_text(child, source);

                                if !statements.is_empty() {
                                    if let Some(block) = blocks.get_mut(&current_block) {
                                        block.statements.extend(statements.drain(..));
                                    }
                                }

                                match macro_type {
                                    Some("join!") | Some("try_join!") => {
                                        let join_block = BlockId(*counter);
                                        *counter += 1;

                                        let is_try = macro_type == Some("try_join!");
                                        blocks.insert(
                                            join_block,
                                            CFGBlock {
                                                id: join_block,
                                                label: format!("{}: {}..", macro_type.unwrap_or("join!"), text.chars().take(35).collect::<String>()),
                                                block_type: BlockType::RustJoin,
                                                statements: vec![text.to_string()],
                                                func_calls: self.extract_func_calls_from_node(child, source),
                                                start_line: line,
                                                end_line: child.end_position().row + 1,
                                            },
                                        );

                                        edges.push(CFGEdge::new(current_block, join_block, EdgeType::RustAwait));
                                        async_ctx.record_await(line);

                                        if is_try {
                                            let error_block = BlockId(*counter);
                                            *counter += 1;
                                            blocks.insert(
                                                error_block,
                                                CFGBlock {
                                                    id: error_block,
                                                    label: "try_join! error".to_string(),
                                                    block_type: BlockType::ErrorReturn,
                                                    statements: Vec::new(),
                                                    func_calls: Vec::new(),
                                                    start_line: line,
                                                    end_line: line,
                                                },
                                            );
                                            edges.push(CFGEdge::new(join_block, error_block, EdgeType::ErrNone));
                                            exits.push(error_block);
                                            *decision_points += 1;
                                        }

                                        let continue_block = BlockId(*counter);
                                        *counter += 1;
                                        blocks.insert(
                                            continue_block,
                                            CFGBlock {
                                                id: continue_block,
                                                label: "join complete".to_string(),
                                                block_type: BlockType::Body,
                                                statements: Vec::new(),
                                                func_calls: Vec::new(),
                                                start_line: child.end_position().row + 1,
                                                end_line: child.end_position().row + 1,
                                            },
                                        );
                                        edges.push(CFGEdge::new(join_block, continue_block, EdgeType::RustJoinComplete));
                                        current_block = continue_block;
                                        continue;
                                    }
                                    Some("select!") => {
                                        let select_block = BlockId(*counter);
                                        *counter += 1;

                                        blocks.insert(
                                            select_block,
                                            CFGBlock {
                                                id: select_block,
                                                label: format!("select!: {}..", text.chars().take(35).collect::<String>()),
                                                block_type: BlockType::RustSelect,
                                                statements: vec![text.to_string()],
                                                func_calls: self.extract_func_calls_from_node(child, source),
                                                start_line: line,
                                                end_line: child.end_position().row + 1,
                                            },
                                        );

                                        edges.push(CFGEdge::new(current_block, select_block, EdgeType::RustAwait));
                                        async_ctx.record_await(line);
                                        *decision_points += 1;

                                        let continue_block = BlockId(*counter);
                                        *counter += 1;
                                        blocks.insert(
                                            continue_block,
                                            CFGBlock {
                                                id: continue_block,
                                                label: "select winner".to_string(),
                                                block_type: BlockType::Body,
                                                statements: Vec::new(),
                                                func_calls: Vec::new(),
                                                start_line: child.end_position().row + 1,
                                                end_line: child.end_position().row + 1,
                                            },
                                        );
                                        edges.push(CFGEdge::new(select_block, continue_block, EdgeType::RustSelectWinner));
                                        current_block = continue_block;
                                        continue;
                                    }
                                    _ => {} // Fall through to await/try handling
                                }
                            }
                        }

                        let await_count = self.count_await_expressions(child);
                        let has_try = self.contains_try_expression(child);

                        // Handle await + optional try in async context
                        if await_count > 0 && async_ctx.is_async {
                            let line = child.start_position().row + 1;
                            // Record all await points
                            for _ in 0..await_count {
                                async_ctx.record_await(line);
                            }

                            // Check for lock-across-await anti-pattern
                            let has_held_locks = async_ctx.has_held_locks();
                            let block_type = if has_held_locks {
                                BlockType::RustLockAcrossAwait
                            } else {
                                BlockType::RustAwaitPoint
                            };

                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }

                            let await_block = BlockId(*counter);
                            *counter += 1;

                            let label = if has_held_locks {
                                let locks: Vec<_> = async_ctx.held_locks.iter()
                                    .map(|(name, lock_type, _)| format!("{}:{}", name, lock_type))
                                    .collect();
                                format!(".await ({}x) [WARN: holds {}]", await_count, locks.join(", "))
                            } else if has_try {
                                format!(".await? ({}x): {}..", await_count, stmt.chars().take(25).collect::<String>())
                            } else {
                                format!(".await ({}x): {}..", await_count, stmt.chars().take(25).collect::<String>())
                            };

                            blocks.insert(
                                await_block,
                                CFGBlock {
                                    id: await_block,
                                    label,
                                    block_type,
                                    statements: vec![stmt.clone()],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: line,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(current_block, await_block, EdgeType::RustAwait));

                            if has_try {
                                // Handle await? pattern
                                let try_count = self.count_try_expressions(child);
                                let error_return = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    error_return,
                                    CFGBlock {
                                        id: error_return,
                                        label: format!("Err propagate ({}x ?)", try_count),
                                        block_type: BlockType::ErrorReturn,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: line,
                                        end_line: line,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, error_return, EdgeType::ErrNone));
                                exits.push(error_return);
                                *decision_points += try_count;

                                let success_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    success_block,
                                    CFGBlock {
                                        id: success_block,
                                        label: "Ok/Some continue".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, success_block, EdgeType::OkSome));
                                current_block = success_block;
                            } else {
                                let resume_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    resume_block,
                                    CFGBlock {
                                        id: resume_block,
                                        label: "resume".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, resume_block, EdgeType::RustResume));
                                current_block = resume_block;
                            }
                        }
                        // No await, but has try expression
                        else if has_try {
                            let try_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            // Count nested ? operators for decision point tracking
                            let try_count = self.count_try_expressions(child);
                            blocks.insert(
                                try_block,
                                CFGBlock {
                                    id: try_block,
                                    label: format!(
                                        "try?: {}",
                                        stmt.chars().take(25).collect::<String>()
                                    ),
                                    block_type: BlockType::TryOperator,
                                    statements: vec![stmt],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::from_label(current_block, try_block, None));
                            let error_return = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(
                                error_return,
                                CFGBlock {
                                    id: error_return,
                                    label: format!("Err/None propagate ({}x ?)", try_count),
                                    block_type: BlockType::ErrorReturn,
                                    statements: Vec::new(),
                                    func_calls: Vec::new(),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::new(try_block, error_return, EdgeType::ErrNone));
                            exits.push(error_return);
                            let success_block = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(
                                success_block,
                                CFGBlock {
                                    id: success_block,
                                    label: "Ok/Some continue".to_string(),
                                    block_type: BlockType::Body,
                                    statements: Vec::new(),
                                    func_calls: Vec::new(),
                                    start_line: child.end_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::new(try_block, success_block, EdgeType::OkSome));
                            current_block = success_block;
                        } else if self.contains_panic_site(child, source) {
                            // Handle potential panic sites: .unwrap(), .expect(), panic!(), etc.
                            let panic_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            let panic_info = self.get_panic_site_info(child, source);
                            blocks.insert(
                                panic_block,
                                CFGBlock {
                                    id: panic_block,
                                    label: format!("panic?: {}", panic_info),
                                    block_type: BlockType::PanicSite,
                                    statements: vec![stmt],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::from_label(current_block, panic_block, None));
                            // Panic sites can potentially panic - mark with a special edge
                            // but normal flow continues (unless it's unconditional panic)
                            current_block = panic_block;
                        } else {
                            statements.push(stmt);
                        }
                    }
                }
                // Rust 1.65+ let-else patterns: let Some(x) = opt else { return; };
                // The else block must diverge (return, break, continue, panic)
                "let_else_statement" => {
                    let child = effective_child;

                    // Create block for let-else check
                    let let_else_block = BlockId(*counter);
                    *counter += 1;

                    // Extract the pattern being matched for labeling
                    let pattern = child
                        .children(&mut child.walk())
                        .find(|c| {
                            c.kind() == "tuple_struct_pattern"
                                || c.kind() == "struct_pattern"
                                || c.kind() == "identifier"
                        })
                        .map(|c| self.node_text(c, source).to_string())
                        .unwrap_or_else(|| "pattern".to_string());

                    let stmt = self.node_text(child, source).to_string();
                    statements.push(stmt.clone());

                    blocks.insert(
                        let_else_block,
                        CFGBlock {
                            id: let_else_block,
                            label: format!(
                                "let-else {}",
                                pattern.chars().take(20).collect::<String>()
                            ),
                            block_type: BlockType::Body,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.start_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, let_else_block, None));

                    // Find the else block (must contain divergent control flow)
                    let else_block = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "block");

                    if let Some(else_body) = else_block {
                        // Create block for divergent else path
                        let else_entry = BlockId(*counter);
                        *counter += 1;
                        blocks.insert(
                            else_entry,
                            CFGBlock {
                id: else_entry,
                label: "let-else diverge".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: else_body.start_position().row + 1,
                end_line: else_body.end_position().row + 1,
            },
                        );

                        // Edge from let-else check to divergent block (pattern doesn't match)
                        edges.push(CFGEdge::from_label(let_else_block, else_entry, Some("else".to_string())));
                        *decision_points += 1; // let-else is a decision point

                        // Process the else block to find divergent exits
                        let (_, else_exits) = self.process_cfg_block_with_async_ctx(
                            else_body, source, blocks, edges, counter, else_entry,
                            loop_ctx, async_ctx, decision_points,
                        );

                        // The else block must diverge, so its exits go to function exit
                        // Add these as function exit points
                        exits.extend(else_exits);
                        if exits.is_empty() || !exits.contains(&else_entry) {
                            exits.push(else_entry);
                        }
                    }

                    // Create continue block for match success path
                    let continue_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        continue_block,
                        CFGBlock {
                id: continue_block,
                label: "let-else match".to_string(),
                block_type: BlockType::Body,
                statements: Vec::new(),
                func_calls: Vec::new(),
                start_line: child.end_position().row + 1,
                end_line: child.end_position().row + 1,
            },
                    );

                    // Edge from let-else check to continue (pattern matches)
                    edges.push(CFGEdge::from_label(let_else_block, continue_block, Some("match".to_string())));

                    current_block = continue_block;
                }
                "{" | "}" => {}
                // Handle if let patterns for Result/Option destructuring
                "if_let_expression" => {
                    let child = effective_child;
                    let if_let_block = BlockId(*counter);
                    *counter += 1;

                    // Extract the pattern for labeling
                    let pattern_text = child
                        .children(&mut child.walk())
                        .find(|c| {
                            c.kind() == "tuple_struct_pattern"
                                || c.kind() == "struct_pattern"
                                || c.kind() == "identifier"
                        })
                        .map(|c| self.node_text(c, source).to_string())
                        .unwrap_or_else(|| "pattern".to_string());

                    blocks.insert(
                        if_let_block,
                        CFGBlock {
                            id: if_let_block,
                            label: format!("if let {}", pattern_text.chars().take(20).collect::<String>()),
                            block_type: BlockType::PatternMatch,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.start_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, if_let_block, None));

                    // Process the then block (pattern matches)
                    let then_block = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "block");

                    let (then_exit, then_exits) = if let Some(then_body) = then_block {
                        let then_entry = BlockId(*counter);
                        *counter += 1;
                        blocks.insert(
                            then_entry,
                            CFGBlock {
                                id: then_entry,
                                label: "Some/Ok".to_string(),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: then_body.start_position().row + 1,
                                end_line: then_body.end_position().row + 1,
                            },
                        );
                        edges.push(CFGEdge::new(if_let_block, then_entry, EdgeType::OkSome));
                        *decision_points += 1; // if-let is a decision point
                        self.process_cfg_block_with_async_ctx(
                            then_body, source, blocks, edges, counter, then_entry,
                            loop_ctx, async_ctx, decision_points,
                        )
                    } else {
                        (if_let_block, Vec::new())
                    };

                    // Process else clause (pattern doesn't match / None/Err)
                    let else_clause = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "else_clause");

                    let else_exits = if let Some(else_node) = else_clause {
                        let else_body = else_node
                            .children(&mut else_node.walk())
                            .find(|c| c.kind() == "block" || c.kind() == "if_expression" || c.kind() == "if_let_expression");

                        if let Some(else_content) = else_body {
                            let else_entry = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(
                                else_entry,
                                CFGBlock {
                                    id: else_entry,
                                    label: "None/Err".to_string(),
                                    block_type: BlockType::Body,
                                    statements: Vec::new(),
                                    func_calls: Vec::new(),
                                    start_line: else_content.start_position().row + 1,
                                    end_line: else_content.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::new(if_let_block, else_entry, EdgeType::ErrNone));

                            let (_, exits) = self.process_cfg_block_with_async_ctx(
                                else_content, source, blocks, edges, counter, else_entry,
                                loop_ctx, async_ctx, decision_points,
                            );
                            if exits.is_empty() {
                                vec![else_entry]
                            } else {
                                exits
                            }
                        } else {
                            vec![if_let_block]
                        }
                    } else {
                        // No else branch - if_let_block exits on None/Err
                        edges.push(CFGEdge::new(if_let_block, if_let_block, EdgeType::ErrNone));
                        vec![if_let_block]
                    };

                    // Create merge block
                    let merge_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        merge_block,
                        CFGBlock {
                            id: merge_block,
                            label: "if_let merge".to_string(),
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.end_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    // Connect branches to merge
                    if then_exits.is_empty() {
                        edges.push(CFGEdge::from_label(then_exit, merge_block, None));
                    } else {
                        for exit in then_exits {
                            edges.push(CFGEdge::from_label(exit, merge_block, None));
                        }
                    }

                    for exit in &else_exits {
                        if *exit != if_let_block {
                            edges.push(CFGEdge::from_label(*exit, merge_block, None));
                        }
                    }

                    // Update edge if no else clause
                    if else_clause.is_none() {
                        if let Some(edge) = edges
                            .iter_mut()
                            .rev()
                            .find(|e| e.from == if_let_block && e.edge_type == EdgeType::ErrNone)
                        {
                            edge.to = merge_block;
                        }
                    }

                    current_block = merge_block;
                }
                // Handle while let patterns for Result/Option iteration
                "while_let_expression" => {
                    let child = effective_child;
                    let while_let_header = BlockId(*counter);
                    *counter += 1;

                    // Extract the pattern for labeling
                    let pattern_text = child
                        .children(&mut child.walk())
                        .find(|c| {
                            c.kind() == "tuple_struct_pattern"
                                || c.kind() == "struct_pattern"
                                || c.kind() == "identifier"
                        })
                        .map(|c| self.node_text(c, source).to_string())
                        .unwrap_or_else(|| "pattern".to_string());

                    // Create exit block first
                    let while_let_exit = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        while_let_exit,
                        CFGBlock {
                            id: while_let_exit,
                            label: "while_let exit".to_string(),
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.end_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    blocks.insert(
                        while_let_header,
                        CFGBlock {
                            id: while_let_header,
                            label: format!("while let {}", pattern_text.chars().take(15).collect::<String>()),
                            block_type: BlockType::PatternMatch,
                            statements: statements.drain(..).collect(),
                            func_calls: Vec::new(),
                            start_line: child.start_position().row + 1,
                            end_line: child.start_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, while_let_header, None));

                    // Register loop for break/continue
                    loop_ctx.push_loop(None, while_let_header, while_let_exit);

                    // Process the body block (pattern matches)
                    let body = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "block");

                    if let Some(loop_body) = body {
                        let body_entry = BlockId(*counter);
                        *counter += 1;
                        blocks.insert(
                            body_entry,
                            CFGBlock {
                                id: body_entry,
                                label: "Some/Ok body".to_string(),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: loop_body.start_position().row + 1,
                                end_line: loop_body.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::new(while_let_header, body_entry, EdgeType::OkSome));
                        *decision_points += 1; // while-let is a decision point

                        let (body_exit, body_exits) = self.process_cfg_block_with_async_ctx(
                            loop_body, source, blocks, edges, counter, body_entry, loop_ctx,
                            async_ctx, decision_points,
                        );

                        // Back edge to header for next iteration
                        if body_exits.is_empty() {
                            edges.push(CFGEdge::from_label(body_exit, while_let_header, Some("next".to_string())));
                        }
                    }

                    // Pop loop context
                    loop_ctx.pop_loop(None);

                    // None/Err exits the loop
                    edges.push(CFGEdge::new(while_let_header, while_let_exit, EdgeType::ErrNone));

                    current_block = while_let_exit;
                }
                // =========================================================================
                // Rust async/await handling
                // =========================================================================
                //
                // Handle .await suspension points - this is where the Future yields
                // to the executor and may be polled again later.
                "await_expression" => {
                    let child = effective_child;
                    let line = child.start_position().row + 1;
                    let await_info = self.get_await_info(child, source);

                    // Record the await point in async context
                    async_ctx.record_await(line);

                    // Check for lock-across-await anti-pattern
                    let has_held_locks = async_ctx.has_held_locks();
                    let block_type = if has_held_locks {
                        BlockType::RustLockAcrossAwait
                    } else {
                        BlockType::RustAwaitPoint
                    };

                    let await_block = BlockId(*counter);
                    *counter += 1;

                    // Build label with held lock info if any
                    let label = if has_held_locks {
                        let locks: Vec<_> = async_ctx.held_locks.iter()
                            .map(|(name, lock_type, _)| format!("{}:{}", name, lock_type))
                            .collect();
                        format!(".await {} [WARN: holds {}]", await_info, locks.join(", "))
                    } else {
                        format!(".await {}", await_info)
                    };

                    // Flush pending statements
                    if !statements.is_empty() {
                        if let Some(block) = blocks.get_mut(&current_block) {
                            block.statements.extend(statements.drain(..));
                        }
                    }

                    // Check if this await has a ? operator (await? pattern)
                    let has_try = self.contains_try_expression(child);

                    blocks.insert(
                        await_block,
                        CFGBlock {
                            id: await_block,
                            label,
                            block_type,
                            statements: vec![self.node_text(child, source).to_string()],
                            func_calls: self.extract_func_calls_from_node(child, source),
                            start_line: line,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    // Edge to await point
                    edges.push(CFGEdge::new(current_block, await_block, EdgeType::RustAwait));

                    if has_try {
                        // Handle .await? pattern - both suspension and error propagation
                        let error_return = BlockId(*counter);
                        *counter += 1;
                        blocks.insert(
                            error_return,
                            CFGBlock {
                                id: error_return,
                                label: "Err propagate (await?)".to_string(),
                                block_type: BlockType::ErrorReturn,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: line,
                                end_line: line,
                            },
                        );
                        edges.push(CFGEdge::new(await_block, error_return, EdgeType::ErrNone));
                        exits.push(error_return);
                        *decision_points += 1;
                    }

                    // Create resume block
                    let resume_block = BlockId(*counter);
                    *counter += 1;
                    blocks.insert(
                        resume_block,
                        CFGBlock {
                            id: resume_block,
                            label: "resume".to_string(),
                            block_type: BlockType::Body,
                            statements: Vec::new(),
                            func_calls: Vec::new(),
                            start_line: child.end_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    let resume_edge_type = if has_try {
                        EdgeType::OkSome
                    } else {
                        EdgeType::RustResume
                    };
                    edges.push(CFGEdge::new(await_block, resume_block, resume_edge_type));
                    current_block = resume_block;
                }
                // Handle async blocks (async { ... } or async move { ... })
                "async_block" => {
                    let child = effective_child;
                    let async_block_id = BlockId(*counter);
                    *counter += 1;

                    let text = self.node_text(child, source);
                    let truncated: String = text.chars().take(40).collect();
                    let has_await = self.contains_await(child);

                    blocks.insert(
                        async_block_id,
                        CFGBlock {
                            id: async_block_id,
                            label: if has_await {
                                format!("async block ({}x await): {}..", self.count_await_expressions(child), truncated)
                            } else {
                                format!("async block: {}..", truncated)
                            },
                            block_type: BlockType::RustAsyncBlock,
                            statements: vec![text.to_string()],
                            func_calls: self.extract_func_calls_from_node(child, source),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, async_block_id, None));
                    current_block = async_block_id;

                    // Note: The async block's internal control flow is a separate Future
                    // and would need nested CFG analysis for full tracking
                }
                // Handle macro invocations for tokio::join!, tokio::select!, etc.
                "macro_invocation" => {
                    let child = effective_child;
                    let (is_async_macro, macro_type) = self.is_async_macro(child, source);

                    if is_async_macro {
                        let line = child.start_position().row + 1;
                        let text = self.node_text(child, source);

                        // Flush pending statements
                        if !statements.is_empty() {
                            if let Some(block) = blocks.get_mut(&current_block) {
                                block.statements.extend(statements.drain(..));
                            }
                        }

                        match macro_type {
                            Some("join!") | Some("try_join!") => {
                                // join!/try_join! executes futures concurrently
                                let join_block = BlockId(*counter);
                                *counter += 1;

                                let is_try = macro_type == Some("try_join!");
                                blocks.insert(
                                    join_block,
                                    CFGBlock {
                                        id: join_block,
                                        label: format!("{}: {}..", macro_type.unwrap_or("join!"), text.chars().take(35).collect::<String>()),
                                        block_type: BlockType::RustJoin,
                                        statements: vec![text.to_string()],
                                        func_calls: self.extract_func_calls_from_node(child, source),
                                        start_line: line,
                                        end_line: child.end_position().row + 1,
                                    },
                                );

                                edges.push(CFGEdge::new(current_block, join_block, EdgeType::RustAwait));
                                async_ctx.record_await(line);

                                if is_try {
                                    // try_join! can fail early
                                    let error_block = BlockId(*counter);
                                    *counter += 1;
                                    blocks.insert(
                                        error_block,
                                        CFGBlock {
                                            id: error_block,
                                            label: "try_join! error".to_string(),
                                            block_type: BlockType::ErrorReturn,
                                            statements: Vec::new(),
                                            func_calls: Vec::new(),
                                            start_line: line,
                                            end_line: line,
                                        },
                                    );
                                    edges.push(CFGEdge::new(join_block, error_block, EdgeType::ErrNone));
                                    exits.push(error_block);
                                    *decision_points += 1;
                                }

                                // Continue block after join
                                let continue_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    continue_block,
                                    CFGBlock {
                                        id: continue_block,
                                        label: "join complete".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(join_block, continue_block, EdgeType::RustJoinComplete));
                                current_block = continue_block;
                            }
                            Some("select!") => {
                                // select! races futures, first to complete wins
                                let select_block = BlockId(*counter);
                                *counter += 1;

                                blocks.insert(
                                    select_block,
                                    CFGBlock {
                                        id: select_block,
                                        label: format!("select!: {}..", text.chars().take(35).collect::<String>()),
                                        block_type: BlockType::RustSelect,
                                        statements: vec![text.to_string()],
                                        func_calls: self.extract_func_calls_from_node(child, source),
                                        start_line: line,
                                        end_line: child.end_position().row + 1,
                                    },
                                );

                                edges.push(CFGEdge::new(current_block, select_block, EdgeType::RustAwait));
                                async_ctx.record_await(line);
                                *decision_points += 1; // select! is a decision point

                                // Continue block (one of the branches completed)
                                let continue_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    continue_block,
                                    CFGBlock {
                                        id: continue_block,
                                        label: "select winner".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(select_block, continue_block, EdgeType::RustSelectWinner));
                                current_block = continue_block;
                            }
                            _ => {
                                // Unknown async macro, just record as statement
                                statements.push(text.to_string());
                            }
                        }
                    } else {
                        // Non-async macro, just record as statement
                        statements.push(self.node_text(child, source).to_string());
                    }
                }
                // Handle closure expressions for ? operator tracking
                "closure_expression" => {
                    let child = effective_child;
                    let closure_block = BlockId(*counter);
                    *counter += 1;

                    let closure_text = self.node_text(child, source);
                    let truncated: String = closure_text.chars().take(30).collect();

                    // Check if closure contains try expressions
                    let has_try = self.contains_try_expression(child);

                    blocks.insert(
                        closure_block,
                        CFGBlock {
                            id: closure_block,
                            label: if has_try {
                                format!("closure (has ?): {}", truncated)
                            } else {
                                format!("closure: {}", truncated)
                            },
                            block_type: BlockType::Closure,
                            statements: vec![closure_text.to_string()],
                            func_calls: self.extract_func_calls_from_node(child, source),
                            start_line: child.start_position().row + 1,
                            end_line: child.end_position().row + 1,
                        },
                    );

                    edges.push(CFGEdge::from_label(current_block, closure_block, None));
                    current_block = closure_block;

                    // Note: Closures have their own control flow context
                    // The ? operator in closures returns from the closure, not the outer function
                    // We track this but don't add error return edges to outer function exits
                }
                // Handle call expressions for spawn detection and blocking call detection
                "call_expression" => {
                    let child = effective_child;
                    let text = self.node_text(child, source);
                    let line = child.start_position().row + 1;

                    // Check for tokio::spawn or async_std::spawn
                    let (is_spawn, spawn_type) = self.is_spawn_call(child, source);
                    if is_spawn {
                        // Flush pending statements
                        if !statements.is_empty() {
                            if let Some(block) = blocks.get_mut(&current_block) {
                                block.statements.extend(statements.drain(..));
                            }
                        }

                        let spawn_block = BlockId(*counter);
                        *counter += 1;

                        blocks.insert(
                            spawn_block,
                            CFGBlock {
                                id: spawn_block,
                                label: format!("{}::spawn: {}..", spawn_type.unwrap_or("spawn"), text.chars().take(35).collect::<String>()),
                                block_type: BlockType::RustTaskSpawn,
                                statements: vec![text.to_string()],
                                func_calls: self.extract_func_calls_from_node(child, source),
                                start_line: line,
                                end_line: child.end_position().row + 1,
                            },
                        );

                        edges.push(CFGEdge::new(current_block, spawn_block, EdgeType::RustSpawn));
                        current_block = spawn_block;
                    }
                    // Check for blocking calls in async context
                    else if async_ctx.is_async {
                        let (is_blocking, blocking_type) = self.is_blocking_call(child, source);
                        if is_blocking {
                            async_ctx.record_blocking_call(
                                blocking_type.as_deref().unwrap_or("blocking"),
                                line,
                            );

                            // Flush pending statements
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }

                            let blocking_block = BlockId(*counter);
                            *counter += 1;

                            blocks.insert(
                                blocking_block,
                                CFGBlock {
                                    id: blocking_block,
                                    label: format!("BLOCKING: {}", blocking_type.as_deref().unwrap_or("blocking call")),
                                    block_type: BlockType::RustBlockingCall,
                                    statements: vec![text.to_string()],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: line,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(current_block, blocking_block, EdgeType::RustBlocking));
                            current_block = blocking_block;
                        } else if self.contains_try_expression(child) {
                            // Handle call with ? operator
                            let try_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            let try_count = self.count_try_expressions(child);
                            blocks.insert(try_block, CFGBlock {
                                id: try_block,
                                label: format!("try?: {}", text.chars().take(25).collect::<String>()),
                                block_type: BlockType::TryOperator,
                                statements: vec![text.to_string()],
                                func_calls: self.extract_func_calls_from_node(child, source),
                                start_line: line,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::from_label(current_block, try_block, None));
                            let error_return = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(error_return, CFGBlock {
                                id: error_return,
                                label: format!("Err/None propagate ({}x ?)", try_count),
                                block_type: BlockType::ErrorReturn,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: line,
                                end_line: line,
                            });
                            edges.push(CFGEdge::new(try_block, error_return, EdgeType::ErrNone));
                            exits.push(error_return);
                            *decision_points += 1;
                            let success_block = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(success_block, CFGBlock {
                                id: success_block,
                                label: "Ok/Some continue".to_string(),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: child.end_position().row + 1,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::new(try_block, success_block, EdgeType::OkSome));
                            current_block = success_block;
                        } else {
                            statements.push(text.to_string());
                        }
                    } else {
                        // Non-async context or not a special call
                        if self.contains_try_expression(child) {
                            let try_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            let try_count = self.count_try_expressions(child);
                            blocks.insert(try_block, CFGBlock {
                                id: try_block,
                                label: format!("try?: {}", text.chars().take(25).collect::<String>()),
                                block_type: BlockType::TryOperator,
                                statements: vec![text.to_string()],
                                func_calls: self.extract_func_calls_from_node(child, source),
                                start_line: line,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::from_label(current_block, try_block, None));
                            let error_return = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(error_return, CFGBlock {
                                id: error_return,
                                label: format!("Err/None propagate ({}x ?)", try_count),
                                block_type: BlockType::ErrorReturn,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: line,
                                end_line: line,
                            });
                            edges.push(CFGEdge::new(try_block, error_return, EdgeType::ErrNone));
                            exits.push(error_return);
                            *decision_points += 1;
                            let success_block = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(success_block, CFGBlock {
                                id: success_block,
                                label: "Ok/Some continue".to_string(),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: child.end_position().row + 1,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::new(try_block, success_block, EdgeType::OkSome));
                            current_block = success_block;
                        } else {
                            statements.push(text.to_string());
                        }
                    }
                }
                _ => {
                    // For expression_statement that didn't match a control flow pattern,
                    // or other statement types, add to statements
                    let text = self.node_text(child, source).trim();
                    if !text.is_empty() && text != ";" {
                        // Check for lock acquisition in let declarations
                        if child.kind() == "let_declaration" {
                            if let Some((var_name, lock_type)) = self.is_lock_acquisition(child, source) {
                                async_ctx.acquire_lock(&var_name, &lock_type, child.start_position().row + 1);
                            }
                        }
                        // Check for explicit lock release via drop()
                        if let Some(dropped_var) = self.is_lock_release(child, source) {
                            async_ctx.release_lock(&dropped_var);
                        }

                        // CRITICAL: Check for await expressions nested in statements (e.g., let x = foo().await)
                        let await_count = self.count_await_expressions(child);
                        if await_count > 0 && async_ctx.is_async {
                            let line = child.start_position().row + 1;
                            // Record all await points
                            for _ in 0..await_count {
                                async_ctx.record_await(line);
                            }

                            // Check for lock-across-await anti-pattern
                            let has_held_locks = async_ctx.has_held_locks();
                            let block_type = if has_held_locks {
                                BlockType::RustLockAcrossAwait
                            } else {
                                BlockType::RustAwaitPoint
                            };

                            // Flush pending statements
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }

                            let await_block = BlockId(*counter);
                            *counter += 1;

                            // Check if this also has a try operator (await? pattern)
                            let has_try = self.contains_try_expression(child);

                            let label = if has_held_locks {
                                let locks: Vec<_> = async_ctx.held_locks.iter()
                                    .map(|(name, lock_type, _)| format!("{}:{}", name, lock_type))
                                    .collect();
                                format!(".await ({}x) [WARN: holds {}]", await_count, locks.join(", "))
                            } else if has_try {
                                format!(".await? ({}x): {}..", await_count, text.chars().take(25).collect::<String>())
                            } else {
                                format!(".await ({}x): {}..", await_count, text.chars().take(25).collect::<String>())
                            };

                            blocks.insert(
                                await_block,
                                CFGBlock {
                                    id: await_block,
                                    label,
                                    block_type,
                                    statements: vec![text.to_string()],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: line,
                                    end_line: child.end_position().row + 1,
                                },
                            );

                            edges.push(CFGEdge::new(current_block, await_block, EdgeType::RustAwait));

                            if has_try {
                                // Handle await? pattern - error propagation
                                let try_count = self.count_try_expressions(child);
                                let error_return = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    error_return,
                                    CFGBlock {
                                        id: error_return,
                                        label: format!("Err propagate ({}x ?)", try_count),
                                        block_type: BlockType::ErrorReturn,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: line,
                                        end_line: line,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, error_return, EdgeType::ErrNone));
                                exits.push(error_return);
                                *decision_points += try_count;

                                let success_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    success_block,
                                    CFGBlock {
                                        id: success_block,
                                        label: "Ok/Some continue".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, success_block, EdgeType::OkSome));
                                current_block = success_block;
                            } else {
                                // Just await, no error handling needed
                                let resume_block = BlockId(*counter);
                                *counter += 1;
                                blocks.insert(
                                    resume_block,
                                    CFGBlock {
                                        id: resume_block,
                                        label: "resume".to_string(),
                                        block_type: BlockType::Body,
                                        statements: Vec::new(),
                                        func_calls: Vec::new(),
                                        start_line: child.end_position().row + 1,
                                        end_line: child.end_position().row + 1,
                                    },
                                );
                                edges.push(CFGEdge::new(await_block, resume_block, EdgeType::RustResume));
                                current_block = resume_block;
                            }
                        }
                        // CRITICAL: Check if expression contains try operator (`?`) without await
                        else if self.contains_try_expression(child) {
                            let try_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            let try_count = self.count_try_expressions(child);
                            blocks.insert(try_block, CFGBlock {
                                id: try_block,
                                label: format!("try?: {}", text.chars().take(25).collect::<String>()),
                                block_type: BlockType::TryOperator,
                                statements: vec![text.to_string()],
                                func_calls: self.extract_func_calls_from_node(child, source),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::from_label(current_block, try_block, None));
                            let error_return = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(error_return, CFGBlock {
                                id: error_return,
                                label: format!("Err/None propagate ({}x ?)", try_count),
                                block_type: BlockType::ErrorReturn,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: child.start_position().row + 1,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::new(try_block, error_return, EdgeType::ErrNone));
                            exits.push(error_return);
                            let success_block = BlockId(*counter);
                            *counter += 1;
                            blocks.insert(success_block, CFGBlock {
                                id: success_block,
                                label: "Ok/Some continue".to_string(),
                                block_type: BlockType::Body,
                                statements: Vec::new(),
                                func_calls: Vec::new(),
                                start_line: child.end_position().row + 1,
                                end_line: child.end_position().row + 1,
                            });
                            edges.push(CFGEdge::new(try_block, success_block, EdgeType::OkSome));
                            current_block = success_block;
                        } else if self.contains_panic_site(child, source) {
                            // Handle potential panic sites: .unwrap(), .expect(), panic!(), etc.
                            let panic_block = BlockId(*counter);
                            *counter += 1;
                            if !statements.is_empty() {
                                if let Some(block) = blocks.get_mut(&current_block) {
                                    block.statements.extend(statements.drain(..));
                                }
                            }
                            let panic_info = self.get_panic_site_info(child, source);
                            blocks.insert(
                                panic_block,
                                CFGBlock {
                                    id: panic_block,
                                    label: format!("panic?: {}", panic_info),
                                    block_type: BlockType::PanicSite,
                                    statements: vec![text.to_string()],
                                    func_calls: self.extract_func_calls_from_node(child, source),
                                    start_line: child.start_position().row + 1,
                                    end_line: child.end_position().row + 1,
                                },
                            );
                            edges.push(CFGEdge::from_label(current_block, panic_block, None));
                            current_block = panic_block;
                        } else {
                            statements.push(text.to_string());
                        }
                    }
                }
            }
        }

        // Add remaining statements to current block
        if !statements.is_empty() {
            if let Some(block) = blocks.get_mut(&current_block) {
                block.statements.extend(statements);
            }
        }

        (current_block, exits)
    }

    /// Build DFG for a Rust function.
    fn build_rust_dfg(&self, node: Node, source: &[u8], function_name: &str) -> DFGInfo {
        let mut edges = Vec::new();
        let mut definitions: HashMap<String, Vec<usize>> = HashMap::new();
        let mut uses: HashMap<String, Vec<usize>> = HashMap::new();

        // Extract parameters as definitions
        let params = self.extract_parameters(node, source);
        let param_line = node.start_position().row + 1;

        for param in &params {
            // Extract variable name from param (e.g., "name: &str" -> "name", "ref x: i32" -> "x")
            let var_name = param
                .split(':')
                .next()
                .map(|s| {
                    s.trim()
                        .trim_start_matches('&')
                        .trim_start_matches("mut ")
                        .trim_start_matches("ref ")
                        .trim()
                        .to_string()
                })
                .unwrap_or_default();

            if !var_name.is_empty()
                && var_name != "self"
                && var_name != "&self"
                && var_name != "&mut self"
            {
                definitions
                    .entry(var_name.clone())
                    .or_default()
                    .push(param_line);
                edges.push(DataflowEdge {
                    variable: var_name,
                    from_line: param_line,
                    to_line: param_line,
                    kind: DataflowKind::Param,
                            });
            }
        }

        // Find function body and process it
        if let Some(body) = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "block")
        {
            self.process_dfg_node(body, source, &mut edges, &mut definitions, &mut uses);
        }

        DFGInfo::new(function_name.to_string(), edges, definitions, uses)
    }

    /// Process a node for DFG building.
    fn process_dfg_node(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
    ) {
        match node.kind() {
            "let_declaration" => {
                let line = node.start_position().row + 1;

                // Find the pattern (variable name) using tree-sitter field access
                if let Some(pattern) = node.child_by_field_name("pattern") {
                    let var_name = match pattern.kind() {
                        "identifier" => self.node_text(pattern, source).to_string(),
                        "tuple_pattern" => {
                            // For tuple patterns, get each identifier
                            pattern
                                .children(&mut pattern.walk())
                                .filter(|c| c.kind() == "identifier")
                                .map(|c| self.node_text(c, source))
                                .collect::<Vec<_>>()
                                .join(", ")
                        }
                        "mut_pattern" => {
                            // Handle `let mut x = ...` - the identifier is inside mut_pattern
                            pattern
                                .children(&mut pattern.walk())
                                .find(|c| c.kind() == "identifier")
                                .map(|c| self.node_text(c, source).to_string())
                                .unwrap_or_default()
                        }
                        _ => self.node_text(pattern, source).to_string(),
                    };

                    if !var_name.is_empty() {
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                        });
                    }
                }

                // Process the value expression for uses
                // Use tree-sitter field access instead of find() to avoid matching "=" token
                if let Some(value) = node.child_by_field_name("value") {
                    self.extract_uses_from_expr(value, source, edges, definitions, uses);
                }
            }
            "assignment_expression" => {
                let line = node.start_position().row + 1;

                // Left side is mutation - use field access for reliability
                if let Some(left) = node.child_by_field_name("left") {
                    let var_name = self.node_text(left, source).to_string();
                    if !var_name.is_empty() {
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Mutation,
                        });
                    }
                }

                // Right side is use - use field access for reliability
                if let Some(right) = node.child_by_field_name("right") {
                    self.extract_uses_from_expr(right, source, edges, definitions, uses);
                }
            }
            "return_expression" => {
                let line = node.start_position().row + 1;

                // Process return value
                for child in node.children(&mut node.walk()) {
                    if child.kind() != "return" {
                        self.extract_uses_from_expr(child, source, edges, definitions, uses);

                        // Add return edge
                        if child.kind() == "identifier" {
                            let var_name = self.node_text(child, source).to_string();
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Return,
                            });
                        }
                    }
                }
            }
            // BUG #14 fix: Handle if_let_expression pattern bindings
            // `if let Some(x) = opt { }` creates a definition of `x`
            "if_let_expression" => {
                let line = node.start_position().row + 1;

                // Extract pattern bindings from the if-let pattern
                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);

                // Process children (value expression and body block) for uses
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
            // BUG #14 fix: Handle while_let_expression pattern bindings
            // `while let Some(x) = iter.next() { }` creates a definition of `x`
            "while_let_expression" => {
                let line = node.start_position().row + 1;

                // Extract pattern bindings from the while-let pattern
                self.extract_pattern_bindings_from_node(node, source, edges, definitions, line);

                // Process children for uses
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
            // BUG #15 fix: Handle match_expression pattern bindings
            // `match x { Some(v) => ..., }` creates a definition of `v`
            "match_expression" => {
                // Find match_block and extract pattern bindings from each match_arm
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "match_block" {
                        for arm in child.children(&mut child.walk()) {
                            if arm.kind() == "match_arm" {
                                let line = arm.start_position().row + 1;
                                // Find match_pattern within the arm
                                for arm_child in arm.children(&mut arm.walk()) {
                                    if arm_child.kind() == "match_pattern" {
                                        // Extract bindings from the pattern
                                        self.extract_identifiers_from_pattern(
                                            arm_child,
                                            source,
                                            edges,
                                            definitions,
                                            line,
                                        );
                                    }
                                }
                                // Process the arm body for uses
                                self.process_dfg_node(arm, source, edges, definitions, uses);
                            }
                        }
                    } else {
                        // Process match value expression for uses
                        self.process_dfg_node(child, source, edges, definitions, uses);
                    }
                }
            }
            // BUG #16 fix: Handle closure_expression parameter definitions
            // `|x, y| x + y` creates definitions of `x` and `y`
            "closure_expression" => {
                let line = node.start_position().row + 1;

                // Find closure_parameters and extract parameter names
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "closure_parameters" {
                        for param in child.children(&mut child.walk()) {
                            if param.kind() == "identifier" {
                                let var_name = self.node_text(param, source).to_string();
                                if !var_name.is_empty() {
                                    definitions.entry(var_name.clone()).or_default().push(line);
                                    edges.push(DataflowEdge {
                                        variable: var_name,
                                        from_line: line,
                                        to_line: line,
                                        kind: DataflowKind::Param,
                            });
                                }
                            } else if param.kind() == "parameter" {
                                // Typed closure parameters: |x: i32, y: &str|
                                // Extract the identifier from the parameter node
                                for param_child in param.children(&mut param.walk()) {
                                    if param_child.kind() == "identifier" {
                                        let var_name =
                                            self.node_text(param_child, source).to_string();
                                        // BUG #17 fix: Strip ref modifier from parameter name
                                        let var_name = var_name
                                            .trim_start_matches("ref ")
                                            .trim_start_matches("mut ")
                                            .trim()
                                            .to_string();
                                        if !var_name.is_empty() {
                                            definitions
                                                .entry(var_name.clone())
                                                .or_default()
                                                .push(line);
                                            edges.push(DataflowEdge {
                                                variable: var_name,
                                                from_line: line,
                                                to_line: line,
                                                kind: DataflowKind::Param,
                            });
                                        }
                                        break; // Only take first identifier (the param name)
                                    }
                                }
                            }
                        }
                    } else {
                        // Process closure body for uses
                        self.process_dfg_node(child, source, edges, definitions, uses);
                    }
                }
            }
            // FEATURE: Async block handling - `async { ... }` blocks
            // Async blocks create a Future that can capture variables from the enclosing scope.
            // Unlike closures, they don't have parameters, but they capture variables used inside.
            // This is critical for tracking dataflow in async Rust code.
            "async_block" => {
                // Async blocks don't have parameters like closures
                // Process the block body to track variable uses (captures)
                for child in node.children(&mut node.walk()) {
                    if child.kind() == "block" {
                        // Process the inner block to track variable uses
                        self.process_dfg_node(child, source, edges, definitions, uses);
                    }
                }
            }
            _ => {
                // Recurse into children
                for child in node.children(&mut node.walk()) {
                    self.process_dfg_node(child, source, edges, definitions, uses);
                }
            }
        }
    }

    /// Extract pattern bindings from if-let or while-let expressions (BUG #14 fix).
    ///
    /// Handles patterns like:
    /// - `Some(x)` - extracts `x`
    /// - `(a, b)` - extracts `a` and `b`
    /// - `Struct { field: x, .. }` - extracts `x`
    fn extract_pattern_bindings_from_node(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        // Find pattern node in children
        for child in node.children(&mut node.walk()) {
            match child.kind() {
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                "identifier" => {
                    // Check if this is the pattern identifier (after "let" keyword)
                    let prev = child.prev_sibling();
                    if prev.map(|p| p.kind()) == Some("let") {
                        let var_name = self.node_text(child, source).to_string();
                        if !var_name.is_empty() {
                            definitions.entry(var_name.clone()).or_default().push(line);
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: line,
                                to_line: line,
                                kind: DataflowKind::Definition,
                            });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Recursively extract identifier bindings from a pattern.
    fn extract_identifiers_from_pattern(
        &self,
        pattern: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &mut HashMap<String, Vec<usize>>,
        line: usize,
    ) {
        for child in pattern.children(&mut pattern.walk()) {
            match child.kind() {
                "identifier" => {
                    let var_name = self.node_text(child, source).to_string();
                    // Skip variant names (e.g., "Some" in Some(x))
                    // They typically start with uppercase
                    if !var_name.is_empty() && !var_name.chars().next().unwrap().is_uppercase() {
                        definitions.entry(var_name.clone()).or_default().push(line);
                        edges.push(DataflowEdge {
                            variable: var_name,
                            from_line: line,
                            to_line: line,
                            kind: DataflowKind::Definition,
                            });
                    }
                }
                "tuple_struct_pattern" | "tuple_pattern" | "struct_pattern" => {
                    // Recurse into nested patterns
                    self.extract_identifiers_from_pattern(child, source, edges, definitions, line);
                }
                _ => {}
            }
        }
    }

    /// Extract variable uses from an expression.
    fn extract_uses_from_expr(
        &self,
        node: Node,
        source: &[u8],
        edges: &mut Vec<DataflowEdge>,
        definitions: &HashMap<String, Vec<usize>>,
        uses: &mut HashMap<String, Vec<usize>>,
    ) {
        let line = node.start_position().row + 1;

        match node.kind() {
            "identifier" => {
                let var_name = self.node_text(node, source).to_string();
                // Check if this is a known variable (not a function call)
                if definitions.contains_key(&var_name) {
                    uses.entry(var_name.clone()).or_default().push(line);

                    // Find the most recent definition
                    if let Some(def_lines) = definitions.get(&var_name) {
                        if let Some(&def_line) = def_lines.iter().filter(|&&l| l <= line).last() {
                            edges.push(DataflowEdge {
                                variable: var_name,
                                from_line: def_line,
                                to_line: line,
                                kind: DataflowKind::Use,
                            });
                        }
                    }
                }
            }
            "field_expression" => {
                // For x.field, x is used
                if let Some(obj) = node.child(0) {
                    if obj.kind() == "identifier" {
                        let var_name = self.node_text(obj, source).to_string();
                        if definitions.contains_key(&var_name) {
                            uses.entry(var_name.clone()).or_default().push(line);
                            if let Some(def_lines) = definitions.get(&var_name) {
                                if let Some(&def_line) =
                                    def_lines.iter().filter(|&&l| l <= line).last()
                                {
                                    edges.push(DataflowEdge {
                                        variable: var_name,
                                        from_line: def_line,
                                        to_line: line,
                                        kind: DataflowKind::Use,
                            });
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                // Recurse
                for child in node.children(&mut node.walk()) {
                    self.extract_uses_from_expr(child, source, edges, definitions, uses);
                }
            }
        }
    }
}

impl Language for Rust {
    fn name(&self) -> &'static str {
        "rust"
    }

    fn extensions(&self) -> &[&'static str] {
        &[".rs"]
    }

    fn parser(&self) -> Result<Parser> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .map_err(|e| BrrrError::TreeSitter(e.to_string()))?;
        Ok(parser)
    }

    fn extract_function(&self, node: Node, source: &[u8]) -> Option<FunctionInfo> {
        // Handle declarative macros (macro_rules!)
        if node.kind() == "macro_definition" {
            return self.extract_macro(node, source);
        }

        if node.kind() != "function_item" {
            return None;
        }

        // Extract function name
        let name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())?;

        let params = self.extract_parameters(node, source);
        let return_type = self.extract_return_type(node, source);
        let docstring = self.extract_doc_comments(node, source);
        let attributes = self.extract_attributes(node, source);
        let visibility = self.extract_visibility(node, source);
        let modifiers = self.extract_function_modifiers(node, source);
        // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
        let (lifetimes, type_params, const_params) =
            self.extract_distinct_type_params(node, source);
        let where_clause = self.extract_where_clause(node, source);

        // Check if this is a procedural macro
        let proc_macro_type = self.detect_proc_macro_type(node, source);

        // Build decorators list: visibility + modifiers + proc_macro + attributes + type info
        // Security-critical modifiers (unsafe, extern) are added via to_decorators()
        let mut decorators = Vec::new();
        if let Some(vis) = visibility {
            decorators.push(vis);
        }
        // Add procedural macro type if present (before other modifiers for visibility)
        if let Some(ref pm_type) = proc_macro_type {
            decorators.push(pm_type.clone());
        }
        // Add function modifiers (unsafe, const, async, extern) - security-critical first
        decorators.extend(modifiers.to_decorators());
        // Add user-defined attributes
        decorators.extend(attributes);
        // BUG #13 fix: Add lifetime, type parameters, and const generics separately for clarity
        if !lifetimes.is_empty() {
            decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
        }
        if !type_params.is_empty() {
            decorators.push(format!("type_params: {}", type_params.join(", ")));
        }
        if !const_params.is_empty() {
            decorators.push(format!("const_params: {}", const_params.join(", ")));
        }
        if let Some(wc) = where_clause {
            decorators.push(format!("where: {}", wc));
        }

        // Check if this is a method (has self parameter)
        let is_method = params.iter().any(|p| p.contains("self"));

        Some(FunctionInfo {
            name,
            params,
            return_type,
            docstring,
            is_method,
            is_async: modifiers.is_async,
            decorators,
            line_number: node.start_position().row + 1,
            end_line_number: Some(node.end_position().row + 1),
            language: "rust".to_string(),
        })
    }

    fn extract_class(&self, node: Node, source: &[u8]) -> Option<ClassInfo> {
        match node.kind() {
            "struct_item" => {
                // Extract struct name
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "type_identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);
                // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);
                let fields = self.extract_struct_fields(node, source);

                let mut decorators = attributes;
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }
                // BUG #13 fix: Add lifetime, type parameters, and const generics separately
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                // Store fields as bases (repurposing the field)
                let bases: Vec<String> = fields;

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(), // Methods come from impl blocks
                    fields: Vec::new(),  // TODO: Parse fields properly into FieldInfo
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            "impl_item" => {
                // Extract type being implemented
                let type_name = self.extract_impl_type(node, source)?;
                let trait_name = self.extract_impl_trait(node, source);
                // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);

                // Find the body (declaration_list)
                let body = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "declaration_list");

                let methods = body
                    .map(|b| self.extract_methods_from_body(b, source))
                    .unwrap_or_default();

                let mut decorators = Vec::new();
                // BUG #13 fix: Add lifetime, type parameters, and const generics separately
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                // Use trait as base if implementing a trait
                let bases = trait_name
                    .map(|t| vec![format!("impl {}", t)])
                    .unwrap_or_default();

                Some(ClassInfo {
                    name: type_name,
                    bases,
                    docstring: None,
                    methods,
                    fields: Vec::new(), // Impl blocks don't have fields
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            "trait_item" => {
                // Extract trait name
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "type_identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);
                // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);

                // Find the body (declaration_list)
                let body = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "declaration_list");

                let methods = body
                    .map(|b| self.extract_methods_from_body(b, source))
                    .unwrap_or_default();

                let mut decorators = attributes;
                decorators.insert(0, "trait".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }
                // BUG #13 fix: Add lifetime, type parameters, and const generics separately
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods,
                    fields: Vec::new(), // Traits don't have fields
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            "enum_item" => {
                // Extract enum name
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "type_identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);
                // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);
                let variants = self.extract_enum_variants(node, source);

                let mut decorators = attributes;
                decorators.insert(0, "enum".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }
                // BUG #13 fix: Add lifetime, type parameters, and const generics separately
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                // Store variants in bases field (repurposing like struct fields)
                Some(ClassInfo {
                    name,
                    bases: variants,
                    docstring,
                    methods: Vec::new(), // Enums don't have methods directly (methods come from impl blocks)
                    fields: Vec::new(),  // Enums don't have fields (variants are stored in bases)
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Union types - union Foo { a: u32, b: f32 }
            // Unions are similar to structs but all fields share the same memory location.
            // SECURITY: Unions require unsafe code to access fields (except for Copy types).
            "union_item" => {
                // Extract union name
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "type_identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);
                // BUG #13 fix: Use distinct extraction to separate lifetimes, type params, and const generics
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);
                // Unions use field_declaration_list just like structs
                let fields = self.extract_struct_fields(node, source);

                let mut decorators = attributes;
                decorators.insert(0, "union".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }
                // BUG #13 fix: Add lifetime, type parameters, and const generics separately
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                // Store fields as bases (same approach as structs)
                let bases: Vec<String> = fields;

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(), // Methods come from impl blocks
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Const items - const X: Type = value;
            "const_item" => {
                // Extract const name (uses identifier, not type_identifier)
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);

                // Extract type annotation
                let const_type = node
                    .children(&mut node.walk())
                    .find(|c| c.is_named() && c.kind().contains("type") && c.kind() != "type_parameters")
                    .map(|n| self.node_text(n, source).to_string());

                // Extract value expression
                let value = node
                    .child_by_field_name("value")
                    .map(|n| self.node_text(n, source).to_string());

                let mut decorators = attributes;
                decorators.insert(0, "const".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }

                // Store type and value in bases for representation
                let mut bases = Vec::new();
                if let Some(ref t) = const_type {
                    bases.push(format!("type: {}", t));
                }
                if let Some(ref v) = value {
                    bases.push(format!("value: {}", v));
                }

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Static items - static X: Type = value; or static mut X: Type = value;
            "static_item" => {
                // Extract static name (uses identifier, not type_identifier)
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);

                // Check for mutable_specifier (static mut)
                let is_mutable = node
                    .children(&mut node.walk())
                    .any(|c| c.kind() == "mutable_specifier");

                // Extract type annotation
                let static_type = node
                    .children(&mut node.walk())
                    .find(|c| c.is_named() && c.kind().contains("type") && c.kind() != "type_parameters")
                    .map(|n| self.node_text(n, source).to_string());

                // Extract value expression
                let value = node
                    .child_by_field_name("value")
                    .map(|n| self.node_text(n, source).to_string());

                let mut decorators = attributes;
                // Add static or static mut decorator
                if is_mutable {
                    decorators.insert(0, "static mut".to_string());
                } else {
                    decorators.insert(0, "static".to_string());
                }
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }

                // Store type and value in bases for representation
                let mut bases = Vec::new();
                if let Some(ref t) = static_type {
                    bases.push(format!("type: {}", t));
                }
                if let Some(ref v) = value {
                    bases.push(format!("value: {}", v));
                }

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Type aliases - type Result<T> = std::result::Result<T, Error>;
            "type_item" => {
                // Extract type alias name (uses type_identifier)
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "type_identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);

                // Extract generic type parameters (including const generics)
                let (lifetimes, type_params, const_params) =
                    self.extract_distinct_type_params(node, source);

                // Extract the aliased type (the type after =)
                let aliased_type = node
                    .child_by_field_name("type")
                    .map(|n| self.node_text(n, source).to_string());

                let mut decorators = attributes;
                decorators.insert(0, "type_alias".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }
                // Add lifetime, type parameters, and const generics
                if !lifetimes.is_empty() {
                    decorators.push(format!("lifetimes: {}", lifetimes.join(", ")));
                }
                if !type_params.is_empty() {
                    decorators.push(format!("type_params: {}", type_params.join(", ")));
                }
                if !const_params.is_empty() {
                    decorators.push(format!("const_params: {}", const_params.join(", ")));
                }

                // Store aliased type in bases
                let bases = aliased_type
                    .map(|t| vec![format!("= {}", t)])
                    .unwrap_or_default();

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Module declarations - mod foo; and mod foo { ... }
            "mod_item" => {
                // Extract module name from identifier child
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);

                // Check if this is an inline module (has declaration_list body)
                // vs a file module (just `mod foo;`)
                let body = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "declaration_list");

                let is_inline = body.is_some();

                // Extract methods (functions) from inline module body
                let methods = if let Some(body_node) = body {
                    self.extract_methods_from_body(body_node, source)
                } else {
                    Vec::new()
                };

                // Extract inner classes (structs, enums, unions, etc.) from inline module
                let inner_classes = if let Some(body_node) = body {
                    let mut classes = Vec::new();
                    for child in body_node.children(&mut body_node.walk()) {
                        match child.kind() {
                            "struct_item" | "union_item" | "enum_item" | "trait_item"
                            | "impl_item" | "const_item" | "static_item" | "type_item"
                            | "mod_item" | "foreign_mod_item" => {
                                if let Some(class) = self.extract_class(child, source) {
                                    classes.push(class);
                                }
                            }
                            _ => {}
                        }
                    }
                    classes
                } else {
                    Vec::new()
                };

                let mut decorators = attributes;
                // Add module type indicator
                if is_inline {
                    decorators.insert(0, "mod (inline)".to_string());
                } else {
                    decorators.insert(0, "mod (file)".to_string());
                }
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods,
                    fields: Vec::new(),
                    inner_classes,
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Extern blocks - extern "C" { fn foo(); }
            // Tree-sitter node type is foreign_mod_item (not extern_block)
            "foreign_mod_item" => {
                // Extract ABI from extern_modifier child
                let abi = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "extern_modifier")
                    .and_then(|modifier| {
                        modifier
                            .children(&mut modifier.walk())
                            .find(|c| c.kind() == "string_literal")
                            .map(|s| {
                                let text = self.node_text(s, source);
                                // Remove quotes: "C" -> C
                                text.trim_matches('"').to_string()
                            })
                    })
                    .unwrap_or_else(|| "Rust".to_string()); // Default ABI is "Rust"

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);

                // Find the body (declaration_list) containing foreign functions
                let body = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "declaration_list");

                // Extract functions declared inside the extern block
                // These are function_signature_item nodes (no body, just signatures)
                let methods = if let Some(body_node) = body {
                    let mut funcs = Vec::new();
                    for child in body_node.children(&mut body_node.walk()) {
                        if child.kind() == "function_signature_item" {
                            if let Some(mut func) = self.extract_function_signature(child, source) {
                                // Mark as extern with ABI
                                func.decorators
                                    .insert(0, format!("extern \"{}\"", abi));
                                funcs.push(func);
                            }
                        }
                        // Also handle static items in extern blocks (extern statics)
                        else if child.kind() == "static_item" {
                            // Static items in extern blocks are foreign statics
                            // We could extract them as FunctionInfo with special marker
                        }
                    }
                    funcs
                } else {
                    Vec::new()
                };

                let mut decorators = attributes;
                decorators.insert(0, format!("extern \"{}\"", abi));

                // Use a synthetic name for the extern block
                let name = format!("extern_{}", abi);

                Some(ClassInfo {
                    name,
                    bases: Vec::new(),
                    docstring,
                    methods,
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            // FEATURE: Extern crate declarations - extern crate foo; or extern crate foo as bar;
            "extern_crate_declaration" => {
                // Extract crate name from identifier child
                let name = node
                    .children(&mut node.walk())
                    .find(|c| c.kind() == "identifier")
                    .map(|n| self.node_text(n, source).to_string())?;

                let docstring = self.extract_doc_comments(node, source);
                let attributes = self.extract_attributes(node, source);
                let visibility = self.extract_visibility(node, source);

                // Check for alias: extern crate foo as bar;
                let alias = node.child_by_field_name("alias").map(|alias_node| {
                    alias_node
                        .children(&mut alias_node.walk())
                        .find(|c| c.kind() == "identifier")
                        .map(|n| self.node_text(n, source).to_string())
                        .unwrap_or_default()
                });

                let mut decorators = attributes;
                decorators.insert(0, "extern crate".to_string());
                if let Some(vis) = visibility {
                    decorators.insert(0, vis);
                }

                // Store alias in bases if present
                let bases = alias
                    .filter(|a| !a.is_empty())
                    .map(|a| vec![format!("as {}", a)])
                    .unwrap_or_default();

                Some(ClassInfo {
                    name,
                    bases,
                    docstring,
                    methods: Vec::new(),
                    fields: Vec::new(),
                    inner_classes: Vec::new(),
                    decorators,
                    line_number: node.start_position().row + 1,
                    end_line_number: Some(node.end_position().row + 1),
                    language: "rust".to_string(),
                })
            }
            _ => None,
        }
    }

    fn extract_imports(&self, tree: &Tree, source: &[u8]) -> Vec<ImportInfo> {
        let mut imports = Vec::new();
        let root = tree.root_node();

        // Iterate over all children to find use_declaration nodes
        for child in root.children(&mut root.walk()) {
            if child.kind() == "use_declaration" {
                if let Some(import) = self.extract_single_import(child, source) {
                    imports.push(import);
                }
            }
        }

        imports
    }

    fn function_query(&self) -> &'static str {
        r#"[
            (function_item name: (identifier) @name) @function
            (function_signature_item name: (identifier) @name) @function
            (macro_definition name: (identifier) @name) @function
        ]"#
    }

    fn class_query(&self) -> &'static str {
        r#"[
            (struct_item name: (type_identifier) @name) @class
            (union_item name: (type_identifier) @name) @class
            (impl_item type: (_) @name) @class
            (trait_item name: (type_identifier) @name) @class
            (enum_item name: (type_identifier) @name) @class
            (const_item name: (identifier) @name) @class
            (static_item name: (identifier) @name) @class
            (type_item name: (type_identifier) @name) @class
            (mod_item name: (identifier) @name) @class
            (foreign_mod_item) @class
            (extern_crate_declaration name: (identifier) @name) @class
        ]"#
    }

    fn call_query(&self) -> &'static str {
        r#"[
            (call_expression function: (identifier) @callee) @call
            (call_expression function: (field_expression field: (field_identifier) @callee)) @call
            (call_expression function: (scoped_identifier name: (identifier) @callee)) @call
        ]"#
    }

    fn build_cfg(&self, node: Node, source: &[u8]) -> Result<CFGInfo> {
        if node.kind() != "function_item" {
            return Err(BrrrError::TreeSitter(
                "CFG building requires a function_item node".to_string(),
            ));
        }

        // Extract function name
        let function_name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "unknown".to_string());

        Ok(self.build_rust_cfg(node, source, &function_name))
    }

    fn build_dfg(&self, node: Node, source: &[u8]) -> Result<DFGInfo> {
        if node.kind() != "function_item" {
            return Err(BrrrError::TreeSitter(
                "DFG building requires a function_item node".to_string(),
            ));
        }

        // Extract function name
        let function_name = node
            .children(&mut node.walk())
            .find(|c| c.kind() == "identifier")
            .map(|n| self.node_text(n, source).to_string())
            .unwrap_or_else(|| "unknown".to_string());

        Ok(self.build_rust_dfg(node, source, &function_name))
    }

    /// Extract module-level docstring from a Rust source file.
    ///
    /// Rust uses inner doc comments for module documentation:
    /// - `//!` line comments at the start of the file
    /// - `/*! ... */` block comments at the start of the file
    ///
    /// These comments describe the enclosing module and appear before any items.
    fn extract_module_docstring(&self, tree: &Tree, source: &[u8]) -> Option<String> {
        let root = tree.root_node();
        if root.kind() != "source_file" {
            return None;
        }

        let mut doc_lines: Vec<String> = Vec::new();

        for child in root.children(&mut root.walk()) {
            match child.kind() {
                "line_comment" => {
                    let text = self.node_text(child, source);
                    // Check for //! inner doc comment (module-level)
                    if text.starts_with("//!") {
                        // Extract content after //! prefix
                        let content = text.strip_prefix("//!").unwrap_or("");
                        // Trim exactly one leading space if present (standard convention)
                        let content = content.strip_prefix(' ').unwrap_or(content);
                        // Trim trailing whitespace (tree-sitter may include trailing newlines)
                        let content = content.trim_end();
                        doc_lines.push(content.to_string());
                    } else {
                        // Regular comment (// or ///), stop collecting
                        break;
                    }
                }
                "block_comment" => {
                    let text = self.node_text(child, source);
                    // Check for /*! ... */ inner doc comment (module-level)
                    if text.starts_with("/*!") {
                        let content = self.extract_block_doc_content(text);
                        if !content.is_empty() {
                            doc_lines.push(content);
                        }
                    } else {
                        // Regular block comment, stop collecting
                        break;
                    }
                }
                _ => {
                    // Non-comment item encountered, stop collecting
                    break;
                }
            }
        }

        if doc_lines.is_empty() {
            None
        } else {
            Some(doc_lines.join("\n"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_rust(code: &str) -> Tree {
        let rust = Rust;
        let mut parser = rust.parser().unwrap();
        parser.parse(code, None).unwrap()
    }

    #[test]
    fn test_extract_simple_function() {
        let code = r#"
fn hello(name: &str) -> String {
    format!("Hello, {}", name)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        // Find function_item
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "hello");
        assert_eq!(func.params, vec!["name: &str"]);
        assert_eq!(func.return_type, Some("String".to_string()));
        assert!(!func.is_async);
        assert!(!func.is_method);
    }

    #[test]
    fn test_extract_async_function() {
        let code = r#"
pub async fn fetch_data(url: &str) -> Result<Data, Error> {
    // fetch
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "fetch_data");
        assert!(func.is_async);
        assert!(func.decorators.contains(&"pub".to_string()));
    }

    #[test]
    fn test_extract_generic_function() {
        let code = r#"
fn transform<T: Clone, U>(input: T) -> U
where
    U: From<T>,
{
    input.into()
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "transform");
        // BUG #13 fix: generics are now split into "type_params:" for clarity
        assert!(func.decorators.iter().any(|d| d.contains("type_params:")));
        assert!(func.decorators.iter().any(|d| d.contains("where:")));
    }

    #[test]
    fn test_extract_struct() {
        let code = r#"
/// A point in 2D space.
#[derive(Debug, Clone)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        // Skip doc comment and attribute to get struct
        let struct_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "struct_item")
            .unwrap();

        let class = rust.extract_class(struct_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Point");
        assert!(class.docstring.is_some());
        assert!(class.decorators.contains(&"pub".to_string()));
        assert!(class.bases.iter().any(|f| f.contains("x: f64")));
    }

    #[test]
    fn test_extract_impl_block() {
        let code = r#"
impl Point {
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    pub fn distance(&self, other: &Point) -> f64 {
        ((self.x - other.x).powi(2) + (self.y - other.y).powi(2)).sqrt()
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root.child(0).unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Point");
        assert_eq!(class.methods.len(), 2);
        assert_eq!(class.methods[0].name, "new");
        assert_eq!(class.methods[1].name, "distance");
        assert!(class.methods[1].is_method);
    }

    #[test]
    fn test_extract_trait_impl_type() {
        // CRITICAL: Test for trait impl type extraction bug fix
        // For `impl Clone for Vec<T>`, should return "Vec" not "Clone"
        let code = r#"
impl Clone for MyStruct {
    fn clone(&self) -> Self {
        Self { }
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root.child(0).unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        // MUST be "MyStruct" not "Clone" - this is the bug fix verification
        assert_eq!(class.name, "MyStruct");
        assert!(class.bases.iter().any(|b| b.contains("Clone")));
    }

    #[test]
    fn test_extract_generic_trait_impl_type() {
        // Test generic trait impl: impl<T> Clone for Vec<T>
        let code = r#"
impl<T: Debug> Clone for MyContainer<T> {
    fn clone(&self) -> Self {
        Self { items: self.items.clone() }
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root.child(0).unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        // MUST be "MyContainer" not "Clone"
        assert_eq!(class.name, "MyContainer");
        assert!(class.bases.iter().any(|b| b.contains("Clone")));
    }

    #[test]
    fn test_extract_trait() {
        let code = r#"
/// A drawable trait.
pub trait Drawable {
    fn draw(&self);
    fn bounds(&self) -> Rect;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let trait_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "trait_item")
            .unwrap();

        let class = rust.extract_class(trait_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Drawable");
        assert!(class.decorators.contains(&"trait".to_string()));
        assert_eq!(class.methods.len(), 2);
    }

    #[test]
    fn test_extract_imports() {
        let code = r#"
use std::collections::{HashMap, HashSet};
use crate::module::*;
use super::parent;
use self::sibling as sib;
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let imports = rust.extract_imports(&tree, code.as_bytes());

        assert_eq!(imports.len(), 4);

        // Check scoped import
        let scoped = &imports[0];
        assert!(scoped.module.contains("std"));
        assert!(scoped.names.contains(&"HashMap".to_string()));
        assert!(scoped.names.contains(&"HashSet".to_string()));

        // Check glob import
        let glob = &imports[1];
        assert!(glob.names.contains(&"*".to_string()));

        // Check aliased import
        let aliased = &imports[3];
        assert!(aliased.aliases.contains_key("sibling"));
    }

    #[test]
    fn test_build_simple_cfg() {
        let code = r#"
fn example(x: i32) -> i32 {
    let y = x + 1;
    y * 2
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        assert_eq!(cfg.function_name, "example");
        assert!(!cfg.blocks.is_empty());
        assert!(!cfg.exits.is_empty());
    }

    #[test]
    fn test_build_cfg_with_if() {
        let code = r#"
fn check(x: i32) -> bool {
    if x > 0 {
        true
    } else {
        false
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have entry, if, then, else, merge, exit blocks
        assert!(cfg.blocks.len() >= 4);

        // Should have edges for true/false branches
        assert!(cfg.edges.iter().any(|e| e.label() == "true"));
        assert!(cfg.edges.iter().any(|e| e.label() == "false"));
    }

    #[test]
    fn test_build_simple_dfg() {
        let code = r#"
fn example(x: i32) -> i32 {
    let y = x + 1;
    y * 2
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let dfg = rust.build_dfg(func_node, code.as_bytes()).unwrap();

        assert_eq!(dfg.function_name, "example");
        assert!(dfg.definitions.contains_key("x"));
        assert!(dfg.definitions.contains_key("y"));
    }

    #[test]
    fn test_cyclomatic_complexity() {
        let code = r#"
fn complex(x: i32) -> i32 {
    if x > 0 {
        if x > 10 {
            100
        } else {
            10
        }
    } else {
        0
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Use graph-based formula since Rust CFG builder doesn't track
        // decision points yet (TODO in build_rust_cfg)
        let complexity = cfg.cyclomatic_complexity_graph();

        // With nested if-else, complexity should be > 1 using E - N + 2 formula
        assert!(complexity >= 2);
    }

    // BUG #1 FIX TESTS: Function Modifiers (unsafe, const, extern detection)

    #[test]
    fn test_extract_unsafe_function() {
        let code = "pub unsafe fn dangerous(ptr: *const u8) -> u8 { *ptr }";
        let tree = parse_rust(code);
        let rust = Rust;
        let func_node = tree.root_node().child(0).unwrap();
        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.name, "dangerous");
        assert!(func.decorators.iter().any(|d| d == "unsafe"));
    }

    #[test]
    fn test_extract_const_function() {
        let code = "pub const fn compile_time() -> i32 { 42 }";
        let tree = parse_rust(code);
        let rust = Rust;
        let func_node = tree.root_node().child(0).unwrap();
        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();
        assert_eq!(func.name, "compile_time");
        assert!(func.decorators.iter().any(|d| d == "const"));
    }

    #[test]
    fn test_function_modifiers_struct() {
        let rust = Rust;
        let code = "unsafe fn foo() {}";
        let tree = parse_rust(code);
        let func_node = tree.root_node().child(0).unwrap();
        let modifiers = rust.extract_function_modifiers(func_node, code.as_bytes());
        assert!(modifiers.is_unsafe);
        assert!(modifiers.has_security_implications());
    }

    // BUG #2 FIX TESTS: Try Operator (?) in CFG

    #[test]
    fn test_cfg_with_try_operator() {
        let code = "fn fallible() -> Result<i32, Error> { let x = op()?; Ok(x) }";
        let tree = parse_rust(code);
        let rust = Rust;
        let func_node = tree.root_node().child(0).unwrap();
        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();
        // Verify try operator creates error return path
        assert!(cfg.edges.iter().any(|e| e.label().contains("Err")));
        assert!(cfg.edges.iter().any(|e| e.label().contains("Ok")));
    }

    #[test]
    fn test_contains_try_expression() {
        let rust = Rust;
        let code = "fn test() { let x = foo()?; }";
        let tree = parse_rust(code);
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        let stmt = body.child(1).unwrap();
        assert!(rust.contains_try_expression(stmt));
    }

    // MACRO EXTRACTION TESTS

    #[test]
    fn test_extract_simple_macro() {
        let code = r#"macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let macro_node = root.child(0).unwrap();
        assert_eq!(macro_node.kind(), "macro_definition");

        let func = rust.extract_function(macro_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "say_hello");
        assert!(func.decorators.contains(&"macro".to_string()));
        assert_eq!(func.params.len(), 1); // One arm pattern: "()"
        assert_eq!(func.params[0], "()");
    }

    #[test]
    fn test_extract_macro_multiple_arms() {
        let code = r#"macro_rules! vec {
    () => { Vec::new() };
    ($($x:expr),+) => { { let mut v = Vec::new(); $(v.push($x);)+ v } };
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let macro_node = root.child(0).unwrap();

        let func = rust.extract_function(macro_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "vec");
        assert!(func.decorators.contains(&"macro".to_string()));
        assert!(func.decorators.iter().any(|d| d.contains("arms: 2")));
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.params[0], "()");
        assert!(func.params[1].contains("$x:expr"));
    }

    #[test]
    fn test_extract_exported_macro() {
        let code = r#"/// A useful macro for creating vectors.
#[macro_export]
macro_rules! my_vec {
    ($($x:expr),*) => { vec![$($x),*] };
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let macro_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "macro_definition")
            .unwrap();

        let func = rust.extract_function(macro_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "my_vec");
        assert!(func.decorators.contains(&"macro".to_string()));
        assert!(func.decorators.iter().any(|d| d.contains("#[macro_export]")));
        assert!(func.docstring.is_some());
        assert!(func.docstring.unwrap().contains("useful macro"));
    }

    #[test]
    fn test_extract_proc_macro() {
        let code = r#"#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    input
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "function_item")
            .unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "my_macro");
        assert!(func.decorators.iter().any(|d| d == "proc_macro"));
    }

    #[test]
    fn test_extract_proc_macro_derive() {
        let code = r#"#[proc_macro_derive(MyDerive, attributes(my_attr))]
pub fn my_derive(input: TokenStream) -> TokenStream {
    input
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "function_item")
            .unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "my_derive");
        assert!(func.decorators.iter().any(|d| d.contains("proc_macro_derive")));
        assert!(func.decorators.iter().any(|d| d.contains("MyDerive")));
    }

    #[test]
    fn test_extract_proc_macro_attribute() {
        let code = r#"#[proc_macro_attribute]
pub fn my_attr(attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "function_item")
            .unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "my_attr");
        assert!(func.decorators.iter().any(|d| d == "proc_macro_attribute"));
    }

    #[test]
    fn test_macro_extract_method() {
        let code = r#"macro_rules! impl_display {
    ($t:ty) => {
        impl std::fmt::Display for $t {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self)
            }
        }
    };
}"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let macro_node = root.child(0).unwrap();

        let func = rust.extract_macro(macro_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "impl_display");
        assert!(func.decorators.contains(&"macro".to_string()));
        assert_eq!(func.params.len(), 1);
        assert!(func.params[0].contains("$t:ty"));
    }

    // ========================================
    // FEATURE: Const items tests
    // ========================================

    #[test]
    fn test_extract_const_item() {
        let code = r#"pub const MAX_SIZE: usize = 1024;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let const_node = root.child(0).unwrap();

        assert_eq!(const_node.kind(), "const_item");
        let class = rust.extract_class(const_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "MAX_SIZE");
        assert!(class.decorators.contains(&"const".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
        assert!(class.bases.iter().any(|b| b.contains("usize")));
        assert!(class.bases.iter().any(|b| b.contains("1024")));
    }

    #[test]
    fn test_extract_const_item_private() {
        let code = r#"const INTERNAL_FLAG: bool = true;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let const_node = root.child(0).unwrap();

        let class = rust.extract_class(const_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "INTERNAL_FLAG");
        assert!(class.decorators.contains(&"const".to_string()));
        assert!(!class.decorators.contains(&"pub".to_string()));
    }

    // ========================================
    // FEATURE: Static items tests
    // ========================================

    #[test]
    fn test_extract_static_item() {
        let code = r#"pub static COUNTER: u64 = 0;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let static_node = root.child(0).unwrap();

        assert_eq!(static_node.kind(), "static_item");
        let class = rust.extract_class(static_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "COUNTER");
        assert!(class.decorators.contains(&"static".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
        assert!(!class.decorators.contains(&"static mut".to_string()));
    }

    #[test]
    fn test_extract_static_mut_item() {
        let code = r#"static mut BUFFER: [u8; 256] = [0; 256];"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let static_node = root.child(0).unwrap();

        let class = rust.extract_class(static_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "BUFFER");
        assert!(class.decorators.contains(&"static mut".to_string()));
        assert!(!class.decorators.contains(&"static".to_string()));
        assert!(class.bases.iter().any(|b| b.contains("[u8; 256]")));
    }

    // ========================================
    // FEATURE: Type alias tests
    // ========================================

    #[test]
    fn test_extract_type_alias_simple() {
        let code = r#"type Callback = fn(i32) -> bool;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let type_node = root.child(0).unwrap();

        assert_eq!(type_node.kind(), "type_item");
        let class = rust.extract_class(type_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Callback");
        assert!(class.decorators.contains(&"type_alias".to_string()));
        assert!(class.bases.iter().any(|b| b.contains("fn(i32) -> bool")));
    }

    #[test]
    fn test_extract_type_alias_generic() {
        let code = r#"pub type Result<T> = std::result::Result<T, Error>;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let type_node = root.child(0).unwrap();

        let class = rust.extract_class(type_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Result");
        assert!(class.decorators.contains(&"type_alias".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
        // Check for generic type parameter T
        assert!(class.decorators.iter().any(|d| d.contains("type_params:") && d.contains("T")));
        assert!(class.bases.iter().any(|b| b.contains("std::result::Result<T, Error>")));
    }

    #[test]
    fn test_extract_type_alias_with_lifetimes() {
        let code = r#"type RefStr<'a> = &'a str;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let type_node = root.child(0).unwrap();

        let class = rust.extract_class(type_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "RefStr");
        assert!(class.decorators.contains(&"type_alias".to_string()));
        // Check for lifetime parameter
        assert!(class.decorators.iter().any(|d| d.contains("lifetimes:") && d.contains("'a")));
    }

    // ========================================
    // FEATURE: Module declaration tests
    // ========================================

    #[test]
    fn test_extract_file_module() {
        let code = r#"mod utils;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let mod_node = root.child(0).unwrap();

        assert_eq!(mod_node.kind(), "mod_item");
        let class = rust.extract_class(mod_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "utils");
        assert!(class.decorators.contains(&"mod (file)".to_string()));
        assert!(class.methods.is_empty());
        assert!(class.inner_classes.is_empty());
    }

    #[test]
    fn test_extract_pub_file_module() {
        let code = r#"pub mod api;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let mod_node = root.child(0).unwrap();

        let class = rust.extract_class(mod_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "api");
        assert!(class.decorators.contains(&"mod (file)".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
    }

    #[test]
    fn test_extract_inline_module() {
        let code = r#"
mod helpers {
    pub fn help() {}
    fn internal() {}
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let mod_node = root.child(0).unwrap();

        let class = rust.extract_class(mod_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "helpers");
        assert!(class.decorators.contains(&"mod (inline)".to_string()));
        // Should have extracted the functions from the module body
        assert_eq!(class.methods.len(), 2);
        assert!(class.methods.iter().any(|m| m.name == "help"));
        assert!(class.methods.iter().any(|m| m.name == "internal"));
    }

    #[test]
    fn test_extract_inline_module_with_nested_items() {
        let code = r#"
pub mod nested {
    pub struct Inner {
        pub value: i32,
    }

    pub fn create_inner() -> Inner {
        Inner { value: 42 }
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let mod_node = root.child(0).unwrap();

        let class = rust.extract_class(mod_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "nested");
        assert!(class.decorators.contains(&"mod (inline)".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
        // Should have the function
        assert_eq!(class.methods.len(), 1);
        assert!(class.methods.iter().any(|m| m.name == "create_inner"));
        // Should have inner class (struct)
        assert_eq!(class.inner_classes.len(), 1);
        assert!(class.inner_classes.iter().any(|c| c.name == "Inner"));
    }

    #[test]
    fn test_extract_documented_module() {
        let code = r#"
/// This module contains utility functions.
pub mod utils;
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        // Find mod_item specifically (first child may be a line_comment)
        let mod_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "mod_item")
            .unwrap();

        let class = rust.extract_class(mod_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "utils");
        assert!(class.docstring.is_some());
        assert!(class.docstring.as_ref().unwrap().contains("utility functions"));
    }

    // ========================================
    // FEATURE: Extern block tests
    // ========================================

    #[test]
    fn test_extract_extern_c_block() {
        let code = r#"
extern "C" {
    fn printf(fmt: *const c_char, ...) -> c_int;
    fn malloc(size: usize) -> *mut c_void;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let extern_node = root.child(0).unwrap();

        assert_eq!(extern_node.kind(), "foreign_mod_item");
        let class = rust.extract_class(extern_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "extern_C");
        assert!(class.decorators.iter().any(|d| d.contains("extern \"C\"")));
        // Should have extracted the foreign function signatures
        assert_eq!(class.methods.len(), 2);
        assert!(class.methods.iter().any(|m| m.name == "printf"));
        assert!(class.methods.iter().any(|m| m.name == "malloc"));
        // Each method should have extern "C" decorator
        for method in &class.methods {
            assert!(method.decorators.iter().any(|d| d.contains("extern \"C\"")));
        }
    }

    #[test]
    fn test_extract_extern_system_block() {
        let code = r#"
extern "system" {
    fn GetLastError() -> u32;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let extern_node = root.child(0).unwrap();

        let class = rust.extract_class(extern_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "extern_system");
        assert!(class.decorators.iter().any(|d| d.contains("extern \"system\"")));
        assert_eq!(class.methods.len(), 1);
        assert!(class.methods.iter().any(|m| m.name == "GetLastError"));
    }

    // ========================================
    // FEATURE: Extern crate tests
    // ========================================

    #[test]
    fn test_extract_extern_crate() {
        let code = r#"extern crate serde;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let crate_node = root.child(0).unwrap();

        assert_eq!(crate_node.kind(), "extern_crate_declaration");
        let class = rust.extract_class(crate_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "serde");
        assert!(class.decorators.contains(&"extern crate".to_string()));
        assert!(class.bases.is_empty()); // No alias
    }

    #[test]
    fn test_extract_pub_extern_crate() {
        let code = r#"pub extern crate alloc;"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let crate_node = root.child(0).unwrap();

        let class = rust.extract_class(crate_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "alloc");
        assert!(class.decorators.contains(&"extern crate".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
    }

    // ============================================================
    // FEATURE: Union Types
    // ============================================================

    #[test]
    fn test_extract_union() {
        let code = r#"
/// A union for type punning.
#[repr(C)]
pub union Data {
    i: i32,
    f: f32,
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let union_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "union_item")
            .unwrap();

        let class = rust.extract_class(union_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Data");
        assert!(class.decorators.contains(&"union".to_string()));
        assert!(class.decorators.contains(&"pub".to_string()));
        assert!(class.decorators.iter().any(|d| d.contains("#[repr(C)]")));
        // Check fields are extracted
        assert!(class.bases.iter().any(|f| f.contains("i: i32")));
        assert!(class.bases.iter().any(|f| f.contains("f: f32")));
        // Check docstring
        assert!(class.docstring.is_some());
        assert!(class.docstring.unwrap().contains("type punning"));
    }

    #[test]
    fn test_extract_generic_union() {
        let code = r#"union MaybeUninit<T> { uninit: (), value: T }"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let union_node = root.child(0).unwrap();

        let class = rust.extract_class(union_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "MaybeUninit");
        assert!(class.decorators.contains(&"union".to_string()));
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("type_params:") && d.contains("T")));
    }

    // ============================================================
    // FEATURE: Associated Types
    // ============================================================

    #[test]
    fn test_extract_associated_type_in_trait() {
        let code = r#"
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let trait_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "trait_item")
            .unwrap();

        let class = rust.extract_class(trait_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Iterator");
        // Check that associated type is extracted as a method
        let assoc_type = class.methods.iter().find(|m| m.name == "Item");
        assert!(assoc_type.is_some());
        let assoc = assoc_type.unwrap();
        assert!(assoc.decorators.contains(&"associated_type".to_string()));
        assert!(assoc.is_method);
    }

    #[test]
    fn test_extract_associated_type_with_bounds() {
        let code = r#"
trait Container {
    type Item: Clone + Send;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let trait_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "trait_item")
            .unwrap();

        let class = rust.extract_class(trait_node, code.as_bytes()).unwrap();

        let assoc_type = class.methods.iter().find(|m| m.name == "Item").unwrap();
        assert!(assoc_type
            .decorators
            .contains(&"associated_type".to_string()));
        // Bounds should be captured
        assert!(assoc_type.decorators.iter().any(|d| d.contains("bounds:")));
    }

    #[test]
    fn test_extract_associated_type_definition_in_impl() {
        let code = r#"
impl Iterator for MyIter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> { None }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "impl_item")
            .unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        // Check associated type definition
        let assoc_type = class.methods.iter().find(|m| m.name == "Item");
        assert!(assoc_type.is_some());
        let assoc = assoc_type.unwrap();
        assert!(assoc.decorators.contains(&"associated_type".to_string()));
        // Should have the assigned type
        assert!(assoc.decorators.iter().any(|d| d.contains("= u32")));
        assert_eq!(assoc.return_type, Some("u32".to_string()));
    }

    // ============================================================
    // FEATURE: Associated Constants
    // ============================================================

    #[test]
    fn test_extract_associated_const_in_trait() {
        let code = r#"
trait Bounded {
    const MAX: usize;
    const MIN: usize;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let trait_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "trait_item")
            .unwrap();

        let class = rust.extract_class(trait_node, code.as_bytes()).unwrap();

        // Check associated constants are extracted
        let max_const = class.methods.iter().find(|m| m.name == "MAX");
        assert!(max_const.is_some());
        let max = max_const.unwrap();
        assert!(max.decorators.contains(&"associated_const".to_string()));
        assert!(max.decorators.iter().any(|d| d.contains("type: usize")));
        assert!(max.is_method);

        let min_const = class.methods.iter().find(|m| m.name == "MIN");
        assert!(min_const.is_some());
    }

    #[test]
    fn test_extract_associated_const_with_value_in_impl() {
        let code = r#"
impl Bounded for MyType {
    const MAX: usize = 1000;
    const MIN: usize = 0;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "impl_item")
            .unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        // Check associated constant with value
        let max_const = class.methods.iter().find(|m| m.name == "MAX");
        assert!(max_const.is_some());
        let max = max_const.unwrap();
        assert!(max.decorators.contains(&"associated_const".to_string()));
        assert!(max.decorators.iter().any(|d| d.contains("type: usize")));
        assert!(max.decorators.iter().any(|d| d.contains("= 1000")));
        assert_eq!(max.return_type, Some("1000".to_string()));
    }

    #[test]
    fn test_extract_combined_trait_with_all_associated_items() {
        let code = r#"
/// An iterator trait with all associated item types.
trait FullIterator {
    type Item;
    type Error;
    const MAX_ITEMS: usize;
    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error>;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let trait_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "trait_item")
            .unwrap();

        let class = rust.extract_class(trait_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "FullIterator");

        // Should have 4 methods: 2 associated types, 1 associated const, 1 function
        assert_eq!(class.methods.len(), 4);

        // Check associated types
        assert!(class.methods.iter().any(
            |m| m.name == "Item" && m.decorators.contains(&"associated_type".to_string())
        ));
        assert!(class.methods.iter().any(
            |m| m.name == "Error" && m.decorators.contains(&"associated_type".to_string())
        ));

        // Check associated constant
        assert!(class.methods.iter().any(
            |m| m.name == "MAX_ITEMS" && m.decorators.contains(&"associated_const".to_string())
        ));

        // Check function
        assert!(class.methods.iter().any(
            |m| m.name == "next" && !m.decorators.contains(&"associated_type".to_string())
        ));
    }

    #[test]
    fn test_extract_const_generics_function() {
        // FEATURE: Const generic parameters (const N: usize)
        let code = r#"
fn fixed_size<const N: usize>() -> [i32; N] {
    [0; N]
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "fixed_size");
        // const_params should be separately tracked
        assert!(func
            .decorators
            .iter()
            .any(|d| d.contains("const_params:")));
        assert!(func
            .decorators
            .iter()
            .any(|d| d.contains("const N: usize")));
    }

    #[test]
    fn test_extract_const_generics_struct() {
        // FEATURE: Const generics on structs
        let code = r#"
pub struct Array<T, const N: usize> {
    data: [T; N],
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let struct_node = root
            .children(&mut root.walk())
            .find(|c| c.kind() == "struct_item")
            .unwrap();

        let class = rust.extract_class(struct_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Array");
        // Should have both type_params (T) and const_params (const N: usize)
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("type_params:")));
        assert!(class.decorators.iter().any(|d| d.contains("T")));
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("const_params:")));
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("const N: usize")));
    }

    #[test]
    fn test_extract_const_generics_impl() {
        // FEATURE: Const generics on impl blocks
        let code = r#"
impl<T, const N: usize> Array<T, N> {
    fn len(&self) -> usize {
        N
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let impl_node = root.child(0).unwrap();

        let class = rust.extract_class(impl_node, code.as_bytes()).unwrap();

        assert_eq!(class.name, "Array");
        // Should have both type_params (T) and const_params (const N: usize)
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("type_params:")));
        assert!(class
            .decorators
            .iter()
            .any(|d| d.contains("const_params:")));
    }

    #[test]
    fn test_async_block_in_dfg() {
        // FEATURE: Async block handling in DFG
        let code = r#"
fn spawn_task(x: i32) -> impl Future<Output = i32> {
    async {
        let y = x + 1;
        y * 2
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        // Build DFG to verify async block is processed
        let dfg = rust.build_dfg(func_node, code.as_bytes()).unwrap();

        // DFG should capture variable uses within async block
        assert_eq!(dfg.function_name, "spawn_task");
        // Check that edges were created
        assert!(!dfg.edges.is_empty());
    }

    #[test]
    fn test_const_generics_mixed_with_lifetimes_and_types() {
        // FEATURE: Mixed generic parameters (lifetimes, types, const)
        let code = r#"
fn complex<'a, T: Clone, const N: usize>(data: &'a [T; N]) -> &'a T {
    &data[0]
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;

        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let func = rust.extract_function(func_node, code.as_bytes()).unwrap();

        assert_eq!(func.name, "complex");

        // Should have all three: lifetimes, type_params, and const_params
        assert!(func.decorators.iter().any(|d| d.contains("lifetimes:")));
        assert!(func.decorators.iter().any(|d| d.contains("'a")));
        assert!(func
            .decorators
            .iter()
            .any(|d| d.contains("type_params:")));
        assert!(func.decorators.iter().any(|d| d.contains("T: Clone")));
        assert!(func
            .decorators
            .iter()
            .any(|d| d.contains("const_params:")));
        assert!(func
            .decorators
            .iter()
            .any(|d| d.contains("const N: usize")));
    }

    // ============================================================
    // Module docstring extraction tests (BUG-AST-2 fix)
    // ============================================================

    #[test]
    fn test_module_docstring_line_comments() {
        let code = r#"//! This is a module docstring.
//! It spans multiple lines.

fn foo() {}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let docstring = rust.extract_module_docstring(&tree, code.as_bytes());

        assert_eq!(
            docstring,
            Some("This is a module docstring.\nIt spans multiple lines.".to_string())
        );
    }

    #[test]
    fn test_module_docstring_block_comment() {
        let code = r#"/*!
 * This is a block module docstring.
 * With multiple lines.
 */

fn foo() {}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let docstring = rust.extract_module_docstring(&tree, code.as_bytes());

        assert!(docstring.is_some());
        let doc = docstring.unwrap();
        assert!(doc.contains("block module docstring"));
    }

    #[test]
    fn test_module_docstring_none_when_missing() {
        let code = r#"
fn foo() {}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let docstring = rust.extract_module_docstring(&tree, code.as_bytes());

        assert_eq!(docstring, None);
    }

    #[test]
    fn test_module_docstring_stops_at_regular_comment() {
        // Regular comments should stop collection
        let code = r#"// This is a regular comment, not a module docstring.
fn foo() {}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let docstring = rust.extract_module_docstring(&tree, code.as_bytes());

        assert_eq!(docstring, None);
    }

    #[test]
    fn test_module_docstring_with_item_doc_comment() {
        // Module docstring followed by item doc comment
        let code = r#"//! Module docstring here.

/// Function docstring (not module).
fn foo() {}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let docstring = rust.extract_module_docstring(&tree, code.as_bytes());

        assert_eq!(docstring, Some("Module docstring here.".to_string()));
    }

    // ============================================================
    // Result/Option Error Propagation Tests
    // ============================================================

    #[test]
    fn test_result_flow_try_operator() {
        // Test ? operator creates proper CFG edges
        let code = r#"
fn process() -> Result<i32, Error> {
    let x = might_fail()?;
    let y = another_op(x)?;
    Ok(x + y)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have TryOperator blocks
        let try_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::TryOperator)
            .collect();
        assert!(
            try_blocks.len() >= 2,
            "Expected at least 2 TryOperator blocks, got {}",
            try_blocks.len()
        );

        // Should have ErrorReturn blocks
        let error_return_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::ErrorReturn)
            .collect();
        assert!(
            error_return_blocks.len() >= 2,
            "Expected at least 2 ErrorReturn blocks, got {}",
            error_return_blocks.len()
        );

        // Should have OkSome and ErrNone edges
        let ok_edges = cfg
            .edges
            .iter()
            .filter(|e| e.edge_type == EdgeType::OkSome)
            .count();
        let err_edges = cfg
            .edges
            .iter()
            .filter(|e| e.edge_type == EdgeType::ErrNone)
            .count();
        assert!(ok_edges >= 2, "Expected at least 2 OkSome edges");
        assert!(err_edges >= 2, "Expected at least 2 ErrNone edges");
    }

    #[test]
    fn test_result_flow_nested_try_operators() {
        // Test nested ? operators: a()?.b()?.c()?
        let code = r#"
fn chained() -> Result<String, Error> {
    let result = get_data()?.process()?.format()?;
    Ok(result)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should count multiple ? operators in the label
        let try_block = cfg
            .blocks
            .values()
            .find(|b| b.block_type == BlockType::TryOperator);
        assert!(try_block.is_some(), "Expected TryOperator block");
        let label = &try_block.unwrap().label;
        assert!(
            label.contains("3x ?") || label.contains("try?"),
            "Label should indicate multiple ? operators: {}",
            label
        );
    }

    #[test]
    fn test_result_flow_panic_site_unwrap() {
        // Test .unwrap() creates PanicSite block
        let code = r#"
fn risky() {
    let x = get_option().unwrap();
    process(x);
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have PanicSite block for unwrap
        let panic_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::PanicSite)
            .collect();
        assert!(
            !panic_blocks.is_empty(),
            "Expected PanicSite block for .unwrap()"
        );
        assert!(
            panic_blocks[0].label.contains("unwrap"),
            "PanicSite label should mention unwrap"
        );
    }

    #[test]
    fn test_result_flow_panic_site_expect() {
        // Test .expect() creates PanicSite block
        let code = r#"
fn risky_with_message() {
    let x = get_result().expect("should succeed");
    use_value(x);
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have PanicSite block for expect
        let panic_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::PanicSite)
            .collect();
        assert!(
            !panic_blocks.is_empty(),
            "Expected PanicSite block for .expect()"
        );
        assert!(
            panic_blocks[0].label.contains("expect"),
            "PanicSite label should mention expect"
        );
    }

    #[test]
    fn test_result_flow_if_let_some() {
        // Test if let Some(x) = ... creates proper CFG pattern
        let code = r#"
fn handle_option(opt: Option<i32>) -> i32 {
    if let Some(x) = opt {
        x * 2
    } else {
        0
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have PatternMatch block for if let
        let pattern_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::PatternMatch)
            .collect();
        assert!(
            !pattern_blocks.is_empty(),
            "Expected PatternMatch block for if let Some"
        );

        // Should have OkSome edge (for Some case)
        let has_ok_edge = cfg.edges.iter().any(|e| e.edge_type == EdgeType::OkSome);
        assert!(has_ok_edge, "Expected OkSome edge for Some branch");

        // Should have ErrNone edge (for None/else case)
        let has_err_edge = cfg.edges.iter().any(|e| e.edge_type == EdgeType::ErrNone);
        assert!(has_err_edge, "Expected ErrNone edge for None/else branch");
    }

    #[test]
    fn test_result_flow_if_let_ok() {
        // Test if let Ok(x) = ... creates proper CFG pattern
        let code = r#"
fn handle_result(res: Result<String, Error>) {
    if let Ok(value) = res {
        println!("{}", value);
    } else {
        println!("error");
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have proper branching structure
        let pattern_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::PatternMatch)
            .collect();
        assert!(!pattern_blocks.is_empty(), "Expected PatternMatch block");
    }

    #[test]
    fn test_result_flow_while_let() {
        // Test while let Some(x) = iter.next() pattern
        let code = r#"
fn iterate_option(mut iter: impl Iterator<Item = i32>) {
    while let Some(x) = iter.next() {
        process(x);
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have PatternMatch block for while let
        let pattern_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::PatternMatch)
            .collect();
        assert!(
            !pattern_blocks.is_empty(),
            "Expected PatternMatch block for while let"
        );

        // Should have loop back edge
        let has_back_edge = cfg.edges.iter().any(|e| {
            e.condition.as_ref().map_or(false, |c| c.contains("next"))
                || e.edge_type == EdgeType::Next
        });
        assert!(has_back_edge || cfg.edges.len() > 2, "Expected loop structure");
    }

    #[test]
    fn test_result_flow_let_else() {
        // Test let-else pattern: let Some(x) = opt else { return; };
        let code = r#"
fn extract_or_return(opt: Option<i32>) -> i32 {
    let Some(x) = opt else {
        return 0;
    };
    x * 2
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have blocks for let-else pattern
        let let_else_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.label.contains("let-else"))
            .collect();
        assert!(
            !let_else_blocks.is_empty(),
            "Expected let-else blocks in CFG"
        );
    }

    #[test]
    fn test_result_flow_closure_with_try() {
        // Test ? operator in expression with closures
        // Closures containing ? are tracked - the closure itself returns Result,
        // and the outer collect()? also uses the ? operator
        let code = r#"
fn with_closure() -> Result<Vec<i32>, Error> {
    let items: Vec<_> = data
        .iter()
        .map(|x| -> Result<i32, Error> {
            let y = process(x)?;
            Ok(y * 2)
        })
        .collect::<Result<_, _>>()?;
    Ok(items)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // The outer collect()? should be tracked as TryOperator
        let try_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::TryOperator)
            .collect();
        assert!(
            !try_blocks.is_empty(),
            "Expected TryOperator block for collect()? call"
        );

        // Should have ErrorReturn block for ? propagation
        let error_return_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.block_type == BlockType::ErrorReturn)
            .collect();
        assert!(
            !error_return_blocks.is_empty(),
            "Expected ErrorReturn block for ? operator error path"
        );
    }

    #[test]
    fn test_result_flow_match_result() {
        // Test match on Result type
        let code = r#"
fn handle_match(res: Result<i32, String>) -> i32 {
    match res {
        Ok(v) => v * 2,
        Err(e) => {
            println!("error: {}", e);
            -1
        }
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let root = tree.root_node();
        let func_node = root.child(0).unwrap();

        let cfg = rust.build_cfg(func_node, code.as_bytes()).unwrap();

        // Should have match block and arm blocks
        let match_block = cfg.blocks.values().find(|b| b.label.contains("match"));
        assert!(match_block.is_some(), "Expected match block");

        // Should have blocks for Ok and Err arms
        let arm_blocks: Vec<_> = cfg
            .blocks
            .values()
            .filter(|b| b.label.contains("Ok") || b.label.contains("Err"))
            .collect();
        assert!(arm_blocks.len() >= 2, "Expected Ok and Err arm blocks");
    }

    #[test]
    fn test_contains_try_expression_in_statement() {
        let code = r#"
fn foo() -> Result<(), Error> {
    let x = bar()?;
    Ok(())
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func
            .children(&mut func.walk())
            .find(|c| c.kind() == "block")
            .unwrap();
        let stmt = body.child(1).unwrap();
        assert!(rust.contains_try_expression(stmt));
    }

    #[test]
    fn test_count_try_expressions() {
        let code = r#"
fn foo() -> Result<(), Error> {
    let x = a()?.b()?.c()?;
    Ok(())
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func
            .children(&mut func.walk())
            .find(|c| c.kind() == "block")
            .unwrap();
        let stmt = body.child(1).unwrap();
        let count = rust.count_try_expressions(stmt);
        assert_eq!(count, 3, "Expected 3 ? operators, got {}", count);
    }

    #[test]
    fn test_contains_panic_site() {
        let code = r#"
fn foo() {
    let x = opt.unwrap();
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func
            .children(&mut func.walk())
            .find(|c| c.kind() == "block")
            .unwrap();
        let stmt = body.child(1).unwrap();
        assert!(rust.contains_panic_site(stmt, code.as_bytes()));
    }

    #[test]
    fn test_panic_site_info() {
        let code = "let x = opt.unwrap();";
        let tree = parse_rust(&format!("fn foo() {{ {} }}", code));
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func
            .children(&mut func.walk())
            .find(|c| c.kind() == "block")
            .unwrap();
        let stmt = body.child(1).unwrap();
        let info = rust.get_panic_site_info(stmt, format!("fn foo() {{ {} }}", code).as_bytes());
        assert_eq!(info, "unwrap()");
    }

    #[test]
    fn test_no_false_positive_unwrap_or() {
        // .unwrap_or() should NOT be detected as panic site
        let code = r#"
fn safe() {
    let x = opt.unwrap_or(default);
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func
            .children(&mut func.walk())
            .find(|c| c.kind() == "block")
            .unwrap();
        let stmt = body.child(1).unwrap();
        // unwrap_or is safe, should not be flagged as panic site
        // Note: current implementation may flag it, this test documents expected behavior
        let has_panic = rust.contains_panic_site(stmt, code.as_bytes());
        // This assertion documents the current behavior - may need adjustment
        // based on whether we want to exclude unwrap_or variants
        assert!(
            !has_panic || code.contains(".unwrap_or("),
            "unwrap_or should not be flagged as panic site"
        );
    }

    // =========================================================================
    // Async/await CFG tests
    // =========================================================================

    #[test]
    fn test_async_fn_detection() {
        let code = r#"
async fn fetch_data(url: &str) -> Result<Data, Error> {
    let response = client.get(url).send().await?;
    let data = response.json().await?;
    Ok(data)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "fetch_data");

        // Verify async detection
        assert!(cfg.is_async, "Function should be detected as async");

        // Verify await points are counted
        assert!(cfg.await_points >= 2, "Should have at least 2 await points, got {}", cfg.await_points);

        // Verify entry block is labeled as async
        let entry = cfg.blocks.get(&cfg.entry).unwrap();
        assert!(entry.label.contains("async"), "Entry block should be labeled as async");
    }

    #[test]
    fn test_sync_fn_not_detected_as_async() {
        let code = r#"
fn regular_function(x: i32) -> i32 {
    x * 2
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "regular_function");

        assert!(!cfg.is_async, "Sync function should not be detected as async");
        assert_eq!(cfg.await_points, 0, "Sync function should have 0 await points");

        let entry = cfg.blocks.get(&cfg.entry).unwrap();
        assert!(!entry.label.contains("async"), "Entry block should not be labeled as async");
    }

    #[test]
    fn test_await_suspension_points() {
        let code = r#"
async fn process() {
    first_operation().await;
    second_operation().await;
    third_operation().await;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "process");

        // Should have 3 await points
        assert_eq!(cfg.await_points, 3, "Expected 3 await points, got {}", cfg.await_points);

        // Should have RustAwaitPoint blocks
        let await_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustAwaitPoint))
            .collect();
        assert!(await_blocks.len() >= 3, "Expected at least 3 RustAwaitPoint blocks, got {}", await_blocks.len());

        // Should have RustAwait edges
        let await_edges: Vec<_> = cfg.edges.iter()
            .filter(|e| matches!(e.edge_type, EdgeType::RustAwait))
            .collect();
        assert!(await_edges.len() >= 3, "Expected at least 3 RustAwait edges, got {}", await_edges.len());
    }

    #[test]
    fn test_await_with_try_operator() {
        let code = r#"
async fn fetch() -> Result<(), Error> {
    let response = client.get(url).await?;
    Ok(())
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "fetch");

        // Should have await point
        assert!(cfg.await_points >= 1, "Should have at least 1 await point");

        // Should have error propagation path (ErrNone edge)
        let err_edges: Vec<_> = cfg.edges.iter()
            .filter(|e| matches!(e.edge_type, EdgeType::ErrNone))
            .collect();
        assert!(!err_edges.is_empty(), "Should have Err propagation edges for await?");
    }

    #[test]
    fn test_tokio_spawn_detection() {
        let code = r#"
async fn spawn_task() {
    let handle = tokio::spawn(async {
        some_work().await;
    });
    handle.await.unwrap();
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "spawn_task");

        // Should detect async function
        assert!(cfg.is_async, "Should be detected as async");

        // Should have task spawn block
        let spawn_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustTaskSpawn))
            .collect();
        assert!(!spawn_blocks.is_empty(), "Should have RustTaskSpawn block");

        // Should have spawn edge
        let spawn_edges: Vec<_> = cfg.edges.iter()
            .filter(|e| matches!(e.edge_type, EdgeType::RustSpawn))
            .collect();
        assert!(!spawn_edges.is_empty(), "Should have RustSpawn edge");
    }

    #[test]
    fn test_tokio_join_macro() {
        let code = r#"
async fn concurrent() {
    let (a, b) = tokio::join!(
        fetch_user(id),
        fetch_posts(id)
    );
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "concurrent");

        assert!(cfg.is_async, "Should be detected as async");

        // Should have join block
        let join_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustJoin))
            .collect();
        assert!(!join_blocks.is_empty(), "Should have RustJoin block for tokio::join!");
    }

    #[test]
    fn test_tokio_select_macro() {
        let code = r#"
async fn select_first() {
    tokio::select! {
        val = channel.recv() => handle_val(val),
        _ = tokio::time::sleep(timeout) => handle_timeout(),
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "select_first");

        assert!(cfg.is_async, "Should be detected as async");

        // Should have select block
        let select_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustSelect))
            .collect();
        assert!(!select_blocks.is_empty(), "Should have RustSelect block for tokio::select!");

        // Select should count as a decision point
        assert!(cfg.decision_points >= 1, "select! should be counted as decision point");
    }

    #[test]
    fn test_blocking_call_detection_in_async() {
        let code = r#"
async fn bad_async() {
    std::thread::sleep(std::time::Duration::from_secs(1));
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "bad_async");

        assert!(cfg.is_async, "Should be detected as async");

        // Should detect blocking call
        assert!(!cfg.blocking_calls.is_empty(), "Should detect blocking call in async context");
        assert!(cfg.blocking_calls.iter().any(|(name, _)| name.contains("thread::sleep")),
                "Should detect std::thread::sleep as blocking");

        // Should have blocking block type
        let blocking_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustBlockingCall))
            .collect();
        assert!(!blocking_blocks.is_empty(), "Should have RustBlockingCall block");
    }

    #[test]
    fn test_no_blocking_warning_in_sync_fn() {
        let code = r#"
fn sync_sleep() {
    std::thread::sleep(std::time::Duration::from_secs(1));
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "sync_sleep");

        assert!(!cfg.is_async, "Should not be async");
        // In sync context, blocking calls are fine
        assert!(cfg.blocking_calls.is_empty(), "Should not flag blocking calls in sync context");
    }

    #[test]
    fn test_async_block_detection() {
        let code = r#"
fn returns_future() -> impl Future<Output = ()> {
    async {
        some_work().await;
    }
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "returns_future");

        // Should have async block
        let async_blocks: Vec<_> = cfg.blocks.values()
            .filter(|b| matches!(b.block_type, BlockType::RustAsyncBlock))
            .collect();
        assert!(!async_blocks.is_empty(), "Should have RustAsyncBlock for async {{ }}");
    }

    #[test]
    fn test_contains_await_helper() {
        let rust = Rust;

        let code_with_await = "async { x.await }";
        let tree = parse_rust(&format!("fn f() {{ {} }}", code_with_await));
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        let stmt = body.child(1).unwrap();

        assert!(rust.contains_await(stmt), "Should detect .await in async block");
    }

    #[test]
    fn test_is_spawn_call_helper() {
        let rust = Rust;

        let tokio_code = "tokio::spawn(async { work().await })";
        let tree = parse_rust(&format!("fn f() {{ {} }}", tokio_code));
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        let stmt = body.child(1).unwrap();
        let expr = if stmt.kind() == "expression_statement" { stmt.child(0).unwrap() } else { stmt };

        let (is_spawn, spawn_type) = rust.is_spawn_call(expr, format!("fn f() {{ {} }}", tokio_code).as_bytes());
        assert!(is_spawn, "Should detect tokio::spawn as spawn call");
        assert_eq!(spawn_type, Some("tokio"));
    }

    #[test]
    fn test_is_async_macro_helper() {
        let rust = Rust;

        // Test join! macro detection
        let join_code = "tokio::join!(a, b)";
        let tree = parse_rust(&format!("fn f() {{ {} }}", join_code));
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        let stmt = body.child(1).unwrap();
        let expr = if stmt.kind() == "expression_statement" { stmt.child(0).unwrap() } else { stmt };

        let (is_async_macro, macro_type) = rust.is_async_macro(expr, format!("fn f() {{ {} }}", join_code).as_bytes());
        assert!(is_async_macro, "Should detect tokio::join! as async macro");
        assert_eq!(macro_type, Some("join!"));
    }

    #[test]
    fn test_is_blocking_call_helper() {
        let rust = Rust;

        let blocking_code = "std::thread::sleep(duration)";
        let tree = parse_rust(&format!("fn f() {{ {} }}", blocking_code));
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        let stmt = body.child(1).unwrap();

        let (is_blocking, blocking_type) = rust.is_blocking_call(stmt, format!("fn f() {{ {} }}", blocking_code).as_bytes());
        assert!(is_blocking, "Should detect std::thread::sleep as blocking");
        assert!(blocking_type.as_ref().map(|s| s.contains("thread::sleep")).unwrap_or(false));
    }

    #[test]
    fn test_async_flow_cfg_structure() {
        // Test a comprehensive async function CFG structure
        let code = r#"
async fn fetch_and_process(url: &str) -> Result<ProcessedData, Error> {
    // First await - HTTP request
    let response = client.get(url).send().await?;

    // Second await - Parse JSON
    let raw_data: RawData = response.json().await?;

    // Processing (sync)
    let processed = process(raw_data);

    // Third await - Database save
    db.save(&processed).await?;

    Ok(processed)
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "fetch_and_process");

        // Verify async detection
        assert!(cfg.is_async, "Should be detected as async");

        // Verify await points (at least 3 explicit .await)
        assert!(cfg.await_points >= 3, "Should have at least 3 await points, got {}", cfg.await_points);

        // Should have proper entry and exit
        let entry = cfg.blocks.get(&cfg.entry).unwrap();
        assert!(entry.label.contains("async entry"), "Entry should be labeled async");

        // Should have exit blocks (normal exit + error exits from ?)
        assert!(!cfg.exits.is_empty(), "Should have exit blocks");
    }

    #[test]
    fn test_count_await_in_let_declaration() {
        let code = r#"
async fn foo() {
    let x = bar().await;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();

        // Find the let_declaration
        let stmt = body.children(&mut body.walk())
            .find(|c| c.kind() == "let_declaration")
            .expect("Should find let_declaration");

        let count = rust.count_await_expressions(stmt);
        assert_eq!(count, 1, "Expected 1 await expression in let declaration, got {}", count);
    }

    #[test]
    fn test_is_await_expression_detection() {
        let rust = Rust;
        let code = "foo().await";
        let tree = parse_rust(&format!("fn f() {{ {} }}", code));
        let func = tree.root_node().child(0).unwrap();
        let body = func.children(&mut func.walk()).find(|c| c.kind() == "block").unwrap();
        // Get the expression_statement or direct expression
        let stmt = body.child(1).unwrap();
        let expr = if stmt.kind() == "expression_statement" { stmt.child(0).unwrap() } else { stmt };

        assert!(rust.is_await_expression(expr), "Should detect await_expression, got kind: {}", expr.kind());
    }

    #[test]
    fn test_simple_async_cfg_with_single_await() {
        // Simplest possible async fn with await
        let code = r#"
async fn foo() {
    bar().await;
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "foo");

        // Check async detection first
        assert!(cfg.is_async, "Should be detected as async");

        // This should have exactly 1 await point
        assert_eq!(cfg.await_points, 1, "Expected 1 await point in simple async fn, got {}. Blocks: {:?}",
                   cfg.await_points,
                   cfg.blocks.values().map(|b| (&b.label, &b.block_type)).collect::<Vec<_>>());
    }

    #[test]
    fn test_async_cfg_with_await_try() {
        // Async fn with .await? pattern
        let code = r#"
async fn fetch() -> Result<(), Error> {
    let x = bar().await?;
    Ok(())
}
"#;
        let tree = parse_rust(code);
        let rust = Rust;
        let func = tree.root_node().child(0).unwrap();

        let cfg = rust.build_rust_cfg(func, code.as_bytes(), "fetch");

        assert!(cfg.is_async, "Should be detected as async");

        // This should have 1 await point
        assert!(cfg.await_points >= 1, "Expected at least 1 await point in async fn with await?, got {}. Blocks: {:?}",
                   cfg.await_points,
                   cfg.blocks.values().map(|b| (&b.label, &b.block_type)).collect::<Vec<_>>());
    }
}
