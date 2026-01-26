//! Translation context for Go to Brrr IR conversion.
//!
//! Provides shared state during translation including string interning,
//! type environment, and node ID generation.

use crate::TranslationContext;
use brrr_repr::{BrrrType, NodeId, NodeIdCounter};
use lasso::{Rodeo, Spur};
use rustc_hash::FxHashMap;
use tree_sitter::Node;

/// Context for Go to Brrr IR translation.
///
/// Maintains state during translation including:
/// - String interning via lasso
/// - Type environment for declared types
/// - Variable environment for scope tracking
/// - Node ID counter for CPG integration
/// - Channel session type tracking
pub struct GoTranslationContext<'src> {
    /// Source code bytes
    source: &'src [u8],

    /// String interner
    interner: Rodeo,

    /// Type environment: name -> type
    type_env: FxHashMap<Spur, BrrrType>,

    /// Variable environment stack (for nested scopes)
    var_env: Vec<FxHashMap<Spur, VarInfo>>,

    /// Node ID counter for unique IDs
    node_counter: NodeIdCounter,

    /// Type variable counter
    type_var_counter: u32,

    /// Package name (from package clause)
    package_name: String,

    /// Channel types for session type tracking
    channel_types: FxHashMap<Spur, ChannelInfo>,

    /// Current function's named return variables (if any)
    named_returns: Vec<(Spur, BrrrType)>,

    /// Defer stack: collects deferred expressions in order of appearance.
    /// At function exit, these are wrapped in nested Try-finally blocks
    /// in reverse order (LIFO semantics).
    defer_stack: Vec<brrr_repr::Expr>,

    /// Collected imports
    imports: Vec<brrr_repr::decl::Import>,

    /// Iota counter for const declarations
    iota_counter: Option<i128>,
}

/// Information about a variable binding
#[derive(Debug, Clone)]
pub struct VarInfo {
    /// Variable's type
    pub ty: BrrrType,
    /// Is this a mutable binding?
    pub is_mut: bool,
    /// Variable ID for Brrr IR
    pub var_id: Spur,
}

/// Information about a channel for session type tracking
#[derive(Debug, Clone)]
pub struct ChannelInfo {
    /// Element type of the channel
    pub elem_type: BrrrType,
    /// Channel direction (bidirectional, send-only, recv-only)
    pub direction: ChannelDirection,
    /// Buffer size (0 for unbuffered)
    pub buffer_size: Option<usize>,
}

/// Channel direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelDirection {
    Bidirectional,
    SendOnly,
    RecvOnly,
}

impl<'src> GoTranslationContext<'src> {
    /// Create a new translation context for the given source.
    pub fn new(source: &'src [u8]) -> Self {
        let mut interner = Rodeo::default();

        // Pre-intern common Go type names
        let _ = interner.get_or_intern("bool");
        let _ = interner.get_or_intern("int");
        let _ = interner.get_or_intern("int8");
        let _ = interner.get_or_intern("int16");
        let _ = interner.get_or_intern("int32");
        let _ = interner.get_or_intern("int64");
        let _ = interner.get_or_intern("uint");
        let _ = interner.get_or_intern("uint8");
        let _ = interner.get_or_intern("uint16");
        let _ = interner.get_or_intern("uint32");
        let _ = interner.get_or_intern("uint64");
        let _ = interner.get_or_intern("uintptr");
        let _ = interner.get_or_intern("float32");
        let _ = interner.get_or_intern("float64");
        let _ = interner.get_or_intern("complex64");
        let _ = interner.get_or_intern("complex128");
        let _ = interner.get_or_intern("string");
        let _ = interner.get_or_intern("byte");
        let _ = interner.get_or_intern("rune");
        let _ = interner.get_or_intern("error");
        let _ = interner.get_or_intern("any");

        Self {
            source,
            interner,
            type_env: FxHashMap::default(),
            var_env: vec![FxHashMap::default()], // Start with global scope
            node_counter: NodeIdCounter::new(),
            type_var_counter: 0,
            package_name: String::new(),
            channel_types: FxHashMap::default(),
            named_returns: Vec::new(),
            defer_stack: Vec::new(),
            imports: Vec::new(),
            iota_counter: None,
        }
    }

    /// Get the package name.
    pub fn package_name(&self) -> &str {
        &self.package_name
    }

    /// Set the package name.
    pub fn set_package_name(&mut self, name: &str) {
        self.package_name = name.to_string();
    }

    /// Enter a new scope (e.g., function body, block).
    pub fn push_scope(&mut self) {
        self.var_env.push(FxHashMap::default());
    }

    /// Exit the current scope.
    pub fn pop_scope(&mut self) {
        self.var_env.pop();
    }

    /// Bind a variable in the current scope.
    pub fn bind_var(&mut self, name: Spur, ty: BrrrType, is_mut: bool) {
        let info = VarInfo {
            ty,
            is_mut,
            var_id: name,
        };
        if let Some(scope) = self.var_env.last_mut() {
            scope.insert(name, info);
        }
    }

    /// Look up a variable, searching from innermost to outermost scope.
    pub fn lookup_var(&self, name: Spur) -> Option<&VarInfo> {
        for scope in self.var_env.iter().rev() {
            if let Some(info) = scope.get(&name) {
                return Some(info);
            }
        }
        None
    }

    /// Register a channel with its type info.
    pub fn register_channel(&mut self, name: Spur, info: ChannelInfo) {
        self.channel_types.insert(name, info);
    }

    /// Look up channel info.
    pub fn lookup_channel(&self, name: Spur) -> Option<&ChannelInfo> {
        self.channel_types.get(&name)
    }

    /// Set named return variables for current function.
    pub fn set_named_returns(&mut self, returns: Vec<(Spur, BrrrType)>) {
        self.named_returns = returns;
    }

    /// Get named return variables.
    pub fn named_returns(&self) -> &[(Spur, BrrrType)] {
        &self.named_returns
    }

    /// Clear named returns (when exiting function).
    pub fn clear_named_returns(&mut self) {
        self.named_returns.clear();
    }

    /// Push a deferred expression onto the defer stack.
    /// Defers are collected in order of appearance and executed in LIFO order
    /// at function exit.
    pub fn push_defer(&mut self, expr: brrr_repr::Expr) {
        self.defer_stack.push(expr);
    }

    /// Take all collected defers and clear the stack.
    /// Returns defers in order of appearance (caller should reverse for LIFO).
    pub fn take_defers(&mut self) -> Vec<brrr_repr::Expr> {
        std::mem::take(&mut self.defer_stack)
    }

    /// Check if there are pending defers.
    pub fn has_defers(&self) -> bool {
        !self.defer_stack.is_empty()
    }

    /// Get the number of pending defers.
    pub fn defer_count(&self) -> usize {
        self.defer_stack.len()
    }

    /// Clear the defer stack (used when entering a new function scope).
    pub fn clear_defers(&mut self) {
        self.defer_stack.clear();
    }

    /// Resolve an interned string back to &str.
    pub fn resolve(&self, spur: Spur) -> &str {
        self.interner.resolve(&spur)
    }

    /// Get source bytes.
    pub fn source_bytes(&self) -> &[u8] {
        self.source
    }

    /// Add an import.
    pub fn add_import(&mut self, import: brrr_repr::decl::Import) {
        self.imports.push(import);
    }

    /// Get collected imports.
    pub fn imports(&self) -> &[brrr_repr::decl::Import] {
        &self.imports
    }

    /// Start a const block (initialize iota to 0).
    pub fn start_const_block(&mut self) {
        self.iota_counter = Some(0);
    }

    /// End a const block.
    pub fn end_const_block(&mut self) {
        self.iota_counter = None;
    }

    /// Get current iota value and increment for next const.
    pub fn next_iota(&mut self) -> Option<i128> {
        let current = self.iota_counter;
        if let Some(ref mut counter) = self.iota_counter {
            *counter += 1;
        }
        current
    }

    /// Get current iota value without incrementing.
    pub fn current_iota(&self) -> Option<i128> {
        self.iota_counter
    }

    /// Check if we're inside a const block.
    pub fn in_const_block(&self) -> bool {
        self.iota_counter.is_some()
    }
}

impl<'src> TranslationContext for GoTranslationContext<'src> {
    fn intern(&mut self, s: &str) -> Spur {
        self.interner.get_or_intern(s)
    }

    fn lookup_type(&self, name: Spur) -> Option<&BrrrType> {
        self.type_env.get(&name)
    }

    fn bind_type(&mut self, name: Spur, ty: BrrrType) {
        self.type_env.insert(name, ty);
    }

    fn fresh_node_id(&mut self) -> NodeId {
        self.node_counter.fresh()
    }

    fn fresh_type_var(&mut self) -> brrr_repr::types::TypeVar {
        let id = self.type_var_counter;
        self.type_var_counter += 1;
        // Create a type variable name like _T0, _T1, etc.
        let name = format!("_T{}", id);
        self.intern(&name)
    }

    fn node_text<'a>(&self, node: Node<'a>) -> &'a str {
        // Safety: node came from parsing self.source, so the source outlives the node.
        // We use unsafe to extend the lifetime from 'src to 'a.
        // This is safe because:
        // 1. The node was created from parsing self.source
        // 2. The node's lifetime 'a is bounded by self.source's lifetime
        // 3. We're returning a subslice of self.source
        let bytes = &self.source[node.byte_range()];
        // Go source is always valid UTF-8
        let s = std::str::from_utf8(bytes).unwrap_or("");
        // SAFETY: The source outlives any node derived from it
        unsafe { std::mem::transmute::<&str, &'a str>(s) }
    }

    fn source(&self) -> &[u8] {
        self.source
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_creation() {
        let source = b"package main";
        let ctx = GoTranslationContext::new(source);
        assert!(ctx.package_name().is_empty());
    }

    #[test]
    fn test_scope_management() {
        let source = b"package main";
        let mut ctx = GoTranslationContext::new(source);

        let name = ctx.intern("x");
        ctx.bind_var(name, BrrrType::BOOL, false);
        assert!(ctx.lookup_var(name).is_some());

        ctx.push_scope();
        let inner_name = ctx.intern("y");
        ctx.bind_var(inner_name, BrrrType::STRING, true);

        // Can see both x and y
        assert!(ctx.lookup_var(name).is_some());
        assert!(ctx.lookup_var(inner_name).is_some());

        ctx.pop_scope();

        // Can only see x now
        assert!(ctx.lookup_var(name).is_some());
        assert!(ctx.lookup_var(inner_name).is_none());
    }

    #[test]
    fn test_interning() {
        let source = b"package main";
        let mut ctx = GoTranslationContext::new(source);

        let s1 = ctx.intern("hello");
        let s2 = ctx.intern("hello");
        assert_eq!(s1, s2);

        let s3 = ctx.intern("world");
        assert_ne!(s1, s3);
    }
}
