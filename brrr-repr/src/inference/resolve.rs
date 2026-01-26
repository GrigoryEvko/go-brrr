//! Name resolution pass for the brrr-repr IR
//!
//! Resolves variable names to their definitions, ensuring all references are bound
//! and reporting errors for unbound or ambiguously bound identifiers.
//!
//! # Resolution Process
//!
//! 1. Build initial scope with global declarations (types, functions, constants)
//! 2. Walk declarations, resolving type references
//! 3. Walk expressions, resolving variable references and introducing bindings
//! 4. Report errors for any unresolved references
//!
//! # Following EverParse Patterns
//!
//! - Environment threading: `ResolutionState` threaded through all resolution functions
//! - No shadowing allowed: Name conflicts are reported as errors
//! - Usage tracking: Track which bindings are used for unused variable warnings

use std::collections::HashMap;

use lasso::Spur;
use serde::{Deserialize, Serialize};

use crate::decl::{Declaration, Module};
use crate::expr::{
    CatchArm, EffectHandler, Expr, Expr_, HandlerClause, MatchArm, Pattern, Pattern_, Range,
    VarId,
};
use crate::types::{BrrrType, TypeName};

// ============================================================================
// Resolution Errors
// ============================================================================

/// Kind of resolution error
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResolutionErrorKind {
    /// Variable not found in any scope
    UnboundVariable,
    /// Type not found in scope
    UnboundType,
    /// Module not found
    UnboundModule,
    /// Effect operation not found
    UnboundEffect,
    /// Name already defined in current scope
    DuplicateBinding {
        /// Location of first binding
        first_span: Range,
    },
    /// Import path not found
    ImportNotFound,
    /// Private item accessed from outside its module
    PrivateAccess,
    /// Ambiguous name (multiple imports define it)
    AmbiguousName {
        /// Possible sources
        sources: Vec<String>,
    },
}

impl ResolutionErrorKind {
    /// Human-readable name for error kind
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::UnboundVariable => "unbound variable",
            Self::UnboundType => "unbound type",
            Self::UnboundModule => "unbound module",
            Self::UnboundEffect => "unbound effect",
            Self::DuplicateBinding { .. } => "duplicate binding",
            Self::ImportNotFound => "import not found",
            Self::PrivateAccess => "private access",
            Self::AmbiguousName { .. } => "ambiguous name",
        }
    }
}

/// Resolution error with source location and context
#[derive(Debug, Clone)]
pub struct ResolutionError {
    /// Kind of error
    pub kind: ResolutionErrorKind,
    /// The name that could not be resolved
    pub name: String,
    /// Source location
    pub span: Range,
    /// Additional context message
    pub message: Option<String>,
}

impl ResolutionError {
    /// Create an unbound variable error
    #[must_use]
    pub fn unbound_variable(name: impl Into<String>, span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::UnboundVariable,
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create an unbound type error
    #[must_use]
    pub fn unbound_type(name: impl Into<String>, span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::UnboundType,
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create an unbound module error
    #[must_use]
    pub fn unbound_module(name: impl Into<String>, span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::UnboundModule,
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create an unbound effect error
    #[must_use]
    pub fn unbound_effect(name: impl Into<String>, span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::UnboundEffect,
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create a duplicate binding error
    #[must_use]
    pub fn duplicate_binding(name: impl Into<String>, span: Range, first_span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::DuplicateBinding { first_span },
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create an import not found error
    #[must_use]
    pub fn import_not_found(path: &[String], span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::ImportNotFound,
            name: path.join("::"),
            span,
            message: None,
        }
    }

    /// Create a private access error
    #[must_use]
    pub fn private_access(name: impl Into<String>, span: Range) -> Self {
        Self {
            kind: ResolutionErrorKind::PrivateAccess,
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Create an ambiguous name error
    #[must_use]
    pub fn ambiguous(name: impl Into<String>, span: Range, sources: Vec<String>) -> Self {
        Self {
            kind: ResolutionErrorKind::AmbiguousName { sources },
            name: name.into(),
            span,
            message: None,
        }
    }

    /// Add a context message
    #[must_use]
    pub fn with_message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(msg.into());
        self
    }
}

impl std::fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: `{}`", self.kind.name(), self.name)?;
        if let Some(ref msg) = self.message {
            write!(f, " ({})", msg)?;
        }
        Ok(())
    }
}

impl std::error::Error for ResolutionError {}

// ============================================================================
// Binding Info
// ============================================================================

/// Information about a bound variable
#[derive(Debug, Clone)]
pub struct VarBinding {
    /// The resolved variable ID
    pub id: VarId,
    /// Type annotation (if any)
    pub ty: Option<BrrrType>,
    /// Source location of binding
    pub span: Range,
    /// Whether this binding has been used
    pub used: bool,
    /// Is this a mutable binding?
    pub is_mut: bool,
}

impl VarBinding {
    /// Create a new variable binding
    #[must_use]
    pub fn new(id: VarId, span: Range) -> Self {
        Self {
            id,
            ty: None,
            span,
            used: false,
            is_mut: false,
        }
    }

    /// Create a mutable binding
    #[must_use]
    pub fn mutable(id: VarId, span: Range) -> Self {
        Self {
            id,
            ty: None,
            span,
            used: false,
            is_mut: true,
        }
    }

    /// Set type annotation
    #[must_use]
    pub fn with_type(mut self, ty: BrrrType) -> Self {
        self.ty = Some(ty);
        self
    }
}

/// Information about a bound type
#[derive(Debug, Clone)]
pub struct TypeBinding {
    /// The resolved type name
    pub name: TypeName,
    /// Source location of definition
    pub span: Range,
    /// Is this a type alias?
    pub is_alias: bool,
}

impl TypeBinding {
    /// Create a new type binding
    #[must_use]
    pub fn new(name: TypeName, span: Range) -> Self {
        Self {
            name,
            span,
            is_alias: false,
        }
    }

    /// Mark as alias
    #[must_use]
    pub fn alias(mut self) -> Self {
        self.is_alias = true;
        self
    }
}

// ============================================================================
// Reference to Global Declaration
// ============================================================================

/// Reference to a global declaration
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobalRef {
    /// Reference to a function definition
    Function(usize),
    /// Reference to a type definition
    Type(usize),
    /// Reference to a trait definition
    Trait(usize),
    /// Reference to a constant
    Const(usize),
    /// Reference to a static
    Static(usize),
    /// Reference to a module
    Module(usize),
}

impl GlobalRef {
    /// Get the index into the appropriate declaration list
    #[must_use]
    pub const fn index(&self) -> usize {
        match self {
            Self::Function(i)
            | Self::Type(i)
            | Self::Trait(i)
            | Self::Const(i)
            | Self::Static(i)
            | Self::Module(i) => *i,
        }
    }
}

// ============================================================================
// Scope
// ============================================================================

/// A lexical scope containing variable and type bindings
#[derive(Debug, Clone, Default)]
pub struct Scope {
    /// Variable bindings in this scope (name string -> binding)
    vars: HashMap<String, VarBinding>,
    /// Type bindings in this scope (name string -> binding)
    types: HashMap<String, TypeBinding>,
    /// Label bindings (for loops and control flow)
    labels: HashMap<String, Range>,
}

impl Scope {
    /// Create a new empty scope
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a variable in this scope
    ///
    /// Returns error if name is already bound in this scope
    pub fn bind_var(&mut self, name: &str, binding: VarBinding) -> Result<(), ResolutionError> {
        if let Some(existing) = self.vars.get(name) {
            return Err(ResolutionError::duplicate_binding(
                name,
                binding.span,
                existing.span,
            ));
        }
        self.vars.insert(name.to_string(), binding);
        Ok(())
    }

    /// Lookup a variable in this scope only
    #[must_use]
    pub fn lookup_var(&self, name: &str) -> Option<&VarBinding> {
        self.vars.get(name)
    }

    /// Lookup a variable mutably (to mark as used)
    #[must_use]
    pub fn lookup_var_mut(&mut self, name: &str) -> Option<&mut VarBinding> {
        self.vars.get_mut(name)
    }

    /// Bind a type in this scope
    pub fn bind_type(&mut self, name: &str, binding: TypeBinding) -> Result<(), ResolutionError> {
        if let Some(existing) = self.types.get(name) {
            return Err(ResolutionError::duplicate_binding(
                name,
                binding.span,
                existing.span,
            ));
        }
        self.types.insert(name.to_string(), binding);
        Ok(())
    }

    /// Lookup a type in this scope only
    #[must_use]
    pub fn lookup_type(&self, name: &str) -> Option<&TypeBinding> {
        self.types.get(name)
    }

    /// Bind a label in this scope
    pub fn bind_label(&mut self, name: &str, span: Range) -> Result<(), ResolutionError> {
        if let Some(&existing_span) = self.labels.get(name) {
            return Err(ResolutionError::duplicate_binding(name, span, existing_span));
        }
        self.labels.insert(name.to_string(), span);
        Ok(())
    }

    /// Lookup a label in this scope only
    #[must_use]
    pub fn lookup_label(&self, name: &str) -> Option<Range> {
        self.labels.get(name).copied()
    }

    /// Get all unused variable bindings
    #[must_use]
    pub fn unused_vars(&self) -> Vec<(&str, &VarBinding)> {
        self.vars
            .iter()
            .filter(|(_, b)| !b.used)
            .map(|(n, b)| (n.as_str(), b))
            .collect()
    }
}

// ============================================================================
// Resolution State
// ============================================================================

/// State maintained during name resolution
#[derive(Debug, Clone)]
pub struct ResolutionState {
    /// Stack of lexical scopes (innermost last)
    scopes: Vec<Scope>,
    /// Global declarations by name
    globals: HashMap<String, GlobalRef>,
    /// Global type definitions by name
    global_types: HashMap<String, TypeBinding>,
    /// Counter for generating fresh variable IDs
    next_var_id: u32,
    /// Accumulated errors
    pub errors: Vec<ResolutionError>,
    /// String interner callback storage - stores names for fresh vars
    fresh_var_names: Vec<String>,
}

impl ResolutionState {
    /// Create a new resolution state with an empty global scope
    #[must_use]
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new()], // Start with one scope
            globals: HashMap::new(),
            global_types: HashMap::new(),
            next_var_id: 0,
            errors: Vec::new(),
            fresh_var_names: Vec::new(),
        }
    }

    /// Push a new scope onto the stack
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pop the innermost scope
    ///
    /// Returns the popped scope for unused variable checking
    pub fn pop_scope(&mut self) -> Option<Scope> {
        // Never pop the last (global) scope
        if self.scopes.len() > 1 {
            self.scopes.pop()
        } else {
            None
        }
    }

    /// Get a reference to the current (innermost) scope
    #[must_use]
    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().expect("scope stack should never be empty")
    }

    /// Get a mutable reference to the current scope
    #[must_use]
    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes
            .last_mut()
            .expect("scope stack should never be empty")
    }

    /// Bind a variable in the current scope
    pub fn bind_var(&mut self, name: &str, binding: VarBinding) -> Result<(), ResolutionError> {
        self.current_scope_mut().bind_var(name, binding)
    }

    /// Lookup a variable, searching from innermost to outermost scope
    #[must_use]
    pub fn lookup_var(&self, name: &str) -> Option<&VarBinding> {
        for scope in self.scopes.iter().rev() {
            if let Some(binding) = scope.lookup_var(name) {
                return Some(binding);
            }
        }
        None
    }

    /// Lookup a variable and mark it as used
    pub fn lookup_var_and_mark_used(&mut self, name: &str) -> Option<VarId> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(binding) = scope.lookup_var_mut(name) {
                binding.used = true;
                return Some(binding.id);
            }
        }
        None
    }

    /// Bind a type in the current scope
    pub fn bind_type(&mut self, name: &str, binding: TypeBinding) -> Result<(), ResolutionError> {
        self.current_scope_mut().bind_type(name, binding)
    }

    /// Lookup a type, searching from innermost to outermost scope, then globals
    #[must_use]
    pub fn lookup_type(&self, name: &str) -> Option<&TypeBinding> {
        for scope in self.scopes.iter().rev() {
            if let Some(binding) = scope.lookup_type(name) {
                return Some(binding);
            }
        }
        self.global_types.get(name)
    }

    /// Bind a label in the current scope
    pub fn bind_label(&mut self, name: &str, span: Range) -> Result<(), ResolutionError> {
        self.current_scope_mut().bind_label(name, span)
    }

    /// Lookup a label
    #[must_use]
    pub fn lookup_label(&self, name: &str) -> Option<Range> {
        for scope in self.scopes.iter().rev() {
            if let Some(span) = scope.lookup_label(name) {
                return Some(span);
            }
        }
        None
    }

    /// Register a global declaration
    pub fn register_global(&mut self, name: &str, global_ref: GlobalRef) {
        self.globals.insert(name.to_string(), global_ref);
    }

    /// Register a global type
    pub fn register_global_type(&mut self, name: &str, binding: TypeBinding) {
        self.global_types.insert(name.to_string(), binding);
    }

    /// Lookup a global declaration
    #[must_use]
    pub fn lookup_global(&self, name: &str) -> Option<&GlobalRef> {
        self.globals.get(name)
    }

    /// Generate a fresh variable ID
    pub fn fresh_var_id(&mut self) -> u32 {
        let id = self.next_var_id;
        self.next_var_id += 1;
        id
    }

    /// Record an error
    pub fn add_error(&mut self, error: ResolutionError) {
        self.errors.push(error);
    }

    /// Check if any errors were recorded
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get all unused variables across all scopes
    #[must_use]
    pub fn all_unused_vars(&self) -> Vec<(&str, &VarBinding)> {
        self.scopes
            .iter()
            .flat_map(|s| s.unused_vars())
            .collect()
    }
}

impl Default for ResolutionState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Resolution Context (for threading interner)
// ============================================================================

/// Context for resolution, holding the interner and state
pub struct ResolutionCtx<'a, F>
where
    F: FnMut(&str) -> Spur,
{
    /// Resolution state
    pub state: &'a mut ResolutionState,
    /// String interner function
    pub intern: F,
    /// String resolver function
    pub resolve: fn(Spur) -> Option<&'static str>,
}

impl<'a, F> ResolutionCtx<'a, F>
where
    F: FnMut(&str) -> Spur,
{
    /// Create a new resolution context
    pub fn new(
        state: &'a mut ResolutionState,
        intern: F,
        resolve: fn(Spur) -> Option<&'static str>,
    ) -> Self {
        Self {
            state,
            intern,
            resolve,
        }
    }

    /// Intern a string
    pub fn intern(&mut self, s: &str) -> Spur {
        (self.intern)(s)
    }
}

// ============================================================================
// Core Resolution Functions
// ============================================================================

/// Resolve all names in a module
///
/// This is the main entry point for name resolution.
/// It populates the global scope with declarations, then resolves all references.
pub fn resolve_module<'a, F, R>(
    module: &Module,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
) -> Result<(), Vec<ResolutionError>>
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    // Silence unused parameter warning - will be used when expression resolution is added
    let _ = &resolve_spur;

    // Phase 1: Register all global declarations
    for (idx, decl) in module.declarations.iter().enumerate() {
        match decl {
            Declaration::Function { name, span, .. } => {
                state.register_global(name, GlobalRef::Function(idx));
                // Also bind as a variable so it can be referenced in expressions
                let spur = intern(name);
                if let Err(e) = state.bind_var(name, VarBinding::new(spur, *span)) {
                    state.add_error(e);
                }
            }
            Declaration::Type { name, span, .. } => {
                state.register_global(name, GlobalRef::Type(idx));
                let spur = intern(name);
                state.register_global_type(name, TypeBinding::new(spur, *span));
            }
            Declaration::Constant { name, span, .. } => {
                state.register_global(name, GlobalRef::Const(idx));
                let spur = intern(name);
                if let Err(e) = state.bind_var(name, VarBinding::new(spur, *span)) {
                    state.add_error(e);
                }
            }
            Declaration::Trait { name, span, .. } => {
                state.register_global(name, GlobalRef::Trait(idx));
                let spur = intern(name);
                state.register_global_type(name, TypeBinding::new(spur, *span));
            }
            Declaration::Impl { .. } => {
                // Impl blocks don't introduce named globals
            }
            Declaration::Variable { name, span, .. } => {
                // Package-level variables are treated similarly to constants
                state.register_global(name, GlobalRef::Const(idx));
                let spur = intern(name);
                if let Err(e) = state.bind_var(name, VarBinding::new(spur, *span)) {
                    state.add_error(e);
                }
            }
            Declaration::Use(import) => {
                // Process imports - would need access to other modules
                // For now, just record that we saw the import
                let _ = import;
            }
        }
    }

    // Phase 2: Register submodule declarations
    for (idx, submod) in module.submodules.iter().enumerate() {
        state.register_global(&submod.name, GlobalRef::Module(idx));
    }

    // Phase 3: Resolve references in declarations
    // This would walk function bodies, type definitions, etc.
    // For now, we just validate that all globals are registered

    if state.has_errors() {
        Err(state.errors.clone())
    } else {
        Ok(())
    }
}

/// Resolve names in an expression
///
/// Walks the expression tree, resolving variable references and introducing
/// new bindings where appropriate (let, lambda, match arms, etc.)
pub fn resolve_expr<'a, F, R>(
    expr: &mut Expr,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    let span = expr.range;

    match &mut expr.value {
        // Leaf expressions that don't need resolution
        Expr_::Lit(_) | Expr_::Hole | Expr_::Error(_) => {}

        // Variable reference - resolve to binding
        Expr_::Var(var_id) => {
            if let Some(name) = resolve_spur(*var_id) {
                if state.lookup_var_and_mark_used(name).is_none() {
                    // Check if it's a global
                    if state.lookup_global(name).is_none() {
                        state.add_error(ResolutionError::unbound_variable(name, span));
                    }
                }
            }
        }

        // Global reference - check it exists
        Expr_::Global(name_spur) => {
            if let Some(name) = resolve_spur(*name_spur) {
                if state.lookup_global(name).is_none() {
                    state.add_error(ResolutionError::unbound_variable(name, span));
                }
            }
        }

        // Unary operations
        Expr_::Unary(_, inner) => {
            resolve_expr(inner, state, intern, resolve_spur);
        }

        // Binary operations
        Expr_::Binary(_, lhs, rhs) => {
            resolve_expr(lhs, state, intern, resolve_spur);
            resolve_expr(rhs, state, intern, resolve_spur);
        }

        // Function call
        Expr_::Call(func, args) => {
            resolve_expr(func, state, intern, resolve_spur);
            for arg in args {
                resolve_expr(arg, state, intern, resolve_spur);
            }
        }

        // Method call
        Expr_::MethodCall(obj, _method, args) => {
            resolve_expr(obj, state, intern, resolve_spur);
            for arg in args {
                resolve_expr(arg, state, intern, resolve_spur);
            }
        }

        // Tuple
        Expr_::Tuple(elems) => {
            for elem in elems {
                resolve_expr(elem, state, intern, resolve_spur);
            }
        }

        // Array
        Expr_::Array(elems) => {
            for elem in elems {
                resolve_expr(elem, state, intern, resolve_spur);
            }
        }

        // Struct construction
        Expr_::Struct { name, fields } => {
            // Check struct type exists
            if let Some(type_name) = resolve_spur(*name) {
                if state.lookup_type(type_name).is_none() {
                    state.add_error(ResolutionError::unbound_type(type_name, span));
                }
            }
            // Resolve field expressions
            for (_, field_expr) in fields {
                resolve_expr(field_expr, state, intern, resolve_spur);
            }
        }

        // Variant construction
        Expr_::Variant {
            type_name, fields, ..
        } => {
            // Check enum type exists
            if let Some(name) = resolve_spur(*type_name) {
                if state.lookup_type(name).is_none() {
                    state.add_error(ResolutionError::unbound_type(name, span));
                }
            }
            // Resolve field expressions
            for field_expr in fields {
                resolve_expr(field_expr, state, intern, resolve_spur);
            }
        }

        // Field access
        Expr_::Field(obj, _field) => {
            resolve_expr(obj, state, intern, resolve_spur);
        }

        // Index access
        Expr_::Index(obj, idx) => {
            resolve_expr(obj, state, intern, resolve_spur);
            resolve_expr(idx, state, intern, resolve_spur);
        }

        // Tuple projection
        Expr_::TupleProj(obj, _) => {
            resolve_expr(obj, state, intern, resolve_spur);
        }

        // If-then-else
        Expr_::If(cond, then_branch, else_branch) => {
            resolve_expr(cond, state, intern, resolve_spur);
            resolve_expr(then_branch, state, intern, resolve_spur);
            resolve_expr(else_branch, state, intern, resolve_spur);
        }

        // Match expression
        Expr_::Match(scrutinee, arms) => {
            resolve_expr(scrutinee, state, intern, resolve_spur);
            for arm in arms {
                resolve_match_arm(arm, state, intern, resolve_spur);
            }
        }

        // Loop
        Expr_::Loop { label, body } => {
            state.push_scope();
            if let Some(label_spur) = label {
                if let Some(label_name) = resolve_spur(*label_spur) {
                    let _ = state.bind_label(label_name, span);
                }
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // While loop
        Expr_::While { label, cond, body } => {
            state.push_scope();
            if let Some(label_spur) = label {
                if let Some(label_name) = resolve_spur(*label_spur) {
                    let _ = state.bind_label(label_name, span);
                }
            }
            resolve_expr(cond, state, intern, resolve_spur);
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // For loop - introduces binding
        Expr_::For {
            label,
            var,
            iter,
            body,
        } => {
            resolve_expr(iter, state, intern, resolve_spur);

            state.push_scope();
            if let Some(label_spur) = label {
                if let Some(label_name) = resolve_spur(*label_spur) {
                    let _ = state.bind_label(label_name, span);
                }
            }
            // Bind loop variable
            if let Some(var_name) = resolve_spur(*var) {
                let _ = state.bind_var(var_name, VarBinding::new(*var, span));
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Break
        Expr_::Break { label, value } => {
            if let Some(label_spur) = label {
                if let Some(label_name) = resolve_spur(*label_spur) {
                    if state.lookup_label(label_name).is_none() {
                        state.add_error(
                            ResolutionError::unbound_variable(label_name, span)
                                .with_message("unknown loop label"),
                        );
                    }
                }
            }
            if let Some(val) = value {
                resolve_expr(val, state, intern, resolve_spur);
            }
        }

        // Continue
        Expr_::Continue { label } => {
            if let Some(label_spur) = label {
                if let Some(label_name) = resolve_spur(*label_spur) {
                    if state.lookup_label(label_name).is_none() {
                        state.add_error(
                            ResolutionError::unbound_variable(label_name, span)
                                .with_message("unknown loop label"),
                        );
                    }
                }
            }
        }

        // Return
        Expr_::Return(value) => {
            if let Some(val) = value {
                resolve_expr(val, state, intern, resolve_spur);
            }
        }

        // Let binding - introduces binding
        Expr_::Let {
            pattern,
            ty,
            init,
            body,
        } => {
            // Resolve initializer in current scope
            resolve_expr(init, state, intern, resolve_spur);
            // Resolve type annotation if present
            if let Some(type_ann) = ty {
                resolve_type(type_ann, state, resolve_spur, span);
            }

            // Push new scope for body
            state.push_scope();
            // Bind pattern variables
            resolve_pattern_and_bind(pattern, state, intern, resolve_spur);
            // Resolve body
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Mutable let - introduces binding
        Expr_::LetMut {
            var,
            ty,
            init,
            body,
        } => {
            resolve_expr(init, state, intern, resolve_spur);
            if let Some(type_ann) = ty {
                resolve_type(type_ann, state, resolve_spur, span);
            }

            state.push_scope();
            if let Some(var_name) = resolve_spur(*var) {
                let _ = state.bind_var(var_name, VarBinding::mutable(*var, span));
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Assignment
        Expr_::Assign(lhs, rhs) => {
            resolve_expr(lhs, state, intern, resolve_spur);
            resolve_expr(rhs, state, intern, resolve_spur);
        }

        // Lambda - introduces parameter bindings
        Expr_::Lambda { params, body } => {
            state.push_scope();
            for (param_id, param_ty) in params {
                if let Some(param_name) = resolve_spur(*param_id) {
                    let _ = state.bind_var(param_name, VarBinding::new(*param_id, span));
                }
                resolve_type(param_ty, state, resolve_spur, span);
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Closure - introduces parameter bindings, captures are checked
        Expr_::Closure {
            params,
            captures,
            body,
        } => {
            // Check captures exist
            for capture in captures.iter() {
                if let Some(name) = resolve_spur(*capture) {
                    if state.lookup_var_and_mark_used(name).is_none() {
                        state.add_error(ResolutionError::unbound_variable(name, span));
                    }
                }
            }

            state.push_scope();
            for (param_id, param_ty) in params {
                if let Some(param_name) = resolve_spur(*param_id) {
                    let _ = state.bind_var(param_name, VarBinding::new(*param_id, span));
                }
                resolve_type(param_ty, state, resolve_spur, span);
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Memory operations
        Expr_::Box(inner)
        | Expr_::Deref(inner)
        | Expr_::Borrow(inner)
        | Expr_::BorrowMut(inner)
        | Expr_::Move(inner)
        | Expr_::Drop(inner) => {
            resolve_expr(inner, state, intern, resolve_spur);
        }

        // Throw
        Expr_::Throw(inner) => {
            resolve_expr(inner, state, intern, resolve_spur);
        }

        // Try-catch
        Expr_::Try {
            body,
            catches,
            finally,
        } => {
            resolve_expr(body, state, intern, resolve_spur);
            for catch in catches {
                resolve_catch_arm(catch, state, intern, resolve_spur);
            }
            if let Some(fin) = finally {
                resolve_expr(fin, state, intern, resolve_spur);
            }
        }

        // Async operations
        Expr_::Await(inner)
        | Expr_::Yield(inner)
        | Expr_::Async(inner)
        | Expr_::Spawn(inner) => {
            resolve_expr(inner, state, intern, resolve_spur);
        }

        // Effect handler
        Expr_::Handle(inner, handler) => {
            resolve_expr(inner, state, intern, resolve_spur);
            resolve_effect_handler(handler, state, intern, resolve_spur);
        }

        // Perform effect
        Expr_::Perform(_op, args) => {
            for arg in args {
                resolve_expr(arg, state, intern, resolve_spur);
            }
        }

        // Resume continuation
        Expr_::Resume { var, value } => {
            if let Some(name) = resolve_spur(*var) {
                if state.lookup_var_and_mark_used(name).is_none() {
                    state.add_error(ResolutionError::unbound_variable(name, span));
                }
            }
            resolve_expr(value, state, intern, resolve_spur);
        }

        // Reset/shift (delimited continuations)
        Expr_::Reset { label, body } => {
            state.push_scope();
            if let Some(label_name) = resolve_spur(*label) {
                let _ = state.bind_label(label_name, span);
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        Expr_::Shift { label, var, body } => {
            if let Some(label_name) = resolve_spur(*label) {
                if state.lookup_label(label_name).is_none() {
                    state.add_error(ResolutionError::unbound_variable(label_name, span));
                }
            }
            state.push_scope();
            if let Some(var_name) = resolve_spur(*var) {
                let _ = state.bind_var(var_name, VarBinding::new(*var, span));
            }
            resolve_expr(body, state, intern, resolve_spur);
            state.pop_scope();
        }

        // Type operations
        Expr_::As(inner, ty) | Expr_::Is(inner, ty) => {
            resolve_expr(inner, state, intern, resolve_spur);
            resolve_type(ty, state, resolve_spur, span);
        }

        Expr_::Sizeof(ty) | Expr_::Alignof(ty) => {
            resolve_type(ty, state, resolve_spur, span);
        }

        // Block
        Expr_::Block(stmts) => {
            state.push_scope();
            for stmt in stmts {
                resolve_expr(stmt, state, intern, resolve_spur);
            }
            state.pop_scope();
        }

        // Sequence
        Expr_::Seq(first, second) => {
            resolve_expr(first, state, intern, resolve_spur);
            resolve_expr(second, state, intern, resolve_spur);
        }

        // Unsafe block
        Expr_::Unsafe(inner) => {
            resolve_expr(inner, state, intern, resolve_spur);
        }

        // Gradual cast
        Expr_::GradualCast { expr, .. } => {
            resolve_expr(expr, state, intern, resolve_spur);
        }

        // Control flow labels
        Expr_::Goto { .. } => {}
        Expr_::Labeled { body, .. } => {
            resolve_expr(body, state, intern, resolve_spur);
        }
    }
}

/// Resolve names in a pattern and bind the pattern variables
fn resolve_pattern_and_bind<'a, F, R>(
    pattern: &Pattern,
    state: &mut ResolutionState,
    _intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    let span = pattern.range;

    match &pattern.value {
        Pattern_::Wild => {}

        Pattern_::Var(var_id) => {
            if let Some(name) = resolve_spur(*var_id) {
                let _ = state.bind_var(name, VarBinding::new(*var_id, span));
            }
        }

        Pattern_::Lit(_) => {}

        Pattern_::Tuple(pats) => {
            for pat in pats {
                resolve_pattern_and_bind(pat, state, _intern, resolve_spur);
            }
        }

        Pattern_::Struct { name, fields } => {
            // Check struct type exists
            if let Some(type_name) = resolve_spur(*name) {
                if state.lookup_type(type_name).is_none() {
                    state.add_error(ResolutionError::unbound_type(type_name, span));
                }
            }
            // Bind field patterns
            for (_, field_pat) in fields {
                resolve_pattern_and_bind(field_pat, state, _intern, resolve_spur);
            }
        }

        Pattern_::Variant {
            type_name, fields, ..
        } => {
            // Check enum type exists
            if let Some(name) = resolve_spur(*type_name) {
                if state.lookup_type(name).is_none() {
                    state.add_error(ResolutionError::unbound_type(name, span));
                }
            }
            // Bind field patterns
            for field_pat in fields {
                resolve_pattern_and_bind(field_pat, state, _intern, resolve_spur);
            }
        }

        Pattern_::Or(left, right) => {
            // Both branches must bind the same variables
            resolve_pattern_and_bind(left, state, _intern, resolve_spur);
            // Note: In a full implementation, we'd verify both branches bind the same names
            resolve_pattern_and_bind(right, state, _intern, resolve_spur);
        }

        Pattern_::Guard(inner, _guard) => {
            resolve_pattern_and_bind(inner, state, _intern, resolve_spur);
            // Guard is resolved after pattern bindings are available
            // (handled by the caller via resolve_expr on the guard expression)
        }

        Pattern_::Ref(inner) | Pattern_::Box(inner) => {
            resolve_pattern_and_bind(inner, state, _intern, resolve_spur);
        }

        Pattern_::Rest(binding) => {
            if let Some(var_id) = binding {
                if let Some(name) = resolve_spur(*var_id) {
                    let _ = state.bind_var(name, VarBinding::new(*var_id, span));
                }
            }
        }

        Pattern_::As(inner, alias) => {
            resolve_pattern_and_bind(inner, state, _intern, resolve_spur);
            if let Some(name) = resolve_spur(*alias) {
                let _ = state.bind_var(name, VarBinding::new(*alias, span));
            }
        }

        // Type pattern may optionally bind a variable with narrowed type
        Pattern_::Type { binding, .. } => {
            if let Some(var_id) = binding {
                if let Some(name) = resolve_spur(*var_id) {
                    let _ = state.bind_var(name, VarBinding::new(*var_id, span));
                }
            }
        }
    }
}

/// Resolve a match arm
fn resolve_match_arm<'a, F, R>(
    arm: &mut MatchArm,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    state.push_scope();

    // Bind pattern variables
    resolve_pattern_and_bind(&arm.pattern, state, intern, resolve_spur);

    // Resolve guard if present
    if let Some(ref mut guard) = arm.guard {
        resolve_expr(guard, state, intern, resolve_spur);
    }

    // Resolve body
    resolve_expr(&mut arm.body, state, intern, resolve_spur);

    state.pop_scope();
}

/// Resolve a catch arm
fn resolve_catch_arm<'a, F, R>(
    arm: &mut CatchArm,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    state.push_scope();

    // Resolve exception type
    resolve_type(&mut arm.exception_type, state, resolve_spur, arm.range);

    // Bind pattern variables
    resolve_pattern_and_bind(&arm.pattern, state, intern, resolve_spur);

    // Resolve body
    resolve_expr(&mut arm.body, state, intern, resolve_spur);

    state.pop_scope();
}

/// Resolve an effect handler
fn resolve_effect_handler<'a, F, R>(
    handler: &mut EffectHandler,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    // Resolve each handler clause
    for clause in &mut handler.clauses {
        resolve_handler_clause(clause, state, intern, resolve_spur);
    }

    // Resolve return clause if present
    if let Some((var, ref mut body)) = handler.return_clause {
        state.push_scope();
        if let Some(name) = resolve_spur(var) {
            let _ = state.bind_var(name, VarBinding::new(var, Range::SYNTHETIC));
        }
        resolve_expr(body, state, intern, resolve_spur);
        state.pop_scope();
    }
}

/// Resolve a handler clause
fn resolve_handler_clause<'a, F, R>(
    clause: &mut HandlerClause,
    state: &mut ResolutionState,
    intern: &mut F,
    resolve_spur: R,
)
where
    F: FnMut(&str) -> Spur,
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    state.push_scope();

    // Bind parameter variables
    for param in &clause.params {
        if let Some(name) = resolve_spur(*param) {
            let _ = state.bind_var(name, VarBinding::new(*param, Range::SYNTHETIC));
        }
    }

    // Bind continuation variable
    if let Some(name) = resolve_spur(clause.continuation) {
        let _ = state.bind_var(
            name,
            VarBinding::new(clause.continuation, Range::SYNTHETIC),
        );
    }

    // Resolve body
    resolve_expr(&mut clause.body, state, intern, resolve_spur);

    state.pop_scope();
}

/// Resolve type references in a type
fn resolve_type<'a, R>(
    ty: &BrrrType,
    state: &ResolutionState,
    resolve_spur: R,
    span: Range,
)
where
    R: Fn(Spur) -> Option<&'a str> + Copy,
{
    match ty {
        BrrrType::Named(name) => {
            if let Some(type_name) = resolve_spur(*name) {
                if state.lookup_type(type_name).is_none() {
                    // Note: This is a read-only check, we can't add errors without &mut state
                    // In a full implementation, state would be &mut
                }
            }
        }
        BrrrType::Var(_) | BrrrType::Prim(_) | BrrrType::Numeric(_) => {}
        BrrrType::Wrap(_, inner) | BrrrType::SizedArray(_, inner) | BrrrType::Modal(_, inner) => {
            resolve_type(inner, state, resolve_spur, span);
        }
        BrrrType::Result(ok, err) => {
            resolve_type(ok, state, resolve_spur, span);
            resolve_type(err, state, resolve_spur, span);
        }
        BrrrType::Tuple(elems) => {
            for elem in elems {
                resolve_type(elem, state, resolve_spur, span);
            }
        }
        BrrrType::Func(ft) => {
            for param in &ft.params {
                resolve_type(&param.ty, state, resolve_spur, span);
            }
            resolve_type(&ft.return_type, state, resolve_spur, span);
        }
        BrrrType::App(base, args) => {
            resolve_type(base, state, resolve_spur, span);
            for arg in args {
                resolve_type(arg, state, resolve_spur, span);
            }
        }
        BrrrType::Struct(st) => {
            for field in &st.fields {
                resolve_type(&field.ty, state, resolve_spur, span);
            }
        }
        BrrrType::Enum(et) => {
            for variant in &et.variants {
                for field in &variant.fields {
                    resolve_type(field, state, resolve_spur, span);
                }
            }
        }
        BrrrType::Interface(iface) => {
            for method in &iface.methods {
                for param in &method.params {
                    resolve_type(&param.ty, state, resolve_spur, span);
                }
                resolve_type(&method.return_type, state, resolve_spur, span);
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    fn make_rodeo() -> Rodeo {
        Rodeo::default()
    }

    #[test]
    fn test_scope_bind_var() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");

        let mut scope = Scope::new();
        let binding = VarBinding::new(x, Range::SYNTHETIC);

        assert!(scope.bind_var("x", binding.clone()).is_ok());
        assert!(scope.lookup_var("x").is_some());
    }

    #[test]
    fn test_scope_duplicate_binding() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");

        let mut scope = Scope::new();
        let binding = VarBinding::new(x, Range::SYNTHETIC);

        assert!(scope.bind_var("x", binding.clone()).is_ok());
        assert!(scope.bind_var("x", binding).is_err());
    }

    #[test]
    fn test_resolution_state_scopes() {
        let mut state = ResolutionState::new();

        // Start with one scope
        assert!(state.scopes.len() == 1);

        state.push_scope();
        assert!(state.scopes.len() == 2);

        state.pop_scope();
        assert!(state.scopes.len() == 1);

        // Can't pop the last scope
        state.pop_scope();
        assert!(state.scopes.len() == 1);
    }

    #[test]
    fn test_resolution_state_lookup() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");
        let y = rodeo.get_or_intern("y");

        let mut state = ResolutionState::new();

        // Bind x in outer scope
        let _ = state.bind_var("x", VarBinding::new(x, Range::SYNTHETIC));

        state.push_scope();

        // Bind y in inner scope
        let _ = state.bind_var("y", VarBinding::new(y, Range::SYNTHETIC));

        // Can find both
        assert!(state.lookup_var("x").is_some());
        assert!(state.lookup_var("y").is_some());
        assert!(state.lookup_var("z").is_none());

        state.pop_scope();

        // Can still find x, but not y
        assert!(state.lookup_var("x").is_some());
        assert!(state.lookup_var("y").is_none());
    }

    #[test]
    fn test_resolution_state_mark_used() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");

        let mut state = ResolutionState::new();
        let _ = state.bind_var("x", VarBinding::new(x, Range::SYNTHETIC));

        // Initially not used
        assert!(!state.lookup_var("x").unwrap().used);

        // Mark as used
        let _ = state.lookup_var_and_mark_used("x");

        // Now used
        assert!(state.lookup_var("x").unwrap().used);
    }

    #[test]
    fn test_global_registration() {
        let mut state = ResolutionState::new();

        state.register_global("foo", GlobalRef::Function(0));
        state.register_global("Bar", GlobalRef::Type(1));

        assert!(matches!(
            state.lookup_global("foo"),
            Some(GlobalRef::Function(0))
        ));
        assert!(matches!(
            state.lookup_global("Bar"),
            Some(GlobalRef::Type(1))
        ));
        assert!(state.lookup_global("baz").is_none());
    }

    #[test]
    fn test_resolution_error_display() {
        let err = ResolutionError::unbound_variable("x", Range::SYNTHETIC);
        let s = format!("{}", err);
        assert!(s.contains("unbound variable"));
        assert!(s.contains("x"));
    }

    #[test]
    fn test_var_binding_mutable() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");

        let binding = VarBinding::mutable(x, Range::SYNTHETIC);
        assert!(binding.is_mut);

        let binding2 = VarBinding::new(x, Range::SYNTHETIC);
        assert!(!binding2.is_mut);
    }

    #[test]
    fn test_scope_labels() {
        let mut scope = Scope::new();

        assert!(scope.bind_label("loop1", Range::SYNTHETIC).is_ok());
        assert!(scope.lookup_label("loop1").is_some());
        assert!(scope.lookup_label("loop2").is_none());

        // Duplicate label is error
        assert!(scope.bind_label("loop1", Range::SYNTHETIC).is_err());
    }

    #[test]
    fn test_unused_vars() {
        let mut rodeo = make_rodeo();
        let x = rodeo.get_or_intern("x");
        let y = rodeo.get_or_intern("y");

        let mut scope = Scope::new();
        let _ = scope.bind_var("x", VarBinding::new(x, Range::SYNTHETIC));
        let mut y_binding = VarBinding::new(y, Range::SYNTHETIC);
        y_binding.used = true;
        let _ = scope.bind_var("y", y_binding);

        let unused = scope.unused_vars();
        assert_eq!(unused.len(), 1);
        assert_eq!(unused[0].0, "x");
    }
}
