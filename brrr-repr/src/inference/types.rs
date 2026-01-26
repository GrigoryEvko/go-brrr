//! Type inference types and data structures
//!
//! Standard Hindley-Milner type inference with bidirectional typing support.
//! Mirrors F* patterns for constraint generation and unification.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::expr::{Range, VarId};
use crate::types::{BrrrType, Kind, TypeName, TypeScheme, TypeVar};

// ============================================================================
// Type Constraints
// ============================================================================

/// Type constraint generated during inference.
///
/// These constraints are collected during the inference pass and solved
/// by the unification algorithm.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeConstraint {
    /// Type equality constraint: `T1 = T2`
    ///
    /// Generated when two types must be equal, e.g., in function application
    /// the argument type must equal the parameter type.
    Equal(BrrrType, BrrrType, Range),

    /// Subtype constraint: `T1 <: T2`
    ///
    /// Generated when one type must be a subtype of another, e.g., in
    /// assignments or coercions.
    Subtype(BrrrType, BrrrType, Range),

    /// Field access constraint: `T has field f: U`
    ///
    /// Generated when accessing a field on an expression. The type T
    /// must have a field named `f` with type U.
    HasField(BrrrType, String, BrrrType, Range),

    /// Instantiation constraint: `instantiate(scheme, args) = T`
    ///
    /// Generated when applying a polymorphic type to type arguments.
    Instantiate(TypeScheme, Vec<BrrrType>, BrrrType, Range),
}

impl TypeConstraint {
    /// Create an equality constraint
    #[must_use]
    pub fn equal(t1: BrrrType, t2: BrrrType, span: Range) -> Self {
        Self::Equal(t1, t2, span)
    }

    /// Create a subtype constraint
    #[must_use]
    pub fn subtype(sub: BrrrType, sup: BrrrType, span: Range) -> Self {
        Self::Subtype(sub, sup, span)
    }

    /// Create a field constraint
    #[must_use]
    pub fn has_field(base: BrrrType, field: impl Into<String>, ty: BrrrType, span: Range) -> Self {
        Self::HasField(base, field.into(), ty, span)
    }

    /// Create an instantiation constraint
    #[must_use]
    pub fn instantiate(
        scheme: TypeScheme,
        args: Vec<BrrrType>,
        result: BrrrType,
        span: Range,
    ) -> Self {
        Self::Instantiate(scheme, args, result, span)
    }

    /// Get the source range for error reporting
    #[must_use]
    pub const fn span(&self) -> Range {
        match self {
            Self::Equal(_, _, r)
            | Self::Subtype(_, _, r)
            | Self::HasField(_, _, _, r)
            | Self::Instantiate(_, _, _, r) => *r,
        }
    }
}

// ============================================================================
// Type Errors
// ============================================================================

/// Kind of type error that occurred during inference or checking.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeErrorKind {
    /// Type mismatch: expected one type, found another
    Mismatch,

    /// Infinite type detected during unification (occurs check failure)
    ///
    /// This happens when a type variable would need to unify with a type
    /// containing itself, e.g., `a = List<a>` where `a` is unconstrained.
    InfiniteType,

    /// Unbound variable reference
    UnboundVariable(VarId),

    /// Unbound type name reference
    UnboundType(TypeName),

    /// Function arity mismatch
    ArityMismatch {
        expected: usize,
        found: usize,
    },

    /// Expression is not a function but was called
    NotAFunction,

    /// Expression is not callable (variant of NotAFunction with more context)
    NotCallable,

    /// Field not found on struct/record type
    FieldNotFound(String),

    /// Kind mismatch during type application
    KindMismatch {
        expected: Kind,
        found: Kind,
    },

    /// Cannot infer type without annotation
    CannotInfer,

    /// Ambiguous type needs annotation
    AmbiguousType,

    /// Pattern type mismatch in match
    PatternMismatch,

    /// Duplicate binding in pattern
    DuplicateBinding(VarId),
}

impl TypeErrorKind {
    /// Get a human-readable name for this error kind
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Mismatch => "type mismatch",
            Self::InfiniteType => "infinite type",
            Self::UnboundVariable(_) => "unbound variable",
            Self::UnboundType(_) => "unbound type",
            Self::ArityMismatch { .. } => "arity mismatch",
            Self::NotAFunction => "not a function",
            Self::NotCallable => "not callable",
            Self::FieldNotFound(_) => "field not found",
            Self::KindMismatch { .. } => "kind mismatch",
            Self::CannotInfer => "cannot infer type",
            Self::AmbiguousType => "ambiguous type",
            Self::PatternMismatch => "pattern mismatch",
            Self::DuplicateBinding(_) => "duplicate binding",
        }
    }
}

/// Type error with source location and context.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeError {
    /// The kind of error
    pub kind: TypeErrorKind,

    /// Source location where the error occurred
    pub span: Range,

    /// Expected type (if applicable)
    pub expected: Option<BrrrType>,

    /// Found type (if applicable)
    pub found: Option<BrrrType>,

    /// Additional context message
    pub message: Option<String>,
}

impl TypeError {
    /// Create a new type error
    #[must_use]
    pub fn new(kind: TypeErrorKind, span: Range) -> Self {
        Self {
            kind,
            span,
            expected: None,
            found: None,
            message: None,
        }
    }

    /// Create a type mismatch error
    #[must_use]
    pub fn mismatch(expected: BrrrType, found: BrrrType, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::Mismatch,
            span,
            expected: Some(expected),
            found: Some(found),
            message: None,
        }
    }

    /// Create an infinite type error
    #[must_use]
    pub fn infinite_type(var: BrrrType, ty: BrrrType, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::InfiniteType,
            span,
            expected: Some(var),
            found: Some(ty),
            message: None,
        }
    }

    /// Create an unbound variable error
    #[must_use]
    pub fn unbound_variable(var: VarId, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::UnboundVariable(var),
            span,
            expected: None,
            found: None,
            message: None,
        }
    }

    /// Create an unbound type error
    #[must_use]
    pub fn unbound_type(name: TypeName, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::UnboundType(name),
            span,
            expected: None,
            found: None,
            message: None,
        }
    }

    /// Create an arity mismatch error
    #[must_use]
    pub fn arity_mismatch(expected: usize, found: usize, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::ArityMismatch { expected, found },
            span,
            expected: None,
            found: None,
            message: None,
        }
    }

    /// Create a not-a-function error
    #[must_use]
    pub fn not_a_function(found: BrrrType, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::NotAFunction,
            span,
            expected: None,
            found: Some(found),
            message: None,
        }
    }

    /// Create a field-not-found error
    #[must_use]
    pub fn field_not_found(field: impl Into<String>, ty: BrrrType, span: Range) -> Self {
        Self {
            kind: TypeErrorKind::FieldNotFound(field.into()),
            span,
            expected: None,
            found: Some(ty),
            message: None,
        }
    }

    /// Add a context message
    #[must_use]
    pub fn with_message(mut self, msg: impl Into<String>) -> Self {
        self.message = Some(msg.into());
        self
    }

    /// Format as a diagnostic message
    #[must_use]
    pub fn format(&self) -> String {
        let mut msg = format!("Error: {}", self.kind.name());

        if let Some(ref expected) = self.expected {
            msg.push_str(&format!("\n  expected: {:?}", expected));
        }
        if let Some(ref found) = self.found {
            msg.push_str(&format!("\n  found: {:?}", found));
        }
        if let Some(ref context) = self.message {
            msg.push_str(&format!("\n  note: {}", context));
        }

        msg
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format())
    }
}

impl std::error::Error for TypeError {}

// ============================================================================
// Inference State
// ============================================================================

/// State maintained during type inference.
///
/// This tracks generated constraints, fresh type variable counter,
/// the current substitution, and accumulated errors.
#[derive(Debug, Clone)]
pub struct InferenceState {
    /// Constraints generated during inference
    pub constraints: Vec<TypeConstraint>,

    /// Counter for generating fresh type variables
    pub type_var_counter: u32,

    /// Current substitution mapping type variables to types
    pub substitution: HashMap<TypeVar, BrrrType>,

    /// Accumulated type errors
    pub errors: Vec<TypeError>,
}

impl InferenceState {
    /// Create a new empty inference state
    #[must_use]
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            type_var_counter: 0,
            substitution: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// Generate a fresh type variable.
    ///
    /// Uses the interner closure to create a new interned name.
    pub fn fresh_type_var<F>(&mut self, intern: &mut F) -> TypeVar
    where
        F: FnMut(&str) -> TypeVar,
    {
        let id = self.type_var_counter;
        self.type_var_counter += 1;
        let name = format!("_t{}", id);
        intern(&name)
    }

    /// Generate a fresh type variable as a BrrrType.
    #[must_use]
    pub fn fresh_type<F>(&mut self, intern: &mut F) -> BrrrType
    where
        F: FnMut(&str) -> TypeVar,
    {
        BrrrType::Var(self.fresh_type_var(intern))
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: TypeConstraint) {
        self.constraints.push(constraint);
    }

    /// Add an equality constraint
    pub fn constrain_equal(&mut self, t1: BrrrType, t2: BrrrType, span: Range) {
        self.constraints.push(TypeConstraint::equal(t1, t2, span));
    }

    /// Add a subtype constraint
    pub fn constrain_subtype(&mut self, sub: BrrrType, sup: BrrrType, span: Range) {
        self.constraints.push(TypeConstraint::subtype(sub, sup, span));
    }

    /// Record a type error
    pub fn add_error(&mut self, error: TypeError) {
        self.errors.push(error);
    }

    /// Check if any errors have been recorded
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Apply the current substitution to a type
    #[must_use]
    pub fn apply(&self, ty: &BrrrType) -> BrrrType {
        apply_substitution(ty, &self.substitution)
    }

    /// Extend the substitution with a new mapping.
    ///
    /// Also applies the new mapping to all existing substitution values.
    pub fn extend_substitution(&mut self, var: TypeVar, ty: BrrrType) {
        // Apply the new binding to all existing substitution values
        let mut new_subst = HashMap::new();
        for (k, v) in &self.substitution {
            let updated = substitute_var(&ty, var, v);
            new_subst.insert(*k, updated);
        }
        new_subst.insert(var, ty);
        self.substitution = new_subst;
    }

    /// Clear all constraints (after solving)
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
    }
}

impl Default for InferenceState {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Type Context (Typing Environment)
// ============================================================================

/// Typing context mapping variables to their type schemes.
///
/// Supports scoped variable bindings through shadowing in the HashMap.
#[derive(Debug, Clone, Default)]
pub struct TypeCtx {
    /// Variable bindings: name -> type scheme
    pub vars: HashMap<VarId, TypeScheme>,

    /// Type definitions: name -> kind
    pub types: HashMap<TypeName, Kind>,
}

impl TypeCtx {
    /// Create an empty type context
    #[must_use]
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            types: HashMap::new(),
        }
    }

    /// Look up a variable's type scheme
    #[must_use]
    pub fn lookup(&self, var: &VarId) -> Option<&TypeScheme> {
        self.vars.get(var)
    }

    /// Look up a type's kind
    #[must_use]
    pub fn lookup_type(&self, name: &TypeName) -> Option<&Kind> {
        self.types.get(name)
    }

    /// Extend the context with a new variable binding
    pub fn extend(&mut self, var: VarId, scheme: TypeScheme) {
        self.vars.insert(var, scheme);
    }

    /// Extend the context with a monomorphic type
    pub fn extend_mono(&mut self, var: VarId, ty: BrrrType) {
        self.vars.insert(var, TypeScheme::mono(ty));
    }

    /// Extend the context with a type definition
    pub fn extend_type(&mut self, name: TypeName, kind: Kind) {
        self.types.insert(name, kind);
    }

    /// Create a child context (for entering a new scope)
    ///
    /// This clones the current context so modifications don't affect the parent.
    #[must_use]
    pub fn child(&self) -> Self {
        self.clone()
    }

    /// Get all free type variables in the context
    #[must_use]
    pub fn free_vars(&self) -> Vec<TypeVar> {
        let mut result = Vec::new();
        for scheme in self.vars.values() {
            // Only include free vars from the scheme body that aren't bound
            let body_vars = free_type_vars(&scheme.body);
            let bound: std::collections::HashSet<_> =
                scheme.type_vars.iter().map(|kv| kv.var).collect();
            for v in body_vars {
                if !bound.contains(&v) && !result.contains(&v) {
                    result.push(v);
                }
            }
        }
        result
    }
}

// ============================================================================
// Substitution Operations
// ============================================================================

/// Apply a substitution to a type, replacing type variables with their bindings.
#[must_use]
pub fn apply_substitution(ty: &BrrrType, subst: &HashMap<TypeVar, BrrrType>) -> BrrrType {
    match ty {
        BrrrType::Var(v) => {
            if let Some(replacement) = subst.get(v) {
                // Recursively apply substitution to the replacement
                apply_substitution(replacement, subst)
            } else {
                ty.clone()
            }
        }
        BrrrType::Prim(_) | BrrrType::Numeric(_) | BrrrType::Named(_) => ty.clone(),
        BrrrType::Wrap(kind, inner) => {
            BrrrType::Wrap(*kind, Box::new(apply_substitution(inner, subst)))
        }
        BrrrType::SizedArray(size, inner) => {
            BrrrType::SizedArray(*size, Box::new(apply_substitution(inner, subst)))
        }
        BrrrType::Modal(kind, inner) => {
            BrrrType::Modal(*kind, Box::new(apply_substitution(inner, subst)))
        }
        BrrrType::Result(ok, err) => BrrrType::Result(
            Box::new(apply_substitution(ok, subst)),
            Box::new(apply_substitution(err, subst)),
        ),
        BrrrType::Tuple(elems) => {
            BrrrType::Tuple(elems.iter().map(|e| apply_substitution(e, subst)).collect())
        }
        BrrrType::Func(ft) => {
            let params = ft
                .params
                .iter()
                .map(|p| crate::types::ParamType {
                    name: p.name,
                    ty: apply_substitution(&p.ty, subst),
                    mode: p.mode,
                })
                .collect();
            let return_type = apply_substitution(&ft.return_type, subst);
            BrrrType::Func(Box::new(crate::types::FuncType {
                params,
                return_type,
                effects: ft.effects.clone(),
                is_unsafe: ft.is_unsafe,
            }))
        }
        BrrrType::App(base, args) => BrrrType::App(
            Box::new(apply_substitution(base, subst)),
            args.iter().map(|a| apply_substitution(a, subst)).collect(),
        ),
        BrrrType::Struct(st) => {
            let fields = st
                .fields
                .iter()
                .map(|f| crate::types::FieldType {
                    name: f.name,
                    ty: apply_substitution(&f.ty, subst),
                    vis: f.vis,
                })
                .collect();
            BrrrType::Struct(crate::types::StructType {
                name: st.name,
                fields,
                repr: st.repr,
            })
        }
        BrrrType::Enum(et) => {
            let variants = et
                .variants
                .iter()
                .map(|v| crate::types::VariantType {
                    name: v.name,
                    fields: v.fields.iter().map(|f| apply_substitution(f, subst)).collect(),
                })
                .collect();
            BrrrType::Enum(crate::types::EnumType {
                name: et.name,
                variants,
            })
        }
        BrrrType::Interface(iface) => {
            let methods = iface
                .methods
                .iter()
                .map(|m| crate::types::MethodSig {
                    name: m.name,
                    params: m
                        .params
                        .iter()
                        .map(|p| crate::types::MethodParam {
                            name: p.name,
                            ty: apply_substitution(&p.ty, subst),
                        })
                        .collect(),
                    return_type: apply_substitution(&m.return_type, subst),
                })
                .collect();
            BrrrType::Interface(crate::types::InterfaceType {
                name: iface.name,
                methods,
                embedded: iface.embedded.clone(),
            })
        }
    }
}

/// Substitute a single type variable in a type
#[must_use]
fn substitute_var(replacement: &BrrrType, var: TypeVar, ty: &BrrrType) -> BrrrType {
    let mut single_subst = HashMap::new();
    single_subst.insert(var, replacement.clone());
    apply_substitution(ty, &single_subst)
}

/// Get all free type variables in a type
#[must_use]
pub fn free_type_vars(ty: &BrrrType) -> Vec<TypeVar> {
    let mut result = Vec::new();
    collect_free_vars(ty, &mut result);
    result
}

fn collect_free_vars(ty: &BrrrType, result: &mut Vec<TypeVar>) {
    match ty {
        BrrrType::Var(v) => {
            if !result.contains(v) {
                result.push(*v);
            }
        }
        BrrrType::Prim(_) | BrrrType::Numeric(_) | BrrrType::Named(_) => {}
        BrrrType::Wrap(_, inner) | BrrrType::SizedArray(_, inner) | BrrrType::Modal(_, inner) => {
            collect_free_vars(inner, result);
        }
        BrrrType::Result(ok, err) => {
            collect_free_vars(ok, result);
            collect_free_vars(err, result);
        }
        BrrrType::Tuple(elems) => {
            for e in elems {
                collect_free_vars(e, result);
            }
        }
        BrrrType::Func(ft) => {
            for p in &ft.params {
                collect_free_vars(&p.ty, result);
            }
            collect_free_vars(&ft.return_type, result);
        }
        BrrrType::App(base, args) => {
            collect_free_vars(base, result);
            for a in args {
                collect_free_vars(a, result);
            }
        }
        BrrrType::Struct(st) => {
            for f in &st.fields {
                collect_free_vars(&f.ty, result);
            }
        }
        BrrrType::Enum(et) => {
            for v in &et.variants {
                for f in &v.fields {
                    collect_free_vars(f, result);
                }
            }
        }
        BrrrType::Interface(iface) => {
            for m in &iface.methods {
                for p in &m.params {
                    collect_free_vars(&p.ty, result);
                }
                collect_free_vars(&m.return_type, result);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_inference_state_fresh_var() {
        let mut rodeo = Rodeo::default();
        let mut state = InferenceState::new();

        let v1 = state.fresh_type_var(&mut |s| rodeo.get_or_intern(s));
        let v2 = state.fresh_type_var(&mut |s| rodeo.get_or_intern(s));

        assert_ne!(v1, v2);
        assert_eq!(state.type_var_counter, 2);
    }

    #[test]
    fn test_apply_substitution_simple() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");

        let mut subst = HashMap::new();
        subst.insert(alpha, BrrrType::BOOL);

        let ty = BrrrType::Var(alpha);
        let result = apply_substitution(&ty, &subst);
        assert_eq!(result, BrrrType::BOOL);
    }

    #[test]
    fn test_apply_substitution_nested() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");

        let mut subst = HashMap::new();
        subst.insert(alpha, BrrrType::BOOL);

        let ty = BrrrType::option(BrrrType::Var(alpha));
        let result = apply_substitution(&ty, &subst);
        assert_eq!(result, BrrrType::option(BrrrType::BOOL));
    }

    #[test]
    fn test_free_type_vars() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");
        let beta = rodeo.get_or_intern("beta");

        let ty = BrrrType::result(BrrrType::Var(alpha), BrrrType::Var(beta));
        let vars = free_type_vars(&ty);

        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&alpha));
        assert!(vars.contains(&beta));
    }

    #[test]
    fn test_type_ctx_extend() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");

        let mut ctx = TypeCtx::new();
        ctx.extend_mono(x, BrrrType::BOOL);

        assert!(ctx.lookup(&x).is_some());
        assert_eq!(ctx.lookup(&x).unwrap().body, BrrrType::BOOL);
    }

    #[test]
    fn test_type_error_format() {
        let err = TypeError::mismatch(BrrrType::BOOL, BrrrType::STRING, Range::SYNTHETIC);
        let msg = err.format();

        assert!(msg.contains("type mismatch"));
        assert!(msg.contains("expected"));
        assert!(msg.contains("found"));
    }

    #[test]
    fn test_constraint_creation() {
        let c = TypeConstraint::equal(BrrrType::BOOL, BrrrType::STRING, Range::SYNTHETIC);
        assert_eq!(c.span(), Range::SYNTHETIC);

        let c2 = TypeConstraint::has_field(
            BrrrType::BOOL,
            "x",
            BrrrType::STRING,
            Range::SYNTHETIC,
        );
        if let TypeConstraint::HasField(_, field, _, _) = c2 {
            assert_eq!(field, "x");
        } else {
            panic!("Expected HasField constraint");
        }
    }
}
