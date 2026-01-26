//! Detailed declaration type definitions
//!
//! Provides comprehensive types for function definitions, type definitions,
//! traits, and impl blocks following the F* BrrrTypes.fsti patterns.
//!
//! # Declaration Types
//!
//! - `FunctionDef` - Full function definition with type params, contracts, effects
//! - `TypeDef` - Type aliases, newtypes, structs, and enums
//! - `TraitDef` - Trait definitions with methods and associated types
//! - `ImplBlock` - Inherent and trait implementations
//!
//! These types are more detailed than the simpler `Declaration` enum in `module.rs`,
//! providing full AST representation for semantic analysis and code generation.

use lasso::{Key, Spur};
use serde::{Deserialize, Serialize};

use crate::effects::EffectRow;
use crate::expr::{Expr, Range};
use crate::types::{
    BrrrType, EnumType, KindedVar, ParamType, StructType, TypeName, Visibility,
};
use crate::verification::Contract;

// Re-export VarId from expr for convenience
pub use crate::expr::VarId;

/// Function definition with full metadata
///
/// Maps to F* function declaration pattern:
/// ```fstar
/// val func_name : params -> return_type
/// let func_name params = body
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionDef {
    /// Function name (interned)
    pub name: VarId,
    /// Generic type parameters with kind annotations
    pub type_params: Vec<KindedVar>,
    /// Function parameters with types and modes
    pub params: Vec<ParamType>,
    /// Return type
    pub return_type: BrrrType,
    /// Effect row: effects this function may perform
    pub effects: EffectRow,
    /// Function body (None for extern/abstract functions)
    pub body: Option<Expr>,
    /// Pre/post condition contract (requires/ensures)
    pub contract: Option<Contract>,
    /// Visibility (pub, priv, mod)
    pub visibility: Visibility,
    /// Is this an unsafe function?
    pub is_unsafe: bool,
    /// Is this an async function?
    pub is_async: bool,
    /// Is this a const function?
    pub is_const: bool,
    /// Source location
    pub span: Range,
}

impl FunctionDef {
    /// Create a new function definition with minimal fields
    pub fn new(name: VarId, params: Vec<ParamType>, return_type: BrrrType) -> Self {
        Self {
            name,
            type_params: Vec::new(),
            params,
            return_type,
            effects: EffectRow::pure(),
            body: None,
            contract: None,
            visibility: Visibility::Public,
            is_unsafe: false,
            is_async: false,
            is_const: false,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a pure function with body
    pub fn with_body(name: VarId, params: Vec<ParamType>, return_type: BrrrType, body: Expr) -> Self {
        Self {
            name,
            type_params: Vec::new(),
            params,
            return_type,
            effects: EffectRow::pure(),
            body: Some(body),
            contract: None,
            visibility: Visibility::Public,
            is_unsafe: false,
            is_async: false,
            is_const: false,
            span: Range::SYNTHETIC,
        }
    }

    /// Create an extern function (no body)
    pub fn extern_fn(name: VarId, params: Vec<ParamType>, return_type: BrrrType) -> Self {
        Self::new(name, params, return_type)
    }

    /// Set type parameters
    pub fn with_type_params(mut self, type_params: Vec<KindedVar>) -> Self {
        self.type_params = type_params;
        self
    }

    /// Set effects
    pub fn with_effects(mut self, effects: EffectRow) -> Self {
        self.effects = effects;
        self
    }

    /// Set contract
    pub fn with_contract(mut self, contract: Contract) -> Self {
        self.contract = Some(contract);
        self
    }

    /// Set visibility
    pub fn with_visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }

    /// Mark as unsafe
    pub fn mark_unsafe(mut self) -> Self {
        self.is_unsafe = true;
        self
    }

    /// Mark as async
    pub fn mark_async(mut self) -> Self {
        self.is_async = true;
        self
    }

    /// Mark as const
    pub fn mark_const(mut self) -> Self {
        self.is_const = true;
        self
    }

    /// Set source span
    pub fn at(mut self, span: Range) -> Self {
        self.span = span;
        self
    }

    /// Check if function is pure (no effects)
    pub fn is_pure(&self) -> bool {
        self.effects.is_pure()
    }

    /// Check if function has a body (not extern)
    pub fn has_body(&self) -> bool {
        self.body.is_some()
    }

    /// Check if function has a contract
    pub fn has_contract(&self) -> bool {
        self.contract.is_some()
    }

    /// Get arity (number of parameters)
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

impl Default for FunctionDef {
    fn default() -> Self {
        // Use a sentinel value for the name
        Self {
            name: Spur::try_from_usize(0).expect("zero index should be valid"),
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: BrrrType::UNIT,
            effects: EffectRow::pure(),
            body: None,
            contract: None,
            visibility: Visibility::Public,
            is_unsafe: false,
            is_async: false,
            is_const: false,
            span: Range::SYNTHETIC,
        }
    }
}

/// Type definition variants
///
/// Maps to F* type declaration patterns:
/// ```fstar
/// type alias = target                    (* Alias *)
/// type newtype = | Wrap : inner -> t     (* Newtype *)
/// type struct = { fields... }            (* Struct *)
/// type enum = | Variant1 | Variant2      (* Enum *)
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeDef {
    /// Type alias: `type Alias<T> = Target<T>`
    Alias {
        name: TypeName,
        params: Vec<KindedVar>,
        target: BrrrType,
    },
    /// Newtype wrapper: `type Newtype<T> = Newtype(Inner<T>)`
    Newtype {
        name: TypeName,
        params: Vec<KindedVar>,
        inner: BrrrType,
    },
    /// Struct type definition
    Struct(StructType),
    /// Enum type definition
    Enum(EnumType),
}

impl TypeDef {
    /// Create a simple type alias (no params)
    pub fn alias(name: TypeName, target: BrrrType) -> Self {
        Self::Alias {
            name,
            params: Vec::new(),
            target,
        }
    }

    /// Create a generic type alias
    pub fn generic_alias(name: TypeName, params: Vec<KindedVar>, target: BrrrType) -> Self {
        Self::Alias { name, params, target }
    }

    /// Create a newtype wrapper
    pub fn newtype(name: TypeName, inner: BrrrType) -> Self {
        Self::Newtype {
            name,
            params: Vec::new(),
            inner,
        }
    }

    /// Create a generic newtype wrapper
    pub fn generic_newtype(name: TypeName, params: Vec<KindedVar>, inner: BrrrType) -> Self {
        Self::Newtype { name, params, inner }
    }

    /// Get the type name
    pub fn name(&self) -> TypeName {
        match self {
            Self::Alias { name, .. } => *name,
            Self::Newtype { name, .. } => *name,
            Self::Struct(s) => s.name,
            Self::Enum(e) => e.name,
        }
    }

    /// Get the type parameters
    pub fn type_params(&self) -> &[KindedVar] {
        match self {
            Self::Alias { params, .. } => params,
            Self::Newtype { params, .. } => params,
            Self::Struct(_) => &[], // StructType doesn't have params in current impl
            Self::Enum(_) => &[],   // EnumType doesn't have params in current impl
        }
    }

    /// Check if this is a struct
    pub const fn is_struct(&self) -> bool {
        matches!(self, Self::Struct(_))
    }

    /// Check if this is an enum
    pub const fn is_enum(&self) -> bool {
        matches!(self, Self::Enum(_))
    }

    /// Check if this is an alias
    pub const fn is_alias(&self) -> bool {
        matches!(self, Self::Alias { .. })
    }

    /// Check if this is a newtype
    pub const fn is_newtype(&self) -> bool {
        matches!(self, Self::Newtype { .. })
    }
}

/// Trait definition
///
/// Maps to F* typeclass pattern:
/// ```fstar
/// class TraitName (a: Type) = {
///   method1 : a -> a;
///   method2 : a -> b -> a;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitDef {
    /// Trait name
    pub name: TypeName,
    /// Type parameters (the Self type and additional params)
    pub type_params: Vec<KindedVar>,
    /// Super traits (traits this trait extends)
    pub super_traits: Vec<TypeName>,
    /// Method definitions
    pub methods: Vec<FunctionDef>,
    /// Associated type declarations
    pub assoc_types: Vec<AssocTypeDef>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: Range,
}

impl TraitDef {
    /// Create a new trait definition
    pub fn new(name: TypeName, type_params: Vec<KindedVar>) -> Self {
        Self {
            name,
            type_params,
            super_traits: Vec::new(),
            methods: Vec::new(),
            assoc_types: Vec::new(),
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Add a super trait
    pub fn with_super_trait(mut self, super_trait: TypeName) -> Self {
        self.super_traits.push(super_trait);
        self
    }

    /// Add super traits
    pub fn with_super_traits(mut self, super_traits: Vec<TypeName>) -> Self {
        self.super_traits = super_traits;
        self
    }

    /// Add a method
    pub fn with_method(mut self, method: FunctionDef) -> Self {
        self.methods.push(method);
        self
    }

    /// Add methods
    pub fn with_methods(mut self, methods: Vec<FunctionDef>) -> Self {
        self.methods = methods;
        self
    }

    /// Add an associated type
    pub fn with_assoc_type(mut self, assoc_type: AssocTypeDef) -> Self {
        self.assoc_types.push(assoc_type);
        self
    }

    /// Set visibility
    pub fn with_visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }

    /// Set source span
    pub fn at(mut self, span: Range) -> Self {
        self.span = span;
        self
    }

    /// Get method by name
    pub fn get_method(&self, name: VarId) -> Option<&FunctionDef> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Number of methods
    pub fn method_count(&self) -> usize {
        self.methods.len()
    }

    /// Check if trait has super traits
    pub fn has_super_traits(&self) -> bool {
        !self.super_traits.is_empty()
    }
}

impl Default for TraitDef {
    fn default() -> Self {
        Self {
            name: Spur::try_from_usize(0).expect("zero index should be valid"),
            type_params: Vec::new(),
            super_traits: Vec::new(),
            methods: Vec::new(),
            assoc_types: Vec::new(),
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }
}

/// Associated type definition within a trait
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AssocTypeDef {
    /// Associated type name
    pub name: TypeName,
    /// Type bounds (trait bounds on the associated type)
    pub bounds: Vec<TypeName>,
    /// Default type (if provided)
    pub default: Option<BrrrType>,
}

impl AssocTypeDef {
    /// Create a new associated type with no bounds or default
    pub fn new(name: TypeName) -> Self {
        Self {
            name,
            bounds: Vec::new(),
            default: None,
        }
    }

    /// Add bounds
    pub fn with_bounds(mut self, bounds: Vec<TypeName>) -> Self {
        self.bounds = bounds;
        self
    }

    /// Add default type
    pub fn with_default(mut self, default: BrrrType) -> Self {
        self.default = Some(default);
        self
    }
}

/// Impl block (inherent or trait implementation)
///
/// Maps to F* instance pattern:
/// ```fstar
/// instance TraitName Type : TraitName Type = {
///   method1 = ...;
///   method2 = ...;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ImplBlock {
    /// Generic type parameters for this impl
    pub type_params: Vec<KindedVar>,
    /// Trait being implemented (None for inherent impl)
    pub trait_ref: Option<TraitRef>,
    /// The type this impl is for
    pub self_type: BrrrType,
    /// Method implementations
    pub methods: Vec<FunctionDef>,
    /// Associated type bindings
    pub assoc_type_bindings: Vec<AssocTypeBinding>,
    /// Visibility
    pub visibility: Visibility,
    /// Source location
    pub span: Range,
}

impl ImplBlock {
    /// Create an inherent impl block (no trait)
    pub fn inherent(self_type: BrrrType) -> Self {
        Self {
            type_params: Vec::new(),
            trait_ref: None,
            self_type,
            methods: Vec::new(),
            assoc_type_bindings: Vec::new(),
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a trait impl block
    pub fn for_trait(trait_name: TypeName, self_type: BrrrType) -> Self {
        Self {
            type_params: Vec::new(),
            trait_ref: Some(TraitRef::simple(trait_name)),
            self_type,
            methods: Vec::new(),
            assoc_type_bindings: Vec::new(),
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a generic trait impl block
    pub fn for_trait_generic(
        trait_ref: TraitRef,
        self_type: BrrrType,
        type_params: Vec<KindedVar>,
    ) -> Self {
        Self {
            type_params,
            trait_ref: Some(trait_ref),
            self_type,
            methods: Vec::new(),
            assoc_type_bindings: Vec::new(),
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Add type parameters
    pub fn with_type_params(mut self, type_params: Vec<KindedVar>) -> Self {
        self.type_params = type_params;
        self
    }

    /// Add a method
    pub fn with_method(mut self, method: FunctionDef) -> Self {
        self.methods.push(method);
        self
    }

    /// Add methods
    pub fn with_methods(mut self, methods: Vec<FunctionDef>) -> Self {
        self.methods = methods;
        self
    }

    /// Add an associated type binding
    pub fn with_assoc_type_binding(mut self, binding: AssocTypeBinding) -> Self {
        self.assoc_type_bindings.push(binding);
        self
    }

    /// Set visibility
    pub fn with_visibility(mut self, visibility: Visibility) -> Self {
        self.visibility = visibility;
        self
    }

    /// Set source span
    pub fn at(mut self, span: Range) -> Self {
        self.span = span;
        self
    }

    /// Check if this is a trait impl
    pub fn is_trait_impl(&self) -> bool {
        self.trait_ref.is_some()
    }

    /// Check if this is an inherent impl
    pub fn is_inherent(&self) -> bool {
        self.trait_ref.is_none()
    }

    /// Get method by name
    pub fn get_method(&self, name: VarId) -> Option<&FunctionDef> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Number of methods
    pub fn method_count(&self) -> usize {
        self.methods.len()
    }
}

impl Default for ImplBlock {
    fn default() -> Self {
        Self::inherent(BrrrType::UNIT)
    }
}

/// Reference to a trait (possibly with type arguments)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TraitRef {
    /// Trait name
    pub name: TypeName,
    /// Type arguments for the trait
    pub type_args: Vec<BrrrType>,
}

impl TraitRef {
    /// Create a simple trait reference (no type args)
    pub fn simple(name: TypeName) -> Self {
        Self {
            name,
            type_args: Vec::new(),
        }
    }

    /// Create a trait reference with type arguments
    pub fn with_args(name: TypeName, type_args: Vec<BrrrType>) -> Self {
        Self { name, type_args }
    }
}

/// Associated type binding in an impl block
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AssocTypeBinding {
    /// Associated type name
    pub name: TypeName,
    /// Bound type
    pub ty: BrrrType,
}

impl AssocTypeBinding {
    /// Create a new associated type binding
    pub fn new(name: TypeName, ty: BrrrType) -> Self {
        Self { name, ty }
    }
}

/// Item within an extern block
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExternItem {
    /// Extern function: `fn name(params) -> ret;`
    Function(FunctionDef),
    /// Extern static: `static [mut] NAME: Type;`
    Static {
        name: VarId,
        ty: BrrrType,
        is_mut: bool,
    },
    /// Extern type: `type Name;`
    Type { name: TypeName },
}

impl ExternItem {
    /// Create an extern function
    pub fn function(def: FunctionDef) -> Self {
        Self::Function(def)
    }

    /// Create an extern static
    pub fn static_item(name: VarId, ty: BrrrType, is_mut: bool) -> Self {
        Self::Static { name, ty, is_mut }
    }

    /// Create an extern type
    pub fn type_item(name: TypeName) -> Self {
        Self::Type { name }
    }
}

/// Full declaration enum with detailed variants
///
/// This is the comprehensive declaration type for semantic analysis.
/// For simpler module-level tracking, see `module::Declaration`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum FullDeclaration {
    /// Function definition (includes methods, closures as top-level)
    Function(FunctionDef),

    /// Type definition (alias, newtype, struct, enum)
    Type(TypeDef),

    /// Trait definition
    Trait(TraitDef),

    /// Impl block (inherent or trait implementation)
    Impl(ImplBlock),

    /// Const item: `const NAME: Type = value;`
    Const {
        name: VarId,
        ty: BrrrType,
        value: Expr,
        visibility: Visibility,
        span: Range,
    },

    /// Static item: `static [mut] NAME: Type = value;`
    Static {
        name: VarId,
        ty: BrrrType,
        value: Option<Expr>,
        is_mut: bool,
        visibility: Visibility,
        span: Range,
    },

    /// Module declaration: `mod name { ... }` or `mod name;`
    Module {
        name: Spur,
        declarations: Vec<FullDeclaration>,
        visibility: Visibility,
        span: Range,
    },

    /// Use/import declaration: `use path::to::item;`
    Use {
        path: Vec<Spur>,
        alias: Option<Spur>,
        visibility: Visibility,
        span: Range,
    },

    /// Extern block: `extern "C" { ... }`
    Extern {
        abi: Option<Spur>,
        items: Vec<ExternItem>,
        span: Range,
    },
}

impl FullDeclaration {
    /// Create a function declaration
    pub fn function(def: FunctionDef) -> Self {
        Self::Function(def)
    }

    /// Create a type declaration
    pub fn type_def(def: TypeDef) -> Self {
        Self::Type(def)
    }

    /// Create a trait declaration
    pub fn trait_def(def: TraitDef) -> Self {
        Self::Trait(def)
    }

    /// Create an impl declaration
    pub fn impl_block(block: ImplBlock) -> Self {
        Self::Impl(block)
    }

    /// Create a const declaration
    pub fn const_item(name: VarId, ty: BrrrType, value: Expr) -> Self {
        Self::Const {
            name,
            ty,
            value,
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a static declaration
    pub fn static_item(name: VarId, ty: BrrrType, value: Option<Expr>, is_mut: bool) -> Self {
        Self::Static {
            name,
            ty,
            value,
            is_mut,
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a module declaration
    pub fn module(name: Spur, declarations: Vec<FullDeclaration>) -> Self {
        Self::Module {
            name,
            declarations,
            visibility: Visibility::Public,
            span: Range::SYNTHETIC,
        }
    }

    /// Create a use declaration
    pub fn use_item(path: Vec<Spur>, alias: Option<Spur>) -> Self {
        Self::Use {
            path,
            alias,
            visibility: Visibility::Private,
            span: Range::SYNTHETIC,
        }
    }

    /// Create an extern block
    pub fn extern_block(abi: Option<Spur>, items: Vec<ExternItem>) -> Self {
        Self::Extern {
            abi,
            items,
            span: Range::SYNTHETIC,
        }
    }

    /// Get the name of this declaration (if it has one)
    pub fn name(&self) -> Option<Spur> {
        match self {
            Self::Function(f) => Some(f.name),
            Self::Type(t) => Some(t.name()),
            Self::Trait(t) => Some(t.name),
            Self::Impl(_) => None, // Impl blocks don't have names
            Self::Const { name, .. } => Some(*name),
            Self::Static { name, .. } => Some(*name),
            Self::Module { name, .. } => Some(*name),
            Self::Use { .. } => None,
            Self::Extern { .. } => None,
        }
    }

    /// Get the visibility of this declaration
    pub fn visibility(&self) -> Visibility {
        match self {
            Self::Function(f) => f.visibility,
            Self::Type(TypeDef::Struct(_)) => Visibility::Public,
            Self::Type(TypeDef::Enum(_)) => Visibility::Public,
            Self::Type(TypeDef::Alias { .. }) => Visibility::Public,
            Self::Type(TypeDef::Newtype { .. }) => Visibility::Public,
            Self::Trait(t) => t.visibility,
            Self::Impl(i) => i.visibility,
            Self::Const { visibility, .. } => *visibility,
            Self::Static { visibility, .. } => *visibility,
            Self::Module { visibility, .. } => *visibility,
            Self::Use { visibility, .. } => *visibility,
            Self::Extern { .. } => Visibility::Public,
        }
    }

    /// Get the source span of this declaration
    pub fn span(&self) -> Range {
        match self {
            Self::Function(f) => f.span,
            Self::Type(_) => Range::SYNTHETIC,
            Self::Trait(t) => t.span,
            Self::Impl(i) => i.span,
            Self::Const { span, .. } => *span,
            Self::Static { span, .. } => *span,
            Self::Module { span, .. } => *span,
            Self::Use { span, .. } => *span,
            Self::Extern { span, .. } => *span,
        }
    }

    /// Check if this is a function declaration
    pub const fn is_function(&self) -> bool {
        matches!(self, Self::Function(_))
    }

    /// Check if this is a type declaration
    pub const fn is_type(&self) -> bool {
        matches!(self, Self::Type(_))
    }

    /// Check if this is a trait declaration
    pub const fn is_trait(&self) -> bool {
        matches!(self, Self::Trait(_))
    }

    /// Check if this is an impl declaration
    pub const fn is_impl(&self) -> bool {
        matches!(self, Self::Impl(_))
    }

    /// Check if this is a const declaration
    pub const fn is_const(&self) -> bool {
        matches!(self, Self::Const { .. })
    }

    /// Check if this is a static declaration
    pub const fn is_static(&self) -> bool {
        matches!(self, Self::Static { .. })
    }

    /// Check if this is a module declaration
    pub const fn is_module(&self) -> bool {
        matches!(self, Self::Module { .. })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    fn intern(rodeo: &mut Rodeo, s: &str) -> Spur {
        rodeo.get_or_intern(s)
    }

    #[test]
    fn test_function_def_basic() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "foo");

        let func = FunctionDef::new(name, vec![], BrrrType::UNIT);

        assert_eq!(func.name, name);
        assert!(func.params.is_empty());
        assert_eq!(func.return_type, BrrrType::UNIT);
        assert!(func.is_pure());
        assert!(!func.has_body());
        assert!(!func.is_unsafe);
    }

    #[test]
    fn test_function_def_with_body() {
        use crate::expr::{Expr_, Literal, WithLoc};

        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "add");
        let body = WithLoc::synthetic(Expr_::Lit(Literal::i32(42)));

        let func = FunctionDef::with_body(name, vec![], BrrrType::BOOL, body);

        assert!(func.has_body());
        assert!(!func.is_unsafe);
        assert!(!func.is_async);
    }

    #[test]
    fn test_function_def_modifiers() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "unsafe_async_fn");

        let func = FunctionDef::new(name, vec![], BrrrType::UNIT)
            .mark_unsafe()
            .mark_async()
            .with_visibility(Visibility::Private);

        assert!(func.is_unsafe);
        assert!(func.is_async);
        assert_eq!(func.visibility, Visibility::Private);
    }

    #[test]
    fn test_type_def_alias() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "MyInt");

        let alias = TypeDef::alias(name, BrrrType::Numeric(crate::types::NumericType::Int(
            crate::types::IntType::I32,
        )));

        assert!(alias.is_alias());
        assert!(!alias.is_struct());
        assert_eq!(alias.name(), name);
    }

    #[test]
    fn test_type_def_newtype() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "UserId");

        let newtype = TypeDef::newtype(name, BrrrType::STRING);

        assert!(newtype.is_newtype());
        assert_eq!(newtype.name(), name);
    }

    #[test]
    fn test_trait_def() {
        let mut rodeo = Rodeo::default();
        let trait_name = intern(&mut rodeo, "Display");
        let method_name = intern(&mut rodeo, "fmt");
        let t_var = intern(&mut rodeo, "T");

        let method = FunctionDef::new(method_name, vec![], BrrrType::STRING);

        let trait_def = TraitDef::new(trait_name, vec![KindedVar::of_type(t_var)])
            .with_method(method);

        assert_eq!(trait_def.name, trait_name);
        assert_eq!(trait_def.method_count(), 1);
        assert!(!trait_def.has_super_traits());
    }

    #[test]
    fn test_trait_def_with_supers() {
        let mut rodeo = Rodeo::default();
        let trait_name = intern(&mut rodeo, "PartialOrd");
        let super_trait = intern(&mut rodeo, "PartialEq");
        let t_var = intern(&mut rodeo, "T");

        let trait_def = TraitDef::new(trait_name, vec![KindedVar::of_type(t_var)])
            .with_super_trait(super_trait);

        assert!(trait_def.has_super_traits());
        assert_eq!(trait_def.super_traits.len(), 1);
    }

    #[test]
    fn test_impl_block_inherent() {
        let mut rodeo = Rodeo::default();
        let method_name = intern(&mut rodeo, "new");

        let method = FunctionDef::new(method_name, vec![], BrrrType::UNIT);
        let impl_block = ImplBlock::inherent(BrrrType::STRING).with_method(method);

        assert!(impl_block.is_inherent());
        assert!(!impl_block.is_trait_impl());
        assert_eq!(impl_block.method_count(), 1);
    }

    #[test]
    fn test_impl_block_trait() {
        let mut rodeo = Rodeo::default();
        let trait_name = intern(&mut rodeo, "Clone");

        let impl_block = ImplBlock::for_trait(trait_name, BrrrType::STRING);

        assert!(impl_block.is_trait_impl());
        assert!(!impl_block.is_inherent());
        assert_eq!(impl_block.trait_ref.as_ref().unwrap().name, trait_name);
    }

    #[test]
    fn test_full_declaration_variants() {
        let mut rodeo = Rodeo::default();
        let func_name = intern(&mut rodeo, "my_func");
        let type_name = intern(&mut rodeo, "MyType");
        let const_name = intern(&mut rodeo, "MY_CONST");

        // Function
        let func = FunctionDef::new(func_name, vec![], BrrrType::UNIT);
        let func_decl = FullDeclaration::function(func);
        assert!(func_decl.is_function());
        assert_eq!(func_decl.name(), Some(func_name));

        // Type
        let type_def = TypeDef::alias(type_name, BrrrType::BOOL);
        let type_decl = FullDeclaration::type_def(type_def);
        assert!(type_decl.is_type());
        assert_eq!(type_decl.name(), Some(type_name));

        // Const
        use crate::expr::{Expr_, Literal, WithLoc};
        let value = WithLoc::synthetic(Expr_::Lit(Literal::i32(42)));
        let const_decl = FullDeclaration::const_item(const_name, BrrrType::BOOL, value);
        assert!(const_decl.is_const());
        assert_eq!(const_decl.name(), Some(const_name));
    }

    #[test]
    fn test_static_declaration() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "GLOBAL");

        let static_decl = FullDeclaration::static_item(name, BrrrType::STRING, None, true);

        assert!(static_decl.is_static());
        if let FullDeclaration::Static { is_mut, .. } = static_decl {
            assert!(is_mut);
        }
    }

    #[test]
    fn test_module_declaration() {
        let mut rodeo = Rodeo::default();
        let mod_name = intern(&mut rodeo, "submodule");
        let func_name = intern(&mut rodeo, "inner_fn");

        let func = FunctionDef::new(func_name, vec![], BrrrType::UNIT);
        let mod_decl = FullDeclaration::module(mod_name, vec![FullDeclaration::function(func)]);

        assert!(mod_decl.is_module());
        if let FullDeclaration::Module { declarations, .. } = mod_decl {
            assert_eq!(declarations.len(), 1);
        }
    }

    #[test]
    fn test_extern_block() {
        let mut rodeo = Rodeo::default();
        let func_name = intern(&mut rodeo, "c_function");
        let abi = intern(&mut rodeo, "C");

        let func = FunctionDef::extern_fn(func_name, vec![], BrrrType::UNIT);
        let extern_decl = FullDeclaration::extern_block(
            Some(abi),
            vec![ExternItem::function(func)],
        );

        if let FullDeclaration::Extern { abi: Some(a), items, .. } = extern_decl {
            assert_eq!(a, abi);
            assert_eq!(items.len(), 1);
        }
    }

    #[test]
    fn test_assoc_type_def() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "Item");
        let bound = intern(&mut rodeo, "Clone");

        let assoc = AssocTypeDef::new(name)
            .with_bounds(vec![bound])
            .with_default(BrrrType::UNIT);

        assert_eq!(assoc.name, name);
        assert_eq!(assoc.bounds.len(), 1);
        assert!(assoc.default.is_some());
    }

    #[test]
    fn test_trait_ref() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "Iterator");

        let simple = TraitRef::simple(name);
        assert!(simple.type_args.is_empty());

        let with_args = TraitRef::with_args(name, vec![BrrrType::STRING]);
        assert_eq!(with_args.type_args.len(), 1);
    }
}
