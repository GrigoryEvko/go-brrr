//! Translation output types
//!
//! Provides richer output structures than brrr-repr's Module, containing
//! full function definitions with bodies.

use brrr_repr::decl::{Declaration, FunctionDef, Import, Module, TypeDef};
use brrr_repr::expr::Range;
use serde::{Deserialize, Serialize};

/// A fully translated module with complete definitions.
///
/// This extends brrr-repr's Module with actual function/type bodies.
/// Used as the output of translation before integration into analysis pipelines.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TranslatedModule {
    /// Module metadata (name, path, imports, declaration stubs)
    pub module: Module,

    /// Full function definitions with bodies
    pub functions: Vec<FunctionDef>,

    /// Full type definitions
    pub types: Vec<TypeDef>,

    /// Package-level constants (name, type, value expression)
    pub constants: Vec<ConstantDef>,

    /// Package-level variables (name, type, optional initializer)
    pub variables: Vec<VariableDef>,
}

impl TranslatedModule {
    /// Create a new translated module from a base module
    pub fn new(module: Module) -> Self {
        Self {
            module,
            functions: Vec::new(),
            types: Vec::new(),
            constants: Vec::new(),
            variables: Vec::new(),
        }
    }

    /// Add a function definition
    pub fn add_function(&mut self, func: FunctionDef) {
        // Also add to module declarations for metadata
        let name = format!("fn_{}", self.functions.len());
        let is_public = matches!(func.visibility, brrr_repr::types::Visibility::Public);
        self.module.declarations.push(Declaration::Function {
            name,
            is_public,
            span: func.span.clone(),
        });
        self.functions.push(func);
    }

    /// Add a type definition
    pub fn add_type(&mut self, typedef: TypeDef, name: String, is_public: bool, span: Range) {
        self.module.declarations.push(Declaration::Type {
            name,
            is_public,
            span,
        });
        self.types.push(typedef);
    }

    /// Add a constant definition
    pub fn add_constant(&mut self, constant: ConstantDef) {
        self.module.declarations.push(Declaration::Constant {
            name: constant.name.clone(),
            is_public: constant.is_public,
            span: constant.span.clone(),
        });
        self.constants.push(constant);
    }

    /// Add a variable definition
    pub fn add_variable(&mut self, var: VariableDef) {
        self.variables.push(var);
    }

    /// Get function by index
    pub fn get_function(&self, index: usize) -> Option<&FunctionDef> {
        self.functions.get(index)
    }

    /// Get all exported function names
    pub fn exported_functions(&self) -> impl Iterator<Item = &FunctionDef> {
        self.functions
            .iter()
            .filter(|f| matches!(f.visibility, brrr_repr::types::Visibility::Public))
    }
}

/// Package-level constant definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstantDef {
    /// Constant name
    pub name: String,
    /// Constant type (inferred if not explicit)
    pub ty: brrr_repr::BrrrType,
    /// Constant value expression (must be compile-time evaluable)
    pub value: brrr_repr::Expr,
    /// Is this exported?
    pub is_public: bool,
    /// Source location
    pub span: Range,
}

/// Package-level variable definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariableDef {
    /// Variable name
    pub name: String,
    /// Variable type
    pub ty: brrr_repr::BrrrType,
    /// Optional initializer expression
    pub initializer: Option<brrr_repr::Expr>,
    /// Is this exported?
    pub is_public: bool,
    /// Source location
    pub span: Range,
}
