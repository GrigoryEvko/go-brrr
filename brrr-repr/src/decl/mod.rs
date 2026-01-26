//! Declaration and module system types
//!
//! Provides module structure, import/export declarations, and cross-module references.
//! Following EverParse's module organization patterns.
//!
//! # Module Organization
//!
//! - `module` - Module identity, imports/exports, and simple declaration tracking
//! - `definitions` - Detailed declaration types (FunctionDef, TypeDef, TraitDef, etc.)
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::decl::{FunctionDef, TypeDef, ImplBlock};
//!
//! // Create a function definition
//! let func = FunctionDef::new(name, params, return_type);
//!
//! // Create a type alias
//! let alias = TypeDef::alias(name, target_type);
//!
//! // Create a trait impl
//! let impl_block = ImplBlock::for_trait(trait_name, self_type);
//! ```

mod definitions;
mod module;

// Re-export everything from definitions (detailed declaration types)
pub use definitions::{
    // Core declaration types
    FunctionDef, TypeDef, TraitDef, ImplBlock,
    // Associated types and trait references
    AssocTypeDef, AssocTypeBinding, TraitRef,
    // Extern items
    ExternItem,
    // Full declaration enum
    FullDeclaration,
    // Re-exported VarId
    VarId,
};

pub use module::{
    // Module identity
    ModuleId, ModuleIdCounter, QualifiedName,
    // Import system
    Import, ImportItem, ImportItems,
    // Export system
    Export,
    // Module structure
    Declaration, Module, SourceFile,
    // Full compilation unit
    BrrrModuleData,
};
