//! Module system types
//!
//! Provides import/export declarations, module structure, and cross-module references.
//! Following EverParse's module organization patterns from Ast.fst.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::expr::Range;

// ============================================================================
// Module Identity
// ============================================================================

/// Unique identifier for a module within a compilation unit.
///
/// Used for efficient cross-module references without storing full paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct ModuleId(pub u32);

impl ModuleId {
    /// Unknown/unresolved module ID
    pub const UNKNOWN: Self = Self(u32::MAX);

    /// Root module (crate root)
    pub const ROOT: Self = Self(0);

    /// Create a new module ID
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Check if this is an unknown module ID
    pub const fn is_unknown(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw ID value
    pub const fn as_u32(self) -> u32 {
        self.0
    }
}

/// Fully qualified name with optional module scope.
///
/// Used for referencing items across module boundaries.
/// Following EverParse's ident' pattern with modul_name field.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QualifiedName {
    /// Module containing this item (None = current module)
    pub module: Option<ModuleId>,
    /// Local name within the module
    pub name: String,
}

impl QualifiedName {
    /// Create a local (unqualified) name
    pub fn local(name: impl Into<String>) -> Self {
        Self {
            module: None,
            name: name.into(),
        }
    }

    /// Create a fully qualified name
    pub fn qualified(module: ModuleId, name: impl Into<String>) -> Self {
        Self {
            module: Some(module),
            name: name.into(),
        }
    }

    /// Check if this is a local reference
    pub const fn is_local(&self) -> bool {
        self.module.is_none()
    }

    /// Check if this is a qualified reference
    pub const fn is_qualified(&self) -> bool {
        self.module.is_some()
    }
}

impl From<String> for QualifiedName {
    fn from(name: String) -> Self {
        Self::local(name)
    }
}

impl From<&str> for QualifiedName {
    fn from(name: &str) -> Self {
        Self::local(name)
    }
}

// ============================================================================
// Import System
// ============================================================================

/// A single item being imported from a module.
///
/// Represents `name` or `name as alias` in an import list.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ImportItem {
    /// Original name in the source module
    pub name: String,
    /// Optional local alias (e.g., `as Foo`)
    pub alias: Option<String>,
}

impl ImportItem {
    /// Create a simple import without alias
    pub fn simple(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            alias: None,
        }
    }

    /// Create an aliased import
    pub fn aliased(name: impl Into<String>, alias: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            alias: Some(alias.into()),
        }
    }

    /// Get the name to use locally (alias if present, otherwise original name)
    pub fn local_name(&self) -> &str {
        self.alias.as_deref().unwrap_or(&self.name)
    }
}

impl From<String> for ImportItem {
    fn from(name: String) -> Self {
        Self::simple(name)
    }
}

impl From<&str> for ImportItem {
    fn from(name: &str) -> Self {
        Self::simple(name)
    }
}

/// Which items are being imported from a module.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImportItems {
    /// Import all public items: `use module::*`
    All,
    /// Import specific named items: `use module::{a, b as c}`
    Named(Vec<ImportItem>),
}

impl ImportItems {
    /// Create an all-items import
    pub const fn all() -> Self {
        Self::All
    }

    /// Create a named items import
    pub fn named(items: Vec<ImportItem>) -> Self {
        Self::Named(items)
    }

    /// Check if this is a glob import
    pub const fn is_glob(&self) -> bool {
        matches!(self, Self::All)
    }

    /// Get the list of named items (empty for glob imports)
    pub fn items(&self) -> &[ImportItem] {
        match self {
            Self::All => &[],
            Self::Named(items) => items,
        }
    }
}

impl Default for ImportItems {
    fn default() -> Self {
        Self::Named(Vec::new())
    }
}

/// An import declaration.
///
/// Represents a `use` statement that brings items from another module into scope.
/// Examples:
/// - `use std::collections::HashMap;`
/// - `use std::io::{Read, Write as W};`
/// - `use crate::utils::*;`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Import {
    /// Module path segments: `["std", "collections", "HashMap"]`
    pub module_path: Vec<String>,
    /// Optional module alias: `use long::path::module as m`
    pub alias: Option<String>,
    /// Which items to import
    pub items: ImportItems,
    /// Source location
    pub span: Range,
}

impl Import {
    /// Create a simple path import (entire module)
    pub fn path(path: Vec<String>) -> Self {
        Self {
            module_path: path,
            alias: None,
            items: ImportItems::Named(Vec::new()),
            span: Range::SYNTHETIC,
        }
    }

    /// Create a glob import: `use module::*`
    pub fn glob(path: Vec<String>) -> Self {
        Self {
            module_path: path,
            alias: None,
            items: ImportItems::All,
            span: Range::SYNTHETIC,
        }
    }

    /// Create an import with specific items
    pub fn named(path: Vec<String>, items: Vec<ImportItem>) -> Self {
        Self {
            module_path: path,
            alias: None,
            items: ImportItems::Named(items),
            span: Range::SYNTHETIC,
        }
    }

    /// Set the source span
    pub fn with_span(mut self, span: Range) -> Self {
        self.span = span;
        self
    }

    /// Set a module alias
    pub fn with_alias(mut self, alias: impl Into<String>) -> Self {
        self.alias = Some(alias.into());
        self
    }

    /// Get the full path as a string (e.g., "std::collections::HashMap")
    pub fn path_string(&self) -> String {
        self.module_path.join("::")
    }

    /// Check if this is a glob import
    pub const fn is_glob(&self) -> bool {
        self.items.is_glob()
    }
}

// ============================================================================
// Export System
// ============================================================================

/// An export declaration.
///
/// Describes how items are made available to other modules.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Export {
    /// A public declaration: `pub fn foo`, `pub struct Bar`
    Public(String),

    /// A re-export from another module: `pub use other::{a, b}`
    Reexport {
        /// Source module path
        from: String,
        /// Items being re-exported
        items: Vec<String>,
    },

    /// Re-export all items from another module: `pub use other::*`
    ReexportAll {
        /// Source module path
        from: String,
    },
}

impl Export {
    /// Create a public export
    pub fn public(name: impl Into<String>) -> Self {
        Self::Public(name.into())
    }

    /// Create a re-export
    pub fn reexport(from: impl Into<String>, items: Vec<String>) -> Self {
        Self::Reexport {
            from: from.into(),
            items,
        }
    }

    /// Create a glob re-export
    pub fn reexport_all(from: impl Into<String>) -> Self {
        Self::ReexportAll { from: from.into() }
    }

    /// Get the name of the exported item (for Public variant)
    pub fn name(&self) -> Option<&str> {
        match self {
            Self::Public(name) => Some(name),
            _ => None,
        }
    }

    /// Check if this is a re-export
    pub const fn is_reexport(&self) -> bool {
        matches!(self, Self::Reexport { .. } | Self::ReexportAll { .. })
    }
}

// ============================================================================
// Module Structure
// ============================================================================

/// A source file in a module.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceFile {
    /// File path (relative to project root)
    pub path: String,
    /// File ID for position tracking
    pub file_id: u32,
    /// Content hash for incremental compilation
    pub content_hash: Option<[u8; 16]>,
}

impl SourceFile {
    /// Create a new source file entry
    pub fn new(path: impl Into<String>, file_id: u32) -> Self {
        Self {
            path: path.into(),
            file_id,
            content_hash: None,
        }
    }

    /// Set the content hash
    pub fn with_hash(mut self, hash: [u8; 16]) -> Self {
        self.content_hash = Some(hash);
        self
    }
}

/// A declaration within a module.
///
/// This is a placeholder type that will be expanded with actual declaration
/// variants (functions, types, constants, etc.) as the module system matures.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Declaration {
    /// Function declaration
    Function {
        name: String,
        is_public: bool,
        span: Range,
    },

    /// Type declaration (struct, enum, type alias)
    Type {
        name: String,
        is_public: bool,
        span: Range,
    },

    /// Constant declaration
    Constant {
        name: String,
        is_public: bool,
        span: Range,
    },

    /// Trait declaration
    Trait {
        name: String,
        is_public: bool,
        span: Range,
    },

    /// Trait implementation
    Impl {
        trait_name: Option<String>,
        for_type: String,
        span: Range,
    },

    /// Variable declaration
    Variable {
        name: String,
        is_public: bool,
        span: Range,
    },

    /// Module-level use declaration (internal)
    Use(Import),
}

impl Declaration {
    /// Get the name of the declaration (if it has one)
    pub fn name(&self) -> Option<&str> {
        match self {
            Self::Function { name, .. } => Some(name),
            Self::Type { name, .. } => Some(name),
            Self::Constant { name, .. } => Some(name),
            Self::Trait { name, .. } => Some(name),
            Self::Variable { name, .. } => Some(name),
            Self::Impl { .. } => None,
            Self::Use(_) => None,
        }
    }

    /// Check if this declaration is public
    pub fn is_public(&self) -> bool {
        match self {
            Self::Function { is_public, .. } => *is_public,
            Self::Type { is_public, .. } => *is_public,
            Self::Constant { is_public, .. } => *is_public,
            Self::Trait { is_public, .. } => *is_public,
            Self::Variable { is_public, .. } => *is_public,
            Self::Impl { .. } => false, // Impls are not directly public
            Self::Use(_) => false,
        }
    }

    /// Get the source span
    pub fn span(&self) -> Range {
        match self {
            Self::Function { span, .. } => *span,
            Self::Type { span, .. } => *span,
            Self::Constant { span, .. } => *span,
            Self::Trait { span, .. } => *span,
            Self::Variable { span, .. } => *span,
            Self::Impl { span, .. } => *span,
            Self::Use(import) => import.span,
        }
    }
}

/// A complete module AST.
///
/// Represents a single module with its imports, declarations, and submodules.
/// Following EverParse's organizational patterns for module structure.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Module {
    /// Module name (e.g., "utils")
    pub name: String,
    /// Full path from crate root (e.g., ["crate", "utils", "helpers"])
    pub path: Vec<String>,
    /// Import declarations
    pub imports: Vec<Import>,
    /// Declarations (functions, types, constants, etc.)
    pub declarations: Vec<Declaration>,
    /// Inline submodules (modules defined within this module)
    pub submodules: Vec<Module>,
    /// Source span for the module declaration
    pub span: Range,
}

impl Module {
    /// Create a new empty module
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            path: vec![name.clone()],
            name,
            imports: Vec::new(),
            declarations: Vec::new(),
            submodules: Vec::new(),
            span: Range::SYNTHETIC,
        }
    }

    /// Create a module with a full path
    pub fn with_path(name: impl Into<String>, path: Vec<String>) -> Self {
        Self {
            name: name.into(),
            path,
            imports: Vec::new(),
            declarations: Vec::new(),
            submodules: Vec::new(),
            span: Range::SYNTHETIC,
        }
    }

    /// Set the source span
    pub fn with_span(mut self, span: Range) -> Self {
        self.span = span;
        self
    }

    /// Add an import
    pub fn add_import(&mut self, import: Import) {
        self.imports.push(import);
    }

    /// Add a declaration
    pub fn add_declaration(&mut self, decl: Declaration) {
        self.declarations.push(decl);
    }

    /// Add a submodule
    pub fn add_submodule(&mut self, submodule: Module) {
        self.submodules.push(submodule);
    }

    /// Get the fully qualified path string (e.g., "crate::utils::helpers")
    pub fn full_path(&self) -> String {
        self.path.join("::")
    }

    /// Get all public declarations
    pub fn public_declarations(&self) -> impl Iterator<Item = &Declaration> {
        self.declarations.iter().filter(|d| d.is_public())
    }

    /// Find a declaration by name
    pub fn find_declaration(&self, name: &str) -> Option<&Declaration> {
        self.declarations.iter().find(|d| d.name() == Some(name))
    }

    /// Find a submodule by name
    pub fn find_submodule(&self, name: &str) -> Option<&Module> {
        self.submodules.iter().find(|m| m.name == name)
    }

    /// Check if this module is empty
    pub fn is_empty(&self) -> bool {
        self.imports.is_empty() && self.declarations.is_empty() && self.submodules.is_empty()
    }

    /// Get the depth of this module (number of path segments)
    pub fn depth(&self) -> usize {
        self.path.len()
    }
}

impl Default for Module {
    fn default() -> Self {
        Self::new("unnamed")
    }
}

// ============================================================================
// Brrr Module (Full Compilation Unit)
// ============================================================================

/// A complete brrr module with all source files and module index.
///
/// This represents a full compilation unit ready for analysis or code generation.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BrrrModuleData {
    /// The root module AST
    pub module: Module,
    /// All source files in this compilation unit
    pub source_files: Vec<SourceFile>,
    /// Index mapping module paths to their IDs for fast lookup
    pub module_index: HashMap<String, ModuleId>,
}

impl BrrrModuleData {
    /// Create a new brrr module
    pub fn new(module: Module) -> Self {
        Self {
            module,
            source_files: Vec::new(),
            module_index: HashMap::new(),
        }
    }

    /// Add a source file
    pub fn add_source_file(&mut self, file: SourceFile) -> u32 {
        let id = self.source_files.len() as u32;
        self.source_files.push(file);
        id
    }

    /// Register a module in the index
    pub fn register_module(&mut self, path: &str, id: ModuleId) {
        self.module_index.insert(path.to_string(), id);
    }

    /// Look up a module by path
    pub fn lookup_module(&self, path: &str) -> Option<ModuleId> {
        self.module_index.get(path).copied()
    }

    /// Get a source file by ID
    pub fn get_source_file(&self, file_id: u32) -> Option<&SourceFile> {
        self.source_files.get(file_id as usize)
    }

    /// Get the total number of modules
    pub fn module_count(&self) -> usize {
        self.module_index.len()
    }

    /// Get all module paths
    pub fn module_paths(&self) -> impl Iterator<Item = &str> {
        self.module_index.keys().map(|s| s.as_str())
    }
}

// ============================================================================
// Module ID Counter
// ============================================================================

/// Counter for generating unique module IDs.
#[derive(Debug, Default)]
pub struct ModuleIdCounter {
    next_id: std::sync::atomic::AtomicU32,
}

impl Clone for ModuleIdCounter {
    fn clone(&self) -> Self {
        Self {
            next_id: std::sync::atomic::AtomicU32::new(
                self.next_id.load(std::sync::atomic::Ordering::Relaxed),
            ),
        }
    }
}

impl ModuleIdCounter {
    /// Create a new counter starting at 0
    pub const fn new() -> Self {
        Self {
            next_id: std::sync::atomic::AtomicU32::new(0),
        }
    }

    /// Generate a fresh module ID
    pub fn fresh(&self) -> ModuleId {
        ModuleId(
            self.next_id
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        )
    }

    /// Get the current count without incrementing
    pub fn current(&self) -> u32 {
        self.next_id.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Reset the counter (use with caution)
    pub fn reset(&self) {
        self.next_id
            .store(0, std::sync::atomic::Ordering::Relaxed);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_id() {
        let id = ModuleId::new(42);
        assert_eq!(id.as_u32(), 42);
        assert!(!id.is_unknown());
        assert!(ModuleId::UNKNOWN.is_unknown());
    }

    #[test]
    fn test_qualified_name() {
        let local = QualifiedName::local("foo");
        assert!(local.is_local());
        assert!(!local.is_qualified());

        let qualified = QualifiedName::qualified(ModuleId::new(1), "bar");
        assert!(qualified.is_qualified());
        assert!(!qualified.is_local());
    }

    #[test]
    fn test_import_item() {
        let simple = ImportItem::simple("HashMap");
        assert_eq!(simple.local_name(), "HashMap");

        let aliased = ImportItem::aliased("HashMap", "Map");
        assert_eq!(aliased.local_name(), "Map");
    }

    #[test]
    fn test_import() {
        let import = Import::named(
            vec!["std".into(), "collections".into()],
            vec![ImportItem::simple("HashMap"), ImportItem::aliased("HashSet", "Set")],
        );

        assert!(!import.is_glob());
        assert_eq!(import.path_string(), "std::collections");
        assert_eq!(import.items.items().len(), 2);
    }

    #[test]
    fn test_glob_import() {
        let import = Import::glob(vec!["crate".into(), "utils".into()]);
        assert!(import.is_glob());
        assert_eq!(import.path_string(), "crate::utils");
    }

    #[test]
    fn test_export() {
        let public = Export::public("foo");
        assert_eq!(public.name(), Some("foo"));
        assert!(!public.is_reexport());

        let reexport = Export::reexport("other", vec!["a".into(), "b".into()]);
        assert!(reexport.is_reexport());
    }

    #[test]
    fn test_module() {
        let mut module = Module::new("utils");
        assert_eq!(module.name, "utils");
        assert!(module.is_empty());

        module.add_import(Import::path(vec!["std".into()]));
        module.add_declaration(Declaration::Function {
            name: "helper".into(),
            is_public: true,
            span: Range::SYNTHETIC,
        });

        assert!(!module.is_empty());
        assert_eq!(module.depth(), 1);
        assert!(module.find_declaration("helper").is_some());
    }

    #[test]
    fn test_module_with_submodules() {
        let mut parent = Module::new("parent");
        let child = Module::with_path("child", vec!["parent".into(), "child".into()]);

        parent.add_submodule(child);

        assert!(parent.find_submodule("child").is_some());
        assert!(parent.find_submodule("nonexistent").is_none());
    }

    #[test]
    fn test_brrr_module_data() {
        let module = Module::new("main");
        let mut data = BrrrModuleData::new(module);

        let file_id = data.add_source_file(SourceFile::new("src/main.brrr", 0));
        assert_eq!(file_id, 0);

        data.register_module("main", ModuleId::new(0));
        assert_eq!(data.lookup_module("main"), Some(ModuleId::new(0)));
        assert_eq!(data.lookup_module("unknown"), None);
    }

    #[test]
    fn test_module_id_counter() {
        let counter = ModuleIdCounter::new();
        assert_eq!(counter.current(), 0);

        let id1 = counter.fresh();
        let id2 = counter.fresh();
        assert_eq!(id1.as_u32(), 0);
        assert_eq!(id2.as_u32(), 1);
        assert_eq!(counter.current(), 2);
    }

    #[test]
    fn test_declaration_properties() {
        let func = Declaration::Function {
            name: "foo".into(),
            is_public: true,
            span: Range::SYNTHETIC,
        };
        assert_eq!(func.name(), Some("foo"));
        assert!(func.is_public());

        let type_decl = Declaration::Type {
            name: "Bar".into(),
            is_public: false,
            span: Range::SYNTHETIC,
        };
        assert_eq!(type_decl.name(), Some("Bar"));
        assert!(!type_decl.is_public());

        let impl_decl = Declaration::Impl {
            trait_name: Some("Display".into()),
            for_type: "Bar".into(),
            span: Range::SYNTHETIC,
        };
        assert_eq!(impl_decl.name(), None);
        assert!(!impl_decl.is_public());
    }
}
