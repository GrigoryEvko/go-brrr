//! Public API for the representation engine
//!
//! Provides high-level encode/decode functions for .brrr and .brrrx formats.

use std::io::{Read, Write};
use std::path::Path;

use crate::decl::{FunctionDef, TypeDef, TraitDef, ImplBlock, FullDeclaration};
use crate::encoding::{BinaryDecoder, BinaryEncoder, TextDecoder, TextEncoder};
use crate::error::ReprResult;
use crate::expr::Expr;
use crate::types::BrrrType;

/// Output format for encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Format {
    /// Binary format (.brrr) - efficient, compact
    #[default]
    Binary,
    /// Text format (.brrrx) - human-readable, debuggable
    Text,
}

impl Format {
    /// Detect format from file extension
    pub fn from_extension(path: impl AsRef<Path>) -> Self {
        match path.as_ref().extension().and_then(|e| e.to_str()) {
            Some("brrrx") => Self::Text,
            _ => Self::Binary,
        }
    }

    /// Get file extension for this format
    pub const fn extension(self) -> &'static str {
        match self {
            Self::Binary => "brrr",
            Self::Text => "brrrx",
        }
    }
}

/// A complete brrr module with types, expressions, declarations, and metadata.
///
/// This struct unifies the module representation for both analysis and serialization.
/// It includes:
/// - Legacy type and expression vectors for backward compatibility
/// - Full declaration support via `FullDeclaration` for functions, types, traits, and impls
#[derive(Debug, Clone, Default)]
pub struct BrrrModule {
    /// Module name
    pub name: String,
    /// Source files referenced
    pub files: Vec<String>,
    /// Type definitions (for backward compatibility with legacy formats)
    pub types: Vec<BrrrType>,
    /// Top-level expressions (for backward compatibility with legacy formats)
    pub exprs: Vec<Expr>,
    /// Top-level declarations (functions, types, traits, impls, consts, statics)
    pub declarations: Vec<FullDeclaration>,
    /// Module version
    pub version: u16,
}

impl BrrrModule {
    /// Create a new empty module
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            files: Vec::new(),
            types: Vec::new(),
            exprs: Vec::new(),
            declarations: Vec::new(),
            version: 1,
        }
    }

    /// Add a source file, returns file ID
    pub fn add_file(&mut self, path: impl Into<String>) -> u32 {
        let id = self.files.len() as u32;
        self.files.push(path.into());
        id
    }

    /// Add a type definition (legacy API), returns type ID
    pub fn add_type(&mut self, ty: BrrrType) -> u32 {
        let id = self.types.len() as u32;
        self.types.push(ty);
        id
    }

    /// Add an expression (legacy API), returns expression ID
    pub fn add_expr(&mut self, expr: Expr) -> u32 {
        let id = self.exprs.len() as u32;
        self.exprs.push(expr);
        id
    }

    // =========================================================================
    // Declaration Management
    // =========================================================================

    /// Add a generic declaration, returns declaration index
    pub fn add_declaration(&mut self, decl: FullDeclaration) -> usize {
        let id = self.declarations.len();
        self.declarations.push(decl);
        id
    }

    /// Add a function definition, returns declaration index
    pub fn add_function(&mut self, func: FunctionDef) -> usize {
        self.add_declaration(FullDeclaration::Function(func))
    }

    /// Add a type definition (detailed), returns declaration index
    pub fn add_type_def(&mut self, typedef: TypeDef) -> usize {
        self.add_declaration(FullDeclaration::Type(typedef))
    }

    /// Add a trait definition, returns declaration index
    pub fn add_trait(&mut self, traitdef: TraitDef) -> usize {
        self.add_declaration(FullDeclaration::Trait(traitdef))
    }

    /// Add an impl block, returns declaration index
    pub fn add_impl(&mut self, impl_block: ImplBlock) -> usize {
        self.add_declaration(FullDeclaration::Impl(impl_block))
    }

    // =========================================================================
    // Declaration Iterators
    // =========================================================================

    /// Get all function definitions
    pub fn functions(&self) -> impl Iterator<Item = &FunctionDef> {
        self.declarations.iter().filter_map(|d| match d {
            FullDeclaration::Function(f) => Some(f),
            _ => None,
        })
    }

    /// Get all type definitions
    pub fn type_defs(&self) -> impl Iterator<Item = &TypeDef> {
        self.declarations.iter().filter_map(|d| match d {
            FullDeclaration::Type(t) => Some(t),
            _ => None,
        })
    }

    /// Get all trait definitions
    pub fn traits(&self) -> impl Iterator<Item = &TraitDef> {
        self.declarations.iter().filter_map(|d| match d {
            FullDeclaration::Trait(t) => Some(t),
            _ => None,
        })
    }

    /// Get all impl blocks
    pub fn impls(&self) -> impl Iterator<Item = &ImplBlock> {
        self.declarations.iter().filter_map(|d| match d {
            FullDeclaration::Impl(i) => Some(i),
            _ => None,
        })
    }

    /// Get all module declarations
    pub fn modules(&self) -> impl Iterator<Item = (&lasso::Spur, &Vec<FullDeclaration>)> {
        self.declarations.iter().filter_map(|d| match d {
            FullDeclaration::Module { name, declarations, .. } => Some((name, declarations)),
            _ => None,
        })
    }

    /// Get declaration by index
    pub fn get_declaration(&self, index: usize) -> Option<&FullDeclaration> {
        self.declarations.get(index)
    }

    /// Get mutable declaration by index
    pub fn get_declaration_mut(&mut self, index: usize) -> Option<&mut FullDeclaration> {
        self.declarations.get_mut(index)
    }

    /// Count declarations of each kind
    pub fn declaration_counts(&self) -> DeclarationCounts {
        let mut counts = DeclarationCounts::default();
        for decl in &self.declarations {
            match decl {
                FullDeclaration::Function(_) => counts.functions += 1,
                FullDeclaration::Type(_) => counts.types += 1,
                FullDeclaration::Trait(_) => counts.traits += 1,
                FullDeclaration::Impl(_) => counts.impls += 1,
                FullDeclaration::Const { .. } => counts.consts += 1,
                FullDeclaration::Static { .. } => counts.statics += 1,
                FullDeclaration::Module { .. } => counts.modules += 1,
                FullDeclaration::Use { .. } => counts.uses += 1,
                FullDeclaration::Extern { .. } => counts.externs += 1,
            }
        }
        counts
    }

    /// Check if module has any declarations
    pub fn has_declarations(&self) -> bool {
        !self.declarations.is_empty()
    }

    /// Total number of declarations
    pub fn declaration_count(&self) -> usize {
        self.declarations.len()
    }
}

/// Counts of different declaration types in a module
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DeclarationCounts {
    pub functions: usize,
    pub types: usize,
    pub traits: usize,
    pub impls: usize,
    pub consts: usize,
    pub statics: usize,
    pub modules: usize,
    pub uses: usize,
    pub externs: usize,
}

/// Main encoder for .brrr format
#[derive(Debug)]
pub struct BrrrEncoder {
    module: BrrrModule,
}

impl BrrrEncoder {
    /// Create a new encoder
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            module: BrrrModule::new(name),
        }
    }

    /// Create from an existing module
    pub fn from_module(module: BrrrModule) -> Self {
        Self { module }
    }

    /// Get a reference to the underlying module
    pub fn module(&self) -> &BrrrModule {
        &self.module
    }

    /// Get a mutable reference to the underlying module
    pub fn module_mut(&mut self) -> &mut BrrrModule {
        &mut self.module
    }

    /// Add a source file, returns file ID
    pub fn add_file(&mut self, path: impl Into<String>) -> u32 {
        self.module.add_file(path)
    }

    /// Add a type (legacy API), returns type ID
    pub fn add_type(&mut self, ty: BrrrType) -> u32 {
        self.module.add_type(ty)
    }

    /// Add an expression (legacy API), returns expression ID
    pub fn add_expr(&mut self, expr: Expr) -> u32 {
        self.module.add_expr(expr)
    }

    // =========================================================================
    // Declaration Methods
    // =========================================================================

    /// Add a generic declaration, returns declaration index
    pub fn add_declaration(&mut self, decl: FullDeclaration) -> usize {
        self.module.add_declaration(decl)
    }

    /// Add a function definition, returns declaration index
    pub fn add_function(&mut self, func: FunctionDef) -> usize {
        self.module.add_function(func)
    }

    /// Add a type definition, returns declaration index
    pub fn add_type_def(&mut self, typedef: TypeDef) -> usize {
        self.module.add_type_def(typedef)
    }

    /// Add a trait definition, returns declaration index
    pub fn add_trait(&mut self, traitdef: TraitDef) -> usize {
        self.module.add_trait(traitdef)
    }

    /// Add an impl block, returns declaration index
    pub fn add_impl(&mut self, impl_block: ImplBlock) -> usize {
        self.module.add_impl(impl_block)
    }

    // =========================================================================
    // Encoding Methods
    // =========================================================================

    /// Encode to binary format
    pub fn encode_binary<W: Write>(&self, writer: W) -> ReprResult<()> {
        let encoder = BinaryEncoder::new();
        encoder.encode(&self.module, writer)
    }

    /// Encode to text format
    pub fn encode_text<W: Write>(&self, writer: W) -> ReprResult<()> {
        let encoder = TextEncoder::new();
        encoder.encode(&self.module, writer)
    }

    /// Encode to the specified format
    pub fn encode<W: Write>(&self, writer: W, format: Format) -> ReprResult<()> {
        match format {
            Format::Binary => self.encode_binary(writer),
            Format::Text => self.encode_text(writer),
        }
    }

    /// Compute content hash of the module
    pub fn content_hash(&self) -> [u8; 16] {
        crate::encoding::content_hash(&self.module)
    }
}

/// Main decoder for .brrr format
#[derive(Debug)]
pub struct BrrrDecoder {
    module: BrrrModule,
}

impl BrrrDecoder {
    /// Decode from binary format
    pub fn decode_binary<R: Read>(reader: R) -> ReprResult<Self> {
        let decoder = BinaryDecoder::new();
        let module = decoder.decode(reader)?;
        Ok(Self { module })
    }

    /// Decode from text format
    pub fn decode_text<R: Read>(reader: R) -> ReprResult<Self> {
        let decoder = TextDecoder::new();
        let module = decoder.decode(reader)?;
        Ok(Self { module })
    }

    /// Auto-detect format and decode
    pub fn decode<R: Read>(reader: R, format: Format) -> ReprResult<Self> {
        match format {
            Format::Binary => Self::decode_binary(reader),
            Format::Text => Self::decode_text(reader),
        }
    }

    /// Get the decoded module
    pub fn into_module(self) -> BrrrModule {
        self.module
    }

    /// Borrow the decoded module
    pub fn module(&self) -> &BrrrModule {
        &self.module
    }

    /// Get type by ID (legacy API)
    pub fn get_type(&self, id: u32) -> Option<&BrrrType> {
        self.module.types.get(id as usize)
    }

    /// Get expression by ID (legacy API)
    pub fn get_expr(&self, id: u32) -> Option<&Expr> {
        self.module.exprs.get(id as usize)
    }

    // =========================================================================
    // Declaration Access
    // =========================================================================

    /// Get declaration by index
    pub fn get_declaration(&self, index: usize) -> Option<&FullDeclaration> {
        self.module.get_declaration(index)
    }

    /// Get all function definitions
    pub fn functions(&self) -> impl Iterator<Item = &FunctionDef> {
        self.module.functions()
    }

    /// Get all type definitions
    pub fn type_defs(&self) -> impl Iterator<Item = &TypeDef> {
        self.module.type_defs()
    }

    /// Get all trait definitions
    pub fn traits(&self) -> impl Iterator<Item = &TraitDef> {
        self.module.traits()
    }

    /// Get all impl blocks
    pub fn impls(&self) -> impl Iterator<Item = &ImplBlock> {
        self.module.impls()
    }

    /// Get declaration counts
    pub fn declaration_counts(&self) -> DeclarationCounts {
        self.module.declaration_counts()
    }

    // =========================================================================
    // Verification
    // =========================================================================

    /// Verify content hash
    pub fn verify_hash(&self, expected: &[u8; 16]) -> bool {
        let actual = crate::encoding::content_hash(&self.module);
        actual == *expected
    }
}

// ============================================================================
// Convenience functions
// ============================================================================

/// Encode a module to a file
pub fn encode_file(path: impl AsRef<Path>, module: &BrrrModule) -> ReprResult<()> {
    let path = path.as_ref();
    let format = Format::from_extension(path);
    let file = std::fs::File::create(path)?;
    let writer = std::io::BufWriter::new(file);

    let encoder = BrrrEncoder::from_module(module.clone());
    encoder.encode(writer, format)
}

/// Decode a module from a file
pub fn decode_file(path: impl AsRef<Path>) -> ReprResult<BrrrModule> {
    let path = path.as_ref();
    let format = Format::from_extension(path);
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);

    let decoder = BrrrDecoder::decode(reader, format)?;
    Ok(decoder.into_module())
}

/// Convert between formats
pub fn convert(input: impl AsRef<Path>, output: impl AsRef<Path>) -> ReprResult<()> {
    let module = decode_file(input)?;
    encode_file(output, &module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_format_from_extension() {
        assert_eq!(Format::from_extension("foo.brrr"), Format::Binary);
        assert_eq!(Format::from_extension("foo.brrrx"), Format::Text);
        assert_eq!(Format::from_extension("foo.txt"), Format::Binary); // Default
    }

    #[test]
    fn test_module_builder() {
        let mut encoder = BrrrEncoder::new("test");
        let file_id = encoder.add_file("main.brrr");
        assert_eq!(file_id, 0);

        let type_id = encoder.add_type(BrrrType::Prim(crate::types::PrimKind::Unit));
        assert_eq!(type_id, 0);
    }

    #[test]
    fn test_module_declarations() {
        let mut module = BrrrModule::new("test_module");
        assert!(!module.has_declarations());
        assert_eq!(module.declaration_count(), 0);

        // Add a function declaration
        let mut rodeo = Rodeo::default();
        let func_name = rodeo.get_or_intern("my_function");
        let func = FunctionDef::new(func_name, vec![], BrrrType::UNIT);
        let func_id = module.add_function(func);
        assert_eq!(func_id, 0);

        assert!(module.has_declarations());
        assert_eq!(module.declaration_count(), 1);

        // Add a type definition
        let type_name = rodeo.get_or_intern("MyType");
        let typedef = TypeDef::alias(type_name, BrrrType::BOOL);
        let type_id = module.add_type_def(typedef);
        assert_eq!(type_id, 1);

        // Add a trait definition
        let trait_name = rodeo.get_or_intern("MyTrait");
        let t_param = rodeo.get_or_intern("T");
        let traitdef = TraitDef::new(trait_name, vec![crate::types::KindedVar::of_type(t_param)]);
        let trait_id = module.add_trait(traitdef);
        assert_eq!(trait_id, 2);

        // Add an impl block
        let impl_block = ImplBlock::inherent(BrrrType::STRING);
        let impl_id = module.add_impl(impl_block);
        assert_eq!(impl_id, 3);

        assert_eq!(module.declaration_count(), 4);

        // Check counts
        let counts = module.declaration_counts();
        assert_eq!(counts.functions, 1);
        assert_eq!(counts.types, 1);
        assert_eq!(counts.traits, 1);
        assert_eq!(counts.impls, 1);
    }

    #[test]
    fn test_module_iterators() {
        let mut module = BrrrModule::new("iterator_test");
        let mut rodeo = Rodeo::default();

        // Add multiple functions
        for i in 0..3 {
            let name = rodeo.get_or_intern(format!("func_{}", i));
            let func = FunctionDef::new(name, vec![], BrrrType::UNIT);
            module.add_function(func);
        }

        // Add a type and trait
        let type_name = rodeo.get_or_intern("SomeType");
        module.add_type_def(TypeDef::alias(type_name, BrrrType::BOOL));

        let trait_name = rodeo.get_or_intern("SomeTrait");
        let t_param = rodeo.get_or_intern("T");
        module.add_trait(TraitDef::new(trait_name, vec![crate::types::KindedVar::of_type(t_param)]));

        // Test iterators
        assert_eq!(module.functions().count(), 3);
        assert_eq!(module.type_defs().count(), 1);
        assert_eq!(module.traits().count(), 1);
        assert_eq!(module.impls().count(), 0);
    }

    #[test]
    fn test_encoder_with_declarations() {
        let mut encoder = BrrrEncoder::new("encoder_test");
        let mut rodeo = Rodeo::default();

        // Add a function via encoder
        let func_name = rodeo.get_or_intern("encode_me");
        let func = FunctionDef::new(func_name, vec![], BrrrType::UNIT);
        let decl_id = encoder.add_function(func);
        assert_eq!(decl_id, 0);

        // Verify module has the declaration
        assert_eq!(encoder.module().declaration_count(), 1);
    }

    #[test]
    fn test_declaration_counts_default() {
        let counts = DeclarationCounts::default();
        assert_eq!(counts.functions, 0);
        assert_eq!(counts.types, 0);
        assert_eq!(counts.traits, 0);
        assert_eq!(counts.impls, 0);
        assert_eq!(counts.consts, 0);
        assert_eq!(counts.statics, 0);
        assert_eq!(counts.modules, 0);
        assert_eq!(counts.uses, 0);
        assert_eq!(counts.externs, 0);
    }
}
