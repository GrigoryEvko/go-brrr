//! Integration tests for the full compilation pipeline

use crate::api::{BrrrDecoder, BrrrEncoder, BrrrModule, Format};
use crate::decl::{Declaration, Module};
use crate::effects::EffectRow;
use crate::encoding::{BinaryDecoder, BinaryEncoder, TextDecoder, TextEncoder};
use crate::expr::{Expr, Expr_, Literal, Pos, Range, WithLoc};
use crate::pipeline::{compile, compile_with_recovery, CompilationConfig, CompilationResult};
use crate::types::{BrrrType, IntType, NumericType, PrimKind};

// ============================================================================
// Helper Functions
// ============================================================================

/// Create a simple empty module for testing
fn create_empty_module(name: &str) -> Module {
    Module::new(name)
}

/// Create a module with a single function declaration
fn create_module_with_function(name: &str) -> Module {
    let mut module = Module::new(name);
    module.add_declaration(Declaration::Function {
        name: "test_fn".to_string(),
        is_public: true,
        span: Range::SYNTHETIC,
    });
    module
}

/// Create a module with multiple declarations
fn create_module_with_declarations(name: &str) -> Module {
    let mut module = Module::new(name);

    // Add function
    module.add_declaration(Declaration::Function {
        name: "helper".to_string(),
        is_public: false,
        span: Range::SYNTHETIC,
    });

    // Add type
    module.add_declaration(Declaration::Type {
        name: "MyStruct".to_string(),
        is_public: true,
        span: Range::SYNTHETIC,
    });

    // Add constant
    module.add_declaration(Declaration::Constant {
        name: "MAX_SIZE".to_string(),
        is_public: true,
        span: Range::SYNTHETIC,
    });

    // Add trait
    module.add_declaration(Declaration::Trait {
        name: "Display".to_string(),
        is_public: true,
        span: Range::SYNTHETIC,
    });

    // Add impl
    module.add_declaration(Declaration::Impl {
        trait_name: Some("Display".to_string()),
        for_type: "MyStruct".to_string(),
        span: Range::SYNTHETIC,
    });

    module
}

/// Create a BrrrModule for encoding tests
fn create_test_brrr_module(name: &str) -> BrrrModule {
    let mut module = BrrrModule::new(name);
    module.add_file("test.brrr");
    module.add_type(BrrrType::BOOL);
    module.add_type(BrrrType::STRING);
    module.add_type(BrrrType::Numeric(NumericType::Int(IntType::I32)));
    module
}

/// Create a BrrrModule with complex types
fn create_module_with_complex_types(name: &str) -> BrrrModule {
    let mut module = BrrrModule::new(name);

    // Add various type constructors
    module.add_type(BrrrType::UNIT);
    module.add_type(BrrrType::BOOL);
    module.add_type(BrrrType::Numeric(NumericType::Int(IntType::I64)));
    module.add_type(BrrrType::option(BrrrType::STRING));
    module.add_type(BrrrType::result(BrrrType::BOOL, BrrrType::STRING));
    module.add_type(BrrrType::tuple(vec![BrrrType::BOOL, BrrrType::Numeric(NumericType::Int(IntType::I32))]));
    module.add_type(BrrrType::array(BrrrType::Numeric(NumericType::Int(IntType::U8))));

    module
}

// ============================================================================
// Pipeline Tests
// ============================================================================

#[test]
fn test_compile_empty_module() {
    let module = create_empty_module("empty");
    let config = CompilationConfig::default();
    let result = compile(&module, &config);

    assert!(result.is_success(), "Empty module should compile successfully");
    assert_eq!(result.error_count(), 0);
    assert_eq!(result.warning_count(), 0);
}

#[test]
fn test_compile_module_with_function() {
    let module = create_module_with_function("with_function");
    let config = CompilationConfig::default();
    let result = compile(&module, &config);

    assert!(result.is_success(), "Module with function should compile");
}

#[test]
fn test_compile_module_with_declarations() {
    let module = create_module_with_declarations("with_decls");
    let config = CompilationConfig::default();
    let result = compile(&module, &config);

    assert!(
        result.is_success(),
        "Module with declarations should compile: {:?}",
        result.errors
    );
}

#[test]
fn test_compile_minimal_config() {
    let module = create_module_with_function("minimal");
    let config = CompilationConfig::minimal();
    let result = compile(&module, &config);

    assert!(result.is_success());
    assert!(result.type_info.is_some());
}

#[test]
fn test_compile_full_config() {
    let module = create_module_with_function("full");
    let config = CompilationConfig::full();
    let result = compile(&module, &config);

    // Full config may produce warnings but should not fail on empty module
    assert!(result.is_success());
    assert!(result.type_info.is_some());
    assert!(result.effect_info.is_some());
    assert!(result.borrow_info.is_some());
}

#[test]
fn test_compile_with_recovery_collects_all_errors() {
    let module = create_empty_module("recovery");
    let config = CompilationConfig::default().with_fail_fast();
    let result = compile_with_recovery(&module, &config);

    // Recovery should not have fail_fast behavior
    assert!(result.is_success());
}

#[test]
fn test_compilation_result_accessors() {
    let mut result = CompilationResult::new("test");

    assert!(result.is_success());
    assert!(!result.has_errors());
    assert_eq!(result.error_count(), 0);
    assert_eq!(result.warning_count(), 0);

    // Access type info
    result.type_info = Some(crate::pipeline::TypeInfo::new());
    assert!(result.type_info.is_some());
}

// ============================================================================
// Encoding Roundtrip Tests
// ============================================================================

#[test]
fn test_text_encode_decode_roundtrip() {
    let original = create_test_brrr_module("roundtrip");

    // Encode to text
    let mut buffer: Vec<u8> = Vec::new();
    let encoder = TextEncoder::new();
    encoder.encode(&original, &mut buffer).expect("text encoding should succeed");

    // Decode from text
    let decoder = TextDecoder::new();
    let decoded = decoder.decode(&buffer[..]).expect("text decoding should succeed");

    // Verify basic properties preserved
    assert_eq!(original.name, decoded.name);
    assert_eq!(original.version, decoded.version);
}

#[test]
fn test_binary_encode_decode_roundtrip() {
    let original = create_test_brrr_module("binary_test");

    // Encode to binary
    let mut buffer: Vec<u8> = Vec::new();
    let encoder = BinaryEncoder::new();
    encoder.encode(&original, &mut buffer).expect("binary encoding should succeed");

    // Decode from binary
    let decoder = BinaryDecoder::new();
    let decoded = decoder.decode(&buffer[..]).expect("binary decoding should succeed");

    // Verify properties preserved
    assert_eq!(original.name, decoded.name);
    assert_eq!(original.version, decoded.version);
    assert_eq!(original.files.len(), decoded.files.len());
    assert_eq!(original.types.len(), decoded.types.len());
}

#[test]
fn test_encoder_api_roundtrip() {
    let mut encoder = BrrrEncoder::new("api_test");
    encoder.add_file("main.brrr");
    encoder.add_type(BrrrType::BOOL);

    // Compute content hash
    let hash = encoder.content_hash();
    assert_ne!(hash, [0u8; 16], "Content hash should be non-zero");

    // Encode to binary
    let mut binary_buf: Vec<u8> = Vec::new();
    encoder.encode_binary(&mut binary_buf).expect("binary encoding should work");

    // Decode
    let decoder = BrrrDecoder::decode_binary(&binary_buf[..]).expect("decoding should work");
    let module = decoder.module();

    assert_eq!(module.name, "api_test");
    assert_eq!(module.files.len(), 1);
    assert_eq!(module.types.len(), 1);
}

#[test]
fn test_format_detection() {
    assert_eq!(Format::from_extension("foo.brrr"), Format::Binary);
    assert_eq!(Format::from_extension("foo.brrrx"), Format::Text);
    assert_eq!(Format::from_extension("foo.txt"), Format::Binary); // default

    assert_eq!(Format::Binary.extension(), "brrr");
    assert_eq!(Format::Text.extension(), "brrrx");
}

#[test]
fn test_encode_complex_types() {
    let original = create_module_with_complex_types("complex");

    // Binary roundtrip
    let mut buffer: Vec<u8> = Vec::new();
    let encoder = BinaryEncoder::new();
    encoder.encode(&original, &mut buffer).expect("encoding complex types should succeed");

    let decoder = BinaryDecoder::new();
    let decoded = decoder.decode(&buffer[..]).expect("decoding complex types should succeed");

    assert_eq!(original.types.len(), decoded.types.len());
}

// ============================================================================
// Type System Tests
// ============================================================================

#[test]
fn test_type_construction() {
    // Test constant types
    assert!(matches!(BrrrType::UNIT, BrrrType::Prim(PrimKind::Unit)));
    assert!(matches!(BrrrType::BOOL, BrrrType::Prim(PrimKind::Bool)));
    assert!(matches!(BrrrType::NEVER, BrrrType::Prim(PrimKind::Never)));

    // Test wrapper types
    let opt = BrrrType::option(BrrrType::BOOL);
    assert!(matches!(opt, BrrrType::Wrap(crate::types::WrapperKind::Option, _)));

    let arr = BrrrType::array(BrrrType::Numeric(NumericType::Int(IntType::I32)));
    assert!(matches!(arr, BrrrType::Wrap(crate::types::WrapperKind::Array, _)));

    // Test result type
    let res = BrrrType::result(BrrrType::STRING, BrrrType::BOOL);
    assert!(matches!(res, BrrrType::Result(_, _)));

    // Test tuple type
    let tup = BrrrType::tuple(vec![BrrrType::BOOL, BrrrType::STRING]);
    assert!(matches!(tup, BrrrType::Tuple(_)));
}

#[test]
fn test_type_predicates() {
    assert!(BrrrType::BOOL.is_primitive());
    assert!(BrrrType::Numeric(NumericType::Int(IntType::I64)).is_primitive());
    assert!(!BrrrType::option(BrrrType::BOOL).is_primitive());

    assert!(BrrrType::ref_shared(BrrrType::BOOL).is_reference());
    assert!(BrrrType::ref_mut(BrrrType::BOOL).is_reference());
    assert!(!BrrrType::BOOL.is_reference());
}

// ============================================================================
// Effect System Tests
// ============================================================================

#[test]
fn test_effect_row_creation() {
    let pure = EffectRow::pure();
    assert!(pure.is_empty());

    let total = EffectRow::total();
    // Total effect should exist
    assert!(matches!(total, EffectRow { .. }));
}

// ============================================================================
// Module System Tests
// ============================================================================

#[test]
fn test_module_operations() {
    let mut module = Module::new("test_module");

    assert!(module.is_empty());
    assert_eq!(module.depth(), 1);
    assert_eq!(module.full_path(), "test_module");

    module.add_declaration(Declaration::Function {
        name: "foo".to_string(),
        is_public: true,
        span: Range::SYNTHETIC,
    });

    assert!(!module.is_empty());
    assert!(module.find_declaration("foo").is_some());
    assert!(module.find_declaration("bar").is_none());
}

#[test]
fn test_module_submodules() {
    let mut parent = Module::new("parent");
    let child = Module::with_path("child", vec!["parent".to_string(), "child".to_string()]);

    parent.add_submodule(child);

    assert!(parent.find_submodule("child").is_some());
    assert!(parent.find_submodule("nonexistent").is_none());
}

#[test]
fn test_public_declarations_filter() {
    let module = create_module_with_declarations("filter_test");

    let public_decls: Vec<_> = module.public_declarations().collect();

    // Should have: MyStruct (public type), MAX_SIZE (public const), Display (public trait)
    // helper (private function) and Impl should not be in public list
    assert!(public_decls.len() >= 3);

    for decl in &public_decls {
        assert!(decl.is_public());
    }
}

// ============================================================================
// Import/Export Tests
// ============================================================================

#[test]
fn test_import_creation() {
    use crate::decl::{Import, ImportItem, ImportItems};

    let simple = Import::path(vec!["std".to_string(), "io".to_string()]);
    assert_eq!(simple.path_string(), "std::io");
    assert!(!simple.is_glob());

    let glob = Import::glob(vec!["crate".to_string(), "utils".to_string()]);
    assert!(glob.is_glob());

    let named = Import::named(
        vec!["std".to_string(), "collections".to_string()],
        vec![
            ImportItem::simple("HashMap"),
            ImportItem::aliased("HashSet", "Set"),
        ],
    );
    assert!(!named.is_glob());
    assert_eq!(named.items.items().len(), 2);
}

#[test]
fn test_export_creation() {
    use crate::decl::Export;

    let public = Export::public("my_function");
    assert_eq!(public.name(), Some("my_function"));
    assert!(!public.is_reexport());

    let reexport = Export::reexport("other", vec!["a".to_string(), "b".to_string()]);
    assert!(reexport.is_reexport());
    assert!(reexport.name().is_none());

    let reexport_all = Export::reexport_all("utils");
    assert!(reexport_all.is_reexport());
}

// ============================================================================
// Configuration Tests
// ============================================================================

#[test]
fn test_config_builders() {
    let config = CompilationConfig::default()
        .with_fail_fast()
        .with_verbose()
        .with_session_check()
        .with_contracts();

    assert!(config.fail_fast);
    assert!(config.verbose_diagnostics);
    assert!(config.session_check);
    assert!(config.verify_contracts);
    assert!(config.has_verification());
}

#[test]
fn test_config_presets() {
    let minimal = CompilationConfig::minimal();
    assert!(minimal.type_check);
    assert!(!minimal.effect_check);
    assert!(minimal.fail_fast);

    let full = CompilationConfig::full();
    assert!(full.type_check);
    assert!(full.effect_check);
    assert!(full.borrow_check);
    assert!(full.session_check);
    assert!(full.verify_contracts);
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_compilation_error_display() {
    use crate::inference::{TypeError, TypeErrorKind};
    use crate::pipeline::CompilationError;

    let err = CompilationError::Type(TypeError::new(TypeErrorKind::Mismatch, Range::SYNTHETIC));

    let display = format!("{}", err);
    assert!(display.contains("TYPE"), "Error display should contain type code");
}

#[test]
fn test_error_categories() {
    use crate::inference::{TypeError, TypeErrorKind};
    use crate::pipeline::{CompilationError, ErrorCategory};

    let type_err = CompilationError::Type(TypeError::new(TypeErrorKind::Mismatch, Range::SYNTHETIC));
    assert_eq!(type_err.category(), ErrorCategory::TypeSystem);
    assert_eq!(type_err.code(), "TYPE");
}

#[test]
fn test_warning_creation() {
    use crate::pipeline::{CompilationWarning, WarningKind};

    let warning = CompilationWarning::unused_variable("x", Range::SYNTHETIC);
    assert_eq!(warning.kind, WarningKind::UnusedVariable);
    assert!(warning.message.contains("x"));

    let unreachable = CompilationWarning::unreachable(Range::SYNTHETIC, "after return");
    assert_eq!(unreachable.kind, WarningKind::UnreachableCode);
}

// ============================================================================
// Content Hash Tests
// ============================================================================

#[test]
fn test_content_hash_stability() {
    let module1 = create_test_brrr_module("hash_test");
    let module2 = create_test_brrr_module("hash_test");

    let encoder1 = BrrrEncoder::from_module(module1);
    let encoder2 = BrrrEncoder::from_module(module2);

    let hash1 = encoder1.content_hash();
    let hash2 = encoder2.content_hash();

    assert_eq!(hash1, hash2, "Same content should produce same hash");
}

#[test]
fn test_content_hash_varies_with_content() {
    let module1 = create_test_brrr_module("hash_test_1");
    let module2 = create_test_brrr_module("hash_test_2");

    let encoder1 = BrrrEncoder::from_module(module1);
    let encoder2 = BrrrEncoder::from_module(module2);

    let hash1 = encoder1.content_hash();
    let hash2 = encoder2.content_hash();

    assert_ne!(hash1, hash2, "Different content should produce different hash");
}

// ============================================================================
// Decoder API Tests
// ============================================================================

#[test]
fn test_decoder_accessors() {
    let original = create_test_brrr_module("decoder_test");

    let mut buffer: Vec<u8> = Vec::new();
    let encoder = BinaryEncoder::new();
    encoder.encode(&original, &mut buffer).unwrap();

    let decoder = BrrrDecoder::decode_binary(&buffer[..]).unwrap();

    // Test get_type
    assert!(decoder.get_type(0).is_some());
    assert!(decoder.get_type(1).is_some());
    assert!(decoder.get_type(2).is_some());
    assert!(decoder.get_type(100).is_none());

    // Test verify_hash
    let hash = BrrrEncoder::from_module(original).content_hash();
    assert!(decoder.verify_hash(&hash));

    let wrong_hash = [0u8; 16];
    assert!(!decoder.verify_hash(&wrong_hash));
}

// ============================================================================
// Pass ID Tests
// ============================================================================

#[test]
fn test_pass_id_names() {
    use crate::pipeline::PassId;

    assert_eq!(PassId::TypeInference.name(), "type inference");
    assert_eq!(PassId::EffectInference.name(), "effect inference");
    assert_eq!(PassId::BorrowCheck.name(), "borrow checking");
    assert_eq!(PassId::SessionCheck.name(), "session type checking");
    assert_eq!(PassId::ContractVerification.name(), "contract verification");
}
