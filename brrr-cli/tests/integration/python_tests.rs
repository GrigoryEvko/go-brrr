//! Comprehensive Python support integration tests.
//!
//! Tests all Python language features: decorators, async/await, generators,
//! match/case, walrus operator, comprehensions, type annotations, imports,
//! dead code detection, and security scanning.

use std::path::PathBuf;

use brrr::ast::extractor::AstExtractor;
use brrr::security::{scan_security, SecurityConfig};

fn python_fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("python")
        .join(name)
}

fn extract_python(name: &str) -> brrr::ast::types::ModuleInfo {
    let path = python_fixture(name);
    AstExtractor::extract_file(&path).expect("Failed to extract Python file")
}

// =============================================================================
// Function Extraction Tests
// =============================================================================

#[test]
fn python_extracts_module_docstring() {
    let module = extract_python("comprehensive.py");
    assert!(module.docstring.is_some(), "Should extract module docstring");
    assert!(
        module.docstring.as_ref().unwrap().contains("comprehensive"),
        "Docstring should contain 'comprehensive'"
    );
}

#[test]
fn python_extracts_decorated_functions() {
    let module = extract_python("comprehensive.py");

    // prop_example has @property decorator
    let prop = module.functions.iter().find(|f| f.name == "prop_example");
    assert!(prop.is_some(), "Should find prop_example");
    assert!(
        prop.unwrap().decorators.contains(&"property".to_string()),
        "prop_example should have @property decorator"
    );

    // static_example has @staticmethod decorator
    let stat = module.functions.iter().find(|f| f.name == "static_example");
    assert!(stat.is_some(), "Should find static_example");
    assert!(
        stat.unwrap()
            .decorators
            .contains(&"staticmethod".to_string()),
        "static_example should have @staticmethod decorator"
    );
}

#[test]
fn python_extracts_class_with_methods() {
    let module = extract_python("comprehensive.py");

    let class = module.classes.iter().find(|c| c.name == "MyClass");
    assert!(class.is_some(), "Should find MyClass");
    let class = class.unwrap();

    // Check methods
    let method_names: Vec<&str> = class.methods.iter().map(|m| m.name.as_str()).collect();
    assert!(
        method_names.contains(&"__init__"),
        "Should have __init__, got: {:?}",
        method_names
    );
    assert!(
        method_names.contains(&"value"),
        "Should have value property"
    );
    assert!(method_names.contains(&"create"), "Should have create");
    assert!(
        method_names.contains(&"from_dict"),
        "Should have from_dict"
    );
    assert!(
        method_names.contains(&"regular_method"),
        "Should have regular_method"
    );

    // Check decorator on property method
    let value_method = class.methods.iter().find(|m| m.name == "value").unwrap();
    assert!(
        value_method.decorators.contains(&"property".to_string()),
        "value method should have @property"
    );

    // Check decorator on staticmethod
    let create_method = class.methods.iter().find(|m| m.name == "create").unwrap();
    assert!(
        create_method
            .decorators
            .contains(&"staticmethod".to_string()),
        "create should have @staticmethod"
    );

    // Check decorator on classmethod
    let from_dict = class.methods.iter().find(|m| m.name == "from_dict").unwrap();
    assert!(
        from_dict.decorators.contains(&"classmethod".to_string()),
        "from_dict should have @classmethod"
    );
}

#[test]
fn python_extracts_async_functions() {
    let module = extract_python("comprehensive.py");

    let fetch = module.functions.iter().find(|f| f.name == "fetch_data");
    assert!(fetch.is_some(), "Should find fetch_data");
    assert!(
        fetch.unwrap().is_async,
        "fetch_data should be marked as async"
    );
}

#[test]
fn python_extracts_generator_functions() {
    let module = extract_python("comprehensive.py");

    // fibonacci is a generator (contains yield)
    let fib = module.functions.iter().find(|f| f.name == "fibonacci");
    assert!(fib.is_some(), "Should find fibonacci");

    // chain uses yield from
    let chain_fn = module.functions.iter().find(|f| f.name == "chain");
    assert!(chain_fn.is_some(), "Should find chain (yield from)");
}

#[test]
fn python_extracts_nested_functions() {
    let module = extract_python("comprehensive.py");

    let inner = module.functions.iter().find(|f| f.name == "inner");
    assert!(inner.is_some(), "Should find nested function 'inner'");
    assert!(
        inner
            .unwrap()
            .decorators
            .iter()
            .any(|d| d.starts_with("nested_in:")),
        "inner should have nested_in decorator"
    );
}

#[test]
fn python_extracts_complex_type_annotations() {
    let module = extract_python("comprehensive.py");

    let func = module
        .functions
        .iter()
        .find(|f| f.name == "complex_types");
    assert!(func.is_some(), "Should find complex_types");
    let func = func.unwrap();

    // Check return type
    assert_eq!(
        func.return_type,
        Some("dict[str, list[int]]".to_string()),
        "Return type should be dict[str, list[int]]"
    );

    // Check params include typed *args and **kwargs
    let params_str = func.params.join(", ");
    assert!(
        params_str.contains("*args: tuple[str, ...]"),
        "Should have typed *args, got: {}",
        params_str
    );
    assert!(
        params_str.contains("**kwargs: dict[str, Any]"),
        "Should have typed **kwargs, got: {}",
        params_str
    );

    // Check forward reference handling (quoted type)
    assert!(
        params_str.contains("Callable[[int], bool]"),
        "Forward ref should be unquoted, got: {}",
        params_str
    );
}

#[test]
fn python_extracts_imports_with_type_checking() {
    let module = extract_python("comprehensive.py");

    // Regular imports
    let os_import = module.imports.iter().find(|i| i.module == "os");
    assert!(os_import.is_some(), "Should find 'import os'");

    // From imports
    let typing_import = module.imports.iter().find(|i| i.module == "typing");
    assert!(typing_import.is_some(), "Should find 'from typing import'");
    let typing_import = typing_import.unwrap();
    assert!(
        typing_import.names.contains(&"Optional".to_string()),
        "typing import should include Optional"
    );
    assert!(
        typing_import.names.contains(&"TYPE_CHECKING".to_string()),
        "typing import should include TYPE_CHECKING"
    );

    // TYPE_CHECKING import
    let od_import = module.imports.iter().find(|i| i.module == "collections");
    assert!(
        od_import.is_some(),
        "Should find TYPE_CHECKING guarded import from collections"
    );
}

// =============================================================================
// CFG Tests
// =============================================================================

#[test]
fn python_cfg_complex_control_flow() {
    let path = python_fixture("comprehensive.py");
    let source = std::fs::read(&path).unwrap();

    let registry = brrr::lang::LanguageRegistry::global();
    let lang = registry.detect_language(&path).unwrap();

    let mut parser = lang.parser().unwrap();
    let tree = parser.parse(&source, None).unwrap();

    // Find complex_control_flow function
    let func_node = find_function_node(&tree, &source, "complex_control_flow");
    assert!(func_node.is_some(), "Should find complex_control_flow");

    let cfg = lang.build_cfg(func_node.unwrap(), &source).unwrap();

    // Should have multiple blocks (if/elif/else/for/while/try/except)
    assert!(
        cfg.blocks.len() > 10,
        "Complex control flow should have >10 blocks, got {}",
        cfg.blocks.len()
    );

    // Cyclomatic complexity should be high
    let complexity = cfg.decision_points + 1;
    assert!(
        complexity >= 7,
        "Complexity should be >= 7 (if + elif + for + if + 2 excepts + while), got {}",
        complexity
    );
}

#[test]
fn python_cfg_match_case() {
    let path = python_fixture("comprehensive.py");
    let source = std::fs::read(&path).unwrap();

    let registry = brrr::lang::LanguageRegistry::global();
    let lang = registry.detect_language(&path).unwrap();

    let mut parser = lang.parser().unwrap();
    let tree = parser.parse(&source, None).unwrap();

    let func_node = find_function_node(&tree, &source, "process_command");
    assert!(func_node.is_some(), "Should find process_command");

    let cfg = lang.build_cfg(func_node.unwrap(), &source).unwrap();

    // match/case with 3 cases + 1 guard should have several decision points
    assert!(
        cfg.decision_points >= 3,
        "Match/case should have >= 3 decision points (3 cases + guard), got {}",
        cfg.decision_points
    );
}

#[test]
fn python_cfg_exception_handling() {
    let path = python_fixture("comprehensive.py");
    let source = std::fs::read(&path).unwrap();

    let registry = brrr::lang::LanguageRegistry::global();
    let lang = registry.detect_language(&path).unwrap();

    let mut parser = lang.parser().unwrap();
    let tree = parser.parse(&source, None).unwrap();

    let func_node = find_function_node(&tree, &source, "exception_handling");
    assert!(func_node.is_some(), "Should find exception_handling");

    let cfg = lang.build_cfg(func_node.unwrap(), &source).unwrap();

    // Should have blocks for try, each except, else, finally
    assert!(
        cfg.blocks.len() >= 5,
        "Exception handling should have >= 5 blocks, got {}",
        cfg.blocks.len()
    );
}

// =============================================================================
// DFG Tests
// =============================================================================

#[test]
fn python_dfg_walrus_operator() {
    let path = python_fixture("comprehensive.py");
    let source = std::fs::read(&path).unwrap();

    let registry = brrr::lang::LanguageRegistry::global();
    let lang = registry.detect_language(&path).unwrap();

    let mut parser = lang.parser().unwrap();
    let tree = parser.parse(&source, None).unwrap();

    let func_node = find_function_node(&tree, &source, "process_data");
    assert!(func_node.is_some(), "Should find process_data");

    let dfg = lang.build_dfg(func_node.unwrap(), &source).unwrap();

    // n should be defined by walrus operator
    assert!(
        dfg.definitions.contains_key("n"),
        "DFG should track 'n' from walrus operator, got keys: {:?}",
        dfg.definitions.keys().collect::<Vec<_>>()
    );

    // y should be defined by walrus in comprehension
    assert!(
        dfg.definitions.contains_key("y"),
        "DFG should track 'y' from walrus in comprehension"
    );

    // line should be defined by walrus in while
    assert!(
        dfg.definitions.contains_key("line"),
        "DFG should track 'line' from walrus in while"
    );
}

// =============================================================================
// Security Tests
// =============================================================================

#[test]
fn python_security_detects_eval_exec() {
    let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("python");

    let config = SecurityConfig::default();
    let report = scan_security(&fixture_dir, &config).unwrap();

    // Should detect eval and exec as code injection
    let code_injection_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| f.title.contains("Code Injection") || f.title.contains("Command Injection"))
        .filter(|f| {
            f.title.contains("eval") || f.title.contains("exec") || f.title.contains("system")
        })
        .collect();

    assert!(
        code_injection_findings.len() >= 3,
        "Should detect eval, exec, and os.system, found {} findings: {:?}",
        code_injection_findings.len(),
        code_injection_findings
            .iter()
            .map(|f| &f.title)
            .collect::<Vec<_>>()
    );
}

#[test]
fn python_security_detects_pickle() {
    let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("python");

    let config = SecurityConfig::default();
    let report = scan_security(&fixture_dir, &config).unwrap();

    let pickle_findings: Vec<_> = report
        .findings
        .iter()
        .filter(|f| {
            f.title.to_lowercase().contains("pickle")
                || f.title.to_lowercase().contains("deserialization")
        })
        .collect();

    assert!(
        !pickle_findings.is_empty(),
        "Should detect pickle.loads as unsafe deserialization"
    );
}

// =============================================================================
// Structure Tests
// =============================================================================

#[test]
fn python_structure_finds_all_functions() {
    let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("python");

    let result =
        brrr::ast::code_structure(fixture_dir.to_str().unwrap(), Some("python"), 0, false)
            .unwrap();

    // Should find a good number of top-level functions
    assert!(
        result.functions.len() >= 10,
        "Should find >= 10 functions, got {}",
        result.functions.len()
    );

    // Check specific functions exist
    let names: Vec<&str> = result.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(
        names.contains(&"fetch_data"),
        "Should find async function fetch_data"
    );
    assert!(
        names.contains(&"fibonacci"),
        "Should find generator fibonacci"
    );
    assert!(
        names.contains(&"process_command"),
        "Should find match/case function"
    );
    assert!(
        names.contains(&"complex_types"),
        "Should find typed function"
    );
}

#[test]
fn python_structure_finds_classes() {
    let fixture_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("python");

    let result =
        brrr::ast::code_structure(fixture_dir.to_str().unwrap(), Some("python"), 0, false)
            .unwrap();

    assert!(
        !result.classes.is_empty(),
        "Should find at least one class"
    );

    let class = result.classes.iter().find(|c| c.name == "MyClass");
    assert!(class.is_some(), "Should find MyClass");
    assert!(
        class.unwrap().method_count >= 4,
        "MyClass should have >= 4 methods"
    );
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Find a function node by name in a parsed tree.
fn find_function_node<'a>(
    tree: &'a tree_sitter::Tree,
    source: &[u8],
    name: &str,
) -> Option<tree_sitter::Node<'a>> {
    find_function_node_recursive(tree.root_node(), source, name)
}

fn find_function_node_recursive<'a>(
    node: tree_sitter::Node<'a>,
    source: &[u8],
    name: &str,
) -> Option<tree_sitter::Node<'a>> {
    if node.kind() == "function_definition" {
        // Check the name child
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" {
                let text = std::str::from_utf8(&source[child.start_byte()..child.end_byte()])
                    .unwrap_or("");
                if text == name {
                    return Some(node);
                }
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if let Some(found) = find_function_node_recursive(child, source, name) {
            return Some(found);
        }
    }

    None
}
