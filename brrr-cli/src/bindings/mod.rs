//! Cross-language binding detection engine.
//!
//! Detects binding declarations across language boundaries (pybind11, ctypes,
//! Rust FFI, CGo, JNI, napi-rs, CUDA dispatch, TORCH_LIBRARY) and produces:
//! - Standalone JSON reports via `brrr bindings scan`
//! - Synthetic CallEdge injection into the callgraph for dead/impact/context

pub mod detector;
pub mod detectors;
pub mod inject;
pub mod registry;
pub mod resolve;
pub mod types;

use std::path::PathBuf;

use rayon::prelude::*;

use crate::bindings::registry::BindingRegistry;
use crate::bindings::resolve::resolve_bindings;
use crate::bindings::types::{BindingDeclaration, BindingReport, FileBindings};
use crate::callgraph::indexer::FunctionIndex;
use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::Result;
use crate::lang::registry::LanguageRegistry;

/// Scan a project for all cross-language bindings.
///
/// This is the standalone entry point (used by `brrr bindings scan`).
/// Builds its own file list and function index.
pub fn scan_bindings(
    path: &str,
    lang_filter: Option<&str>,
    no_ignore: bool,
) -> Result<BindingReport> {
    let scanner = ProjectScanner::new(path)?;

    let mut config = match lang_filter {
        Some(l) if l != "all" => ScanConfig::for_language(l),
        _ => ScanConfig::default(),
    };
    config.no_ignore = no_ignore;

    let scan_result = scanner.scan_with_config(&config)?;
    let files = scan_result.files;

    // Build function index for cross-file resolution
    let index = FunctionIndex::build(&files)?;

    scan_bindings_from_files(&files, &index)
}

/// Scan pre-discovered files for bindings using an existing function index.
///
/// This is the callgraph-integration entry point — avoids duplicate scanning
/// when the callgraph builder already has the file list and index.
pub fn scan_bindings_from_files(
    files: &[PathBuf],
    index: &FunctionIndex,
) -> Result<BindingReport> {
    let binding_registry = BindingRegistry::global();
    let lang_registry = LanguageRegistry::global();

    // Phase 1: Parallel per-file detection
    let file_results: Vec<FileBindings> = files
        .par_iter()
        .filter_map(|path| scan_file_bindings(path, binding_registry, lang_registry))
        .collect();

    let files_with_bindings = file_results.len();

    // Phase 2: Flatten all declarations
    let mut declarations: Vec<BindingDeclaration> = file_results
        .into_iter()
        .flat_map(|fb| fb.declarations)
        .collect();

    // Phase 3: Cross-file resolution
    resolve_bindings(&mut declarations, index);

    // Phase 4: Build report
    Ok(BindingReport::from_declarations(
        declarations,
        files.len(),
        files_with_bindings,
    ))
}

/// Scan a single file for binding declarations.
fn scan_file_bindings(
    path: &PathBuf,
    binding_registry: &BindingRegistry,
    lang_registry: &LanguageRegistry,
) -> Option<FileBindings> {
    // Detect language
    let lang = lang_registry.detect_language(path)?;
    let language = lang.name();

    // Get applicable detectors
    let detectors = binding_registry.detectors_for_language(language);
    if detectors.is_empty() {
        return None;
    }

    // Read source
    let source = std::fs::read(path).ok()?;

    // Quick check: any detector interested?
    let interested: Vec<_> = detectors
        .iter()
        .filter(|d| d.quick_check(&source, language))
        .collect();
    if interested.is_empty() {
        return None;
    }

    // Parse once with cached tree-sitter parser
    let mut parser = lang.parser_for_path(path).ok()?;
    let tree = parser.parse(&source, None)?;

    // Run all interested detectors
    let mut declarations = Vec::new();
    let file_str = path.display().to_string();
    for detector in interested {
        if let Ok(mut decls) = detector.detect(&tree, &source, &file_str, language) {
            declarations.append(&mut decls);
        }
    }

    if declarations.is_empty() {
        return None;
    }

    Some(FileBindings {
        file_path: file_str,
        language: language.to_string(),
        declarations,
    })
}
