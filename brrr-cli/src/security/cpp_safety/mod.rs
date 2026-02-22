//! C++26 Safety Axiom Analyzer.
//!
//! Enforces 7 safety axioms plus performance and anti-pattern rules (62+ rules total).
//!
//! **Safety Axioms** (from the Crucible model):
//! - **MemSafe** (Critical): No use-after-free, double-free, buffer overflow
//! - **TypeSafe** (High): Type system prevents category errors
//! - **NullSafe** (Medium): No null pointer dereference
//! - **RaceFree** (High): No data races
//! - **LeakFree** (Low): No resource leaks
//! - **DetDrop** (Low): Deterministic destruction order
//! - **InitSafe** (Medium): Every value initialized before first read
//!
//! **Supplementary categories**:
//! - **Performance**: Performance anti-patterns (false sharing, unnecessary allocations)
//! - **AntiPattern**: C++ anti-patterns (RTTI abuse, exception misuse)
//!
//! Detection uses tree-sitter AST analysis combined with text pattern matching
//! for robust cross-grammar-version support.

mod checkers;
mod helpers;
mod lifetime;
mod pattern_match;
pub(crate) mod rules;
mod type_safety_ext;
mod types;
mod unsafe_ctx;

#[cfg(test)]
mod tests;

pub use types::*;

use std::collections::HashMap;
use std::path::Path;

use rayon::prelude::*;

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;

// =============================================================================
// Scanner Entry Points
// =============================================================================

/// Scan a directory or file for C++ safety axiom violations.
pub fn scan_cpp_safety(path: &Path, config: &CppSafetyConfig) -> Result<CppSafetyReport> {
    if path.is_file() {
        let findings = scan_file_cpp_safety(path, config)?;
        let report = build_report(findings, 1);
        return Ok(report);
    }

    let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;

    let mut cfg = ScanConfig::default();
    cfg.extensions = vec![
        ".cpp".into(), ".cc".into(), ".cxx".into(),
        ".hpp".into(), ".hh".into(), ".hxx".into(),
        ".h".into(),
        ".cu".into(), ".cuh".into(),
        ".c".into(),
    ];

    let result = scanner.scan_with_config(&cfg)?;
    let files_scanned = result.files.len();

    let all_findings: Vec<Vec<CppSafetyFinding>> = result
        .files
        .par_iter()
        .filter_map(|file| scan_file_cpp_safety(file, config).ok())
        .collect();

    let findings: Vec<CppSafetyFinding> = all_findings.into_iter().flatten().collect();
    Ok(build_report(findings, files_scanned))
}

/// Scan a single file for C++ safety axiom violations.
pub fn scan_file_cpp_safety(
    path: &Path,
    config: &CppSafetyConfig,
) -> Result<Vec<CppSafetyFinding>> {
    let registry = LanguageRegistry::global();

    let lang = registry.detect_language(path);
    let lang = match lang {
        Some(l) if l.name() == "c" || l.name() == "cpp" => l,
        _ => return Ok(Vec::new()),
    };

    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
    let source_str = std::str::from_utf8(&source).unwrap_or("");

    let mut parser = lang.parser()?;
    let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
        file: path.display().to_string(),
        message: "Failed to parse file".to_string(),
    })?;

    let file_path = path.to_string_lossy().to_string();
    let is_cpp = lang.name() == "cpp"
        || path.extension().map_or(false, |ext| {
            matches!(ext.to_str(), Some("cpp" | "cc" | "cxx" | "hpp" | "hh" | "hxx" | "cu" | "cuh"))
        });

    let mut findings = Vec::new();

    // Run all checkers
    checkers::check_init_safe(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;
    checkers::check_type_safe(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    checkers::check_null_safe(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;
    checkers::check_mem_safe(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    checkers::check_race_free(source_str, &file_path, is_cpp, &mut findings);
    checkers::check_leak_free(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    checkers::check_det_drop(source_str, &file_path, &mut findings);
    checkers::check_performance(source_str, &file_path, &mut findings);
    checkers::check_anti_patterns(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    lifetime::check_lifetime_safety(source_str, &file_path, is_cpp, &mut findings);
    lifetime::check_iterator_invalidation(source_str, &file_path, is_cpp, &mut findings);
    lifetime::check_initializer_list_dangling(source_str, &file_path, is_cpp, &mut findings);
    lifetime::check_return_ref_to_local(source_str, &file_path, is_cpp, &mut findings);
    lifetime::check_lambda_ref_escape(source_str, &file_path, is_cpp, &mut findings);
    unsafe_ctx::check_unsafe_context(source_str, &file_path, is_cpp, &mut findings);
    type_safety_ext::check_type_safety_ext(source_str, &file_path, is_cpp, &mut findings);
    pattern_match::check_pattern_match(source_str, &file_path, is_cpp, &mut findings);

    // Apply filters
    let filtered = findings
        .into_iter()
        .filter(|f| {
            if let Some(ref ax) = config.axiom_filter {
                if f.axiom != *ax {
                    return false;
                }
            }
            if f.severity < config.min_severity {
                return false;
            }
            if config.profile == CppSafetyProfile::Crucible {
                if matches!(f.axiom, SafetyAxiom::Performance | SafetyAxiom::AntiPattern) {
                    return false;
                }
            }
            true
        })
        .collect();

    Ok(filtered)
}

/// Build a report from collected findings.
fn build_report(findings: Vec<CppSafetyFinding>, files_scanned: usize) -> CppSafetyReport {
    let mut axiom_summary: HashMap<String, usize> = HashMap::new();
    for f in &findings {
        *axiom_summary.entry(f.axiom.to_string()).or_insert(0) += 1;
    }
    CppSafetyReport {
        findings,
        files_scanned,
        axiom_summary,
    }
}
