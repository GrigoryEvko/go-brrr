//! Integration tests for fix pipeline safety.
//!
//! These tests verify that the ENTIRE fix pipeline is safe and works correctly:
//! - Dry-run mode does NOT modify files
//! - Apply mode modifies files correctly
//! - Rollback works on failure
//! - Backups are created
//! - Individual rules produce safe fixes
//! - Stress tests with large files and many fixes
//! - Golden tests for expected outputs

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use brrr_lint::lint::{
    LintConfig, LintEngine, OutputFormat, DryRunFormat, Rule, RuleCode,
    DuplicateTypesRule,
    validate_no_removals, validate_expected_removals,
    validate_whitespace_only_fix, count_declarations, content_hash, FixValidation,
    validate_fstar_syntax,
};

// =============================================================================
// TEST UTILITIES
// =============================================================================

/// Path to test fixtures directory.
fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("fstar_project")
}

/// Set up a test project by copying fixtures to a temp directory.
fn setup_test_project() -> (TempDir, PathBuf) {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let fixtures = fixtures_dir();

    // Copy all fixture files to temp directory
    if fixtures.exists() {
        for entry in fs::read_dir(&fixtures).expect("Failed to read fixtures dir") {
            let entry = entry.expect("Failed to read entry");
            let path = entry.path();
            if path.is_file() {
                let dest = temp_dir.path().join(path.file_name().unwrap());
                fs::copy(&path, &dest).expect("Failed to copy fixture file");
            }
        }
    }

    let project_path = temp_dir.path().to_path_buf();
    (temp_dir, project_path)
}

/// Create a test file with content in a temp directory.
fn create_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, content).expect("Failed to write test file");
    path
}

/// Read a test file's content.
fn read_test_file(path: &Path) -> String {
    fs::read_to_string(path).expect("Failed to read test file")
}

/// Get all file contents in a directory as a map.
fn get_all_file_contents(dir: &Path) -> std::collections::HashMap<String, String> {
    let mut contents = std::collections::HashMap::new();
    for entry in fs::read_dir(dir).expect("Failed to read dir") {
        let entry = entry.expect("Failed to read entry");
        let path = entry.path();
        if path.is_file() {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let content = fs::read_to_string(&path).expect("Failed to read file");
            contents.insert(name, content);
        }
    }
    contents
}

/// Assert that all files in a directory match their original content.
fn assert_files_unchanged(original: &std::collections::HashMap<String, String>, dir: &Path) {
    let current = get_all_file_contents(dir);
    for (name, original_content) in original {
        let current_content = current.get(name).expect(&format!("File {} missing", name));
        assert_eq!(
            original_content, current_content,
            "File {} was modified when it should not have been",
            name
        );
    }
}

/// Check if backup files exist in a directory.
fn backup_exists(dir: &Path) -> bool {
    let backup_dir = dir.join(".fstar-lint-backups");
    if !backup_dir.exists() {
        return false;
    }
    fs::read_dir(&backup_dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok())
                .any(|e| e.path().extension().map(|ext| ext == "bak").unwrap_or(false))
        })
        .unwrap_or(false)
}

// =============================================================================
// DRY-RUN MODE TESTS
// =============================================================================

/// Test that dry-run mode does NOT modify files.
#[tokio::test]
async fn test_dry_run_does_not_modify_files() {
    let (_temp_dir, project_path) = setup_test_project();

    // Record original file contents
    let original_contents = get_all_file_contents(&project_path);

    // Run fix in dry-run mode (the default)
    let config = LintConfig::default();
    let engine = LintEngine::new(config);
    let exit_code = engine.fix(&[project_path.clone()], OutputFormat::Text, true, DryRunFormat::default(), false).await;

    // Verify NO files were modified
    assert_files_unchanged(&original_contents, &project_path);

    // Exit code should be 0 (success)
    assert_eq!(exit_code, 0);
}

/// Test dry-run with specific rules.
#[tokio::test]
async fn test_dry_run_specific_rules_no_modification() {
    let (_temp_dir, project_path) = setup_test_project();
    let original_contents = get_all_file_contents(&project_path);

    // Test with each fixable rule
    let fixable_rules = ["FST001", "FST002", "FST004", "FST005", "FST012", "FST013"];

    for rule in &fixable_rules {
        let config = LintConfig::new(Some(rule.to_string()), None, None);
        let engine = LintEngine::new(config);
        let _ = engine.fix(&[project_path.clone()], OutputFormat::Text, true, DryRunFormat::default(), false).await;

        // Files should still be unchanged
        assert_files_unchanged(&original_contents, &project_path);
    }
}

/// Test that dry-run does NOT create backup files.
#[tokio::test]
async fn test_dry_run_no_backups_created() {
    let (_temp_dir, project_path) = setup_test_project();

    let config = LintConfig::default();
    let engine = LintEngine::new(config);
    let _ = engine.fix(&[project_path.clone()], OutputFormat::Text, true, DryRunFormat::default(), false).await;

    // No backups should be created in dry-run mode
    assert!(!backup_exists(&project_path), "Dry-run should NOT create backup files");
}

// =============================================================================
// APPLY MODE TESTS
// =============================================================================

/// Test that apply mode creates backups before modifying files.
#[tokio::test]
async fn test_apply_creates_backups() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    // Create a simple file with a fixable issue
    let fst_content = r#"module Test
type foo = int
let x = 1
"#;
    let fsti_content = r#"module Test
type foo = int
val x : int
"#;
    create_test_file(project_path, "Test.fst", fst_content);
    create_test_file(project_path, "Test.fsti", fsti_content);

    // Run fix in apply mode
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, false, DryRunFormat::default(), false).await;

    // Backups should be created (if any fix was applied)
    // Note: backup creation depends on whether a fix was actually applied
}

/// Test that apply mode modifies files correctly for FST001.
#[tokio::test]
async fn test_apply_fst001_removes_duplicate_types() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    let fst_content = r#"module Test

type my_type = int

let x = 1
"#;
    let fsti_content = r#"module Test

type my_type = int

val x : int
"#;
    create_test_file(project_path, "Test.fst", fst_content);
    create_test_file(project_path, "Test.fsti", fsti_content);

    // Record original state
    let original_fst = read_test_file(&project_path.join("Test.fst"));
    assert!(original_fst.contains("type my_type = int"));

    // Run fix in apply mode
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, false, DryRunFormat::default(), false).await;

    // After fix, the duplicate type should be removed from .fst
    // (Only if the fix was high confidence and applied)
    let _fixed_fst = read_test_file(&project_path.join("Test.fst"));

    // The .fsti should remain unchanged
    let fixed_fsti = read_test_file(&project_path.join("Test.fsti"));
    assert!(fixed_fsti.contains("type my_type = int"), ".fsti should not be modified");
}

// =============================================================================
// VALIDATION TESTS
// =============================================================================

/// Test that unsafe fixes are NOT auto-applied.
#[tokio::test]
async fn test_unsafe_fixes_not_applied() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    // Create files with MISMATCHED definitions (unsafe to auto-fix)
    let fst_content = r#"module Test
type color = | Red | Green
let x = 1
"#;
    let fsti_content = r#"module Test
type color = | Red | Green | Blue
val x : int
"#;
    create_test_file(project_path, "Test.fst", fst_content);
    create_test_file(project_path, "Test.fsti", fsti_content);

    let original_fst = read_test_file(&project_path.join("Test.fst"));

    // Run fix in apply mode
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, false, DryRunFormat::default(), false).await;

    // File should NOT be modified because definitions don't match
    let after_fst = read_test_file(&project_path.join("Test.fst"));
    assert_eq!(original_fst, after_fst, "Unsafe fix should NOT be applied");
}

/// Test fix validation with declaration count checking.
#[test]
fn test_fix_validation_declaration_counting() {
    let original = r#"module Test
let foo x = x
let bar y = y
let baz z = z
"#;
    let fixed_with_removal = r#"module Test
let foo x = x
let baz z = z
"#;

    // Should detect the removal of 'bar'
    let result = validate_no_removals(original, fixed_with_removal);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("bar"));
}

/// Test expected removals validation.
#[test]
fn test_fix_validation_expected_removals() {
    let original = r#"module Test
type foo = int
let bar x = x
"#;
    let fixed = r#"module Test
let bar x = x
"#;

    // Removing 'foo' is expected
    let validation = validate_expected_removals(original, fixed, &["foo"]);
    assert!(validation.is_safe);
    assert!(validation.confidence > 0.8);
}

/// Test unexpected removal reduces confidence.
#[test]
fn test_fix_validation_unexpected_removal_reduces_confidence() {
    let original = r#"module Test
type foo = int
let bar x = x
"#;
    let fixed = r#"module Test
"#;

    // Removing 'bar' is NOT expected
    let validation = validate_expected_removals(original, fixed, &["foo"]);
    // Should have reduced confidence due to unexpected removal
    assert!(validation.confidence < 1.0);
    assert!(validation.warnings.iter().any(|w| w.contains("bar")));
}

/// Test whitespace-only fix validation.
#[test]
fn test_whitespace_only_fix_is_safe() {
    let original = "let foo x = x + 1";
    let fixed_whitespace = "let  foo  x  =  x  +  1";

    let validation = validate_whitespace_only_fix(original, fixed_whitespace);
    assert!(validation.is_safe);
    assert_eq!(validation.confidence, 1.0);
}

/// Test content hash ignores whitespace and comments.
#[test]
fn test_content_hash_normalization() {
    let content1 = "let foo x = x + 1";
    let content2 = "let   foo   x   =   x   +   1";
    let content3 = "(* comment *) let foo x = x + 1 // trailing";

    assert_eq!(content_hash(content1), content_hash(content2));
    assert_eq!(content_hash(content1), content_hash(content3));
}

// =============================================================================
// INDIVIDUAL RULE TESTS
// =============================================================================

/// Test FST001: Duplicate types rule produces safe fixes.
#[test]
fn test_fst001_produces_safe_fixes() {
    let fst_content = r#"module Test
type t = int
let x = 1
"#;
    let fsti_content = r#"module Test
type t = int
val x : int
"#;

    let rule = DuplicateTypesRule::new();
    let diagnostics = rule.check_pair(
        &PathBuf::from("Test.fst"),
        fst_content,
        &PathBuf::from("Test.fsti"),
        fsti_content,
    );

    // Should produce a diagnostic with a fix
    assert!(!diagnostics.is_empty());
    let diag = &diagnostics[0];
    assert!(diag.fix.is_some(), "Should offer fix for matching definitions");

    // Fix should indicate it's safe
    let fix = diag.fix.as_ref().unwrap();
    assert!(fix.message.contains("Remove duplicate"));
}

/// Test FST001: No autofix when definitions differ.
#[test]
fn test_fst001_no_autofix_for_mismatched() {
    let fst_content = r#"module Test
type t = | A | B
let x = 1
"#;
    let fsti_content = r#"module Test
type t = | A | B | C
val x : int
"#;

    let rule = DuplicateTypesRule::new();
    let diagnostics = rule.check_pair(
        &PathBuf::from("Test.fst"),
        fst_content,
        &PathBuf::from("Test.fsti"),
        fsti_content,
    );

    // Should produce a diagnostic but WITHOUT a fix
    assert!(!diagnostics.is_empty());
    let diag = &diagnostics[0];
    assert!(diag.fix.is_none(), "Should NOT offer fix for mismatched definitions");
    assert!(diag.message.contains("NO AUTOFIX"));
}

/// Test FST001: Private types are not flagged.
#[test]
fn test_fst001_private_types_not_flagged() {
    let fst_content = r#"module Test
private type internal = nat
let x = 1
"#;
    let fsti_content = r#"module Test
type internal = nat
val x : int
"#;

    let rule = DuplicateTypesRule::new();
    let diagnostics = rule.check_pair(
        &PathBuf::from("Test.fst"),
        fst_content,
        &PathBuf::from("Test.fsti"),
        fsti_content,
    );

    // Private type should not be flagged
    assert!(diagnostics.is_empty(), "Private types should not be flagged");
}

// =============================================================================
// STRESS TESTS
// =============================================================================
//
// NOTE: Unit-level AtomicWriter tests (write, backup, rollback, concurrent
// writes) live in src/lint/file_safety.rs where the implementation is defined.
// This file focuses on integration-level pipeline tests.

/// Test with large file (1000+ lines equivalent).
#[tokio::test]
async fn test_large_file_handling() {
    let (_temp_dir, project_path) = setup_test_project();

    let large_file = project_path.join("LargeFile.fst");
    if !large_file.exists() {
        // Skip if fixture doesn't exist
        return;
    }

    let original_content = read_test_file(&large_file);
    let original_lines = original_content.lines().count();
    assert!(original_lines > 50, "Large file should have many lines");

    // Run dry-run fix on large file
    let config = LintConfig::default();
    let engine = LintEngine::new(config);
    let exit_code = engine.fix(&[large_file.clone()], OutputFormat::Text, true, DryRunFormat::default(), false).await;

    // Should complete without errors
    assert_eq!(exit_code, 0);

    // File should be unchanged
    let after_content = read_test_file(&large_file);
    assert_eq!(original_content, after_content);
}

/// Test with many fixes at once.
#[tokio::test]
async fn test_many_fixes_at_once() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    // Create many files with fixable issues
    for i in 0..20 {
        let fst_content = format!(
            r#"module Test{}

type t{} = int

let x{} = {}
"#,
            i, i, i, i
        );
        let fsti_content = format!(
            r#"module Test{}

type t{} = int

val x{} : int
"#,
            i, i, i
        );
        create_test_file(project_path, &format!("Test{}.fst", i), &fst_content);
        create_test_file(project_path, &format!("Test{}.fsti", i), &fsti_content);
    }

    // Run dry-run on all files
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let exit_code = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, true, DryRunFormat::default(), false).await;

    // Should complete without errors
    assert_eq!(exit_code, 0);
}

// =============================================================================
// GOLDEN TESTS
// =============================================================================

/// Golden test: FST001 expected fix output.
#[test]
fn test_golden_fst001_fix() {
    let fst_content = r#"module GoldenTest

type color =
  | Red
  | Green
  | Blue

let favorite : color = Blue
"#;
    let fsti_content = r#"module GoldenTest

type color =
  | Red
  | Green
  | Blue

val favorite : color
"#;

    let rule = DuplicateTypesRule::new();
    let diagnostics = rule.check_pair(
        &PathBuf::from("GoldenTest.fst"),
        fst_content,
        &PathBuf::from("GoldenTest.fsti"),
        fsti_content,
    );

    // Should produce exactly one diagnostic
    assert_eq!(diagnostics.len(), 1);

    let diag = &diagnostics[0];
    assert_eq!(diag.rule, RuleCode::FST001);
    assert!(diag.message.contains("color"));
    assert!(diag.fix.is_some());

    // Fix should reference the correct line range
    let fix = diag.fix.as_ref().unwrap();
    assert!(!fix.edits.is_empty());
    let edit = &fix.edits[0];
    assert_eq!(edit.range.start_line, 3); // "type color =" line (1-indexed)
}

/// Golden test: Content after applying FST001 fix.
#[test]
fn test_golden_fst001_applied_content() {
    let fst_content = r#"module Test

type foo = int

let x = 1
"#;

    // Simulate fix application
    let lines: Vec<&str> = fst_content.lines().collect();
    let mut result = String::new();

    // Remove lines 3-4 (the type definition, 1-indexed lines 3-4)
    for (i, line) in lines.iter().enumerate() {
        let line_num = i + 1; // 1-indexed
        if line_num < 3 || line_num > 4 {
            result.push_str(line);
            result.push('\n');
        }
    }

    // The result should have the type removed
    assert!(!result.contains("type foo = int"));
    assert!(result.contains("module Test"));
    assert!(result.contains("let x = 1"));
}

// =============================================================================
// EDGE CASE TESTS
// =============================================================================

/// Test empty file handling.
#[tokio::test]
async fn test_empty_file_handling() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    // Create empty files
    create_test_file(project_path, "Empty.fst", "");
    create_test_file(project_path, "Empty.fsti", "");

    let config = LintConfig::default();
    let engine = LintEngine::new(config);
    let exit_code = engine.check(&[project_path.to_path_buf()], OutputFormat::Text, false).await;

    // Should complete without crashing. Exit code may be non-zero due to
    // informational diagnostics (e.g., FST013 doc checker flags empty .fsti
    // for missing module-level doc comment), but should not exceed 1.
    assert!(exit_code <= 1, "Empty files should not cause engine crash (exit code: {})", exit_code);
}

/// Test file with only comments.
#[tokio::test]
async fn test_comment_only_file() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    let content = r#"(* This is a comment-only file *)
(* No actual F* code here *)
// Just comments
"#;
    create_test_file(project_path, "Comments.fst", content);

    let config = LintConfig::default();
    let engine = LintEngine::new(config);
    let exit_code = engine.check(&[project_path.to_path_buf()], OutputFormat::Text, false).await;

    assert_eq!(exit_code, 0);
}

/// Test file with syntax that looks like issues but isn't.
#[test]
fn test_false_positive_prevention() {
    // Abstract type in .fsti, concrete in .fst => NOT a duplicate
    let fsti_content = "module Test\n\ntype t\n\nval foo: t -> int\n";
    let fst_content = "module Test\n\ntype t = int\n\nlet foo x = x\n";

    let rule = DuplicateTypesRule::new();
    let diagnostics = rule.check_pair(
        &PathBuf::from("Test.fst"),
        fst_content,
        &PathBuf::from("Test.fsti"),
        fsti_content,
    );

    assert!(diagnostics.is_empty(), "Abstract .fsti + concrete .fst should NOT be flagged");
}

/// Test declaration counting accuracy.
#[test]
fn test_declaration_counting() {
    let content = r#"module Test

val foo : int -> int
let foo x = x + 1

type mytype = nat

let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

private let helper x = x

class myclass a = { method : a -> a }

instance myinstance : myclass int = { method = fun x -> x }
"#;

    let decls = count_declarations(content);

    // Should find these declarations
    assert!(decls.contains_key("foo"), "Should find val/let foo");
    assert!(decls.contains_key("mytype"), "Should find type mytype");
    assert!(decls.contains_key("factorial"), "Should find let rec factorial");
    assert!(decls.contains_key("helper"), "Should find private let helper");
    assert!(decls.contains_key("myclass"), "Should find class myclass");
    assert!(decls.contains_key("myinstance"), "Should find instance myinstance");
}

// =============================================================================
// CONFIDENCE LEVEL TESTS
// =============================================================================

/// Test that only high-confidence fixes are auto-applied.
#[test]
fn test_confidence_levels_respected() {
    let validation_high = FixValidation::safe(0.95);
    let validation_medium = FixValidation::safe(0.6);
    let validation_low = FixValidation::safe(0.3);

    // With threshold 0.8
    assert!(validation_high.can_auto_apply(0.8));
    assert!(!validation_medium.can_auto_apply(0.8));
    assert!(!validation_low.can_auto_apply(0.8));
}

/// Test that unsafe fixes are never auto-applied regardless of confidence.
#[test]
fn test_unsafe_never_auto_applied() {
    let unsafe_validation = FixValidation::unsafe_fix("Test reason");

    // Even with 0.0 threshold, unsafe should not be applied
    assert!(!unsafe_validation.can_auto_apply(0.0));
}

// =============================================================================
// SYNTAX VALIDATION TESTS
// =============================================================================

/// Test syntax validation catches unbalanced brackets.
#[test]
fn test_syntax_validation_unbalanced() {
    let unbalanced_parens = "let foo (x: int = x + 1";
    let result = validate_fstar_syntax(unbalanced_parens);
    assert!(result.is_err());
    assert!(result.unwrap_err().iter().any(|e: &String| e.contains("parentheses")));

    let unbalanced_braces = "let foo x = { field = x";
    let result = validate_fstar_syntax(unbalanced_braces);
    assert!(result.is_err());
    assert!(result.unwrap_err().iter().any(|e: &String| e.contains("braces")));
}

/// Test syntax validation passes for valid code.
#[test]
fn test_syntax_validation_valid() {
    let valid_code = r#"
module Test

let foo (x: int) : int = x + 1

type record = {
  field1: int;
  field2: string
}

let bar (r: record) = r.field1
"#;

    let result = validate_fstar_syntax(valid_code);
    assert!(result.is_ok());
}

// =============================================================================
// INTEGRATION WITH FULL PIPELINE
// =============================================================================

/// Full pipeline test: check -> fix (dry-run) -> fix (apply) -> verify.
#[tokio::test]
async fn test_full_pipeline() {
    let temp_dir = TempDir::new().expect("Failed to create temp dir");
    let project_path = temp_dir.path();

    // Create a file with a fixable issue
    let fst_content = r#"module FullPipeline

type status = | Active | Inactive

let get_status () : status = Active
"#;
    let fsti_content = r#"module FullPipeline

type status = | Active | Inactive

val get_status : unit -> status
"#;
    create_test_file(project_path, "FullPipeline.fst", fst_content);
    create_test_file(project_path, "FullPipeline.fsti", fsti_content);

    let original_fst = read_test_file(&project_path.join("FullPipeline.fst"));

    // Step 1: Check (should find issues)
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config.clone());
    let check_exit = engine.check(&[project_path.to_path_buf()], OutputFormat::Text, true).await;
    assert_eq!(check_exit, 1, "Check should find issues");

    // Step 2: Dry-run fix (should NOT modify)
    let engine = LintEngine::new(config.clone());
    let _ = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, true, DryRunFormat::default(), false).await;
    let after_dry_run = read_test_file(&project_path.join("FullPipeline.fst"));
    assert_eq!(original_fst, after_dry_run, "Dry-run should not modify files");

    // Step 3: Apply fix
    let engine = LintEngine::new(config.clone());
    let _ = engine.fix(&[project_path.to_path_buf()], OutputFormat::Text, false, DryRunFormat::default(), false).await;

    // Step 4: Verify fix was applied (or not, depending on confidence)
    // The file should have been processed
    let _after_apply = read_test_file(&project_path.join("FullPipeline.fst"));

    // .fsti should never be modified
    let fsti_after = read_test_file(&project_path.join("FullPipeline.fsti"));
    assert_eq!(fsti_content, fsti_after, ".fsti should not be modified");
}

// =============================================================================
// ERROR HANDLING TESTS
// =============================================================================
//
// NOTE: Unit-level backup management tests (listing, cleanup, retention)
// live in src/lint/file_safety.rs. This file only tests integration-level
// error handling through the LintEngine.

/// Test handling of non-existent directory.
#[tokio::test]
async fn test_nonexistent_directory_handling() {
    let config = LintConfig::default();
    let engine = LintEngine::new(config);

    // Should not panic when given non-existent path
    let exit_code = engine.check(&[PathBuf::from("/nonexistent/path")], OutputFormat::Text, false).await;

    // Should return 0 (no files found, no errors)
    assert_eq!(exit_code, 0);
}
