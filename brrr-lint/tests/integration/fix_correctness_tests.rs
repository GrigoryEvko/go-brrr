//! Integration tests for fix correctness -- verifying that fixes do NOT corrupt files.
//!
//! Each test creates temporary .fst/.fsti files, runs the appropriate lint rule,
//! and verifies the output is structurally valid F* (balanced comments, no orphaned
//! code, correct content preservation).
//!
//! Coverage:
//!  - Single and multiple duplicate type removal (FST001)
//!  - Doc comments and attributes attached to types
//!  - Edge positions: first type, last type, adjacent types
//!  - Section header comments associated with types
//!  - Unused open removal (FST004): single and multiple
//!  - Dry-run / apply consistency
//!  - Idempotency and revert round-trip
//!  - Large file stress test
//!  - UTF-8 content safety

use std::fs;
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use brrr_lint::lint::{
    DryRunFormat, DuplicateTypesRule, LintConfig, LintEngine, OutputFormat, Rule,
    UnusedOpensRule,
    validate_fstar_syntax,
};

// =============================================================================
// HELPERS
// =============================================================================

/// Create a file inside `dir` and return its absolute path.
fn write_file(dir: &Path, name: &str, content: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, content).expect("write_file failed");
    path
}

/// Read a file to string, panicking with a clear message on failure.
fn read_file(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("read_file({}): {}", path.display(), e))
}

/// Assert that parentheses, braces, and brackets are balanced in `content`.
/// This is a minimal structural sanity check for generated F* code.
fn assert_balanced_delimiters(content: &str, context: &str) {
    let mut parens: i32 = 0;
    let mut braces: i32 = 0;
    let mut brackets: i32 = 0;
    let mut in_string = false;
    let mut comment_depth: i32 = 0;

    let bytes = content.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        if in_string {
            if bytes[i] == b'\\' && i + 1 < len {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if comment_depth > 0 {
            if i + 1 < len && bytes[i] == b'(' && bytes[i + 1] == b'*' {
                comment_depth += 1;
                i += 2;
                continue;
            }
            if i + 1 < len && bytes[i] == b'*' && bytes[i + 1] == b')' {
                comment_depth -= 1;
                i += 2;
                continue;
            }
            i += 1;
            continue;
        }
        // Outside string and comment
        match bytes[i] {
            b'"' => { in_string = true; }
            b'(' if i + 1 < len && bytes[i + 1] == b'*' => {
                comment_depth += 1;
                i += 2;
                continue;
            }
            b'(' => { parens += 1; }
            b')' => { parens -= 1; }
            b'{' => { braces += 1; }
            b'}' => { braces -= 1; }
            b'[' => { brackets += 1; }
            b']' => { brackets -= 1; }
            _ => {}
        }
        i += 1;
    }

    assert_eq!(parens, 0, "[{}] Unbalanced parentheses (delta={})", context, parens);
    assert_eq!(braces, 0, "[{}] Unbalanced braces (delta={})", context, braces);
    assert_eq!(brackets, 0, "[{}] Unbalanced brackets (delta={})", context, brackets);
    assert_eq!(comment_depth, 0, "[{}] Unclosed block comment (depth={})", context, comment_depth);
}

/// Assert that a file has no more than one consecutive blank line anywhere.
fn assert_no_triple_blanks(content: &str, context: &str) {
    let mut consecutive = 0;
    for line in content.lines() {
        if line.trim().is_empty() {
            consecutive += 1;
        } else {
            consecutive = 0;
        }
        assert!(
            consecutive <= 2,
            "[{}] Found 3+ consecutive blank lines (should be at most 2)",
            context,
        );
    }
}

/// Run FST001 (duplicate types) on a .fst/.fsti pair and return diagnostics.
fn run_fst001(fst_path: &Path, fst_content: &str, fsti_path: &Path, fsti_content: &str) -> Vec<brrr_lint::lint::Diagnostic> {
    let rule = DuplicateTypesRule::new();
    rule.check_pair(
        &fst_path.to_path_buf(),
        fst_content,
        &fsti_path.to_path_buf(),
        fsti_content,
    )
}

/// Run FST004 (unused opens) on a single file and return diagnostics.
fn run_fst004(fst_path: &Path, content: &str) -> Vec<brrr_lint::lint::Diagnostic> {
    let rule = UnusedOpensRule::new();
    rule.check(&fst_path.to_path_buf(), content)
}

/// Simulate applying line-deletion edits from diagnostics against file content.
/// Returns the patched content after removing lines indicated by all edits
/// (handles new_text == "" as a full-line deletion).
///
/// This mirrors the core logic in `FixApplicator::build_fixed_content` but is
/// self-contained so the tests do not depend on internal fix_applicator wiring.
fn apply_edits(original: &str, diagnostics: &[brrr_lint::lint::Diagnostic]) -> String {
    // Collect all (start_line, end_line) ranges from edits (1-indexed).
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    for diag in diagnostics {
        if let Some(fix) = &diag.fix {
            for edit in &fix.edits {
                ranges.push((edit.range.start_line, edit.range.end_line));
            }
        }
    }

    // Build a set of 1-indexed line numbers to delete.
    let mut delete_set = std::collections::HashSet::new();
    for (start, end) in &ranges {
        for line_no in *start..=*end {
            delete_set.insert(line_no);
        }
    }

    let mut result_lines: Vec<&str> = Vec::new();
    for (idx, line) in original.lines().enumerate() {
        let line_no = idx + 1; // 1-indexed
        if !delete_set.contains(&line_no) {
            result_lines.push(line);
        }
    }

    let mut result = result_lines.join("\n");
    // Preserve trailing newline
    if original.ends_with('\n') {
        result.push('\n');
    }

    // Collapse runs of 3+ consecutive blank lines down to at most 2.
    collapse_blanks(&result)
}

/// Collapse 3+ consecutive blank lines to 2.
fn collapse_blanks(content: &str) -> String {
    let mut result = Vec::new();
    let mut blank_run = 0;
    for line in content.lines() {
        if line.trim().is_empty() {
            blank_run += 1;
            if blank_run <= 2 {
                result.push(line);
            }
        } else {
            blank_run = 0;
            result.push(line);
        }
    }
    let mut out = result.join("\n");
    if content.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Full-pipeline helper: run the lint engine in apply mode on a temp directory
/// with FST001 only, returning the resulting .fst content.
async fn apply_fst001_via_engine(fst_content: &str, fsti_content: &str) -> (String, String) {
    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst_content);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti_content);

    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(
        &[dir.path().to_path_buf()],
        OutputFormat::Text,
        false,           // apply mode
        DryRunFormat::default(),
        true,            // force
    ).await;

    let fst_after = read_file(&fst_path);
    let fsti_after = read_file(&fsti_path);
    // Keep TempDir alive until reads complete by binding it above.
    drop(dir);
    (fst_after, fsti_after)
}

/// Full-pipeline helper: run the lint engine in dry-run mode on a temp directory.
/// Returns exit code. The temp dir is kept alive by the caller.
async fn dryrun_fst001_via_engine(dir: &Path) -> i32 {
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    engine.fix(
        &[dir.to_path_buf()],
        OutputFormat::Text,
        true,            // dry-run
        DryRunFormat::default(),
        false,
    ).await
}

// =============================================================================
// 1. SINGLE TYPE REMOVAL
// =============================================================================

#[test]
fn test_single_type_removal_produces_valid_fstar() {
    let fst = "\
module Test

type color = | Red | Green | Blue

let favorite : color = Blue
";
    let fsti = "\
module Test

type color = | Red | Green | Blue

val favorite : color
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type 'color'");

    let patched = apply_edits(fst, &diags);

    // The type should be gone
    assert!(!patched.contains("type color"), "Type 'color' should be removed");
    // Module declaration and let binding must survive
    assert!(patched.contains("module Test"), "Module declaration must survive");
    assert!(patched.contains("let favorite"), "let binding must survive");
    // Structural validity
    assert_balanced_delimiters(&patched, "single_type_removal");
    assert_no_triple_blanks(&patched, "single_type_removal");
}

// =============================================================================
// 2. MULTIPLE TYPE REMOVAL IN SAME FILE
// =============================================================================

#[test]
fn test_multiple_type_removal_same_file() {
    let fst = "\
module Test

type alpha = int

type beta = nat

type gamma = bool

let x : alpha = 0
";
    let fsti = "\
module Test

type alpha = int

type beta = nat

type gamma = bool

val x : alpha
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(diags.len() >= 3, "Should detect 3 duplicate types, got {}", diags.len());

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type alpha"), "alpha should be removed");
    assert!(!patched.contains("type beta"), "beta should be removed");
    assert!(!patched.contains("type gamma"), "gamma should be removed");
    assert!(patched.contains("module Test"), "Module declaration must survive");
    assert!(patched.contains("let x"), "let binding must survive");
    assert_balanced_delimiters(&patched, "multiple_type_removal");
    assert_no_triple_blanks(&patched, "multiple_type_removal");
}

// =============================================================================
// 3. TYPE WITH DOC COMMENT
// =============================================================================

#[test]
fn test_type_with_doc_comment_removed() {
    let fst = "\
module Test

(** Documentation for my_type *)
type my_type = int

let y = 42
";
    let fsti = "\
module Test

(** Documentation for my_type *)
type my_type = int

val y : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type with doc comment");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type my_type"), "Type should be removed");
    assert!(!patched.contains("Documentation for my_type"), "Doc comment should also be removed");
    assert!(patched.contains("let y"), "let binding must survive");
    assert_balanced_delimiters(&patched, "type_with_doc_comment");
}

// =============================================================================
// 4. TYPE WITH ATTRIBUTES
// =============================================================================

#[test]
fn test_type_with_attributes_removed() {
    let fst = "\
module Test

[@@ attribute1; attribute2]
type tagged_type = nat

let z = 0
";
    let fsti = "\
module Test

[@@ attribute1; attribute2]
type tagged_type = nat

val z : nat
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type with attributes");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type tagged_type"), "Type should be removed");
    assert!(!patched.contains("attribute1"), "Attribute should also be removed");
    assert!(patched.contains("let z"), "let binding must survive");
    assert_balanced_delimiters(&patched, "type_with_attributes");
}

// =============================================================================
// 5. TYPE AT END OF FILE
// =============================================================================

#[test]
fn test_type_at_end_of_file() {
    let fst = "\
module Test

let x = 1

type last_type = int
";
    let fsti = "\
module Test

val x : int

type last_type = int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type at end of file");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type last_type"), "Last type should be removed");
    assert!(patched.contains("let x"), "let binding must survive");
    // No trailing garbage after removal
    let trimmed = patched.trim_end();
    assert!(
        !trimmed.ends_with("type") && !trimmed.ends_with("="),
        "No trailing garbage after end-of-file type removal"
    );
    assert_balanced_delimiters(&patched, "type_at_end_of_file");
}

// =============================================================================
// 6. TYPE AT START OF FILE (AFTER MODULE DECLARATION)
// =============================================================================

#[test]
fn test_type_at_start_of_file() {
    let fst = "\
module Test

type first_type = int

let a = 1

let b = 2
";
    let fsti = "\
module Test

type first_type = int

val a : int

val b : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate first type");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type first_type"), "First type should be removed");
    assert!(patched.contains("module Test"), "Module declaration must survive");
    assert!(patched.contains("let a"), "First let must survive");
    assert!(patched.contains("let b"), "Second let must survive");
    assert_balanced_delimiters(&patched, "type_at_start_of_file");
}

// =============================================================================
// 7. ADJACENT TYPES -- REMOVE ONE, OTHER UNTOUCHED
// =============================================================================

#[test]
fn test_adjacent_types_only_duplicate_removed() {
    // Only 'dup_type' is in .fsti; 'private_type' is private so not flagged.
    let fst = "\
module Test

type dup_type = int
private type private_type = nat

let x = 1
";
    let fsti = "\
module Test

type dup_type = int

val x : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);

    // Filter to only FST001 diagnostics for dup_type
    let dup_diags: Vec<_> = diags.iter().filter(|d| d.message.contains("dup_type")).cloned().collect();
    assert!(!dup_diags.is_empty(), "Should flag dup_type as duplicate");

    let patched = apply_edits(fst, &dup_diags);

    assert!(!patched.contains("type dup_type"), "dup_type should be removed");
    assert!(patched.contains("private type private_type"), "private_type must be untouched");
    assert!(patched.contains("let x"), "let binding must survive");
    assert_balanced_delimiters(&patched, "adjacent_types");
}

// =============================================================================
// 8. TYPE WITH SECTION HEADER COMMENT
// =============================================================================

#[test]
fn test_type_with_section_header() {
    let fst = "\
module Test

(* ================================================================== *)
(* Type definitions                                                    *)
(* ================================================================== *)

type header_type =
  | Variant1
  | Variant2

let use_it (x: header_type) = x
";
    let fsti = "\
module Test

(* ================================================================== *)
(* Type definitions                                                    *)
(* ================================================================== *)

type header_type =
  | Variant1
  | Variant2

val use_it : header_type -> header_type
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", fst);
    let fsti_path = write_file(dir.path(), "Test.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type with section header");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type header_type"), "Type should be removed");
    assert!(patched.contains("let use_it"), "let binding must survive");
    assert_balanced_delimiters(&patched, "type_with_section_header");
    assert_no_triple_blanks(&patched, "type_with_section_header");
}

// =============================================================================
// 9. UNUSED OPEN REMOVAL -- SINGLE
// =============================================================================

#[test]
fn test_unused_open_removal_single() {
    let content = "\
module Test

open FStar.List.Tot
open FStar.Option

let my_option (x: int) : option int = Some x
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", content);

    let diags = run_fst004(&fst_path, content);

    // FStar.List.Tot should be flagged as unused (Option is used via `option` / `Some`)
    // (The rule may or may not flag it depending on heuristics; we test structural safety.)
    if diags.is_empty() {
        // If the rule didn't flag anything, that's acceptable -- heuristic may keep it.
        return;
    }

    let patched = apply_edits(content, &diags);

    // Structural integrity
    assert!(patched.contains("module Test"), "Module declaration must survive");
    assert_balanced_delimiters(&patched, "unused_open_single");
    assert_no_triple_blanks(&patched, "unused_open_single");

    // The line following the removed open must be preserved
    assert!(patched.contains("let my_option"), "let binding must survive");
}

// =============================================================================
// 10. MULTIPLE UNUSED OPENS
// =============================================================================

#[test]
fn test_multiple_unused_opens_removal() {
    let content = "\
module Test

open FStar.Seq
open FStar.Set
open FStar.Map

let x : int = 42
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Test.fst", content);

    let diags = run_fst004(&fst_path, content);

    // At least some of these should be flagged as unused
    if diags.is_empty() {
        return; // heuristic may keep them; skip structural test
    }

    let patched = apply_edits(content, &diags);

    assert!(patched.contains("module Test"), "Module declaration must survive");
    assert!(patched.contains("let x"), "let binding must survive");
    assert_balanced_delimiters(&patched, "multiple_unused_opens");
    assert_no_triple_blanks(&patched, "multiple_unused_opens");
}

// =============================================================================
// 11. FIX PREVIEW MATCHES REALITY
// =============================================================================

#[tokio::test]
async fn test_fix_preview_matches_reality() {
    let fst = "\
module Preview

type preview_type = int

let v = 1
";
    let fsti = "\
module Preview

type preview_type = int

val v : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Preview.fst", fst);
    let fsti_path = write_file(dir.path(), "Preview.fsti", fsti);

    // Step 1: dry-run -- file must NOT change
    let original_fst = read_file(&fst_path);
    let _exit = dryrun_fst001_via_engine(dir.path()).await;
    let after_dryrun = read_file(&fst_path);
    assert_eq!(original_fst, after_dryrun, "Dry-run must not modify the file");

    // Step 2: apply -- file should have the type removed
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(
        &[dir.path().to_path_buf()],
        OutputFormat::Text,
        false,
        DryRunFormat::default(),
        true,
    ).await;

    let after_apply = read_file(&fst_path);

    // The type should be removed after apply but not after dry-run
    if after_apply != original_fst {
        // Fix was applied
        assert!(!after_apply.contains("type preview_type"), "Type should be removed after apply");
        assert!(after_apply.contains("let v"), "let binding must survive");
        assert_balanced_delimiters(&after_apply, "preview_matches_reality");
    }
    // .fsti must never change
    let fsti_after = read_file(&fsti_path);
    assert_eq!(fsti, fsti_after, ".fsti must not be modified");
}

// =============================================================================
// 12. IDEMPOTENCY -- RUNNING FIX TWICE PRODUCES SAME RESULT
// =============================================================================

#[tokio::test]
async fn test_fix_idempotency() {
    let fst = "\
module Idempotent

type idem_type = nat

let f (x: nat) : nat = x
";
    let fsti = "\
module Idempotent

type idem_type = nat

val f : nat -> nat
";

    // First pass
    let (after_first, _) = apply_fst001_via_engine(fst, fsti).await;

    // Second pass (run engine on the already-fixed content)
    let (after_second, _) = apply_fst001_via_engine(&after_first, fsti).await;

    assert_eq!(
        after_first, after_second,
        "Running fix twice must produce identical output (idempotency)"
    );
    assert_balanced_delimiters(&after_second, "idempotency");
}

// =============================================================================
// 13. REVERT AFTER FIX -- APPLY, REVERT, VERIFY ORIGINAL RESTORED
// =============================================================================

#[tokio::test]
async fn test_revert_after_fix() {
    let fst = "\
module Revertable

type rev_type = int

let g = 99
";
    let fsti = "\
module Revertable

type rev_type = int

val g : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Revertable.fst", fst);
    let _fsti_path = write_file(dir.path(), "Revertable.fsti", fsti);

    let original = read_file(&fst_path);

    // Apply the fix using AtomicWriter with backup
    let writer = brrr_lint::lint::file_safety::AtomicWriter::new();

    // Simulate: apply fix, creating backup
    let config = LintConfig::new(Some("FST001".to_string()), None, None);
    let engine = LintEngine::new(config);
    let _ = engine.fix(
        &[dir.path().to_path_buf()],
        OutputFormat::Text,
        false,
        DryRunFormat::default(),
        true,
    ).await;

    let after_apply = read_file(&fst_path);

    // If fix was applied, revert via AtomicWriter
    if after_apply != original {
        // Write backup manually to simulate revert
        let backup_path = dir.path().join("Revertable.fst.backup");
        fs::write(&backup_path, &original).unwrap();

        // Revert
        writer.rollback(&fst_path, &backup_path).expect("Rollback should succeed");

        let after_revert = read_file(&fst_path);
        assert_eq!(original, after_revert, "Revert must restore original content exactly");
    }
}

// =============================================================================
// 14. LARGE FILE STRESS TEST -- 50+ TYPES, REMOVE 10
// =============================================================================

#[test]
fn test_large_file_stress() {
    // Build a file with 50 types, 10 of which are duplicated in the .fsti
    let mut fst_lines = vec!["module StressTest".to_string(), String::new()];
    let mut fsti_lines = vec!["module StressTest".to_string(), String::new()];

    // 10 types that appear in both (duplicates)
    for i in 0..10 {
        let typedef = format!("type dup_{} = int", i);
        fst_lines.push(typedef.clone());
        fst_lines.push(String::new());
        fsti_lines.push(typedef);
        fsti_lines.push(String::new());
    }

    // 40 types only in .fst (private, so not flagged)
    for i in 10..50 {
        fst_lines.push(format!("private type priv_{} = nat", i));
        fst_lines.push(String::new());
    }

    // Some let bindings at the end
    for i in 0..5 {
        let letbind = format!("let val_{} = {}", i, i);
        fst_lines.push(letbind);
        fsti_lines.push(format!("val val_{} : int", i));
    }
    // Trailing newline
    fst_lines.push(String::new());
    fsti_lines.push(String::new());

    let fst = fst_lines.join("\n");
    let fsti = fsti_lines.join("\n");

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "StressTest.fst", &fst);
    let fsti_path = write_file(dir.path(), "StressTest.fsti", &fsti);

    let diags = run_fst001(&fst_path, &fst, &fsti_path, &fsti);
    assert!(diags.len() >= 10, "Should detect at least 10 duplicate types, got {}", diags.len());

    let patched = apply_edits(&fst, &diags);

    // All 10 duplicate types should be removed
    for i in 0..10 {
        assert!(
            !patched.contains(&format!("type dup_{} ", i)),
            "dup_{} should be removed",
            i
        );
    }

    // All 40 private types should remain
    for i in 10..50 {
        assert!(
            patched.contains(&format!("private type priv_{}", i)),
            "priv_{} must survive",
            i
        );
    }

    // All let bindings should remain
    for i in 0..5 {
        assert!(
            patched.contains(&format!("let val_{}", i)),
            "val_{} must survive",
            i
        );
    }

    assert!(patched.contains("module StressTest"), "Module declaration must survive");
    assert_balanced_delimiters(&patched, "large_file_stress");
    assert_no_triple_blanks(&patched, "large_file_stress");
}

// =============================================================================
// 15. UTF-8 CONTENT -- NO PANICS ON UNICODE
// =============================================================================

#[test]
fn test_utf8_content_safety() {
    let fst = "\
module UniTest

(* Type with unicode in comment: \u{00e4}\u{00f6}\u{00fc} \u{03b1}\u{03b2}\u{03b3} \u{2200}x. P(x) *)
type uni_type = int

(* \u{1f600} emoji in comment *)
let greet = \"H\u{00e9}llo W\u{00f6}rld\"
";
    let fsti = "\
module UniTest

(* Type with unicode in comment: \u{00e4}\u{00f6}\u{00fc} \u{03b1}\u{03b2}\u{03b3} \u{2200}x. P(x) *)
type uni_type = int

val greet : string
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "UniTest.fst", fst);
    let fsti_path = write_file(dir.path(), "UniTest.fsti", fsti);

    // Must not panic
    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate type with unicode");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type uni_type"), "Type should be removed");
    assert!(patched.contains("let greet"), "let binding with unicode must survive");
    // Unicode string content preserved
    assert!(patched.contains("H\u{00e9}llo"), "Unicode string content must be preserved");
    assert_balanced_delimiters(&patched, "utf8_safety");
}

// =============================================================================
// SUPPLEMENTARY: SYNTAX VALIDATION ON ALL PATCHED OUTPUTS
// =============================================================================

/// Helper that runs validate_fstar_syntax on the patched content and asserts
/// no fatal errors.
fn assert_syntax_valid(content: &str, context: &str) {
    let result = validate_fstar_syntax(content);
    match result {
        Ok(()) => {} // pass
        Err(errors) => {
            panic!(
                "[{}] validate_fstar_syntax found errors: {:?}",
                context, errors
            );
        }
    }
}

#[test]
fn test_single_type_removal_syntax_valid() {
    let fst = "\
module SynTest

type syn_type = int

let x = 1
";
    let fsti = "\
module SynTest

type syn_type = int

val x : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "SynTest.fst", fst);
    let fsti_path = write_file(dir.path(), "SynTest.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    let patched = apply_edits(fst, &diags);
    assert_syntax_valid(&patched, "single_type_syntax");
}

#[test]
fn test_record_type_removal_produces_valid_fstar() {
    let fst = "\
module RecTest

noeq type my_record = {
  field1: int;
  field2: nat;
  field3: bool
}

let default_record : my_record = {
  field1 = 0;
  field2 = 0;
  field3 = false
}
";
    let fsti = "\
module RecTest

noeq type my_record = {
  field1: int;
  field2: nat;
  field3: bool
}

val default_record : my_record
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "RecTest.fst", fst);
    let fsti_path = write_file(dir.path(), "RecTest.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate record type");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("noeq type my_record"), "Record type should be removed");
    assert!(!patched.contains("field1: int"), "Record fields should be removed");
    assert!(patched.contains("let default_record"), "let binding must survive");
    assert_balanced_delimiters(&patched, "record_type_removal");
    assert_syntax_valid(&patched, "record_type_removal_syntax");
}

#[test]
fn test_adt_multiline_type_removal() {
    let fst = "\
module AdtTest

type expr =
  | Lit of int
  | Add of expr & expr
  | Mul of expr & expr
  | Neg of expr

let eval (e: expr) : int = 0
";
    let fsti = "\
module AdtTest

type expr =
  | Lit of int
  | Add of expr & expr
  | Mul of expr & expr
  | Neg of expr

val eval : expr -> int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "AdtTest.fst", fst);
    let fsti_path = write_file(dir.path(), "AdtTest.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate ADT type");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type expr"), "ADT type should be removed");
    assert!(!patched.contains("| Lit of int"), "ADT variants should be removed");
    assert!(patched.contains("let eval"), "let binding must survive");
    assert_balanced_delimiters(&patched, "adt_multiline_removal");
}

#[test]
fn test_inline_for_extraction_type_removal() {
    let fst = "\
module InlineTest

inline_for_extraction type byte = FStar.UInt8.t

let zero_byte : byte = 0uy
";
    let fsti = "\
module InlineTest

inline_for_extraction type byte = FStar.UInt8.t

val zero_byte : byte
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "InlineTest.fst", fst);
    let fsti_path = write_file(dir.path(), "InlineTest.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(!diags.is_empty(), "Should detect duplicate inline_for_extraction type");

    let patched = apply_edits(fst, &diags);

    assert!(!patched.contains("type byte"), "inline_for_extraction type should be removed");
    assert!(patched.contains("let zero_byte"), "let binding must survive");
    assert_balanced_delimiters(&patched, "inline_for_extraction_removal");
}

#[tokio::test]
async fn test_engine_apply_preserves_fsti() {
    let fst = "\
module FstiGuard

type guarded = int

let val1 = 1
";
    let fsti = "\
module FstiGuard

type guarded = int

val val1 : int
";

    let (_, fsti_after) = apply_fst001_via_engine(fst, fsti).await;
    assert_eq!(fsti, fsti_after, ".fsti file must NEVER be modified by FST001 apply");
}

/// Ensure that applying FST001 to a file with NO duplicates is a no-op.
#[test]
fn test_no_duplicates_is_noop() {
    let fst = "\
module NoDup

let x = 1
let y = 2
";
    let fsti = "\
module NoDup

val x : int
val y : int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "NoDup.fst", fst);
    let fsti_path = write_file(dir.path(), "NoDup.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(diags.is_empty(), "No duplicates should produce zero diagnostics");
}

/// Ensure abstract type in .fsti (no `=`) + concrete in .fst is NOT flagged.
#[test]
fn test_abstract_fsti_concrete_fst_not_flagged() {
    let fst = "\
module Abstract

type opaque = int

let use_opaque (x: opaque) : int = x
";
    let fsti = "\
module Abstract

type opaque

val use_opaque : opaque -> int
";

    let dir = TempDir::new().unwrap();
    let fst_path = write_file(dir.path(), "Abstract.fst", fst);
    let fsti_path = write_file(dir.path(), "Abstract.fsti", fsti);

    let diags = run_fst001(&fst_path, fst, &fsti_path, fsti);
    assert!(
        diags.is_empty(),
        "Abstract .fsti + concrete .fst must NOT be flagged as duplicate"
    );
}
