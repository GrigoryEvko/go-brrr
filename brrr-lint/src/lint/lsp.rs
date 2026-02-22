//! LSP integration for the brrr-lint F* linter.
//!
//! Converts lint diagnostics to LSP protocol types and provides:
//! - `publishDiagnostics` with correct severity, range, code, source, and tags
//! - `textDocument/codeAction` quick fixes (FST001, FST004, etc.)
//! - Workspace lint configuration
//! - `DiagnosticTag::UNNECESSARY` for dead code (FST005)
//! - Progress reporting via `$/progress`

use std::collections::HashMap;
use std::path::Path;

use tower_lsp::lsp_types::{
    self as lsp, CodeAction, CodeActionKind, DiagnosticSeverity as LspSeverity, DiagnosticTag,
    NumberOrString, Position, Range as LspRange, TextEdit, Url, WorkspaceEdit,
};

use super::engine::{LintConfig, LintEngine};
use super::rules::{self, Diagnostic, DiagnosticSeverity, RuleCode};

// ---------------------------------------------------------------------------
// Workspace lint configuration
// ---------------------------------------------------------------------------

/// Lint settings received from the LSP client via `workspace/configuration`
/// or `initializationOptions`.
#[derive(Debug, Clone, serde::Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct LintSettings {
    /// Master switch for lint diagnostics.
    pub enabled: bool,
    /// Rule codes to enable (empty = all).
    pub select: Vec<String>,
    /// Rule codes to disable.
    pub ignore: Vec<String>,
    /// Lint when a document is opened.
    pub lint_on_open: bool,
    /// Lint when a document changes (debounced).
    pub lint_on_change: bool,
    /// Debounce delay in milliseconds for `didChange` re-lint.
    pub debounce_ms: u64,
}

impl Default for LintSettings {
    fn default() -> Self {
        Self {
            enabled: true,
            select: Vec::new(),
            ignore: Vec::new(),
            lint_on_open: true,
            lint_on_change: true,
            debounce_ms: 300,
        }
    }
}

impl LintSettings {
    /// Build a `LintConfig` from these settings.
    pub fn to_lint_config(&self) -> LintConfig {
        let select = if self.select.is_empty() {
            None
        } else {
            Some(self.select.join(","))
        };
        let ignore = if self.ignore.is_empty() {
            None
        } else {
            Some(self.ignore.join(","))
        };
        LintConfig::new(select, ignore, None)
    }
}

// ---------------------------------------------------------------------------
// Conversion helpers
// ---------------------------------------------------------------------------

/// Convert a 1-indexed lint range to a 0-indexed LSP range.
///
/// The lint `Range` uses 1-based line and column numbers (following the F*
/// convention). LSP uses 0-based positions. This function performs the
/// subtraction safely -- lint ranges are validated to be >= 1 at construction.
pub fn to_lsp_range(range: &rules::Range) -> LspRange {
    LspRange {
        start: Position {
            line: (range.start_line - 1) as u32,
            character: (range.start_col - 1) as u32,
        },
        end: Position {
            line: (range.end_line - 1) as u32,
            character: (range.end_col - 1) as u32,
        },
    }
}

/// Convert lint severity to LSP severity.
fn to_lsp_severity(severity: DiagnosticSeverity) -> LspSeverity {
    match severity {
        DiagnosticSeverity::Error => LspSeverity::ERROR,
        DiagnosticSeverity::Warning => LspSeverity::WARNING,
        DiagnosticSeverity::Info => LspSeverity::INFORMATION,
        DiagnosticSeverity::Hint => LspSeverity::HINT,
    }
}

/// Compute diagnostic tags for a given rule.
///
/// - FST005 (dead code) -> `DiagnosticTag::UNNECESSARY` (renders as faded text)
/// - FST004 (unused opens) -> `DiagnosticTag::UNNECESSARY`
fn diagnostic_tags(rule: RuleCode) -> Option<Vec<DiagnosticTag>> {
    match rule {
        RuleCode::FST004 | RuleCode::FST005 => Some(vec![DiagnosticTag::UNNECESSARY]),
        _ => None,
    }
}

/// Convert a lint `Diagnostic` to an LSP `Diagnostic`.
///
/// Maps severity, range (1-indexed -> 0-indexed), rule code, source name,
/// and diagnostic tags.
pub fn to_lsp_diagnostic(diag: &Diagnostic) -> lsp::Diagnostic {
    lsp::Diagnostic {
        range: to_lsp_range(&diag.range),
        severity: Some(to_lsp_severity(diag.severity)),
        code: Some(NumberOrString::String(diag.rule.to_string())),
        code_description: None,
        source: Some("brrr-lint".to_string()),
        message: diag.message.clone(),
        related_information: None,
        tags: diagnostic_tags(diag.rule),
        data: None,
    }
}

/// Convert a lint diagnostic with a fix to an LSP `CodeAction`.
///
/// Returns `None` when the diagnostic carries no fix. Each edit in the fix
/// is mapped to an LSP `TextEdit` inside a `WorkspaceEdit`. Edits whose
/// file differs from the diagnostic's file produce entries under a separate
/// URI (e.g., pair-rule fixes that touch the .fsti file).
pub fn to_code_action(diag: &Diagnostic, uri: &Url) -> Option<CodeAction> {
    let fix = diag.fix.as_ref()?;

    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for edit in &fix.edits {
        let edit_uri = if edit.file == diag.file {
            uri.clone()
        } else {
            Url::from_file_path(&edit.file).ok()?
        };
        let text_edit = TextEdit {
            range: to_lsp_range(&edit.range),
            new_text: edit.new_text.clone(),
        };
        changes.entry(edit_uri).or_default().push(text_edit);
    }

    Some(CodeAction {
        title: format!("{}: {}", diag.rule, fix.message),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![to_lsp_diagnostic(diag)]),
        edit: Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }),
        command: None,
        is_preferred: Some(fix.is_safe()),
        disabled: None,
        data: None,
    })
}

/// Check if two LSP ranges overlap (inclusive endpoints).
pub fn ranges_overlap(a: LspRange, b: LspRange) -> bool {
    let a_before_b = a.end.line < b.start.line
        || (a.end.line == b.start.line && a.end.character < b.start.character);
    let b_before_a = b.end.line < a.start.line
        || (b.end.line == a.start.line && b.end.character < a.start.character);
    !(a_before_b || b_before_a)
}

// ---------------------------------------------------------------------------
// Lint backend
// ---------------------------------------------------------------------------

/// LSP lint backend that wraps the lint engine.
///
/// Thread-safe (`Send + Sync`) so it can be shared across async tasks
/// via `Arc<LintBackend>`. All methods take `&self` and perform no
/// interior mutation.
pub struct LintBackend {
    engine: LintEngine,
}

impl LintBackend {
    /// Create a new lint backend with the given configuration.
    pub fn new(config: LintConfig) -> Self {
        Self {
            engine: LintEngine::new(config),
        }
    }

    /// Create a backend with default configuration (all rules enabled).
    pub fn default_backend() -> Self {
        Self::new(LintConfig::default())
    }

    /// Rebuild the backend with new settings (e.g., after workspace/configuration change).
    pub fn with_settings(settings: &LintSettings) -> Self {
        Self::new(settings.to_lint_config())
    }

    /// Lint file content and return LSP diagnostics.
    pub fn lint(&self, file: &Path, content: &str) -> Vec<lsp::Diagnostic> {
        self.engine
            .check_content(file, content)
            .iter()
            .map(to_lsp_diagnostic)
            .collect()
    }

    /// Lint file content and return both LSP diagnostics and raw lint diagnostics.
    ///
    /// The raw diagnostics are stored for later code-action generation (they
    /// carry the `Fix` payload that LSP diagnostics do not).
    pub fn lint_full(
        &self,
        file: &Path,
        content: &str,
    ) -> (Vec<lsp::Diagnostic>, Vec<Diagnostic>) {
        let raw = self.engine.check_content(file, content);
        let lsp_diags = raw.iter().map(to_lsp_diagnostic).collect();
        (lsp_diags, raw)
    }

    /// Generate code actions for lint diagnostics overlapping `range`.
    pub fn code_actions(
        &self,
        uri: &Url,
        range: LspRange,
        diagnostics: &[Diagnostic],
    ) -> Vec<CodeAction> {
        diagnostics
            .iter()
            .filter(|d| d.fix.is_some() && ranges_overlap(to_lsp_range(&d.range), range))
            .filter_map(|d| to_code_action(d, uri))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Progress helpers
// ---------------------------------------------------------------------------

/// Progress token used for lint operations.
pub const LINT_PROGRESS_TOKEN: &str = "brrr-lint/lint";

/// Build a `WorkDoneProgressBegin` value for lint start.
pub fn progress_begin(file_name: &str) -> lsp::WorkDoneProgressBegin {
    lsp::WorkDoneProgressBegin {
        title: "Linting".to_string(),
        cancellable: Some(false),
        message: Some(format!("Checking {}", file_name)),
        percentage: None,
    }
}

/// Build a `WorkDoneProgressEnd` value for lint completion.
pub fn progress_end(count: usize) -> lsp::WorkDoneProgressEnd {
    lsp::WorkDoneProgressEnd {
        message: Some(if count == 0 {
            "No issues found".to_string()
        } else {
            format!("{} issue{} found", count, if count == 1 { "" } else { "s" })
        }),
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lint::rules::{Edit, Fix, Range};
    use std::path::PathBuf;

    // =====================================================================
    // Range conversion
    // =====================================================================

    #[test]
    fn test_to_lsp_range_basic() {
        let range = Range::new(1, 1, 1, 10);
        let lsp = to_lsp_range(&range);
        assert_eq!(lsp.start.line, 0);
        assert_eq!(lsp.start.character, 0);
        assert_eq!(lsp.end.line, 0);
        assert_eq!(lsp.end.character, 9);
    }

    #[test]
    fn test_to_lsp_range_multiline() {
        let range = Range::new(5, 3, 10, 20);
        let lsp = to_lsp_range(&range);
        assert_eq!(lsp.start.line, 4);
        assert_eq!(lsp.start.character, 2);
        assert_eq!(lsp.end.line, 9);
        assert_eq!(lsp.end.character, 19);
    }

    #[test]
    fn test_to_lsp_range_point() {
        let range = Range::point(7, 15);
        let lsp = to_lsp_range(&range);
        assert_eq!(lsp.start.line, 6);
        assert_eq!(lsp.start.character, 14);
        assert_eq!(lsp.end.line, 6);
        assert_eq!(lsp.end.character, 14);
    }

    // =====================================================================
    // Severity conversion
    // =====================================================================

    #[test]
    fn test_severity_mapping() {
        assert_eq!(to_lsp_severity(DiagnosticSeverity::Error), LspSeverity::ERROR);
        assert_eq!(
            to_lsp_severity(DiagnosticSeverity::Warning),
            LspSeverity::WARNING
        );
        assert_eq!(
            to_lsp_severity(DiagnosticSeverity::Info),
            LspSeverity::INFORMATION
        );
        assert_eq!(to_lsp_severity(DiagnosticSeverity::Hint), LspSeverity::HINT);
    }

    // =====================================================================
    // Diagnostic tags
    // =====================================================================

    #[test]
    fn test_dead_code_tag() {
        let tags = diagnostic_tags(RuleCode::FST005);
        assert_eq!(tags, Some(vec![DiagnosticTag::UNNECESSARY]));
    }

    #[test]
    fn test_unused_opens_tag() {
        let tags = diagnostic_tags(RuleCode::FST004);
        assert_eq!(tags, Some(vec![DiagnosticTag::UNNECESSARY]));
    }

    #[test]
    fn test_no_tag_for_other_rules() {
        assert!(diagnostic_tags(RuleCode::FST001).is_none());
        assert!(diagnostic_tags(RuleCode::FST003).is_none());
        assert!(diagnostic_tags(RuleCode::FST006).is_none());
        assert!(diagnostic_tags(RuleCode::FST007).is_none());
    }

    // =====================================================================
    // Full diagnostic conversion
    // =====================================================================

    #[test]
    fn test_to_lsp_diagnostic_full() {
        let diag = Diagnostic {
            rule: RuleCode::FST004,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("Test.fst"),
            range: Range::new(3, 1, 3, 25),
            message: "Unused open FStar.Pervasives".to_string(),
            fix: None,
        };

        let lsp = to_lsp_diagnostic(&diag);
        assert_eq!(lsp.range.start.line, 2);
        assert_eq!(lsp.range.start.character, 0);
        assert_eq!(lsp.range.end.line, 2);
        assert_eq!(lsp.range.end.character, 24);
        assert_eq!(lsp.severity, Some(LspSeverity::WARNING));
        assert_eq!(lsp.code, Some(NumberOrString::String("FST004".to_string())));
        assert_eq!(lsp.source, Some("brrr-lint".to_string()));
        assert_eq!(lsp.message, "Unused open FStar.Pervasives");
        assert_eq!(lsp.tags, Some(vec![DiagnosticTag::UNNECESSARY]));
    }

    #[test]
    fn test_to_lsp_diagnostic_error() {
        let diag = Diagnostic {
            rule: RuleCode::FST003,
            severity: DiagnosticSeverity::Error,
            file: PathBuf::from("Bad.fst"),
            range: Range::new(1, 1, 1, 5),
            message: "Unclosed comment".to_string(),
            fix: None,
        };

        let lsp = to_lsp_diagnostic(&diag);
        assert_eq!(lsp.severity, Some(LspSeverity::ERROR));
        assert_eq!(lsp.code, Some(NumberOrString::String("FST003".to_string())));
        assert!(lsp.tags.is_none());
    }

    // =====================================================================
    // Code action conversion
    // =====================================================================

    fn test_uri() -> Url {
        Url::parse("file:///tmp/Test.fst").unwrap()
    }

    #[test]
    fn test_code_action_from_fix() {
        let diag = Diagnostic {
            rule: RuleCode::FST004,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/tmp/Test.fst"),
            range: Range::new(3, 1, 3, 25),
            message: "Unused open FStar.Pervasives".to_string(),
            fix: Some(Fix::safe(
                "Remove unused open",
                vec![Edit {
                    file: PathBuf::from("/tmp/Test.fst"),
                    range: Range::new(3, 1, 4, 1),
                    new_text: String::new(),
                }],
            )),
        };

        let uri = test_uri();
        let action = to_code_action(&diag, &uri).expect("should produce code action");

        assert_eq!(action.title, "FST004: Remove unused open");
        assert_eq!(action.kind, Some(CodeActionKind::QUICKFIX));
        assert_eq!(action.is_preferred, Some(true));

        let edit = action.edit.expect("should have workspace edit");
        let changes = edit.changes.expect("should have changes map");
        assert!(changes.contains_key(&uri));
        let text_edits = &changes[&uri];
        assert_eq!(text_edits.len(), 1);
        assert_eq!(text_edits[0].new_text, "");
        assert_eq!(text_edits[0].range.start.line, 2); // 0-indexed
    }

    #[test]
    fn test_code_action_none_without_fix() {
        let diag = Diagnostic {
            rule: RuleCode::FST006,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/tmp/Test.fst"),
            range: Range::new(1, 1, 1, 10),
            message: "Naming violation".to_string(),
            fix: None,
        };

        let uri = test_uri();
        assert!(to_code_action(&diag, &uri).is_none());
    }

    #[test]
    fn test_code_action_unsafe_not_preferred() {
        let diag = Diagnostic {
            rule: RuleCode::FST005,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/tmp/Test.fst"),
            range: Range::new(5, 1, 5, 20),
            message: "Unused binding".to_string(),
            fix: Some(Fix::unsafe_fix(
                "Remove unused binding",
                vec![Edit {
                    file: PathBuf::from("/tmp/Test.fst"),
                    range: Range::new(5, 1, 6, 1),
                    new_text: String::new(),
                }],
                rules::FixConfidence::Low,
                "May be used via SMTPat",
            )),
        };

        let uri = test_uri();
        let action = to_code_action(&diag, &uri).expect("should produce code action");
        assert_eq!(action.is_preferred, Some(false)); // Unsafe is NOT preferred
    }

    // =====================================================================
    // Range overlap
    // =====================================================================

    #[test]
    fn test_ranges_overlap_same() {
        let r = LspRange {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 10,
            },
        };
        assert!(ranges_overlap(r, r));
    }

    #[test]
    fn test_ranges_overlap_partial() {
        let a = LspRange {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 10,
            },
        };
        let b = LspRange {
            start: Position {
                line: 0,
                character: 5,
            },
            end: Position {
                line: 0,
                character: 15,
            },
        };
        assert!(ranges_overlap(a, b));
        assert!(ranges_overlap(b, a));
    }

    #[test]
    fn test_ranges_no_overlap() {
        let a = LspRange {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 5,
            },
        };
        let b = LspRange {
            start: Position {
                line: 0,
                character: 6,
            },
            end: Position {
                line: 0,
                character: 10,
            },
        };
        assert!(!ranges_overlap(a, b));
        assert!(!ranges_overlap(b, a));
    }

    #[test]
    fn test_ranges_overlap_multiline() {
        let a = LspRange {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 5,
                character: 0,
            },
        };
        let b = LspRange {
            start: Position {
                line: 3,
                character: 0,
            },
            end: Position {
                line: 8,
                character: 0,
            },
        };
        assert!(ranges_overlap(a, b));
    }

    #[test]
    fn test_ranges_adjacent_no_overlap() {
        let a = LspRange {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 2,
                character: 0,
            },
        };
        let b = LspRange {
            start: Position {
                line: 3,
                character: 0,
            },
            end: Position {
                line: 5,
                character: 0,
            },
        };
        assert!(!ranges_overlap(a, b));
    }

    // =====================================================================
    // LintSettings
    // =====================================================================

    #[test]
    fn test_lint_settings_default() {
        let s = LintSettings::default();
        assert!(s.enabled);
        assert!(s.select.is_empty());
        assert!(s.ignore.is_empty());
        assert!(s.lint_on_open);
        assert!(s.lint_on_change);
        assert_eq!(s.debounce_ms, 300);
    }

    #[test]
    fn test_lint_settings_deserialize_partial() {
        let json = r#"{"enabled": false, "debounceMs": 500}"#;
        let s: LintSettings = serde_json::from_str(json).unwrap();
        assert!(!s.enabled);
        assert_eq!(s.debounce_ms, 500);
        // Defaults for unspecified fields
        assert!(s.select.is_empty());
        assert!(s.lint_on_open);
    }

    #[test]
    fn test_lint_settings_deserialize_full() {
        let json = r#"{
            "enabled": true,
            "select": ["FST001", "FST004"],
            "ignore": ["FST006"],
            "lintOnOpen": false,
            "lintOnChange": true,
            "debounceMs": 100
        }"#;
        let s: LintSettings = serde_json::from_str(json).unwrap();
        assert!(s.enabled);
        assert_eq!(s.select, vec!["FST001", "FST004"]);
        assert_eq!(s.ignore, vec!["FST006"]);
        assert!(!s.lint_on_open);
        assert!(s.lint_on_change);
        assert_eq!(s.debounce_ms, 100);
    }

    #[test]
    fn test_lint_settings_to_config_all_rules() {
        let s = LintSettings::default();
        let config = s.to_lint_config();
        assert!(config.is_rule_enabled(RuleCode::FST001));
        assert!(config.is_rule_enabled(RuleCode::FST004));
    }

    #[test]
    fn test_lint_settings_to_config_select() {
        let s = LintSettings {
            select: vec!["FST001".to_string(), "FST004".to_string()],
            ..Default::default()
        };
        let config = s.to_lint_config();
        assert!(config.is_rule_enabled(RuleCode::FST001));
        assert!(config.is_rule_enabled(RuleCode::FST004));
        assert!(!config.is_rule_enabled(RuleCode::FST006));
    }

    #[test]
    fn test_lint_settings_to_config_ignore() {
        let s = LintSettings {
            ignore: vec!["FST006".to_string()],
            ..Default::default()
        };
        let config = s.to_lint_config();
        assert!(config.is_rule_enabled(RuleCode::FST001));
        assert!(!config.is_rule_enabled(RuleCode::FST006));
    }

    // =====================================================================
    // LintBackend integration
    // =====================================================================

    #[test]
    fn test_lint_backend_empty_file() {
        let backend = LintBackend::default_backend();
        let diags = backend.lint(Path::new("Empty.fst"), "module Empty\n");
        // Should not crash; may or may not produce diagnostics
        let _ = diags;
    }

    #[test]
    fn test_lint_backend_unused_open_produces_diagnostic() {
        let backend = LintBackend::new(LintConfig::new(
            Some("FST004".to_string()),
            None,
            None,
        ));
        let content = "module Test\n\nopen FStar.Pervasives\n\nlet x = 1\n";
        let diags = backend.lint(Path::new("Test.fst"), content);

        // FST004 should flag the unused open
        let fst004: Vec<_> = diags
            .iter()
            .filter(|d| d.code == Some(NumberOrString::String("FST004".to_string())))
            .collect();
        assert!(
            !fst004.is_empty(),
            "FST004 should detect unused open FStar.Pervasives"
        );
        assert_eq!(fst004[0].source, Some("brrr-lint".to_string()));
        assert_eq!(fst004[0].tags, Some(vec![DiagnosticTag::UNNECESSARY]));
    }

    #[test]
    fn test_lint_full_returns_raw_and_lsp() {
        let backend = LintBackend::new(LintConfig::new(
            Some("FST004".to_string()),
            None,
            None,
        ));
        let content = "module Test\n\nopen FStar.Pervasives\n\nlet x = 1\n";
        let (lsp_diags, raw_diags) = backend.lint_full(Path::new("Test.fst"), content);

        assert_eq!(
            lsp_diags.len(),
            raw_diags.len(),
            "LSP and raw diagnostic counts must match"
        );
    }

    #[test]
    fn test_code_actions_filters_by_range() {
        let backend = LintBackend::default_backend();
        let diags = vec![
            Diagnostic {
                rule: RuleCode::FST004,
                severity: DiagnosticSeverity::Warning,
                file: PathBuf::from("/tmp/Test.fst"),
                range: Range::new(3, 1, 3, 25),
                message: "Unused open".to_string(),
                fix: Some(Fix::safe(
                    "Remove open",
                    vec![Edit {
                        file: PathBuf::from("/tmp/Test.fst"),
                        range: Range::new(3, 1, 4, 1),
                        new_text: String::new(),
                    }],
                )),
            },
            Diagnostic {
                rule: RuleCode::FST006,
                severity: DiagnosticSeverity::Warning,
                file: PathBuf::from("/tmp/Test.fst"),
                range: Range::new(10, 1, 10, 20),
                message: "Naming issue".to_string(),
                fix: None,
            },
        ];

        let uri = test_uri();

        // Range that covers only line 3 (0-indexed: line 2)
        let range = LspRange {
            start: Position {
                line: 2,
                character: 0,
            },
            end: Position {
                line: 2,
                character: 30,
            },
        };
        let actions = backend.code_actions(&uri, range, &diags);
        assert_eq!(actions.len(), 1, "Only FST004 fix should match this range");
        assert!(actions[0].title.contains("FST004"));
    }

    #[test]
    fn test_code_actions_empty_for_no_overlap() {
        let backend = LintBackend::default_backend();
        let diags = vec![Diagnostic {
            rule: RuleCode::FST004,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/tmp/Test.fst"),
            range: Range::new(3, 1, 3, 25),
            message: "Unused open".to_string(),
            fix: Some(Fix::safe("Remove open", vec![])),
        }];

        let uri = test_uri();
        let range = LspRange {
            start: Position {
                line: 50,
                character: 0,
            },
            end: Position {
                line: 51,
                character: 0,
            },
        };
        let actions = backend.code_actions(&uri, range, &diags);
        assert!(actions.is_empty(), "No actions should match a distant range");
    }

    // =====================================================================
    // Progress helpers
    // =====================================================================

    #[test]
    fn test_progress_begin() {
        let p = progress_begin("Test.fst");
        assert_eq!(p.title, "Linting");
        assert!(p.message.unwrap().contains("Test.fst"));
    }

    #[test]
    fn test_progress_end_zero() {
        let p = progress_end(0);
        assert!(p.message.unwrap().contains("No issues"));
    }

    #[test]
    fn test_progress_end_singular() {
        let p = progress_end(1);
        assert!(p.message.unwrap().contains("1 issue found"));
    }

    #[test]
    fn test_progress_end_plural() {
        let p = progress_end(5);
        assert!(p.message.unwrap().contains("5 issues found"));
    }

    // =====================================================================
    // Edge cases
    // =====================================================================

    #[test]
    fn test_code_action_with_multi_file_edit() {
        let diag = Diagnostic {
            rule: RuleCode::FST001,
            severity: DiagnosticSeverity::Warning,
            file: PathBuf::from("/tmp/Test.fst"),
            range: Range::new(5, 1, 8, 1),
            message: "Duplicate type in .fst".to_string(),
            fix: Some(Fix::safe(
                "Remove duplicate",
                vec![Edit {
                    file: PathBuf::from("/tmp/Test.fst"),
                    range: Range::new(5, 1, 8, 1),
                    new_text: String::new(),
                }],
            )),
        };

        let uri = Url::parse("file:///tmp/Test.fst").unwrap();
        let action = to_code_action(&diag, &uri).unwrap();
        assert!(action.title.contains("FST001"));
        assert!(action.title.contains("Remove duplicate"));
    }
}
