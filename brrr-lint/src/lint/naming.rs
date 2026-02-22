//! FST006: Naming convention checker for F* code.
//!
//! Enforces real F* naming conventions derived from comprehensive analysis of
//! FStar/ulib, hacl-star/code, and everparse/src (hundreds of files):
//!
//! **Modules**: Dot-separated CamelCase components. Standard prefixes are
//! `Spec.`, `Impl.`, `Hacl.`, `Hacl.Spec.`, `Hacl.Impl.`, `Hacl.Meta.`,
//! `FStar.`, `LowStar.`, `LowParse.`, `Lib.`. Each component must start
//! with an uppercase letter. Examples: `Hacl.Impl.Chacha20.Core32`,
//! `Spec.Hash.Definitions`, `FStar.List.Tot.Base`.
//!
//! **Types**: Must start with lowercase. snake_case is the dominant convention:
//! `hash_alg`, `sha2_alg`, `range_t`, `bare_parser`. The suffix `_t` is
//! idiomatic for type abbreviations (`modBits_t`, `pub_int_t`). camelCase is
//! also accepted (`inttype`, `buftype`). PascalCase types are flagged because
//! they collide with constructors/modules.
//!
//! **Functions/values**: Must start with lowercase. snake_case (`chacha20_encrypt`,
//! `load_state`, `fold_left`) and camelCase (`loadState`, `fillT`, `mapT`) are
//! both widely used. PascalCase is flagged.
//!
//! **Lemmas**: Functions with Lemma effect should follow `lemma_*` prefix or
//! `*_lemma` suffix convention (e.g., `lemma_mod_plus`, `transpose4_lemma`).
//! This is the overwhelming pattern in FStar.Math.Lemmas and HACL* specs.
//!
//! **Effects**: CamelCase starting with uppercase (e.g., `Tot`, `GTot`, `Lemma`,
//! `Stack`, `ST`). This is enforced by the F* compiler itself.
//!
//! **Constructors**: Must start with uppercase (CamelCase). Extracted from
//! algebraic type definitions: `| SHA2_256`, `| Blake2S`, `| U8`, `| Some`.
//! ALL_CAPS with underscores is also valid (`MUT`, `IMMUT`, `CONST`).
//!
//! **Operator names**: Names consisting of F* operator characters
//! (`+.`, `*!`, `|+|`, `=.`, etc.) are skipped.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::parser::{parse_fstar_file, BlockType, DeclarationBlock};
use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};

lazy_static! {
    /// Recognized standard module prefixes from HACL*, FStar, EverParse, LowStar.
    static ref STANDARD_MODULE_PREFIXES: Vec<&'static str> = vec![
        "Spec.",
        "Impl.",
        "Hacl.",
        "Hacl.Spec.",
        "Hacl.Impl.",
        "Hacl.Meta.",
        "FStar.",
        "LowStar.",
        "LowParse.",
        "Lib.",
        "Prims",
        "Steel.",
        "Pulse.",
        "Vale.",
        "EverCrypt.",
        "EverParse.",
        "Meta.",
        "Test.",
    ];

    /// Constructor line pattern in algebraic type definitions.
    /// Matches lines like `  | SHA2_256` or `  | Some of 'a` or `  | Cons : ...`
    static ref CONSTRUCTOR_LINE: Regex = Regex::new(
        r"^\s*\|\s+([A-Z][a-zA-Z0-9_]*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// F* operator character set. Names made entirely of these chars (plus dots)
    /// are operators, not identifiers, and should be skipped.
    static ref OPERATOR_CHARS: Regex = Regex::new(
        r"^[!@#\$%\^&\*\+\-\./\\<>=\|~\?:]+$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

/// Check if name starts with uppercase (looks like constructor/module/effect).
fn starts_with_uppercase(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_uppercase())
}

/// Check if a name consists entirely of F* operator characters.
/// These should be skipped by naming checks (e.g., `+.`, `*!`, `|+|`, `=.`).
fn is_operator_name(name: &str) -> bool {
    OPERATOR_CHARS.is_match(name)
}

/// Check if a module name follows the standard F* module prefix conventions.
fn has_standard_module_prefix(name: &str) -> bool {
    STANDARD_MODULE_PREFIXES.iter().any(|prefix| {
        name.starts_with(prefix) || name == prefix.trim_end_matches('.')
    })
}

/// Check if a module name has valid dot-separated CamelCase structure.
fn is_valid_module_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    // Each dot-separated component must start with uppercase
    name.split('.').all(|component| {
        !component.is_empty() && component.starts_with(|c: char| c.is_ascii_uppercase())
    })
}

/// Check whether a name follows the lemma naming convention.
/// Returns true if the name has `lemma_` prefix or `_lemma` suffix.
fn follows_lemma_naming(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("lemma_") || lower.ends_with("_lemma")
        || lower.starts_with("lemma")  // e.g., `lemmaFoo` camelCase variant
}

/// Extract constructor names from a type block's lines.
/// Looks for `| ConstructorName` patterns in algebraic data type definitions.
fn extract_constructors(block: &DeclarationBlock) -> Vec<(String, usize)> {
    let mut constructors = Vec::new();
    for (offset, line) in block.lines.iter().enumerate() {
        if let Some(caps) = CONSTRUCTOR_LINE.captures(line) {
            if let Some(m) = caps.get(1) {
                let line_num = block.start_line + offset;
                constructors.push((m.as_str().to_string(), line_num));
            }
        }
    }
    constructors
}

/// Convert a PascalCase name to snake_case for suggestion purposes.
///
/// Examples:
/// - "BadType" -> "bad_type"
/// - "FooBar" -> "foo_bar"
/// - "XMLParser" -> "xml_parser"
fn to_snake_case(name: &str) -> String {
    let mut result = String::with_capacity(name.len() + 4);
    let mut prev_was_upper = false;
    let mut prev_was_underscore = true;

    for (i, c) in name.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 && !prev_was_underscore {
                let next_is_lower = name
                    .chars()
                    .nth(i + 1)
                    .map(|n| n.is_lowercase())
                    .unwrap_or(false);
                if !prev_was_upper || next_is_lower {
                    result.push('_');
                }
            }
            result.push(c.to_ascii_lowercase());
            prev_was_upper = true;
            prev_was_underscore = false;
        } else if c == '_' {
            result.push(c);
            prev_was_upper = false;
            prev_was_underscore = true;
        } else {
            result.push(c);
            prev_was_upper = false;
            prev_was_underscore = false;
        }
    }

    result
}

/// FST006: Naming convention checker rule.
pub struct NamingRule;

impl NamingRule {
    pub fn new() -> Self {
        Self
    }
}

impl Default for NamingRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for NamingRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST006
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (header_lines, blocks) = parse_fstar_file(content);

        // Check module name from header (first `module` line)
        check_module_name(file, &header_lines, &mut diagnostics);

        for block in &blocks {
            // Check constructor naming in type blocks
            if block.block_type == BlockType::Type {
                check_constructor_naming(file, block, &mut diagnostics);
            }

            for name in &block.names {
                // Skip names starting with underscore (intentionally unused/internal)
                if name.starts_with('_') {
                    continue;
                }

                // Skip operator names (+., *!, |+|, etc.)
                if is_operator_name(name) {
                    continue;
                }

                // Strip trailing primes for checking (e.g., expr', pattern')
                let check_name = name.trim_end_matches('\'');
                if check_name.is_empty() {
                    continue;
                }

                match block.block_type {
                    BlockType::Type => {
                        check_type_naming(file, block, name, check_name, &mut diagnostics);
                    }

                    BlockType::Let
                    | BlockType::Val
                    | BlockType::UnfoldLet
                    | BlockType::InlineLet => {
                        check_function_naming(file, block, name, check_name, &mut diagnostics);
                    }

                    BlockType::Effect | BlockType::NewEffect | BlockType::EffectAbbrev => {
                        check_effect_naming(file, block, name, check_name, &mut diagnostics);
                    }

                    // Skip other block types (Module, Open, Friend, etc.)
                    _ => {}
                }
            }
        }

        diagnostics
    }
}

/// Check module name from header lines.
fn check_module_name(
    file: &Path,
    header_lines: &[String],
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (i, line) in header_lines.iter().enumerate() {
        let trimmed = line.trim();
        // Find the `module Foo.Bar.Baz` line (not module abbreviations like `module M = ...`)
        if trimmed.starts_with("module ") && !trimmed.contains('=') {
            let module_name = trimmed.strip_prefix("module ").unwrap_or("").trim();
            if module_name.is_empty() {
                continue;
            }

            let line_num = i + 1;

            // Check dot-separated CamelCase structure
            if !is_valid_module_name(module_name) {
                let bad_components: Vec<&str> = module_name
                    .split('.')
                    .filter(|c| !c.is_empty() && !c.starts_with(|ch: char| ch.is_ascii_uppercase()))
                    .collect();
                if !bad_components.is_empty() {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST006,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "Module `{}`: each dot-separated component must start \
                             with uppercase (CamelCase). Bad component(s): {}",
                            module_name,
                            bad_components.join(", ")
                        ),
                        fix: None,
                    });
                }
            }

            // Suggest standard prefixes for top-level modules
            if !has_standard_module_prefix(module_name) {
                // Only suggest for multi-component names (single component = test/scratch)
                if module_name.contains('.') {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST006,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "Module `{}` does not use a standard F* prefix. \
                             Consider: Spec.*, Impl.*, Hacl.*, FStar.*, \
                             LowStar.*, Lib.*, or similar",
                            module_name
                        ),
                        fix: None,
                    });
                }
            }

            break; // Only check first module declaration
        }
    }
}

/// Check type naming conventions.
fn check_type_naming(
    file: &Path,
    block: &DeclarationBlock,
    name: &str,
    check_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Types must start with lowercase in F*.
    // Names starting with uppercase look like constructors or modules.
    if starts_with_uppercase(check_name) {
        let suggested = to_snake_case(check_name);
        diagnostics.push(Diagnostic {
            rule: RuleCode::FST006,
            severity: DiagnosticSeverity::Info,
            file: file.to_path_buf(),
            range: Range::point(block.start_line, 1),
            message: format!(
                "Type `{}` should start with lowercase. \
                 PascalCase is reserved for constructors/modules. \
                 Suggested: `{}`",
                name, suggested
            ),
            fix: None,
        });
    }
}

/// Check function/value naming conventions.
fn check_function_naming(
    file: &Path,
    block: &DeclarationBlock,
    name: &str,
    check_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Functions/values must start with lowercase in F*.
    // Both snake_case and camelCase are accepted.
    if starts_with_uppercase(check_name) {
        let suggested = to_snake_case(check_name);
        diagnostics.push(Diagnostic {
            rule: RuleCode::FST006,
            severity: DiagnosticSeverity::Info,
            file: file.to_path_buf(),
            range: Range::point(block.start_line, 1),
            message: format!(
                "Function/value `{}` should start with lowercase. \
                 PascalCase is reserved for constructors/modules. \
                 Suggested: `{}`",
                name, suggested
            ),
            fix: None,
        });
    }

    // Check lemma naming convention for functions with Lemma effect.
    // Use the block's effect_signature if available.
    if !starts_with_uppercase(check_name) {
        let has_lemma_effect = block
            .effect_signature
            .as_ref()
            .map(|sig| sig.is_lemma_effect())
            .unwrap_or(false);

        if has_lemma_effect && !follows_lemma_naming(check_name) {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST006,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::point(block.start_line, 1),
                message: format!(
                    "Lemma `{}` should follow naming convention: \
                     `lemma_*` prefix or `*_lemma` suffix \
                     (e.g., `lemma_{}` or `{}_lemma`)",
                    name, check_name, check_name
                ),
                fix: None,
            });
        }
    }
}

/// Check effect naming conventions.
fn check_effect_naming(
    file: &Path,
    block: &DeclarationBlock,
    name: &str,
    check_name: &str,
    diagnostics: &mut Vec<Diagnostic>,
) {
    // Effects must start with uppercase (CamelCase) in F*.
    // sub_effect names are of the form SRC~>DST which is not a CamelCase name.
    if !starts_with_uppercase(check_name) {
        diagnostics.push(Diagnostic {
            rule: RuleCode::FST006,
            severity: DiagnosticSeverity::Info,
            file: file.to_path_buf(),
            range: Range::point(block.start_line, 1),
            message: format!(
                "Effect `{}` should use CamelCase (start with uppercase)",
                name
            ),
            fix: None,
        });
    }
}

/// Check constructor naming within algebraic type definitions.
fn check_constructor_naming(
    file: &Path,
    block: &DeclarationBlock,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let constructors = extract_constructors(block);
    for (ctor_name, line_num) in constructors {
        // Constructors must start with uppercase
        if !starts_with_uppercase(&ctor_name) {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST006,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(line_num, 1),
                message: format!(
                    "Constructor `{}` must start with uppercase (CamelCase). \
                     F* requires constructors to be capitalized",
                    ctor_name
                ),
                fix: None,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    // =========================================================================
    // Helper utilities
    // =========================================================================

    fn check(content: &str) -> Vec<Diagnostic> {
        let rule = NamingRule::new();
        let file = PathBuf::from("test.fst");
        rule.check(&file, content)
    }

    fn has_message_containing(diagnostics: &[Diagnostic], needle: &str) -> bool {
        diagnostics.iter().any(|d| d.message.contains(needle))
    }

    fn count_with_severity(diagnostics: &[Diagnostic], severity: DiagnosticSeverity) -> usize {
        diagnostics.iter().filter(|d| d.severity == severity).count()
    }

    // =========================================================================
    // Utility function tests
    // =========================================================================

    #[test]
    fn test_starts_with_uppercase() {
        assert!(starts_with_uppercase("Foo"));
        assert!(starts_with_uppercase("FooBar"));
        assert!(starts_with_uppercase("Tot"));
        assert!(starts_with_uppercase("GTot"));
        assert!(starts_with_uppercase("FOO_BAR"));

        assert!(!starts_with_uppercase("foo"));
        assert!(!starts_with_uppercase("fooBar"));
        assert!(!starts_with_uppercase("_foo"));
    }

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("BadType"), "bad_type");
        assert_eq!(to_snake_case("FooBar"), "foo_bar");
        assert_eq!(to_snake_case("foo"), "foo");
        assert_eq!(to_snake_case("XMLParser"), "xml_parser");
        assert_eq!(to_snake_case("SHA2"), "sha2");
        assert_eq!(to_snake_case("SHA2_256"), "sha2_256");
        assert_eq!(to_snake_case("HTTPSServer"), "https_server");
    }

    #[test]
    fn test_is_operator_name() {
        assert!(is_operator_name("+."));
        assert!(is_operator_name("*!"));
        assert!(is_operator_name("|+|"));
        assert!(is_operator_name("=."));
        assert!(is_operator_name("=="));
        assert!(is_operator_name("<=."));
        assert!(is_operator_name("+!"));

        assert!(!is_operator_name("foo"));
        assert!(!is_operator_name("Foo"));
        assert!(!is_operator_name("foo_bar"));
        assert!(!is_operator_name("x1"));
    }

    #[test]
    fn test_is_valid_module_name() {
        assert!(is_valid_module_name("FStar"));
        assert!(is_valid_module_name("FStar.List"));
        assert!(is_valid_module_name("FStar.List.Tot"));
        assert!(is_valid_module_name("Hacl.Impl.Chacha20.Core32"));
        assert!(is_valid_module_name("Spec.Hash.Definitions"));
        assert!(is_valid_module_name("Test"));

        assert!(!is_valid_module_name("fstar.list"));
        assert!(!is_valid_module_name("FStar.list"));
        assert!(!is_valid_module_name(""));
        assert!(!is_valid_module_name(".FStar"));
    }

    #[test]
    fn test_has_standard_module_prefix() {
        assert!(has_standard_module_prefix("Spec.Chacha20"));
        assert!(has_standard_module_prefix("Hacl.Impl.SHA2"));
        assert!(has_standard_module_prefix("FStar.List.Tot"));
        assert!(has_standard_module_prefix("LowStar.Buffer"));
        assert!(has_standard_module_prefix("LowParse.Spec.Base"));
        assert!(has_standard_module_prefix("Lib.IntTypes"));

        assert!(!has_standard_module_prefix("Custom.Module"));
        assert!(!has_standard_module_prefix("MyProject.Core"));
    }

    #[test]
    fn test_follows_lemma_naming() {
        assert!(follows_lemma_naming("lemma_mod_plus"));
        assert!(follows_lemma_naming("lemma_pow2_128"));
        assert!(follows_lemma_naming("transpose4_lemma"));
        assert!(follows_lemma_naming("state_spec_v_lemma"));
        assert!(follows_lemma_naming("lemmaFoo"));

        assert!(!follows_lemma_naming("add_identity"));
        assert!(!follows_lemma_naming("mul_commutativity"));
        assert!(!follows_lemma_naming("check_something"));
    }

    // =========================================================================
    // Module naming tests
    // =========================================================================

    #[test]
    fn test_module_valid_standard_prefixes() {
        // Valid standard module names should produce no warnings
        for module in &[
            "Spec.Chacha20",
            "Hacl.Impl.Chacha20.Core32",
            "Hacl.Spec.Chacha20.Lemmas",
            "FStar.List.Tot.Base",
            "LowStar.Buffer",
            "LowParse.Spec.Base",
            "Lib.IntTypes",
        ] {
            let content = format!("module {}\n\nlet x = 1\n", module);
            let diags = check(&content);
            let module_diags: Vec<_> = diags.iter()
                .filter(|d| d.message.contains("Module"))
                .collect();
            assert!(
                module_diags.is_empty(),
                "Module `{}` should not be flagged, got: {:?}",
                module,
                module_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn test_module_non_standard_prefix_hint() {
        let content = "module Custom.MyProject.Core\n\nlet x = 1\n";
        let diags = check(content);
        let module_hints: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("standard F* prefix"))
            .collect();
        assert_eq!(module_hints.len(), 1);
        assert_eq!(module_hints[0].severity, DiagnosticSeverity::Hint);
    }

    #[test]
    fn test_module_single_component_no_prefix_hint() {
        // Single-component module names (like "Test") should not get prefix hints
        let content = "module Test\n\nlet x = 1\n";
        let diags = check(content);
        let prefix_hints: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("standard F* prefix"))
            .collect();
        assert!(prefix_hints.is_empty());
    }

    #[test]
    fn test_module_bad_component_casing() {
        let content = "module FStar.list.tot\n\nlet x = 1\n";
        let diags = check(content);
        assert!(
            has_message_containing(&diags, "component must start with uppercase"),
            "Expected warning about lowercase component, got: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // Type naming tests
    // =========================================================================

    #[test]
    fn test_type_pascal_case_flagged() {
        let content = "module Test\n\ntype BadType = int\ntype good_type = int\n";
        let diags = check(content);
        assert_eq!(
            diags.iter().filter(|d| d.message.contains("BadType")).count(),
            1
        );
        assert!(has_message_containing(&diags, "lowercase"));
    }

    #[test]
    fn test_type_snake_case_accepted() {
        let content = "module Test\n\ntype inttype = int\ntype range_t = int\ntype secrecy_level = int\n";
        let diags = check(content);
        let type_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Type"))
            .collect();
        assert!(type_diags.is_empty());
    }

    #[test]
    fn test_type_t_suffix_accepted() {
        // _t suffix is idiomatic in HACL* (modBits_t, pub_int_t, range_t)
        let content = "module Test\n\ntype modBits_t = int\ntype pub_int_t = int\n";
        let diags = check(content);
        let type_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Type"))
            .collect();
        assert!(type_diags.is_empty());
    }

    #[test]
    fn test_type_abstract_t() {
        // Abstract type `t` is the standard F* convention (FStar.Set, FStar.Map)
        let content = "module Test\n\nval t : Type0\n";
        let diags = check(content);
        let flagged: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("`t`"))
            .collect();
        assert!(flagged.is_empty());
    }

    // =========================================================================
    // Function naming tests
    // =========================================================================

    #[test]
    fn test_function_camelcase_accepted() {
        let content = r#"module Test

val loadState : int -> int
let loadState x = x

val createL : int -> int
let createL x = x

val storeState_inner : int -> int
let storeState_inner x = x

val good_func : int -> int
let good_func x = x
"#;
        let diags = check(content);
        let func_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(
            func_diags.is_empty(),
            "Expected no function diagnostics for camelCase, got: {:?}",
            func_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_function_pascal_case_flagged() {
        let content = "module Test\n\nval BadFunc : int -> int\nlet BadFunc x = x\n";
        let diags = check(content);
        let bad_func_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("BadFunc"))
            .collect();
        assert_eq!(bad_func_diags.len(), 2); // val + let
        assert!(bad_func_diags[0].message.contains("lowercase"));
    }

    #[test]
    fn test_function_underscore_prefix_skipped() {
        let content = "module Test\n\nval _internal : int -> int\nlet _internal x = x\n";
        let diags = check(content);
        let func_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("_internal"))
            .collect();
        assert!(func_diags.is_empty());
    }

    #[test]
    fn test_function_primed_names() {
        let content = r#"module Test

val foo' : int -> int
let foo' x = x

val loadState' : int -> int
let loadState' x = x
"#;
        let diags = check(content);
        let func_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(
            func_diags.is_empty(),
            "Expected no diagnostics for primed names, got: {:?}",
            func_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_hacl_star_naming_patterns() {
        // Real patterns from hacl-star that MUST NOT be flagged
        let content = r#"module Test

val sigmaTable : int -> int
let sigmaTable x = x

val ivTable_S : int -> int
let ivTable_S x = x

val rTable_B : int -> int
let rTable_B x = x

val msgHash2 : int -> int
let msgHash2 x = x

val modBits_t : int -> int
let modBits_t x = x

inline_for_extraction let fillT x = x

unfold let createL x = x
"#;
        let diags = check(content);
        let func_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function") || d.message.contains("Type"))
            .collect();
        assert!(
            func_diags.is_empty(),
            "Expected no diagnostics for hacl-star patterns, got: {:?}",
            func_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // Lemma naming tests
    // =========================================================================

    #[test]
    fn test_lemma_with_proper_prefix() {
        let content = r#"module Test

val lemma_mod_plus : a:int -> k:int -> n:int -> Lemma (ensures True)
let lemma_mod_plus a k n = ()
"#;
        let diags = check(content);
        let lemma_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Lemma") && d.message.contains("naming convention"))
            .collect();
        assert!(
            lemma_diags.is_empty(),
            "lemma_mod_plus should not be flagged, got: {:?}",
            lemma_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lemma_with_proper_suffix() {
        let content = r#"module Test

val transpose4_lemma : int -> Lemma (ensures True)
let transpose4_lemma x = ()
"#;
        let diags = check(content);
        let lemma_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("naming convention"))
            .collect();
        assert!(
            lemma_diags.is_empty(),
            "transpose4_lemma should not be flagged, got: {:?}",
            lemma_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lemma_without_convention_flagged() {
        let content = r#"module Test

val add_identity : int -> Lemma (ensures True)
let add_identity x = ()
"#;
        let diags = check(content);
        let lemma_hints: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("naming convention") && d.message.contains("add_identity"))
            .collect();
        // Should produce hint-level diagnostics for missing lemma prefix/suffix
        assert!(
            !lemma_hints.is_empty(),
            "add_identity with Lemma effect should get naming hint"
        );
        assert_eq!(lemma_hints[0].severity, DiagnosticSeverity::Hint);
    }

    #[test]
    fn test_non_lemma_not_checked_for_lemma_naming() {
        // Regular functions should NOT get lemma naming hints
        let content = r#"module Test

val add_identity : int -> int
let add_identity x = x
"#;
        let diags = check(content);
        let lemma_hints: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("naming convention"))
            .collect();
        assert!(lemma_hints.is_empty());
    }

    // =========================================================================
    // Effect naming tests
    // =========================================================================

    #[test]
    fn test_effect_camelcase_required() {
        let content = "module Test\n\neffect bad_effect = Tot\neffect GoodEffect = Tot\n";
        let diags = check(content);
        assert_eq!(
            diags.iter().filter(|d| d.message.contains("bad_effect")).count(),
            1
        );
        assert!(has_message_containing(&diags, "CamelCase"));
    }

    #[test]
    fn test_effect_standard_names_accepted() {
        // Standard F* effect names
        let content = "module Test\n\neffect MyStack (a:Type) = Stack a\n";
        let diags = check(content);
        let effect_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Effect") && d.message.contains("CamelCase"))
            .collect();
        assert!(effect_diags.is_empty());
    }

    // =========================================================================
    // Constructor naming tests
    // =========================================================================

    #[test]
    fn test_constructor_uppercase_accepted() {
        let content = r#"module Test

type hash_alg =
  | SHA2_224
  | SHA2_256
  | Blake2S
  | Blake2B
"#;
        let diags = check(content);
        let ctor_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Constructor"))
            .collect();
        assert!(ctor_diags.is_empty());
    }

    #[test]
    fn test_constructor_all_caps_accepted() {
        let content = r#"module Test

type buftype =
  | MUT
  | IMMUT
  | CONST
"#;
        let diags = check(content);
        let ctor_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Constructor"))
            .collect();
        assert!(ctor_diags.is_empty());
    }

    #[test]
    fn test_constructor_inttype_pattern() {
        let content = r#"module Test

type inttype =
  | U1
  | U8
  | U16
  | U32
  | U64
  | U128
  | S8
  | S16
  | S32
  | S64
  | S128
"#;
        let diags = check(content);
        let ctor_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Constructor"))
            .collect();
        assert!(ctor_diags.is_empty());
    }

    #[test]
    fn test_constructor_standard_option_list() {
        let content = r#"module Test

type my_option (a:Type) =
  | MySome : v:a -> my_option a
  | MyNone : my_option a
"#;
        let diags = check(content);
        let ctor_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Constructor"))
            .collect();
        assert!(ctor_diags.is_empty());
    }

    // =========================================================================
    // Operator name tests
    // =========================================================================

    #[test]
    fn test_operator_names_skipped() {
        // F* operator-like names should be silently skipped
        assert!(is_operator_name("+."));
        assert!(is_operator_name("*!"));
        assert!(is_operator_name("|+|"));
        assert!(is_operator_name("=."));
        assert!(!is_operator_name("add"));
    }

    // =========================================================================
    // Comprehensive real-world pattern tests
    // =========================================================================

    #[test]
    fn test_fstar_ulib_patterns() {
        // Patterns from FStar.Seq.Base, FStar.Math.Lemmas, FStar.Ghost
        let content = r#"module FStar.Seq.Base

val length : int -> int
let length x = x

val index : int -> int -> int
let index s i = i

val create : int -> int -> int
let create n v = v

val empty : int
let empty = 0

val upd : int -> int -> int -> int
let upd s n v = s

val append : int -> int -> int
let append s1 s2 = s1

val lemma_empty : int -> Lemma (ensures True)
let lemma_empty s = ()
"#;
        let diags = check(content);
        let bad_diags: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function") || d.message.contains("Type")
            })
            .collect();
        assert!(
            bad_diags.is_empty(),
            "FStar.Seq.Base patterns should not be flagged, got: {:?}",
            bad_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_hacl_impl_patterns() {
        // Patterns from Hacl.Impl.Chacha20.Core32
        let content = r#"module Hacl.Impl.Chacha20.Core32

type state = int
type index = int

val create_state : int -> int
let create_state x = x

val load_state : int -> int -> int
let load_state st b = st

val store_state : int -> int -> int
let store_state b st = b

val set_counter : int -> int -> int
let set_counter st c = st

val incr_counter : int -> int
let incr_counter st = st
"#;
        let diags = check(content);
        let naming_diags: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function") || d.message.contains("Type")
            })
            .collect();
        assert!(
            naming_diags.is_empty(),
            "Hacl.Impl patterns should not be flagged, got: {:?}",
            naming_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_hacl_spec_lemma_patterns() {
        // Patterns from Hacl.Spec.Chacha20.Lemmas
        let content = r#"module Hacl.Spec.Chacha20.Lemmas

val transpose4_lemma : int -> int -> Lemma (ensures True)
let transpose4_lemma k i = ()

val transpose8_lemma : int -> int -> Lemma (ensures True)
let transpose8_lemma k i = ()

val transpose_lemma_index : int -> int -> Lemma (ensures True)
let transpose_lemma_index k i = ()
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function")
                || (d.message.contains("naming convention") && d.severity != DiagnosticSeverity::Hint)
            })
            .collect();
        assert!(
            naming_issues.is_empty(),
            "HACL* lemma patterns should not be flagged, got: {:?}",
            naming_issues.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_spec_hash_definitions_patterns() {
        // Patterns from Spec.Hash.Definitions
        let content = r#"module Spec.Hash.Definitions

type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA1
  | MD5
  | Blake2S
  | Blake2B

let is_sha2 x = true
let is_keccak x = true
let is_shake x = true
let is_blake x = true
let is_md x = true

type sha2_alg = int
type keccak_alg = int
type blake_alg = int
type md_alg = int
type fixed_len_alg = int
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function")
                || d.message.contains("Type")
                || d.message.contains("Constructor")
            })
            .collect();
        assert!(
            naming_issues.is_empty(),
            "Spec.Hash.Definitions patterns should not be flagged, got: {:?}",
            naming_issues.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lib_intypes_patterns() {
        // Patterns from Lib.IntTypes
        let content = r#"module Lib.IntTypes

type inttype =
  | U1
  | U8
  | U16
  | U32
  | U64
  | U128
  | S8
  | S16
  | S32
  | S64
  | S128

let unsigned x = true
let signed x = false
let numbytes x = 1
let bits x = 8
let modulus x = 256
let maxint x = 255
let minint x = 0
type range_t = int
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function")
                || d.message.contains("Type")
                || d.message.contains("Constructor")
            })
            .collect();
        assert!(
            naming_issues.is_empty(),
            "Lib.IntTypes patterns should not be flagged, got: {:?}",
            naming_issues.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lib_buffer_patterns() {
        // Patterns from Lib.Buffer (buftype, lbuffer, etc.)
        let content = r#"module Lib.Buffer

type buftype =
  | MUT
  | IMMUT
  | CONST

let length x = 0
let to_const x = x
let lbuffer x = x
let lbuffer_t x = x
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function")
                || d.message.contains("Type")
                || d.message.contains("Constructor")
            })
            .collect();
        assert!(
            naming_issues.is_empty(),
            "Lib.Buffer patterns should not be flagged, got: {:?}",
            naming_issues.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lowparse_patterns() {
        // Patterns from LowParse.Spec.Base
        let content = r#"module LowParse.Spec.Base

type consumed_length = int
type bare_parser = int

val parse : int -> int
let parse p = p

val injective_precond : int -> int -> int
let injective_precond p b1 = 0
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function") || d.message.contains("Type")
            })
            .collect();
        assert!(naming_issues.is_empty());
    }

    #[test]
    fn test_hacl_rsapss_patterns() {
        // Patterns from Hacl.Impl.RSAPSS
        let content = r#"module Hacl.Impl.RSAPSS

let modBits_t x = x
let rsapss_sign_bn x = x
let rsapss_sign_msg_to_bn x = x
let blocks_bits_lemma x = x
let blocks_numb_lemma x = x
let bn_lt_pow2 x = x
let bn_eval_lt_pow2_modBits x = x
"#;
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_curve25519_patterns() {
        // Patterns from Hacl.Impl.Curve25519.Field51
        let content = r#"module Hacl.Impl.Curve25519.Field51

type felem = int
type felem2 = int
type felem_wide = int

let as_nat x = x
let wide_as_nat x = x
let fevalh x = x
let feval_wideh x = x
let felem_fits x = x
let felem_wide_fits x = x
let as_felem x = x
let mul_inv_t x = x
"#;
        let diags = check(content);
        let naming_issues: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function") || d.message.contains("Type")
            })
            .collect();
        assert!(naming_issues.is_empty());
    }

    #[test]
    fn test_fstar_math_lemmas_patterns() {
        // Patterns from FStar.Math.Lemmas
        let content = r#"module FStar.Math.Lemmas

val lemma_eucl_div_bound : int -> int -> int -> Lemma (ensures True)
let lemma_eucl_div_bound a b q = ()

val lemma_mult_le_left : int -> int -> int -> Lemma (ensures True)
let lemma_mult_le_left a b c = ()

val lemma_mult_lt_sqr : int -> int -> int -> Lemma (ensures True)
let lemma_mult_lt_sqr n m k = ()

val swap_mul : int -> int -> Lemma (ensures True)
let swap_mul a b = ()
"#;
        let diags = check(content);
        // lemma_* functions should not be flagged
        let lemma_prefix_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("lemma_eucl") || d.message.contains("lemma_mult"))
            .collect();
        assert!(lemma_prefix_issues.is_empty());

        // swap_mul with Lemma effect but no lemma_ prefix should get a HINT
        let swap_mul_hints: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("swap_mul") && d.message.contains("naming convention"))
            .collect();
        // We expect hints for swap_mul (both val and let if both have Lemma effect)
        // The val should detect Lemma effect, the let might or might not depending on parser
        assert!(
            !swap_mul_hints.is_empty(),
            "swap_mul with Lemma effect should get naming hint"
        );
        for hint in &swap_mul_hints {
            assert_eq!(hint.severity, DiagnosticSeverity::Hint);
        }
    }

    // =========================================================================
    // Edge cases and regression tests
    // =========================================================================

    #[test]
    fn test_empty_module() {
        let content = "module Test\n";
        let diags = check(content);
        // Should produce no errors
        let naming_diags: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function") || d.message.contains("Type"))
            .collect();
        assert!(naming_diags.is_empty());
    }

    #[test]
    fn test_mk_prefix_pattern() {
        // mk_* factory pattern from HACL*
        let content = "module Test\n\nlet mk_init x = x\nlet mk_alloca x = x\nlet mk_compute x = x\n";
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_is_prefix_pattern() {
        // is_* predicate pattern
        let content = "module Test\n\nlet is_sha2 x = true\nlet is_keccak x = false\n";
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_to_as_prefix_patterns() {
        // to_* and as_* conversion patterns
        let content = "module Test\n\nlet to_blake_alg x = x\nlet as_nat x = x\nlet to_const x = x\n";
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_inline_for_extraction_pattern() {
        let content = "module Test\n\ninline_for_extraction let fast_helper x = x + 1\n";
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_unfold_let_pattern() {
        let content = "module Test\n\nunfold let createEmpty x = x\n";
        let diags = check(content);
        let func_issues: Vec<_> = diags.iter()
            .filter(|d| d.message.contains("Function"))
            .collect();
        assert!(func_issues.is_empty());
    }

    #[test]
    fn test_severity_levels() {
        // Module bad component: Warning
        // Type PascalCase: Info
        // Function PascalCase: Info
        // Effect lowercase: Info
        // Lemma naming: Hint
        // Module non-standard prefix: Hint
        let content = r#"module Custom.Bad.module_name

type BadType = int

val BadFunc : int -> int
let BadFunc x = x

effect bad_effect = Tot
"#;
        let diags = check(content);
        // Check that we have multiple severity levels
        assert!(count_with_severity(&diags, DiagnosticSeverity::Warning) >= 1);
        assert!(count_with_severity(&diags, DiagnosticSeverity::Info) >= 1);
    }

    #[test]
    fn test_no_false_positives_on_module_opens() {
        // open/friend/include lines should not trigger naming checks
        let content = r#"module Test

open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes
open Lib.Buffer

let x = 1
"#;
        let diags = check(content);
        let naming_diags: Vec<_> = diags.iter()
            .filter(|d| {
                d.message.contains("Function")
                || d.message.contains("Type")
                || d.message.contains("Constructor")
            })
            .collect();
        assert!(naming_diags.is_empty());
    }
}
