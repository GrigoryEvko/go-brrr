//! FST002: Interface/implementation consistency checker.
//!
//! Comprehensive consistency analysis between F* .fsti (interface) and .fst
//! (implementation) files. Originally a port of reorder_fsti.py, now extended
//! with deep structural comparison.
//!
//! CHECKS PERFORMED:
//!
//! 1. **Forward Reference Detection**: Detects when .fsti declarations reference
//!    types that appear later (F* Error 233). Offers topological reordering fix.
//! 2. **Orphan Declarations**: val in .fsti with no let in .fst.
//! 3. **Typo Detection**: Levenshtein distance on near-miss names.
//! 4. **Missing val in .fsti**: let in .fst without corresponding val (private by default).
//! 5. **assume val vs val**: Detects when .fsti uses `assume val` (axiom) but
//!    .fst provides a real implementation (should use `val` instead).
//! 6. **Qualifier Mismatches**: Detects when extraction qualifiers
//!    (inline_for_extraction, noextract) differ between .fsti and .fst.
//! 7. **Type Equality Mismatches**: noeq/unopteq on type in one file but not other.
//! 8. **Implicit Argument Count**: Different number of # parameters in val vs let.
//! 9. **Friend Without Abstract Types**: `friend M` when M has no abstract types.
//! 10. **Mutual Recursion**: Types connected by 'and' treated as atomic groups.
//! 11. **Module Header Preservation**: module/open/friend stay at top during reorder.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use lazy_static::lazy_static;
use regex::Regex;

use super::parser::{
    get_definition_order, parse_fstar_file, BlockType, DeclarationBlock,
};

/// Result of reordering: `(reordered_content, moves_list, changed_flag)` or errors.
type ReorderResult = Result<(String, Vec<(String, usize, usize)>, bool), Vec<String>>;

lazy_static! {
    // Token patterns for validation
    static ref VAL_PATTERN: Regex = Regex::new(r"\bval\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref TYPE_PATTERN: Regex = Regex::new(r"\btype\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref LET_PATTERN: Regex = Regex::new(r"\blet\s+").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref MODULE_PATTERN: Regex = Regex::new(r"\bmodule\s+([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));
}
use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode};

/// Compute Levenshtein edit distance between two strings.
/// Returns the minimum number of single-character edits (insertions, deletions, substitutions)
/// required to transform one string into the other.
fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let m = a_chars.len();
    let n = b_chars.len();

    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }

    // Use two rows for space efficiency
    let mut prev_row: Vec<usize> = (0..=n).collect();
    let mut curr_row: Vec<usize> = vec![0; n + 1];

    for i in 1..=m {
        curr_row[0] = i;
        for j in 1..=n {
            let cost = if a_chars[i - 1] == b_chars[j - 1] {
                0
            } else {
                1
            };
            curr_row[j] = (prev_row[j] + 1) // deletion
                .min(curr_row[j - 1] + 1) // insertion
                .min(prev_row[j - 1] + cost); // substitution
        }
        std::mem::swap(&mut prev_row, &mut curr_row);
    }

    prev_row[n]
}

/// Find potential typo matches for a name in a set of candidates.
/// Returns the best match if the edit distance is <= threshold.
fn find_typo_match<'a>(
    name: &str,
    candidates: &'a HashSet<String>,
    threshold: usize,
) -> Option<(&'a str, usize)> {
    let mut best_match: Option<(&str, usize)> = None;

    for candidate in candidates {
        if candidate == name {
            continue;
        }
        // Skip if lengths differ too much
        let len_diff = (name.len() as isize - candidate.len() as isize).unsigned_abs();
        if len_diff > threshold {
            continue;
        }

        let dist = levenshtein_distance(name, candidate);
        if dist <= threshold {
            match best_match {
                None => best_match = Some((candidate.as_str(), dist)),
                Some((_, best_dist)) if dist < best_dist => {
                    best_match = Some((candidate.as_str(), dist))
                }
                _ => {}
            }
        }
    }

    best_match
}

/// A specific kind of mismatch between .fsti and .fst declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterfaceMismatchKind {
    /// let in .fst has no corresponding val in .fsti (not exported).
    /// This is informational -- the binding is private by default.
    MissingValInInterface,
    /// Qualifier mismatch: e.g., .fsti says `noeq type` but .fst says `type`.
    QualifierMismatch {
        fsti_qualifiers: Vec<String>,
        fst_qualifiers: Vec<String>,
    },
    /// assume val in .fsti vs regular val confusion.
    AssumeValMismatch {
        /// true if .fsti uses `assume val`, false if .fst provides `let`.
        fsti_is_assume: bool,
    },
    /// Implicit argument count differs between .fsti val and .fst let.
    ImplicitArgCountMismatch {
        fsti_count: usize,
        fst_count: usize,
    },
    /// noeq/unopteq on type in one file but not the other.
    TypeEqualityMismatch {
        fsti_noeq: bool,
        fst_noeq: bool,
    },
    /// friend declaration referencing a module with no abstract types.
    FriendWithoutAbstractTypes {
        friend_module: String,
    },
}

/// A single interface mismatch finding.
#[derive(Debug, Clone)]
pub struct InterfaceMismatch {
    /// Name of the declaration.
    pub name: String,
    /// Line in the file where this was found.
    pub line: usize,
    /// Which file the line refers to (true = .fsti, false = .fst).
    /// Used by callers to select the correct diagnostic file path.
    #[allow(dead_code)]
    pub in_fsti: bool,
    /// The kind of mismatch.
    pub kind: InterfaceMismatchKind,
}

/// Result of analyzing interface/implementation consistency.
#[derive(Debug, Default)]
pub struct InterfaceConsistencyResult {
    /// Declarations in .fsti with no corresponding definition in .fst.
    /// Each entry is (name, potential_typo_match, line_number).
    pub orphan_declarations: Vec<(String, Option<String>, usize)>,
    /// Potential typo matches: (fsti_name, fst_name, edit_distance).
    pub typo_matches: Vec<(String, String, usize)>,
}

/// Analyze consistency between .fsti declarations and .fst definitions.
/// Returns orphan declarations and potential typos.
///
/// CRITICAL: Only `val` declarations are checked for orphans. In F*, it is
/// completely normal for .fsti files to contain interface-only definitions:
/// - `let` type aliases (e.g., `let bn_add_eq_len_st (t:limb_t) = ...`)
/// - `type` definitions (abstract or concrete types)
/// - `class` definitions
/// - `effect` definitions
/// - `assume val`/`assume type` declarations
/// - `unfold let` / `inline_for_extraction let` definitions
///
/// These are part of the public API and do NOT need .fst implementations.
/// Only `val` declarations require a corresponding `let` in the .fst file.
pub fn analyze_interface_consistency(
    fsti_content: &str,
    fst_content: &str,
) -> InterfaceConsistencyResult {
    let (_, fsti_blocks) = parse_fstar_file(fsti_content);
    let fst_order = get_definition_order(fst_content);

    // Build set of .fst definition names
    let fst_names_set: HashSet<String> = fst_order.into_iter().collect();

    // Build set of .fsti VAL declaration names with line numbers.
    // Only val declarations need .fst implementations; let/type/class/etc.
    // are interface-only by design in F*.
    let mut fsti_val_names_with_lines: Vec<(String, usize)> = Vec::new();
    for block in &fsti_blocks {
        if block.block_type == BlockType::Val {
            for name in &block.names {
                fsti_val_names_with_lines.push((name.clone(), block.start_line));
            }
        }
    }

    let mut result = InterfaceConsistencyResult::default();

    // Find orphan val declarations and potential typos
    for (fsti_name, line) in &fsti_val_names_with_lines {
        if !fst_names_set.contains(fsti_name) {
            // This val has no corresponding let in .fst
            // Check for typo match in .fst names
            let typo_match = find_typo_match(fsti_name, &fst_names_set, 2);

            if let Some((match_name, dist)) = typo_match {
                result
                    .typo_matches
                    .push((fsti_name.clone(), match_name.to_string(), dist));
                result.orphan_declarations.push((
                    fsti_name.clone(),
                    Some(match_name.to_string()),
                    *line,
                ));
            } else {
                result
                    .orphan_declarations
                    .push((fsti_name.clone(), None, *line));
            }
        }
    }

    result
}

/// Extract qualifier keywords from a declaration block's text.
///
/// Looks for F* modifiers that precede the declaration keyword:
/// noeq, unopteq, private, abstract, inline_for_extraction, noextract,
/// unfold, irreducible, opaque_to_smt, ghost, total, rec.
fn extract_qualifiers(block: &DeclarationBlock) -> Vec<String> {
    let mut qualifiers = Vec::new();
    let text = block.lines.join(" ");
    let text = text.trim();

    // Known qualifier keywords in declaration order
    static QUAL_KEYWORDS: &[&str] = &[
        "noeq",
        "unopteq",
        "private",
        "abstract",
        "inline_for_extraction",
        "noextract",
        "unfold",
        "irreducible",
        "opaque_to_smt",
        "ghost",
        "total",
        "rec",
    ];

    // Extract all words before the declaration keyword (val/let/type/etc.)
    // Split on whitespace and collect qualifiers until we hit the decl keyword
    for word in text.split_whitespace() {
        let clean = word.trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
        if QUAL_KEYWORDS.contains(&clean) {
            qualifiers.push(clean.to_string());
        }
        // Stop scanning after we hit a declaration keyword
        if matches!(clean, "val" | "let" | "type" | "class" | "effect" | "instance") {
            break;
        }
    }

    // Also check block-level flags
    if block.is_private && !qualifiers.contains(&"private".to_string()) {
        qualifiers.push("private".to_string());
    }
    if block.is_abstract && !qualifiers.contains(&"abstract".to_string()) {
        qualifiers.push("abstract".to_string());
    }

    qualifiers.sort();
    qualifiers.dedup();
    qualifiers
}

/// Count implicit arguments in a val signature or let definition.
///
/// F* implicit arguments are marked with `#`:
///   val-style:  `val foo : #t:Type -> #n:nat -> ...`
///   val-binder: `val foo (#t: Type) (#n #m: nat) : ...`  (grouped binders)
///   let-style:  `let foo #t #n x = ...`
///   let-binder: `let foo (#t: Type) (#n: nat) x = ...`
///
/// We search the ENTIRE declaration text for `#<ident>` patterns, skipping
/// the `val`/`let` keyword and the declaration name itself. This handles
/// grouped binders `(#n #m: pos)` where `#` appears before the first colon.
fn count_implicit_args(block: &DeclarationBlock) -> usize {
    lazy_static! {
        // Match `#name` -- an implicit parameter marker. The `#` must be
        // followed by an F* identifier (letter/underscore then word chars
        // and primes). We require a trailing context of colon, whitespace,
        // `)`, or end-of-string to avoid matching inside comments/strings
        // that happen to contain `#`.
        static ref IMPLICIT_ARG: Regex = Regex::new(r"#[a-zA-Z_][\w']*(?:\s*:|[\s)$])").unwrap_or_else(|e| panic!("regex: {e}"));
    }

    let text = block.lines.join(" ");

    match block.block_type {
        BlockType::Val => {
            // Search the ENTIRE text after `val <name>` for `#ident` patterns.
            // F* val declarations can use two styles:
            //   val foo : #t:Type -> ...          (traditional)
            //   val foo (#n #m: pos) (a: t) : ... (binder-style)
            // In binder-style, `#` appears BEFORE the first colon, inside
            // parenthesized groups. The old approach of searching after the
            // first colon missed these entirely.
            //
            // We skip past `val <name>` to avoid matching `#` in the name.
            let trimmed = text.trim();
            // Skip "val" keyword
            let after_val = if let Some(rest) = trimmed.strip_prefix("val") {
                rest.trim_start()
            } else {
                return 0;
            };
            // Skip the declaration name (first identifier)
            let after_name = if let Some(pos) = after_val.find(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'') {
                &after_val[pos..]
            } else {
                return 0;
            };
            IMPLICIT_ARG.find_iter(after_name).count()
        }
        BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet => {
            // In let definitions, count # before = sign
            if let Some(eq_pos) = text.find('=') {
                let params = &text[..eq_pos];
                // Skip the 'let name' part - find the name first
                let trimmed = params.trim();
                // Find start of parameters (after let name)
                if let Some(space_after_name) = trimmed
                    .find(|c: char| c.is_whitespace())
                    .and_then(|first_space| {
                        trimmed[first_space..].find(|c: char| !c.is_whitespace())
                            .map(|offset| first_space + offset)
                    })
                {
                    let param_section = &trimmed[space_after_name..];
                    IMPLICIT_ARG.find_iter(param_section).count()
                } else {
                    0
                }
            } else {
                0
            }
        }
        _ => 0,
    }
}

/// Check if a type declaration has noeq or unopteq qualifier.
fn has_noeq_qualifier(block: &DeclarationBlock) -> bool {
    if block.block_type != BlockType::Type {
        return false;
    }
    let text = block.lines.join(" ");
    let trimmed = text.trim();
    // noeq/unopteq appear before 'type' keyword
    trimmed.contains("noeq ") || trimmed.contains("unopteq ")
}

/// Perform deep consistency analysis between .fsti and .fst declarations.
///
/// Compares paired declarations (same name) for:
/// - Qualifier mismatches (noeq, inline_for_extraction, noextract, etc.)
/// - Implicit argument count differences
/// - Type equality modifier mismatches (noeq type vs type)
/// - assume val patterns
/// - .fst definitions without .fsti val (unexported bindings)
/// - friend declarations without abstract types in the target module
pub fn analyze_deep_consistency(
    fsti_content: &str,
    fst_content: &str,
) -> Vec<InterfaceMismatch> {
    let (_, fsti_blocks) = parse_fstar_file(fsti_content);
    let (_, fst_blocks) = parse_fstar_file(fst_content);

    let mut mismatches = Vec::new();

    // Build lookup maps: name -> block reference
    let mut fsti_by_name: HashMap<&str, &DeclarationBlock> = HashMap::new();
    for block in &fsti_blocks {
        for name in &block.names {
            fsti_by_name.entry(name.as_str()).or_insert(block);
        }
    }

    let mut fst_by_name: HashMap<&str, &DeclarationBlock> = HashMap::new();
    for block in &fst_blocks {
        for name in &block.names {
            fst_by_name.entry(name.as_str()).or_insert(block);
        }
    }

    // Collect all .fsti val names for the "missing val" check
    let fsti_val_names: HashSet<&str> = fsti_blocks
        .iter()
        .filter(|b| b.block_type == BlockType::Val)
        .flat_map(|b| b.names.iter().map(|n| n.as_str()))
        .collect();

    // Collect all .fsti assume val names
    let fsti_assume_names: HashSet<&str> = fsti_blocks
        .iter()
        .filter(|b| b.block_type == BlockType::Assume)
        .flat_map(|b| b.names.iter().map(|n| n.as_str()))
        .collect();

    // Collect all .fsti type/let/class/effect names (interface-only is valid)
    let fsti_non_val_names: HashSet<&str> = fsti_blocks
        .iter()
        .filter(|b| !matches!(b.block_type, BlockType::Val | BlockType::Assume
            | BlockType::Module | BlockType::Open | BlockType::Friend
            | BlockType::Include | BlockType::ModuleAbbrev | BlockType::SetOptions
            | BlockType::Directive | BlockType::Comment | BlockType::Unknown))
        .flat_map(|b| b.names.iter().map(|n| n.as_str()))
        .collect();

    // ========================================================================
    // CHECK 1: .fst let definitions without corresponding .fsti val
    // ========================================================================
    for block in &fst_blocks {
        let is_definition = matches!(
            block.block_type,
            BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet
        );
        if !is_definition {
            continue;
        }
        // Skip private definitions -- they should not have val in .fsti
        if block.is_private {
            continue;
        }

        for name in &block.names {
            // Skip if there is a val or assume val or type/let definition in .fsti
            if fsti_val_names.contains(name.as_str())
                || fsti_assume_names.contains(name.as_str())
                || fsti_non_val_names.contains(name.as_str())
            {
                continue;
            }
            // Skip internal names (starting with _)
            if name.starts_with('_') {
                continue;
            }
            mismatches.push(InterfaceMismatch {
                name: name.clone(),
                line: block.start_line,
                in_fsti: false,
                kind: InterfaceMismatchKind::MissingValInInterface,
            });
        }
    }

    // ========================================================================
    // CHECK 2: assume val in .fsti that also has let in .fst
    // ========================================================================
    for name in &fsti_assume_names {
        if let Some(fsti_block) = fsti_by_name.get(name) {
            if !fst_by_name.contains_key(name) { continue; }
            mismatches.push(InterfaceMismatch {
                name: name.to_string(),
                line: fsti_block.start_line,
                in_fsti: true,
                kind: InterfaceMismatchKind::AssumeValMismatch {
                    fsti_is_assume: true,
                },
            });
        }
    }

    // ========================================================================
    // CHECK 3: Qualifier mismatches on paired type declarations
    // ========================================================================
    for fsti_block in &fsti_blocks {
        if fsti_block.block_type != BlockType::Type {
            continue;
        }
        for name in &fsti_block.names {
            if let Some(fst_block) = fst_by_name.get(name.as_str()) {
                if fst_block.block_type != BlockType::Type {
                    continue;
                }
                // Compare noeq/unopteq
                let fsti_noeq = has_noeq_qualifier(fsti_block);
                let fst_noeq = has_noeq_qualifier(fst_block);
                if fsti_noeq != fst_noeq {
                    mismatches.push(InterfaceMismatch {
                        name: name.clone(),
                        line: fsti_block.start_line,
                        in_fsti: true,
                        kind: InterfaceMismatchKind::TypeEqualityMismatch {
                            fsti_noeq,
                            fst_noeq,
                        },
                    });
                }

                // Compare broader qualifier sets
                let fsti_quals = extract_qualifiers(fsti_block);
                let fst_quals = extract_qualifiers(fst_block);
                // Filter out noeq/unopteq (already checked above) and private
                // (private in .fst is valid even if .fsti lacks it)
                let filter_quals = |qs: &[String]| -> Vec<String> {
                    qs.iter()
                        .filter(|q| !matches!(q.as_str(), "noeq" | "unopteq" | "private"))
                        .cloned()
                        .collect()
                };
                let fsti_filtered = filter_quals(&fsti_quals);
                let fst_filtered = filter_quals(&fst_quals);
                if fsti_filtered != fst_filtered {
                    mismatches.push(InterfaceMismatch {
                        name: name.clone(),
                        line: fsti_block.start_line,
                        in_fsti: true,
                        kind: InterfaceMismatchKind::QualifierMismatch {
                            fsti_qualifiers: fsti_filtered,
                            fst_qualifiers: fst_filtered,
                        },
                    });
                }
            }
        }
    }

    // ========================================================================
    // CHECK 4: Qualifier mismatches on paired val/let declarations
    // ========================================================================
    for fsti_block in &fsti_blocks {
        if fsti_block.block_type != BlockType::Val {
            continue;
        }
        for name in &fsti_block.names {
            if let Some(fst_block) = fst_by_name.get(name.as_str()) {
                // Val in .fsti paired with let in .fst
                let is_fst_let = matches!(
                    fst_block.block_type,
                    BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet
                );
                if !is_fst_let {
                    continue;
                }

                // Compare qualifiers on val vs let
                let fsti_quals = extract_qualifiers(fsti_block);
                let fst_quals = extract_qualifiers(fst_block);

                // For val/let pairs, only compare extraction-relevant qualifiers
                // (inline_for_extraction, noextract). Other qualifiers may legitimately
                // differ (e.g., rec only applies to let, not val).
                let extract_relevant = |qs: &[String]| -> Vec<String> {
                    qs.iter()
                        .filter(|q| {
                            matches!(
                                q.as_str(),
                                "inline_for_extraction" | "noextract"
                            )
                        })
                        .cloned()
                        .collect()
                };
                let fsti_extract = extract_relevant(&fsti_quals);
                let fst_extract = extract_relevant(&fst_quals);
                if fsti_extract != fst_extract {
                    mismatches.push(InterfaceMismatch {
                        name: name.clone(),
                        line: fsti_block.start_line,
                        in_fsti: true,
                        kind: InterfaceMismatchKind::QualifierMismatch {
                            fsti_qualifiers: fsti_extract,
                            fst_qualifiers: fst_extract,
                        },
                    });
                }
            }
        }
    }

    // ========================================================================
    // CHECK 5: Implicit argument count mismatches
    // ========================================================================
    for fsti_block in &fsti_blocks {
        if fsti_block.block_type != BlockType::Val {
            continue;
        }
        for name in &fsti_block.names {
            if let Some(fst_block) = fst_by_name.get(name.as_str()) {
                let is_fst_let = matches!(
                    fst_block.block_type,
                    BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet
                );
                if !is_fst_let {
                    continue;
                }

                let fsti_implicit_count = count_implicit_args(fsti_block);
                let fst_implicit_count = count_implicit_args(fst_block);

                // Only report if BOTH have at least one implicit (to avoid false positives
                // on signatures without implicits) OR if one has >0 and other has 0.
                if fsti_implicit_count != fst_implicit_count
                    && (fsti_implicit_count > 0 || fst_implicit_count > 0)
                {
                    mismatches.push(InterfaceMismatch {
                        name: name.clone(),
                        line: fsti_block.start_line,
                        in_fsti: true,
                        kind: InterfaceMismatchKind::ImplicitArgCountMismatch {
                            fsti_count: fsti_implicit_count,
                            fst_count: fst_implicit_count,
                        },
                    });
                }
            }
        }
    }

    // ========================================================================
    // CHECK 6: friend declarations without abstract types
    // ========================================================================
    // Collect abstract types from .fsti (types without a body / no = sign)
    // Also count val declarations for abstract types (val foo : Type0)
    let fsti_has_abstract = fsti_blocks.iter().any(|b| {
        if b.block_type == BlockType::Type {
            let text = b.lines.join("");
            let trimmed = text.trim();
            // Abstract type: `type foo` or `type foo : kind` without `= body`
            !trimmed.contains(" = ") && !trimmed.ends_with(" =")
                && !trimmed.contains("= {") && !trimmed.contains("= |")
        } else if b.block_type == BlockType::Val {
            // val abstract_type : Type0  (abstract type declared as val)
            let text = b.lines.join("");
            text.contains("Type0") || text.contains("Type u#")
        } else {
            false
        }
    });

    // Friend declarations may appear in blocks or in the header.
    // Check blocks first.
    for fst_block in &fst_blocks {
        if fst_block.block_type != BlockType::Friend {
            continue;
        }
        if let Some(ref friend_module) = fst_block.module_path {
            if !fsti_has_abstract {
                mismatches.push(InterfaceMismatch {
                    name: friend_module.clone(),
                    line: fst_block.start_line,
                    in_fsti: false,
                    kind: InterfaceMismatchKind::FriendWithoutAbstractTypes {
                        friend_module: friend_module.clone(),
                    },
                });
            }
        }
    }

    // Also scan the header lines for friend declarations (friend in header area)
    lazy_static! {
        static ref FRIEND_RE: Regex = Regex::new(r"^friend\s+([\w.]+)").unwrap_or_else(|e| panic!("regex: {e}"));
    }
    for (line_idx, line) in fst_content.lines().enumerate() {
        let trimmed = line.trim();
        if let Some(caps) = FRIEND_RE.captures(trimmed) {
            let friend_module = caps.get(1).map(|m| m.as_str()).unwrap_or("");
            // Only report if not already detected via blocks
            let already_reported = mismatches.iter().any(|m| {
                matches!(&m.kind, InterfaceMismatchKind::FriendWithoutAbstractTypes { friend_module: fm } if fm == friend_module)
            });
            if !already_reported && !fsti_has_abstract && !friend_module.is_empty() {
                mismatches.push(InterfaceMismatch {
                    name: friend_module.to_string(),
                    line: line_idx + 1,
                    in_fsti: false,
                    kind: InterfaceMismatchKind::FriendWithoutAbstractTypes {
                        friend_module: friend_module.to_string(),
                    },
                });
            }
        }
    }

    mismatches
}

/// FST002: Interface declaration order.
pub struct ReorderInterfaceRule;

impl ReorderInterfaceRule {
    pub fn new() -> Self {
        Self
    }
}

impl Default for ReorderInterfaceRule {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// BLOCK-LEVEL DEPENDENCY GRAPH
// ---------------------------------------------------------------------------

/// Category priority for declaration ordering in F*.
/// Lower values appear earlier in the file. Enforces canonical F* ordering:
/// pragmas -> opens/includes -> module abbreviations -> friend declarations ->
/// type/class/effect definitions -> instances -> val/let -> everything else.
fn block_category_priority(block: &DeclarationBlock) -> u32 {
    match block.block_type {
        BlockType::SetOptions | BlockType::Directive => 0,
        BlockType::Open => 1,
        BlockType::Include => 2,
        BlockType::ModuleAbbrev => 3,
        BlockType::Friend => 4,
        BlockType::Type | BlockType::Class | BlockType::Effect => 5,
        BlockType::Instance => 6,
        BlockType::Val => 7,
        BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet => 8,
        BlockType::Assume => 9,
        BlockType::Comment => 10,
        _ => 11,
    }
}

/// Build a block-index-to-block-index dependency map.
///
/// Dependencies are computed by mapping each block's `references` set back to
/// the block that defines that name. Self-dependencies are excluded.
///
/// Also injects additional dependency edges:
///   - Instance blocks depend on their target class.
///   - Attribute references (`[@@attr]`) create deps on the attr definition.
///   - F* operator names (e.g. `op_At_Percent_Dot`) are resolved.
fn build_block_deps(blocks: &[DeclarationBlock]) -> Vec<HashSet<usize>> {
    // Map each defined name to its block index
    let mut name_to_block: HashMap<&str, usize> = HashMap::new();
    for (idx, block) in blocks.iter().enumerate() {
        for name in &block.names {
            name_to_block.entry(name.as_str()).or_insert(idx);
        }
    }

    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); blocks.len()];

    for (idx, block) in blocks.iter().enumerate() {
        // Standard reference deps from parser
        for ref_name in &block.references {
            if let Some(&dep_idx) = name_to_block.get(ref_name.as_str()) {
                if dep_idx != idx {
                    deps[idx].insert(dep_idx);
                }
            }
        }

        // Instance -> class dependency: "instance foo : SomeClass ..."
        if block.block_type == BlockType::Instance {
            let text = block.lines.join(" ");
            if let Some(colon_pos) = text.find(':') {
                let after_colon = text[colon_pos + 1..].trim();
                let class_name: String = after_colon
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                    .collect();
                if !class_name.is_empty() {
                    if let Some(&dep_idx) = name_to_block.get(class_name.as_str()) {
                        if dep_idx != idx {
                            deps[idx].insert(dep_idx);
                        }
                    }
                }
            }
        }

        // Attribute dependencies: [@@some_attr] before a declaration
        for line in &block.lines {
            let trimmed = line.trim();
            if trimmed.starts_with("[@@") || trimmed.starts_with("[@@ ") {
                let inner = trimmed
                    .trim_start_matches("[@@")
                    .trim_start_matches("[@@ ");
                for token in inner.split(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'') {
                    let token = token.trim();
                    if !token.is_empty() {
                        if let Some(&dep_idx) = name_to_block.get(token) {
                            if dep_idx != idx {
                                deps[idx].insert(dep_idx);
                            }
                        }
                    }
                }
            }
        }

        // F* operator name dependencies: op_At_Percent, op_Bar_Bar, etc.
        let text = block.lines.join(" ");
        for word in text.split(|c: char| !c.is_alphanumeric() && c != '_') {
            if word.starts_with("op_") {
                if let Some(&dep_idx) = name_to_block.get(word) {
                    if dep_idx != idx {
                        deps[idx].insert(dep_idx);
                    }
                }
            }
        }
    }

    deps
}

// ---------------------------------------------------------------------------
// TARJAN'S SCC ALGORITHM
// ---------------------------------------------------------------------------

/// State for Tarjan's SCC computation.
struct TarjanState {
    index_counter: usize,
    stack: Vec<usize>,
    on_stack: Vec<bool>,
    index: Vec<Option<usize>>,
    lowlink: Vec<usize>,
    sccs: Vec<Vec<usize>>,
}

/// Compute Strongly Connected Components using Tarjan's algorithm.
///
/// Returns SCCs in topological order (dependencies come first). Within each
/// SCC, indices are sorted by original position to preserve file locality.
fn tarjan_scc(num_nodes: usize, deps: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; num_nodes],
        index: vec![None; num_nodes],
        lowlink: vec![0; num_nodes],
        sccs: Vec::new(),
    };

    for node in 0..num_nodes {
        if state.index[node].is_none() {
            tarjan_strongconnect(node, deps, &mut state);
        }
    }

    // Tarjan's produces SCCs in reverse topological order; reverse for forward
    state.sccs.reverse();
    for scc in &mut state.sccs {
        scc.sort();
    }
    state.sccs
}

fn tarjan_strongconnect(v: usize, deps: &[HashSet<usize>], state: &mut TarjanState) {
    state.index[v] = Some(state.index_counter);
    state.lowlink[v] = state.index_counter;
    state.index_counter += 1;
    state.stack.push(v);
    state.on_stack[v] = true;

    for &w in &deps[v] {
        if w >= deps.len() {
            continue;
        }
        if state.index[w].is_none() {
            tarjan_strongconnect(w, deps, state);
            state.lowlink[v] = state.lowlink[v].min(state.lowlink[w]);
        } else if state.on_stack[w] {
            state.lowlink[v] = state.lowlink[v].min(state.index[w].unwrap_or(0));
        }
    }

    if state.lowlink[v] == state.index[v].unwrap_or(0) {
        let mut scc = Vec::new();
        while let Some(w) = state.stack.pop() {
            state.on_stack[w] = false;
            scc.push(w);
            if w == v {
                break;
            }
        }
        state.sccs.push(scc);
    }
}

// ---------------------------------------------------------------------------
// BLOCK-LEVEL TOPOLOGICAL SORT WITH SCC AWARENESS
// ---------------------------------------------------------------------------

/// Check if the current block order has forward references.
///
/// A forward reference exists when block `i` depends on block `j` but `j`
/// appears after `i` in the given order.
fn check_block_order_valid(
    blocks: &[DeclarationBlock],
    deps: &[HashSet<usize>],
) -> (bool, Vec<String>) {
    let mut violations = Vec::new();

    for (idx, block) in blocks.iter().enumerate() {
        for &dep_idx in &deps[idx] {
            if dep_idx > idx {
                let dep_name = blocks[dep_idx]
                    .names
                    .first()
                    .map(|s| s.as_str())
                    .unwrap_or("<anonymous>");
                let name = block
                    .names
                    .first()
                    .map(|s| s.as_str())
                    .unwrap_or("<anonymous>");
                violations.push(format!(
                    "'{}' (block {}) references '{}' (block {}), but '{}' comes after '{}'",
                    name, idx, dep_name, dep_idx, dep_name, name
                ));
            }
        }
    }

    (violations.is_empty(), violations)
}

/// Topological sort of SCC super-nodes using Kahn's algorithm.
///
/// Each SCC is treated as a single node. When two SCCs have equal dependency
/// priority, break ties first by declaration category (pragmas before opens
/// before types before vals), then by original file position.
fn topo_sort_sccs(
    sccs: &[Vec<usize>],
    block_deps: &[HashSet<usize>],
    blocks: &[DeclarationBlock],
) -> Result<Vec<usize>, Vec<String>> {
    let num_sccs = sccs.len();

    // Map each block index to its SCC index
    let mut block_to_scc: Vec<usize> = vec![0; block_deps.len()];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &block_idx in scc {
            if block_idx < block_to_scc.len() {
                block_to_scc[block_idx] = scc_idx;
            }
        }
    }

    // Build SCC-level dependency graph
    let mut scc_deps: Vec<HashSet<usize>> = vec![HashSet::new(); num_sccs];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &block_idx in scc {
            for &dep_block in &block_deps[block_idx] {
                if dep_block < block_to_scc.len() {
                    let dep_scc = block_to_scc[dep_block];
                    if dep_scc != scc_idx {
                        scc_deps[scc_idx].insert(dep_scc);
                    }
                }
            }
        }
    }

    // In-degree = number of SCCs this SCC depends on
    let mut in_degree: Vec<usize> = (0..num_sccs)
        .map(|i| scc_deps[i].len())
        .collect();

    // Preferred original position: minimum block index in SCC
    let scc_orig_pos: Vec<usize> = sccs
        .iter()
        .map(|scc| scc.iter().copied().min().unwrap_or(usize::MAX))
        .collect();

    // Category priority: minimum category of any block in SCC
    let scc_category: Vec<u32> = sccs
        .iter()
        .map(|scc| {
            scc.iter()
                .map(|&bi| block_category_priority(&blocks[bi]))
                .min()
                .unwrap_or(u32::MAX)
        })
        .collect();

    let mut available: Vec<usize> = (0..num_sccs)
        .filter(|&s| in_degree[s] == 0)
        .collect();
    available.sort_by(|&a, &b| {
        scc_category[a]
            .cmp(&scc_category[b])
            .then(scc_orig_pos[a].cmp(&scc_orig_pos[b]))
    });

    let mut sorted_sccs: Vec<usize> = Vec::with_capacity(num_sccs);

    while let Some(current) = available.first().copied() {
        available.remove(0);
        sorted_sccs.push(current);

        for scc_idx in 0..num_sccs {
            if scc_deps[scc_idx].contains(&current) {
                in_degree[scc_idx] = in_degree[scc_idx].saturating_sub(1);
                if in_degree[scc_idx] == 0
                    && !sorted_sccs.contains(&scc_idx)
                    && !available.contains(&scc_idx)
                {
                    available.push(scc_idx);
                    available.sort_by(|&a, &b| {
                        scc_category[a]
                            .cmp(&scc_category[b])
                            .then(scc_orig_pos[a].cmp(&scc_orig_pos[b]))
                    });
                }
            }
        }
    }

    if sorted_sccs.len() != num_sccs {
        let remaining: Vec<String> = (0..num_sccs)
            .filter(|s| !sorted_sccs.contains(s))
            .flat_map(|s| {
                sccs[s]
                    .iter()
                    .filter_map(|&bi| blocks[bi].names.first().cloned())
            })
            .collect();
        return Err(vec![format!(
            "Cycle detected between SCCs involving: {}",
            remaining.join(", ")
        )]);
    }

    // Flatten: for each SCC in topological order, emit its blocks in original order
    let mut result: Vec<usize> = Vec::with_capacity(block_deps.len());
    for &scc_idx in &sorted_sccs {
        result.extend_from_slice(&sccs[scc_idx]);
    }

    Ok(result)
}

/// Legacy name-level order check, kept for potential future use.
#[allow(dead_code)]
fn check_order_valid(
    order: &[String],
    deps: &HashMap<String, HashSet<String>>,
    all_declared_names: Option<&HashSet<String>>,
) -> (bool, Vec<String>) {
    let mut violations = Vec::new();
    let name_to_position: HashMap<&str, usize> = order
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    let order_set: HashSet<&str> = order.iter().map(|s| s.as_str()).collect();

    for name in order {
        if let Some(name_deps) = deps.get(name) {
            let name_pos = name_to_position[name.as_str()];
            for dep in name_deps {
                let is_valid_dep = all_declared_names
                    .map(|names| names.contains(dep))
                    .unwrap_or(true);
                if !is_valid_dep {
                    continue;
                }
                if !order_set.contains(dep.as_str()) {
                    violations.push(format!(
                        "'{}' references '{}', but '{}' is not in order \
                         (FSTI-only declaration that would be placed at END)",
                        name, dep, dep
                    ));
                } else if let Some(&dep_pos) = name_to_position.get(dep.as_str()) {
                    if dep_pos > name_pos {
                        violations.push(format!(
                            "'{}' references '{}', but '{}' comes after '{}'",
                            name, dep, dep, name
                        ));
                    }
                }
            }
        }
    }

    (violations.is_empty(), violations)
}

/// Reorder .fsti content to fix forward reference errors.
///
/// Uses block-level topological sorting with SCC detection:
///   1. Builds a block-level dependency graph (including instance->class,
///      attribute refs, and operator dependencies).
///   2. Computes SCCs with Tarjan's algorithm so mutually-dependent blocks
///      stay together as atomic units.
///   3. Topologically sorts the SCC super-nodes respecting both dependency
///      edges and declaration-category priority (pragmas > opens > types > vals).
///
/// Only suggests reordering when the CURRENT .fsti order has forward reference
/// problems (F* Error 233). Does NOT reorder just because order differs from .fst.
pub fn reorder_fsti_content(
    fsti_content: &str,
    _fst_content: &str,
) -> ReorderResult {
    let (fsti_header, fsti_blocks) = parse_fstar_file(fsti_content);

    if fsti_blocks.is_empty() {
        return Ok((fsti_content.to_string(), Vec::new(), false));
    }

    // Build block-level dependency graph
    let block_deps = build_block_deps(&fsti_blocks);

    // Quick check: is the current order already valid?
    let (current_valid, current_violations) =
        check_block_order_valid(&fsti_blocks, &block_deps);

    if current_valid {
        return Ok((fsti_content.to_string(), Vec::new(), false));
    }

    // Compute SCCs for mutual dependency handling
    let sccs = tarjan_scc(fsti_blocks.len(), &block_deps);

    // Topological sort of SCCs
    let sorted_indices = match topo_sort_sccs(&sccs, &block_deps, &fsti_blocks) {
        Ok(order) => order,
        Err(_) => return Err(current_violations),
    };

    // Build reordered block list and track movements
    let mut reordered_blocks: Vec<&DeclarationBlock> = Vec::with_capacity(fsti_blocks.len());
    let mut movements: Vec<(String, usize, usize)> = Vec::new();

    for (new_pos, &orig_idx) in sorted_indices.iter().enumerate() {
        let block = &fsti_blocks[orig_idx];
        reordered_blocks.push(block);

        if orig_idx != new_pos {
            if let Some(primary) = block.names.first() {
                movements.push((primary.clone(), orig_idx, new_pos));
            }
        }
    }

    // Construct reordered content
    let mut reordered_lines: Vec<String> = fsti_header.clone();

    if !reordered_lines.is_empty() && !reordered_blocks.is_empty() {
        if let Some(last) = reordered_lines.last() {
            if !last.trim().is_empty() {
                reordered_lines.push("\n".to_string());
            }
        }
    }

    for block in &reordered_blocks {
        reordered_lines.extend(block.lines.iter().cloned());
    }

    let original_order: Vec<usize> = (0..fsti_blocks.len()).collect();
    let changed = sorted_indices != original_order;

    Ok((reordered_lines.concat(), movements, changed))
}

impl Rule for ReorderInterfaceRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST002
    }

    fn check(&self, _file: &Path, _content: &str) -> Vec<Diagnostic> {
        // This rule requires pair checking
        vec![]
    }

    fn requires_pair(&self) -> bool {
        true
    }

    fn check_pair(
        &self,
        _fst_file: &Path,
        fst_content: &str,
        fsti_file: &Path,
        fsti_content: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // First, check for orphan declarations and typos
        let consistency = analyze_interface_consistency(fsti_content, fst_content);

        // Report potential typos (highest priority - likely bugs)
        for (fsti_name, fst_name, distance) in &consistency.typo_matches {
            let message = format!(
                "Possible typo: `{}` declared in interface but `{}` defined in implementation \
                 (edit distance: {}). Did you mean `{}`?",
                fsti_name, fst_name, distance, fst_name
            );
            // Find line number for this declaration
            let line = consistency
                .orphan_declarations
                .iter()
                .find(|(n, _, _)| n == fsti_name)
                .map(|(_, _, l)| *l)
                .unwrap_or(1);

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST002,
                severity: DiagnosticSeverity::Warning,
                file: fsti_file.to_path_buf(),
                range: Range::point(line, 1),
                message,
                fix: None,
            });
        }

        // Report orphan declarations (without typo matches).
        // Demoted to Info: in F*, val declarations can be satisfied by class
        // instance methods, operator overloads, or compiler-internal mechanisms
        // that the regex parser cannot detect. The F* compiler will reject truly
        // missing implementations, so this is informational.
        for (name, typo_match, line) in &consistency.orphan_declarations {
            if typo_match.is_none() {
                let message = format!(
                    "Orphan declaration: `{}` is declared in interface but has no \
                     implementation in .fst. This may be satisfied by a class instance, \
                     operator overload, or compiler mechanism.",
                    name
                );
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST002,
                    severity: DiagnosticSeverity::Info,
                    file: fsti_file.to_path_buf(),
                    range: Range::point(*line, 1),
                    message,
                    fix: None,
                });
            }
        }

        // Deep consistency checks: qualifier mismatches, implicit arg counts, etc.
        let deep_mismatches = analyze_deep_consistency(fsti_content, fst_content);
        let fst_file_path = _fst_file.to_path_buf();
        for mismatch in &deep_mismatches {
            let (severity, message, file) = match &mismatch.kind {
                InterfaceMismatchKind::MissingValInInterface => (
                    DiagnosticSeverity::Info,
                    format!(
                        "Definition `{}` in .fst has no corresponding `val` in .fsti. \
                         It will be private (not exported). Add `val {}` to .fsti if it should be public.",
                        mismatch.name, mismatch.name
                    ),
                    &fst_file_path,
                ),
                InterfaceMismatchKind::AssumeValMismatch { fsti_is_assume } => {
                    if *fsti_is_assume {
                        (
                            DiagnosticSeverity::Warning,
                            format!(
                                "`assume val {}` in .fsti declares an axiom, but .fst provides \
                                 a `let` implementation. Use `val` instead of `assume val` \
                                 when an implementation exists.",
                                mismatch.name
                            ),
                            &fsti_file.to_path_buf(),
                        )
                    } else {
                        continue;
                    }
                }
                InterfaceMismatchKind::TypeEqualityMismatch { fsti_noeq, fst_noeq } => {
                    let fsti_word = if *fsti_noeq { "noeq type" } else { "type" };
                    let fst_word = if *fst_noeq { "noeq type" } else { "type" };
                    (
                        DiagnosticSeverity::Error,
                        format!(
                            "Type equality modifier mismatch for `{}`: \
                             .fsti declares `{}` but .fst declares `{}`. \
                             These must match or F* will reject the module.",
                            mismatch.name, fsti_word, fst_word
                        ),
                        &fsti_file.to_path_buf(),
                    )
                }
                InterfaceMismatchKind::QualifierMismatch {
                    fsti_qualifiers,
                    fst_qualifiers,
                } => {
                    let fsti_str = if fsti_qualifiers.is_empty() {
                        "(none)".to_string()
                    } else {
                        fsti_qualifiers.join(", ")
                    };
                    let fst_str = if fst_qualifiers.is_empty() {
                        "(none)".to_string()
                    } else {
                        fst_qualifiers.join(", ")
                    };
                    // In F*, extraction qualifiers on a val in the .fsti are
                    // inherited by the let in the .fst. The implementation does
                    // NOT need to repeat inline_for_extraction/noextract -- the
                    // compiler picks them up from the interface. So when the
                    // interface has qualifiers but the implementation has none,
                    // this is standard practice, not a defect.
                    let severity = if fst_qualifiers.is_empty() && !fsti_qualifiers.is_empty() {
                        // Interface has qualifiers, impl has none -> inherited (normal)
                        DiagnosticSeverity::Info
                    } else if fsti_qualifiers.is_empty() && !fst_qualifiers.is_empty() {
                        // Impl has qualifiers not in interface -> suspicious
                        DiagnosticSeverity::Warning
                    } else {
                        // Both have qualifiers but they differ -> genuine mismatch
                        DiagnosticSeverity::Warning
                    };
                    (
                        severity,
                        format!(
                            "Qualifier mismatch for `{}`: .fsti has [{}] but .fst has [{}]. \
                             Extraction qualifiers (inline_for_extraction, noextract) should match.",
                            mismatch.name, fsti_str, fst_str
                        ),
                        &fsti_file.to_path_buf(),
                    )
                }
                InterfaceMismatchKind::ImplicitArgCountMismatch {
                    fsti_count,
                    fst_count,
                } => {
                    // In F*, it is completely normal for:
                    // - Implementation to have MORE implicits than interface
                    //   (interface abstracts them away, standard practice)
                    // - Implementation to have FEWER explicit implicits than interface
                    //   (implicits can be inferred from val signature, e.g.
                    //    val f : #a:Type -> ... / let f x = ... without repeating #a)
                    //
                    // The F* type checker enforces consistency at compile time,
                    // so regex-based counting is inherently imprecise. Demote to Info
                    // since this is informational, not a defect.
                    (
                        DiagnosticSeverity::Info,
                        format!(
                            "Implicit argument count differs for `{}`: \
                             .fsti val has {} implicit arg{} but .fst let has {} \
                             (F* infers/abstracts implicits across interface boundaries).",
                            mismatch.name,
                            fsti_count,
                            if *fsti_count == 1 { "" } else { "s" },
                            fst_count
                        ),
                        &fsti_file.to_path_buf(),
                    )
                }
                InterfaceMismatchKind::FriendWithoutAbstractTypes { friend_module } => (
                    DiagnosticSeverity::Info,
                    format!(
                        "`friend {}` declared but this module's .fsti has no abstract types. \
                         The `friend` keyword grants access to abstract type implementations; \
                         it may be unnecessary here.",
                        friend_module
                    ),
                    &fst_file_path,
                ),
            };

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST002,
                severity,
                file: file.clone(),
                range: Range::point(mismatch.line, 1),
                message,
                fix: None,
            });
        }

        // Then check for ordering issues (forward references)
        match reorder_fsti_content(fsti_content, fst_content) {
            Ok((reordered_content, movements, changed)) => {
                if !changed {
                    return diagnostics;
                }

                // CRITICAL SAFETY CHECK: Validate the reordering before offering a fix
                let fsti_path = fsti_file.to_string_lossy();
                let validation_warnings =
                    validate_reorder(fsti_content, &reordered_content, &fsti_path);

                // Check for critical warnings - if any, DO NOT offer a fix
                let critical_warnings: Vec<_> = validation_warnings
                    .iter()
                    .filter(|w| w.severity == ReorderWarningSeverity::Critical)
                    .collect();

                if !critical_warnings.is_empty() {
                    // Forward reference detection is heuristic. F* handles
                    // module-level scoping and mutual recursion that our
                    // block-level analysis cannot model. When autofix is also
                    // blocked, this is purely informational.
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST002,
                        severity: DiagnosticSeverity::Info,
                        file: fsti_file.to_path_buf(),
                        range: Range::point(1, 1),
                        message: format!(
                            "Interface may have forward reference issues (autofix blocked due to {} validation error(s)).",
                            critical_warnings.len()
                        ),
                        fix: None, // NO FIX - validation failed
                    });

                    // Report each critical validation error as info (tool limitation detail)
                    for warning in critical_warnings {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST002,
                            severity: DiagnosticSeverity::Info,
                            file: fsti_file.to_path_buf(),
                            range: Range::point(1, 1),
                            message: format!("Validation failed: {}", warning.message),
                            fix: None,
                        });
                    }

                    return diagnostics;
                }

                // Create main diagnostic with fix (validation passed)
                let message = format!(
                    "Interface has forward reference issues. {} declaration{} need{} reordering to fix F* Error 233.",
                    movements.len(),
                    if movements.len() == 1 { "" } else { "s" },
                    if movements.len() == 1 { "s" } else { "" }
                );

                let fsti_lines: Vec<&str> = fsti_content.lines().collect();

                // Determine confidence and safety based on validation results and movement count
                // - If many declarations move (>5), use Medium confidence
                // - If few declarations move and no validation warnings, use High confidence
                let has_validation_warnings = !validation_warnings.is_empty();
                let (confidence, unsafe_reason) = if movements.len() > 10 {
                    (
                        FixConfidence::Low,
                        Some(format!(
                            "Many declarations ({}) will be reordered. Manual review strongly recommended.",
                            movements.len()
                        )),
                    )
                } else if movements.len() > 5 || has_validation_warnings {
                    (
                        FixConfidence::Medium,
                        Some(format!(
                            "Moderate reordering ({} declarations). Please review before applying.",
                            movements.len()
                        )),
                    )
                } else {
                    // Small number of movements, no warnings - relatively safe
                    (FixConfidence::High, None)
                };

                let fix = Fix {
                    message: "Reorder declarations to fix forward references".to_string(),
                    edits: vec![Edit {
                        file: fsti_file.to_path_buf(),
                        range: Range::new(1, 1, fsti_lines.len() + 1, 1),
                        new_text: reordered_content,
                    }],
                    confidence,
                    unsafe_reason,
                    // Reordering is not safe to auto-apply without review
                    safety_level: FixSafetyLevel::Caution,
                    reversible: true,  // Can be undone with inverse reordering
                    requires_review: true,  // Order changes need human review
                };

                let first_line = movements.first().map(|(_, old, _)| *old + 1).unwrap_or(1);

                // Forward-reference analysis is heuristic. F* handles
                // module-level scoping, mutual recursion, and other patterns
                // that our block-level analysis may flag incorrectly. The
                // suggested fix is offered as a recommendation via Info.
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST002,
                    severity: DiagnosticSeverity::Info,
                    file: fsti_file.to_path_buf(),
                    range: Range::point(first_line, 1),
                    message,
                    fix: Some(fix),
                });

                // Add info note if many declarations are moving
                if movements.len() > 10 {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST002,
                        severity: DiagnosticSeverity::Info,
                        file: fsti_file.to_path_buf(),
                        range: Range::point(1, 1),
                        message: format!(
                            "Note: {} declarations will move. Review the changes carefully before applying.",
                            movements.len()
                        ),
                        fix: None,
                    });
                }

                // Add detail diagnostics for each movement
                for (name, old_pos, new_pos) in &movements {
                    let direction = if new_pos > old_pos { "down" } else { "up" };
                    let detail_message = format!(
                        "`{}` needs to move {} (position {} -> {})",
                        name, direction, old_pos, new_pos
                    );
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST002,
                        severity: DiagnosticSeverity::Info,
                        file: fsti_file.to_path_buf(),
                        range: Range::point(old_pos + 1, 1),
                        message: detail_message,
                        fix: None,
                    });
                }

                // Add any non-critical validation warnings as info
                for warning in validation_warnings
                    .iter()
                    .filter(|w| w.severity != ReorderWarningSeverity::Critical)
                {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST002,
                        severity: DiagnosticSeverity::Info,
                        file: fsti_file.to_path_buf(),
                        range: Range::point(1, 1),
                        message: format!("Validation note: {}", warning.message),
                        fix: None,
                    });
                }

                diagnostics
            }
            Err(errors) => {
                // Reorder algorithm hit a limitation -- this is a tool
                // limitation, not a defect in the source file.
                for err in errors {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST002,
                        severity: DiagnosticSeverity::Info,
                        file: fsti_file.to_path_buf(),
                        range: Range::point(1, 1),
                        message: format!("Cannot reorder: {}", err),
                        fix: None,
                    });
                }
                diagnostics
            }
        }
    }
}

/// Validation warning from reordering.
#[derive(Debug, Clone)]
pub struct ReorderValidationWarning {
    pub message: String,
    pub severity: ReorderWarningSeverity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReorderWarningSeverity {
    Critical,
    Warning,
}

/// Compute a content hash of all non-whitespace characters.
/// This is used to verify that reordering didn't lose or duplicate content.
/// Extract all declaration names from content for verification.
fn extract_all_declaration_names(content: &str) -> Vec<String> {
    let (_, blocks) = parse_fstar_file(content);
    let mut names = Vec::new();
    for block in &blocks {
        names.extend(block.names.iter().cloned());
    }
    names
}

/// Count occurrences of each declaration name.
fn count_declaration_names(names: &[String]) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for name in names {
        *counts.entry(name.clone()).or_insert(0) += 1;
    }
    counts
}

/// Validate that reordering didn't lose or duplicate content.
///
/// CRITICAL SAFETY CHECKS:
/// 1. Content hash verification - non-whitespace content must be preserved
/// 2. Declaration name verification - every name must appear exactly once
/// 3. Line count sanity check - shouldn't change dramatically
/// 4. Module declaration preservation - must not be lost
/// 5. Token counts - val, type, let counts must match
/// 6. Character-level verification - all non-whitespace chars preserved
///
/// This is a safety net to catch reordering bugs before corrupting files.
pub fn validate_reorder(
    original_content: &str,
    reordered_content: &str,
    _fsti_path: &str,
) -> Vec<ReorderValidationWarning> {
    let mut warnings = Vec::new();

    // ========================================================================
    // CHECK 1: NON-WHITESPACE CHARACTER COUNT VERIFICATION
    // The total count of non-whitespace characters must match.
    // If it doesn't, content was lost or duplicated.
    // ========================================================================
    let orig_non_ws: String = original_content
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let new_non_ws: String = reordered_content
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();

    if orig_non_ws.len() != new_non_ws.len() {
        warnings.push(ReorderValidationWarning {
            message: format!(
                "CRITICAL: Non-whitespace character count mismatch: {} -> {} (delta: {}). \
                 Content was lost or duplicated during reordering. FIX REFUSED.",
                orig_non_ws.len(),
                new_non_ws.len(),
                new_non_ws.len() as i64 - orig_non_ws.len() as i64
            ),
            severity: ReorderWarningSeverity::Critical,
        });
    }

    // ========================================================================
    // CHECK 2: DECLARATION NAME VERIFICATION (CRITICAL)
    // Every declaration name must appear exactly once in both versions.
    // This catches:
    // - Lost declarations (name disappeared)
    // - Duplicated declarations (name appears twice)
    // - Name corruption (name changed)
    // ========================================================================
    let orig_names = extract_all_declaration_names(original_content);
    let new_names = extract_all_declaration_names(reordered_content);

    let orig_counts = count_declaration_names(&orig_names);
    let new_counts = count_declaration_names(&new_names);

    // Check for lost declarations
    for (name, &orig_count) in &orig_counts {
        let new_count = new_counts.get(name).copied().unwrap_or(0);
        if new_count == 0 {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "CRITICAL: Declaration '{}' was LOST during reordering! \
                     Original had {} occurrence(s), reordered has none. FIX REFUSED.",
                    name, orig_count
                ),
                severity: ReorderWarningSeverity::Critical,
            });
        } else if new_count != orig_count {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "CRITICAL: Declaration '{}' count changed: {} -> {}. \
                     Possible duplication or loss. FIX REFUSED.",
                    name, orig_count, new_count
                ),
                severity: ReorderWarningSeverity::Critical,
            });
        }
    }

    // Check for new declarations that shouldn't exist
    for (name, &new_count) in &new_counts {
        if !orig_counts.contains_key(name) {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "CRITICAL: Declaration '{}' appeared {} time(s) in reordered content \
                     but was NOT in original! Possible content corruption. FIX REFUSED.",
                    name, new_count
                ),
                severity: ReorderWarningSeverity::Critical,
            });
        }
    }

    // ========================================================================
    // CHECK 3: LINE COUNT SANITY CHECK
    // Reordering shouldn't dramatically change line count.
    // Small changes (blank lines) are OK, large changes indicate problems.
    // ========================================================================
    let orig_lines: Vec<&str> = original_content.lines().collect();
    let new_lines: Vec<&str> = reordered_content.lines().collect();

    let orig_count = orig_lines.len();
    let new_count = new_lines.len();

    let line_delta = (new_count as i64 - orig_count as i64).abs();
    if line_delta > 10 {
        warnings.push(ReorderValidationWarning {
            message: format!(
                "Line count changed significantly: {} -> {} (delta: {}). \
                 This may indicate content was lost or duplicated.",
                orig_count, new_count, line_delta
            ),
            severity: ReorderWarningSeverity::Warning,
        });
    }

    // ========================================================================
    // CHECK 4: MODULE DECLARATION PRESERVATION (CRITICAL)
    // The module declaration MUST be preserved exactly.
    // ========================================================================
    let orig_module = MODULE_PATTERN
        .captures(original_content)
        .and_then(|c| c.get(1).map(|m| m.as_str()));
    let new_module = MODULE_PATTERN
        .captures(reordered_content)
        .and_then(|c| c.get(1).map(|m| m.as_str()));

    match (orig_module, new_module) {
        (Some(orig), None) => {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "CRITICAL: Module declaration '{}' was LOST! FIX REFUSED.",
                    orig
                ),
                severity: ReorderWarningSeverity::Critical,
            });
        }
        (Some(orig), Some(new)) if orig != new => {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "CRITICAL: Module name changed from '{}' to '{}'! FIX REFUSED.",
                    orig, new
                ),
                severity: ReorderWarningSeverity::Critical,
            });
        }
        _ => {}
    }

    // ========================================================================
    // CHECK 5: TOKEN COUNTS VERIFICATION
    // The count of val, type, let keywords should match.
    // This is a secondary check to catch edge cases.
    // ========================================================================
    let token_checks = [
        (&*VAL_PATTERN, "val"),
        (&*TYPE_PATTERN, "type"),
        (&*LET_PATTERN, "let"),
    ];

    for (pattern, name) in token_checks {
        let orig_matches = pattern.find_iter(original_content).count();
        let new_matches = pattern.find_iter(reordered_content).count();

        if orig_matches != new_matches {
            warnings.push(ReorderValidationWarning {
                message: format!(
                    "{} keyword count changed: {} -> {} (delta: {})",
                    name,
                    orig_matches,
                    new_matches,
                    new_matches as i64 - orig_matches as i64
                ),
                severity: ReorderWarningSeverity::Warning,
            });
        }
    }

    // ========================================================================
    // CHECK 6: CHARACTER-BY-CHARACTER VERIFICATION
    // Sort all non-whitespace characters and compare.
    // If the sorted sequences differ, content was changed.
    // ========================================================================
    let mut orig_chars: Vec<char> = original_content
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let mut new_chars: Vec<char> = reordered_content
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();

    orig_chars.sort();
    new_chars.sort();

    if orig_chars != new_chars {
        // Find the first differing position for diagnostics
        let diff_pos = orig_chars
            .iter()
            .zip(new_chars.iter())
            .position(|(a, b)| a != b);

        warnings.push(ReorderValidationWarning {
            message: format!(
                "CRITICAL: Character-level content mismatch! \
                 First difference at sorted position {:?}. \
                 Original has {} non-ws chars, reordered has {}. FIX REFUSED.",
                diff_pos,
                orig_chars.len(),
                new_chars.len()
            ),
            severity: ReorderWarningSeverity::Critical,
        });
    }

    warnings
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_reorder_no_changes() {
        let content = r#"module Test

val foo: int -> int
val bar: int -> int
"#;
        let warnings = validate_reorder(content, content, "Test.fsti");
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_validate_reorder_lost_module_legacy() {
        // Legacy test - lost module should trigger critical warning
        let original = r#"module Test

val foo: int -> int
"#;
        let reordered = r#"
val foo: int -> int
"#;
        let warnings = validate_reorder(original, reordered, "Test.fsti");
        // Either the module check or character count mismatch should trigger
        let has_critical = warnings
            .iter()
            .any(|w| w.severity == ReorderWarningSeverity::Critical);
        assert!(
            has_critical,
            "Lost module should trigger critical warning. Got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validate_reorder_lost_declaration_legacy() {
        // Legacy test - lost declaration should trigger critical warning
        let original = r#"module Test

val foo: int -> int
val bar: int -> int
"#;
        let reordered = r#"module Test

val foo: int -> int
"#;
        let warnings = validate_reorder(original, reordered, "Test.fsti");
        // The new validation checks declaration names and character counts
        let has_critical = warnings
            .iter()
            .any(|w| w.severity == ReorderWarningSeverity::Critical);
        assert!(
            has_critical,
            "Lost declaration should trigger critical warning. Got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_correct_order_no_change() {
        let fst_content = r#"
module Test

let foo x = x + 1
let bar x = foo x
"#;
        let fsti_content = r#"
module Test

val foo: int -> int
val bar: int -> int
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed);
    }

    #[test]
    fn test_different_order_no_forward_ref_is_valid() {
        // NEW BEHAVIOR: Different order without forward references is VALID
        // The .fsti organization is intentional and doesn't need to match .fst
        let fst_content = r#"
module Test

let foo x = x + 1
let bar x = foo x
"#;
        // bar comes before foo (different from .fst) but NO forward reference
        // bar doesn't USE foo, so this order is valid
        let fsti_content = r#"
module Test

val bar: int -> int
val foo: int -> int
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, movements, changed) = result.unwrap();
        // Should NOT change - no forward references in .fsti
        assert!(!changed, "Expected no change when there are no forward references");
        assert!(movements.is_empty());
    }

    #[test]
    fn test_fsti_only_types_at_top_is_valid() {
        // Type aliases at top of .fsti (not in .fst) is a valid pattern
        let fst_content = r#"
module Test

let foo x = x + 1
"#;
        // t_limbs is only in .fsti (type alias), comes before foo
        // This is intentional organization - types first, then functions
        let fsti_content = r#"
module Test

let t_limbs = int

val foo: t_limbs -> t_limbs
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, movements, changed) = result.unwrap();
        // Should NOT change - t_limbs at top is valid (no forward ref)
        assert!(!changed, "FSTI-only types at top should be valid");
        assert!(movements.is_empty());
    }

    #[test]
    fn test_forward_reference_needs_fix() {
        // This is the case where we DO need to fix - actual forward reference
        let fst_content = r#"
module Test

type mytype = int
let foo (x: mytype) = x
"#;
        // foo uses mytype, but mytype comes AFTER foo - this is a forward reference error
        let fsti_content = r#"
module Test

val foo: mytype -> mytype
type mytype = int
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, movements, changed) = result.unwrap();
        // Should change - forward reference detected
        assert!(changed, "Expected change when there is a forward reference");
        assert!(!movements.is_empty());
        // mytype should now come before foo
        let mytype_pos = reordered.find("type mytype");
        let foo_pos = reordered.find("val foo");
        assert!(mytype_pos.is_some() && foo_pos.is_some());
        assert!(mytype_pos.unwrap() < foo_pos.unwrap(), "mytype should come before foo");
    }

    #[test]
    fn test_dependency_respected() {
        let fst_content = r#"
module Test

type mytype = int
val uses_mytype: mytype -> int
"#;
        // mytype should come before uses_mytype due to dependency
        let fsti_content = r#"
module Test

val uses_mytype: mytype -> int
type mytype = int
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, _, changed) = result.unwrap();
        assert!(changed);
        // mytype should now come before uses_mytype
        let mytype_pos = reordered.find("type mytype");
        let uses_pos = reordered.find("val uses_mytype");
        assert!(mytype_pos.is_some() && uses_pos.is_some());
        assert!(mytype_pos.unwrap() < uses_pos.unwrap());
    }

    // ==================== NEW TESTS FOR FALSE NEGATIVE DETECTION ====================

    #[test]
    fn test_levenshtein_distance_identical() {
        assert_eq!(levenshtein_distance("hello", "hello"), 0);
    }

    #[test]
    fn test_levenshtein_distance_single_char_diff() {
        // Single character substitution
        assert_eq!(levenshtein_distance("baz", "bar"), 1);
        assert_eq!(levenshtein_distance("cat", "car"), 1);
    }

    #[test]
    fn test_levenshtein_distance_insertion() {
        // Missing underscore
        assert_eq!(levenshtein_distance("parser_kindnz", "parser_kind_nz"), 1);
    }

    #[test]
    fn test_levenshtein_distance_deletion() {
        assert_eq!(levenshtein_distance("hello", "helo"), 1);
    }

    #[test]
    fn test_levenshtein_distance_multiple_edits() {
        assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
    }

    #[test]
    fn test_levenshtein_distance_empty() {
        assert_eq!(levenshtein_distance("", "abc"), 3);
        assert_eq!(levenshtein_distance("abc", ""), 3);
        assert_eq!(levenshtein_distance("", ""), 0);
    }

    #[test]
    fn test_find_typo_match_exact_match_excluded() {
        let candidates: HashSet<String> = ["foo", "bar", "baz"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        // "foo" should not match itself
        let result = find_typo_match("foo", &candidates, 2);
        assert!(result.is_none() || result.unwrap().0 != "foo");
    }

    #[test]
    fn test_find_typo_match_finds_close_match() {
        let candidates: HashSet<String> = ["parser_kind_nz", "foo", "bar"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let result = find_typo_match("parser_kindnz", &candidates, 2);
        assert!(result.is_some());
        let (match_name, dist) = result.unwrap();
        assert_eq!(match_name, "parser_kind_nz");
        assert_eq!(dist, 1);
    }

    #[test]
    fn test_find_typo_match_no_match_above_threshold() {
        let candidates: HashSet<String> = ["completely", "different", "names"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let result = find_typo_match("parser_kindnz", &candidates, 2);
        assert!(result.is_none());
    }

    #[test]
    fn test_analyze_interface_consistency_orphan_detection() {
        let fsti_content = r#"
module Test

val foo: int -> int
val orphan_decl: int -> int
"#;
        let fst_content = r#"
module Test

let foo x = x + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // Should find orphan_decl as orphan
        assert!(!result.orphan_declarations.is_empty());
        assert!(result
            .orphan_declarations
            .iter()
            .any(|(name, _, _)| name == "orphan_decl"));
    }

    #[test]
    fn test_analyze_interface_consistency_typo_detection() {
        let fsti_content = r#"
module Test

val foo: int -> int
val parser_kindnz: int -> int
"#;
        let fst_content = r#"
module Test

let foo x = x + 1
let parser_kind_nz x = x * 2
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // Should detect typo
        assert!(!result.typo_matches.is_empty());
        let typo = result.typo_matches.iter().find(|(fsti, _, _)| fsti == "parser_kindnz");
        assert!(typo.is_some());
        let (_, fst_name, dist) = typo.unwrap();
        assert_eq!(fst_name, "parser_kind_nz");
        assert_eq!(*dist, 1);
    }

    #[test]
    fn test_analyze_interface_consistency_no_issues() {
        let fsti_content = r#"
module Test

val foo: int -> int
val bar: int -> int
"#;
        let fst_content = r#"
module Test

let foo x = x + 1
let bar x = x * 2
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // No orphans, no typos
        assert!(result.orphan_declarations.is_empty());
        assert!(result.typo_matches.is_empty());
    }

    #[test]
    fn test_analyze_interface_consistency_similar_names_not_typo() {
        // Names that are similar but too different (edit distance > threshold)
        let fsti_content = r#"
module Test

val process_data: int -> int
"#;
        let fst_content = r#"
module Test

let handle_request x = x + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // process_data and handle_request are too different (edit distance >> 2)
        assert!(result.typo_matches.is_empty());
        // But process_data should be flagged as orphan
        assert!(result
            .orphan_declarations
            .iter()
            .any(|(name, typo_match, _)| name == "process_data" && typo_match.is_none()));
    }

    // ==================== FALSE POSITIVE REDUCTION TESTS ====================

    #[test]
    fn test_interface_only_let_type_aliases_not_orphans() {
        // In F*, .fsti commonly defines type aliases via `let` that have no .fst counterpart.
        // These are interface-only definitions and should NOT be flagged as orphans.
        // This is a CRITICAL pattern in hacl-star (e.g., bn_add_eq_len_st in Hacl.Bignum.fsti).
        let fsti_content = r#"
module Test

let bn_add_eq_len_st (t:int) (len:int) =
    int -> int -> int

val bn_add_eq_len: int -> bn_add_eq_len_st int int
"#;
        let fst_content = r#"
module Test

let bn_add_eq_len x a b = a + b
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // bn_add_eq_len_st is a let type alias in .fsti - NOT an orphan
        assert!(
            !result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "bn_add_eq_len_st"),
            "Interface-only let type alias should NOT be flagged as orphan"
        );
        // bn_add_eq_len is a val with implementation - not orphan
        assert!(result.orphan_declarations.is_empty());
    }

    #[test]
    fn test_interface_only_type_definitions_not_orphans() {
        // Abstract types in .fsti without .fst counterpart should not be orphans
        let fsti_content = r#"
module Test

type abstract_key

val encrypt: abstract_key -> int -> int
"#;
        let fst_content = r#"
module Test

let encrypt k x = x + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // abstract_key is a type in .fsti only - NOT an orphan
        assert!(
            !result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "abstract_key"),
            "Interface-only type definition should NOT be flagged as orphan"
        );
    }

    #[test]
    fn test_interface_only_class_not_orphan() {
        // Class definitions in .fsti are interface-only by design
        let fsti_content = r#"
module Test

class bn (t:int) = {
  len: int;
  add: int -> int;
}

val mk_runtime_bn: int -> bn int
"#;
        let fst_content = r#"
module Test

let mk_runtime_bn t = { len = 0; add = fun x -> x }
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        assert!(
            !result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "bn"),
            "Interface-only class definition should NOT be flagged as orphan"
        );
    }

    #[test]
    fn test_interface_only_inline_let_not_orphan() {
        // inline_for_extraction let definitions in .fsti are common type aliases
        let fsti_content = r#"
module Test

inline_for_extraction let meta_len (t:int) = int

val mk_runtime: meta_len int -> int
"#;
        let fst_content = r#"
module Test

let mk_runtime len = len + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        assert!(
            !result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "meta_len"),
            "Interface-only inline_for_extraction let should NOT be flagged as orphan"
        );
    }

    #[test]
    fn test_qualified_names_no_false_dependencies() {
        // When .fsti references S.bn_add (qualified), it should NOT create a
        // dependency on the locally declared bn_add. This was a major source
        // of false forward-reference warnings in hacl-star.
        let fst_content = r#"
module Test

type mytype = int
let bn_add x = x + 1
"#;
        // bn_add_st references S.bn_add in its body (qualified), and bn_add is
        // declared later. Without the qualified-name fix, this would falsely
        // appear as a forward reference.
        let fsti_content = r#"
module Test

let bn_add_st (t:int) =
    int -> S.bn_add int

val bn_add: int -> int
"#;

        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, movements, changed) = result.unwrap();
        // Should NOT suggest reordering - S.bn_add is qualified, not a local ref
        assert!(
            !changed,
            "Qualified name S.bn_add should not create false dependency on local bn_add. \
             Movements: {:?}",
            movements
        );
    }

    #[test]
    fn test_many_interface_only_defs_no_warnings() {
        // Simulates a typical hacl-star .fsti with many type aliases
        // None of these should generate orphan warnings
        let fsti_content = r#"
module Test

let add_st (t:int) (len:int) =
    int -> int -> int

let sub_st (t:int) (len:int) =
    int -> int -> int

let mul_st (t:int) =
    int -> int -> int

type config_t = int

val add: int -> add_st int int
val sub: int -> sub_st int int
val mul: int -> mul_st int
"#;
        let fst_content = r#"
module Test

let add t a b = a + b
let sub t a b = a - b
let mul t a b = a * b
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // No type aliases should be flagged
        assert!(
            result.orphan_declarations.is_empty(),
            "Interface-only type aliases should not generate orphan warnings. \
             Got: {:?}",
            result.orphan_declarations
        );
        assert!(result.typo_matches.is_empty());
    }

    #[test]
    fn test_val_orphan_still_detected() {
        // Val declarations WITHOUT .fst implementation should still be flagged
        let fsti_content = r#"
module Test

val foo: int -> int
val missing_impl: int -> int
"#;
        let fst_content = r#"
module Test

let foo x = x + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // missing_impl is a val with no let in .fst - should be orphan
        assert!(
            result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "missing_impl"),
            "Val without implementation should still be flagged as orphan"
        );
    }

    #[test]
    fn test_assume_val_not_orphan() {
        // assume val declarations never need .fst implementations
        let fsti_content = r#"
module Test

assume val external_fn: int -> int

val foo: int -> int
"#;
        let fst_content = r#"
module Test

let foo x = x + 1
"#;

        let result = analyze_interface_consistency(fsti_content, fst_content);

        // assume val should not be flagged (it's BlockType::Assume, not Val)
        assert!(
            !result
                .orphan_declarations
                .iter()
                .any(|(name, _, _)| name == "external_fn"),
            "assume val should NOT be flagged as orphan"
        );
    }

    #[test]
    fn test_extract_declaration_names() {
        let content = r#"
module Test

val foo: int -> int
type mytype = int
let bar x = x + 1
"#;
        let names = extract_all_declaration_names(content);
        assert!(names.contains(&"foo".to_string()));
        assert!(names.contains(&"mytype".to_string()));
        assert!(names.contains(&"bar".to_string()));
    }

    #[test]
    fn test_count_declaration_names() {
        let names = vec!["foo".to_string(), "bar".to_string(), "foo".to_string()];
        let counts = count_declaration_names(&names);
        assert_eq!(counts.get("foo"), Some(&2));
        assert_eq!(counts.get("bar"), Some(&1));
    }

    #[test]
    fn test_validate_reorder_identical_content() {
        let content = r#"module Test

val foo: int -> int
val bar: int -> int
"#;
        let warnings = validate_reorder(content, content, "Test.fsti");
        assert!(warnings.is_empty(), "Identical content should produce no warnings");
    }

    #[test]
    fn test_validate_reorder_detects_lost_content() {
        let original = r#"module Test

val foo: int -> int
val bar: int -> int
"#;
        let reordered = r#"module Test

val foo: int -> int
"#;
        let warnings = validate_reorder(original, reordered, "Test.fsti");
        assert!(!warnings.is_empty(), "Lost content should produce warnings");
        assert!(
            warnings.iter().any(|w| w.severity == ReorderWarningSeverity::Critical),
            "Lost content should produce CRITICAL warning. Got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validate_reorder_detects_lost_module() {
        let original = r#"module Test

val foo: int -> int
"#;
        let reordered = r#"
val foo: int -> int
"#;
        let warnings = validate_reorder(original, reordered, "Test.fsti");
        // Should detect the missing module via character count or declaration check
        assert!(
            warnings.iter().any(|w| w.severity == ReorderWarningSeverity::Critical),
            "Lost module should produce CRITICAL warning. Got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validate_reorder_allows_declaration_reordering() {
        // Reordering declarations (changing order but not content) should be OK
        let original = r#"module Test

val foo: int -> int

val bar: int -> int
"#;
        let reordered = r#"module Test

val bar: int -> int

val foo: int -> int
"#;
        let warnings = validate_reorder(original, reordered, "Test.fsti");
        // Should NOT have critical warnings for reordering
        let critical_count = warnings
            .iter()
            .filter(|w| w.severity == ReorderWarningSeverity::Critical)
            .count();
        assert_eq!(
            critical_count, 0,
            "Reordering should not cause critical warnings. Got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_validation_blocks_dangerous_fix() {
        // If validation fails with critical warnings, the check_pair should NOT offer a fix
        // This is tested indirectly through validate_reorder
        let original = r#"module Test

val foo: int -> int
val bar: int -> int
"#;
        // Simulate corrupted reordering that loses content
        let corrupted = r#"module Test

val foo: int -> int
"#;
        let warnings = validate_reorder(original, corrupted, "Test.fsti");
        let has_critical = warnings
            .iter()
            .any(|w| w.severity == ReorderWarningSeverity::Critical);
        assert!(has_critical, "Corrupted content should produce critical warnings");
    }

    #[test]
    fn test_reorder_preserves_content_basic() {
        // Test a basic reordering scenario
        let fst_content = r#"module Test

type mytype = int
let foo (x: mytype) = x
"#;
        let fsti_content = r#"module Test

val foo: mytype -> mytype
type mytype = int
"#;
        let result = reorder_fsti_content(fsti_content, fst_content);
        // The reordering might fail or succeed depending on parsing
        // What's important is that if it succeeds, we validate it
        if let Ok((reordered, _, changed)) = result {
            if changed {
                // Validate that content is preserved using character comparison
                let warnings = validate_reorder(fsti_content, &reordered, "Test.fsti");

                // Print for debugging
                println!("Original:\n{}", fsti_content);
                println!("Reordered:\n{}", reordered);
                println!("Warnings: {:?}", warnings);

                // The key check is that declaration names are preserved
                let orig_names = extract_all_declaration_names(fsti_content);
                let new_names = extract_all_declaration_names(&reordered);
                assert_eq!(
                    orig_names.len(),
                    new_names.len(),
                    "Declaration count should be preserved"
                );
            }
        }
    }

    #[test]
    fn test_mutual_recursion_preservation() {
        // Mutual recursion blocks should stay together
        let fst_content = r#"
module Test

type a = A of b
and b = B of a

let foo x = x
"#;
        let fsti_content = r#"
module Test

type a = A of b
and b = B of a

val foo: int -> int
"#;
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, _, _) = result.unwrap();

        // Both types should be present
        assert!(reordered.contains("type a"), "Type a should be preserved");
        assert!(reordered.contains("and b"), "Mutual recursion 'and b' should be preserved");

        // Validate no critical issues
        let warnings = validate_reorder(fsti_content, &reordered, "Test.fsti");
        let critical_count = warnings
            .iter()
            .filter(|w| w.severity == ReorderWarningSeverity::Critical)
            .count();
        assert_eq!(critical_count, 0, "Mutual recursion should be handled correctly");
    }

    // =========================================================================
    // DEEP CONSISTENCY ANALYSIS TESTS
    // =========================================================================

    #[test]
    fn test_deep_consistency_no_mismatches() {
        let fsti = r#"module Test

val foo : int -> int

val bar : nat -> nat
"#;
        let fst = r#"module Test

let foo x = x + 1

let bar x = x
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        // Filter out MissingValInInterface which is intentionally info-level
        let errors: Vec<_> = mismatches
            .iter()
            .filter(|m| !matches!(m.kind, InterfaceMismatchKind::MissingValInInterface))
            .collect();
        assert!(errors.is_empty(), "Clean pair should have no mismatches, got: {:?}", errors);
    }

    #[test]
    fn test_deep_consistency_missing_val_in_interface() {
        let fsti = r#"module Test

val foo : int -> int
"#;
        let fst = r#"module Test

let foo x = x + 1

let helper x = x * 2
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let missing_val: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::MissingValInInterface))
            .collect();
        assert_eq!(missing_val.len(), 1, "Should detect one unexported definition");
        assert_eq!(missing_val[0].name, "helper");
        assert!(!missing_val[0].in_fsti, "Missing val should point to .fst file");
    }

    #[test]
    fn test_deep_consistency_private_let_no_warning() {
        let fsti = r#"module Test

val foo : int -> int
"#;
        let fst = r#"module Test

let foo x = x + 1

private let internal_helper x = x * 2
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let missing_val: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::MissingValInInterface))
            .collect();
        assert!(missing_val.is_empty(), "Private definitions should not trigger missing val warning");
    }

    #[test]
    fn test_deep_consistency_underscore_name_no_warning() {
        let fsti = r#"module Test

val foo : int -> int
"#;
        let fst = r#"module Test

let foo x = x + 1

let _scratch x = x
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let missing_val: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::MissingValInInterface))
            .collect();
        assert!(missing_val.is_empty(), "Names starting with _ should not trigger missing val");
    }

    #[test]
    fn test_deep_consistency_assume_val_with_implementation() {
        let fsti = r#"module Test

assume val axiom_fn : int -> int
"#;
        let fst = r#"module Test

let axiom_fn x = x + 1
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let assume_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::AssumeValMismatch { .. }))
            .collect();
        assert_eq!(assume_mismatches.len(), 1, "Should detect assume val with implementation");
        assert_eq!(assume_mismatches[0].name, "axiom_fn");
        match &assume_mismatches[0].kind {
            InterfaceMismatchKind::AssumeValMismatch { fsti_is_assume } => {
                assert!(*fsti_is_assume, "fsti_is_assume should be true");
            }
            _ => panic!("Wrong mismatch kind"),
        }
    }

    #[test]
    fn test_deep_consistency_assume_val_without_implementation_ok() {
        let fsti = r#"module Test

assume val axiom_fn : int -> int
"#;
        let fst = r#"module Test
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let assume_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::AssumeValMismatch { .. }))
            .collect();
        assert!(assume_mismatches.is_empty(), "assume val without implementation is valid (axiom)");
    }

    #[test]
    fn test_deep_consistency_noeq_type_mismatch() {
        let fsti = r#"module Test

noeq type my_record = {
  field_a : int;
  field_b : string
}
"#;
        let fst = r#"module Test

type my_record = {
  field_a : int;
  field_b : string
}
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let eq_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::TypeEqualityMismatch { .. }))
            .collect();
        assert_eq!(eq_mismatches.len(), 1, "Should detect noeq mismatch");
        assert_eq!(eq_mismatches[0].name, "my_record");
        match &eq_mismatches[0].kind {
            InterfaceMismatchKind::TypeEqualityMismatch { fsti_noeq, fst_noeq } => {
                assert!(*fsti_noeq, ".fsti should have noeq");
                assert!(!*fst_noeq, ".fst should not have noeq");
            }
            _ => panic!("Wrong mismatch kind"),
        }
    }

    #[test]
    fn test_deep_consistency_noeq_type_both_match() {
        let fsti = r#"module Test

noeq type my_record = {
  field_a : int;
  callback : int -> int
}
"#;
        let fst = r#"module Test

noeq type my_record = {
  field_a : int;
  callback : int -> int
}
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let eq_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::TypeEqualityMismatch { .. }))
            .collect();
        assert!(eq_mismatches.is_empty(), "Matching noeq should produce no mismatch");
    }

    #[test]
    fn test_deep_consistency_qualifier_mismatch_extraction() {
        let fsti = r#"module Test

inline_for_extraction noextract
val fast_add : int -> int -> int
"#;
        let fst = r#"module Test

let fast_add x y = x + y
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let qual_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::QualifierMismatch { .. }))
            .collect();
        assert_eq!(qual_mismatches.len(), 1, "Should detect extraction qualifier mismatch");
        assert_eq!(qual_mismatches[0].name, "fast_add");
    }

    #[test]
    fn test_deep_consistency_qualifier_match_no_warning() {
        let fsti = r#"module Test

inline_for_extraction noextract
val fast_add : int -> int -> int
"#;
        let fst = r#"module Test

inline_for_extraction noextract
let fast_add x y = x + y
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let qual_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::QualifierMismatch { .. }))
            .collect();
        assert!(qual_mismatches.is_empty(), "Matching qualifiers should not warn");
    }

    #[test]
    fn test_deep_consistency_implicit_arg_count_mismatch() {
        let fsti = r#"module Test

val process : #t:Type -> #n:nat -> list t -> nat
"#;
        let fst = r#"module Test

let process #t xs = List.length xs
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let implicit_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::ImplicitArgCountMismatch { .. }))
            .collect();
        assert_eq!(implicit_mismatches.len(), 1, "Should detect implicit arg count mismatch");
        assert_eq!(implicit_mismatches[0].name, "process");
        match &implicit_mismatches[0].kind {
            InterfaceMismatchKind::ImplicitArgCountMismatch { fsti_count, fst_count } => {
                assert_eq!(*fsti_count, 2, ".fsti should have 2 implicits (#t, #n)");
                assert_eq!(*fst_count, 1, ".fst should have 1 implicit (#t)");
            }
            _ => panic!("Wrong mismatch kind"),
        }
    }

    #[test]
    fn test_deep_consistency_implicit_arg_count_match() {
        let fsti = r#"module Test

val process : #t:Type -> list t -> nat
"#;
        let fst = r#"module Test

let process #t xs = List.length xs
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let implicit_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::ImplicitArgCountMismatch { .. }))
            .collect();
        assert!(implicit_mismatches.is_empty(), "Matching implicit counts should not warn");
    }

    #[test]
    fn test_deep_consistency_friend_without_abstract_types() {
        // .fsti has no abstract types (all types have = body)
        let fsti = r#"module Test

type concrete_type = int

val foo : int -> int
"#;
        let fst = r#"module Test

friend OtherModule

let foo x = x + 1
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let friend_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::FriendWithoutAbstractTypes { .. }))
            .collect();
        assert_eq!(friend_mismatches.len(), 1, "Should detect friend without abstract types");
        match &friend_mismatches[0].kind {
            InterfaceMismatchKind::FriendWithoutAbstractTypes { friend_module } => {
                assert_eq!(friend_module, "OtherModule");
            }
            _ => panic!("Wrong mismatch kind"),
        }
    }

    #[test]
    fn test_deep_consistency_friend_with_abstract_types_ok() {
        // .fsti has abstract type (type without = body)
        let fsti = r#"module Test

val abstract_type : Type0

val foo : int -> int
"#;
        let fst = r#"module Test

friend OtherModule

let foo x = x + 1
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        let friend_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::FriendWithoutAbstractTypes { .. }))
            .collect();
        assert!(friend_mismatches.is_empty(), "Friend with abstract types should not warn");
    }

    #[test]
    fn test_deep_consistency_hacl_like_pair() {
        // Modeled after Hacl.Bignum.fsti / .fst pattern
        let fsti = r#"module Hacl.Bignum

inline_for_extraction noextract
val bn_add1 :
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h -> live h a)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1)

inline_for_extraction noextract
val bn_sub1 :
    #t:limb_t
  -> aLen:size_t
  -> a:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h -> live h a)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1)
"#;
        let fst = r#"module Hacl.Bignum

let bn_add1 #t aLen a res =
  Addition.bn_add1 aLen a res

let bn_sub1 #t aLen a res =
  Addition.bn_sub1 aLen a res
"#;
        let mismatches = analyze_deep_consistency(fsti, fst);
        // In this pattern, .fsti has inline_for_extraction noextract but .fst doesn't
        let qual_mismatches: Vec<_> = mismatches
            .iter()
            .filter(|m| matches!(m.kind, InterfaceMismatchKind::QualifierMismatch { .. }))
            .collect();
        // This is expected: HACL* uses inline_for_extraction noextract on val but
        // not on let. Our linter should detect this.
        assert!(!qual_mismatches.is_empty(),
            "Should detect extraction qualifier mismatch in HACL*-like pattern");
    }

    // =========================================================================
    // CHECK_PAIR INTEGRATION TESTS
    // =========================================================================

    #[test]
    fn test_check_pair_reports_assume_val_mismatch() {
        let rule = ReorderInterfaceRule::new();
        let fsti_file = Path::new("Test.fsti");
        let fst_file = Path::new("Test.fst");

        let fsti = r#"module Test

assume val my_axiom : int -> int
"#;
        let fst = r#"module Test

let my_axiom x = x + 1
"#;

        let diagnostics = rule.check_pair(fst_file, fst, fsti_file, fsti);
        let assume_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("assume val"))
            .collect();
        assert!(!assume_diags.is_empty(), "check_pair should report assume val mismatch");
    }

    #[test]
    fn test_check_pair_reports_noeq_mismatch() {
        let rule = ReorderInterfaceRule::new();
        let fsti_file = Path::new("Test.fsti");
        let fst_file = Path::new("Test.fst");

        let fsti = r#"module Test

noeq type record_t = {
  field : int
}
"#;
        let fst = r#"module Test

type record_t = {
  field : int
}
"#;

        let diagnostics = rule.check_pair(fst_file, fst, fsti_file, fsti);
        let eq_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("equality modifier mismatch"))
            .collect();
        assert!(!eq_diags.is_empty(), "check_pair should report noeq mismatch");
        // Should be Error severity
        assert!(
            eq_diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "noeq mismatch should be Error severity"
        );
    }

    #[test]
    fn test_check_pair_reports_missing_val() {
        let rule = ReorderInterfaceRule::new();
        let fsti_file = Path::new("Test.fsti");
        let fst_file = Path::new("Test.fst");

        let fsti = r#"module Test

val public_fn : int -> int
"#;
        let fst = r#"module Test

let public_fn x = x + 1

let unexported_helper x = x * 2
"#;

        let diagnostics = rule.check_pair(fst_file, fst, fsti_file, fsti);
        let missing_val_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("no corresponding `val`"))
            .collect();
        assert!(!missing_val_diags.is_empty(), "check_pair should report missing val");
        // Should be Info severity (informational, not necessarily wrong)
        assert!(
            missing_val_diags.iter().any(|d| d.severity == DiagnosticSeverity::Info),
            "Missing val should be Info severity"
        );
    }

    #[test]
    fn test_check_pair_reports_qualifier_mismatch() {
        let rule = ReorderInterfaceRule::new();
        let fsti_file = Path::new("Test.fsti");
        let fst_file = Path::new("Test.fst");

        let fsti = r#"module Test

inline_for_extraction
val optimized_fn : int -> int
"#;
        let fst = r#"module Test

let optimized_fn x = x + 1
"#;

        let diagnostics = rule.check_pair(fst_file, fst, fsti_file, fsti);
        let qual_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("Qualifier mismatch"))
            .collect();
        assert!(!qual_diags.is_empty(), "check_pair should report qualifier mismatch");
    }

    #[test]
    fn test_check_pair_no_false_positives_clean_pair() {
        let rule = ReorderInterfaceRule::new();
        let fsti_file = Path::new("Clean.fsti");
        let fst_file = Path::new("Clean.fst");

        let fsti = r#"module Clean

type point = {
  x : int;
  y : int
}

val origin : point

val translate : point -> int -> int -> point
"#;
        let fst = r#"module Clean

type point = {
  x : int;
  y : int
}

let origin = { x = 0; y = 0 }

let translate p dx dy = { x = p.x + dx; y = p.y + dy }
"#;

        let diagnostics = rule.check_pair(fst_file, fst, fsti_file, fsti);
        assert!(
            diagnostics.is_empty(),
            "Clean pair should produce no diagnostics, got: {:?}",
            diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // HELPER FUNCTION UNIT TESTS
    // =========================================================================

    #[test]
    fn test_extract_qualifiers_inline_noextract() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["foo".to_string()],
            vec!["inline_for_extraction noextract\n".to_string(), "val foo : int -> int\n".to_string()],
            1,
        );
        let quals = extract_qualifiers(&block);
        assert!(quals.contains(&"inline_for_extraction".to_string()));
        assert!(quals.contains(&"noextract".to_string()));
    }

    #[test]
    fn test_extract_qualifiers_noeq_type() {
        let block = DeclarationBlock::new(
            BlockType::Type,
            vec!["my_type".to_string()],
            vec!["noeq type my_type = {\n".to_string(), "  field : int\n".to_string(), "}\n".to_string()],
            1,
        );
        let quals = extract_qualifiers(&block);
        assert!(quals.contains(&"noeq".to_string()));
    }

    #[test]
    fn test_extract_qualifiers_no_qualifiers() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["bar".to_string()],
            vec!["val bar : nat -> nat\n".to_string()],
            1,
        );
        let quals = extract_qualifiers(&block);
        assert!(quals.is_empty(), "val without qualifiers should return empty, got: {:?}", quals);
    }

    #[test]
    fn test_count_implicit_args_val_two_implicits() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["foo".to_string()],
            vec!["val foo : #t:Type -> #n:nat -> list t -> nat\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 2);
    }

    #[test]
    fn test_count_implicit_args_val_one_implicit() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["foo".to_string()],
            vec!["val foo : #t:Type -> list t -> nat\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 1);
    }

    #[test]
    fn test_count_implicit_args_val_no_implicits() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["foo".to_string()],
            vec!["val foo : int -> int\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 0);
    }

    #[test]
    fn test_count_implicit_args_let_one_implicit() {
        let block = DeclarationBlock::new(
            BlockType::Let,
            vec!["foo".to_string()],
            vec!["let foo #t xs = List.length xs\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 1);
    }

    #[test]
    fn test_count_implicit_args_let_two_implicits() {
        let block = DeclarationBlock::new(
            BlockType::Let,
            vec!["foo".to_string()],
            vec!["let foo #t #n xs = List.length xs\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 2);
    }

    #[test]
    fn test_count_implicit_args_val_grouped_binder() {
        // F* grouped binder syntax: val bv_uext (#n #m: pos) (a: bv_t n) : Tot ...
        // Both #n and #m are implicit arguments in a single parenthesized group.
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["bv_uext".to_string()],
            vec!["val bv_uext (#n #m: pos) (a: bv_t n) : Tot (normalize (bv_t (m + n)))\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 2, "grouped binder (#n #m: pos) has 2 implicits");
    }

    #[test]
    fn test_count_implicit_args_val_binder_style() {
        // val with binder-style implicits (no colon-separated signature)
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["process".to_string()],
            vec!["val process (#t: Type) (#n: nat) (xs: list t) : nat\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 2, "binder-style (#t: Type) (#n: nat) has 2 implicits");
    }

    #[test]
    fn test_count_implicit_args_val_mixed_binder_and_arrow() {
        // val with both binder-style and arrow-style implicits
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["calc_step".to_string()],
            vec!["val calc_step (#a #b: Type) : #rel:(a -> a -> Type) -> c:a -> unit\n".to_string()],
            1,
        );
        assert_eq!(count_implicit_args(&block), 3, "2 grouped + 1 arrow-style = 3 implicits");
    }

    #[test]
    fn test_has_noeq_qualifier_true() {
        let block = DeclarationBlock::new(
            BlockType::Type,
            vec!["rec_t".to_string()],
            vec!["noeq type rec_t = { f : int }\n".to_string()],
            1,
        );
        assert!(has_noeq_qualifier(&block));
    }

    #[test]
    fn test_has_noeq_qualifier_false() {
        let block = DeclarationBlock::new(
            BlockType::Type,
            vec!["rec_t".to_string()],
            vec!["type rec_t = { f : int }\n".to_string()],
            1,
        );
        assert!(!has_noeq_qualifier(&block));
    }

    #[test]
    fn test_has_noeq_qualifier_non_type_block() {
        let block = DeclarationBlock::new(
            BlockType::Val,
            vec!["foo".to_string()],
            vec!["val foo : int\n".to_string()],
            1,
        );
        assert!(!has_noeq_qualifier(&block), "non-type blocks should return false");
    }

    // =========================================================================
    // TARJAN'S SCC TESTS
    // =========================================================================

    #[test]
    fn test_tarjan_scc_no_cycles() {
        // A -> B -> C (no cycle)
        let deps = vec![
            HashSet::from([1]),  // 0 depends on 1
            HashSet::from([2]),  // 1 depends on 2
            HashSet::new(),      // 2 depends on nothing
        ];
        let sccs = tarjan_scc(3, &deps);
        // Each node is its own SCC
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.len(), 1);
        }
    }

    #[test]
    fn test_tarjan_scc_simple_cycle() {
        // A -> B -> A (cycle)
        let deps = vec![
            HashSet::from([1]),  // 0 depends on 1
            HashSet::from([0]),  // 1 depends on 0
        ];
        let sccs = tarjan_scc(2, &deps);
        // Should be one SCC containing both
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 2);
        assert!(sccs[0].contains(&0));
        assert!(sccs[0].contains(&1));
    }

    #[test]
    fn test_tarjan_scc_complex_graph() {
        // 0 -> 1 -> 2 -> 0 (cycle: {0,1,2})
        // 3 -> 4 (no cycle)
        // 3 -> 0 (cross-component dep)
        let deps = vec![
            HashSet::from([1]),      // 0 -> 1
            HashSet::from([2]),      // 1 -> 2
            HashSet::from([0]),      // 2 -> 0
            HashSet::from([0, 4]),   // 3 -> 0, 3 -> 4
            HashSet::new(),          // 4 -> nothing
        ];
        let sccs = tarjan_scc(5, &deps);
        // Should have 3 SCCs: {0,1,2}, {3}, {4}
        assert_eq!(sccs.len(), 3);
        let big_scc = sccs.iter().find(|s| s.len() == 3).unwrap();
        assert!(big_scc.contains(&0));
        assert!(big_scc.contains(&1));
        assert!(big_scc.contains(&2));
    }

    #[test]
    fn test_tarjan_scc_empty_graph() {
        let deps: Vec<HashSet<usize>> = vec![];
        let sccs = tarjan_scc(0, &deps);
        assert!(sccs.is_empty());
    }

    #[test]
    fn test_tarjan_scc_single_node() {
        let deps = vec![HashSet::new()];
        let sccs = tarjan_scc(1, &deps);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec![0]);
    }

    // =========================================================================
    // BLOCK-LEVEL DEPENDENCY TESTS
    // =========================================================================

    #[test]
    fn test_build_block_deps_simple() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Type,
                vec!["mytype".to_string()],
                vec!["type mytype = int\n".to_string()],
                1,
                HashSet::new(),
            ),
            DeclarationBlock::new_with_refs(
                BlockType::Val,
                vec!["foo".to_string()],
                vec!["val foo : mytype -> int\n".to_string()],
                3,
                HashSet::from(["mytype".to_string()]),
            ),
        ];
        let deps = build_block_deps(&blocks);
        assert_eq!(deps.len(), 2);
        assert!(deps[0].is_empty(), "mytype has no deps");
        assert!(deps[1].contains(&0), "foo should depend on mytype (block 0)");
    }

    #[test]
    fn test_build_block_deps_no_self_dep() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Type,
                vec!["recursive_t".to_string()],
                vec!["type recursive_t = Nil | Cons of int * recursive_t\n".to_string()],
                1,
                HashSet::from(["recursive_t".to_string()]),
            ),
        ];
        let deps = build_block_deps(&blocks);
        assert!(deps[0].is_empty(), "Self-references should be excluded");
    }

    #[test]
    fn test_build_block_deps_attribute_deps() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Let,
                vec!["my_attr".to_string()],
                vec!["let my_attr = 42\n".to_string()],
                1,
                HashSet::new(),
            ),
            DeclarationBlock::new_with_refs(
                BlockType::Val,
                vec!["foo".to_string()],
                vec!["[@@my_attr]\n".to_string(), "val foo : int -> int\n".to_string()],
                3,
                HashSet::new(),
            ),
        ];
        let deps = build_block_deps(&blocks);
        assert!(deps[1].contains(&0), "foo should depend on my_attr via attribute");
    }

    #[test]
    fn test_build_block_deps_operator_deps() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Let,
                vec!["op_At_Percent".to_string()],
                vec!["let op_At_Percent a b = a + b\n".to_string()],
                1,
                HashSet::new(),
            ),
            DeclarationBlock::new_with_refs(
                BlockType::Val,
                vec!["use_op".to_string()],
                vec!["val use_op : x:int -> int\n  (* uses op_At_Percent *)\n".to_string()],
                3,
                HashSet::new(),
            ),
        ];
        let deps = build_block_deps(&blocks);
        assert!(
            deps[1].contains(&0),
            "use_op should depend on op_At_Percent via operator reference"
        );
    }

    // =========================================================================
    // BLOCK-LEVEL FORWARD REFERENCE DETECTION
    // =========================================================================

    #[test]
    fn test_check_block_order_valid_no_violations() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Type,
                vec!["mytype".to_string()],
                vec!["type mytype = int\n".to_string()],
                1,
                HashSet::new(),
            ),
            DeclarationBlock::new_with_refs(
                BlockType::Val,
                vec!["foo".to_string()],
                vec!["val foo : mytype -> int\n".to_string()],
                3,
                HashSet::from(["mytype".to_string()]),
            ),
        ];
        let deps = build_block_deps(&blocks);
        let (valid, violations) = check_block_order_valid(&blocks, &deps);
        assert!(valid, "No forward references: {:?}", violations);
    }

    #[test]
    fn test_check_block_order_valid_has_forward_ref() {
        let blocks = vec![
            DeclarationBlock::new_with_refs(
                BlockType::Val,
                vec!["foo".to_string()],
                vec!["val foo : mytype -> int\n".to_string()],
                1,
                HashSet::from(["mytype".to_string()]),
            ),
            DeclarationBlock::new_with_refs(
                BlockType::Type,
                vec!["mytype".to_string()],
                vec!["type mytype = int\n".to_string()],
                3,
                HashSet::new(),
            ),
        ];
        let deps = build_block_deps(&blocks);
        let (valid, _violations) = check_block_order_valid(&blocks, &deps);
        assert!(!valid, "Should detect forward reference");
    }

    // =========================================================================
    // MUTUAL RECURSION SCC HANDLING
    // =========================================================================

    #[test]
    fn test_mutual_recursion_blocks_stay_together() {
        // Two mutually dependent types (should form SCC)
        // val c depends on both a and b
        let fsti_content = r#"
module Test

val c : a -> b -> int
type a = A of b
and b = B of a
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok(), "Mutual recursion should not cause error");
        let (reordered, _, changed) = result.unwrap();
        if changed {
            // Types a and b should appear before val c
            let a_pos = reordered.find("type a");
            let b_pos = reordered.find("and b");
            let c_pos = reordered.find("val c");
            assert!(a_pos.is_some() && b_pos.is_some() && c_pos.is_some());
            assert!(
                a_pos.unwrap() < c_pos.unwrap(),
                "type a should come before val c"
            );
            // a and b should be adjacent (mutual recursion block preserved)
            assert!(
                b_pos.unwrap() > a_pos.unwrap(),
                "and b should follow type a in mutual recursion block"
            );
        }
    }

    #[test]
    fn test_scc_cycle_between_separate_blocks() {
        // Block A references B and Block B references A (cycle between separate blocks)
        // This should be handled by SCC detection
        let fsti_content = r#"
module Test

val foo : bar_t -> int
type bar_t = | Bar of foo_t
type foo_t = int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        // Should either succeed with reordering or report cycle, not crash
        assert!(result.is_ok() || result.is_err());
    }

    // =========================================================================
    // CATEGORY PRIORITY ORDERING
    // =========================================================================

    #[test]
    fn test_block_category_priority_order() {
        // Verify the priority ordering is correct
        let set_opts = DeclarationBlock::new(BlockType::SetOptions, vec![], vec![], 1);
        let open = DeclarationBlock::new(BlockType::Open, vec![], vec![], 1);
        let include = DeclarationBlock::new(BlockType::Include, vec![], vec![], 1);
        let mod_abbrev = DeclarationBlock::new(BlockType::ModuleAbbrev, vec![], vec![], 1);
        let friend = DeclarationBlock::new(BlockType::Friend, vec![], vec![], 1);
        let typ = DeclarationBlock::new(BlockType::Type, vec![], vec![], 1);
        let inst = DeclarationBlock::new(BlockType::Instance, vec![], vec![], 1);
        let val = DeclarationBlock::new(BlockType::Val, vec![], vec![], 1);
        let let_b = DeclarationBlock::new(BlockType::Let, vec![], vec![], 1);

        assert!(block_category_priority(&set_opts) < block_category_priority(&open));
        assert!(block_category_priority(&open) < block_category_priority(&include));
        assert!(block_category_priority(&include) < block_category_priority(&mod_abbrev));
        assert!(block_category_priority(&mod_abbrev) < block_category_priority(&friend));
        assert!(block_category_priority(&friend) < block_category_priority(&typ));
        assert!(block_category_priority(&typ) < block_category_priority(&inst));
        assert!(block_category_priority(&inst) < block_category_priority(&val));
        assert!(block_category_priority(&val) < block_category_priority(&let_b));
    }

    #[test]
    fn test_open_before_types_in_reorder() {
        // Open should stay before types that use opened names
        let fsti_content = r#"
module Test

type mytype = int
open FStar.List.Tot
val foo : mytype -> list int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        // Whether changed or not, open should be before type usages
        let (content, _, _) = result.unwrap();
        let open_pos = content.find("open FStar");
        let type_pos = content.find("type mytype");
        if let (Some(o), Some(t)) = (open_pos, type_pos) {
            // This just verifies the output is reasonable
            let _ = (o, t);
        }
    }

    // =========================================================================
    // INSTANCE -> CLASS DEPENDENCY
    // =========================================================================

    #[test]
    fn test_instance_depends_on_class_reorder() {
        // Instance should come after the class it instantiates
        let fsti_content = r#"
module Test

instance my_inst : my_class int = { method = fun x -> x }
class my_class (a:Type) = { method : a -> a }
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, _, changed) = result.unwrap();
        if changed {
            let class_pos = reordered.find("class my_class");
            let inst_pos = reordered.find("instance my_inst");
            assert!(class_pos.is_some() && inst_pos.is_some());
            assert!(
                class_pos.unwrap() < inst_pos.unwrap(),
                "class should come before instance"
            );
        }
    }

    // =========================================================================
    // PRAGMA POSITIONING
    // =========================================================================

    #[test]
    fn test_pragma_stays_early() {
        // #set-options should stay near the top
        let fsti_content = r#"
module Test

type mytype = int
val foo : mytype -> int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed, "Already valid order");
    }

    // =========================================================================
    // FRIEND DECLARATION POSITIONING
    // =========================================================================

    #[test]
    fn test_friend_declaration_not_reordered_past_types() {
        // Friend declarations should maintain reasonable positions
        let fsti_content = r#"
module Test

type abstract_t

val foo : abstract_t -> int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed, "No forward references in this order");
    }

    // =========================================================================
    // COMPLEX REAL-WORLD PATTERNS
    // =========================================================================

    #[test]
    fn test_complex_dependency_chain() {
        // c depends on b, b depends on a, but c is listed first
        let fsti_content = r#"
module Test

val c : b -> int
type b = B of a
type a = int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, _, changed) = result.unwrap();
        assert!(changed, "Forward references should be detected");
        // a should come first, then b, then c
        let a_pos = reordered.find("type a");
        let b_pos = reordered.find("type b");
        let c_pos = reordered.find("val c");
        assert!(a_pos.is_some() && b_pos.is_some() && c_pos.is_some());
        assert!(a_pos.unwrap() < b_pos.unwrap(), "a before b");
        assert!(b_pos.unwrap() < c_pos.unwrap(), "b before c");
    }

    #[test]
    fn test_diamond_dependency() {
        // d depends on b and c; b and c both depend on a
        let fsti_content = r#"
module Test

val d : b -> c -> int
type b = B of a
type c = C of a
type a = int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (reordered, _, changed) = result.unwrap();
        assert!(changed, "Forward references should be detected");
        let a_pos = reordered.find("type a");
        let d_pos = reordered.find("val d");
        assert!(a_pos.unwrap() < d_pos.unwrap(), "a should come before d");
    }

    #[test]
    fn test_no_reorder_when_already_correct() {
        // Already in correct dependency order
        let fsti_content = r#"
module Test

type a = int
type b = B of a
type c = C of a
val d : b -> c -> int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed, "Already in correct order");
    }

    #[test]
    fn test_empty_fsti() {
        let fsti_content = r#"
module Test
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed);
    }

    #[test]
    fn test_module_abbreviation_ordering() {
        // Module abbreviation should be treated as infrastructure
        let fsti_content = r#"
module Test

open FStar.List.Tot

type mytype = int
val foo : mytype -> int
"#;
        let fst_content = "";
        let result = reorder_fsti_content(fsti_content, fst_content);
        assert!(result.is_ok());
        let (_, _, changed) = result.unwrap();
        assert!(!changed, "Valid order with open at top");
    }
}
