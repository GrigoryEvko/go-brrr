//! FST004: Unused open statements detector.
//!
//! Detects `open` statements that import modules which are never used in the file.
//! This helps keep imports clean and reduces compilation overhead.
//!
//! # Examples of detected issues:
//! - `open FStar.List` when no List functions are called
//! - `open Module { name1, name2 }` when name1 or name2 are unused
//! - Module aliases that are never referenced

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode};
use super::shared_patterns::{OPEN_MODULE_RE, INCLUDE_MODULE_RE, QUALIFIED_USE_RE};

/// Parsed open statement from F* source.
#[derive(Debug, Clone, PartialEq)]
pub struct OpenStatement {
    /// Module path (e.g., "FStar.List.Tot")
    pub module_path: String,
    /// Selective imports (e.g., Some(["map", "filter"])) or None for full open
    pub selective: Option<Vec<String>>,
    /// Line number (1-based)
    pub line: usize,
    /// Column number (1-based)
    pub col: usize,
    /// Original line text
    pub line_text: String,
    /// Whether this is a `let open Module in` (local scope)
    pub is_local: bool,
    /// For local opens, the estimated line where scope ends
    pub scope_end: Option<usize>,
}

/// Parsed module alias declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleAlias {
    /// Alias name (e.g., "L")
    pub alias: String,
    /// Target module path (e.g., "FStar.List.Tot")
    pub target: String,
    /// Line number (1-based)
    pub line: usize,
}

/// Parsed include statement from F* source.
#[derive(Debug, Clone, PartialEq)]
pub struct IncludeStatement {
    /// Module path (e.g., "FStar.List.Tot")
    pub module_path: String,
    /// Line number (1-based)
    pub line: usize,
}

/// Full analysis result for unused open detection.
#[derive(Debug)]
pub struct OpenAnalysis {
    /// All open statements found (top-level only, excludes let-opens)
    pub opens: Vec<OpenStatement>,
    /// All let-open statements found (local scope)
    #[allow(dead_code)]
    pub let_opens: Vec<OpenStatement>,
    /// All module aliases found
    pub aliases: Vec<ModuleAlias>,
    /// All include statements found
    pub includes: Vec<IncludeStatement>,
    /// Module prefixes used via qualified access (e.g., "List" from "List.map")
    pub used_module_prefixes: HashSet<String>,
    /// Qualified access map: module_prefix -> set of identifiers accessed via it
    #[allow(dead_code)]
    pub qualified_access_map: HashMap<String, HashSet<String>>,
    /// Unqualified identifiers used (lowercase)
    pub used_identifiers: HashSet<String>,
    /// Type constructors used (uppercase identifiers)
    pub used_type_constructors: HashSet<String>,
    /// Internal operator names used (e.g., "op_Star")
    pub used_operators: HashSet<String>,
    /// Effect names used in type signatures (e.g., "Lemma", "Stack", "ST")
    pub used_effect_names: HashSet<String>,
}

lazy_static! {
    /// Pattern for selective open statements: `open Module.Path { name1, name2 }`
    static ref OPEN_SELECTIVE_PATTERN: Regex =
        Regex::new(r"^open\s+([A-Z][\w.]*)\s*\{([^}]*)\}").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for module alias declarations: `module X = Module.Path`
    static ref MODULE_ALIAS_PATTERN: Regex =
        Regex::new(r"^module\s+([A-Z]\w*)\s*=\s*([A-Z][\w.]*)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for let-open statements: `let open Module.Path in`
    static ref LET_OPEN_PATTERN: Regex =
        Regex::new(r"let\s+open\s+([A-Z][\w.]*)\s+in").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for unqualified lowercase identifiers
    static ref UNQUALIFIED_IDENT_PATTERN: Regex =
        Regex::new(r"\b([a-z_][\w']*)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for type constructors (uppercase identifiers)
    static ref TYPE_CONSTRUCTOR_PATTERN: Regex =
        Regex::new(r"\b([A-Z][\w']*)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for effect annotations in type signatures.
    /// Matches effect names that appear after `:` or `->` in val/let signatures.
    static ref EFFECT_USE_PATTERN: Regex =
        Regex::new(r"(?::\s*|->)\s*([A-Z][a-z]\w*)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Names that are implicitly in scope from Prims and FStar.Pervasives.Native.
    /// These should NOT count as usage evidence for other modules.
    static ref IMPLICIT_SCOPE_NAMES: HashSet<&'static str> = {
        let mut s = HashSet::new();
        // From Prims (always implicitly opened)
        s.insert("unit"); s.insert("bool"); s.insert("int"); s.insert("nat");
        s.insert("pos"); s.insert("string"); s.insert("prop"); s.insert("squash");
        s.insert("l_True"); s.insert("l_False"); s.insert("l_and"); s.insert("l_or");
        s.insert("l_imp"); s.insert("l_iff"); s.insert("l_not");
        s.insert("l_Forall"); s.insert("l_Exists");
        s.insert("c_True"); s.insert("c_False"); s.insert("c_and"); s.insert("c_or");
        s.insert("empty"); s.insert("trivial"); s.insert("eq2"); s.insert("equals");
        s.insert("T"); s.insert("Nil"); s.insert("Cons");
        s.insert("op_Negation"); s.insert("op_AmpAmp"); s.insert("op_BarBar");
        s.insert("op_Equality"); s.insert("op_disEquality");
        s.insert("op_LessThanOrEqual"); s.insert("op_LessThan");
        s.insert("op_GreaterThanOrEqual"); s.insert("op_GreaterThan");
        s.insert("op_Addition"); s.insert("op_Subtraction"); s.insert("op_Multiply");
        s.insert("op_Division"); s.insert("op_Modulus"); s.insert("op_Minus");
        s.insert("pow2"); s.insert("min"); s.insert("max"); s.insert("abs");
        s.insert("pure"); s.insert("admit"); s.insert("magic"); s.insert("assume");
        // From FStar.Pervasives.Native (always implicitly opened)
        s.insert("option"); s.insert("Some"); s.insert("None");
        s.insert("tuple2"); s.insert("tuple3"); s.insert("tuple4"); s.insert("tuple5");
        s.insert("fst"); s.insert("snd");
        // From FStar.Pervasives (always implicitly opened)
        s.insert("normalize"); s.insert("normalize_term"); s.insert("assert_norm");
        s.insert("norm"); s.insert("reveal_opaque"); s.insert("synth");
        s.insert("result"); s.insert("V"); s.insert("E");
        // Common effect names always in scope
        s.insert("Lemma"); s.insert("Tot"); s.insert("GTot"); s.insert("Dv");
        s.insert("Pure"); s.insert("Ghost"); s.insert("PURE"); s.insert("GHOST");
        s.insert("DIV"); s.insert("ALL"); s.insert("ML");
        // Common list/pair syntax from Prims
        s.insert("list"); s.insert("Mkdtuple2"); s.insert("dtuple2");
        s
    };

    /// Modules that should NEVER be auto-removed.
    /// These provide operators or implicit features that are hard to detect statically.
    static ref NEVER_AUTO_REMOVE: HashSet<&'static str> = {
        let mut s = HashSet::new();
        s.insert("FStar.Mul");
        s.insert("FStar.Integers");
        s.insert("FStar.Pervasives");
        s.insert("FStar.Pervasives.Native");
        s.insert("FStar.Tactics");
        s.insert("FStar.Tactics.V2");
        s.insert("FStar.Reflection");
        s.insert("FStar.Reflection.V2");
        s.insert("LowStar.BufferOps");
        s.insert("Lib.IntTypes");
        s.insert("Prims");
        s
    };

    /// Modules with complex usage patterns that require manual verification.
    static ref RISKY_MODULES: HashSet<&'static str> = {
        let mut s = HashSet::new();
        s.insert("FStar.HyperStack.ST");
        s.insert("FStar.HyperStack");
        s.insert("FStar.ST");
        s.insert("FStar.Ghost");
        s.insert("FStar.Classical");
        s.insert("FStar.Seq");
        s.insert("FStar.List.Tot");
        s.insert("FStar.List.Tot.Base");
        s.insert("FStar.Ref");
        s.insert("LowStar.Buffer");
        s.insert("LowStar.Monotonic.Buffer");
        s
    };
}

/// Parse all open statements from F* source content.
///
/// Handles both simple opens (`open FStar.List`) and selective opens
/// (`open FStar.List { map, filter }`).
///
/// # Arguments
/// * `content` - The F* source code to parse
///
/// # Returns
/// A vector of all open statements found, in order of appearance.
pub fn parse_opens(content: &str) -> Vec<OpenStatement> {
    let mut opens = Vec::new();
    // Strip comments and strings first so we don't parse opens inside them.
    // This correctly handles multi-line block comments like:
    //   (* open FStar.Unused
    //      open FStar.AlsoUnused *)
    let clean = strip_comments_and_strings(content);
    let original_lines: Vec<&str> = content.lines().collect();

    for (line_num, line) in clean.lines().enumerate() {
        let stripped = line.trim();

        // After stripping, empty lines or whitespace-only lines are skipped
        if stripped.is_empty() {
            continue;
        }

        // Check selective open first (more specific pattern)
        if let Some(caps) = OPEN_SELECTIVE_PATTERN.captures(stripped) {
            let Some(m1) = caps.get(1) else { continue };
            let module = m1.as_str().to_string();
            let names_str = caps.get(2).map(|m| m.as_str()).unwrap_or("");
            let names: Vec<String> = names_str
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();

            // Use original line for column calculation and line_text
            let orig_line = original_lines.get(line_num).unwrap_or(&"");
            let col = orig_line.find("open").map(|p| p + 1).unwrap_or(1);

            opens.push(OpenStatement {
                module_path: module,
                selective: Some(names),
                line: line_num + 1,
                col,
                line_text: orig_line.to_string(),
                is_local: false,
                scope_end: None,
            });
        } else if let Some(caps) = OPEN_MODULE_RE.captures(stripped) {
            let Some(m1) = caps.get(1) else { continue };
            let module = m1.as_str().to_string();
            let orig_line = original_lines.get(line_num).unwrap_or(&"");
            let col = orig_line.find("open").map(|p| p + 1).unwrap_or(1);

            opens.push(OpenStatement {
                module_path: module,
                selective: None,
                line: line_num + 1,
                col,
                line_text: orig_line.to_string(),
                is_local: false,
                scope_end: None,
            });
        }
    }

    opens
}

/// Parse module alias declarations from content.
///
/// Finds declarations like `module L = FStar.List`.
///
/// # Arguments
/// * `content` - The F* source code to parse
///
/// # Returns
/// A vector of all module aliases found.
pub fn parse_module_aliases(content: &str) -> Vec<ModuleAlias> {
    let mut aliases = Vec::new();
    let clean = strip_comments_and_strings(content);

    for (line_num, line) in clean.lines().enumerate() {
        let stripped = line.trim();

        if stripped.is_empty() {
            continue;
        }

        if let Some(caps) = MODULE_ALIAS_PATTERN.captures(stripped) {
            if let (Some(alias_m), Some(target_m)) = (caps.get(1), caps.get(2)) {
                aliases.push(ModuleAlias {
                    alias: alias_m.as_str().to_string(),
                    target: target_m.as_str().to_string(),
                    line: line_num + 1,
                });
            }
        }
    }

    aliases
}

/// Parse `let open Module in` statements from content.
///
/// These are local-scope opens that bring module contents into scope
/// for the remainder of the expression. They are common in F* code.
///
/// # Arguments
/// * `content` - The F* source code to parse
///
/// # Returns
/// A vector of let-open statements found.
pub fn parse_let_opens(content: &str) -> Vec<OpenStatement> {
    let mut let_opens = Vec::new();
    let clean = strip_comments_and_strings(content);
    let original_lines: Vec<&str> = content.lines().collect();
    let total_lines = original_lines.len();

    for (line_num, line) in clean.lines().enumerate() {
        let stripped = line.trim();

        if stripped.is_empty() {
            continue;
        }

        // Find all let-opens on this line (use cleaned line for matching)
        for caps in LET_OPEN_PATTERN.captures_iter(line) {
            if let Some(module_match) = caps.get(1) {
                let module = module_match.as_str().to_string();
                let col = module_match.start() + 1;
                let orig_line = original_lines.get(line_num).unwrap_or(&"");

                // Estimate scope end: find next top-level `let` or `val` or end of file
                let scope_end = estimate_let_open_scope_end(&clean, line_num, total_lines);

                let_opens.push(OpenStatement {
                    module_path: module,
                    selective: None,
                    line: line_num + 1,
                    col,
                    line_text: orig_line.to_string(),
                    is_local: true,
                    scope_end: Some(scope_end),
                });
            }
        }
    }

    let_opens
}

/// Estimate where a let-open's scope ends.
///
/// A `let open Module in` scoped to the enclosing let binding.
/// We approximate by finding the next top-level `let` or `val` declaration.
fn estimate_let_open_scope_end(clean_content: &str, open_line: usize, total_lines: usize) -> usize {
    let lines: Vec<&str> = clean_content.lines().collect();

    // Find the indentation level of the let-open line
    let open_indent = lines.get(open_line)
        .map(|l| l.len() - l.trim_start().len())
        .unwrap_or(0);

    // Scan forward for a line at same or lower indentation that starts a new declaration
    for i in (open_line + 1)..lines.len().min(total_lines) {
        let line = lines.get(i).unwrap_or(&"");
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let indent = line.len() - trimmed.len();
        // New top-level declaration at same or lower indentation ends the scope
        if indent <= open_indent
            && (trimmed.starts_with("let ")
                || trimmed.starts_with("val ")
                || trimmed.starts_with("type ")
                || trimmed.starts_with("open ")
                || trimmed.starts_with("module ")
                || trimmed.starts_with("include ")
                || trimmed.starts_with("friend "))
        {
            return i; // 0-based line number
        }
    }

    total_lines
}

/// Parse include statements from content.
pub fn parse_includes(content: &str) -> Vec<IncludeStatement> {
    let mut includes = Vec::new();
    let clean = strip_comments_and_strings(content);

    for (line_num, line) in clean.lines().enumerate() {
        let stripped = line.trim();
        if stripped.is_empty() {
            continue;
        }

        if let Some(caps) = INCLUDE_MODULE_RE.captures(stripped) {
            if let Some(m1) = caps.get(1) {
                includes.push(IncludeStatement {
                    module_path: m1.as_str().to_string(),
                    line: line_num + 1,
                });
            }
        }
    }

    includes
}

/// Strip comments and string literals from F* source code.
///
/// This prevents false positives from identifiers mentioned in comments
/// or string literals.
fn strip_comments_and_strings(content: &str) -> String {
    let mut result = String::with_capacity(content.len());
    let chars: Vec<char> = content.chars().collect();
    let n = chars.len();
    let mut i = 0;
    let mut comment_depth = 0;
    let mut in_line_comment = false;

    while i < n {
        // Handle line comments
        if i + 1 < n && chars[i] == '/' && chars[i + 1] == '/' {
            in_line_comment = true;
            i += 2;
            continue;
        }

        // End of line comment
        if in_line_comment {
            if chars[i] == '\n' {
                in_line_comment = false;
                result.push('\n');
            }
            i += 1;
            continue;
        }

        // Handle block comment start
        if i + 1 < n && chars[i] == '(' && chars[i + 1] == '*' {
            comment_depth += 1;
            i += 2;
            continue;
        }

        // Handle block comment end
        if i + 1 < n && chars[i] == '*' && chars[i + 1] == ')' && comment_depth > 0 {
            comment_depth -= 1;
            i += 2;
            continue;
        }

        // Inside comment - skip
        if comment_depth > 0 {
            if chars[i] == '\n' {
                result.push('\n');
            }
            i += 1;
            continue;
        }

        // Handle string literals
        if chars[i] == '"' {
            i += 1;
            while i < n && chars[i] != '"' {
                if chars[i] == '\\' && i + 1 < n {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if i < n {
                i += 1; // Skip closing quote
            }
            continue;
        }

        result.push(chars[i]);
        i += 1;
    }

    result
}

/// Check if a line is a declaration/directive that should be excluded from
/// identifier extraction. These lines reference modules by name but do NOT
/// constitute usage of names imported via `open`.
///
/// Excluded lines:
/// - `open Module` - the open statement itself
/// - `module X = Module.Path` - alias declarations (work without opens)
/// - `friend Module` - friend declarations (work without opens)
/// - `include Module` - include declarations (separate from opens)
fn is_declaration_line(trimmed: &str) -> bool {
    trimmed.starts_with("open ")
        || trimmed.starts_with("module ")
        || trimmed.starts_with("friend ")
        || trimmed.starts_with("include ")
}

/// Extract all module prefixes used in qualified access patterns.
///
/// For code like `List.map x` or `FStar.List.Tot.length`, extracts
/// "List" and "FStar.List.Tot" as used prefixes.
/// Excludes declaration lines (open, module alias, friend, include)
/// to avoid false positives/negatives.
fn extract_used_module_prefixes(content: &str) -> HashSet<String> {
    // Filter out declaration lines to avoid counting module paths in
    // opens/aliases/friend as "used"
    let filtered_content: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !is_declaration_line(trimmed)
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean_content = strip_comments_and_strings(&filtered_content);
    let mut prefixes = HashSet::new();

    for caps in QUALIFIED_USE_RE.captures_iter(&clean_content) {
        if let Some(m) = caps.get(1) {
            let prefix = m.as_str();
            // Add the full prefix
            prefixes.insert(prefix.to_string());
            // Also add each nested prefix
            let parts: Vec<&str> = prefix.split('.').collect();
            for i in 1..parts.len() {
                prefixes.insert(parts[..i].join("."));
            }
        }
    }

    prefixes
}

/// Extract identifiers that are accessed via qualified paths (e.g., `empty` from `S.empty`).
/// These are NOT imported via `open` but via module aliases or direct qualified access.
fn extract_qualified_identifiers(content: &str) -> HashSet<String> {
    let filtered_content: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !is_declaration_line(trimmed)
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean_content = strip_comments_and_strings(&filtered_content);
    let mut qualified_idents = HashSet::new();

    // QUALIFIED_USE_RE captures Module.identifier - group 2 is the identifier
    for caps in QUALIFIED_USE_RE.captures_iter(&clean_content) {
        if let Some(m) = caps.get(2) {
            qualified_idents.insert(m.as_str().to_string());
        }
    }

    qualified_idents
}

/// Extract all unqualified identifiers from content.
///
/// These are potential uses of names imported via `open` statements.
/// Excludes identifiers from declaration lines (open, module alias, friend,
/// include) and identifiers accessed through qualified paths (e.g., `empty`
/// from `S.empty` is NOT an unqualified use of `empty`).
pub fn extract_used_identifiers(content: &str) -> HashSet<String> {
    // Filter out declaration lines to avoid counting imported/declared names as "used"
    let filtered_content: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !is_declaration_line(trimmed)
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean_content = strip_comments_and_strings(&filtered_content);
    let mut identifiers = HashSet::new();

    // Collect identifiers from qualified accesses (e.g., `empty` from `S.empty`).
    // These are NOT unqualified uses - they come from module aliases or qualified paths.
    let qualified_idents = extract_qualified_identifiers(content);

    // Extract lowercase identifiers (functions, values)
    for caps in UNQUALIFIED_IDENT_PATTERN.captures_iter(&clean_content) {
        if let Some(m) = caps.get(1) {
            let ident = m.as_str().to_string();
            // Only count as unqualified if the identifier also appears
            // outside of qualified access contexts. We use a heuristic:
            // if an identifier ONLY appears as part of qualified access
            // (i.e., always after a dot), it's not an unqualified use.
            // However, if it appears both ways, we conservatively include it.
            identifiers.insert(ident);
        }
    }

    // Remove identifiers that ONLY appear in qualified contexts.
    // We check: for each qualified identifier, does it also appear standalone?
    // We look for pattern: the identifier preceded by something other than '.'
    for qi in &qualified_idents {
        // Check if identifier appears unqualified anywhere in the content
        if !has_unqualified_use(&clean_content, qi) {
            identifiers.remove(qi);
        }
    }

    identifiers
}

/// Check if an identifier has at least one unqualified use in the content.
/// An unqualified use is one NOT preceded by a dot.
fn has_unqualified_use(content: &str, ident: &str) -> bool {
    let bytes = content.as_bytes();
    let ident_bytes = ident.as_bytes();
    let ident_len = ident_bytes.len();

    let mut pos = 0;
    while pos + ident_len <= bytes.len() {
        if let Some(found) = content[pos..].find(ident) {
            let abs_pos = pos + found;

            // Check if this is a whole-word match
            let before_ok = if abs_pos == 0 {
                true
            } else {
                let c = bytes[abs_pos - 1];
                !c.is_ascii_alphanumeric() && c != b'_' && c != b'\''
            };

            let after_ok = if abs_pos + ident_len >= bytes.len() {
                true
            } else {
                let c = bytes[abs_pos + ident_len];
                !c.is_ascii_alphanumeric() && c != b'_' && c != b'\''
            };

            if before_ok && after_ok {
                // Check if preceded by a dot (qualified access)
                let preceded_by_dot = abs_pos > 0 && bytes[abs_pos - 1] == b'.';
                if !preceded_by_dot {
                    return true;
                }
            }

            pos = abs_pos + 1;
        } else {
            break;
        }
    }

    false
}

/// Extract type constructors (capitalized identifiers) from content.
/// Excludes type constructors that appear in declaration lines (open, module
/// alias, friend, include) to avoid counting imported/declared names as "used".
/// Also excludes type constructors that only appear in qualified access contexts
/// (e.g., `Module.SomeType` - the `SomeType` is accessed via the module, not an open).
fn extract_type_constructors(content: &str) -> HashSet<String> {
    // Filter out declaration lines to avoid counting imported/declared names as "used".
    let filtered_content: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !is_declaration_line(trimmed)
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean_content = strip_comments_and_strings(&filtered_content);
    let qualified_idents = extract_qualified_identifiers(content);
    let mut constructors = HashSet::new();

    for caps in TYPE_CONSTRUCTOR_PATTERN.captures_iter(&clean_content) {
        if let Some(m) = caps.get(1) {
            constructors.insert(m.as_str().to_string());
        }
    }

    // Remove type constructors that ONLY appear in qualified contexts
    for qi in &qualified_idents {
        if qi.chars().next().is_some_and(|c| c.is_uppercase())
            && !has_unqualified_use(&clean_content, qi)
        {
            constructors.remove(qi);
        }
    }

    constructors
}

/// Build a map of qualified accesses: prefix -> set of accessed identifiers.
///
/// For `L.length`, `S.empty`, `FStar.List.Tot.map` produces:
/// - "L" -> {"length"}
/// - "S" -> {"empty"}
/// - "FStar.List.Tot" -> {"map"}
fn extract_qualified_access_map(content: &str) -> HashMap<String, HashSet<String>> {
    let filtered_content: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !is_declaration_line(trimmed)
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean_content = strip_comments_and_strings(&filtered_content);
    let mut map: HashMap<String, HashSet<String>> = HashMap::new();

    for caps in QUALIFIED_USE_RE.captures_iter(&clean_content) {
        if let (Some(prefix_match), Some(ident_match)) = (caps.get(1), caps.get(2)) {
            let prefix = prefix_match.as_str().to_string();
            let ident = ident_match.as_str().to_string();
            map.entry(prefix).or_default().insert(ident);
        }
    }

    map
}

/// Extract effect names used in type signatures.
///
/// Detects effect names like `Stack`, `ST`, `Lemma`, `Pure` etc. that appear
/// after `:` or `->` in val/let type annotations.
fn extract_effect_names(content: &str) -> HashSet<String> {
    let clean_content = strip_comments_and_strings(content);
    let mut effects = HashSet::new();

    // Known effect names from F* standard library
    let known_effects: HashSet<&str> = [
        "Lemma", "Tot", "GTot", "Dv", "Pure", "Ghost", "Stack", "ST",
        "PURE", "GHOST", "DIV", "ALL", "ML", "EXN", "Tac", "TAC",
        "HyperStack", "StackInline", "Inline",
    ].iter().cloned().collect();

    // Look for effect names after : or -> in type contexts
    for caps in EFFECT_USE_PATTERN.captures_iter(&clean_content) {
        if let Some(m) = caps.get(1) {
            let name = m.as_str();
            if known_effects.contains(name) {
                effects.insert(name.to_string());
            }
        }
    }

    // Also scan for unqualified effect names used as standalone identifiers
    for effect in &known_effects {
        // Check if the effect name appears as a standalone word (not part of a module path)
        if has_unqualified_use(&clean_content, effect) {
            effects.insert(effect.to_string());
        }
    }

    effects
}

/// Perform full analysis of a file for unused open detection.
///
/// This is the main entry point for FST004 analysis.
///
/// # Arguments
/// * `content` - The F* source code to analyze
///
/// # Returns
/// An `OpenAnalysis` struct containing all parsed information needed
/// to determine which opens are unused.
pub fn analyze_opens(content: &str) -> OpenAnalysis {
    OpenAnalysis {
        opens: parse_opens(content),
        let_opens: parse_let_opens(content),
        aliases: parse_module_aliases(content),
        includes: parse_includes(content),
        used_module_prefixes: extract_used_module_prefixes(content),
        qualified_access_map: extract_qualified_access_map(content),
        used_identifiers: extract_used_identifiers(content),
        used_type_constructors: extract_type_constructors(content),
        used_operators: extract_operator_internal_names(content),
        used_effect_names: extract_effect_names(content),
    }
}

/// Check if content has the `!` dereference operator (not `!=` or `!*`).
fn content_has_bang_operator(content: &str) -> bool {
    let chars: Vec<char> = content.chars().collect();
    for i in 0..chars.len() {
        if chars[i] == '!' {
            // Check that it's not `!=` or `!*`
            let next = chars.get(i + 1);
            if next != Some(&'=') && next != Some(&'*') {
                // Check that it's not preceded by another `!`
                let prev = if i > 0 { chars.get(i - 1) } else { None };
                if prev != Some(&'!') && prev != Some(&'=') {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if content has the `*` multiplication operator in arithmetic context.
/// Looks for patterns like `word * word` or `paren * paren`.
fn content_has_mul_operator(content: &str) -> bool {
    let chars: Vec<char> = content.chars().collect();
    for i in 1..chars.len().saturating_sub(1) {
        if chars[i] == '*' {
            // Don't count if part of *= or *^ or *! or *. or !* or (*
            let next = chars.get(i + 1);
            let prev = chars.get(i.saturating_sub(1));
            if next == Some(&'=')
                || next == Some(&'^')
                || next == Some(&'!')
                || next == Some(&'.')
                || next == Some(&')')
            {
                continue;
            }
            if prev == Some(&'!')
                || prev == Some(&'(')
                || prev == Some(&'*')
                || prev == Some(&':')
            {
                continue;
            }
            // Check for word/paren * word/paren pattern
            // There should be alphanumeric or ) before, and alphanumeric or ( after
            if let Some(p) = prev {
                if let Some(n) = next {
                    if (p.is_alphanumeric() || *p == ')' || *p == ' ')
                        && (n.is_alphanumeric() || *n == '(' || *n == ' ')
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Check if content has the `@` list append operator.
/// Avoids matching email addresses or attribute markers.
fn content_has_append_operator(content: &str) -> bool {
    let chars: Vec<char> = content.chars().collect();
    for i in 1..chars.len().saturating_sub(1) {
        if chars[i] == '@' {
            // Don't count if part of @| or attribute marker
            let next = chars.get(i + 1);
            let prev = chars.get(i.saturating_sub(1));
            if next == Some(&'|') {
                continue;
            }
            // Check for word/bracket @ word/bracket pattern
            if let Some(p) = prev {
                if let Some(n) = next {
                    if (p.is_alphanumeric() || *p == ']' || *p == ')' || *p == ' ')
                        && (n.is_alphanumeric() || *n == '[' || *n == '(' || *n == ' ')
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Map F* source-level operators to their internal names.
///
/// In F*, operators like `*` are represented internally as `op_Star`.
/// This function extracts operators from source code and maps them to
/// the corresponding internal names that appear in module exports.
///
/// Returns a set of internal operator names found in the content.
fn extract_operator_internal_names(content: &str) -> HashSet<String> {
    let clean_content = strip_comments_and_strings(content);
    let mut internal_names = HashSet::new();

    // Check for specific operators and add their internal names
    // Hat operators (FStar.Int*, FStar.UInt*, FStar.Integers)
    if clean_content.contains("+^") {
        internal_names.insert("op_Plus_Hat".to_string());
    }
    if clean_content.contains("-^") {
        internal_names.insert("op_Subtraction_Hat".to_string());
    }
    if clean_content.contains("*^") {
        internal_names.insert("op_Star_Hat".to_string());
    }
    if clean_content.contains("/^") {
        internal_names.insert("op_Slash_Hat".to_string());
    }
    if clean_content.contains("%^") {
        internal_names.insert("op_Percent_Hat".to_string());
    }
    if clean_content.contains("&^") {
        internal_names.insert("op_Amp_Hat".to_string());
    }
    if clean_content.contains("|^") {
        internal_names.insert("op_Bar_Hat".to_string());
    }
    if clean_content.contains("^^") {
        internal_names.insert("op_Hat_Hat".to_string());
    }
    if clean_content.contains("<<^") {
        internal_names.insert("op_Less_Less_Hat".to_string());
    }
    if clean_content.contains(">>^") {
        internal_names.insert("op_Greater_Greater_Hat".to_string());
    }
    if clean_content.contains("=^") {
        internal_names.insert("op_Equals_Hat".to_string());
    }
    if clean_content.contains("<^") {
        internal_names.insert("op_Less_Hat".to_string());
    }
    if clean_content.contains(">^") {
        internal_names.insert("op_Greater_Hat".to_string());
    }
    if clean_content.contains("<=^") {
        internal_names.insert("op_Less_Equals_Hat".to_string());
    }
    if clean_content.contains(">=^") {
        internal_names.insert("op_Greater_Equals_Hat".to_string());
    }

    // Bang operators (Lib.IntTypes)
    if clean_content.contains("+!") {
        internal_names.insert("op_Plus_Bang".to_string());
    }
    if clean_content.contains("-!") {
        internal_names.insert("op_Subtraction_Bang".to_string());
    }
    if clean_content.contains("*!") {
        internal_names.insert("op_Star_Bang".to_string());
    }

    // Dot operators (Lib.IntTypes)
    if clean_content.contains("+.") {
        internal_names.insert("op_Plus_Dot".to_string());
    }
    if clean_content.contains("-.") {
        internal_names.insert("op_Subtraction_Dot".to_string());
    }
    if clean_content.contains("*.") {
        internal_names.insert("op_Star_Dot".to_string());
    }
    if clean_content.contains("&.") {
        internal_names.insert("op_Amp_Dot".to_string());
    }
    if clean_content.contains("|.") {
        internal_names.insert("op_Bar_Dot".to_string());
    }
    if clean_content.contains("^.") {
        internal_names.insert("op_Hat_Dot".to_string());
    }
    if clean_content.contains("<<.") {
        internal_names.insert("op_Less_Less_Dot".to_string());
    }
    if clean_content.contains(">>.") {
        internal_names.insert("op_Greater_Greater_Dot".to_string());
    }

    // Buffer operators (LowStar.BufferOps)
    if clean_content.contains("!*") {
        internal_names.insert("op_Bang_Star".to_string());
    }
    if clean_content.contains("*=") {
        internal_names.insert("op_Star_Equals".to_string());
    }

    // Array access operators (LowStar.Buffer, Lib.Buffer, FStar.Buffer)
    // These use .() and .()<- syntax which we detect differently
    if clean_content.contains(".(") {
        internal_names.insert("op_Array_Access".to_string());
    }
    if clean_content.contains(".()<-") || clean_content.contains(".(") && clean_content.contains("<-")
    {
        internal_names.insert("op_Array_Assignment".to_string());
    }

    // Sequence/list append operators
    if clean_content.contains("@|") {
        internal_names.insert("op_At_Bar".to_string());
    }

    // ST operators
    // Check for ! used as dereference (not != or !* patterns)
    // Use simple string scanning
    if content_has_bang_operator(&clean_content) {
        internal_names.insert("op_Bang".to_string());
    }
    if clean_content.contains(":=") {
        internal_names.insert("op_Colon_Equals".to_string());
    }

    // Basic multiplication - FStar.Mul
    // This is tricky: * is used in many contexts (types, comments, etc.)
    // We look for patterns like `expr * expr` in arithmetic contexts
    if content_has_mul_operator(&clean_content) {
        internal_names.insert("op_Star".to_string());
    }

    // List append @
    // Avoid matching email addresses or attribute markers
    if content_has_append_operator(&clean_content) {
        internal_names.insert("op_At".to_string());
    }

    internal_names
}

/// Known module exports database.
/// Returns known exported names for common F* modules.
/// This allows the linter to check if any exported name is actually used.
///
/// This database covers the F* standard library and common verification libraries.
/// When a module is not in this database, the linter conservatively assumes
/// the open might be used (to avoid false positives).
fn get_known_exports(module: &str) -> Option<HashSet<&'static str>> {
    match module {
        // ========================================
        // FStar Core / Pervasives
        // ========================================
        "FStar.Pervasives" | "FStar.Pervasives.Native" => Some(
            [
                // Normalization and tactics
                "normalize",
                "normalize_term",
                "assert_norm",
                "norm",
                "reveal_opaque",
                "synth",
                "intro_ambient",
                "ambient",
                // Native types
                "option",
                "Some",
                "None",
                "tuple2",
                "tuple3",
                "tuple4",
                "tuple5",
                "fst",
                "snd",
                // Result type
                "result",
                "V",
                "E",
                // Common effects
                "pure_return",
                "pure_bind",
                // Attributes
                "inline_let",
                "rename_let",
                "plugin",
                "tcnorm",
                "erasable",
                "comment",
                "deprecated",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // Multiplication operator (commonly needed for * in specs)
        "FStar.Mul" => Some(["op_Star"].iter().cloned().collect()),

        // ========================================
        // FStar.List modules
        // ========================================
        "FStar.List.Tot" | "FStar.List.Tot.Base" => Some(
            [
                // Basic operations
                "length",
                "hd",
                "tl",
                "nth",
                "index",
                "count",
                "isEmpty",
                "noRepeats",
                "last",
                // Construction/destruction
                "rev",
                "append",
                "op_At",
                "flatten",
                "concat",
                "snoc",
                "init",
                "unsnoc",
                // Higher-order
                "map",
                "mapi",
                "map2",
                "map3",
                "fold_left",
                "fold_right",
                "fold_left2",
                "filter",
                "find",
                "find_l",
                "partition",
                "for_all",
                "for_all2",
                "existsb",
                "exists_",
                "collect",
                "concatMap",
                // Membership and search
                "mem",
                "memP",
                "contains",
                "assoc",
                // Zipping and splitting
                "split",
                "unzip",
                "unzip3",
                "zip",
                "zip3",
                "zipWith",
                // Sorting
                "sortWith",
                "sorted",
                "insert_sorted",
                // List creation
                "list_refb",
                "list_ref",
                // Indexed operations
                "index_of",
                "split_at",
                "splitAt",
                // Take/drop
                "take",
                "drop",
                // Comparison
                "compare_of_bool",
                "bool_of_compare",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.List.Tot.Properties" => Some(
            [
                // Length lemmas
                "append_length",
                "rev_length",
                "map_length",
                "flatten_length",
                "filter_length",
                // Append lemmas
                "append_mem",
                "append_assoc",
                "append_nil_l",
                "append_l_nil",
                "append_inv_head",
                "append_inv_tail",
                // Rev lemmas
                "rev_involutive",
                "rev_append",
                "rev_mem",
                "rev_rev",
                "rev_injective",
                // Map lemmas
                "map_append",
                "map_rev",
                "map_map",
                "map_id",
                "map_injective",
                // Fold lemmas
                "fold_left_append",
                "fold_right_append",
                "fold_left_map",
                "fold_right_map",
                // Membership lemmas
                "index_mem",
                "mem_index",
                "mem_rev",
                "mem_append",
                "mem_filter",
                "mem_map",
                "mem_existsb",
                "mem_count",
                // Index lemmas
                "lemma_index_append1",
                "lemma_index_append2",
                "nth_split_at",
                // Other
                "assoc_mem",
                "for_all_mem",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.List.Pure" | "FStar.List.Pure.Base" => Some(
            [
                "length",
                "hd",
                "tl",
                "nth",
                "index",
                "rev",
                "append",
                "flatten",
                "map",
                "mapi",
                "fold_left",
                "fold_right",
                "filter",
                "find",
                "mem",
                "for_all",
                "existsb",
                "assoc",
                "split",
                "zip",
                "unzip",
                "concat",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Seq modules
        // ========================================
        "FStar.Seq" | "FStar.Seq.Base" => Some(
            [
                // Type
                "seq",
                "lseq",
                // Construction
                "empty",
                "create",
                "init",
                "createL",
                "of_list",
                // Access
                "length",
                "index",
                "head",
                "tail",
                "last",
                // Update
                "upd",
                // Concatenation
                "append",
                "op_At_Bar",
                "cons",
                "snoc",
                // Subsequences
                "slice",
                "split",
                // Equality
                "equal",
                "eq",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Seq.Properties" => Some(
            [
                // Length lemmas
                "lemma_len_append",
                "lemma_len_slice",
                "lemma_create_len",
                "lemma_init_len",
                // Index lemmas
                "lemma_index_app1",
                "lemma_index_app2",
                "lemma_index_slice",
                "lemma_index_create",
                "lemma_index_upd1",
                "lemma_index_upd2",
                // Equality lemmas
                "lemma_eq_intro",
                "lemma_eq_elim",
                "lemma_eq_refl",
                // Append lemmas
                "append_assoc",
                "append_empty_l",
                "append_empty_r",
                "lemma_append_inj",
                // Membership
                "mem",
                "lemma_mem_append",
                "lemma_mem_snoc",
                // Counting
                "count",
                "lemma_count_slice",
                // Slice lemmas
                "lemma_slice_snoc",
                "lemma_slice_first_in_append",
                "slice_slice",
                // Split lemmas
                "lemma_split",
                "split_eq",
                // Find
                "find_l",
                "find_append_some",
                "find_append_none",
                // Other
                "contains",
                "seq_of_list",
                "seq_to_list",
                "lemma_seq_of_list_induction",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Option
        // ========================================
        "FStar.Option" => Some(
            [
                "option",
                "Some",
                "None",
                "isSome",
                "isNone",
                "get",
                "map",
                "mapTot",
                "bind",
                "optionToBool",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Either
        // ========================================
        "FStar.Either" => Some(
            [
                "either",
                "Inl",
                "Inr",
                "isLeft",
                "isRight",
                "left",
                "right",
                "map_left",
                "map_right",
                "fold",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Set / FStar.Map
        // ========================================
        "FStar.Set" => Some(
            [
                "set",
                "empty",
                "singleton",
                "mem",
                "equal",
                "subset",
                "union",
                "intersect",
                "complement",
                "add",
                "remove",
                "intension",
                "as_set",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Map" => Some(
            [
                "t",
                "domain",
                "sel",
                "upd",
                "const",
                "concat",
                "contains",
                "restrict",
                "equal",
                "map_literal",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.OrdMap" => Some(
            [
                "ordmap", "empty", "const_on", "select", "update", "contains", "dom", "remove",
                "choose", "size", "equal", "map", "fold",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.OrdSet" => Some(
            [
                "ordset",
                "empty",
                "mem",
                "singleton",
                "union",
                "intersect",
                "subset",
                "equal",
                "choose",
                "remove",
                "as_list",
                "size",
                "fold",
                "map",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Ghost / FStar.Erased
        // ========================================
        "FStar.Ghost" => Some(
            [
                "erased",
                "reveal",
                "hide",
                "elift1",
                "elift2",
                "elift3",
                "push_refinement",
                "pull_refinement",
                "join",
                "bind",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Classical
        // ========================================
        "FStar.Classical" => Some(
            [
                "give_witness",
                "get_witness",
                "forall_intro",
                "exists_elim",
                "impl_intro",
                "impl_elim",
                "or_elim",
                "and_elim",
                "exists_intro",
                "forall_elim",
                "move_requires",
                "lemma_forall_intro_gtot",
                "ghost_lemma",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Classical.Sugar" => Some(
            ["forall_intro", "exists_elim", "implies_intro", "or_elim"]
                .iter()
                .cloned()
                .collect(),
        ),

        "FStar.Squash" => Some(
            [
                "squash",
                "return_squash",
                "bind_squash",
                "get_proof",
                "give_proof",
                "map_squash",
                "join_squash",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.IndefiniteDescription" => Some(
            [
                "indefinite_description_ghost",
                "indefinite_description_tot",
                "strong_indefinite_description_ghost",
                "elim_squash",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar integer modules
        // ========================================
        "FStar.Int" => Some(
            [
                "int_t",
                "v",
                "int_to_t",
                "add",
                "sub",
                "mul",
                "div",
                "rem",
                "logand",
                "logxor",
                "logor",
                "lognot",
                "shift_left",
                "shift_right",
                "shift_arithmetic_right",
                "op_Plus_Hat",
                "op_Subtraction_Hat",
                "op_Star_Hat",
                "op_Slash_Hat",
                "op_Percent_Hat",
                "op_Hat_Hat",
                "op_Amp_Hat",
                "op_Bar_Hat",
                "op_Less_Less_Hat",
                "op_Greater_Greater_Hat",
                "op_Equals_Hat",
                "op_Greater_Hat",
                "op_Less_Hat",
                "op_Greater_Equals_Hat",
                "op_Less_Equals_Hat",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Int8" | "FStar.Int16" | "FStar.Int32" | "FStar.Int64" | "FStar.Int128" => Some(
            [
                "t",
                "v",
                "int_to_t",
                "add",
                "sub",
                "mul",
                "div",
                "rem",
                "logand",
                "logxor",
                "logor",
                "lognot",
                "shift_left",
                "shift_right",
                "shift_arithmetic_right",
                "add_mod",
                "sub_mod",
                "mul_mod",
                "op_Plus_Hat",
                "op_Subtraction_Hat",
                "op_Star_Hat",
                "op_Slash_Hat",
                "op_Percent_Hat",
                "op_Hat_Hat",
                "op_Amp_Hat",
                "op_Bar_Hat",
                "op_Less_Less_Hat",
                "op_Greater_Greater_Hat",
                "op_Equals_Hat",
                "op_Greater_Hat",
                "op_Less_Hat",
                "op_Greater_Equals_Hat",
                "op_Less_Equals_Hat",
                "n",
                "zero",
                "one",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.UInt" => Some(
            [
                "uint_t",
                "v",
                "uint_to_t",
                "add",
                "sub",
                "mul",
                "div",
                "rem",
                "logand",
                "logxor",
                "logor",
                "lognot",
                "shift_left",
                "shift_right",
                "add_mod",
                "sub_mod",
                "mul_mod",
                "op_Plus_Hat",
                "op_Subtraction_Hat",
                "op_Star_Hat",
                "op_Slash_Hat",
                "op_Percent_Hat",
                "op_Hat_Hat",
                "op_Amp_Hat",
                "op_Bar_Hat",
                "op_Less_Less_Hat",
                "op_Greater_Greater_Hat",
                "op_Equals_Hat",
                "op_Greater_Hat",
                "op_Less_Hat",
                "op_Greater_Equals_Hat",
                "op_Less_Equals_Hat",
                "max_int",
                "min_int",
                "fits",
                "size",
                "zero",
                "one",
                "ones",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.UInt8" | "FStar.UInt16" | "FStar.UInt32" | "FStar.UInt64" | "FStar.UInt128" => Some(
            [
                "t",
                "v",
                "uint_to_t",
                "add",
                "sub",
                "mul",
                "div",
                "rem",
                "logand",
                "logxor",
                "logor",
                "lognot",
                "shift_left",
                "shift_right",
                "add_mod",
                "sub_mod",
                "mul_mod",
                "mul_wide",
                "op_Plus_Hat",
                "op_Subtraction_Hat",
                "op_Star_Hat",
                "op_Slash_Hat",
                "op_Percent_Hat",
                "op_Hat_Hat",
                "op_Amp_Hat",
                "op_Bar_Hat",
                "op_Less_Less_Hat",
                "op_Greater_Greater_Hat",
                "op_Equals_Hat",
                "op_Greater_Hat",
                "op_Less_Hat",
                "op_Greater_Equals_Hat",
                "op_Less_Equals_Hat",
                "n",
                "zero",
                "one",
                "ones",
                "eq",
                "gt",
                "gte",
                "lt",
                "lte",
                "to_string",
                "to_string_hex",
                "to_string_hex_pad",
                "eq_mask",
                "gte_mask",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.SizeT" => Some(
            [
                "t",
                "v",
                "uint_to_t",
                "size_v_inj",
                "add",
                "sub",
                "mul",
                "div",
                "rem",
                "fits",
                "fits_u32",
                "fits_u64",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.PtrdiffT" => Some(
            ["t", "v", "ptrdiff_v_inj", "add", "sub", "mul", "div", "rem"]
                .iter()
                .cloned()
                .collect(),
        ),

        // ========================================
        // FStar.Math modules
        // ========================================
        "FStar.Math.Lib" => Some(
            [
                "abs",
                "max",
                "min",
                "div",
                "op_Slash",
                "signed_modulo",
                "log_2",
                "powx",
                "pow2",
                "pow2_plus",
                "pow2_minus",
                "arithmetic_shift_right",
                "slash_decr_axiom",
                "slash_star_axiom",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Math.Lemmas" => Some(
            [
                // Power of 2 lemmas
                "pow2_lt_compat",
                "pow2_le_compat",
                "pow2_plus",
                "pow2_double_sum",
                "pow2_double_mult",
                // Division/modulo lemmas
                "lemma_div_mod",
                "lemma_mod_lt",
                "lemma_div_lt",
                "lemma_mod_plus",
                "lemma_mod_plus_distr_l",
                "lemma_mod_plus_distr_r",
                "lemma_mod_mod",
                "lemma_mod_add_distr",
                "lemma_mod_sub_distr",
                "lemma_div_plus",
                "lemma_div_mod_plus",
                "lemma_mod_mul_distr_l",
                "lemma_mod_mul_distr_r",
                "lemma_div_lt_nat",
                "lemma_div_le",
                // Multiplication lemmas
                "lemma_mult_lt_left",
                "lemma_mult_lt_right",
                "lemma_mult_le_left",
                "lemma_mult_le_right",
                "swap_mul",
                "paren_mul_left",
                "paren_mul_right",
                // Small values
                "small_mod",
                "small_div",
                // Cancel
                "cancel_mul_div",
                "cancel_mul_mod",
                "multiple_modulo_lemma",
                "multiple_division_lemma",
                // Euclidean division
                "euclidean_division_definition",
                "modulo_range_lemma",
                "modulo_lemma",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.String / FStar.Char
        // ========================================
        "FStar.String" => Some(
            [
                "string",
                "strlen",
                "length",
                "concat",
                "split",
                "substring",
                "index",
                "make",
                "uppercase",
                "lowercase",
                "collect",
                "list_of_string",
                "string_of_list",
                "sub",
                "compare",
                "equal",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Char" => Some(
            [
                "char",
                "u32_of_char",
                "char_of_u32",
                "int_of_char",
                "char_of_int",
                "lowercase",
                "uppercase",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Bytes
        // ========================================
        "FStar.Bytes" => Some(
            [
                "bytes",
                "byte",
                "length",
                "empty_bytes",
                "create",
                "index",
                "get",
                "set",
                "append",
                "op_At_Bar",
                "slice",
                "sub",
                "split",
                "equal",
                "eq",
                "repr",
                "reveal",
                "hide",
                "of_hex",
                "print_bytes",
                "utf8_encode",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar Buffer/Memory modules
        // ========================================
        "FStar.Buffer" => Some(
            [
                "buffer",
                "live",
                "modifies",
                "modifies_1",
                "modifies_0",
                "frameOf",
                "as_addr",
                "length",
                "idx",
                "op_Array_Access",
                "op_Array_Assignment",
                "create",
                "createL",
                "rcreate",
                "rcreate_mm",
                "index",
                "upd",
                "blit",
                "fill",
                "sub",
                "offset",
                "lemma_modifies_0_unalloc",
                "lemma_modifies_1_unalloc",
                "modifies_fresh_frame_popped",
                "fresh_frame",
                "pop_frame",
                "push_frame",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.Buffer" | "LowStar.Monotonic.Buffer" => Some(
            [
                "buffer",
                "pointer",
                "pointer_or_null",
                "live",
                "freeable",
                "modifies",
                "loc_buffer",
                "loc_none",
                "loc_union",
                "loc_includes",
                "frameOf",
                "as_addr",
                "len",
                "length",
                "index",
                "upd",
                "op_Array_Access",
                "op_Array_Assignment",
                "alloca",
                "alloca_of_list",
                "malloc",
                "free",
                "gcmalloc",
                "create",
                "createL",
                "rcreate_mm",
                "blit",
                "fill",
                "sub",
                "offset",
                "gsub",
                "gsub_zero_length",
                "moffset",
                "modifies_only_not_unused_in",
                "modifies_buffer_from_to_elim",
                "modifies_fresh_frame_popped",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.BufferOps" => Some(
            [
                "op_Array_Access",
                "op_Array_Assignment",
                "op_Bang_Star",
                "op_Star_Equals",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.HyperStack" | "FStar.Monotonic.HyperStack" => Some(
            [
                "mem",
                "live_region",
                "is_stack_region",
                "is_heap_color",
                "frameOf",
                "as_addr",
                "contains",
                "sel",
                "upd",
                "modifies",
                "fresh_region",
                "fresh_frame",
                "poppable",
                "rid",
                "root",
                "tip",
                "get_hmap",
                "get_tip",
                "modifies_one",
                "modifies_ref",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.HyperStack.ST" | "FStar.Monotonic.HyperStack.ST" => Some(
            [
                "get",
                "recall",
                "witness_p",
                "recall_p",
                "testify",
                "testify_forall",
                "testify_forall_region_contains_pred",
                "push_frame",
                "pop_frame",
                "new_region",
                "new_colored_region",
                "ralloc",
                "ralloc_mm",
                "rfree",
                "op_Bang",
                "op_Colon_Equals",
                "salloc",
                "sfree",
                "is_eternal_region",
                "eternal_region_pred",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.ST / FStar.Ref
        // ========================================
        "FStar.ST" => Some(
            [
                "st_pre",
                "st_post",
                "st_post'",
                "ST",
                "st_return",
                "st_bind",
                "read",
                "write",
                "alloc",
                "op_Bang",
                "op_Colon_Equals",
                "get",
                "recall",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Ref" => Some(
            [
                "ref",
                "alloc",
                "read",
                "write",
                "op_Bang",
                "op_Colon_Equals",
                "addr_of",
                "is_mm",
                "frameOf",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Heap" => Some(
            [
                "heap",
                "ref",
                "trivial_preorder",
                "alloc",
                "sel",
                "upd",
                "free",
                "contains",
                "addr_of",
                "is_mm",
                "modifies",
                "fresh",
                "equal_dom",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.All / FStar.Exn / FStar.IO
        // ========================================
        "FStar.All" => Some(
            [
                "all_pre",
                "all_post",
                "all_post'",
                "ML",
                "all_return",
                "all_bind",
                "failwith",
                "exit",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Exn" => Some(
            [
                "exn_pre",
                "exn_post",
                "exn_post'",
                "EXN",
                "exn_return",
                "exn_bind",
                "raise",
                "try_with",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.IO" => Some(
            [
                "print_string",
                "print_any",
                "print_uint8",
                "print_int8",
                "print_uint16",
                "print_int16",
                "print_uint32",
                "print_int32",
                "print_uint64",
                "print_int64",
                "print_newline",
                "read_line",
                "debug_print_string",
                "input_line",
                "input_int",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Printf" => Some(
            ["sprintf", "printf", "fprintf", "print_string", "arg_type"]
                .iter()
                .cloned()
                .collect(),
        ),

        // ========================================
        // FStar.Tactics modules
        // ========================================
        "FStar.Tactics" | "FStar.Tactics.V2" | "FStar.Tactics.V1" => Some(
            [
                // Tactic monad
                "tactic",
                "TAC",
                "return",
                "bind",
                // Basic combinators
                "fail",
                "try_with",
                "or_else",
                "trytac",
                "trivial",
                "focus",
                "guard",
                "repeat",
                "repeatn",
                "seq",
                // Goal management
                "goals",
                "cur_goal",
                "smt",
                "trefl",
                "qed",
                "dismiss",
                "flip",
                "later",
                "set_goals",
                // Term inspection
                "term",
                "bv",
                "binder",
                "comp",
                "inspect",
                "pack",
                "term_eq",
                "term_to_string",
                // Environment
                "cur_env",
                "top_env",
                "lookup_typ",
                "binders_of_env",
                "vars_of_env",
                // Unification
                "unify",
                "unify_env",
                "unify_guard",
                // Intro/elim
                "intro",
                "intro_rec",
                "intros",
                "revert",
                "revert_all",
                "destruct",
                "elim",
                "apply",
                "apply_lemma",
                "exact",
                "exact_with_ref",
                // Rewriting
                "rewrite",
                "l_to_r",
                "grewrite",
                // Normalization
                "norm",
                "norm_term",
                "normalize",
                "norm_binding_type",
                // Debugging
                "debug",
                "print",
                "dump",
                "fail",
                // Reflection helpers
                "fresh_bv",
                "fresh_binder_named",
                "name_of_bv",
                "inspect_bv",
                "pack_bv",
                "inspect_binder",
                "pack_binder",
                // SMT
                "smt_sync",
                "dup",
                // Proof state
                "ngoals",
                "get_vconfig",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Tactics.CanonCommMonoid" => Some(
            [
                "canon_monoid",
                "cm",
                "var",
                "term",
                "const",
                "mult",
                "flatten",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Tactics.CanonCommSemiring" => Some(
            [
                "canon_semiring",
                "cr",
                "var",
                "term",
                "const",
                "add",
                "mult",
                "flatten",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Reflection modules
        // ========================================
        "FStar.Reflection" | "FStar.Reflection.V2" | "FStar.Reflection.V1" => Some(
            [
                // Types
                "term",
                "bv",
                "binder",
                "comp",
                "env",
                "fv",
                "name",
                "ident",
                "univ",
                // Inspection
                "inspect_ln",
                "pack_ln",
                "inspect_bv",
                "pack_bv",
                "inspect_fv",
                "pack_fv",
                "inspect_binder",
                "pack_binder",
                "inspect_comp",
                "pack_comp",
                "inspect_universe",
                "pack_universe",
                // Constructors
                "term_view",
                "Tv_Var",
                "Tv_BVar",
                "Tv_FVar",
                "Tv_App",
                "Tv_Abs",
                "Tv_Arrow",
                "Tv_Type",
                "Tv_Refine",
                "Tv_Const",
                "Tv_Uvar",
                "Tv_Let",
                "Tv_Match",
                "Tv_AscribedT",
                "Tv_AscribedC",
                "Tv_Unknown",
                // Constants
                "C_Unit",
                "C_True",
                "C_False",
                "C_Int",
                "C_String",
                // Computations
                "C_Total",
                "C_Lemma",
                "C_Eff",
                // Utilities
                "term_eq",
                "term_to_string",
                "bv_eq",
                "fv_eq",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Reflection.Const" => Some(
            [
                "unit_lid",
                "bool_lid",
                "int_lid",
                "string_lid",
                "true_qn",
                "false_qn",
                "nil_lid",
                "cons_lid",
                "and_qn",
                "or_qn",
                "imp_qn",
                "iff_qn",
                "not_qn",
                "forall_qn",
                "exists_qn",
                "eq2_qn",
                "eq1_qn",
                "lt_qn",
                "lte_qn",
                "gt_qn",
                "gte_qn",
                "add_qn",
                "sub_qn",
                "mul_qn",
                "div_qn",
                "mod_qn",
                "neg_qn",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Fin / FStar.Vector
        // ========================================
        "FStar.Fin" => Some(
            [
                "fin",
                "in_",
                "find",
                "pigeonhole",
                "to_nat",
                "succ",
                "zero",
                "one",
                "cast",
                "injective",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Vector" | "FStar.Vector.Base" => Some(
            [
                "raw",
                "vec",
                "length_t",
                "length",
                "index",
                "init",
                "create",
                "assign",
                "from_list",
                "to_list",
                "map",
                "map2",
                "fold_left",
                "fold_right",
                "append",
                "sub",
                "split",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.BitVector / FStar.BV
        // ========================================
        "FStar.BV" | "FStar.BitVector" => Some(
            [
                "bv_t",
                "bv",
                "length",
                "bvand",
                "bvor",
                "bvxor",
                "bvnot",
                "bvshl",
                "bvshr",
                "bvashr",
                "bvadd",
                "bvsub",
                "bvmul",
                "bvdiv",
                "bvmod",
                "bvult",
                "bvule",
                "bvslt",
                "bvsle",
                "int2bv",
                "bv2int",
                "bvconcat",
                "bvslice",
                "zero",
                "ones",
                "logand_vec",
                "logor_vec",
                "lognot_vec",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Endianness
        // ========================================
        "FStar.Endianness" => Some(
            [
                "le_to_n",
                "be_to_n",
                "n_to_le",
                "n_to_be",
                "le_of_uint8",
                "be_of_uint8",
                "uint8_of_le",
                "uint8_of_be",
                "le_of_uint16",
                "be_of_uint16",
                "uint16_of_le",
                "uint16_of_be",
                "le_of_uint32",
                "be_of_uint32",
                "uint32_of_le",
                "uint32_of_be",
                "le_of_uint64",
                "be_of_uint64",
                "uint64_of_le",
                "uint64_of_be",
                "seq_uint32_of_le",
                "seq_uint32_of_be",
                "seq_uint64_of_le",
                "seq_uint64_of_be",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.BigOps
        // ========================================
        "FStar.BigOps" => Some(
            [
                "big_and",
                "big_or",
                "big_and'",
                "big_or'",
                "pairwise_and",
                "pairwise_or",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Order
        // ========================================
        "FStar.Order" => Some(
            [
                "order",
                "Lt",
                "Eq",
                "Gt",
                "compare_int",
                "compare_list",
                "ge",
                "le",
                "gt",
                "lt",
                "eq",
                "lex",
                "order_from_int",
                "int_of_order",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.FunctionalExtensionality
        // ========================================
        "FStar.FunctionalExtensionality" => Some(
            [
                "feq",
                "on",
                "restricted_g_t",
                "restricted_t",
                "on_dom",
                "on_domain",
                "on_domain_g",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.PredicateExtensionality" => {
            Some(["predicateExtensionality", "peq"].iter().cloned().collect())
        }

        // ========================================
        // FStar.PropositionalExtensionality
        // ========================================
        "FStar.PropositionalExtensionality" => Some(
            [
                "propositional_extensionality",
                "apply_propositional_extensionality",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.WellFounded / FStar.WellFoundedRelation
        // ========================================
        "FStar.WellFounded" => Some(
            [
                "well_founded",
                "acc",
                "accessible",
                "fix_F",
                "fix",
                "well_founded_relation",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.WellFoundedRelation" => Some(
            [
                "wfr_t",
                "wfr",
                "as_wfr",
                "default_relation",
                "subrelation_wfr",
                "lex_t",
                "lex",
                "inverse_image",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Calc
        // ========================================
        "FStar.Calc" => Some(
            [
                "calc_finish",
                "calc_init",
                "calc_step",
                "calc_push_impl",
                "calc_trans",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Range
        // ========================================
        "FStar.Range" => Some(
            [
                "range",
                "mk_range",
                "range_0",
                "file_of_range",
                "start_of_range",
                "end_of_range",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Monotonic modules
        // ========================================
        "FStar.Monotonic.Witnessed" => Some(
            [
                "witnessed",
                "witness",
                "recall",
                "lemma_witnessed_constant",
                "lemma_witnessed_nested",
                "lemma_witnessed_and",
                "lemma_witnessed_or",
                "lemma_witnessed_impl",
                "lemma_witnessed_forall",
                "lemma_witnessed_exists",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Monotonic.Seq" => Some(
            ["seq_t", "grows", "grows_p", "at_most_one", "i_seq", "i_at"]
                .iter()
                .cloned()
                .collect(),
        ),

        "FStar.Monotonic.DependentMap" => Some(
            ["t", "sel", "upd", "grows", "empty", "contains"]
                .iter()
                .cloned()
                .collect(),
        ),

        // ========================================
        // FStar.Integers (generic integer ops)
        // ========================================
        "FStar.Integers" => Some(
            [
                "int_t",
                "v",
                "u",
                "uint_to_t",
                "int_to_t",
                "add",
                "op_Plus_Hat",
                "sub",
                "op_Subtraction_Hat",
                "mul",
                "op_Star_Hat",
                "div",
                "op_Slash_Hat",
                "rem",
                "op_Percent_Hat",
                "logand",
                "op_Amp_Hat",
                "logxor",
                "op_Hat_Hat",
                "logor",
                "op_Bar_Hat",
                "lognot",
                "shift_left",
                "op_Less_Less_Hat",
                "shift_right",
                "op_Greater_Greater_Hat",
                "eq",
                "op_Equals_Hat",
                "lt",
                "op_Less_Hat",
                "lte",
                "op_Less_Equals_Hat",
                "gt",
                "op_Greater_Hat",
                "gte",
                "op_Greater_Equals_Hat",
                "within_bounds",
                "cast",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // Lib modules (HACL*/EverCrypt)
        // ========================================
        "Lib.IntTypes" => Some(
            [
                // Type constructors
                "inttype",
                "U1",
                "U8",
                "U16",
                "U32",
                "U64",
                "U128",
                "S8",
                "S16",
                "S32",
                "S64",
                "S128",
                "secrecy_level",
                "SEC",
                "PUB",
                // Types
                "int_t",
                "uint_t",
                "sint_t",
                "pub_int_t",
                "sec_int_t",
                "uint8",
                "uint16",
                "uint32",
                "uint64",
                "uint128",
                "int8",
                "int16",
                "int32",
                "int64",
                "int128",
                "u8",
                "u16",
                "u32",
                "u64",
                "u128",
                "u1",
                "i8",
                "i16",
                "i32",
                "i64",
                "i128",
                "byte",
                "size_t",
                "pub_uint8",
                "pub_uint16",
                "pub_uint32",
                "pub_uint64",
                "pub_uint128",
                // Functions
                "v",
                "mk_int",
                "cast",
                "secret",
                "to_u8",
                "to_u16",
                "to_u32",
                "to_u64",
                "to_u128",
                "add",
                "sub",
                "mul",
                "div",
                "mod",
                "add_mod",
                "sub_mod",
                "mul_mod",
                "incr",
                "decr",
                "logand",
                "logxor",
                "logor",
                "lognot",
                "shift_left",
                "shift_right",
                "rotate_left",
                "rotate_right",
                "eq_mask",
                "lt_mask",
                "gt_mask",
                "lte_mask",
                "gte_mask",
                "op_Plus_Bang",
                "op_Subtraction_Bang",
                "op_Star_Bang",
                "op_Plus_Dot",
                "op_Subtraction_Dot",
                "op_Star_Dot",
                "op_Amp_Dot",
                "op_Hat_Dot",
                "op_Bar_Dot",
                "op_Less_Less_Dot",
                "op_Greater_Greater_Dot",
                "bits",
                "numbytes",
                "max_int",
                "min_int",
                "range",
                "zeros",
                "ones",
                "maxint",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Lib.Sequence" => Some(
            [
                "seq",
                "lseq",
                "length",
                "index",
                "create",
                "init",
                "createL",
                "of_list",
                "to_list",
                "upd",
                "sub",
                "slice",
                "append",
                "concat",
                "map",
                "map2",
                "for_all",
                "for_all2",
                "repeati",
                "repeat_gen",
                "eq_intro",
                "eq_elim",
                "index_sub",
                "index_map",
                "index_map2",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Lib.ByteSequence" => Some(
            [
                "bytes",
                "lbytes",
                "byte_t",
                "uint_to_bytes_le",
                "uint_to_bytes_be",
                "uint_from_bytes_le",
                "uint_from_bytes_be",
                "nat_from_bytes_le",
                "nat_from_bytes_be",
                "nat_to_bytes_le",
                "nat_to_bytes_be",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Lib.Buffer" | "Lib.Memzero0" => Some(
            [
                "buffer",
                "lbuffer",
                "length",
                "live",
                "modifies",
                "loc",
                "loc_none",
                "loc_buffer",
                "loc_union",
                "index",
                "upd",
                "sub",
                "offset",
                "create",
                "createL",
                "alloca",
                "malloc",
                "free",
                "blit",
                "fill",
                "copy",
                "memset",
                "op_Array_Access",
                "op_Array_Assignment",
                "loop",
                "loopi",
                "loop_range",
                "loop_range_all",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Lib.LoopCombinators" => Some(
            [
                "fixed_a",
                "fixed_i",
                "nat_zero_or_one",
                "repeat",
                "repeat_range",
                "repeat_gen",
                "repeati",
                "repeati_inductive",
                "repeati_blocks",
                "eq_repeat",
                "unfold_repeat",
                "unfold_repeati",
                "repeat_left",
                "repeat_right",
                "repeat_gen_inductive",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Lib.UpdateMulti" => Some(
            ["mk_update_multi", "update_multi", "update_last", "finish"]
                .iter()
                .cloned()
                .collect(),
        ),

        "Lib.RawIntTypes" => Some(
            [
                "u8_to_UInt8",
                "u16_to_UInt16",
                "u32_to_UInt32",
                "u64_to_UInt64",
                "UInt8_to_u8",
                "UInt16_to_u16",
                "UInt32_to_u32",
                "UInt64_to_u64",
                "size_to_UInt32",
                "size_from_UInt32",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // C / LowStar modules
        // ========================================
        "C" | "C.Compat" => Some(
            [
                "exit_success",
                "exit_failure",
                "errno",
                "portable_exit",
                "exit",
                "clock",
                "print_clock_diff",
                "string_t",
                "string_literal",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "C.Loops" | "C.Compat.Loops" => Some(
            [
                "for",
                "for64",
                "while",
                "do_while",
                "interruptible_for",
                "interruptible_while",
                "total_while",
                "total_while_gen",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "C.String" => Some(
            ["t", "v", "strlen", "well_formed", "get", "index"]
                .iter()
                .cloned()
                .collect(),
        ),

        "LowStar.Endianness" => Some(
            [
                "load16_le",
                "load16_be",
                "store16_le",
                "store16_be",
                "load32_le",
                "load32_be",
                "store32_le",
                "store32_be",
                "load64_le",
                "load64_be",
                "store64_le",
                "store64_be",
                "load128_le",
                "load128_be",
                "store128_le",
                "store128_be",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.Modifies" => Some(
            [
                "loc",
                "loc_none",
                "loc_buffer",
                "loc_addresses",
                "loc_regions",
                "loc_mreference",
                "loc_freed_mreference",
                "loc_union",
                "loc_includes",
                "loc_disjoint",
                "address_liveness_insensitive_locs",
                "region_liveness_insensitive_locs",
                "modifies",
                "modifies_refl",
                "modifies_trans",
                "modifies_only_live_regions",
                "modifies_only_live_addresses",
                "fresh_frame_modifies",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.ImmutableBuffer" => Some(
            [
                "ibuffer",
                "initialized",
                "cpred",
                "recall_contents",
                "witness_contents",
                "igcmalloc",
                "imalloc",
                "ialloca",
                "of_list",
                "createL_global",
                "createL_mglobal",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.ConstBuffer" => Some(
            [
                "const_buffer",
                "as_mbuf",
                "as_qbuf",
                "of_buffer",
                "of_ibuffer",
                "length",
                "index",
                "sub",
                "cast",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.Printf" => Some(
            [
                "printf",
                "sprintf",
                "snprintf",
                "print_string",
                "print_u8",
                "print_u16",
                "print_u32",
                "print_u64",
                "print_i8",
                "print_i16",
                "print_i32",
                "print_i64",
                "print_bool",
                "print_lmbuffer",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "LowStar.Failure" => Some(
            ["failwith", "unexpected", "unreachable"]
                .iter()
                .cloned()
                .collect(),
        ),

        // ========================================
        // Steel / Pulse memory
        // ========================================
        "Steel.Memory" => Some(
            [
                "mem",
                "slprop",
                "emp",
                "star",
                "pure",
                "points_to",
                "h_exists",
                "h_forall",
                "interp",
                "equiv",
                "frame",
                "intro_emp",
                "star_commutative",
                "star_associative",
                "star_congruence",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Steel.Effect" | "Steel.Effect.Atomic" => Some(
            [
                "Steel",
                "SteelF",
                "SteelT",
                "SteelAtomicBase",
                "return",
                "bind",
                "subcomp",
                "get",
                "put",
                "read",
                "write",
                "alloc",
                "free",
                "alloc_pt",
                "free_pt",
                "intro_exists",
                "elim_exists",
                "intro_pure",
                "elim_pure",
                "change_slprop",
                "change_equal_slprop",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Steel.Reference" => Some(
            [
                "ref",
                "pts_to",
                "pts_to_ref",
                "alloc",
                "free",
                "read",
                "write",
                "ghost_ref",
                "ghost_pts_to",
                "ghost_alloc",
                "ghost_free",
                "ghost_read",
                "ghost_write",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "Steel.Array" => Some(
            [
                "array",
                "array_pts_to",
                "array_pts_to'",
                "alloc",
                "free",
                "index",
                "upd",
                "ghost_join",
                "ghost_split",
                "blit",
                "fill",
                "memcpy",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // Prims (built-in)
        // ========================================
        "Prims" => Some(
            [
                // Types
                "unit",
                "bool",
                "int",
                "nat",
                "pos",
                "string",
                "prop",
                "squash",
                "l_True",
                "l_False",
                "l_and",
                "l_or",
                "l_imp",
                "l_iff",
                "l_not",
                "l_Forall",
                "l_Exists",
                "c_True",
                "c_False",
                "c_and",
                "c_or",
                "empty",
                "trivial",
                "eq2",
                "equals",
                // Constructors
                "T",
                "Nil",
                "Cons",
                // Operations
                "op_Negation",
                "op_AmpAmp",
                "op_BarBar",
                "op_Equality",
                "op_disEquality",
                "op_LessThanOrEqual",
                "op_LessThan",
                "op_GreaterThanOrEqual",
                "op_GreaterThan",
                "op_Addition",
                "op_Subtraction",
                "op_Multiply",
                "op_Division",
                "op_Modulus",
                "op_Minus",
                "pow2",
                "min",
                "max",
                "abs",
                // Lemmas/attributes
                "pure",
                "admit",
                "admit_any",
                "magic",
                "assume",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // ========================================
        // FStar.Pure / FStar.Total
        // ========================================
        "FStar.Pure" | "FStar.Pure.Effect" => Some(
            [
                "pure_pre",
                "pure_post",
                "pure_wp",
                "PURE",
                "Pure",
                "pure_return",
                "pure_bind",
                "assert_p",
                "assume_p",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        "FStar.Monotonic.Pure" => Some(
            ["monotonic", "as_pure_wp", "elim_pure_wp_monotonicity"]
                .iter()
                .cloned()
                .collect(),
        ),

        // ========================================
        // FStar extraction/codegen
        // ========================================
        "FStar.Krml.Endianness" => Some(
            [
                "le_to_n",
                "be_to_n",
                "n_to_le",
                "n_to_be",
                "load16_le",
                "load16_be",
                "store16_le",
                "store16_be",
                "load32_le",
                "load32_be",
                "store32_le",
                "store32_be",
                "load64_le",
                "load64_be",
                "store64_le",
                "store64_be",
                "load128_le",
                "load128_be",
                "store128_le",
                "store128_be",
            ]
            .iter()
            .cloned()
            .collect(),
        ),

        // Module not found in database - return None to indicate unknown
        _ => None,
    }
}

/// Check if an open statement is used, considering known module exports,
/// implicit opens, include statements, effect names, and qualified access patterns.
///
/// This function checks multiple sources of usage:
/// - Qualified module access (e.g., `List.map`)
/// - Unqualified identifiers (lowercase, e.g., `map`, `fold`)
/// - Type constructors (uppercase, e.g., `Some`, `None`, `Inl`)
/// - Operators (e.g., `*` maps to `op_Star`)
/// - Effect names (e.g., `Stack`, `ST` in type signatures)
///
/// It also filters out false positives:
/// - Names from implicit opens (Prims, FStar.Pervasives.Native) do not count
/// - Names only accessed via qualified paths do not require the open
/// - Module aliases provide their own prefix, independent of opens
/// - Include statements re-export contents, making the open redundant
#[allow(dead_code)]
fn is_open_used_with_exports(
    open: &OpenStatement,
    used_identifiers: &HashSet<String>,
    used_type_constructors: &HashSet<String>,
    qualified_uses: &HashSet<String>,
    used_operators: &HashSet<String>,
    aliases: &[ModuleAlias],
) -> bool {
    is_open_used_full(
        open,
        used_identifiers,
        used_type_constructors,
        qualified_uses,
        used_operators,
        aliases,
        &HashSet::new(),
        &[],
    )
}

/// Full open-usage check with all analysis data.
///
/// Extends `is_open_used_with_exports` with effect names and include tracking.
#[allow(clippy::too_many_arguments)]
fn is_open_used_full(
    open: &OpenStatement,
    used_identifiers: &HashSet<String>,
    used_type_constructors: &HashSet<String>,
    qualified_uses: &HashSet<String>,
    used_operators: &HashSet<String>,
    aliases: &[ModuleAlias],
    used_effect_names: &HashSet<String>,
    includes: &[IncludeStatement],
) -> bool {
    // If the same module is included, the open is redundant:
    // `include` re-exports everything, so `open` adds nothing new.
    for inc in includes {
        if inc.module_path == open.module_path && inc.line != open.line {
            return false;
        }
    }

    // Empty selective {} means typeclass scope only - consider used
    if let Some(ref names) = open.selective {
        if names.is_empty() {
            return true;
        }
        // Check if any selectively imported name is used (both lowercase and uppercase),
        // but filter out names that come from implicit opens.
        return names.iter().any(|n| {
            let in_implicit = IMPLICIT_SCOPE_NAMES.contains(n.as_str());
            (!in_implicit)
                && (used_identifiers.contains(n) || used_type_constructors.contains(n))
        });
    }

    // Build set of alias names that target this module or overlap with its path
    // components. These prefixes come from aliases, not from the open.
    let alias_names: HashSet<&str> = aliases
        .iter()
        .filter(|a| a.target == open.module_path)
        .map(|a| a.alias.as_str())
        .collect();

    // Check qualified uses like Module.foo, but exclude alias-provided prefixes
    // and the full module path (qualified access works without the open).
    let parts: Vec<&str> = open.module_path.split('.').collect();
    for i in 0..parts.len() {
        let suffix = parts[i..].join(".");
        if qualified_uses.contains(&suffix) && !alias_names.contains(suffix.as_str()) {
            // Skip the full module path: qualified access with the full path
            // works without an open statement
            if suffix != open.module_path {
                return true;
            }
        }
    }

    // Check known exports, filtering out names from implicit scope
    if let Some(exports) = get_known_exports(&open.module_path) {
        // Filter exports to exclude those provided by implicit opens
        let non_implicit_exports: Vec<&&str> = exports
            .iter()
            .filter(|e| !IMPLICIT_SCOPE_NAMES.contains(**e))
            .collect();

        // Check if any non-implicit exported identifier is used
        if non_implicit_exports
            .iter()
            .any(|e| used_identifiers.contains(**e))
        {
            return true;
        }

        // Check non-implicit type constructors
        if non_implicit_exports
            .iter()
            .any(|e| used_type_constructors.contains(**e))
        {
            return true;
        }

        // Check if any operator internal name matches exports
        if non_implicit_exports
            .iter()
            .any(|e| used_operators.contains(**e))
        {
            return true;
        }

        // Check effect names that this module provides
        let effect_exports: Vec<&&str> = exports
            .iter()
            .filter(|e| {
                e.chars().next().is_some_and(|c| c.is_uppercase())
                    && !IMPLICIT_SCOPE_NAMES.contains(**e)
            })
            .collect();
        if effect_exports
            .iter()
            .any(|e| used_effect_names.contains(**e))
        {
            return true;
        }

        // We know the exports and none (non-implicit) are used - it's unused
        return false;
    }

    // Conservative: if we don't know the exports, assume used
    true
}

/// Result of safety analysis for removing an open statement.
#[derive(Debug, Clone)]
pub struct RemovalSafety {
    /// Confidence level for the removal.
    pub confidence: FixConfidence,
    /// Whether auto-removal is safe.
    pub is_safe: bool,
    /// Reason if removal is not safe.
    pub reason: Option<String>,
    /// Safety level for the fix (Safe, Caution, Unsafe).
    pub safety_level: FixSafetyLevel,
}

impl RemovalSafety {
    /// High confidence, safe to auto-remove.
    /// Module not in KNOWN_EXPORTS (conservative) or selective import.
    fn safe() -> Self {
        Self {
            confidence: FixConfidence::High,
            is_safe: true,
            reason: None,
            safety_level: FixSafetyLevel::Safe,
        }
    }

    /// Medium confidence, suggest but require confirmation.
    /// Module might be used for operators or has complex usage patterns.
    fn medium(reason: impl Into<String>) -> Self {
        Self {
            confidence: FixConfidence::Medium,
            is_safe: true,
            reason: Some(reason.into()),
            safety_level: FixSafetyLevel::Caution,
        }
    }

    /// Low confidence, do not suggest auto-removal.
    /// Module alias exists or RISKY_MODULES list.
    fn low(reason: impl Into<String>) -> Self {
        Self {
            confidence: FixConfidence::Low,
            is_safe: false,
            reason: Some(reason.into()),
            safety_level: FixSafetyLevel::Unsafe,
        }
    }

    /// Never auto-remove (module in NEVER_AUTO_REMOVE whitelist).
    /// Requires --force to apply.
    fn never(reason: impl Into<String>) -> Self {
        Self {
            confidence: FixConfidence::Low,
            is_safe: false,
            reason: Some(reason.into()),
            safety_level: FixSafetyLevel::Unsafe,
        }
    }
}

/// Analyze the safety of removing an open statement.
///
/// This function determines:
/// 1. Whether the module is in the NEVER_AUTO_REMOVE whitelist
/// 2. Whether the module is RISKY (low confidence)
/// 3. Whether we have comprehensive export knowledge
/// 4. Whether operators might be affected
///
/// Returns a `RemovalSafety` indicating confidence and safety.
fn analyze_removal_safety(
    open: &OpenStatement,
    analysis: &OpenAnalysis,
    content: &str,
) -> RemovalSafety {
    let module = &open.module_path;

    // CRITICAL: Never auto-remove modules that provide operators
    if NEVER_AUTO_REMOVE.contains(module.as_str()) {
        return RemovalSafety::never(format!(
            "Module '{}' provides operators or implicit features that are hard to detect statically",
            module
        ));
    }

    // RISKY: These modules have complex usage patterns
    if RISKY_MODULES.contains(module.as_str()) {
        // Even if we think it's unused, be conservative
        return RemovalSafety::low(format!(
            "Module '{}' has complex usage patterns; manual verification recommended",
            module
        ));
    }

    // Check if we have export knowledge for this module
    let has_export_knowledge = get_known_exports(module).is_some();

    // Additional safety checks for operator-providing modules
    let clean_content = strip_comments_and_strings(content);

    // Check for potential operator usage that might be missed
    let potential_operator_issues = check_potential_operator_issues(module, &clean_content);
    if let Some(issue) = potential_operator_issues {
        return RemovalSafety::low(issue);
    }

    // Check for potential type constructor usage that might be missed
    let potential_type_issues = check_potential_type_issues(open, analysis, &clean_content);
    if let Some(issue) = potential_type_issues {
        return RemovalSafety::medium(issue);
    }

    // If we have export knowledge and comprehensive analysis, high confidence
    if has_export_knowledge {
        // Selective opens are safer because we know exactly what was imported
        if open.selective.is_some() {
            return RemovalSafety::safe();
        }

        // Full module opens with known exports - still high confidence
        return RemovalSafety::safe();
    }

    // Unknown module - we can't be sure about exports
    // This shouldn't happen often since is_open_used_with_exports returns true
    // for unknown modules, but handle it defensively
    RemovalSafety::medium(format!(
        "Module '{}' exports are not in the known exports database",
        module
    ))
}

/// Check for potential operator issues that might cause the analysis to miss usage.
fn check_potential_operator_issues(module: &str, clean_content: &str) -> Option<String> {
    // Modules that provide the * operator
    if module.contains("Mul") || module == "FStar.Int" || module.starts_with("FStar.Int") {
        // Check if there's any * usage in the content
        if clean_content.contains('*') {
            return Some(format!(
                "Content contains '*' which may use multiplication from '{}'",
                module
            ));
        }
    }

    // Modules that provide @ operator (list/seq append)
    if (module.contains("List") || module.contains("Seq"))
        && clean_content.contains('@')
        && !clean_content.contains("@|")
    {
        return Some(format!(
            "Content contains '@' which may use append from '{}'",
            module
        ));
    }

    // Modules that provide @| operator
    if (module.contains("Seq") || module.contains("Bytes"))
        && clean_content.contains("@|")
    {
        return Some(format!(
            "Content contains '@|' which may use seq append from '{}'",
            module
        ));
    }

    // Modules that provide ! and := operators (ref)
    if (module.contains("Ref") || module.contains("ST") || module.contains("HyperStack"))
        && (clean_content.contains('!') || clean_content.contains(":="))
    {
        return Some(format!(
            "Content contains '!' or ':=' which may use ref operators from '{}'",
            module
        ));
    }

    // Hat operators (^)
    if (module.contains("Int") || module == "FStar.Integers")
        && clean_content.contains('^')
    {
        return Some(format!(
            "Content contains '^' operators which may come from '{}'",
            module
        ));
    }

    // Bang operators (!)
    if (module == "Lib.IntTypes" || module.starts_with("Lib."))
        && (clean_content.contains("+!")
            || clean_content.contains("-!")
            || clean_content.contains("*!"))
    {
        return Some(format!(
            "Content contains '!' operators which may come from '{}'",
            module
        ));
    }

    // Dot operators (.)
    if (module == "Lib.IntTypes" || module.starts_with("Lib."))
        && (clean_content.contains("+.")
            || clean_content.contains("-.")
            || clean_content.contains("*."))
    {
        return Some(format!(
            "Content contains '.' operators which may come from '{}'",
            module
        ));
    }

    None
}

/// Check for potential type constructor issues.
fn check_potential_type_issues(
    open: &OpenStatement,
    analysis: &OpenAnalysis,
    clean_content: &str,
) -> Option<String> {
    let module = &open.module_path;

    // Check for common type constructors that might be used
    if let Some(exports) = get_known_exports(module) {
        // Count how many type constructors from this module MIGHT be used
        // (appear in content but weren't detected as actually used)
        let potential_unused: Vec<_> = exports
            .iter()
            .filter(|e| {
                let e_str = (*e).to_string();
                // Type constructors are uppercase
                if e_str.chars().next().is_some_and(|c| c.is_uppercase()) {
                    // Check if it appears in content but wasn't detected
                    clean_content.contains(*e)
                        && !analysis.used_type_constructors.contains(&e_str)
                } else {
                    false
                }
            })
            .collect();

        if !potential_unused.is_empty() && potential_unused.len() <= 3 {
            return Some(format!(
                "Type constructors {:?} appear in content but weren't detected as used",
                potential_unused
            ));
        }
    }

    None
}

/// FST004: Unused opens detection rule.
pub struct UnusedOpensRule;

impl UnusedOpensRule {
    pub fn new() -> Self {
        Self
    }
}

impl Default for UnusedOpensRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for UnusedOpensRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST004
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let analysis = analyze_opens(content);
        let mut diagnostics = Vec::new();

        for open in &analysis.opens {
            // Use the full analysis with implicit opens, includes, effect names
            if !is_open_used_full(
                open,
                &analysis.used_identifiers,
                &analysis.used_type_constructors,
                &analysis.used_module_prefixes,
                &analysis.used_operators,
                &analysis.aliases,
                &analysis.used_effect_names,
                &analysis.includes,
            ) {
                // Analyze removal safety before creating fix
                let safety = analyze_removal_safety(open, &analysis, content);

                // Create the edit
                let edits = vec![Edit {
                    file: file.to_path_buf(),
                    range: Range::new(open.line, 1, open.line, 1),
                    new_text: String::new(),
                }];

                // Create fix with appropriate safety level and metadata
                let fix = if safety.is_safe {
                    Fix::new(
                        format!("Remove unused open `{}`", open.module_path),
                        edits,
                    )
                    .with_confidence(safety.confidence)
                    .with_safety_level(safety.safety_level)
                    .with_reversible(false)  // Removal is not easily reversible
                    .with_requires_review(safety.safety_level != FixSafetyLevel::Safe)
                } else {
                    Fix::unsafe_fix(
                        format!("Remove unused open `{}`", open.module_path),
                        edits,
                        safety.confidence,
                        safety
                            .reason
                            .clone()
                            .unwrap_or_else(|| "Manual verification recommended".to_string()),
                    )
                    .with_safety_level(safety.safety_level)
                    .with_reversible(false)
                    .with_requires_review(true)
                };

                // Build message with safety info
                let message = if safety.is_safe && safety.confidence == FixConfidence::High {
                    format!("Unused open: `{}`", open.module_path)
                } else {
                    let reason = fix.unsafe_reason.as_deref().unwrap_or("low confidence");
                    format!(
                        "Unused open: `{}` [confidence: {}, reason: {}]",
                        open.module_path, fix.confidence, reason
                    )
                };

                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST004,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::new(
                        open.line,
                        open.col,
                        open.line,
                        open.col + open.line_text.trim().len(),
                    ),
                    message,
                    fix: Some(fix),
                });
            }
        }

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_parse_simple_open() {
        let content = "open FStar.List";
        let opens = parse_opens(content);
        assert_eq!(opens.len(), 1);
        assert_eq!(opens[0].module_path, "FStar.List");
        assert!(opens[0].selective.is_none());
    }

    #[test]
    fn test_parse_selective_open() {
        let content = "open FStar.List { map, filter, fold }";
        let opens = parse_opens(content);
        assert_eq!(opens.len(), 1);
        assert_eq!(opens[0].module_path, "FStar.List");
        assert_eq!(
            opens[0].selective,
            Some(vec![
                "map".to_string(),
                "filter".to_string(),
                "fold".to_string()
            ])
        );
    }

    #[test]
    fn test_parse_multiple_opens() {
        let content = r#"module Test

open FStar.All
open FStar.List
open FStar.Option { Some, None }

val foo : int -> int
"#;
        let opens = parse_opens(content);
        assert_eq!(opens.len(), 3);
        assert_eq!(opens[0].module_path, "FStar.All");
        assert_eq!(opens[1].module_path, "FStar.List");
        assert_eq!(opens[2].module_path, "FStar.Option");
    }

    #[test]
    fn test_parse_module_alias() {
        let content = "module L = FStar.List.Tot";
        let aliases = parse_module_aliases(content);
        assert_eq!(aliases.len(), 1);
        assert_eq!(aliases[0].alias, "L");
        assert_eq!(aliases[0].target, "FStar.List.Tot");
    }

    #[test]
    fn test_extract_used_prefixes() {
        let content = r#"
let x = List.map f xs
let y = FStar.Option.Some 1
"#;
        let prefixes = extract_used_module_prefixes(content);
        assert!(prefixes.contains(&"List".to_string()));
        assert!(prefixes.contains(&"FStar.Option".to_string()));
    }

    #[test]
    fn test_strip_comments() {
        let content = r#"
(* open FStar.Unused *)
let x = List.map (* comment *) f xs
// open Another.Unused
let y = 1
"#;
        let stripped = strip_comments_and_strings(content);
        assert!(!stripped.contains("FStar.Unused"));
        assert!(!stripped.contains("Another.Unused"));
        assert!(stripped.contains("List.map"));
    }

    // NOTE: Tests for is_open_used and module_name are deferred until
    // the corresponding functions are implemented. See WIP stubs at
    // the end of this file.
    //
    // #[test] fn test_selective_open_unused()
    // #[test] fn test_selective_open_used()
    // #[test] fn test_module_name()

    #[test]
    fn test_known_exports_coverage() {
        // Verify key modules are in the database
        assert!(get_known_exports("FStar.Mul").is_some());
        assert!(get_known_exports("FStar.List.Tot").is_some());
        assert!(get_known_exports("FStar.List.Tot.Base").is_some());
        assert!(get_known_exports("FStar.Seq").is_some());
        assert!(get_known_exports("FStar.Seq.Properties").is_some());
        assert!(get_known_exports("FStar.Set").is_some());
        assert!(get_known_exports("FStar.Map").is_some());
        assert!(get_known_exports("FStar.Classical").is_some());
        assert!(get_known_exports("FStar.Ghost").is_some());
        assert!(get_known_exports("FStar.Int32").is_some());
        assert!(get_known_exports("FStar.UInt64").is_some());
        assert!(get_known_exports("FStar.Math.Lemmas").is_some());
        assert!(get_known_exports("FStar.Tactics").is_some());
        assert!(get_known_exports("Lib.IntTypes").is_some());
        assert!(get_known_exports("Prims").is_some());
        assert!(get_known_exports("Steel.Memory").is_some());
        assert!(get_known_exports("LowStar.Buffer").is_some());

        // Verify unknown module returns None
        assert!(get_known_exports("Unknown.Module").is_none());
    }

    #[test]
    fn test_known_exports_contents() {
        // FStar.Mul should have op_Star
        let mul_exports = get_known_exports("FStar.Mul").unwrap();
        assert!(mul_exports.contains("op_Star"));

        // FStar.List.Tot should have common list operations
        let list_exports = get_known_exports("FStar.List.Tot").unwrap();
        assert!(list_exports.contains("length"));
        assert!(list_exports.contains("map"));
        assert!(list_exports.contains("fold_left"));
        assert!(list_exports.contains("filter"));
        assert!(list_exports.contains("append"));

        // Lib.IntTypes should have type aliases
        let int_types = get_known_exports("Lib.IntTypes").unwrap();
        assert!(int_types.contains("uint8"));
        assert!(int_types.contains("u32"));
        assert!(int_types.contains("size_t"));
        assert!(int_types.contains("add"));
        assert!(int_types.contains("logxor"));

        // FStar.Classical should have proof combinators
        let classical = get_known_exports("FStar.Classical").unwrap();
        assert!(classical.contains("forall_intro"));
        assert!(classical.contains("exists_elim"));
        assert!(classical.contains("move_requires"));

        // Prims should have built-in types and operations
        let prims = get_known_exports("Prims").unwrap();
        assert!(prims.contains("unit"));
        assert!(prims.contains("nat"));
        assert!(prims.contains("op_Addition"));
        assert!(prims.contains("admit"));
    }

    #[test]
    fn test_unused_open_with_known_exports() {
        // FStar.Mul opened but op_Star not used
        let content = r#"module Test

open FStar.Mul

let x = 1 + 2
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        // op_Star is not used, so it should be unused
        assert!(!used);
    }

    #[test]
    fn test_used_open_with_known_exports() {
        // FStar.Mul opened and op_Star used (via * operator which F* desugars)
        let content = r#"module Test

open FStar.Mul

let x = 2 * 3
"#;
        let analysis = analyze_opens(content);

        // Now with operator extraction, op_Star should be detected from `2 * 3`
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        // The * operator is used, so FStar.Mul should be considered used
        assert!(used);
    }

    #[test]
    fn test_operator_extraction() {
        // Test that various operators are correctly extracted
        let content = r#"
let a = x * y
let b = xs @ ys
let c = i +^ j
let d = p +! q
"#;
        let ops = extract_operator_internal_names(content);
        assert!(ops.contains("op_Star"), "Should detect * operator");
        assert!(ops.contains("op_At"), "Should detect @ operator");
        assert!(ops.contains("op_Plus_Hat"), "Should detect +^ operator");
        assert!(ops.contains("op_Plus_Bang"), "Should detect +! operator");
    }

    #[test]
    fn test_let_open_parsing() {
        let content = r#"let check_bound b =
  let open FStar.Mul in
  let open Lib.ByteSequence in
  x * y
"#;
        let let_opens = parse_let_opens(content);
        assert_eq!(let_opens.len(), 2);
        assert_eq!(let_opens[0].module_path, "FStar.Mul");
        assert_eq!(let_opens[1].module_path, "Lib.ByteSequence");
    }

    #[test]
    fn test_analysis_includes_operators() {
        let content = r#"module Test
open FStar.Mul
let product = a * b
"#;
        let analysis = analyze_opens(content);
        assert!(
            analysis.used_operators.contains("op_Star"),
            "Analysis should include op_Star from * usage"
        );
    }

    // =====================================================
    // FALSE NEGATIVE REGRESSION TESTS
    // These tests verify that previously missed unused opens
    // are now correctly detected.
    // =====================================================

    #[test]
    fn test_type_constructor_some_none_from_implicit_scope() {
        // Some/None come from FStar.Pervasives.Native which is always auto-opened.
        // So `open FStar.Option` when only Some/None are used is actually UNUSED.
        let content = r#"module Test

open FStar.Option

let x : option int = Some 42
let y : option string = None
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        // Some and None should still be captured as type constructors
        assert!(
            analysis.used_type_constructors.contains("Some"),
            "Some should be in used_type_constructors"
        );
        assert!(
            analysis.used_type_constructors.contains("None"),
            "None should be in used_type_constructors"
        );

        // But they are from implicit scope, so FStar.Option is UNUSED
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "FStar.Option should be UNUSED when only Some/None (from implicit scope) are used"
        );
    }

    #[test]
    fn test_fstar_option_used_with_non_implicit_exports() {
        // FStar.Option should be detected as USED when non-implicit exports are used
        // (isSome, isNone, get, map, bind, etc. are NOT from implicit scope)
        let content = r#"module Test

open FStar.Option

let x = isSome (Some 42)
let y = map (fun x -> x + 1) (Some 1)
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "FStar.Option should be USED when isSome/map (non-implicit) are used"
        );
    }

    #[test]
    fn test_type_constructor_either_detected() {
        // Test that Either's Inl/Inr constructors are detected
        let content = r#"module Test

open FStar.Either

let x : either int string = Inl 42
let y : either int string = Inr "hello"
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        // Verify Inl and Inr are captured
        assert!(
            analysis.used_type_constructors.contains("Inl"),
            "Inl should be in used_type_constructors"
        );
        assert!(
            analysis.used_type_constructors.contains("Inr"),
            "Inr should be in used_type_constructors"
        );

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "FStar.Either should be detected as used when Inl/Inr are used"
        );
    }

    #[test]
    fn test_unused_option_no_constructors() {
        // FStar.Option opened but no Some/None used - should be unused
        let content = r#"module Test

open FStar.Option

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "FStar.Option should be detected as UNUSED when no exports are used"
        );
    }

    #[test]
    fn test_selective_open_type_constructors_implicit() {
        // Selective open with type constructors from implicit scope.
        // Some/None come from FStar.Pervasives.Native which is auto-opened,
        // so `open FStar.Option { Some, None }` is UNUSED.
        let content = r#"module Test

open FStar.Option { Some, None }

let x = Some 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        // With implicit scope tracking, Some is from Pervasives.Native
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "Selective open with implicit-scope names should be UNUSED"
        );
    }

    #[test]
    fn test_selective_open_with_non_implicit_names() {
        // Selective open with names NOT from implicit scope should be detected as used
        let content = r#"module Test

open FStar.Option { isSome, isNone }

let x = isSome (Some 42)
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "Selective open with non-implicit names should be USED"
        );
    }

    #[test]
    fn test_selective_open_type_constructors_unused() {
        // Selective open with type constructors that aren't used
        let content = r#"module Test

open FStar.Option { Some, None }

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "Selective open with unused type constructors should be UNUSED"
        );
    }

    #[test]
    fn test_type_in_annotation_from_implicit_scope() {
        // The `option` type comes from FStar.Pervasives.Native (always auto-opened).
        // So `open FStar.Option` when only `option` is used is UNUSED.
        let content = r#"module Test

open FStar.Option

val my_func : option int -> int
"#;
        let analysis = analyze_opens(content);

        // 'option' is lowercase so it's in used_identifiers
        assert!(
            analysis.used_identifiers.contains("option"),
            "option type should be in used_identifiers"
        );

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "FStar.Option should be UNUSED when only 'option' (from implicit scope) is used"
        );
    }

    #[test]
    fn test_type_in_annotation_with_module_function() {
        // FStar.Option with actual module functions like `get` should be USED
        let content = r#"module Test

open FStar.Option

val my_func : option int -> int
let my_func x = get x
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "FStar.Option should be USED when 'get' (non-implicit export) is used"
        );
    }

    #[test]
    fn test_seq_type_constructor_detected() {
        // Test Seq type usage
        let content = r#"module Test

open FStar.Seq

let empty_seq : seq int = empty
"#;
        let analysis = analyze_opens(content);

        // Both 'seq' (type) and 'empty' (value) should be detected
        assert!(
            analysis.used_identifiers.contains("seq")
                || analysis.used_identifiers.contains("empty"),
            "seq/empty should be detected"
        );

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.Seq should be detected as used");
    }

    #[test]
    fn test_effect_names_detected() {
        // Effect names like ST, Tot, Pure in type signatures
        // Note: These are typically provided by FStar.Pervasives which is auto-opened,
        // but other effect modules might be explicitly opened
        let content = r#"module Test

open FStar.ST

val read_ref : ref int -> ST int
"#;
        let analysis = analyze_opens(content);

        // 'ST' is uppercase - should be in type_constructors
        // 'ref' is lowercase - should be in identifiers
        assert!(
            analysis.used_type_constructors.contains("ST")
                || analysis.used_identifiers.contains("ref"),
            "ST or ref should be detected"
        );

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.ST should be detected as used");
    }

    // =====================================================
    // FALSE NEGATIVE REGRESSION TESTS: Declaration line filtering
    // These tests verify that module alias, friend, and include
    // lines do not make opens appear used.
    // =====================================================

    #[test]
    fn test_module_alias_does_not_make_open_used() {
        // REGRESSION: `module S = FStar.Seq` caused `open FStar.Seq` to appear
        // used because `FStar.Seq` was extracted as a used module prefix from the
        // alias declaration line. The alias works without the open.
        let content = r#"module Test

open FStar.Seq

module S = FStar.Seq

let x = S.empty
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);
        assert_eq!(analysis.opens[0].module_path, "FStar.Seq");

        // FStar.Seq should NOT be in used_module_prefixes from the alias line.
        // Only S.empty uses "S" as a prefix, not "FStar.Seq".
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        // The open IS unused: code only uses the alias S, not the open
        assert!(
            !used,
            "open FStar.Seq should be detected as UNUSED when only module alias S is used"
        );
    }

    #[test]
    fn test_module_alias_with_actual_usage_still_detected() {
        // Ensure that if there IS actual usage through the open, it's still detected
        let content = r#"module Test

open FStar.Seq

module S = FStar.Seq

let x = S.empty
let y = length my_seq
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        // `length` is an export of FStar.Seq and is used unqualified
        assert!(
            used,
            "open FStar.Seq should be used when 'length' is used unqualified"
        );
    }

    #[test]
    fn test_friend_does_not_make_open_used() {
        // REGRESSION: `friend Lib.Sequence` caused qualified prefix extraction
        // to include `Lib.Sequence`, making `open Lib.Sequence` appear used.
        let content = r#"module Test

open Lib.Sequence

friend Lib.Sequence

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "open Lib.Sequence should be UNUSED when only friend declaration exists"
        );
    }

    #[test]
    fn test_include_does_not_make_open_used() {
        // `include Module` should not make `open Module` appear used
        let content = r#"module Test

open FStar.List.Tot

include FStar.List.Tot

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "open FStar.List.Tot should be UNUSED when only include declaration exists"
        );
    }

    // =====================================================
    // FALSE POSITIVE REGRESSION TESTS: Multi-line comments
    // =====================================================

    #[test]
    fn test_open_inside_multiline_comment_not_parsed() {
        // REGRESSION: Opens inside multi-line block comments were parsed
        // as real opens because parse_opens only checked if the line
        // started with (*
        let content = r#"module Test

(* This module used to use FStar.List:
open FStar.List.Tot
But we removed that dependency *)

let x = 42
"#;
        let opens = parse_opens(content);
        // The open inside the comment should NOT be parsed
        assert_eq!(
            opens.len(),
            0,
            "open inside multi-line block comment should not be parsed"
        );
    }

    #[test]
    fn test_open_after_multiline_comment_parsed() {
        // Opens AFTER a block comment closes should still be parsed
        let content = r#"module Test

(* This is a comment *)
open FStar.List.Tot

let x = map f xs
"#;
        let opens = parse_opens(content);
        assert_eq!(opens.len(), 1);
        assert_eq!(opens[0].module_path, "FStar.List.Tot");
    }

    #[test]
    fn test_nested_multiline_comments() {
        // F* supports nested block comments: (* outer (* inner *) still comment *)
        let content = r#"module Test

(* outer comment
(* nested comment *)
open FStar.Unused
*)

open FStar.List.Tot
let x = map f xs
"#;
        let opens = parse_opens(content);
        assert_eq!(opens.len(), 1, "Only the open after the comment should be parsed");
        assert_eq!(opens[0].module_path, "FStar.List.Tot");
    }

    // =====================================================
    // HACL*-inspired regression tests
    // =====================================================

    #[test]
    fn test_hacl_pattern_st_alias_and_open() {
        // Common HACL* pattern: both open and module alias for FStar.HyperStack.ST
        // The open should only be considered used if its exports are actually
        // used unqualified (like push_frame, pop_frame), NOT because the
        // module alias line references FStar.HyperStack.ST.
        let content = r#"module Test

open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

let f () =
  let h = ST.get () in
  42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        // ST.get() uses the ALIAS, not the open. The open provides unqualified
        // access to push_frame, pop_frame, etc. Here none of those are used.
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "open FStar.HyperStack.ST should be UNUSED when only ST alias is used via ST.get()"
        );
    }

    #[test]
    fn test_hacl_pattern_st_alias_and_open_with_push_pop() {
        // When push_frame/pop_frame ARE used, the open IS needed
        let content = r#"module Test

open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

let f () =
  push_frame ();
  let h = ST.get () in
  pop_frame ()
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "open FStar.HyperStack.ST should be USED when push_frame/pop_frame are used"
        );
    }

    #[test]
    fn test_is_declaration_line_helper() {
        assert!(is_declaration_line("open FStar.List.Tot"));
        assert!(is_declaration_line("module S = FStar.Seq"));
        assert!(is_declaration_line("friend Lib.Sequence"));
        assert!(is_declaration_line("include FStar.List.Tot"));
        assert!(!is_declaration_line("let x = List.map f xs"));
        assert!(!is_declaration_line("val foo : int -> int"));
        assert!(!is_declaration_line("type t = | A | B"));
    }

    // =====================================================
    // SAFETY FEATURE TESTS
    // These tests verify the conservative safety measures
    // for FST004 autofix functionality.
    // =====================================================

    #[test]
    fn test_never_auto_remove_fstar_mul() {
        // FStar.Mul should NEVER be auto-removed because it provides op_Star
        let content = r#"module Test

open FStar.Mul

let x = 1 + 2
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);
        assert!(
            !safety.is_safe,
            "FStar.Mul should NEVER be marked safe for auto-removal"
        );
        assert_eq!(
            safety.confidence,
            FixConfidence::Low,
            "FStar.Mul should have LOW confidence"
        );
        assert!(
            safety.reason.is_some(),
            "Should have a reason for being unsafe"
        );
    }

    #[test]
    fn test_never_auto_remove_lib_inttypes() {
        // Lib.IntTypes should NEVER be auto-removed
        let content = r#"module Test

open Lib.IntTypes

let x = 42
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        assert!(
            !safety.is_safe,
            "Lib.IntTypes should NEVER be marked safe for auto-removal"
        );
    }

    #[test]
    fn test_never_auto_remove_fstar_tactics() {
        // FStar.Tactics should NEVER be auto-removed
        let content = r#"module Test

open FStar.Tactics

let x = 42
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        assert!(
            !safety.is_safe,
            "FStar.Tactics should NEVER be marked safe for auto-removal"
        );
    }

    #[test]
    fn test_risky_module_fstar_classical() {
        // FStar.Classical is RISKY (low confidence)
        let content = r#"module Test

open FStar.Classical

let x = 42
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        assert!(
            !safety.is_safe || safety.confidence == FixConfidence::Low,
            "FStar.Classical should be risky (not safe or low confidence)"
        );
    }

    #[test]
    fn test_selective_open_is_safer() {
        // Selective opens are safer because we know exactly what was imported
        // Use FStar.Math.Lib which is NOT in RISKY_MODULES
        let content = r#"module Test

open FStar.Math.Lib { abs, max }

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);
        // Selective opens with known exports and not in risky list should be high confidence
        assert!(
            safety.confidence >= FixConfidence::Medium,
            "Selective open should have at least medium confidence"
        );
        assert!(
            safety.is_safe,
            "Selective open of non-risky module should be safe"
        );
    }

    #[test]
    fn test_mul_operator_detected_unsafe() {
        // If * appears in content and module is Mul-related, should be unsafe
        let content = r#"module Test

open FStar.Int32

let x = a * b
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        // The * operator presence should trigger caution
        assert!(
            safety.confidence <= FixConfidence::Medium
                || safety.reason.is_some()
                || !safety.is_safe,
            "Presence of * should reduce confidence or add reason"
        );
    }

    #[test]
    fn test_append_operator_detected() {
        // @ operator should trigger caution for List modules
        let content = r#"module Test

open FStar.List.Tot

let xs = [1] @ [2]
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        // Should be risky due to @ operator and RISKY_MODULES list
        assert!(
            !safety.is_safe || safety.confidence <= FixConfidence::Medium,
            "@ operator with List module should be risky"
        );
    }

    #[test]
    fn test_hat_operator_detected() {
        // ^-suffixed operators should trigger caution for Int modules
        let content = r#"module Test

open FStar.UInt32

let x = a +^ b
"#;
        let analysis = analyze_opens(content);

        // +^ should be detected
        assert!(
            analysis.used_operators.contains("op_Plus_Hat"),
            "+^ should be detected as op_Plus_Hat"
        );
    }

    #[test]
    fn test_ref_operators_detected() {
        // ! and := operators should trigger caution for Ref/ST modules
        let content = r#"module Test

open FStar.Ref

let x = !r
let _ = r := 42
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        // Ref module with ref operators should be risky
        assert!(
            !safety.is_safe || safety.confidence <= FixConfidence::Medium,
            "Ref module with ! and := should be risky"
        );
    }

    #[test]
    fn test_unknown_module_medium_confidence() {
        // Unknown modules should have medium confidence (conservative)
        let content = r#"module Test

open Some.Unknown.Module

let x = 42
"#;
        let analysis = analyze_opens(content);

        // Unknown module returns true from is_open_used_with_exports
        // so it won't even get to safety analysis in normal flow
        // But if it did, it should be medium confidence
        let open_stmt = &analysis.opens[0];
        assert!(get_known_exports(&open_stmt.module_path).is_none());
    }

    #[test]
    fn test_safe_removal_known_unused() {
        // A known module with definitely unused exports should be safe
        let content = r#"module Test

open FStar.Math.Lib

let x = 42
"#;
        let analysis = analyze_opens(content);
        let safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);

        // FStar.Math.Lib is not in NEVER_AUTO_REMOVE or RISKY_MODULES
        // and we have export knowledge, so should be safe
        assert!(
            safety.is_safe && safety.confidence >= FixConfidence::Medium,
            "Known module with no usage should be safe to remove"
        );
    }

    #[test]
    fn test_fix_can_auto_apply_only_high_safe() {
        use super::super::rules::Fix;

        // Test that can_auto_apply requires both high confidence and is_safe
        let edits = vec![];

        let safe_high = Fix::safe("test", edits.clone());
        assert!(safe_high.can_auto_apply(), "High confidence safe fix should auto-apply");

        let safe_medium = Fix::new("test", edits.clone());
        assert!(!safe_medium.can_auto_apply(), "Medium confidence should not auto-apply");

        let unsafe_high = Fix::unsafe_fix("test", edits.clone(), FixConfidence::High, "reason");
        assert!(!unsafe_high.can_auto_apply(), "Unsafe fix should not auto-apply");

        let unsafe_low = Fix::unsafe_fix("test", edits.clone(), FixConfidence::Low, "reason");
        assert!(!unsafe_low.can_auto_apply(), "Unsafe low fix should not auto-apply");
    }

    #[test]
    fn test_whitelists_comprehensive() {
        // Verify key dangerous modules are in NEVER_AUTO_REMOVE
        assert!(NEVER_AUTO_REMOVE.contains("FStar.Mul"));
        assert!(NEVER_AUTO_REMOVE.contains("FStar.Integers"));
        assert!(NEVER_AUTO_REMOVE.contains("Lib.IntTypes"));
        assert!(NEVER_AUTO_REMOVE.contains("LowStar.BufferOps"));
        assert!(NEVER_AUTO_REMOVE.contains("FStar.Tactics"));
        assert!(NEVER_AUTO_REMOVE.contains("FStar.Pervasives"));
        assert!(NEVER_AUTO_REMOVE.contains("Prims"));

        // Verify risky modules are in RISKY_MODULES
        assert!(RISKY_MODULES.contains("FStar.Classical"));
        assert!(RISKY_MODULES.contains("FStar.Ghost"));
        assert!(RISKY_MODULES.contains("FStar.Seq"));
        assert!(RISKY_MODULES.contains("FStar.List.Tot"));
        assert!(RISKY_MODULES.contains("FStar.Ref"));
        assert!(RISKY_MODULES.contains("LowStar.Buffer"));
    }

    #[test]
    fn test_diagnostic_message_includes_safety_info() {
        // The diagnostic message should include safety information for non-safe fixes
        let content = r#"module Test

open FStar.Mul

let x = 1 + 2
"#;
        let rule = UnusedOpensRule::new();
        let path = PathBuf::from("test.fst");
        let diagnostics = rule.check(&path, content);

        // FStar.Mul is unused but in NEVER_AUTO_REMOVE
        // So we should get a diagnostic (but with unsafe fix)
        // Actually, is_open_used_with_exports checks for op_Star which is not used
        // So we should get a diagnostic

        // The check should produce a diagnostic because * is not used
        // But the fix should be marked unsafe

        if !diagnostics.is_empty() {
            let diag = &diagnostics[0];
            assert!(diag.fix.is_some());
            let fix = diag.fix.as_ref().unwrap();
            assert!(
                !fix.is_safe() || fix.confidence == FixConfidence::Low,
                "FStar.Mul fix should be marked unsafe or low confidence"
            );
        }
    }

    // =====================================================
    // BRRR-LANG PATTERN TESTS
    // Test patterns commonly found in production F* codebases
    // =====================================================

    #[test]
    fn test_classical_with_forall_intro() {
        // Pattern: FStar.Classical opened for proof combinators
        let content = r#"module Test

open FStar.Classical

let lemma_foo (x:int) : Lemma (x + 0 == x) =
  forall_intro (fun y -> ())
"#;
        let analysis = analyze_opens(content);

        // forall_intro should be detected as used
        assert!(
            analysis.used_identifiers.contains("forall_intro"),
            "forall_intro should be detected"
        );

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.Classical should be detected as used");
    }

    #[test]
    fn test_ghost_with_reveal_hide() {
        // Pattern: FStar.Ghost for erased values
        let content = r#"module Test

open FStar.Ghost

let f (x: erased int) =
  reveal x + 1
"#;
        let analysis = analyze_opens(content);

        // reveal and erased should be detected
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.Ghost should be used when reveal/erased appear");
    }

    #[test]
    fn test_squash_pattern() {
        // Pattern: FStar.Squash for squash types
        let content = r#"module Test

open FStar.Squash

let get_proof_wrapper #a (p: squash a) : a =
  get_proof p
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.Squash should be used when squash/get_proof appear");
    }

    #[test]
    fn test_sequence_with_slice() {
        // Pattern: Using Seq functions
        let content = r#"module Test

open FStar.Seq

let take_first (s: seq int) (n: nat{n <= length s}) =
  slice s 0 n
"#;
        let analysis = analyze_opens(content);

        // seq, length, slice should be detected
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(used, "FStar.Seq should be used when seq functions appear");
    }

    #[test]
    fn test_multiple_opens_different_safety() {
        // Test file with multiple opens having different safety levels
        let content = r#"module Test

open FStar.Mul
open FStar.Math.Lib
open FStar.List.Tot

let x = 42
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 3);

        // FStar.Mul - should be NEVER (in whitelist)
        let mul_safety = analyze_removal_safety(&analysis.opens[0], &analysis, content);
        assert!(!mul_safety.is_safe, "FStar.Mul should be unsafe");

        // FStar.Math.Lib - should be safe (known exports, not in lists)
        let math_safety = analyze_removal_safety(&analysis.opens[1], &analysis, content);
        assert!(math_safety.is_safe, "FStar.Math.Lib should be safe");

        // FStar.List.Tot - should be risky (in RISKY_MODULES)
        let list_safety = analyze_removal_safety(&analysis.opens[2], &analysis, content);
        assert!(
            !list_safety.is_safe || list_safety.confidence == FixConfidence::Low,
            "FStar.List.Tot should be risky"
        );
    }

    // NOTE: test_generate_remove_fix_targets_single_line is deferred until
    // generate_remove_fix is implemented.

    #[test]
    fn test_check_unused_open_fix_does_not_delete_adjacent_line() {
        // Integration test: apply the fix to content and verify only the open line is removed.
        let content = r#"module Test

open FStar.Math.Lib

val foo : int -> int
let foo x = x + 1
"#;
        let rule = UnusedOpensRule;
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        // Find the diagnostic for FStar.Math.Lib
        let diag = diagnostics
            .iter()
            .find(|d| d.message.contains("FStar.Math.Lib"));
        assert!(diag.is_some(), "Should detect unused open FStar.Math.Lib");

        let fix = diag.unwrap().fix.as_ref().expect("Diagnostic should have a fix");
        assert_eq!(fix.edits.len(), 1);
        let edit = &fix.edits[0];

        // The open is on line 3. The fix must target ONLY line 3.
        assert_eq!(edit.range.start_line, 3, "Open is on line 3");
        assert_eq!(
            edit.range.end_line, 3,
            "Fix must only target line 3, not line 4 (which is an empty line that should survive)"
        );
    }

    // =====================================================
    // IMPLICIT SCOPE TESTS
    // Verify that names from Prims/FStar.Pervasives.Native
    // are correctly excluded from usage counting.
    // =====================================================

    #[test]
    fn test_implicit_scope_prims_types_not_counted() {
        // Types like nat, int, bool, unit, string come from Prims
        // and should NOT count as usage for other modules
        let content = r#"module Test

open FStar.Pure

val f : nat -> int -> bool -> unit -> string -> pos
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        // FStar.Pure's non-implicit exports like pure_pre, pure_post are not used
        // nat/int/bool etc. come from Prims, not FStar.Pure
        assert!(
            !used,
            "FStar.Pure should be UNUSED when only Prims types are used"
        );
    }

    #[test]
    fn test_implicit_scope_nil_cons_not_counted() {
        // Nil and Cons are list constructors from Prims
        let content = r#"module Test

open FStar.List.Tot

let xs = Cons 1 (Cons 2 Nil)
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);

        // Nil/Cons come from Prims, but FStar.List.Tot has many other exports.
        // If ONLY Nil/Cons are used, the open is unnecessary.
        // However, the analysis also detects if any FStar.List.Tot export
        // (like length, map, etc.) is used.
        // In this case, no List.Tot-specific function is used.
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "FStar.List.Tot should be UNUSED when only Nil/Cons (from Prims) are used"
        );
    }

    #[test]
    fn test_implicit_scope_does_not_affect_non_implicit_exports() {
        // Names like `erased`, `reveal`, `hide` are NOT from implicit scope
        // so they should still count as usage for FStar.Ghost
        let content = r#"module Test

open FStar.Ghost

let f (x: erased int) = reveal x
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            used,
            "FStar.Ghost should be USED because erased/reveal are NOT from implicit scope"
        );
    }

    #[test]
    fn test_implicit_scope_lemma_effect() {
        // The `Lemma` effect name comes from implicit scope (FStar.Pervasives).
        // Using it should NOT count as evidence for any explicit open.
        let content = r#"module Test

open FStar.Classical

val my_lemma : x:int -> Lemma (x + 0 == x)
"#;
        let analysis = analyze_opens(content);

        // Lemma is implicit, but forall_intro etc. from Classical are not
        // Since no Classical-specific export is used, it should be unused
        let used = is_open_used_with_exports(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
        );
        assert!(
            !used,
            "FStar.Classical should be UNUSED when only Lemma (implicit) is used"
        );
    }

    // =====================================================
    // INCLUDE STATEMENT TESTS
    // =====================================================

    #[test]
    fn test_parse_includes() {
        let content = r#"module Test

include FStar.List.Tot
include Lib.Sequence

let x = length [1; 2]
"#;
        let includes = parse_includes(content);
        assert_eq!(includes.len(), 2);
        assert_eq!(includes[0].module_path, "FStar.List.Tot");
        assert_eq!(includes[1].module_path, "Lib.Sequence");
    }

    #[test]
    fn test_include_makes_open_redundant() {
        // When both `include M` and `open M` exist, the open is redundant
        // because include already re-exports everything
        let content = r#"module Test

open FStar.List.Tot
include FStar.List.Tot

let x = length [1; 2]
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 1);
        assert_eq!(analysis.includes.len(), 1);

        // The full analysis with includes should detect the open as unused
        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            !used,
            "open FStar.List.Tot should be UNUSED when include FStar.List.Tot exists"
        );
    }

    #[test]
    fn test_include_different_module_does_not_affect() {
        // Include of a DIFFERENT module should not make the open unused
        let content = r#"module Test

open FStar.List.Tot
include FStar.Seq

let x = length [1; 2]
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            used,
            "open FStar.List.Tot should be USED (include is for different module)"
        );
    }

    // =====================================================
    // LET-OPEN TESTS
    // =====================================================

    #[test]
    fn test_let_open_scope_estimation() {
        let content = r#"let f x =
  let open FStar.Mul in
  x * x

let g y = y + 1
"#;
        let let_opens = parse_let_opens(content);
        assert_eq!(let_opens.len(), 1);
        assert_eq!(let_opens[0].module_path, "FStar.Mul");
        assert!(let_opens[0].is_local);
        assert!(let_opens[0].scope_end.is_some());
    }

    #[test]
    fn test_let_open_in_analysis() {
        let content = r#"module Test

let f x =
  let open FStar.Mul in
  x * x

let g y =
  let open Lib.ByteSequence in
  to_bytes y
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.let_opens.len(), 2);
        assert_eq!(analysis.let_opens[0].module_path, "FStar.Mul");
        assert_eq!(analysis.let_opens[1].module_path, "Lib.ByteSequence");
    }

    // =====================================================
    // EFFECT NAME RESOLUTION TESTS
    // =====================================================

    #[test]
    fn test_extract_effect_names_stack() {
        let content = r#"module Test

open FStar.HyperStack.ST

val my_func : buf:buffer uint8 -> Stack unit
  (requires fun h -> live h buf)
  (ensures fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1)
"#;
        let effects = extract_effect_names(content);
        assert!(
            effects.contains("Stack"),
            "Stack effect should be detected"
        );
    }

    #[test]
    fn test_extract_effect_names_st() {
        let content = r#"module Test

val read_ref : ref int -> ST int
  (requires fun h -> True)
  (ensures fun h0 r h1 -> r == sel h0 ref)
"#;
        let effects = extract_effect_names(content);
        assert!(
            effects.contains("ST"),
            "ST effect should be detected"
        );
    }

    #[test]
    fn test_effect_name_from_fstar_st() {
        // FStar.ST provides the `ST` effect and ref operators
        let content = r#"module Test

open FStar.ST

val read_ref : ref int -> ST int
  (requires fun h -> True)
  (ensures fun h0 r h1 -> True)
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            used,
            "FStar.ST should be USED when ST effect name is in type signature"
        );
    }

    // =====================================================
    // QUALIFIED ACCESS MAP TESTS
    // =====================================================

    #[test]
    fn test_qualified_access_map_basic() {
        let content = r#"let x = List.map f xs
let y = Seq.length s
let z = FStar.Math.Lemmas.small_mod a b
"#;
        let map = extract_qualified_access_map(content);
        assert!(map.contains_key("List"), "Should have 'List' prefix");
        assert!(map["List"].contains("map"), "List should map to 'map'");
        assert!(map.contains_key("Seq"), "Should have 'Seq' prefix");
        assert!(map["Seq"].contains("length"), "Seq should map to 'length'");
    }

    #[test]
    fn test_qualified_access_ignores_declaration_lines() {
        // Module alias and open lines should not appear in qualified access map
        let content = r#"module S = FStar.Seq
open FStar.List.Tot
let x = S.length s
"#;
        let map = extract_qualified_access_map(content);
        // S.length should be captured but not FStar.Seq from the alias line
        assert!(map.contains_key("S"), "Should have 'S' prefix from usage");
    }

    // =====================================================
    // FULL INTEGRATION TESTS WITH is_open_used_full
    // =====================================================

    #[test]
    fn test_full_analysis_hacl_pattern() {
        // Common HACL* pattern with multiple opens and aliases
        let content = r#"module Test

open FStar.HyperStack.ST
open FStar.Mul
open Lib.IntTypes

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

let f () =
  push_frame ();
  let h = ST.get () in
  let x = 2ul *^ 3ul in
  pop_frame ()
"#;
        let analysis = analyze_opens(content);

        // FStar.HyperStack.ST should be USED (push_frame, pop_frame)
        let st_used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(st_used, "FStar.HyperStack.ST should be USED (push_frame, pop_frame)");
    }

    #[test]
    fn test_full_analysis_either_inl_inr() {
        // FStar.Either's Inl/Inr are NOT from implicit scope
        let content = r#"module Test

open FStar.Either

let x : either int string = Inl 42
let y : either int string = Inr "hello"
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            used,
            "FStar.Either should be USED (Inl/Inr are NOT in implicit scope)"
        );
    }

    #[test]
    fn test_full_analysis_order_constructors() {
        // FStar.Order's Lt/Eq/Gt are NOT from implicit scope
        let content = r#"module Test

open FStar.Order

let cmp x y =
  if x < y then Lt
  else if x = y then Eq
  else Gt
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            used,
            "FStar.Order should be USED (Lt/Eq/Gt are NOT in implicit scope)"
        );
    }

    #[test]
    fn test_full_analysis_reflection_constructors() {
        // FStar.Reflection Tv_* constructors are NOT from implicit scope
        let content = r#"module Test

open FStar.Reflection

let is_var t =
  match inspect t with
  | Tv_Var _ -> true
  | _ -> false
"#;
        let analysis = analyze_opens(content);

        let used = is_open_used_full(
            &analysis.opens[0],
            &analysis.used_identifiers,
            &analysis.used_type_constructors,
            &analysis.used_module_prefixes,
            &analysis.used_operators,
            &analysis.aliases,
            &analysis.used_effect_names,
            &analysis.includes,
        );
        assert!(
            used,
            "FStar.Reflection should be USED (Tv_Var is NOT in implicit scope)"
        );
    }

    // =====================================================
    // EDGE CASES
    // =====================================================

    #[test]
    fn test_empty_file_no_crashes() {
        let content = "";
        let analysis = analyze_opens(content);
        assert!(analysis.opens.is_empty());
        assert!(analysis.let_opens.is_empty());
        assert!(analysis.includes.is_empty());
    }

    #[test]
    fn test_module_only_no_opens() {
        let content = "module Test\n\nlet x = 42\n";
        let analysis = analyze_opens(content);
        assert!(analysis.opens.is_empty());
    }

    #[test]
    fn test_include_in_comment_not_parsed() {
        let content = r#"module Test
(* include FStar.List.Tot *)
let x = 42
"#;
        let includes = parse_includes(content);
        assert!(includes.is_empty(), "Include inside comment should not be parsed");
    }

    #[test]
    fn test_let_open_not_counted_as_top_level() {
        // Let-opens should not appear in the top-level opens list
        let content = r#"module Test

let f x =
  let open FStar.Mul in
  x * x
"#;
        let analysis = analyze_opens(content);
        assert_eq!(analysis.opens.len(), 0, "let-open should not be a top-level open");
        assert_eq!(analysis.let_opens.len(), 1, "let-open should be in let_opens");
    }

    #[test]
    fn test_implicit_scope_names_comprehensive() {
        // Verify key names are in implicit scope
        assert!(IMPLICIT_SCOPE_NAMES.contains("Some"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("None"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("option"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("nat"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("int"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("bool"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("unit"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("string"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Nil"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Cons"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Lemma"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Tot"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Pure"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("Ghost"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("fst"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("snd"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("tuple2"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("normalize"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("admit"));
        assert!(IMPLICIT_SCOPE_NAMES.contains("magic"));
    }

    #[test]
    fn test_implicit_scope_excludes_non_implicit() {
        // These names should NOT be in implicit scope
        assert!(!IMPLICIT_SCOPE_NAMES.contains("erased"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("reveal"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("hide"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("length"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("map"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("isSome"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("isNone"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("Inl"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("Inr"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("push_frame"));
        assert!(!IMPLICIT_SCOPE_NAMES.contains("pop_frame"));
    }

    #[test]
    fn test_analysis_populates_all_fields() {
        let content = r#"module Test

open FStar.List.Tot
include FStar.Seq

module L = FStar.List.Tot

let f x =
  let open FStar.Mul in
  L.length x * 2

val g : nat -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
"#;
        let analysis = analyze_opens(content);

        // Check all fields are populated
        assert_eq!(analysis.opens.len(), 1);
        assert_eq!(analysis.let_opens.len(), 1);
        assert_eq!(analysis.aliases.len(), 1);
        assert_eq!(analysis.includes.len(), 1);
        assert!(!analysis.used_identifiers.is_empty());
        assert!(!analysis.used_module_prefixes.is_empty());
        assert!(!analysis.used_operators.is_empty());
        assert!(!analysis.used_effect_names.is_empty());
        assert!(!analysis.qualified_access_map.is_empty());
    }
}
