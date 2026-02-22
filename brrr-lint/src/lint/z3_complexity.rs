//! FST007: Z3 complexity analyzer.
//!
//! Detects code patterns that cause Z3 performance issues in F* verification:
//!
//! 1. Quantifiers without SMTPat triggers - unbounded search
//! 2. Non-linear arithmetic (var * var) - undecidable in general
//! 3. Deep quantifier nesting (>3 levels) - exponential blowup
//! 4. Large match expressions (>10 branches) - case splitting explosion
//! 5. Recursive functions without decreases clause - termination proving difficulty
//! 6. High z3rlimit (>100) - symptom of proof complexity
//! 7. Wildcard pattern in non-last position - unreachable branches
//! 8. Duplicate match arms - redundant case analysis

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{ASSERT_NORM_CALL_RE, ASSERT_BY_TACTIC_RE};

lazy_static! {
    /// Quantifier patterns - forall and exists with type bindings
    static ref FORALL_PATTERN: Regex = Regex::new(r"forall\s*\([^)]+\)\s*\.").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref EXISTS_PATTERN: Regex = Regex::new(r"exists\s*\([^)]+\)\s*\.").unwrap_or_else(|e| panic!("regex: {e}"));

    /// SMTPat trigger annotation (lemma-level)
    static ref SMTPAT_PATTERN: Regex = Regex::new(r"\[SMTPat").unwrap_or_else(|e| panic!("regex: {e}"));
    static ref SMTPATALL_PATTERN: Regex = Regex::new(r"\[SMTPatOr").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Inline pattern triggers in quantifiers: {:pattern ...}
    static ref INLINE_PATTERN_TRIGGER: Regex = Regex::new(r"\{:pattern\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Non-linear arithmetic: identifier * identifier (excluding literals)
    /// Captures two variable names to check if they're different
    static ref NONLINEAR_MUL: Regex = Regex::new(
        r"\b([a-z_][a-z0-9_]*)\s*\*\s*([a-z_][a-z0-9_]*)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Recursive function definition
    static ref LET_REC: Regex = Regex::new(r"let\s+rec\s+(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Decreases clause (can appear as annotation or inline)
    static ref DECREASES_CLAUSE: Regex = Regex::new(r"\(decreases\s|\bdecreases\s*\{").unwrap_or_else(|e| panic!("regex: {e}"));

    /// High z3rlimit pragma
    static ref Z3RLIMIT: Regex = Regex::new(r#"#set-options\s*"[^"]*z3rlimit\s+(\d+)"#).unwrap_or_else(|e| panic!("regex: {e}"));
    static ref Z3RLIMIT_INLINE: Regex = Regex::new(r"z3rlimit\s+(\d+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Match expression start - captures the discriminant (may be multi-word like `inspect t`)
    static ref MATCH_START: Regex = Regex::new(r"\bmatch\s+(.+?)\s+with\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Match branch (pipe followed by pattern) - captures the pattern text after `|`
    static ref MATCH_BRANCH: Regex = Regex::new(r"^\s*\|").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Wildcard pattern: standalone `_` or `_ ->` at branch start
    static ref WILDCARD_BRANCH: Regex = Regex::new(r"^\s*\|\s*_\s*(->|when\b)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Branch pattern extractor: captures everything between `|` and `->`
    static ref BRANCH_PATTERN: Regex = Regex::new(r"^\s*\|\s*(.+?)\s*->").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Nested quantifier detection - simplified approach
    static ref QUANTIFIER_KEYWORD: Regex = Regex::new(r"\b(forall|exists)\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Literals and constants to exclude from non-linear check
    static ref NUMERIC_LITERAL: Regex = Regex::new(r"^[0-9]+$").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Common safe multiplications (index calculations, etc.)
    static ref SAFE_VARS: &'static [&'static str] = &[
        "sizeof", "alignof", "len", "length", "size", "count", "n", "m", "i", "j", "k"
    ];

    /// assert with tactic - has explicit proof guidance
    static ref ASSERT_BY: Regex = Regex::new(r"\bassert\s*\([^)]*\)\s+by\b").unwrap_or_else(|e| panic!("regex: {e}"));
    /// Plain assert statement
    static ref PLAIN_ASSERT: Regex = Regex::new(r"\bassert\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));
}

/// FST007: Z3 Complexity Analyzer
///
/// Configurable thresholds for detecting Z3 performance anti-patterns.
pub struct Z3ComplexityRule {
    /// Maximum allowed quantifier nesting depth before warning
    pub max_quantifier_depth: usize,
    /// Maximum match branches before suggesting split
    pub max_match_branches: usize,
    /// z3rlimit threshold above which to warn
    pub max_z3rlimit: u32,
    /// Number of lines to look ahead for SMTPat after quantifier
    pub smtpat_lookahead_lines: usize,
}

impl Z3ComplexityRule {
    pub fn new() -> Self {
        Self {
            max_quantifier_depth: 3,
            max_match_branches: 10,
            max_z3rlimit: 100,
            smtpat_lookahead_lines: 5,
        }
    }

    /// Check for quantifiers without any triggers.
    ///
    /// Quantifiers without triggers can force Z3 to enumerate possible instantiations,
    /// leading to exponential search space and timeouts.
    ///
    /// This check recognizes:
    /// - [SMTPat ...] lemma-level patterns
    /// - [SMTPatOr ...] disjunctive patterns
    /// - {:pattern ...} inline quantifier triggers
    ///
    /// This check SKIPS quantifiers that don't need triggers:
    /// - Quantifiers inside refinement types `{forall x. P x}`
    /// - Quantifiers in requires/ensures clauses (specification only)
    /// - Quantifiers with explicit inline patterns
    fn check_quantifiers_without_triggers(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            // Skip lines inside comments (simple heuristic)
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Check for forall/exists
            let has_forall = FORALL_PATTERN.is_match(line);
            let has_exists = EXISTS_PATTERN.is_match(line);

            if has_forall || has_exists {
                // Check if this quantifier is inside a refinement type (curly braces)
                // Example: s:seq a{forall i. P i} - this doesn't need SMTPat
                if self.is_in_refinement_type(line, lines.get(line_idx.saturating_sub(1))) {
                    continue;
                }

                // Look ahead for triggers within configured range
                let context_end =
                    std::cmp::min(line_idx + self.smtpat_lookahead_lines, lines.len());
                let context: String = lines[line_idx..context_end].join("\n");

                // Check for any kind of trigger:
                // 1. [SMTPat ...] - lemma-level pattern
                // 2. [SMTPatOr ...] - disjunctive pattern
                // 3. {:pattern ...} - inline quantifier trigger
                let has_trigger = SMTPAT_PATTERN.is_match(&context)
                    || SMTPATALL_PATTERN.is_match(&context)
                    || INLINE_PATTERN_TRIGGER.is_match(&context);

                if !has_trigger {
                    // Check if this appears to be in a specification context
                    // (val declarations, requires/ensures) where triggers are less critical
                    if self.is_specification_context(&lines, line_idx) {
                        continue;
                    }

                    let quantifier = if has_forall { "forall" } else { "exists" };
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST007,
                        severity: DiagnosticSeverity::Info, // Reduced from Warning
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "{} quantifier without trigger pattern. Consider adding \
                             {{:pattern (...)}} inline or [SMTPat ...] for lemmas \
                             if Z3 struggles with instantiation.",
                            quantifier
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check if a quantifier appears to be inside a refinement type.
    ///
    /// Refinement types like `s:seq a{forall i. P i}` use quantifiers for
    /// specification only and don't need SMTPat triggers.
    fn is_in_refinement_type(&self, line: &str, prev_line: Option<&&str>) -> bool {
        // Count unbalanced braces before the forall/exists
        // If there's an open { without matching }, we're likely in a refinement
        let mut brace_depth: i32 = 0;

        // Check previous line for unclosed brace
        if let Some(prev) = prev_line {
            for ch in prev.chars() {
                match ch {
                    '{' => brace_depth += 1,
                    '}' => brace_depth = brace_depth.saturating_sub(1),
                    _ => {}
                }
            }
        }

        // Check current line up to the quantifier
        if let Some(pos) = line.find("forall").or_else(|| line.find("exists")) {
            for ch in line[..pos].chars() {
                match ch {
                    '{' => brace_depth += 1,
                    '}' => brace_depth = brace_depth.saturating_sub(1),
                    _ => {}
                }
            }
        }

        brace_depth > 0
    }

    /// Check if we're in a specification context where quantifiers don't need triggers.
    ///
    /// This includes val declarations, requires clauses, and ensures clauses
    /// that are not part of lemma postconditions requiring automatic instantiation.
    fn is_specification_context(&self, lines: &[&str], line_idx: usize) -> bool {
        // Look back for context markers
        let lookback = 10.min(line_idx);
        for i in (line_idx.saturating_sub(lookback)..=line_idx).rev() {
            let line = lines[i].trim();

            // val declarations are specifications
            if line.starts_with("val ") {
                return true;
            }

            // If we hit a let/let rec, check if it's a Lemma
            if line.starts_with("let ") {
                // Continue checking - Lemmas need triggers, other lets don't
                return !line.contains("Lemma");
            }

            // requires clauses are specification
            if line.starts_with("(requires") || line.contains("requires ") {
                return true;
            }
        }

        false
    }

    /// Check for non-linear arithmetic.
    ///
    /// Multiplication of two variables (not constants) creates non-linear
    /// arithmetic constraints that Z3 struggles with.
    fn check_nonlinear_arithmetic(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Skip comment lines
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            for caps in NONLINEAR_MUL.captures_iter(line) {
                let var1 = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                let var2 = caps.get(2).map(|m| m.as_str()).unwrap_or("");

                // Skip if either is a numeric literal
                if NUMERIC_LITERAL.is_match(var1) || NUMERIC_LITERAL.is_match(var2) {
                    continue;
                }

                // Skip x * x (squaring) - often acceptable
                if var1 == var2 {
                    continue;
                }

                // All non-linear arithmetic is Info level. Regex-based detection
                // cannot determine whether NLA is problematic in context (e.g., math
                // libraries, lemma specifications, or code with proper SMT hints).
                // Emitting Warning for every `a * b` is far too noisy on real codebases.
                let var1_safe = SAFE_VARS.contains(&var1);
                let var2_safe = SAFE_VARS.contains(&var2);
                let detail = if var1_safe && var2_safe {
                    format!(
                        "Non-linear arithmetic `{} * {}` detected. While common for indexing, \
                         this can cause Z3 difficulty if verification times out.",
                        var1, var2
                    )
                } else {
                    format!(
                        "Non-linear arithmetic `{} * {}` may cause Z3 difficulty. \
                         Consider using linear approximations or lemmas if verification times out.",
                        var1, var2
                    )
                };
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST007,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(line_num, 1),
                    message: detail,
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for deep quantifier nesting.
    ///
    /// Each nested quantifier level exponentially increases the search space.
    fn check_quantifier_depth(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut max_depth_seen = 0;
        let mut max_depth_line = 0;
        let mut current_depth: usize = 0;
        let mut paren_depth = 0;
        let mut quantifier_paren_depths: Vec<usize> = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Track parenthesis depth and quantifiers
            let chars: Vec<char> = line.chars().collect();
            let mut i = 0;

            while i < chars.len() {
                match chars[i] {
                    '(' => {
                        // Check if this is a quantifier
                        let rest: String = chars[i..].iter().collect();
                        if QUANTIFIER_KEYWORD.is_match(&rest) {
                            current_depth += 1;
                            quantifier_paren_depths.push(paren_depth);

                            if current_depth > max_depth_seen {
                                max_depth_seen = current_depth;
                                max_depth_line = line_num;
                            }
                        }
                        paren_depth += 1;
                    }
                    ')' => {
                        if paren_depth > 0 {
                            paren_depth -= 1;
                            // Check if we're closing a quantifier scope
                            if let Some(&q_depth) = quantifier_paren_depths.last() {
                                if paren_depth < q_depth {
                                    quantifier_paren_depths.pop();
                                    current_depth = current_depth.saturating_sub(1);
                                }
                            }
                        }
                    }
                    _ => {}
                }
                i += 1;
            }
        }

        if max_depth_seen > self.max_quantifier_depth {
            // Demoted to Info: per-file depth tracking cannot distinguish between
            // independent definitions and actual nesting. Deep quantifiers are often
            // inherent to specifications (e.g., FStar.Classical, FStar.Pervasives).
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST007,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(max_depth_line, 1),
                message: format!(
                    "Quantifier nesting depth {} exceeds threshold {}. \
                     Deep nesting causes exponential Z3 search space. \
                     Consider splitting into separate lemmas.",
                    max_depth_seen, self.max_quantifier_depth
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for large match expressions.
    ///
    /// Each match branch creates a case split in Z3, and many branches
    /// lead to proof state explosion.
    fn check_large_match(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut in_match = false;
        let mut match_start_line = 0;
        let mut branch_count = 0;
        let mut brace_depth: i32 = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            // Track brace depth for scope
            brace_depth += line.matches('{').count() as i32;
            brace_depth -= line.matches('}').count() as i32;
            brace_depth = std::cmp::max(0, brace_depth);

            if MATCH_START.is_match(line) {
                in_match = true;
                match_start_line = line_num;
                branch_count = 0;
            }

            if in_match && MATCH_BRANCH.is_match(line) {
                branch_count += 1;
            }

            // End match when we see another top-level definition
            if in_match && line_num > match_start_line + 2 {
                let trimmed = line.trim();
                if (trimmed.starts_with("let ")
                    || trimmed.starts_with("val ")
                    || trimmed.starts_with("type "))
                    && !trimmed.contains("match")
                {
                    if branch_count > self.max_match_branches {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST007,
                            severity: DiagnosticSeverity::Info,
                            file: file.to_path_buf(),
                            range: Range::point(match_start_line, 1),
                            message: format!(
                                "Match expression with {} branches exceeds threshold {}. \
                                 Consider grouping cases or using helper functions.",
                                branch_count, self.max_match_branches
                            ),
                            fix: None,
                        });
                    }
                    in_match = false;
                }
            }
        }

        // Handle match at end of file
        if in_match && branch_count > self.max_match_branches {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST007,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(match_start_line, 1),
                message: format!(
                    "Match expression with {} branches exceeds threshold {}. \
                     Consider grouping cases or using helper functions.",
                    branch_count, self.max_match_branches
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for wildcard patterns in non-last position.
    ///
    /// A wildcard `_` pattern matches everything, so any branches after it
    /// are unreachable dead code. This is a logic error that also wastes Z3
    /// effort on case analysis that can never execute.
    ///
    /// Uses indent-aware match nesting to avoid confusing branches from inner
    /// match expressions with branches from outer match expressions.
    fn check_wildcard_in_non_last(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Track match nesting: each entry = (match_indent, wildcard_line, branches_after)
        struct MatchState {
            indent: usize,
            wildcard_line: Option<usize>,
            branches_after_wildcard: usize,
        }

        let mut match_stack: Vec<MatchState> = Vec::new();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();

            if trimmed.is_empty() {
                continue;
            }

            let indent = line.len() - trimmed.len();

            // Reset on top-level definitions
            if indent == 0
                && (trimmed.starts_with("let ") || trimmed.starts_with("val ") || trimmed.starts_with("type "))
                && !trimmed.contains("match")
            {
                // Flush pending diagnostics from remaining stack entries
                for state in match_stack.drain(..) {
                    if let Some(wc_line) = state.wildcard_line {
                        if state.branches_after_wildcard > 0 {
                            diagnostics.push(Self::wildcard_diagnostic(file, wc_line, state.branches_after_wildcard));
                        }
                    }
                }
                continue;
            }

            // Pop match contexts that are at same or deeper indent when we return
            // to their level (meaning the match is done)
            while let Some(top) = match_stack.last() {
                // A branch `|` at the match's indent level belongs to that match -- don't pop
                if trimmed.starts_with('|') && indent >= top.indent {
                    break;
                }
                // Non-branch line at or below the match's indent means the match ended
                if !trimmed.starts_with('|') && indent <= top.indent && !MATCH_START.is_match(line) {
                    let state = match_stack.pop().unwrap();
                    if let Some(wc_line) = state.wildcard_line {
                        if state.branches_after_wildcard > 0 {
                            diagnostics.push(Self::wildcard_diagnostic(file, wc_line, state.branches_after_wildcard));
                        }
                    }
                } else {
                    break;
                }
            }

            // New match expression
            if MATCH_START.is_match(line) {
                match_stack.push(MatchState {
                    indent,
                    wildcard_line: None,
                    branches_after_wildcard: 0,
                });
            }

            // Check branch lines -- attribute them to the innermost match whose
            // indent is <= this branch's indent
            if MATCH_BRANCH.is_match(line) {
                // Find the innermost (topmost on stack) match this branch belongs to
                if let Some(state) = match_stack.last_mut() {
                    if state.wildcard_line.is_some() {
                        state.branches_after_wildcard += 1;
                    } else if WILDCARD_BRANCH.is_match(line) {
                        state.wildcard_line = Some(line_num);
                    }
                }
            }
        }

        // Flush remaining stack
        for state in match_stack.drain(..) {
            if let Some(wc_line) = state.wildcard_line {
                if state.branches_after_wildcard > 0 {
                    diagnostics.push(Self::wildcard_diagnostic(file, wc_line, state.branches_after_wildcard));
                }
            }
        }

        diagnostics
    }

    /// Build a wildcard-in-non-last diagnostic.
    fn wildcard_diagnostic(file: &Path, wc_line: usize, branches_after: usize) -> Diagnostic {
        Diagnostic {
            rule: RuleCode::FST007,
            severity: DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: Range::point(wc_line, 1),
            message: format!(
                "Wildcard `_` pattern is not the last branch ({} branch{} after it \
                 are unreachable). Move `_` to the last position or remove dead branches.",
                branches_after,
                if branches_after == 1 { "" } else { "es" }
            ),
            fix: None,
        }
    }

    /// Check for duplicate match arms with identical patterns.
    ///
    /// Duplicate patterns mean the second one is unreachable dead code.
    /// Even if the RHS differs, the first matching branch wins in F*.
    ///
    /// Uses indent-aware match nesting to correctly attribute branches to
    /// their enclosing match expression, avoiding false positives when
    /// inner matches share patterns (like `_`) with outer matches.
    fn check_duplicate_match_arms(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Each entry: (match_indent, seen_patterns for that match)
        struct DupMatchState {
            indent: usize,
            seen_patterns: Vec<(String, usize)>,
        }

        let mut match_stack: Vec<DupMatchState> = Vec::new();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();

            if trimmed.is_empty() {
                continue;
            }

            let indent = line.len() - trimmed.len();

            // Reset on top-level definitions
            if indent == 0
                && (trimmed.starts_with("let ") || trimmed.starts_with("val ") || trimmed.starts_with("type "))
                && !trimmed.contains("match")
            {
                match_stack.clear();
                continue;
            }

            // Pop match contexts that are done (non-branch line at or below match indent)
            while let Some(top) = match_stack.last() {
                if trimmed.starts_with('|') && indent >= top.indent {
                    break;
                }
                if !trimmed.starts_with('|') && indent <= top.indent && !MATCH_START.is_match(line) {
                    match_stack.pop();
                } else {
                    break;
                }
            }

            // New match expression
            if MATCH_START.is_match(line) {
                match_stack.push(DupMatchState {
                    indent,
                    seen_patterns: Vec::new(),
                });
            }

            // Check branch patterns -- attribute to innermost match
            if let Some(state) = match_stack.last_mut() {
                if let Some(caps) = BRANCH_PATTERN.captures(line) {
                    if let Some(pat_match) = caps.get(1) {
                        let pattern = pat_match.as_str().trim().to_string();
                        let normalized: String = pattern
                            .split_whitespace()
                            .collect::<Vec<_>>()
                            .join(" ");

                        if let Some((_, first_line)) = state.seen_patterns.iter().find(|(p, _)| *p == normalized) {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST007,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::point(line_num, 1),
                                message: format!(
                                    "Duplicate match arm `{}` (first seen on line {}). \
                                     The second branch is unreachable dead code.",
                                    pattern, first_line
                                ),
                                fix: None,
                            });
                        } else {
                            state.seen_patterns.push((normalized, line_num));
                        }
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for nested match expressions.
    ///
    /// Nested matches can cause combinatorial explosion of case analysis in Z3.
    /// However, we need to be smart about what we warn on to reduce false positives:
    ///
    /// - Depth 2 with DIFFERENT discriminants: Very common, usually fine (no warning)
    /// - Depth 3+: Always concerning due to exponential case splits (Info)
    /// - Same discriminant at multiple levels: Suspicious pattern (Warning)
    ///
    /// Example that should NOT warn (common pattern):
    /// ```fstar
    /// match x with
    /// | None -> 0
    /// | Some a -> match y with  // Different variable y - fine at depth 2
    ///   | None -> a
    ///   | Some b -> a + b
    /// ```
    ///
    /// Example that SHOULD warn:
    /// ```fstar
    /// match x with
    /// | Some _ -> match x with  // Same variable x - suspicious!
    ///   | _ -> ...
    /// ```
    fn check_nested_match(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Track match nesting with discriminants
        struct MatchContext {
            line: usize,
            indent: usize,
            discriminant: String,
        }

        let mut match_stack: Vec<MatchContext> = Vec::new();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();

            // Skip comment lines
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Calculate indentation level
            let indent = line.len() - line.trim_start().len();

            // Check if this is a new top-level definition (reset context)
            let is_new_toplevel_def = indent == 0
                && (trimmed.starts_with("let ")
                    || trimmed.starts_with("val ")
                    || trimmed.starts_with("type "));

            if is_new_toplevel_def && !match_stack.is_empty() {
                match_stack.clear();
            }

            // Pop match contexts when returning to lower indentation
            while let Some(ctx) = match_stack.last() {
                if !trimmed.is_empty()
                    && indent <= ctx.indent
                    && line_num > ctx.line
                    && !trimmed.starts_with('|')
                    && !trimmed.starts_with("->")
                {
                    match_stack.pop();
                } else {
                    break;
                }
            }

            // Check for match expression start - extract discriminant
            if let Some(caps) = MATCH_START.captures(line) {
                let discriminant = caps
                    .get(1)
                    .map(|m| m.as_str().to_string())
                    .unwrap_or_default();

                let depth = match_stack.len() + 1;

                // Check if this discriminant was already matched in the stack
                let same_discriminant_matched = match_stack
                    .iter()
                    .any(|ctx| Self::discriminants_overlap(&ctx.discriminant, &discriminant));

                // Determine if we should warn and at what severity
                let should_warn = if same_discriminant_matched {
                    // Matching same variable at multiple levels is suspicious
                    Some((
                        DiagnosticSeverity::Warning,
                        format!(
                            "Nested match on potentially same discriminant '{}' (depth {}). \
                             Matching the same expression at multiple levels may indicate \
                             incomplete pattern matching or opportunity to simplify.",
                            discriminant, depth
                        ),
                    ))
                } else if depth >= 3 {
                    // Deep nesting (3+) is always concerning
                    Some((
                        DiagnosticSeverity::Info,
                        format!(
                            "Deeply nested match expression (depth {}). \
                             Deep nesting causes combinatorial case splitting in Z3. \
                             Consider extracting inner matches to helper functions.",
                            depth
                        ),
                    ))
                } else {
                    // Depth 2 with different discriminants is common and fine - NO WARNING
                    None
                };

                if let Some((severity, message)) = should_warn {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST007,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message,
                        fix: None,
                    });
                }

                match_stack.push(MatchContext {
                    line: line_num,
                    indent,
                    discriminant,
                });
            }
        }

        diagnostics
    }

    /// Check if two discriminants potentially refer to the same value.
    ///
    /// This handles cases like:
    /// - Exact match: "x" == "x"
    /// - Field access: "x.field" and "x" share base variable
    /// - Tuple patterns: "fst x" and "x" share base variable
    fn discriminants_overlap(d1: &str, d2: &str) -> bool {
        // Exact match
        if d1 == d2 {
            return true;
        }

        // Extract the base variable name (handles field access and function application)
        fn extract_base(s: &str) -> &str {
            // Handle field access: x.field -> x
            let s = if let Some(pos) = s.find('.') {
                &s[..pos]
            } else {
                s
            };

            // Handle function application like "fst x" -> "x"
            // Take the last word as the likely variable
            s.split_whitespace().last().unwrap_or(s)
        }

        let base1 = extract_base(d1);
        let base2 = extract_base(d2);

        // Same base variable indicates potential overlap
        base1 == base2
    }

    /// Check for recursive functions without decreases clause.
    ///
    /// Without explicit decreases, F* must infer termination. For simple
    /// structural recursion (recursing on a smaller argument), F* handles
    /// this well. Only non-obvious termination patterns benefit from
    /// explicit decreases clauses.
    ///
    /// This check is conservative:
    /// - Skips .fst files that have corresponding .fsti interfaces (decreases in interface)
    /// - Only issues Info-level suggestions, not warnings
    /// - Recognizes common structural recursion patterns
    fn check_recursive_without_decreases(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Check if this is a .fst file with a corresponding .fsti
        // In that case, the decreases clause is typically in the interface
        let has_interface = if file.extension().is_some_and(|e| e == "fst") {
            let fsti_path = file.with_extension("fsti");
            fsti_path.exists()
        } else {
            false
        };

        // If there's an interface file, skip this check entirely
        // The decreases clause should be in the interface
        if has_interface {
            return diagnostics;
        }

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            if let Some(caps) = LET_REC.captures(line) {
                let func_name = caps.get(1).map(|m| m.as_str()).unwrap_or("unknown");

                // Look for decreases clause within next 10 lines or until next definition
                let mut found_decreases = false;
                let search_end = std::cmp::min(line_idx + 10, lines.len());

                for check_line in &lines[line_idx..search_end] {
                    if DECREASES_CLAUSE.is_match(check_line) {
                        found_decreases = true;
                        break;
                    }
                    // Stop at next definition
                    if *check_line != *line
                        && (check_line.trim().starts_with("let ")
                            || check_line.trim().starts_with("val ")
                            || check_line.trim().starts_with("type "))
                    {
                        break;
                    }
                }

                if !found_decreases {
                    // Check if this looks like simple structural recursion
                    // (recursion on obvious decreasing argument)
                    if self.looks_like_structural_recursion(&lines, line_idx, func_name) {
                        continue; // Skip - F* handles this well
                    }

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST007,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "Recursive function `{}` has no explicit decreases clause. \
                             F* can often infer termination, but explicit (decreases ...) \
                             helps when inference struggles.",
                            func_name
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check if a recursive function looks like simple structural recursion.
    ///
    /// Patterns that F* handles well without explicit decreases:
    /// - Recursion on list tail: `f tl`, `f (List.tl l)`
    /// - Recursion on predecessor: `f (n - 1)`, `f (x - 1)`
    /// - Recursion with hi-lo pattern: `f lo (hi - 1)`, `f (lo + 1) hi`
    fn looks_like_structural_recursion(
        &self,
        lines: &[&str],
        start_idx: usize,
        func_name: &str,
    ) -> bool {
        // Look at the function body (next few lines)
        let search_end = std::cmp::min(start_idx + 15, lines.len());
        let body: String = lines[start_idx..search_end].join("\n");

        // Check for common structural recursion patterns
        let structural_patterns = [
            // List recursion: func tl, func (List.tl x), func xs
            format!(r"{}\s+tl\b", func_name),
            format!(r"{}\s+\(List\.tl", func_name),
            format!(r"{}\s+xs\b", func_name),
            // Natural number recursion: func (n - 1), func (x - 1)
            format!(r"{}\s+\([a-z_]+\s*-\s*1\)", func_name),
            // Range recursion: func (lo + 1) hi, func lo (hi - 1)
            format!(r"{}\s+\([a-z_]+\s*\+\s*1\)\s+[a-z_]+", func_name),
            format!(r"{}\s+[a-z_]+\s+\([a-z_]+\s*-\s*1\)", func_name),
        ];

        for pattern in &structural_patterns {
            if let Ok(re) = Regex::new(pattern) {
                if re.is_match(&body) {
                    return true;
                }
            }
        }

        false
    }

    /// Check for complex assert statements without tactic guidance.
    ///
    /// F* has several assert variants:
    /// - `assert_norm (...)` - forces normalization, often necessary (no warning)
    /// - `assert (...) by (...)` - has explicit tactic (no warning)
    /// - `assert_by_tactic` - has explicit tactic (no warning)
    /// - `assert (...)` with quantifiers or complex expressions - may cause Z3 difficulty
    ///
    /// We only warn about plain asserts containing quantifiers (forall/exists)
    /// or very long conditions that suggest complexity.
    fn check_complex_asserts(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();

            // Skip comment lines
            if trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }

            // Skip assert_norm - these are intentional normalization hints
            if ASSERT_NORM_CALL_RE.is_match(line) {
                continue;
            }

            // Skip assert_by_tactic - has explicit tactic guidance
            if ASSERT_BY_TACTIC_RE.is_match(line) {
                continue;
            }

            // Check for plain assert
            if PLAIN_ASSERT.is_match(line) {
                // Check if this assert has a `by` clause on this or next line
                let context_end = std::cmp::min(line_idx + 2, lines.len());
                let context: String = lines[line_idx..context_end].join(" ");

                if ASSERT_BY.is_match(&context) || context.contains(") by ") {
                    continue; // Has tactic guidance
                }

                // Check if the assert contains quantifiers
                let has_quantifier = QUANTIFIER_KEYWORD.is_match(line);

                // Check if the condition spans multiple lines (complex expression)
                let is_multiline = trimmed.ends_with('(')
                    || (!trimmed.contains(");") && !trimmed.contains(") ;"));

                // Only warn if the assert contains a quantifier
                // Complex multiline asserts without quantifiers are usually fine
                if has_quantifier {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST007,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: "assert with quantifier may cause Z3 difficulty. \
                             Consider using `assert (...) by (tactic)` for explicit proof guidance, \
                             or add intermediate lemmas."
                            .to_string(),
                        fix: None,
                    });
                } else if is_multiline {
                    // Check if the full assertion (multiline) contains quantifiers
                    let search_end = std::cmp::min(line_idx + 5, lines.len());
                    let full_assert: String = lines[line_idx..search_end].join(" ");

                    if QUANTIFIER_KEYWORD.is_match(&full_assert) {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST007,
                            severity: DiagnosticSeverity::Info,
                            file: file.to_path_buf(),
                            range: Range::point(line_num, 1),
                            message: "assert with quantifier may cause Z3 difficulty. \
                                 Consider using `assert (...) by (tactic)` for explicit proof guidance."
                                .to_string(),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for high z3rlimit settings.
    ///
    /// High rlimits are often a symptom of proof complexity issues rather
    /// than a proper solution.
    fn check_z3rlimit(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let line_num = line_idx + 1;

            // Check #set-options pattern
            if let Some(caps) = Z3RLIMIT.captures(line) {
                if let Some(limit_match) = caps.get(1) {
                    if let Ok(limit) = limit_match.as_str().parse::<u32>() {
                        if limit > self.max_z3rlimit {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST007,
                                severity: DiagnosticSeverity::Info,
                                file: file.to_path_buf(),
                                range: Range::point(line_num, 1),
                                message: format!(
                                    "High z3rlimit {} exceeds threshold {}. \
                                     Consider splitting the proof or adding intermediate lemmas.",
                                    limit, self.max_z3rlimit
                                ),
                                fix: None,
                            });
                        }
                    }
                }
            }

            // Also check inline z3rlimit (in attributes)
            if !Z3RLIMIT.is_match(line) {
                if let Some(caps) = Z3RLIMIT_INLINE.captures(line) {
                    if let Some(limit_match) = caps.get(1) {
                        if let Ok(limit) = limit_match.as_str().parse::<u32>() {
                            if limit > self.max_z3rlimit {
                                diagnostics.push(Diagnostic {
                                    rule: RuleCode::FST007,
                                    severity: DiagnosticSeverity::Info,
                                    file: file.to_path_buf(),
                                    range: Range::point(line_num, 1),
                                    message: format!(
                                        "High z3rlimit {} exceeds threshold {}. \
                                         Consider splitting the proof or adding intermediate lemmas.",
                                        limit, self.max_z3rlimit
                                    ),
                                    fix: None,
                                });
                            }
                        }
                    }
                }
            }
        }

        diagnostics
    }
}

impl Default for Z3ComplexityRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for Z3ComplexityRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST007
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_quantifiers_without_triggers(file, content));
        diagnostics.extend(self.check_nonlinear_arithmetic(file, content));
        diagnostics.extend(self.check_quantifier_depth(file, content));
        diagnostics.extend(self.check_large_match(file, content));
        diagnostics.extend(self.check_wildcard_in_non_last(file, content));
        diagnostics.extend(self.check_duplicate_match_arms(file, content));
        diagnostics.extend(self.check_nested_match(file, content));
        diagnostics.extend(self.check_recursive_without_decreases(file, content));
        diagnostics.extend(self.check_complex_asserts(file, content));
        diagnostics.extend(self.check_z3rlimit(file, content));

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn make_path() -> PathBuf {
        PathBuf::from("test.fst")
    }

    // ========== Quantifier trigger tests ==========

    #[test]
    fn test_quantifier_without_trigger_in_lemma() {
        let rule = Z3ComplexityRule::new();
        // Lemma with forall but no trigger - should warn
        let content = "let lemma_foo (x:int) : Lemma (forall (y:int). y >= 0) = ()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("trigger")));
    }

    #[test]
    fn test_quantifier_with_smtpat() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let lemma_foo (x:int) : Lemma
  (forall (y:int). y >= 0)
  [SMTPat (y >= 0)]
= ()
"#;
        let diags = rule.check(&make_path(), content);
        // Should not warn - SMTPat trigger is present
        assert!(!diags.iter().any(|d| d.message.contains("trigger")));
    }

    #[test]
    fn test_quantifier_with_inline_pattern() {
        let rule = Z3ComplexityRule::new();
        // F* inline pattern trigger syntax
        let content = r#"
let lemma_foo (x:int) : Lemma
  (forall (y:int). {:pattern (f y)} f y >= 0)
= ()
"#;
        let diags = rule.check(&make_path(), content);
        // Should not warn - inline pattern trigger is present
        assert!(!diags.iter().any(|d| d.message.contains("trigger")));
    }

    #[test]
    fn test_quantifier_in_refinement_type() {
        let rule = Z3ComplexityRule::new();
        // Quantifier inside refinement type - should NOT warn
        let content = r#"
val create:
    #a:Type
  -> len:size_nat
  -> init:a ->
  Tot (s:lseq a len{forall (i:nat). i < len ==> index s i == init})
"#;
        let diags = rule.check(&make_path(), content);
        // Quantifiers in refinement types don't need triggers
        assert!(!diags.iter().any(|d| d.message.contains("trigger")));
    }

    #[test]
    fn test_quantifier_in_val_declaration() {
        let rule = Z3ComplexityRule::new();
        // Quantifier in val declaration (specification) - should NOT warn
        let content = r#"
val lemma_forall_intro: p:(a -> prop) ->
  Lemma (requires (forall (x:a). p x))
        (ensures True)
"#;
        let diags = rule.check(&make_path(), content);
        // val declarations are specification context
        assert!(!diags.iter().any(|d| d.message.contains("trigger")));
    }

    #[test]
    fn test_exists_without_trigger() {
        let rule = Z3ComplexityRule::new();
        let content = "let lemma_exists (x:int) : Lemma (exists (y:int). y > x) = ()";
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("exists") && d.message.contains("trigger")));
    }

    #[test]
    fn test_quantifier_with_smtpator() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let lemma_or (x:int) : Lemma
  (forall (y:int). y >= 0 \/ y < 0)
  [SMTPatOr [[SMTPat (y >= 0)]; [SMTPat (y < 0)]]]
= ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("trigger")));
    }

    // ========== Non-linear arithmetic tests ==========

    #[test]
    fn test_nonlinear_arithmetic() {
        let rule = Z3ComplexityRule::new();
        let content = "let result = a * b + c";
        let diags = rule.check(&make_path(), content);
        // Non-linear arithmetic is always Info level (too noisy for Warning)
        assert!(diags.iter().any(|d| d.message.contains("Non-linear") && d.severity == DiagnosticSeverity::Info));
    }

    #[test]
    fn test_squaring_allowed() {
        let rule = Z3ComplexityRule::new();
        let content = "let square = x * x";
        let diags = rule.check(&make_path(), content);
        // x * x should not trigger warning
        assert!(!diags.iter().any(|d| d.message.contains("x * x")));
    }

    #[test]
    fn test_safe_vars_multiplication() {
        let rule = Z3ComplexityRule::new();
        let content = "let index = i * len";
        let diags = rule.check(&make_path(), content);
        // Should produce Info level, not Warning
        let info_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Non-linear") && d.severity == DiagnosticSeverity::Info)
            .collect();
        assert!(!info_diags.is_empty());
    }

    #[test]
    fn test_constant_multiplication_ignored() {
        let rule = Z3ComplexityRule::new();
        // Numeric literals should not trigger
        let content = "let result = 2 * x";
        let diags = rule.check(&make_path(), content);
        // 2 is numeric, so this should not warn
        assert!(!diags.iter().any(|d| d.message.contains("2 * x")));
    }

    // ========== z3rlimit tests ==========

    #[test]
    fn test_high_z3rlimit() {
        let rule = Z3ComplexityRule::new();
        let content = r#"#set-options "--z3rlimit 500""#;
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("z3rlimit 500")));
    }

    #[test]
    fn test_acceptable_z3rlimit() {
        let rule = Z3ComplexityRule::new();
        let content = r#"#set-options "--z3rlimit 50""#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("z3rlimit")));
    }

    #[test]
    fn test_z3rlimit_boundary() {
        let rule = Z3ComplexityRule::new();
        // Exactly at threshold should not warn
        let content = r#"#set-options "--z3rlimit 100""#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("z3rlimit")));

        // Just over threshold should warn
        let content2 = r#"#set-options "--z3rlimit 101""#;
        let diags2 = rule.check(&make_path(), content2);
        assert!(diags2.iter().any(|d| d.message.contains("z3rlimit 101")));
    }

    // ========== Recursive without decreases tests ==========

    #[test]
    fn test_recursive_structural_no_warning() {
        let rule = Z3ComplexityRule::new();
        // Simple structural recursion on (n - 1) - F* handles this well
        let content = r#"
let rec factorial (n:nat) : nat =
  if n = 0 then 1
  else n * factorial (n - 1)
"#;
        let diags = rule.check(&make_path(), content);
        // Structural recursion should NOT warn
        assert!(!diags.iter().any(|d| d.message.contains("decreases")));
    }

    #[test]
    fn test_recursive_list_structural_no_warning() {
        let rule = Z3ComplexityRule::new();
        // Structural recursion on list tail
        let content = r#"
let rec length #a (l:list a) : nat =
  match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl
"#;
        let diags = rule.check(&make_path(), content);
        // Structural recursion on tl should NOT warn
        assert!(!diags.iter().any(|d| d.message.contains("decreases")));
    }

    #[test]
    fn test_recursive_complex_should_warn() {
        let rule = Z3ComplexityRule::new();
        // Non-obvious recursion pattern without structural pattern - should warn
        // This function uses a computed recursive argument, not simple decrement
        let content = r#"
let rec collatz (n:pos) : nat =
  if n = 1 then 0
  else if n % 2 = 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)
"#;
        let diags = rule.check(&make_path(), content);
        // Complex recursion (no structural pattern) should warn
        assert!(diags.iter().any(|d| d.message.contains("decreases")));
    }

    #[test]
    fn test_recursive_with_decreases() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let rec factorial (n:nat) : nat
  (decreases n)
= if n = 0 then 1
  else n * factorial (n - 1)
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("decreases")));
    }

    #[test]
    fn test_recursive_with_decreases_braces() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let rec length #a (l:list a) : nat
  decreases { l }
= match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("decreases")));
    }

    #[test]
    fn test_recursive_range_pattern() {
        let rule = Z3ComplexityRule::new();
        // Range recursion: lo+1, hi-1 patterns
        let content = r#"
let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)
"#;
        let diags = rule.check(&make_path(), content);
        // Should recognize (lo + 1) hi pattern as structural
        assert!(!diags.iter().any(|d| d.message.contains("decreases")));
    }

    // ========== Deep quantifier nesting tests ==========

    #[test]
    fn test_deep_quantifier_nesting() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let deep_nesting : Lemma
  (forall (x:int). forall (y:int). forall (z:int). forall (w:int). x + y + z + w >= 0)
= ()
"#;
        let diags = rule.check(&make_path(), content);
        // Quantifier nesting is Info level (too noisy for Warning on real codebases)
        assert!(diags.iter().any(|d|
            d.message.contains("nesting depth") && d.message.contains("exceeds")
            && d.severity == DiagnosticSeverity::Info
        ));
    }

    #[test]
    fn test_acceptable_quantifier_nesting() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let shallow_nesting : Lemma
  (forall (x:int). forall (y:int). x + y >= 0)
= ()
"#;
        let diags = rule.check(&make_path(), content);
        // Depth 2 should be acceptable (threshold is 3)
        assert!(!diags.iter().any(|d| d.message.contains("nesting depth")));
    }

    #[test]
    fn test_mixed_quantifier_nesting() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let mixed_quantifiers : Lemma
  (forall (x:int). exists (y:int). forall (z:int). exists (w:int). x < y /\ z < w)
= ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("nesting depth")));
    }

    // ========== Large match tests ==========

    #[test]
    fn test_large_match() {
        let rule = Z3ComplexityRule::new();
        // Create a match with more than 10 branches (new default threshold)
        let mut content = String::from("let big_match x = match x with\n");
        for i in 0..15 {
            content.push_str(&format!("  | Case{} -> {}\n", i, i));
        }
        let diags = rule.check(&make_path(), &content);
        assert!(diags.iter().any(|d| d.message.contains("branches")));
    }

    #[test]
    fn test_acceptable_match() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let small_match x = match x with
  | None -> 0
  | Some y -> y
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("branches")));
    }

    // ========== Nested match tests ==========

    #[test]
    fn test_nested_match_depth2_different_discriminants_no_warning() {
        let rule = Z3ComplexityRule::new();
        // Depth 2 with different discriminants (x and y) should NOT warn
        let content = r#"
let nested_match x y = match x with
  | None -> 0
  | Some a ->
    match y with
      | None -> a
      | Some b -> a + b
"#;
        let diags = rule.check(&make_path(), content);
        // Should NOT warn for depth 2 with different discriminants
        assert!(!diags.iter().any(|d| d.message.contains("match")));
    }

    #[test]
    fn test_nested_match_depth3_warns() {
        let rule = Z3ComplexityRule::new();
        // Depth 3 should always warn regardless of discriminants
        let content = r#"
let triple_match x y z = match x with
  | None -> 0
  | Some a ->
    match y with
      | None -> a
      | Some b ->
        match z with
          | None -> a + b
          | Some c -> a + b + c
"#;
        let diags = rule.check(&make_path(), content);
        // Should detect exactly 1 warning at depth 3 (not depth 2)
        let nested_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Deeply nested match"))
            .collect();
        assert_eq!(nested_diags.len(), 1);
        assert!(nested_diags[0].message.contains("depth 3"));
    }

    #[test]
    fn test_nested_match_same_discriminant_warns() {
        let rule = Z3ComplexityRule::new();
        // Matching the same variable at multiple levels SHOULD warn
        let content = r#"
let suspicious_match x = match x with
  | Some (Some a) ->
    match x with
      | Some _ -> a
      | None -> 0
  | _ -> 0
"#;
        let diags = rule.check(&make_path(), content);
        // Should warn about same discriminant
        assert!(diags.iter().any(|d|
            d.message.contains("same discriminant") && d.severity == DiagnosticSeverity::Warning
        ));
    }

    #[test]
    fn test_non_nested_match_no_warning() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let first_match x = match x with
  | None -> 0
  | Some a -> a

let second_match y = match y with
  | None -> 1
  | Some b -> b
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("Nested match")));
    }

    // ========== Assert pattern tests ==========

    #[test]
    fn test_assert_norm_no_warning() {
        let rule = Z3ComplexityRule::new();
        // assert_norm is intentional - should not warn
        let content = r#"
let test () =
  assert_norm (forall (x:int). x >= 0);
  ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("assert") && d.message.contains("tactic")));
    }

    #[test]
    fn test_assert_by_no_warning() {
        let rule = Z3ComplexityRule::new();
        // assert with by clause has tactic guidance - should not warn
        let content = r#"
let test () =
  assert (forall (x:int). x >= 0) by (smt());
  ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("assert") && d.message.contains("tactic")));
    }

    #[test]
    fn test_plain_assert_with_quantifier_warns() {
        let rule = Z3ComplexityRule::new();
        // Plain assert with quantifier - should warn
        let content = r#"
let test () =
  assert (forall (x:int). x * x >= 0);
  ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("assert") && d.message.contains("quantifier")));
    }

    #[test]
    fn test_simple_assert_no_warning() {
        let rule = Z3ComplexityRule::new();
        // Simple assert without quantifiers - should not warn
        let content = r#"
let test x =
  assert (x >= 0);
  ()
"#;
        let diags = rule.check(&make_path(), content);
        assert!(!diags.iter().any(|d| d.message.contains("assert") && d.message.contains("quantifier")));
    }

    // ========== Comment filtering tests ==========

    #[test]
    fn test_comments_ignored() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
// forall (x:int). x >= 0
(* exists (y:int). y > 0 *)
let foo = 1
"#;
        let diags = rule.check(&make_path(), content);
        // Comments should not trigger quantifier warnings
        assert!(!diags.iter().any(|d| d.message.contains("SMTPat")));
    }

    // ========== Rule code test ==========

    #[test]
    fn test_rule_code() {
        let rule = Z3ComplexityRule::new();
        assert_eq!(rule.code(), RuleCode::FST007);
    }

    // ========== Configuration tests ==========

    #[test]
    fn test_custom_thresholds() {
        let mut rule = Z3ComplexityRule::new();
        rule.max_quantifier_depth = 2;
        rule.max_match_branches = 3;
        rule.max_z3rlimit = 50;

        // Test stricter quantifier depth (need 4 foralls to exceed depth 2)
        // The depth detection increments when there's another forall ahead
        let content1 =
            r#"(forall (x:int). forall (y:int). forall (z:int). forall (w:int). x >= 0)"#;
        let diags1 = rule.check(&make_path(), content1);
        assert!(diags1.iter().any(|d| d.message.contains("nesting depth")));

        // Test stricter z3rlimit
        let content2 = r#"#set-options "--z3rlimit 60""#;
        let diags2 = rule.check(&make_path(), content2);
        assert!(diags2.iter().any(|d| d.message.contains("z3rlimit 60")));
    }

    // ========== Wildcard in non-last position tests ==========

    #[test]
    fn test_wildcard_last_position_ok() {
        let rule = Z3ComplexityRule::new();
        // Wildcard at last position is fine
        let content = r#"
let classify x = match x with
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"

let y = 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Wildcard")),
            "Wildcard in last position should not warn"
        );
    }

    #[test]
    fn test_wildcard_non_last_warns() {
        let rule = Z3ComplexityRule::new();
        // Wildcard NOT in last position - branches after it are unreachable
        let content = r#"
let classify x = match x with
  | 0 -> "zero"
  | _ -> "other"
  | 1 -> "one"

let y = 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Wildcard") && d.message.contains("unreachable")),
            "Wildcard before other branches should warn: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_wildcard_non_last_counts_branches() {
        let rule = Z3ComplexityRule::new();
        // 3 branches after wildcard
        let content = r#"
let classify x = match x with
  | _ -> "other"
  | 0 -> "zero"
  | 1 -> "one"
  | 2 -> "two"

let y = 1
"#;
        let diags = rule.check(&make_path(), content);
        let wc_diag = diags.iter().find(|d| d.message.contains("Wildcard"));
        assert!(wc_diag.is_some(), "Should detect wildcard in non-last position");
        assert!(
            wc_diag.unwrap().message.contains("3 branches"),
            "Should report 3 unreachable branches, got: {}",
            wc_diag.unwrap().message
        );
    }

    // ========== Duplicate match arms tests ==========

    #[test]
    fn test_duplicate_match_arm_warns() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let classify x = match x with
  | None -> 0
  | Some y -> y
  | None -> 1

let z = 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Duplicate match arm")),
            "Duplicate match arm should warn: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_no_duplicate_arms_ok() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let classify x = match x with
  | None -> 0
  | Some 0 -> 1
  | Some y -> y

let z = 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Duplicate match arm")),
            "Distinct arms should not warn"
        );
    }

    #[test]
    fn test_duplicate_arm_reports_first_line() {
        let rule = Z3ComplexityRule::new();
        let content = r#"
let classify x = match x with
  | Some 1 -> "one"
  | Some 2 -> "two"
  | Some 1 -> "one again"

let z = 1
"#;
        let diags = rule.check(&make_path(), content);
        let dup = diags.iter().find(|d| d.message.contains("Duplicate match arm"));
        assert!(dup.is_some(), "Should detect duplicate arm");
        assert!(
            dup.unwrap().message.contains("first seen on line"),
            "Should reference the first occurrence"
        );
    }

    // ========== Threshold boundary test ==========

    #[test]
    fn test_match_at_exact_threshold_no_warning() {
        let rule = Z3ComplexityRule::new();
        // Exactly 10 branches (threshold) should NOT warn
        let mut content = String::from("let f x = match x with\n");
        for i in 0..10 {
            content.push_str(&format!("  | C{} -> {}\n", i, i));
        }
        let diags = rule.check(&make_path(), &content);
        assert!(
            !diags.iter().any(|d| d.message.contains("branches") && d.message.contains("exceeds")),
            "Exactly at threshold should not warn"
        );
    }

    #[test]
    fn test_match_one_over_threshold_warns() {
        let rule = Z3ComplexityRule::new();
        // 11 branches (threshold + 1) SHOULD warn
        let mut content = String::from("let f x = match x with\n");
        for i in 0..11 {
            content.push_str(&format!("  | C{} -> {}\n", i, i));
        }
        let diags = rule.check(&make_path(), &content);
        assert!(
            diags.iter().any(|d| d.message.contains("branches") && d.message.contains("exceeds")),
            "One over threshold should warn"
        );
    }

    // ========== Nested match FP regression tests ==========

    #[test]
    fn test_nested_match_wildcard_no_false_positive() {
        let rule = Z3ComplexityRule::new();
        // Inner match wildcard should NOT be confused with outer match
        // This was the main source of FPs in ulib
        let content = r#"
let f x lbs = match x with
  | Sg_Let _ lbs -> (
    match lbs with
    | [lb] -> lb
    | _ -> fail "GGG1"
  )
  | Sg_Val nm _ _ -> nm
  | _ -> fail "GGG2"

let y = 1
"#;
        let diags = rule.check(&make_path(), content);
        // Should NOT detect wildcard FP or duplicate `_` across match boundaries
        assert!(
            !diags.iter().any(|d| d.message.contains("Wildcard")),
            "Wildcard in inner match should not FP against outer match: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(
            !diags.iter().any(|d| d.message.contains("Duplicate match arm")),
            "Duplicate `_` across match boundaries should not FP: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_nested_match_duplicate_no_false_positive() {
        let rule = Z3ComplexityRule::new();
        // Two nested matches each with `_ ->` should NOT trigger duplicate arm
        let content = r#"
let collect_arr' bs c =
    match c with
    | C_Total t ->
        begin match inspect t with
        | Tv_Arrow b c ->
            collect_arr' (b::bs) c
        | _ ->
            (bs, c)
        end
    | _ -> (bs, c)

let y = 1
"#;
        let diags = rule.check(&make_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Duplicate match arm")),
            "Inner/outer `_` should not be duplicates: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(
            !diags.iter().any(|d| d.message.contains("Wildcard")),
            "No wildcard FP for nested match: {:?}",
            diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }
}
