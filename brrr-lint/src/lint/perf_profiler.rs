//! FST016: Verification performance profiler.
//!
//! Detects patterns that cause slow verification:
//! - High fuel/ifuel requirements
//! - Large contexts
//! - Timeout-prone patterns
//!
//! This rule performs static analysis to identify code patterns that commonly
//! lead to slow F* verification times, providing actionable hints for optimization.

use regex::Regex;
use std::path::Path;
use std::sync::LazyLock;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};

/// Compile a regex at first use. Panics at runtime if the pattern is invalid.
macro_rules! re {
    ($pat:expr) => {
        LazyLock::new(|| Regex::new($pat).expect(concat!("invalid regex: ", $pat)))
    };
}

/// Matches --fuel N settings in push-options or other directives.
static FUEL_SETTING: LazyLock<Regex> = re!(r#"--fuel\s+(\d+)"#);

/// Matches --ifuel N settings.
static IFUEL_SETTING: LazyLock<Regex> = re!(r#"--ifuel\s+(\d+)"#);

/// Matches --z3rlimit N settings.
static RLIMIT_SETTING: LazyLock<Regex> = re!(r#"--z3rlimit\s+(\d+)"#);

/// Matches --quake option indicating proof instability testing.
static QUAKE_OPTION: LazyLock<Regex> = re!(r"--quake");

/// Matches --retry option indicating proof flakiness workaround.
static RETRY_OPTION: LazyLock<Regex> = re!(r"--retry");

/// Matches calc (==) blocks which can be expensive for large chains.
#[allow(dead_code)]
static LONG_CALC: LazyLock<Regex> = re!(r"calc\s*\(\s*==\s*\)");

/// Matches assert statements for counting assertion density.
static MANY_ASSERTS: LazyLock<Regex> = re!(r"assert\s*\(");

/// Matches SMTPat annotations (many patterns can slow verification).
static SMTPAT_MANY: LazyLock<Regex> = re!(r"SMTPat");

/// Matches #push-options directives.
static PUSH_OPTIONS: LazyLock<Regex> = re!(r"#push-options");

/// Matches split_queries option.
static SPLIT_QUERIES: LazyLock<Regex> = re!(r"--split_queries");

// === Low*/LowStar-specific performance patterns ===

/// Matches #reset-options (resets all options, may lose optimizations).
static RESET_OPTIONS: LazyLock<Regex> = re!(r"#reset-options");

/// Matches --z3rlimit_factor (multiplier on z3rlimit, can be very expensive).
static RLIMIT_FACTOR: LazyLock<Regex> = re!(r"--z3rlimit_factor\s+(\d+)");

/// Matches --using_facts_from (restricts Z3 context, good for performance).
static USING_FACTS_FROM: LazyLock<Regex> = re!(r"--using_facts_from");

/// Matches --record_options (records hints, good for CI stability).
static RECORD_OPTIONS: LazyLock<Regex> = re!(r"--record_options");

// === Additional performance patterns ===

/// Matches #pop-options directives.
static POP_OPTIONS: LazyLock<Regex> = re!(r"#pop-options");

/// Matches #restart-solver directive.
static RESTART_SOLVER: LazyLock<Regex> = re!(r"#restart-solver");

/// Matches --admit_smt_queries true (disables all SMT checking).
static ADMIT_SMT_QUERIES: LazyLock<Regex> = re!(r"--admit_smt_queries\s+true");

/// Matches --lax flag (lax type checking mode).
static LAX_FLAG: LazyLock<Regex> = re!(r"--lax\b");

/// Matches calc block opening.
#[allow(dead_code)]
static CALC_BLOCK_OPEN: LazyLock<Regex> = re!(r"\bcalc\s*\(");

/// Matches calc step line (== { ... }).
#[allow(dead_code)]
static CALC_STEP_LINE: LazyLock<Regex> = re!(r"^\s*==\s*\{");

/// Matches --no_smt flag.
#[allow(dead_code)]
static NO_SMT_FLAG: LazyLock<Regex> = re!(r"--no_smt\b");

/// Matches #set-options directive (global, not scoped).
static SET_OPTIONS: LazyLock<Regex> = re!(r"#set-options");

/// Matches admit() calls (unconditional proof admission).
static ADMIT_CALL: LazyLock<Regex> = re!(r"\badmit\s*\(\s*\)");

/// Matches assume val declarations (unverified axioms).
static ASSUME_VAL: LazyLock<Regex> = re!(r"^\s*assume\s+val\b");

/// FST016: Performance profiler rule.
///
/// Detects patterns that commonly cause slow verification in F* code:
/// - High fuel settings (> threshold) indicating complex recursion unfolding
/// - High ifuel settings (> threshold) indicating deep inductive reasoning
/// - High z3rlimit values (> threshold) suggesting SMT solver stress
/// - Usage of --quake indicating proof instability
/// - High assertion density suggesting overly complex proof obligations
pub struct PerfProfilerRule {
    /// Threshold above which fuel settings trigger a warning.
    pub fuel_threshold: u32,
    /// Threshold above which ifuel settings trigger a warning.
    pub ifuel_threshold: u32,
    /// Threshold above which z3rlimit settings trigger a warning.
    pub rlimit_threshold: u32,
    /// Threshold for assertion count to trigger module complexity warning.
    pub assert_count_threshold: usize,
}

impl PerfProfilerRule {
    /// Create a new performance profiler rule with default thresholds.
    ///
    /// Default thresholds calibrated against HACL* and real-world F* projects:
    /// - fuel_threshold: 4 (fuel 0-4 is standard practice; >4 is elevated)
    /// - ifuel_threshold: 3 (ifuel 0-2 is standard, 3 is borderline)
    /// - rlimit_threshold: 200 (z3rlimit 50-200 is common for crypto proofs)
    /// - assert_count_threshold: 50
    ///
    /// Severity is proportional to the value:
    /// - fuel 5-6 / ifuel 4: Info, fuel 7+ / ifuel 5+: Warning
    /// - z3rlimit 201-400: Info, 401-600: Warning, 601+: Error
    pub fn new() -> Self {
        Self {
            fuel_threshold: 4,
            ifuel_threshold: 3,
            rlimit_threshold: 200,
            assert_count_threshold: 50,
        }
    }

    /// Create a rule with custom thresholds.
    pub fn with_thresholds(
        fuel_threshold: u32,
        ifuel_threshold: u32,
        rlimit_threshold: u32,
        assert_count_threshold: usize,
    ) -> Self {
        Self {
            fuel_threshold,
            ifuel_threshold,
            rlimit_threshold,
            assert_count_threshold,
        }
    }

    /// Check for high fuel setting on a single line.
    ///
    /// Severity scales with the value:
    /// - threshold+1 to threshold+2: Info (mildly elevated)
    /// - threshold+3 and above: Warning (significantly elevated)
    fn check_fuel(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if let Some(caps) = FUEL_SETTING.captures(line) {
            if let Ok(fuel) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                if fuel > self.fuel_threshold {
                    let severity = if fuel > self.fuel_threshold + 2 {
                        DiagnosticSeverity::Warning
                    } else {
                        DiagnosticSeverity::Info
                    };
                    return Some(Diagnostic {
                        rule: RuleCode::FST016,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "High fuel setting ({}) may indicate proof complexity. \
                             Consider splitting into smaller lemmas or adding explicit hints.",
                            fuel
                        ),
                        fix: None,
                    });
                }
            }
        }
        None
    }

    /// Check for high ifuel setting on a single line.
    ///
    /// Severity scales with the value:
    /// - threshold+1: Info (mildly elevated)
    /// - threshold+2 and above: Warning (significantly elevated)
    fn check_ifuel(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if let Some(caps) = IFUEL_SETTING.captures(line) {
            if let Ok(ifuel) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                if ifuel > self.ifuel_threshold {
                    let severity = if ifuel > self.ifuel_threshold + 1 {
                        DiagnosticSeverity::Warning
                    } else {
                        DiagnosticSeverity::Info
                    };
                    return Some(Diagnostic {
                        rule: RuleCode::FST016,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "High ifuel setting ({}) suggests deep inductive reasoning. \
                             Consider adding explicit inversion lemmas.",
                            ifuel
                        ),
                        fix: None,
                    });
                }
            }
        }
        None
    }

    /// Check for high z3rlimit setting on a single line.
    ///
    /// Severity scales with the value:
    /// - threshold+1 to 2*threshold: Info (elevated but manageable)
    /// - 2*threshold+1 to 3*threshold: Warning (high, likely needs refactoring)
    /// - above 3*threshold: Error (extremely high, proof architecture issue)
    fn check_rlimit(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if let Some(caps) = RLIMIT_SETTING.captures(line) {
            if let Ok(rlimit) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                if rlimit > self.rlimit_threshold {
                    let severity = if rlimit > self.rlimit_threshold * 3 {
                        DiagnosticSeverity::Error
                    } else if rlimit > self.rlimit_threshold * 2 {
                        DiagnosticSeverity::Warning
                    } else {
                        DiagnosticSeverity::Info
                    };
                    return Some(Diagnostic {
                        rule: RuleCode::FST016,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "High z3rlimit ({}) detected. Consider using --split_queries always \
                             or extracting helper lemmas to reduce SMT solver load.",
                            rlimit
                        ),
                        fix: None,
                    });
                }
            }
        }
        None
    }

    /// Check for --quake option indicating proof instability.
    ///
    /// Quake is a legitimate tool for testing proof stability in CI environments.
    /// Only emit a Hint (lowest severity) as an informational note, not a warning.
    fn check_quake(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if QUAKE_OPTION.is_match(line) {
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "Using --quake for proof stability testing. \
                         This is fine for CI; consider removing if proof is now stable."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for --retry option indicating flaky proof workaround.
    ///
    /// Retry is acceptable during development and incremental proving.
    /// Emit as Info rather than Warning to reduce noise.
    fn check_retry(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if RETRY_OPTION.is_match(line) {
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "Using --retry for flaky verification. \
                         Acceptable during development; consider stabilizing for production."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for #reset-options which resets all solver settings.
    ///
    /// In Low* projects (HACL*), #reset-options is common but can be problematic
    /// when it resets carefully-tuned settings. Prefer #set-options for explicit control.
    fn check_reset_options(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if RESET_OPTIONS.is_match(line) && !USING_FACTS_FROM.is_match(line) && !RECORD_OPTIONS.is_match(line) {
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "Using #reset-options resets all solver settings. Consider #set-options \
                         to only change what is needed, or add --using_facts_from to restrict \
                         Z3 context for better performance."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for --admit_smt_queries true (disables ALL verification).
    ///
    /// Demoted to Warning: ulib modules (FStar.Int*.fst, FStar.Char.fsti,
    /// FStar.Tactics.Effect.*) legitimately use this for FFI-backed machine
    /// integer operations and tactic effect definitions where SMT is not needed.
    fn check_admit_smt_queries(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if ADMIT_SMT_QUERIES.is_match(line) {
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "`--admit_smt_queries true` disables ALL SMT verification in scope. \
                         Acceptable for FFI bindings and tactic definitions; \
                         remove before merging proof-critical code to production."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for --lax flag in pragmas.
    fn check_lax_flag(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if LAX_FLAG.is_match(line) {
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "`--lax` enables lax type checking mode, skipping proof obligations. \
                         Remove before production verification."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for high z3rlimit without --split_queries.
    ///
    /// When z3rlimit is very high (> rlimit_threshold), using --split_queries always can
    /// significantly improve verification time by splitting VCs.
    fn check_high_rlimit_no_split(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if let Some(caps) = RLIMIT_SETTING.captures(line) {
            if let Ok(rlimit) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                if rlimit > self.rlimit_threshold && !SPLIT_QUERIES.is_match(line) {
                    return Some(Diagnostic {
                        rule: RuleCode::FST016,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "z3rlimit {} without `--split_queries always`. \
                             Splitting queries can improve verification speed \
                             by breaking large VCs into smaller independent obligations.",
                            rlimit
                        ),
                        fix: None,
                    });
                }
            }
        }
        None
    }

    /// Check for --z3rlimit_factor which multiplies the z3rlimit.
    ///
    /// z3rlimit_factor > 4 is almost always a sign of a proof architecture issue
    /// since it multiplies the already-set z3rlimit.
    fn check_rlimit_factor(&self, file: &Path, line_num: usize, line: &str) -> Option<Diagnostic> {
        if let Some(caps) = RLIMIT_FACTOR.captures(line) {
            if let Ok(factor) = caps.get(1).map_or("", |m| m.as_str()).parse::<u32>() {
                if factor > 4 {
                    let severity = if factor > 8 {
                        DiagnosticSeverity::Warning
                    } else {
                        DiagnosticSeverity::Info
                    };
                    return Some(Diagnostic {
                        rule: RuleCode::FST016,
                        severity,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "High z3rlimit_factor ({}) multiplies the base z3rlimit. \
                             Consider increasing z3rlimit directly or splitting the proof.",
                            factor
                        ),
                        fix: None,
                    });
                }
            }
        }
        None
    }

    /// Check for #set-options used where #push-options/#pop-options should be used.
    ///
    /// `#set-options` applies globally to the rest of the file, which can cause
    /// option leakage to subsequent definitions. HACL* best practice is to use
    /// `#push-options` / `#pop-options` to scope changes to individual proofs.
    ///
    /// Exception: `#set-options` at the very start of a file (first 5 lines)
    /// is a common and legitimate pattern for setting module-wide defaults.
    fn check_set_options_without_push(
        &self,
        file: &Path,
        line_num: usize,
        line: &str,
    ) -> Option<Diagnostic> {
        if SET_OPTIONS.is_match(line) && !PUSH_OPTIONS.is_match(line) {
            // Allow #set-options in the first 5 lines (module-wide defaults)
            if line_num < 5 {
                return None;
            }
            return Some(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(line_num + 1, 1),
                message: "`#set-options` applies globally to the rest of the file. \
                         Prefer `#push-options` / `#pop-options` to scope changes \
                         to individual definitions, preventing option leakage."
                    .to_string(),
                fix: None,
            });
        }
        None
    }

    /// Check for admit() calls which bypass all verification.
    ///
    /// `admit()` unconditionally discharges the current proof obligation
    /// without any verification. This is a development-time escape hatch
    /// and must not appear in production-verified code.
    ///
    /// Severity: Info. In expert-written code (ulib, HACL*), admit() is used
    /// intentionally in FFI wrappers, tactic effect definitions, and experimental
    /// modules. Warning-level would flood these codebases with noise.
    fn check_admit_calls(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if ADMIT_CALL.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST016,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::point(line_idx + 1, 1),
                    message: "`admit()` bypasses all verification for this proof obligation. \
                             Remove before production verification."
                        .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for excessive assume val declarations.
    ///
    /// `assume val` introduces unverified axioms. A few are acceptable
    /// for FFI bindings, but many indicate incomplete verification.
    ///
    /// Threshold: 10 (raised from 5). In ulib and Low*, FFI-heavy modules
    /// (LowStar.Endianness, LowStar.Printf, FStar.Crypto) routinely have
    /// 10-30 assume vals for external C/OCaml bindings.
    ///
    /// Severity: Info. These are architectural decisions, not bugs.
    fn check_assume_val_count(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let assume_count = content
            .lines()
            .filter(|l| {
                let trimmed = l.trim();
                !trimmed.starts_with("//")
                    && !trimmed.starts_with("(*")
                    && ASSUME_VAL.is_match(l)
            })
            .count();

        if assume_count > 10 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "File has {} `assume val` declarations. Excessive unverified axioms \
                     weaken the verification guarantee. Consider proving these or \
                     consolidating into a dedicated assumptions module.",
                    assume_count
                ),
                fix: None,
            });
        }

        diagnostics
    }
}

impl Default for PerfProfilerRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for PerfProfilerRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST016
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            // Skip comment lines
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            // Check fuel settings
            if let Some(diag) = self.check_fuel(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check ifuel settings
            if let Some(diag) = self.check_ifuel(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check z3rlimit settings
            if let Some(diag) = self.check_rlimit(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for quake option
            if let Some(diag) = self.check_quake(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for retry option
            if let Some(diag) = self.check_retry(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for #reset-options (Low* pattern)
            if let Some(diag) = self.check_reset_options(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for high z3rlimit_factor (Low* pattern)
            if let Some(diag) = self.check_rlimit_factor(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for --admit_smt_queries true
            if let Some(diag) = self.check_admit_smt_queries(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for --lax flag
            if let Some(diag) = self.check_lax_flag(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for high rlimit without split_queries
            if let Some(diag) = self.check_high_rlimit_no_split(file, line_num, line) {
                diagnostics.push(diag);
            }

            // Check for #set-options without push/pop scoping
            if let Some(diag) = self.check_set_options_without_push(file, line_num, line) {
                diagnostics.push(diag);
            }
        }

        // Check for push/pop-options balance (file-level)
        let push_count = content.lines()
            .filter(|l| !l.trim().starts_with("//") && !l.trim().starts_with("(*"))
            .filter(|l| PUSH_OPTIONS.is_match(l))
            .count();
        let pop_count = content.lines()
            .filter(|l| !l.trim().starts_with("//") && !l.trim().starts_with("(*"))
            .filter(|l| POP_OPTIONS.is_match(l))
            .count();

        if push_count > pop_count + 1 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "Unbalanced push/pop-options: {} `#push-options` but only {} `#pop-options`. \
                     Leaked options may affect subsequent definitions.",
                    push_count, pop_count
                ),
                fix: None,
            });
        }

        // Check for excessive #restart-solver usage (file-level)
        let restart_count = content.lines()
            .filter(|l| !l.trim().starts_with("//") && !l.trim().starts_with("(*"))
            .filter(|l| RESTART_SOLVER.is_match(l))
            .count();

        if restart_count > 5 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "File uses `#restart-solver` {} times. Frequent solver restarts suggest \
                     Z3 context pollution. Consider splitting into smaller modules.",
                    restart_count
                ),
                fix: None,
            });
        }

        // Check for high assertion density (file-level metric)
        let assert_count = MANY_ASSERTS.find_iter(content).count();
        if assert_count > self.assert_count_threshold {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "File has {} assertions. High assertion density ({} > {}) may slow \
                     verification. Consider splitting into smaller modules.",
                    assert_count, assert_count, self.assert_count_threshold
                ),
                fix: None,
            });
        }

        // Check for many SMTPat annotations (can cause pattern explosion)
        // Threshold 50: ulib math modules (FStar.Math.Lemmas, FStar.Seq.Properties)
        // routinely have 30-50+ patterns. Only flag truly excessive counts.
        let smtpat_count = SMTPAT_MANY.find_iter(content).count();
        if smtpat_count > 50 {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST016,
                severity: DiagnosticSeverity::Info,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "File has {} SMTPat annotations. Many patterns can cause quantifier \
                     instantiation explosion. Review pattern selectivity.",
                    smtpat_count
                ),
                fix: None,
            });
        }

        // Check for admit() calls (file-level)
        diagnostics.extend(self.check_admit_calls(file, content));

        // Check for excessive assume val declarations (file-level)
        diagnostics.extend(self.check_assume_val_count(file, content));

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn test_file() -> PathBuf {
        PathBuf::from("test.fst")
    }

    // ---------------------------------------------------------------
    // Fuel threshold tests
    // ---------------------------------------------------------------

    #[test]
    fn test_fuel_below_threshold_no_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 4
        // fuel 0-4 should produce no warnings (common in real F* code)
        for fuel in [0, 1, 2, 3, 4] {
            let content = format!("#push-options \"--fuel {}\"", fuel);
            let diagnostics = rule.check(&test_file(), &content);
            assert!(
                diagnostics.is_empty(),
                "fuel {} should not trigger a warning",
                fuel
            );
        }
    }

    #[test]
    fn test_fuel_mildly_elevated_is_info() {
        let rule = PerfProfilerRule::new(); // threshold = 4, info for 5-6
        let content = "#push-options \"--fuel 5\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Info);
        assert!(diagnostics[0].message.contains("5"));
    }

    #[test]
    fn test_fuel_high_is_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 4, warning for 7+
        let content = "#push-options \"--fuel 10\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Warning);
        assert!(diagnostics[0].message.contains("10"));
    }

    // ---------------------------------------------------------------
    // Ifuel threshold tests
    // ---------------------------------------------------------------

    #[test]
    fn test_ifuel_below_threshold_no_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 3
        // ifuel 0-3 should produce no warnings (standard in F*)
        for ifuel in [0, 1, 2, 3] {
            let content = format!("#push-options \"--ifuel {}\"", ifuel);
            let diagnostics = rule.check(&test_file(), &content);
            assert!(
                diagnostics.is_empty(),
                "ifuel {} should not trigger a warning",
                ifuel
            );
        }
    }

    #[test]
    fn test_ifuel_mildly_elevated_is_info() {
        let rule = PerfProfilerRule::new(); // threshold = 3, info for 4
        let content = "#push-options \"--ifuel 4\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Info);
        assert!(diagnostics[0].message.contains("4"));
    }

    #[test]
    fn test_ifuel_high_is_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 3, warning for 5+
        let content = "#push-options \"--ifuel 5\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Warning);
        assert!(diagnostics[0].message.contains("5"));
    }

    // ---------------------------------------------------------------
    // z3rlimit threshold tests (the main source of false positives)
    // ---------------------------------------------------------------

    #[test]
    fn test_rlimit_common_values_no_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 200
        // These are all common in crypto proofs and should NOT warn
        for rlimit in [10, 20, 30, 40, 50, 60, 75, 80, 100, 150, 200] {
            let content = format!("#push-options \"--z3rlimit {}\"", rlimit);
            let diagnostics = rule.check(&test_file(), &content);
            assert!(
                diagnostics.is_empty(),
                "z3rlimit {} should not trigger a warning (common in crypto proofs)",
                rlimit
            );
        }
    }

    #[test]
    fn test_rlimit_elevated_is_info() {
        let rule = PerfProfilerRule::new(); // threshold = 200, info for 201-400
        let content = "#push-options \"--z3rlimit 300\"";
        let diagnostics = rule.check(&test_file(), content);
        // High rlimit diagnostic + split_queries suggestion
        assert!(diagnostics.iter().any(|d| d.message.contains("300") && d.severity == DiagnosticSeverity::Info));
    }

    #[test]
    fn test_rlimit_high_is_warning() {
        let rule = PerfProfilerRule::new(); // threshold = 200, warning for 401-600
        let content = "#push-options \"--z3rlimit 500\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("500") && d.severity == DiagnosticSeverity::Warning));
    }

    #[test]
    fn test_rlimit_extreme_is_error() {
        let rule = PerfProfilerRule::new(); // threshold = 200, error for 601+
        let content = "#push-options \"--z3rlimit 2000\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("2000") && d.severity == DiagnosticSeverity::Error));
    }

    #[test]
    fn test_rlimit_boundary_400_is_info() {
        let rule = PerfProfilerRule::new(); // 400 <= 2*200, so Info
        let content = "#push-options \"--z3rlimit 400\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit") && d.severity == DiagnosticSeverity::Info));
    }

    #[test]
    fn test_rlimit_boundary_401_is_warning() {
        let rule = PerfProfilerRule::new(); // 401 > 2*200, so Warning
        let content = "#push-options \"--z3rlimit 401\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit") && d.severity == DiagnosticSeverity::Warning));
    }

    #[test]
    fn test_rlimit_boundary_600_is_warning() {
        let rule = PerfProfilerRule::new(); // 600 <= 3*200, so Warning
        let content = "#push-options \"--z3rlimit 600\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit") && d.severity == DiagnosticSeverity::Warning));
    }

    #[test]
    fn test_rlimit_boundary_601_is_error() {
        let rule = PerfProfilerRule::new(); // 601 > 3*200, so Error
        let content = "#push-options \"--z3rlimit 601\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit") && d.severity == DiagnosticSeverity::Error));
    }

    // ---------------------------------------------------------------
    // Quake and retry tests
    // ---------------------------------------------------------------

    #[test]
    fn test_quake_is_hint() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--quake 3/5\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Hint);
        assert!(diagnostics[0].message.contains("stability"));
    }

    #[test]
    fn test_retry_is_info() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--retry 3\"";
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].severity, DiagnosticSeverity::Info);
        assert!(diagnostics[0].message.contains("retry"));
    }

    // ---------------------------------------------------------------
    // File-level metrics tests
    // ---------------------------------------------------------------

    #[test]
    fn test_many_asserts_detection() {
        let rule = PerfProfilerRule::with_thresholds(5, 3, 300, 5);
        let content = r#"
let test () =
    assert (1 = 1);
    assert (2 = 2);
    assert (3 = 3);
    assert (4 = 4);
    assert (5 = 5);
    assert (6 = 6);
    ()
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("assertions"));
        assert!(diagnostics[0].message.contains("6"));
    }

    #[test]
    fn test_smtpat_count_below_threshold() {
        let rule = PerfProfilerRule::new();
        let mut content = String::new();
        for i in 0..25 {
            content.push_str(&format!(
                "val lemma_{} : x:int -> Lemma (requires True) (ensures True) [SMTPat (x + {})]\n",
                i, i
            ));
        }
        let diagnostics = rule.check(&test_file(), &content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("SMTPat")),
            "25 SMTPat annotations should be below threshold (50)"
        );
    }

    #[test]
    fn test_smtpat_count_above_threshold() {
        let rule = PerfProfilerRule::new();
        let mut content = String::new();
        for i in 0..55 {
            content.push_str(&format!(
                "val lemma_{} : x:int -> Lemma (requires True) (ensures True) [SMTPat (x + {})]\n",
                i, i
            ));
        }
        let diagnostics = rule.check(&test_file(), &content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("SMTPat") && d.message.contains("55")),
            "55 SMTPat annotations should trigger Info"
        );
    }

    // ---------------------------------------------------------------
    // Combined and edge case tests
    // ---------------------------------------------------------------

    #[test]
    fn test_multiple_issues_on_one_line() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--fuel 10 --ifuel 5 --z3rlimit 300 --quake 3/5\"";
        let diagnostics = rule.check(&test_file(), content);
        // fuel, ifuel, rlimit, quake, + split_queries hint
        assert!(diagnostics.len() >= 4);
        assert!(diagnostics.iter().any(|d| d.message.contains("fuel")));
        assert!(diagnostics.iter().any(|d| d.message.contains("ifuel")));
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit")));
        assert!(diagnostics.iter().any(|d| d.message.contains("quake") || d.message.contains("stability")));
    }

    #[test]
    fn test_comments_skipped() {
        let rule = PerfProfilerRule::new();
        let content = r#"
// #push-options "--fuel 10"
(* --fuel 10 *)
let normal () = ()
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_custom_thresholds() {
        let rule = PerfProfilerRule::with_thresholds(2, 1, 50, 10);
        let content = "#push-options \"--fuel 3 --ifuel 2 --z3rlimit 60\"";
        let diagnostics = rule.check(&test_file(), content);
        // All three exceed lower thresholds + possible split_queries hint
        assert!(diagnostics.len() >= 3);
        assert!(diagnostics.iter().any(|d| d.message.contains("fuel")));
        assert!(diagnostics.iter().any(|d| d.message.contains("ifuel")));
        assert!(diagnostics.iter().any(|d| d.message.contains("z3rlimit")));
    }

    #[test]
    fn test_hacl_star_common_pattern_no_warning() {
        // This is the most common pattern in hacl-star: should produce zero warnings
        let rule = PerfProfilerRule::new();
        let content = r#"
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let poly1305_update (ctx: poly_ctx) (block: lbytes 16) : poly_ctx =
    let acc = ctx.acc in
    let r = ctx.r in
    (acc +. encode block) *. r
#pop-options
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_hacl_star_elevated_rlimit_no_warning() {
        // z3rlimit 200 is used 77 times in hacl-star -- must not warn
        let rule = PerfProfilerRule::new();
        let content = r#"
#push-options "--fuel 1 --ifuel 0 --z3rlimit 200"
let lemma_chacha20_quarter_round a b c d s =
    ()
#pop-options
"#;
        let diagnostics = rule.check(&test_file(), content);
        // z3rlimit 200 is at threshold (200), no high rlimit warnings
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("z3rlimit")),
            "z3rlimit 200 should not trigger any z3rlimit-related warnings"
        );
    }

    #[test]
    fn test_severity_proportional_to_value() {
        let rule = PerfProfilerRule::new(); // fuel=4, ifuel=3, rlimit=200

        // Just over threshold: Info
        let d = rule.check_fuel(&test_file(), 0, "--fuel 5").unwrap();
        assert_eq!(d.severity, DiagnosticSeverity::Info);

        // Well over threshold: Warning
        let d = rule.check_fuel(&test_file(), 0, "--fuel 8").unwrap();
        assert_eq!(d.severity, DiagnosticSeverity::Warning);

        // rlimit tiers
        let d = rule.check_rlimit(&test_file(), 0, "--z3rlimit 300").unwrap();
        assert_eq!(d.severity, DiagnosticSeverity::Info);

        let d = rule.check_rlimit(&test_file(), 0, "--z3rlimit 500").unwrap();
        assert_eq!(d.severity, DiagnosticSeverity::Warning);

        let d = rule.check_rlimit(&test_file(), 0, "--z3rlimit 700").unwrap();
        assert_eq!(d.severity, DiagnosticSeverity::Error);
    }

    // ---------------------------------------------------------------
    // Low*/LowStar-specific performance tests
    // ---------------------------------------------------------------

    #[test]
    fn test_reset_options_hint() {
        let rule = PerfProfilerRule::new();
        let content = "#reset-options \"--z3rlimit 50 --fuel 0 --ifuel 0\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("reset-options")),
            "#reset-options should trigger a hint"
        );
    }

    #[test]
    fn test_reset_options_with_using_facts_no_hint() {
        let rule = PerfProfilerRule::new();
        // When --using_facts_from is present, reset-options is intentional optimization
        let content = "#reset-options \"--z3rlimit 300 --fuel 0 --ifuel 1 --using_facts_from '* -FStar.Seq' --record_options\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("reset-options")),
            "#reset-options with --using_facts_from should not trigger hint"
        );
    }

    #[test]
    fn test_rlimit_factor_below_threshold() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--z3rlimit_factor 2\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("z3rlimit_factor")),
            "z3rlimit_factor 2 should not trigger warning"
        );
    }

    #[test]
    fn test_rlimit_factor_high_info() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--z3rlimit_factor 5\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("z3rlimit_factor") && d.severity == DiagnosticSeverity::Info),
            "z3rlimit_factor 5 should trigger info"
        );
    }

    #[test]
    fn test_rlimit_factor_very_high_warning() {
        let rule = PerfProfilerRule::new();
        let content = "#push-options \"--z3rlimit_factor 10\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("z3rlimit_factor") && d.severity == DiagnosticSeverity::Warning),
            "z3rlimit_factor 10 should trigger warning"
        );
    }

    #[test]
    fn test_hacl_curve25519_reset_options_pattern() {
        // Real pattern from Hacl.Impl.Curve25519.AddAndDouble.fst
        // Note: z3rlimit 300 now exceeds default threshold of 200
        let rule = PerfProfilerRule::new();
        let content = "#reset-options \"--z3rlimit 200 --fuel 0 --ifuel 1 --using_facts_from '* -FStar.Seq' --record_options\"";
        let diagnostics = rule.check(&test_file(), content);
        // Should NOT warn about reset-options (has --using_facts_from)
        // Should NOT warn about z3rlimit 200 (at threshold, not above)
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("reset-options") || d.message.contains("High z3rlimit")),
            "HACL* Curve25519 reset-options pattern should not trigger reset-options or high rlimit warnings"
        );
    }

    // ---------------------------------------------------------------
    // NEW: admit_smt_queries tests
    // ---------------------------------------------------------------

    #[test]
    fn test_admit_smt_queries_detected() {
        let rule = PerfProfilerRule::new();
        let content = r#"#set-options "--admit_smt_queries true""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("admit_smt_queries")),
            "Should detect --admit_smt_queries true"
        );
        assert!(
            diagnostics.iter().any(|d| d.severity == DiagnosticSeverity::Warning && d.message.contains("admit_smt_queries")),
            "Should be Warning severity (demoted from Error for ulib compatibility)"
        );
    }

    #[test]
    fn test_admit_smt_queries_false_no_warning() {
        let rule = PerfProfilerRule::new();
        let content = r#"#set-options "--admit_smt_queries false""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("admit_smt_queries")),
            "Should not flag --admit_smt_queries false"
        );
    }

    // ---------------------------------------------------------------
    // NEW: lax flag tests
    // ---------------------------------------------------------------

    #[test]
    fn test_lax_flag_detected() {
        let rule = PerfProfilerRule::new();
        let content = r#"#push-options "--lax""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("lax")),
            "Should detect --lax flag"
        );
    }

    // ---------------------------------------------------------------
    // NEW: push/pop balance tests
    // ---------------------------------------------------------------

    #[test]
    fn test_unbalanced_push_pop() {
        let rule = PerfProfilerRule::new();
        let content = r#"
#push-options "--fuel 2"
let foo x = x + 1
#push-options "--fuel 4"
let bar x = x + 2
#push-options "--fuel 6"
let baz x = x + 3
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("push") && d.message.contains("pop")),
            "Should detect unbalanced push/pop-options (3 push, 0 pop)"
        );
    }

    #[test]
    fn test_balanced_push_pop_no_warning() {
        let rule = PerfProfilerRule::new();
        let content = r#"
#push-options "--fuel 2"
let foo x = x + 1
#pop-options
#push-options "--fuel 4"
let bar x = x + 2
#pop-options
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("Unbalanced")),
            "Balanced push/pop should not trigger warning"
        );
    }

    // ---------------------------------------------------------------
    // NEW: restart-solver frequency tests
    // ---------------------------------------------------------------

    #[test]
    fn test_excessive_restart_solver() {
        let rule = PerfProfilerRule::new();
        let mut content = String::new();
        for _ in 0..7 {
            content.push_str("#restart-solver\nlet foo = 1\n");
        }
        let diagnostics = rule.check(&test_file(), &content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("restart-solver")),
            "Should detect excessive restart-solver usage"
        );
    }

    #[test]
    fn test_few_restart_solver_no_warning() {
        let rule = PerfProfilerRule::new();
        let content = r#"
#restart-solver
let foo x = x + 1
#restart-solver
let bar x = x + 2
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("restart-solver") && d.message.contains("times")),
            "Few restart-solver uses should not trigger warning"
        );
    }

    // ---------------------------------------------------------------
    // NEW: high rlimit without split_queries tests
    // ---------------------------------------------------------------

    #[test]
    fn test_high_rlimit_without_split_queries() {
        let rule = PerfProfilerRule::new();
        let content = r#"#push-options "--z3rlimit 300""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("split_queries")),
            "Should suggest --split_queries for high rlimit"
        );
    }

    #[test]
    fn test_high_rlimit_with_split_queries_no_hint() {
        let rule = PerfProfilerRule::new();
        let content = r#"#push-options "--z3rlimit 300 --split_queries always""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("split_queries") && d.severity == DiagnosticSeverity::Hint),
            "Should not suggest split_queries when already present"
        );
    }

    #[test]
    fn test_low_rlimit_no_split_queries_hint() {
        let rule = PerfProfilerRule::new();
        let content = r#"#push-options "--z3rlimit 50""#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("split_queries")),
            "Low rlimit should not trigger split_queries suggestion"
        );
    }

    // ---------------------------------------------------------------
    // NEW: #set-options without push tests
    // ---------------------------------------------------------------

    #[test]
    fn test_set_options_early_in_file_ok() {
        let rule = PerfProfilerRule::new();
        // #set-options at the top of file (line 0-4) is a common module-wide default
        let content = r#"module Foo
#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let foo x = x
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("set-options") && d.message.contains("push-options")),
            "#set-options at file top should not trigger warning"
        );
    }

    #[test]
    fn test_set_options_mid_file_warns() {
        let rule = PerfProfilerRule::new();
        // #set-options deep in the file leaks to subsequent definitions
        let content = "line1\nline2\nline3\nline4\nline5\n#set-options \"--fuel 2\"\nlet bar = 1";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("set-options") && d.message.contains("push-options")),
            "#set-options mid-file should suggest push-options"
        );
    }

    // ---------------------------------------------------------------
    // NEW: admit() call tests
    // ---------------------------------------------------------------

    #[test]
    fn test_admit_call_detected() {
        let rule = PerfProfilerRule::new();
        let content = r#"
let lemma_foo x : Lemma (x >= 0) =
  admit ()
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("admit()") && d.severity == DiagnosticSeverity::Info),
            "admit() call should be detected as Info"
        );
    }

    #[test]
    fn test_admit_in_comment_ignored() {
        let rule = PerfProfilerRule::new();
        let content = r#"
// admit ()
(* admit () *)
let foo x = x
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("admit()")),
            "admit() in comments should be ignored"
        );
    }

    // ---------------------------------------------------------------
    // NEW: assume val count tests
    // ---------------------------------------------------------------

    #[test]
    fn test_excessive_assume_val() {
        let rule = PerfProfilerRule::new();
        let mut content = String::from("module Foo\n");
        for i in 0..12 {
            content.push_str(&format!("assume val f{} : int -> int\n", i));
        }
        let diagnostics = rule.check(&test_file(), &content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("assume val") && d.severity == DiagnosticSeverity::Info),
            "Excessive assume val (>10) should trigger Info"
        );
    }

    #[test]
    fn test_few_assume_val_ok() {
        let rule = PerfProfilerRule::new();
        let content = r#"
assume val external_func : int -> int
assume val another_func : bool -> bool
let foo x = x
"#;
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("assume val")),
            "Few assume val declarations should not trigger warning"
        );
    }

    // ---------------------------------------------------------------
    // NEW: fuel >4 tests (lowered threshold)
    // ---------------------------------------------------------------

    #[test]
    fn test_fuel_4_is_now_ok() {
        let rule = PerfProfilerRule::new(); // threshold = 4
        let content = "#push-options \"--fuel 4\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("fuel")),
            "fuel 4 should be at threshold, no warning"
        );
    }

    #[test]
    fn test_fuel_5_is_now_info() {
        let rule = PerfProfilerRule::new(); // threshold = 4
        let content = "#push-options \"--fuel 5\"";
        let diagnostics = rule.check(&test_file(), content);
        assert!(
            diagnostics.iter().any(|d| d.message.contains("fuel") && d.severity == DiagnosticSeverity::Info),
            "fuel 5 should be Info with threshold=4"
        );
    }
}
