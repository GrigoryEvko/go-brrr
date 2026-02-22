//! FST017: Security checker for cryptographic code.
//!
//! Detects common cryptographic security issues in F* code:
//!
//! 1. Hardcoded secrets - keys, passwords, tokens embedded in source
//! 2. RawIntTypes usage - may break secret independence guarantees
//! 3. Secret-dependent branches - potential timing side-channel vulnerabilities
//! 4. Buffer operations without bounds verification
//! 5. Key variables without zeroization
//! 6. Nonce/IV initialization issues
//! 7. Division/modulo timing leaks on secrets
//!
//! This rule specifically targets crypto-related files (Hacl*, Crypto*, Spec*).
//!
//! IMPORTANT: This rule distinguishes between PUBLIC and SECRET types in F*:
//!
//! - PUBLIC (safe for branches/division):
//!   - `size_t`, `size_nat` - public size types
//!   - Size operators: `/. `, `%. `, `<. `, `>. `, `=. `, `<>. `, `<=. `, `>=. `
//!   - Variables like `len`, `bLen`, `bBits`, `i`, `j`, `k` (indices/lengths)
//!   - Size literals: `0ul`, `1ul`, `32ul`, etc.
//!
//! - SECRET (requires constant-time operations):
//!   - `uint_t t SEC`, `uint #t #SEC`, `limb t` - secret integers
//!   - Variables named `key`, `secret`, `priv`, or containing these substrings
//!   - Operations on cryptographic values
//!
//! HACL* is designed to be constant-time, and this linter respects that by
//! not flagging valid patterns like `len /. 2ul` or `if i <. len then`.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::LEMMA_RE;

lazy_static! {
    // === Existing patterns ===

    /// Potential secret-dependent branch pattern.
    /// Matches conditionals comparing variables that may contain secrets.
    /// NOTE: This is now more conservative - we check context for public types.
    static ref SECRET_BRANCH: Regex = Regex::new(
        r"if\s+(?:v\s+)?(\w+)\s*(?:=|<>|<|>|<=|>=)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Hardcoded secrets patterns - matches assignments of string literals
    /// to variables with security-sensitive names.
    static ref HARDCODED_KEY: Regex = Regex::new(
        r#"(?:key|secret|password|token)\s*=\s*["'][^"']+["']"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Key usage pattern - tracks where key variables are referenced.
    static ref KEY_USAGE: Regex = Regex::new(r"\bkey\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// RawIntTypes module usage - can break secret independence guarantees
    /// by exposing implementation details or enabling timing attacks.
    static ref RAW_INT_TYPES: Regex = Regex::new(r"\bRawIntTypes\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Constant-time mask operations (GOOD patterns) - indicate proper
    /// side-channel resistant implementations.
    static ref CT_MASK: Regex = Regex::new(r"\b(?:eq_mask|gte_mask|lt_mask|gt_mask|lte_mask|neq_mask)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Secret-indicating variable name patterns.
    /// Base pattern - refined by is_secret_variable() helper function.
    static ref SECRET_VAR_PATTERN: Regex = Regex::new(
        r"\b(\w*(?:key|secret|priv)\w*)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Metadata suffixes that indicate a value is NOT secret (e.g., key_len, secret_size).
    static ref METADATA_SUFFIX: Regex = Regex::new(
        r"(?i)(?:_len|_length|_size|_sz|_bytes|_bits|len$|length$|size$|bits$)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Function name prefixes that indicate a function, not a secret variable.
    static ref FUNCTION_PREFIX: Regex = Regex::new(
        r"^(?:update_|get_|set_|init_|derive_|expand_|clear_|malloc_|blake2_|poly1305_|chacha20_|aead_|hmac_|hash_|encrypt_|decrypt_|sign_|verify_)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // === F* Public Type Patterns (safe for branches/division) ===

    /// Size type operators in F* - these operate on public size_t values.
    /// Examples: `/. `, `%. `, `<. `, `>. `, `=. `, `<>. `, `<=. `, `>=. `
    static ref SIZE_OPERATORS: Regex = Regex::new(
        r"(?:/\.|%\.|<\.|>\.|=\.|<>\.|<=\.|>=\.)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Size literals in F* - public values like `0ul`, `1ul`, `32ul`.
    static ref SIZE_LITERAL: Regex = Regex::new(r"\b\d+ul\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Public size variable names - indices, lengths, bit counts.
    /// These are commonly used in HACL* and are always public.
    static ref PUBLIC_VAR_NAMES: Regex = Regex::new(
        r"\b(?:len|bLen|aLen|cLen|nLen|bBits|nBits|ind|idx|pbits|nbits|table_len|ctx_len)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Loop index variable patterns - typically single letters used in loops.
    /// When used with size operators, these are public.
    static ref LOOP_INDEX: Regex = Regex::new(r"\bfor\s+\d+ul\s+\w+\s+inv").unwrap_or_else(|e| panic!("regex: {e}"));

    /// F* SEC (secret) type annotation - marks secret integers.
    static ref SEC_TYPE: Regex = Regex::new(
        r"(?:uint_t\s+\w+\s+SEC|uint\s+#\w+\s+#SEC|\bSEC\b)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// F* PUB (public) type annotation - marks public integers.
    static ref PUB_TYPE: Regex = Regex::new(
        r"(?:uint_t\s+\w+\s+PUB|uint\s+#\w+\s+#PUB|\bPUB\b)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Size type declarations - these are always public.
    static ref SIZE_TYPE_DECL: Regex = Regex::new(
        r"(?:size_t|size_nat|size_pos)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Mask select operations (constant-time conditional).
    static ref MASK_SELECT: Regex = Regex::new(r"\bmask_select\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Buffer operations patterns ===

    /// Buffer.index without explicit bounds - potential out-of-bounds access.
    static ref BUFFER_INDEX: Regex = Regex::new(r"Buffer\.index\s+\w+\s+(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer.sub slice operation - needs bounds verification.
    static ref BUFFER_SUB: Regex = Regex::new(r"Buffer\.sub\s+\w+\s+(\w+)\s+(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer.blit copy operation - needs bounds on both source and destination.
    static ref BUFFER_BLIT: Regex = Regex::new(r"Buffer\.blit\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Unsafe buffer upd without length check.
    static ref BUFFER_UPD: Regex = Regex::new(r"Buffer\.upd\s+\w+\s+(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Low*/LowStar buffer patterns ===

    /// LowStar.Ignore.ignore on potentially security-sensitive return values.
    /// Pattern: `LowStar.Ignore.ignore <var>`
    /// Ignoring carry/borrow returns from bignum operations can be a security bug.
    static ref LOWSTAR_IGNORE: Regex = Regex::new(
        r"LowStar\.Ignore\.ignore\s+(\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Carry/borrow return value names that should NOT be ignored in crypto code.
    static ref CARRY_BORROW_VAR: Regex = Regex::new(
        r"^(?:c\d*|carry|borrow|overflow)$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer create/alloca without explicit initial value in crypto context.
    /// Uninitialized memory can leak secrets from previous allocations.
    static ref UNINIT_BUFFER: Regex = Regex::new(
        r"(?:create|alloca)\s+\d+ul\s*$"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Direct memory comparison (non-constant-time) in crypto context.
    static ref DIRECT_MEM_COMPARE: Regex = Regex::new(
        r"\b(?:Lib\.ByteBuffer\.buf_eq_mask|buf_eq)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Lib.Buffer lbuffer operations (HACL* style).
    static ref LIB_BUFFER_OP: Regex = Regex::new(
        r"\blbuffer\s+(?:uint8|uint32|uint64|limb)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // === Key/secret lifecycle patterns ===

    /// Key buffer allocation - matches ACTUAL buffer allocations containing secrets.
    /// Pattern: `let key = create/alloca/sub/malloc ...`
    /// This specifically matches buffer creation operations, not function definitions.
    static ref KEY_BUFFER_ALLOC: Regex = Regex::new(
        r"let\s+(\w*(?:key|secret|priv)\w*)\s*=\s*(?:create|alloca|sub|malloc|gcmalloc|B\.create|Buffer\.create)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Names that indicate metadata (length/size), NOT the actual secret.
    /// These suffixes are excluded from key zeroization warnings.
    static ref KEY_METADATA_SUFFIX: Regex = Regex::new(
        r"(?i)(?:_len|_length|_size|_sz|_bytes|_bits|len$|length$|size$)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Function name patterns - prefixes for functions operating on keys.
    /// These are function names, not key buffer variables.
    static ref KEY_FUNCTION_PREFIX: Regex = Regex::new(
        r"^(?:update_|get_|set_|init_|derive_|expand_|clear_|malloc_|blake2_|poly1305_|chacha20_|aead_|hmac_)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Type definition suffix - indicates a type alias, not a variable.
    static ref TYPE_DEF_SUFFIX: Regex = Regex::new(r"(?:_st|_t)$").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Function definition pattern - detects `let name : type -> type` or `val name :`.
    /// These are function definitions, not variable bindings.
    static ref FUNCTION_TYPE_DEF: Regex = Regex::new(
        r"(?:let|val)\s+\w+\s*:\s*[^=]*->"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Memory zeroing function call - should be used to clear secrets.
    static ref MEMZERO: Regex = Regex::new(r"\bmemzero\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Clear function variants for secret cleanup.
    static ref CLEAR_FN: Regex = Regex::new(r"\b(?:clear_\w+|wipe|scrub)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Secret allocation on stack - may leak on early returns.
    /// Matches actual buffer allocation with secret-like content.
    static ref STACK_ALLOC_SECRET: Regex = Regex::new(
        r"let\s+\w*(?:secret|priv)\w*\s*=\s*(?:create|alloca)\s+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // === Nonce/IV patterns ===

    /// Nonce variable detection.
    static ref NONCE_VAR: Regex = Regex::new(r"\bnonce\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// IV (initialization vector) variable detection.
    static ref IV_VAR: Regex = Regex::new(r"\biv\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Counter variable that may be used as nonce.
    static ref COUNTER_VAR: Regex = Regex::new(r"\b(?:counter|ctr)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Random source usage (good pattern for nonce generation).
    static ref RANDOM_SOURCE: Regex = Regex::new(r"(?i)\b(?:random|randombytes|getrandom)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Zero initialization (bad for nonce/IV).
    static ref ZERO_INIT: Regex = Regex::new(r"(?:=|<-)\s*(?:0x0+|0+)\s*$").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Timing side-channel patterns ===

    /// Division by variable (potential timing leak).
    /// NOTE: `/. ` is the PUBLIC size division operator - safe!
    /// Only flag bare `/` without the dot when operating on secrets.
    static ref DIV_BY_VAR: Regex = Regex::new(r"/\s*(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Size division operator (PUBLIC - safe).
    /// In F*, `/. ` operates on size_t values which are public.
    static ref SIZE_DIV: Regex = Regex::new(r"/\.").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Modulo by variable (potential timing leak).
    /// NOTE: `%. ` is the PUBLIC size modulo operator - safe!
    static ref MOD_BY_VAR: Regex = Regex::new(r"%\s*(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Size modulo operator (PUBLIC - safe).
    /// In F*, `%. ` operates on size_t values which are public.
    static ref SIZE_MOD: Regex = Regex::new(r"%\.").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Comparison operators on potential secrets in if conditions.
    /// Must be more specific to avoid false positives on public comparisons.
    static ref SECRET_COMPARISON: Regex = Regex::new(
        r"if\s+.*\b(\w*(?:_key|secret_|_secret|priv_|_priv)\w*)\s*(?:=|<>|<|>|<=|>=)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Public comparison operators in F* (size comparisons - safe).
    /// Examples: `<. `, `>. `, `=. `, `<>. `, `<=. `, `>=. `
    static ref SIZE_COMPARISON: Regex = Regex::new(r"(?:<\.|>\.|=\.|<>\.|<=\.|>=\.)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Early return pattern that may leak information.
    static ref EARLY_RETURN: Regex = Regex::new(r"\breturn\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Short-circuit evaluation on secrets (timing leak).
    static ref SHORT_CIRCUIT: Regex = Regex::new(r"(?:&&|\|\|)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Secret type annotation in function signatures.
    /// Used to detect functions operating on secret data.
    static ref SECRET_PARAM: Regex = Regex::new(
        r"(?:uint_t\s+\w+\s+SEC|limb\s+\w+|lbuffer\s+\(uint_t\s+\w+\s+SEC\))"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // === Safe constant-time operations (GOOD patterns) ===

    /// Constant-time select operations.
    static ref CT_SELECT: Regex = Regex::new(r"\b(?:ct_select|select_constant_time|cmov)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Constant-time comparison operations.
    static ref CT_COMPARE: Regex = Regex::new(
        r"\b(?:ct_compare|constant_time_compare|crypto_verify|verify_\d+)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Constant-time conditional operations.
    static ref CT_COND: Regex = Regex::new(r"\b(?:ct_cond|constant_time_cond)\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Bounds check patterns (GOOD patterns) ===

    /// Explicit length check before buffer operation.
    static ref LENGTH_CHECK: Regex = Regex::new(r"(?:length|len|size)\s*(?:>=|>|<=|<|=)\s*\d+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Assert for bounds verification.
    static ref BOUNDS_ASSERT: Regex = Regex::new(r"assert\s*\(.*(?:length|len|<|>)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Requires clause with length constraint.
    static ref REQUIRES_LEN: Regex = Regex::new(r"requires\s*\{.*(?:length|len)").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Secret-dependent loop bound patterns ===

    /// Loop with bound expression referencing a secret-like variable.
    /// Matches patterns like: `for 0ul secret_len inv`
    /// or `Lib.Loops.for 0ul (v key_rounds)`.
    /// A loop bound that depends on a secret value causes variable-time execution.
    static ref LOOP_WITH_SECRET_BOUND: Regex = Regex::new(
        r"(?:Lib\.Loops\.for|Lib\.LoopCombinators\.repeati?|for\s+\d+ul)\s+.*\b(\w*(?:secret|priv)\w*)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // === Quantifier without pattern in security lemmas ===

    /// Matches `forall` or `exists` quantifiers.
    static ref QUANTIFIER: Regex = Regex::new(r"\b(?:forall|exists)\s+\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches SMTPat annotations (good pattern triggers).
    static ref SMTPAT_IN_LINE: Regex = Regex::new(r"\bSMTPat\b").unwrap_or_else(|e| panic!("regex: {e}"));

    // === Non-linear arithmetic on secrets ===

    /// Multiplication involving secret-named variables.
    /// Non-linear arithmetic `a * b` where either is secret causes
    /// variable-time execution on most CPUs (e.g. mulx takes data-dependent time).
    static ref SECRET_MULTIPLICATION: Regex = Regex::new(
        r"\b(\w*(?:secret|priv)\w*)\s*\*\s*\w+|\w+\s*\*\s*(\w*(?:secret|priv)\w*)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

/// FST017: Security checker for cryptographic F* code.
///
/// Analyzes code for common cryptographic security issues including
/// hardcoded secrets, potential timing vulnerabilities, buffer safety,
/// key lifecycle management, and nonce handling.
pub struct SecurityRule;

impl SecurityRule {
    /// Create a new SecurityRule instance.
    pub fn new() -> Self {
        Self
    }

    /// Check if a file is crypto-related based on its path.
    ///
    /// Returns true for files in HACL*, Crypto, or Spec directories.
    fn is_crypto_file(file: &Path) -> bool {
        let filename = file.to_string_lossy();
        filename.contains("Hacl")
            || filename.contains("Crypto")
            || filename.contains("crypto")
            || filename.contains("Spec")
    }

    /// Check if a file is a specification module (not compiled to executable code).
    ///
    /// In F*, Spec modules contain mathematical specifications used for verification.
    /// They are NOT compiled to executable code, so timing attacks don't apply.
    /// Pattern: `*.Spec.*` or `Spec.*` in the filename.
    fn is_spec_module(file: &Path) -> bool {
        let filename = file.to_string_lossy();
        // Match patterns like:
        // - Hacl.Spec.Bignum.fst
        // - Spec.Blake2.fst
        // - anything.Spec.something.fst
        filename.contains(".Spec.") || filename.starts_with("Spec.")
    }

    /// Check for buffer operations without obvious bounds verification.
    ///
    /// Scans surrounding context for length checks, asserts, or requires clauses.
    fn check_buffer_operations(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            let line_number = line_num + 1;

            // Skip comments
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") || trimmed.starts_with("*") {
                continue;
            }

            // Check Buffer.index usage
            if BUFFER_INDEX.is_match(line) && !self.has_bounds_context(&lines, line_num) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Buffer.index without visible bounds check - verify index is within bounds".to_string(),
                    fix: None,
                });
            }

            // Check Buffer.sub usage
            if BUFFER_SUB.is_match(line) && !self.has_bounds_context(&lines, line_num) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Buffer.sub without visible bounds check - verify start+len is within bounds".to_string(),
                    fix: None,
                });
            }

            // Check Buffer.blit usage
            if BUFFER_BLIT.is_match(line) && !self.has_bounds_context(&lines, line_num) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Buffer.blit without visible bounds check - verify both buffers have sufficient space".to_string(),
                    fix: None,
                });
            }

            // Check Buffer.upd usage
            if BUFFER_UPD.is_match(line) && !self.has_bounds_context(&lines, line_num) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Buffer.upd without visible bounds check - verify index is within bounds".to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check if there's a bounds verification in the surrounding context.
    ///
    /// Looks at a window of lines before/after for length checks,
    /// asserts, or requires clauses.
    fn has_bounds_context(&self, lines: &[&str], current_line: usize) -> bool {
        // Look at 5 lines before and after
        let start = current_line.saturating_sub(5);
        let end = (current_line + 5).min(lines.len());

        for line in &lines[start..end] {
            if LENGTH_CHECK.is_match(line)
                || BOUNDS_ASSERT.is_match(line)
                || REQUIRES_LEN.is_match(line)
            {
                return true;
            }
        }
        false
    }

    /// Check if a variable name represents a metadata value (length, size, etc.)
    /// rather than actual secret data.
    fn is_key_metadata(name: &str) -> bool {
        KEY_METADATA_SUFFIX.is_match(name)
    }

    /// Check if a variable name looks like a function name rather than a buffer variable.
    fn is_function_name(name: &str) -> bool {
        KEY_FUNCTION_PREFIX.is_match(name) || TYPE_DEF_SUFFIX.is_match(name)
    }

    /// Check if a line is a function/type definition (not a variable binding).
    fn is_function_definition(line: &str) -> bool {
        FUNCTION_TYPE_DEF.is_match(line)
    }

    /// Check if a variable name indicates it holds secret data.
    /// Returns false for:
    /// - Metadata names: key_len, key_size, secret_length, etc.
    /// - Function names: update_key, derive_key, init_secret, etc.
    /// - Type names: key_t, key_st
    /// - Loop indices and public variables
    fn is_secret_variable(name: &str) -> bool {
        // Must contain a secret-indicating substring
        let lower = name.to_lowercase();
        let has_secret_indicator =
            lower.contains("key") || lower.contains("secret") || lower.contains("priv");

        if !has_secret_indicator {
            return false;
        }

        // Exclude metadata (lengths, sizes, etc.)
        if METADATA_SUFFIX.is_match(name) {
            return false;
        }

        // Exclude function names
        if FUNCTION_PREFIX.is_match(name) {
            return false;
        }

        // Exclude type definitions
        if TYPE_DEF_SUFFIX.is_match(name) {
            return false;
        }

        true
    }

    /// Check if a line contains a secret variable that would be affected by timing.
    fn line_has_secret_variable(line: &str) -> bool {
        SECRET_VAR_PATTERN
            .captures_iter(line)
            .filter_map(|c| c.get(1))
            .any(|m| Self::is_secret_variable(m.as_str()))
    }

    /// Check for key variables that may not be properly zeroized.
    ///
    /// This function uses precise pattern matching to avoid false positives:
    /// - Only matches actual buffer allocations (create, alloca, sub, malloc)
    /// - Excludes length/size variables (key_len, key_size, etc.)
    /// - Excludes function names (update_key, derive_key, etc.)
    /// - Excludes type definitions (key_st, key_t, etc.)
    fn check_key_zeroization(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Collect actual key buffer allocations with line numbers
        // Must be: let <name> = create/alloca/sub/malloc (actual buffer allocation)
        let key_vars: Vec<(usize, String)> = content
            .lines()
            .enumerate()
            .filter_map(|(i, line)| {
                // Skip comments
                let trimmed = line.trim();
                if trimmed.starts_with("(*")
                    || trimmed.starts_with("//")
                    || trimmed.starts_with("*")
                {
                    return None;
                }

                // Skip function/type definitions
                if Self::is_function_definition(line) {
                    return None;
                }

                // Match actual buffer allocations
                KEY_BUFFER_ALLOC
                    .captures(line)
                    .and_then(|c| c.get(1))
                    .map(|m| m.as_str().to_string())
                    .filter(|name| {
                        // Exclude metadata variables (lengths, sizes)
                        !Self::is_key_metadata(name)
                            // Exclude function names
                            && !Self::is_function_name(name)
                    })
                    .map(|name| (i + 1, name))
            })
            .collect();

        // Check if any cleanup function is present in the file
        let has_cleanup = MEMZERO.is_match(content) || CLEAR_FN.is_match(content);

        // If there are key allocations but no cleanup, warn
        for (line, key_var) in &key_vars {
            // Only warn if no cleanup is found anywhere in the file
            if !has_cleanup {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(*line, 1),
                    message: format!(
                        "Key buffer `{}` may not be zeroized - use `memzero` or `clear_*` before deallocation",
                        key_var
                    ),
                    fix: None,
                });
            }
        }

        // Check for stack-allocated secrets (may leak on early returns)
        for (line_num, line) in content.lines().enumerate() {
            // Skip comments
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") || trimmed.starts_with("*") {
                continue;
            }

            if STACK_ALLOC_SECRET.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num + 1, 1),
                    message:
                        "Stack-allocated secret may leak on early return - ensure cleanup on all paths"
                            .to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for nonce/IV initialization issues.
    ///
    /// Detects zero-initialization of nonces and missing random sources.
    fn check_nonce_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let line_number = line_num + 1;

            // Skip comments
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") || trimmed.starts_with("*") {
                continue;
            }

            let is_nonce_line =
                NONCE_VAR.is_match(line) || IV_VAR.is_match(line) || COUNTER_VAR.is_match(line);

            if !is_nonce_line {
                continue;
            }

            // Check for zero initialization of nonce/IV
            if ZERO_INIT.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Error,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message:
                        "Nonce/IV initialized to zero - use random generation or unique counter"
                            .to_string(),
                    fix: None,
                });
            }

            // Check for assignment without random source
            if (line.contains('=') || line.contains("<-"))
                && !RANDOM_SOURCE.is_match(line)
                && !line.contains("increment")
                && !line.contains("++")
                && !line.contains("+")
            {
                // Look for a literal assignment (not from another variable that might be random)
                if line.contains("0x") || trimmed.ends_with("0") {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_number, 1),
                        message: "Nonce/IV assigned constant value - ensure uniqueness for each encryption".to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for LowStar.Ignore.ignore on security-sensitive return values.
    ///
    /// In HACL* bignum code, carry/borrow returns from arithmetic operations
    /// are critical for correctness. While `LowStar.Ignore.ignore` is sometimes
    /// intentional (the carry is known to be zero), in crypto code it deserves
    /// a hint to verify the intent.
    ///
    /// Real pattern from Hacl.Bignum.Karatsuba:
    /// ```text
    /// let c1 = bn_sub_eq_len_u aLen b a res in
    /// LowStar.Ignore.ignore c1;
    /// ```
    fn check_ignored_returns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if let Some(caps) = LOWSTAR_IGNORE.captures(line) {
                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");

                // Check if the ignored variable looks like a carry/borrow
                if CARRY_BORROW_VAR.is_match(var_name) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "LowStar.Ignore.ignore on `{}` - verify that ignoring this \
                             carry/borrow value is intentional and does not affect correctness",
                            var_name
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for buffer operations in crypto code that may leak previous contents.
    ///
    /// In crypto contexts, uninitialized buffers can leak secrets from previous
    /// stack frames. This is especially dangerous with `alloca` which reuses
    /// stack memory.
    fn check_buffer_init_safety(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            // Check for alloca without explicit zero initialization in crypto code
            // Good: `let buf = alloca 0uy 32ul` (zero-initialized)
            // Bad: `let buf = alloca 32ul` (potentially uninitialized - though F* typically requires init)
            if UNINIT_BUFFER.is_match(trimmed) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Hint,
                    file: file.to_path_buf(),
                    range: Range::point(line_num + 1, 1),
                    message: "Buffer allocation without visible initial value - \
                              ensure buffer is zero-initialized in crypto context to prevent \
                              leaking secrets from previous allocations".to_string(),
                    fix: None,
                });
            }
        }

        diagnostics
    }

    /// Check for secret-dependent loop bounds.
    ///
    /// Loops whose iteration count depends on secret data cause variable-time
    /// execution, which is a classic timing side-channel. In HACL*, loop bounds
    /// must always be public (size_t/size_nat). This detects patterns where
    /// a secret-named variable appears in a loop bound expression.
    ///
    /// Safe pattern: `Lib.Loops.for 0ul len inv` (len is public size_t)
    /// Unsafe pattern: `Lib.Loops.for 0ul (v secret_rounds) inv`
    fn check_secret_loop_bounds(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") || trimmed.starts_with("*") {
                continue;
            }

            if let Some(caps) = LOOP_WITH_SECRET_BOUND.captures(line) {
                let var_name = caps.get(1).map(|m| m.as_str()).unwrap_or("");
                if Self::is_secret_variable(var_name) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "Loop bound depends on secret variable `{}`. \
                             Variable iteration count leaks information through timing. \
                             Use a public bound or pad to a fixed iteration count.",
                            var_name
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for quantifiers without SMTPat in security-related lemmas.
    ///
    /// In security proofs, universal quantifiers without patterns cause the
    /// Z3 solver to use E-matching heuristics, which can lead to:
    /// 1. Verification timeouts (proof doesn't complete)
    /// 2. Proof instability (works on one Z3 version, fails on another)
    /// 3. Missed proof obligations (quantifier not instantiated)
    ///
    /// HACL* best practice: every quantified lemma should have SMTPat triggers.
    fn check_quantifier_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Track whether we're inside a Lemma context
        let mut in_lemma = false;
        let mut lemma_depth = 0;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") || trimmed.starts_with("*") {
                continue;
            }

            // Track Lemma context
            if LEMMA_RE.is_match(line) {
                in_lemma = true;
                lemma_depth = 0;
            }

            // Track nesting depth (rough heuristic)
            lemma_depth += line.chars().filter(|c| *c == '(').count();
            lemma_depth = lemma_depth.saturating_sub(line.chars().filter(|c| *c == ')').count());

            // Reset context at top-level let/val declarations
            if (trimmed.starts_with("let ") || trimmed.starts_with("val "))
                && !trimmed.contains("Lemma")
                && lemma_depth == 0
            {
                in_lemma = false;
            }

            // Check for quantifiers in lemma context
            if in_lemma && QUANTIFIER.is_match(line) {
                // Look ahead for SMTPat within 5 lines
                let has_pattern = (line_num..=(line_num + 5).min(lines.len() - 1))
                    .any(|i| SMTPAT_IN_LINE.is_match(lines[i]));

                if !has_pattern {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: "Quantifier in security lemma without SMTPat trigger. \
                                 Missing patterns cause proof instability and potential \
                                 verification timeouts. Add `[SMTPat (...)]` to guide \
                                 Z3 instantiation."
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for non-linear arithmetic operations on secret values.
    ///
    /// On most CPUs, multiplication/division time depends on operand values.
    /// When operands are secret, this leaks information through timing.
    /// HACL* uses dedicated constant-time bignum multiplication routines
    /// instead of native `*` on secrets.
    ///
    /// Safe: `let x = a *. b` (size operator, public)
    /// Unsafe: `let x = secret_a * secret_b` (native multiply on secrets)
    fn check_nonlinear_arithmetic_on_secrets(
        &self,
        file: &Path,
        content: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") || trimmed.starts_with("*") {
                continue;
            }

            // Skip constant-time operations
            if CT_SELECT.is_match(line) || CT_MASK.is_match(line) || MASK_SELECT.is_match(line) {
                continue;
            }

            // Skip size operators (public, safe)
            if line.contains("*.") {
                continue;
            }

            if let Some(caps) = SECRET_MULTIPLICATION.captures(line) {
                let var_name = caps
                    .get(1)
                    .or_else(|| caps.get(2))
                    .map(|m| m.as_str())
                    .unwrap_or("");

                if Self::is_secret_variable(var_name) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "Non-linear arithmetic on secret `{}`. Native multiplication \
                             has data-dependent timing on most CPUs. Use constant-time \
                             bignum multiplication routines (e.g., bn_mul) instead.",
                            var_name
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for timing side-channel vulnerabilities.
    ///
    /// Detects division/modulo on secrets and early returns based on secret comparisons.
    fn check_timing_patterns(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_num, line) in content.lines().enumerate() {
            let line_number = line_num + 1;

            // Skip comments
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") || trimmed.starts_with("*") {
                continue;
            }

            // Skip lines that use constant-time operations
            if CT_SELECT.is_match(line) || CT_COMPARE.is_match(line) || CT_COND.is_match(line) {
                continue;
            }

            // Check division/modulo operations involving secrets
            // Use refined check that excludes metadata (key_len, key_size, etc.)
            if (DIV_BY_VAR.is_match(line) || MOD_BY_VAR.is_match(line))
                && Self::line_has_secret_variable(line)
            {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Division/modulo operation on secret data may leak timing information"
                        .to_string(),
                    fix: None,
                });
            }

            // Check early return based on secret comparison
            if EARLY_RETURN.is_match(line) && SECRET_COMPARISON.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Early return based on secret value may leak timing information"
                        .to_string(),
                    fix: None,
                });
            }

            // Check short-circuit evaluation on secrets
            // Use refined check that excludes metadata (key_len, key_size, etc.)
            if SHORT_CIRCUIT.is_match(line) && Self::line_has_secret_variable(line) {
                // Only warn if it looks like a boolean expression on secret
                if line.contains("if ") || line.contains("then") || line.contains("else") {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_number, 1),
                        message: "Short-circuit evaluation on secret may leak timing information - consider constant-time alternative".to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }
}

impl Default for SecurityRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for SecurityRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST017
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Only check crypto-related files to reduce false positives
        if !Self::is_crypto_file(file) {
            return diagnostics;
        }

        // Run line-by-line checks for original patterns
        for (line_num, line) in content.lines().enumerate() {
            let line_number = line_num + 1;

            // Skip comment lines (simple heuristic)
            let trimmed = line.trim();
            if trimmed.starts_with("(*") || trimmed.starts_with("//") || trimmed.starts_with("*") {
                continue;
            }

            // Check for hardcoded secrets - highest severity
            if HARDCODED_KEY.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Error,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "Hardcoded secret detected - use secure key derivation".to_string(),
                    fix: None,
                });
            }

            // Check for RawIntTypes (may break secret independence)
            if RAW_INT_TYPES.is_match(line) {
                diagnostics.push(Diagnostic {
                    rule: RuleCode::FST017,
                    severity: DiagnosticSeverity::Warning,
                    file: file.to_path_buf(),
                    range: Range::point(line_number, 1),
                    message: "RawIntTypes usage may break secret independence".to_string(),
                    fix: None,
                });
            }

            // Check for potential secret-dependent branches
            // Skip if line uses constant-time masks (proper implementation)
            // Skip for Spec modules (specification code, not compiled)
            if SECRET_BRANCH.is_match(line)
                && !CT_MASK.is_match(line)
                && !CT_SELECT.is_match(line)
                && !CT_COMPARE.is_match(line)
                && !Self::is_spec_module(file)
            {
                // Heuristic: check if variable name suggests secret data
                // Use refined check that excludes metadata (key_len, key_size, etc.)
                if Self::line_has_secret_variable(line) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST017,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_number, 1),
                        message: "Potential secret-dependent branch - use constant-time masks"
                            .to_string(),
                        fix: None,
                    });
                }
            }
        }

        // Run additional specialized checks
        diagnostics.extend(self.check_buffer_operations(file, content));
        diagnostics.extend(self.check_key_zeroization(file, content));
        diagnostics.extend(self.check_nonce_patterns(file, content));
        diagnostics.extend(self.check_ignored_returns(file, content));
        diagnostics.extend(self.check_buffer_init_safety(file, content));

        // Skip timing checks for Spec modules (specification code, not compiled)
        if !Self::is_spec_module(file) {
            diagnostics.extend(self.check_timing_patterns(file, content));
            diagnostics.extend(self.check_secret_loop_bounds(file, content));
            diagnostics.extend(self.check_nonlinear_arithmetic_on_secrets(file, content));
        }

        // Quantifier pattern checks apply to both Spec and Impl
        diagnostics.extend(self.check_quantifier_patterns(file, content));

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn crypto_path() -> PathBuf {
        PathBuf::from("Hacl.Impl.Curve25519.fst")
    }

    fn non_crypto_path() -> PathBuf {
        PathBuf::from("Utils.fst")
    }

    // === Original tests ===

    #[test]
    fn test_hardcoded_secret() {
        let rule = SecurityRule::new();
        let content = r#"let key = "supersecretkey123""#;
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("Hardcoded secret")));
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Error));
    }

    #[test]
    fn test_raw_int_types() {
        let rule = SecurityRule::new();
        let content = "open FStar.RawIntTypes";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("RawIntTypes usage")));
    }

    #[test]
    fn test_secret_branch() {
        let rule = SecurityRule::new();
        let content = "if secret_val = 0 then branch1 else branch2";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("secret-dependent")));
    }

    #[test]
    fn test_constant_time_mask_ok() {
        let rule = SecurityRule::new();
        let content = "let mask = eq_mask secret_a secret_b";
        let diags = rule.check(&crypto_path(), content);
        // Should not warn about secret-dependent branch when using CT masks
        assert!(!diags.iter().any(|d| d.message.contains("secret-dependent")));
    }

    #[test]
    fn test_non_crypto_file_skipped() {
        let rule = SecurityRule::new();
        let content = r#"let key = "notsosecret""#;
        let diags = rule.check(&non_crypto_path(), content);
        // Non-crypto files should not be checked
        assert!(diags.is_empty());
    }

    #[test]
    fn test_comment_lines_skipped() {
        let rule = SecurityRule::new();
        let content = r#"(* let key = "shouldbeignored" *)"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.is_empty());
    }

    // === Buffer operations tests ===

    #[test]
    fn test_buffer_index_without_bounds() {
        let rule = SecurityRule::new();
        let content = "let x = Buffer.index buf idx";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("Buffer.index")));
        assert!(diags.iter().any(|d| d.severity == DiagnosticSeverity::Hint));
    }

    #[test]
    fn test_buffer_index_with_bounds_check() {
        let rule = SecurityRule::new();
        let content = r#"
assert (length buf > idx);
let x = Buffer.index buf idx
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should not warn when bounds check is present
        assert!(!diags.iter().any(|d| d.message.contains("Buffer.index")));
    }

    #[test]
    fn test_buffer_sub_without_bounds() {
        let rule = SecurityRule::new();
        let content = "let slice = Buffer.sub buf start len";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("Buffer.sub")));
    }

    #[test]
    fn test_buffer_blit_without_bounds() {
        let rule = SecurityRule::new();
        let content = "Buffer.blit src 0ul dst 0ul len";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("Buffer.blit")));
    }

    // === Key zeroization tests ===

    #[test]
    fn test_key_without_zeroization() {
        let rule = SecurityRule::new();
        let content = r#"
let my_key = create 32 0uy
(* use key *)
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("zeroized")));
    }

    #[test]
    fn test_key_with_memzero() {
        let rule = SecurityRule::new();
        let content = r#"
let my_key = create 32 0uy
(* use key *)
memzero my_key 32ul
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should not warn when memzero is present
        assert!(!diags.iter().any(|d| d.message.contains("zeroized")));
    }

    #[test]
    fn test_key_with_clear_function() {
        let rule = SecurityRule::new();
        let content = r#"
let secret_data = alloc 64ul
(* use secret *)
clear_bytes secret_data
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should not warn when clear function is present
        assert!(!diags.iter().any(|d| d.message.contains("zeroized")));
    }

    #[test]
    fn test_stack_alloc_secret() {
        let rule = SecurityRule::new();
        // A secret-named buffer being stack-allocated should warn
        let content = "let secret_data = create 32ul (u8 0)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags
                .iter()
                .any(|d| d.message.contains("Stack-allocated secret")),
            "Stack-allocated secret buffer should trigger warning"
        );
    }

    // === Nonce/IV tests ===

    #[test]
    fn test_nonce_zero_init() {
        let rule = SecurityRule::new();
        let content = "let nonce = 0";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("Nonce/IV initialized to zero")));
        assert!(diags
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Error));
    }

    #[test]
    fn test_iv_zero_init() {
        let rule = SecurityRule::new();
        let content = "let iv <- 0x00";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("Nonce/IV initialized to zero")));
    }

    #[test]
    fn test_nonce_with_random() {
        let rule = SecurityRule::new();
        let content = "let nonce = randombytes 12";
        let diags = rule.check(&crypto_path(), content);
        // Should not warn when random source is used
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("Nonce/IV initialized to zero")));
    }

    #[test]
    fn test_counter_constant_value() {
        let rule = SecurityRule::new();
        let content = "let counter = 0x00000001";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.iter().any(|d| d.message.contains("constant value")));
    }

    // === Timing pattern tests ===

    #[test]
    fn test_division_by_secret() {
        let rule = SecurityRule::new();
        let content = "let result = total / secret_divisor";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("Division/modulo operation")));
    }

    #[test]
    fn test_modulo_by_key_len_not_flagged() {
        let rule = SecurityRule::new();
        // key_len is metadata (length), NOT the actual secret - should NOT warn
        let content = "let remainder = value % key_len";
        let diags = rule.check(&crypto_path(), content);
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("Division/modulo operation")));
    }

    #[test]
    fn test_modulo_by_actual_secret() {
        let rule = SecurityRule::new();
        // key_byte is an actual secret value - SHOULD warn
        let content = "let remainder = value % secret_divisor";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("Division/modulo operation")));
    }

    #[test]
    fn test_early_return_on_secret() {
        let rule = SecurityRule::new();
        let content = "if key_byte = 0 then return false";
        let diags = rule.check(&crypto_path(), content);
        // Should detect both secret-dependent branch AND early return
        assert!(
            diags.iter().any(|d| d.message.contains("secret-dependent"))
                || diags.iter().any(|d| d.message.contains("Early return"))
        );
    }

    #[test]
    fn test_short_circuit_on_secret() {
        let rule = SecurityRule::new();
        let content = "if secret_a > 0 && secret_b < 10 then process else skip";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags
            .iter()
            .any(|d| d.message.contains("Short-circuit evaluation")));
    }

    // === Safe patterns tests ===

    #[test]
    fn test_ct_select_ok() {
        let rule = SecurityRule::new();
        let content = "let result = ct_select mask val_a val_b";
        let diags = rule.check(&crypto_path(), content);
        // ct_select should suppress timing warnings
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("timing information")));
    }

    #[test]
    fn test_ct_compare_ok() {
        let rule = SecurityRule::new();
        let content = "let equal = constant_time_compare key1 key2 32";
        let diags = rule.check(&crypto_path(), content);
        // constant_time_compare should suppress timing warnings
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("timing information")));
    }

    #[test]
    fn test_verify_function_ok() {
        let rule = SecurityRule::new();
        let content = "let valid = verify_32 mac expected";
        let diags = rule.check(&crypto_path(), content);
        // verify_* functions are constant-time
        assert!(!diags
            .iter()
            .any(|d| d.message.contains("timing information")));
    }

    // === Edge cases ===

    #[test]
    fn test_multiple_issues_same_line() {
        let rule = SecurityRule::new();
        // Line has both key variable and division
        let content = "let key_part = total_key / 2";
        let diags = rule.check(&crypto_path(), content);
        // Should detect division/modulo issue (2 is not secret, but key_part is)
        assert!(diags.len() >= 1);
    }

    #[test]
    fn test_empty_file() {
        let rule = SecurityRule::new();
        let content = "";
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_only_comments() {
        let rule = SecurityRule::new();
        let content = r#"
(* This is a comment *)
// Another comment
(* let key = "hidden" *)
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_requires_clause_bounds() {
        let rule = SecurityRule::new();
        let content = r#"
requires { length buf >= idx }
let x = Buffer.index buf idx
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should not warn when requires clause with length is present
        assert!(!diags.iter().any(|d| d.message.contains("Buffer.index")));
    }

    // === FALSE POSITIVE PREVENTION TESTS ===
    // These tests verify that the linter does NOT incorrectly flag valid code

    #[test]
    fn test_function_name_update_key_not_flagged() {
        let rule = SecurityRule::new();
        // update_key is a FUNCTION name, not a key variable - should NOT warn
        let content = r#"
let update_key : blake2_update_key_st Spec.Blake2S Core.M32 =
  blake2_update_key #Spec.Blake2S #Core.M32 update_block
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should NOT have zeroization warning for function definition
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "Function name update_key should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_key_length_variable_not_flagged() {
        let rule = SecurityRule::new();
        // key_len is the LENGTH of a key, not the key itself - should NOT warn for zeroization
        let content = "let key_len = 32ul";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "key_len (length variable) should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_key_size_variable_not_flagged() {
        let rule = SecurityRule::new();
        // size_key is a SIZE constant, not the key itself
        let content = "let size_key = 32";
        let diags = rule.check(&crypto_path(), content);
        // size_key ends with "key" but doesn't look like a buffer allocation
        // No create/alloca/sub = no zeroization warning
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "size_key (size constant) should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_derive_key_function_not_flagged() {
        let rule = SecurityRule::new();
        // derive_key is a function name
        let content = "let derive_key_poly1305_do #w k n aadlen aad mlen m out =";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "Function derive_key_poly1305_do should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_actual_key_buffer_allocation_flagged() {
        let rule = SecurityRule::new();
        // This IS an actual key buffer allocation - SHOULD warn if no cleanup
        let content = "let key = sub tmp 0ul 32ul";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("zeroized")),
            "Actual key buffer allocation should trigger zeroization warning"
        );
    }

    #[test]
    fn test_secret_buffer_with_create_flagged() {
        let rule = SecurityRule::new();
        // Actual secret buffer allocation
        let content = "let my_secret = create 64ul (u8 0)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("zeroized")),
            "Secret buffer allocation should trigger zeroization warning"
        );
    }

    #[test]
    fn test_priv_key_buffer_allocation_flagged() {
        let rule = SecurityRule::new();
        // priv_key buffer allocation
        let content = "let priv_key = alloca 32ul (u8 0)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("zeroized")),
            "priv_key buffer allocation should trigger zeroization warning"
        );
    }

    #[test]
    fn test_key_type_st_not_flagged() {
        let rule = SecurityRule::new();
        // blake2_update_key_st is a TYPE, not a variable
        let content = "let blake2_update_key_st (al:Spec.alg) (ms:m_spec) =";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "Type definition _st should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_key_bytes_metadata_not_flagged_for_timing() {
        let rule = SecurityRule::new();
        // key_bytes is metadata (byte count), not secret data
        let content = "if key_bytes = 32 then use_aes256 else use_aes128";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "key_bytes (metadata) should not trigger secret-dependent branch warning"
        );
    }

    #[test]
    fn test_actual_key_in_branch_flagged() {
        let rule = SecurityRule::new();
        // key_data is actual secret data
        let content = "if key_data = 0 then skip else process";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("secret-dependent")),
            "Actual key variable in branch should trigger warning"
        );
    }

    #[test]
    fn test_real_hacl_pattern_key_parameter() {
        let rule = SecurityRule::new();
        // Real HACL* pattern: key is a parameter, not allocation
        // This is just a function type annotation
        let content = r#"
val aead_encrypt: #w:field_spec -> aead_encrypt_st w

let aead_encrypt #w output tag input input_len data data_len key nonce =
  chacha20_encrypt #w input_len output input key nonce 1ul
"#;
        let diags = rule.check(&crypto_path(), content);
        // Parameter references should not trigger zeroization
        assert!(
            !diags.iter().any(|d| d.message.contains("zeroized")),
            "Function parameter references should not trigger zeroization warning"
        );
    }

    #[test]
    fn test_real_hacl_derived_key_pattern() {
        let rule = SecurityRule::new();
        // Real HACL* pattern: derived key that gets properly handled
        let content = r#"
push_frame ();
let tmp = create 64ul (u8 0) in
chacha20_encrypt #w 64ul tmp tmp k n 0ul;
let key = sub tmp 0ul 32ul in
poly1305_do #w key aadlen aad mlen m out;
pop_frame()
"#;
        let diags = rule.check(&crypto_path(), content);
        // This SHOULD warn - the derived key should be zeroized but isn't
        assert!(
            diags.iter().any(|d| d.message.contains("zeroized")),
            "Derived key without explicit zeroization should warn"
        );
    }

    #[test]
    fn test_division_by_key_length_not_flagged() {
        let rule = SecurityRule::new();
        // Division by key_length is safe - it's public metadata
        let content = "let blocks = total /. key_length";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Division by key_length (metadata) should not trigger timing warning"
        );
    }

    #[test]
    fn test_secret_in_division_operand_flagged() {
        let rule = SecurityRule::new();
        // Division involving actual secret value
        let content = "let result = secret_value / 2";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Division on secret value should trigger timing warning"
        );
    }

    #[test]
    fn test_helper_is_secret_variable() {
        // Test the is_secret_variable helper directly
        assert!(SecurityRule::is_secret_variable("key"));
        assert!(SecurityRule::is_secret_variable("my_key"));
        assert!(SecurityRule::is_secret_variable("secret"));
        assert!(SecurityRule::is_secret_variable("priv_key"));
        assert!(SecurityRule::is_secret_variable("key_data"));

        // Metadata should NOT be flagged as secret
        assert!(!SecurityRule::is_secret_variable("key_len"));
        assert!(!SecurityRule::is_secret_variable("key_length"));
        assert!(!SecurityRule::is_secret_variable("key_size"));
        assert!(!SecurityRule::is_secret_variable("keylen"));
        assert!(!SecurityRule::is_secret_variable("secret_size"));
        assert!(!SecurityRule::is_secret_variable("key_bits"));
        assert!(!SecurityRule::is_secret_variable("key_bytes"));

        // Function names should NOT be flagged as secret
        assert!(!SecurityRule::is_secret_variable("update_key"));
        assert!(!SecurityRule::is_secret_variable("derive_key"));
        assert!(!SecurityRule::is_secret_variable("init_secret"));
        assert!(!SecurityRule::is_secret_variable("get_key"));
        assert!(!SecurityRule::is_secret_variable("set_key"));
        assert!(!SecurityRule::is_secret_variable("expand_key"));
        assert!(!SecurityRule::is_secret_variable("clear_key"));

        // Type names should NOT be flagged as secret
        assert!(!SecurityRule::is_secret_variable("key_t"));
        assert!(!SecurityRule::is_secret_variable("key_st"));
    }

    // === HACL* SIZE OPERATOR TESTS ===
    // F* uses `/. ` and `%. ` for size_t operations which are PUBLIC

    #[test]
    fn test_size_division_operator_public() {
        let rule = SecurityRule::new();
        // `/. ` is the F* size division operator - operates on public size_t
        let content = "let i = ind /. pbits";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - this is a public operation
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Size division operator /. should not trigger timing warning"
        );
    }

    #[test]
    fn test_size_modulo_operator_public() {
        let rule = SecurityRule::new();
        // `%. ` is the F* size modulo operator - operates on public size_t
        let content = "let j = ind %. pbits";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - this is a public operation
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Size modulo operator %. should not trigger timing warning"
        );
    }

    #[test]
    fn test_size_comparison_operators_public() {
        let rule = SecurityRule::new();
        // Size comparisons like `<. `, `>. ` are public operations
        let content = "if len <. bn_mul_threshold then branch1 else branch2";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - size comparisons are public
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "Size comparison operators should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_hacl_karatsuba_pattern() {
        let rule = SecurityRule::new();
        // Real pattern from Hacl.Bignum.Karatsuba.fst
        let content = r#"
  if len <. bn_mul_threshold || len %. 2ul =. 1ul then
    bn_mul res a b
  else
    let len2 = len /. 2ul in
    karatsuba_mul res a b len2
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn on any of these - all public size operations
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "HACL* Karatsuba pattern should not trigger Division/modulo warning"
        );
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "HACL* Karatsuba pattern should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_hacl_exponentiation_pattern() {
        let rule = SecurityRule::new();
        // Real pattern from Hacl.Impl.Exponentiation.fst
        let content = r#"
  let bk = bBits -! bBits %. l in
  Lib.Loops.for 0ul (bBits /. l) inv (fun i -> ladder_step k i)
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - bBits, l are public, using size operators
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "HACL* exponentiation pattern should not trigger Division/modulo warning"
        );
    }

    #[test]
    fn test_eq_mask_constant_time() {
        let rule = SecurityRule::new();
        // eq_mask is a constant-time operation
        let content = "let beq = eq_mask a.(i) b.(i) in acc.(0ul) <- mask_select beq acc.(0ul) blt";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - using constant-time operations
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "eq_mask should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_mask_select_constant_time() {
        let rule = SecurityRule::new();
        // mask_select is a constant-time conditional
        let content = "priv.(0ul) <- mask_select mask priv.(0ul) (size_to_limb i)";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - mask_select is constant-time
        assert!(
            !diags.iter().any(|d| d.message.contains("timing")),
            "mask_select should not trigger timing warning"
        );
    }

    #[test]
    fn test_cswap_pattern_constant_time() {
        let rule = SecurityRule::new();
        // Pattern from cswap2_st - constant-time conditional swap
        let content = r#"
let mask = uint #t 0 -. bit in
let dummy = mask &. (b1.(i) ^. b2.(i)) in
b1.(i) <- b1.(i) ^. dummy
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - this is a constant-time swap pattern
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "cswap pattern should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_bbits_public_variable() {
        let rule = SecurityRule::new();
        // bBits (bit count) is always public
        let content = "if bBits <. size SE.bn_exp_mont_consttime_threshold then fast_path else slow_path";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - bBits is public metadata
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "bBits should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_len_public_variable() {
        let rule = SecurityRule::new();
        // len is always public
        let content = "if len > 0ul then process len else skip";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - len is public
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "len should not trigger secret-dependent warning"
        );
    }

    #[test]
    fn test_ind_public_index() {
        let rule = SecurityRule::new();
        // ind (index) is always public
        let content = "let x = ind /. 64 in buf.(ind)";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - ind is a public index
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "ind (public index) should not trigger timing warning"
        );
    }

    #[test]
    fn test_size_literal_division() {
        let rule = SecurityRule::new();
        // Division by size literal is public
        let content = "let half = total / 2ul";
        let diags = rule.check(&crypto_path(), content);
        // Should NOT warn - size literal division is public
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Division by size literal should not trigger timing warning"
        );
    }

    // === SPEC MODULE TESTS ===
    // Spec modules are mathematical specifications, not compiled code

    fn spec_module_path() -> PathBuf {
        PathBuf::from("Hacl.Spec.Bignum.Lib.fst")
    }

    #[test]
    fn test_spec_module_detection() {
        // Test the is_spec_module helper
        assert!(SecurityRule::is_spec_module(&PathBuf::from("Hacl.Spec.Bignum.fst")));
        assert!(SecurityRule::is_spec_module(&PathBuf::from("Hacl.Spec.Bignum.Lib.fst")));
        assert!(SecurityRule::is_spec_module(&PathBuf::from("Spec.Blake2.fst")));
        assert!(SecurityRule::is_spec_module(&PathBuf::from("Spec.Chacha20.fst")));
        assert!(SecurityRule::is_spec_module(&PathBuf::from("Lib.Spec.Something.fst")));

        // These are NOT spec modules
        assert!(!SecurityRule::is_spec_module(&PathBuf::from("Hacl.Impl.Bignum.fst")));
        assert!(!SecurityRule::is_spec_module(&PathBuf::from("Hacl.Bignum.Lib.fst")));
        assert!(!SecurityRule::is_spec_module(&PathBuf::from("Speculative.fst"))); // Not a spec module
    }

    #[test]
    fn test_spec_module_branch_not_flagged() {
        let rule = SecurityRule::new();
        // This pattern WOULD be flagged in implementation code,
        // but Spec modules are specifications, not compiled code
        let content = "if v mask = 0 then secret_val else other_val";
        let diags = rule.check(&spec_module_path(), content);
        // Should NOT warn - spec modules are not compiled
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "Spec modules should not trigger secret-dependent branch warnings"
        );
    }

    #[test]
    fn test_spec_module_timing_not_flagged() {
        let rule = SecurityRule::new();
        // Division/modulo in spec modules is fine
        let content = "let result = secret_val / divisor";
        let diags = rule.check(&spec_module_path(), content);
        // Should NOT warn for timing - spec modules are not compiled
        assert!(
            !diags.iter().any(|d| d.message.contains("Division/modulo")),
            "Spec modules should not trigger timing warnings"
        );
    }

    #[test]
    fn test_impl_module_branch_flagged() {
        let rule = SecurityRule::new();
        // In implementation modules, secret-dependent branches SHOULD be flagged
        let content = "if secret_val = 0 then branch1 else branch2";
        let diags = rule.check(&crypto_path(), content);
        // SHOULD warn - implementation code needs constant-time operations
        assert!(
            diags.iter().any(|d| d.message.contains("secret-dependent")),
            "Implementation modules SHOULD trigger secret-dependent branch warnings"
        );
    }

    // =========================================================================
    // LOW*/LOWSTAR SECURITY TESTS
    // =========================================================================

    #[test]
    fn test_lowstar_ignore_carry_warns() {
        let rule = SecurityRule::new();
        // Real pattern from Hacl.Bignum.Karatsuba - ignoring carry return
        let content = r#"
let c1 = bn_sub_eq_len_u aLen b a res in
LowStar.Ignore.ignore c1;
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("LowStar.Ignore.ignore") && d.message.contains("c1")),
            "Ignoring carry return should trigger hint"
        );
    }

    #[test]
    fn test_lowstar_ignore_non_carry_no_warn() {
        let rule = SecurityRule::new();
        // Ignoring a non-carry variable
        let content = "LowStar.Ignore.ignore unused_result;";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("carry/borrow")),
            "Non-carry/borrow ignore should NOT trigger carry warning"
        );
    }

    #[test]
    fn test_lowstar_ignore_overflow_warns() {
        let rule = SecurityRule::new();
        let content = "LowStar.Ignore.ignore overflow;";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("LowStar.Ignore.ignore") && d.message.contains("overflow")),
            "Ignoring overflow should trigger hint"
        );
    }

    #[test]
    fn test_hacl_karatsuba_ignore_pattern() {
        let rule = SecurityRule::new();
        // Full HACL* Karatsuba pattern
        let content = r#"
let bn_sign_abs #t #aLen a b tmp res =
  let c0 = bn_sub_eq_len_u aLen a b tmp in
  let c1 = bn_sub_eq_len_u aLen b a res in
  map2T aLen res (mask_select (uint #t 0 -. c0)) res tmp;
  LowStar.Ignore.ignore c1;
  c0
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should hint about ignoring c1 (which is a carry)
        assert!(
            diags.iter().any(|d| d.message.contains("c1")),
            "HACL* Karatsuba pattern should hint about ignored carry c1"
        );
    }

    #[test]
    fn test_buffer_uninit_crypto_context() {
        let rule = SecurityRule::new();
        let content = "let buf = create 32ul";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("initial value")),
            "Buffer without init value in crypto context should trigger hint"
        );
    }

    #[test]
    fn test_buffer_zero_init_ok() {
        let rule = SecurityRule::new();
        let content = "let buf = create 32ul (u8 0)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("initial value")),
            "Zero-initialized buffer should NOT trigger init warning"
        );
    }

    #[test]
    fn test_hacl_real_chacha20poly1305_pattern() {
        let rule = SecurityRule::new();
        // Real pattern from Hacl.Impl.Chacha20Poly1305
        let content = r#"
push_frame();
let ctx = create (nlimb w +! precomplen w) (limb_zero w) in
let block = create 16ul (u8 0) in
poly1305_do_ #w k aadlen aad mlen m ctx block;
Poly.poly1305_finish out k ctx;
pop_frame()
"#;
        let diags = rule.check(&crypto_path(), content);
        // Both buffers are properly initialized - should not warn about init
        assert!(
            !diags.iter().any(|d| d.message.contains("initial value")),
            "HACL* Chacha20Poly1305 properly initialized buffers should not warn"
        );
    }

    #[test]
    fn test_hacl_derive_key_pattern() {
        let rule = SecurityRule::new();
        // Real HACL* pattern with key derivation
        let content = r#"
push_frame ();
let tmp = create 64ul (u8 0) in
chacha20_encrypt #w 64ul tmp tmp k n 0ul;
let key = sub tmp 0ul 32ul in
poly1305_do #w key aadlen aad mlen m out;
pop_frame ()
"#;
        let diags = rule.check(&crypto_path(), content);
        // Should flag the derived key for zeroization (sub creates an alias, not freed)
        assert!(
            diags.iter().any(|d| d.message.contains("zeroized")),
            "Derived key from sub should trigger zeroization warning"
        );
    }

    #[test]
    fn test_full_hacl_bignum_pattern_no_false_positives() {
        let rule = SecurityRule::new();
        // Representative HACL* bignum code
        let content = r#"
let bn_middle_karatsuba #t #aLen c0 c1 c2 t01 t23 tmp res =
  let c_sign = c0 ^. c1 in
  let c3 = bn_sub_eq_len_u aLen t01 t23 tmp in let c3 = c2 -. c3 in
  let c4 = bn_add_eq_len_u aLen t01 t23 res in let c4 = c2 +. c4 in
  let mask = uint #t 0 -. c_sign in
  map2T aLen res (mask_select mask) res tmp;
  mask_select mask c4 c3
"#;
        let diags = rule.check(&crypto_path(), content);
        // mask_select is constant-time - no timing warnings
        assert!(
            !diags.iter().any(|d| d.message.contains("secret-dependent")),
            "HACL* bignum code with mask_select should not trigger timing warnings"
        );
    }

    // =========================================================================
    // NEW: SECRET-DEPENDENT LOOP BOUND TESTS
    // =========================================================================

    #[test]
    fn test_secret_loop_bound_warns() {
        let rule = SecurityRule::new();
        let content = "Lib.Loops.for 0ul (v secret_rounds) inv (fun i -> step i)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Loop bound") && d.message.contains("secret")),
            "Loop bound on secret variable should trigger warning"
        );
    }

    #[test]
    fn test_public_loop_bound_ok() {
        let rule = SecurityRule::new();
        // len is a public variable (size_t)
        let content = "Lib.Loops.for 0ul len inv (fun i -> step i)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Loop bound")),
            "Loop with public bound should NOT trigger warning"
        );
    }

    #[test]
    fn test_repeati_secret_bound_warns() {
        let rule = SecurityRule::new();
        let content = "Lib.LoopCombinators.repeati secret_count f init";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Loop bound") && d.message.contains("secret")),
            "repeati with secret bound should trigger warning"
        );
    }

    #[test]
    fn test_hacl_loop_pattern_ok() {
        let rule = SecurityRule::new();
        // Real HACL* pattern: loop bound is bBits /. l (public size operations)
        let content = "Lib.Loops.for 0ul (bBits /. l) inv (fun i -> ladder_step k i)";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Loop bound")),
            "HACL* loop with public size operator bound should NOT trigger warning"
        );
    }

    #[test]
    fn test_spec_module_secret_loop_not_flagged() {
        let rule = SecurityRule::new();
        // Spec modules are not compiled, so timing doesn't matter
        let content = "Lib.Loops.for 0ul secret_count inv (fun i -> step i)";
        let diags = rule.check(&spec_module_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Loop bound")),
            "Spec module loops should NOT trigger timing warnings"
        );
    }

    // =========================================================================
    // NEW: QUANTIFIER WITHOUT PATTERN TESTS
    // =========================================================================

    #[test]
    fn test_quantifier_in_lemma_without_pattern_warns() {
        let rule = SecurityRule::new();
        let content = r#"
val my_lemma : x:nat -> Lemma
  (requires True)
  (ensures forall (y:nat). y >= x)
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Quantifier") && d.message.contains("SMTPat")),
            "Quantifier in lemma without SMTPat should trigger info"
        );
    }

    #[test]
    fn test_quantifier_with_smtpat_ok() {
        let rule = SecurityRule::new();
        let content = r#"
val my_lemma : x:nat -> Lemma
  (ensures forall (y:nat). f y >= x)
  [SMTPat (f x)]
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Quantifier") && d.message.contains("SMTPat")),
            "Quantifier with SMTPat should NOT trigger warning"
        );
    }

    #[test]
    fn test_quantifier_outside_lemma_not_flagged() {
        let rule = SecurityRule::new();
        // forall in a type definition, not a lemma
        let content = r#"
let my_prop = forall (x:nat). x >= 0
let foo x = x + 1
"#;
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Quantifier") && d.message.contains("lemma")),
            "Quantifier outside lemma context should NOT trigger warning"
        );
    }

    // =========================================================================
    // NEW: NON-LINEAR ARITHMETIC ON SECRETS TESTS
    // =========================================================================

    #[test]
    fn test_secret_multiplication_warns() {
        let rule = SecurityRule::new();
        let content = "let result = secret_val * factor";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Non-linear arithmetic") && d.message.contains("secret")),
            "Multiplication on secret should trigger warning"
        );
    }

    #[test]
    fn test_secret_multiplication_rhs_warns() {
        let rule = SecurityRule::new();
        let content = "let result = factor * secret_val";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Multiplication with secret on RHS should trigger warning"
        );
    }

    #[test]
    fn test_public_multiplication_ok() {
        let rule = SecurityRule::new();
        // Public values: len, idx are always public
        let content = "let result = len * 4";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Multiplication on public values should NOT trigger warning"
        );
    }

    #[test]
    fn test_size_multiplication_operator_ok() {
        let rule = SecurityRule::new();
        // `*.` is the size multiplication operator (public, safe)
        let content = "let result = secret_val *. 2ul";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Size multiplication operator *. should NOT trigger warning"
        );
    }

    #[test]
    fn test_key_len_multiplication_ok() {
        let rule = SecurityRule::new();
        // key_len is metadata, not secret
        let content = "let total = key_len * 2";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Multiplication on key_len (metadata) should NOT trigger warning"
        );
    }

    #[test]
    fn test_mask_select_multiplication_ok() {
        let rule = SecurityRule::new();
        // mask_select is constant-time, suppresses warnings
        let content = "let x = mask_select mask (secret * factor) other";
        let diags = rule.check(&crypto_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Multiplication inside mask_select should NOT trigger warning"
        );
    }

    #[test]
    fn test_spec_module_nonlinear_ok() {
        let rule = SecurityRule::new();
        // Spec modules are not compiled
        let content = "let result = secret_val * secret_other";
        let diags = rule.check(&spec_module_path(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("Non-linear arithmetic")),
            "Spec module non-linear arithmetic should NOT trigger warning"
        );
    }
}
