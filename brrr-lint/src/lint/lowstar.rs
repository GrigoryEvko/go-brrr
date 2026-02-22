//! FST018 & FST019: Low*/LowStar lint rules for verified C code.
//!
//! FST018: LowStar Buffer Safety
//!   Detects unsafe buffer operation patterns in Low* code:
//!   - Unmatched push_frame/pop_frame pairs
//!   - Stack allocation (alloca/create) outside push_frame/pop_frame scope
//!   - Heap allocation (malloc/gcmalloc) without corresponding free
//!   - Missing liveness predicates in Stack effect signatures
//!   - Missing disjointness predicates for buffer parameters
//!   - Missing modifies clause in ensures
//!   - Buffer.sub/gsub without bounds constraints
//!
//! FST019: LowStar Verification Performance
//!   Detects expensive Low* proof patterns:
//!   - Missing inline_for_extraction on helper functions used in Low* code
//!   - Large modifies clauses (many buffers in |+| chain)
//!   - Missing noextract on specification-only bindings
//!   - Excessive ST.get() snapshots suggesting proof refactoring needed
//!   - Heavy disjointness conjunctions (O(n^2) in buffer count)
//!
//! These rules are designed around patterns observed in HACL*, EverParse,
//! and other real-world Low* projects.

use lazy_static::lazy_static;
use regex::Regex;
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Range, Rule, RuleCode};
use super::shared_patterns::{INLINE_FOR_EXTRACTION_RE, NOEXTRACT_RE, ASSERT_NORM_CALL_RE};

lazy_static! {
    // =========================================================================
    // Stack frame patterns
    // =========================================================================

    /// Matches push_frame() call (with optional parentheses/semicolons).
    static ref PUSH_FRAME: Regex = Regex::new(
        r"\bpush_frame\s*\(\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Matches pop_frame() call (with optional parentheses/semicolons).
    static ref POP_FRAME: Regex = Regex::new(
        r"\bpop_frame\s*\(\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Buffer allocation patterns
    // =========================================================================

    /// Stack buffer allocation: create, alloca.
    /// Examples: `let buf = create 16ul (u8 0)`, `let tmp = alloca 0uy 32ul`
    static ref STACK_ALLOC: Regex = Regex::new(
        r"\b(?:let\s+(\w+)\s*=\s*)?(?:create|alloca)\s+\d+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Heap buffer allocation: malloc, gcmalloc.
    /// Examples: `let buf = malloc HyperStack.root 0uy 32ul`
    static ref HEAP_ALLOC: Regex = Regex::new(
        r"\b(?:malloc|gcmalloc)\s+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Free call for heap buffers.
    static ref FREE_CALL: Regex = Regex::new(
        r"\bfree\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Effect signature patterns
    // =========================================================================

    /// Stack effect signature: `Stack <type> (requires ...) (ensures ...)`
    static ref STACK_EFFECT: Regex = Regex::new(
        r"\bStack\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// ST effect signature: `ST <type> (requires ...) (ensures ...)`
    static ref ST_EFFECT: Regex = Regex::new(
        r"\bST\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Requires clause in effect signatures.
    static ref REQUIRES_CLAUSE: Regex = Regex::new(
        r"\(\s*requires\s+fun\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Ensures clause in effect signatures.
    static ref ENSURES_CLAUSE: Regex = Regex::new(
        r"\(\s*ensures\s+fun\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Memory predicate patterns
    // =========================================================================

    /// Liveness predicate: `live h buf`
    static ref LIVE_PRED: Regex = Regex::new(
        r"\blive\s+\w+\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Disjointness predicate: `disjoint buf1 buf2`
    static ref DISJOINT_PRED: Regex = Regex::new(
        r"\bdisjoint\s+\w+\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Modifies clause: `modifies (loc ...) h0 h1` or `modifies (loc ... |+| loc ...) h0 h1`
    static ref MODIFIES_CLAUSE: Regex = Regex::new(
        r"\bmodifies\s*(?:\(|(?:loc\b))"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Modifies with loc_union chain: `loc buf1 |+| loc buf2 |+| ...`
    /// Count the |+| operators to measure modifies clause complexity.
    static ref LOC_UNION: Regex = Regex::new(
        r"\|\+\|"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Buffer operation patterns
    // =========================================================================

    /// Buffer sub/gsub operation: `sub buf start len` or `gsub buf start len`
    static ref BUFFER_SUB_OP: Regex = Regex::new(
        r"\b(?:sub|gsub)\s+\w+\s+\w+\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer index operation: `buf.(idx)` or `index buf idx`
    static ref BUFFER_INDEX_OP: Regex = Regex::new(
        r"(?:\w+\.\(\s*\w+\s*\)|\bindex\s+\w+\s+\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer update operation: `buf.(idx) <- val` or `upd buf idx val`
    static ref BUFFER_UPD_OP: Regex = Regex::new(
        r"(?:\w+\.\(\s*\w+\s*\)\s*<-|\bupd\s+\w+\s+\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Buffer blit operation.
    static ref BUFFER_BLIT_OP: Regex = Regex::new(
        r"\bblit\s+\w+\s+\w+\s+\w+\s+\w+\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Buffer aliasing patterns (HACL* uses sub/gsub heavily for views)
    // =========================================================================

    /// Buffer aliasing via sub/gsub creating views into parent buffer.
    /// Pattern: `let x = sub parent offset len` or `let x = gsub parent offset len`
    /// These create aliased views that share memory with the parent.
    static ref BUFFER_ALIAS: Regex = Regex::new(
        r"let\s+(\w+)\s*(?::\s*\w+(?:\s+\w+)*)?\s*=\s*(?:sub|gsub)\s+(\w+)\s+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// copy_felem / copy operations between buffers.
    static ref BUFFER_COPY: Regex = Regex::new(
        r"\b(?:copy_felem|copy|blit)\s+(\w+)\s+(\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Module alias patterns
    // =========================================================================

    /// HyperStack ST module alias: `module ST = FStar.HyperStack.ST`
    static ref ST_MODULE_ALIAS: Regex = Regex::new(
        r"module\s+ST\s*=\s*FStar\.HyperStack\.ST"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// LowStar.Ignore usage (suppressing unused values).
    static ref LOWSTAR_IGNORE: Regex = Regex::new(
        r"\bLowStar\.Ignore\.ignore\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // HACL* attribute patterns
    // =========================================================================

    /// Meta.Attribute.inline_ attribute (HACL* style).
    static ref META_INLINE: Regex = Regex::new(
        r"(?:\[@\s*Meta\.Attribute\.inline_\s*\]|\[@\s*Meta\.Attribute\.specialize\s*\])"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// unfold noextract pattern (common HACL* idiom for spec-only helpers).
    static ref UNFOLD_NOEXTRACT: Regex = Regex::new(
        r"\bunfold\s+noextract\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Machine integer operation patterns
    // =========================================================================

    /// Machine integer arithmetic with overflow potential.
    /// Matches `x +! y`, `x *! y` which are checked overflow ops.
    static ref CHECKED_INT_OPS: Regex = Regex::new(
        r"\w+\s*(?:\+!|\*!|-!|/!|%!)\s*\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Unchecked machine integer operations (potential overflow).
    /// Matches bare `+.`, `*.` etc. on machine integers.
    static ref UNCHECKED_INT_OPS: Regex = Regex::new(
        r"\w+\s*(?:\+\.|\*\.|-\.)\s*\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// update_sub_f pattern (framing helper used in HACL*).
    static ref UPDATE_SUB_F_PATTERN: Regex = Regex::new(
        r"\bupdate_sub_f(?:_carry)?\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// lbuffer typed parameter: `lbuffer <type> <size>`
    static ref LBUFFER_PARAM: Regex = Regex::new(
        r"\blbuffer\s+\w+\s+\w+"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Function val signature with buffer parameters.
    static ref VAL_WITH_BUFFER: Regex = Regex::new(
        r"val\s+\w+\s*:[\s\S]*?\blbuffer\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // LowStar-specific module patterns
    // =========================================================================

    /// LowStar module imports (open or abbreviation).
    static ref LOWSTAR_IMPORT: Regex = Regex::new(
        r"(?:open\s+|module\s+\w+\s*=\s*)(?:LowStar\.\w+|Lib\.Buffer|Lib\.ByteBuffer|FStar\.HyperStack)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Machine integer module usage: FStar.UInt32, UInt8, etc.
    static ref MACHINE_INT_MODULE: Regex = Regex::new(
        r"\bFStar\.(?:U?Int(?:8|16|32|64|128)|Int\.Cast)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Machine integer literal suffixes: 0ul, 1uy, 32uL, etc.
    static ref MACHINE_INT_LITERAL: Regex = Regex::new(
        r"\b\d+(?:ul|uL|uy|us|u)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// LowStar endianness operations.
    static ref ENDIANNESS_OP: Regex = Regex::new(
        r"\b(?:uint_to_bytes_le|uint_to_bytes_be|uint_from_bytes_le|uint_from_bytes_be|load(?:32|64|128)_(?:le|be)|store(?:32|64|128)_(?:le|be))\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    // =========================================================================
    // Performance-related patterns (FST019)
    // =========================================================================

    /// ST.get() heap snapshot captures.
    static ref ST_GET: Regex = Regex::new(
        r"\bST\.get\s*\(\s*\)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Val declaration (function signature).
    static ref VAL_DECL: Regex = Regex::new(
        r"^(?:inline_for_extraction\s+)?(?:noextract\s+)?val\s+(\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Let declaration (function binding).
    static ref LET_DECL: Regex = Regex::new(
        r"^(?:\[@[^\]]*\]\s*)?(?:inline_for_extraction\s+)?(?:noextract\s+)?let\s+(\w+)"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Sequence equality intro lemma (often needed but expensive).
    static ref SEQ_EQ_INTRO: Regex = Regex::new(
        r"\b(?:Seq\.eq_intro|LSeq\.eq_intro|Lib\.Sequence\.eq_intro)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Sequence lemma_concat (common proof pattern).
    static ref SEQ_LEMMA_CONCAT: Regex = Regex::new(
        r"\b(?:lemma_concat2?|Seq\.lemma_concat)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Modifies refl/trans/only_not_unused_in lemmas.
    static ref MODIFIES_LEMMA: Regex = Regex::new(
        r"\b(?:modifies_refl|modifies_trans|modifies_only_not_unused_in|reveal_ctx_inv)\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// update_sub_f helper (complex framing operation).
    static ref UPDATE_SUB_F: Regex = Regex::new(
        r"\bupdate_sub_f\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// eq_or_disjoint predicate (weaker disjointness).
    static ref EQ_OR_DISJOINT: Regex = Regex::new(
        r"\beq_or_disjoint\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

// =============================================================================
// FST018: LowStar Buffer Safety
// =============================================================================

/// FST018: LowStar buffer safety checker.
///
/// Analyzes Low* code for common buffer safety issues including unmatched
/// stack frame operations, missing memory predicates, and unsafe allocation
/// patterns. Designed around real patterns from HACL* and EverParse.
pub struct LowStarBufferRule;

impl LowStarBufferRule {
    pub fn new() -> Self {
        Self
    }

    /// Check if a file uses Low*/LowStar features.
    ///
    /// Returns true if the file imports LowStar modules, uses Stack/ST effects,
    /// or contains buffer operations. Avoids running expensive checks on pure
    /// specification files.
    fn is_lowstar_file(content: &str) -> bool {
        LOWSTAR_IMPORT.is_match(content)
            || STACK_EFFECT.is_match(content)
            || ST_EFFECT.is_match(content)
            || PUSH_FRAME.is_match(content)
            || content.contains("Lib.Buffer")
            || content.contains("LowStar.Buffer")
            || content.contains("FStar.HyperStack")
    }

    /// Check for unmatched push_frame/pop_frame pairs.
    ///
    /// In Low*, every push_frame() MUST be matched by a pop_frame() in the same
    /// function. Unmatched frames cause memory leaks or stack corruption.
    fn check_frame_discipline(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut push_stack: Vec<usize> = Vec::new(); // line numbers of unmatched pushes
        let mut in_comment = false;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();

            // Skip single-line block comments: (* ... *)
            if trimmed.contains("(*") && trimmed.contains("*)") {
                continue;
            }
            // Track multi-line block comments
            if trimmed.starts_with("(*") {
                in_comment = true;
                continue;
            }
            if in_comment {
                if trimmed.contains("*)") {
                    in_comment = false;
                }
                continue;
            }
            if trimmed.starts_with("//") {
                continue;
            }

            if PUSH_FRAME.is_match(line) {
                push_stack.push(line_num + 1);
            }

            if POP_FRAME.is_match(line) {
                if push_stack.is_empty() {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST018,
                        severity: DiagnosticSeverity::Error,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: "pop_frame() without matching push_frame() - potential stack corruption".to_string(),
                        fix: None,
                    });
                } else {
                    push_stack.pop();
                }
            }
        }

        // Report any unmatched push_frame calls
        for push_line in push_stack {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST018,
                severity: DiagnosticSeverity::Error,
                file: file.to_path_buf(),
                range: Range::point(push_line, 1),
                message: "push_frame() without matching pop_frame() - stack frame leak".to_string(),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for stack allocation outside push_frame/pop_frame scope.
    ///
    /// In Low*, alloca/create for stack-allocated buffers MUST be within a
    /// push_frame/pop_frame scope. Allocation outside this scope leads to
    /// undefined behavior when extracted to C.
    fn check_alloca_scope(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut in_frame = false;
        let mut frame_depth = 0;
        let mut in_comment = false;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();

            // Skip single-line block comments: (* ... *)
            if trimmed.contains("(*") && trimmed.contains("*)") {
                continue;
            }
            // Track multi-line block comments
            if trimmed.starts_with("(*") {
                in_comment = true;
                continue;
            }
            if in_comment {
                if trimmed.contains("*)") {
                    in_comment = false;
                }
                continue;
            }
            if trimmed.starts_with("//") {
                continue;
            }

            if PUSH_FRAME.is_match(line) {
                in_frame = true;
                frame_depth += 1;
            }

            if POP_FRAME.is_match(line) {
                frame_depth -= 1;
                if frame_depth == 0 {
                    in_frame = false;
                }
            }

            // alloca specifically requires stack frame
            if trimmed.contains("alloca ") && !in_frame {
                // Skip if it's in a type signature (val/type declaration)
                if !trimmed.starts_with("val ") && !trimmed.starts_with("type ") {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST018,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: "alloca outside push_frame/pop_frame scope - buffer will not be properly deallocated".to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for heap allocation without corresponding free.
    ///
    /// In Low*, malloc/gcmalloc allocate on the heap and the caller is responsible
    /// for calling free. Missing free causes memory leaks in the extracted C code.
    fn check_heap_alloc_free(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let has_malloc = HEAP_ALLOC.is_match(content);
        let has_free = FREE_CALL.is_match(content);

        if has_malloc && !has_free {
            // Find the malloc lines for precise reporting
            for (line_num, line) in content.lines().enumerate() {
                let trimmed = line.trim();
                if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                    continue;
                }

                if HEAP_ALLOC.is_match(line) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST018,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: "Heap allocation (malloc/gcmalloc) without corresponding free in this module - potential memory leak".to_string(),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check Stack effect signatures for missing memory predicates.
    ///
    /// A well-formed Stack effect should include:
    /// - `live h <buf>` for each buffer parameter in requires
    /// - `modifies ...` in ensures
    /// - `disjoint` for overlapping buffer parameters
    fn check_effect_signatures(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Find Stack/ST effect signatures and check their requires/ensures
        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim();

            // Skip comments
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                i += 1;
                continue;
            }

            // Look for Stack/ST effect with lbuffer parameters
            if (STACK_EFFECT.is_match(lines[i]) || ST_EFFECT.is_match(lines[i]))
                && !trimmed.starts_with("//")
            {
                // Scan the surrounding context (up to 30 lines) for the effect body
                let start = i.saturating_sub(10);
                let end = (i + 30).min(lines.len());
                let context: String = lines[start..end].join("\n");

                let has_buffer_params = context.contains("lbuffer")
                    || context.contains("buffer ")
                    || context.contains("buffer\n");

                if has_buffer_params {
                    let has_requires = REQUIRES_CLAUSE.is_match(&context);
                    let has_ensures = ENSURES_CLAUSE.is_match(&context);

                    if has_requires {
                        let has_live = LIVE_PRED.is_match(&context);
                        if !has_live {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST018,
                                severity: DiagnosticSeverity::Warning,
                                file: file.to_path_buf(),
                                range: Range::point(i + 1, 1),
                                message: "Stack effect with buffer parameters but no `live` predicate in requires - buffers may be dangling".to_string(),
                                fix: None,
                            });
                        }
                    }

                    if has_ensures {
                        let has_modifies = MODIFIES_CLAUSE.is_match(&context);
                        if !has_modifies {
                            diagnostics.push(Diagnostic {
                                rule: RuleCode::FST018,
                                severity: DiagnosticSeverity::Hint,
                                file: file.to_path_buf(),
                                range: Range::point(i + 1, 1),
                                message: "Stack effect with buffer parameters but no `modifies` clause in ensures - frame conditions may be unprovable".to_string(),
                                fix: None,
                            });
                        }
                    }
                }
            }

            i += 1;
        }

        diagnostics
    }

    /// Check for buffer aliasing without disjointness awareness.
    ///
    /// In HACL*, `sub`/`gsub` creates views into a parent buffer that share
    /// the same memory. When multiple sub-buffers are created from the same
    /// parent and both are passed to modifying operations, they need
    /// disjointness predicates to avoid silent memory corruption.
    ///
    /// Real pattern from HACL* Curve25519:
    /// ```text
    /// let x2 = sub nq 0ul (nlimb s) in
    /// let z2 = sub nq (nlimb s) (nlimb s) in
    /// ```
    /// Here x2 and z2 alias into nq and must have non-overlapping ranges.
    fn check_buffer_aliasing(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Track sub-buffer aliases per parent buffer within each function body
        let mut current_aliases: Vec<(String, String, usize)> = Vec::new(); // (child, parent, line)
        let mut in_frame = false;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            // Track frame boundaries to scope alias analysis
            if PUSH_FRAME.is_match(line) {
                in_frame = true;
                current_aliases.clear();
            }
            if POP_FRAME.is_match(line) {
                in_frame = false;
                current_aliases.clear();
            }

            // Detect sub/gsub aliasing
            if let Some(caps) = BUFFER_ALIAS.captures(line) {
                let child = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
                let parent = caps.get(2).map(|m| m.as_str().to_string()).unwrap_or_default();
                if !child.is_empty() && !parent.is_empty() {
                    current_aliases.push((child, parent.clone(), line_num + 1));
                }

                // Check for multiple aliases from the same parent
                let same_parent_count = current_aliases.iter()
                    .filter(|(_, p, _)| p == &parent)
                    .count();

                if same_parent_count > 3 && in_frame {
                    // Many sub-buffer views from same parent - common in HACL* but worth noting
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST018,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "Buffer `{}` has {} sub-buffer aliases in this scope - \
                             ensure all sub-buffers have non-overlapping ranges to avoid memory corruption",
                            parent, same_parent_count
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for missing ST module alias in files using ST.get().
    ///
    /// Files that call `ST.get()` need `module ST = FStar.HyperStack.ST` at the top.
    /// Without this alias, ST.get() will fail to resolve. This is a common HACL* pattern.
    fn check_st_module_alias(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let uses_st_get = ST_GET.is_match(content);
        let has_st_alias = ST_MODULE_ALIAS.is_match(content);
        // Also check for direct open
        let has_st_open = content.contains("open FStar.HyperStack.ST");

        if uses_st_get && !has_st_alias && !has_st_open {
            // Find first ST.get() usage for reporting
            for (line_num, line) in content.lines().enumerate() {
                if ST_GET.is_match(line) {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST018,
                        severity: DiagnosticSeverity::Warning,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: "ST.get() used but `module ST = FStar.HyperStack.ST` alias not found - \
                                  add module alias or `open FStar.HyperStack.ST`".to_string(),
                        fix: None,
                    });
                    break; // Only report once per file
                }
            }
        }

        diagnostics
    }

    /// Check for multiple buffer parameters in val signatures without disjointness.
    ///
    /// When a function takes multiple buffer parameters (2+), the requires clause
    /// should typically include disjointness predicates. Missing disjointness can
    /// lead to soundness issues or unprovable postconditions.
    ///
    /// Real HACL* pattern (Karatsuba):
    /// ```text
    /// val bn_sign_abs:
    ///     a:lbignum t aLen
    ///   -> b:lbignum t aLen
    ///   -> tmp:lbignum t aLen
    ///   -> res:lbignum t aLen ->
    ///   Stack (carry t)
    ///   (requires fun h ->
    ///     live h a /\ live h b /\ live h res /\ live h tmp /\
    ///     eq_or_disjoint a b /\ disjoint a res /\ ...)
    /// ```
    fn check_multi_buffer_disjointness(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                i += 1;
                continue;
            }

            // Look for val declarations
            if trimmed.starts_with("val ") {
                // Scan the signature block (up to 40 lines)
                let sig_end = (i + 40).min(lines.len());
                let sig_block: String = lines[i..sig_end].join("\n");

                // Count lbuffer/lbignum parameters
                let buffer_param_count = LBUFFER_PARAM.find_iter(&sig_block).count()
                    + sig_block.matches("lbignum").count();

                // Check if it has Stack/ST effect
                let has_stateful_effect = STACK_EFFECT.is_match(&sig_block)
                    || ST_EFFECT.is_match(&sig_block);

                if buffer_param_count >= 3 && has_stateful_effect {
                    let has_disjoint = DISJOINT_PRED.is_match(&sig_block)
                        || EQ_OR_DISJOINT.is_match(&sig_block);

                    if !has_disjoint {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST018,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(i + 1, 1),
                            message: format!(
                                "Function signature with {} buffer parameters but no disjointness \
                                 predicates - add `disjoint` or `eq_or_disjoint` to requires clause",
                                buffer_param_count
                            ),
                            fix: None,
                        });
                    }
                }

                // Skip past this signature
                i = sig_end.min(lines.len());
                continue;
            }

            i += 1;
        }

        diagnostics
    }
}

impl Default for LowStarBufferRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for LowStarBufferRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST018
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        // Only check files that use Low*/LowStar features
        if !Self::is_lowstar_file(content) {
            return Vec::new();
        }

        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_frame_discipline(file, content));
        diagnostics.extend(self.check_alloca_scope(file, content));
        diagnostics.extend(self.check_heap_alloc_free(file, content));
        diagnostics.extend(self.check_effect_signatures(file, content));
        diagnostics.extend(self.check_buffer_aliasing(file, content));
        diagnostics.extend(self.check_st_module_alias(file, content));
        diagnostics.extend(self.check_multi_buffer_disjointness(file, content));

        diagnostics
    }
}

// =============================================================================
// FST019: LowStar Verification Performance
// =============================================================================

/// FST019: LowStar verification performance checker.
///
/// Detects patterns that commonly cause slow verification in Low* code,
/// based on observations from HACL* and similar projects.
pub struct LowStarPerfRule {
    /// Threshold for loc_union chain length before warning.
    pub loc_union_threshold: usize,
    /// Threshold for ST.get() count per function before warning.
    pub st_get_threshold: usize,
    /// Threshold for disjointness predicates before warning.
    pub disjoint_threshold: usize,
    /// Threshold for assert_norm count before warning.
    pub assert_norm_threshold: usize,
}

impl LowStarPerfRule {
    /// Create with default thresholds calibrated from HACL* patterns.
    ///
    /// HACL* commonly uses 4-5 loc_unions, 3-4 ST.get() per function,
    /// and 6-8 disjointness predicates. Thresholds are set above these.
    pub fn new() -> Self {
        Self {
            loc_union_threshold: 6,
            st_get_threshold: 5,
            disjoint_threshold: 10,
            assert_norm_threshold: 8,
        }
    }

    /// Check for overly large modifies clauses.
    ///
    /// When a modifies clause contains many loc_union (|+|) operators,
    /// it creates combinatorial explosion for the SMT solver trying to
    /// prove frame conditions.
    fn check_modifies_complexity(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if MODIFIES_CLAUSE.is_match(line) {
                // Count |+| operators in this line and continuation lines
                let mut union_count = LOC_UNION.find_iter(line).count();

                // Check continuation lines (indented more)
                let mut j = line_num + 1;
                while j < lines.len() {
                    let next = lines[j].trim();
                    if next.is_empty() || next.starts_with("(") || next.starts_with("let")
                        || next.starts_with("val") || next.starts_with("))")
                    {
                        break;
                    }
                    union_count += LOC_UNION.find_iter(lines[j]).count();
                    if next.contains(")") && !next.contains("(") {
                        break;
                    }
                    j += 1;
                }

                if union_count >= self.loc_union_threshold {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST019,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num + 1, 1),
                        message: format!(
                            "Large modifies clause with {} loc_union operators. \
                             Consider grouping buffers or using loc_union_l for lists.",
                            union_count
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for excessive ST.get() heap snapshots.
    ///
    /// Each ST.get() captures a heap snapshot that the solver must reason about.
    /// Many snapshots in a single function make proofs exponentially harder.
    /// HACL* typically uses 2-4 per function.
    fn check_st_get_density(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Count ST.get() calls between push/pop frame pairs (per function)
        let lines: Vec<&str> = content.lines().collect();
        let mut st_get_lines: Vec<usize> = Vec::new();
        let mut in_frame = false;
        let mut frame_start = 0;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if PUSH_FRAME.is_match(line) {
                in_frame = true;
                frame_start = line_num + 1;
                st_get_lines.clear();
            }

            if in_frame && ST_GET.is_match(line) {
                st_get_lines.push(line_num + 1);
            }

            if POP_FRAME.is_match(line) && in_frame {
                if st_get_lines.len() > self.st_get_threshold {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST019,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(frame_start, 1),
                        message: format!(
                            "Function has {} ST.get() heap snapshots (threshold: {}). \
                             Each snapshot creates proof obligations. Consider splitting \
                             into smaller helper functions.",
                            st_get_lines.len(), self.st_get_threshold
                        ),
                        fix: None,
                    });
                }
                in_frame = false;
                st_get_lines.clear();
            }
        }

        diagnostics
    }

    /// Check for heavy disjointness conjunctions.
    ///
    /// When a function takes N buffer parameters, it needs O(N^2) disjointness
    /// predicates. When N > threshold, suggest restructuring.
    fn check_disjoint_density(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Find requires clauses and count disjoint predicates
        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                i += 1;
                continue;
            }

            if REQUIRES_CLAUSE.is_match(lines[i]) {
                let mut disjoint_count = 0;
                // Scan the requires block (until ensures or closing paren)
                let start_line = i;
                let mut j = i;
                while j < lines.len() && j < i + 30 {
                    disjoint_count += DISJOINT_PRED.find_iter(lines[j]).count();
                    // Also count eq_or_disjoint
                    disjoint_count += EQ_OR_DISJOINT.find_iter(lines[j]).count();

                    if ENSURES_CLAUSE.is_match(lines[j]) {
                        break;
                    }
                    j += 1;
                }

                if disjoint_count > self.disjoint_threshold {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST019,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(start_line + 1, 1),
                        message: format!(
                            "Requires clause has {} disjointness predicates. \
                             Consider grouping buffer parameters into a record type \
                             or using loc_includes patterns to reduce proof complexity.",
                            disjoint_count
                        ),
                        fix: None,
                    });
                }
            }

            i += 1;
        }

        diagnostics
    }

    /// Check for excessive assert_norm usage.
    ///
    /// assert_norm triggers full normalization by the F* normalizer,
    /// which can be extremely expensive. Each assert_norm can add seconds
    /// to verification time.
    fn check_assert_norm_density(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        let assert_norm_count = ASSERT_NORM_CALL_RE.find_iter(content).count();
        if assert_norm_count > self.assert_norm_threshold {
            diagnostics.push(Diagnostic {
                rule: RuleCode::FST019,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message: format!(
                    "File has {} assert_norm calls (threshold: {}). \
                     Each triggers full normalization which is expensive. \
                     Consider using norm_spec or inline_for_extraction instead.",
                    assert_norm_count, self.assert_norm_threshold
                ),
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for missing inline_for_extraction on Low* helper functions.
    ///
    /// In Low* code, helper functions that are not marked inline_for_extraction
    /// become separate C functions with overhead. Small helpers should be inlined.
    fn check_missing_inline(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            // Check for let bindings that define function types used in Low* context
            // Pattern: `let helper_type = ... -> Stack unit ...`
            if LET_DECL.is_match(trimmed)
                && (trimmed.contains("-> Stack") || trimmed.contains("-> ST"))
                && !INLINE_FOR_EXTRACTION_RE.is_match(trimmed)
                && !NOEXTRACT_RE.is_match(trimmed)
                && !trimmed.starts_with("[@")
            {
                // Check if the previous line has inline_for_extraction or Meta.Attribute.inline_
                let prev_has_inline = if line_num > 0 {
                    INLINE_FOR_EXTRACTION_RE.is_match(lines[line_num - 1])
                        || META_INLINE.is_match(lines[line_num - 1])
                } else {
                    false
                };

                // Check 2 lines back (HACL* often puts attribute on separate line)
                let prev2_has_inline = if line_num > 1 {
                    INLINE_FOR_EXTRACTION_RE.is_match(lines[line_num - 2])
                        || META_INLINE.is_match(lines[line_num - 2])
                } else {
                    false
                };

                if !prev_has_inline && !prev2_has_inline {
                    // Look at the next few lines to see if this is actually a function type
                    let end_check = (line_num + 5).min(lines.len());
                    let block: String = lines[line_num..end_check].join("\n");
                    if block.contains("Stack") || block.contains("ST ") {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST019,
                            severity: DiagnosticSeverity::Hint,
                            file: file.to_path_buf(),
                            range: Range::point(line_num + 1, 1),
                            message: "Low* function type without inline_for_extraction - consider adding it for better C code generation".to_string(),
                            fix: None,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check for heavy use of Seq.eq_intro/lemma_concat which are expensive.
    ///
    /// In HACL*, `Seq.eq_intro` and `lemma_concat2` are commonly used but each
    /// invocation creates expensive proof obligations. Multiple uses in the same
    /// function suggest the proof could be restructured.
    fn check_seq_lemma_density(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        // Count per function (between push/pop frame pairs)
        let mut seq_eq_count = 0;
        let mut seq_concat_count = 0;
        let mut in_frame = false;
        let mut frame_start = 0;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if PUSH_FRAME.is_match(line) {
                in_frame = true;
                frame_start = line_num + 1;
                seq_eq_count = 0;
                seq_concat_count = 0;
            }

            if in_frame {
                seq_eq_count += SEQ_EQ_INTRO.find_iter(line).count();
                seq_concat_count += SEQ_LEMMA_CONCAT.find_iter(line).count();
            }

            if POP_FRAME.is_match(line) && in_frame {
                let total = seq_eq_count + seq_concat_count;
                if total > 4 {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST019,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(frame_start, 1),
                        message: format!(
                            "Function has {} sequence proof lemma calls ({} eq_intro, {} lemma_concat). \
                             Consider extracting sequence reasoning into a separate lemma.",
                            total, seq_eq_count, seq_concat_count
                        ),
                        fix: None,
                    });
                }
                in_frame = false;
                seq_eq_count = 0;
                seq_concat_count = 0;
            }
        }

        diagnostics
    }

    /// Check for functions with both update_sub_f and ST.get() patterns.
    ///
    /// In HACL*, `update_sub_f` combined with multiple `ST.get()` and
    /// `reveal_ctx_inv` calls indicates a complex framing proof that could
    /// benefit from helper lemmas. This pattern appears frequently in
    /// Chacha20Poly1305 and similar modules.
    fn check_update_sub_f_complexity(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut in_frame = false;
        let mut frame_start = 0;
        let mut update_sub_count = 0;
        let mut reveal_count = 0;

        for (line_num, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                continue;
            }

            if PUSH_FRAME.is_match(line) {
                in_frame = true;
                frame_start = line_num + 1;
                update_sub_count = 0;
                reveal_count = 0;
            }

            if in_frame {
                update_sub_count += UPDATE_SUB_F_PATTERN.find_iter(line).count();
                reveal_count += MODIFIES_LEMMA.find_iter(line).count();
            }

            if POP_FRAME.is_match(line) && in_frame {
                if update_sub_count >= 2 && reveal_count >= 2 {
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST019,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(frame_start, 1),
                        message: format!(
                            "Function has {} update_sub_f calls with {} reveal/modifies lemmas. \
                             Consider extracting framing proofs into a helper lemma to reduce verification time.",
                            update_sub_count, reveal_count
                        ),
                        fix: None,
                    });
                }
                in_frame = false;
            }
        }

        diagnostics
    }
}

impl Default for LowStarPerfRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for LowStarPerfRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST019
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        // Only check files that use Low*/LowStar features
        if !LowStarBufferRule::is_lowstar_file(content) {
            return Vec::new();
        }

        let mut diagnostics = Vec::new();

        diagnostics.extend(self.check_modifies_complexity(file, content));
        diagnostics.extend(self.check_st_get_density(file, content));
        diagnostics.extend(self.check_disjoint_density(file, content));
        diagnostics.extend(self.check_assert_norm_density(file, content));
        diagnostics.extend(self.check_missing_inline(file, content));
        diagnostics.extend(self.check_seq_lemma_density(file, content));
        diagnostics.extend(self.check_update_sub_f_complexity(file, content));

        diagnostics
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn lowstar_file() -> PathBuf {
        PathBuf::from("Hacl.Impl.Chacha20Poly1305.fst")
    }

    fn non_lowstar_file() -> PathBuf {
        PathBuf::from("Spec.Pure.Algorithm.fst")
    }

    // =========================================================================
    // FST018: LowStar Buffer Safety Tests
    // =========================================================================

    // --- Frame discipline tests ---

    #[test]
    fn test_matched_push_pop_frame() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let my_function () : Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
=
  push_frame ();
  let buf = create 16ul (u8 0) in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("push_frame") || d.message.contains("pop_frame")),
            "Matched push/pop should not trigger warning"
        );
    }

    #[test]
    fn test_unmatched_push_frame() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let leaky_function () =
  push_frame ();
  let buf = create 16ul (u8 0) in
  ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("push_frame") && d.message.contains("stack frame leak")),
            "Unmatched push_frame should trigger error"
        );
    }

    #[test]
    fn test_unmatched_pop_frame() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST

let bad_function () =
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("pop_frame") && d.message.contains("stack corruption")),
            "pop_frame without push_frame should trigger error"
        );
    }

    #[test]
    fn test_nested_push_pop_frames() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let nested () : Stack unit (requires fun h -> True) (ensures fun h0 _ h1 -> True) =
  push_frame ();
  let buf1 = create 16ul (u8 0) in
  push_frame ();
  let buf2 = create 32ul (u8 0) in
  pop_frame ();
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("push_frame") || d.message.contains("pop_frame")),
            "Nested matched frames should not trigger warning"
        );
    }

    // --- Alloca scope tests ---

    #[test]
    fn test_alloca_inside_frame() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let safe () =
  push_frame ();
  let buf = alloca 0uy 32ul in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("alloca outside")),
            "alloca inside frame should not trigger warning"
        );
    }

    #[test]
    fn test_alloca_outside_frame() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let unsafe_alloc () =
  let buf = alloca 0uy 32ul in
  ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("alloca outside")),
            "alloca outside frame should trigger warning"
        );
    }

    // --- Heap allocation tests ---

    #[test]
    fn test_malloc_without_free() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let leak () =
  let buf = malloc HyperStack.root 0uy 32ul in
  ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("malloc") && d.message.contains("memory leak")),
            "malloc without free should trigger warning"
        );
    }

    #[test]
    fn test_malloc_with_free() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let safe_alloc () =
  let buf = malloc HyperStack.root 0uy 32ul in
  free buf
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("memory leak")),
            "malloc with free should not trigger warning"
        );
    }

    // --- Effect signature tests ---

    #[test]
    fn test_stack_effect_with_live() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val copy : src:lbuffer uint8 32ul -> dst:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h src /\ live h dst /\ disjoint src dst)
  (ensures fun h0 _ h1 ->
    modifies (loc dst) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("live") && d.message.contains("dangling")),
            "Stack effect with live predicate should not trigger warning"
        );
    }

    #[test]
    fn test_stack_effect_missing_live() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val bad_copy : src:lbuffer uint8 32ul -> dst:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 ->
    modifies (loc dst) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("live") || d.message.contains("dangling")),
            "Stack effect with buffer params but no live predicate should trigger warning"
        );
    }

    // --- Non-LowStar files skipped ---

    #[test]
    fn test_non_lowstar_file_skipped() {
        let rule = LowStarBufferRule::new();
        let content = r#"
module Spec.Pure.Math

let add (x y : nat) : nat = x + y
"#;
        let diags = rule.check(&non_lowstar_file(), content);
        assert!(diags.is_empty(), "Non-LowStar files should be skipped entirely");
    }

    // --- Comments skipped ---

    #[test]
    fn test_comments_skipped_in_frame_check() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST

(* push_frame (); *)
// push_frame ();
let x = 1
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("push_frame")),
            "Comments containing push_frame should be ignored"
        );
    }

    // --- Real HACL* pattern tests ---

    #[test]
    fn test_hacl_chacha20poly1305_pattern() {
        let rule = LowStarBufferRule::new();
        // Actual pattern from Hacl.Impl.Chacha20Poly1305.fst
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let poly1305_do #w k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb w +! precomplen w) (limb_zero w) in
  let block = create 16ul (u8 0) in
  poly1305_do_ #w k aadlen aad mlen m ctx block;
  Poly.poly1305_finish out k ctx;
  pop_frame()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // Should not trigger push/pop warnings (matched pair)
        assert!(
            !diags.iter().any(|d| d.message.contains("push_frame") || d.message.contains("pop_frame")),
            "Real HACL* pattern should not trigger frame warnings"
        );
    }

    #[test]
    fn test_hacl_aead_decrypt_pattern() {
        let rule = LowStarBufferRule::new();
        // Actual pattern from Hacl.Impl.Chacha20Poly1305.fst aead_decrypt
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let aead_decrypt #w output input input_len data data_len key nonce tag =
  push_frame();
  let h0 = ST.get() in
  let computed_tag = create 16ul (u8 0) in
  derive_key_poly1305_do #w key nonce data_len data input_len input computed_tag;
  let h1 = ST.get() in
  let res =
    if lbytes_eq computed_tag tag then (
      chacha20_encrypt #w input_len output input key nonce 1ul;
      0ul
    ) else 1ul
  in
  pop_frame();
  res
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "HACL* aead_decrypt pattern should not trigger errors"
        );
    }

    #[test]
    fn test_hacl_exponentiation_pattern() {
        let rule = LowStarBufferRule::new();
        // Pattern from Hacl.Impl.Exponentiation.fst
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let lexp_mont_ladder_swap_consttime #a_t len ctx_len k ctx a bLen bBits b acc =
  push_frame ();
  let sw = create 1ul (uint #a_t #SEC 0) in
  k.lone ctx acc;
  let h0 = ST.get () in
  Lib.Loops.for 0ul bBits inv (fun i -> ladder_step);
  BN.cswap2 len sw.(0ul) acc a;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "HACL* exponentiation pattern should not trigger errors"
        );
    }

    // =========================================================================
    // FST019: LowStar Verification Performance Tests
    // =========================================================================

    #[test]
    fn test_small_modifies_no_warning() {
        let rule = LowStarPerfRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val f : buf1:lbuffer uint8 32ul -> buf2:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> live h buf1 /\ live h buf2)
  (ensures fun h0 _ h1 -> modifies (loc buf1 |+| loc buf2) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("loc_union")),
            "Small modifies clause should not trigger warning"
        );
    }

    #[test]
    fn test_large_modifies_warns() {
        let rule = LowStarPerfRule::new(); // threshold = 6
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val complex : a:lbuffer uint8 32ul -> b:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b |+| loc c |+| loc d |+| loc e |+| loc f |+| loc g) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("loc_union")),
            "Large modifies clause should trigger warning"
        );
    }

    #[test]
    fn test_few_st_get_no_warning() {
        let rule = LowStarPerfRule::new(); // threshold = 5
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let small_function () =
  push_frame ();
  let h0 = ST.get () in
  let h1 = ST.get () in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("ST.get()")),
            "Few ST.get() calls should not trigger warning"
        );
    }

    #[test]
    fn test_many_st_get_warns() {
        let rule = LowStarPerfRule::new(); // threshold = 5
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let snapshot_heavy () =
  push_frame ();
  let h0 = ST.get () in
  let h1 = ST.get () in
  let h2 = ST.get () in
  let h3 = ST.get () in
  let h4 = ST.get () in
  let h5 = ST.get () in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("ST.get()")),
            "Many ST.get() calls should trigger warning"
        );
    }

    #[test]
    fn test_few_disjoint_no_warning() {
        let rule = LowStarPerfRule::new(); // threshold = 10
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val f : a:lbuffer uint8 32ul -> b:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("disjointness")),
            "Few disjoint predicates should not trigger warning"
        );
    }

    #[test]
    fn test_many_disjoint_warns() {
        let rule = LowStarPerfRule::new(); // threshold = 10
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val complex : a:lbuffer uint8 32ul -> b:lbuffer uint8 32ul -> c:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\
    disjoint a b /\ disjoint a c /\ disjoint b c /\
    disjoint a d /\ disjoint a e /\ disjoint b d /\
    disjoint b e /\ disjoint c d /\ disjoint c e /\
    disjoint d e /\ disjoint d f /\ disjoint e f)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("disjointness")),
            "Many disjoint predicates should trigger warning"
        );
    }

    #[test]
    fn test_assert_norm_density() {
        let rule = LowStarPerfRule { assert_norm_threshold: 3, ..LowStarPerfRule::new() };
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let heavy_normalization () =
  assert_norm (UInt32.logxor 0ul 0ul == 0ul);
  assert_norm (UInt32.logxor 0ul 1ul == 1ul);
  assert_norm (UInt32.logxor 1ul 0ul == 1ul);
  assert_norm (UInt32.logxor 1ul 1ul == 0ul);
  ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("assert_norm")),
            "Many assert_norm calls should trigger warning"
        );
    }

    #[test]
    fn test_non_lowstar_skipped_perf() {
        let rule = LowStarPerfRule::new();
        let content = "let add x y = x + y";
        let diags = rule.check(&non_lowstar_file(), content);
        assert!(diags.is_empty(), "Non-LowStar files should be skipped");
    }

    // --- Real HACL* performance patterns ---

    #[test]
    fn test_hacl_blake2_typical_modifies() {
        let rule = LowStarPerfRule::new();
        // Typical HACL* Blake2 pattern with moderate loc_union
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val g1: #al:Spec.alg -> #m:m_spec -> wv:state_p al m -> a:index_t -> b:index_t ->
  Stack unit
    (requires (fun h -> live h wv /\ a <> b))
    (ensures  (fun h0 _ h1 -> modifies (loc wv) h0 h1))
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("loc_union")),
            "Typical HACL* Blake2 modifies should not trigger warning"
        );
    }

    #[test]
    fn test_hacl_curve25519_disjoint_pattern() {
        let rule = LowStarPerfRule::new();
        // Real pattern from Hacl.Impl.Curve25519.AddAndDouble
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val point_add_and_double0:
    #s:field_spec
  -> nq_p1:point s
  -> ab:lbuffer (limb s) (2ul *! nlimb s)
  -> dc:lbuffer (limb s) (2ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 nq_p1 /\ live h0 ab /\ live h0 dc /\ live h0 tmp2 /\
      disjoint nq_p1 ab /\ disjoint nq_p1 dc /\ disjoint nq_p1 tmp2 /\
      disjoint ab dc /\ disjoint ab tmp2 /\ disjoint dc tmp2)
    (ensures  fun h0 _ h1 ->
      modifies (loc nq_p1 |+| loc dc |+| loc tmp2) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        // 6 disjoint predicates is under the 10 threshold
        assert!(
            !diags.iter().any(|d| d.message.contains("disjointness")),
            "HACL* Curve25519 disjoint pattern should be under threshold"
        );
    }

    #[test]
    fn test_hacl_poly1305_do_st_get_pattern() {
        let rule = LowStarPerfRule::new();
        // Real pattern from Hacl.Impl.Chacha20Poly1305 - 3 ST.get() calls
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let poly1305_do_ #w k aadlen aad mlen m ctx block =
  push_frame ();
  Poly.poly1305_init ctx k;
  let h0 = ST.get () in
  update_sub_f h0 block 0ul 8ul (fun h -> f1) (fun _ -> g1);
  let h1 = ST.get () in
  Poly.reveal_ctx_inv ctx h0 h1;
  update_sub_f h1 block 8ul 8ul (fun h -> f2) (fun _ -> g2);
  let h2 = ST.get () in
  Poly.reveal_ctx_inv ctx h1 h2;
  Poly.poly1305_update1 ctx block;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // 3 ST.get() is under the 5 threshold
        assert!(
            !diags.iter().any(|d| d.message.contains("ST.get()")),
            "HACL* poly1305_do pattern (3 ST.get()) should be under threshold"
        );
    }

    // =========================================================================
    // FST018: Buffer Aliasing Tests (new)
    // =========================================================================

    #[test]
    fn test_sub_buffer_aliasing_few_aliases() {
        let rule = LowStarBufferRule::new();
        // 2 aliases from same parent - should NOT warn (common, safe pattern)
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let f () =
  push_frame ();
  let x2 = sub nq 0ul (nlimb s) in
  let z2 = sub nq (nlimb s) (nlimb s) in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("sub-buffer aliases")),
            "2 sub-buffer aliases should NOT trigger warning"
        );
    }

    #[test]
    fn test_sub_buffer_aliasing_many_aliases() {
        let rule = LowStarBufferRule::new();
        // 4+ aliases from same parent - should warn (hint)
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let f () =
  push_frame ();
  let a = sub tmp1 0ul (nlimb s) in
  let b = sub tmp1 (nlimb s) (nlimb s) in
  let c = sub tmp1 (2ul *! nlimb s) (nlimb s) in
  let d = sub tmp1 (3ul *! nlimb s) (nlimb s) in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("sub-buffer aliases")),
            "4+ sub-buffer aliases should trigger hint"
        );
    }

    #[test]
    fn test_hacl_curve25519_sub_pattern() {
        let rule = LowStarBufferRule::new();
        // Real HACL* Curve25519 pattern with multiple sub-buffers
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let point_add_and_double1 #s nq nq_p1 tmp1 tmp2 =
  push_frame ();
  let x2 = sub nq 0ul (nlimb s) in
  let z2 = sub nq (nlimb s) (nlimb s) in
  let x3 = sub nq_p1 0ul (nlimb s) in
  let z3 = sub nq_p1 (nlimb s) (nlimb s) in
  let a : felem s = sub tmp1 0ul (nlimb s) in
  let b : felem s = sub tmp1 (nlimb s) (nlimb s) in
  let d : felem s = sub tmp1 (2ul *! nlimb s) (nlimb s) in
  let c : felem s = sub tmp1 (3ul *! nlimb s) (nlimb s) in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // Should detect the 4+ aliases from tmp1 (a, b, d, c)
        assert!(
            diags.iter().any(|d| d.message.contains("sub-buffer aliases") && d.message.contains("tmp1")),
            "HACL* Curve25519 pattern should detect many tmp1 aliases"
        );
    }

    // =========================================================================
    // FST018: ST Module Alias Tests (new)
    // =========================================================================

    #[test]
    fn test_st_get_with_module_alias() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open Lib.Buffer
module ST = FStar.HyperStack.ST

let f () =
  push_frame ();
  let h0 = ST.get () in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("module ST")),
            "ST.get() with module alias should NOT trigger warning"
        );
    }

    #[test]
    fn test_st_get_with_open() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let f () =
  push_frame ();
  let h0 = ST.get () in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("module ST")),
            "ST.get() with open should NOT trigger warning"
        );
    }

    #[test]
    fn test_st_get_without_alias_or_open() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open Lib.Buffer

let f () =
  push_frame ();
  let h0 = ST.get () in
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("module ST") || d.message.contains("ST.get()")),
            "ST.get() without module alias or open should trigger warning"
        );
    }

    // =========================================================================
    // FST018: Multi-Buffer Disjointness Tests (new)
    // =========================================================================

    #[test]
    fn test_multi_buffer_with_disjointness() {
        let rule = LowStarBufferRule::new();
        // Real HACL* pattern with proper disjointness
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val bn_sign_abs:
    a:lbuffer uint8 32ul
  -> b:lbuffer uint8 32ul
  -> tmp:lbuffer uint8 32ul
  -> res:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h tmp /\
    eq_or_disjoint a b /\ disjoint a res /\ disjoint b res /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint tmp res)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("disjointness predicates")),
            "Multi-buffer with disjointness predicates should NOT trigger warning"
        );
    }

    #[test]
    fn test_multi_buffer_without_disjointness() {
        let rule = LowStarBufferRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val bad_function:
    a:lbuffer uint8 32ul
  -> b:lbuffer uint8 32ul
  -> c:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> live h a /\ live h b /\ live h c)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("disjointness")),
            "3+ buffer params without disjointness should trigger warning"
        );
    }

    #[test]
    fn test_two_buffer_params_no_warning() {
        let rule = LowStarBufferRule::new();
        // Only 2 buffer params - below threshold
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

val simple_copy:
    src:lbuffer uint8 32ul
  -> dst:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> live h src /\ live h dst)
  (ensures fun h0 _ h1 -> modifies (loc dst) h0 h1)
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("disjointness predicates")),
            "2 buffer params should NOT trigger disjointness warning (threshold is 3)"
        );
    }

    // =========================================================================
    // FST019: Sequence Lemma Density Tests (new)
    // =========================================================================

    #[test]
    fn test_few_seq_lemmas_no_warning() {
        let rule = LowStarPerfRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let f () =
  push_frame ();
  LSeq.eq_intro x y;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.message.contains("sequence proof lemma")),
            "1 seq lemma call should NOT trigger warning"
        );
    }

    #[test]
    fn test_many_seq_lemmas_warns() {
        let rule = LowStarPerfRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let heavy_proof () =
  push_frame ();
  LSeq.eq_intro x1 y1;
  LSeq.eq_intro x2 y2;
  lemma_concat2 8 a 8 b c;
  LSeq.eq_intro x3 y3;
  Seq.lemma_concat a b c;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            diags.iter().any(|d| d.message.contains("sequence proof lemma")),
            "5+ seq lemma calls should trigger info"
        );
    }

    #[test]
    fn test_hacl_poly1305_update_sub_f_pattern() {
        let rule = LowStarPerfRule::new();
        // Real HACL* pattern from Chacha20Poly1305
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let poly1305_do_ #w k aadlen aad mlen m ctx block =
  push_frame ();
  Poly.poly1305_init ctx k;
  let h0 = ST.get () in
  update_sub_f h0 block 0ul 8ul (fun h -> f1) (fun _ -> g1);
  let h1 = ST.get () in
  Poly.reveal_ctx_inv ctx h0 h1;
  update_sub_f h1 block 8ul 8ul (fun h -> f2) (fun _ -> g2);
  let h2 = ST.get () in
  Poly.reveal_ctx_inv ctx h1 h2;
  Poly.poly1305_update1 ctx block;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // 2 update_sub_f + 2 reveal_ctx_inv matches the threshold
        assert!(
            diags.iter().any(|d| d.message.contains("update_sub_f")),
            "2+ update_sub_f with 2+ reveal calls should trigger info"
        );
    }

    // =========================================================================
    // FST018: Real HACL* pattern regression tests (new)
    // =========================================================================

    #[test]
    fn test_hacl_karatsuba_full_pattern() {
        let rule = LowStarBufferRule::new();
        // Real pattern from Hacl.Bignum.Karatsuba.fst
        let content = r#"
open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

val bn_sign_abs:
    #t:limb_t
  -> #aLen:size_t
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> tmp:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h tmp /\
    eq_or_disjoint a b /\ disjoint a res /\ disjoint b res /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint tmp res)
  (ensures  fun h0 c h1 -> modifies (loc res |+| loc tmp) h0 h1)

let bn_sign_abs #t #aLen a b tmp res =
  let c0 = bn_sub_eq_len_u aLen a b tmp in
  let c1 = bn_sub_eq_len_u aLen b a res in
  map2T aLen res (mask_select (uint #t 0 -. c0)) res tmp;
  LowStar.Ignore.ignore c1;
  c0
"#;
        let diags = rule.check(&lowstar_file(), content);
        // Well-formed HACL* code should NOT produce errors
        assert!(
            !diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "Well-formed HACL* Karatsuba code should not produce errors"
        );
    }

    #[test]
    fn test_hacl_chacha20poly1305_full_pattern() {
        let rule = LowStarBufferRule::new();
        // Real pattern from Hacl.Impl.Chacha20Poly1305.fst
        let content = r#"
open FStar.HyperStack.All
open FStar.HyperStack
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST

let poly1305_do #w k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb w +! precomplen w) (limb_zero w) in
  let block = create 16ul (u8 0) in
  poly1305_do_ #w k aadlen aad mlen m ctx block;
  Poly.poly1305_finish out k ctx;
  pop_frame()

let derive_key_poly1305_do #w k n aadlen aad mlen m out =
  push_frame ();
  let tmp = create 64ul (u8 0) in
  chacha20_encrypt #w 64ul tmp tmp k n 0ul;
  let key = sub tmp 0ul 32ul in
  poly1305_do #w key aadlen aad mlen m out;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        assert!(
            !diags.iter().any(|d| d.severity == DiagnosticSeverity::Error),
            "Real HACL* Chacha20Poly1305 pattern should not produce errors"
        );
    }

    #[test]
    fn test_hacl_derive_key_sub_aliasing() {
        let rule = LowStarBufferRule::new();
        // derive_key_poly1305_do creates a sub-buffer alias
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

let f () =
  push_frame ();
  let tmp = create 64ul (u8 0) in
  let key = sub tmp 0ul 32ul in
  use_key key;
  pop_frame ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // Only 1 alias from tmp - should NOT warn
        assert!(
            !diags.iter().any(|d| d.message.contains("sub-buffer aliases")),
            "Single sub-buffer alias should NOT trigger warning"
        );
    }

    // =========================================================================
    // FST019: Meta.Attribute.inline_ recognition tests (new)
    // =========================================================================

    #[test]
    fn test_meta_inline_attribute_recognized() {
        let rule = LowStarPerfRule::new();
        let content = r#"
open FStar.HyperStack.ST
open Lib.Buffer

[@ Meta.Attribute.inline_ ]
let point_add_and_double0 #s nq_p1 ab dc tmp2 =
  let x3 = sub nq_p1 0ul (nlimb s) in
  ()
"#;
        let diags = rule.check(&lowstar_file(), content);
        // Should NOT warn about missing inline_for_extraction
        // because Meta.Attribute.inline_ is the HACL* equivalent
        assert!(
            !diags.iter().any(|d| d.message.contains("inline_for_extraction") &&
                d.range.start_line == 6),
            "Meta.Attribute.inline_ should be recognized as equivalent to inline_for_extraction"
        );
    }
}
