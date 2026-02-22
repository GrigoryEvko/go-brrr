//! FST005: Dead code detection.
//!
//! Detects:
//! - Unused private let bindings
//! - Unused private type definitions
//! - Unreachable code after `assert false`, `admit()`, `false_elim()`, or `absurd()`
//! - Unused function parameters (with autofix: add underscore prefix)
//! - Unreachable match branches (after wildcard pattern)
//! - Discarded non-unit results via `let _ = expr in` (potential bug)
//!
//! Suppresses false positives for F*-specific patterns:
//! - `[@@noextract]` / `noextract` bindings (proof-only, erased at extraction)
//! - Ghost/erased functions (`GTot`, `Ghost` effect, `erased` return type)
//! - Lemmas with `SMTPat`/`SMTPatOr` (auto-triggered by Z3 solver)
//! - Type class instances (`instance`) and classes (`class`) (used by resolution)
//! - `unfold let` bindings (used by F* normalizer)
//! - `inline_for_extraction let` bindings (used at extraction)
//! - `friend` module access (private bindings may be used by friend modules)
//! - Interface-declared bindings (`.fsti` files define public API)
//! - `assume val` declarations (axioms -- removing breaks proofs)
//! - `[@@"opaque_to_smt"]` / `[@@"substitute"]` / `[@irreducible]` attributes
//! - `abstract type` definitions (part of module interface)
//! - Effect system declarations (`effect`, `sub_effect`, etc.)
//! - Spec.* module bindings (verification-only specifications in HACL*-style projects)
//! - Private val declarations with Lemma/GTot/Ghost return types

use lazy_static::lazy_static;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::parser::{parse_fstar_file, BlockType};
use super::shared_patterns::{
    PARAM_EXTRACT_RE, SMTPAT_OPEN_RE, INLINE_FOR_EXTRACTION_RE, NOEXTRACT_RE,
};
use super::rules::{
    DeadCodeSafetyLevel, Diagnostic, DiagnosticSeverity, Edit, Fix, FixSafetyLevel, Range, Rule, RuleCode,
};

lazy_static! {
    /// Pattern matching `assert false` statements (terminates execution).
    /// Uses word boundary to avoid matching inside identifiers.
    static ref ASSERT_FALSE: Regex = Regex::new(r"\bassert\s+false\b\s*;").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern matching `admit()` calls (terminates proof obligation).
    /// Uses word boundary to avoid matching inside identifiers like "readmit".
    static ref ADMIT_PATTERN: Regex = Regex::new(r"\badmit\s*\(\s*\)\s*;?").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern matching `false_elim()` calls (bottom value for impossible branches).
    /// In F*, `false_elim()` has type `False -> a` and diverges.
    /// Uses word boundary to avoid matching inside identifiers like "my_false_elim".
    static ref FALSE_ELIM_PATTERN: Regex = Regex::new(r"\bfalse_elim\s*\(\s*\)\s*;?").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern matching `absurd()` calls (bottom value, similar to false_elim).
    /// Uses word boundary to avoid matching inside identifiers like "handle_absurd".
    static ref ABSURD_PATTERN: Regex = Regex::new(r"\babsurd\s*\(\s*\)\s*;?").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern matching `let _ = expr in` where the result is discarded.
    /// Captures the expression between `=` and `in` for analysis.
    /// Matches both `let _ = expr in` and `let () = expr in` forms.
    static ref LET_DISCARD: Regex = Regex::new(
        r"let\s+(?:_|\(\s*\))\s*=\s*(.+?)\s+in\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Known safe functions whose results can be discarded (proof/side-effect).
    /// These return unit or are called for their proof obligations, not their value.
    static ref SAFE_DISCARD_FUNCS: Regex = Regex::new(
        r"^(?:assert|assert_norm|assert_by_tactic|assume|allow_inversion|print|print_string|IO\.print_string|B\.recall|recall|norm_spec|Classical\.|FStar\.Classical\.|[@\[])"
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern matching `[@unused]` or `[@@unused]` attributes.
    /// F* allows single @ (local) or double @@ (global) attribute syntax.
    static ref UNUSED_ATTR: Regex = Regex::new(r"\[@+\s*unused\s*\]").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for wildcard match arm `| _ ->` WITHOUT a guard.
    /// CRITICAL: `| _ when cond ->` has a guard and does NOT match everything.
    /// We match `| _ ->` but ensure there's no `when` keyword between `_` and `->`.
    static ref MATCH_WILDCARD: Regex = Regex::new(r"\|\s*_\s*->").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for guarded wildcard match arm `| _ when ...`.
    /// This does NOT catch everything because the guard can be false.
    static ref MATCH_GUARDED_WILDCARD: Regex = Regex::new(r"\|\s*_\s+when\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for private type definitions.
    /// Matches: private type, private noeq type
    static ref PRIVATE_TYPE: Regex = Regex::new(r"^private\s+(?:noeq\s+)?type\s+(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `squash` type parameters - these are proof witnesses.
    /// In F*, `(u:squash condition)` is a proof that `condition` holds.
    /// The parameter `u` is intentionally not used at runtime.
    static ref SQUASH_PARAM: Regex = Regex::new(r"\(\s*\w+\s*:\s*squash\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `erased` type parameters - ghost/erased at extraction.
    /// In F*, erased parameters exist only for specifications.
    static ref ERASED_PARAM: Regex = Regex::new(r"\(\s*\w+\s*:\s*(?:Ghost\.)?erased\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for refinement type with unit - often carries constraints.
    /// `(u: unit { constraint })` - the binding is not used but carries proof.
    static ref UNIT_REFINEMENT_PARAM: Regex = Regex::new(r"\(\s*(\w+)\s*:\s*unit\s*\{").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for requires clause (F* specification).
    static ref REQUIRES_CLAUSE: Regex = Regex::new(r"\brequires\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for ensures clause (F* specification).
    static ref ENSURES_CLAUSE: Regex = Regex::new(r"\bensures\s*\(").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for decreases clause (termination measure).
    static ref DECREASES_CLAUSE: Regex = Regex::new(r"\bdecreases\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern to detect implicit parameters `#name` or `(#name : type)`.
    /// Implicit parameters are often erased/resolved by type inference.
    static ref IMPLICIT_PARAM: Regex = Regex::new(r"\(?\s*#(\w+)").unwrap_or_else(|e| panic!("regex: {e}"));

    // ==========================================================================
    // SAFETY-CRITICAL ATTRIBUTE PATTERNS
    // These patterns indicate bindings that should NEVER be auto-removed.
    // ==========================================================================

    /// Pattern for SMTPatOr (alternative SMT trigger patterns).
    /// Parameters used in SMTPatOr are important for proof automation.
    static ref SMTPATOR_PATTERN: Regex = Regex::new(r"\[SMTPatOr\s*\[").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `[@"opaque_to_smt"]` or `[@@"opaque_to_smt"]` attribute.
    /// Opaque bindings are intentionally hidden from the SMT solver but still used.
    /// CRITICAL: Never suggest removing these - they're part of proof architecture.
    static ref OPAQUE_TO_SMT_ATTR: Regex = Regex::new(
        r#"\[@+\s*"?opaque_to_smt"?\s*\]"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `[@opaque]` attribute (older syntax for opaque_to_smt).
    static ref OPAQUE_ATTR: Regex = Regex::new(r"\[@+\s*opaque\s*\]").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `irreducible` attribute.
    /// Irreducible definitions don't unfold but are still semantically used.
    static ref IRREDUCIBLE_ATTR: Regex = Regex::new(r"\[@+\s*irreducible\s*\]").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `assume val` declarations (axioms).
    /// CRITICAL: Assume vals are axioms - removing them can break proofs.
    /// Never offer autofix for assume val, even if appears unused.
    static ref ASSUME_VAL_PATTERN: Regex = Regex::new(r"^\s*assume\s+val\s+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `friend` module declarations.
    /// If a file has `friend` declarations, private bindings may be accessed
    /// by friend modules. This affects safety level of unused binding warnings.
    static ref FRIEND_DECL: Regex = Regex::new(r"^\s*friend\s+\w+").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `val` with attributes that suggest SMT usage.
    /// Bindings with `[SMTPat ...]` in their val declaration are auto-triggered.
    static ref VAL_WITH_SMTPAT: Regex = Regex::new(r"val\s+\w+[^=]*\[SMTPat").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for abstract type definitions.
    /// Abstract types are part of the module interface even if marked private.
    static ref ABSTRACT_TYPE: Regex = Regex::new(r"\babstract\s+type\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for GTot (ghost total) effect return type.
    /// Functions returning GTot exist only for specifications and are erased.
    /// Matches both `let f (x:nat) : GTot nat = ...` and `val f : x:nat -> GTot nat`.
    static ref GTOT_RETURN: Regex = Regex::new(r"(?::\s*|->\s*)GTot\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for Ghost effect return type (NOT Ghost.erased - that's handled separately).
    /// Ghost functions exist only for specifications and are erased at extraction.
    /// Matches both `let f (x:nat) : Ghost nat ...` and `val f : ... -> Ghost nat ...`.
    /// Uses `Ghost\s` to avoid matching `Ghost.erased` (which has a dot, not space).
    static ref GHOST_RETURN: Regex = Regex::new(r"(?::\s*|->\s*)Ghost\s").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `erased` return type.
    /// Functions returning `erased t` or `Ghost.erased t` are spec-only.
    /// Matches both `: erased nat` and `-> erased nat` and `-> Ghost.erased nat`.
    static ref ERASED_RETURN: Regex = Regex::new(r"(?::\s*|->\s*)(?:Ghost\.)?erased\b").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for `[@@"substitute"]` attribute.
    /// Similar to unfold, tells the normalizer to substitute the definition.
    static ref SUBSTITUTE_ATTR: Regex = Regex::new(
        r#"\[@+\s*"?substitute"?\s*\]"#
    ).unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for module declaration to extract module name.
    /// Used to detect Spec.* modules which are verification-only.
    static ref MODULE_DECL: Regex = Regex::new(r"^\s*module\s+([\w.]+)").unwrap_or_else(|e| panic!("regex: {e}"));

    /// Pattern for private val with Lemma return type (standalone spec declaration).
    /// Private val declarations for lemmas may not have a corresponding let
    /// because they serve as axiom-like declarations or are implemented in friend modules.
    static ref PRIVATE_VAL_LEMMA: Regex = Regex::new(
        r"private\s+val\s+\w+\s*.*Lemma\b"
    ).unwrap_or_else(|e| panic!("regex: {e}"));
}

/// FST005: Dead code detection rule.
///
/// This rule identifies code that is never executed or declarations
/// that are never referenced, helping maintain a clean codebase.
pub struct DeadCodeRule;

impl DeadCodeRule {
    pub fn new() -> Self {
        Self
    }

    // ==========================================================================
    // SAFETY LEVEL DETERMINATION
    // ==========================================================================

    /// Determine the safety level for removing a binding based on its attributes
    /// and context.
    ///
    /// CRITICAL: This is the core safety logic for FST005. We are VERY paranoid
    /// about suggesting dead code removal in F* because:
    /// - SMTPat bindings are auto-triggered by the solver
    /// - Opaque bindings are hidden but used
    /// - Ghost/noextract bindings exist for proofs only
    /// - Private bindings may be used by friend modules
    fn determine_binding_safety(&self, block_text: &str, file: &Path) -> DeadCodeSafetyLevel {
        // UNSAFE: Never remove if has critical attributes
        if self.has_unsafe_removal_pattern(block_text) {
            return DeadCodeSafetyLevel::Unsafe;
        }

        // UNSAFE: Interface files (.fsti) define public API - never auto-remove
        if self.is_interface_file(file) {
            return DeadCodeSafetyLevel::Unsafe;
        }

        // UNSAFE: Assume val declarations are axioms
        if ASSUME_VAL_PATTERN.is_match(block_text) {
            return DeadCodeSafetyLevel::Unsafe;
        }

        // CAUTION: If file has friend declarations, private bindings might be used
        // We can't easily check this per-binding, so we use CAUTION
        DeadCodeSafetyLevel::Caution
    }

    /// Check if block text contains patterns that make removal UNSAFE.
    ///
    /// Returns true if the binding should NEVER be auto-removed because it:
    /// - Has SMTPat/SMTPatOr (auto-triggered by solver)
    /// - Has opaque_to_smt attribute (hidden but used)
    /// - Is marked noextract (exists only for proofs)
    /// - Has irreducible attribute
    /// - Has inline_for_extraction (used via inlining)
    fn has_unsafe_removal_pattern(&self, block_text: &str) -> bool {
        // SMT patterns make bindings auto-triggered
        if SMTPAT_OPEN_RE.is_match(block_text) || SMTPATOR_PATTERN.is_match(block_text) {
            return true;
        }

        // Opaque bindings are hidden but semantically used
        if OPAQUE_TO_SMT_ATTR.is_match(block_text) || OPAQUE_ATTR.is_match(block_text) {
            return true;
        }

        // Noextract means it exists only for proofs
        if NOEXTRACT_RE.is_match(block_text) {
            return true;
        }

        // Irreducible definitions don't unfold but are used
        if IRREDUCIBLE_ATTR.is_match(block_text) {
            return true;
        }

        // Inline for extraction means used via inlining
        if INLINE_FOR_EXTRACTION_RE.is_match(block_text) {
            return true;
        }

        // Abstract types are part of module interface
        if ABSTRACT_TYPE.is_match(block_text) {
            return true;
        }

        // Ghost/GTot/erased return types indicate spec-only code
        if GTOT_RETURN.is_match(block_text) || GHOST_RETURN.is_match(block_text) {
            return true;
        }

        // Functions returning erased types are spec-only
        if ERASED_RETURN.is_match(block_text) {
            return true;
        }

        // [@@"substitute"] attribute means used by normalizer
        if SUBSTITUTE_ATTR.is_match(block_text) {
            return true;
        }

        false
    }

    /// Check if the file is an interface file (.fsti).
    /// Interface files define the public API and private bindings in them
    /// should never be flagged as unused (they're exported).
    fn is_interface_file(&self, file: &Path) -> bool {
        file.extension()
            .map(|ext| ext == "fsti")
            .unwrap_or(false)
    }

    /// Check if the content contains friend declarations.
    /// If a module has friends, private bindings might be used by those friends.
    fn has_friend_declarations(&self, content: &str) -> bool {
        content.lines().any(|line| FRIEND_DECL.is_match(line))
    }

    /// Check if the module is a Spec.* module (verification-only specification).
    ///
    /// In HACL* and similar projects, modules named `Spec.*` contain pure
    /// mathematical specifications used for verification. Their bindings are
    /// referenced by implementation modules during proof, even if not directly
    /// called. Private bindings in Spec modules serve as internal proof helpers.
    fn is_spec_module(&self, content: &str) -> bool {
        for line in content.lines().take(5) {
            if let Some(caps) = MODULE_DECL.captures(line) {
                if let Some(name) = caps.get(1) {
                    let module_name = name.as_str();
                    return module_name.starts_with("Spec.")
                        || module_name == "Spec";
                }
            }
        }
        false
    }

    /// Check if a block type represents a definition that is inherently "used"
    /// by the F* compiler/solver infrastructure, even without explicit references.
    ///
    /// These block types should NEVER be flagged as unused:
    /// - Instance: type class instances are resolved by the instance resolution mechanism
    /// - Class: type class declarations define the resolution interface
    /// - UnfoldLet: `unfold let` bindings are used by the F* normalizer
    /// - InlineLet: `inline_for_extraction let` bindings are used at extraction
    /// - Effect/NewEffect/SubEffect/EffectAbbrev: effect system definitions
    fn is_infrastructure_block_type(&self, block_type: BlockType) -> bool {
        matches!(
            block_type,
            BlockType::Instance
                | BlockType::Class
                | BlockType::UnfoldLet
                | BlockType::InlineLet
                | BlockType::Effect
                | BlockType::NewEffect
                | BlockType::SubEffect
                | BlockType::EffectAbbrev
        )
    }

    /// Generate a safety warning message based on the safety level.
    fn safety_warning_suffix(&self, safety: DeadCodeSafetyLevel) -> &'static str {
        match safety {
            DeadCodeSafetyLevel::Safe => "",
            DeadCodeSafetyLevel::Caution => {
                " NOTE: This binding might be used by friend modules or via reflection."
            }
            DeadCodeSafetyLevel::Unsafe => {
                " WARNING: This binding has attributes suggesting it IS used. Do NOT remove automatically."
            }
        }
    }

    // ==========================================================================
    // UNUSED BINDING CHECKS
    // ==========================================================================

    /// Check for unused private bindings (let, type, val).
    ///
    /// A private binding is considered unused if:
    /// - It has the `private` keyword
    /// - Its name is not referenced anywhere in the same file
    /// - It does not have the `[@unused]` attribute
    /// - It is not an SMTPat lemma (auto-triggered by solver)
    /// - It is not a ghost/erased binding (exists for proofs only)
    /// - It is not a private val that has a corresponding let with the same name
    ///
    /// SAFETY: This check is VERY conservative because removing code in F* is risky:
    /// - SMTPat bindings are auto-triggered by the solver
    /// - Private bindings may be used by friend modules
    /// - Opaque/noextract bindings exist for proofs only
    fn check_unused_private_bindings(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // SAFETY: Interface files (.fsti) define the public API.
        // Private bindings in .fsti are still part of the interface - DO NOT flag them.
        if self.is_interface_file(file) {
            return diagnostics;
        }

        let (_, blocks) = parse_fstar_file(content);

        // Check if file has friend declarations - affects safety level
        let has_friends = self.has_friend_declarations(content);

        // SAFETY: Spec.* modules are verification-only specifications.
        // All their bindings are used for proof, not runtime.
        let is_spec_module = self.is_spec_module(content);

        // Collect all defined names with their metadata
        // Map: name -> (line_number, is_private, block_text, block_type)
        let mut defined: HashMap<String, (usize, bool, String, BlockType)> = HashMap::new();

        // Collect all references across the file
        let mut all_references: HashSet<String> = HashSet::new();

        // Track all names that have a let implementation
        // (private val + public let is a valid pattern: val constrains the type)
        let mut names_with_let: HashSet<String> = HashSet::new();

        for block in &blocks {
            let block_text = block.lines.join("");

            // Detect private: must be at declaration level, not in comments.
            // Check that "private" appears before the first name definition.
            let is_private = self.is_genuinely_private(&block_text);

            // Check for [@unused] attribute which suppresses this warning
            let has_unused_attr = UNUSED_ATTR.is_match(&block_text);

            for name in &block.names {
                // Store definition info (but skip if has unused attribute)
                if !has_unused_attr {
                    defined.insert(
                        name.clone(),
                        (block.start_line, is_private, block_text.clone(), block.block_type),
                    );
                }

                // Track names that have let implementations
                if matches!(
                    block.block_type,
                    BlockType::Let | BlockType::UnfoldLet | BlockType::InlineLet
                ) {
                    names_with_let.insert(name.clone());
                }
            }

            // Accumulate all references
            all_references.extend(block.references.iter().cloned());
        }

        // Find unused private bindings
        for (name, (line, is_private, block_text, block_type)) in &defined {
            if !is_private {
                continue;
            }

            // Skip if the name is referenced anywhere
            if all_references.contains(name) {
                continue;
            }

            // Skip infrastructure block types that are inherently "used" by F*:
            // - Instance: type class instances are used by resolution
            // - Class: type class declarations define resolution interface
            // - UnfoldLet: `unfold let` bindings are used by the normalizer
            // - InlineLet: `inline_for_extraction let` are used at extraction
            // - Effect/NewEffect/SubEffect/EffectAbbrev: effect system definitions
            if self.is_infrastructure_block_type(*block_type) {
                continue;
            }

            // Skip private val declarations if they have a corresponding let.
            // The val provides the type signature; the let provides the implementation.
            // Together they form one logical unit.
            if *block_type == BlockType::Val && names_with_let.contains(name) {
                continue;
            }

            // Skip private val declarations with Lemma return type even without
            // a corresponding let. Lemma val declarations serve as axiom-like
            // specifications or are implemented in friend modules.
            if *block_type == BlockType::Val && self.has_lemma_return_type(block_text) {
                continue;
            }

            // Skip private val declarations with GTot/Ghost return type.
            // These are spec-only type signatures.
            if *block_type == BlockType::Val
                && (GTOT_RETURN.is_match(block_text) || GHOST_RETURN.is_match(block_text))
            {
                continue;
            }

            // Skip all private bindings in Spec.* modules.
            // In HACL* and similar projects, Spec modules are pure mathematical
            // specifications. Their private bindings are internal proof helpers
            // referenced by implementation modules during verification.
            if is_spec_module {
                continue;
            }

            // Heuristic: skip common naming patterns that indicate intentional unused bindings
            // - Names starting with underscore (conventional "unused" marker)
            // - Names containing "test" or "lemma" (often standalone proofs)
            // - Names containing "unused" (explicit marker)
            if name.starts_with('_')
                || name.to_lowercase().contains("test")
                || name.to_lowercase().contains("lemma")
                || name.to_lowercase().contains("unused")
            {
                continue;
            }

            // SAFETY: Skip if the binding has unsafe removal patterns.
            // These indicate the binding IS used even if we can't see the usage:
            // - SMTPat/SMTPatOr (auto-triggered by solver)
            // - opaque_to_smt (hidden but used)
            // - noextract (exists only for proofs)
            // - inline_for_extraction (used via inlining)
            // - irreducible (doesn't unfold but used)
            if self.has_unsafe_removal_pattern(block_text) {
                continue;
            }

            // Skip if the binding has SMTPat -- these lemmas are auto-triggered
            // by the SMT solver and don't need explicit call sites.
            // NOTE: This is redundant with has_unsafe_removal_pattern but kept for clarity.
            if SMTPAT_OPEN_RE.is_match(block_text) || SMTPATOR_PATTERN.is_match(block_text) {
                continue;
            }

            // Skip ghost let bindings -- they exist purely for proof purposes
            // and may not be explicitly referenced.
            if block_text.contains("ghost let ") || block_text.contains("ghost\nlet ") {
                continue;
            }

            // Skip if the binding has Lemma return type -- private lemmas
            // often exist to help the solver without explicit call sites,
            // especially when combined with attributes like [@@"opaque_to_smt"].
            if self.has_lemma_return_type(block_text) {
                continue;
            }

            // Skip assume val -- these are axioms and must NEVER be removed
            if ASSUME_VAL_PATTERN.is_match(block_text) {
                continue;
            }

            // Determine the kind of binding for a more specific message
            let kind = if block_text.contains("type ") {
                "type"
            } else if block_text.contains("val ") {
                "val"
            } else {
                "let binding"
            };

            // Determine safety level for the message
            let safety = self.determine_binding_safety(block_text, file);
            let friend_warning = if has_friends {
                " This module has friend declarations - the binding may be used by friend modules."
            } else {
                ""
            };

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST005,
                severity: DiagnosticSeverity::Warning,
                file: file.to_path_buf(),
                range: Range::point(*line, 1),
                message: format!(
                    "Private {} `{}` is never used in this module. \
                     Consider removing it or adding `[@unused]` attribute if intentional.{}{}",
                    kind, name, friend_warning, self.safety_warning_suffix(safety)
                ),
                // SAFETY: Never auto-remove bindings. This is too risky in F*.
                // The user must manually verify the binding is truly unused.
                fix: None,
            });
        }

        diagnostics
    }

    /// Check for unreachable code after bottom values.
    ///
    /// In F*, `assert false` and `admit()` are "bottom" values that
    /// terminate execution/proof. Any code after them on the same
    /// logical statement is unreachable.
    fn check_unreachable_after_bottom(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1; // 1-indexed

            // Check for assert false
            if let Some(m) = ASSERT_FALSE.find(line) {
                if let Some(diag) =
                    self.check_code_after_match(file, line, line_num, m.end(), "assert false")
                {
                    diagnostics.push(diag);
                }
            }

            // Check for admit()
            if let Some(m) = ADMIT_PATTERN.find(line) {
                if let Some(diag) =
                    self.check_code_after_match(file, line, line_num, m.end(), "admit()")
                {
                    diagnostics.push(diag);
                }
            }

            // Check for false_elim()
            if let Some(m) = FALSE_ELIM_PATTERN.find(line) {
                if let Some(diag) =
                    self.check_code_after_match(file, line, line_num, m.end(), "false_elim()")
                {
                    diagnostics.push(diag);
                }
            }

            // Check for absurd()
            if let Some(m) = ABSURD_PATTERN.find(line) {
                if let Some(diag) =
                    self.check_code_after_match(file, line, line_num, m.end(), "absurd()")
                {
                    diagnostics.push(diag);
                }
            }
        }

        diagnostics
    }

    /// Helper to check if there's meaningful code after a bottom expression.
    fn check_code_after_match(
        &self,
        file: &Path,
        line: &str,
        line_num: usize,
        match_end: usize,
        pattern_name: &str,
    ) -> Option<Diagnostic> {
        let after = &line[match_end..];
        let trimmed = after.trim();

        // Skip if nothing follows, or only comments/closing parens
        if trimmed.is_empty()
            || trimmed.starts_with("//")
            || trimmed.starts_with("(*")
            || trimmed.starts_with(")")
            || trimmed.starts_with("}")
            || trimmed.starts_with("]")
            || trimmed == "end"
        {
            return None;
        }

        Some(Diagnostic {
            rule: RuleCode::FST005,
            severity: DiagnosticSeverity::Warning,
            file: file.to_path_buf(),
            range: Range::point(line_num, match_end + 1),
            message: format!(
                "Code after `{}` is unreachable. \
                 This expression diverges and never returns.",
                pattern_name
            ),
            fix: None,
        })
    }

    /// Check for unused function parameters.
    ///
    /// A parameter is considered unused if:
    /// - It appears in the function signature as `(name : type)`
    /// - It is not referenced ANYWHERE in the block text after its definition
    ///   (this covers: other params' types, return type, spec clauses, AND the body)
    /// - It does not already start with underscore (conventional "unused" marker)
    /// - It is not a proof witness type (squash, erased, unit refinement)
    /// - It is not an implicit parameter (#param)
    ///
    /// IMPORTANT: Val declarations (type signatures) should NOT have unused parameter
    /// warnings - they don't have bodies. Parameters in val are part of the interface.
    ///
    /// IMPORTANT: In F*, parameters can be "used" in many places before the body:
    /// - Other parameters' types: `(x:t) (y:depends_on x)` -- x is used in y's type
    /// - Return type annotations: `(x:t) : result_type x` -- x is used in return type
    /// - Lemma specifications: `(x:t) : Lemma (property x)` -- x is used in spec
    /// - requires/ensures/decreases clauses
    /// - The actual function body after `=`
    ///
    /// We handle ALL of these by checking if the parameter name appears anywhere
    /// in the block text AFTER its own definition `(param :`.
    ///
    /// Provides autofix to add underscore prefix to the parameter name.
    fn check_unused_parameters(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let (_, blocks) = parse_fstar_file(content);
        let lines: Vec<&str> = content.lines().collect();

        for block in &blocks {
            // Only check let bindings, NOT val declarations.
            // Val declarations are type signatures - they have no body.
            if !matches!(block.block_type, BlockType::Let) {
                continue;
            }

            let text = block.lines.join("");

            // Skip if block has SMTPat/SMTPatOr - parameters may be used for triggering
            if SMTPAT_OPEN_RE.is_match(&text) || SMTPATOR_PATTERN.is_match(&text) {
                continue;
            }

            // Skip ghost let bindings - they exist for proofs, params may be
            // intentionally unused at runtime.
            if text.contains("ghost let ") || text.contains("ghost\nlet ") {
                continue;
            }

            // Skip if has unsafe removal patterns (noextract, opaque, etc.)
            // Parameters in these functions may be intentionally unused at runtime.
            if self.has_unsafe_removal_pattern(&text) {
                continue;
            }

            // Must have a body (contains `=` somewhere meaningful).
            // We no longer rely on finding the definition `=` to split sig/body,
            // since `=` can appear in refinement types `{x = 0}`. Instead, we
            // check for param usage AFTER the param's own definition.
            if !text.contains('=') {
                continue;
            }

            // Extract parameter names from the text (anywhere in the block).
            // PARAM_EXTRACT_RE matches `(name :` which is F*'s parameter syntax.
            for caps in PARAM_EXTRACT_RE.captures_iter(&text) {
                let (Some(full_match), Some(param_match)) = (caps.get(0), caps.get(1)) else {
                    continue;
                };
                let param = param_match.as_str();

                // Skip if already underscore-prefixed (intentionally unused)
                if param.starts_with('_') {
                    continue;
                }

                // Skip common parameter names that are often intentionally unused
                if param == "unit" {
                    continue;
                }

                // Skip if this is a proof witness parameter (squash, erased, unit refinement).
                if self.is_proof_witness_param(&text, param) {
                    continue;
                }

                // Skip if this is an implicit parameter (#param).
                if self.is_implicit_param(&text, param) {
                    continue;
                }

                // Check if the parameter is used AFTER its definition.
                // The definition is `(param :`, so we look at everything after that match.
                let after_def = &text[full_match.end()..];
                let param_pattern = format!(r"\b{}\b", regex::escape(param));
                if let Ok(re) = Regex::new(&param_pattern) {
                    if !re.is_match(after_def) {
                        // Parameter is not used anywhere after its definition
                        let param_fix =
                            self.find_param_position(&lines, block.start_line, param);

                        // SAFETY: Adding underscore prefix is SAFE - it doesn't break code.
                        // This is a standard F* convention for unused parameters.
                        // We use high confidence because this transformation is always safe.
                        let fix = param_fix.map(|(line_num, col_start, col_end)| {
                            Fix::safe(
                                format!("Add underscore prefix to `{}`", param),
                                vec![Edit {
                                    file: file.to_path_buf(),
                                    range: Range::new(line_num, col_start, line_num, col_end),
                                    new_text: format!("_{}", param),
                                }],
                            )
                            .with_safety_level(FixSafetyLevel::Safe)  // Safe: just renaming
                            .with_reversible(true)  // Can remove underscore prefix
                            .with_requires_review(false)  // No review needed for safe rename
                        });

                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST005,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(block.start_line, 1),
                            message: format!(
                                "Parameter `{}` is unused. Prefix with underscore: `_{}`",
                                param, param
                            ),
                            fix,
                        });
                    }
                }
            }
        }

        diagnostics
    }

    /// Check if "private" in block text is genuinely at declaration level.
    ///
    /// Avoids matching "private" inside comments or string literals.
    /// A genuine private keyword appears at the start of the block text
    /// (possibly after attributes and whitespace).
    fn is_genuinely_private(&self, block_text: &str) -> bool {
        // Check each line: "private" must appear at the start of a non-indented line,
        // or right after attributes. For multi-line blocks, we check the first
        // non-comment, non-attribute line.
        for line in block_text.lines() {
            let trimmed = line.trim();
            // Skip empty lines and comments
            if trimmed.is_empty() || trimmed.starts_with("(*") || trimmed.starts_with("//") {
                continue;
            }
            // Skip attribute lines
            if trimmed.starts_with("[@") || trimmed.starts_with("[@@") {
                continue;
            }
            // Skip push/pop/set options
            if trimmed.starts_with("#push") || trimmed.starts_with("#pop") || trimmed.starts_with("#set") {
                continue;
            }
            // This is the declaration line: check if it starts with "private"
            return trimmed.starts_with("private ");
        }
        false
    }

    /// Check if a block has a Lemma return type.
    ///
    /// F* lemmas are proofs, not runtime code. Private lemmas often exist
    /// to assist the SMT solver or establish intermediate proof steps.
    fn has_lemma_return_type(&self, block_text: &str) -> bool {
        // Match `: Lemma` or `: Lemma (` in the block text.
        // Also match `Lemma` after various effect combinators.
        lazy_static! {
            static ref LEMMA_RETURN: Regex =
                Regex::new(r":\s*(?:Tot\s+|GTot\s+|Ghost\s+)?Lemma\b").unwrap_or_else(|e| panic!("regex: {e}"));
        }
        LEMMA_RETURN.is_match(block_text)
    }

    /// Check if a parameter is a proof witness type (squash, erased, unit refinement).
    ///
    /// In F*, these parameter types carry compile-time proofs but are erased at runtime:
    /// - `(u:squash condition)` - proof that condition holds
    /// - `(x:erased t)` or `(x:Ghost.erased t)` - ghost/erased values
    /// - `(u: unit { constraint })` - unit carrying a refinement
    fn is_proof_witness_param(&self, signature: &str, param: &str) -> bool {
        // Look for the parameter definition pattern and check its type
        let param_def_pattern = format!(r"\(\s*{}\s*:\s*(\w+)", regex::escape(param));
        if let Ok(re) = Regex::new(&param_def_pattern) {
            if let Some(caps) = re.captures(signature) {
                if let Some(type_match) = caps.get(1) {
                    let type_name = type_match.as_str();
                    // Check for proof witness types
                    if type_name == "squash"
                        || type_name == "erased"
                        || type_name == "Ghost"
                    {
                        return true;
                    }
                }
            }
        }

        // Also check for unit refinement: `(param : unit { ... })`
        let unit_ref_pattern = format!(r"\(\s*{}\s*:\s*unit\s*\{{", regex::escape(param));
        if let Ok(re) = Regex::new(&unit_ref_pattern) {
            if re.is_match(signature) {
                return true;
            }
        }

        false
    }

    /// Check if a parameter is an implicit parameter (#param).
    ///
    /// Implicit parameters in F* are resolved by type inference and may not
    /// appear explicitly in the function body.
    fn is_implicit_param(&self, signature: &str, param: &str) -> bool {
        // Look for `#param` or `(#param : type)` pattern
        let implicit_pattern = format!(r"#\s*{}\b", regex::escape(param));
        if let Ok(re) = Regex::new(&implicit_pattern) {
            return re.is_match(signature);
        }
        false
    }

    /// Find the exact position of a parameter in the source for autofix.
    ///
    /// Returns (line_number, column_start, column_end) if found.
    fn find_param_position(
        &self,
        lines: &[&str],
        start_line: usize,
        param: &str,
    ) -> Option<(usize, usize, usize)> {
        // Search within a reasonable range from the block start
        let search_end = (start_line + 10).min(lines.len());

        for line_idx in (start_line.saturating_sub(1))..search_end {
            let line = lines.get(line_idx)?;
            // Look for `(param :` pattern - escape the paren for regex
            let pattern = format!(r"\({}\s*:", regex::escape(param));
            if let Ok(re) = Regex::new(&pattern) {
                if let Some(m) = re.find(line) {
                    // The parameter name starts after the opening paren
                    let col_start = m.start() + 2; // 1-indexed, after '('
                    let col_end = col_start + param.len();
                    return Some((line_idx + 1, col_start, col_end));
                }
            }
        }
        None
    }

    /// Check for discarded non-unit results via `let _ = expr in`.
    ///
    /// In F*, `let _ = f x in body` discards the return value of `f x`.
    /// When `f` returns a meaningful value (not unit), this is often a bug:
    /// - Discarding error codes (e.g., `let _ = ecdsa_sign msg sk nonce in`)
    /// - Ignoring return values that indicate success/failure
    ///
    /// Known safe patterns that are NOT flagged:
    /// - `let _ = assert ...` / `let _ = assert_norm ...` (proof obligations)
    /// - `let _ = allow_inversion ...` (type inversion hints)
    /// - `let _ = print ...` / `let _ = IO.print_string ...` (side effects)
    /// - `let _ = B.recall ...` / `let _ = recall ...` (memory model hints)
    /// - `let _ = norm_spec ...` (normalization hints)
    /// - `let _ = Classical. ...` (classical logic lemmas)
    /// - `[@inline_let] let _ = ...` (inline proof hints)
    fn check_discarded_results(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let trimmed = line.trim();

            // Match `let _ = expr in` or `let () = expr in` patterns.
            // These discard the result of expr.
            if let Some(caps) = LET_DISCARD.captures(trimmed) {
                if let Some(expr_match) = caps.get(1) {
                    let expr = expr_match.as_str().trim();

                    // Skip empty expressions
                    if expr.is_empty() {
                        continue;
                    }

                    // Skip known safe patterns (proofs, assertions, side-effects)
                    if SAFE_DISCARD_FUNCS.is_match(expr) {
                        continue;
                    }

                    // Skip if the line or the PREVIOUS line has [@inline_let] attribute.
                    // F* often puts the attribute on a separate line:
                    //   [@inline_let]
                    //   let _ = c.state.invariant_loc_in_footprint #i in
                    if trimmed.contains("@inline_let") {
                        continue;
                    }
                    if line_idx > 0 {
                        let prev_line = lines[line_idx - 1].trim();
                        if prev_line.contains("@inline_let") {
                            continue;
                        }
                    }

                    // Skip expressions that are clearly unit-returning:
                    // - Literals like `()`, `true`, `false`
                    // - Simple assignments
                    if expr == "()" || expr == "true" || expr == "false" {
                        continue;
                    }

                    // Skip if expression calls a known lemma pattern
                    // (function names ending in _lemma, _fact, _aux that return unit proofs)
                    if expr.contains("_lemma")
                        || expr.contains("_fact")
                        || expr.contains("hmac_input_bound")
                    {
                        continue;
                    }

                    // Skip record field method calls that look like proof obligations.
                    // Pattern: `c.field.method` or `c.field.method #i`
                    // These are commonly type class methods or frame lemmas in F*.
                    // Examples: c.state.frame_freeable, c.key.invariant_loc_in_footprint
                    let func_name_tmp = expr.split_whitespace().next().unwrap_or("");
                    if func_name_tmp.contains('.') {
                        let parts: Vec<&str> = func_name_tmp.split('.').collect();
                        if let Some(last) = parts.last() {
                            // Common proof-obligation method names in F* records
                            if last.starts_with("frame_")
                                || last.starts_with("invariant_")
                                || last.contains("_loc_in_")
                                || last.contains("_footprint")
                                || last.contains("_freeable")
                            {
                                continue;
                            }
                        }
                    }

                    // Extract the function name (first identifier in the expression)
                    let func_name = expr.split_whitespace().next().unwrap_or("");

                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST005,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "Result of `{}` is discarded via `let _ = ... in`. \
                             If the function returns a meaningful value (not unit), \
                             this may be a bug. Consider binding to a named variable \
                             or using `let () = ... in` if the function returns unit.",
                            func_name
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for unreachable match branches after wildcard pattern.
    ///
    /// In F*, a wildcard `| _ ->` matches everything, so any branches
    /// after it are unreachable.
    fn check_unreachable_branches(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let lines: Vec<&str> = content.lines().collect();

        let mut in_match = false;
        let mut found_wildcard = false;
        let mut wildcard_line = 0;
        let mut match_indent = 0;

        for (line_idx, line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;
            let stripped = line.trim();

            // Calculate current line's indentation
            let current_indent = line.len() - line.trim_start().len();

            // Track match expressions
            if stripped.starts_with("match ") || stripped.contains(" match ") {
                in_match = true;
                found_wildcard = false;
                match_indent = current_indent;
            }

            if in_match {
                // Check for wildcard pattern, but NOT guarded wildcards.
                // `| _ ->` catches everything (unguarded wildcard).
                // `| _ when cond ->` does NOT catch everything (guarded wildcard).
                if MATCH_WILDCARD.is_match(stripped)
                    && !MATCH_GUARDED_WILDCARD.is_match(stripped)
                    && !found_wildcard
                {
                    found_wildcard = true;
                    wildcard_line = line_num;
                }
                // Check for branch after wildcard (unreachable)
                else if found_wildcard && stripped.starts_with('|') {
                    // Make sure we're still in the same match (same or greater indent)
                    if current_indent >= match_indent {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST005,
                            severity: DiagnosticSeverity::Warning,
                            file: file.to_path_buf(),
                            range: Range::point(line_num, 1),
                            message: format!(
                                "Unreachable match branch after wildcard pattern at line {}",
                                wildcard_line
                            ),
                            fix: None,
                        });
                    }
                }

                // End of match detection (heuristic):
                // - Non-empty line at same or lower indentation that isn't a branch
                // - Or a new declaration keyword
                if !stripped.is_empty()
                    && current_indent <= match_indent
                    && !stripped.starts_with('|')
                    && !stripped.starts_with("match ")
                    && !stripped.contains(" match ")
                {
                    // Check for keywords that definitely end a match
                    if stripped.starts_with("let ")
                        || stripped.starts_with("val ")
                        || stripped.starts_with("type ")
                        || stripped.starts_with("in ")
                        || stripped == "in"
                    {
                        in_match = false;
                        found_wildcard = false;
                    }
                }
            }
        }

        diagnostics
    }
}

impl Default for DeadCodeRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for DeadCodeRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST005
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        diagnostics.extend(self.check_unused_private_bindings(file, content));
        diagnostics.extend(self.check_unreachable_after_bottom(file, content));
        diagnostics.extend(self.check_unused_parameters(file, content));
        diagnostics.extend(self.check_unreachable_branches(file, content));
        diagnostics.extend(self.check_discarded_results(file, content));
        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    // =========================================================================
    // Tests for unused private bindings
    // =========================================================================

    #[test]
    fn test_unused_private_binding() {
        let content = r#"module Test

open FStar.All

private let internal_helper x = x + 1

let public_func y = y * 2
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_binding_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert_eq!(unused_binding_diags.len(), 1);
        assert!(unused_binding_diags[0].message.contains("internal_helper"));
    }

    #[test]
    fn test_used_private_binding() {
        let content = r#"module Test

private let helper x = x + 1

let public_func y = helper y
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // helper is used by public_func, so no diagnostic
        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Expected no unused binding warnings"
        );
    }

    #[test]
    fn test_underscore_prefix_ignored() {
        let content = r#"module Test

private let _intentionally_unused x = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // Names starting with _ are ignored
        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(unused_diags.is_empty());
    }

    // =========================================================================
    // Tests for unreachable code after bottom values
    // =========================================================================

    #[test]
    fn test_unreachable_after_assert_false() {
        let content = r#"module Test

let impossible () =
  assert false; let x = 1 in x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("unreachable") || d.message.contains("Unreachable"))
            .collect();
        assert_eq!(unreachable_diags.len(), 1);
    }

    #[test]
    fn test_assert_false_at_end_ok() {
        let content = r#"module Test

let impossible () =
  assert false;
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // No code after assert false, so no diagnostic for that
        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Code after"))
            .collect();
        assert!(unreachable_diags.is_empty());
    }

    #[test]
    fn test_unreachable_after_admit() {
        let content = r#"module Test

let bogus () =
  admit(); let result = 42 in result
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("admit()"))
            .collect();
        assert_eq!(unreachable_diags.len(), 1);
    }

    // =========================================================================
    // Tests for unused function parameters
    // =========================================================================

    #[test]
    fn test_unused_parameter_detected() {
        let content = r#"module Test

let add_one (unused_param : int) (x : int) : int = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert_eq!(param_diags.len(), 1);
        assert!(param_diags[0].message.contains("unused_param"));
        assert!(param_diags[0].message.contains("_unused_param"));
    }

    #[test]
    fn test_used_parameter_no_warning() {
        let content = r#"module Test

let add (a : int) (b : int) : int = a + b
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(param_diags.is_empty());
    }

    #[test]
    fn test_underscore_prefixed_param_ignored() {
        let content = r#"module Test

let const (x : int) (_ignored : int) : int = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("_ignored"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Underscore-prefixed params should be ignored"
        );
    }

    #[test]
    fn test_unused_parameter_has_autofix() {
        let content = r#"module Test

let identity (phantom : int) (x : int) : int = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("phantom"))
            .collect();

        assert_eq!(param_diags.len(), 1);
        assert!(
            param_diags[0].fix.is_some(),
            "Expected autofix for unused parameter"
        );

        let fix = param_diags[0].fix.as_ref().unwrap();
        assert!(fix.message.contains("underscore"));
        assert!(!fix.edits.is_empty());
        assert_eq!(fix.edits[0].new_text, "_phantom");
    }

    #[test]
    fn test_multiple_unused_parameters() {
        let content = r#"module Test

let ignore_all (a : int) (b : int) (c : int) : int = 42
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        // All three parameters are unused
        assert_eq!(param_diags.len(), 3);
    }

    // =========================================================================
    // Tests for unreachable match branches
    // =========================================================================

    #[test]
    fn test_unreachable_branch_after_wildcard() {
        let content = r#"module Test

let classify x =
  match x with
  | 0 -> "zero"
  | _ -> "other"
  | 1 -> "one"
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        assert_eq!(branch_diags.len(), 1);
        assert!(branch_diags[0].message.contains("wildcard"));
    }

    #[test]
    fn test_wildcard_at_end_ok() {
        let content = r#"module Test

let classify x =
  match x with
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        assert!(
            branch_diags.is_empty(),
            "Wildcard at end should not trigger warning"
        );
    }

    #[test]
    fn test_multiple_unreachable_branches() {
        let content = r#"module Test

let bad_match x =
  match x with
  | 0 -> "zero"
  | _ -> "catch-all"
  | 1 -> "one"
  | 2 -> "two"
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        // Both `| 1 ->` and `| 2 ->` are unreachable
        assert_eq!(branch_diags.len(), 2);
    }

    #[test]
    fn test_no_match_no_warning() {
        let content = r#"module Test

let simple x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        assert!(branch_diags.is_empty());
    }

    #[test]
    fn test_nested_match_expressions() {
        let content = r#"module Test

let nested x y =
  match x with
  | 0 ->
    match y with
    | 0 -> "both zero"
    | _ -> "x zero"
  | _ -> "x not zero"
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // No unreachable branches - all wildcards are at the end
        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        assert!(branch_diags.is_empty());
    }

    // =========================================================================
    // Integration tests
    // =========================================================================

    #[test]
    fn test_combined_dead_code_issues() {
        // Note: Use `internal_helper` instead of `unused_helper` because names
        // containing "unused" are intentionally skipped by the heuristic.
        let content = r#"module Test

private let internal_helper x = x

let bad_function (phantom : int) (y : int) : int =
  match y with
  | 0 -> 0
  | _ -> 1
  | 2 -> 2
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // Should detect:
        // 1. Unused private binding: internal_helper
        // 2. Unused parameter: phantom
        // 3. Unreachable branch: | 2 -> 2

        let unused_binding = diags.iter().any(|d| d.message.contains("internal_helper"));
        let unused_param = diags.iter().any(|d| d.message.contains("phantom"));
        let unreachable = diags
            .iter()
            .any(|d| d.message.contains("Unreachable match"));

        assert!(unused_binding, "Should detect unused private binding");
        assert!(unused_param, "Should detect unused parameter");
        assert!(unreachable, "Should detect unreachable branch");
    }

    #[test]
    fn test_unused_attr_suppresses_all() {
        let content = r#"module Test

[@unused]
private let intentionally_unused x = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(unused_diags.is_empty(), "[@unused] should suppress warning");
    }

    // =========================================================================
    // Tests for unreachable code after false_elim() and absurd()
    // =========================================================================

    #[test]
    fn test_unreachable_after_false_elim() {
        let content = r#"module Test

let handle_impossible () =
  false_elim(); let x = 1 in x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("false_elim()"))
            .collect();
        assert_eq!(
            unreachable_diags.len(),
            1,
            "Should detect unreachable code after false_elim()"
        );
    }

    #[test]
    fn test_unreachable_after_absurd() {
        let content = r#"module Test

let handle_absurd () =
  absurd(); let x = 1 in x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("absurd()"))
            .collect();
        assert_eq!(
            unreachable_diags.len(),
            1,
            "Should detect unreachable code after absurd()"
        );
    }

    #[test]
    fn test_false_elim_at_end_ok() {
        let content = r#"module Test

let handle_impossible () =
  false_elim()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unreachable_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Code after"))
            .collect();
        assert!(
            unreachable_diags.is_empty(),
            "false_elim() at end should not trigger warning"
        );
    }

    // =========================================================================
    // Tests for discarded results (let _ = expr in)
    // =========================================================================

    #[test]
    fn test_discarded_result_flagged() {
        let content = r#"module Test

let process () =
  let _ = K256.ecdsa_sign_hashed_msg sgnt msgHash sk nonce in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert_eq!(
            discard_diags.len(),
            1,
            "Should flag discarded result from K256.ecdsa_sign_hashed_msg"
        );
        assert!(discard_diags[0].severity == DiagnosticSeverity::Hint);
    }

    #[test]
    fn test_discarded_assert_norm_ok() {
        let content = r#"module Test

let check () =
  let _ = assert_norm (pow2 31 == 2147483648) in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert!(
            discard_diags.is_empty(),
            "assert_norm should not be flagged as discarded result"
        );
    }

    #[test]
    fn test_discarded_allow_inversion_ok() {
        let content = r#"module Test

let process (a : hash_alg) =
  let _ = allow_inversion hash_alg in
  a
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert!(
            discard_diags.is_empty(),
            "allow_inversion should not be flagged"
        );
    }

    #[test]
    fn test_discarded_inline_let_ok() {
        let content = r#"module Test

let process () =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert!(
            discard_diags.is_empty(),
            "[@inline_let] let _ should not be flagged"
        );
    }

    #[test]
    fn test_discarded_recall_ok() {
        let content = r#"module Test

let process () =
  let _ = B.recall vs in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert!(
            discard_diags.is_empty(),
            "B.recall should not be flagged as discarded result"
        );
    }

    #[test]
    fn test_discarded_function_call_flagged() {
        let content = r#"module Test

let process () =
  let _ = Hacl.Hash.Blake2s_128.init p in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert_eq!(
            discard_diags.len(),
            1,
            "Should flag discarded result from Hacl.Hash.Blake2s_128.init"
        );
    }

    #[test]
    fn test_discarded_print_ok() {
        let content = r#"module Test

let process () =
  let _ = print "hello" in
  ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let discard_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("discarded"))
            .collect();
        assert!(
            discard_diags.is_empty(),
            "print should not be flagged as discarded result"
        );
    }

    // =========================================================================
    // FALSE POSITIVE REGRESSION TESTS
    // Patterns from real F* codebases (everparse, hacl-star) that must NOT
    // generate spurious warnings.
    // =========================================================================

    #[test]
    fn test_fp_param_used_in_return_type() {
        // Dependent return types: params used in the return type are NOT unused.
        // Common in lowparse combinators.
        let content = r#"module Test

let tag_of_payload
  (min : nat)
  (max : nat)
  (s : serializer)
  (x : bounded_vldata_strong_t min max s)
  : bounded_int32 min max
= compute_tag s x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Params used in return type should not be flagged: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_param_used_in_lemma_spec() {
        // Lemma params used in the specification, not the body.
        let content = r#"module Test

let my_proof (a : nat) (b : nat) : Lemma (a + b >= 0) = ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Params used in Lemma spec should not be flagged: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_param_used_in_dependent_type() {
        // Later param's type depends on earlier param.
        let content = r#"module Test

let dep_func (n : nat) (v : vec n) : nat = length v
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Params used in dependent types should not be flagged: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_equals_in_refinement_type() {
        // The `=` in refinement type `{x = 0}` must not confuse sig/body detection.
        let content = r#"module Test

let refine_func (y : int) (x : int{x = 0}) : int = y + x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Params should not be falsely flagged due to = in refinement: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_private_smtpat_lemma() {
        // Private lemmas with SMTPat are auto-triggered by the SMT solver.
        let content = r#"module Test

private let nat_mult_is_nat (a : nat) (b : nat)
  : Lemma (a * b >= 0)
  [SMTPat (a * b)]
= ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private SMTPat lemmas should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_lemma_return_type() {
        // Private lemmas exist as proof helpers.
        let content = r#"module Test

private let div_nat_is_nat (a : nat) (b : pos) : Lemma (a / b >= 0) = ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private lemmas should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_val_with_let() {
        // private val + let is valid: val constrains the type.
        let content = r#"module Test

private val helper_func : int -> int -> int

let helper_func a b = a + b

let use_it x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("helper_func") && d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private val with corresponding let should not be flagged: {:?}",
            unused_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_ghost_let_binding() {
        // Ghost bindings exist for proofs and are erased at extraction.
        let content = r#"module Test

private ghost let proof_witness = assert (1 + 1 = 2)
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Ghost let bindings should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_guarded_wildcard_not_catch_all() {
        // `| _ when cond ->` does NOT catch everything, branches after it
        // are still reachable.
        let content = r#"module Test

let classify x =
  match x with
  | _ when x > 0 -> "positive"
  | 0 -> "zero"
  | _ -> "negative"
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let branch_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Unreachable match branch"))
            .collect();
        assert!(
            branch_diags.is_empty(),
            "Branches after guarded wildcard should not be flagged: {:?}",
            branch_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_squash_param() {
        // Squash parameters are proof witnesses, intentionally unused at runtime.
        let content = r#"module Test

let guarded_op (p : squash (x > 0)) (x : int) : int = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter `p`"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Squash proof witness params should not be flagged"
        );
    }

    #[test]
    fn test_fp_erased_param() {
        // Ghost.erased parameters exist only for specifications.
        let content = r#"module Test

let spec_func (g : Ghost.erased nat) (x : int) : int = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter `g`"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Ghost.erased params should not be flagged"
        );
    }

    #[test]
    fn test_fp_private_in_comment() {
        // "private" in a comment should NOT make the binding private.
        let content = r#"module Test

(* This is a private helper *)
let normal_func x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used") && d.message.contains("normal_func"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Binding with 'private' only in comment should not be treated as private"
        );
    }

    #[test]
    fn test_fp_param_used_in_requires_ensures() {
        // Parameters used in requires/ensures clauses are not unused.
        let content = r#"module Test

let safe_div (a : int) (b : int)
  : Pure int (requires (b <> 0)) (ensures (fun r -> r * b = a))
= a / b
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Params used in requires/ensures should not be flagged: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_multiline_lowparse_combinator() {
        // Real lowparse pattern with multiline sig, refinement types with `=`,
        // and implicit parameters.
        let content = r#"module Test

let parse_bounded_vlgen_payload
  (min : nat)
  (max : nat { min <= max /\ max < 4294967296 })
  (#k : parser_kind)
  (#t : Type)
  (#p : parser k t)
  (s : serializer p)
  (sz : bounded_int32 min max)
  : parser (parse_bounded_vlgen_payload_kind min max k) (refine_with_tag (tag_of_bounded_vlgen_payload min max s) sz)
= weaken (parse_bounded_vlgen_payload_kind min max k)
    (parse_fldata_strong s (U32.v sz))
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Lowparse combinator params should not be falsely flagged: {:?}",
            param_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // SAFETY FEATURE TESTS
    // Tests for the new safety patterns (opaque, noextract, assume val, etc.)
    // =========================================================================

    #[test]
    fn test_safety_opaque_to_smt_not_flagged() {
        // Bindings with [@"opaque_to_smt"] are hidden but still used by the solver.
        // They must NEVER be flagged as unused.
        let content = r#"module Test

[@@"opaque_to_smt"]
private let secret_impl x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Bindings with opaque_to_smt should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_noextract_not_flagged() {
        // noextract bindings exist only for proofs and are erased at extraction.
        let content = r#"module Test

private noextract let proof_helper x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "noextract bindings should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_inline_for_extraction_not_flagged() {
        // inline_for_extraction bindings are inlined and may appear unused.
        let content = r#"module Test

private inline_for_extraction let inline_helper x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "inline_for_extraction bindings should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_assume_val_not_flagged() {
        // assume val declarations are axioms - removing them would break proofs.
        let content = r#"module Test

assume val secret_axiom : int -> int

private let other_unused x = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let assume_val_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("secret_axiom"))
            .collect();
        assert!(
            assume_val_diags.is_empty(),
            "assume val declarations should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_fsti_file_no_warnings() {
        // .fsti files define the public API. Private bindings in them
        // are still part of the interface and should not be flagged.
        let content = r#"module Test

private val internal_helper : int -> int
"#;
        let rule = DeadCodeRule::new();
        // Note: file extension is .fsti
        let diags = rule.check(&PathBuf::from("test.fsti"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Interface files (.fsti) should not have unused binding warnings"
        );
    }

    #[test]
    fn test_safety_friend_module_warning() {
        // When a file has friend declarations, the warning message should
        // mention that private bindings might be used by friend modules.
        let content = r#"module Test

friend OtherModule

private let internal_helper x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        // Should still warn (it's still unused in THIS file), but with friend warning
        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("internal_helper") && d.message.contains("never used"))
            .collect();
        assert_eq!(
            unused_diags.len(),
            1,
            "Should warn about unused binding even with friend declarations"
        );
        assert!(
            unused_diags[0].message.contains("friend"),
            "Warning should mention friend modules: {}",
            unused_diags[0].message
        );
    }

    #[test]
    fn test_safety_smtpator_not_flagged() {
        // SMTPatOr lemmas are auto-triggered by the solver.
        let content = r#"module Test

private let disjoint_lemma (a : nat) (b : nat)
  : Lemma (a + b >= a)
  [SMTPatOr [[SMTPat a]; [SMTPat b]]]
= ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "SMTPatOr lemmas should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_irreducible_not_flagged() {
        // [@irreducible] bindings don't unfold but are semantically used.
        let content = r#"module Test

[@irreducible]
private let hidden_impl x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "irreducible bindings should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_unused_param_fix_is_safe() {
        // The fix for unused parameters should be marked as safe (high confidence)
        // because adding underscore prefix is always a safe transformation.
        let content = r#"module Test

let func (unused_param : int) (x : int) : int = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("unused_param"))
            .collect();
        assert_eq!(param_diags.len(), 1, "Should detect unused parameter");

        let fix = param_diags[0].fix.as_ref().expect("Should have a fix");
        assert!(
            fix.can_auto_apply(),
            "Unused parameter fix should be safe for auto-apply"
        );
    }

    #[test]
    fn test_safety_noextract_param_not_flagged() {
        // Parameters in noextract functions should not be flagged
        // because the function exists only for proofs.
        let content = r#"module Test

noextract let proof_func (phantom : int) (x : int) : int = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("phantom") && d.message.contains("unused"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Parameters in noextract functions should not be flagged as unused"
        );
    }

    #[test]
    fn test_safety_abstract_type_not_flagged() {
        // abstract type definitions are part of module interface.
        let content = r#"module Test

private abstract type secret_t = int
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("secret_t") && d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "abstract type definitions should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: Type class instances and classes
    // =========================================================================

    #[test]
    fn test_fp_private_instance_not_flagged() {
        // Type class instances are used by the instance resolution mechanism.
        // They should NEVER be flagged as unused even if private.
        let content = r#"module Test

private instance printable_int : printable int = {
  print = string_of_int
}
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Type class instances should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_class_not_flagged() {
        // Type class declarations define the resolution interface.
        // They should NEVER be flagged as unused even if private.
        let content = r#"module Test

private class serializable (a:Type) = {
  serialize : a -> bytes;
  deserialize : bytes -> option a
}
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Type class declarations should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: unfold let (normalizer usage)
    // =========================================================================

    #[test]
    fn test_fp_private_unfold_let_not_flagged() {
        // `unfold let` bindings are used by the F* normalizer.
        // They should NEVER be flagged as unused.
        // This is a very common pattern in HACL* Spec modules:
        //   unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x
        let content = r#"module Test

private unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "unfold let bindings should not be flagged as unused (used by normalizer)"
        );
    }

    #[test]
    fn test_fp_unfold_let_type_alias_not_flagged() {
        // unfold let type aliases are common in HACL* specs:
        //   unfold let row (a:alg) = lseq (word_t a) 4
        let content = r#"module Test

private unfold let state_type (a:alg) = lseq (word_t a) 4
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "unfold let type aliases should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: inline_for_extraction let (block type)
    // =========================================================================

    #[test]
    fn test_fp_private_inline_let_block_type_not_flagged() {
        // inline_for_extraction let bindings are used at extraction.
        // The parser classifies these as InlineLet block type.
        let content = r#"module Test

private inline_for_extraction let buffer_size = 1024ul
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "inline_for_extraction let bindings should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: Ghost/GTot/erased return types
    // =========================================================================

    #[test]
    fn test_fp_private_gtot_function_not_flagged() {
        // Functions with GTot return type are specification-only.
        // They are erased at extraction and exist for verification.
        let content = r#"module Test

private let spec_length (s:seq int) : GTot nat = Seq.length s
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Functions with GTot return type should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_ghost_function_not_flagged() {
        // Functions with Ghost effect return type are spec-only.
        let content = r#"module Test

private let ghost_helper (x:nat) : Ghost nat (requires (x > 0)) (ensures (fun r -> r >= x)) = x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Functions with Ghost effect should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_erased_return_not_flagged() {
        // Functions returning erased types are spec-only.
        let content = r#"module Test

private let spec_val (x:nat) : erased nat = hide x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Functions returning erased types should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_ghost_erased_return_not_flagged() {
        // Functions returning Ghost.erased types are spec-only.
        let content = r#"module Test

private let ghost_spec (x:nat) : Ghost.erased nat = Ghost.hide x
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Functions returning Ghost.erased types should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_gtot_param_not_flagged() {
        // Parameters in GTot functions should not be flagged either.
        let content = r#"module Test

let spec_func (phantom : int) (x : nat) : GTot nat = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let param_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("Parameter") && d.message.contains("phantom"))
            .collect();
        assert!(
            param_diags.is_empty(),
            "Parameters in GTot functions should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: Private val for Lemma without corresponding let
    // =========================================================================

    #[test]
    fn test_fp_private_val_lemma_no_let_not_flagged() {
        // A private val with Lemma return type may not have a corresponding let.
        // It serves as an axiom-like specification or is implemented in friend modules.
        let content = r#"module Test

private val helper_lemma : x:nat -> y:nat -> Lemma (x + y >= x)
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("helper_lemma") && d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private val declarations for Lemma should not be flagged as unused"
        );
    }

    #[test]
    fn test_fp_private_val_gtot_no_let_not_flagged() {
        // A private val with GTot return type is a spec-only declaration.
        let content = r#"module Test

private val spec_helper : x:nat -> GTot nat
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("spec_helper") && d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private val declarations with GTot should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: Spec.* module bindings
    // =========================================================================

    #[test]
    fn test_fp_spec_module_private_binding_not_flagged() {
        // In HACL* and similar projects, Spec.* modules are pure specifications.
        // All their bindings are used for verification, not runtime.
        let content = r#"module Spec.Hash.SHA256

private let internal_constant = 42

let public_func x = x + internal_constant
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Spec.Hash.SHA256.fst"), content);

        // Even unreferenced private bindings in Spec modules should not be flagged
        // because they may be used by implementation modules during verification.
        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Private bindings in Spec.* modules should not be flagged: {:?}",
            unused_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fp_spec_module_unfold_let_not_flagged() {
        // Spec modules commonly use unfold let for type aliases.
        let content = r#"module Spec.Chacha20

unfold let size_key = 32
unfold let size_block = 64

private let internal_helper x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Spec.Chacha20.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Spec module bindings should not be flagged as unused"
        );
    }

    #[test]
    fn test_non_spec_module_still_flags_unused() {
        // Non-Spec modules should still flag genuinely unused private bindings.
        let content = r#"module Hacl.Impl.SHA256

private let dead_code x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Hacl.Impl.SHA256.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert_eq!(
            unused_diags.len(),
            1,
            "Non-Spec modules should still flag unused private bindings"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: substitute attribute
    // =========================================================================

    #[test]
    fn test_fp_substitute_attr_not_flagged() {
        // [@@"substitute"] attribute tells the normalizer to substitute.
        let content = r#"module Test

[@@"substitute"]
private let helper_def x = x + 1
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Bindings with [@@\"substitute\"] should not be flagged as unused"
        );
    }

    // =========================================================================
    // NEW FALSE POSITIVE TESTS: Effect system blocks
    // =========================================================================

    #[test]
    fn test_fp_private_effect_not_flagged() {
        // Effect declarations are part of the effect system infrastructure.
        let content = r#"module Test

private effect MyEffect (a:Type) = Pure a (requires True) (ensures (fun _ -> True))
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("test.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Effect declarations should not be flagged as unused"
        );
    }

    // =========================================================================
    // REGRESSION: Ensure we still detect genuinely unused private bindings
    // =========================================================================

    #[test]
    fn test_genuine_unused_still_flagged() {
        // A genuinely unused private let binding (no special attributes, no
        // Spec module, no ghost/erased, no unfold, no instance) should still
        // be flagged.
        let content = r#"module Impl.Something

private let dead_helper x = x + 1

let public_func y = y * 2
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Impl.Something.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("dead_helper") && d.message.contains("never used"))
            .collect();
        assert_eq!(
            unused_diags.len(),
            1,
            "Genuinely unused private bindings should still be flagged"
        );
    }

    #[test]
    fn test_genuine_unused_val_still_flagged() {
        // A genuinely unused private val without Lemma/GTot/Ghost return type
        // and without a corresponding let should still be flagged.
        let content = r#"module Impl.Something

private val orphan_declaration : int -> int

let public_func y = y * 2
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Impl.Something.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("orphan_declaration") && d.message.contains("never used"))
            .collect();
        assert_eq!(
            unused_diags.len(),
            1,
            "Genuinely unused private val declarations should still be flagged"
        );
    }

    // =========================================================================
    // COMBINED: Real-world HACL* patterns
    // =========================================================================

    #[test]
    fn test_hacl_spec_agile_hash_pattern() {
        // Real pattern from HACL* Spec.Agile.Hash:
        // `unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x`
        // This is a verification-only module with unfold let.
        let content = r#"module Spec.Agile.Hash

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

let init a =
  match a with
  | SHA2_256 -> Spec.SHA2.init a
  | SHA1 -> Spec.SHA1.init
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Spec.Agile.Hash.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "HACL* Spec.Agile.Hash pattern should produce no unused warnings: {:?}",
            unused_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_hacl_bignum_instance_pattern() {
        // Real pattern from HACL* code/bignum:
        // `instance bn_inst: BN.bn t_limbs = { ... }`
        // Type class instances are resolved by instance resolution.
        let content = r#"module Hacl.Bignum4096

private instance bn_inst: BN.bn t_limbs = {
  BN.len = n;
  BN.add = add;
  BN.sub = sub
}

let main () = ()
"#;
        let rule = DeadCodeRule::new();
        let diags = rule.check(&PathBuf::from("Hacl.Bignum4096.fst"), content);

        let unused_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.message.contains("bn_inst") && d.message.contains("never used"))
            .collect();
        assert!(
            unused_diags.is_empty(),
            "Type class instances should not be flagged: {:?}",
            unused_diags.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }
}
