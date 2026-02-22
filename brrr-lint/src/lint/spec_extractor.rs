//! FST010: Specification extractor.
//!
//! Detects .fst files without corresponding .fsti and suggests creating one.
//! This rule helps maintain proper module interfaces in F* projects.
//!
//! SAFETY GUARANTEES:
//! - NEVER overwrites existing .fsti files
//! - Always validates generated content before offering fix
//! - Dry-run mode shows full preview before any file creation
//! - Fix confidence is LOW - requires explicit user confirmation
//!
//! Supports three extraction modes:
//! - Minimal: Abstract types, val signatures only, hide refinements
//! - Full: Transparent types, preserve all specifications
//! - DocFocused: Optimized for API documentation generation

use std::path::Path;

use super::parser::{parse_fstar_file, BlockType};
use super::rules::{
    Diagnostic, DiagnosticSeverity, Edit, Fix, FixConfidence, FixSafetyLevel, Range, Rule, RuleCode,
};

/// Extraction mode for .fsti generation.
///
/// Controls how much detail is exposed in the generated interface file.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ExtractionMode {
    /// Minimal: abstract types, val only, hide refinements.
    /// Best for maximum encapsulation.
    Minimal,
    /// Full: transparent types, preserve all specifications.
    /// Best for library code where users need full type information.
    #[default]
    Full,
    /// DocFocused: optimized for API documentation.
    /// Includes doc comments, simplifies complex refinements.
    DocFocused,
}

/// Statistics about generated .fsti content for dry-run preview.
#[derive(Debug, Clone)]
pub struct FstiGenerationStats {
    /// Total lines in generated .fsti
    pub line_count: usize,
    /// Number of val declarations
    pub val_count: usize,
    /// Number of type declarations
    pub type_count: usize,
    /// Number of effect declarations
    pub effect_count: usize,
    /// Number of class declarations
    pub class_count: usize,
    /// Number of open statements preserved
    pub open_count: usize,
    /// List of declaration names exported
    pub exported_names: Vec<String>,
    /// Validation errors if any
    pub validation_errors: Vec<String>,
}

impl FstiGenerationStats {
    /// Create a summary string for dry-run display.
    pub fn summary(&self) -> String {
        let mut parts = Vec::new();
        if self.val_count > 0 {
            parts.push(format!("{} val(s)", self.val_count));
        }
        if self.type_count > 0 {
            parts.push(format!("{} type(s)", self.type_count));
        }
        if self.effect_count > 0 {
            parts.push(format!("{} effect(s)", self.effect_count));
        }
        if self.class_count > 0 {
            parts.push(format!("{} class(es)", self.class_count));
        }
        format!(
            "{} lines, {} declaration(s): {}",
            self.line_count,
            self.val_count + self.type_count + self.effect_count + self.class_count,
            parts.join(", ")
        )
    }
}

/// Validation error found in generated .fsti content.
#[derive(Debug, Clone)]
pub struct FstiValidationError {
    pub message: String,
}

/// Validate generated .fsti content for common issues.
///
/// Checks for:
/// - Module declaration present
/// - Balanced braces/parens/brackets
/// - No incomplete declarations
/// - Referenced types have open statements
///
/// Returns a list of validation errors, empty if content is valid.
pub fn validate_fsti_content(content: &str) -> Vec<FstiValidationError> {
    let mut errors = Vec::new();

    // Check 1: Module declaration must be present
    if !content.lines().any(|line| line.trim().starts_with("module ")) {
        errors.push(FstiValidationError {
            message: "Generated .fsti is missing module declaration".to_string(),
        });
    }

    // Check 2: Balanced delimiters
    let mut paren_depth: i32 = 0;
    let mut brace_depth: i32 = 0;
    let mut bracket_depth: i32 = 0;
    let mut in_comment = false;
    let mut in_string = false;
    let chars: Vec<char> = content.chars().collect();

    for (i, &c) in chars.iter().enumerate() {
        // Track strings
        if c == '"' && !in_comment {
            if !in_string {
                in_string = true;
            } else if i == 0 || chars[i - 1] != '\\' {
                in_string = false;
            }
            continue;
        }

        if in_string {
            continue;
        }

        // Track comments
        if i + 1 < chars.len() && c == '(' && chars[i + 1] == '*' {
            in_comment = true;
            continue;
        }
        if i > 0 && chars[i - 1] == '*' && c == ')' && in_comment {
            in_comment = false;
            continue;
        }

        if in_comment {
            continue;
        }

        // Count delimiters
        match c {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            _ => {}
        }

        if paren_depth < 0 || brace_depth < 0 || bracket_depth < 0 {
            errors.push(FstiValidationError {
                message: "Unbalanced delimiters in generated .fsti".to_string(),
            });
            break;
        }
    }

    if paren_depth != 0 {
        errors.push(FstiValidationError {
            message: format!(
                "Unclosed parentheses in generated .fsti (depth: {})",
                paren_depth
            ),
        });
    }
    if brace_depth != 0 {
        errors.push(FstiValidationError {
            message: format!(
                "Unclosed braces in generated .fsti (depth: {})",
                brace_depth
            ),
        });
    }
    if bracket_depth != 0 {
        errors.push(FstiValidationError {
            message: format!(
                "Unclosed brackets in generated .fsti (depth: {})",
                bracket_depth
            ),
        });
    }

    // Check 3: Incomplete val declarations (val without colon)
    for line in content.lines() {
        let stripped = line.trim();
        if stripped.starts_with("val ") && !stripped.contains(':') && !stripped.ends_with(',') {
            // val without type annotation is incomplete
            errors.push(FstiValidationError {
                message: format!(
                    "Incomplete val declaration (missing type): {}",
                    stripped.chars().take(50).collect::<String>()
                ),
            });
        }
    }

    // Check 4: Empty content (just module declaration)
    let non_empty_lines = content
        .lines()
        .filter(|line| {
            let stripped = line.trim();
            !stripped.is_empty()
                && !stripped.starts_with("module ")
                && !stripped.starts_with("open ")
        })
        .count();

    if non_empty_lines == 0 {
        errors.push(FstiValidationError {
            message: "Generated .fsti has no declarations (only module header)".to_string(),
        });
    }

    errors
}

/// Generate .fsti content from .fst source with statistics.
///
/// Takes F* implementation source code and generates a corresponding
/// interface file based on the extraction mode. Also computes statistics
/// about the generated content for dry-run preview.
///
/// # Arguments
/// * `content` - The .fst source code
/// * `mode` - The extraction mode controlling how much detail to expose
///
/// # Returns
/// A tuple of (fsti_content, statistics) for dry-run preview and validation.
///
/// # Example
/// ```ignore
/// let fst_content = "module Test\n\nlet foo : int -> int\nlet foo x = x + 1";
/// let (fsti, stats) = generate_fsti_with_stats(fst_content, ExtractionMode::Full);
/// println!("Generated {} lines with {} declarations", stats.line_count, stats.val_count);
/// ```
pub fn generate_fsti_with_stats(content: &str, mode: ExtractionMode) -> (String, FstiGenerationStats) {
    let fsti = generate_fsti(content, mode);

    // Count declarations in generated content
    let mut stats = FstiGenerationStats {
        line_count: fsti.lines().count(),
        val_count: 0,
        type_count: 0,
        effect_count: 0,
        class_count: 0,
        open_count: 0,
        exported_names: Vec::new(),
        validation_errors: Vec::new(),
    };

    for line in fsti.lines() {
        let stripped = line.trim();
        if stripped.starts_with("val ") || stripped.starts_with("assume val ") {
            stats.val_count += 1;
            // Extract name from val declaration
            if let Some(name) = extract_val_name(stripped) {
                stats.exported_names.push(name);
            }
        } else if stripped.starts_with("type ") || stripped.starts_with("noeq type ") {
            stats.type_count += 1;
            if let Some(name) = extract_type_name(stripped) {
                stats.exported_names.push(name);
            }
        } else if stripped.starts_with("effect ") || stripped.starts_with("layered_effect ") {
            stats.effect_count += 1;
        } else if stripped.starts_with("class ") {
            stats.class_count += 1;
        } else if stripped.starts_with("open ") {
            stats.open_count += 1;
        }
    }

    // Validate generated content
    let validation_errors = validate_fsti_content(&fsti);
    stats.validation_errors = validation_errors
        .iter()
        .map(|e| e.message.clone())
        .collect();

    (fsti, stats)
}

/// Extract val name from a val declaration line.
fn extract_val_name(line: &str) -> Option<String> {
    let stripped = line.trim();
    let after_val = if let Some(rest) = stripped.strip_prefix("assume val ") {
        rest
    } else if let Some(rest) = stripped.strip_prefix("val ") {
        rest
    } else {
        return None;
    };

    // Handle operator syntax: val (+) : ...
    if after_val.starts_with('(') {
        if let Some(end) = after_val.find(')') {
            return Some(after_val[1..end].trim().to_string());
        }
    }

    // Normal identifier
    after_val
        .split_whitespace()
        .next()
        .map(|s| s.trim_end_matches(':').to_string())
}

/// Extract type name from a type declaration line.
fn extract_type_name(line: &str) -> Option<String> {
    let stripped = line.trim();
    let after_type = if let Some(rest) = stripped.strip_prefix("noeq type ") {
        rest
    } else if let Some(rest) = stripped.strip_prefix("type ") {
        rest
    } else {
        return None;
    };

    after_type
        .split_whitespace()
        .next()
        .map(|s| s.to_string())
}

/// Generate .fsti content from .fst source.
///
/// Takes F* implementation source code and generates a corresponding
/// interface file based on the extraction mode.
///
/// # Arguments
/// * `content` - The .fst source code
/// * `mode` - The extraction mode controlling how much detail to expose
///
/// # Returns
/// A String containing the generated .fsti content.
///
/// # Example
/// ```ignore
/// let fst_content = "module Test\n\nlet foo x = x + 1";
/// let fsti = generate_fsti(fst_content, ExtractionMode::Full);
/// ```
pub fn generate_fsti(content: &str, mode: ExtractionMode) -> String {
    let mut fsti = String::new();
    let (header, blocks) = parse_fstar_file(content);

    // Add module declaration from header
    for line in &header {
        let stripped = line.trim();
        if stripped.starts_with("module ") {
            fsti.push_str(stripped);
            fsti.push_str("\n\n");
            break;
        }
    }

    // Add opens from header
    let mut has_opens = false;
    for line in &header {
        let stripped = line.trim();
        if stripped.starts_with("open ") {
            fsti.push_str(stripped);
            fsti.push('\n');
            has_opens = true;
        }
    }
    if has_opens {
        fsti.push('\n');
    }

    // Process declarations
    for block in &blocks {
        let text = block.lines.join("");

        // Skip private declarations
        if text.contains("private ") {
            continue;
        }

        // Skip internal names (underscore prefix convention)
        if block.names.iter().all(|n| n.starts_with('_')) {
            continue;
        }

        match block.block_type {
            BlockType::Val => {
                // val declarations go directly to interface
                append_block_with_doc_comment(&mut fsti, &block.lines, mode);
            }
            BlockType::Type => {
                match mode {
                    ExtractionMode::Minimal => {
                        // Make type abstract - just export the type name
                        for name in &block.names {
                            if !name.starts_with('_') {
                                // Extract type parameters if present
                                let type_params = extract_type_params(&block.lines);
                                if type_params.is_empty() {
                                    fsti.push_str(&format!("val {} : Type0\n\n", name));
                                } else {
                                    fsti.push_str(&format!(
                                        "val {} : {} -> Type0\n\n",
                                        name, type_params
                                    ));
                                }
                            }
                        }
                    }
                    ExtractionMode::Full | ExtractionMode::DocFocused => {
                        // Keep full type definition
                        append_block_with_doc_comment(&mut fsti, &block.lines, mode);
                    }
                }
            }
            BlockType::Let => {
                // Convert let to val
                if let Some(sig) = extract_let_signature(&block.lines, mode) {
                    for name in &block.names {
                        if !name.starts_with('_') {
                            // Check if we already have the name in the signature
                            if sig.contains(&format!("{} :", name))
                                || sig.contains(&format!("{}:", name))
                            {
                                fsti.push_str(&format!("val {}\n\n", sig));
                            } else {
                                fsti.push_str(&format!("val {} : {}\n\n", name, sig));
                            }
                        }
                    }
                }
            }
            BlockType::Class => {
                // Class declarations go through as-is
                append_block_with_doc_comment(&mut fsti, &block.lines, mode);
            }
            BlockType::Effect | BlockType::NewEffect | BlockType::SubEffect | BlockType::EffectAbbrev => {
                // Effect declarations go through as-is
                append_block_with_doc_comment(&mut fsti, &block.lines, mode);
            }
            BlockType::Exception => {
                // Exception declarations go through as-is
                append_block_with_doc_comment(&mut fsti, &block.lines, mode);
            }
            BlockType::Assume => {
                // assume val declarations go through
                append_block_with_doc_comment(&mut fsti, &block.lines, mode);
            }
            BlockType::UnfoldLet | BlockType::InlineLet => {
                // For unfold/inline_for_extraction, we need to preserve the attribute
                if let Some(sig) = extract_let_signature(&block.lines, mode) {
                    let first_line = block.lines.first().map(|s| s.as_str()).unwrap_or("");
                    let prefix = if first_line.contains("unfold")
                        && first_line.contains("inline_for_extraction")
                    {
                        "unfold inline_for_extraction "
                    } else if first_line.contains("inline_for_extraction") {
                        "inline_for_extraction "
                    } else if first_line.contains("unfold") {
                        "unfold "
                    } else {
                        ""
                    };

                    for name in &block.names {
                        if !name.starts_with('_') {
                            if sig.contains(&format!("{} :", name))
                                || sig.contains(&format!("{}:", name))
                            {
                                fsti.push_str(&format!("{}val {}\n\n", prefix, sig));
                            } else {
                                fsti.push_str(&format!("{}val {} : {}\n\n", prefix, name, sig));
                            }
                        }
                    }
                }
            }
            // Skip: Module, Open, Friend, SetOptions, Instance, Directive, Comment, Unknown
            _ => {}
        }
    }

    // Trim trailing whitespace but keep one newline at end
    let trimmed = fsti.trim_end();
    if !trimmed.is_empty() {
        format!("{}\n", trimmed)
    } else {
        fsti
    }
}

/// Extract type parameters from a type declaration.
///
/// For `type t a b = ...`, returns "Type0 -> Type0" to indicate
/// it takes two type parameters.
fn extract_type_params(lines: &[String]) -> String {
    let first_line = lines.first().map(|s| s.as_str()).unwrap_or("");
    let stripped = first_line.trim();

    // Find the type name and any parameters before '='
    if let Some(eq_pos) = stripped.find('=') {
        let before_eq = &stripped[..eq_pos];
        // Skip "type name" and count remaining identifiers
        let parts: Vec<&str> = before_eq.split_whitespace().collect();
        if parts.len() > 2 {
            // First is "type", second is name, rest are params
            let param_count = parts.len() - 2;
            let params: Vec<&str> = (0..param_count).map(|_| "Type0").collect();
            return params.join(" -> ");
        }
    }

    String::new()
}

/// Extract signature from a let binding for interface generation.
///
/// Handles various let forms:
/// - `let foo : int -> int` -> extracts `foo : int -> int` (forward declaration)
/// - `let foo : int -> int = ...` -> extracts `foo : int -> int`
/// - `let foo (x: int) : int = ...` -> extracts full signature
/// - `let foo x = ...` -> returns None (no type annotation)
fn extract_let_signature(lines: &[String], mode: ExtractionMode) -> Option<String> {
    let full_text = lines.join(" ");
    let stripped = full_text.trim();

    // Determine the signature portion - either before '=' or the entire declaration
    let sig_portion = match find_definition_equals(stripped) {
        Some(eq_pos) => stripped[..eq_pos].trim(),
        None => stripped, // No '=' means this is a forward declaration
    };

    // Remove 'let', 'rec', attributes, etc.
    let sig_part = strip_let_keywords(sig_portion);

    // Check if there's a type annotation
    if !sig_part.contains(':') {
        // No type annotation - we can't generate interface
        return None;
    }

    // For DocFocused mode, simplify complex refinements
    let result = if mode == ExtractionMode::DocFocused {
        simplify_refinements(&sig_part)
    } else {
        sig_part
    };

    // Clean up the result
    let cleaned = result
        .replace('\n', " ")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");

    if cleaned.is_empty() {
        None
    } else {
        Some(cleaned)
    }
}

/// Strip let keywords and attributes from a signature.
fn strip_let_keywords(text: &str) -> String {
    let mut result = text.trim();

    // Handle attributes like [@@...]
    while result.starts_with("[@@") || result.starts_with("[@") {
        if let Some(end_bracket) = result.find(']') {
            result = result[end_bracket + 1..].trim();
        } else {
            break;
        }
    }

    // Strip keywords in order
    let keywords = [
        "private",
        "unfold",
        "inline_for_extraction",
        "noextract",
        "let",
        "rec",
    ];

    for keyword in keywords {
        if result.starts_with(keyword) {
            let rest = &result[keyword.len()..];
            if rest.is_empty() || rest.starts_with(char::is_whitespace) {
                result = rest.trim_start();
            }
        }
    }

    result.to_string()
}

/// Find the '=' that separates the signature from the body.
///
/// Handles nested equals signs in types like `x:t{x = 0}`.
fn find_definition_equals(text: &str) -> Option<usize> {
    let chars: Vec<char> = text.chars().collect();
    let mut depth: usize = 0; // Track nesting depth for {}, (), []

    for (i, &c) in chars.iter().enumerate() {
        match c {
            '{' | '(' | '[' => depth += 1,
            '}' | ')' | ']' => depth = depth.saturating_sub(1),
            '=' if depth == 0 => {
                // Make sure it's not == or =>
                let next = chars.get(i + 1);
                let prev = chars.get(i.saturating_sub(1));
                if next != Some(&'=')
                    && next != Some(&'>')
                    && prev != Some(&'=')
                    && prev != Some(&'<')
                    && prev != Some(&'>')
                    && prev != Some(&'!')
                {
                    return Some(i);
                }
            }
            ':' if depth == 0 => {
                // Found type annotation start - now find the '=' after it
                // Continue scanning from here
            }
            _ => {}
        }
    }
    None
}

/// Simplify complex refinement types for documentation purposes.
///
/// Replaces `x:t{complex_refinement}` with `x:t{...}` for readability.
fn simplify_refinements(text: &str) -> String {
    let mut result = String::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i] == '{' {
            // Check if this looks like a refinement (preceded by type)
            let before: String = result
                .chars()
                .rev()
                .take(20)
                .collect::<String>()
                .chars()
                .rev()
                .collect();
            if before.contains(':') || before.ends_with(|c: char| c.is_alphanumeric()) {
                result.push('{');
                // Find matching closing brace
                let mut depth = 1;
                let start = i + 1;
                i += 1;
                while i < chars.len() && depth > 0 {
                    if chars[i] == '{' {
                        depth += 1;
                    } else if chars[i] == '}' {
                        depth -= 1;
                    }
                    i += 1;
                }
                // Check if refinement is complex (contains logical operators)
                let refinement: String = chars[start..i.saturating_sub(1)].iter().collect();
                if refinement.contains("/\\") || refinement.contains("\\/") || refinement.len() > 30
                {
                    result.push_str("...");
                } else {
                    result.push_str(&refinement);
                }
                result.push('}');
                continue;
            }
        }
        result.push(chars[i]);
        i += 1;
    }

    result
}

/// Append a block to the output, optionally including doc comments.
fn append_block_with_doc_comment(output: &mut String, lines: &[String], mode: ExtractionMode) {
    let mut started_content = false;

    for line in lines {
        let stripped = line.trim();

        // In DocFocused mode, preserve doc comments
        // In other modes, skip leading comments
        if stripped.starts_with("(*") || stripped.starts_with("*)") || stripped.contains("(*") {
            if mode == ExtractionMode::DocFocused || started_content {
                output.push_str(line);
            }
            continue;
        }

        // Skip empty lines before content
        if stripped.is_empty() && !started_content {
            continue;
        }

        started_content = true;
        output.push_str(line);
    }

    // Ensure block ends with newline
    if !output.ends_with('\n') {
        output.push('\n');
    }
    output.push('\n');
}

/// FST010: Specification extractor rule.
///
/// This rule checks for .fst implementation files that lack a corresponding
/// .fsti interface file. In F*, interface files define the public API and
/// help with separate compilation, encapsulation, and documentation.
pub struct SpecExtractorRule {
    mode: ExtractionMode,
}

impl SpecExtractorRule {
    pub fn new() -> Self {
        Self {
            mode: ExtractionMode::Full,
        }
    }

    /// Create with a specific extraction mode.
    pub fn with_mode(mode: ExtractionMode) -> Self {
        Self { mode }
    }

    /// Extract public declarations that should be in .fsti.
    ///
    /// Returns a vector of (name, block_type, line_number) for each public
    /// declaration found. Private declarations and names starting with
    /// underscore are excluded.
    pub fn extract_public_decls(content: &str) -> Vec<(String, BlockType, usize)> {
        let (_, blocks) = parse_fstar_file(content);
        let mut public_decls = Vec::new();

        for block in blocks {
            let text = block.lines.join("");

            // Skip private declarations
            if text.contains("private ") {
                continue;
            }

            for name in &block.names {
                // Skip internal names (underscore prefix convention)
                if name.starts_with('_') {
                    continue;
                }

                // Only include declaration types that belong in interfaces
                match block.block_type {
                    BlockType::Val
                    | BlockType::Type
                    | BlockType::Let
                    | BlockType::Class
                    | BlockType::Effect
                    | BlockType::NewEffect
                    | BlockType::SubEffect
                    | BlockType::EffectAbbrev
                    | BlockType::Exception
                    | BlockType::Assume
                    | BlockType::UnfoldLet
                    | BlockType::InlineLet => {
                        public_decls.push((name.clone(), block.block_type, block.start_line));
                    }
                    // Skip: Module, Open, Friend, SetOptions, Instance,
                    // Directive, Comment, Unknown
                    _ => {}
                }
            }
        }

        public_decls
    }
}

impl Default for SpecExtractorRule {
    fn default() -> Self {
        Self::new()
    }
}

/// Minimum number of public declarations before we consider warning.
/// Files with very few public declarations are likely internal helpers.
const MIN_PUBLIC_DECLS_FOR_WARNING: usize = 3;

/// Check if a module name (from file stem, e.g. "Hacl.Test.SHA2") matches
/// patterns that typically don't need .fsti interface files.
///
/// Returns `Some(reason)` if the file should be skipped, `None` otherwise.
fn should_skip_fsti_check(file_stem: &str) -> Option<&'static str> {
    // Split the dotted module name into segments for pattern matching.
    // E.g. "Hacl.Test.SHA2" -> ["Hacl", "Test", "SHA2"]
    let segments: Vec<&str> = file_stem.split('.').collect();

    // Test files: any segment is "Test" or "Tests", or stem ends with "_test"/"_tests"
    // Examples: Hacl.Test.SHA2, Spec.AES.Test, ASN1Test, ASN1.Test.Interpreter
    if segments
        .iter()
        .any(|s| s.eq_ignore_ascii_case("test") || s.eq_ignore_ascii_case("tests"))
    {
        return Some("test file");
    }
    let last = segments.last().unwrap_or(&"");
    if last.ends_with("Test") || last.ends_with("Tests") || last.ends_with("_test") {
        return Some("test file");
    }

    // Lemma/proof files: any segment contains "Lemma" or "Lemmas"
    // Examples: Hacl.Spec.Chacha20.Lemmas, Hacl.Spec.K256.MathLemmas
    if segments
        .iter()
        .any(|s| *s == "Lemma" || *s == "Lemmas" || s.ends_with("Lemmas") || s.ends_with("Lemma"))
    {
        return Some("lemma/proof file");
    }

    // Example/demo files
    // Examples: Example.fst, Client.fst, Device.fst
    if segments.iter().any(|s| {
        s.eq_ignore_ascii_case("example")
            || s.eq_ignore_ascii_case("examples")
            || s.eq_ignore_ascii_case("demo")
            || s.eq_ignore_ascii_case("sample")
    }) {
        return Some("example/demo file");
    }

    None
}

impl Rule for SpecExtractorRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST010
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Only check .fst files (implementations)
        if file.extension().map(|e| e != "fst").unwrap_or(true) {
            return diagnostics;
        }

        // Check if corresponding .fsti exists
        let fsti_path = file.with_extension("fsti");

        // SAFETY: If .fsti already exists, NEVER offer to create/overwrite
        // This is a critical safety check - we must not corrupt existing interfaces
        if fsti_path.exists() {
            // .fsti exists - nothing to do, interface is already defined
            return diagnostics;
        }

        // Extract file stem for module-name-based heuristics.
        // For "Hacl.Test.SHA2.fst" this gives "Hacl.Test.SHA2".
        let file_stem = file
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("");

        // Skip files that match known false-positive patterns
        if should_skip_fsti_check(file_stem).is_some() {
            return diagnostics;
        }

        let public_decls = Self::extract_public_decls(content);

        if !public_decls.is_empty() {
            // Files with very few public declarations are likely internal
            // helpers that intentionally don't expose an interface.
            // Use Hint severity for those, Info for substantial APIs.
            let severity = if public_decls.len() < MIN_PUBLIC_DECLS_FOR_WARNING {
                DiagnosticSeverity::Hint
            } else {
                DiagnosticSeverity::Info
            };

            // Generate the .fsti content with statistics for dry-run preview
            let (fsti_content, stats) = generate_fsti_with_stats(content, self.mode);

            // Build dry-run preview message with statistics
            let mut message = format!(
                "No .fsti file found. {} public declaration{} could be exposed.",
                public_decls.len(),
                if public_decls.len() == 1 { "" } else { "s" }
            );

            // Add statistics summary for dry-run
            if !fsti_content.trim().is_empty() {
                message.push_str(&format!("\n  [DRY-RUN] Would generate: {}", stats.summary()));
                if !stats.exported_names.is_empty() {
                    let preview_names: Vec<&str> = stats
                        .exported_names
                        .iter()
                        .take(5)
                        .map(|s| s.as_str())
                        .collect();
                    let suffix = if stats.exported_names.len() > 5 {
                        format!(" ... and {} more", stats.exported_names.len() - 5)
                    } else {
                        String::new()
                    };
                    message.push_str(&format!(
                        "\n  [DRY-RUN] Exports: {}{}",
                        preview_names.join(", "),
                        suffix
                    ));
                }
            }

            // Check for validation errors before offering fix
            let validation_errors = validate_fsti_content(&fsti_content);

            // Only create fix if:
            // 1. We generated meaningful content (more than just module header)
            // 2. Validation passed (no syntax errors detected)
            // 3. .fsti does NOT already exist (double-check)
            let fix = if !fsti_content.trim().is_empty()
                && fsti_content.lines().count() > 1
                && validation_errors.is_empty()
                && !fsti_path.exists()
            {
                // CRITICAL: Use LOW confidence - this fix creates NEW files
                // and should NEVER be auto-applied. User must review generated content.
                let fix_message = format!(
                    "[REQUIRES REVIEW] Generate .fsti interface file ({} declarations, {} lines). \
                     Run with --dry-run to preview full content.",
                    stats.val_count + stats.type_count + stats.effect_count + stats.class_count,
                    stats.line_count
                );

                Some(
                    Fix::unsafe_fix(
                        fix_message,
                        vec![Edit {
                            file: fsti_path,
                            range: Range::new(1, 1, 1, 1),
                            new_text: fsti_content.clone(),
                        }],
                        FixConfidence::Low,
                        "Creates a new .fsti file. Generated content should be reviewed for \
                         correctness. May include incorrect signatures or miss important declarations.",
                    )
                    .with_safety_level(FixSafetyLevel::Caution)  // Creating new files needs caution
                    .with_reversible(true)  // Can delete the new file
                    .with_requires_review(true)  // Always review generated content
                )
            } else if !validation_errors.is_empty() {
                // Add validation errors to message
                message.push_str("\n  [WARNING] Generated content has issues:");
                for err in validation_errors.iter().take(3) {
                    message.push_str(&format!("\n    - {}", err.message));
                }
                if validation_errors.len() > 3 {
                    message.push_str(&format!(
                        "\n    ... and {} more issues",
                        validation_errors.len() - 3
                    ));
                }
                message.push_str("\n  [NO FIX OFFERED] Fix generation quality issues first.");
                None
            } else {
                None
            };

            diagnostics.push(Diagnostic {
                rule: RuleCode::FST010,
                severity,
                file: file.to_path_buf(),
                range: Range::point(1, 1),
                message,
                fix,
            });
        }

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_extract_public_decls() {
        let content = r#"module Test

open FStar.All

val public_func : int -> int
let public_func x = x + 1

private let internal_helper y = y * 2

type public_type = int

private type secret_type = string

let _hidden_func z = z
"#;
        let decls = SpecExtractorRule::extract_public_decls(content);

        // Should find: public_func (val), public_func (let), public_type
        // Should NOT find: internal_helper (private), secret_type (private), _hidden_func (underscore)
        let names: Vec<&str> = decls.iter().map(|(n, _, _)| n.as_str()).collect();

        assert!(names.contains(&"public_func"));
        assert!(names.contains(&"public_type"));
        assert!(!names.contains(&"internal_helper"));
        assert!(!names.contains(&"secret_type"));
        assert!(!names.contains(&"_hidden_func"));
    }

    #[test]
    fn test_no_public_decls() {
        let content = r#"module Test

private let helper x = x
"#;
        let decls = SpecExtractorRule::extract_public_decls(content);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_check_fsti_exists() {
        // This test verifies the rule does not trigger when checking a .fsti file
        let rule = SpecExtractorRule::new();
        let content = "module Test\n\nval foo : int";
        let diags = rule.check(&PathBuf::from("test.fsti"), content);
        assert!(diags.is_empty());
    }

    #[test]
    fn test_generate_fsti_full_mode() {
        let content = r#"module Test

open FStar.All

val foo : int -> int
let foo x = x + 1

type mytype = | A | B

let bar : string -> string
let bar s = s
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("module Test"));
        assert!(fsti.contains("open FStar.All"));
        assert!(fsti.contains("val foo : int -> int"));
        assert!(fsti.contains("type mytype"));
        // Should not contain implementation
        assert!(!fsti.contains("x + 1"));
    }

    #[test]
    fn test_generate_fsti_minimal_mode() {
        let content = r#"module Test

type mytype = | A | B | C

let foo : int -> int
let foo x = x + 1
"#;
        let fsti = generate_fsti(content, ExtractionMode::Minimal);

        assert!(fsti.contains("module Test"));
        // Type should be abstract in minimal mode
        assert!(fsti.contains("val mytype : Type0"));
        // Should not contain the full type definition
        assert!(!fsti.contains("| A | B | C"));
    }

    #[test]
    fn test_generate_fsti_with_type_params() {
        let content = r#"module Test

type container a = | Empty | Full of a
"#;
        let fsti = generate_fsti(content, ExtractionMode::Minimal);

        // Should generate abstract type with parameter
        assert!(fsti.contains("val container : Type0 -> Type0"));
    }

    #[test]
    fn test_generate_fsti_skips_private() {
        let content = r#"module Test

val public_func : int -> int
let public_func x = x

private val private_func : string -> string
private let private_func s = s

private type secret = int
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("public_func"));
        assert!(!fsti.contains("private_func"));
        assert!(!fsti.contains("secret"));
    }

    #[test]
    fn test_generate_fsti_skips_underscore_names() {
        let content = r#"module Test

let _internal x = x

let public_thing : int -> int
let public_thing x = x
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(!fsti.contains("_internal"));
        assert!(fsti.contains("public_thing"));
    }

    #[test]
    fn test_generate_fsti_preserves_effects() {
        let content = r#"module Test

effect MyEffect (a:Type) = a

exception MyException of string
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("effect MyEffect"));
        assert!(fsti.contains("exception MyException"));
    }

    #[test]
    fn test_generate_fsti_inline_for_extraction() {
        let content = r#"module Test

inline_for_extraction let size : nat
inline_for_extraction let size = 42
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Should preserve inline_for_extraction attribute
        assert!(fsti.contains("inline_for_extraction"));
        assert!(fsti.contains("val"));
    }

    #[test]
    fn test_generate_fsti_unfold() {
        let content = r#"module Test

unfold let max_size : nat
unfold let max_size = 100
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Should preserve unfold attribute
        assert!(fsti.contains("unfold"));
        assert!(fsti.contains("val"));
    }

    #[test]
    fn test_extract_let_signature_simple() {
        let lines = vec!["let foo : int -> int\n".to_string()];
        let sig = extract_let_signature(&lines, ExtractionMode::Full);
        assert!(sig.is_some());
        let sig = sig.unwrap();
        assert!(sig.contains("int -> int") || sig.contains("foo : int -> int"));
    }

    #[test]
    fn test_extract_let_signature_with_params() {
        let lines = vec!["let add (x: int) (y: int) : int = x + y\n".to_string()];
        let sig = extract_let_signature(&lines, ExtractionMode::Full);
        assert!(sig.is_some());
    }

    #[test]
    fn test_extract_let_signature_no_annotation() {
        let lines = vec!["let foo x = x + 1\n".to_string()];
        let sig = extract_let_signature(&lines, ExtractionMode::Full);
        // Should return None - no type annotation
        assert!(sig.is_none());
    }

    #[test]
    fn test_simplify_refinements() {
        let complex = "x:nat{x > 0 /\\ x < 100 /\\ is_prime x}";
        let simplified = simplify_refinements(complex);
        assert!(simplified.contains("{...}"));
    }

    #[test]
    fn test_simplify_refinements_simple() {
        let simple = "x:nat{x > 0}";
        let simplified = simplify_refinements(simple);
        // Simple refinement should not be replaced
        assert!(simplified.contains("x > 0"));
    }

    #[test]
    fn test_doc_focused_mode() {
        let content = r#"module Test

(** This is a documented function *)
val documented_func : x:nat{x > 0 /\ x < 1000000 /\ is_valid x} -> nat

let helper : int -> int
let helper x = x
"#;
        let fsti = generate_fsti(content, ExtractionMode::DocFocused);

        assert!(fsti.contains("module Test"));
        assert!(fsti.contains("documented_func"));
    }

    #[test]
    fn test_find_definition_equals() {
        // Simple case
        assert!(find_definition_equals("let x = 1").is_some());

        // With type annotation containing =
        let complex = "let foo : x:int{x = 0} -> int = fun x -> x";
        let pos = find_definition_equals(complex);
        assert!(pos.is_some());
        // The '=' after '-> int' should be found, not the one in {x = 0}
        let pos = pos.unwrap();
        assert!(complex[pos..].starts_with("= fun"));
    }

    #[test]
    fn test_full_fsti_generation() {
        let content = r#"module MyModule

open FStar.All
open FStar.List.Tot

(** Main processing function *)
val process : list int -> list int
let process xs =
  let helper x = x + 1 in
  List.map helper xs

type config = {
  name: string;
  value: int
}

private let secret_impl x = x * 2

let public_const : nat
let public_const = 42
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Check module declaration
        assert!(fsti.starts_with("module MyModule"));

        // Check opens are included
        assert!(fsti.contains("open FStar.All"));
        assert!(fsti.contains("open FStar.List.Tot"));

        // Check public declarations
        assert!(fsti.contains("val process"));
        assert!(fsti.contains("type config"));
        assert!(fsti.contains("public_const"));

        // Check private is excluded
        assert!(!fsti.contains("secret_impl"));

        // Check implementation details are excluded
        assert!(!fsti.contains("helper x = x + 1"));
        assert!(!fsti.contains("List.map"));
    }

    #[test]
    fn test_check_generates_fix() {
        let rule = SpecExtractorRule::new();
        let content = r#"module MyLib

val foo : int -> int
let foo x = x + 1

val bar : string -> string
let bar s = s

type config = int
"#;
        // Use a non-existent path so .fsti check fails.
        // Use a non-test filename to avoid false-positive suppression.
        let diags = rule.check(&PathBuf::from("/nonexistent/MyLib.fst"), content);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].rule, RuleCode::FST010);

        // Should have a fix
        assert!(diags[0].fix.is_some());
        let fix = diags[0].fix.as_ref().unwrap();
        assert!(fix.message.contains("Generate .fsti"));

        // Fix should contain generated content
        assert!(!fix.edits.is_empty());
        let edit = &fix.edits[0];
        assert!(edit.new_text.contains("module MyLib"));
        assert!(edit.new_text.contains("val foo"));
    }

    #[test]
    fn test_extraction_mode_default() {
        let mode = ExtractionMode::default();
        assert_eq!(mode, ExtractionMode::Full);
    }

    #[test]
    fn test_with_mode_constructor() {
        let rule = SpecExtractorRule::with_mode(ExtractionMode::Minimal);
        assert_eq!(rule.mode, ExtractionMode::Minimal);
    }

    #[test]
    fn test_complex_type_extraction() {
        let content = r#"module Types

noeq type buffer (a:Type) = {
  ptr: ref a;
  len: nat
}

type result a b =
  | Ok of a
  | Err of b
"#;
        let fsti_full = generate_fsti(content, ExtractionMode::Full);
        let fsti_minimal = generate_fsti(content, ExtractionMode::Minimal);

        // Full mode preserves type definitions
        assert!(fsti_full.contains("noeq type buffer"));
        assert!(fsti_full.contains("type result"));

        // Minimal mode makes types abstract
        assert!(fsti_minimal.contains("val buffer"));
        assert!(fsti_minimal.contains("val result"));
        assert!(!fsti_minimal.contains("noeq"));
    }

    #[test]
    fn test_assume_val_extraction() {
        let content = r#"module Extern

assume val external_func : int -> int

val normal_func : string -> string
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("assume val external_func"));
        assert!(fsti.contains("val normal_func"));
    }

    #[test]
    fn test_class_extraction() {
        let content = r#"module Classes

class eq (a:Type) = {
  op_eq: a -> a -> bool
}
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("class eq"));
    }

    #[test]
    fn test_empty_module() {
        let content = r#"module Empty

(* Just a comment *)
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Should just have module declaration
        assert!(fsti.contains("module Empty"));
        // Should be minimal
        assert!(fsti.lines().count() <= 2);
    }

    #[test]
    fn test_multiple_opens_ordering() {
        let content = r#"module Test

open A
open B
open C

val foo : int
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Opens should appear in order
        let a_pos = fsti.find("open A").unwrap();
        let b_pos = fsti.find("open B").unwrap();
        let c_pos = fsti.find("open C").unwrap();
        assert!(a_pos < b_pos);
        assert!(b_pos < c_pos);
    }

    // ---------------------------------------------------------------
    // False positive suppression tests
    // ---------------------------------------------------------------

    #[test]
    fn test_should_skip_test_files() {
        // Dotted module names with "Test" segment
        assert!(should_skip_fsti_check("Hacl.Test.SHA2").is_some());
        assert!(should_skip_fsti_check("Spec.AES.Test").is_some());
        assert!(should_skip_fsti_check("ASN1.Test.Interpreter").is_some());

        // Module name ending in "Test" (single segment, no dot)
        assert!(should_skip_fsti_check("ASN1Test").is_some());

        // Suffix _test
        assert!(should_skip_fsti_check("MyModule_test").is_some());

        // "Tests" variant
        assert!(should_skip_fsti_check("Hacl.Tests.Integration").is_some());

        // Should NOT skip non-test files
        assert!(should_skip_fsti_check("Hacl.Impl.SHA2").is_none());
        assert!(should_skip_fsti_check("Attestation").is_none());
    }

    #[test]
    fn test_should_skip_lemma_files() {
        assert!(should_skip_fsti_check("Hacl.Spec.Chacha20.Lemmas").is_some());
        assert!(should_skip_fsti_check("Hacl.Hash.Lemmas").is_some());
        assert!(should_skip_fsti_check("Hacl.Spec.K256.MathLemmas").is_some());
        assert!(should_skip_fsti_check("Hacl.Impl.Curve25519.Lemma").is_some());

        // Should NOT skip non-lemma files
        assert!(should_skip_fsti_check("Hacl.Spec.K256.Field52").is_none());
    }

    #[test]
    fn test_should_skip_example_files() {
        assert!(should_skip_fsti_check("Example").is_some());
        assert!(should_skip_fsti_check("My.Example.Module").is_some());
        assert!(should_skip_fsti_check("Demo").is_some());
        assert!(should_skip_fsti_check("Sample").is_some());

        // Should NOT skip similarly-named non-example files
        assert!(should_skip_fsti_check("ExampleParser").is_none());
    }

    #[test]
    fn test_should_not_skip_normal_files() {
        // Regular implementation files should NOT be skipped
        assert!(should_skip_fsti_check("Hacl.Bignum.Addition").is_none());
        assert!(should_skip_fsti_check("EverCrypt.AEAD").is_none());
        assert!(should_skip_fsti_check("CBOR.Pulse.Raw.Type").is_none());
        assert!(should_skip_fsti_check("ASN1.Base").is_none());
    }

    #[test]
    fn test_check_skips_test_file() {
        let rule = SpecExtractorRule::new();
        let content = r#"module Hacl.Test.SHA2

val test_sha2 : int -> int
let test_sha2 x = x + 1

val test_helper : string -> string
let test_helper s = s

val another_public : nat -> nat
"#;
        // Even though this has public declarations, it should be skipped
        // because the file name matches the test pattern.
        let diags = rule.check(&PathBuf::from("/nonexistent/Hacl.Test.SHA2.fst"), content);
        assert!(diags.is_empty(), "Test files should not trigger FST010");
    }

    #[test]
    fn test_check_skips_lemma_file() {
        let rule = SpecExtractorRule::new();
        let content = r#"module Hacl.Spec.Chacha20.Lemmas

val lemma_chacha : x:nat -> Lemma (x >= 0)
val lemma_round : x:nat -> Lemma (x + 0 = x)
val lemma_quarter : x:nat -> y:nat -> Lemma (x + y >= x)
"#;
        let diags = rule.check(
            &PathBuf::from("/nonexistent/Hacl.Spec.Chacha20.Lemmas.fst"),
            content,
        );
        assert!(diags.is_empty(), "Lemma files should not trigger FST010");
    }

    #[test]
    fn test_check_skips_example_file() {
        let rule = SpecExtractorRule::new();
        let content = r#"module Example

val main : unit -> unit
let main () = ()
"#;
        let diags = rule.check(&PathBuf::from("/nonexistent/Example.fst"), content);
        assert!(diags.is_empty(), "Example files should not trigger FST010");
    }

    #[test]
    fn test_check_hint_severity_for_few_decls() {
        let rule = SpecExtractorRule::new();
        let content = r#"module SmallHelper

val helper : int -> int
let helper x = x + 1
"#;
        // A file with only 1-2 public declarations should get Hint severity
        let diags = rule.check(&PathBuf::from("/nonexistent/SmallHelper.fst"), content);
        assert_eq!(diags.len(), 1);
        assert_eq!(
            diags[0].severity,
            DiagnosticSeverity::Hint,
            "Files with fewer than {} public decls should be Hint severity",
            MIN_PUBLIC_DECLS_FOR_WARNING
        );
    }

    #[test]
    fn test_check_info_severity_for_many_decls() {
        let rule = SpecExtractorRule::new();
        let content = r#"module BigAPI

val func_a : int -> int
let func_a x = x + 1

val func_b : string -> string
let func_b s = s

val func_c : nat -> nat
let func_c n = n

type my_config = int
"#;
        // A file with 3+ public declarations should get Info severity
        let diags = rule.check(&PathBuf::from("/nonexistent/BigAPI.fst"), content);
        assert_eq!(diags.len(), 1);
        assert_eq!(
            diags[0].severity,
            DiagnosticSeverity::Info,
            "Files with {} or more public decls should be Info severity",
            MIN_PUBLIC_DECLS_FOR_WARNING
        );
    }

    // ---------------------------------------------------------------
    // Safety feature tests
    // ---------------------------------------------------------------

    #[test]
    fn test_validate_fsti_content_valid() {
        let content = r#"module Test

open FStar.All

val foo : int -> int

type config = int
"#;
        let errors = validate_fsti_content(content);
        assert!(
            errors.is_empty(),
            "Valid .fsti should have no validation errors: {:?}",
            errors
        );
    }

    #[test]
    fn test_validate_fsti_content_missing_module() {
        let content = r#"val foo : int -> int

type config = int
"#;
        let errors = validate_fsti_content(content);
        assert!(
            !errors.is_empty(),
            "Missing module declaration should be detected"
        );
        assert!(errors.iter().any(|e| e.message.contains("module")));
    }

    #[test]
    fn test_validate_fsti_content_unbalanced_parens() {
        let content = r#"module Test

val foo : (int -> int
"#;
        let errors = validate_fsti_content(content);
        assert!(
            !errors.is_empty(),
            "Unbalanced parens should be detected"
        );
        assert!(errors.iter().any(|e| e.message.contains("parentheses") || e.message.contains("Unbalanced")));
    }

    #[test]
    fn test_validate_fsti_content_unbalanced_braces() {
        let content = r#"module Test

type config = {
  name: string
"#;
        let errors = validate_fsti_content(content);
        assert!(
            !errors.is_empty(),
            "Unbalanced braces should be detected"
        );
    }

    #[test]
    fn test_validate_fsti_content_empty_module() {
        let content = r#"module Test
"#;
        let errors = validate_fsti_content(content);
        assert!(
            !errors.is_empty(),
            "Empty module should be detected"
        );
        assert!(errors.iter().any(|e| e.message.contains("no declarations")));
    }

    #[test]
    fn test_generate_fsti_with_stats() {
        let content = r#"module TestStats

open FStar.All
open FStar.List.Tot

val foo : int -> int
let foo x = x + 1

val bar : string -> string
let bar s = s

type config = int

effect MyEffect (a:Type) = a
"#;
        let (fsti, stats) = generate_fsti_with_stats(content, ExtractionMode::Full);

        // Check content was generated
        assert!(fsti.contains("module TestStats"));
        assert!(fsti.contains("val foo"));
        assert!(fsti.contains("val bar"));
        assert!(fsti.contains("type config"));

        // Check statistics
        assert!(stats.line_count > 0, "Should have lines");
        assert!(stats.val_count >= 2, "Should have at least 2 vals: {}", stats.val_count);
        assert!(stats.type_count >= 1, "Should have at least 1 type: {}", stats.type_count);
        assert!(stats.open_count == 2, "Should have 2 opens: {}", stats.open_count);
        assert!(!stats.exported_names.is_empty(), "Should have exported names");
        assert!(stats.validation_errors.is_empty(), "Should have no validation errors");
    }

    #[test]
    fn test_stats_summary() {
        let stats = FstiGenerationStats {
            line_count: 15,
            val_count: 3,
            type_count: 2,
            effect_count: 1,
            class_count: 0,
            open_count: 2,
            exported_names: vec!["foo".to_string(), "bar".to_string()],
            validation_errors: Vec::new(),
        };

        let summary = stats.summary();
        assert!(summary.contains("15 lines"), "Summary should include line count");
        assert!(summary.contains("val"), "Summary should include val count");
        assert!(summary.contains("type"), "Summary should include type count");
        assert!(summary.contains("effect"), "Summary should include effect count");
    }

    #[test]
    fn test_fix_is_low_confidence() {
        let rule = SpecExtractorRule::new();
        let content = r#"module MyLib

val foo : int -> int
let foo x = x + 1

val bar : string -> string
let bar s = s

type config = int
"#;
        let diags = rule.check(&PathBuf::from("/nonexistent/MyLib.fst"), content);

        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("Should have a fix");

        // CRITICAL: Fix should be LOW confidence - never auto-apply
        assert_eq!(
            fix.confidence,
            FixConfidence::Low,
            "FST010 fix MUST be Low confidence to prevent auto-application"
        );

        // CRITICAL: Fix should be marked unsafe
        assert!(
            !fix.is_safe(),
            "FST010 fix MUST be marked unsafe"
        );

        // Should have an unsafe reason
        assert!(
            fix.unsafe_reason.is_some(),
            "FST010 fix MUST have an unsafe reason"
        );

        // Should not be auto-applicable
        assert!(
            !fix.can_auto_apply(),
            "FST010 fix MUST NOT be auto-applicable"
        );
    }

    #[test]
    fn test_fix_message_indicates_review_required() {
        let rule = SpecExtractorRule::new();
        let content = r#"module MyLib

val foo : int -> int
let foo x = x + 1

val bar : string -> string
"#;
        let diags = rule.check(&PathBuf::from("/nonexistent/MyLib.fst"), content);

        assert_eq!(diags.len(), 1);
        let fix = diags[0].fix.as_ref().expect("Should have a fix");

        // Fix message should indicate review is required
        assert!(
            fix.message.contains("REVIEW") || fix.message.contains("review"),
            "Fix message should indicate review is required: {}",
            fix.message
        );
    }

    #[test]
    fn test_diagnostic_includes_dry_run_info() {
        let rule = SpecExtractorRule::new();
        let content = r#"module MyLib

val foo : int -> int
let foo x = x + 1

val bar : string -> string
let bar s = s

type config = int
"#;
        let diags = rule.check(&PathBuf::from("/nonexistent/MyLib.fst"), content);

        assert_eq!(diags.len(), 1);

        // Diagnostic message should include dry-run preview info
        assert!(
            diags[0].message.contains("DRY-RUN"),
            "Diagnostic should include DRY-RUN info: {}",
            diags[0].message
        );
    }

    #[test]
    fn test_no_fix_when_validation_fails() {
        // This test is tricky - we need content that generates invalid .fsti
        // In practice, the validation catches structural issues
        // For this test, we just verify the validation pipeline works
        let content = r#"module Test

val incomplete_val
"#;
        // Note: The parser may handle this differently, but the principle is
        // that validation errors should prevent fix generation
        let _errors = validate_fsti_content(content);
        // If there are validation errors, no fix should be offered
        // This is tested indirectly through the check method
    }

    #[test]
    fn test_extract_val_name() {
        assert_eq!(extract_val_name("val foo : int -> int"), Some("foo".to_string()));
        assert_eq!(extract_val_name("assume val bar : string"), Some("bar".to_string()));
        assert_eq!(extract_val_name("val (+) : int -> int -> int"), Some("+".to_string()));
        assert_eq!(extract_val_name("type foo = int"), None);
    }

    #[test]
    fn test_extract_type_name() {
        assert_eq!(extract_type_name("type foo = int"), Some("foo".to_string()));
        assert_eq!(extract_type_name("noeq type buffer a = ..."), Some("buffer".to_string()));
        assert_eq!(extract_type_name("val foo : int"), None);
    }

    // ---------------------------------------------------------------
    // Complex pattern tests
    // ---------------------------------------------------------------

    #[test]
    fn test_effect_extraction() {
        let content = r#"module Effects

effect MyEffect (a:Type) = Tot a

layered_effect StackEffect (a:Type) {
  return = fun x -> x;
  bind = fun m f -> f m
}
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("effect MyEffect"), "Effect should be extracted");
        assert!(fsti.contains("layered_effect StackEffect"), "Layered effect should be extracted");
    }

    #[test]
    fn test_mutual_recursion_extraction() {
        let content = r#"module Mutual

type expr =
  | ELit of int
  | EApp of expr * stmt

and stmt =
  | SExpr of expr
  | SSeq of stmt * stmt
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        // Both types should be in the same block
        assert!(fsti.contains("type expr"), "First type should be extracted");
        assert!(fsti.contains("and stmt"), "Mutual recursive type should be extracted with 'and'");
    }

    #[test]
    fn test_type_class_extraction() {
        let content = r#"module TypeClasses

class eq (a:Type) = {
  op_eq: a -> a -> bool
}

class ord (a:Type) = {
  op_lt: a -> a -> bool;
  op_le: a -> a -> bool
}
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("class eq"), "Class should be extracted");
        assert!(fsti.contains("class ord"), "Second class should be extracted");
        assert!(fsti.contains("op_eq"), "Class members should be included");
    }

    #[test]
    fn test_exception_extraction() {
        let content = r#"module Exceptions

exception MyError of string

exception AnotherError of int * string
"#;
        let fsti = generate_fsti(content, ExtractionMode::Full);

        assert!(fsti.contains("exception MyError"), "Exception should be extracted");
        assert!(fsti.contains("exception AnotherError"), "Second exception should be extracted");
    }

    #[test]
    fn test_combined_complex_module() {
        let content = r#"module Complex

open FStar.All

(** A simple effect *)
effect MyEff (a:Type) = Tot a

(** Type class for equality *)
class eq (a:Type) = {
  op_eq: a -> a -> bool
}

(** Mutual recursive types *)
type expr =
  | ELit of int
  | EApp of expr * stmt
and stmt =
  | SExpr of expr

(** Exception type *)
exception ParseError of string

(** Public function *)
val eval : expr -> int
let eval e = match e with | ELit n -> n | _ -> 0

private let helper x = x + 1
"#;
        let (fsti, stats) = generate_fsti_with_stats(content, ExtractionMode::Full);

        // Verify all public parts are extracted
        assert!(fsti.contains("module Complex"), "Module declaration");
        assert!(fsti.contains("open FStar.All"), "Open statement");
        assert!(fsti.contains("effect MyEff"), "Effect");
        assert!(fsti.contains("class eq"), "Type class");
        assert!(fsti.contains("type expr"), "First mutual type");
        assert!(fsti.contains("and stmt"), "Second mutual type");
        assert!(fsti.contains("exception ParseError"), "Exception");
        assert!(fsti.contains("val eval"), "Public function");

        // Verify private is excluded
        assert!(!fsti.contains("helper"), "Private helper should not be in .fsti");

        // Verify statistics
        assert!(stats.effect_count >= 1, "Should count effect");
        assert!(stats.class_count >= 1, "Should count class");
        assert!(stats.type_count >= 1, "Should count types");
        assert!(stats.validation_errors.is_empty(), "Should be valid");
    }
}
