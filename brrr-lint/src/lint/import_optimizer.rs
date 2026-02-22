//! FST008: Import optimization.
//!
//! Detects import patterns that can be improved for better verification performance
//! and code clarity. This rule focuses on optimizing module imports in F* source files.
//!
//! # Detection Categories
//!
//! - **FST008-A**: Broad import when selective would suffice (`open M` when only 1-3 names used)
//! - **FST008-B**: Unused import (redundant with FST004 but provides additional context)
//! - **FST008-C**: Qualified names preferred over open for infrequently used modules
//! - **FST008-D**: Circular import detection (module A opens B which opens A)
//! - **FST008-E**: Unnecessary transitive import (opening module that re-exports another)
//! - **FST008-H**: Heavy module import warning (Tactics, Reflection)
//!
//! Note: FST008-F (import ordering) was removed. The "Core > Pure > Effect > Project"
//! categorization produced false positives because it did not match actual F* conventions.
//! Many FStar.* modules were miscategorized, and no community standard for import ordering
//! exists in the F* ecosystem.
//!
//! # Heavy Modules
//!
//! Some F* modules are known to significantly slow down verification when imported:
//! - `FStar.Tactics.V2` and `FStar.Tactics` - Full tactics machinery
//! - `FStar.Reflection.V2` and `FStar.Reflection` - Reflection capabilities
//!
//! These should be imported selectively or avoided when not necessary.

use lazy_static::lazy_static;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::rules::{Diagnostic, DiagnosticSeverity, Edit, Fix, Range, Rule, RuleCode};
use super::shared_patterns::{INCLUDE_MODULE_RE, QUALIFIED_USE_RE, MODULE_DECL_RE};
use super::unused_opens::{analyze_opens, OpenStatement};

/// Broadness classification for modules that are too broad to open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BroadnessLevel {
    /// Top-level namespace (e.g., `open FStar`) -- not a real module
    Critical,
    /// Umbrella module re-exporting many submodules (e.g., `FStar.All`)
    High,
    /// Large module with many exports
    Medium,
}

impl BroadnessLevel {
    fn severity(self) -> DiagnosticSeverity {
        match self {
            // Critical: top-level namespaces (`open FStar`) are not real modules
            BroadnessLevel::Critical => DiagnosticSeverity::Error,
            // High/Medium: umbrella and large modules are a style preference,
            // not a correctness issue. Demoted to Info to avoid noise.
            BroadnessLevel::High => DiagnosticSeverity::Info,
            BroadnessLevel::Medium => DiagnosticSeverity::Hint,
        }
    }

    fn label(self) -> &'static str {
        match self {
            BroadnessLevel::Critical => "namespace, not a module",
            BroadnessLevel::High => "umbrella module with many re-exports",
            BroadnessLevel::Medium => "large module with many exports",
        }
    }
}

lazy_static! {
    /// Heavy modules that significantly slow verification when imported.
    /// These should be imported selectively or with caution.
    static ref HEAVY_MODULES: HashSet<&'static str> = {
        let mut set = HashSet::new();
        set.insert("FStar.Tactics.V2");
        set.insert("FStar.Tactics");
        set.insert("FStar.Reflection.V2");
        set.insert("FStar.Reflection");
        set.insert("FStar.Tactics.V2.Derived");
        set.insert("FStar.Tactics.V2.SyntaxCoercions");
        set.insert("FStar.Tactics.CanonCommMonoid");
        set.insert("FStar.Tactics.CanonCommSemiring");
        set
    };

    /// Modules that are idiomatically opened in their entirety in F* code.
    /// These provide operators, types, or pervasive definitions that are
    /// designed to be used unqualified. Opening them is standard practice
    /// and should never trigger FST008-A or FST008-C warnings.
    static ref WHITELISTED_OPENS: HashSet<&'static str> = {
        let mut set = HashSet::new();
        // Prims - the fundamental prelude module (int, bool, nat, list, etc.)
        // Implicitly opened in every F* file; explicitly opened in [@@"no_prelude"] modules
        set.insert("Prims");
        // Operator modules - bring arithmetic operators into scope
        set.insert("FStar.Mul");                // op_Star for natural number multiplication (*)
        set.insert("FStar.Pervasives");         // Core pervasives
        set.insert("FStar.Pervasives.Native");  // Native tuples etc.
        // Commonly opened effect/memory modules
        set.insert("FStar.HyperStack");         // mem, contains, etc.
        set.insert("FStar.HyperStack.ST");      // Stack effect, push/pop_frame
        set.insert("FStar.HyperStack.All");     // Combined HyperStack effect
        set.insert("FStar.ST");                 // State effect
        set.insert("FStar.Ghost");              // Ghost/erased types
        // Buffer/memory modules - provide many unqualified names
        set.insert("Lib.Buffer");               // HACL* buffer operations
        set.insert("Lib.IntTypes");             // Integer types and operators
        set.insert("Lib.Sequence");             // Sequence operations
        set.insert("Lib.ByteBuffer");           // Byte buffer operations
        set.insert("Lib.ByteSequence");         // Byte sequence operations
        set.insert("Lib.LoopCombinators");      // Loop combinators
        set.insert("Lib.IntVector");            // SIMD vector types
        set.insert("Lib.NTuple");               // N-tuples
        set.insert("Lib.MultiBuffer");          // Multi-buffer operations
        set.insert("LowStar.Buffer");           // Low* buffer operations
        set.insert("LowStar.BufferOps");        // Low* buffer operators (!*, *=)
        set.insert("LowStar.Monotonic.Buffer"); // Monotonic buffer
        // Common spec/math modules
        set.insert("FStar.Math.Lemmas");        // Math lemma helpers
        set.insert("FStar.Classical");          // Classical reasoning
        set.insert("FStar.Calc");               // Calculation proofs
        set
    };

    /// Modules that re-export other modules (transitive imports).
    /// Maps re-exporting module to what it re-exports.
    static ref TRANSITIVE_EXPORTS: HashMap<&'static str, Vec<&'static str>> = {
        let mut map = HashMap::new();
        map.insert("FStar.All", vec!["FStar.Exn", "FStar.ST"]);
        map.insert("FStar.HyperStack.All", vec!["FStar.HyperStack.ST", "FStar.HyperStack"]);
        map.insert("FStar.Tactics.V2", vec!["FStar.Tactics.V2.Derived", "FStar.Tactics.V2.SyntaxHelpers"]);
        map
    };

    /// Known module exports - maps module name to commonly used exports.
    /// Used to suggest selective imports when only a few names are used.
    static ref KNOWN_EXPORTS: HashMap<&'static str, Vec<&'static str>> = {
        let mut map = HashMap::new();
        map.insert("FStar.List.Tot", vec![
            "length", "hd", "tl", "nth", "index", "rev", "append",
            "map", "mapi", "fold_left", "fold_right", "filter", "mem",
            "for_all", "existsb", "find", "assoc", "split", "concatMap",
        ]);
        map.insert("FStar.Seq", vec![
            "seq", "length", "index", "create", "upd", "append", "slice",
            "init", "head", "tail", "last", "cons", "snoc", "equal",
        ]);
        map.insert("FStar.Set", vec![
            "set", "empty", "singleton", "union", "intersect", "complement",
            "mem", "equal", "subset", "disjoint",
        ]);
        map.insert("FStar.Map", vec![
            "map", "sel", "upd", "const", "concat", "restrict", "contains",
            "domain", "equal",
        ]);
        // Note: FStar.Mul and Lib.IntTypes are in WHITELISTED_OPENS and excluded
        // from KNOWN_EXPORTS. FStar.Mul provides op_Star (the * operator) which
        // is not detectable as an identifier. Lib.IntTypes provides operators,
        // type abbreviations, and coercions that are pervasive in HACL* code.
        map.insert("FStar.UInt32", vec![
            "t", "v", "uint_to_t", "add", "sub", "mul", "div",
            "add_mod", "sub_mod", "mul_mod", "logand", "logor", "logxor",
        ]);
        map.insert("FStar.UInt64", vec![
            "t", "v", "uint_to_t", "add", "sub", "mul", "div",
            "add_mod", "sub_mod", "mul_mod", "logand", "logor", "logxor",
        ]);
        map
    };

    /// Threshold for suggesting selective import (if using <= this many names, suggest selective)
    static ref SELECTIVE_THRESHOLD: usize = 3;

    /// Broadness database: modules that are considered "too broad" to open.
    /// These are top-level namespace modules or umbrella modules that bring
    /// hundreds of names into scope. Opening them pollutes the namespace and
    /// makes code harder to understand.
    ///
    /// Broadness levels:
    /// - Critical: Top-level namespace opens (open FStar, open LowStar)
    /// - High: Umbrella modules re-exporting many submodules
    /// - Medium: Large modules with many exports
    static ref BROAD_MODULES: HashMap<&'static str, BroadnessLevel> = {
        let mut map = HashMap::new();
        // Critical: top-level namespaces - these don't even exist as real modules
        map.insert("FStar", BroadnessLevel::Critical);
        map.insert("LowStar", BroadnessLevel::Critical);
        map.insert("Lib", BroadnessLevel::Critical);
        map.insert("Hacl", BroadnessLevel::Critical);
        map.insert("Spec", BroadnessLevel::Critical);
        // NOTE: Prims is NOT a namespace -- it is a real F* module containing
        // fundamental types (int, bool, nat, string, list, etc.) and operators.
        // It is implicitly opened in every F* file, but core ulib modules with
        // [@@"no_prelude"] explicitly `open Prims`. Do NOT add it here.
        // High: umbrella modules that re-export many things
        map.insert("FStar.All", BroadnessLevel::High);
        map.insert("FStar.Tactics.V2", BroadnessLevel::High);
        map.insert("FStar.Reflection.V2", BroadnessLevel::High);
        // Medium: large modules with many exports
        map.insert("FStar.Pervasives", BroadnessLevel::Medium);
        map
    };
}

/// Information about how a module's exports are used in the file.
#[derive(Debug, Default, Clone)]
struct ModuleUsage {
    /// Names from this module that are used unqualified
    unqualified_names: HashSet<String>,
    /// Times this module is used with qualified access (e.g., Module.foo)
    qualified_uses: usize,
    /// The open statement for this module (if any)
    open_line: Option<usize>,
}

/// Import optimization analysis result.
#[derive(Debug)]
struct ImportAnalysis {
    /// Open statements in the file
    opens: Vec<OpenStatement>,
    /// Module usage information
    module_usage: HashMap<String, ModuleUsage>,
    /// Current module name (from module declaration)
    current_module: Option<String>,
}

/// Analyze imports and their usage in the file.
fn analyze_imports(content: &str) -> ImportAnalysis {
    let open_analysis = analyze_opens(content);
    let mut module_usage: HashMap<String, ModuleUsage> = HashMap::new();

    // Extract current module name
    let current_module = extract_current_module(content);

    // Track open statements
    for open in &open_analysis.opens {
        let usage = module_usage.entry(open.module_path.clone()).or_default();
        usage.open_line = Some(open.line);
    }

    // Track qualified uses
    let qualified_modules = extract_qualified_modules(content);
    for module in &qualified_modules {
        let usage = module_usage.entry(module.clone()).or_default();
        usage.qualified_uses += 1;
    }

    // Track unqualified identifier usage per module (for modules with known exports)
    for (module, exports) in KNOWN_EXPORTS.iter() {
        let usage = module_usage.entry(module.to_string()).or_default();
        for export in exports.iter() {
            if open_analysis.used_identifiers.contains(*export) {
                usage.unqualified_names.insert(export.to_string());
            }
        }
    }

    ImportAnalysis {
        opens: open_analysis.opens,
        module_usage,
        current_module,
    }
}

/// Extract the current module name from the module declaration.
fn extract_current_module(content: &str) -> Option<String> {
    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(caps) = MODULE_DECL_RE.captures(trimmed) {
            return caps.get(1).map(|m| m.as_str().to_string());
        }
    }
    None
}

/// Extract modules used via qualified access.
///
/// Filters out declaration lines (open, module, friend, include) so that
/// qualified module paths appearing in those lines are not mistakenly counted
/// as "qualified usage". For example, `open FStar.HyperStack.ST` should not
/// cause `FStar.HyperStack` to appear as a qualified use of that module.
fn extract_qualified_modules(content: &str) -> HashSet<String> {
    let mut modules = HashSet::new();

    // Filter out declaration lines before analysis to avoid false positives.
    // Without this, `open FStar.HyperStack.ST` would make the regex extract
    // `FStar.HyperStack` as a qualified use, causing FST008-C to fire on
    // `open FStar.HyperStack` (claiming it's "only accessed via qualified names").
    let filtered: String = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            !trimmed.starts_with("open ")
                && !trimmed.starts_with("module ")
                && !trimmed.starts_with("friend ")
                && !trimmed.starts_with("include ")
        })
        .collect::<Vec<_>>()
        .join("\n");

    let clean = strip_comments_and_strings(&filtered);

    for caps in QUALIFIED_USE_RE.captures_iter(&clean) {
        if let Some(m) = caps.get(1) {
            modules.insert(m.as_str().to_string());
        }
    }

    modules
}

/// Strip comments and string literals for accurate analysis.
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
                i += 1;
            }
            continue;
        }

        result.push(chars[i]);
        i += 1;
    }

    result
}

/// Result of circular import analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircularImportType {
    /// Module imports itself (A opens A)
    SelfImport,
    /// Child module imports parent (A.B opens A) - may cause dependency cycle
    ChildImportsParent,
    /// Parent module imports child (A opens A.B) - unusual but sometimes valid
    ParentImportsChild,
    /// No circular dependency detected
    None,
}

impl CircularImportType {
    /// Returns the severity for this type of circular import.
    pub fn severity(&self) -> DiagnosticSeverity {
        match self {
            CircularImportType::SelfImport => DiagnosticSeverity::Error,
            CircularImportType::ChildImportsParent => DiagnosticSeverity::Warning,
            CircularImportType::ParentImportsChild => DiagnosticSeverity::Info,
            CircularImportType::None => DiagnosticSeverity::Hint,
        }
    }

    /// Returns a descriptive message for this type of circular import.
    pub fn message(&self, current: &str, imported: &str) -> String {
        match self {
            CircularImportType::SelfImport => {
                format!("[FST008-D] Self-import: module `{}` opens itself", current)
            }
            CircularImportType::ChildImportsParent => {
                format!(
                    "[FST008-D] Parent import: module `{}` opens parent `{}` - may cause circular dependency",
                    current, imported
                )
            }
            CircularImportType::ParentImportsChild => {
                format!(
                    "[FST008-D] Child import: module `{}` opens child `{}` - unusual pattern, ensure no dependency cycle",
                    current, imported
                )
            }
            CircularImportType::None => String::new(),
        }
    }
}

/// Extract the top-level namespace of a module path.
///
/// For `FStar.Tactics.V2.Derived` returns `FStar.Tactics`.
/// For `FStar.Reflection.V2` returns `FStar.Reflection`.
/// For `FStar.All` returns `FStar`.
/// For `Prims` returns `Prims`.
///
/// This groups modules into their logical subsystem so we can determine
/// when an umbrella import is natural (within the same subsystem).
fn umbrella_namespace(module: &str) -> &str {
    // Take the first two components: FStar.Tactics, FStar.Reflection, etc.
    let mut dots = 0;
    for (i, c) in module.char_indices() {
        if c == '.' {
            dots += 1;
            if dots == 2 {
                return &module[..i];
            }
        }
    }
    // Fewer than 2 dots: return the whole thing
    module
}

/// Check whether two namespaces are tightly coupled such that importing
/// one from the other is expected and should not be flagged.
///
/// F*'s Tactics system is deeply intertwined with Reflection: every tactic
/// inspects and manipulates terms via Reflection. Similarly, Reflection
/// modules use Tactics for proof automation. Flagging `open FStar.Reflection.V2`
/// inside `FStar.Tactics.Canon` would produce 30+ false positives on ulib.
fn namespaces_are_coupled(ns_a: &str, ns_b: &str) -> bool {
    if ns_a == ns_b {
        return true;
    }
    // Tactics <-> Reflection are tightly coupled
    let coupled_pairs: &[(&str, &str)] = &[
        ("FStar.Tactics", "FStar.Reflection"),
        ("FStar.Stubs", "FStar.Reflection"),
        ("FStar.Stubs", "FStar.Tactics"),
    ];
    for &(a, b) in coupled_pairs {
        if (ns_a == a && ns_b == b) || (ns_a == b && ns_b == a) {
            return true;
        }
    }
    false
}

/// Analyze circular import relationship between current module and imported module.
fn analyze_circular_import(current_module: &Option<String>, imported: &str) -> CircularImportType {
    if let Some(current) = current_module {
        // Direct circular: A opens A
        if current == imported {
            return CircularImportType::SelfImport;
        }

        // Child imports parent: A.B.C opens A.B or A
        // Check if current module starts with imported module (current is a child of imported)
        if current.starts_with(&format!("{}.", imported)) {
            return CircularImportType::ChildImportsParent;
        }

        // Parent imports child: A opens A.B or A.B.C
        // Check if imported module starts with current module (imported is a child of current)
        if imported.starts_with(&format!("{}.", current)) {
            return CircularImportType::ParentImportsChild;
        }
    }
    CircularImportType::None
}

/// Check if a module path indicates circular dependency with current module.
/// Returns true for any form of circular dependency (self, parent, or child).
#[allow(dead_code)]
fn is_circular_import(current_module: &Option<String>, imported: &str) -> bool {
    analyze_circular_import(current_module, imported) != CircularImportType::None
}

/// Generate a fix to convert broad open to selective open.
fn generate_selective_fix(
    open: &OpenStatement,
    used_names: &HashSet<String>,
    file: &Path,
) -> Option<Fix> {
    if used_names.is_empty() {
        return None;
    }

    let names: Vec<_> = used_names.iter().cloned().collect();
    let selective_import = format!("open {} {{ {} }}", open.module_path, names.join(", "));

    Some(Fix::new(
        format!(
            "Convert to selective import: only {} name{} used",
            names.len(),
            if names.len() == 1 { "" } else { "s" }
        ),
        vec![Edit {
            file: file.to_path_buf(),
            range: Range::new(open.line, 1, open.line, 1),
            new_text: format!("{}\n", selective_import),
        }],
    ))
}

/// Generate a fix to use qualified access instead of open.
fn generate_qualified_fix(open: &OpenStatement, file: &Path) -> Fix {
    Fix::new(
        format!(
            "Remove open and use qualified access: `{}.name`",
            open.module_path
        ),
        vec![Edit {
            file: file.to_path_buf(),
            range: Range::new(open.line, 1, open.line, 1),
            new_text: String::new(),
        }],
    )
}

/// Determine if an `include` statement is an aggregation pattern.
///
/// Returns true when the include is part of a standard F* module
/// composition pattern, meaning the diagnostic should be suppressed.
///
/// Aggregation patterns:
/// 1. Including a direct sub-module: `FStar.Seq` includes `FStar.Seq.Base`
/// 2. Including a sibling with shared prefix: `FStar.All` includes `FStar.ST`
/// 3. Including a Stubs/internal module: `FStar.Reflection.V2` includes
///    `FStar.Stubs.Reflection.V2.Data`
/// 4. Including bootstrap modules: `FStar.Prelude` includes `Prims`
/// 5. Including modules in the whitelisted opens set (these are designed
///    to be composed into aggregate modules)
fn is_aggregation_include(current_module: &Option<String>, included: &str) -> bool {
    let Some(current) = current_module else {
        return false;
    };

    // Pattern 1: Sub-module inclusion (most common aggregation pattern)
    // FStar.Seq includes FStar.Seq.Base -> included starts with current + "."
    if included.starts_with(&format!("{}.", current)) {
        return true;
    }

    // Pattern 2: Parent aggregation -- parent module includes its parts
    // FStar.List.Pure includes FStar.List.Tot (sibling)
    // FStar.All includes FStar.ST, FStar.Exn (siblings under FStar)
    // Both current and included share a common prefix
    if let Some(parent) = current.rsplit_once('.').map(|(p, _)| p) {
        if included.starts_with(&format!("{}.", parent)) {
            return true;
        }
    }

    // Pattern 3: Including Stubs/internal implementation modules
    // FStar.Reflection.V2 includes FStar.Stubs.Reflection.V2.Data
    // FStar.Stubs.Tactics.Types includes FStar.Stubs.Tactics.Common
    if included.contains(".Stubs.") || current.contains(".Stubs.") {
        return true;
    }

    // Pattern 4: Bootstrapping -- FStar.Prelude includes Prims
    // These are fundamental module composition at the language level
    if WHITELISTED_OPENS.contains(included) {
        return true;
    }

    // Pattern 5: Same or coupled top-level namespace. The current module
    // is an aggregate building from closely related subsystems.
    // FStar.Tactics.V2.Bare includes FStar.Reflection.V2 (coupled ns)
    // FStar.Seq includes FStar.Seq.Base (same ns)
    if namespaces_are_coupled(umbrella_namespace(current), umbrella_namespace(included)) {
        return true;
    }

    false
}

/// FST008: Import Optimizer rule.
///
/// Detects import patterns that can be improved for better verification
/// performance and code clarity.
pub struct ImportOptimizerRule {
    /// Threshold for suggesting selective import.
    /// If a module is opened but only N or fewer names are used, suggest selective import.
    selective_threshold: usize,
}

impl ImportOptimizerRule {
    /// Create a new ImportOptimizerRule with default settings.
    pub fn new() -> Self {
        Self {
            selective_threshold: *SELECTIVE_THRESHOLD,
        }
    }

    /// Create with custom selective threshold.
    pub fn with_threshold(threshold: usize) -> Self {
        Self {
            selective_threshold: threshold,
        }
    }

    /// Check for heavy module imports that may slow verification.
    ///
    /// Suppresses the warning when the current module is within the same
    /// subsystem as the heavy import. For example, `FStar.Tactics.Canon`
    /// importing `FStar.Tactics.V2.Derived` is necessary and expected --
    /// every tactics module needs the derived combinators.
    fn check_heavy_modules(
        &self,
        open: &OpenStatement,
        current_module: &Option<String>,
        file: &Path,
    ) -> Option<Diagnostic> {
        if !HEAVY_MODULES.contains(open.module_path.as_str()) {
            return None;
        }

        // Suppress when current module is in the same or coupled subsystem.
        // FStar.Tactics.Canon importing FStar.Tactics.V2.Derived -> suppress (same ns)
        // FStar.Tactics.Auto importing FStar.Reflection -> suppress (coupled ns)
        // FStar.Reflection.V2.Arith importing FStar.Reflection -> suppress (same ns)
        if let Some(current) = current_module {
            let current_ns = umbrella_namespace(current);
            let import_ns = umbrella_namespace(&open.module_path);
            if namespaces_are_coupled(current_ns, import_ns) {
                return None;
            }
        }

        Some(Diagnostic {
            rule: RuleCode::FST008,
            severity: DiagnosticSeverity::Info,
            file: file.to_path_buf(),
            range: Range::new(
                open.line,
                open.col,
                open.line,
                open.col + open.line_text.trim().len(),
            ),
            message: format!(
                "[FST008-H] Heavy import: `{}` may significantly slow verification. \
                 Consider selective import or ensure it's necessary.",
                open.module_path
            ),
            fix: None,
        })
    }

    /// Check for broad imports where selective would suffice.
    fn check_broad_import(
        &self,
        open: &OpenStatement,
        usage: &ModuleUsage,
        file: &Path,
    ) -> Option<Diagnostic> {
        // Skip if already selective
        if open.selective.is_some() {
            return None;
        }

        // Skip whitelisted modules - they are designed to be opened entirely
        // (e.g., FStar.Mul for operators, Lib.IntTypes for integer types)
        if WHITELISTED_OPENS.contains(open.module_path.as_str()) {
            return None;
        }

        // Check if we have known exports for this module
        if let Some(_exports) = KNOWN_EXPORTS.get(open.module_path.as_str()) {
            let used_count = usage.unqualified_names.len();

            // If only a few names are used, suggest selective import
            if used_count > 0 && used_count <= self.selective_threshold {
                let fix = generate_selective_fix(open, &usage.unqualified_names, file);

                return Some(Diagnostic {
                    rule: RuleCode::FST008,
                    severity: DiagnosticSeverity::Info,
                    file: file.to_path_buf(),
                    range: Range::new(
                        open.line,
                        open.col,
                        open.line,
                        open.col + open.line_text.trim().len(),
                    ),
                    message: format!(
                        "[FST008-A] Broad import: `open {}` but only {} name{} used ({}). \
                         Consider selective import.",
                        open.module_path,
                        used_count,
                        if used_count == 1 { "" } else { "s" },
                        usage
                            .unqualified_names
                            .iter()
                            .cloned()
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    fix,
                });
            }
        }

        None
    }

    /// Check for imports where qualified access would be clearer.
    ///
    /// Only emits a diagnostic when we can reliably determine that the module
    /// is not used unqualified. This requires the module to be in KNOWN_EXPORTS
    /// so we can check which names it provides. For modules not in KNOWN_EXPORTS,
    /// we cannot know what names the open brings into scope, so we skip the check
    /// to avoid false positives.
    fn check_prefer_qualified(
        &self,
        open: &OpenStatement,
        usage: &ModuleUsage,
        file: &Path,
    ) -> Option<Diagnostic> {
        // Skip whitelisted modules - they are designed to be opened entirely
        // and may bring operators or types not trackable by identifier scanning
        if WHITELISTED_OPENS.contains(open.module_path.as_str()) {
            return None;
        }

        // Only emit FST008-C for modules in KNOWN_EXPORTS where we can reliably
        // determine unqualified usage. For unknown modules, we have no way to know
        // what names the open brings into scope, so emitting a warning would be
        // a false positive in most cases.
        if !KNOWN_EXPORTS.contains_key(open.module_path.as_str()) {
            return None;
        }

        // If module is only used via qualified access anyway, the open is redundant
        if usage.qualified_uses > 0 && usage.unqualified_names.is_empty() {
            return Some(Diagnostic {
                rule: RuleCode::FST008,
                severity: DiagnosticSeverity::Hint,
                file: file.to_path_buf(),
                range: Range::new(
                    open.line,
                    open.col,
                    open.line,
                    open.col + open.line_text.trim().len(),
                ),
                message: format!(
                    "[FST008-C] Unnecessary open: `{}` is only accessed via qualified names. \
                     Consider removing the open statement.",
                    open.module_path
                ),
                fix: Some(generate_qualified_fix(open, file)),
            });
        }

        None
    }

    /// Check for circular imports with differentiated severity.
    ///
    /// Only reports truly problematic circular imports:
    /// - Self-import (Error): Module opens itself -- always a bug
    ///
    /// Child-imports-parent (`A.B` opens `A`) is suppressed because it is a
    /// completely normal and pervasive pattern in F*. The standard library uses
    /// this extensively: `FStar.Seq.Permutation` opens `FStar.Seq`,
    /// `FStar.HyperStack.ST` opens `FStar.HyperStack`, etc. F* resolves
    /// dependencies via interface files (.fsti), so there is no circular
    /// dependency risk. Flagging this would produce 17+ false positives on ulib.
    ///
    /// Parent-imports-child (`A` opens `A.B`) is similarly suppressed -- parent
    /// modules routinely open child sub-modules to compose functionality.
    fn check_circular_import(
        &self,
        open: &OpenStatement,
        current_module: &Option<String>,
        file: &Path,
    ) -> Option<Diagnostic> {
        let circular_type = analyze_circular_import(current_module, &open.module_path);

        // Only report self-import. Both child-imports-parent and parent-imports-child
        // are normal F* patterns that do not indicate bugs:
        // - Child-imports-parent: FStar.Seq.Permutation opens FStar.Seq (pervasive)
        // - Parent-imports-child: FStar.Seq opens FStar.Seq.Base (aggregation)
        if circular_type != CircularImportType::SelfImport {
            return None;
        }

        let current = current_module.as_deref().unwrap_or("<unknown>");
        Some(Diagnostic {
            rule: RuleCode::FST008,
            severity: circular_type.severity(),
            file: file.to_path_buf(),
            range: Range::new(
                open.line,
                open.col,
                open.line,
                open.col + open.line_text.trim().len(),
            ),
            message: circular_type.message(current, &open.module_path),
            fix: None,
        })
    }

    /// Check for overly broad namespace opens from the broadness database.
    ///
    /// Detects `open FStar`, `open LowStar`, `open Hacl` etc. which are
    /// namespace prefixes, not real modules. Also flags umbrella modules
    /// that bring too many names into scope.
    ///
    /// Suppresses umbrella warnings when the current module is within the
    /// umbrella's namespace (e.g., `FStar.Tactics.Canon` opening
    /// `FStar.Tactics.V2` is standard practice within the tactics library).
    fn check_broad_namespace(
        &self,
        open: &OpenStatement,
        current_module: &Option<String>,
        file: &Path,
    ) -> Option<Diagnostic> {
        if let Some(level) = BROAD_MODULES.get(open.module_path.as_str()) {
            // For High/Medium (umbrella modules), suppress when the current module
            // is within the same or a coupled namespace. Examples:
            //   FStar.Tactics.Canon opening FStar.Tactics.V2 -> suppress (same ns)
            //   FStar.Tactics.Canon opening FStar.Reflection.V2 -> suppress (coupled)
            //   FStar.Reflection.V2.Arith opening FStar.Reflection.V2 -> suppress (same ns)
            //   FStar.IO opening FStar.All -> suppress (FStar.All is standard)
            //   FStar.List.fst opening FStar.All -> suppress (FStar.All is standard)
            //
            // The rationale: within the standard library's tactics/reflection
            // subsystem, these umbrella opens are the idiomatic and only way to
            // get the required names in scope. Tactics code necessarily uses
            // Reflection for term inspection/manipulation. Flagging these produces
            // 30+ false positives on ulib alone.
            if *level != BroadnessLevel::Critical {
                if let Some(current) = current_module {
                    let umbrella_ns = umbrella_namespace(&open.module_path);
                    let current_ns = umbrella_namespace(current);

                    if current.starts_with(&format!("{}.", open.module_path))
                        || namespaces_are_coupled(current_ns, umbrella_ns)
                        || open.module_path == "FStar.All"
                    {
                        return None;
                    }
                }
            }

            let suggestion = match *level {
                BroadnessLevel::Critical => format!(
                    "Use a specific submodule instead (e.g., `open {}.List.Tot` or `open {}.Seq`).",
                    open.module_path, open.module_path
                ),
                BroadnessLevel::High => format!(
                    "Import specific submodules of `{}` instead of the umbrella module.",
                    open.module_path
                ),
                BroadnessLevel::Medium => format!(
                    "Consider using qualified access (`{}.name`) or selective import.",
                    open.module_path
                ),
            };

            return Some(Diagnostic {
                rule: RuleCode::FST008,
                severity: level.severity(),
                file: file.to_path_buf(),
                range: Range::new(
                    open.line,
                    open.col,
                    open.line,
                    open.col + open.line_text.trim().len(),
                ),
                message: format!(
                    "[FST008-G] Overly broad import: `open {}` is a {} -- {}",
                    open.module_path,
                    level.label(),
                    suggestion
                ),
                fix: None,
            });
        }
        None
    }

    /// Check for `include` statements that may be overly broad.
    ///
    /// `include` in F* brings ALL names from the included module into scope
    /// and makes them appear as if defined in the current module. This is
    /// more invasive than `open` and should be used sparingly.
    ///
    /// However, `include` is the standard F* mechanism for building aggregate
    /// modules. For example:
    /// - `FStar.Seq` includes `FStar.Seq.Base` + `FStar.Seq.Properties`
    /// - `FStar.List.Tot` includes `FStar.List.Tot.Base` + `FStar.List.Tot.Properties`
    /// - `FStar.Reflection.V2` includes all reflection sub-modules
    /// - `FStar.Prelude` includes `Prims`, `FStar.Pervasives`, etc.
    ///
    /// These aggregation patterns are suppressed to avoid false positives.
    fn check_include_statements(
        &self,
        current_module: &Option<String>,
        file: &Path,
        content: &str,
    ) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        for (line_idx, line) in content.lines().enumerate() {
            let trimmed = line.trim();
            if let Some(caps) = INCLUDE_MODULE_RE.captures(trimmed) {
                let Some(module_match) = caps.get(1) else { continue };
                let module_path = module_match.as_str();
                let line_num = line_idx + 1;

                // Suppress aggregation patterns: when a module includes its
                // own sub-modules or closely related sibling modules.
                // Examples:
                //   FStar.Seq includes FStar.Seq.Base (sub-module)
                //   FStar.List.Tot includes FStar.List.Tot.Base (sub-module)
                //   FStar.Reflection.V1 includes FStar.Reflection.V1.Derived (sub-module)
                //   FStar.Reflection.V1 includes FStar.Stubs.Reflection.Types (cross-subsystem)
                //   FStar.Prelude includes Prims, FStar.Pervasives (bootstrapping)
                //   FStar.All includes FStar.ST (effect composition)
                if is_aggregation_include(current_module, module_path) {
                    continue;
                }

                // Check if included module is in broadness database (bare namespaces)
                if let Some(level) = BROAD_MODULES.get(module_path) {
                    // Only flag Critical (bare namespaces like `include FStar`)
                    if *level == BroadnessLevel::Critical {
                        diagnostics.push(Diagnostic {
                            rule: RuleCode::FST008,
                            severity: level.severity(),
                            file: file.to_path_buf(),
                            range: Range::point(line_num, 1),
                            message: format!(
                                "[FST008-I] Broad include: `include {}` is a {} and brings all its \
                                 definitions into the current module's namespace. Use `open` instead, \
                                 or include a more specific submodule.",
                                module_path,
                                level.label()
                            ),
                            fix: None,
                        });
                    }
                    // High/Medium umbrella includes are normal aggregation
                } else if HEAVY_MODULES.contains(module_path) {
                    // Heavy include in non-aggregation context
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST008,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[FST008-I] Heavy include: `include {}` brings a heavyweight module's \
                             entire namespace into scope. Consider using `open` with selective imports \
                             or qualified access instead.",
                            module_path
                        ),
                        fix: None,
                    });
                } else {
                    // General include warning - include is more invasive than open
                    diagnostics.push(Diagnostic {
                        rule: RuleCode::FST008,
                        severity: DiagnosticSeverity::Hint,
                        file: file.to_path_buf(),
                        range: Range::point(line_num, 1),
                        message: format!(
                            "[FST008-I] Include statement: `include {}` makes all definitions from \
                             `{}` appear as local definitions. Prefer `open` unless the module is \
                             designed to be included (e.g., Spec.Hash.Definitions).",
                            module_path, module_path
                        ),
                        fix: None,
                    });
                }
            }
        }

        diagnostics
    }

    /// Check for unnecessary transitive imports.
    fn check_transitive_import(
        &self,
        open: &OpenStatement,
        analysis: &ImportAnalysis,
        file: &Path,
    ) -> Option<Diagnostic> {
        // Check if this module re-exports something else that's also imported
        if let Some(reexports) = TRANSITIVE_EXPORTS.get(open.module_path.as_str()) {
            for reexported in reexports {
                // Check if the re-exported module is also directly imported
                if analysis.opens.iter().any(|o| o.module_path == *reexported) {
                    return Some(Diagnostic {
                        rule: RuleCode::FST008,
                        severity: DiagnosticSeverity::Info,
                        file: file.to_path_buf(),
                        range: Range::new(
                            open.line,
                            open.col,
                            open.line,
                            open.col + open.line_text.trim().len(),
                        ),
                        message: format!(
                            "[FST008-E] Potentially redundant import: `{}` re-exports `{}`, \
                             which is also directly imported.",
                            open.module_path, reexported
                        ),
                        fix: None,
                    });
                }
            }
        }

        None
    }

}

impl Default for ImportOptimizerRule {
    fn default() -> Self {
        Self::new()
    }
}

impl Rule for ImportOptimizerRule {
    fn code(&self) -> RuleCode {
        RuleCode::FST008
    }

    fn check(&self, file: &Path, content: &str) -> Vec<Diagnostic> {
        let analysis = analyze_imports(content);
        let mut diagnostics = Vec::new();

        for open in &analysis.opens {
            // Get usage info for this module
            let usage = analysis
                .module_usage
                .get(&open.module_path)
                .cloned()
                .unwrap_or_default();

            // Check for overly broad namespace opens (FST008-G)
            if let Some(diag) = self.check_broad_namespace(open, &analysis.current_module, file) {
                diagnostics.push(diag);
                // Skip other checks for this open -- it's fundamentally wrong
                continue;
            }

            // Check for heavy module imports (always check first)
            if let Some(diag) = self.check_heavy_modules(open, &analysis.current_module, file) {
                diagnostics.push(diag);
            }

            // Check for circular imports (with differentiated severity)
            if let Some(diag) = self.check_circular_import(open, &analysis.current_module, file) {
                diagnostics.push(diag);
            }

            // Check for transitive imports
            if let Some(diag) = self.check_transitive_import(open, &analysis, file) {
                diagnostics.push(diag);
            }

            // Check for broad imports (only if not already flagged as heavy)
            if !HEAVY_MODULES.contains(open.module_path.as_str()) {
                if let Some(diag) = self.check_broad_import(open, &usage, file) {
                    diagnostics.push(diag);
                }
            }

            // Check for prefer qualified access
            if let Some(diag) = self.check_prefer_qualified(open, &usage, file) {
                diagnostics.push(diag);
            }
        }

        // Check include statements (FST008-I)
        diagnostics.extend(self.check_include_statements(&analysis.current_module, file, content));

        diagnostics
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_heavy_module_detection() {
        // Use FStar.Reflection which is in HEAVY_MODULES but not BROAD_MODULES
        let content = r#"module Test

open FStar.Reflection

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let heavy = diagnostics.iter().find(|d| d.message.contains("FST008-H"));
        assert!(
            heavy.is_some(),
            "Heavy module should trigger FST008-H: {:?}",
            diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(heavy.unwrap().message.contains("Heavy import"));
    }

    #[test]
    fn test_broad_import_detection() {
        let content = r#"module Test

open FStar.List.Tot

let x = length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        // Should detect that only "length" is used from FStar.List.Tot
        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-A"));
        assert!(broad.is_some(), "Should detect broad import");
    }

    #[test]
    fn test_circular_import_detection() {
        let content = r#"module Test.Sub

open Test.Sub

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("Test/Sub.fst"), content);

        let circular = diagnostics.iter().find(|d| d.message.contains("FST008-D"));
        assert!(circular.is_some(), "Should detect circular import");
    }

    #[test]
    fn test_selective_import_no_warning() {
        let content = r#"module Test

open FStar.List.Tot { length }

let x = length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        // Selective import should not trigger FST008-A
        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-A"));
        assert!(
            broad.is_none(),
            "Selective import should not trigger broad import warning"
        );
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

    #[test]
    fn test_extract_current_module() {
        let content = r#"module MyProject.Utils.Helper

open FStar.All

let helper x = x + 1
"#;
        let module_name = extract_current_module(content);
        assert_eq!(module_name, Some("MyProject.Utils.Helper".to_string()));
    }

    #[test]
    fn test_parent_child_circular_suppressed() {
        // Child importing parent is a completely normal F* pattern:
        // FStar.Seq.Permutation opens FStar.Seq, FStar.HyperStack.ST opens
        // FStar.HyperStack, etc. F* resolves dependencies via .fsti files,
        // so there is no circular dependency risk. Suppressed to avoid 17+
        // false positives on ulib.
        let content = r#"module Test.Sub.Child

open Test.Sub

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let circular = diagnostics.iter().find(|d| d.message.contains("FST008-D"));
        assert!(
            circular.is_none(),
            "Child importing parent should NOT trigger FST008-D (normal F* pattern)"
        );
    }

    #[test]
    fn test_self_import_detection() {
        let content = r#"module MyModule

open MyModule

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let circular = diagnostics.iter().find(|d| d.message.contains("FST008-D"));
        assert!(circular.is_some(), "Should detect self-import");
        assert!(
            circular.unwrap().message.contains("Self-import"),
            "Should identify as self-import"
        );
        // Self-import should be an error
        assert_eq!(
            circular.unwrap().severity,
            DiagnosticSeverity::Error,
            "Self-import should be Error severity"
        );
    }

    #[test]
    fn test_parent_imports_child_suppressed() {
        // Parent module opening child is a normal F* pattern and should NOT
        // produce a diagnostic. Parent modules routinely open child sub-modules
        // to compose functionality.
        let content = r#"module Parent

open Parent.Child

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let circular = diagnostics.iter().find(|d| d.message.contains("FST008-D"));
        assert!(
            circular.is_none(),
            "Parent importing child should NOT trigger FST008-D (normal F* pattern)"
        );
    }

    #[test]
    fn test_deep_parent_import_suppressed() {
        // Deep child importing parent is also a normal F* pattern and should
        // not trigger FST008-D.
        let content = r#"module A.B.C.D

open A.B

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let circular = diagnostics.iter().find(|d| d.message.contains("FST008-D"));
        assert!(
            circular.is_none(),
            "Deep child importing parent should NOT trigger FST008-D (normal F* pattern)"
        );
    }

    #[test]
    fn test_no_fst008f_import_order() {
        // FST008-F was removed: import ordering (Core > Pure > Effect > Project)
        // produces false positives because:
        // 1. FStar.Ghost was wrongly categorized as "Effect" (it's pure erasure types)
        // 2. Many FStar.* modules (Calc, Squash, Tactics, etc.) fell through to "Project"
        // 3. No F* community convention for this ordering exists
        // 4. Real F* codebases (hacl-star, everparse) don't follow this ordering
        let content = r#"module Test

open MyProject.Utils
open FStar.Pervasives
open FStar.ST
open FStar.List.Tot
open FStar.Ghost
open FStar.Calc
open Hacl.Impl.SHA256

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let order_issues: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("FST008-F"))
            .collect();
        assert!(
            order_issues.is_empty(),
            "FST008-F import ordering should not be emitted"
        );
    }

    #[test]
    fn test_circular_import_type_messages() {
        let self_msg = CircularImportType::SelfImport.message("A", "A");
        assert!(self_msg.contains("Self-import"));
        assert!(self_msg.contains("opens itself"));

        let parent_msg = CircularImportType::ChildImportsParent.message("A.B", "A");
        assert!(parent_msg.contains("Parent import"));
        assert!(parent_msg.contains("may cause circular"));

        let child_msg = CircularImportType::ParentImportsChild.message("A", "A.B");
        assert!(child_msg.contains("Child import"));
        assert!(child_msg.contains("unusual pattern"));
    }

    #[test]
    fn test_analyze_circular_import() {
        // Self-import
        assert_eq!(
            analyze_circular_import(&Some("Test".to_string()), "Test"),
            CircularImportType::SelfImport
        );

        // Child imports parent
        assert_eq!(
            analyze_circular_import(&Some("A.B.C".to_string()), "A.B"),
            CircularImportType::ChildImportsParent
        );
        assert_eq!(
            analyze_circular_import(&Some("A.B".to_string()), "A"),
            CircularImportType::ChildImportsParent
        );

        // Parent imports child
        assert_eq!(
            analyze_circular_import(&Some("A".to_string()), "A.B"),
            CircularImportType::ParentImportsChild
        );
        assert_eq!(
            analyze_circular_import(&Some("A.B".to_string()), "A.B.C"),
            CircularImportType::ParentImportsChild
        );

        // No circular
        assert_eq!(
            analyze_circular_import(&Some("A".to_string()), "B"),
            CircularImportType::None
        );
        assert_eq!(
            analyze_circular_import(&Some("A.B".to_string()), "C.D"),
            CircularImportType::None
        );
        assert_eq!(
            analyze_circular_import(&None, "A"),
            CircularImportType::None
        );
    }

    #[test]
    fn test_no_false_positive_similar_names() {
        // "AModule" should not be considered parent of "AModuleExtended"
        assert_eq!(
            analyze_circular_import(&Some("AModuleExtended".to_string()), "AModule"),
            CircularImportType::None
        );

        // "Test" should not match "Testing" as parent
        assert_eq!(
            analyze_circular_import(&Some("Testing.Sub".to_string()), "Test"),
            CircularImportType::None
        );
    }

    // ========================================================================
    // FALSE POSITIVE PREVENTION TESTS
    // ========================================================================

    #[test]
    fn test_whitelisted_module_no_broad_import_warning() {
        // FStar.Mul is whitelisted - opening it should never trigger FST008-A
        // even though the linter cannot detect op_Star usage (written as `*`)
        let content = r#"module Test

open FStar.Mul

let x = 2 * 3
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-A"));
        assert!(
            broad.is_none(),
            "Whitelisted module FStar.Mul should not trigger FST008-A"
        );
    }

    #[test]
    fn test_whitelisted_module_no_prefer_qualified_warning() {
        // Lib.IntTypes is whitelisted - should not trigger FST008-C even if
        // qualified access like Lib.IntTypes.Intrinsics.foo exists
        let content = r#"module Test

open Lib.IntTypes

let x = Lib.IntTypes.Intrinsics.add_carry 0uy 1ul 2ul out
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let prefer_qual = diagnostics.iter().find(|d| d.message.contains("FST008-C"));
        assert!(
            prefer_qual.is_none(),
            "Whitelisted module Lib.IntTypes should not trigger FST008-C"
        );
    }

    #[test]
    fn test_no_fst008c_for_unknown_modules() {
        // Modules not in KNOWN_EXPORTS should not trigger FST008-C because
        // we cannot reliably determine what names they bring into scope.
        // This was the #1 source of false positives.
        let content = r#"module Test

open Hacl.Bignum.Definitions

let x = Hacl.Bignum.Definitions.bn_v h b
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let prefer_qual = diagnostics.iter().find(|d| d.message.contains("FST008-C"));
        assert!(
            prefer_qual.is_none(),
            "Unknown module should not trigger FST008-C"
        );
    }

    #[test]
    fn test_no_false_qualified_use_from_open_lines() {
        // When a file has `open FStar.HyperStack` and `open FStar.HyperStack.ST`,
        // the second open line should NOT cause FStar.HyperStack to appear as a
        // "qualified use". This was the main source of false FST008-C warnings.
        let content = r#"module Test

open FStar.HyperStack
open FStar.HyperStack.ST

let f (h: mem) = h
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let prefer_qual = diagnostics.iter().find(|d| d.message.contains("FST008-C"));
        assert!(
            prefer_qual.is_none(),
            "open FStar.HyperStack.ST should not make FStar.HyperStack appear as qualified use"
        );
    }

    #[test]
    fn test_extract_qualified_modules_filters_declarations() {
        // Verify that extract_qualified_modules does not pick up module
        // paths from open/module/friend/include declaration lines
        let content = r#"module Test

open FStar.HyperStack
open FStar.HyperStack.ST
module S = Hacl.Spec.Bignum

let x = S.bn_v h b
"#;
        let modules = extract_qualified_modules(content);

        // S should be found (used in code)
        assert!(
            modules.contains("S"),
            "Should find S as qualified module from `S.bn_v`"
        );

        // FStar.HyperStack should NOT be found (only appears in open lines)
        assert!(
            !modules.contains("FStar.HyperStack"),
            "Should not extract FStar.HyperStack from `open FStar.HyperStack.ST` line"
        );

        // Hacl.Spec should NOT be found (only appears in module alias line)
        assert!(
            !modules.contains("Hacl.Spec"),
            "Should not extract Hacl.Spec from module alias declaration"
        );
    }

    #[test]
    fn test_hacl_star_typical_file_no_false_positives() {
        // Simulate a typical HACL* file header - should produce zero warnings
        // from FST008-A, FST008-C
        let content = r#"module Hacl.Bignum.Base

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Hacl.Bignum.Definitions

module LSeq = Lib.Sequence

let addcarry_st c_in a b out =
  Lib.IntTypes.Intrinsics.add_carry c_in a b out

let x = LSeq.index (as_seq h out) 0
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("Hacl/Bignum/Base.fst"), content);

        let a_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("FST008-A"))
            .collect();
        let c_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.message.contains("FST008-C"))
            .collect();

        assert!(
            a_warnings.is_empty(),
            "Typical HACL* file should not trigger FST008-A, got: {:?}",
            a_warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(
            c_warnings.is_empty(),
            "Typical HACL* file should not trigger FST008-C, got: {:?}",
            c_warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fst008c_still_fires_for_known_exports_modules() {
        // FST008-C should still fire for modules in KNOWN_EXPORTS that are
        // NOT whitelisted, when they are only used qualified.
        let content = r#"module Test

open FStar.List.Tot

let x = FStar.List.Tot.length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let prefer_qual = diagnostics.iter().find(|d| d.message.contains("FST008-C"));
        assert!(
            prefer_qual.is_some(),
            "FST008-C should still fire for KNOWN_EXPORTS module used only qualified"
        );
    }

    #[test]
    fn test_whitelisted_modules_comprehensive() {
        // Verify all critical whitelisted modules are covered
        let critical_modules = vec![
            "Prims",
            "FStar.Mul",
            "FStar.HyperStack",
            "FStar.HyperStack.ST",
            "Lib.IntTypes",
            "Lib.Buffer",
            "LowStar.Buffer",
            "LowStar.BufferOps",
        ];

        for module in critical_modules {
            assert!(
                WHITELISTED_OPENS.contains(module),
                "Module {} should be in WHITELISTED_OPENS",
                module
            );
        }
    }

    #[test]
    fn test_generate_selective_fix_targets_single_line() {
        // Regression test: selective import fix must replace exactly one line.
        // Previously used open.line + 1 as end_line, which replaced TWO lines.
        let open = OpenStatement {
            module_path: "FStar.List.Tot".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.List.Tot".to_string(),
            is_local: false,
            scope_end: None,
        };
        let mut used = HashSet::new();
        used.insert("length".to_string());
        let file = PathBuf::from("test.fst");

        let fix = generate_selective_fix(&open, &used, &file)
            .expect("Should generate a selective fix");

        assert_eq!(fix.edits.len(), 1, "Should produce exactly one edit");
        let edit = &fix.edits[0];
        assert_eq!(
            edit.range.start_line, edit.range.end_line,
            "Selective fix must target a single line (start_line == end_line), \
             got start_line={} end_line={}",
            edit.range.start_line, edit.range.end_line
        );
        assert_eq!(edit.range.start_line, 3, "Edit should target line 3");
        assert!(
            edit.new_text.contains("open FStar.List.Tot {"),
            "Should produce selective import syntax, got: {}",
            edit.new_text
        );
    }

    #[test]
    fn test_generate_qualified_fix_targets_single_line() {
        // Regression test: qualified access fix must remove exactly one line.
        // Previously used open.line + 1 as end_line, which deleted TWO lines.
        let open = OpenStatement {
            module_path: "FStar.Option".to_string(),
            selective: None,
            line: 7,
            col: 1,
            line_text: "open FStar.Option".to_string(),
            is_local: false,
            scope_end: None,
        };
        let file = PathBuf::from("test.fst");

        let fix = generate_qualified_fix(&open, &file);

        assert_eq!(fix.edits.len(), 1, "Should produce exactly one edit");
        let edit = &fix.edits[0];
        assert_eq!(
            edit.range.start_line, edit.range.end_line,
            "Qualified fix must target a single line (start_line == end_line), \
             got start_line={} end_line={}",
            edit.range.start_line, edit.range.end_line
        );
        assert_eq!(edit.range.start_line, 7, "Edit should target line 7");
        assert!(edit.new_text.is_empty(), "Removal edit should have empty new_text");
    }

    // ========================================================================
    // EDIT APPLICATION INTEGRATION TESTS
    // ========================================================================
    //
    // These tests simulate apply_single_edit's line-replacement semantics to
    // verify that edits produce correct content. The helper mirrors the real
    // applicator: lines[start..=end] (0-indexed) are replaced by new_text.

    /// Simulate apply_single_edit: replace lines [start_line, end_line] (1-indexed)
    /// with new_text. Mirrors fix_applicator.rs logic.
    fn simulate_apply_edit(content: &str, edit: &Edit) -> String {
        let lines: Vec<&str> = content.lines().collect();
        let start = edit.range.start_line.saturating_sub(1);
        let end = edit.range.end_line.saturating_sub(1);
        let mut result = String::new();

        for line in lines.iter().take(start) {
            result.push_str(line);
            result.push('\n');
        }
        if !edit.new_text.is_empty() {
            result.push_str(&edit.new_text);
            if !edit.new_text.ends_with('\n') {
                result.push('\n');
            }
        }
        for line in lines.iter().skip(end + 1) {
            result.push_str(line);
            result.push('\n');
        }
        result
    }

    #[test]
    fn test_selective_fix_applied_to_content() {
        // Verify that applying the selective fix edit to actual content
        // replaces ONLY the target line and preserves surrounding lines.
        let content = "module Test\n\
                       \n\
                       open FStar.List.Tot\n\
                       \n\
                       let x = length [1; 2; 3]\n";
        let open = OpenStatement {
            module_path: "FStar.List.Tot".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.List.Tot".to_string(),
            is_local: false,
            scope_end: None,
        };
        let mut used = HashSet::new();
        used.insert("length".to_string());
        let file = PathBuf::from("test.fst");

        let fix = generate_selective_fix(&open, &used, &file).unwrap();
        let result = simulate_apply_edit(content, &fix.edits[0]);
        let result_lines: Vec<&str> = result.lines().collect();

        assert_eq!(result_lines[0], "module Test", "Line 1 must be preserved");
        assert_eq!(result_lines[1], "", "Line 2 (blank) must be preserved");
        assert!(
            result_lines[2].starts_with("open FStar.List.Tot {"),
            "Line 3 must be the selective import, got: '{}'",
            result_lines[2]
        );
        assert!(
            result_lines[2].contains("length"),
            "Selective import must contain 'length', got: '{}'",
            result_lines[2]
        );
        assert_eq!(result_lines[3], "", "Line 4 (blank) must be preserved");
        assert_eq!(
            result_lines[4], "let x = length [1; 2; 3]",
            "Line 5 must be preserved"
        );
        assert_eq!(
            result_lines.len(),
            5,
            "Result must have exactly 5 lines (same as input)"
        );
    }

    #[test]
    fn test_removal_fix_preserves_adjacent_lines() {
        // Verify that the removal fix deletes ONLY the target line.
        // This is the core regression: with line+1 as end_line, the NEXT
        // line after the open would also be deleted.
        let content = "module Test\n\
                       \n\
                       open FStar.Option\n\
                       open FStar.List.Tot\n\
                       \n\
                       let x = 1\n";
        let open = OpenStatement {
            module_path: "FStar.Option".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.Option".to_string(),
            is_local: false,
            scope_end: None,
        };
        let file = PathBuf::from("test.fst");

        let fix = generate_qualified_fix(&open, &file);
        let result = simulate_apply_edit(content, &fix.edits[0]);
        let result_lines: Vec<&str> = result.lines().collect();

        assert_eq!(result_lines[0], "module Test", "Line 1 preserved");
        assert_eq!(result_lines[1], "", "Line 2 (blank) preserved");
        assert_eq!(
            result_lines[2], "open FStar.List.Tot",
            "Line 4 (was after removed line) must survive -- \
             the old line+1 bug would delete this line too"
        );
        assert_eq!(result_lines[3], "", "Line 5 preserved");
        assert_eq!(result_lines[4], "let x = 1", "Line 6 preserved");
        assert_eq!(
            result_lines.len(),
            5,
            "Result must have 5 lines (original 6 minus 1 removed)"
        );
    }

    #[test]
    fn test_selective_fix_multiple_names_all_present() {
        // When multiple names are used, the selective import must list all of them.
        let open = OpenStatement {
            module_path: "FStar.List.Tot".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.List.Tot".to_string(),
            is_local: false,
            scope_end: None,
        };
        let mut used = HashSet::new();
        used.insert("map".to_string());
        used.insert("filter".to_string());
        used.insert("length".to_string());
        let file = PathBuf::from("test.fst");

        let fix = generate_selective_fix(&open, &used, &file).unwrap();
        let edit = &fix.edits[0];

        assert!(
            edit.new_text.contains("map"),
            "Selective import must include 'map'"
        );
        assert!(
            edit.new_text.contains("filter"),
            "Selective import must include 'filter'"
        );
        assert!(
            edit.new_text.contains("length"),
            "Selective import must include 'length'"
        );
        assert!(
            edit.new_text.starts_with("open FStar.List.Tot {"),
            "Must use selective import syntax: 'open M {{ names }}'"
        );
        assert!(
            edit.new_text.trim_end().ends_with('}'),
            "Selective import must close with '}}', got: '{}'",
            edit.new_text.trim_end()
        );
    }

    #[test]
    fn test_selective_fix_new_text_has_exactly_one_trailing_newline() {
        // The replacement text must end with exactly one newline so that
        // apply_single_edit does not insert an extra blank line.
        let open = OpenStatement {
            module_path: "FStar.Seq".to_string(),
            selective: None,
            line: 5,
            col: 1,
            line_text: "open FStar.Seq".to_string(),
            is_local: false,
            scope_end: None,
        };
        let mut used = HashSet::new();
        used.insert("length".to_string());
        let file = PathBuf::from("test.fst");

        let fix = generate_selective_fix(&open, &used, &file).unwrap();
        let text = &fix.edits[0].new_text;

        assert!(
            text.ends_with('\n'),
            "new_text must end with newline for correct line replacement"
        );
        assert!(
            !text.ends_with("\n\n"),
            "new_text must not end with double newline (would insert blank line)"
        );
    }

    #[test]
    fn test_selective_fix_empty_names_returns_none() {
        let open = OpenStatement {
            module_path: "FStar.List.Tot".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.List.Tot".to_string(),
            is_local: false,
            scope_end: None,
        };
        let used = HashSet::new();
        let file = PathBuf::from("test.fst");

        let result = generate_selective_fix(&open, &used, &file);
        assert!(
            result.is_none(),
            "Empty used names must return None (no fix to suggest)"
        );
    }

    #[test]
    fn test_removal_fix_on_last_line_does_not_panic() {
        // If the open statement is on the very last line, the removal
        // must not panic or produce garbage.
        let content = "module Test\n\
                       open FStar.Option";
        let open = OpenStatement {
            module_path: "FStar.Option".to_string(),
            selective: None,
            line: 2,
            col: 1,
            line_text: "open FStar.Option".to_string(),
            is_local: false,
            scope_end: None,
        };
        let file = PathBuf::from("test.fst");

        let fix = generate_qualified_fix(&open, &file);
        let result = simulate_apply_edit(content, &fix.edits[0]);
        let result_lines: Vec<&str> = result.lines().collect();

        assert_eq!(result_lines.len(), 1, "Only module declaration should remain");
        assert_eq!(result_lines[0], "module Test");
    }

    #[test]
    fn test_diagnostic_range_spans_open_statement_text() {
        // Diagnostic ranges should span from the column of 'open' to the end
        // of the trimmed line text, providing accurate highlighting.
        let content = r#"module Test

open FStar.List.Tot

let x = length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        // FST008-A should fire for FStar.List.Tot with only 'length' used
        if let Some(diag) = diagnostics.iter().find(|d| d.message.contains("FST008-A")) {
            assert_eq!(
                diag.range.start_line, diag.range.end_line,
                "Diagnostic must be single-line"
            );
            assert!(
                diag.range.end_col > diag.range.start_col,
                "Diagnostic range must have non-zero width, \
                 got start_col={} end_col={}",
                diag.range.start_col,
                diag.range.end_col
            );
            // "open FStar.List.Tot" is 19 chars; range width should match
            let width = diag.range.end_col - diag.range.start_col;
            assert_eq!(
                width,
                "open FStar.List.Tot".len(),
                "Diagnostic range width must match the open statement text length"
            );
        }
    }

    #[test]
    fn test_selective_fix_description_mentions_name_count() {
        let open = OpenStatement {
            module_path: "FStar.List.Tot".to_string(),
            selective: None,
            line: 3,
            col: 1,
            line_text: "open FStar.List.Tot".to_string(),
            is_local: false,
            scope_end: None,
        };

        // Single name
        let mut one = HashSet::new();
        one.insert("map".to_string());
        let fix1 = generate_selective_fix(&open, &one, &PathBuf::from("t.fst")).unwrap();
        assert!(
            fix1.message.contains("1 name"),
            "Fix message should say '1 name' (singular), got: '{}'",
            fix1.message
        );

        // Multiple names
        let mut two = HashSet::new();
        two.insert("map".to_string());
        two.insert("filter".to_string());
        let fix2 = generate_selective_fix(&open, &two, &PathBuf::from("t.fst")).unwrap();
        assert!(
            fix2.message.contains("2 names"),
            "Fix message should say '2 names' (plural), got: '{}'",
            fix2.message
        );
    }

    // ========================================================================
    // FST008-G: Broad namespace detection tests
    // ========================================================================

    #[test]
    fn test_open_fstar_namespace_error() {
        // `open FStar` is a namespace, not a module -- should be Critical/Error
        let content = r#"module Test

open FStar

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(
            broad.is_some(),
            "open FStar should trigger FST008-G: {:?}",
            diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert_eq!(
            broad.unwrap().severity,
            DiagnosticSeverity::Error,
            "Top-level namespace open should be Error severity"
        );
        assert!(
            broad.unwrap().message.contains("namespace"),
            "Message should mention 'namespace'"
        );
    }

    #[test]
    fn test_open_lowstar_namespace_error() {
        let content = r#"module Test

open LowStar

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(broad.is_some(), "open LowStar should trigger FST008-G");
    }

    #[test]
    fn test_open_fstar_submodule_no_g_warning() {
        // `open FStar.List.Tot` is a specific module -- should NOT trigger FST008-G
        let content = r#"module Test

open FStar.List.Tot

let x = length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(
            broad.is_none(),
            "Specific submodule should NOT trigger FST008-G"
        );
    }

    #[test]
    fn test_open_fstar_all_suppressed() {
        // FStar.All is a standard F* effect combinator module used pervasively
        // in FStar.List, FStar.Option, FStar.IO, etc. It is always suppressed
        // because it provides the `All` effect which many modules need.
        let content = r#"module Test

open FStar.All

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(
            broad.is_none(),
            "FStar.All should be suppressed (standard effect combinator)"
        );
    }

    #[test]
    fn test_open_umbrella_from_outside_is_info() {
        // Opening an umbrella module like FStar.Tactics.V2 from outside the
        // Tactics namespace should produce Info (not Warning), since it's
        // a style preference, not a correctness issue.
        let content = r#"module MyProject.Utils

open FStar.Tactics.V2

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(broad.is_some(), "Umbrella module should trigger FST008-G from outside namespace");
        assert_eq!(
            broad.unwrap().severity,
            DiagnosticSeverity::Info,
            "Umbrella module should be Info severity (style preference, not correctness)"
        );
    }

    #[test]
    fn test_broadness_skips_other_checks() {
        // When FST008-G fires, other checks should be skipped for that open
        let content = r#"module Test

open FStar

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        // Should have FST008-G but NOT FST008-A, FST008-C, or FST008-H
        assert!(diagnostics.iter().any(|d| d.message.contains("FST008-G")));
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("FST008-A")),
            "FST008-A should be skipped when FST008-G fires"
        );
        assert!(
            !diagnostics.iter().any(|d| d.message.contains("FST008-C")),
            "FST008-C should be skipped when FST008-G fires"
        );
    }

    // ========================================================================
    // FST008-I: Include statement tests
    // ========================================================================

    #[test]
    fn test_include_statement_hint() {
        // General include statements are demoted to Hint since include is
        // a common and valid F* pattern for module aggregation.
        let content = r#"module Test

include Spec.Hash.Definitions

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let include_diag = diagnostics.iter().find(|d| d.message.contains("FST008-I"));
        assert!(
            include_diag.is_some(),
            "include statement should trigger FST008-I"
        );
        assert_eq!(
            include_diag.unwrap().severity,
            DiagnosticSeverity::Hint,
            "Normal include should be Hint severity"
        );
    }

    #[test]
    fn test_include_broad_namespace_error() {
        let content = r#"module Test

include FStar

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let include_diag = diagnostics.iter().find(|d| d.message.contains("FST008-I") && d.message.contains("Broad"));
        assert!(
            include_diag.is_some(),
            "include of namespace should trigger broad FST008-I"
        );
        assert_eq!(
            include_diag.unwrap().severity,
            DiagnosticSeverity::Error,
            "Including a namespace should be Error"
        );
    }

    #[test]
    fn test_include_heavy_module_warning() {
        let content = r#"module Test

include FStar.Tactics.V2

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let include_diag = diagnostics.iter().find(|d| d.message.contains("FST008-I"));
        assert!(
            include_diag.is_some(),
            "include of heavy module should trigger FST008-I"
        );
    }

    #[test]
    fn test_no_include_when_none_present() {
        let content = r#"module Test

open FStar.List.Tot

let x = length [1; 2; 3]
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("test.fst"), content);

        let include_diag = diagnostics.iter().find(|d| d.message.contains("FST008-I"));
        assert!(
            include_diag.is_none(),
            "No include statements means no FST008-I"
        );
    }

    // ========================================================================
    // Broadness level tests
    // ========================================================================

    #[test]
    fn test_broadness_level_properties() {
        assert_eq!(BroadnessLevel::Critical.severity(), DiagnosticSeverity::Error);
        assert_eq!(BroadnessLevel::High.severity(), DiagnosticSeverity::Info);
        assert_eq!(BroadnessLevel::Medium.severity(), DiagnosticSeverity::Hint);

        assert!(BroadnessLevel::Critical.label().contains("namespace"));
        assert!(BroadnessLevel::High.label().contains("umbrella"));
        assert!(BroadnessLevel::Medium.label().contains("large"));
    }

    #[test]
    fn test_broad_modules_database() {
        // Critical entries
        assert_eq!(BROAD_MODULES.get("FStar"), Some(&BroadnessLevel::Critical));
        assert_eq!(BROAD_MODULES.get("LowStar"), Some(&BroadnessLevel::Critical));
        assert_eq!(BROAD_MODULES.get("Lib"), Some(&BroadnessLevel::Critical));
        assert_eq!(BROAD_MODULES.get("Hacl"), Some(&BroadnessLevel::Critical));

        // High entries
        assert_eq!(BROAD_MODULES.get("FStar.All"), Some(&BroadnessLevel::High));

        // Specific submodules should NOT be in the database
        assert!(BROAD_MODULES.get("FStar.List.Tot").is_none());
        assert!(BROAD_MODULES.get("FStar.Seq").is_none());
    }

    #[test]
    fn test_prims_not_flagged_as_broad_namespace() {
        // Prims is a real F* module (not a namespace). Core ulib files like
        // FStar.Attributes.fsti and FStar.NormSteps.fst use [@@"no_prelude"]
        // which disables the implicit `open Prims`, so they explicitly `open Prims`.
        // This must NOT produce any FST008-G error.
        let content = r#"[@@"no_prelude"]
module FStar.Attributes

open Prims

let x : bool = true
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("FStar.Attributes.fsti"), content);

        let broad = diagnostics.iter().find(|d| d.message.contains("FST008-G"));
        assert!(
            broad.is_none(),
            "Prims is a real module, not a namespace -- should NOT trigger FST008-G. \
             Got: {:?}",
            diagnostics.iter().map(|d| &d.message).collect::<Vec<_>>()
        );

        // Also ensure Prims is NOT in BROAD_MODULES
        assert!(
            BROAD_MODULES.get("Prims").is_none(),
            "Prims must NOT be in BROAD_MODULES -- it is a real F* module"
        );

        // And ensure Prims IS in WHITELISTED_OPENS
        assert!(
            WHITELISTED_OPENS.contains("Prims"),
            "Prims must be in WHITELISTED_OPENS"
        );
    }

    #[test]
    fn test_include_prims_not_flagged_as_broad() {
        // FStar.Prelude.fsti uses `include Prims`. This should produce only
        // a normal FST008-I info, NOT a broad/error FST008-I.
        let content = r#"[@@"no_prelude"]
module FStar.Prelude

include Prims
include FStar.Pervasives.Native
include FStar.Pervasives

let x = 1
"#;
        let rule = ImportOptimizerRule::new();
        let diagnostics = rule.check(&PathBuf::from("FStar.Prelude.fsti"), content);

        let broad_include = diagnostics
            .iter()
            .find(|d| d.message.contains("FST008-I") && d.message.contains("Prims") && d.severity == DiagnosticSeverity::Error);
        assert!(
            broad_include.is_none(),
            "include Prims should NOT be Error severity. \
             Prims is a real module. Got: {:?}",
            diagnostics.iter().filter(|d| d.message.contains("Prims")).map(|d| format!("{}: {}", d.severity, d.message)).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_qualified_fix_description_includes_module_path() {
        let open = OpenStatement {
            module_path: "FStar.Seq".to_string(),
            selective: None,
            line: 4,
            col: 1,
            line_text: "open FStar.Seq".to_string(),
            is_local: false,
            scope_end: None,
        };
        let fix = generate_qualified_fix(&open, &PathBuf::from("t.fst"));
        assert!(
            fix.message.contains("FStar.Seq"),
            "Fix description must mention the module path, got: '{}'",
            fix.message
        );
    }
}
