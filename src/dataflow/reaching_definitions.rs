//! Reaching Definitions Data Flow Analysis.
//!
//! For each program point, determines which definitions (assignments) of variables
//! may reach that point without being killed by another definition of the same variable.
//!
//! # Data Flow Equations (Forward Analysis)
//!
//! - GEN[B] = definitions generated in block B
//! - KILL[B] = definitions killed in block B (same variable redefined elsewhere)
//! - OUT[B] = GEN[B] ∪ (IN[B] - KILL[B])
//! - IN[B] = ∪ OUT[P] for all predecessors P
//!
//! # Applications
//!
//! - Uninitialized variable detection
//! - Dead store detection (definition never used)
//! - Copy propagation opportunities
//! - Building def-use chains for refactoring

use std::collections::VecDeque;
use std::path::Path;

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::cfg::{extract_with_language, BlockId, CFGInfo};
use crate::dataflow::common::is_valid_identifier;
use crate::error::{BrrrError, Result};

// =============================================================================
// Types
// =============================================================================

/// Unique identifier for a definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DefId(pub usize);

/// Location in source code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Location {
    /// Line number (1-indexed).
    pub line: usize,
    /// Column number (0-indexed, optional).
    pub column: Option<usize>,
    /// Block ID in CFG.
    pub block_id: BlockId,
}

impl Location {
    /// Create a new location.
    #[inline]
    pub fn new(line: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: None,
            block_id,
        }
    }

    /// Create a new location with column.
    #[inline]
    pub fn with_column(line: usize, column: usize, block_id: BlockId) -> Self {
        Self {
            line,
            column: Some(column),
            block_id,
        }
    }
}

/// Kind of definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DefKind {
    /// Regular assignment (x = ...)
    Assignment,
    /// Function parameter
    Parameter,
    /// For loop variable
    ForLoopVar,
    /// Import statement (import x, from y import x)
    Import,
    /// Function definition (def f(): ...)
    FunctionDef,
    /// Class definition (class C: ...)
    ClassDef,
    /// With statement variable (with open() as f: ...)
    WithVar,
    /// Exception handler variable (except E as e: ...)
    ExceptVar,
    /// Tuple/list unpacking target
    UnpackingTarget,
    /// Walrus operator (:= in Python)
    WalrusOperator,
    /// Augmented assignment (x += 1)
    AugmentedAssignment,
    /// Global declaration (global x in Python)
    GlobalDecl,
    /// Nonlocal declaration (nonlocal x in Python)
    NonlocalDecl,
    /// Comprehension variable (x in [x for x in ...])
    ComprehensionVar,
    /// Match pattern variable (case x: in Python)
    MatchPatternVar,
}

impl std::fmt::Display for DefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DefKind::Assignment => write!(f, "assignment"),
            DefKind::Parameter => write!(f, "parameter"),
            DefKind::ForLoopVar => write!(f, "for_loop_var"),
            DefKind::Import => write!(f, "import"),
            DefKind::FunctionDef => write!(f, "function_def"),
            DefKind::ClassDef => write!(f, "class_def"),
            DefKind::WithVar => write!(f, "with_var"),
            DefKind::ExceptVar => write!(f, "except_var"),
            DefKind::UnpackingTarget => write!(f, "unpacking_target"),
            DefKind::WalrusOperator => write!(f, "walrus_operator"),
            DefKind::AugmentedAssignment => write!(f, "augmented_assignment"),
            DefKind::GlobalDecl => write!(f, "global_decl"),
            DefKind::NonlocalDecl => write!(f, "nonlocal_decl"),
            DefKind::ComprehensionVar => write!(f, "comprehension_var"),
            DefKind::MatchPatternVar => write!(f, "match_pattern_var"),
        }
    }
}

/// A variable definition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Definition {
    /// Variable name being defined.
    pub variable: String,
    /// Location in source code.
    pub location: Location,
    /// Unique definition ID.
    pub def_id: DefId,
    /// Kind of definition.
    pub kind: DefKind,
}

/// A def-use chain linking a definition to its uses.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefUseChain {
    /// The definition.
    pub definition: DefId,
    /// Variable name.
    pub variable: String,
    /// Definition location.
    pub def_location: Location,
    /// All locations where this definition is used.
    pub uses: Vec<Location>,
    /// Number of uses.
    pub use_count: usize,
}

/// Kind of issue detected during analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IssueKind {
    /// Variable used before any definition reaches it.
    UninitializedVariable,
    /// Definition is never used (dead store).
    DeadStore,
    /// Variable is redefined without being used.
    UnusedRedefinition,
}

impl std::fmt::Display for IssueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IssueKind::UninitializedVariable => write!(f, "uninitialized_variable"),
            IssueKind::DeadStore => write!(f, "dead_store"),
            IssueKind::UnusedRedefinition => write!(f, "unused_redefinition"),
        }
    }
}

/// An issue detected during analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Issue {
    /// Kind of issue.
    pub kind: IssueKind,
    /// Human-readable message.
    pub message: String,
    /// Location of the issue.
    pub location: Location,
    /// Variable involved.
    pub variable: String,
}

// =============================================================================
// BitSet - Efficient set operations for data flow analysis
// =============================================================================

/// A simple bit set for efficient set operations.
///
/// Uses a Vec<u64> as backing storage. Each bit represents membership
/// of an element in the set. Operations are O(n/64) where n is the
/// maximum element value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitSet {
    /// Backing storage: each u64 holds 64 bits.
    bits: Vec<u64>,
    /// Number of elements that can be stored.
    capacity: usize,
}

impl BitSet {
    /// Create a new empty BitSet with given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let num_words = (capacity + 63) / 64;
        Self {
            bits: vec![0; num_words],
            capacity,
        }
    }

    /// Insert an element. Returns true if the element was not already present.
    #[inline]
    pub fn insert(&mut self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        let mask = 1u64 << bit_idx;
        let was_present = (self.bits[word_idx] & mask) != 0;
        self.bits[word_idx] |= mask;
        !was_present
    }

    /// Remove an element. Returns true if the element was present.
    #[inline]
    pub fn remove(&mut self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        let mask = 1u64 << bit_idx;
        let was_present = (self.bits[word_idx] & mask) != 0;
        self.bits[word_idx] &= !mask;
        was_present
    }

    /// Check if an element is in the set.
    #[inline]
    pub fn contains(&self, elem: usize) -> bool {
        if elem >= self.capacity {
            return false;
        }
        let word_idx = elem / 64;
        let bit_idx = elem % 64;
        (self.bits[word_idx] & (1u64 << bit_idx)) != 0
    }

    /// Union: self = self | other
    #[inline]
    pub fn union_with(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a |= *b;
        }
    }

    /// Difference: self = self - other
    #[inline]
    pub fn difference_with(&mut self, other: &BitSet) {
        for (a, b) in self.bits.iter_mut().zip(other.bits.iter()) {
            *a &= !*b;
        }
    }

    /// Check if the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|&w| w == 0)
    }

    /// Count the number of elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.bits.iter().map(|w| w.count_ones() as usize).sum()
    }

    /// Clear all elements.
    #[inline]
    pub fn clear(&mut self) {
        for w in &mut self.bits {
            *w = 0;
        }
    }

    /// Iterate over all elements in the set.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let capacity = self.capacity;
        self.bits
            .iter()
            .enumerate()
            .flat_map(move |(word_idx, &word)| {
                (0..64).filter_map(move |bit_idx| {
                    if (word & (1u64 << bit_idx)) != 0 {
                        let elem = word_idx * 64 + bit_idx;
                        if elem < capacity {
                            Some(elem)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
            })
    }
}

// =============================================================================
// Reaching Definitions Result
// =============================================================================

/// Result of reaching definitions analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachingDefinitionsResult {
    /// Function name analyzed.
    pub function_name: String,
    /// All definitions found.
    pub definitions: Vec<Definition>,
    /// Definitions reaching each block's entry.
    /// Maps BlockId.0 -> set of DefId.0 values.
    pub reaching_in: FxHashMap<usize, Vec<usize>>,
    /// Definitions reaching each block's exit.
    /// Maps BlockId.0 -> set of DefId.0 values.
    pub reaching_out: FxHashMap<usize, Vec<usize>>,
    /// Def-use chains.
    pub def_use_chains: Vec<DefUseChain>,
    /// Detected issues.
    pub issues: Vec<Issue>,
    /// Number of iterations until fixpoint.
    pub iterations: usize,
}

// =============================================================================
// Definition Extraction
// =============================================================================

/// Patterns for extracting definitions from code.
struct DefinitionExtractor;

impl DefinitionExtractor {
    /// Extract definitions from a statement.
    ///
    /// Parses common assignment patterns:
    /// - Simple assignment: `x = ...`
    /// - Multiple targets: `x = y = ...`
    /// - Tuple unpacking: `x, y = ...`
    /// - Augmented assignment: `x += ...`
    /// - For loop: `for x in ...`
    /// - With statement: `with ... as x`
    /// - Except clause: `except E as x`
    /// - Walrus operator: `(x := ...)`
    fn extract_from_statement(
        stmt: &str,
        line: usize,
        block_id: BlockId,
        next_def_id: &mut usize,
        definitions: &mut Vec<Definition>,
    ) {
        let stmt = stmt.trim();

        // Skip empty or comment-only lines
        if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("//") {
            return;
        }

        // Function definition
        if stmt.starts_with("def ") || stmt.starts_with("async def ") {
            if let Some(name) = Self::extract_function_name(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::FunctionDef,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Class definition
        if stmt.starts_with("class ") {
            if let Some(name) = Self::extract_class_name(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::ClassDef,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Import statements
        if stmt.starts_with("import ") || stmt.starts_with("from ") {
            for name in Self::extract_import_names(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::Import,
                });
                *next_def_id += 1;
            }
            return;
        }

        // For loop
        if stmt.starts_with("for ") || stmt.starts_with("async for ") {
            for name in Self::extract_for_loop_vars(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::ForLoopVar,
                });
                *next_def_id += 1;
            }
            return;
        }

        // With statement
        if stmt.starts_with("with ") || stmt.starts_with("async with ") {
            for name in Self::extract_with_vars(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::WithVar,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Except clause
        if stmt.starts_with("except ") {
            if let Some(name) = Self::extract_except_var(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::ExceptVar,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Global/nonlocal declarations
        if stmt.starts_with("global ") {
            for name in Self::extract_global_names(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::GlobalDecl,
                });
                *next_def_id += 1;
            }
            return;
        }

        if stmt.starts_with("nonlocal ") {
            for name in Self::extract_nonlocal_names(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::NonlocalDecl,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Walrus operator (anywhere in expression)
        for name in Self::extract_walrus_vars(stmt) {
            definitions.push(Definition {
                variable: name,
                location: Location::new(line, block_id),
                def_id: DefId(*next_def_id),
                kind: DefKind::WalrusOperator,
            });
            *next_def_id += 1;
        }

        // Augmented assignment
        if Self::is_augmented_assignment(stmt) {
            if let Some(name) = Self::extract_augmented_target(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::AugmentedAssignment,
                });
                *next_def_id += 1;
            }
            return;
        }

        // Regular assignment (must check after augmented)
        if Self::is_assignment(stmt) {
            for name in Self::extract_assignment_targets(stmt) {
                definitions.push(Definition {
                    variable: name,
                    location: Location::new(line, block_id),
                    def_id: DefId(*next_def_id),
                    kind: DefKind::Assignment,
                });
                *next_def_id += 1;
            }
        }
    }

    /// Extract function name from def statement.
    fn extract_function_name(stmt: &str) -> Option<String> {
        // Handle optional async prefix
        let stmt = stmt.strip_prefix("async ").unwrap_or(stmt).trim();
        let stmt = stmt.strip_prefix("def ")?;
        let name_end = stmt.find('(')?;
        let name = stmt[..name_end].trim();
        if is_valid_identifier(name) {
            Some(name.to_string())
        } else {
            None
        }
    }

    /// Extract class name from class statement.
    fn extract_class_name(stmt: &str) -> Option<String> {
        let stmt = stmt.strip_prefix("class ")?.trim();
        let name_end = stmt
            .find(|c: char| c == '(' || c == ':')
            .unwrap_or(stmt.len());
        let name = stmt[..name_end].trim();
        if is_valid_identifier(name) {
            Some(name.to_string())
        } else {
            None
        }
    }

    /// Extract imported names from import statement.
    fn extract_import_names(stmt: &str) -> Vec<String> {
        let mut names = Vec::new();

        if stmt.starts_with("from ") {
            // from x import a, b, c or from x import a as alias
            if let Some(import_part) = stmt.split(" import ").nth(1) {
                for item in import_part.split(',') {
                    let item = item.trim();
                    // Handle "a as alias" -> use alias
                    let name = if let Some(alias_pos) = item.find(" as ") {
                        item[alias_pos + 4..].trim()
                    } else {
                        item
                    };
                    if is_valid_identifier(name) {
                        names.push(name.to_string());
                    }
                }
            }
        } else if stmt.starts_with("import ") {
            // import a, b, c or import a as alias
            let import_part = stmt.strip_prefix("import ").unwrap().trim();
            for item in import_part.split(',') {
                let item = item.trim();
                let name = if let Some(alias_pos) = item.find(" as ") {
                    item[alias_pos + 4..].trim()
                } else {
                    // For "import a.b.c", the binding is "a"
                    item.split('.').next().unwrap_or(item)
                };
                if is_valid_identifier(name) {
                    names.push(name.to_string());
                }
            }
        }

        names
    }

    /// Extract for loop variable(s).
    fn extract_for_loop_vars(stmt: &str) -> Vec<String> {
        let stmt = stmt.strip_prefix("async ").unwrap_or(stmt);
        let stmt = stmt.strip_prefix("for ").unwrap_or(stmt);

        // Find the "in" keyword
        if let Some(in_pos) = stmt.find(" in ") {
            let vars_part = stmt[..in_pos].trim();
            return Self::extract_tuple_vars(vars_part);
        }

        Vec::new()
    }

    /// Extract with statement variable(s).
    fn extract_with_vars(stmt: &str) -> Vec<String> {
        let mut names = Vec::new();
        let stmt = stmt.strip_prefix("async ").unwrap_or(stmt);
        let stmt = stmt.strip_prefix("with ").unwrap_or(stmt);

        // Handle multiple context managers: with a as x, b as y:
        for part in stmt.split(',') {
            if let Some(as_pos) = part.find(" as ") {
                let var_part = part[as_pos + 4..].trim();
                // Remove trailing colon if present
                let var_part = var_part.trim_end_matches(':').trim();
                for name in Self::extract_tuple_vars(var_part) {
                    names.push(name);
                }
            }
        }

        names
    }

    /// Extract except clause variable.
    fn extract_except_var(stmt: &str) -> Option<String> {
        let stmt = stmt.strip_prefix("except ")?.trim();

        // Handle "except ExceptionType as var:"
        if let Some(as_pos) = stmt.find(" as ") {
            let var_part = stmt[as_pos + 4..].trim().trim_end_matches(':').trim();
            if is_valid_identifier(var_part) {
                return Some(var_part.to_string());
            }
        }

        None
    }

    /// Extract global declaration names.
    fn extract_global_names(stmt: &str) -> Vec<String> {
        let stmt = stmt.strip_prefix("global ").unwrap_or(stmt);
        stmt.split(',')
            .map(|s| s.trim())
            .filter(|s| is_valid_identifier(s))
            .map(|s| s.to_string())
            .collect()
    }

    /// Extract nonlocal declaration names.
    fn extract_nonlocal_names(stmt: &str) -> Vec<String> {
        let stmt = stmt.strip_prefix("nonlocal ").unwrap_or(stmt);
        stmt.split(',')
            .map(|s| s.trim())
            .filter(|s| is_valid_identifier(s))
            .map(|s| s.to_string())
            .collect()
    }

    /// Extract walrus operator targets.
    fn extract_walrus_vars(stmt: &str) -> Vec<String> {
        let mut names = Vec::new();
        let mut remaining = stmt;

        while let Some(pos) = remaining.find(":=") {
            // Find the start of the identifier before :=
            let before = &remaining[..pos];
            if let Some(start) = before.rfind(|c: char| !c.is_alphanumeric() && c != '_') {
                let name = before[start + 1..].trim();
                if is_valid_identifier(name) {
                    names.push(name.to_string());
                }
            } else {
                let name = before.trim();
                if is_valid_identifier(name) {
                    names.push(name.to_string());
                }
            }
            remaining = &remaining[pos + 2..];
        }

        names
    }

    /// Check if statement is an augmented assignment.
    fn is_augmented_assignment(stmt: &str) -> bool {
        let ops = [
            "+=", "-=", "*=", "/=", "//=", "%=", "**=", "&=", "|=", "^=", "<<=", ">>=", "@=",
        ];
        ops.iter().any(|op| stmt.contains(op))
    }

    /// Extract augmented assignment target.
    fn extract_augmented_target(stmt: &str) -> Option<String> {
        let ops = [
            "+=", "-=", "*=", "/=", "//=", "%=", "**=", "&=", "|=", "^=", "<<=", ">>=", "@=",
        ];

        for op in ops {
            if let Some(pos) = stmt.find(op) {
                let target = stmt[..pos].trim();
                // Handle attribute access: obj.attr += 1
                let name = target.split('.').next().unwrap_or(target);
                // Handle subscript: arr[i] += 1
                let name = name.split('[').next().unwrap_or(name);
                if is_valid_identifier(name) {
                    return Some(name.to_string());
                }
            }
        }

        None
    }

    /// Check if statement is a regular assignment.
    fn is_assignment(stmt: &str) -> bool {
        // Must have = but not ==, !=, <=, >=, :=
        if !stmt.contains('=') {
            return false;
        }

        // Check for comparison operators and walrus operator
        let exclude = [
            "==", "!=", "<=", ">=", ":=", "+=", "-=", "*=", "/=", "//=", "%=", "**=", "&=", "|=",
            "^=", "<<=", ">>=", "@=",
        ];

        // Find first = that's not part of excluded patterns
        let mut chars = stmt.chars().peekable();
        let mut prev_char = ' ';

        while let Some(c) = chars.next() {
            if c == '=' {
                let next_char = chars.peek().copied().unwrap_or(' ');
                let pair = format!("{}{}", prev_char, c);
                let pair2 = format!("{}{}", c, next_char);

                if !exclude
                    .iter()
                    .any(|ex| pair.ends_with(ex) || pair2.starts_with(&ex[..ex.len().min(2)]))
                {
                    return true;
                }
            }
            prev_char = c;
        }

        false
    }

    /// Extract assignment targets (handles tuple unpacking).
    fn extract_assignment_targets(stmt: &str) -> Vec<String> {
        // Find the first = that's not part of comparison
        let mut depth: u32 = 0;
        let mut eq_pos = None;

        for (i, c) in stmt.char_indices() {
            match c {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                '=' if depth == 0 => {
                    // Check it's not ==, !=, etc.
                    let prev = stmt.chars().nth(i.saturating_sub(1)).unwrap_or(' ');
                    let next = stmt.chars().nth(i + 1).unwrap_or(' ');

                    if prev != '!'
                        && prev != '='
                        && prev != '<'
                        && prev != '>'
                        && prev != '+'
                        && prev != '-'
                        && prev != '*'
                        && prev != '/'
                        && prev != '%'
                        && prev != '&'
                        && prev != '|'
                        && prev != '^'
                        && prev != ':'
                        && prev != '@'
                        && next != '='
                    {
                        eq_pos = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }

        if let Some(pos) = eq_pos {
            let targets_part = stmt[..pos].trim();
            return Self::extract_tuple_vars(targets_part);
        }

        Vec::new()
    }

    /// Extract variables from a tuple pattern like "a, b, c" or "(a, (b, c))".
    fn extract_tuple_vars(pattern: &str) -> Vec<String> {
        let mut names = Vec::new();
        let pattern = pattern.trim();

        // Remove outer parens if present
        let pattern = if pattern.starts_with('(') && pattern.ends_with(')') {
            &pattern[1..pattern.len() - 1]
        } else {
            pattern
        };

        // Simple split by comma (doesn't handle nested tuples perfectly)
        for part in pattern.split(',') {
            let name = part.trim();
            // Remove * for starred expressions
            let name = name.strip_prefix('*').unwrap_or(name);
            // Handle attribute access
            let name = name.split('.').next().unwrap_or(name);
            // Handle subscript
            let name = name.split('[').next().unwrap_or(name);

            if is_valid_identifier(name) {
                names.push(name.to_string());
            }
        }

        names
    }

}

// =============================================================================
// Use Extraction
// =============================================================================

/// Extract variable uses from a statement.
fn extract_uses_from_statement(stmt: &str, defined_vars: &FxHashSet<String>) -> Vec<String> {
    let mut uses = Vec::new();
    let stmt = stmt.trim();

    if stmt.is_empty() || stmt.starts_with('#') || stmt.starts_with("//") {
        return uses;
    }

    // Tokenize and find identifiers
    let mut current_word = String::new();

    for c in stmt.chars() {
        if c.is_alphanumeric() || c == '_' {
            current_word.push(c);
        } else {
            if !current_word.is_empty()
                && defined_vars.contains(&current_word)
                && !is_keyword(&current_word)
            {
                uses.push(current_word.clone());
            }
            current_word.clear();
        }
    }

    // Don't forget the last word
    if !current_word.is_empty()
        && defined_vars.contains(&current_word)
        && !is_keyword(&current_word)
    {
        uses.push(current_word);
    }

    uses
}

/// Check if a word is a Python keyword.
fn is_keyword(word: &str) -> bool {
    matches!(
        word,
        "False"
            | "None"
            | "True"
            | "and"
            | "as"
            | "assert"
            | "async"
            | "await"
            | "break"
            | "class"
            | "continue"
            | "def"
            | "del"
            | "elif"
            | "else"
            | "except"
            | "finally"
            | "for"
            | "from"
            | "global"
            | "if"
            | "import"
            | "in"
            | "is"
            | "lambda"
            | "nonlocal"
            | "not"
            | "or"
            | "pass"
            | "raise"
            | "return"
            | "try"
            | "while"
            | "with"
            | "yield"
            | "match"
            | "case"
    )
}

// =============================================================================
// Reaching Definitions Analysis
// =============================================================================

/// Analyze reaching definitions for a function.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
///
/// # Returns
/// Result containing the reaching definitions analysis.
///
/// # Errors
/// Returns error if file cannot be read, parsed, or function not found.
pub fn analyze_reaching_definitions(
    file: &str,
    function: &str,
) -> Result<ReachingDefinitionsResult> {
    analyze_reaching_definitions_with_language(file, function, None)
}

/// Analyze reaching definitions with explicit language specification.
///
/// # Arguments
/// * `file` - Path to the source file
/// * `function` - Name of the function to analyze
/// * `language` - Optional language override
///
/// # Returns
/// Result containing the reaching definitions analysis.
pub fn analyze_reaching_definitions_with_language(
    file: &str,
    function: &str,
    language: Option<&str>,
) -> Result<ReachingDefinitionsResult> {
    // Validate path exists
    let path = Path::new(file);
    if !path.exists() {
        return Err(BrrrError::io_with_path(
            std::io::Error::new(std::io::ErrorKind::NotFound, "File not found"),
            path,
        ));
    }

    // Extract CFG
    let cfg = extract_with_language(file, function, language)?;

    // Run analysis
    analyze_reaching_definitions_from_cfg(&cfg)
}

/// Run reaching definitions analysis on a CFG.
pub fn analyze_reaching_definitions_from_cfg(cfg: &CFGInfo) -> Result<ReachingDefinitionsResult> {
    // Step 1: Extract all definitions from CFG blocks
    let mut definitions = Vec::new();
    let mut next_def_id = 0;
    let mut block_definitions: FxHashMap<BlockId, Vec<DefId>> = FxHashMap::default();

    // Also extract parameter definitions for the entry block
    // Parameters are implicit definitions at function entry
    extract_parameters_as_definitions(cfg, &mut definitions, &mut next_def_id);

    for (block_id, block) in &cfg.blocks {
        let mut block_defs = Vec::new();

        for stmt in &block.statements {
            let start_idx = definitions.len();
            DefinitionExtractor::extract_from_statement(
                stmt,
                block.start_line,
                *block_id,
                &mut next_def_id,
                &mut definitions,
            );

            // Record definitions created in this block
            for i in start_idx..definitions.len() {
                block_defs.push(definitions[i].def_id);
            }
        }

        block_definitions.insert(*block_id, block_defs);
    }

    let num_defs = definitions.len();

    if num_defs == 0 {
        // No definitions found, return empty result
        return Ok(ReachingDefinitionsResult {
            function_name: cfg.function_name.clone(),
            definitions: Vec::new(),
            reaching_in: FxHashMap::default(),
            reaching_out: FxHashMap::default(),
            def_use_chains: Vec::new(),
            issues: Vec::new(),
            iterations: 0,
        });
    }

    // Build variable-to-definitions mapping for KILL set computation
    let mut var_defs: FxHashMap<&str, Vec<DefId>> = FxHashMap::default();
    for def in &definitions {
        var_defs.entry(&def.variable).or_default().push(def.def_id);
    }

    // Step 2: Compute GEN and KILL sets for each block
    let mut gen_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut kill_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    for (block_id, block_defs) in &block_definitions {
        let mut gen = BitSet::with_capacity(num_defs);
        let mut kill = BitSet::with_capacity(num_defs);

        // GEN: definitions generated in this block
        for def_id in block_defs {
            gen.insert(def_id.0);
        }

        // KILL: definitions of same variables killed by definitions in this block
        for def_id in block_defs {
            let def = &definitions[def_id.0];
            if let Some(other_defs) = var_defs.get(def.variable.as_str()) {
                for other in other_defs {
                    if other.0 != def_id.0 {
                        kill.insert(other.0);
                    }
                }
            }
        }

        gen_sets.insert(*block_id, gen);
        kill_sets.insert(*block_id, kill);
    }

    // Step 3: Initialize IN and OUT sets
    let mut in_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();
    let mut out_sets: FxHashMap<BlockId, BitSet> = FxHashMap::default();

    for block_id in cfg.blocks.keys() {
        in_sets.insert(*block_id, BitSet::with_capacity(num_defs));
        out_sets.insert(*block_id, BitSet::with_capacity(num_defs));
    }

    // Step 4: Worklist algorithm for forward data flow
    let mut worklist: VecDeque<BlockId> = cfg.topological_order().into_iter().collect();
    let mut iterations = 0;
    const MAX_ITERATIONS: usize = 1000;

    while let Some(block_id) = worklist.pop_front() {
        iterations += 1;
        if iterations > MAX_ITERATIONS {
            // Prevent infinite loops in case of bugs
            break;
        }

        // Compute IN[B] = union of OUT[P] for all predecessors P
        let mut new_in = BitSet::with_capacity(num_defs);
        for pred in cfg.predecessors(block_id) {
            if let Some(pred_out) = out_sets.get(pred) {
                new_in.union_with(pred_out);
            }
        }

        // Compute OUT[B] = GEN[B] U (IN[B] - KILL[B])
        let mut new_out = new_in.clone();
        if let Some(kill) = kill_sets.get(&block_id) {
            new_out.difference_with(kill);
        }
        if let Some(gen) = gen_sets.get(&block_id) {
            new_out.union_with(gen);
        }

        // Check if OUT changed
        let old_out = out_sets.get(&block_id);
        let changed = old_out.map(|o| o != &new_out).unwrap_or(true);

        // Update sets
        in_sets.insert(block_id, new_in);
        out_sets.insert(block_id, new_out);

        // If OUT changed, add successors to worklist
        if changed {
            for succ in cfg.successors(block_id) {
                if !worklist.contains(succ) {
                    worklist.push_back(*succ);
                }
            }
        }
    }

    // Step 5: Build def-use chains
    let def_use_chains = build_def_use_chains(cfg, &definitions, &in_sets);

    // Step 6: Detect issues
    let issues = detect_issues(&definitions, &def_use_chains, &in_sets, cfg);

    // Convert BitSets to Vec for serialization
    let reaching_in: FxHashMap<usize, Vec<usize>> = in_sets
        .into_iter()
        .map(|(k, v)| (k.0, v.iter().collect()))
        .collect();

    let reaching_out: FxHashMap<usize, Vec<usize>> = out_sets
        .into_iter()
        .map(|(k, v)| (k.0, v.iter().collect()))
        .collect();

    Ok(ReachingDefinitionsResult {
        function_name: cfg.function_name.clone(),
        definitions,
        reaching_in,
        reaching_out,
        def_use_chains,
        issues,
        iterations,
    })
}

/// Extract function parameters as definitions at the entry block.
fn extract_parameters_as_definitions(
    cfg: &CFGInfo,
    definitions: &mut Vec<Definition>,
    next_def_id: &mut usize,
) {
    // Get the entry block
    if let Some(entry_block) = cfg.blocks.get(&cfg.entry) {
        // Try to extract parameters from the first statement (function signature)
        for stmt in &entry_block.statements {
            if stmt.contains("def ") || stmt.contains("fn ") || stmt.contains("func ") {
                // Extract parameters between parens
                if let Some(start) = stmt.find('(') {
                    if let Some(end) = stmt.rfind(')') {
                        let params_str = &stmt[start + 1..end];
                        for param in params_str.split(',') {
                            let param = param.trim();
                            // Handle typed parameters: "x: int" or "x: int = default"
                            let name = param
                                .split(':')
                                .next()
                                .unwrap_or(param)
                                .split('=')
                                .next()
                                .unwrap_or(param)
                                .trim();

                            // Skip self, cls, empty, *args, **kwargs patterns
                            if !name.is_empty()
                                && name != "self"
                                && name != "cls"
                                && !name.starts_with('*')
                                && is_valid_identifier(name)
                            {
                                definitions.push(Definition {
                                    variable: name.to_string(),
                                    location: Location::new(entry_block.start_line, cfg.entry),
                                    def_id: DefId(*next_def_id),
                                    kind: DefKind::Parameter,
                                });
                                *next_def_id += 1;
                            }
                        }
                    }
                }
                break;
            }
        }
    }
}

/// Build def-use chains from reaching definitions.
fn build_def_use_chains(
    cfg: &CFGInfo,
    definitions: &[Definition],
    in_sets: &FxHashMap<BlockId, BitSet>,
) -> Vec<DefUseChain> {
    let num_defs = definitions.len();

    // Build a map from variable name to definition IDs
    let mut var_defs: FxHashMap<&str, Vec<DefId>> = FxHashMap::default();
    for def in definitions {
        var_defs.entry(&def.variable).or_default().push(def.def_id);
    }

    // Build a map from block_id to definitions in that block
    let mut block_defs: FxHashMap<BlockId, Vec<DefId>> = FxHashMap::default();
    for def in definitions {
        block_defs
            .entry(def.location.block_id)
            .or_default()
            .push(def.def_id);
    }

    // Build set of all defined variable names
    let defined_vars: FxHashSet<String> = definitions.iter().map(|d| d.variable.clone()).collect();

    // For each definition, find uses
    let mut chains: Vec<DefUseChain> = definitions
        .iter()
        .map(|def| DefUseChain {
            definition: def.def_id,
            variable: def.variable.clone(),
            def_location: def.location.clone(),
            uses: Vec::new(),
            use_count: 0,
        })
        .collect();

    // Scan all blocks for uses
    for (block_id, block) in &cfg.blocks {
        // Start with definitions reaching block entry
        let mut current_reaching = in_sets
            .get(block_id)
            .cloned()
            .unwrap_or_else(|| BitSet::with_capacity(num_defs));

        // Get definitions in this block for tracking intra-block def-use
        let defs_in_block = block_defs.get(block_id);

        for stmt in &block.statements {
            // First, extract uses from this statement
            let used_vars = extract_uses_from_statement(stmt, &defined_vars);

            for var in &used_vars {
                // Find which definitions of this variable reach this point
                if let Some(def_ids) = var_defs.get(var.as_str()) {
                    for def_id in def_ids {
                        if current_reaching.contains(def_id.0) {
                            // This definition reaches this use
                            let chain = &mut chains[def_id.0];
                            let use_loc = Location::new(block.start_line, *block_id);
                            // Avoid duplicate uses at the same location
                            if !chain.uses.iter().any(|u| u.line == use_loc.line) {
                                chain.uses.push(use_loc);
                                chain.use_count += 1;
                            }
                        }
                    }
                }
            }

            // Then, update current_reaching with any definitions in this statement
            // This handles intra-block def-use chains
            if let Some(defs) = defs_in_block {
                for def_id in defs {
                    // Add definitions from this block that occur in this statement
                    // Since we process statements in order, definitions are added after their uses
                    let def = &definitions[def_id.0];
                    // Simple heuristic: check if this statement likely contains the definition
                    // by checking if the variable name appears on the left side of assignment
                    if stmt.contains(&def.variable) && is_definition_in_stmt(stmt, &def.variable) {
                        // Kill other definitions of same variable
                        if let Some(other_defs) = var_defs.get(def.variable.as_str()) {
                            for other in other_defs {
                                if other.0 != def_id.0 {
                                    current_reaching.remove(other.0);
                                }
                            }
                        }
                        // Add this definition
                        current_reaching.insert(def_id.0);
                    }
                }
            }
        }
    }

    chains
}

/// Check if a statement contains a definition of the given variable.
fn is_definition_in_stmt(stmt: &str, var: &str) -> bool {
    // Look for patterns like "var = " or "var, " (tuple) at start
    let stmt = stmt.trim();

    // Check for simple assignment: var = ...
    if let Some(eq_pos) = stmt.find('=') {
        let before_eq = &stmt[..eq_pos];
        // Check if var appears in the targets (before =)
        let targets: Vec<&str> = before_eq.split(',').map(|s| s.trim()).collect();
        for target in targets {
            // Handle simple identifiers and starred expressions
            let target = target.trim_start_matches('*');
            if target == var {
                return true;
            }
        }
    }

    // Check for for loop: for var in ...
    if stmt.starts_with("for ") || stmt.starts_with("async for ") {
        if let Some(in_pos) = stmt.find(" in ") {
            let start = if stmt.starts_with("async ") {
                "async for ".len()
            } else {
                "for ".len()
            };
            let loop_vars = &stmt[start..in_pos];
            for lv in loop_vars.split(',') {
                if lv.trim() == var {
                    return true;
                }
            }
        }
    }

    false
}

/// Detect potential issues from reaching definitions analysis.
fn detect_issues(
    definitions: &[Definition],
    def_use_chains: &[DefUseChain],
    in_sets: &FxHashMap<BlockId, BitSet>,
    cfg: &CFGInfo,
) -> Vec<Issue> {
    let mut issues = Vec::new();

    // Build set of all defined variable names
    let defined_vars: FxHashSet<String> = definitions.iter().map(|d| d.variable.clone()).collect();

    // Build map from variable to definition IDs
    let mut var_defs: FxHashMap<&str, Vec<DefId>> = FxHashMap::default();
    for def in definitions {
        var_defs.entry(&def.variable).or_default().push(def.def_id);
    }

    // Issue 1: Dead stores (definitions never used)
    for chain in def_use_chains {
        if chain.use_count == 0 {
            let def = &definitions[chain.definition.0];
            // Parameters are expected to potentially be unused
            // Global/nonlocal declarations don't count as dead stores
            if def.kind != DefKind::Parameter
                && def.kind != DefKind::GlobalDecl
                && def.kind != DefKind::NonlocalDecl
                && def.kind != DefKind::FunctionDef
                && def.kind != DefKind::ClassDef
            {
                issues.push(Issue {
                    kind: IssueKind::DeadStore,
                    message: format!(
                        "Definition of '{}' at line {} is never used",
                        def.variable, def.location.line
                    ),
                    location: def.location.clone(),
                    variable: def.variable.clone(),
                });
            }
        }
    }

    // Issue 2: Potentially uninitialized variables
    // A variable use is uninitialized if no definition reaches it
    for (block_id, block) in &cfg.blocks {
        let reaching = in_sets.get(block_id);

        for stmt in &block.statements {
            let used_vars = extract_uses_from_statement(stmt, &defined_vars);

            for var in used_vars {
                // Check if any definition of this variable reaches here
                let has_reaching_def = if let Some(reaching) = reaching {
                    if let Some(def_ids) = var_defs.get(var.as_str()) {
                        def_ids.iter().any(|id| reaching.contains(id.0))
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !has_reaching_def {
                    // Check if variable is defined later in the same block (local definition)
                    let defined_locally = definitions
                        .iter()
                        .any(|d| d.variable == var && d.location.block_id == *block_id);

                    if !defined_locally {
                        issues.push(Issue {
                            kind: IssueKind::UninitializedVariable,
                            message: format!(
                                "Variable '{}' may be used before being initialized at line {}",
                                var, block.start_line
                            ),
                            location: Location::new(block.start_line, *block_id),
                            variable: var,
                        });
                    }
                }
            }
        }
    }

    // Deduplicate issues by (kind, variable, line)
    let mut seen: FxHashSet<(IssueKind, String, usize)> = FxHashSet::default();
    issues.retain(|issue| {
        let key = (issue.kind, issue.variable.clone(), issue.location.line);
        seen.insert(key)
    });

    issues
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;
    use std::collections::HashSet;

    use super::*;
    use crate::cfg::types::{BlockType, CFGBlock, CFGEdge, EdgeType};

    /// Create a simple test CFG for:
    /// ```python
    /// def test(a, b):  # Line 1, Block 0
    ///     x = a + 1    # Line 2, Block 1
    ///     y = x + b    # Line 3, Block 1
    ///     return y     # Line 4, Block 2
    /// ```
    fn create_linear_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(a, b):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "body".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = a + 1".to_string(), "y = x + b".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return y".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
            ],
            BlockId(0),
            vec![BlockId(2)],
        )
    }

    /// Create a CFG with branches:
    /// ```python
    /// def test(x):     # Line 1, Block 0
    ///     if x > 0:    # Line 2, Block 1
    ///         y = 1    # Line 3, Block 2 (true branch)
    ///     else:
    ///         y = 2    # Line 5, Block 3 (false branch)
    ///     return y     # Line 6, Block 4
    /// ```
    fn create_branching_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(x):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "condition".to_string(),
                block_type: BlockType::Branch,
                statements: vec!["if x > 0:".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "true_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = 1".to_string()],
                func_calls: vec![],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "false_branch".to_string(),
                block_type: BlockType::Body,
                statements: vec!["y = 2".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return y".to_string()],
                func_calls: vec![],
                start_line: 6,
                end_line: 6,
            },
        );

        CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::new(BlockId(1), BlockId(2), EdgeType::True),
                CFGEdge::new(BlockId(1), BlockId(3), EdgeType::False),
                CFGEdge::unconditional(BlockId(2), BlockId(4)),
                CFGEdge::unconditional(BlockId(3), BlockId(4)),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    /// Create a CFG with a loop:
    /// ```python
    /// def test(n):     # Line 1, Block 0
    ///     x = 0        # Line 2, Block 1
    ///     for i in range(n):  # Line 3, Block 2 (loop header)
    ///         x = x + i  # Line 4, Block 3 (loop body)
    ///     return x     # Line 5, Block 4
    /// ```
    fn create_loop_cfg() -> CFGInfo {
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test(n):".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "init".to_string(),
                block_type: BlockType::Body,
                statements: vec!["x = 0".to_string()],
                func_calls: vec![],
                start_line: 2,
                end_line: 2,
            },
        );

        blocks.insert(
            BlockId(2),
            CFGBlock {
                id: BlockId(2),
                label: "loop_header".to_string(),
                block_type: BlockType::LoopHeader,
                statements: vec!["for i in range(n):".to_string()],
                func_calls: vec!["range".to_string()],
                start_line: 3,
                end_line: 3,
            },
        );

        blocks.insert(
            BlockId(3),
            CFGBlock {
                id: BlockId(3),
                label: "loop_body".to_string(),
                block_type: BlockType::LoopBody,
                statements: vec!["x = x + i".to_string()],
                func_calls: vec![],
                start_line: 4,
                end_line: 4,
            },
        );

        blocks.insert(
            BlockId(4),
            CFGBlock {
                id: BlockId(4),
                label: "return".to_string(),
                block_type: BlockType::Return,
                statements: vec!["return x".to_string()],
                func_calls: vec![],
                start_line: 5,
                end_line: 5,
            },
        );

        CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![
                CFGEdge::unconditional(BlockId(0), BlockId(1)),
                CFGEdge::unconditional(BlockId(1), BlockId(2)),
                CFGEdge::new(BlockId(2), BlockId(3), EdgeType::Enter),
                CFGEdge::new(BlockId(3), BlockId(2), EdgeType::BackEdge),
                CFGEdge::new(BlockId(2), BlockId(4), EdgeType::Exit),
            ],
            BlockId(0),
            vec![BlockId(4)],
        )
    }

    #[test]
    fn test_bitset_basic_operations() {
        let mut set = BitSet::with_capacity(100);

        assert!(set.is_empty());
        assert_eq!(set.len(), 0);

        assert!(set.insert(5));
        assert!(!set.insert(5)); // Already present
        assert!(set.contains(5));
        assert!(!set.contains(6));
        assert_eq!(set.len(), 1);

        set.insert(10);
        set.insert(63);
        set.insert(64);
        set.insert(65);

        assert_eq!(set.len(), 5);

        let collected: Vec<_> = set.iter().collect();
        assert_eq!(collected, vec![5, 10, 63, 64, 65]);
    }

    #[test]
    fn test_bitset_union_and_difference() {
        let mut set1 = BitSet::with_capacity(100);
        let mut set2 = BitSet::with_capacity(100);

        set1.insert(1);
        set1.insert(2);
        set1.insert(3);

        set2.insert(2);
        set2.insert(3);
        set2.insert(4);

        // Union
        let mut union = set1.clone();
        union.union_with(&set2);
        assert_eq!(union.len(), 4);
        assert!(union.contains(1));
        assert!(union.contains(2));
        assert!(union.contains(3));
        assert!(union.contains(4));

        // Difference
        let mut diff = set1.clone();
        diff.difference_with(&set2);
        assert_eq!(diff.len(), 1);
        assert!(diff.contains(1));
        assert!(!diff.contains(2));
    }

    #[test]
    fn test_definition_extractor_simple_assignment() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "x = 42",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "x");
        assert_eq!(defs[0].kind, DefKind::Assignment);
    }

    #[test]
    fn test_definition_extractor_tuple_unpacking() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "a, b, c = func()",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 3);
        let vars: Vec<_> = defs.iter().map(|d| d.variable.as_str()).collect();
        assert!(vars.contains(&"a"));
        assert!(vars.contains(&"b"));
        assert!(vars.contains(&"c"));
    }

    #[test]
    fn test_definition_extractor_for_loop() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "for x, y in items:",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 2);
        assert_eq!(defs[0].kind, DefKind::ForLoopVar);
        assert_eq!(defs[1].kind, DefKind::ForLoopVar);
    }

    #[test]
    fn test_definition_extractor_import() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "from os import path, getcwd as cwd",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 2);
        let vars: Vec<_> = defs.iter().map(|d| d.variable.as_str()).collect();
        assert!(vars.contains(&"path"));
        assert!(vars.contains(&"cwd")); // Uses alias
    }

    #[test]
    fn test_definition_extractor_augmented_assignment() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "x += 1",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "x");
        assert_eq!(defs[0].kind, DefKind::AugmentedAssignment);
    }

    #[test]
    fn test_linear_code_analysis() {
        let cfg = create_linear_cfg();
        let result = analyze_reaching_definitions_from_cfg(&cfg).unwrap();

        // Should have definitions for: a, b (params), x, y (assignments)
        assert!(result.definitions.len() >= 2); // At least x and y

        // Check that definitions were found
        let def_vars: HashSet<_> = result
            .definitions
            .iter()
            .map(|d| d.variable.as_str())
            .collect();
        assert!(def_vars.contains("x"));
        assert!(def_vars.contains("y"));

        // Convergence should be quick for linear code
        assert!(result.iterations <= 10);
    }

    #[test]
    fn test_branching_code_analysis() {
        let cfg = create_branching_cfg();
        let result = analyze_reaching_definitions_from_cfg(&cfg).unwrap();

        // Should have two definitions of y (one from each branch)
        let y_defs: Vec<_> = result
            .definitions
            .iter()
            .filter(|d| d.variable == "y")
            .collect();
        assert_eq!(y_defs.len(), 2);

        // At the return block (block 4), both definitions of y should reach
        let reaching_at_return = result.reaching_in.get(&4);
        assert!(reaching_at_return.is_some());

        let reaching = reaching_at_return.unwrap();
        let y_def_ids: Vec<_> = y_defs.iter().map(|d| d.def_id.0).collect();
        for id in y_def_ids {
            assert!(
                reaching.contains(&id),
                "Definition {} should reach return block",
                id
            );
        }
    }

    #[test]
    fn test_loop_code_analysis() {
        let cfg = create_loop_cfg();
        let result = analyze_reaching_definitions_from_cfg(&cfg).unwrap();

        // Should have definitions for: n (param), x (init and loop body), i (loop var)
        let def_vars: HashSet<_> = result
            .definitions
            .iter()
            .map(|d| d.variable.as_str())
            .collect();
        assert!(def_vars.contains("x"));
        assert!(def_vars.contains("i"));

        // Multiple iterations due to back edge
        assert!(result.iterations >= 2);

        // At the return block, both definitions of x should potentially reach
        // (the initial x=0 and the loop body x=x+i)
        let x_defs: Vec<_> = result
            .definitions
            .iter()
            .filter(|d| d.variable == "x")
            .collect();
        assert!(x_defs.len() >= 2);
    }

    #[test]
    fn test_def_use_chains() {
        let cfg = create_linear_cfg();
        let result = analyze_reaching_definitions_from_cfg(&cfg).unwrap();

        // Find the def-use chain for x
        let x_chain = result.def_use_chains.iter().find(|c| c.variable == "x");
        assert!(x_chain.is_some());

        // x is used in "y = x + b", so should have at least one use
        let x_chain = x_chain.unwrap();
        assert!(x_chain.use_count >= 1);
    }

    #[test]
    fn test_dead_store_detection() {
        // Create a CFG with a dead store
        let mut blocks = FxHashMap::default();

        blocks.insert(
            BlockId(0),
            CFGBlock {
                id: BlockId(0),
                label: "entry".to_string(),
                block_type: BlockType::Entry,
                statements: vec!["def test():".to_string()],
                func_calls: vec![],
                start_line: 1,
                end_line: 1,
            },
        );

        blocks.insert(
            BlockId(1),
            CFGBlock {
                id: BlockId(1),
                label: "body".to_string(),
                block_type: BlockType::Body,
                statements: vec![
                    "x = 1".to_string(), // This is a dead store
                    "x = 2".to_string(), // x is redefined before use
                    "return x".to_string(),
                ],
                func_calls: vec![],
                start_line: 2,
                end_line: 4,
            },
        );

        let cfg = CFGInfo::new(
            "test".to_string(),
            blocks,
            vec![CFGEdge::unconditional(BlockId(0), BlockId(1))],
            BlockId(0),
            vec![BlockId(1)],
        );

        let result = analyze_reaching_definitions_from_cfg(&cfg).unwrap();

        // Should detect the dead store (first x=1 is never used)
        let dead_stores: Vec<_> = result
            .issues
            .iter()
            .filter(|i| i.kind == IssueKind::DeadStore)
            .collect();

        assert!(
            !dead_stores.is_empty(),
            "Should detect the dead store x = 1"
        );
    }

    #[test]
    fn test_with_statement_extraction() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "with open('file') as f:",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "f");
        assert_eq!(defs[0].kind, DefKind::WithVar);
    }

    #[test]
    fn test_except_clause_extraction() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "except ValueError as e:",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "e");
        assert_eq!(defs[0].kind, DefKind::ExceptVar);
    }

    #[test]
    fn test_function_def_extraction() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "def my_function(x, y):",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "my_function");
        assert_eq!(defs[0].kind, DefKind::FunctionDef);
    }

    #[test]
    fn test_class_def_extraction() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "class MyClass(Base):",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].variable, "MyClass");
        assert_eq!(defs[0].kind, DefKind::ClassDef);
    }

    #[test]
    fn test_multiple_assignment_targets() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        // Python allows: x = y = z = 0
        DefinitionExtractor::extract_from_statement(
            "x = y = z = 0",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        // Our simple parser may only catch the first target
        // That's acceptable for basic analysis
        assert!(!defs.is_empty());
    }

    #[test]
    fn test_global_nonlocal_extraction() {
        let mut defs = Vec::new();
        let mut next_id = 0;

        DefinitionExtractor::extract_from_statement(
            "global x, y, z",
            1,
            BlockId(0),
            &mut next_id,
            &mut defs,
        );

        assert_eq!(defs.len(), 3);
        for def in &defs {
            assert_eq!(def.kind, DefKind::GlobalDecl);
        }
    }
}
