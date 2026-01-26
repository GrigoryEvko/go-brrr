//! Effect rows for tracking combined effects with row polymorphism
//!
//! An effect row represents the set of effects a computation may perform.
//! Row variables enable effect polymorphism (like F* Effects.fsti).
//!
//! # Row Types
//!
//! - `<>` - Empty closed row (pure)
//! - `<E>` - Single effect, closed
//! - `<E | ρ>` - Effect E plus row variable ρ (polymorphic)
//! - `<E₁, E₂ | ρ>` - Multiple effects plus row variable
//!
//! # Handler Semantics
//!
//! Handlers consume ONE instance of an effect at a time. If a computation
//! has type `<Throw, Throw | ρ> T`, a handler for Throw produces
//! `<Throw | ρ> T` - still one Throw remaining.

use serde::{Deserialize, Serialize};
use super::ops::EffectOp;

/// Effect variable for row polymorphism (de Bruijn index)
///
/// Used in polymorphic effect signatures like:
/// ```text
/// ∀ε. (A -<ε>-> B) -> (List A -<ε>-> List B)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectVar(pub u32);

impl EffectVar {
    /// Create a new effect variable with the given index
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    /// Get the de Bruijn index
    pub const fn index(&self) -> u32 {
        self.0
    }

    /// Shift the variable by a given amount (for substitution under binders)
    pub const fn shift(&self, by: u32) -> Self {
        Self(self.0 + by)
    }
}

impl std::fmt::Display for EffectVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use Greek letters for effect variables: ε, ρ, φ, ψ, ...
        const VARS: &[char] = &['ε', 'ρ', 'φ', 'ψ', 'ω', 'θ', 'δ', 'σ'];
        if (self.0 as usize) < VARS.len() {
            write!(f, "{}", VARS[self.0 as usize])
        } else {
            write!(f, "ε{}", self.0)
        }
    }
}

/// Algebraic effect row representation (mirrors F* effect_row)
///
/// This is the full algebraic representation used for type checking
/// and unification. For efficient runtime operations, use `EffectRow`.
///
/// Maps to F*:
/// ```fstar
/// noeq type effect_row =
///   | RowEmpty : effect_row
///   | RowExt   : effect_op -> effect_row -> effect_row
///   | RowVar   : string -> effect_row
///   | RowVarUnify : string -> string -> effect_row
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectRowKind {
    /// Empty closed row `<>` - pure computation
    Empty,

    /// Row variable `ε` for polymorphism
    Var(EffectVar),

    /// Extended row `<E | ρ>` - effect E plus tail row
    Extend {
        effect: EffectOp,
        tail: Box<EffectRowKind>,
    },

    /// Unification constraint between two row variables
    /// Used during type inference to record that two row variables
    /// must be unified
    VarUnify(EffectVar, EffectVar),
}

impl EffectRowKind {
    /// Create an empty (pure) row
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// Create a row variable
    pub const fn var(v: EffectVar) -> Self {
        Self::Var(v)
    }

    /// Create an extended row
    pub fn extend(effect: EffectOp, tail: Self) -> Self {
        Self::Extend {
            effect,
            tail: Box::new(tail),
        }
    }

    /// Create a single-effect closed row
    pub fn single(effect: EffectOp) -> Self {
        Self::extend(effect, Self::Empty)
    }

    /// Create a unification constraint
    pub const fn unify(v1: EffectVar, v2: EffectVar) -> Self {
        Self::VarUnify(v1, v2)
    }

    /// Check if this is a closed row (no variables)
    pub fn is_closed(&self) -> bool {
        match self {
            Self::Empty => true,
            Self::Var(_) | Self::VarUnify(_, _) => false,
            Self::Extend { tail, .. } => tail.is_closed(),
        }
    }

    /// Check if this is pure (empty and closed)
    pub fn is_pure(&self) -> bool {
        matches!(self, Self::Empty)
    }

    /// Get the tail row variable if this row is open
    pub fn tail_var(&self) -> Option<EffectVar> {
        match self {
            Self::Empty => None,
            Self::Var(v) => Some(*v),
            Self::Extend { tail, .. } => tail.tail_var(),
            Self::VarUnify(v, _) => Some(*v),
        }
    }

    /// Flatten to an EffectRow for efficient operations
    pub fn flatten(&self) -> EffectRow {
        let mut ops = Vec::new();
        let mut tail = RowTail::Closed;
        self.flatten_into(&mut ops, &mut tail);
        ops.sort_by_key(|op| op.discriminant());
        EffectRow { ops, tail }
    }

    fn flatten_into(&self, ops: &mut Vec<EffectOp>, row_tail: &mut RowTail) {
        match self {
            Self::Empty => {}
            Self::Var(v) => *row_tail = RowTail::Var(*v),
            Self::Extend { effect, tail } => {
                ops.push(effect.clone());
                tail.flatten_into(ops, row_tail);
            }
            Self::VarUnify(v1, v2) => *row_tail = RowTail::Unify(*v1, *v2),
        }
    }

    /// Substitute a row variable with another row
    pub fn substitute(&self, target: EffectVar, replacement: &EffectRowKind) -> Self {
        match self {
            Self::Empty => Self::Empty,
            Self::Var(v) if *v == target => replacement.clone(),
            Self::Var(v) => Self::Var(*v),
            Self::Extend { effect, tail } => Self::Extend {
                effect: effect.clone(),
                tail: Box::new(tail.substitute(target, replacement)),
            },
            Self::VarUnify(v1, v2) if *v1 == target || *v2 == target => {
                // If substituting a unified variable, propagate
                replacement.clone()
            }
            Self::VarUnify(v1, v2) => Self::VarUnify(*v1, *v2),
        }
    }
}

impl std::fmt::Display for EffectRowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "<>"),
            Self::Var(v) => write!(f, "<{}>", v),
            Self::Extend { effect, tail } => {
                write!(f, "<{}", effect.as_symbol())?;
                let mut current = tail.as_ref();
                loop {
                    match current {
                        Self::Empty => {
                            write!(f, ">")?;
                            break;
                        }
                        Self::Var(v) => {
                            write!(f, " | {}>", v)?;
                            break;
                        }
                        Self::Extend { effect: e, tail: t } => {
                            write!(f, ", {}", e.as_symbol())?;
                            current = t.as_ref();
                        }
                        Self::VarUnify(v1, v2) => {
                            write!(f, " | {} ~ {}>", v1, v2)?;
                            break;
                        }
                    }
                }
                Ok(())
            }
            Self::VarUnify(v1, v2) => write!(f, "<{} ~ {}>", v1, v2),
        }
    }
}

/// Row tail - represents the tail of an effect row (closed, variable, or unification)
///
/// Maps to F* effect_row tail variants:
/// - `Closed` -> RowEmpty in tail position
/// - `Var(v)` -> RowVar v
/// - `Unify(v1, v2)` -> RowVarUnify v1 v2 (unification constraint during type inference)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RowTail {
    /// Closed row (no more effects possible)
    Closed,
    /// Open row with a single variable
    Var(EffectVar),
    /// Unification constraint: two row variables that must be unified
    /// Created when joining `<E1 | v1>` with `<E2 | v2>` where v1 != v2
    Unify(EffectVar, EffectVar),
}

impl RowTail {
    /// Check if this is a closed tail
    pub const fn is_closed(&self) -> bool {
        matches!(self, Self::Closed)
    }

    /// Check if this is open (has at least one variable)
    pub const fn is_open(&self) -> bool {
        !matches!(self, Self::Closed)
    }

    /// Get the primary variable (if any)
    pub const fn var(&self) -> Option<EffectVar> {
        match self {
            Self::Closed => None,
            Self::Var(v) => Some(*v),
            Self::Unify(v, _) => Some(*v),
        }
    }

    /// Get both variables for unification (if this is a Unify tail)
    pub const fn unify_vars(&self) -> Option<(EffectVar, EffectVar)> {
        match self {
            Self::Unify(v1, v2) => Some((*v1, *v2)),
            _ => None,
        }
    }

    /// Combine two tails (used during join)
    /// - Closed + Closed = Closed
    /// - Closed + Var(v) = Var(v)
    /// - Var(v) + Closed = Var(v)
    /// - Var(v1) + Var(v2) = Unify(v1, v2) if v1 != v2, else Var(v1)
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Closed, Self::Closed) => Self::Closed,
            (Self::Closed, Self::Var(v)) | (Self::Var(v), Self::Closed) => Self::Var(v),
            (Self::Var(v1), Self::Var(v2)) => {
                if v1.0 == v2.0 {
                    Self::Var(v1)
                } else {
                    Self::Unify(v1, v2)
                }
            }
            // When either side already has a unification constraint, preserve it
            (Self::Unify(a, b), Self::Closed) | (Self::Closed, Self::Unify(a, b)) => {
                Self::Unify(a, b)
            }
            (Self::Unify(a, b), Self::Var(_)) | (Self::Var(_), Self::Unify(a, b)) => {
                // Already have a constraint, keep it (could merge but complicates things)
                Self::Unify(a, b)
            }
            (Self::Unify(a, b), Self::Unify(_, _)) => {
                // Both have constraints - keep the first (in practice, type checker resolves)
                Self::Unify(a, b)
            }
        }
    }

    /// Substitute a variable with a new tail
    pub fn substitute(self, target: EffectVar, replacement: Self) -> Self {
        match self {
            Self::Closed => Self::Closed,
            Self::Var(v) if v == target => replacement,
            Self::Var(v) => Self::Var(v),
            Self::Unify(v1, v2) => {
                // If either matches, use replacement
                if v1 == target || v2 == target {
                    replacement
                } else {
                    Self::Unify(v1, v2)
                }
            }
        }
    }
}

impl Default for RowTail {
    fn default() -> Self {
        Self::Closed
    }
}

impl std::fmt::Display for RowTail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closed => write!(f, ""),
            Self::Var(v) => write!(f, " | {}", v),
            Self::Unify(v1, v2) => write!(f, " | {} ~ {}", v1, v2),
        }
    }
}

/// Pure effect row constant
pub const PURE: EffectRow = EffectRow {
    ops: Vec::new(),
    tail: RowTail::Closed,
};

/// Effect row - a set of effect operations with optional row variable
///
/// This is the flattened representation for efficient operations.
/// For algebraic representation, use `EffectRowKind`.
///
/// Effect rows form a lattice:
/// - Bottom: `Pure` (no effects, closed)
/// - Top: `Total` (all effects possible, open with no known var)
/// - Join: union of effects (preserving duplicates for handler semantics)
///
/// # Handler Semantics
///
/// Effects are NOT deduplicated. A row `<Throw, Throw>` has two Throw effects.
/// When a handler handles one Throw, the result is `<Throw>`.
///
/// # Row Variables and Unification
///
/// When joining two rows with different variables:
/// - `<E1 | v1>` join `<E2 | v2>` = `<E1, E2 | v1 ~ v2>`
/// The `Unify(v1, v2)` tail indicates these variables must be unified.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct EffectRow {
    /// Effect operations in this row (sorted by discriminant, NOT deduplicated)
    ops: Vec<EffectOp>,
    /// Row tail: closed, variable, or unification constraint
    tail: RowTail,
}

impl EffectRow {
    /// Pure effect row constant
    pub const PURE: Self = Self {
        ops: Vec::new(),
        tail: RowTail::Closed,
    };

    /// Empty effect row (pure) - function version
    pub const fn pure() -> Self {
        Self {
            ops: Vec::new(),
            tail: RowTail::Closed,
        }
    }

    /// Create a new closed effect row with the given operations
    /// Note: Does NOT deduplicate - handlers consume one at a time
    pub fn new(mut ops: Vec<EffectOp>) -> Self {
        ops.sort_by_key(|op| op.discriminant());
        Self { ops, tail: RowTail::Closed }
    }

    /// Create an open effect row with a row variable
    pub fn open_with_var(mut ops: Vec<EffectOp>, var: EffectVar) -> Self {
        ops.sort_by_key(|op| op.discriminant());
        Self { ops, tail: RowTail::Var(var) }
    }

    /// Create an open effect row (can have additional effects)
    /// Uses a fresh variable (index 0)
    pub fn open(mut ops: Vec<EffectOp>) -> Self {
        ops.sort_by_key(|op| op.discriminant());
        Self { ops, tail: RowTail::Var(EffectVar(0)) }
    }

    /// Create a row with a single effect (closed)
    pub fn single(op: EffectOp) -> Self {
        Self {
            ops: vec![op],
            tail: RowTail::Closed,
        }
    }

    /// Create a row with just a row variable (no known effects)
    pub fn just_var(var: EffectVar) -> Self {
        Self {
            ops: Vec::new(),
            tail: RowTail::Var(var),
        }
    }

    /// Total effects (everything possible) - open row with no known effects
    pub fn total() -> Self {
        Self {
            ops: Vec::new(),
            tail: RowTail::Var(EffectVar(0)),
        }
    }

    /// Check if this row is pure (no effects and closed)
    pub fn is_pure(&self) -> bool {
        self.ops.is_empty() && self.tail.is_closed()
    }

    /// Check if this row is open (has a row variable)
    pub fn is_open(&self) -> bool {
        self.tail.is_open()
    }

    /// Get the row variable if this row is open
    pub fn row_var(&self) -> Option<EffectVar> {
        self.tail.var()
    }

    /// Check if this row contains a specific effect (by discriminant)
    pub fn contains(&self, op: &EffectOp) -> bool {
        let disc = op.discriminant();
        self.ops.iter().any(|o| o.discriminant() == disc)
    }

    /// Check if this row contains an effect with the given discriminant
    pub fn contains_discriminant(&self, disc: u8) -> bool {
        self.ops.iter().any(|o| o.discriminant() == disc)
    }

    /// Count occurrences of an effect (for handler consumption tracking)
    pub fn count(&self, op: &EffectOp) -> usize {
        let disc = op.discriminant();
        self.ops.iter().filter(|o| o.discriminant() == disc).count()
    }

    /// Get the operations in this row
    pub fn ops(&self) -> &[EffectOp] {
        &self.ops
    }

    /// Handle one instance of an effect (remove FIRST occurrence only)
    ///
    /// Returns `None` if the effect is not explicitly present in the row.
    /// This matches F* `effect_handle` semantics:
    /// - `RowVar _ -> None` (cannot remove from a row variable)
    /// - Only explicitly listed effects can be handled
    ///
    /// This is the core operation for effect handler type checking:
    /// a handler for effect E transforms `<E, E | ρ>` into `<E | ρ>`.
    ///
    /// # Examples
    /// ```text
    /// handle(<exn, exn>, exn) = Some(<exn>)    // removes first exn
    /// handle(<exn, io>, exn)  = Some(<io>)     // removes the exn
    /// handle(<io>, exn)       = None           // exn not present
    /// handle(<io | ρ>, exn)   = None           // exn not explicit, can't remove from ρ
    /// ```
    pub fn handle(&self, effect: &EffectOp) -> Option<EffectRow> {
        let disc = effect.discriminant();
        if let Some(pos) = self.ops.iter().position(|e| e.discriminant() == disc) {
            let mut ops = self.ops.clone();
            ops.remove(pos); // Remove ONE instance only
            Some(EffectRow { ops, tail: self.tail })
        } else {
            // Effect not explicitly present - cannot handle from row variable
            // This matches F* semantics: `RowVar _ -> None`
            None
        }
    }

    /// Handle ALL occurrences of an effect (remove every instance)
    ///
    /// Unlike `handle()` which removes only the first occurrence, this removes
    /// all instances of the effect from the row. Returns the resulting row
    /// (which may be unchanged if the effect wasn't present).
    ///
    /// # Examples
    /// ```text
    /// handle_all(<exn, exn, io>, exn) = <io>   // removes both exn
    /// handle_all(<io>, exn)           = <io>   // unchanged, exn not present
    /// ```
    pub fn handle_all(&self, effect: &EffectOp) -> EffectRow {
        let disc = effect.discriminant();
        let ops: Vec<EffectOp> = self.ops.iter()
            .filter(|e| e.discriminant() != disc)
            .cloned()
            .collect();
        EffectRow { ops, tail: self.tail }
    }

    /// Handle multiple effects at once
    pub fn handle_many(&self, effects: &[EffectOp]) -> Option<EffectRow> {
        let mut result = self.clone();
        for effect in effects {
            result = result.handle(effect)?;
        }
        Some(result)
    }

    /// Join two effect rows (union)
    ///
    /// Preserves all effects from both rows (no deduplication).
    /// If either row has a variable, the result is open.
    pub fn join(&self, other: &Self) -> Self {
        let mut ops = self.ops.clone();
        ops.extend(other.ops.iter().cloned());
        ops.sort_by_key(|op| op.discriminant());

        // Join the tails
        let tail = self.tail.join(other.tail);

        Self { ops, tail }
    }

    /// Meet two effect rows (intersection)
    ///
    /// Only keeps effects present in both rows.
    /// Result is open only if both rows are open with the same variable.
    pub fn meet(&self, other: &Self) -> Self {
        // For meet, we take minimum count of each effect
        let mut ops = Vec::new();
        let mut used_other = vec![false; other.ops.len()];

        for op in &self.ops {
            let disc = op.discriminant();
            // Find an unused matching effect in other
            if let Some(pos) = other.ops.iter().enumerate()
                .position(|(i, o)| o.discriminant() == disc && !used_other[i])
            {
                ops.push(op.clone());
                used_other[pos] = true;
            }
        }

        ops.sort_by_key(|op| op.discriminant());

        // Meet of tails: both must have same variable for result to be open
        let tail = match (self.tail, other.tail) {
            (RowTail::Var(v1), RowTail::Var(v2)) if v1 == v2 => RowTail::Var(v1),
            _ => RowTail::Closed,
        };

        Self { ops, tail }
    }

    /// Substitute a row variable with another row
    ///
    /// If this row has the target variable, replaces it with the replacement.
    pub fn substitute(&self, target: EffectVar, replacement: &EffectRow) -> EffectRow {
        if self.tail.var() == Some(target) {
            // Combine our effects with the replacement
            let mut ops = self.ops.clone();
            ops.extend(replacement.ops.iter().cloned());
            ops.sort_by_key(|op| op.discriminant());
            EffectRow {
                ops,
                tail: replacement.tail,
            }
        } else {
            self.clone()
        }
    }

    /// Check if this row is a subrow of another
    ///
    /// A subrow has fewer or equal effects. Open rows are ordered by
    /// the effects they MUST have (ignoring variables).
    pub fn is_subrow_of(&self, other: &Self) -> bool {
        // If other is open, any closed row with subset effects is a subrow
        if other.tail.is_open() && self.tail.is_closed() {
            return self.ops.iter().all(|op| other.contains(op));
        }

        // If self is open but other is closed, can't be a subrow
        // (self might have more effects via the variable)
        if self.tail.is_open() && other.tail.is_closed() {
            return false;
        }

        // Both closed or both open with same structure
        // Check that each effect in self appears at least as many times in other
        for op in &self.ops {
            let self_count = self.count(op);
            let other_count = other.count(op);
            if self_count > other_count && !other.tail.is_open() {
                return false;
            }
        }

        true
    }

    /// Add an effect to this row (in place)
    pub fn add(&mut self, op: EffectOp) {
        self.ops.push(op);
        self.ops.sort_by_key(|o| o.discriminant());
    }

    /// Set the row tail
    pub fn set_tail(&mut self, tail: RowTail) {
        self.tail = tail;
    }

    /// Set the row variable (convenience method)
    pub fn set_var(&mut self, var: Option<EffectVar>) {
        self.tail = match var {
            Some(v) => RowTail::Var(v),
            None => RowTail::Closed,
        };
    }

    /// Number of effects in this row
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Check if empty (not necessarily pure - could have a variable)
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Convert to algebraic representation
    pub fn to_kind(&self) -> EffectRowKind {
        let kind_tail = match self.tail {
            RowTail::Closed => EffectRowKind::Empty,
            RowTail::Var(v) => EffectRowKind::Var(v),
            RowTail::Unify(v1, v2) => EffectRowKind::VarUnify(v1, v2),
        };

        // Build from the end (last effect wraps the tail)
        self.ops.iter().rev().fold(kind_tail, |acc, op| {
            EffectRowKind::Extend {
                effect: op.clone(),
                tail: Box::new(acc),
            }
        })
    }

    /// Format the effect row as a string
    pub fn format(&self) -> String {
        if self.ops.is_empty() {
            return match self.tail {
                RowTail::Closed => "Pure".to_string(),
                RowTail::Var(v) => format!("<{}>", v),
                RowTail::Unify(v1, v2) => format!("<{} ~ {}>", v1, v2),
            };
        }

        let effects: Vec<String> = self.ops.iter()
            .map(|op| op.as_symbol())
            .collect();

        match self.tail {
            RowTail::Closed => format!("<{}>", effects.join(", ")),
            RowTail::Var(v) => format!("<{} | {}>", effects.join(", "), v),
            RowTail::Unify(v1, v2) => format!("<{} | {} ~ {}>", effects.join(", "), v1, v2),
        }
    }
}

impl From<EffectRowKind> for EffectRow {
    fn from(kind: EffectRowKind) -> Self {
        kind.flatten()
    }
}

impl From<&EffectRowKind> for EffectRow {
    fn from(kind: &EffectRowKind) -> Self {
        kind.flatten()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_effect_var_display() {
        assert_eq!(format!("{}", EffectVar(0)), "ε");
        assert_eq!(format!("{}", EffectVar(1)), "ρ");
        assert_eq!(format!("{}", EffectVar(8)), "ε8");
    }

    #[test]
    fn test_pure() {
        let row = EffectRow::pure();
        assert!(row.is_pure());
        assert!(!row.is_open());
        assert_eq!(row.row_var(), None);
    }

    #[test]
    fn test_single() {
        let row = EffectRow::single(EffectOp::ReadSimple);
        assert!(!row.is_pure());
        assert!(!row.is_open());
        assert!(row.contains(&EffectOp::ReadSimple));
        assert!(!row.contains(&EffectOp::WriteSimple));
    }

    #[test]
    fn test_open_with_var() {
        let var = EffectVar(1);
        let row = EffectRow::open_with_var(vec![EffectOp::Io], var);
        assert!(row.is_open());
        assert_eq!(row.row_var(), Some(var));
        assert!(row.contains(&EffectOp::Io));
    }

    #[test]
    fn test_join() {
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let row2 = EffectRow::single(EffectOp::WriteSimple);
        let joined = row1.join(&row2);
        assert!(joined.contains(&EffectOp::ReadSimple));
        assert!(joined.contains(&EffectOp::WriteSimple));
        assert!(!joined.is_open());
    }

    #[test]
    fn test_join_open() {
        let var = EffectVar(0);
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let row2 = EffectRow::open_with_var(vec![EffectOp::WriteSimple], var);
        let joined = row1.join(&row2);
        assert!(joined.is_open());
        assert_eq!(joined.row_var(), Some(var));
    }

    #[test]
    fn test_handle_single() {
        let row = EffectRow::new(vec![EffectOp::Io, EffectOp::Panic]);
        let handled = row.handle(&EffectOp::Io).unwrap();
        assert!(!handled.contains(&EffectOp::Io));
        assert!(handled.contains(&EffectOp::Panic));
    }

    #[test]
    fn test_handle_preserves_duplicates() {
        // Row with two Io effects
        let row = EffectRow::new(vec![EffectOp::Io, EffectOp::Io, EffectOp::Panic]);
        assert_eq!(row.count(&EffectOp::Io), 2);

        // Handle one Io
        let handled = row.handle(&EffectOp::Io).unwrap();
        assert_eq!(handled.count(&EffectOp::Io), 1);
        assert!(handled.contains(&EffectOp::Io));

        // Handle second Io
        let handled2 = handled.handle(&EffectOp::Io).unwrap();
        assert_eq!(handled2.count(&EffectOp::Io), 0);
        assert!(!handled2.contains(&EffectOp::Io));
    }

    #[test]
    fn test_handle_not_present_closed() {
        let row = EffectRow::single(EffectOp::Panic);
        assert!(row.handle(&EffectOp::Io).is_none());
    }

    #[test]
    fn test_handle_open_row_explicit_effect() {
        // Can handle an explicitly listed effect in an open row
        let var = EffectVar(0);
        let row = EffectRow::open_with_var(vec![EffectOp::Panic], var);
        let handled = row.handle(&EffectOp::Panic);
        assert!(handled.is_some());
        let result = handled.unwrap();
        assert!(result.is_open()); // Still open (has row variable)
        assert!(!result.contains(&EffectOp::Panic)); // Panic removed
    }

    #[test]
    fn test_handle_open_row_not_present() {
        // Cannot handle an effect that's not explicitly listed (F* semantics)
        // Even if row is open, we can't remove from the row variable
        let var = EffectVar(0);
        let row = EffectRow::open_with_var(vec![EffectOp::Panic], var);
        let handled = row.handle(&EffectOp::Io);
        // F* semantics: RowVar _ -> None (can't remove from variable)
        assert!(handled.is_none());
    }

    #[test]
    fn test_substitute() {
        let var = EffectVar(0);
        let row = EffectRow::open_with_var(vec![EffectOp::Io], var);

        // Substitute with closed row
        let replacement = EffectRow::single(EffectOp::Panic);
        let result = row.substitute(var, &replacement);

        assert!(result.contains(&EffectOp::Io));
        assert!(result.contains(&EffectOp::Panic));
        assert!(!result.is_open());
    }

    #[test]
    fn test_substitute_different_var() {
        let var0 = EffectVar(0);
        let var1 = EffectVar(1);
        let row = EffectRow::open_with_var(vec![EffectOp::Io], var0);

        // Substitute different variable - no change
        let replacement = EffectRow::single(EffectOp::Panic);
        let result = row.substitute(var1, &replacement);

        assert_eq!(result, row);
    }

    #[test]
    fn test_subrow() {
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let row2 = EffectRow::new(vec![EffectOp::ReadSimple, EffectOp::WriteSimple]);
        assert!(row1.is_subrow_of(&row2));
        assert!(!row2.is_subrow_of(&row1));
    }

    #[test]
    fn test_subrow_open() {
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let var = EffectVar(0);
        let row2 = EffectRow::open_with_var(vec![EffectOp::ReadSimple], var);

        // Closed row is subrow of open row with same effects
        assert!(row1.is_subrow_of(&row2));
    }

    #[test]
    fn test_format() {
        let pure = EffectRow::pure();
        assert_eq!(pure.format(), "Pure");

        let row = EffectRow::single(EffectOp::Io);
        assert_eq!(row.format(), "<IO>");

        let var = EffectVar(0);
        let open = EffectRow::open_with_var(vec![EffectOp::Io], var);
        assert_eq!(open.format(), "<IO | ε>");

        let just_var = EffectRow::just_var(EffectVar(1));
        assert_eq!(just_var.format(), "<ρ>");
    }

    #[test]
    fn test_effect_row_kind_display() {
        let empty = EffectRowKind::Empty;
        assert_eq!(format!("{}", empty), "<>");

        let var = EffectRowKind::Var(EffectVar(0));
        assert_eq!(format!("{}", var), "<ε>");

        let ext = EffectRowKind::extend(
            EffectOp::Io,
            EffectRowKind::Var(EffectVar(0)),
        );
        assert_eq!(format!("{}", ext), "<IO | ε>");

        let multi = EffectRowKind::extend(
            EffectOp::Io,
            EffectRowKind::extend(
                EffectOp::Panic,
                EffectRowKind::Empty,
            ),
        );
        assert_eq!(format!("{}", multi), "<IO, Panic>");
    }

    #[test]
    fn test_effect_row_kind_flatten() {
        let kind = EffectRowKind::extend(
            EffectOp::Io,
            EffectRowKind::extend(
                EffectOp::Panic,
                EffectRowKind::Var(EffectVar(0)),
            ),
        );

        let row = kind.flatten();
        assert!(row.contains(&EffectOp::Io));
        assert!(row.contains(&EffectOp::Panic));
        assert!(row.is_open());
        assert_eq!(row.row_var(), Some(EffectVar(0)));
    }

    #[test]
    fn test_effect_row_kind_substitute() {
        let var = EffectVar(0);
        let kind = EffectRowKind::extend(
            EffectOp::Io,
            EffectRowKind::Var(var),
        );

        let replacement = EffectRowKind::extend(
            EffectOp::Panic,
            EffectRowKind::Empty,
        );

        let result = kind.substitute(var, &replacement);
        let row = result.flatten();

        assert!(row.contains(&EffectOp::Io));
        assert!(row.contains(&EffectOp::Panic));
        assert!(!row.is_open());
    }

    #[test]
    fn test_to_kind_roundtrip() {
        let var = EffectVar(1);
        let row = EffectRow::open_with_var(
            vec![EffectOp::Io, EffectOp::Panic],
            var,
        );

        let kind = row.to_kind();
        let row2 = kind.flatten();

        assert_eq!(row, row2);
    }

    #[test]
    fn test_meet() {
        let row1 = EffectRow::new(vec![EffectOp::Io, EffectOp::Panic]);
        let row2 = EffectRow::new(vec![EffectOp::Io, EffectOp::Fs]);

        let met = row1.meet(&row2);
        assert!(met.contains(&EffectOp::Io));
        assert!(!met.contains(&EffectOp::Panic));
        assert!(!met.contains(&EffectOp::Fs));
    }

    #[test]
    fn test_meet_with_duplicates() {
        // Two Io in first, one in second
        let row1 = EffectRow::new(vec![EffectOp::Io, EffectOp::Io, EffectOp::Panic]);
        let row2 = EffectRow::new(vec![EffectOp::Io]);

        let met = row1.meet(&row2);
        assert_eq!(met.count(&EffectOp::Io), 1); // Minimum of counts
        assert!(!met.contains(&EffectOp::Panic));
    }

    // === Row Variable Unification Tests ===

    #[test]
    fn test_join_different_vars_creates_unify() {
        // Key semantic: joining rows with different variables creates unification constraint
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v1);
        let row2 = EffectRow::open_with_var(vec![EffectOp::Panic], v2);

        let joined = row1.join(&row2);

        // Should have both effects
        assert!(joined.contains(&EffectOp::Io));
        assert!(joined.contains(&EffectOp::Panic));

        // Should be open with a unification constraint
        assert!(joined.is_open());
        assert_eq!(joined.tail, RowTail::Unify(v1, v2));
        assert_eq!(joined.row_var(), Some(v1)); // Primary var is first

        // Should format with unification notation
        assert!(joined.format().contains("~"));
    }

    #[test]
    fn test_join_same_var_no_unify() {
        // Joining with same variable should NOT create Unify
        let v = EffectVar(0);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v);
        let row2 = EffectRow::open_with_var(vec![EffectOp::Panic], v);

        let joined = row1.join(&row2);

        assert!(joined.is_open());
        assert_eq!(joined.tail, RowTail::Var(v));
        assert!(!joined.format().contains("~"));
    }

    #[test]
    fn test_row_tail_join() {
        // Test RowTail::join directly
        assert_eq!(RowTail::Closed.join(RowTail::Closed), RowTail::Closed);

        let v1 = EffectVar(0);
        let v2 = EffectVar(1);

        assert_eq!(RowTail::Closed.join(RowTail::Var(v1)), RowTail::Var(v1));
        assert_eq!(RowTail::Var(v1).join(RowTail::Closed), RowTail::Var(v1));
        assert_eq!(RowTail::Var(v1).join(RowTail::Var(v1)), RowTail::Var(v1));
        assert_eq!(RowTail::Var(v1).join(RowTail::Var(v2)), RowTail::Unify(v1, v2));
    }

    #[test]
    fn test_unify_vars_accessor() {
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v1);
        let row2 = EffectRow::open_with_var(vec![], v2);

        let joined = row1.join(&row2);

        assert_eq!(joined.tail.unify_vars(), Some((v1, v2)));
    }

    #[test]
    fn test_effect_row_kind_varunify_flatten() {
        // Test that EffectRowKind::VarUnify flattens to RowTail::Unify
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let kind = EffectRowKind::extend(
            EffectOp::Io,
            EffectRowKind::VarUnify(v1, v2),
        );

        let row = kind.flatten();

        assert!(row.contains(&EffectOp::Io));
        assert_eq!(row.tail, RowTail::Unify(v1, v2));
    }

    #[test]
    fn test_to_kind_with_unify() {
        // Test roundtrip with unification
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v1);
        let row2 = EffectRow::open_with_var(vec![EffectOp::Panic], v2);
        let joined = row1.join(&row2);

        let kind = joined.to_kind();
        let row_back = kind.flatten();

        assert_eq!(joined, row_back);
    }

    #[test]
    fn test_format_with_unify() {
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v1);
        let row2 = EffectRow::open_with_var(vec![], v2);
        let joined = row1.join(&row2);

        // Format should show unification: <IO | ε ~ ρ>
        let formatted = joined.format();
        assert!(formatted.contains("IO"));
        assert!(formatted.contains("ε"));
        assert!(formatted.contains("ρ"));
        assert!(formatted.contains("~"));
    }

    #[test]
    fn test_substitute_with_unify_tail() {
        // Substituting a variable from a Unify tail should replace the whole tail
        let v1 = EffectVar(0);
        let v2 = EffectVar(1);
        let row1 = EffectRow::open_with_var(vec![EffectOp::Io], v1);
        let row2 = EffectRow::open_with_var(vec![], v2);
        let joined = row1.join(&row2); // <Io | v1 ~ v2>

        // Substitute v1 with a closed row
        let replacement = EffectRow::single(EffectOp::Panic);
        let result = joined.substitute(v1, &replacement);

        assert!(result.contains(&EffectOp::Io));
        assert!(result.contains(&EffectOp::Panic));
        assert!(!result.is_open()); // Became closed
    }

    // ========== Handler Semantics Tests (Critical for F* Correspondence) ==========

    #[test]
    fn test_handle_removes_first_only() {
        // CRITICAL: handle(<exn, exn>, exn) == Some(<exn>)
        // This is the key semantic from F* Effects.fst effect_handle
        let row = EffectRow::new(vec![EffectOp::Panic, EffectOp::Panic]);
        assert_eq!(row.count(&EffectOp::Panic), 2);

        let handled = row.handle(&EffectOp::Panic);
        assert!(handled.is_some(), "handle should succeed when effect is present");

        let result = handled.unwrap();
        assert_eq!(result.count(&EffectOp::Panic), 1, "should remove exactly ONE instance");
        assert!(result.contains(&EffectOp::Panic), "one Panic should remain");
    }

    #[test]
    fn test_handle_with_mixed_effects() {
        // handle(<exn, exn, io>, exn) == Some(<exn, io>)
        let row = EffectRow::new(vec![EffectOp::Panic, EffectOp::Panic, EffectOp::Io]);
        assert_eq!(row.count(&EffectOp::Panic), 2);
        assert_eq!(row.count(&EffectOp::Io), 1);

        let handled = row.handle(&EffectOp::Panic).unwrap();
        assert_eq!(handled.count(&EffectOp::Panic), 1);
        assert_eq!(handled.count(&EffectOp::Io), 1);
    }

    #[test]
    fn test_handle_chain() {
        // Chaining handlers: handle(handle(<exn, exn>, exn), exn) == Some(<>)
        let row = EffectRow::new(vec![EffectOp::Panic, EffectOp::Panic]);

        let first = row.handle(&EffectOp::Panic).unwrap();
        assert_eq!(first.count(&EffectOp::Panic), 1);

        let second = first.handle(&EffectOp::Panic).unwrap();
        assert_eq!(second.count(&EffectOp::Panic), 0);
        assert!(second.is_pure() || second.is_empty());

        // Third handle should fail - no more Panic effects
        let third = second.handle(&EffectOp::Panic);
        assert!(third.is_none(), "cannot handle effect that's not present");
    }

    #[test]
    fn test_handle_all_removes_all() {
        // handle_all(<exn, exn, io>, exn) == <io>
        let row = EffectRow::new(vec![EffectOp::Panic, EffectOp::Panic, EffectOp::Io]);

        let result = row.handle_all(&EffectOp::Panic);
        assert_eq!(result.count(&EffectOp::Panic), 0, "all Panic should be removed");
        assert_eq!(result.count(&EffectOp::Io), 1, "Io should remain");
        assert!(!result.contains(&EffectOp::Panic));
        assert!(result.contains(&EffectOp::Io));
    }

    #[test]
    fn test_handle_all_not_present() {
        // handle_all(<io>, exn) == <io> (unchanged)
        let row = EffectRow::single(EffectOp::Io);
        let result = row.handle_all(&EffectOp::Panic);
        assert_eq!(result, row, "should be unchanged when effect not present");
    }

    #[test]
    fn test_handle_all_preserves_tail() {
        // handle_all(<exn, exn | ρ>, exn) == <ρ>
        let var = EffectVar(0);
        let row = EffectRow::open_with_var(vec![EffectOp::Panic, EffectOp::Panic], var);

        let result = row.handle_all(&EffectOp::Panic);
        assert!(!result.contains(&EffectOp::Panic));
        assert!(result.is_open(), "should still be open");
        assert_eq!(result.row_var(), Some(var), "row variable should be preserved");
    }

    #[test]
    fn test_handle_all_multiple_different_effects() {
        // handle_all on row with multiple different effect types
        let row = EffectRow::new(vec![
            EffectOp::Panic, EffectOp::Io, EffectOp::Panic, EffectOp::Fs, EffectOp::Panic
        ]);
        assert_eq!(row.count(&EffectOp::Panic), 3);

        let result = row.handle_all(&EffectOp::Panic);
        assert_eq!(result.count(&EffectOp::Panic), 0);
        assert_eq!(result.count(&EffectOp::Io), 1);
        assert_eq!(result.count(&EffectOp::Fs), 1);
    }

    #[test]
    fn test_handle_vs_handle_all_semantics() {
        // Verify the difference between handle and handle_all
        let row = EffectRow::new(vec![EffectOp::Panic, EffectOp::Panic, EffectOp::Panic]);

        // handle removes ONE
        let after_handle = row.handle(&EffectOp::Panic).unwrap();
        assert_eq!(after_handle.count(&EffectOp::Panic), 2);

        // handle_all removes ALL
        let after_handle_all = row.handle_all(&EffectOp::Panic);
        assert_eq!(after_handle_all.count(&EffectOp::Panic), 0);
    }

    #[test]
    fn test_duplicates_not_deduplicated() {
        // CRITICAL: Ensure Vec<EffectOp> preserves duplicates
        // This is essential for correct handler semantics
        let row = EffectRow::new(vec![
            EffectOp::Io, EffectOp::Io, EffectOp::Io
        ]);

        // Should have 3 Io effects, not 1
        assert_eq!(row.count(&EffectOp::Io), 3);
        assert_eq!(row.len(), 3);

        // Each handle removes exactly one
        let r1 = row.handle(&EffectOp::Io).unwrap();
        assert_eq!(r1.count(&EffectOp::Io), 2);

        let r2 = r1.handle(&EffectOp::Io).unwrap();
        assert_eq!(r2.count(&EffectOp::Io), 1);

        let r3 = r2.handle(&EffectOp::Io).unwrap();
        assert_eq!(r3.count(&EffectOp::Io), 0);

        // Fourth should fail
        assert!(r3.handle(&EffectOp::Io).is_none());
    }
}
