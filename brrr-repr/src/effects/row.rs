//! Effect rows for tracking combined effects
//!
//! An effect row represents the set of effects a computation may perform.

use serde::{Deserialize, Serialize};
use super::ops::EffectOp;

/// Pure effect row constant
pub const PURE: EffectRow = EffectRow {
    ops: Vec::new(),
    open: false,
};

/// Effect row - a set of effect operations
///
/// Effect rows form a lattice:
/// - Bottom: `Pure` (no effects)
/// - Top: `Total` (all effects possible)
/// - Join: union of effects
/// - Meet: intersection of effects
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct EffectRow {
    /// Effect operations in this row (sorted by discriminant, deduplicated)
    ops: Vec<EffectOp>,
    /// Whether this row is open (can be extended with more effects)
    open: bool,
}

impl EffectRow {
    /// Pure effect row constant
    pub const PURE: Self = Self {
        ops: Vec::new(),
        open: false,
    };

    /// Empty effect row (pure) - function version
    pub const fn pure() -> Self {
        Self {
            ops: Vec::new(),
            open: false,
        }
    }

    /// Create a new effect row with the given operations
    pub fn new(mut ops: Vec<EffectOp>) -> Self {
        ops.sort_by_key(|op| op.discriminant());
        ops.dedup_by(|a, b| a.discriminant() == b.discriminant());
        Self { ops, open: false }
    }

    /// Create an open effect row (can have additional effects)
    pub fn open(mut ops: Vec<EffectOp>) -> Self {
        ops.sort_by_key(|op| op.discriminant());
        ops.dedup_by(|a, b| a.discriminant() == b.discriminant());
        Self { ops, open: true }
    }

    /// Create a row with a single effect
    pub fn single(op: EffectOp) -> Self {
        Self {
            ops: vec![op],
            open: false,
        }
    }

    /// Total effects (everything possible)
    pub fn total() -> Self {
        Self {
            ops: Vec::new(),
            open: true,
        }
    }

    /// Check if this row is pure (no effects)
    pub fn is_pure(&self) -> bool {
        self.ops.is_empty() && !self.open
    }

    /// Check if this row is open
    pub fn is_open(&self) -> bool {
        self.open
    }

    /// Check if this row contains a specific effect (by discriminant)
    pub fn contains(&self, op: &EffectOp) -> bool {
        let disc = op.discriminant();
        self.ops.binary_search_by_key(&disc, |o| o.discriminant()).is_ok()
    }

    /// Check if this row contains an effect with the given discriminant
    pub fn contains_discriminant(&self, disc: u8) -> bool {
        self.ops.binary_search_by_key(&disc, |o| o.discriminant()).is_ok()
    }

    /// Get the operations in this row
    pub fn ops(&self) -> &[EffectOp] {
        &self.ops
    }

    /// Join two effect rows (union)
    pub fn join(&self, other: &Self) -> Self {
        let mut ops = self.ops.clone();
        for op in &other.ops {
            if !self.contains(op) {
                ops.push(op.clone());
            }
        }
        ops.sort_by_key(|op| op.discriminant());
        Self {
            ops,
            open: self.open || other.open,
        }
    }

    /// Meet two effect rows (intersection)
    pub fn meet(&self, other: &Self) -> Self {
        let ops: Vec<_> = self.ops.iter()
            .filter(|op| other.contains(op))
            .cloned()
            .collect();
        Self {
            ops,
            open: self.open && other.open,
        }
    }

    /// Check if this row is a subrow of another (all effects in self are in other)
    pub fn is_subrow_of(&self, other: &Self) -> bool {
        if other.open {
            return true;
        }
        if self.open && !other.open {
            return false;
        }
        self.ops.iter().all(|op| other.contains(op))
    }

    /// Add an effect to this row
    pub fn add(&mut self, op: EffectOp) {
        if !self.contains(&op) {
            self.ops.push(op);
            self.ops.sort_by_key(|o| o.discriminant());
        }
    }

    /// Number of effects in this row
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Check if empty (not necessarily pure - could be open)
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Format the effect row as a string
    pub fn format(&self) -> String {
        if self.ops.is_empty() {
            if self.open {
                return "...".to_string();
            } else {
                return "Pure".to_string();
            }
        }

        let effects: Vec<String> = self.ops.iter()
            .map(|op| op.as_symbol())
            .collect();

        if self.open {
            format!("{{{},...}}", effects.join(", "))
        } else {
            format!("{{{}}}", effects.join(", "))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pure() {
        let row = EffectRow::pure();
        assert!(row.is_pure());
        assert!(!row.is_open());
    }

    #[test]
    fn test_single() {
        let row = EffectRow::single(EffectOp::ReadSimple);
        assert!(!row.is_pure());
        assert!(row.contains(&EffectOp::ReadSimple));
        assert!(!row.contains(&EffectOp::WriteSimple));
    }

    #[test]
    fn test_join() {
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let row2 = EffectRow::single(EffectOp::WriteSimple);
        let joined = row1.join(&row2);
        assert!(joined.contains(&EffectOp::ReadSimple));
        assert!(joined.contains(&EffectOp::WriteSimple));
    }

    #[test]
    fn test_subrow() {
        let row1 = EffectRow::single(EffectOp::ReadSimple);
        let row2 = EffectRow::new(vec![EffectOp::ReadSimple, EffectOp::WriteSimple]);
        assert!(row1.is_subrow_of(&row2));
        assert!(!row2.is_subrow_of(&row1));
    }

    #[test]
    fn test_format() {
        let pure = EffectRow::pure();
        assert_eq!(pure.format(), "Pure");

        let row = EffectRow::single(EffectOp::Io);
        assert_eq!(row.format(), "{IO}");

        let open = EffectRow::total();
        assert_eq!(open.format(), "...");
    }
}
