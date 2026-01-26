//! Coeffect system types
//!
//! Coeffects track what a computation REQUIRES from its environment, dual to
//! effects which track what a computation DOES to its environment.
//!
//! Based on F* Effects.fsti (synthesis_part6.tex):
//! ```text
//! (* Liveness Coeffect Algebra *)
//! L = { LDead, LLive }
//!
//! LDead + LDead = LDead
//! LDead + LLive = LLive
//! LLive + LLive = LLive
//! ```
//!
//! # Coeffect vs Effect
//!
//! - **Effect**: "This computation may write to memory" (what it DOES)
//! - **Coeffect**: "This computation needs variable x to be live" (what it NEEDS)
//!
//! # Semiring Structure
//!
//! Both `Liveness` and `Usage` form semirings with:
//! - Addition: parallel composition (alternative branches)
//! - Multiplication: sequential composition (one after another)
//!
//! # Use Cases
//!
//! 1. **Liveness analysis**: Track which variables must be live at each point
//! 2. **Usage counting**: Track how many times each variable is used
//! 3. **Resource requirements**: Track what capabilities a computation needs

use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Variable identifier (re-exported for convenience)
pub type VarId = Spur;

// ============================================================================
// Liveness Coeffect
// ============================================================================

/// Liveness coeffect - tracks whether a variable is needed (live) or not (dead).
///
/// Forms a semiring where:
/// - Addition (parallel/join): Dead + Dead = Dead, Dead + Live = Live, Live + Live = Live
/// - Multiplication (sequential): Dead * _ = Dead, Live * x = x
///
/// Maps to F*:
/// ```fstar
/// type liveness = LDead | LLive
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum Liveness {
    /// Variable is not needed (dead) - additive identity
    #[default]
    Dead = 0,
    /// Variable is needed (live) - absorbs in addition
    Live = 1,
}

impl Liveness {
    /// Semiring addition (parallel composition / join).
    ///
    /// Represents "either branch may execute" - if either branch needs
    /// the variable live, it must be live.
    ///
    /// ```text
    /// Dead + Dead = Dead
    /// Dead + Live = Live
    /// Live + Dead = Live
    /// Live + Live = Live
    /// ```
    #[must_use]
    pub const fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Dead, Self::Dead) => Self::Dead,
            _ => Self::Live,
        }
    }

    /// Semiring multiplication (sequential composition).
    ///
    /// Represents "first computation then second" - if the first
    /// computation doesn't need the variable, the result doesn't either.
    ///
    /// ```text
    /// Dead * _ = Dead  (annihilator)
    /// Live * x = x     (identity)
    /// ```
    #[must_use]
    pub const fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Dead, _) => Self::Dead,
            (Self::Live, x) => x,
        }
    }

    /// Join (least upper bound) in the liveness lattice.
    ///
    /// Dead <= Live, so join returns Live if either is Live.
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        self.add(other) // Same as semiring addition for liveness
    }

    /// Meet (greatest lower bound) in the liveness lattice.
    ///
    /// Returns Dead only if both are Dead.
    #[must_use]
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Live, Self::Live) => Self::Live,
            _ => Self::Dead,
        }
    }

    /// Check if this is the dead (not needed) state.
    #[must_use]
    pub const fn is_dead(self) -> bool {
        matches!(self, Self::Dead)
    }

    /// Check if this is the live (needed) state.
    #[must_use]
    pub const fn is_live(self) -> bool {
        matches!(self, Self::Live)
    }

    /// Subliveness relation: self <= other in the lattice (Dead <= Live).
    #[must_use]
    pub const fn subliveness(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Dead, _) | (Self::Live, Self::Live)
        )
    }

    /// Parse from text format.
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "dead" | "d" | "0" => Some(Self::Dead),
            "live" | "l" | "1" => Some(Self::Live),
            _ => None,
        }
    }

    /// Format to text.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Dead => "dead",
            Self::Live => "live",
        }
    }

    /// Unicode symbol for display.
    #[must_use]
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Dead => "\u{2205}", // Empty set symbol
            Self::Live => "\u{2713}", // Check mark
        }
    }
}

// ============================================================================
// Usage Coeffect
// ============================================================================

/// Usage coeffect - tracks how many times a variable is used.
///
/// Forms a semiring where:
/// - Zero: not used (additive identity, multiplicative annihilator)
/// - One: used exactly once (multiplicative identity)
/// - Many: used multiple times (absorbs in addition with itself)
///
/// This is dual to the Mode semiring in modes.rs but tracks requirements
/// rather than provisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum Usage {
    /// Not used - additive identity, multiplicative annihilator
    #[default]
    Zero = 0,
    /// Used exactly once - multiplicative identity
    One = 1,
    /// Used multiple times - absorbs in addition
    Many = 2,
}

impl Usage {
    /// Semiring addition (parallel composition).
    ///
    /// Represents "variable used in either/both branches".
    ///
    /// ```text
    /// Zero + x = x          (identity)
    /// One + One = Many      (used twice = many)
    /// Many + x = Many       (absorbs)
    /// ```
    #[must_use]
    pub const fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, x) | (x, Self::Zero) => x,
            (Self::Many, _) | (_, Self::Many) => Self::Many,
            (Self::One, Self::One) => Self::Many,
        }
    }

    /// Semiring multiplication (sequential composition).
    ///
    /// Represents "variable used in first, then used in second".
    ///
    /// ```text
    /// Zero * _ = Zero       (annihilator)
    /// One * x = x           (identity)
    /// Many * Many = Many
    /// ```
    #[must_use]
    pub const fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, x) | (x, Self::One) => x,
            (Self::Many, Self::Many) => Self::Many,
        }
    }

    /// Join (least upper bound) in the usage lattice.
    ///
    /// Zero <= One <= Many
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, x) | (x, Self::Zero) => x,
            (Self::Many, _) | (_, Self::Many) => Self::Many,
            (Self::One, Self::One) => Self::One,
        }
    }

    /// Meet (greatest lower bound) in the usage lattice.
    ///
    /// Zero absorbs, Many is identity.
    #[must_use]
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Many, x) | (x, Self::Many) => x,
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, Self::One) => Self::One,
        }
    }

    /// Check if this is zero usage.
    #[must_use]
    pub const fn is_zero(self) -> bool {
        matches!(self, Self::Zero)
    }

    /// Check if this is exactly one usage.
    #[must_use]
    pub const fn is_one(self) -> bool {
        matches!(self, Self::One)
    }

    /// Check if this is many usages.
    #[must_use]
    pub const fn is_many(self) -> bool {
        matches!(self, Self::Many)
    }

    /// Subusage relation: self <= other in the lattice.
    #[must_use]
    pub const fn subusage(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Zero, _) | (Self::One, Self::One | Self::Many) | (Self::Many, Self::Many)
        )
    }

    /// Parse from text format.
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "zero" | "0" | "none" => Some(Self::Zero),
            "one" | "1" | "once" => Some(Self::One),
            "many" | "n" | "omega" | "w" => Some(Self::Many),
            _ => None,
        }
    }

    /// Format to text.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::One => "one",
            Self::Many => "many",
        }
    }

    /// Unicode symbol for display.
    #[must_use]
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::Many => "\u{03C9}", // omega
        }
    }
}

// ============================================================================
// Flat Coeffects
// ============================================================================

/// Flat coeffect for whole-context properties.
///
/// Unlike structural coeffects which track per-variable information,
/// flat coeffects track global properties of what a computation needs.
///
/// Examples:
/// - "needs console access"
/// - "needs network access"
/// - "needs random number generator"
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum FlatCoeffect {
    /// No special requirements (pure computation).
    Pure,
    /// Needs console I/O access.
    Console,
    /// Needs network access.
    Network,
    /// Needs filesystem access.
    FileSystem,
    /// Needs random number generation.
    Random,
    /// Needs clock/time access.
    Clock,
    /// Needs environment variable access.
    Env,
    /// Needs specific capability (named).
    Capability(Spur),
    /// Combination of multiple flat coeffects.
    Many(Vec<FlatCoeffect>),
}

impl FlatCoeffect {
    /// Create a pure (no requirements) coeffect.
    #[must_use]
    pub const fn pure() -> Self {
        Self::Pure
    }

    /// Combine two flat coeffects.
    #[must_use]
    pub fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Pure, x) | (x, Self::Pure) => x,
            (Self::Many(mut v1), Self::Many(v2)) => {
                v1.extend(v2);
                Self::Many(v1)
            }
            (Self::Many(mut v), x) | (x, Self::Many(mut v)) => {
                v.push(x);
                Self::Many(v)
            }
            (x, y) => Self::Many(vec![x, y]),
        }
    }

    /// Check if this is pure (no requirements).
    #[must_use]
    pub const fn is_pure(&self) -> bool {
        matches!(self, Self::Pure)
    }

    /// Get discriminant for binary encoding.
    #[must_use]
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Pure => 0,
            Self::Console => 1,
            Self::Network => 2,
            Self::FileSystem => 3,
            Self::Random => 4,
            Self::Clock => 5,
            Self::Env => 6,
            Self::Capability(_) => 7,
            Self::Many(_) => 8,
        }
    }

    /// Check if this coeffect requires a specific capability.
    #[must_use]
    pub fn requires(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Pure, _) => false,
            (x, y) if x == y => true,
            (Self::Many(v), x) => v.iter().any(|c| c.requires(x)),
            _ => false,
        }
    }
}

impl Default for FlatCoeffect {
    fn default() -> Self {
        Self::Pure
    }
}

// ============================================================================
// Structural Coeffects
// ============================================================================

/// Structural coeffect - tracks per-variable coeffect information.
///
/// This is a map from variables to their coeffect annotations.
/// Generic over the coeffect type (typically `Liveness` or `Usage`).
///
/// # Example
///
/// ```text
/// { x: Live, y: Dead, z: Live }  -- x and z are needed, y is not
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StructuralCoeffect<T> {
    /// Map from variable to coeffect annotation.
    coeffects: HashMap<VarId, T>,
}

impl<T: Clone + Default> Default for StructuralCoeffect<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Default> StructuralCoeffect<T> {
    /// Create a new empty structural coeffect.
    #[must_use]
    pub fn new() -> Self {
        Self {
            coeffects: HashMap::new(),
        }
    }

    /// Create from an iterator of (VarId, T) pairs.
    pub fn from_iter(iter: impl IntoIterator<Item = (VarId, T)>) -> Self {
        Self {
            coeffects: iter.into_iter().collect(),
        }
    }

    /// Get the coeffect for a variable, or default if not present.
    #[must_use]
    pub fn get(&self, var: VarId) -> T {
        self.coeffects.get(&var).cloned().unwrap_or_default()
    }

    /// Get the coeffect for a variable, returning None if not present.
    #[must_use]
    pub fn get_opt(&self, var: VarId) -> Option<&T> {
        self.coeffects.get(&var)
    }

    /// Set the coeffect for a variable.
    pub fn set(&mut self, var: VarId, coeffect: T) {
        self.coeffects.insert(var, coeffect);
    }

    /// Remove a variable from the coeffect map.
    pub fn remove(&mut self, var: VarId) -> Option<T> {
        self.coeffects.remove(&var)
    }

    /// Check if the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.coeffects.is_empty()
    }

    /// Get the number of tracked variables.
    #[must_use]
    pub fn len(&self) -> usize {
        self.coeffects.len()
    }

    /// Iterate over all (VarId, coeffect) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&VarId, &T)> {
        self.coeffects.iter()
    }

    /// Get all tracked variable IDs.
    pub fn vars(&self) -> impl Iterator<Item = &VarId> {
        self.coeffects.keys()
    }

    /// Get the underlying map.
    #[must_use]
    pub fn as_map(&self) -> &HashMap<VarId, T> {
        &self.coeffects
    }

    /// Convert to the underlying map.
    #[must_use]
    pub fn into_map(self) -> HashMap<VarId, T> {
        self.coeffects
    }
}

impl<T: Clone + Default + PartialEq> StructuralCoeffect<T>
where
    T: Copy,
{
    /// Pointwise join of two structural coeffects.
    ///
    /// For each variable, takes the join of the two coeffects.
    /// Variables only in one map use their value directly.
    pub fn join<F>(&self, other: &Self, join_fn: F) -> Self
    where
        F: Fn(T, T) -> T,
    {
        let mut result = self.clone();
        for (&var, &coeff) in &other.coeffects {
            let current = result.get(var);
            result.set(var, join_fn(current, coeff));
        }
        result
    }

    /// Pointwise meet of two structural coeffects.
    ///
    /// For each variable present in both maps, takes the meet.
    /// Variables only in one map are excluded from the result.
    pub fn meet<F>(&self, other: &Self, meet_fn: F) -> Self
    where
        F: Fn(T, T) -> T,
    {
        let mut result = Self::new();
        for (&var, &coeff1) in &self.coeffects {
            if let Some(&coeff2) = other.coeffects.get(&var) {
                result.set(var, meet_fn(coeff1, coeff2));
            }
        }
        result
    }
}

// ============================================================================
// Coeffect Context
// ============================================================================

/// Coeffect context for liveness analysis.
///
/// Maps each variable to its liveness status at a program point.
/// This is the primary data structure for backward dataflow analysis.
pub type CoeffectCtx = HashMap<VarId, Liveness>;

/// Coeffect context for usage analysis.
///
/// Maps each variable to its usage count at a program point.
pub type UsageCtx = HashMap<VarId, Usage>;

/// Create an empty liveness context.
#[must_use]
pub fn empty_liveness_ctx() -> CoeffectCtx {
    HashMap::new()
}

/// Create an empty usage context.
#[must_use]
pub fn empty_usage_ctx() -> UsageCtx {
    HashMap::new()
}

/// Join two liveness contexts pointwise.
///
/// For backward analysis, this represents the merge at a join point.
#[must_use]
pub fn join_liveness_ctx(ctx1: &CoeffectCtx, ctx2: &CoeffectCtx) -> CoeffectCtx {
    let mut result = ctx1.clone();
    for (&var, &liveness) in ctx2 {
        let current = result.get(&var).copied().unwrap_or(Liveness::Dead);
        result.insert(var, current.join(liveness));
    }
    result
}

/// Join two usage contexts pointwise.
#[must_use]
pub fn join_usage_ctx(ctx1: &UsageCtx, ctx2: &UsageCtx) -> UsageCtx {
    let mut result = ctx1.clone();
    for (&var, &usage) in ctx2 {
        let current = result.get(&var).copied().unwrap_or(Usage::Zero);
        result.insert(var, current.join(usage));
    }
    result
}

/// Mark a variable as live in a context.
pub fn mark_live(ctx: &mut CoeffectCtx, var: VarId) {
    ctx.insert(var, Liveness::Live);
}

/// Mark a variable as dead in a context.
pub fn mark_dead(ctx: &mut CoeffectCtx, var: VarId) {
    ctx.insert(var, Liveness::Dead);
}

/// Check if a variable is live in a context.
#[must_use]
pub fn is_live(ctx: &CoeffectCtx, var: VarId) -> bool {
    ctx.get(&var).copied().unwrap_or(Liveness::Dead).is_live()
}

/// Increment usage count for a variable.
pub fn use_var(ctx: &mut UsageCtx, var: VarId) {
    let current = ctx.get(&var).copied().unwrap_or(Usage::Zero);
    ctx.insert(var, current.add(Usage::One));
}

// ============================================================================
// Semiring operations as free functions (for convenience)
// ============================================================================

/// Add two liveness values (semiring addition).
#[inline]
#[must_use]
pub const fn liveness_add(l1: Liveness, l2: Liveness) -> Liveness {
    l1.add(l2)
}

/// Multiply two liveness values (semiring multiplication).
#[inline]
#[must_use]
pub const fn liveness_mul(l1: Liveness, l2: Liveness) -> Liveness {
    l1.mul(l2)
}

/// Add two usage values (semiring addition).
#[inline]
#[must_use]
pub const fn usage_add(u1: Usage, u2: Usage) -> Usage {
    u1.add(u2)
}

/// Multiply two usage values (semiring multiplication).
#[inline]
#[must_use]
pub const fn usage_mul(u1: Usage, u2: Usage) -> Usage {
    u1.mul(u2)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Key;

    // Helper to create test VarIds
    fn var(n: usize) -> VarId {
        Spur::try_from_usize(n).unwrap()
    }

    // ========== Liveness Tests ==========

    #[test]
    fn test_liveness_semiring_add() {
        // Dead is identity
        assert_eq!(Liveness::Dead.add(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Dead.add(Liveness::Live), Liveness::Live);
        assert_eq!(Liveness::Live.add(Liveness::Dead), Liveness::Live);

        // Live absorbs
        assert_eq!(Liveness::Live.add(Liveness::Live), Liveness::Live);
    }

    #[test]
    fn test_liveness_semiring_mul() {
        // Dead annihilates
        assert_eq!(Liveness::Dead.mul(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Dead.mul(Liveness::Live), Liveness::Dead);

        // Live is identity
        assert_eq!(Liveness::Live.mul(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Live.mul(Liveness::Live), Liveness::Live);
    }

    #[test]
    fn test_liveness_semiring_laws() {
        let values = [Liveness::Dead, Liveness::Live];

        for &a in &values {
            for &b in &values {
                // Commutativity of add
                assert_eq!(a.add(b), b.add(a), "add not commutative");

                for &c in &values {
                    // Associativity of add
                    assert_eq!(
                        a.add(b).add(c),
                        a.add(b.add(c)),
                        "add not associative"
                    );
                    // Associativity of mul
                    assert_eq!(
                        a.mul(b).mul(c),
                        a.mul(b.mul(c)),
                        "mul not associative"
                    );
                }
            }
        }

        // Identity laws
        for &x in &values {
            assert_eq!(Liveness::Dead.add(x), x, "Dead not additive identity");
            assert_eq!(x.add(Liveness::Dead), x, "Dead not additive identity");
        }

        // Annihilator law
        for &x in &values {
            assert_eq!(Liveness::Dead.mul(x), Liveness::Dead, "Dead not annihilator");
        }
    }

    #[test]
    fn test_liveness_lattice() {
        // Join
        assert_eq!(Liveness::Dead.join(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Dead.join(Liveness::Live), Liveness::Live);
        assert_eq!(Liveness::Live.join(Liveness::Dead), Liveness::Live);
        assert_eq!(Liveness::Live.join(Liveness::Live), Liveness::Live);

        // Meet
        assert_eq!(Liveness::Dead.meet(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Dead.meet(Liveness::Live), Liveness::Dead);
        assert_eq!(Liveness::Live.meet(Liveness::Dead), Liveness::Dead);
        assert_eq!(Liveness::Live.meet(Liveness::Live), Liveness::Live);

        // Subliveness
        assert!(Liveness::Dead.subliveness(Liveness::Dead));
        assert!(Liveness::Dead.subliveness(Liveness::Live));
        assert!(!Liveness::Live.subliveness(Liveness::Dead));
        assert!(Liveness::Live.subliveness(Liveness::Live));
    }

    #[test]
    fn test_liveness_parsing() {
        assert_eq!(Liveness::from_str("dead"), Some(Liveness::Dead));
        assert_eq!(Liveness::from_str("DEAD"), Some(Liveness::Dead));
        assert_eq!(Liveness::from_str("d"), Some(Liveness::Dead));
        assert_eq!(Liveness::from_str("0"), Some(Liveness::Dead));
        assert_eq!(Liveness::from_str("live"), Some(Liveness::Live));
        assert_eq!(Liveness::from_str("LIVE"), Some(Liveness::Live));
        assert_eq!(Liveness::from_str("l"), Some(Liveness::Live));
        assert_eq!(Liveness::from_str("1"), Some(Liveness::Live));
        assert_eq!(Liveness::from_str("invalid"), None);
    }

    // ========== Usage Tests ==========

    #[test]
    fn test_usage_semiring_add() {
        // Zero is identity
        assert_eq!(Usage::Zero.add(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::Zero.add(Usage::One), Usage::One);
        assert_eq!(Usage::Zero.add(Usage::Many), Usage::Many);
        assert_eq!(Usage::One.add(Usage::Zero), Usage::One);
        assert_eq!(Usage::Many.add(Usage::Zero), Usage::Many);

        // One + One = Many
        assert_eq!(Usage::One.add(Usage::One), Usage::Many);

        // Many absorbs
        assert_eq!(Usage::Many.add(Usage::One), Usage::Many);
        assert_eq!(Usage::One.add(Usage::Many), Usage::Many);
        assert_eq!(Usage::Many.add(Usage::Many), Usage::Many);
    }

    #[test]
    fn test_usage_semiring_mul() {
        // Zero annihilates
        assert_eq!(Usage::Zero.mul(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::Zero.mul(Usage::One), Usage::Zero);
        assert_eq!(Usage::Zero.mul(Usage::Many), Usage::Zero);
        assert_eq!(Usage::One.mul(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::Many.mul(Usage::Zero), Usage::Zero);

        // One is identity
        assert_eq!(Usage::One.mul(Usage::One), Usage::One);
        assert_eq!(Usage::One.mul(Usage::Many), Usage::Many);
        assert_eq!(Usage::Many.mul(Usage::One), Usage::Many);

        // Many * Many = Many
        assert_eq!(Usage::Many.mul(Usage::Many), Usage::Many);
    }

    #[test]
    fn test_usage_semiring_laws() {
        let values = [Usage::Zero, Usage::One, Usage::Many];

        for &a in &values {
            for &b in &values {
                // Commutativity of add
                assert_eq!(a.add(b), b.add(a), "add not commutative: {a:?}, {b:?}");
                // Commutativity of mul
                assert_eq!(a.mul(b), b.mul(a), "mul not commutative: {a:?}, {b:?}");

                for &c in &values {
                    // Associativity of add
                    assert_eq!(
                        a.add(b).add(c),
                        a.add(b.add(c)),
                        "add not associative: {a:?}, {b:?}, {c:?}"
                    );
                    // Associativity of mul
                    assert_eq!(
                        a.mul(b).mul(c),
                        a.mul(b.mul(c)),
                        "mul not associative: {a:?}, {b:?}, {c:?}"
                    );
                    // Left distributivity
                    assert_eq!(
                        a.mul(b.add(c)),
                        a.mul(b).add(a.mul(c)),
                        "left distributivity failed: {a:?}, {b:?}, {c:?}"
                    );
                    // Right distributivity
                    assert_eq!(
                        a.add(b).mul(c),
                        a.mul(c).add(b.mul(c)),
                        "right distributivity failed: {a:?}, {b:?}, {c:?}"
                    );
                }
            }
        }

        // Identity laws
        for &m in &values {
            assert_eq!(Usage::Zero.add(m), m, "Zero not additive identity");
            assert_eq!(m.add(Usage::Zero), m, "Zero not additive identity");
            assert_eq!(Usage::One.mul(m), m, "One not multiplicative identity");
            assert_eq!(m.mul(Usage::One), m, "One not multiplicative identity");
        }

        // Annihilator law
        for &m in &values {
            assert_eq!(Usage::Zero.mul(m), Usage::Zero, "Zero not annihilator");
            assert_eq!(m.mul(Usage::Zero), Usage::Zero, "Zero not annihilator");
        }
    }

    #[test]
    fn test_usage_lattice() {
        // Join: Zero <= One <= Many
        assert_eq!(Usage::Zero.join(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::Zero.join(Usage::One), Usage::One);
        assert_eq!(Usage::Zero.join(Usage::Many), Usage::Many);
        assert_eq!(Usage::One.join(Usage::One), Usage::One);
        assert_eq!(Usage::One.join(Usage::Many), Usage::Many);
        assert_eq!(Usage::Many.join(Usage::Many), Usage::Many);

        // Meet
        assert_eq!(Usage::Many.meet(Usage::Many), Usage::Many);
        assert_eq!(Usage::Many.meet(Usage::One), Usage::One);
        assert_eq!(Usage::Many.meet(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::One.meet(Usage::One), Usage::One);
        assert_eq!(Usage::One.meet(Usage::Zero), Usage::Zero);
        assert_eq!(Usage::Zero.meet(Usage::Zero), Usage::Zero);

        // Subusage
        assert!(Usage::Zero.subusage(Usage::Zero));
        assert!(Usage::Zero.subusage(Usage::One));
        assert!(Usage::Zero.subusage(Usage::Many));
        assert!(!Usage::One.subusage(Usage::Zero));
        assert!(Usage::One.subusage(Usage::One));
        assert!(Usage::One.subusage(Usage::Many));
        assert!(!Usage::Many.subusage(Usage::Zero));
        assert!(!Usage::Many.subusage(Usage::One));
        assert!(Usage::Many.subusage(Usage::Many));
    }

    #[test]
    fn test_usage_parsing() {
        assert_eq!(Usage::from_str("zero"), Some(Usage::Zero));
        assert_eq!(Usage::from_str("0"), Some(Usage::Zero));
        assert_eq!(Usage::from_str("one"), Some(Usage::One));
        assert_eq!(Usage::from_str("1"), Some(Usage::One));
        assert_eq!(Usage::from_str("many"), Some(Usage::Many));
        assert_eq!(Usage::from_str("omega"), Some(Usage::Many));
        assert_eq!(Usage::from_str("invalid"), None);
    }

    // ========== FlatCoeffect Tests ==========

    #[test]
    fn test_flat_coeffect_combine() {
        let pure = FlatCoeffect::Pure;
        let console = FlatCoeffect::Console;
        let network = FlatCoeffect::Network;

        // Pure is identity
        assert_eq!(pure.clone().combine(console.clone()), console);
        assert_eq!(console.clone().combine(pure.clone()), console);

        // Combining non-pure creates Many
        let combined = console.clone().combine(network.clone());
        assert!(matches!(combined, FlatCoeffect::Many(_)));
    }

    #[test]
    fn test_flat_coeffect_requires() {
        let console = FlatCoeffect::Console;
        let many = FlatCoeffect::Many(vec![FlatCoeffect::Console, FlatCoeffect::Network]);

        assert!(many.requires(&console));
        assert!(!console.requires(&FlatCoeffect::Network));
        assert!(!FlatCoeffect::Pure.requires(&console));
    }

    // ========== StructuralCoeffect Tests ==========

    #[test]
    fn test_structural_coeffect_basic() {
        let mut sc: StructuralCoeffect<Liveness> = StructuralCoeffect::new();

        let x = var(1);
        let y = var(2);

        sc.set(x, Liveness::Live);
        sc.set(y, Liveness::Dead);

        assert_eq!(sc.get(x), Liveness::Live);
        assert_eq!(sc.get(y), Liveness::Dead);
        assert_eq!(sc.get(var(99)), Liveness::Dead); // Default

        assert_eq!(sc.len(), 2);
        assert!(!sc.is_empty());
    }

    #[test]
    fn test_structural_coeffect_join() {
        let mut sc1: StructuralCoeffect<Liveness> = StructuralCoeffect::new();
        let mut sc2: StructuralCoeffect<Liveness> = StructuralCoeffect::new();

        let x = var(1);
        let y = var(2);
        let z = var(3);

        sc1.set(x, Liveness::Live);
        sc1.set(y, Liveness::Dead);

        sc2.set(y, Liveness::Live);
        sc2.set(z, Liveness::Live);

        let joined = sc1.join(&sc2, Liveness::join);

        assert_eq!(joined.get(x), Liveness::Live);
        assert_eq!(joined.get(y), Liveness::Live); // Dead join Live = Live
        assert_eq!(joined.get(z), Liveness::Live);
    }

    #[test]
    fn test_structural_coeffect_meet() {
        let mut sc1: StructuralCoeffect<Liveness> = StructuralCoeffect::new();
        let mut sc2: StructuralCoeffect<Liveness> = StructuralCoeffect::new();

        let x = var(1);
        let y = var(2);

        sc1.set(x, Liveness::Live);
        sc1.set(y, Liveness::Dead);

        sc2.set(x, Liveness::Live);
        sc2.set(y, Liveness::Live);

        let met = sc1.meet(&sc2, Liveness::meet);

        assert_eq!(met.get(x), Liveness::Live);
        assert_eq!(met.get(y), Liveness::Dead); // Dead meet Live = Dead
    }

    // ========== Context Tests ==========

    #[test]
    fn test_liveness_context() {
        let mut ctx = empty_liveness_ctx();
        let x = var(1);
        let y = var(2);

        mark_live(&mut ctx, x);
        mark_dead(&mut ctx, y);

        assert!(is_live(&ctx, x));
        assert!(!is_live(&ctx, y));
        assert!(!is_live(&ctx, var(99))); // Not in context
    }

    #[test]
    fn test_join_liveness_ctx() {
        let mut ctx1 = empty_liveness_ctx();
        let mut ctx2 = empty_liveness_ctx();

        let x = var(1);
        let y = var(2);
        let z = var(3);

        mark_live(&mut ctx1, x);
        mark_dead(&mut ctx1, y);

        mark_dead(&mut ctx2, x);
        mark_live(&mut ctx2, y);
        mark_live(&mut ctx2, z);

        let joined = join_liveness_ctx(&ctx1, &ctx2);

        assert!(is_live(&joined, x)); // Live join Dead = Live
        assert!(is_live(&joined, y)); // Dead join Live = Live
        assert!(is_live(&joined, z)); // Only in ctx2, but Live
    }

    #[test]
    fn test_usage_context() {
        let mut ctx = empty_usage_ctx();
        let x = var(1);

        use_var(&mut ctx, x);
        assert_eq!(ctx.get(&x).copied(), Some(Usage::One));

        use_var(&mut ctx, x);
        assert_eq!(ctx.get(&x).copied(), Some(Usage::Many));

        use_var(&mut ctx, x);
        assert_eq!(ctx.get(&x).copied(), Some(Usage::Many)); // Stays Many
    }

    // ========== Free Function Tests ==========

    #[test]
    fn test_free_functions() {
        assert_eq!(liveness_add(Liveness::Dead, Liveness::Live), Liveness::Live);
        assert_eq!(liveness_mul(Liveness::Dead, Liveness::Live), Liveness::Dead);
        assert_eq!(usage_add(Usage::One, Usage::One), Usage::Many);
        assert_eq!(usage_mul(Usage::One, Usage::Many), Usage::Many);
    }
}
