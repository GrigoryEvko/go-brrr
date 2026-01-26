//! Mode (linearity) and permission types
//!
//! Mirrors F* Modes.fsti: mode, ref_kind, fraction
//!
//! The mode semiring has three elements forming a lattice Zero <= One <= Omega:
//! - Zero: consumed/absent - additive identity, multiplicative annihilator
//! - One: linear - exactly once - multiplicative identity
//! - Omega: unrestricted - any number of times
//!
//! Semiring laws:
//! - Addition (parallel): 0 + m = m, 1 + 1 = omega, omega + m = omega
//! - Multiplication (sequential): 0 * m = 0, 1 * m = m, omega * omega = omega

use lasso::Spur;
use serde::{Deserialize, Serialize};

/// Variable identifier (interned string key)
pub type VarId = Spur;

/// Usage mode - linear typing with mode semiring
/// Maps to F*: type mode = MZero | MOne | MOmega
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum Mode {
    /// Consumed/absent - `@0` - additive identity, multiplicative annihilator
    Zero = 0,
    /// Use exactly once (linear) - `@1` or `@lin`
    One = 1,
    /// Use any number of times (unrestricted) - `@omega` or `@unr`
    #[default]
    Omega = 2,
}

impl Mode {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "0" | "zero" => Some(Self::Zero),
            "1" | "one" | "lin" | "linear" => Some(Self::One),
            "omega" | "w" | "unr" | "unrestricted" => Some(Self::Omega),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::Omega => "omega",
        }
    }

    /// Format with full name
    pub const fn as_name(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::One => "linear",
            Self::Omega => "unrestricted",
        }
    }

    /// Join (least upper bound) in the mode lattice
    /// Zero is bottom, Omega is top: Zero <= One <= Omega
    /// Zero join m = m, One join One = One, Omega join m = Omega
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, m) | (m, Self::Zero) => m,
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::One, Self::One) => Self::One,
        }
    }

    /// Meet (greatest lower bound) in the mode lattice
    /// Zero absorbs, Omega is identity: Zero <= One <= Omega
    /// Zero meet m = Zero, Omega meet m = m, One meet One = One
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Omega, m) | (m, Self::Omega) => m,
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, Self::One) => Self::One,
        }
    }

    /// Submode relation: self <= other in the lattice Zero <= One <= Omega
    pub const fn submode(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Zero, _) | (Self::One, Self::One | Self::Omega) | (Self::Omega, Self::Omega)
        )
    }

    /// Mode multiplication (for sequential composition)
    /// Zero annihilates: 0 * m = 0
    /// One is identity: 1 * m = m
    /// Omega * Omega = Omega
    pub const fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, m) | (m, Self::One) => m,
            (Self::Omega, Self::Omega) => Self::Omega,
        }
    }

    /// Mode addition (for parallel composition)
    /// Zero is identity: 0 + m = m
    /// One + One = Omega (using twice means unrestricted)
    /// Omega absorbs: Omega + m = Omega
    pub const fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Zero, m) | (m, Self::Zero) => m,
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::One, Self::One) => Self::Omega,
        }
    }

    /// Check if this is the zero mode (consumed/absent)
    pub const fn is_zero(self) -> bool {
        matches!(self, Self::Zero)
    }

    /// Check if this is the one mode (linear)
    pub const fn is_one(self) -> bool {
        matches!(self, Self::One)
    }

    /// Check if this is the omega mode (unrestricted)
    pub const fn is_omega(self) -> bool {
        matches!(self, Self::Omega)
    }
}

/// Reference kind for fractional permissions
/// Maps to F*: type ref_kind = RkShared fraction | RkExclusive
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RefKind {
    /// Permission fraction: 0 = none, 255 = full (1/1)
    /// Encoded as numerator where denominator is 256
    /// e.g., 128 = 1/2 permission, 64 = 1/4 permission
    pub permission: u8,
}

impl RefKind {
    /// Full permission (1/1)
    pub const FULL: Self = Self { permission: 255 };

    /// Half permission (1/2)
    pub const HALF: Self = Self { permission: 128 };

    /// Quarter permission (1/4)
    pub const QUARTER: Self = Self { permission: 64 };

    /// No permission (0)
    pub const NONE: Self = Self { permission: 0 };

    /// Create from fraction numerator/denominator
    pub fn from_fraction(num: u32, den: u32) -> Self {
        if den == 0 {
            return Self::NONE;
        }
        let permission = ((num as u64 * 255) / den as u64).min(255) as u8;
        Self { permission }
    }

    /// Get as fraction (numerator, denominator)
    pub const fn as_fraction(self) -> (u8, u8) {
        // Simplify common fractions
        match self.permission {
            255 => (1, 1),
            128 => (1, 2),
            64 => (1, 4),
            32 => (1, 8),
            0 => (0, 1),
            p => (p, 255),
        }
    }

    /// Split permission in half
    pub const fn split(self) -> Self {
        Self {
            permission: self.permission / 2,
        }
    }

    /// Join two permissions (requires they sum to at most full)
    pub const fn join(self, other: Self) -> Option<Self> {
        let sum = self.permission as u16 + other.permission as u16;
        if sum <= 255 {
            Some(Self {
                permission: sum as u8,
            })
        } else {
            None
        }
    }

    /// Is this full permission?
    pub const fn is_full(self) -> bool {
        self.permission == 255
    }

    /// Is this no permission?
    pub const fn is_none(self) -> bool {
        self.permission == 0
    }

    /// Format as fraction string
    pub fn as_str(&self) -> String {
        let (num, den) = self.as_fraction();
        if den == 1 {
            format!("{num}")
        } else {
            format!("{num}/{den}")
        }
    }
}

impl Default for RefKind {
    fn default() -> Self {
        Self::FULL
    }
}

/// Extended mode for more precise linearity tracking
/// Maps to F*: type extended_mode = EMLinear | EMAffine | EMRelevant | EMUnrestricted
///
/// The lattice structure (different from base Mode):
/// ```text
///     Unrestricted (both weakening + contraction)
///        /      \
///    Affine    Relevant
///    (weak)    (contract)
///        \      /
///         Linear (neither)
/// ```
///
/// Note: ExtendedMode captures structural rules, while Mode is the underlying
/// usage count. Affine/Relevant map to Mode::One since they still require
/// at most one/at least one use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum ExtendedMode {
    /// Use exactly once - no weakening, no contraction
    /// Must be used precisely once: cannot drop, cannot duplicate
    Linear = 0,
    /// Use at most once - weakening allowed (can drop)
    /// Can be used 0 or 1 times, but not more
    Affine = 1,
    /// Use at least once - contraction allowed (can duplicate)
    /// Must be used 1 or more times, cannot be dropped
    Relevant = 2,
    /// Use any number of times - both weakening and contraction allowed
    /// Can be used 0, 1, or many times
    Unrestricted = 3,
}

impl ExtendedMode {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "lin" | "linear" => Some(Self::Linear),
            "aff" | "affine" => Some(Self::Affine),
            "rel" | "relevant" => Some(Self::Relevant),
            "unr" | "unrestricted" => Some(Self::Unrestricted),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Linear => "linear",
            Self::Affine => "affine",
            Self::Relevant => "relevant",
            Self::Unrestricted => "unrestricted",
        }
    }

    /// Short format
    pub const fn as_short(self) -> &'static str {
        match self {
            Self::Linear => "lin",
            Self::Affine => "aff",
            Self::Relevant => "rel",
            Self::Unrestricted => "unr",
        }
    }

    /// Allows weakening (can drop without using)?
    pub const fn allows_weakening(self) -> bool {
        matches!(self, Self::Affine | Self::Unrestricted)
    }

    /// Allows contraction (can use multiple times)?
    pub const fn allows_contraction(self) -> bool {
        matches!(self, Self::Relevant | Self::Unrestricted)
    }

    /// Convert to base Mode
    /// Linear/Affine/Relevant all map to One (single use tracking)
    /// Only Unrestricted maps to Omega
    pub const fn to_mode(self) -> Mode {
        match self {
            Self::Linear => Mode::One,
            Self::Affine => Mode::One, // Affine still requires tracking single use
            Self::Relevant => Mode::One, // Relevant must use at least once
            Self::Unrestricted => Mode::Omega,
        }
    }

    /// Convert base mode to most general compatible extended mode
    ///
    /// - Zero: Affine (can be dropped - zero uses allowed)
    /// - One: Linear (exact usage)
    /// - Omega: Unrestricted (any usage)
    pub const fn from_mode(mode: Mode) -> Self {
        match mode {
            Mode::Zero => Self::Affine, // Zero means "can be dropped"
            Mode::One => Self::Linear, // Exact usage
            Mode::Omega => Self::Unrestricted,
        }
    }

    /// Check if a transition to target mode is valid
    ///
    /// - Linear: can only stay at One (must use exactly once)
    /// - Affine: can go to Zero (weakening) or stay at One
    /// - Relevant: can stay at One or go to Omega (contraction)
    /// - Unrestricted: can transition to any mode
    pub const fn can_transition(self, target: Mode) -> bool {
        match (self, target) {
            // Linear: exactly once - only One is valid
            (Self::Linear, Mode::One) => true,

            // Affine: at most once - Zero (dropped) or One allowed
            (Self::Affine, Mode::Zero) => true,
            (Self::Affine, Mode::One) => true,

            // Relevant: at least once - One or Omega (duplicated)
            (Self::Relevant, Mode::One) => true,
            (Self::Relevant, Mode::Omega) => true,

            // Unrestricted: any transition valid
            (Self::Unrestricted, _) => true,

            _ => false,
        }
    }

    /// Join two extended modes (least upper bound in the lattice)
    ///
    /// The lattice has Unrestricted at top, Linear at bottom:
    /// - Linear join X = X (for any X)
    /// - Affine join Relevant = Unrestricted
    /// - Unrestricted join X = Unrestricted
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            // Linear is bottom
            (Self::Linear, x) | (x, Self::Linear) => x,

            // Unrestricted is top
            (Self::Unrestricted, _) | (_, Self::Unrestricted) => Self::Unrestricted,

            // Same modes
            (Self::Affine, Self::Affine) => Self::Affine,
            (Self::Relevant, Self::Relevant) => Self::Relevant,

            // Affine + Relevant = Unrestricted (both properties needed)
            (Self::Affine, Self::Relevant) | (Self::Relevant, Self::Affine) => Self::Unrestricted,
        }
    }

    /// Meet two extended modes (greatest lower bound in the lattice)
    ///
    /// - Linear meet X = Linear (for any X)
    /// - Unrestricted meet X = X
    /// - Affine meet Relevant = Linear
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            // Linear is bottom
            (Self::Linear, _) | (_, Self::Linear) => Self::Linear,

            // Unrestricted is top
            (Self::Unrestricted, x) | (x, Self::Unrestricted) => x,

            // Same modes
            (Self::Affine, Self::Affine) => Self::Affine,
            (Self::Relevant, Self::Relevant) => Self::Relevant,

            // Affine meet Relevant = Linear (must satisfy both constraints)
            (Self::Affine, Self::Relevant) | (Self::Relevant, Self::Affine) => Self::Linear,
        }
    }
}

impl Default for ExtendedMode {
    fn default() -> Self {
        Self::Unrestricted
    }
}

// ============================================================================
// MODE CONTEXT - Chapter 8: Consumption Tracking
// Maps to F* Modes.fst lines 380-519
// ============================================================================

/// Entry in a mode context tracking a variable's usage mode
/// Maps to F*: type mode_ctx_entry = string & mode & extended_mode
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModeCtxEntry {
    /// Variable identifier
    pub var: VarId,
    /// Current usage mode (tracks consumption state)
    pub mode: Mode,
    /// Extended mode (tracks structural rules: weakening/contraction)
    pub extended: ExtendedMode,
}

impl ModeCtxEntry {
    /// Create a new mode context entry
    pub fn new(var: VarId, mode: Mode, extended: ExtendedMode) -> Self {
        Self { var, mode, extended }
    }

    /// Check if this entry is valid (mode consistent with extended mode)
    /// Maps to F*: valid_mode_ctx_entry
    pub fn is_valid(&self) -> bool {
        match self.extended {
            ExtendedMode::Linear | ExtendedMode::Affine => {
                self.mode == Mode::One || self.mode == Mode::Zero
            }
            ExtendedMode::Relevant | ExtendedMode::Unrestricted => true,
        }
    }
}

/// Mode context for tracking variable usage in linear type checking
/// Maps to F*: type mode_ctx = list mode_ctx_entry
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModeCtx {
    entries: Vec<ModeCtxEntry>,
}

impl ModeCtx {
    /// Create an empty mode context
    /// Maps to F*: empty_mode_ctx
    #[must_use]
    pub fn empty() -> Self {
        Self { entries: Vec::new() }
    }

    /// Create a mode context with given capacity
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Number of entries in the context
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if context is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over entries
    pub fn iter(&self) -> impl Iterator<Item = &ModeCtxEntry> {
        self.entries.iter()
    }

    /// Lookup mode and extended_mode of a variable
    /// Maps to F*: lookup_mode
    ///
    /// Returns (MZero, EMUnrestricted) if variable not found
    #[must_use]
    pub fn lookup(&self, var: VarId) -> (Mode, ExtendedMode) {
        for entry in &self.entries {
            if entry.var == var {
                return (entry.mode, entry.extended);
            }
        }
        (Mode::Zero, ExtendedMode::Unrestricted)
    }

    /// Lookup just the mode
    /// Maps to F*: lookup_mode_only
    #[must_use]
    pub fn lookup_mode(&self, var: VarId) -> Mode {
        self.lookup(var).0
    }

    /// Lookup just the extended_mode
    /// Maps to F*: lookup_extended_mode
    #[must_use]
    pub fn lookup_extended(&self, var: VarId) -> ExtendedMode {
        self.lookup(var).1
    }

    /// Update mode of variable while preserving extended_mode
    /// Maps to F*: update_mode
    pub fn update_mode(&mut self, var: VarId, mode: Mode) {
        for entry in &mut self.entries {
            if entry.var == var {
                entry.mode = mode;
                return;
            }
        }
        self.entries.push(ModeCtxEntry {
            var,
            mode,
            extended: ExtendedMode::Unrestricted,
        });
    }

    /// Update mode and return new context (functional style)
    #[must_use]
    pub fn with_mode(&self, var: VarId, mode: Mode) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.update_mode(var, mode);
        new_ctx
    }

    /// Update both mode and extended_mode of variable
    /// Maps to F*: update_mode_full
    pub fn update_full(&mut self, var: VarId, mode: Mode, extended: ExtendedMode) {
        for entry in &mut self.entries {
            if entry.var == var {
                entry.mode = mode;
                entry.extended = extended;
                return;
            }
        }
        self.entries.push(ModeCtxEntry { var, mode, extended });
    }

    /// Update both mode and extended_mode (functional style)
    #[must_use]
    pub fn with_full(&self, var: VarId, mode: Mode, extended: ExtendedMode) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.update_full(var, mode, extended);
        new_ctx
    }

    /// Add a new variable to context (prepends for shadowing)
    /// Maps to F*: extend_mode_ctx
    pub fn extend(&mut self, var: VarId, mode: Mode, extended: ExtendedMode) {
        self.entries.insert(0, ModeCtxEntry { var, mode, extended });
    }

    /// Extend context (functional style)
    #[must_use]
    pub fn with_extend(&self, var: VarId, mode: Mode, extended: ExtendedMode) -> Self {
        let mut new_ctx = self.clone();
        new_ctx.extend(var, mode, extended);
        new_ctx
    }

    /// Consume a linear variable: 1 -> 0
    /// Maps to F*: consume
    ///
    /// Returns None if already consumed (MZero).
    /// MOne: decrements to MZero
    /// MOmega: no change
    #[must_use]
    pub fn consume(&self, var: VarId) -> Option<Self> {
        let (mode, _) = self.lookup(var);
        match mode {
            Mode::Zero => None,
            Mode::One => Some(self.with_mode(var, Mode::Zero)),
            Mode::Omega => Some(self.clone()),
        }
    }

    /// Split context for parallel composition (L-App rule)
    /// Maps to F*: split_ctx
    ///
    /// MOmega: both branches get it
    /// MOne: left gets it, right gets MZero
    /// MZero: both get MZero
    #[must_use]
    pub fn split(&self) -> (Self, Self) {
        let mut left = Vec::with_capacity(self.entries.len());
        let mut right = Vec::with_capacity(self.entries.len());

        for entry in &self.entries {
            match entry.mode {
                Mode::Omega => {
                    left.push(entry.clone());
                    right.push(entry.clone());
                }
                Mode::One => {
                    left.push(entry.clone());
                    right.push(ModeCtxEntry {
                        var: entry.var,
                        mode: Mode::Zero,
                        extended: entry.extended,
                    });
                }
                Mode::Zero => {
                    left.push(entry.clone());
                    right.push(entry.clone());
                }
            }
        }

        (Self { entries: left }, Self { entries: right })
    }

    /// Join contexts after branches
    /// Maps to F*: join_ctx
    ///
    /// Mode is joined (least upper bound), extended_mode from self.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let entries = self
            .entries
            .iter()
            .map(|entry| {
                let other_mode = other.lookup_mode(entry.var);
                ModeCtxEntry {
                    var: entry.var,
                    mode: entry.mode.join(other_mode),
                    extended: entry.extended,
                }
            })
            .collect();

        Self { entries }
    }

    /// Check if variable can be weakened (dropped)
    #[must_use]
    pub fn can_weaken(&self, var: VarId) -> bool {
        self.lookup_extended(var).allows_weakening()
    }

    /// Check if variable can be contracted (duplicated)
    #[must_use]
    pub fn can_contract(&self, var: VarId) -> bool {
        self.lookup_extended(var).allows_contraction()
    }

    /// Contract a variable (change to MOmega)
    /// Maps to F*: contract_mode_ctx
    #[must_use]
    pub fn contract(&self, var: VarId) -> Option<Self> {
        if !self.can_contract(var) {
            return None;
        }
        let (mode, _) = self.lookup(var);
        if mode == Mode::Zero {
            return None;
        }
        Some(self.with_mode(var, Mode::Omega))
    }

    /// Check if all entries are valid
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.entries.iter().all(ModeCtxEntry::is_valid)
    }

    /// Check for duplicate variable names
    #[must_use]
    pub fn has_no_duplicates(&self) -> bool {
        let mut seen = std::collections::HashSet::new();
        self.entries.iter().all(|e| seen.insert(e.var))
    }

    /// Check well-formedness
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        self.has_no_duplicates() && self.is_valid()
    }

    /// Check if all linear resources are fully consumed
    #[must_use]
    pub fn is_fully_consumed(&self) -> bool {
        self.entries.iter().all(|entry| match entry.extended {
            ExtendedMode::Linear => entry.mode == Mode::Zero,
            ExtendedMode::Relevant => entry.mode == Mode::Zero || entry.mode == Mode::Omega,
            ExtendedMode::Affine | ExtendedMode::Unrestricted => true,
        })
    }

    /// Count variables with MOne mode
    #[must_use]
    pub fn count_linear(&self) -> usize {
        self.entries.iter().filter(|e| e.mode == Mode::One).count()
    }

    /// Count variables with MOmega mode
    #[must_use]
    pub fn count_unrestricted(&self) -> usize {
        self.entries.iter().filter(|e| e.mode == Mode::Omega).count()
    }

    /// Count variables with MZero mode
    #[must_use]
    pub fn count_consumed(&self) -> usize {
        self.entries.iter().filter(|e| e.mode == Mode::Zero).count()
    }

    /// Remove a variable from the context
    pub fn remove(&mut self, var: VarId) {
        self.entries.retain(|e| e.var != var);
    }

    /// Remove a variable (functional style)
    #[must_use]
    pub fn without(&self, var: VarId) -> Self {
        Self {
            entries: self.entries.iter().filter(|e| e.var != var).cloned().collect(),
        }
    }
}

impl FromIterator<ModeCtxEntry> for ModeCtx {
    fn from_iter<I: IntoIterator<Item = ModeCtxEntry>>(iter: I) -> Self {
        Self { entries: iter.into_iter().collect() }
    }
}

impl<'a> IntoIterator for &'a ModeCtx {
    type Item = &'a ModeCtxEntry;
    type IntoIter = std::slice::Iter<'a, ModeCtxEntry>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

impl IntoIterator for ModeCtx {
    type Item = ModeCtxEntry;
    type IntoIter = std::vec::IntoIter<ModeCtxEntry>;
    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

// F*-style free functions for ModeCtx

/// Create empty mode context
#[must_use]
pub fn empty_mode_ctx() -> ModeCtx {
    ModeCtx::empty()
}

/// Lookup mode and extended_mode
#[must_use]
pub fn lookup_mode_ctx(var: VarId, ctx: &ModeCtx) -> (Mode, ExtendedMode) {
    ctx.lookup(var)
}

/// Lookup just the mode
#[must_use]
pub fn lookup_mode_only(var: VarId, ctx: &ModeCtx) -> Mode {
    ctx.lookup_mode(var)
}

/// Lookup just the extended_mode
#[must_use]
pub fn lookup_extended_mode(var: VarId, ctx: &ModeCtx) -> ExtendedMode {
    ctx.lookup_extended(var)
}

/// Update mode of variable
#[must_use]
pub fn update_mode_ctx(var: VarId, mode: Mode, ctx: &ModeCtx) -> ModeCtx {
    ctx.with_mode(var, mode)
}

/// Update both mode and extended_mode
#[must_use]
pub fn update_mode_full(var: VarId, mode: Mode, extended: ExtendedMode, ctx: &ModeCtx) -> ModeCtx {
    ctx.with_full(var, mode, extended)
}

/// Extend context with new variable
#[must_use]
pub fn extend_mode_ctx(var: VarId, mode: Mode, extended: ExtendedMode, ctx: &ModeCtx) -> ModeCtx {
    ctx.with_extend(var, mode, extended)
}

/// Consume a linear variable
#[must_use]
pub fn consume_mode_ctx(var: VarId, ctx: &ModeCtx) -> Option<ModeCtx> {
    ctx.consume(var)
}

/// Split context for parallel composition
#[must_use]
pub fn split_ctx(ctx: &ModeCtx) -> (ModeCtx, ModeCtx) {
    ctx.split()
}

/// Join contexts after branch merge
#[must_use]
pub fn join_ctx(ctx1: &ModeCtx, ctx2: &ModeCtx) -> ModeCtx {
    ctx1.join(ctx2)
}

// ============================================================================
// Linear Context for Linearity Tracking (with usage tracking)
// ============================================================================

/// Entry in the linear context tracking a variable's linearity state
///
/// Maps to F*:
/// ```fstar
/// type lin_entry = {
///   le_var  : string;
///   le_mode : mode;
///   le_ext  : extended_mode;
///   le_perm : option fraction;
///   le_used : bool
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinEntry {
    /// Variable identifier
    pub var: VarId,
    /// Base usage mode (Zero/One/Omega)
    pub mode: Mode,
    /// Extended mode with structural rule info
    pub extended: ExtendedMode,
    /// Optional fractional permission (0-255 scale, None = no permission tracking)
    pub perm: Option<u8>,
    /// Has this variable been used at least once?
    pub used: bool,
}

impl LinEntry {
    /// Create a new linear entry
    pub fn new(var: VarId, mode: Mode, extended: ExtendedMode) -> Self {
        Self {
            var,
            mode,
            extended,
            perm: None,
            used: false,
        }
    }

    /// Create a linear entry with permission tracking
    pub fn with_perm(var: VarId, mode: Mode, extended: ExtendedMode, perm: u8) -> Self {
        Self {
            var,
            mode,
            extended,
            perm: Some(perm),
            used: false,
        }
    }

    /// Create a linear variable (Mode::One, ExtendedMode::Linear)
    pub fn linear(var: VarId) -> Self {
        Self::new(var, Mode::One, ExtendedMode::Linear)
    }

    /// Create an affine variable (Mode::One, ExtendedMode::Affine)
    pub fn affine(var: VarId) -> Self {
        Self::new(var, Mode::One, ExtendedMode::Affine)
    }

    /// Create a relevant variable (Mode::One, ExtendedMode::Relevant)
    pub fn relevant(var: VarId) -> Self {
        Self::new(var, Mode::One, ExtendedMode::Relevant)
    }

    /// Create an unrestricted variable (Mode::Omega, ExtendedMode::Unrestricted)
    pub fn unrestricted(var: VarId) -> Self {
        Self::new(var, Mode::Omega, ExtendedMode::Unrestricted)
    }

    /// Mark this entry as used
    pub fn mark_used(&mut self) {
        self.used = true;
    }

    /// Check if this variable must be used (linear or relevant)
    pub fn must_be_used(&self) -> bool {
        matches!(self.mode, Mode::One) && !self.extended.allows_weakening()
    }

    /// Check if this variable can be used multiple times
    pub fn allows_reuse(&self) -> bool {
        self.extended.allows_contraction() || self.mode.is_omega()
    }
}

/// Linear context - tracks linearity state for all bound variables
///
/// Maps to F*: `type lin_ctx = list lin_entry`
///
/// Operations:
/// - `empty_lin_ctx`: Empty context
/// - `lookup_lin`: Find entry by variable
/// - `extend_lin`: Add new entry
/// - `use_lin`: Mark variable as used
/// - `split_lin_ctx`: Split for parallel branches
/// - `join_lin_ctx`: Merge after branches
/// - `is_fully_consumed`: Check all linear vars used
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinCtx {
    entries: Vec<LinEntry>,
}

impl LinCtx {
    /// Create an empty linear context
    #[must_use]
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Create a linear context with initial capacity
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            entries: Vec::with_capacity(cap),
        }
    }

    /// Number of entries
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if context is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over entries
    pub fn iter(&self) -> impl Iterator<Item = &LinEntry> {
        self.entries.iter()
    }

    /// Mutable iteration
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut LinEntry> {
        self.entries.iter_mut()
    }

    /// Look up an entry by variable id
    ///
    /// Maps to F*: `val lookup_lin : string -> lin_ctx -> option lin_entry`
    #[must_use]
    pub fn lookup(&self, var: VarId) -> Option<&LinEntry> {
        self.entries.iter().find(|e| e.var == var)
    }

    /// Mutable lookup
    #[must_use]
    pub fn lookup_mut(&mut self, var: VarId) -> Option<&mut LinEntry> {
        self.entries.iter_mut().find(|e| e.var == var)
    }

    /// Extend the context with a new entry
    ///
    /// Maps to F*: `val extend_lin : lin_entry -> lin_ctx -> lin_ctx`
    ///
    /// Note: This shadows any existing binding with the same name
    /// (new entry is prepended, lookup finds first match)
    pub fn extend(&mut self, entry: LinEntry) {
        self.entries.push(entry);
    }

    /// Create a new context with the entry added
    #[must_use]
    pub fn extended(&self, entry: LinEntry) -> Self {
        let mut ctx = self.clone();
        ctx.extend(entry);
        ctx
    }

    /// Mark a variable as used, returning updated context or None if variable not found
    /// or if usage would violate linearity constraints
    ///
    /// Maps to F*: `val use_lin : string -> lin_ctx -> option lin_ctx`
    ///
    /// Returns None if:
    /// - Variable not found
    /// - Variable already used and doesn't allow contraction
    #[must_use]
    pub fn use_var(&self, var: VarId) -> Option<Self> {
        let mut ctx = self.clone();

        let entry = ctx.lookup_mut(var)?;

        // Check if re-use is allowed
        if entry.used && !entry.allows_reuse() {
            return None;
        }

        entry.used = true;
        Some(ctx)
    }

    /// Split context for parallel branches (e.g., both branches of if-else)
    ///
    /// Maps to F*: `val split_lin_ctx : lin_ctx -> (lin_ctx & lin_ctx)`
    ///
    /// For linear/affine variables: each branch gets its own copy with used=false
    /// For unrestricted variables: duplicated normally
    ///
    /// After branches execute, use `join_lin_ctx` to merge results
    #[must_use]
    pub fn split(&self) -> (Self, Self) {
        // Both branches start fresh with used=false for variables that need tracking
        let mut left = self.clone();
        let mut right = self.clone();

        for entry in left.iter_mut() {
            // Reset 'used' for the split so each branch tracks independently
            // Unrestricted vars keep their state, linear/affine reset
            if entry.mode.is_one() {
                entry.used = false;
            }
        }

        for entry in right.iter_mut() {
            if entry.mode.is_one() {
                entry.used = false;
            }
        }

        (left, right)
    }

    /// Join two contexts after parallel branches
    ///
    /// Maps to F*: `val join_lin_ctx : lin_ctx -> lin_ctx -> lin_ctx`
    ///
    /// Takes the most restrictive view:
    /// - A variable is marked used if used in EITHER branch
    /// - Modes/permissions are joined (upper bound)
    ///
    /// Contexts must have the same variables in the same order
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(
            self.len(),
            other.len(),
            "join_lin_ctx: contexts must have same length"
        );

        let entries = self
            .entries
            .iter()
            .zip(other.entries.iter())
            .map(|(left, right)| {
                debug_assert_eq!(left.var, right.var, "join_lin_ctx: variable mismatch");

                LinEntry {
                    var: left.var,
                    // Join modes (take upper bound - most uses)
                    mode: left.mode.join(right.mode),
                    // Join extended modes
                    extended: left.extended.join(right.extended),
                    // Join permissions (if both have, take minimum remaining)
                    perm: match (left.perm, right.perm) {
                        (Some(l), Some(r)) => Some(l.min(r)),
                        (p, None) | (None, p) => p,
                    },
                    // Used in either branch means used overall
                    used: left.used || right.used,
                }
            })
            .collect();

        Self { entries }
    }

    /// Check if all linear variables (Mode::One with !allows_weakening) have been used
    ///
    /// Maps to F*: `val is_fully_consumed : lin_ctx -> bool`
    ///
    /// Returns true if every variable that MUST be used has been used at least once.
    /// - Linear (Mode::One, !allows_weakening): must be used exactly once
    /// - Relevant (Mode::One, allows_contraction): must be used at least once
    /// - Affine (Mode::One, allows_weakening): may remain unused
    /// - Unrestricted (Mode::Omega): may remain unused
    #[must_use]
    pub fn is_fully_consumed(&self) -> bool {
        self.entries.iter().all(|entry| {
            // If variable must be used, check that it was used
            if entry.must_be_used() {
                entry.used
            } else {
                true
            }
        })
    }

    /// Get all unconsumed variables that must be used
    ///
    /// Returns variables that violate linearity (not used when they must be)
    #[must_use]
    pub fn unconsumed(&self) -> Vec<VarId> {
        self.entries
            .iter()
            .filter(|e| e.must_be_used() && !e.used)
            .map(|e| e.var)
            .collect()
    }

    /// Weaken a variable's mode (make it less restrictive)
    ///
    /// Maps to F*: `val weaken_lin : string -> mode -> extended_mode -> lin_ctx -> option lin_ctx`
    ///
    /// Only succeeds if the new mode is compatible with the current extended mode.
    /// Returns None if:
    /// - Variable not found
    /// - Weakening would violate structural rules
    #[must_use]
    pub fn weaken(&self, var: VarId, mode: Mode, extended: ExtendedMode) -> Option<Self> {
        let mut ctx = self.clone();
        let entry = ctx.lookup_mut(var)?;

        // Check that the transition is allowed by current extended mode
        if !entry.extended.can_transition(mode) {
            return None;
        }

        entry.mode = mode;
        entry.extended = extended;
        Some(ctx)
    }

    /// Contract a variable (allow re-use for relevant/unrestricted)
    ///
    /// Maps to F*: `val contract_lin : string -> lin_ctx -> option lin_ctx`
    ///
    /// Only succeeds if the variable allows contraction.
    /// Returns None if:
    /// - Variable not found
    /// - Variable doesn't allow contraction (linear or affine)
    #[must_use]
    pub fn contract(&self, var: VarId) -> Option<Self> {
        let entry = self.lookup(var)?;

        // Check that contraction is allowed
        if !entry.allows_reuse() {
            return None;
        }

        // Contraction doesn't change the context, just allows re-use
        // which is checked in use_var
        Some(self.clone())
    }

    /// Remove a variable from the context (for shadowing or scope exit)
    ///
    /// Returns None if variable not found or would violate linearity
    pub fn remove(&mut self, var: VarId) -> Option<LinEntry> {
        let pos = self.entries.iter().position(|e| e.var == var)?;
        let entry = self.entries.remove(pos);

        // Check that removal doesn't violate linearity
        if entry.must_be_used() && !entry.used {
            // Cannot remove an unused linear variable
            // Re-insert and return None
            self.entries.insert(pos, entry);
            return None;
        }

        Some(entry)
    }
}

/// Create an empty linear context
///
/// Maps to F*: `val empty_lin_ctx : lin_ctx`
#[must_use]
pub fn empty_lin_ctx() -> LinCtx {
    LinCtx::empty()
}

/// Look up a variable in the linear context
///
/// Maps to F*: `val lookup_lin : string -> lin_ctx -> option lin_entry`
#[must_use]
pub fn lookup_lin(var: VarId, ctx: &LinCtx) -> Option<&LinEntry> {
    ctx.lookup(var)
}

/// Extend a linear context with a new entry
///
/// Maps to F*: `val extend_lin : lin_entry -> lin_ctx -> lin_ctx`
#[must_use]
pub fn extend_lin(entry: LinEntry, ctx: &LinCtx) -> LinCtx {
    ctx.extended(entry)
}

/// Mark a variable as used in the context
///
/// Maps to F*: `val use_lin : string -> lin_ctx -> option lin_ctx`
#[must_use]
pub fn use_lin(var: VarId, ctx: &LinCtx) -> Option<LinCtx> {
    ctx.use_var(var)
}

/// Split context for parallel branches
///
/// Maps to F*: `val split_lin_ctx : lin_ctx -> (lin_ctx & lin_ctx)`
#[must_use]
pub fn split_lin_ctx(ctx: &LinCtx) -> (LinCtx, LinCtx) {
    ctx.split()
}

/// Join contexts after parallel branches
///
/// Maps to F*: `val join_lin_ctx : lin_ctx -> lin_ctx -> lin_ctx`
#[must_use]
pub fn join_lin_ctx(left: &LinCtx, right: &LinCtx) -> LinCtx {
    left.join(right)
}

/// Check if all linear variables are fully consumed
///
/// Maps to F*: `val is_fully_consumed : lin_ctx -> bool`
#[must_use]
pub fn is_fully_consumed(ctx: &LinCtx) -> bool {
    ctx.is_fully_consumed()
}

/// Weaken a variable's mode
///
/// Maps to F*: `val weaken_lin : string -> mode -> extended_mode -> lin_ctx -> option lin_ctx`
#[must_use]
pub fn weaken_lin(var: VarId, mode: Mode, extended: ExtendedMode, ctx: &LinCtx) -> Option<LinCtx> {
    ctx.weaken(var, mode, extended)
}

/// Contract a variable for re-use
///
/// Maps to F*: `val contract_lin : string -> lin_ctx -> option lin_ctx`
#[must_use]
pub fn contract_lin(var: VarId, ctx: &LinCtx) -> Option<LinCtx> {
    ctx.contract(var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Key;

    #[test]
    fn test_mode_lattice() {
        // Join tests - Zero is identity (bottom)
        assert_eq!(Mode::Zero.join(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::Zero.join(Mode::One), Mode::One);
        assert_eq!(Mode::Zero.join(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::One.join(Mode::Zero), Mode::One);
        assert_eq!(Mode::One.join(Mode::One), Mode::One);
        assert_eq!(Mode::One.join(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::Omega.join(Mode::Zero), Mode::Omega);
        assert_eq!(Mode::Omega.join(Mode::One), Mode::Omega);
        assert_eq!(Mode::Omega.join(Mode::Omega), Mode::Omega);

        // Meet tests - Omega is identity (top), Zero absorbs
        assert_eq!(Mode::Omega.meet(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::Omega.meet(Mode::One), Mode::One);
        assert_eq!(Mode::Omega.meet(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::One.meet(Mode::Omega), Mode::One);
        assert_eq!(Mode::One.meet(Mode::One), Mode::One);
        assert_eq!(Mode::One.meet(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::Zero.meet(Mode::Omega), Mode::Zero);
        assert_eq!(Mode::Zero.meet(Mode::One), Mode::Zero);
        assert_eq!(Mode::Zero.meet(Mode::Zero), Mode::Zero);

        // Submode tests: Zero <= One <= Omega
        assert!(Mode::Zero.submode(Mode::Zero));
        assert!(Mode::Zero.submode(Mode::One));
        assert!(Mode::Zero.submode(Mode::Omega));
        assert!(!Mode::One.submode(Mode::Zero));
        assert!(Mode::One.submode(Mode::One));
        assert!(Mode::One.submode(Mode::Omega));
        assert!(!Mode::Omega.submode(Mode::Zero));
        assert!(!Mode::Omega.submode(Mode::One));
        assert!(Mode::Omega.submode(Mode::Omega));
    }

    #[test]
    fn test_mode_semiring_add() {
        // Zero is additive identity
        assert_eq!(Mode::Zero.add(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::Zero.add(Mode::One), Mode::One);
        assert_eq!(Mode::Zero.add(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::One.add(Mode::Zero), Mode::One);
        assert_eq!(Mode::Omega.add(Mode::Zero), Mode::Omega);

        // One + One = Omega
        assert_eq!(Mode::One.add(Mode::One), Mode::Omega);

        // Omega absorbs
        assert_eq!(Mode::One.add(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::Omega.add(Mode::One), Mode::Omega);
        assert_eq!(Mode::Omega.add(Mode::Omega), Mode::Omega);
    }

    #[test]
    fn test_mode_semiring_mul() {
        // Zero annihilates
        assert_eq!(Mode::Zero.mul(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::Zero.mul(Mode::One), Mode::Zero);
        assert_eq!(Mode::Zero.mul(Mode::Omega), Mode::Zero);
        assert_eq!(Mode::One.mul(Mode::Zero), Mode::Zero);
        assert_eq!(Mode::Omega.mul(Mode::Zero), Mode::Zero);

        // One is multiplicative identity
        assert_eq!(Mode::One.mul(Mode::One), Mode::One);
        assert_eq!(Mode::One.mul(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::Omega.mul(Mode::One), Mode::Omega);

        // Omega * Omega = Omega
        assert_eq!(Mode::Omega.mul(Mode::Omega), Mode::Omega);
    }

    #[test]
    fn test_mode_semiring_laws() {
        let modes = [Mode::Zero, Mode::One, Mode::Omega];

        for &a in &modes {
            for &b in &modes {
                // Commutativity of add
                assert_eq!(a.add(b), b.add(a), "add not commutative: {a:?}, {b:?}");
                // Commutativity of mul
                assert_eq!(a.mul(b), b.mul(a), "mul not commutative: {a:?}, {b:?}");

                for &c in &modes {
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
                    // Left distributivity: a * (b + c) = (a * b) + (a * c)
                    assert_eq!(
                        a.mul(b.add(c)),
                        a.mul(b).add(a.mul(c)),
                        "left distributivity failed: {a:?}, {b:?}, {c:?}"
                    );
                    // Right distributivity: (a + b) * c = (a * c) + (b * c)
                    assert_eq!(
                        a.add(b).mul(c),
                        a.mul(c).add(b.mul(c)),
                        "right distributivity failed: {a:?}, {b:?}, {c:?}"
                    );
                }
            }
        }

        // Identity laws
        for &m in &modes {
            assert_eq!(Mode::Zero.add(m), m, "Zero not additive identity");
            assert_eq!(m.add(Mode::Zero), m, "Zero not additive identity");
            assert_eq!(Mode::One.mul(m), m, "One not multiplicative identity");
            assert_eq!(m.mul(Mode::One), m, "One not multiplicative identity");
        }

        // Annihilator law
        for &m in &modes {
            assert_eq!(Mode::Zero.mul(m), Mode::Zero, "Zero not annihilator");
            assert_eq!(m.mul(Mode::Zero), Mode::Zero, "Zero not annihilator");
        }
    }

    #[test]
    fn test_ref_kind_fraction() {
        assert_eq!(RefKind::FULL.as_fraction(), (1, 1));
        assert_eq!(RefKind::HALF.as_fraction(), (1, 2));
        assert_eq!(RefKind::QUARTER.as_fraction(), (1, 4));

        let rk = RefKind::from_fraction(1, 3);
        assert!(rk.permission > 80 && rk.permission < 90);
    }

    #[test]
    fn test_ref_kind_split_join() {
        let full = RefKind::FULL;
        let half = full.split();
        assert_eq!(half.permission, 127);

        let rejoined = half.join(half);
        assert!(rejoined.is_some());
    }

    #[test]
    fn test_extended_mode_to_mode() {
        // All non-unrestricted modes map to One
        assert_eq!(ExtendedMode::Linear.to_mode(), Mode::One);
        assert_eq!(ExtendedMode::Affine.to_mode(), Mode::One);
        assert_eq!(ExtendedMode::Relevant.to_mode(), Mode::One);
        // Only Unrestricted maps to Omega
        assert_eq!(ExtendedMode::Unrestricted.to_mode(), Mode::Omega);
    }

    #[test]
    fn test_extended_mode_from_mode() {
        assert_eq!(ExtendedMode::from_mode(Mode::Zero), ExtendedMode::Affine);
        assert_eq!(ExtendedMode::from_mode(Mode::One), ExtendedMode::Linear);
        assert_eq!(
            ExtendedMode::from_mode(Mode::Omega),
            ExtendedMode::Unrestricted
        );
    }

    #[test]
    fn test_extended_mode_can_transition() {
        // Linear: exactly once - only One valid
        assert!(!ExtendedMode::Linear.can_transition(Mode::Zero));
        assert!(ExtendedMode::Linear.can_transition(Mode::One));
        assert!(!ExtendedMode::Linear.can_transition(Mode::Omega));

        // Affine: weakening allowed (can drop to Zero)
        assert!(ExtendedMode::Affine.can_transition(Mode::Zero));
        assert!(ExtendedMode::Affine.can_transition(Mode::One));
        assert!(!ExtendedMode::Affine.can_transition(Mode::Omega));

        // Relevant: contraction allowed (can duplicate to Omega)
        assert!(!ExtendedMode::Relevant.can_transition(Mode::Zero));
        assert!(ExtendedMode::Relevant.can_transition(Mode::One));
        assert!(ExtendedMode::Relevant.can_transition(Mode::Omega));

        // Unrestricted: any transition valid
        assert!(ExtendedMode::Unrestricted.can_transition(Mode::Zero));
        assert!(ExtendedMode::Unrestricted.can_transition(Mode::One));
        assert!(ExtendedMode::Unrestricted.can_transition(Mode::Omega));
    }

    #[test]
    fn test_extended_mode_lattice() {
        // Join: least upper bound
        assert_eq!(
            ExtendedMode::Linear.join(ExtendedMode::Linear),
            ExtendedMode::Linear
        );
        assert_eq!(
            ExtendedMode::Linear.join(ExtendedMode::Affine),
            ExtendedMode::Affine
        );
        assert_eq!(
            ExtendedMode::Linear.join(ExtendedMode::Relevant),
            ExtendedMode::Relevant
        );
        assert_eq!(
            ExtendedMode::Affine.join(ExtendedMode::Relevant),
            ExtendedMode::Unrestricted
        );
        assert_eq!(
            ExtendedMode::Affine.join(ExtendedMode::Unrestricted),
            ExtendedMode::Unrestricted
        );

        // Meet: greatest lower bound
        assert_eq!(
            ExtendedMode::Unrestricted.meet(ExtendedMode::Unrestricted),
            ExtendedMode::Unrestricted
        );
        assert_eq!(
            ExtendedMode::Unrestricted.meet(ExtendedMode::Affine),
            ExtendedMode::Affine
        );
        assert_eq!(
            ExtendedMode::Affine.meet(ExtendedMode::Relevant),
            ExtendedMode::Linear
        );
        assert_eq!(
            ExtendedMode::Linear.meet(ExtendedMode::Unrestricted),
            ExtendedMode::Linear
        );
    }

    #[test]
    fn test_extended_mode_properties() {
        // Weakening: can drop
        assert!(!ExtendedMode::Linear.allows_weakening());
        assert!(ExtendedMode::Affine.allows_weakening());
        assert!(!ExtendedMode::Relevant.allows_weakening());
        assert!(ExtendedMode::Unrestricted.allows_weakening());

        // Contraction: can duplicate
        assert!(!ExtendedMode::Linear.allows_contraction());
        assert!(!ExtendedMode::Affine.allows_contraction());
        assert!(ExtendedMode::Relevant.allows_contraction());
        assert!(ExtendedMode::Unrestricted.allows_contraction());
    }

    #[test]
    fn test_mode_parsing() {
        assert_eq!(Mode::from_str("0"), Some(Mode::Zero));
        assert_eq!(Mode::from_str("zero"), Some(Mode::Zero));
        assert_eq!(Mode::from_str("1"), Some(Mode::One));
        assert_eq!(Mode::from_str("linear"), Some(Mode::One));
        assert_eq!(Mode::from_str("omega"), Some(Mode::Omega));
        assert_eq!(Mode::from_str("unrestricted"), Some(Mode::Omega));
        assert_eq!(Mode::from_str("invalid"), None);
    }

    // ========================================================================
    // LinCtx tests
    // ========================================================================

    fn make_var(n: usize) -> VarId {
        Spur::try_from_usize(n).unwrap()
    }

    #[test]
    fn test_lin_entry_constructors() {
        let v = make_var(1);

        let linear = LinEntry::linear(v);
        assert_eq!(linear.mode, Mode::One);
        assert_eq!(linear.extended, ExtendedMode::Linear);
        assert!(!linear.used);
        assert!(linear.must_be_used());
        assert!(!linear.allows_reuse());

        let affine = LinEntry::affine(v);
        assert_eq!(affine.mode, Mode::One);
        assert_eq!(affine.extended, ExtendedMode::Affine);
        assert!(!affine.must_be_used()); // Can be dropped

        let relevant = LinEntry::relevant(v);
        assert_eq!(relevant.mode, Mode::One);
        assert_eq!(relevant.extended, ExtendedMode::Relevant);
        assert!(relevant.must_be_used());
        assert!(relevant.allows_reuse()); // Can be contracted

        let unr = LinEntry::unrestricted(v);
        assert_eq!(unr.mode, Mode::Omega);
        assert_eq!(unr.extended, ExtendedMode::Unrestricted);
        assert!(!unr.must_be_used());
        assert!(unr.allows_reuse());
    }

    #[test]
    fn test_lin_ctx_empty() {
        let ctx = empty_lin_ctx();
        assert!(ctx.is_empty());
        assert_eq!(ctx.len(), 0);
        assert!(is_fully_consumed(&ctx));
    }

    #[test]
    fn test_lin_ctx_extend_lookup() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::linear(v1));
        ctx.extend(LinEntry::affine(v2));

        assert_eq!(ctx.len(), 2);
        assert!(ctx.lookup(v1).is_some());
        assert!(ctx.lookup(v2).is_some());
        assert!(ctx.lookup(make_var(99)).is_none());
    }

    #[test]
    fn test_lin_ctx_use_linear() {
        let v = make_var(1);
        let ctx = extend_lin(LinEntry::linear(v), &empty_lin_ctx());

        // First use should succeed
        let ctx2 = use_lin(v, &ctx);
        assert!(ctx2.is_some());

        let ctx2 = ctx2.unwrap();
        assert!(ctx2.lookup(v).unwrap().used);

        // Second use should FAIL for linear variable
        let ctx3 = use_lin(v, &ctx2);
        assert!(ctx3.is_none());
    }

    #[test]
    fn test_lin_ctx_use_affine() {
        let v = make_var(1);
        let ctx = extend_lin(LinEntry::affine(v), &empty_lin_ctx());

        // First use should succeed
        let ctx2 = use_lin(v, &ctx).unwrap();
        assert!(ctx2.lookup(v).unwrap().used);

        // Second use should FAIL for affine variable (no contraction)
        let ctx3 = use_lin(v, &ctx2);
        assert!(ctx3.is_none());
    }

    #[test]
    fn test_lin_ctx_use_relevant() {
        let v = make_var(1);
        let ctx = extend_lin(LinEntry::relevant(v), &empty_lin_ctx());

        // First use should succeed
        let ctx2 = use_lin(v, &ctx).unwrap();

        // Second use should SUCCEED for relevant variable (contraction allowed)
        let ctx3 = use_lin(v, &ctx2);
        assert!(ctx3.is_some());
    }

    #[test]
    fn test_lin_ctx_use_unrestricted() {
        let v = make_var(1);
        let ctx = extend_lin(LinEntry::unrestricted(v), &empty_lin_ctx());

        // Any number of uses should succeed
        let ctx2 = use_lin(v, &ctx).unwrap();
        let ctx3 = use_lin(v, &ctx2).unwrap();
        let ctx4 = use_lin(v, &ctx3).unwrap();
        assert!(ctx4.lookup(v).unwrap().used);
    }

    #[test]
    fn test_lin_ctx_is_fully_consumed() {
        let v1 = make_var(1);
        let v2 = make_var(2);
        let v3 = make_var(3);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::linear(v1)); // Must be used
        ctx.extend(LinEntry::affine(v2)); // Can be dropped
        ctx.extend(LinEntry::unrestricted(v3)); // Can be unused

        // Not consumed - linear v1 not used
        assert!(!is_fully_consumed(&ctx));
        assert_eq!(ctx.unconsumed(), vec![v1]);

        // Use v1
        let ctx = use_lin(v1, &ctx).unwrap();
        assert!(is_fully_consumed(&ctx));
        assert!(ctx.unconsumed().is_empty());
    }

    #[test]
    fn test_lin_ctx_split() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::linear(v1));
        ctx.extend(LinEntry::unrestricted(v2));

        let (left, right) = split_lin_ctx(&ctx);

        // Both branches have the same variables
        assert!(left.lookup(v1).is_some());
        assert!(right.lookup(v1).is_some());

        // Both start with used=false for linear vars
        assert!(!left.lookup(v1).unwrap().used);
        assert!(!right.lookup(v1).unwrap().used);
    }

    #[test]
    fn test_lin_ctx_join() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::linear(v1));
        ctx.extend(LinEntry::affine(v2));

        let (left, right) = split_lin_ctx(&ctx);

        // Use v1 in left branch
        let left = use_lin(v1, &left).unwrap();
        // Use v2 in right branch
        let right = use_lin(v2, &right).unwrap();

        let joined = join_lin_ctx(&left, &right);

        // v1 used in left -> marked used in join
        assert!(joined.lookup(v1).unwrap().used);
        // v2 used in right -> marked used in join
        assert!(joined.lookup(v2).unwrap().used);
    }

    #[test]
    fn test_lin_ctx_join_both_use() {
        let v = make_var(1);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::relevant(v)); // Allows contraction

        let (left, right) = split_lin_ctx(&ctx);

        // Use v in both branches (allowed for relevant)
        let left = use_lin(v, &left).unwrap();
        let right = use_lin(v, &right).unwrap();

        let joined = join_lin_ctx(&left, &right);
        assert!(joined.lookup(v).unwrap().used);
    }

    #[test]
    fn test_lin_ctx_contract() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::linear(v1)); // No contraction
        ctx.extend(LinEntry::relevant(v2)); // Allows contraction

        // Contract on linear should fail
        assert!(contract_lin(v1, &ctx).is_none());

        // Contract on relevant should succeed
        assert!(contract_lin(v2, &ctx).is_some());
    }

    #[test]
    fn test_lin_ctx_weaken() {
        let v = make_var(1);
        let ctx = extend_lin(LinEntry::affine(v), &empty_lin_ctx());

        // Weaken affine to Zero should succeed (affine allows weakening)
        let ctx2 = weaken_lin(v, Mode::Zero, ExtendedMode::Affine, &ctx);
        assert!(ctx2.is_some());
        assert_eq!(ctx2.unwrap().lookup(v).unwrap().mode, Mode::Zero);

        // Weaken linear to Zero should fail
        let ctx = extend_lin(LinEntry::linear(v), &empty_lin_ctx());
        let ctx2 = weaken_lin(v, Mode::Zero, ExtendedMode::Linear, &ctx);
        assert!(ctx2.is_none());
    }

    #[test]
    fn test_lin_ctx_remove() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let mut ctx = LinCtx::empty();
        ctx.extend(LinEntry::affine(v1)); // Can be removed unused
        ctx.extend(LinEntry::linear(v2)); // Cannot be removed unused

        // Remove unused affine should succeed
        let entry = ctx.remove(v1);
        assert!(entry.is_some());
        assert!(ctx.lookup(v1).is_none());

        // Remove unused linear should fail
        let entry = ctx.remove(v2);
        assert!(entry.is_none());
        assert!(ctx.lookup(v2).is_some());

        // Use v2, then remove should succeed
        let mut ctx = ctx.use_var(v2).unwrap();
        let entry = ctx.remove(v2);
        assert!(entry.is_some());
    }

    #[test]
    fn test_lin_entry_with_perm() {
        let v = make_var(1);
        let entry = LinEntry::with_perm(v, Mode::One, ExtendedMode::Linear, 128);

        assert_eq!(entry.perm, Some(128));
    }

    #[test]
    fn test_lin_ctx_join_permissions() {
        let v = make_var(1);

        let mut left = LinCtx::empty();
        left.extend(LinEntry::with_perm(v, Mode::One, ExtendedMode::Linear, 200));

        let mut right = LinCtx::empty();
        right.extend(LinEntry::with_perm(v, Mode::One, ExtendedMode::Linear, 100));

        let joined = join_lin_ctx(&left, &right);
        // Should take minimum permission
        assert_eq!(joined.lookup(v).unwrap().perm, Some(100));
    }

    #[test]
    fn test_lin_ctx_functional_api() {
        // Test the free-standing function API matches the method API
        let v = make_var(1);
        let ctx1 = empty_lin_ctx();
        let ctx2 = extend_lin(LinEntry::linear(v), &ctx1);

        assert!(lookup_lin(v, &ctx2).is_some());
        assert!(!is_fully_consumed(&ctx2));

        let ctx3 = use_lin(v, &ctx2).unwrap();
        assert!(is_fully_consumed(&ctx3));

        let (l, r) = split_lin_ctx(&ctx2);
        let l = use_lin(v, &l).unwrap();
        let r = use_lin(v, &r).unwrap();
        let joined = join_lin_ctx(&l, &r);
        assert!(is_fully_consumed(&joined));
    }

    // ========================================================================
    // ModeCtx tests
    // ========================================================================

    #[test]
    fn test_mode_ctx_empty() {
        let ctx = empty_mode_ctx();
        assert!(ctx.is_empty());
        assert_eq!(ctx.len(), 0);
        assert!(ctx.is_well_formed());
        assert!(ctx.is_fully_consumed());
    }

    #[test]
    fn test_mode_ctx_lookup_missing() {
        let ctx = empty_mode_ctx();
        let v = make_var(1);
        let (mode, ext) = ctx.lookup(v);
        assert_eq!(mode, Mode::Zero);
        assert_eq!(ext, ExtendedMode::Unrestricted);
    }

    #[test]
    fn test_mode_ctx_extend_lookup() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let ctx = empty_mode_ctx();
        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &ctx);
        let ctx = extend_mode_ctx(v2, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        assert_eq!(ctx.len(), 2);
        assert_eq!(ctx.lookup_mode(v1), Mode::One);
        assert_eq!(ctx.lookup_extended(v1), ExtendedMode::Linear);
        assert_eq!(ctx.lookup_mode(v2), Mode::Omega);
        assert!(ctx.is_well_formed());
    }

    #[test]
    fn test_mode_ctx_consume_linear() {
        let v = make_var(1);
        let ctx = extend_mode_ctx(v, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());

        // First consume should succeed
        let ctx2 = consume_mode_ctx(v, &ctx);
        assert!(ctx2.is_some());
        let ctx2 = ctx2.unwrap();
        assert_eq!(ctx2.lookup_mode(v), Mode::Zero);

        // Second consume should fail (already zero)
        let ctx3 = consume_mode_ctx(v, &ctx2);
        assert!(ctx3.is_none());
    }

    #[test]
    fn test_mode_ctx_consume_omega() {
        let v = make_var(1);
        let ctx = extend_mode_ctx(v, Mode::Omega, ExtendedMode::Unrestricted, &empty_mode_ctx());

        // Consume omega should succeed and leave it as Omega
        let ctx2 = consume_mode_ctx(v, &ctx);
        assert!(ctx2.is_some());
        assert_eq!(ctx2.unwrap().lookup_mode(v), Mode::Omega);
    }

    #[test]
    fn test_mode_ctx_split_linear() {
        let v = make_var(1);
        let ctx = extend_mode_ctx(v, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());

        let (left, right) = split_ctx(&ctx);

        // Left gets the linear variable
        assert_eq!(left.lookup_mode(v), Mode::One);
        // Right gets Zero
        assert_eq!(right.lookup_mode(v), Mode::Zero);
        // Extended mode preserved
        assert_eq!(left.lookup_extended(v), ExtendedMode::Linear);
        assert_eq!(right.lookup_extended(v), ExtendedMode::Linear);
    }

    #[test]
    fn test_mode_ctx_split_omega() {
        let v = make_var(1);
        let ctx = extend_mode_ctx(v, Mode::Omega, ExtendedMode::Unrestricted, &empty_mode_ctx());

        let (left, right) = split_ctx(&ctx);

        // Both get Omega
        assert_eq!(left.lookup_mode(v), Mode::Omega);
        assert_eq!(right.lookup_mode(v), Mode::Omega);
    }

    #[test]
    fn test_mode_ctx_join() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        // After split, linear variables go to left only, right gets Zero
        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        let (left, right) = split_ctx(&ctx);

        // v1: left has One, right has Zero (linear split)
        // v2: both have Omega (unrestricted)
        assert_eq!(left.lookup_mode(v1), Mode::One);
        assert_eq!(right.lookup_mode(v1), Mode::Zero);
        assert_eq!(left.lookup_mode(v2), Mode::Omega);
        assert_eq!(right.lookup_mode(v2), Mode::Omega);

        // Consume v1 in left (the only branch that has it)
        let left = consume_mode_ctx(v1, &left).unwrap();
        assert_eq!(left.lookup_mode(v1), Mode::Zero);

        let joined = join_ctx(&left, &right);

        // v1: Zero join Zero = Zero
        assert_eq!(joined.lookup_mode(v1), Mode::Zero);
        // v2: Omega join Omega = Omega
        assert_eq!(joined.lookup_mode(v2), Mode::Omega);
    }

    #[test]
    fn test_mode_ctx_contract() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::One, ExtendedMode::Relevant, &ctx);

        // Contract linear should fail
        assert!(ctx.contract(v1).is_none());

        // Contract relevant should succeed
        let ctx2 = ctx.contract(v2);
        assert!(ctx2.is_some());
        assert_eq!(ctx2.unwrap().lookup_mode(v2), Mode::Omega);
    }

    #[test]
    fn test_mode_ctx_is_fully_consumed() {
        let v1 = make_var(1);
        let v2 = make_var(2);
        let v3 = make_var(3);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::One, ExtendedMode::Affine, &ctx);
        let ctx = extend_mode_ctx(v3, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        // Not consumed: linear v1 still at One
        assert!(!ctx.is_fully_consumed());

        // Consume v1
        let ctx = consume_mode_ctx(v1, &ctx).unwrap();
        // Now fully consumed (affine and unrestricted don't need to be consumed)
        assert!(ctx.is_fully_consumed());
    }

    #[test]
    fn test_mode_ctx_counts() {
        let v1 = make_var(1);
        let v2 = make_var(2);
        let v3 = make_var(3);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::Omega, ExtendedMode::Unrestricted, &ctx);
        let ctx = extend_mode_ctx(v3, Mode::Zero, ExtendedMode::Affine, &ctx);

        assert_eq!(ctx.count_linear(), 1);
        assert_eq!(ctx.count_unrestricted(), 1);
        assert_eq!(ctx.count_consumed(), 1);
        assert_eq!(ctx.len(), 3);
    }

    #[test]
    fn test_mode_ctx_entry_validity() {
        let v = make_var(1);

        // Linear with One is valid
        let entry = ModeCtxEntry::new(v, Mode::One, ExtendedMode::Linear);
        assert!(entry.is_valid());

        // Linear with Zero is valid (consumed)
        let entry = ModeCtxEntry::new(v, Mode::Zero, ExtendedMode::Linear);
        assert!(entry.is_valid());

        // Linear with Omega is NOT valid
        let entry = ModeCtxEntry::new(v, Mode::Omega, ExtendedMode::Linear);
        assert!(!entry.is_valid());

        // Relevant with Omega is valid
        let entry = ModeCtxEntry::new(v, Mode::Omega, ExtendedMode::Relevant);
        assert!(entry.is_valid());
    }

    #[test]
    fn test_mode_ctx_without() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        let ctx2 = ctx.without(v1);
        assert_eq!(ctx2.len(), 1);
        assert_eq!(ctx2.lookup_mode(v1), Mode::Zero); // Not found
        assert_eq!(ctx2.lookup_mode(v2), Mode::Omega);
    }

    #[test]
    fn test_mode_ctx_update() {
        let v = make_var(1);

        let ctx = extend_mode_ctx(v, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        assert_eq!(ctx.lookup_mode(v), Mode::One);

        let ctx = update_mode_ctx(v, Mode::Zero, &ctx);
        assert_eq!(ctx.lookup_mode(v), Mode::Zero);
        assert_eq!(ctx.lookup_extended(v), ExtendedMode::Linear); // Preserved

        let ctx = update_mode_full(v, Mode::Omega, ExtendedMode::Unrestricted, &ctx);
        assert_eq!(ctx.lookup_mode(v), Mode::Omega);
        assert_eq!(ctx.lookup_extended(v), ExtendedMode::Unrestricted);
    }

    #[test]
    fn test_mode_ctx_can_weaken_contract() {
        let v1 = make_var(1);
        let v2 = make_var(2);
        let v3 = make_var(3);
        let v4 = make_var(4);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::One, ExtendedMode::Affine, &ctx);
        let ctx = extend_mode_ctx(v3, Mode::One, ExtendedMode::Relevant, &ctx);
        let ctx = extend_mode_ctx(v4, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        // Weakening
        assert!(!ctx.can_weaken(v1)); // Linear: no
        assert!(ctx.can_weaken(v2)); // Affine: yes
        assert!(!ctx.can_weaken(v3)); // Relevant: no
        assert!(ctx.can_weaken(v4)); // Unrestricted: yes

        // Contraction
        assert!(!ctx.can_contract(v1)); // Linear: no
        assert!(!ctx.can_contract(v2)); // Affine: no
        assert!(ctx.can_contract(v3)); // Relevant: yes
        assert!(ctx.can_contract(v4)); // Unrestricted: yes
    }

    #[test]
    fn test_mode_ctx_iterator() {
        let v1 = make_var(1);
        let v2 = make_var(2);

        let ctx = extend_mode_ctx(v1, Mode::One, ExtendedMode::Linear, &empty_mode_ctx());
        let ctx = extend_mode_ctx(v2, Mode::Omega, ExtendedMode::Unrestricted, &ctx);

        let vars: Vec<_> = ctx.iter().map(|e| e.var).collect();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&v1));
        assert!(vars.contains(&v2));
    }
}
