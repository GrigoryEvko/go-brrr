//! Mode (linearity) and permission types
//!
//! Mirrors F* Modes.fsti: mode, ref_kind, fraction

use serde::{Deserialize, Serialize};

/// Usage mode - linear/affine/relevant typing
/// Maps to F*: type mode = MOne | MMany | MOmega
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[repr(u8)]
pub enum Mode {
    /// Use exactly once (linear) - `@1` or `@lin`
    One = 0,
    /// Use at most once (affine) - `@aff`
    /// Note: F* uses MMany which we interpret as affine here
    Many = 1,
    /// Use any number of times (unrestricted) - `@ω` or `@unr`
    #[default]
    Omega = 2,
}

impl Mode {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "0" | "zero" => None, // Zero mode is absence, not a value
            "1" | "one" | "lin" | "linear" => Some(Self::One),
            "aff" | "affine" | "many" => Some(Self::Many),
            "ω" | "omega" | "w" | "unr" | "unrestricted" => Some(Self::Omega),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::One => "1",
            Self::Many => "aff",
            Self::Omega => "ω",
        }
    }

    /// Format with full name
    pub const fn as_name(self) -> &'static str {
        match self {
            Self::One => "linear",
            Self::Many => "affine",
            Self::Omega => "unrestricted",
        }
    }

    /// Join (least upper bound) in the mode lattice
    /// 1 ⊔ 1 = 1, 1 ⊔ ω = ω, ω ⊔ ω = ω
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::Many, _) | (_, Self::Many) => Self::Many,
            (Self::One, Self::One) => Self::One,
        }
    }

    /// Meet (greatest lower bound) in the mode lattice
    /// 1 ⊓ 1 = 1, 1 ⊓ ω = 1, ω ⊓ ω = ω
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::One, _) | (_, Self::One) => Self::One,
            (Self::Many, _) | (_, Self::Many) => Self::Many,
            (Self::Omega, Self::Omega) => Self::Omega,
        }
    }

    /// Submode relation: self ⊑ other
    pub const fn submode(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::One, _) | (Self::Many, Self::Many | Self::Omega) | (Self::Omega, Self::Omega)
        )
    }

    /// Mode multiplication (for sequential composition)
    /// 1 * m = m, ω * 0 = 0, ω * ω = ω
    pub const fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::One, m) | (m, Self::One) => m,
            (Self::Omega, Self::Omega) => Self::Omega,
            (Self::Many, m) | (m, Self::Many) => m.meet(Self::Many),
        }
    }

    /// Mode addition (for parallel composition)
    /// 0 + m = m, 1 + 1 = ω, ω + m = ω
    pub const fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Omega, _) | (_, Self::Omega) => Self::Omega,
            (Self::One, Self::One) => Self::Omega,
            (Self::One, Self::Many) | (Self::Many, Self::One) => Self::Omega,
            (Self::Many, Self::Many) => Self::Omega,
        }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum ExtendedMode {
    /// Use exactly once (linear) - no weakening, no contraction
    Linear = 0,
    /// Use at most once (affine) - weakening allowed
    Affine = 1,
    /// Use at least once (relevant) - contraction allowed
    Relevant = 2,
    /// Use any number (unrestricted) - both allowed
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
    pub const fn to_mode(self) -> Mode {
        match self {
            Self::Linear => Mode::One,
            Self::Affine => Mode::Many,
            Self::Relevant => Mode::One, // Must use at least once
            Self::Unrestricted => Mode::Omega,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mode_lattice() {
        // Join tests
        assert_eq!(Mode::One.join(Mode::One), Mode::One);
        assert_eq!(Mode::One.join(Mode::Omega), Mode::Omega);
        assert_eq!(Mode::Omega.join(Mode::Omega), Mode::Omega);

        // Meet tests
        assert_eq!(Mode::One.meet(Mode::One), Mode::One);
        assert_eq!(Mode::One.meet(Mode::Omega), Mode::One);
        assert_eq!(Mode::Omega.meet(Mode::Omega), Mode::Omega);

        // Submode tests
        assert!(Mode::One.submode(Mode::One));
        assert!(Mode::One.submode(Mode::Omega));
        assert!(!Mode::Omega.submode(Mode::One));
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
}
