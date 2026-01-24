//! Region (lifetime), visibility, and repr attribute types
//!
//! Mirrors F* BrrrTypes.fsti region, visibility, repr_attr.

use lasso::Spur;
use serde::{Deserialize, Serialize};

/// Region (lifetime) for borrow checking
/// Maps to F*:
/// ```fstar
/// type region =
///   | RStatic
///   | RNamed : string -> region
///   | RFresh : nat -> region
///   | RScope : nat -> region
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Region {
    /// `'static` - lives for entire program
    Static,
    /// Named region `'a`, `'b`, etc.
    Named(Spur),
    /// Fresh region from `letregion` - `'_0`, `'_1`
    Fresh(u32),
    /// Scope-bound region - `'#0`, `'#1`
    Scope(u32),
}

impl Region {
    /// Parse from text format
    pub fn from_str(s: &str, interner: &mut lasso::Rodeo) -> Option<Self> {
        if s == "'static" || s == "static" {
            return Some(Self::Static);
        }

        if let Some(rest) = s.strip_prefix("'_") {
            if let Ok(n) = rest.parse::<u32>() {
                return Some(Self::Fresh(n));
            }
        }

        if let Some(rest) = s.strip_prefix("'#") {
            if let Ok(n) = rest.parse::<u32>() {
                return Some(Self::Scope(n));
            }
        }

        if let Some(rest) = s.strip_prefix('\'') {
            return Some(Self::Named(interner.get_or_intern(rest)));
        }

        None
    }

    /// Format as string
    pub fn format(&self) -> String {
        match self {
            Self::Static => "'static".to_string(),
            Self::Named(_) => "'name".to_string(), // Would need interner
            Self::Fresh(n) => format!("'_{n}"),
            Self::Scope(n) => format!("'#{n}"),
        }
    }

    /// Is this the static region?
    pub const fn is_static(self) -> bool {
        matches!(self, Self::Static)
    }
}

impl Default for Region {
    fn default() -> Self {
        Self::Static
    }
}

/// Visibility qualifier
/// Maps to F*:
/// ```fstar
/// type visibility = VisPublic | VisPrivate | VisMod
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[repr(u8)]
pub enum Visibility {
    /// `pub` - visible everywhere
    #[default]
    Public = 0,
    /// `priv` - visible only in defining scope
    Private = 1,
    /// `mod` - visible in module
    Module = 2,
}

impl Visibility {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "pub" | "public" => Some(Self::Public),
            "priv" | "private" => Some(Self::Private),
            "mod" | "module" | "crate" => Some(Self::Module),
            _ => None,
        }
    }

    /// Format as string
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Public => "pub",
            Self::Private => "priv",
            Self::Module => "mod",
        }
    }
}

/// Representation attribute for structs
/// Maps to F*:
/// ```fstar
/// type repr_attr =
///   | ReprRust
///   | ReprC
///   | ReprPacked
///   | ReprTransparent
///   | ReprAlign : valid_alignment -> repr_attr
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum ReprAttr {
    /// Default Rust representation (unspecified layout)
    #[default]
    Rust,
    /// C-compatible layout `#[repr(C)]`
    C,
    /// Packed layout `#[repr(packed)]`
    Packed,
    /// Transparent (same layout as single field) `#[repr(transparent)]`
    Transparent,
    /// Specific alignment `#[repr(align(N))]`
    Align(u32),
}

impl ReprAttr {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "Rust" | "rust" => Some(Self::Rust),
            "C" | "c" => Some(Self::C),
            "packed" => Some(Self::Packed),
            "transparent" => Some(Self::Transparent),
            _ => {
                if let Some(rest) = s.strip_prefix("align(") {
                    if let Some(num) = rest.strip_suffix(')') {
                        if let Ok(n) = num.parse::<u32>() {
                            return Some(Self::Align(n));
                        }
                    }
                }
                None
            }
        }
    }

    /// Format as string
    pub fn as_str(&self) -> String {
        match self {
            Self::Rust => "Rust".to_string(),
            Self::C => "C".to_string(),
            Self::Packed => "packed".to_string(),
            Self::Transparent => "transparent".to_string(),
            Self::Align(n) => format!("align({n})"),
        }
    }

    /// Format as Rust attribute
    pub fn as_attr(&self) -> Option<String> {
        match self {
            Self::Rust => None,
            Self::C => Some("#[repr(C)]".to_string()),
            Self::Packed => Some("#[repr(packed)]".to_string()),
            Self::Transparent => Some("#[repr(transparent)]".to_string()),
            Self::Align(n) => Some(format!("#[repr(align({n}))]")),
        }
    }
}

/// Variance annotation for type parameters
/// Maps to F*: type variance = Covariant | Contravariant | Invariant | Bivariant
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[repr(u8)]
pub enum Variance {
    /// `+T` - covariant (T <: U implies F<T> <: F<U>)
    #[default]
    Covariant = 0,
    /// `-T` - contravariant (T <: U implies F<U> <: F<T>)
    Contravariant = 1,
    /// `=T` - invariant (no subtyping relationship)
    Invariant = 2,
    /// `±T` - bivariant (both directions, unused position)
    Bivariant = 3,
}

impl Variance {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "+" | "co" | "covariant" => Some(Self::Covariant),
            "-" | "contra" | "contravariant" => Some(Self::Contravariant),
            "=" | "inv" | "invariant" => Some(Self::Invariant),
            "+-" | "-+" | "bi" | "bivariant" => Some(Self::Bivariant),
            _ => None,
        }
    }

    /// Format as symbol
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Covariant => "+",
            Self::Contravariant => "-",
            Self::Invariant => "=",
            Self::Bivariant => "±",
        }
    }

    /// Combine variances (for nested type constructors)
    pub const fn compose(self, other: Self) -> Self {
        match (self, other) {
            // Invariant absorbs
            (Self::Invariant, _) | (_, Self::Invariant) => Self::Invariant,
            // Bivariant absorbs
            (Self::Bivariant, _) | (_, Self::Bivariant) => Self::Bivariant,
            // Covariant is identity
            (Self::Covariant, v) | (v, Self::Covariant) => v,
            // Contravariant negates
            (Self::Contravariant, Self::Contravariant) => Self::Covariant,
        }
    }

    /// Negate variance (for contravariant positions)
    pub const fn negate(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Invariant => Self::Invariant,
            Self::Bivariant => Self::Bivariant,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_region_parse() {
        let mut rodeo = lasso::Rodeo::default();

        assert_eq!(Region::from_str("'static", &mut rodeo), Some(Region::Static));
        assert_eq!(Region::from_str("'_42", &mut rodeo), Some(Region::Fresh(42)));
        assert_eq!(Region::from_str("'#3", &mut rodeo), Some(Region::Scope(3)));
        assert!(matches!(Region::from_str("'a", &mut rodeo), Some(Region::Named(_))));
    }

    #[test]
    fn test_repr_attr_parse() {
        assert_eq!(ReprAttr::from_str("C"), Some(ReprAttr::C));
        assert_eq!(ReprAttr::from_str("packed"), Some(ReprAttr::Packed));
        assert_eq!(ReprAttr::from_str("align(16)"), Some(ReprAttr::Align(16)));
    }

    #[test]
    fn test_variance_compose() {
        assert_eq!(
            Variance::Covariant.compose(Variance::Contravariant),
            Variance::Contravariant
        );
        assert_eq!(
            Variance::Contravariant.compose(Variance::Contravariant),
            Variance::Covariant
        );
        assert_eq!(
            Variance::Covariant.compose(Variance::Invariant),
            Variance::Invariant
        );
    }
}
