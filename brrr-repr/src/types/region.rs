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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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

    /// Check if this region outlives another region
    ///
    /// Lifetime ordering rules:
    /// - `'static` outlives all regions
    /// - Named regions only outlive themselves (conservative)
    /// - Fresh regions: earlier (lower number) outlives later
    /// - Scope regions: outer (lower depth) outlives inner
    ///
    /// # Arguments
    /// * `other` - The potentially shorter-lived region
    ///
    /// # Returns
    /// `true` if `self` outlives `other` based on the region structure
    pub fn outlives(&self, other: &Self) -> bool {
        match (self, other) {
            // Static outlives everything
            (Self::Static, _) => true,

            // Named region only outlives itself (conservative without constraint solving)
            (Self::Named(a), Self::Named(b)) => a == b,

            // Fresh region: earlier (lower number) outlives later
            // Fresh(0) was created before Fresh(1), so it lives longer
            (Self::Fresh(n1), Self::Fresh(n2)) => n1 <= n2,

            // Scope region: outer (lower depth) outlives inner
            // Scope(0) is the outermost scope, Scope(1) is inside it, etc.
            (Self::Scope(d1), Self::Scope(d2)) => d1 <= d2,

            // Nothing except static outlives static
            (_, Self::Static) => false,

            // Cross-category: generally cannot determine without constraints
            // Fresh regions are typically more local than named regions
            // Scope regions are typically more local than fresh regions
            // Conservative: return false for cross-category comparisons
            _ => false,
        }
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
    ///
    /// Follows F* `combine_variance` semantics:
    /// - Bivariant absorbs everything (unused position)
    /// - Invariant absorbs next (must be exactly equal)
    /// - Covariant + Covariant = Covariant
    /// - Contravariant + Contravariant = Covariant (double negation)
    /// - Covariant + Contravariant = Contravariant
    /// - Contravariant + Covariant = Contravariant
    pub const fn compose(self, other: Self) -> Self {
        match (self, other) {
            // Bivariant absorbs everything (F* priority: first)
            (Self::Bivariant, _) | (_, Self::Bivariant) => Self::Bivariant,
            // Invariant absorbs next (F* priority: second)
            (Self::Invariant, _) | (_, Self::Invariant) => Self::Invariant,
            // Same variance preserves direction
            (Self::Covariant, Self::Covariant) => Self::Covariant,
            // Double negation: contra + contra = covariant
            (Self::Contravariant, Self::Contravariant) => Self::Covariant,
            // Mixed: one negation = contravariant
            (Self::Covariant, Self::Contravariant)
            | (Self::Contravariant, Self::Covariant) => Self::Contravariant,
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
        // Covariant + Contravariant = Contravariant
        assert_eq!(
            Variance::Covariant.compose(Variance::Contravariant),
            Variance::Contravariant
        );
        // Contravariant + Contravariant = Covariant (double negation)
        assert_eq!(
            Variance::Contravariant.compose(Variance::Contravariant),
            Variance::Covariant
        );
        // Covariant + Invariant = Invariant
        assert_eq!(
            Variance::Covariant.compose(Variance::Invariant),
            Variance::Invariant
        );
        // Covariant + Covariant = Covariant
        assert_eq!(
            Variance::Covariant.compose(Variance::Covariant),
            Variance::Covariant
        );
        // Bivariant absorbs Invariant (F* priority: Bivariant first)
        assert_eq!(
            Variance::Bivariant.compose(Variance::Invariant),
            Variance::Bivariant
        );
        assert_eq!(
            Variance::Invariant.compose(Variance::Bivariant),
            Variance::Bivariant
        );
        // Bivariant absorbs everything
        assert_eq!(
            Variance::Bivariant.compose(Variance::Covariant),
            Variance::Bivariant
        );
        assert_eq!(
            Variance::Bivariant.compose(Variance::Contravariant),
            Variance::Bivariant
        );
    }

    #[test]
    fn test_region_outlives() {
        let mut rodeo = lasso::Rodeo::default();
        let a = Region::Named(rodeo.get_or_intern("a"));
        let b = Region::Named(rodeo.get_or_intern("b"));

        // Static outlives everything
        assert!(Region::Static.outlives(&Region::Static));
        assert!(Region::Static.outlives(&Region::Scope(0)));
        assert!(Region::Static.outlives(&Region::Fresh(0)));
        assert!(Region::Static.outlives(&a));

        // Same region outlives itself
        assert!(Region::Scope(1).outlives(&Region::Scope(1)));
        assert!(Region::Fresh(5).outlives(&Region::Fresh(5)));
        assert!(a.outlives(&a));

        // Outer scope outlives inner scope
        assert!(Region::Scope(0).outlives(&Region::Scope(1)));
        assert!(Region::Scope(0).outlives(&Region::Scope(5)));
        assert!(!Region::Scope(2).outlives(&Region::Scope(1)));

        // Earlier fresh outlives later fresh
        assert!(Region::Fresh(0).outlives(&Region::Fresh(1)));
        assert!(Region::Fresh(0).outlives(&Region::Fresh(10)));
        assert!(!Region::Fresh(5).outlives(&Region::Fresh(3)));

        // Non-static cannot outlive static
        assert!(!Region::Scope(0).outlives(&Region::Static));
        assert!(!Region::Fresh(0).outlives(&Region::Static));
        assert!(!a.outlives(&Region::Static));

        // Different named regions don't outlive each other (conservative)
        assert!(!a.outlives(&b));
        assert!(!b.outlives(&a));

        // Cross-category comparisons are conservative (false)
        assert!(!Region::Scope(0).outlives(&Region::Fresh(0)));
        assert!(!Region::Fresh(0).outlives(&Region::Scope(0)));
        assert!(!a.outlives(&Region::Scope(0)));
    }
}
