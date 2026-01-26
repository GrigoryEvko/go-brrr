//! Pattern types for matching
//!
//! Mirrors F* Expressions.fsti pattern and pattern'.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::location::{Range, WithLoc};
use super::Literal;
use crate::types::{BrrrType, TypeName};

/// Pattern with source location
pub type Pattern = WithLoc<Pattern_>;

/// Pattern underlying type
/// Maps to F*:
/// ```fstar
/// type pattern' =
///   | PatWild
///   | PatVar : var_id -> pattern'
///   | PatLit : literal -> pattern'
///   | PatTuple : list pattern -> pattern'
///   | PatStruct : type_name -> list (string & pattern) -> pattern'
///   | PatVariant : type_name -> string -> list pattern -> pattern'
///   | PatOr : pattern -> pattern -> pattern'
///   | PatGuard : pattern -> expr -> pattern'
///   | PatRef : pattern -> pattern'
///   | PatBox : pattern -> pattern'
///   | PatRest : option var_id -> pattern'
///   | PatAs : pattern -> var_id -> pattern'
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Pattern_ {
    /// Wildcard pattern `_`
    Wild,

    /// Variable binding pattern `x`
    Var(Spur),

    /// Literal pattern `42`, `"hello"`, `true`
    Lit(Literal),

    /// Tuple pattern `(p₁, p₂, ...)`
    Tuple(Vec<Pattern>),

    /// Struct pattern `Point { x, y }`
    Struct {
        name: TypeName,
        fields: Vec<(Spur, Pattern)>,
    },

    /// Enum variant pattern `Some(x)`, `Color::Red`
    Variant {
        type_name: TypeName,
        variant: Spur,
        fields: Vec<Pattern>,
    },

    /// Or-pattern `p₁ | p₂`
    Or(Box<Pattern>, Box<Pattern>),

    /// Guarded pattern `p if e`
    Guard(Box<Pattern>, Box<super::Expr>),

    /// Reference pattern `&p`
    Ref(Box<Pattern>),

    /// Box pattern `box p`
    Box(Box<Pattern>),

    /// Rest pattern `...` or `...rest`
    Rest(Option<Spur>),

    /// As-pattern `p @ x`
    As(Box<Pattern>, Spur),

    /// Type pattern for runtime type matching
    /// Used in Go type switches, TypeScript typeof/instanceof, Java instanceof, etc.
    /// Matches if the runtime type of the scrutinee equals the expected type.
    /// `case int:` in Go becomes `Type { expected: Int, binding: Some("v") }`
    Type {
        /// The expected type to match against
        expected: BrrrType,
        /// Optional variable binding with narrowed type
        binding: Option<Spur>,
    },
}

impl Pattern_ {
    /// Create a wildcard pattern
    pub const WILD: Self = Self::Wild;

    /// Create a variable pattern
    pub fn var(name: Spur) -> Self {
        Self::Var(name)
    }

    /// Create a literal pattern
    pub fn lit(lit: Literal) -> Self {
        Self::Lit(lit)
    }

    /// Create a tuple pattern
    pub fn tuple(elems: Vec<Pattern>) -> Self {
        Self::Tuple(elems)
    }

    /// Create a struct pattern
    pub fn struct_pat(name: TypeName, fields: Vec<(Spur, Pattern)>) -> Self {
        Self::Struct { name, fields }
    }

    /// Create a variant pattern
    pub fn variant(type_name: TypeName, variant: Spur, fields: Vec<Pattern>) -> Self {
        Self::Variant {
            type_name,
            variant,
            fields,
        }
    }

    /// Create an or-pattern
    pub fn or(left: Pattern, right: Pattern) -> Self {
        Self::Or(Box::new(left), Box::new(right))
    }

    /// Create a guarded pattern
    pub fn guard(pattern: Pattern, guard: super::Expr) -> Self {
        Self::Guard(Box::new(pattern), Box::new(guard))
    }

    /// Create a reference pattern
    pub fn ref_pat(inner: Pattern) -> Self {
        Self::Ref(Box::new(inner))
    }

    /// Create a box pattern
    pub fn box_pat(inner: Pattern) -> Self {
        Self::Box(Box::new(inner))
    }

    /// Create a rest pattern
    pub fn rest(binding: Option<Spur>) -> Self {
        Self::Rest(binding)
    }

    /// Create an as-pattern
    pub fn as_pat(pattern: Pattern, binding: Spur) -> Self {
        Self::As(Box::new(pattern), binding)
    }

    /// Create a type pattern for runtime type matching
    /// Used in Go type switches, TypeScript typeof/instanceof, Java instanceof, etc.
    pub fn type_pat(expected: BrrrType, binding: Option<Spur>) -> Self {
        Self::Type { expected, binding }
    }

    /// Get the discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Wild => 0,
            Self::Var(_) => 1,
            Self::Lit(_) => 2,
            Self::Tuple(_) => 3,
            Self::Struct { .. } => 4,
            Self::Variant { .. } => 5,
            Self::Or(_, _) => 6,
            Self::Guard(_, _) => 7,
            Self::Ref(_) => 8,
            Self::Box(_) => 9,
            Self::Rest(_) => 10,
            Self::As(_, _) => 11,
            Self::Type { .. } => 12,
        }
    }

    /// Is this an irrefutable pattern (always matches)?
    pub fn is_irrefutable(&self) -> bool {
        match self {
            Self::Wild | Self::Var(_) | Self::Rest(_) => true,
            Self::Tuple(pats) => pats.iter().all(|p| p.value.is_irrefutable()),
            Self::Ref(p) | Self::Box(p) | Self::As(p, _) => p.value.is_irrefutable(),
            Self::Struct { fields, .. } => fields.iter().all(|(_, p)| p.value.is_irrefutable()),
            // Type patterns are refutable - they only match specific runtime types
            Self::Lit(_) | Self::Variant { .. } | Self::Or(_, _) | Self::Guard(_, _) | Self::Type { .. } => false,
        }
    }

    /// Get all bound variable names
    pub fn bound_vars(&self) -> Vec<Spur> {
        match self {
            Self::Wild | Self::Lit(_) | Self::Rest(None) => vec![],
            Self::Var(v) | Self::Rest(Some(v)) => vec![*v],
            Self::As(p, v) => {
                let mut vars = p.value.bound_vars();
                vars.push(*v);
                vars
            }
            Self::Type { binding: Some(v), .. } => vec![*v],
            Self::Type { binding: None, .. } => vec![],
            Self::Tuple(pats) => pats.iter().flat_map(|p| p.value.bound_vars()).collect(),
            Self::Struct { fields, .. } => {
                fields.iter().flat_map(|(_, p)| p.value.bound_vars()).collect()
            }
            Self::Variant { fields, .. } => {
                fields.iter().flat_map(|p| p.value.bound_vars()).collect()
            }
            Self::Or(l, _r) => {
                // Or-patterns must bind the same vars in both branches
                l.value.bound_vars()
            }
            Self::Guard(p, _) | Self::Ref(p) | Self::Box(p) => p.value.bound_vars(),
        }
    }
}

impl Default for Pattern_ {
    fn default() -> Self {
        Self::Wild
    }
}

impl Pattern {
    /// Create a synthetic wildcard pattern
    pub fn wild() -> Self {
        WithLoc::synthetic(Pattern_::WILD)
    }

    /// Create a synthetic variable pattern
    pub fn var(name: Spur) -> Self {
        WithLoc::synthetic(Pattern_::var(name))
    }

    /// Create a located wildcard pattern
    pub fn wild_at(range: Range) -> Self {
        WithLoc::new(Pattern_::WILD, range)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_pattern_irrefutable() {
        assert!(Pattern_::WILD.is_irrefutable());

        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");
        assert!(Pattern_::var(x).is_irrefutable());

        assert!(!Pattern_::lit(Literal::i32(42)).is_irrefutable());
    }

    #[test]
    fn test_pattern_bound_vars() {
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");
        let y = rodeo.get_or_intern("y");

        let tuple_pat = Pattern_::tuple(vec![Pattern::var(x), Pattern::var(y)]);
        let vars = tuple_pat.bound_vars();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&x));
        assert!(vars.contains(&y));
    }
}
