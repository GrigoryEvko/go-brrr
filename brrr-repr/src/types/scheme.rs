//! Type schemes and quantified types
//!
//! Mirrors F* BrrrTypes.fsti type_scheme, moded_type, regioned_type.
//!
//! # Kind-Annotated Type Variables
//! Type variables now carry kind annotations, enabling higher-kinded types:
//! - `α : *` - a proper type variable
//! - `F : * -> *` - a type constructor variable (like `Option`, `Vec`)
//! - `M : * -> * -> *` - a binary type constructor (like `Result`, `Map`)

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::kind::{Kind, KindedVar};
use super::region::Region;
use super::BrrrType;
use crate::modes::Mode;

/// Effect variable identifier (interned string)
pub type EffectVar = Spur;

/// Type scheme with universal quantification over kinded type variables
/// `∀(α : *)(F : * -> *), ε. τ`
///
/// Maps to F*:
/// ```fstar
/// type type_scheme = {
///   type_vars: list (type_var * kind);  (* Now with kind annotations *)
///   effect_vars: list string;
///   body: brrr_type;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeScheme {
    /// Type variables with their kinds (α : *, F : * -> *, etc.)
    pub type_vars: Vec<KindedVar>,
    /// Effect variables (ε, ρ, ...)
    pub effect_vars: Vec<EffectVar>,
    /// The quantified type body
    pub body: BrrrType,
}

impl TypeScheme {
    /// Create a monomorphic scheme (no quantification)
    #[must_use]
    pub fn mono(ty: BrrrType) -> Self {
        Self {
            type_vars: Vec::new(),
            effect_vars: Vec::new(),
            body: ty,
        }
    }

    /// Create a type-polymorphic scheme with kind `*` for all variables
    ///
    /// This is a convenience method when all type variables are proper types.
    /// For higher-kinded types, use `poly_kinded` instead.
    #[must_use]
    pub fn poly(type_vars: Vec<super::TypeVar>, body: BrrrType) -> Self {
        Self {
            type_vars: type_vars.into_iter().map(KindedVar::of_type).collect(),
            effect_vars: Vec::new(),
            body,
        }
    }

    /// Create a type-polymorphic scheme with explicit kind annotations
    #[must_use]
    pub fn poly_kinded(type_vars: Vec<KindedVar>, body: BrrrType) -> Self {
        Self {
            type_vars,
            effect_vars: Vec::new(),
            body,
        }
    }

    /// Create a fully polymorphic scheme with kind `*` for all type variables
    #[must_use]
    pub fn full(
        type_vars: Vec<super::TypeVar>,
        effect_vars: Vec<EffectVar>,
        body: BrrrType,
    ) -> Self {
        Self {
            type_vars: type_vars.into_iter().map(KindedVar::of_type).collect(),
            effect_vars,
            body,
        }
    }

    /// Create a fully polymorphic scheme with explicit kind annotations
    #[must_use]
    pub fn full_kinded(
        type_vars: Vec<KindedVar>,
        effect_vars: Vec<EffectVar>,
        body: BrrrType,
    ) -> Self {
        Self {
            type_vars,
            effect_vars,
            body,
        }
    }

    /// Is this a monomorphic type (no quantification)?
    #[must_use]
    pub fn is_mono(&self) -> bool {
        self.type_vars.is_empty() && self.effect_vars.is_empty()
    }

    /// Get the number of type parameters
    #[must_use]
    pub fn type_arity(&self) -> usize {
        self.type_vars.len()
    }

    /// Get the number of effect parameters
    #[must_use]
    pub fn effect_arity(&self) -> usize {
        self.effect_vars.len()
    }

    /// Check if any type variable has a higher kind (non-`*`)
    #[must_use]
    pub fn has_higher_kinds(&self) -> bool {
        self.type_vars.iter().any(|kv| !kv.kind.is_type())
    }

    /// Get the kind of a type variable by its identifier
    #[must_use]
    pub fn kind_of(&self, var: super::TypeVar) -> Option<&Kind> {
        self.type_vars
            .iter()
            .find(|kv| kv.var == var)
            .map(|kv| &kv.kind)
    }

    /// Format as `∀(α : *)(F : * -> *), ε. τ`
    #[must_use]
    pub fn format(&self) -> String {
        if self.is_mono() {
            return format!("{:?}", self.body);
        }

        // Format type variables with kinds (omit kind for simple `*`)
        let type_vars: Vec<String> = self
            .type_vars
            .iter()
            .enumerate()
            .map(|(i, kv)| {
                let var_name = format!("α{}", subscript(i));
                if kv.kind == Kind::Star {
                    var_name
                } else {
                    format!("({} : {})", var_name, kv.kind.format())
                }
            })
            .collect();

        let effect_vars: Vec<String> = self
            .effect_vars
            .iter()
            .enumerate()
            .map(|(i, _)| format!("ε{}", subscript(i)))
            .collect();

        let vars = if effect_vars.is_empty() {
            type_vars.join(" ")
        } else {
            format!("{}, {}", type_vars.join(" "), effect_vars.join(" "))
        };

        format!("∀{}. {:?}", vars, self.body)
    }
}

/// Convert index to subscript characters for pretty printing
fn subscript(n: usize) -> String {
    if n == 0 {
        return String::new();
    }
    n.to_string()
        .chars()
        .map(|c| match c {
            '0' => '₀',
            '1' => '₁',
            '2' => '₂',
            '3' => '₃',
            '4' => '₄',
            '5' => '₅',
            '6' => '₆',
            '7' => '₇',
            '8' => '₈',
            '9' => '₉',
            _ => c,
        })
        .collect()
}

impl Default for TypeScheme {
    fn default() -> Self {
        Self::mono(BrrrType::UNIT)
    }
}

/// Type with mode annotation
/// `τ @m` where m ∈ {1, aff, ω}
///
/// Maps to F*:
/// ```fstar
/// type moded_type = {
///   ty: brrr_type;
///   mode: mode;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ModedType {
    /// The base type
    pub ty: BrrrType,
    /// Usage mode
    pub mode: Mode,
}

impl ModedType {
    /// Create a linear type (use exactly once)
    pub fn linear(ty: BrrrType) -> Self {
        Self {
            ty,
            mode: Mode::One,
        }
    }

    /// Create an affine type (use at most once)
    /// Note: Affine semantics (can drop) is tracked via ExtendedMode.
    /// Base Mode is One since the resource starts with one available use.
    pub fn affine(ty: BrrrType) -> Self {
        Self {
            ty,
            mode: Mode::One, // Affine starts as One, can transition to Zero (dropped)
        }
    }

    /// Create an unrestricted type (use any number of times)
    pub fn unrestricted(ty: BrrrType) -> Self {
        Self {
            ty,
            mode: Mode::Omega,
        }
    }

    /// Format as `τ @mode`
    pub fn format(&self) -> String {
        format!("{:?} @{}", self.ty, self.mode.as_str())
    }
}

impl Default for ModedType {
    fn default() -> Self {
        Self::unrestricted(BrrrType::UNIT)
    }
}

/// Type with region annotation
/// `τ ⟦'r⟧` for lifetime tracking
///
/// Maps to F*:
/// ```fstar
/// type regioned_type = {
///   base_type: brrr_type;
///   region: region;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RegionedType {
    /// The base type
    pub base_type: BrrrType,
    /// The region/lifetime
    pub region: Region,
}

impl RegionedType {
    /// Create a static-lifetime type
    pub fn static_lifetime(ty: BrrrType) -> Self {
        Self {
            base_type: ty,
            region: Region::Static,
        }
    }

    /// Create a named-region type
    pub fn named(ty: BrrrType, name: Spur) -> Self {
        Self {
            base_type: ty,
            region: Region::Named(name),
        }
    }

    /// Create a fresh-region type
    pub fn fresh(ty: BrrrType, id: u32) -> Self {
        Self {
            base_type: ty,
            region: Region::Fresh(id),
        }
    }

    /// Format as `τ ⟦'r⟧`
    pub fn format(&self) -> String {
        format!("{:?} ⟦{}⟧", self.base_type, self.region.format())
    }
}

impl Default for RegionedType {
    fn default() -> Self {
        Self::static_lifetime(BrrrType::UNIT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::Rodeo;

    #[test]
    fn test_type_scheme_mono() {
        let scheme = TypeScheme::mono(BrrrType::BOOL);
        assert!(scheme.is_mono());
        assert_eq!(scheme.type_arity(), 0);
        assert!(!scheme.has_higher_kinds());
    }

    #[test]
    fn test_type_scheme_poly() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");
        let beta = rodeo.get_or_intern("beta");

        let scheme = TypeScheme::poly(
            vec![alpha, beta],
            BrrrType::Func(Box::new(crate::types::FuncType::pure(
                vec![crate::types::ParamType::unnamed(BrrrType::Var(alpha))],
                BrrrType::Var(beta),
            ))),
        );

        assert!(!scheme.is_mono());
        assert_eq!(scheme.type_arity(), 2);
        assert!(!scheme.has_higher_kinds());

        // All variables should have kind *
        assert_eq!(scheme.kind_of(alpha), Some(&Kind::Star));
        assert_eq!(scheme.kind_of(beta), Some(&Kind::Star));
    }

    #[test]
    fn test_type_scheme_higher_kinded() {
        let mut rodeo = Rodeo::default();
        let f = rodeo.get_or_intern("F");
        let a = rodeo.get_or_intern("a");

        // ∀(F : * -> *)(a : *). F<a>
        let scheme = TypeScheme::poly_kinded(
            vec![
                KindedVar::new(f, Kind::type_to_type()),
                KindedVar::of_type(a),
            ],
            BrrrType::App(Box::new(BrrrType::Var(f)), vec![BrrrType::Var(a)]),
        );

        assert!(!scheme.is_mono());
        assert_eq!(scheme.type_arity(), 2);
        assert!(scheme.has_higher_kinds());

        assert_eq!(scheme.kind_of(f), Some(&Kind::type_to_type()));
        assert_eq!(scheme.kind_of(a), Some(&Kind::Star));
    }

    #[test]
    fn test_type_scheme_format() {
        let scheme = TypeScheme::mono(BrrrType::BOOL);
        assert!(scheme.format().contains("Bool"));

        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("alpha");

        let poly = TypeScheme::poly(vec![alpha], BrrrType::Var(alpha));
        let formatted = poly.format();
        assert!(formatted.starts_with("∀"));
    }

    #[test]
    fn test_moded_type() {
        let linear = ModedType::linear(BrrrType::STRING);
        assert_eq!(linear.mode, Mode::One);

        let unrestricted = ModedType::unrestricted(BrrrType::STRING);
        assert_eq!(unrestricted.mode, Mode::Omega);
    }

    #[test]
    fn test_subscript_formatting() {
        assert_eq!(subscript(0), "");
        assert_eq!(subscript(1), "₁");
        assert_eq!(subscript(12), "₁₂");
        assert_eq!(subscript(123), "₁₂₃");
    }
}
