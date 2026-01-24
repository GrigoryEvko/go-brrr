//! Type schemes and quantified types
//!
//! Mirrors F* BrrrTypes.fsti type_scheme, moded_type, regioned_type.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::region::Region;
use super::BrrrType;
use crate::modes::Mode;

/// Type variable with kind annotation
pub type TypeVar = Spur;

/// Effect variable
pub type EffectVar = Spur;

/// Type scheme with universal quantification
/// `∀α₁...αₙ, ε₁...εₘ. τ`
///
/// Maps to F*:
/// ```fstar
/// type type_scheme = {
///   type_vars: list type_var;
///   effect_vars: list string;
///   body: brrr_type;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypeScheme {
    /// Type variables (α, β, ...)
    pub type_vars: Vec<TypeVar>,
    /// Effect variables (ε, ρ, ...)
    pub effect_vars: Vec<EffectVar>,
    /// The quantified type body
    pub body: BrrrType,
}

impl TypeScheme {
    /// Create a monomorphic scheme (no quantification)
    pub fn mono(ty: BrrrType) -> Self {
        Self {
            type_vars: Vec::new(),
            effect_vars: Vec::new(),
            body: ty,
        }
    }

    /// Create a type-polymorphic scheme
    pub fn poly(type_vars: Vec<TypeVar>, body: BrrrType) -> Self {
        Self {
            type_vars,
            effect_vars: Vec::new(),
            body,
        }
    }

    /// Create a fully polymorphic scheme
    pub fn full(type_vars: Vec<TypeVar>, effect_vars: Vec<EffectVar>, body: BrrrType) -> Self {
        Self {
            type_vars,
            effect_vars,
            body,
        }
    }

    /// Is this a monomorphic type (no quantification)?
    pub fn is_mono(&self) -> bool {
        self.type_vars.is_empty() && self.effect_vars.is_empty()
    }

    /// Get the number of type parameters
    pub fn type_arity(&self) -> usize {
        self.type_vars.len()
    }

    /// Get the number of effect parameters
    pub fn effect_arity(&self) -> usize {
        self.effect_vars.len()
    }

    /// Format as `∀α β, ε. τ`
    pub fn format(&self) -> String {
        if self.is_mono() {
            return format!("{:?}", self.body);
        }

        let type_vars: Vec<String> = self.type_vars.iter().map(|_| "α".to_string()).collect();
        let effect_vars: Vec<String> = self.effect_vars.iter().map(|_| "ε".to_string()).collect();

        let vars = if effect_vars.is_empty() {
            type_vars.join(" ")
        } else {
            format!("{}, {}", type_vars.join(" "), effect_vars.join(" "))
        };

        format!("∀{}. {:?}", vars, self.body)
    }
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
    pub fn affine(ty: BrrrType) -> Self {
        Self {
            ty,
            mode: Mode::Many,
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
    fn test_type_scheme() {
        let mut rodeo = Rodeo::default();
        let alpha = rodeo.get_or_intern("α");
        let beta = rodeo.get_or_intern("β");

        let scheme = TypeScheme::poly(
            vec![alpha, beta],
            BrrrType::Func(Box::new(crate::types::FuncType::pure(
                vec![crate::types::ParamType::unnamed(BrrrType::Var(alpha))],
                BrrrType::Var(beta),
            ))),
        );

        assert!(!scheme.is_mono());
        assert_eq!(scheme.type_arity(), 2);
    }

    #[test]
    fn test_moded_type() {
        let linear = ModedType::linear(BrrrType::STRING);
        assert_eq!(linear.mode, Mode::One);

        let unrestricted = ModedType::unrestricted(BrrrType::STRING);
        assert_eq!(unrestricted.mode, Mode::Omega);
    }
}
