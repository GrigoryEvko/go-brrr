//! Function type definitions
//!
//! Mirrors F* BrrrTypes.fsti func_type and param_type.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::BrrrType;
use crate::effects::EffectRow;
use crate::modes::Mode;

/// Function type with effects
/// Maps to F*:
/// ```fstar
/// type func_type = {
///   params: list param_type;
///   return_type: brrr_type;
///   effects: effect_row;
///   is_unsafe: bool;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FuncType {
    /// Function parameters
    pub params: Vec<ParamType>,
    /// Return type
    pub return_type: BrrrType,
    /// Effect row: `⟨E₁, E₂ | ρ⟩` or `⊥` for pure
    pub effects: EffectRow,
    /// Is this an unsafe function?
    pub is_unsafe: bool,
}

impl FuncType {
    /// Create a pure function type (no effects)
    pub fn pure(params: Vec<ParamType>, return_type: BrrrType) -> Self {
        Self {
            params,
            return_type,
            effects: EffectRow::PURE,
            is_unsafe: false,
        }
    }

    /// Create a function type with effects
    pub fn with_effects(
        params: Vec<ParamType>,
        return_type: BrrrType,
        effects: EffectRow,
    ) -> Self {
        Self {
            params,
            return_type,
            effects,
            is_unsafe: false,
        }
    }

    /// Create an unsafe function type
    pub fn unsafe_fn(params: Vec<ParamType>, return_type: BrrrType) -> Self {
        Self {
            params,
            return_type,
            effects: EffectRow::PURE,
            is_unsafe: true,
        }
    }

    /// Is this a pure function (no effects)?
    pub fn is_pure(&self) -> bool {
        self.effects.is_pure()
    }

    /// Get arity (number of parameters)
    pub fn arity(&self) -> usize {
        self.params.len()
    }

    /// Format as arrow type: `(T₁, T₂) →ε R`
    pub fn format_arrow(&self) -> String {
        let params: Vec<String> = self.params.iter().map(|p| p.format()).collect();
        let params_str = if params.is_empty() {
            "()".to_string()
        } else {
            format!("({})", params.join(", "))
        };

        let effect_str = if self.effects.is_pure() {
            "⊥".to_string()
        } else {
            self.effects.format()
        };

        let unsafe_prefix = if self.is_unsafe { "unsafe " } else { "" };

        format!("{unsafe_prefix}{params_str} →{effect_str} {}", self.return_type_str())
    }

    fn return_type_str(&self) -> String {
        // Placeholder - would need full type formatting
        format!("{:?}", self.return_type)
    }
}

impl Default for FuncType {
    fn default() -> Self {
        Self {
            params: Vec::new(),
            return_type: BrrrType::UNIT,
            effects: EffectRow::PURE,
            is_unsafe: false,
        }
    }
}

/// Parameter with optional name and mode annotation
/// Maps to F*:
/// ```fstar
/// type param_type = {
///   name: option string;
///   ty: brrr_type;
///   mode: mode;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ParamType {
    /// Optional parameter name
    pub name: Option<Spur>,
    /// Parameter type
    pub ty: BrrrType,
    /// Usage mode (linear, affine, unrestricted)
    pub mode: Mode,
}

impl ParamType {
    /// Create an unnamed parameter with default mode
    pub fn unnamed(ty: BrrrType) -> Self {
        Self {
            name: None,
            ty,
            mode: Mode::Omega,
        }
    }

    /// Create a named parameter with default mode
    pub fn named(name: Spur, ty: BrrrType) -> Self {
        Self {
            name: Some(name),
            ty,
            mode: Mode::Omega,
        }
    }

    /// Create a linear parameter (must be used exactly once)
    pub fn linear(name: Option<Spur>, ty: BrrrType) -> Self {
        Self {
            name,
            ty,
            mode: Mode::One,
        }
    }

    /// Create an affine parameter (used at most once)
    /// Note: Affine semantics (can drop) is tracked via ExtendedMode.
    /// Base Mode is One since the resource starts with one available use.
    pub fn affine(name: Option<Spur>, ty: BrrrType) -> Self {
        Self {
            name,
            ty,
            mode: Mode::One, // Affine starts as One, can transition to Zero (dropped)
        }
    }

    /// Set the mode
    pub fn with_mode(mut self, mode: Mode) -> Self {
        self.mode = mode;
        self
    }

    /// Format as `name: Type @mode`
    pub fn format(&self) -> String {
        let name_str = self
            .name
            .map(|_| "param") // Would need interner for actual name
            .unwrap_or("_");

        let mode_str = match self.mode {
            Mode::Omega => String::new(),
            m => format!(" @{}", m.as_str()),
        };

        format!("{name_str}: {:?}{mode_str}", self.ty)
    }
}

impl Default for ParamType {
    fn default() -> Self {
        Self::unnamed(BrrrType::UNIT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_func_type_pure() {
        let f = FuncType::pure(
            vec![ParamType::unnamed(BrrrType::Numeric(
                crate::types::NumericType::Int(crate::types::IntType::I32),
            ))],
            BrrrType::BOOL,
        );
        assert!(f.is_pure());
        assert_eq!(f.arity(), 1);
        assert!(!f.is_unsafe);
    }

    #[test]
    fn test_param_modes() {
        let linear = ParamType::linear(None, BrrrType::STRING);
        assert_eq!(linear.mode, Mode::One);

        // Affine uses Mode::One as base mode (starts with one use available)
        // The "affine" property (can drop) is tracked via ExtendedMode
        let affine = ParamType::affine(None, BrrrType::STRING);
        assert_eq!(affine.mode, Mode::One);
    }
}
