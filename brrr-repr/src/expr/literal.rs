//! Literal value types
//!
//! Mirrors F* Expressions.fsti literal type.

use serde::{Deserialize, Serialize};

use crate::types::{FloatPrec, IntType};

/// Literal values
/// Maps to F*:
/// ```fstar
/// type literal =
///   | LitUnit
///   | LitBool : bool -> literal
///   | LitInt : int -> int_type -> literal
///   | LitFloat : float_repr -> float_prec -> literal
///   | LitString : string -> literal
///   | LitChar : char -> literal
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Literal {
    /// Unit literal `()`
    Unit,
    /// Boolean literal `true` or `false`
    Bool(bool),
    /// Integer literal with type annotation `42_i32`
    Int(i128, IntType),
    /// Float literal with precision `3.14_f64`
    Float(FloatBits, FloatPrec),
    /// String literal `"hello"`
    String(String),
    /// Character literal `'a'`
    Char(char),
}

/// Float represented as bits for exact equality
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FloatBits(pub u64);

impl FloatBits {
    /// Create from f32
    pub fn from_f32(v: f32) -> Self {
        Self(v.to_bits() as u64)
    }

    /// Create from f64
    pub fn from_f64(v: f64) -> Self {
        Self(v.to_bits())
    }

    /// Convert to f32
    pub fn to_f32(self) -> f32 {
        f32::from_bits(self.0 as u32)
    }

    /// Convert to f64
    pub fn to_f64(self) -> f64 {
        f64::from_bits(self.0)
    }
}

impl Literal {
    /// Create a unit literal
    pub const UNIT: Self = Self::Unit;

    /// Create a boolean literal
    pub const fn bool(v: bool) -> Self {
        Self::Bool(v)
    }

    /// Create an i32 literal
    pub const fn i32(v: i32) -> Self {
        Self::Int(v as i128, IntType::I32)
    }

    /// Create an i64 literal
    pub const fn i64(v: i64) -> Self {
        Self::Int(v as i128, IntType::I64)
    }

    /// Create a u32 literal
    pub const fn u32(v: u32) -> Self {
        Self::Int(v as i128, IntType::U32)
    }

    /// Create a u64 literal
    pub const fn u64(v: u64) -> Self {
        Self::Int(v as i128, IntType::U64)
    }

    /// Create an f32 literal
    pub fn f32(v: f32) -> Self {
        Self::Float(FloatBits::from_f32(v), FloatPrec::F32)
    }

    /// Create an f64 literal
    pub fn f64(v: f64) -> Self {
        Self::Float(FloatBits::from_f64(v), FloatPrec::F64)
    }

    /// Create a string literal
    pub fn string(s: impl Into<String>) -> Self {
        Self::String(s.into())
    }

    /// Create a char literal
    pub const fn char(c: char) -> Self {
        Self::Char(c)
    }

    /// Get the discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Unit => 0,
            Self::Bool(_) => 1,
            Self::Int(_, _) => 2,
            Self::Float(_, _) => 3,
            Self::String(_) => 4,
            Self::Char(_) => 5,
        }
    }

    /// Is this a unit literal?
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }

    /// Is this a boolean literal?
    pub const fn is_bool(&self) -> bool {
        matches!(self, Self::Bool(_))
    }

    /// Is this a numeric literal?
    pub const fn is_numeric(&self) -> bool {
        matches!(self, Self::Int(_, _) | Self::Float(_, _))
    }

    /// Format as text
    pub fn format(&self) -> String {
        match self {
            Self::Unit => "()".to_string(),
            Self::Bool(b) => b.to_string(),
            Self::Int(v, ty) => format!("{v}_{}", ty.as_str()),
            Self::Float(bits, prec) => {
                let v = match prec {
                    FloatPrec::F16 | FloatPrec::F32 => bits.to_f32() as f64,
                    FloatPrec::F64 => bits.to_f64(),
                };
                format!("{v}_{}", prec.as_str())
            }
            Self::String(s) => format!("{s:?}"),
            Self::Char(c) => format!("{c:?}"),
        }
    }
}

impl Default for Literal {
    fn default() -> Self {
        Self::Unit
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_constructors() {
        assert!(Literal::UNIT.is_unit());
        assert!(Literal::bool(true).is_bool());
        assert!(Literal::i32(42).is_numeric());
        assert!(Literal::f64(3.14).is_numeric());
    }

    #[test]
    fn test_float_bits_roundtrip() {
        let f = 3.14159_f64;
        let bits = FloatBits::from_f64(f);
        assert_eq!(bits.to_f64(), f);

        let f32_val = 2.718_f32;
        let bits32 = FloatBits::from_f32(f32_val);
        assert_eq!(bits32.to_f32(), f32_val);
    }

    #[test]
    fn test_literal_format() {
        assert_eq!(Literal::UNIT.format(), "()");
        assert_eq!(Literal::bool(true).format(), "true");
        assert_eq!(Literal::i32(42).format(), "42_i32");
        assert_eq!(Literal::string("hello").format(), "\"hello\"");
        assert_eq!(Literal::char('a').format(), "'a'");
    }
}
