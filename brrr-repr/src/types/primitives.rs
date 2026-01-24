//! Primitive type definitions
//!
//! Mirrors F* BrrrTypes.fsti: prim_kind, numeric_type, wrapper_kind, modal_kind

use serde::{Deserialize, Serialize};

use crate::modes::RefKind;

/// Primitive type kinds - 7 variants
/// Maps to F*: type prim_kind = PUnit | PNever | PBool | PString | PChar | PDynamic | PUnknown
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum PrimKind {
    /// Unit type `()`
    Unit = 0,
    /// Never/bottom type `!`
    Never = 1,
    /// Boolean type
    Bool = 2,
    /// String type
    String = 3,
    /// Character type
    Char = 4,
    /// Dynamic type (unsafe top) `⊤unsafe`
    Dynamic = 5,
    /// Unknown type (gradual typing) `⊤safe`
    Unknown = 6,
}

impl PrimKind {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "unit" | "Unit" | "()" => Some(Self::Unit),
            "never" | "Never" | "!" => Some(Self::Never),
            "bool" | "Bool" => Some(Self::Bool),
            "string" | "String" => Some(Self::String),
            "char" | "Char" => Some(Self::Char),
            "dynamic" | "Dynamic" | "⊤unsafe" => Some(Self::Dynamic),
            "unknown" | "Unknown" | "⊤safe" => Some(Self::Unknown),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unit => "Unit",
            Self::Never => "Never",
            Self::Bool => "Bool",
            Self::String => "String",
            Self::Char => "Char",
            Self::Dynamic => "Dynamic",
            Self::Unknown => "Unknown",
        }
    }

    /// Format with UTF-8 symbols
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Unit => "()",
            Self::Never => "!",
            Self::Bool => "Bool",
            Self::String => "String",
            Self::Char => "Char",
            Self::Dynamic => "⊤unsafe",
            Self::Unknown => "⊤safe",
        }
    }
}

/// Integer types with width and signedness
/// Maps to F*: type int_type = { width: int_width; sign: signedness }
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum IntType {
    I8 = 0,
    I16 = 1,
    I32 = 2,
    I64 = 3,
    I128 = 4,
    ISize = 5,
    IBig = 6,
    U8 = 7,
    U16 = 8,
    U32 = 9,
    U64 = 10,
    U128 = 11,
    USize = 12,
}

impl IntType {
    /// Is this a signed integer type?
    pub const fn is_signed(self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::ISize | Self::IBig
        )
    }

    /// Bit width (None for IBig)
    pub const fn bit_width(self) -> Option<u8> {
        match self {
            Self::I8 | Self::U8 => Some(8),
            Self::I16 | Self::U16 => Some(16),
            Self::I32 | Self::U32 => Some(32),
            Self::I64 | Self::U64 => Some(64),
            Self::I128 | Self::U128 => Some(128),
            Self::ISize | Self::USize => None, // Platform-dependent
            Self::IBig => None,                // Arbitrary precision
        }
    }

    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "i8" => Some(Self::I8),
            "i16" => Some(Self::I16),
            "i32" => Some(Self::I32),
            "i64" => Some(Self::I64),
            "i128" => Some(Self::I128),
            "isize" => Some(Self::ISize),
            "ibig" => Some(Self::IBig),
            "u8" => Some(Self::U8),
            "u16" => Some(Self::U16),
            "u32" => Some(Self::U32),
            "u64" => Some(Self::U64),
            "u128" => Some(Self::U128),
            "usize" => Some(Self::USize),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::ISize => "isize",
            Self::IBig => "ibig",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::U128 => "u128",
            Self::USize => "usize",
        }
    }
}

/// Float precision
/// Maps to F*: type float_prec = F32 | F64
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum FloatPrec {
    F16 = 0,
    F32 = 1,
    F64 = 2,
}

impl FloatPrec {
    /// Bit width
    pub const fn bit_width(self) -> u8 {
        match self {
            Self::F16 => 16,
            Self::F32 => 32,
            Self::F64 => 64,
        }
    }

    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "f16" => Some(Self::F16),
            "f32" => Some(Self::F32),
            "f64" => Some(Self::F64),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::F16 => "f16",
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }
}

/// Numeric types combining int and float
/// Maps to F*: type numeric_type = NumInt int_type | NumFloat float_prec
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NumericType {
    Int(IntType),
    Float(FloatPrec),
}

impl NumericType {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        IntType::from_str(s)
            .map(Self::Int)
            .or_else(|| FloatPrec::from_str(s).map(Self::Float))
    }

    /// Format to text
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Int(i) => i.as_str(),
            Self::Float(f) => f.as_str(),
        }
    }

    /// Get discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Int(i) => *i as u8,
            Self::Float(f) => 16 + *f as u8, // Offset floats past ints
        }
    }
}

/// Wrapper type kinds - 9 single-type wrappers
/// Maps to F*: type wrapper_kind = WArray | WSlice | WOption | WBox | WRef | WRefMut | WRc | WArc | WRaw
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum WrapperKind {
    /// `[T]` or `Array[T]`
    Array = 0,
    /// `&[T]` or `Slice[T]`
    Slice = 1,
    /// `T?` or `Option[T]`
    Option = 2,
    /// `Box[T]`
    Box = 3,
    /// `&T` or `Ref[T]`
    Ref = 4,
    /// `&mut T` or `RefMut[T]`
    RefMut = 5,
    /// `Rc[T]`
    Rc = 6,
    /// `Arc[T]`
    Arc = 7,
    /// `*T` or `Raw[T]`
    Raw = 8,
}

impl WrapperKind {
    /// RefMut is invariant, all others are covariant
    pub const fn is_covariant(self) -> bool {
        !matches!(self, Self::RefMut)
    }

    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "Array" | "array" => Some(Self::Array),
            "Slice" | "slice" => Some(Self::Slice),
            "Option" | "option" => Some(Self::Option),
            "Box" | "box" => Some(Self::Box),
            "Ref" | "ref" => Some(Self::Ref),
            "RefMut" | "refmut" => Some(Self::RefMut),
            "Rc" | "rc" => Some(Self::Rc),
            "Arc" | "arc" => Some(Self::Arc),
            "Raw" | "raw" => Some(Self::Raw),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Array => "Array",
            Self::Slice => "Slice",
            Self::Option => "Option",
            Self::Box => "Box",
            Self::Ref => "Ref",
            Self::RefMut => "RefMut",
            Self::Rc => "Rc",
            Self::Arc => "Arc",
            Self::Raw => "Raw",
        }
    }

    /// Format with UTF-8 sugar syntax
    pub const fn sugar_prefix(self) -> Option<&'static str> {
        match self {
            Self::Array => Some("["),
            Self::Slice => Some("&["),
            Self::Ref => Some("&"),
            Self::RefMut => Some("&mut "),
            Self::Raw => Some("*"),
            _ => None,
        }
    }

    /// Format with UTF-8 sugar suffix
    pub const fn sugar_suffix(self) -> Option<&'static str> {
        match self {
            Self::Array | Self::Slice => Some("]"),
            Self::Option => Some("?"),
            _ => None,
        }
    }
}

/// Modal reference kinds for fractional permissions
/// Maps to F*: type modal_kind = MBoxMod ref_kind | MDiamondMod
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ModalKind {
    /// Box modality `□ T @ p` - shared with fractional permission
    BoxMod(RefKind),
    /// Diamond modality `◇ T` - exclusive/linear
    DiamondMod,
}

impl ModalKind {
    /// Format to text
    pub fn as_symbol(&self) -> String {
        match self {
            Self::BoxMod(rk) => format!("□@{}", rk.permission),
            Self::DiamondMod => "◇".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prim_roundtrip() {
        for kind in [
            PrimKind::Unit,
            PrimKind::Never,
            PrimKind::Bool,
            PrimKind::String,
            PrimKind::Char,
            PrimKind::Dynamic,
            PrimKind::Unknown,
        ] {
            let s = kind.as_str();
            assert_eq!(PrimKind::from_str(s), Some(kind));
        }
    }

    #[test]
    fn test_int_type_roundtrip() {
        for ty in [
            IntType::I8,
            IntType::I16,
            IntType::I32,
            IntType::I64,
            IntType::U8,
            IntType::U16,
            IntType::U32,
            IntType::U64,
        ] {
            let s = ty.as_str();
            assert_eq!(IntType::from_str(s), Some(ty));
        }
    }

    #[test]
    fn test_wrapper_covariance() {
        assert!(WrapperKind::Array.is_covariant());
        assert!(WrapperKind::Option.is_covariant());
        assert!(WrapperKind::Ref.is_covariant());
        assert!(!WrapperKind::RefMut.is_covariant());
    }
}
