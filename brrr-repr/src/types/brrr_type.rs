//! Main BrrrType enum with 12 constructors
//!
//! Mirrors F* BrrrTypes.fsti typ definition.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::{
    EnumType, FuncType, ModalKind, NumericType, PrimKind, StructType, WrapperKind,
};

/// Type variable identifier (interned string)
pub type TypeVar = Spur;

/// Named type reference (interned string)
pub type TypeName = Spur;

/// Type ID for references within a module
pub type TypeId = u32;

/// Main type definition - 12 constructors for SMT tractability
/// Maps to F*:
/// ```fstar
/// noeq type typ =
///   | TPrim : prim_kind -> typ
///   | TNumeric : numeric_type -> typ
///   | TWrap : wrapper_kind -> typ -> typ
///   | TModal : modal_kind -> typ -> typ
///   | TResult : typ -> typ -> typ
///   | TTuple : list typ -> typ
///   | TFunc : func_type -> typ
///   | TVar : type_var -> typ
///   | TApp : typ -> list typ -> typ
///   | TNamed : type_name -> typ
///   | TStruct : struct_type -> typ
///   | TEnum : enum_type -> typ
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum BrrrType {
    /// Primitive types: Unit, Never, Bool, String, Char, Dynamic, Unknown
    Prim(PrimKind),

    /// Numeric types: i8-i128, u8-u128, f16-f64
    Numeric(NumericType),

    /// Wrapper types: Array, Slice, Option, Box, Ref, RefMut, Rc, Arc, Raw
    /// Sugar: `[T]`, `&[T]`, `T?`, `&T`, `&mut T`, `*T`
    Wrap(WrapperKind, Box<BrrrType>),

    /// Modal refs: `□ T @ p` (box), `◇ T` (diamond)
    Modal(ModalKind, Box<BrrrType>),

    /// Result type: `T ! E` or `Result[T, E]`
    Result(Box<BrrrType>, Box<BrrrType>),

    /// Tuple: `(T₁, T₂, ..., Tₙ)`
    Tuple(Vec<BrrrType>),

    /// Function type with effects: `(params) →ε ret`
    Func(Box<FuncType>),

    /// Type variable: `α`, `β`, `'a`
    Var(TypeVar),

    /// Type application: `F<T₁, T₂>`
    App(Box<BrrrType>, Vec<BrrrType>),

    /// Named type reference: `MyStruct`, `module::Type`
    Named(TypeName),

    /// Struct type definition
    Struct(StructType),

    /// Enum type definition
    Enum(EnumType),
}

impl BrrrType {
    /// Unit type `()`
    pub const UNIT: Self = Self::Prim(PrimKind::Unit);

    /// Never type `!`
    pub const NEVER: Self = Self::Prim(PrimKind::Never);

    /// Bool type
    pub const BOOL: Self = Self::Prim(PrimKind::Bool);

    /// String type
    pub const STRING: Self = Self::Prim(PrimKind::String);

    /// Char type
    pub const CHAR: Self = Self::Prim(PrimKind::Char);

    /// Dynamic type `⊤unsafe`
    pub const DYNAMIC: Self = Self::Prim(PrimKind::Dynamic);

    /// Unknown type `⊤safe`
    pub const UNKNOWN: Self = Self::Prim(PrimKind::Unknown);

    /// Create an array type `[T]`
    pub fn array(elem: Self) -> Self {
        Self::Wrap(WrapperKind::Array, Box::new(elem))
    }

    /// Create a slice type `&[T]`
    pub fn slice(elem: Self) -> Self {
        Self::Wrap(WrapperKind::Slice, Box::new(elem))
    }

    /// Create an option type `T?`
    pub fn option(inner: Self) -> Self {
        Self::Wrap(WrapperKind::Option, Box::new(inner))
    }

    /// Create a box type `Box[T]`
    pub fn boxed(inner: Self) -> Self {
        Self::Wrap(WrapperKind::Box, Box::new(inner))
    }

    /// Create a shared ref type `&T`
    pub fn ref_shared(inner: Self) -> Self {
        Self::Wrap(WrapperKind::Ref, Box::new(inner))
    }

    /// Create a mutable ref type `&mut T`
    pub fn ref_mut(inner: Self) -> Self {
        Self::Wrap(WrapperKind::RefMut, Box::new(inner))
    }

    /// Create a result type `T ! E`
    pub fn result(ok: Self, err: Self) -> Self {
        Self::Result(Box::new(ok), Box::new(err))
    }

    /// Create a tuple type `(T₁, T₂, ...)`
    pub fn tuple(elems: Vec<Self>) -> Self {
        Self::Tuple(elems)
    }

    /// Is this a primitive type?
    pub const fn is_primitive(&self) -> bool {
        matches!(self, Self::Prim(_) | Self::Numeric(_))
    }

    /// Is this a reference type?
    pub const fn is_reference(&self) -> bool {
        matches!(
            self,
            Self::Wrap(WrapperKind::Ref | WrapperKind::RefMut | WrapperKind::Raw, _)
        )
    }

    /// Is this a function type?
    pub const fn is_function(&self) -> bool {
        matches!(self, Self::Func(_))
    }

    /// Is this a unit type?
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Prim(PrimKind::Unit))
    }

    /// Is this a never type?
    pub const fn is_never(&self) -> bool {
        matches!(self, Self::Prim(PrimKind::Never))
    }

    /// Get the discriminant tag for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Prim(_) => 0,
            Self::Numeric(_) => 1,
            Self::Wrap(_, _) => 2,
            Self::Modal(_, _) => 3,
            Self::Result(_, _) => 4,
            Self::Tuple(_) => 5,
            Self::Func(_) => 6,
            Self::Var(_) => 7,
            Self::App(_, _) => 8,
            Self::Named(_) => 9,
            Self::Struct(_) => 10,
            Self::Enum(_) => 11,
        }
    }

    /// Get child types for traversal
    pub fn children(&self) -> Vec<&BrrrType> {
        match self {
            Self::Prim(_) | Self::Numeric(_) | Self::Var(_) | Self::Named(_) => vec![],
            Self::Wrap(_, inner) | Self::Modal(_, inner) => vec![inner.as_ref()],
            Self::Result(ok, err) => vec![ok.as_ref(), err.as_ref()],
            Self::Tuple(elems) => elems.iter().collect(),
            Self::Func(f) => {
                let mut children: Vec<&BrrrType> =
                    f.params.iter().map(|p| &p.ty).collect();
                children.push(&f.return_type);
                children
            }
            Self::App(base, args) => {
                let mut children = vec![base.as_ref()];
                children.extend(args.iter());
                children
            }
            Self::Struct(s) => s.fields.iter().map(|f| &f.ty).collect(),
            Self::Enum(e) => e
                .variants
                .iter()
                .flat_map(|v| v.fields.iter())
                .collect(),
        }
    }
}

impl Default for BrrrType {
    fn default() -> Self {
        Self::UNIT
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{FloatPrec, IntType};

    #[test]
    fn test_type_constructors() {
        let int32 = BrrrType::Numeric(NumericType::Int(IntType::I32));
        assert!(int32.is_primitive());

        let array_int = BrrrType::array(int32.clone());
        assert!(!array_int.is_primitive());
        assert_eq!(array_int.children().len(), 1);

        let result = BrrrType::result(int32.clone(), BrrrType::STRING);
        assert_eq!(result.children().len(), 2);
    }

    #[test]
    fn test_discriminants() {
        assert_eq!(BrrrType::UNIT.discriminant(), 0);
        assert_eq!(
            BrrrType::Numeric(NumericType::Float(FloatPrec::F64)).discriminant(),
            1
        );
        assert_eq!(BrrrType::array(BrrrType::BOOL).discriminant(), 2);
    }
}
