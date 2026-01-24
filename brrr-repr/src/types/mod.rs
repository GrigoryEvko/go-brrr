//! Core type definitions mirroring F* BrrrTypes.fsti
//!
//! 12 type constructors for SMT tractability (matching brrr-lang specification).

mod primitives;
mod brrr_type;
mod func_type;
mod struct_enum;
mod scheme;
mod region;

pub use primitives::{FloatPrec, IntType, ModalKind, NumericType, PrimKind, WrapperKind};
pub use brrr_type::{BrrrType, TypeId, TypeName, TypeVar};
pub use func_type::{FuncType, ParamType};
pub use struct_enum::{EnumType, FieldType, StructType, VariantType};
pub use scheme::{ModedType, RegionedType, TypeScheme};
pub use region::{Region, ReprAttr, Visibility};
