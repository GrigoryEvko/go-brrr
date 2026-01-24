//! Struct and enum type definitions
//!
//! Mirrors F* BrrrTypes.fsti struct_type, enum_type, field_type, variant_type.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::region::{ReprAttr, Visibility};
use super::BrrrType;

/// Struct type definition
/// Maps to F*:
/// ```fstar
/// type struct_type = {
///   struct_name: type_name;
///   struct_fields: list field_type;
///   struct_repr: repr_attr;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StructType {
    /// Struct name
    pub name: Spur,
    /// Fields
    pub fields: Vec<FieldType>,
    /// Representation attribute (`#[repr(C)]`, etc.)
    pub repr: ReprAttr,
}

impl StructType {
    /// Create a new struct type
    pub fn new(name: Spur, fields: Vec<FieldType>) -> Self {
        Self {
            name,
            fields,
            repr: ReprAttr::Rust,
        }
    }

    /// Create with specific repr
    pub fn with_repr(name: Spur, fields: Vec<FieldType>, repr: ReprAttr) -> Self {
        Self { name, fields, repr }
    }

    /// Get field by name
    pub fn get_field(&self, name: Spur) -> Option<&FieldType> {
        self.fields.iter().find(|f| f.name == name)
    }

    /// Get field index by name
    pub fn field_index(&self, name: Spur) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
    }

    /// Number of fields
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// Is this a unit struct (no fields)?
    pub fn is_unit(&self) -> bool {
        self.fields.is_empty()
    }
}

/// Field within a struct
/// Maps to F*:
/// ```fstar
/// type field_type = {
///   field_name: string;
///   field_ty: brrr_type;
///   field_vis: visibility;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FieldType {
    /// Field name
    pub name: Spur,
    /// Field type
    pub ty: BrrrType,
    /// Visibility
    pub vis: Visibility,
}

impl FieldType {
    /// Create a public field
    pub fn public(name: Spur, ty: BrrrType) -> Self {
        Self {
            name,
            ty,
            vis: Visibility::Public,
        }
    }

    /// Create a private field
    pub fn private(name: Spur, ty: BrrrType) -> Self {
        Self {
            name,
            ty,
            vis: Visibility::Private,
        }
    }

    /// Create a module-visible field
    pub fn module(name: Spur, ty: BrrrType) -> Self {
        Self {
            name,
            ty,
            vis: Visibility::Module,
        }
    }
}

/// Enum type definition
/// Maps to F*:
/// ```fstar
/// type enum_type = {
///   enum_name: type_name;
///   enum_variants: list variant_type;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnumType {
    /// Enum name
    pub name: Spur,
    /// Variants
    pub variants: Vec<VariantType>,
}

impl EnumType {
    /// Create a new enum type
    pub fn new(name: Spur, variants: Vec<VariantType>) -> Self {
        Self { name, variants }
    }

    /// Get variant by name
    pub fn get_variant(&self, name: Spur) -> Option<&VariantType> {
        self.variants.iter().find(|v| v.name == name)
    }

    /// Get variant index by name
    pub fn variant_index(&self, name: Spur) -> Option<usize> {
        self.variants.iter().position(|v| v.name == name)
    }

    /// Number of variants
    pub fn variant_count(&self) -> usize {
        self.variants.len()
    }

    /// Is this a simple enum (all unit variants)?
    pub fn is_simple(&self) -> bool {
        self.variants.iter().all(|v| v.fields.is_empty())
    }
}

/// Variant within an enum
/// Maps to F*:
/// ```fstar
/// type variant_type = {
///   variant_name: string;
///   variant_fields: list brrr_type;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VariantType {
    /// Variant name
    pub name: Spur,
    /// Variant fields (unnamed, positional)
    pub fields: Vec<BrrrType>,
}

impl VariantType {
    /// Create a unit variant (no data)
    pub fn unit(name: Spur) -> Self {
        Self {
            name,
            fields: Vec::new(),
        }
    }

    /// Create a tuple variant
    pub fn tuple(name: Spur, fields: Vec<BrrrType>) -> Self {
        Self { name, fields }
    }

    /// Create a single-field variant (newtype)
    pub fn newtype(name: Spur, inner: BrrrType) -> Self {
        Self {
            name,
            fields: vec![inner],
        }
    }

    /// Is this a unit variant?
    pub fn is_unit(&self) -> bool {
        self.fields.is_empty()
    }

    /// Number of fields
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::{Rodeo, Spur};

    fn intern(rodeo: &mut Rodeo, s: &str) -> Spur {
        rodeo.get_or_intern(s)
    }

    #[test]
    fn test_struct_type() {
        let mut rodeo = Rodeo::default();
        let point = intern(&mut rodeo, "Point");
        let x = intern(&mut rodeo, "x");
        let y = intern(&mut rodeo, "y");

        let s = StructType::new(
            point,
            vec![
                FieldType::public(x, BrrrType::Numeric(crate::types::NumericType::Float(
                    crate::types::FloatPrec::F64,
                ))),
                FieldType::public(y, BrrrType::Numeric(crate::types::NumericType::Float(
                    crate::types::FloatPrec::F64,
                ))),
            ],
        );

        assert_eq!(s.field_count(), 2);
        assert!(!s.is_unit());
        assert!(s.get_field(x).is_some());
        assert_eq!(s.field_index(y), Some(1));
    }

    #[test]
    fn test_enum_type() {
        let mut rodeo = Rodeo::default();
        let option = intern(&mut rodeo, "Option");
        let none = intern(&mut rodeo, "None");
        let some = intern(&mut rodeo, "Some");

        let e = EnumType::new(
            option,
            vec![
                VariantType::unit(none),
                VariantType::newtype(some, BrrrType::Var(intern(&mut rodeo, "T"))),
            ],
        );

        assert_eq!(e.variant_count(), 2);
        assert!(!e.is_simple()); // Some has data
        assert!(e.get_variant(none).unwrap().is_unit());
    }
}
