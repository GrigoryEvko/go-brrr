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

/// Interface/trait type definition (for Go interfaces, TypeScript interfaces, etc.)
///
/// Represents a structural interface type with method signatures and embedded interfaces.
/// Maps to Go:
/// ```go
/// type Reader interface {
///     Read(p []byte) (n int, err error)
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InterfaceType {
    /// Interface name (may be synthetic for anonymous interfaces)
    pub name: Spur,
    /// Method signatures defined in this interface
    pub methods: Vec<MethodSig>,
    /// Embedded interfaces (interface composition)
    pub embedded: Vec<Spur>,
}

impl InterfaceType {
    /// Create a new interface type
    pub fn new(name: Spur) -> Self {
        Self {
            name,
            methods: Vec::new(),
            embedded: Vec::new(),
        }
    }

    /// Create an interface with methods
    pub fn with_methods(name: Spur, methods: Vec<MethodSig>) -> Self {
        Self {
            name,
            methods,
            embedded: Vec::new(),
        }
    }

    /// Create an interface with embedded interfaces
    pub fn with_embedded(name: Spur, embedded: Vec<Spur>) -> Self {
        Self {
            name,
            methods: Vec::new(),
            embedded,
        }
    }

    /// Add a method to the interface
    pub fn add_method(&mut self, method: MethodSig) {
        self.methods.push(method);
    }

    /// Add an embedded interface
    pub fn add_embedded(&mut self, embedded: Spur) {
        self.embedded.push(embedded);
    }

    /// Check if this is an empty interface (Go's `interface{}` / `any`)
    pub fn is_empty(&self) -> bool {
        self.methods.is_empty() && self.embedded.is_empty()
    }

    /// Get method by name
    pub fn get_method(&self, name: Spur) -> Option<&MethodSig> {
        self.methods.iter().find(|m| m.name == name)
    }

    /// Number of methods (not counting embedded interfaces)
    pub fn method_count(&self) -> usize {
        self.methods.len()
    }

    /// Number of embedded interfaces
    pub fn embedded_count(&self) -> usize {
        self.embedded.len()
    }
}

/// Method signature within an interface
///
/// Represents a method's type signature without implementation.
/// Maps to Go method spec: `Read(p []byte) (n int, err error)`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MethodSig {
    /// Method name
    pub name: Spur,
    /// Parameter types (without receiver - interface methods have implicit receiver)
    pub params: Vec<MethodParam>,
    /// Return type (may be tuple for multiple returns)
    pub return_type: BrrrType,
}

impl MethodSig {
    /// Create a new method signature
    pub fn new(name: Spur, params: Vec<MethodParam>, return_type: BrrrType) -> Self {
        Self {
            name,
            params,
            return_type,
        }
    }

    /// Create a method with no parameters returning unit
    pub fn unit(name: Spur) -> Self {
        Self {
            name,
            params: Vec::new(),
            return_type: BrrrType::UNIT,
        }
    }

    /// Create a method with parameters returning unit
    pub fn void(name: Spur, params: Vec<MethodParam>) -> Self {
        Self {
            name,
            params,
            return_type: BrrrType::UNIT,
        }
    }

    /// Get arity (number of parameters)
    pub fn arity(&self) -> usize {
        self.params.len()
    }
}

/// Parameter within a method signature
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MethodParam {
    /// Optional parameter name
    pub name: Option<Spur>,
    /// Parameter type
    pub ty: BrrrType,
}

impl MethodParam {
    /// Create a named parameter
    pub fn named(name: Spur, ty: BrrrType) -> Self {
        Self {
            name: Some(name),
            ty,
        }
    }

    /// Create an unnamed parameter
    pub fn unnamed(ty: BrrrType) -> Self {
        Self { name: None, ty }
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

    #[test]
    fn test_interface_type_empty() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "EmptyInterface");

        let iface = InterfaceType::new(name);

        assert!(iface.is_empty());
        assert_eq!(iface.method_count(), 0);
        assert_eq!(iface.embedded_count(), 0);
    }

    #[test]
    fn test_interface_type_with_methods() {
        let mut rodeo = Rodeo::default();
        let reader = intern(&mut rodeo, "Reader");
        let read = intern(&mut rodeo, "Read");
        let p_name = intern(&mut rodeo, "p");

        // Read(p []byte) (n int, err error)
        let params = vec![MethodParam::named(
            p_name,
            BrrrType::Wrap(
                crate::types::WrapperKind::Slice,
                Box::new(BrrrType::Numeric(crate::types::NumericType::Int(
                    crate::types::IntType::U8,
                ))),
            ),
        )];
        let return_type = BrrrType::Tuple(vec![
            BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I64)),
            BrrrType::Named(intern(&mut rodeo, "Error")),
        ]);

        let method = MethodSig::new(read, params, return_type);
        let iface = InterfaceType::with_methods(reader, vec![method]);

        assert!(!iface.is_empty());
        assert_eq!(iface.method_count(), 1);
        assert!(iface.get_method(read).is_some());
        assert_eq!(iface.get_method(read).unwrap().arity(), 1);
    }

    #[test]
    fn test_interface_type_with_embedded() {
        let mut rodeo = Rodeo::default();
        let read_writer = intern(&mut rodeo, "ReadWriter");
        let reader = intern(&mut rodeo, "Reader");
        let writer = intern(&mut rodeo, "Writer");
        let close = intern(&mut rodeo, "Close");

        // ReadWriter embeds Reader and Writer, adds Close() method
        let mut iface = InterfaceType::with_embedded(read_writer, vec![reader, writer]);
        iface.add_method(MethodSig::unit(close));

        assert!(!iface.is_empty());
        assert_eq!(iface.method_count(), 1);
        assert_eq!(iface.embedded_count(), 2);
    }

    #[test]
    fn test_method_sig() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "DoSomething");
        let param = intern(&mut rodeo, "x");

        // Method with one int param returning bool
        let params = vec![MethodParam::named(
            param,
            BrrrType::Numeric(crate::types::NumericType::Int(crate::types::IntType::I32)),
        )];
        let method = MethodSig::new(name, params, BrrrType::BOOL);

        assert_eq!(method.arity(), 1);
        assert_eq!(method.return_type, BrrrType::BOOL);
    }

    #[test]
    fn test_method_param() {
        let mut rodeo = Rodeo::default();
        let name = intern(&mut rodeo, "value");

        let named = MethodParam::named(name, BrrrType::STRING);
        assert!(named.name.is_some());
        assert_eq!(named.ty, BrrrType::STRING);

        let unnamed = MethodParam::unnamed(BrrrType::BOOL);
        assert!(unnamed.name.is_none());
        assert_eq!(unnamed.ty, BrrrType::BOOL);
    }
}
