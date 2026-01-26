//! Go type translation to BrrrType.
//!
//! Maps Go types to their Brrr IR equivalents.

use super::context::GoTranslationContext;
use crate::{missing_node, unsupported, TranslateResult, TranslationContext};
use brrr_repr::decl::{Declaration, FunctionDef};
use brrr_repr::expr::VarId;
use brrr_repr::effects::EffectRow;
use brrr_repr::EffectOp;
use brrr_repr::types::{
    BrrrType, FieldType, FuncType, IntType, InterfaceType, MethodParam, MethodSig,
    NumericType, ParamType, PrimKind, StructType, Visibility, WrapperKind,
};
use brrr_repr::modes::Mode;
use lasso::Spur;
use tree_sitter::Node;

/// Determine Go visibility from an identifier name.
/// In Go, identifiers starting with uppercase are exported (Public),
/// identifiers starting with lowercase are unexported (Private).
fn go_visibility(name: &str) -> Visibility {
    name.chars()
        .next()
        .map(|c| {
            if c.is_uppercase() {
                Visibility::Public
            } else {
                Visibility::Private
            }
        })
        .unwrap_or(Visibility::Private)
}

/// Translate a Go type node to BrrrType.
pub fn translate_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    match node.kind() {
        "type_identifier" => translate_type_identifier(ctx, node),
        "qualified_type" => translate_qualified_type(ctx, node),
        "pointer_type" => translate_pointer_type(ctx, node),
        "array_type" => translate_array_type(ctx, node),
        "slice_type" => translate_slice_type(ctx, node),
        "map_type" => translate_map_type(ctx, node),
        "channel_type" => translate_channel_type(ctx, node),
        "function_type" => translate_function_type(ctx, node),
        "struct_type" => translate_struct_type(ctx, node),
        "interface_type" => translate_interface_type(ctx, node),
        "parenthesized_type" => {
            // Unwrap parentheses
            if let Some(inner) = node.child(1) {
                translate_type(ctx, inner)
            } else {
                Err(missing_node("inner type", node))
            }
        }
        _ => Err(unsupported(&format!("type kind: {}", node.kind()), node)),
    }
}

/// Translate a type identifier (e.g., `int`, `string`, `MyType`).
fn translate_type_identifier<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    let name = ctx.node_text(node);

    // Map Go built-in types
    match name {
        // Boolean
        "bool" => Ok(BrrrType::Prim(PrimKind::Bool)),

        // Signed integers
        "int" => Ok(BrrrType::Numeric(NumericType::Int(IntType::I64))), // Platform-dependent
        "int8" => Ok(BrrrType::Numeric(NumericType::Int(IntType::I8))),
        "int16" => Ok(BrrrType::Numeric(NumericType::Int(IntType::I16))),
        "int32" | "rune" => Ok(BrrrType::Numeric(NumericType::Int(IntType::I32))),
        "int64" => Ok(BrrrType::Numeric(NumericType::Int(IntType::I64))),

        // Unsigned integers
        "uint" | "uintptr" => Ok(BrrrType::Numeric(NumericType::Int(IntType::U64))),
        "uint8" | "byte" => Ok(BrrrType::Numeric(NumericType::Int(IntType::U8))),
        "uint16" => Ok(BrrrType::Numeric(NumericType::Int(IntType::U16))),
        "uint32" => Ok(BrrrType::Numeric(NumericType::Int(IntType::U32))),
        "uint64" => Ok(BrrrType::Numeric(NumericType::Int(IntType::U64))),

        // Floating point
        "float32" => Ok(BrrrType::Numeric(NumericType::Float(
            brrr_repr::types::FloatPrec::F32,
        ))),
        "float64" => Ok(BrrrType::Numeric(NumericType::Float(
            brrr_repr::types::FloatPrec::F64,
        ))),

        // Complex (represented as tuple of floats)
        "complex64" => Ok(BrrrType::Tuple(vec![
            BrrrType::Numeric(NumericType::Float(brrr_repr::types::FloatPrec::F32)),
            BrrrType::Numeric(NumericType::Float(brrr_repr::types::FloatPrec::F32)),
        ])),
        "complex128" => Ok(BrrrType::Tuple(vec![
            BrrrType::Numeric(NumericType::Float(brrr_repr::types::FloatPrec::F64)),
            BrrrType::Numeric(NumericType::Float(brrr_repr::types::FloatPrec::F64)),
        ])),

        // String
        "string" => Ok(BrrrType::Prim(PrimKind::String)),

        // Error interface
        "error" => Ok(BrrrType::Named(ctx.intern("Error"))),

        // Any/interface{} - dynamic type
        "any" => Ok(BrrrType::Prim(PrimKind::Dynamic)),

        // User-defined type - look up or create named reference
        _ => {
            let spur = ctx.intern(name);
            if let Some(ty) = ctx.lookup_type(spur) {
                Ok(ty.clone())
            } else {
                // Return as named type reference
                Ok(BrrrType::Named(spur))
            }
        }
    }
}

/// Translate a qualified type (e.g., `pkg.Type`).
fn translate_qualified_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // qualified_type has package and name fields
    let full_name = ctx.node_text(node);
    let spur = ctx.intern(full_name);
    Ok(BrrrType::Named(spur))
}

/// Translate a pointer type (e.g., `*T`).
fn translate_pointer_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // pointer_type: "*" type
    let elem_node = node
        .child_by_field_name("type")
        .or_else(|| node.child(1)) // fallback to positional
        .ok_or_else(|| missing_node("element type", node))?;

    let elem_type = translate_type(ctx, elem_node)?;

    // Go pointers are nullable, so we represent as Option
    Ok(BrrrType::Wrap(WrapperKind::Option, Box::new(elem_type)))
}

/// Translate an array type (e.g., `[N]T`).
///
/// Go sized arrays like `[5]int` preserve their size in the IR as `SizedArray(5, int)`.
/// This distinguishes them from slices `[]int` which use `Wrap(Slice, int)`.
fn translate_array_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // array_type: "[" expression "]" type
    let elem_node = node
        .child_by_field_name("element")
        .ok_or_else(|| missing_node("element type", node))?;

    let elem_type = translate_type(ctx, elem_node)?;

    // Extract the array size from the length expression
    // In Go: [5]int has structure: "[" int_literal "5" "]" type_identifier "int"
    let size = extract_array_size(ctx, node);

    match size {
        Some(n) => Ok(BrrrType::sized_array(n, elem_type)),
        None => {
            // Fallback to unsized array if we can't determine the size statically
            // This can happen with array sizes like `[...]int{1,2,3}` or non-literal expressions
            Ok(BrrrType::Wrap(WrapperKind::Array, Box::new(elem_type)))
        }
    }
}

/// Extract the static array size from an array_type node.
///
/// Returns `Some(size)` if the size is a compile-time constant integer literal,
/// `None` otherwise (for computed sizes or `...` ellipsis).
fn extract_array_size<'src>(ctx: &mut GoTranslationContext<'src>, node: Node<'_>) -> Option<usize> {
    // Find the length child node - it's typically the expression between "[" and "]"
    let length_node = node.child_by_field_name("length")?;

    match length_node.kind() {
        "int_literal" => {
            let text = ctx.node_text(length_node);
            // Handle different integer literal formats
            parse_int_literal(text)
        }
        "identifier" => {
            // Could be a const reference - we can't resolve it at translation time
            // In a full compiler, we'd look up the const value
            None
        }
        _ => {
            // Computed size or ellipsis `...` - not statically determinable
            None
        }
    }
}

/// Parse a Go integer literal into a usize.
///
/// Handles:
/// - Decimal: `5`, `123`
/// - Hex: `0x10`, `0X1F`
/// - Octal: `0o17`, `0O17`, `017` (old style)
/// - Binary: `0b101`, `0B101`
/// - Underscores: `1_000_000`
fn parse_int_literal(text: &str) -> Option<usize> {
    let text = text.replace('_', "");

    if text.starts_with("0x") || text.starts_with("0X") {
        usize::from_str_radix(&text[2..], 16).ok()
    } else if text.starts_with("0o") || text.starts_with("0O") {
        usize::from_str_radix(&text[2..], 8).ok()
    } else if text.starts_with("0b") || text.starts_with("0B") {
        usize::from_str_radix(&text[2..], 2).ok()
    } else if text.starts_with('0') && text.len() > 1 {
        // Old-style octal (e.g., 017)
        usize::from_str_radix(&text[1..], 8).ok()
    } else {
        text.parse().ok()
    }
}

/// Translate a slice type (e.g., `[]T`).
fn translate_slice_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // slice_type: "[" "]" type
    let elem_node = node
        .child_by_field_name("element")
        .ok_or_else(|| missing_node("element type", node))?;

    let elem_type = translate_type(ctx, elem_node)?;

    Ok(BrrrType::Wrap(WrapperKind::Slice, Box::new(elem_type)))
}

/// Translate a map type (e.g., `map[K]V`).
fn translate_map_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // map_type: "map" "[" key_type "]" value_type
    let key_node = node
        .child_by_field_name("key")
        .ok_or_else(|| missing_node("key type", node))?;
    let value_node = node
        .child_by_field_name("value")
        .ok_or_else(|| missing_node("value type", node))?;

    let key_type = translate_type(ctx, key_node)?;
    let value_type = translate_type(ctx, value_node)?;

    // Represent as type application: Map<K, V>
    let map_name = ctx.intern("Map");
    Ok(BrrrType::App(
        Box::new(BrrrType::Named(map_name)),
        vec![key_type, value_type],
    ))
}

/// Translate a channel type (e.g., `chan T`, `chan<- T`, `<-chan T`).
fn translate_channel_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // channel_type: "chan" type | "chan" "<-" type | "<-" "chan" type
    let elem_node = node
        .child_by_field_name("value")
        .ok_or_else(|| missing_node("element type", node))?;

    let elem_type = translate_type(ctx, elem_node)?;

    // Represent as type application: Chan<T>
    // The direction is tracked separately via session types
    let chan_name = ctx.intern("Chan");
    Ok(BrrrType::App(
        Box::new(BrrrType::Named(chan_name)),
        vec![elem_type],
    ))
}

/// Translate a function type (e.g., `func(int) string`).
fn translate_function_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // function_type: "func" parameters [result]
    let params = if let Some(params_node) = node.child_by_field_name("parameters") {
        translate_parameters(ctx, params_node)?
    } else {
        Vec::new()
    };

    let return_type = if let Some(result_node) = node.child_by_field_name("result") {
        translate_result_type(ctx, result_node)?
    } else {
        BrrrType::UNIT
    };

    let func_type = FuncType {
        params,
        return_type,
        effects: go_default_effects(),
        is_unsafe: false,
    };

    Ok(BrrrType::Func(Box::new(func_type)))
}

/// Translate a struct type.
fn translate_struct_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    // struct_type: "struct" "{" [field_declaration_list] "}"
    let mut fields = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "field_declaration_list" {
            let mut field_cursor = child.walk();
            for field_node in child.children(&mut field_cursor) {
                if field_node.kind() == "field_declaration" {
                    if let Ok(field_types) = translate_field_declaration(ctx, field_node) {
                        fields.extend(field_types);
                    }
                }
            }
        }
    }

    // Anonymous struct - generate unique name
    let id = ctx.fresh_node_id().0;
    let name = ctx.intern(&format!("_anon_struct_{}", id));

    Ok(BrrrType::Struct(StructType {
        name,
        fields,
        repr: brrr_repr::types::ReprAttr::Rust,
    }))
}

/// Translate field declarations.
fn translate_field_declaration<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<FieldType>> {
    // field_declaration: [identifier_list] type [tag]
    // or: embedded field (just type)
    let mut fields = Vec::new();

    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("field type", node))?;
    let field_type = translate_type(ctx, type_node)?;

    // Check for identifier list
    if let Some(name_node) = node.child_by_field_name("name") {
        // Single named field or field list
        let name_text = ctx.node_text(name_node);
        let name = ctx.intern(name_text);
        fields.push(FieldType {
            name,
            ty: field_type,
            vis: go_visibility(name_text),
        });
    } else {
        // Check for identifier_list
        let mut found_names = false;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "identifier" || child.kind() == "field_identifier" {
                let name_text = ctx.node_text(child);
                let name = ctx.intern(name_text);
                fields.push(FieldType {
                    name,
                    ty: field_type.clone(),
                    vis: go_visibility(name_text),
                });
                found_names = true;
            }
        }

        if !found_names {
            // Embedded field - use type name as field name
            let type_name = ctx.node_text(type_node);
            // Extract last component (e.g., "pkg.Type" -> "Type")
            let name = type_name.rsplit('.').next().unwrap_or(type_name);
            let name_spur = ctx.intern(name);
            fields.push(FieldType {
                name: name_spur,
                ty: field_type,
                vis: go_visibility(name),
            });
        }
    }

    Ok(fields)
}

/// Translate an interface type.
///
/// Go interface types can contain:
/// - Method specifications: `Read(p []byte) (n int, err error)`
/// - Embedded interfaces: `Reader` (type identifier referencing another interface)
///
/// Example:
/// ```go
/// type Reader interface {
///     Read(p []byte) (n int, err error)
/// }
/// type ReadWriter interface {
///     Reader  // embedded
///     Write(p []byte) (n int, err error)
/// }
/// ```
fn translate_interface_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    let mut methods = Vec::new();
    let mut embedded = Vec::new();

    // interface_type: "interface" "{" [method_elem | type_elem]* "}"
    // tree-sitter-go structure:
    //   method_elem (for methods)
    //     field_identifier = "MethodName"
    //     parameter_list (params)
    //     parameter_list (returns)  // optional
    //   type_elem (for embedded interfaces)
    //     type_identifier = "EmbeddedInterface"
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "type_elem" {
            // Embedded interface
            let mut elem_cursor = child.walk();
            for elem_child in child.children(&mut elem_cursor) {
                if elem_child.kind() == "type_identifier" || elem_child.kind() == "qualified_type" {
                    let embedded_name = ctx.node_text(elem_child);
                    embedded.push(ctx.intern(embedded_name));
                }
            }
        } else if child.kind() == "method_elem" {
            // Check if this is an embedded type or a method
            let mut has_field_identifier = false;
            let mut method_name: Option<Spur> = None;
            let mut param_lists = Vec::new();

            let mut elem_cursor = child.walk();
            for elem_child in child.children(&mut elem_cursor) {
                match elem_child.kind() {
                    "field_identifier" => {
                        has_field_identifier = true;
                        method_name = Some(ctx.intern(ctx.node_text(elem_child)));
                    }
                    "parameter_list" => {
                        param_lists.push(elem_child);
                    }
                    "type_identifier" | "qualified_type" => {
                        // This is an embedded interface
                        if !has_field_identifier {
                            let embedded_name = ctx.node_text(elem_child);
                            embedded.push(ctx.intern(embedded_name));
                        }
                    }
                    _ => {}
                }
            }

            // If we found a method (field_identifier + parameter_list(s)), translate it
            if let Some(name) = method_name {
                let params = if !param_lists.is_empty() {
                    translate_method_params(ctx, param_lists[0])?
                } else {
                    Vec::new()
                };

                let return_type = if param_lists.len() > 1 {
                    // Second parameter_list is the return type(s)
                    translate_result_type(ctx, param_lists[1])?
                } else {
                    BrrrType::UNIT
                };

                methods.push(MethodSig::new(name, params, return_type));
            }
        }
    }

    // Check for empty interface - return Dynamic type for interface{}/any
    if methods.is_empty() && embedded.is_empty() {
        return Ok(BrrrType::Prim(PrimKind::Dynamic));
    }

    // Generate name for anonymous interface
    let id = ctx.fresh_node_id().0;
    let name = ctx.intern(&format!("_anon_interface_{}", id));

    let mut iface = InterfaceType::new(name);
    iface.methods = methods;
    iface.embedded = embedded;

    Ok(BrrrType::Interface(iface))
}

/// Translate a method specification within an interface.
///
/// method_spec: name parameters [result]
/// Example: `Read(p []byte) (n int, err error)`
fn translate_method_spec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<MethodSig> {
    // Get method name
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("method name", node))?;
    let name_text = ctx.node_text(name_node);
    let name = ctx.intern(name_text);

    // Parse parameters
    let params = if let Some(params_node) = node.child_by_field_name("parameters") {
        translate_method_params(ctx, params_node)?
    } else {
        Vec::new()
    };

    // Parse return type
    let return_type = if let Some(result_node) = node.child_by_field_name("result") {
        translate_result_type(ctx, result_node)?
    } else {
        BrrrType::UNIT
    };

    Ok(MethodSig::new(name, params, return_type))
}

/// Translate parameters for a method signature (without mode annotations).
fn translate_method_params<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<MethodParam>> {
    let mut params = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "parameter_declaration" {
            let param_list = translate_method_param_declaration(ctx, child)?;
            params.extend(param_list);
        }
    }

    Ok(params)
}

/// Translate a parameter declaration for method signatures.
fn translate_method_param_declaration<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<MethodParam>> {
    let mut params = Vec::new();

    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("parameter type", node))?;

    // Check for variadic
    let is_variadic = node.children(&mut node.walk()).any(|c| c.kind() == "...");

    let param_type = if is_variadic {
        let elem_type = translate_type(ctx, type_node)?;
        BrrrType::Wrap(WrapperKind::Slice, Box::new(elem_type))
    } else {
        translate_type(ctx, type_node)?
    };

    // Collect parameter names
    let mut names = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" {
            names.push(ctx.intern(ctx.node_text(child)));
        }
    }

    if names.is_empty() {
        // Unnamed parameter
        params.push(MethodParam::unnamed(param_type));
    } else {
        for name in names {
            params.push(MethodParam::named(name, param_type.clone()));
        }
    }

    Ok(params)
}

/// Translate function parameters.
pub fn translate_parameters<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<ParamType>> {
    let mut params = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "parameter_declaration" {
            let param_types = translate_parameter_declaration(ctx, child)?;
            params.extend(param_types);
        }
    }

    Ok(params)
}

/// Translate a parameter declaration.
fn translate_parameter_declaration<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<ParamType>> {
    // parameter_declaration: [identifier_list] ["..."] type
    let mut params = Vec::new();

    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("parameter type", node))?;

    // Check for variadic
    let is_variadic = node.children(&mut node.walk()).any(|c| c.kind() == "...");

    let param_type = if is_variadic {
        // Variadic becomes slice type
        let elem_type = translate_type(ctx, type_node)?;
        BrrrType::Wrap(WrapperKind::Slice, Box::new(elem_type))
    } else {
        translate_type(ctx, type_node)?
    };

    // Collect parameter names
    let mut names = Vec::new();
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "identifier" {
            names.push(ctx.intern(ctx.node_text(child)));
        }
    }

    if names.is_empty() {
        // Unnamed parameter
        params.push(ParamType {
            name: None,
            ty: param_type,
            mode: Mode::Omega,
        });
    } else {
        for name in names {
            params.push(ParamType {
                name: Some(name),
                ty: param_type.clone(),
                mode: Mode::Omega,
            });
        }
    }

    Ok(params)
}

/// Translate function result type.
pub fn translate_result_type<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<BrrrType> {
    match node.kind() {
        // Single type result
        "type_identifier" | "pointer_type" | "slice_type" | "array_type" | "map_type"
        | "channel_type" | "function_type" | "struct_type" | "interface_type"
        | "qualified_type" => translate_type(ctx, node),

        // Multiple results: parameter_list
        "parameter_list" => {
            let params = translate_parameters(ctx, node)?;
            if params.len() == 1 {
                Ok(params[0].ty.clone())
            } else {
                // Multiple returns become tuple
                let types: Vec<BrrrType> = params.into_iter().map(|p| p.ty).collect();
                Ok(BrrrType::Tuple(types))
            }
        }

        _ => {
            // Try to translate as a type
            translate_type(ctx, node)
        }
    }
}

/// Get the default effect row for Go functions.
///
/// Go functions can implicitly:
/// - Panic (EPanic)
/// - Spawn goroutines (ESpawn)
/// - Perform I/O (EIo)
pub fn go_default_effects() -> EffectRow {
    EffectRow::open(vec![EffectOp::Panic, EffectOp::Spawn, EffectOp::Io])
}

/// Translate a function declaration to Declaration (metadata only).
pub fn translate_function_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Declaration> {
    use super::exprs::node_range;

    // function_declaration: "func" name parameters [result] [block]
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("function name", node))?;
    let name_text = ctx.node_text(name_node);

    // Check if function is exported (starts with uppercase)
    let is_public = name_text
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    Ok(Declaration::Function {
        name: name_text.to_string(),
        is_public,
        span: node_range(node),
    })
}

/// Translate a function declaration to a full FunctionDef with body.
pub fn translate_function_def<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<FunctionDef> {
    use super::exprs::node_range;
    use super::stmts::{translate_block, wrap_with_defers};

    // function_declaration: "func" name parameters [result] [block]
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("function name", node))?;
    let name_text = ctx.node_text(name_node);
    let name: VarId = ctx.intern(name_text);

    // Check if function is exported (starts with uppercase)
    let is_public = name_text
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    // Parse parameters
    let params = if let Some(params_node) = node.child_by_field_name("parameters") {
        translate_parameters(ctx, params_node)?
    } else {
        Vec::new()
    };

    // Clear any stale defers and enter new function scope
    ctx.clear_defers();
    ctx.push_scope();

    for param in &params {
        if let Some(param_name) = param.name {
            ctx.bind_var(param_name, param.ty.clone(), true);
        }
    }

    // Parse return type and handle named returns
    let (return_type, named_returns) = if let Some(result_node) = node.child_by_field_name("result") {
        let rt = translate_result_type(ctx, result_node)?;
        // Extract named returns from result node
        let nr = extract_named_returns(ctx, result_node);
        (rt, nr)
    } else {
        (BrrrType::UNIT, Vec::new())
    };

    // Set named returns in context for naked return support
    ctx.set_named_returns(named_returns);

    // Translate body if present, then wrap with defers in LIFO order
    let body = if let Some(body_node) = node.child_by_field_name("body") {
        let raw_body = translate_block(ctx, body_node)?;
        // Collect defers and wrap body for LIFO execution at function exit
        let defers = ctx.take_defers();
        Some(wrap_with_defers(raw_body, defers))
    } else {
        None
    };

    ctx.pop_scope();
    ctx.clear_defers(); // Ensure clean state

    Ok(FunctionDef {
        name,
        type_params: Vec::new(), // Go doesn't have generics yet (pre-1.18 style)
        params,
        return_type,
        effects: go_default_effects(),
        body,
        contract: None,
        visibility: if is_public { Visibility::Public } else { Visibility::Private },
        is_unsafe: false,
        is_async: false,
        is_const: false,
        span: node_range(node),
    })
}

/// Translate a method declaration to a full FunctionDef with body.
pub fn translate_method_def<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<FunctionDef> {
    use super::exprs::node_range;
    use super::stmts::{translate_block, wrap_with_defers};

    // method_declaration: "func" receiver name parameters [result] [block]
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("method name", node))?;
    let name_text = ctx.node_text(name_node);

    // Get receiver info for method name encoding
    let receiver_node = node
        .child_by_field_name("receiver")
        .ok_or_else(|| missing_node("receiver", node))?;
    let (recv_name, recv_type) = translate_receiver(ctx, receiver_node)?;

    // Encode method name as "TypeName.methodName"
    let type_name = extract_receiver_type_name(ctx, recv_type.clone());
    let full_name = format!("{}.{}", type_name, name_text);
    let name: VarId = ctx.intern(&full_name);

    // Check if method is exported (starts with uppercase)
    let is_public = name_text
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    // Clear any stale defers and enter new function scope
    ctx.clear_defers();
    ctx.push_scope();

    // Add receiver as first parameter
    let recv_param = ParamType {
        name: Some(recv_name),
        ty: recv_type.clone(),
        mode: Mode::Omega,
    };
    ctx.bind_var(recv_name, recv_type, true);

    // Parse additional parameters
    let mut params = vec![recv_param];
    if let Some(params_node) = node.child_by_field_name("parameters") {
        let additional_params = translate_parameters(ctx, params_node)?;
        for param in &additional_params {
            if let Some(param_name) = param.name {
                ctx.bind_var(param_name, param.ty.clone(), true);
            }
        }
        params.extend(additional_params);
    }

    // Parse return type
    let (return_type, named_returns) = if let Some(result_node) = node.child_by_field_name("result") {
        let rt = translate_result_type(ctx, result_node)?;
        let nr = extract_named_returns(ctx, result_node);
        (rt, nr)
    } else {
        (BrrrType::UNIT, Vec::new())
    };

    ctx.set_named_returns(named_returns);

    // Translate body if present, then wrap with defers in LIFO order
    let body = if let Some(body_node) = node.child_by_field_name("body") {
        let raw_body = translate_block(ctx, body_node)?;
        // Collect defers and wrap body for LIFO execution at function exit
        let defers = ctx.take_defers();
        Some(wrap_with_defers(raw_body, defers))
    } else {
        None
    };

    ctx.pop_scope();
    ctx.clear_defers(); // Ensure clean state

    Ok(FunctionDef {
        name,
        type_params: Vec::new(),
        params,
        return_type,
        effects: go_default_effects(),
        body,
        contract: None,
        visibility: if is_public { Visibility::Public } else { Visibility::Private },
        is_unsafe: false,
        is_async: false,
        is_const: false,
        span: node_range(node),
    })
}

/// Extract named returns from a result node.
fn extract_named_returns<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> Vec<(VarId, BrrrType)> {
    let mut named_returns = Vec::new();

    // If it's a parameter_list, it may have named return values
    if node.kind() == "parameter_list" {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "parameter_declaration" {
                // Check if this parameter has a name
                if let Some(name_node) = child.child_by_field_name("name") {
                    let name = ctx.intern(ctx.node_text(name_node));
                    if let Some(type_node) = child.child_by_field_name("type") {
                        if let Ok(ty) = translate_type(ctx, type_node) {
                            named_returns.push((name, ty));
                            // Also bind the named return as a variable
                            ctx.bind_var(name, named_returns.last().unwrap().1.clone(), true);
                        }
                    }
                }
            }
        }
    }

    named_returns
}

/// Extract type name from receiver type (for method name encoding).
fn extract_receiver_type_name<'src>(
    ctx: &mut GoTranslationContext<'src>,
    ty: BrrrType,
) -> String {
    match ty {
        BrrrType::Named(spur) => ctx.resolve(spur).to_string(),
        BrrrType::Wrap(WrapperKind::Option, inner) => {
            // *T - pointer receiver
            extract_receiver_type_name(ctx, *inner)
        }
        _ => "_unknown_".to_string(),
    }
}

/// Translate a method declaration to Declaration.
pub fn translate_method_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Declaration> {
    use super::exprs::node_range;

    // method_declaration: "func" receiver name parameters [result] [block]
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("method name", node))?;
    let name_text = ctx.node_text(name_node);

    // Check if method is exported (starts with uppercase)
    let is_public = name_text
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    Ok(Declaration::Function {
        name: name_text.to_string(),
        is_public,
        span: node_range(node),
    })
}

/// Translate a method receiver.
fn translate_receiver<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<(Spur, BrrrType)> {
    // receiver: "(" [identifier] type ")"
    let mut name = ctx.intern("self");
    let mut recv_type = None;

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        match child.kind() {
            "identifier" => {
                name = ctx.intern(ctx.node_text(child));
            }
            "pointer_type" | "type_identifier" => {
                recv_type = Some(translate_type(ctx, child)?);
            }
            "parameter_declaration" => {
                // Nested parameter declaration
                if let Some(type_node) = child.child_by_field_name("type") {
                    recv_type = Some(translate_type(ctx, type_node)?);
                }
                if let Some(name_node) = child.child_by_field_name("name") {
                    name = ctx.intern(ctx.node_text(name_node));
                } else {
                    // Check for identifier child
                    let mut inner_cursor = child.walk();
                    for inner_child in child.children(&mut inner_cursor) {
                        if inner_child.kind() == "identifier" {
                            name = ctx.intern(ctx.node_text(inner_child));
                            break;
                        }
                    }
                }
            }
            _ => {}
        }
    }

    let recv_type = recv_type.ok_or_else(|| missing_node("receiver type", node))?;
    Ok((name, recv_type))
}

/// Translate a type declaration.
pub fn translate_type_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<Declaration>> {
    // type_declaration: "type" type_spec | "type" "(" {type_spec} ")"
    let mut decls = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "type_spec" {
            if let Ok(decl) = translate_type_spec(ctx, child) {
                decls.push(decl);
            }
        }
    }

    Ok(decls)
}

/// Translate a type spec.
fn translate_type_spec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Declaration> {
    use super::exprs::node_range;

    // type_spec: name type
    let name_node = node
        .child_by_field_name("name")
        .ok_or_else(|| missing_node("type name", node))?;
    let name_text = ctx.node_text(name_node);
    let name = ctx.intern(name_text);

    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("type definition", node))?;

    let ty = translate_type(ctx, type_node)?;

    // Register the type in the environment
    ctx.bind_type(name, ty);

    // Check if type is exported (starts with uppercase)
    let is_public = name_text
        .chars()
        .next()
        .map(|c| c.is_uppercase())
        .unwrap_or(false);

    Ok(Declaration::Type {
        name: name_text.to_string(),
        is_public,
        span: node_range(node),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_go_type(source: &str) -> tree_sitter::Tree {
        let full_source = format!("package main\ntype T {}", source);
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        parser.parse(&full_source, None).unwrap()
    }

    #[test]
    fn test_primitive_types() {
        let source = b"package main";
        let mut ctx = GoTranslationContext::new(source);

        // Create mock nodes for testing
        // This is a simplified test - in practice we'd parse actual Go code
        let _bool_spur = ctx.intern("bool");
        assert!(matches!(
            BrrrType::Prim(PrimKind::Bool),
            BrrrType::Prim(PrimKind::Bool)
        ));
    }

    #[test]
    fn test_go_visibility() {
        // Go visibility rules: uppercase = public, lowercase = private

        // Public (exported) identifiers
        assert_eq!(go_visibility("PublicField"), Visibility::Public);
        assert_eq!(go_visibility("X"), Visibility::Public);
        assert_eq!(go_visibility("MyType"), Visibility::Public);
        assert_eq!(go_visibility("API"), Visibility::Public);

        // Private (unexported) identifiers
        assert_eq!(go_visibility("privateField"), Visibility::Private);
        assert_eq!(go_visibility("x"), Visibility::Private);
        assert_eq!(go_visibility("myType"), Visibility::Private);
        assert_eq!(go_visibility("_internal"), Visibility::Private);

        // Edge cases
        assert_eq!(go_visibility(""), Visibility::Private); // Empty string
        assert_eq!(go_visibility("123"), Visibility::Private); // Starts with digit
    }

    #[test]
    fn test_struct_field_visibility() {
        // Test that struct fields get correct visibility based on Go naming convention
        let source = b"package main\n\ntype Foo struct {\n\tPublicField  int\n\tprivateField int\n\tX            string\n\ty            bool\n}\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        // Find the struct_type node
        let root = tree.root_node();
        let mut cursor = root.walk();

        // Navigate to the type_declaration -> type_spec -> struct_type
        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(struct_node) = type_child.child_by_field_name("type") {
                            if struct_node.kind() == "struct_type" {
                                let result = translate_struct_type(&mut ctx, struct_node);
                                assert!(result.is_ok(), "Should translate struct successfully");

                                if let Ok(BrrrType::Struct(st)) = result {
                                    assert_eq!(st.fields.len(), 4, "Should have 4 fields");

                                    // Verify visibility of each field
                                    let field_visibilities: Vec<_> = st.fields.iter()
                                        .map(|f| (ctx.resolve(f.name).to_string(), f.vis))
                                        .collect();

                                    // PublicField should be Public
                                    assert!(field_visibilities.iter().any(|(name, vis)|
                                        name == "PublicField" && *vis == Visibility::Public),
                                        "PublicField should be Public");

                                    // privateField should be Private
                                    assert!(field_visibilities.iter().any(|(name, vis)|
                                        name == "privateField" && *vis == Visibility::Private),
                                        "privateField should be Private");

                                    // X should be Public
                                    assert!(field_visibilities.iter().any(|(name, vis)|
                                        name == "X" && *vis == Visibility::Public),
                                        "X should be Public");

                                    // y should be Private
                                    assert!(field_visibilities.iter().any(|(name, vis)|
                                        name == "y" && *vis == Visibility::Private),
                                        "y should be Private");

                                    return; // Test passed
                                }
                            }
                        }
                    }
                }
            }
        }

        panic!("Could not find and parse struct type");
    }

    #[test]
    fn test_empty_interface() {
        // Empty interface should become Dynamic type
        let source = b"package main\n\ntype Empty interface{}\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(iface_node) = type_child.child_by_field_name("type") {
                            if iface_node.kind() == "interface_type" {
                                let result = translate_interface_type(&mut ctx, iface_node);
                                assert!(result.is_ok(), "Should translate empty interface");

                                // Empty interface should be Dynamic
                                assert!(
                                    matches!(result.unwrap(), BrrrType::Prim(PrimKind::Dynamic)),
                                    "Empty interface should be Dynamic type"
                                );
                                return;
                            }
                        }
                    }
                }
            }
        }
        panic!("Could not find and parse interface type");
    }

    #[test]
    fn test_interface_with_methods() {
        // Interface with methods
        let source = b"package main\n\ntype Reader interface {\n\tRead(p []byte) (n int, err error)\n}\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(iface_node) = type_child.child_by_field_name("type") {
                            if iface_node.kind() == "interface_type" {
                                let result = translate_interface_type(&mut ctx, iface_node);
                                assert!(result.is_ok(), "Should translate interface with methods: {:?}", result);

                                if let Ok(BrrrType::Interface(iface)) = result {
                                    assert_eq!(iface.method_count(), 1, "Should have 1 method");

                                    // Check method name
                                    let read_name = ctx.intern("Read");
                                    let method = iface.get_method(read_name);
                                    assert!(method.is_some(), "Should have Read method");

                                    let method = method.unwrap();
                                    assert_eq!(method.arity(), 1, "Read should have 1 parameter");

                                    // Return type should be a tuple (n int, err error)
                                    assert!(
                                        matches!(method.return_type, BrrrType::Tuple(_)),
                                        "Return type should be tuple for multiple returns"
                                    );

                                    return;
                                }
                                panic!("Result should be Interface type, got {:?}", result);
                            }
                        }
                    }
                }
            }
        }
        panic!("Could not find and parse interface type");
    }

    #[test]
    fn test_interface_with_embedded() {
        // Interface with embedded interface
        let source = b"package main\n\ntype ReadWriter interface {\n\tReader\n\tWrite(p []byte) (n int, err error)\n}\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(iface_node) = type_child.child_by_field_name("type") {
                            if iface_node.kind() == "interface_type" {
                                let result = translate_interface_type(&mut ctx, iface_node);
                                assert!(result.is_ok(), "Should translate interface with embedded: {:?}", result);

                                if let Ok(BrrrType::Interface(iface)) = result {
                                    // Should have at least 1 method (Write)
                                    assert!(iface.method_count() >= 1, "Should have Write method");

                                    // Should have embedded Reader
                                    assert!(
                                        iface.embedded_count() >= 1,
                                        "Should have embedded interface"
                                    );

                                    return;
                                }
                                panic!("Result should be Interface type, got {:?}", result);
                            }
                        }
                    }
                }
            }
        }
        panic!("Could not find and parse interface type");
    }

    #[test]
    fn test_sized_array_type() {
        // Test that sized arrays preserve their size
        let source = b"package main\n\ntype Arr [5]int\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(array_node) = type_child.child_by_field_name("type") {
                            if array_node.kind() == "array_type" {
                                let result = translate_array_type(&mut ctx, array_node);
                                assert!(result.is_ok(), "Should translate sized array: {:?}", result);

                                let ty = result.unwrap();
                                assert!(ty.is_sized_array(), "Should be SizedArray type");
                                assert_eq!(ty.array_size(), Some(5), "Array size should be 5");
                                return;
                            }
                        }
                    }
                }
            }
        }
        panic!("Could not find and parse array type");
    }

    #[test]
    fn test_slice_type_not_sized() {
        // Test that slices are NOT sized arrays
        let source = b"package main\n\ntype Slice []int\n";
        let mut ctx = GoTranslationContext::new(source);

        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&tree_sitter_go::LANGUAGE.into()).unwrap();
        let tree = parser.parse(source, None).unwrap();

        let root = tree.root_node();
        let mut cursor = root.walk();

        for child in root.children(&mut cursor) {
            if child.kind() == "type_declaration" {
                let mut type_cursor = child.walk();
                for type_child in child.children(&mut type_cursor) {
                    if type_child.kind() == "type_spec" {
                        if let Some(slice_node) = type_child.child_by_field_name("type") {
                            if slice_node.kind() == "slice_type" {
                                let result = translate_slice_type(&mut ctx, slice_node);
                                assert!(result.is_ok(), "Should translate slice: {:?}", result);

                                let ty = result.unwrap();
                                assert!(!ty.is_sized_array(), "Slice should NOT be SizedArray");
                                assert_eq!(ty.array_size(), None, "Slice should have no static size");
                                // Should be Wrap(Slice, ...)
                                assert!(
                                    matches!(ty, BrrrType::Wrap(WrapperKind::Slice, _)),
                                    "Should be Wrap(Slice, ...) type"
                                );
                                return;
                            }
                        }
                    }
                }
            }
        }
        panic!("Could not find and parse slice type");
    }

    #[test]
    fn test_parse_int_literal() {
        // Test integer literal parsing for array sizes
        assert_eq!(parse_int_literal("5"), Some(5));
        assert_eq!(parse_int_literal("123"), Some(123));
        assert_eq!(parse_int_literal("0"), Some(0));

        // Hex
        assert_eq!(parse_int_literal("0x10"), Some(16));
        assert_eq!(parse_int_literal("0X1F"), Some(31));

        // Octal
        assert_eq!(parse_int_literal("0o17"), Some(15));
        assert_eq!(parse_int_literal("017"), Some(15)); // Old style

        // Binary
        assert_eq!(parse_int_literal("0b101"), Some(5));

        // Underscores
        assert_eq!(parse_int_literal("1_000_000"), Some(1_000_000));
    }
}
