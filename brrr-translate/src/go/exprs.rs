//! Go expression translation to Brrr Expr.
//!
//! Maps Go expressions to their Brrr IR equivalents.

use super::context::GoTranslationContext;
use super::types::translate_type;
use crate::{missing_node, unsupported, TranslateResult, TranslationContext};
use brrr_repr::effects::EffectType;
use brrr_repr::expr::{BinaryOp, Expr, Expr_, Literal, Pattern, Pattern_, UnaryOp, WithLoc};
use brrr_repr::types::{FloatPrec, IntType, NumericType};
use brrr_repr::{BrrrType, Pos, Range};
use tree_sitter::Node;

/// Translate a Go expression node to Brrr Expr.
pub fn translate_expr<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr> {
    let range = node_range(node);

    let expr_ = match node.kind() {
        // Literals
        "int_literal" => translate_int_literal(ctx, node)?,
        "float_literal" => translate_float_literal(ctx, node)?,
        "imaginary_literal" => translate_imaginary_literal(ctx, node)?,
        "rune_literal" => translate_rune_literal(ctx, node)?,
        "interpreted_string_literal" | "raw_string_literal" => translate_string_literal(ctx, node)?,
        "true" => Expr_::Lit(Literal::Bool(true)),
        "false" => Expr_::Lit(Literal::Bool(false)),
        "nil" => {
            // nil is represented as Option::None
            Expr_::Variant {
                type_name: ctx.intern("Option"),
                variant: ctx.intern("None"),
                fields: Vec::new(),
            }
        }

        // Identifiers
        "identifier" => translate_identifier(ctx, node)?,
        "field_identifier" => translate_identifier(ctx, node)?,

        // Composite literals
        "composite_literal" => translate_composite_literal(ctx, node)?,

        // Selector expression (field access, method call)
        "selector_expression" => translate_selector(ctx, node)?,

        // Index expression
        "index_expression" => translate_index(ctx, node)?,

        // Slice expression
        "slice_expression" => translate_slice(ctx, node)?,

        // Call expression
        "call_expression" => translate_call(ctx, node)?,

        // Type assertion
        "type_assertion_expression" => translate_type_assertion(ctx, node)?,

        // Unary expressions
        "unary_expression" => translate_unary(ctx, node)?,

        // Binary expressions
        "binary_expression" => translate_binary(ctx, node)?,

        // Parenthesized expression
        "parenthesized_expression" => {
            let inner = node.child(1).ok_or_else(|| missing_node("inner expr", node))?;
            return translate_expr(ctx, inner);
        }

        // Function literal (closure)
        "func_literal" => translate_func_literal(ctx, node)?,

        // Type conversion
        "type_conversion_expression" => translate_type_conversion(ctx, node)?,

        // Channel receive
        "receive_expression" => translate_channel_receive(ctx, node)?,

        _ => return Err(unsupported(&format!("expression kind: {}", node.kind()), node)),
    };

    Ok(WithLoc::new(expr_, range))
}

/// Convert tree-sitter position to Brrr Range.
pub fn node_range(node: Node<'_>) -> Range {
    let start = node.start_position();
    let end = node.end_position();
    Range::new(
        Pos {
            file_id: 0,
            line: (start.row + 1) as u32,
            col: start.column as u32,
        },
        Pos {
            file_id: 0,
            line: (end.row + 1) as u32,
            col: end.column as u32,
        },
    )
}

/// Translate an integer literal.
fn translate_int_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let text = ctx.node_text(node);

    // Parse the integer, handling different bases
    let (value, _base) = if text.starts_with("0x") || text.starts_with("0X") {
        (i128::from_str_radix(&text[2..].replace('_', ""), 16), 16)
    } else if text.starts_with("0o") || text.starts_with("0O") {
        (i128::from_str_radix(&text[2..].replace('_', ""), 8), 8)
    } else if text.starts_with("0b") || text.starts_with("0B") {
        (i128::from_str_radix(&text[2..].replace('_', ""), 2), 2)
    } else if text.starts_with('0') && text.len() > 1 && !text.contains('.') {
        // Octal (old style)
        (i128::from_str_radix(&text[1..].replace('_', ""), 8), 8)
    } else {
        (text.replace('_', "").parse::<i128>(), 10)
    };

    let value = value.unwrap_or(0);

    // Determine appropriate type based on value
    let int_type = if value >= 0 && value <= i64::MAX as i128 {
        IntType::I64
    } else {
        IntType::I128
    };

    Ok(Expr_::Lit(Literal::Int(value, int_type)))
}

/// Translate a float literal.
fn translate_float_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let text = ctx.node_text(node);
    let value: f64 = text.replace('_', "").parse().unwrap_or(0.0);

    // Use F64 for float literals (Go's default)
    let bits = brrr_repr::expr::FloatBits(value.to_bits());
    Ok(Expr_::Lit(Literal::Float(bits, FloatPrec::F64)))
}

/// Translate an imaginary literal (complex number component).
fn translate_imaginary_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let text = ctx.node_text(node);
    // Remove trailing 'i'
    let value: f64 = text
        .trim_end_matches('i')
        .replace('_', "")
        .parse()
        .unwrap_or(0.0);

    // Represent as tuple (0.0, imag)
    let zero = Expr_::Lit(Literal::Float(
        brrr_repr::expr::FloatBits(0.0f64.to_bits()),
        FloatPrec::F64,
    ));
    let imag = Expr_::Lit(Literal::Float(
        brrr_repr::expr::FloatBits(value.to_bits()),
        FloatPrec::F64,
    ));

    Ok(Expr_::Tuple(vec![
        WithLoc::new(zero, node_range(node)),
        WithLoc::new(imag, node_range(node)),
    ]))
}

/// Translate a rune literal.
fn translate_rune_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let text = ctx.node_text(node);
    // Remove quotes and parse escape sequences
    let inner = &text[1..text.len() - 1];
    let c = parse_rune_escape(inner);
    Ok(Expr_::Lit(Literal::Char(c)))
}

/// Parse a rune escape sequence.
fn parse_rune_escape(s: &str) -> char {
    if s.starts_with('\\') {
        match s.chars().nth(1) {
            Some('n') => '\n',
            Some('t') => '\t',
            Some('r') => '\r',
            Some('\\') => '\\',
            Some('\'') => '\'',
            Some('"') => '"',
            Some('0') => '\0',
            Some('x') => {
                // Hex escape \xNN
                u8::from_str_radix(&s[2..4], 16)
                    .map(|b| b as char)
                    .unwrap_or('\0')
            }
            Some('u') => {
                // Unicode escape \uNNNN
                u32::from_str_radix(&s[2..6], 16)
                    .ok()
                    .and_then(char::from_u32)
                    .unwrap_or('\0')
            }
            Some('U') => {
                // Unicode escape \UNNNNNNNN
                u32::from_str_radix(&s[2..10], 16)
                    .ok()
                    .and_then(char::from_u32)
                    .unwrap_or('\0')
            }
            _ => s.chars().nth(1).unwrap_or('\0'),
        }
    } else {
        s.chars().next().unwrap_or('\0')
    }
}

/// Translate a string literal.
fn translate_string_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let text = ctx.node_text(node);

    // Remove quotes
    let inner = if text.starts_with('`') {
        // Raw string literal
        text[1..text.len() - 1].to_string()
    } else {
        // Interpreted string literal - process escapes
        let inner = &text[1..text.len() - 1];
        process_string_escapes(inner)
    };

    Ok(Expr_::Lit(Literal::String(inner)))
}

/// Process escape sequences in a string.
fn process_string_escapes(s: &str) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('t') => result.push('\t'),
                Some('r') => result.push('\r'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('\'') => result.push('\''),
                Some('0') => result.push('\0'),
                Some(other) => {
                    result.push('\\');
                    result.push(other);
                }
                None => result.push('\\'),
            }
        } else {
            result.push(c);
        }
    }

    result
}

/// Translate an identifier.
fn translate_identifier<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let name = ctx.node_text(node);
    let spur = ctx.intern(name);

    // Check if it's a variable in scope
    if ctx.lookup_var(spur).is_some() {
        Ok(Expr_::Var(spur))
    } else {
        // Could be a global/package-level identifier
        Ok(Expr_::Global(spur))
    }
}

/// Translate a composite literal (struct/array/slice/map literal).
fn translate_composite_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // composite_literal: type "{" [literal_value] "}"
    let type_node = node.child_by_field_name("type");
    let body_node = node.child_by_field_name("body");

    if let Some(body) = body_node {
        let mut elements = Vec::new();
        let mut cursor = body.walk();

        for child in body.children(&mut cursor) {
            match child.kind() {
                "literal_element" | "keyed_element" => {
                    if let Ok(elem) = translate_literal_element(ctx, child) {
                        elements.push(elem);
                    }
                }
                _ => {}
            }
        }

        // Determine if it's a struct, array, slice, or map based on type
        if let Some(type_node) = type_node {
            let type_kind = type_node.kind();
            match type_kind {
                "struct_type" | "type_identifier" | "qualified_type" => {
                    // Struct literal
                    let type_name = ctx.intern(ctx.node_text(type_node));
                    let fields: Vec<(lasso::Spur, Expr)> = elements
                        .into_iter()
                        .enumerate()
                        .map(|(i, (key, val))| {
                            let field_name = key.unwrap_or_else(|| ctx.intern(&format!("_{}", i)));
                            (field_name, val)
                        })
                        .collect();
                    return Ok(Expr_::Struct {
                        name: type_name,
                        fields,
                    });
                }
                "array_type" | "slice_type" => {
                    // Array/slice literal
                    let values: Vec<Expr> = elements.into_iter().map(|(_, v)| v).collect();
                    return Ok(Expr_::Array(values));
                }
                "map_type" => {
                    // Map literal - represented as array of key-value tuples
                    // TODO: proper map literal support
                    let values: Vec<Expr> = elements.into_iter().map(|(_, v)| v).collect();
                    return Ok(Expr_::Array(values));
                }
                _ => {}
            }
        }

        // Default to array literal
        let values: Vec<Expr> = elements.into_iter().map(|(_, v)| v).collect();
        Ok(Expr_::Array(values))
    } else {
        // Empty literal
        Ok(Expr_::Array(Vec::new()))
    }
}

/// Translate a literal element.
fn translate_literal_element<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<(Option<lasso::Spur>, Expr)> {
    match node.kind() {
        "keyed_element" => {
            // keyed_element: key ":" value
            let key = node.child_by_field_name("key").map(|k| {
                let key_text = ctx.node_text(k);
                ctx.intern(key_text)
            });
            let value_node = node
                .child_by_field_name("value")
                .ok_or_else(|| missing_node("element value", node))?;
            let value = translate_expr(ctx, value_node)?;
            Ok((key, value))
        }
        "literal_element" => {
            // literal_element: value
            if let Some(value_node) = node.child(0) {
                let value = translate_expr(ctx, value_node)?;
                Ok((None, value))
            } else {
                Err(missing_node("element value", node))
            }
        }
        _ => {
            // Direct expression
            let value = translate_expr(ctx, node)?;
            Ok((None, value))
        }
    }
}

/// Translate a selector expression (field access or method reference).
fn translate_selector<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // selector_expression: operand "." field
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;
    let field = node
        .child_by_field_name("field")
        .ok_or_else(|| missing_node("field", node))?;

    let operand_expr = translate_expr(ctx, operand)?;
    let field_name = ctx.intern(ctx.node_text(field));

    Ok(Expr_::Field(Box::new(operand_expr), field_name))
}

/// Translate an index expression.
fn translate_index<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // index_expression: operand "[" index "]"
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;
    let index = node
        .child_by_field_name("index")
        .ok_or_else(|| missing_node("index", node))?;

    let operand_expr = translate_expr(ctx, operand)?;
    let index_expr = translate_expr(ctx, index)?;

    Ok(Expr_::Index(Box::new(operand_expr), Box::new(index_expr)))
}

/// Translate a slice expression.
fn translate_slice<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // slice_expression: operand "[" [start] ":" [end] [":" [cap]] "]"
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;

    let operand_expr = translate_expr(ctx, operand)?;

    // Get start, end, and optional capacity
    let start = node
        .child_by_field_name("start")
        .map(|n| translate_expr(ctx, n))
        .transpose()?;
    let end = node
        .child_by_field_name("end")
        .map(|n| translate_expr(ctx, n))
        .transpose()?;
    let cap = node
        .child_by_field_name("capacity")
        .map(|n| translate_expr(ctx, n))
        .transpose()?;

    // Represent as method call: slice(start, end, cap)
    let slice_name = ctx.intern("slice");
    let mut args = Vec::new();

    if let Some(s) = start {
        args.push(s);
    } else {
        args.push(WithLoc::new(
            Expr_::Lit(Literal::Int(0, IntType::I64)),
            node_range(node),
        ));
    }

    if let Some(e) = end {
        args.push(e);
    }

    if let Some(c) = cap {
        args.push(c);
    }

    Ok(Expr_::MethodCall(Box::new(operand_expr), slice_name, args))
}

/// Translate a call expression.
fn translate_call<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // call_expression: function arguments
    let function = node
        .child_by_field_name("function")
        .ok_or_else(|| missing_node("function", node))?;
    let arguments = node.child_by_field_name("arguments");

    // Translate arguments
    let args = if let Some(args_node) = arguments {
        translate_arguments(ctx, args_node)?
    } else {
        Vec::new()
    };

    // Check if it's a method call (selector_expression)
    if function.kind() == "selector_expression" {
        let operand = function
            .child_by_field_name("operand")
            .ok_or_else(|| missing_node("operand", function))?;
        let field = function
            .child_by_field_name("field")
            .ok_or_else(|| missing_node("field", function))?;

        let operand_expr = translate_expr(ctx, operand)?;
        let method_name = ctx.intern(ctx.node_text(field));

        return Ok(Expr_::MethodCall(Box::new(operand_expr), method_name, args));
    }

    // Regular function call
    let func_expr = translate_expr(ctx, function)?;
    Ok(Expr_::Call(Box::new(func_expr), args))
}

/// Translate call arguments.
fn translate_arguments<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<Expr>> {
    let mut args = Vec::new();

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        match child.kind() {
            "(" | ")" | "," | "..." => {}
            _ => {
                if let Ok(expr) = translate_expr(ctx, child) {
                    args.push(expr);
                }
            }
        }
    }

    Ok(args)
}

/// Translate a type assertion.
fn translate_type_assertion<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // type_assertion_expression: operand "." "(" type ")"
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;
    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("type", node))?;

    let operand_expr = translate_expr(ctx, operand)?;
    let target_type = translate_type(ctx, type_node)?;

    Ok(Expr_::As(Box::new(operand_expr), target_type))
}

/// Translate a unary expression.
fn translate_unary<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // unary_expression: operator operand
    let operator = node
        .child_by_field_name("operator")
        .ok_or_else(|| missing_node("operator", node))?;
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;

    let operand_expr = translate_expr(ctx, operand)?;
    let op_text = ctx.node_text(operator);

    let op = match op_text {
        "-" => UnaryOp::Neg,
        "!" => UnaryOp::Not,
        "^" => UnaryOp::BitNot,
        "&" => return Ok(Expr_::Borrow(Box::new(operand_expr))),
        "*" => return Ok(Expr_::Deref(Box::new(operand_expr))),
        "<-" => {
            // Channel receive - use placeholder channel ID and element type
            return Ok(Expr_::Perform(
                brrr_repr::EffectOp::Recv(0, EffectType::Var(0)),
                vec![operand_expr],
            ));
        }
        _ => return Err(unsupported(&format!("unary operator: {}", op_text), node)),
    };

    Ok(Expr_::Unary(op, Box::new(operand_expr)))
}

/// Translate a binary expression.
fn translate_binary<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // binary_expression: left operator right
    let left = node
        .child_by_field_name("left")
        .ok_or_else(|| missing_node("left operand", node))?;
    let operator = node
        .child_by_field_name("operator")
        .ok_or_else(|| missing_node("operator", node))?;
    let right = node
        .child_by_field_name("right")
        .ok_or_else(|| missing_node("right operand", node))?;

    let left_expr = translate_expr(ctx, left)?;
    let right_expr = translate_expr(ctx, right)?;
    let op_text = ctx.node_text(operator);

    let op = match op_text {
        "+" => BinaryOp::Add,
        "-" => BinaryOp::Sub,
        "*" => BinaryOp::Mul,
        "/" => BinaryOp::Div,
        "%" => BinaryOp::Mod,
        "==" => BinaryOp::Eq,
        "!=" => BinaryOp::Ne,
        "<" => BinaryOp::Lt,
        "<=" => BinaryOp::Le,
        ">" => BinaryOp::Gt,
        ">=" => BinaryOp::Ge,
        "&&" => BinaryOp::And,
        "||" => BinaryOp::Or,
        "&" => BinaryOp::BitAnd,
        "|" => BinaryOp::BitOr,
        "^" => BinaryOp::BitXor,
        "<<" => BinaryOp::Shl,
        ">>" => BinaryOp::Shr,
        "&^" => {
            // Go's bit clear (AND NOT) - translate as x & ^y
            let not_right = WithLoc::new(Expr_::Unary(UnaryOp::BitNot, Box::new(right_expr)), node_range(node));
            return Ok(Expr_::Binary(BinaryOp::BitAnd, Box::new(left_expr), Box::new(not_right)));
        }
        _ => return Err(unsupported(&format!("binary operator: {}", op_text), node)),
    };

    Ok(Expr_::Binary(op, Box::new(left_expr), Box::new(right_expr)))
}

/// Translate a function literal (closure).
fn translate_func_literal<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // func_literal: "func" parameters [result] block
    let params_node = node.child_by_field_name("parameters");
    let body_node = node.child_by_field_name("body");

    let params = if let Some(p) = params_node {
        super::types::translate_parameters(ctx, p)?
    } else {
        Vec::new()
    };

    // Convert ParamType to (VarId, BrrrType)
    let param_pairs: Vec<(lasso::Spur, BrrrType)> = params
        .into_iter()
        .map(|p| (p.name.unwrap_or_else(|| ctx.intern("_")), p.ty))
        .collect();

    // Translate body
    let body = if let Some(b) = body_node {
        super::stmts::translate_block(ctx, b)?
    } else {
        WithLoc::new(Expr_::Lit(Literal::Unit), node_range(node))
    };

    Ok(Expr_::Lambda {
        params: param_pairs,
        body: Box::new(body),
    })
}

/// Translate a type conversion expression.
fn translate_type_conversion<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // type_conversion_expression: type "(" expression ")"
    let type_node = node
        .child_by_field_name("type")
        .ok_or_else(|| missing_node("type", node))?;
    let operand = node
        .child_by_field_name("operand")
        .ok_or_else(|| missing_node("operand", node))?;

    let target_type = translate_type(ctx, type_node)?;
    let operand_expr = translate_expr(ctx, operand)?;

    Ok(Expr_::As(Box::new(operand_expr), target_type))
}

/// Translate a channel receive expression.
fn translate_channel_receive<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // receive_expression: "<-" operand
    let operand = node.child(1).ok_or_else(|| missing_node("channel", node))?;
    let channel_expr = translate_expr(ctx, operand)?;

    // Use placeholder channel ID (0) and unknown element type (Var(0)) at translation time.
    // Actual channel resolution happens during analysis.
    Ok(Expr_::Perform(
        brrr_repr::EffectOp::Recv(0, EffectType::Var(0)),
        vec![channel_expr],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exprs_module_loads() {
        // Verify the module compiles and basic types are available
        let source = b"package main";
        let _ctx = GoTranslationContext::new(source);
        assert!(true);
    }
}
