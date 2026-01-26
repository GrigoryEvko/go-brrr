//! Go statement translation to Brrr Expr.
//!
//! Maps Go statements to their Brrr IR equivalents.
//! Go statements are expression-oriented in Brrr IR.

use super::context::GoTranslationContext;
use super::exprs::{translate_expr, node_range};
use super::types::translate_type;
use crate::{missing_node, unsupported, TranslateResult, TranslationContext};
use brrr_repr::expr::{BinaryOp, Expr, Expr_, Literal, MatchArm, Pattern, Pattern_, UnaryOp, WithLoc};
use brrr_repr::types::IntType;
use brrr_repr::effects::EffectType;
use brrr_repr::{BrrrType, EffectOp};
use tree_sitter::Node;

/// Translate a Go statement node to Brrr Expr.
pub fn translate_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr> {
    let range = node_range(node);

    let expr_ = match node.kind() {
        // Block
        "block" => return translate_block(ctx, node),

        // Variable declarations
        "short_var_declaration" => translate_short_var_decl(ctx, node)?,
        "var_declaration" => translate_var_decl(ctx, node)?,
        "const_declaration" => translate_const_decl(ctx, node)?,

        // Assignments
        "assignment_statement" => translate_assignment(ctx, node)?,

        // Expression statement (function calls, channel operations)
        "expression_statement" => {
            let expr = node.child(0).ok_or_else(|| missing_node("expression", node))?;
            return translate_expr(ctx, expr);
        }

        // Control flow
        "if_statement" => translate_if_stmt(ctx, node)?,
        "for_statement" => translate_for_stmt(ctx, node)?,
        "switch_statement" | "expression_switch_statement" => translate_switch_stmt(ctx, node)?,
        "type_switch_statement" => translate_type_switch_stmt(ctx, node)?,
        "select_statement" => translate_select_stmt(ctx, node)?,

        // Jumps
        "return_statement" => translate_return_stmt(ctx, node)?,
        "break_statement" => translate_break_stmt(ctx, node)?,
        "continue_statement" => translate_continue_stmt(ctx, node)?,
        "goto_statement" => translate_goto_stmt(ctx, node)?,
        "fallthrough_statement" => {
            // Fallthrough is handled specially in switch translation
            Expr_::Lit(Literal::Unit)
        }

        // Special statements
        "defer_statement" => translate_defer_stmt(ctx, node)?,
        "go_statement" => translate_go_stmt(ctx, node)?,
        "send_statement" => translate_send_stmt(ctx, node)?,

        // Increment/Decrement
        "inc_statement" => translate_inc_dec(ctx, node, true)?,
        "dec_statement" => translate_inc_dec(ctx, node, false)?,

        // Labeled statement
        "labeled_statement" => translate_labeled_stmt(ctx, node)?,

        // Empty statement
        "empty_statement" | ";" => Expr_::Lit(Literal::Unit),

        // Type/const declarations at statement level
        "type_declaration" => {
            // Type declarations don't produce runtime expressions
            Expr_::Lit(Literal::Unit)
        }

        _ => return Err(unsupported(&format!("statement kind: {}", node.kind()), node)),
    };

    Ok(WithLoc::new(expr_, range))
}

/// Translate a block to a sequence of expressions.
pub fn translate_block<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr> {
    let range = node_range(node);

    ctx.push_scope();

    let mut stmts = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "{" | "}" | "comment" => {}
            "statement_list" => {
                // Handle nested statement_list by recursively processing its children
                let mut stmt_cursor = child.walk();
                for stmt_child in child.children(&mut stmt_cursor) {
                    if stmt_child.kind() != "comment" {
                        if let Ok(expr) = translate_stmt(ctx, stmt_child) {
                            stmts.push(expr);
                        }
                    }
                }
            }
            _ => {
                if let Ok(expr) = translate_stmt(ctx, child) {
                    stmts.push(expr);
                }
            }
        }
    }

    ctx.pop_scope();

    // Convert statements to block or sequence
    if stmts.is_empty() {
        Ok(WithLoc::new(Expr_::Lit(Literal::Unit), range))
    } else if stmts.len() == 1 {
        Ok(stmts.remove(0))
    } else {
        Ok(WithLoc::new(Expr_::Block(stmts), range))
    }
}

/// Translate short variable declaration: `x := expr` or `x, y := expr`
fn translate_short_var_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let left = node.child_by_field_name("left")
        .ok_or_else(|| missing_node("left", node))?;
    let right = node.child_by_field_name("right")
        .ok_or_else(|| missing_node("right", node))?;

    // Collect left-hand side names
    let mut names = Vec::new();
    let mut cursor = left.walk();
    for child in left.children(&mut cursor) {
        if child.kind() == "identifier" {
            let name = ctx.node_text(child);
            let spur = ctx.intern(name);
            names.push(spur);
        }
    }

    // Translate right-hand side
    let init = translate_expr(ctx, right)?;

    // Bind variables (all Go variables are mutable by default)
    for &name in &names {
        ctx.bind_var(name, BrrrType::UNKNOWN, true);
    }

    // For single variable, use LetMut
    if names.len() == 1 {
        Ok(Expr_::LetMut {
            var: names[0],
            ty: None,
            init: Box::new(init.clone()),
            body: Box::new(WithLoc::new(Expr_::Lit(Literal::Unit), node_range(node))),
        })
    } else {
        // Multiple assignment - destructure tuple
        let pattern = Pattern_::Tuple(
            names.iter()
                .map(|&n| WithLoc::new(Pattern_::Var(n), node_range(node)))
                .collect()
        );
        Ok(Expr_::Let {
            pattern: WithLoc::new(pattern, node_range(node)),
            ty: None,
            init: Box::new(init),
            body: Box::new(WithLoc::new(Expr_::Lit(Literal::Unit), node_range(node))),
        })
    }
}

/// Translate var declaration: `var x T = expr`
fn translate_var_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // var_declaration can have multiple var_spec children
    let mut cursor = node.walk();
    let mut exprs = Vec::new();

    for child in node.children(&mut cursor) {
        if child.kind() == "var_spec" {
            if let Ok(expr) = translate_var_spec(ctx, child) {
                exprs.push(expr);
            }
        }
    }

    if exprs.is_empty() {
        Ok(Expr_::Lit(Literal::Unit))
    } else if exprs.len() == 1 {
        Ok(exprs.remove(0).value)
    } else {
        Ok(Expr_::Block(exprs))
    }
}

/// Translate a single var spec.
fn translate_var_spec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr> {
    let range = node_range(node);

    // Get names
    let name_node = node.child_by_field_name("name")
        .ok_or_else(|| missing_node("name", node))?;
    let name = ctx.intern(ctx.node_text(name_node));

    // Get optional type
    let ty = node.child_by_field_name("type")
        .map(|t| translate_type(ctx, t))
        .transpose()?;

    // Get optional initializer
    let init = node.child_by_field_name("value")
        .map(|v| translate_expr(ctx, v))
        .transpose()?
        .unwrap_or_else(|| {
            // Zero value for the type
            WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
        });

    // Bind the variable
    ctx.bind_var(name, ty.clone().unwrap_or(BrrrType::UNKNOWN), true);

    Ok(WithLoc::new(
        Expr_::LetMut {
            var: name,
            ty,
            init: Box::new(init),
            body: Box::new(WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())),
        },
        range,
    ))
}

/// Translate const declaration.
fn translate_const_decl<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let mut cursor = node.walk();
    let mut exprs = Vec::new();

    for child in node.children(&mut cursor) {
        if child.kind() == "const_spec" {
            if let Ok(expr) = translate_const_spec(ctx, child) {
                exprs.push(expr);
            }
        }
    }

    if exprs.is_empty() {
        Ok(Expr_::Lit(Literal::Unit))
    } else if exprs.len() == 1 {
        Ok(exprs.remove(0).value)
    } else {
        Ok(Expr_::Block(exprs))
    }
}

/// Translate a single const spec.
fn translate_const_spec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr> {
    let range = node_range(node);

    let name_node = node.child_by_field_name("name")
        .ok_or_else(|| missing_node("name", node))?;
    let name = ctx.intern(ctx.node_text(name_node));

    let ty = node.child_by_field_name("type")
        .map(|t| translate_type(ctx, t))
        .transpose()?;

    let init = node.child_by_field_name("value")
        .map(|v| translate_expr(ctx, v))
        .transpose()?
        .unwrap_or_else(|| WithLoc::new(Expr_::Lit(Literal::Unit), range.clone()));

    // Constants are immutable
    ctx.bind_var(name, ty.clone().unwrap_or(BrrrType::UNKNOWN), false);

    Ok(WithLoc::new(
        Expr_::Let {
            pattern: WithLoc::new(Pattern_::Var(name), range.clone()),
            ty,
            init: Box::new(init),
            body: Box::new(WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())),
        },
        range,
    ))
}

/// Translate assignment: `x = expr` or `x, y = expr1, expr2`
fn translate_assignment<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let left = node.child_by_field_name("left")
        .ok_or_else(|| missing_node("left", node))?;
    let right = node.child_by_field_name("right")
        .ok_or_else(|| missing_node("right", node))?;

    // Check for compound assignment operators
    let operator = node.child_by_field_name("operator")
        .map(|o| ctx.node_text(o))
        .unwrap_or("=");

    let left_expr = translate_expr(ctx, left)?;
    let right_expr = translate_expr(ctx, right)?;

    // Handle compound assignments (+=, -=, etc.)
    let final_value = match operator {
        "=" => right_expr,
        "+=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Add, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "-=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Sub, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "*=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Mul, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "/=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Div, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "%=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Mod, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "&=" => WithLoc::new(
            Expr_::Binary(BinaryOp::BitAnd, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "|=" => WithLoc::new(
            Expr_::Binary(BinaryOp::BitOr, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "^=" => WithLoc::new(
            Expr_::Binary(BinaryOp::BitXor, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "<<=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Shl, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        ">>=" => WithLoc::new(
            Expr_::Binary(BinaryOp::Shr, Box::new(left_expr.clone()), Box::new(right_expr)),
            node_range(node),
        ),
        "&^=" => {
            // Bit clear assignment
            let not_right = WithLoc::new(
                Expr_::Unary(UnaryOp::BitNot, Box::new(right_expr)),
                node_range(node),
            );
            WithLoc::new(
                Expr_::Binary(BinaryOp::BitAnd, Box::new(left_expr.clone()), Box::new(not_right)),
                node_range(node),
            )
        }
        _ => right_expr,
    };

    Ok(Expr_::Assign(Box::new(left_expr), Box::new(final_value)))
}

/// Translate if statement.
fn translate_if_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // if_statement: "if" [simple_statement ";"] condition consequence ["else" alternative]

    // Handle optional init statement
    let init_stmt = node.child_by_field_name("initializer")
        .map(|i| translate_stmt(ctx, i))
        .transpose()?;

    let condition = node.child_by_field_name("condition")
        .ok_or_else(|| missing_node("condition", node))?;
    let consequence = node.child_by_field_name("consequence")
        .ok_or_else(|| missing_node("consequence", node))?;
    let alternative = node.child_by_field_name("alternative");

    let cond_expr = translate_expr(ctx, condition)?;
    let then_expr = translate_block(ctx, consequence)?;
    let else_expr = if let Some(alt) = alternative {
        if alt.kind() == "if_statement" {
            translate_stmt(ctx, alt)?
        } else {
            translate_block(ctx, alt)?
        }
    } else {
        WithLoc::new(Expr_::Lit(Literal::Unit), node_range(node))
    };

    let if_expr = Expr_::If(
        Box::new(cond_expr),
        Box::new(then_expr),
        Box::new(else_expr),
    );

    // Wrap in let if there's an init statement
    if let Some(init) = init_stmt {
        Ok(Expr_::Seq(
            Box::new(init),
            Box::new(WithLoc::new(if_expr, node_range(node))),
        ))
    } else {
        Ok(if_expr)
    }
}

/// Translate for statement (all three forms).
fn translate_for_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // Check for range clause
    if let Some(range_clause) = find_child_by_kind(node, "range_clause") {
        return translate_for_range(ctx, node, range_clause);
    }

    // Check for for clause (init; cond; post)
    if let Some(init) = node.child_by_field_name("initializer") {
        return translate_for_clause(ctx, node, Some(init));
    }

    // Simple condition-only or infinite loop
    let condition = node.child_by_field_name("condition");
    let body = node.child_by_field_name("body")
        .ok_or_else(|| missing_node("body", node))?;

    let body_expr = translate_block(ctx, body)?;

    if let Some(cond) = condition {
        let cond_expr = translate_expr(ctx, cond)?;
        Ok(Expr_::While {
            label: None,
            cond: Box::new(cond_expr),
            body: Box::new(body_expr),
        })
    } else {
        // Infinite loop
        Ok(Expr_::Loop {
            label: None,
            body: Box::new(body_expr),
        })
    }
}

/// Translate for-range statement.
fn translate_for_range<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
    range_clause: Node<'_>,
) -> TranslateResult<Expr_> {
    // range_clause: [left ["," left] "=" | ":="] "range" right
    let range_expr = range_clause.child_by_field_name("right")
        .ok_or_else(|| missing_node("range expression", range_clause))?;

    let iter_expr = translate_expr(ctx, range_expr)?;

    // Get iteration variables
    let left = range_clause.child_by_field_name("left");

    let body = node.child_by_field_name("body")
        .ok_or_else(|| missing_node("body", node))?;

    ctx.push_scope();

    // Bind iteration variables
    let var = if let Some(l) = left {
        let name = ctx.intern(ctx.node_text(l));
        ctx.bind_var(name, BrrrType::UNKNOWN, true);
        name
    } else {
        ctx.intern("_")
    };

    let body_expr = translate_block(ctx, body)?;
    ctx.pop_scope();

    Ok(Expr_::For {
        label: None,
        var,
        iter: Box::new(iter_expr),
        body: Box::new(body_expr),
    })
}

/// Translate for-clause statement (init; cond; post).
fn translate_for_clause<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
    init: Option<Node<'_>>,
) -> TranslateResult<Expr_> {
    let condition = node.child_by_field_name("condition");
    let update = node.child_by_field_name("update");
    let body = node.child_by_field_name("body")
        .ok_or_else(|| missing_node("body", node))?;

    ctx.push_scope();

    // Translate init
    let init_expr = if let Some(i) = init {
        Some(translate_stmt(ctx, i)?)
    } else {
        None
    };

    // Translate condition
    let cond_expr = if let Some(c) = condition {
        translate_expr(ctx, c)?
    } else {
        WithLoc::new(Expr_::Lit(Literal::Bool(true)), node_range(node))
    };

    // Translate body
    let body_expr = translate_block(ctx, body)?;

    // Translate post (update)
    let post_expr = if let Some(u) = update {
        Some(translate_stmt(ctx, u)?)
    } else {
        None
    };

    ctx.pop_scope();

    // Combine body and post into loop body
    let loop_body = if let Some(post) = post_expr {
        WithLoc::new(
            Expr_::Seq(Box::new(body_expr), Box::new(post)),
            node_range(node),
        )
    } else {
        body_expr
    };

    let while_loop = Expr_::While {
        label: None,
        cond: Box::new(cond_expr),
        body: Box::new(loop_body),
    };

    // Wrap in init if present
    if let Some(init) = init_expr {
        Ok(Expr_::Seq(
            Box::new(init),
            Box::new(WithLoc::new(while_loop, node_range(node))),
        ))
    } else {
        Ok(while_loop)
    }
}

/// Translate switch statement.
fn translate_switch_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // switch_statement: "switch" [init ";"] [value] "{" cases "}"
    let init = node.child_by_field_name("initializer")
        .map(|i| translate_stmt(ctx, i))
        .transpose()?;

    let value = node.child_by_field_name("value")
        .map(|v| translate_expr(ctx, v))
        .transpose()?
        .unwrap_or_else(|| {
            WithLoc::new(Expr_::Lit(Literal::Bool(true)), node_range(node))
        });

    let mut arms = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "expression_case" | "default_case" => {
                if let Ok(arm) = translate_switch_case(ctx, child) {
                    arms.push(arm);
                }
            }
            _ => {}
        }
    }

    let match_expr = Expr_::Match(Box::new(value), arms);

    if let Some(init_expr) = init {
        Ok(Expr_::Seq(
            Box::new(init_expr),
            Box::new(WithLoc::new(match_expr, node_range(node))),
        ))
    } else {
        Ok(match_expr)
    }
}

/// Translate a switch case.
fn translate_switch_case<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<MatchArm> {
    let range = node_range(node);

    let (pattern, guard) = if node.kind() == "default_case" {
        (WithLoc::new(Pattern_::Wild, range.clone()), None)
    } else {
        // expression_case: "case" expression_list ":" statements
        let expr_list = find_child_by_kind(node, "expression_list");

        if let Some(exprs) = expr_list {
            let mut cursor = exprs.walk();
            let patterns: Vec<_> = exprs.children(&mut cursor)
                .filter(|c| c.kind() != ",")
                .filter_map(|c| translate_expr(ctx, c).ok())
                .map(|e| expr_to_pattern(e))
                .collect();

            if patterns.is_empty() {
                (WithLoc::new(Pattern_::Wild, range.clone()), None)
            } else if patterns.len() == 1 {
                (patterns.into_iter().next().unwrap(), None)
            } else {
                // Multiple values in case - chain Or patterns
                let mut iter = patterns.into_iter();
                let first = iter.next().unwrap();
                let combined = iter.fold(first, |acc, pat| {
                    WithLoc::new(
                        Pattern_::Or(Box::new(acc), Box::new(pat)),
                        range.clone(),
                    )
                });
                (combined, None)
            }
        } else {
            (WithLoc::new(Pattern_::Wild, range.clone()), None)
        }
    };

    // Translate body (statements after the colon)
    let mut body_stmts = Vec::new();
    let mut cursor = node.walk();
    let mut found_colon = false;

    for child in node.children(&mut cursor) {
        if child.kind() == ":" {
            found_colon = true;
            continue;
        }
        if found_colon && child.kind() != "comment" {
            if let Ok(stmt) = translate_stmt(ctx, child) {
                body_stmts.push(stmt);
            }
        }
    }

    let body = if body_stmts.is_empty() {
        WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
    } else if body_stmts.len() == 1 {
        body_stmts.remove(0)
    } else {
        WithLoc::new(Expr_::Block(body_stmts), range.clone())
    };

    Ok(MatchArm { range, pattern, guard, body })
}

/// Convert an expression to a pattern (for switch cases).
fn expr_to_pattern(expr: Expr) -> Pattern {
    let range = expr.range.clone();

    let pattern_ = match expr.value {
        Expr_::Lit(lit) => Pattern_::Lit(lit),
        Expr_::Var(v) => Pattern_::Var(v),
        Expr_::Tuple(es) => {
            Pattern_::Tuple(es.into_iter().map(expr_to_pattern).collect())
        }
        _ => Pattern_::Wild,
    };

    WithLoc::new(pattern_, range)
}

/// Translate type switch statement.
///
/// Go type switch: `switch v := x.(type) { case int: ... case string: ... }`
/// Translates to Match with Pattern::Type patterns that preserve type information.
fn translate_type_switch_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // type_switch_statement: "switch" [init ";"] type_switch_guard "{" cases "}"
    let init = node.child_by_field_name("initializer")
        .map(|i| translate_stmt(ctx, i))
        .transpose()?;

    // Get the type switch guard to extract binding and value
    let guard = find_child_by_kind(node, "type_switch_guard")
        .ok_or_else(|| missing_node("type switch guard", node))?;

    // Extract binding variable from guard (e.g., `v` in `v := x.(type)`)
    // type_switch_guard structure: [identifier ":="] expression "." "(" "type" ")"
    let binding = extract_type_switch_binding(ctx, guard);

    // Get the value being type-switched
    let value = guard.child_by_field_name("value")
        .map(|v| translate_expr(ctx, v))
        .transpose()?
        .unwrap_or_else(|| WithLoc::new(Expr_::Lit(Literal::Unit), node_range(node)));

    let mut arms = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "type_case" | "default_case" => {
                if let Ok(arm) = translate_type_case(ctx, child, binding) {
                    arms.push(arm);
                }
            }
            _ => {}
        }
    }

    let match_expr = Expr_::Match(Box::new(value), arms);

    if let Some(init_expr) = init {
        Ok(Expr_::Seq(
            Box::new(init_expr),
            Box::new(WithLoc::new(match_expr, node_range(node))),
        ))
    } else {
        Ok(match_expr)
    }
}

/// Extract the binding variable from a type switch guard.
/// For `v := x.(type)`, returns `Some(v_spur)`.
/// For `x.(type)` (no binding), returns `None`.
fn extract_type_switch_binding<'src>(
    ctx: &mut GoTranslationContext<'src>,
    guard: Node<'_>,
) -> Option<lasso::Spur> {
    // Look for an identifier that's part of the short var declaration pattern
    // The structure is: identifier ":=" expression "." "(" "type" ")"
    let mut cursor = guard.walk();
    let mut found_identifier = None;
    let mut found_assign = false;

    for child in guard.children(&mut cursor) {
        match child.kind() {
            "identifier" => {
                // This might be the binding variable
                found_identifier = Some(ctx.intern(ctx.node_text(child)));
            }
            ":=" => {
                // Confirm this is a short var declaration
                found_assign = true;
            }
            _ => {}
        }
    }

    // Only return binding if we found both identifier and :=
    if found_assign {
        found_identifier
    } else {
        None
    }
}

/// Translate a type case to a MatchArm with proper type patterns.
///
/// - `case int:` becomes `Pattern_::Type { expected: Int, binding }`
/// - `case int, string:` becomes `Pattern_::Or` of type patterns
/// - `default:` becomes `Pattern_::Wild`
fn translate_type_case<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
    binding: Option<lasso::Spur>,
) -> TranslateResult<MatchArm> {
    let range = node_range(node);

    let pattern = if node.kind() == "default_case" {
        WithLoc::new(Pattern_::Wild, range.clone())
    } else {
        // type_case: "case" type_list ":" statements
        // Parse the type list and create type patterns
        let types = collect_type_case_types(ctx, node)?;

        if types.is_empty() {
            // Fallback to wildcard if no types found
            WithLoc::new(Pattern_::Wild, range.clone())
        } else if types.len() == 1 {
            // Single type: Pattern::Type { expected, binding }
            WithLoc::new(
                Pattern_::Type {
                    expected: types.into_iter().next().unwrap(),
                    binding,
                },
                range.clone(),
            )
        } else {
            // Multiple types: Or-pattern of Type patterns
            // e.g., `case int, string:` becomes `Type{int} | Type{string}`
            // Note: In multiple type cases, the binding is available but
            // has union type semantics - handled downstream
            let mut type_patterns: Vec<Pattern> = types
                .into_iter()
                .map(|ty| {
                    WithLoc::new(
                        Pattern_::Type {
                            expected: ty,
                            // In multi-type cases, binding is only on the outer pattern
                            // to avoid duplicate bindings in or-patterns
                            binding: None,
                        },
                        range.clone(),
                    )
                })
                .collect();

            // Chain into Or patterns
            let first = type_patterns.remove(0);
            let combined = type_patterns.into_iter().fold(first, |acc, pat| {
                WithLoc::new(Pattern_::Or(Box::new(acc), Box::new(pat)), range.clone())
            });

            // If there's a binding with multiple types, wrap in As-pattern
            if let Some(var) = binding {
                WithLoc::new(Pattern_::As(Box::new(combined), var), range.clone())
            } else {
                combined
            }
        }
    };

    // Translate body statements
    let mut body_stmts = Vec::new();
    let mut cursor = node.walk();
    let mut found_colon = false;

    for child in node.children(&mut cursor) {
        if child.kind() == ":" {
            found_colon = true;
            continue;
        }
        if found_colon && child.kind() != "comment" {
            if let Ok(stmt) = translate_stmt(ctx, child) {
                body_stmts.push(stmt);
            }
        }
    }

    let body = if body_stmts.is_empty() {
        WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
    } else if body_stmts.len() == 1 {
        body_stmts.remove(0)
    } else {
        WithLoc::new(Expr_::Block(body_stmts), range.clone())
    };

    Ok(MatchArm {
        range,
        pattern,
        guard: None,
        body,
    })
}

/// Collect types from a type_case node.
/// Handles both single types and type lists (comma-separated).
fn collect_type_case_types<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<BrrrType>> {
    let mut types = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        // Skip "case" keyword and ":"
        if child.kind() == "case" || child.kind() == ":" {
            continue;
        }

        // Handle type list (comma-separated types)
        if child.kind() == "type_list" || child.kind() == "_type_list" {
            let mut type_cursor = child.walk();
            for type_child in child.children(&mut type_cursor) {
                if type_child.kind() != "," {
                    if let Ok(ty) = translate_type(ctx, type_child) {
                        types.push(ty);
                    }
                }
            }
        } else if is_type_node(child.kind()) {
            // Direct type node
            if let Ok(ty) = translate_type(ctx, child) {
                types.push(ty);
            }
        }
    }

    Ok(types)
}

/// Check if a node kind represents a type.
fn is_type_node(kind: &str) -> bool {
    matches!(
        kind,
        "type_identifier"
            | "qualified_type"
            | "pointer_type"
            | "array_type"
            | "slice_type"
            | "map_type"
            | "channel_type"
            | "function_type"
            | "struct_type"
            | "interface_type"
            | "parenthesized_type"
    )
}

/// Translate select statement.
fn translate_select_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // select_statement: "select" "{" comm_clauses "}"
    // Translate to Match with branch effect

    let mut arms = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "communication_case" | "default_case" => {
                if let Ok(arm) = translate_comm_case(ctx, child) {
                    arms.push(arm);
                }
            }
            _ => {}
        }
    }

    // Select is a branching effect operation
    // Use channel ID 0 and empty labels for now - proper channel resolution happens later
    let branch_effect = Expr_::Perform(EffectOp::Branch(0, Vec::new()), Vec::new());
    Ok(Expr_::Match(
        Box::new(WithLoc::new(branch_effect, node_range(node))),
        arms,
    ))
}

/// Translate a communication case.
fn translate_comm_case<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<MatchArm> {
    let range = node_range(node);

    let pattern = if node.kind() == "default_case" {
        WithLoc::new(Pattern_::Wild, range.clone())
    } else {
        // communication_case: "case" (send_statement | receive_statement) ":" statements
        // For now, use wildcard
        WithLoc::new(Pattern_::Wild, range.clone())
    };

    // Translate body
    let mut body_stmts = Vec::new();
    let mut cursor = node.walk();
    let mut found_colon = false;

    for child in node.children(&mut cursor) {
        if child.kind() == ":" {
            found_colon = true;
            continue;
        }
        if found_colon && child.kind() != "comment" {
            if let Ok(stmt) = translate_stmt(ctx, child) {
                body_stmts.push(stmt);
            }
        }
    }

    let body = if body_stmts.is_empty() {
        WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
    } else if body_stmts.len() == 1 {
        body_stmts.remove(0)
    } else {
        WithLoc::new(Expr_::Block(body_stmts), range.clone())
    };

    Ok(MatchArm {
        range,
        pattern,
        guard: None,
        body,
    })
}

/// Translate return statement.
fn translate_return_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // return_statement: "return" [expression_list]
    let expr_list = node.child_by_field_name("result");

    if let Some(exprs) = expr_list {
        let values = translate_expr_list(ctx, exprs)?;
        if values.len() == 1 {
            Ok(Expr_::Return(Some(Box::new(values.into_iter().next().unwrap()))))
        } else if values.is_empty() {
            Ok(Expr_::Return(None))
        } else {
            // Multiple return values - tuple
            Ok(Expr_::Return(Some(Box::new(
                WithLoc::new(Expr_::Tuple(values), node_range(node))
            ))))
        }
    } else {
        // Naked return - check for named returns
        let named_returns = ctx.named_returns();
        if named_returns.is_empty() {
            Ok(Expr_::Return(None))
        } else {
            // Return the named return variables as a tuple
            let returns: Vec<Expr> = named_returns.iter()
                .map(|(name, _)| WithLoc::new(Expr_::Var(*name), node_range(node)))
                .collect();
            if returns.len() == 1 {
                Ok(Expr_::Return(Some(Box::new(returns.into_iter().next().unwrap()))))
            } else {
                Ok(Expr_::Return(Some(Box::new(
                    WithLoc::new(Expr_::Tuple(returns), node_range(node))
                ))))
            }
        }
    }
}

/// Translate expression list.
fn translate_expr_list<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Vec<Expr>> {
    let mut exprs = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        if child.kind() != "," {
            if let Ok(expr) = translate_expr(ctx, child) {
                exprs.push(expr);
            }
        }
    }

    Ok(exprs)
}

/// Translate break statement.
fn translate_break_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let label = node.child_by_field_name("label")
        .map(|l| ctx.intern(ctx.node_text(l)));

    Ok(Expr_::Break {
        label,
        value: None,
    })
}

/// Translate continue statement.
fn translate_continue_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let label = node.child_by_field_name("label")
        .map(|l| ctx.intern(ctx.node_text(l)));

    Ok(Expr_::Continue { label })
}

/// Translate goto statement.
fn translate_goto_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // Goto jumps to a labeled statement. Unlike break/continue which exit/continue
    // loops, goto can jump forward or backward to any label in the same function.
    // Note: Go restricts goto to not skip variable declarations.
    let label = node.child_by_field_name("label")
        .map(|l| ctx.intern(ctx.node_text(l)))
        .ok_or_else(|| missing_node("label", node))?;

    Ok(Expr_::Goto { label })
}

/// Translate defer statement.
///
/// Go defer semantics:
/// - Deferred calls are executed in LIFO order when the surrounding function returns
/// - They execute even if the function panics
/// - Arguments are evaluated when the defer statement executes, not when the
///   deferred function runs
///
/// Implementation:
/// - We collect deferred expressions in the context during translation
/// - At function exit (in translate_function_def), we wrap the body with
///   nested Try-finally blocks in reverse order to achieve LIFO semantics
///
/// Example:
///   defer f()  // Runs LAST
///   defer g()  // Runs SECOND
///   defer h()  // Runs FIRST
///   ...body...
///
/// Becomes:
///   Try { body: Try { body: Try { body: ...body..., finally: h() }, finally: g() }, finally: f() }
fn translate_defer_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // defer_statement: "defer" expression
    let call = node.child(1)
        .ok_or_else(|| missing_node("deferred call", node))?;

    // Translate the deferred expression (arguments are evaluated now)
    let call_expr = translate_expr(ctx, call)?;

    // Push to defer stack - will be wrapped at function exit
    ctx.push_defer(call_expr);

    // Defer statement itself produces no immediate value
    Ok(Expr_::Lit(Literal::Unit))
}

/// Translate go statement (spawn goroutine).
fn translate_go_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // go_statement: "go" expression
    let call = node.child(1)
        .ok_or_else(|| missing_node("goroutine call", node))?;

    let call_expr = translate_expr(ctx, call)?;

    // Spawn effect
    Ok(Expr_::Spawn(Box::new(call_expr)))
}

/// Translate send statement (channel send).
fn translate_send_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // send_statement: channel "<-" value
    let channel = node.child_by_field_name("channel")
        .ok_or_else(|| missing_node("channel", node))?;
    let value = node.child_by_field_name("value")
        .ok_or_else(|| missing_node("value", node))?;

    let channel_expr = translate_expr(ctx, channel)?;
    let value_expr = translate_expr(ctx, value)?;

    // Send effect - channel ID 0 as placeholder, proper resolution happens later
    Ok(Expr_::Perform(EffectOp::Send(0, EffectType::Unit), vec![channel_expr, value_expr]))
}

/// Translate increment/decrement statement.
fn translate_inc_dec<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
    is_increment: bool,
) -> TranslateResult<Expr_> {
    let operand = node.child_by_field_name("operand")
        .or_else(|| node.child(0))
        .ok_or_else(|| missing_node("operand", node))?;

    let operand_expr = translate_expr(ctx, operand)?;
    let one = WithLoc::new(
        Expr_::Lit(Literal::Int(1, IntType::I64)),
        node_range(node),
    );

    let op = if is_increment { BinaryOp::Add } else { BinaryOp::Sub };
    let new_value = WithLoc::new(
        Expr_::Binary(op, Box::new(operand_expr.clone()), Box::new(one)),
        node_range(node),
    );

    Ok(Expr_::Assign(Box::new(operand_expr), Box::new(new_value)))
}

/// Translate labeled statement.
fn translate_labeled_stmt<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    // labeled_statement: label ":" statement
    let label = node.child_by_field_name("label")
        .map(|l| ctx.intern(ctx.node_text(l)))
        .ok_or_else(|| missing_node("label", node))?;

    // Get the actual statement
    let stmt = node.child(2)
        .ok_or_else(|| missing_node("statement", node))?;

    let inner_expr = translate_stmt(ctx, stmt)?;

    // Check if the inner statement is a loop - if so, attach label directly
    // Otherwise, wrap in Labeled
    let result = match &inner_expr.value {
        Expr_::For { var, iter, body, .. } => {
            // Attach label to for loop
            Expr_::For {
                label: Some(label),
                var: *var,
                iter: iter.clone(),
                body: body.clone(),
            }
        }
        Expr_::While { cond, body, .. } => {
            // Attach label to while loop
            Expr_::While {
                label: Some(label),
                cond: cond.clone(),
                body: body.clone(),
            }
        }
        Expr_::Loop { body, .. } => {
            // Attach label to loop
            Expr_::Loop {
                label: Some(label),
                body: body.clone(),
            }
        }
        _ => {
            // Non-loop statement: wrap in Labeled for goto targets
            Expr_::Labeled {
                label,
                body: Box::new(inner_expr),
            }
        }
    };

    Ok(result)
}

/// Find a child node by its kind.
fn find_child_by_kind<'a>(node: Node<'a>, kind: &str) -> Option<Node<'a>> {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == kind {
            return Some(child);
        }
    }
    None
}

/// Wrap an expression with deferred calls in LIFO order.
///
/// Given a body expression and a list of deferred expressions (in order of appearance),
/// wraps the body in nested Try-finally blocks so defers execute in reverse order.
///
/// Example with defers [f, g, h] (f was deferred first, h last):
///
///   Input body: return 42
///   Output:
///     Try {
///       body: Try {
///         body: Try {
///           body: return 42,
///           finally: h()  // Runs FIRST (last defer)
///         },
///         finally: g()    // Runs SECOND
///       },
///       finally: f()      // Runs LAST (first defer)
///     }
///
/// This ensures LIFO (last-in-first-out) execution order as required by Go's defer semantics.
pub fn wrap_with_defers(body: Expr, defers: Vec<Expr>) -> Expr {
    if defers.is_empty() {
        return body;
    }

    let range = body.range.clone();

    // Build nested Try-finally for LIFO defer execution.
    //
    // With defers [f, g, h] (in order of appearance, f first, h last):
    // - f should run LAST (outermost finally)
    // - h should run FIRST (innermost finally)
    //
    // We reverse and fold to build:
    //   Try { body: Try { body: Try { body: BODY, finally: h }, finally: g }, finally: f }
    //
    // Execution: BODY -> h (first) -> g (second) -> f (last)
    // This matches Go's LIFO defer semantics.
    defers.into_iter().rev().fold(body, |inner_body, deferred| {
        WithLoc::new(
            Expr_::Try {
                body: Box::new(inner_body),
                catches: Vec::new(),
                finally: Some(Box::new(deferred)),
            },
            range.clone(),
        )
    })
}

// node_range is defined in exprs.rs and imported at the top

#[cfg(test)]
mod tests {
    use super::*;
    use brrr_repr::expr::{Range, Pos};

    fn dummy_range() -> Range {
        Range::new(
            Pos { file_id: 0, line: 1, col: 0 },
            Pos { file_id: 0, line: 1, col: 1 },
        )
    }

    fn make_expr(e: Expr_) -> Expr {
        WithLoc::new(e, dummy_range())
    }

    #[test]
    fn test_stmt_module_loads() {
        // Basic test to ensure module compiles
        assert!(true);
    }

    #[test]
    fn test_wrap_with_defers_empty() {
        // No defers - body unchanged
        let body = make_expr(Expr_::Lit(Literal::Int(42, brrr_repr::types::IntType::I64)));
        let result = wrap_with_defers(body.clone(), vec![]);

        // Should be the same as body
        assert!(matches!(result.value, Expr_::Lit(Literal::Int(42, _))));
    }

    #[test]
    fn test_wrap_with_defers_single() {
        // Single defer - body wrapped in one Try-finally
        let body = make_expr(Expr_::Lit(Literal::Int(42, brrr_repr::types::IntType::I64)));
        let defer_f = make_expr(Expr_::Lit(Literal::String("f".to_string())));

        let result = wrap_with_defers(body, vec![defer_f]);

        // Should be Try { body: 42, finally: "f" }
        match &result.value {
            Expr_::Try { body, catches, finally } => {
                assert!(catches.is_empty());
                assert!(finally.is_some());
                // Body should be the integer literal
                assert!(matches!(body.value, Expr_::Lit(Literal::Int(42, _))));
                // Finally should be the string
                assert!(matches!(finally.as_ref().unwrap().value, Expr_::Lit(Literal::String(_))));
            }
            _ => panic!("Expected Try expression, got {:?}", result.value),
        }
    }

    #[test]
    fn test_wrap_with_defers_lifo_order() {
        // Three defers [f, g, h] - should produce LIFO execution order
        // f deferred first (runs last), h deferred last (runs first)
        let body = make_expr(Expr_::Lit(Literal::Int(42, brrr_repr::types::IntType::I64)));
        let defer_f = make_expr(Expr_::Lit(Literal::String("f".to_string())));
        let defer_g = make_expr(Expr_::Lit(Literal::String("g".to_string())));
        let defer_h = make_expr(Expr_::Lit(Literal::String("h".to_string())));

        let result = wrap_with_defers(body, vec![defer_f, defer_g, defer_h]);

        // Expected structure:
        // Try { body: Try { body: Try { body: 42, finally: h }, finally: g }, finally: f }
        //
        // Execution order: 42 -> h -> g -> f (LIFO)

        // Outermost should be Try with finally = "f"
        match &result.value {
            Expr_::Try { body: outer_body, finally: outer_finally, .. } => {
                // Outermost finally should be "f" (runs LAST)
                match &outer_finally.as_ref().unwrap().value {
                    Expr_::Lit(Literal::String(s)) => assert_eq!(s, "f"),
                    _ => panic!("Expected string 'f'"),
                }

                // Middle layer
                match &outer_body.value {
                    Expr_::Try { body: middle_body, finally: middle_finally, .. } => {
                        // Middle finally should be "g"
                        match &middle_finally.as_ref().unwrap().value {
                            Expr_::Lit(Literal::String(s)) => assert_eq!(s, "g"),
                            _ => panic!("Expected string 'g'"),
                        }

                        // Innermost layer
                        match &middle_body.value {
                            Expr_::Try { body: inner_body, finally: inner_finally, .. } => {
                                // Innermost finally should be "h" (runs FIRST)
                                match &inner_finally.as_ref().unwrap().value {
                                    Expr_::Lit(Literal::String(s)) => assert_eq!(s, "h"),
                                    _ => panic!("Expected string 'h'"),
                                }

                                // Innermost body should be the original body (42)
                                assert!(matches!(inner_body.value, Expr_::Lit(Literal::Int(42, _))));
                            }
                            _ => panic!("Expected innermost Try"),
                        }
                    }
                    _ => panic!("Expected middle Try"),
                }
            }
            _ => panic!("Expected outermost Try"),
        }
    }
}
