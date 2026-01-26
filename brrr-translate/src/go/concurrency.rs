//! Go concurrency translation to Brrr effects and session types.
//!
//! Maps Go concurrency primitives to Brrr IR:
//! - `go f(x)` → `Spawn(Call(f, [x]))` with ESpawn effect
//! - `ch <- v` → `Perform(ESend, [ch, v])` (session effect)
//! - `<-ch` → `Perform(ERecv, [ch])` (session effect)
//! - `select {...}` → `Match` with session branching
//! - `sync.Mutex.Lock()` → `Perform(ELock, [mutex])`
//! - `sync.WaitGroup.Wait()` → `Perform(EJoin, [])`

use super::context::{ChannelDirection, ChannelInfo, GoTranslationContext};
use super::exprs::translate_expr;
use super::types::translate_type;
use crate::{missing_node, unsupported, TranslateResult, TranslationContext};
use brrr_repr::effects::EffectType;
use brrr_repr::expr::{Expr, Expr_, Literal, MatchArm, Pattern_, Range, Pos, WithLoc};
use brrr_repr::session::{SessionType, SessionVar};
use brrr_repr::{BrrrType, EffectOp};
use tree_sitter::Node;

/// Create a channel type with session type annotation.
pub fn create_channel_type(elem_type: BrrrType, direction: ChannelDirection) -> BrrrType {
    // Channel is represented as App(Named("Chan"), [elem_type])
    // with session type metadata
    let chan_name = lasso::Spur::default(); // Will be resolved by context
    BrrrType::App(
        Box::new(BrrrType::Named(chan_name)),
        vec![elem_type],
    )
}

/// Create a session type for a Go channel.
///
/// Go channels support bidirectional communication with the protocol:
/// ```text
/// Rec X. Branch {
///   send: Send<T, X>,
///   recv: Recv<T, X>,
///   close: End
/// }
/// ```
pub fn create_channel_session(elem_type: BrrrType, direction: ChannelDirection) -> SessionType {
    // Note: Labels use Spur::default() as placeholders - proper label interning
    // would require threading an interner through the translation context.
    let send_label = lasso::Spur::default();
    let recv_label = lasso::Spur::default();
    let close_label = lasso::Spur::default();
    let rec_var = SessionVar::new(0);

    match direction {
        ChannelDirection::Bidirectional => {
            // Full channel protocol: rec X. &{send: !T.X, recv: ?T.X, close: end}
            SessionType::Rec {
                var: rec_var,
                body: Box::new(SessionType::Branch(vec![
                    (send_label, SessionType::Send {
                        payload: elem_type.clone(),
                        continuation: Box::new(SessionType::Var(rec_var)),
                    }),
                    (recv_label, SessionType::Recv {
                        payload: elem_type,
                        continuation: Box::new(SessionType::Var(rec_var)),
                    }),
                    (close_label, SessionType::End),
                ])),
            }
        }
        ChannelDirection::SendOnly => {
            // Send-only channel: rec X. &{send: !T.X, close: end}
            SessionType::Rec {
                var: rec_var,
                body: Box::new(SessionType::Branch(vec![
                    (send_label, SessionType::Send {
                        payload: elem_type,
                        continuation: Box::new(SessionType::Var(rec_var)),
                    }),
                    (close_label, SessionType::End),
                ])),
            }
        }
        ChannelDirection::RecvOnly => {
            // Receive-only channel: rec X. &{recv: ?T.X}
            SessionType::Rec {
                var: rec_var,
                body: Box::new(SessionType::Branch(vec![
                    (recv_label, SessionType::Recv {
                        payload: elem_type,
                        continuation: Box::new(SessionType::Var(rec_var)),
                    }),
                ])),
            }
        }
    }
}

/// Translate a make(chan T) call to channel creation.
pub fn translate_make_chan<'src>(
    ctx: &mut GoTranslationContext<'src>,
    type_node: Node<'_>,
    size_node: Option<Node<'_>>,
) -> TranslateResult<Expr_> {
    // Extract channel element type
    let elem_type = if let Some(elem) = type_node.child_by_field_name("element") {
        translate_type(ctx, elem)?
    } else {
        BrrrType::UNKNOWN
    };

    // Determine buffer size
    let buffer_size = if let Some(size) = size_node {
        // Buffered channel
        Some(extract_buffer_size(ctx, size))
    } else {
        // Unbuffered channel
        Some(0)
    };

    // Determine direction from channel type
    let direction = if type_node.kind() == "channel_type" {
        let mut cursor = type_node.walk();
        let mut has_recv = false;
        let mut has_send = false;

        for child in type_node.children(&mut cursor) {
            match child.kind() {
                "<-" => has_recv = true,
                "chan" => has_send = true,
                _ => {}
            }
        }

        // Check the order: "<-chan" is recv-only, "chan<-" is send-only
        let text = ctx.node_text(type_node);
        if text.starts_with("<-") {
            ChannelDirection::RecvOnly
        } else if text.contains("<-") && !text.starts_with("chan<-") {
            ChannelDirection::Bidirectional
        } else if text.starts_with("chan<-") {
            ChannelDirection::SendOnly
        } else {
            ChannelDirection::Bidirectional
        }
    } else {
        ChannelDirection::Bidirectional
    };

    // Create channel effect with placeholder channel ID (0)
    // In a real implementation, channel IDs would be allocated and tracked
    let chan_id = 0;
    let buf_size = buffer_size.unwrap_or(0) as u32;
    Ok(Expr_::Perform(
        EffectOp::ChanCreate(chan_id, EffectType::Unit, buf_size),
        vec![
            // Element type as a type literal (placeholder)
            WithLoc::new(
                Expr_::Lit(Literal::Unit),
                dummy_range(),
            ),
        ],
    ))
}

/// Extract buffer size from an expression.
fn extract_buffer_size<'src>(
    ctx: &GoTranslationContext<'src>,
    node: Node<'_>,
) -> usize {
    let text = ctx.node_text(node);
    text.parse().unwrap_or(0)
}

/// Translate a channel send operation.
pub fn translate_channel_send<'src>(
    ctx: &mut GoTranslationContext<'src>,
    channel: Node<'_>,
    value: Node<'_>,
) -> TranslateResult<Expr_> {
    let channel_expr = translate_expr(ctx, channel)?;
    let value_expr = translate_expr(ctx, value)?;

    // Placeholder channel ID (0) - real implementation would track channel IDs
    Ok(Expr_::Perform(EffectOp::Send(0, EffectType::Unit), vec![channel_expr, value_expr]))
}

/// Translate a channel receive operation.
pub fn translate_channel_recv<'src>(
    ctx: &mut GoTranslationContext<'src>,
    channel: Node<'_>,
) -> TranslateResult<Expr_> {
    let channel_expr = translate_expr(ctx, channel)?;

    // Placeholder channel ID (0) - real implementation would track channel IDs
    Ok(Expr_::Perform(EffectOp::Recv(0, EffectType::Unit), vec![channel_expr]))
}

/// Translate a channel close operation.
pub fn translate_channel_close<'src>(
    ctx: &mut GoTranslationContext<'src>,
    channel: Node<'_>,
) -> TranslateResult<Expr_> {
    let channel_expr = translate_expr(ctx, channel)?;

    // Placeholder channel ID (0) - real implementation would track channel IDs
    Ok(Expr_::Perform(EffectOp::ChanClose(0), vec![channel_expr]))
}

/// Translate a go statement (spawn goroutine).
pub fn translate_go_spawn<'src>(
    ctx: &mut GoTranslationContext<'src>,
    call: Node<'_>,
) -> TranslateResult<Expr_> {
    let call_expr = translate_expr(ctx, call)?;

    // Spawn wraps the call expression
    Ok(Expr_::Spawn(Box::new(call_expr)))
}

/// Translate a select statement to branch effect with match.
pub fn translate_select<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<Expr_> {
    let mut arms = Vec::new();
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "communication_case" => {
                if let Ok(arm) = translate_comm_case(ctx, child) {
                    arms.push(arm);
                }
            }
            "default_case" => {
                if let Ok(arm) = translate_default_case(ctx, child) {
                    arms.push(arm);
                }
            }
            _ => {}
        }
    }

    // Select is represented as a branch effect followed by match
    let branch = Expr_::Perform(EffectOp::Branch(0, Vec::new()), Vec::new());
    Ok(Expr_::Match(Box::new(WithLoc::new(branch, node_range(node))), arms))
}

/// Translate a communication case in a select.
fn translate_comm_case<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<MatchArm> {
    let range = node_range(node);

    // Get the communication operation
    let comm = find_child_by_kind(node, "send_statement")
        .or_else(|| find_child_by_kind(node, "receive_statement"));

    let (pattern, comm_effect) = if let Some(comm_node) = comm {
        if comm_node.kind() == "send_statement" {
            // Send case
            let channel = comm_node.child_by_field_name("channel")
                .ok_or_else(|| missing_node("channel", comm_node))?;
            let value = comm_node.child_by_field_name("value")
                .ok_or_else(|| missing_node("value", comm_node))?;

            let channel_expr = translate_expr(ctx, channel)?;
            let value_expr = translate_expr(ctx, value)?;

            let effect = Expr_::Perform(EffectOp::Send(0, EffectType::Unit), vec![channel_expr, value_expr]);
            (WithLoc::new(Pattern_::Wild, range.clone()), Some(effect))
        } else {
            // Receive case
            // May have variable binding: x := <-ch or x, ok := <-ch
            let recv_expr = find_child_by_kind(comm_node, "receive_expression")
                .or_else(|| comm_node.child(0));

            if let Some(recv) = recv_expr {
                let channel = recv.child(1)
                    .ok_or_else(|| missing_node("channel", recv))?;
                let channel_expr = translate_expr(ctx, channel)?;

                let effect = Expr_::Perform(EffectOp::Recv(0, EffectType::Unit), vec![channel_expr]);
                (WithLoc::new(Pattern_::Wild, range.clone()), Some(effect))
            } else {
                (WithLoc::new(Pattern_::Wild, range.clone()), None)
            }
        }
    } else {
        (WithLoc::new(Pattern_::Wild, range.clone()), None)
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
            if let Ok(stmt) = super::stmts::translate_stmt(ctx, child) {
                body_stmts.push(stmt);
            }
        }
    }

    // Prepend communication effect to body
    let body = if let Some(effect) = comm_effect {
        let effect_expr = WithLoc::new(effect, range.clone());
        if body_stmts.is_empty() {
            effect_expr
        } else {
            let mut all_stmts = vec![effect_expr];
            all_stmts.extend(body_stmts);
            WithLoc::new(Expr_::Block(all_stmts), range.clone())
        }
    } else if body_stmts.is_empty() {
        WithLoc::new(Expr_::Lit(Literal::Unit), range.clone())
    } else if body_stmts.len() == 1 {
        body_stmts.remove(0)
    } else {
        WithLoc::new(Expr_::Block(body_stmts), range)
    };

    Ok(MatchArm {
        range: range.clone(),
        pattern,
        guard: None,
        body,
    })
}

/// Translate a default case in a select.
fn translate_default_case<'src>(
    ctx: &mut GoTranslationContext<'src>,
    node: Node<'_>,
) -> TranslateResult<MatchArm> {
    let range = node_range(node);

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
            if let Ok(stmt) = super::stmts::translate_stmt(ctx, child) {
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
        range: range.clone(),
        pattern: WithLoc::new(Pattern_::Wild, range),
        guard: None,
        body,
    })
}

/// Translate sync.Mutex.Lock() call.
pub fn translate_mutex_lock<'src>(
    ctx: &mut GoTranslationContext<'src>,
    mutex: Node<'_>,
) -> TranslateResult<Expr_> {
    let mutex_expr = translate_expr(ctx, mutex)?;
    Ok(Expr_::Perform(EffectOp::Lock(0), vec![mutex_expr]))
}

/// Translate sync.Mutex.Unlock() call.
pub fn translate_mutex_unlock<'src>(
    ctx: &mut GoTranslationContext<'src>,
    mutex: Node<'_>,
) -> TranslateResult<Expr_> {
    let mutex_expr = translate_expr(ctx, mutex)?;
    Ok(Expr_::Perform(EffectOp::Unlock(0), vec![mutex_expr]))
}

/// Translate sync.WaitGroup.Wait() call.
pub fn translate_waitgroup_wait<'src>(
    ctx: &mut GoTranslationContext<'src>,
    wg: Node<'_>,
) -> TranslateResult<Expr_> {
    let wg_expr = translate_expr(ctx, wg)?;
    Ok(Expr_::Perform(EffectOp::Join, vec![wg_expr]))
}

/// Translate sync.WaitGroup.Add(n) call.
pub fn translate_waitgroup_add<'src>(
    ctx: &mut GoTranslationContext<'src>,
    wg: Node<'_>,
    count: Node<'_>,
) -> TranslateResult<Expr_> {
    let wg_expr = translate_expr(ctx, wg)?;
    let count_expr = translate_expr(ctx, count)?;
    // WaitGroup.Add signals spawning N tasks - use Spawn effect
    Ok(Expr_::Perform(EffectOp::Spawn, vec![wg_expr, count_expr]))
}

/// Translate sync.WaitGroup.Done() call.
pub fn translate_waitgroup_done<'src>(
    ctx: &mut GoTranslationContext<'src>,
    wg: Node<'_>,
) -> TranslateResult<Expr_> {
    let wg_expr = translate_expr(ctx, wg)?;
    // Done is equivalent to Add(-1), but we use a dedicated effect
    Ok(Expr_::Perform(EffectOp::Join, vec![wg_expr]))
}

/// Check if a call is a sync primitive and translate accordingly.
pub fn try_translate_sync_call<'src>(
    ctx: &mut GoTranslationContext<'src>,
    receiver: Node<'_>,
    method: &str,
    args: &[Node<'_>],
) -> Option<TranslateResult<Expr_>> {
    match method {
        "Lock" => Some(translate_mutex_lock(ctx, receiver)),
        "Unlock" => Some(translate_mutex_unlock(ctx, receiver)),
        "Wait" => Some(translate_waitgroup_wait(ctx, receiver)),
        "Add" if !args.is_empty() => Some(translate_waitgroup_add(ctx, receiver, args[0])),
        "Done" => Some(translate_waitgroup_done(ctx, receiver)),
        _ => None,
    }
}

/// Check if a call is a channel builtin and translate accordingly.
pub fn try_translate_channel_builtin<'src>(
    ctx: &mut GoTranslationContext<'src>,
    func_name: &str,
    args: &[Node<'_>],
) -> Option<TranslateResult<Expr_>> {
    match func_name {
        "close" if !args.is_empty() => {
            Some(translate_channel_close(ctx, args[0]))
        }
        "make" if !args.is_empty() => {
            let type_node = args[0];
            if type_node.kind() == "channel_type" {
                let size_node = args.get(1).copied();
                Some(translate_make_chan(ctx, type_node, size_node))
            } else {
                None
            }
        }
        _ => None,
    }
}

// Helper function to get node range
fn node_range(node: Node<'_>) -> Range {
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

fn dummy_range() -> Range {
    Range::new(
        Pos { file_id: 0, line: 0, col: 0 },
        Pos { file_id: 0, line: 0, col: 0 },
    )
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

#[cfg(test)]
mod tests {
    use super::*;
    use brrr_repr::types::{IntType, NumericType};

    #[test]
    fn test_channel_session_bidirectional() {
        let int64 = BrrrType::Numeric(NumericType::Int(IntType::I64));
        let session = create_channel_session(int64, ChannelDirection::Bidirectional);
        // Verify it creates a recursive session type
        match session {
            SessionType::Rec { var: _, body } => {
                match body.as_ref() {
                    SessionType::Branch(branches) => {
                        assert_eq!(branches.len(), 3);
                    }
                    _ => panic!("Expected Branch"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_channel_session_send_only() {
        let session = create_channel_session(BrrrType::STRING, ChannelDirection::SendOnly);
        match session {
            SessionType::Rec { body, .. } => {
                match body.as_ref() {
                    SessionType::Branch(branches) => {
                        assert_eq!(branches.len(), 2); // send and close only
                    }
                    _ => panic!("Expected Branch"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }
}
