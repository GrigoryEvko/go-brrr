//! Effect handler infrastructure
//!
//! Mirrors F* Effects.fsti effect handler types (lines 767-823):
//! - `OpSig` - Operation signature within an effect
//! - `EffectSig` - Effect signature (list of operations + purity)
//! - `ExtendedHandler` - Handler with depth and linearity annotations
//!
//! # Handler Semantics
//!
//! Handlers intercept effect operations and provide implementations.
//! Each handler clause specifies how to handle one operation, with access
//! to the delimited continuation representing the rest of the computation.
//!
//! ## Handler Depth
//!
//! - `Shallow`: Continuation invoked at most once, at tail position.
//!   More efficient - can use direct style without full CPS.
//! - `Deep`: Continuation can be invoked multiple times or stored.
//!   Requires full CPS transformation.
//!
//! ## Continuation Linearity
//!
//! - `OneShot`: Continuation must be used exactly once (linear).
//!   No need to copy the continuation stack.
//! - `MultiShot`: Continuation can be used zero or more times.
//!   Requires copying/cloning the continuation.

use serde::{Deserialize, Serialize};

use super::ops::EffectOp;
use crate::types::BrrrType;

// Re-export types from expr module for unified access
pub use crate::expr::{
    ContinuationLinearity, Continuation, EffectHandler, HandlerClause, HandlerDepth,
};

/// Type alias for linearity (matches F* naming)
pub type Linearity = ContinuationLinearity;

/// Operation signature within an effect.
///
/// Describes the type signature of a single effect operation,
/// including its parameters and result type.
///
/// Maps to F* Effects.fsti op_sig (lines 772-776):
/// ```fstar
/// noeq type op_sig = {
///   os_op     : effect_op;
///   os_params : list brrr_type;
///   os_result : brrr_type;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OpSig {
    /// The effect operation this signature describes
    pub op: EffectOp,
    /// Parameter types for the operation
    pub params: Vec<BrrrType>,
    /// Result type of the operation
    pub result: BrrrType,
}

impl OpSig {
    /// Create a new operation signature
    pub fn new(op: EffectOp, params: Vec<BrrrType>, result: BrrrType) -> Self {
        Self { op, params, result }
    }

    /// Create a nullary operation (no parameters)
    pub fn nullary(op: EffectOp, result: BrrrType) -> Self {
        Self::new(op, Vec::new(), result)
    }

    /// Create a unary operation (one parameter)
    pub fn unary(op: EffectOp, param: BrrrType, result: BrrrType) -> Self {
        Self::new(op, vec![param], result)
    }

    /// Create a binary operation (two parameters)
    pub fn binary(op: EffectOp, param1: BrrrType, param2: BrrrType, result: BrrrType) -> Self {
        Self::new(op, vec![param1, param2], result)
    }

    /// Number of parameters
    pub fn arity(&self) -> usize {
        self.params.len()
    }

    /// Check if this is a nullary operation
    pub fn is_nullary(&self) -> bool {
        self.params.is_empty()
    }
}

/// Effect signature - describes all operations in an effect.
///
/// An effect is a collection of operations, each with its own signature.
/// The `pure` flag indicates whether the effect represents pure computation
/// (e.g., the `Pure` or `Tot` effect in F*).
///
/// Maps to F* Effects.fsti effect_sig (lines 778-781):
/// ```fstar
/// noeq type effect_sig = {
///   es_ops    : list op_sig;
///   es_pure   : bool;
/// }
/// ```
///
/// # Examples
///
/// ```text
/// // Reader effect with single Ask operation
/// effect Reader[R] {
///   Ask: () -> R
/// }
///
/// // State effect with Get and Put operations
/// effect State[S] {
///   Get: () -> S
///   Put: S -> ()
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EffectSig {
    /// Operation signatures for this effect
    pub ops: Vec<OpSig>,
    /// Whether this is a pure effect (no actual operations)
    pub pure: bool,
}

impl EffectSig {
    /// Create a new effect signature
    pub fn new(ops: Vec<OpSig>, pure: bool) -> Self {
        Self { ops, pure }
    }

    /// Create a pure effect signature (no operations)
    pub fn pure_effect() -> Self {
        Self {
            ops: Vec::new(),
            pure: true,
        }
    }

    /// Create an impure effect signature with the given operations
    pub fn impure(ops: Vec<OpSig>) -> Self {
        Self { ops, pure: false }
    }

    /// Create an effect signature with a single operation
    pub fn single(op_sig: OpSig) -> Self {
        Self::impure(vec![op_sig])
    }

    /// Check if this is a pure effect
    pub fn is_pure(&self) -> bool {
        self.pure
    }

    /// Number of operations in this effect
    pub fn num_ops(&self) -> usize {
        self.ops.len()
    }

    /// Check if this effect has no operations
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Find an operation by its effect op
    pub fn find_op(&self, op: &EffectOp) -> Option<&OpSig> {
        self.ops.iter().find(|sig| &sig.op == op)
    }

    /// Check if this effect contains a specific operation
    pub fn has_op(&self, op: &EffectOp) -> bool {
        self.find_op(op).is_some()
    }

    /// Add an operation to this effect signature
    pub fn add_op(&mut self, op_sig: OpSig) {
        self.ops.push(op_sig);
        // Adding operations makes it impure
        self.pure = false;
    }

    /// Get all effect operations in this signature
    pub fn operations(&self) -> Vec<&EffectOp> {
        self.ops.iter().map(|sig| &sig.op).collect()
    }
}

impl Default for EffectSig {
    fn default() -> Self {
        Self::pure_effect()
    }
}

/// Extended handler with depth and linearity annotations.
///
/// Combines a basic effect handler with metadata about:
/// - Handler depth (shallow vs deep)
/// - Continuation linearity (one-shot vs multi-shot)
///
/// This determines the implementation strategy for the handler:
/// - Shallow + OneShot: Most efficient, direct style
/// - Shallow + MultiShot: Copy continuation on first use
/// - Deep + OneShot: CPS with linear continuation
/// - Deep + MultiShot: Full CPS with copyable continuation
///
/// Maps to F* Effects.fsti extended_handler (lines 818-822):
/// ```fstar
/// noeq type extended_handler = {
///   exh_handler  : effect_handler;
///   exh_depth    : handler_depth;
///   exh_linearity: linearity;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExtendedHandler {
    /// The underlying effect handler
    pub handler: EffectHandler,
    /// Handler depth (shallow or deep)
    pub depth: HandlerDepth,
    /// Continuation linearity (one-shot or multi-shot)
    pub linearity: Linearity,
}

impl ExtendedHandler {
    /// Create a new extended handler
    pub fn new(handler: EffectHandler, depth: HandlerDepth, linearity: Linearity) -> Self {
        Self {
            handler,
            depth,
            linearity,
        }
    }

    /// Create a shallow one-shot handler (most efficient)
    pub fn shallow_one_shot(handler: EffectHandler) -> Self {
        Self::new(handler, HandlerDepth::Shallow, Linearity::OneShot)
    }

    /// Create a shallow multi-shot handler
    pub fn shallow_multi_shot(handler: EffectHandler) -> Self {
        Self::new(handler, HandlerDepth::Shallow, Linearity::MultiShot)
    }

    /// Create a deep one-shot handler
    pub fn deep_one_shot(handler: EffectHandler) -> Self {
        Self::new(handler, HandlerDepth::Deep, Linearity::OneShot)
    }

    /// Create a deep multi-shot handler (most powerful, least efficient)
    pub fn deep_multi_shot(handler: EffectHandler) -> Self {
        Self::new(handler, HandlerDepth::Deep, Linearity::MultiShot)
    }

    /// Create from an existing handler, using its depth and default one-shot linearity
    pub fn from_handler(handler: EffectHandler) -> Self {
        let depth = handler.depth;
        Self::new(handler, depth, Linearity::OneShot)
    }

    /// Check if this is a shallow handler
    pub fn is_shallow(&self) -> bool {
        self.depth.is_shallow()
    }

    /// Check if this is a deep handler
    pub fn is_deep(&self) -> bool {
        self.depth.is_deep()
    }

    /// Check if continuation is one-shot (linear)
    pub fn is_one_shot(&self) -> bool {
        self.linearity.is_one_shot()
    }

    /// Check if continuation is multi-shot
    pub fn is_multi_shot(&self) -> bool {
        self.linearity.is_multi_shot()
    }

    /// Check if this is the most efficient handler configuration
    /// (shallow + one-shot)
    pub fn is_most_efficient(&self) -> bool {
        self.is_shallow() && self.is_one_shot()
    }

    /// Check if this is the most powerful handler configuration
    /// (deep + multi-shot)
    pub fn is_most_powerful(&self) -> bool {
        self.is_deep() && self.is_multi_shot()
    }

    /// Get the underlying handler clauses
    pub fn clauses(&self) -> &[HandlerClause] {
        &self.handler.clauses
    }

    /// Get all effect operations handled
    pub fn handled_effects(&self) -> Vec<EffectOp> {
        self.handler.handled_effects()
    }

    /// Find a clause by operation
    pub fn find_clause(&self, op: &EffectOp) -> Option<&HandlerClause> {
        self.handler.find_clause(op)
    }
}

impl Default for ExtendedHandler {
    fn default() -> Self {
        Self {
            handler: EffectHandler::default(),
            depth: HandlerDepth::Shallow,
            linearity: Linearity::OneShot,
        }
    }
}

impl From<EffectHandler> for ExtendedHandler {
    fn from(handler: EffectHandler) -> Self {
        Self::from_handler(handler)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::EffectOp;
    use crate::types::PrimKind;

    #[test]
    fn test_op_sig_constructors() {
        let nullary = OpSig::nullary(EffectOp::Random, BrrrType::Prim(PrimKind::Unit));
        assert!(nullary.is_nullary());
        assert_eq!(nullary.arity(), 0);

        let unary = OpSig::unary(
            EffectOp::ReadSimple,
            BrrrType::Prim(PrimKind::Unit),
            BrrrType::BOOL,
        );
        assert!(!unary.is_nullary());
        assert_eq!(unary.arity(), 1);

        let binary = OpSig::binary(
            EffectOp::WriteSimple,
            BrrrType::BOOL,
            BrrrType::BOOL,
            BrrrType::UNIT,
        );
        assert_eq!(binary.arity(), 2);
    }

    #[test]
    fn test_effect_sig_pure() {
        let pure = EffectSig::pure_effect();
        assert!(pure.is_pure());
        assert!(pure.is_empty());
        assert_eq!(pure.num_ops(), 0);
    }

    #[test]
    fn test_effect_sig_impure() {
        let read_sig = OpSig::nullary(EffectOp::ReadSimple, BrrrType::BOOL);
        let write_sig = OpSig::unary(EffectOp::WriteSimple, BrrrType::BOOL, BrrrType::UNIT);

        let effect = EffectSig::impure(vec![read_sig, write_sig]);
        assert!(!effect.is_pure());
        assert!(!effect.is_empty());
        assert_eq!(effect.num_ops(), 2);
        assert!(effect.has_op(&EffectOp::ReadSimple));
        assert!(effect.has_op(&EffectOp::WriteSimple));
        assert!(!effect.has_op(&EffectOp::Io));
    }

    #[test]
    fn test_effect_sig_find_op() {
        let read_sig = OpSig::nullary(EffectOp::ReadSimple, BrrrType::BOOL);
        let effect = EffectSig::single(read_sig.clone());

        let found = effect.find_op(&EffectOp::ReadSimple);
        assert!(found.is_some());
        assert_eq!(found.unwrap().result, BrrrType::BOOL);

        assert!(effect.find_op(&EffectOp::WriteSimple).is_none());
    }

    #[test]
    fn test_effect_sig_add_op() {
        let mut effect = EffectSig::pure_effect();
        assert!(effect.is_pure());

        let io_sig = OpSig::nullary(EffectOp::Io, BrrrType::UNIT);
        effect.add_op(io_sig);

        assert!(!effect.is_pure());
        assert_eq!(effect.num_ops(), 1);
    }

    #[test]
    fn test_extended_handler_shallow_one_shot() {
        let handler = EffectHandler::shallow(vec![]);
        let ext = ExtendedHandler::shallow_one_shot(handler);

        assert!(ext.is_shallow());
        assert!(ext.is_one_shot());
        assert!(ext.is_most_efficient());
        assert!(!ext.is_most_powerful());
    }

    #[test]
    fn test_extended_handler_deep_multi_shot() {
        let handler = EffectHandler::deep(vec![]);
        let ext = ExtendedHandler::deep_multi_shot(handler);

        assert!(ext.is_deep());
        assert!(ext.is_multi_shot());
        assert!(!ext.is_most_efficient());
        assert!(ext.is_most_powerful());
    }

    #[test]
    fn test_extended_handler_from_handler() {
        let shallow = EffectHandler::shallow(vec![]);
        let ext_shallow = ExtendedHandler::from_handler(shallow);
        assert!(ext_shallow.is_shallow());
        assert!(ext_shallow.is_one_shot()); // Default linearity

        let deep = EffectHandler::deep(vec![]);
        let ext_deep = ExtendedHandler::from_handler(deep);
        assert!(ext_deep.is_deep());
        assert!(ext_deep.is_one_shot()); // Default linearity
    }

    #[test]
    fn test_extended_handler_into() {
        let handler = EffectHandler::shallow(vec![]);
        let ext: ExtendedHandler = handler.into();
        assert!(ext.is_shallow());
    }

    #[test]
    fn test_extended_handler_handled_effects() {
        use lasso::Rodeo;

        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        let body = crate::expr::WithLoc::synthetic(crate::expr::Expr_::Hole);
        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);

        let handler = EffectHandler::shallow(vec![clause]);
        let ext = ExtendedHandler::shallow_one_shot(handler);

        let effects = ext.handled_effects();
        assert_eq!(effects.len(), 1);
        assert_eq!(effects[0], EffectOp::Io);
    }

    #[test]
    fn test_linearity_alias() {
        // Linearity should be an alias for ContinuationLinearity
        let one_shot: Linearity = ContinuationLinearity::OneShot;
        let multi_shot: Linearity = ContinuationLinearity::MultiShot;

        assert!(one_shot.is_one_shot());
        assert!(multi_shot.is_multi_shot());
    }
}
