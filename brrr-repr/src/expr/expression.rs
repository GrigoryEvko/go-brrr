//! Expression types (51 variants)
//!
//! Mirrors F* Expressions.fsti expr and expr'.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::literal::Literal;
use super::location::{Range, WithLoc};
use super::operators::{BinaryOp, UnaryOp};
use super::pattern::Pattern;
use crate::boundary::{NodeId, NodeIdCounter};
use crate::effects::{EffectOp, EffectRow};
use crate::types::{BrrrType, TypeName};

/// Expression with source location
pub type Expr = WithLoc<Expr_>;

/// Variable identifier
pub type VarId = Spur;

/// Label for loops/control flow
pub type Label = Spur;

/// Expression underlying type - 51 variants
/// Maps to F* Expressions.fsti expr'
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Expr_ {
    // === Literals and Variables ===
    /// Literal value `42`, `"hello"`, `true`
    Lit(Literal),
    /// Variable reference `x`
    Var(VarId),
    /// Global/qualified reference `module::func`
    Global(Spur),

    // === Operations ===
    /// Unary operation `-x`, `!x`, `&x`, `*x`
    Unary(UnaryOp, Box<Expr>),
    /// Binary operation `x + y`, `a && b`
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    /// Function call `f(x, y)`
    Call(Box<Expr>, Vec<Expr>),
    /// Method call `obj.method(args)`
    MethodCall(Box<Expr>, Spur, Vec<Expr>),

    // === Data Construction ===
    /// Tuple `(a, b, c)`
    Tuple(Vec<Expr>),
    /// Array `[1, 2, 3]`
    Array(Vec<Expr>),
    /// Struct construction `Point { x: 1, y: 2 }`
    Struct {
        name: TypeName,
        fields: Vec<(Spur, Expr)>,
    },
    /// Enum variant `Some(x)`, `Color::Red`
    Variant {
        type_name: TypeName,
        variant: Spur,
        fields: Vec<Expr>,
    },

    // === Data Access ===
    /// Field access `obj.field`
    Field(Box<Expr>, Spur),
    /// Index access `arr[i]`
    Index(Box<Expr>, Box<Expr>),
    /// Tuple projection `tuple.0`
    TupleProj(Box<Expr>, u32),

    // === Control Flow ===
    /// If-then-else `if c then t else f`
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// Pattern match `match e { ... }`
    Match(Box<Expr>, Vec<MatchArm>),
    /// Infinite loop `loop { ... }`
    Loop {
        label: Option<Label>,
        body: Box<Expr>,
    },
    /// While loop `while c { ... }`
    While {
        label: Option<Label>,
        cond: Box<Expr>,
        body: Box<Expr>,
    },
    /// For loop `for x in iter { ... }`
    For {
        label: Option<Label>,
        var: VarId,
        iter: Box<Expr>,
        body: Box<Expr>,
    },
    /// Break `break`, `break 'label`, `break value`
    Break {
        label: Option<Label>,
        value: Option<Box<Expr>>,
    },
    /// Continue `continue`, `continue 'label`
    Continue { label: Option<Label> },
    /// Return `return`, `return value`
    Return(Option<Box<Expr>>),
    /// Goto (Go-specific) - requires CFG lowering in analysis
    /// Note: This is an unconditional jump to a labeled statement.
    /// Unlike break/continue which exit/continue loops, goto can jump
    /// forward or backward to any label in the same function.
    Goto { label: Label },
    /// Labeled statement wrapper - attaches a label to any statement
    /// Used for goto targets and labeled break/continue
    Labeled { label: Label, body: Box<Expr> },

    // === Bindings ===
    /// Let binding `let p = e₁ in e₂`
    Let {
        pattern: Pattern,
        ty: Option<BrrrType>,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    /// Mutable let `let mut x = e₁ in e₂`
    LetMut {
        var: VarId,
        ty: Option<BrrrType>,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    /// Assignment `x = e`
    Assign(Box<Expr>, Box<Expr>),

    // === Functions ===
    /// Lambda `λ(x: T). e`
    Lambda {
        params: Vec<(VarId, BrrrType)>,
        body: Box<Expr>,
    },
    /// Closure with captured vars
    Closure {
        params: Vec<(VarId, BrrrType)>,
        captures: Vec<VarId>,
        body: Box<Expr>,
    },

    // === Memory Operations ===
    /// Box allocation `Box::new(e)`
    Box(Box<Expr>),
    /// Dereference `*e`
    Deref(Box<Expr>),
    /// Borrow `&e`
    Borrow(Box<Expr>),
    /// Mutable borrow `&mut e`
    BorrowMut(Box<Expr>),
    /// Move `move(e)`
    Move(Box<Expr>),
    /// Drop `drop(e)`
    Drop(Box<Expr>),

    // === Exception Handling ===
    /// Throw `throw e`
    Throw(Box<Expr>),
    /// Try-catch-finally
    Try {
        body: Box<Expr>,
        catches: Vec<CatchArm>,
        finally: Option<Box<Expr>>,
    },

    // === Async/Concurrency ===
    /// Await `e.await`
    Await(Box<Expr>),
    /// Yield `yield e`
    Yield(Box<Expr>),
    /// Async block `async { e }`
    Async(Box<Expr>),
    /// Spawn `spawn { e }`
    Spawn(Box<Expr>),

    // === Effect Operations ===
    /// Effect handler
    Handle(Box<Expr>, Box<EffectHandler>),
    /// Perform effect `perform Op(args)`
    Perform(EffectOp, Vec<Expr>),
    /// Resume continuation `resume k with v`
    Resume { var: VarId, value: Box<Expr> },

    // === Delimited Continuations ===
    /// Reset `reset<l> { e }`
    Reset { label: Label, body: Box<Expr> },
    /// Shift `shift<l> k. e`
    Shift {
        label: Label,
        var: VarId,
        body: Box<Expr>,
    },

    // === Type Operations ===
    /// Type cast `e as T`
    As(Box<Expr>, BrrrType),
    /// Type test `e is T`
    Is(Box<Expr>, BrrrType),
    /// Size of type `sizeof(T)`
    Sizeof(BrrrType),
    /// Alignment of type `alignof(T)`
    Alignof(BrrrType),

    // === Blocks ===
    /// Block expression `{ e₁; e₂; ... }`
    Block(Vec<Expr>),
    /// Sequence `e₁; e₂`
    Seq(Box<Expr>, Box<Expr>),
    /// Unsafe block `unsafe { e }`
    Unsafe(Box<Expr>),

    // === Special ===
    /// Hole (unfinished code) `_`
    Hole,
    /// Error node (for error recovery)
    Error(Spur),

    // === Gradual Typing ===
    /// Runtime type cast for gradual typing
    /// Inserted during cast elaboration when types involve `?` (dynamic)
    GradualCast {
        /// The expression being cast
        expr: Box<Expr>,
        /// Source gradual type
        from: crate::gradual::GradualType,
        /// Target gradual type
        to: crate::gradual::GradualType,
        /// Kind of cast (upcast, downcast, function cast)
        kind: crate::gradual::elaborate::CastKind,
        /// Blame label for runtime errors
        blame: crate::gradual::elaborate::BlameLabel,
    },
}

impl Expr_ {
    /// Get the discriminant for binary encoding
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::Lit(_) => 0,
            Self::Var(_) => 1,
            Self::Global(_) => 2,
            Self::Unary(_, _) => 3,
            Self::Binary(_, _, _) => 4,
            Self::Call(_, _) => 5,
            Self::MethodCall(_, _, _) => 6,
            Self::Tuple(_) => 7,
            Self::Array(_) => 8,
            Self::Struct { .. } => 9,
            Self::Variant { .. } => 10,
            Self::Field(_, _) => 11,
            Self::Index(_, _) => 12,
            Self::TupleProj(_, _) => 13,
            Self::If(_, _, _) => 14,
            Self::Match(_, _) => 15,
            Self::Loop { .. } => 16,
            Self::While { .. } => 17,
            Self::For { .. } => 18,
            Self::Break { .. } => 19,
            Self::Continue { .. } => 20,
            Self::Return(_) => 21,
            Self::Let { .. } => 22,
            Self::LetMut { .. } => 23,
            Self::Assign(_, _) => 24,
            Self::Lambda { .. } => 25,
            Self::Closure { .. } => 26,
            Self::Box(_) => 27,
            Self::Deref(_) => 28,
            Self::Borrow(_) => 29,
            Self::BorrowMut(_) => 30,
            Self::Move(_) => 31,
            Self::Drop(_) => 32,
            Self::Throw(_) => 33,
            Self::Try { .. } => 34,
            Self::Await(_) => 35,
            Self::Yield(_) => 36,
            Self::Async(_) => 37,
            Self::Spawn(_) => 38,
            Self::Handle(_, _) => 39,
            Self::Perform(_, _) => 40,
            Self::Resume { .. } => 41,
            Self::Reset { .. } => 42,
            Self::Shift { .. } => 43,
            Self::As(_, _) => 44,
            Self::Is(_, _) => 45,
            Self::Sizeof(_) => 46,
            Self::Alignof(_) => 47,
            Self::Block(_) => 48,
            Self::Seq(_, _) => 49,
            Self::Unsafe(_) => 50,
            Self::Hole => 51,
            Self::Error(_) => 52,
            Self::GradualCast { .. } => 53,
            Self::Goto { .. } => 54,
            Self::Labeled { .. } => 55,
        }
    }

    /// Is this a leaf expression (no sub-expressions)?
    pub const fn is_leaf(&self) -> bool {
        matches!(
            self,
            Self::Lit(_)
                | Self::Var(_)
                | Self::Global(_)
                | Self::Break { value: None, .. }
                | Self::Continue { .. }
                | Self::Return(None)
                | Self::Goto { .. }
                | Self::Sizeof(_)
                | Self::Alignof(_)
                | Self::Hole
                | Self::Error(_)
        )
    }

    /// Is this a control flow expression?
    pub const fn is_control_flow(&self) -> bool {
        matches!(
            self,
            Self::If(_, _, _)
                | Self::Match(_, _)
                | Self::Loop { .. }
                | Self::While { .. }
                | Self::For { .. }
                | Self::Break { .. }
                | Self::Continue { .. }
                | Self::Return(_)
                | Self::Goto { .. }
                | Self::Labeled { .. }
                | Self::Throw(_)
                | Self::Try { .. }
        )
    }
}

impl Default for Expr_ {
    fn default() -> Self {
        Self::Lit(Literal::Unit)
    }
}

/// Match arm in a match expression
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MatchArm {
    /// Source range
    pub range: Range,
    /// Pattern to match
    pub pattern: Pattern,
    /// Optional guard `if cond`
    pub guard: Option<Expr>,
    /// Body expression
    pub body: Expr,
}

impl MatchArm {
    /// Create a new match arm
    pub fn new(pattern: Pattern, body: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            pattern,
            guard: None,
            body,
        }
    }

    /// Create a match arm with guard
    pub fn with_guard(pattern: Pattern, guard: Expr, body: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            pattern,
            guard: Some(guard),
            body,
        }
    }
}

/// Catch arm in a try expression
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CatchArm {
    /// Source range
    pub range: Range,
    /// Pattern to match exception
    pub pattern: Pattern,
    /// Exception type
    pub exception_type: BrrrType,
    /// Handler body
    pub body: Expr,
}

impl CatchArm {
    /// Create a new catch arm
    pub fn new(pattern: Pattern, exception_type: BrrrType, body: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            pattern,
            exception_type,
            body,
        }
    }
}

/// Handler depth: shallow handlers invoke continuation at most once
/// at tail position; deep handlers can invoke multiple times.
///
/// Maps to F* Effects.fsti handler_depth (lines 614-616):
/// ```fstar
/// type handler_depth = | Shallow | Deep
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum HandlerDepth {
    /// Shallow handler: continuation invoked at most once, at tail position.
    /// More efficient - can use direct style without CPS.
    #[default]
    Shallow,
    /// Deep handler: continuation can be invoked multiple times.
    /// Requires full CPS transformation.
    Deep,
}

impl HandlerDepth {
    /// Returns true if this is a shallow handler
    pub const fn is_shallow(&self) -> bool {
        matches!(self, Self::Shallow)
    }

    /// Returns true if this is a deep handler
    pub const fn is_deep(&self) -> bool {
        matches!(self, Self::Deep)
    }
}

/// Continuation linearity: whether a continuation can be used once or many times.
///
/// Maps to F* Effects.fsti continuation_linearity (lines 572-574):
/// ```fstar
/// type continuation_linearity = | OneShot | MultiShot
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum ContinuationLinearity {
    /// Continuation must be used exactly once (linear).
    /// More efficient - no need to copy the continuation.
    #[default]
    OneShot,
    /// Continuation can be used zero or more times (unrestricted).
    /// Requires copying/cloning the continuation.
    MultiShot,
}

impl ContinuationLinearity {
    /// Returns true if continuation is one-shot (linear)
    pub const fn is_one_shot(&self) -> bool {
        matches!(self, Self::OneShot)
    }

    /// Returns true if continuation is multi-shot
    pub const fn is_multi_shot(&self) -> bool {
        matches!(self, Self::MultiShot)
    }
}

/// A delimited continuation captured by an effect handler.
///
/// Represents the computation up to the nearest enclosing handler.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Continuation {
    /// Variable binding for the continuation
    pub var: VarId,
    /// Linearity constraint
    pub linearity: ContinuationLinearity,
    /// Expected argument type (optional, for type checking)
    pub arg_type: Option<crate::types::BrrrType>,
    /// Expected result type (optional, for type checking)
    pub result_type: Option<crate::types::BrrrType>,
}

impl Continuation {
    /// Create a new one-shot continuation
    pub fn one_shot(var: VarId) -> Self {
        Self {
            var,
            linearity: ContinuationLinearity::OneShot,
            arg_type: None,
            result_type: None,
        }
    }

    /// Create a new multi-shot continuation
    pub fn multi_shot(var: VarId) -> Self {
        Self {
            var,
            linearity: ContinuationLinearity::MultiShot,
            arg_type: None,
            result_type: None,
        }
    }

    /// Create with explicit linearity
    pub fn with_linearity(var: VarId, linearity: ContinuationLinearity) -> Self {
        Self {
            var,
            linearity,
            arg_type: None,
            result_type: None,
        }
    }
}

/// Effect handler with clauses for effect operations.
///
/// Maps to F* Effects.fsti effect_handler (lines 596-611):
/// ```fstar
/// noeq type effect_handler = {
///   eh_clauses     : list handler_clause;
///   eh_return      : option (var_id & expr);
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EffectHandler {
    /// Handler clauses for each effect operation
    pub clauses: Vec<HandlerClause>,
    /// Return clause (for normal completion): `return x -> body`
    pub return_clause: Option<(VarId, Expr)>,
    /// Handler depth (shallow vs deep)
    pub depth: HandlerDepth,
}

impl EffectHandler {
    /// Create a new shallow handler with no return clause
    pub fn shallow(clauses: Vec<HandlerClause>) -> Self {
        Self {
            clauses,
            return_clause: None,
            depth: HandlerDepth::Shallow,
        }
    }

    /// Create a new deep handler with no return clause
    pub fn deep(clauses: Vec<HandlerClause>) -> Self {
        Self {
            clauses,
            return_clause: None,
            depth: HandlerDepth::Deep,
        }
    }

    /// Add a return clause
    pub fn with_return(mut self, var: VarId, body: Expr) -> Self {
        self.return_clause = Some((var, body));
        self
    }

    /// Get all effect operations handled by this handler
    pub fn handled_effects(&self) -> Vec<EffectOp> {
        self.clauses.iter().map(|c| c.op.clone()).collect()
    }

    /// Check if this handler has a return clause
    pub const fn has_return_clause(&self) -> bool {
        self.return_clause.is_some()
    }

    /// Check if this is a shallow handler
    pub const fn is_shallow(&self) -> bool {
        self.depth.is_shallow()
    }

    /// Check if this is a deep handler
    pub const fn is_deep(&self) -> bool {
        self.depth.is_deep()
    }

    /// Find the clause handling a specific effect operation
    pub fn find_clause(&self, op: &EffectOp) -> Option<&HandlerClause> {
        self.clauses.iter().find(|c| &c.op == op)
    }
}

impl Default for EffectHandler {
    fn default() -> Self {
        Self {
            clauses: Vec::new(),
            return_clause: None,
            depth: HandlerDepth::Shallow,
        }
    }
}

/// Handler clause for a specific effect operation.
///
/// Maps to F* Effects.fsti handler_clause (lines 596-602):
/// ```fstar
/// noeq type handler_clause = {
///   hc_op         : effect_op;
///   hc_params     : list var_id;
///   hc_cont_var   : var_id;
///   hc_body       : expr
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct HandlerClause {
    /// Effect operation being handled
    pub op: EffectOp,
    /// Parameter bindings for operation arguments
    pub params: Vec<VarId>,
    /// Continuation variable (k in `resume k v`)
    pub continuation: VarId,
    /// Linearity of the continuation
    pub continuation_linearity: ContinuationLinearity,
    /// Handler body expression
    pub body: Expr,
}

impl HandlerClause {
    /// Create a new handler clause with one-shot continuation
    pub fn new(op: EffectOp, params: Vec<VarId>, continuation: VarId, body: Expr) -> Self {
        Self {
            op,
            params,
            continuation,
            continuation_linearity: ContinuationLinearity::OneShot,
            body,
        }
    }

    /// Create a handler clause with multi-shot continuation
    pub fn multi_shot(op: EffectOp, params: Vec<VarId>, continuation: VarId, body: Expr) -> Self {
        Self {
            op,
            params,
            continuation,
            continuation_linearity: ContinuationLinearity::MultiShot,
            body,
        }
    }

    /// Get the continuation as a Continuation struct
    pub fn get_continuation(&self) -> Continuation {
        Continuation::with_linearity(self.continuation, self.continuation_linearity)
    }
}

/// Annotated expression with type/effect inference results.
///
/// Maps to F* Expressions.fsti annotated_expr (lines 318-324):
/// ```fstar
/// noeq type annotated_expr = {
///   node    : node_id;       (* Unique node ID for CPG *)
///   span    : span;
///   ty      : option brrr_type;
///   effects : option effect_row;
///   expr    : expr
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnnotatedExpr {
    /// Unique node ID for CPG (Code Property Graph)
    pub node: NodeId,
    /// The expression
    pub expr: Expr,
    /// Inferred type
    pub ty: Option<BrrrType>,
    /// Inferred effects
    pub effects: Option<EffectRow>,
}

impl AnnotatedExpr {
    /// Create an unannotated expression with unknown node ID.
    pub fn unannotated(expr: Expr) -> Self {
        Self {
            node: NodeId::UNKNOWN,
            expr,
            ty: None,
            effects: None,
        }
    }

    /// Create a fully annotated expression with unknown node ID.
    pub fn annotated(expr: Expr, ty: BrrrType, effects: EffectRow) -> Self {
        Self {
            node: NodeId::UNKNOWN,
            expr,
            ty: Some(ty),
            effects: Some(effects),
        }
    }

    /// Create an expression with a specific node ID.
    ///
    /// Use this when you have a pre-allocated node ID.
    pub fn with_node(expr: Expr, node: NodeId) -> Self {
        Self {
            node,
            expr,
            ty: None,
            effects: None,
        }
    }

    /// Create an expression with a fresh node ID from the counter.
    ///
    /// Use this during AST construction to generate unique node IDs.
    pub fn fresh_node(expr: Expr, counter: &NodeIdCounter) -> Self {
        Self {
            node: counter.fresh(),
            expr,
            ty: None,
            effects: None,
        }
    }

    /// Create a fully annotated expression with a specific node ID.
    pub fn with_node_annotated(
        expr: Expr,
        node: NodeId,
        ty: BrrrType,
        effects: EffectRow,
    ) -> Self {
        Self {
            node,
            expr,
            ty: Some(ty),
            effects: Some(effects),
        }
    }

    /// Create a fully annotated expression with a fresh node ID.
    pub fn fresh_node_annotated(
        expr: Expr,
        counter: &NodeIdCounter,
        ty: BrrrType,
        effects: EffectRow,
    ) -> Self {
        Self {
            node: counter.fresh(),
            expr,
            ty: Some(ty),
            effects: Some(effects),
        }
    }

    /// Get the node ID.
    #[must_use]
    pub const fn node_id(&self) -> NodeId {
        self.node
    }

    /// Check if this expression has a valid (non-unknown) node ID.
    #[must_use]
    pub const fn has_node_id(&self) -> bool {
        self.node.0 != NodeId::UNKNOWN.0
    }

    /// Set the node ID, returning self for chaining.
    pub fn set_node(mut self, node: NodeId) -> Self {
        self.node = node;
        self
    }

    /// Set the type annotation, returning self for chaining.
    pub fn set_type(mut self, ty: BrrrType) -> Self {
        self.ty = Some(ty);
        self
    }

    /// Set the effects annotation, returning self for chaining.
    pub fn set_effects(mut self, effects: EffectRow) -> Self {
        self.effects = Some(effects);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_discriminants() {
        assert_eq!(Expr_::Lit(Literal::Unit).discriminant(), 0);
        assert_eq!(Expr_::Hole.discriminant(), 51);
    }

    #[test]
    fn test_expr_is_leaf() {
        assert!(Expr_::Lit(Literal::i32(42)).is_leaf());
        assert!(Expr_::Hole.is_leaf());
        assert!(!Expr_::Block(vec![]).is_leaf());
    }

    #[test]
    fn test_expr_is_control_flow() {
        let unit = WithLoc::synthetic(Expr_::Lit(Literal::Unit));
        assert!(Expr_::If(
            Box::new(unit.clone()),
            Box::new(unit.clone()),
            Box::new(unit)
        )
        .is_control_flow());
        assert!(Expr_::Return(None).is_control_flow());
        assert!(!Expr_::Lit(Literal::Unit).is_control_flow());
    }

    #[test]
    fn test_handler_depth() {
        assert!(HandlerDepth::Shallow.is_shallow());
        assert!(!HandlerDepth::Shallow.is_deep());
        assert!(HandlerDepth::Deep.is_deep());
        assert!(!HandlerDepth::Deep.is_shallow());
        assert_eq!(HandlerDepth::default(), HandlerDepth::Shallow);
    }

    #[test]
    fn test_continuation_linearity() {
        assert!(ContinuationLinearity::OneShot.is_one_shot());
        assert!(!ContinuationLinearity::OneShot.is_multi_shot());
        assert!(ContinuationLinearity::MultiShot.is_multi_shot());
        assert!(!ContinuationLinearity::MultiShot.is_one_shot());
        assert_eq!(ContinuationLinearity::default(), ContinuationLinearity::OneShot);
    }

    #[test]
    fn test_continuation_constructors() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");

        let one_shot = Continuation::one_shot(k);
        assert_eq!(one_shot.var, k);
        assert!(one_shot.linearity.is_one_shot());

        let multi_shot = Continuation::multi_shot(k);
        assert_eq!(multi_shot.var, k);
        assert!(multi_shot.linearity.is_multi_shot());
    }

    #[test]
    fn test_effect_handler_constructors() {
        let shallow = EffectHandler::shallow(vec![]);
        assert!(shallow.is_shallow());
        assert!(!shallow.is_deep());
        assert!(!shallow.has_return_clause());

        let deep = EffectHandler::deep(vec![]);
        assert!(deep.is_deep());
        assert!(!deep.is_shallow());
    }

    #[test]
    fn test_effect_handler_handled_effects() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");
        let body = WithLoc::synthetic(Expr_::Hole);

        let clause1 = HandlerClause::new(EffectOp::ReadSimple, vec![], k, body.clone());
        let clause2 = HandlerClause::new(EffectOp::WriteSimple, vec![], k, body);

        let handler = EffectHandler::shallow(vec![clause1, clause2]);
        let effects = handler.handled_effects();

        assert_eq!(effects.len(), 2);
        assert_eq!(effects[0], EffectOp::ReadSimple);
        assert_eq!(effects[1], EffectOp::WriteSimple);
    }

    #[test]
    fn test_effect_handler_with_return() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let x = rodeo.get_or_intern("x");
        let body = WithLoc::synthetic(Expr_::Var(x));

        let handler = EffectHandler::shallow(vec![]).with_return(x, body);
        assert!(handler.has_return_clause());
        assert!(handler.return_clause.is_some());
    }

    #[test]
    fn test_handler_clause_constructors() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");
        let v = rodeo.get_or_intern("v");
        let body = WithLoc::synthetic(Expr_::Hole);

        let one_shot = HandlerClause::new(EffectOp::ReadSimple, vec![v], k, body.clone());
        assert!(one_shot.continuation_linearity.is_one_shot());
        assert_eq!(one_shot.params.len(), 1);

        let multi_shot = HandlerClause::multi_shot(EffectOp::WriteSimple, vec![v], k, body);
        assert!(multi_shot.continuation_linearity.is_multi_shot());
    }

    #[test]
    fn test_handler_clause_get_continuation() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");
        let body = WithLoc::synthetic(Expr_::Hole);

        let clause = HandlerClause::multi_shot(EffectOp::Io, vec![], k, body);
        let cont = clause.get_continuation();

        assert_eq!(cont.var, k);
        assert!(cont.linearity.is_multi_shot());
    }

    #[test]
    fn test_effect_handler_find_clause() {
        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let k = rodeo.get_or_intern("k");
        let body = WithLoc::synthetic(Expr_::Hole);

        let clause = HandlerClause::new(EffectOp::Io, vec![], k, body);
        let handler = EffectHandler::shallow(vec![clause]);

        assert!(handler.find_clause(&EffectOp::Io).is_some());
        assert!(handler.find_clause(&EffectOp::Fs).is_none());
    }
}
