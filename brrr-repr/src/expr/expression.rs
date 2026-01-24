//! Expression types (51 variants)
//!
//! Mirrors F* Expressions.fsti expr and expr'.

use lasso::Spur;
use serde::{Deserialize, Serialize};

use super::literal::Literal;
use super::location::{Range, WithLoc};
use super::operators::{BinaryOp, UnaryOp};
use super::pattern::Pattern;
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

/// Effect handler
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EffectHandler {
    /// Handler clauses
    pub clauses: Vec<HandlerClause>,
    /// Return clause (for normal completion)
    pub return_clause: Option<(VarId, Expr)>,
}

/// Handler clause for a specific effect operation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct HandlerClause {
    /// Effect operation being handled
    pub op: EffectOp,
    /// Parameter bindings
    pub params: Vec<VarId>,
    /// Continuation variable
    pub continuation: VarId,
    /// Handler body
    pub body: Expr,
}

/// Annotated expression with type/effect inference results
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnnotatedExpr {
    /// The expression
    pub expr: Expr,
    /// Inferred type
    pub ty: Option<BrrrType>,
    /// Inferred effects
    pub effects: Option<EffectRow>,
}

impl AnnotatedExpr {
    /// Create an unannotated expression
    pub fn unannotated(expr: Expr) -> Self {
        Self {
            expr,
            ty: None,
            effects: None,
        }
    }

    /// Create a fully annotated expression
    pub fn annotated(expr: Expr, ty: BrrrType, effects: EffectRow) -> Self {
        Self {
            expr,
            ty: Some(ty),
            effects: Some(effects),
        }
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
}
