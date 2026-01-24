//! Operator types
//!
//! Mirrors F* Expressions.fsti unary_op and binary_op.

use serde::{Deserialize, Serialize};

/// Unary operators
/// Maps to F*:
/// ```fstar
/// type unary_op =
///   | OpNeg | OpNot | OpBitNot | OpDeref | OpRef | OpRefMut
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum UnaryOp {
    /// Arithmetic negation `-x`
    Neg = 0,
    /// Logical not `!x` or `¬x`
    Not = 1,
    /// Bitwise not `~x` or `∼x`
    BitNot = 2,
    /// Dereference `*x`
    Deref = 3,
    /// Shared reference `&x`
    Ref = 4,
    /// Mutable reference `&mut x`
    RefMut = 5,
}

impl UnaryOp {
    /// Parse from text
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "-" | "neg" => Some(Self::Neg),
            "!" | "not" | "¬" => Some(Self::Not),
            "~" | "bitnot" | "∼" => Some(Self::BitNot),
            "*" | "deref" => Some(Self::Deref),
            "&" | "ref" => Some(Self::Ref),
            "&mut" | "refmut" => Some(Self::RefMut),
            _ => None,
        }
    }

    /// Format as symbol
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Neg => "-",
            Self::Not => "¬",
            Self::BitNot => "∼",
            Self::Deref => "*",
            Self::Ref => "&",
            Self::RefMut => "&mut",
        }
    }

    /// Format as text name
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Neg => "neg",
            Self::Not => "not",
            Self::BitNot => "bitnot",
            Self::Deref => "deref",
            Self::Ref => "ref",
            Self::RefMut => "refmut",
        }
    }

    /// Is this a memory operation?
    pub const fn is_memory_op(self) -> bool {
        matches!(self, Self::Deref | Self::Ref | Self::RefMut)
    }
}

/// Binary operators
/// Maps to F*:
/// ```fstar
/// type binary_op =
///   | OpAdd | OpSub | OpMul | OpDiv | OpMod
///   | OpEq | OpNe | OpLt | OpLe | OpGt | OpGe
///   | OpAnd | OpOr | OpBitAnd | OpBitOr | OpBitXor | OpShl | OpShr
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum BinaryOp {
    // Arithmetic
    /// Addition `+`
    Add = 0,
    /// Subtraction `-`
    Sub = 1,
    /// Multiplication `*`
    Mul = 2,
    /// Division `/`
    Div = 3,
    /// Modulo `%`
    Mod = 4,

    // Comparison
    /// Equality `==`
    Eq = 5,
    /// Not equal `!=` or `≠`
    Ne = 6,
    /// Less than `<`
    Lt = 7,
    /// Less or equal `<=` or `≤`
    Le = 8,
    /// Greater than `>`
    Gt = 9,
    /// Greater or equal `>=` or `≥`
    Ge = 10,

    // Logical
    /// Logical and `&&` or `∧`
    And = 11,
    /// Logical or `||` or `∨`
    Or = 12,

    // Bitwise
    /// Bitwise and `&&&` or `∩`
    BitAnd = 13,
    /// Bitwise or `|||` or `∪`
    BitOr = 14,
    /// Bitwise xor `^^^` or `⊕`
    BitXor = 15,
    /// Shift left `<<`
    Shl = 16,
    /// Arithmetic shift right `>>`
    Shr = 17,
    /// Logical shift right `>>>`
    UShr = 18,

    // Overflow-annotated arithmetic
    /// Checked add `+!` (returns Option)
    AddChecked = 19,
    /// Wrapping add `+%`
    AddWrapping = 20,
    /// Saturating add `+|`
    AddSaturating = 21,
    /// Checked sub `-!`
    SubChecked = 22,
    /// Wrapping sub `-%`
    SubWrapping = 23,
    /// Saturating sub `-|`
    SubSaturating = 24,
    /// Checked mul `*!`
    MulChecked = 25,
    /// Wrapping mul `*%`
    MulWrapping = 26,
    /// Saturating mul `*|`
    MulSaturating = 27,
}

impl BinaryOp {
    /// Parse from text
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "+" | "add" => Some(Self::Add),
            "-" | "sub" => Some(Self::Sub),
            "*" | "mul" => Some(Self::Mul),
            "/" | "div" => Some(Self::Div),
            "%" | "mod" => Some(Self::Mod),
            "==" | "eq" => Some(Self::Eq),
            "!=" | "≠" | "ne" => Some(Self::Ne),
            "<" | "lt" => Some(Self::Lt),
            "<=" | "≤" | "le" => Some(Self::Le),
            ">" | "gt" => Some(Self::Gt),
            ">=" | "≥" | "ge" => Some(Self::Ge),
            "&&" | "∧" | "and" => Some(Self::And),
            "||" | "∨" | "or" => Some(Self::Or),
            "&&&" | "∩" | "bitand" => Some(Self::BitAnd),
            "|||" | "∪" | "bitor" => Some(Self::BitOr),
            "^^^" | "⊕" | "bitxor" => Some(Self::BitXor),
            "<<" | "shl" => Some(Self::Shl),
            ">>" | "shr" => Some(Self::Shr),
            ">>>" | "ushr" => Some(Self::UShr),
            "+!" | "add_checked" => Some(Self::AddChecked),
            "+%" | "add_wrapping" => Some(Self::AddWrapping),
            "+|" | "add_saturating" => Some(Self::AddSaturating),
            "-!" | "sub_checked" => Some(Self::SubChecked),
            "-%" | "sub_wrapping" => Some(Self::SubWrapping),
            "-|" | "sub_saturating" => Some(Self::SubSaturating),
            "*!" | "mul_checked" => Some(Self::MulChecked),
            "*%" | "mul_wrapping" => Some(Self::MulWrapping),
            "*|" | "mul_saturating" => Some(Self::MulSaturating),
            _ => None,
        }
    }

    /// Format as symbol
    pub const fn as_symbol(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Eq => "==",
            Self::Ne => "≠",
            Self::Lt => "<",
            Self::Le => "≤",
            Self::Gt => ">",
            Self::Ge => "≥",
            Self::And => "∧",
            Self::Or => "∨",
            Self::BitAnd => "∩",
            Self::BitOr => "∪",
            Self::BitXor => "⊕",
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::UShr => ">>>",
            Self::AddChecked => "+!",
            Self::AddWrapping => "+%",
            Self::AddSaturating => "+|",
            Self::SubChecked => "-!",
            Self::SubWrapping => "-%",
            Self::SubSaturating => "-|",
            Self::MulChecked => "*!",
            Self::MulWrapping => "*%",
            Self::MulSaturating => "*|",
        }
    }

    /// Format as text name
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
            Self::Mod => "mod",
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
            Self::And => "and",
            Self::Or => "or",
            Self::BitAnd => "bitand",
            Self::BitOr => "bitor",
            Self::BitXor => "bitxor",
            Self::Shl => "shl",
            Self::Shr => "shr",
            Self::UShr => "ushr",
            Self::AddChecked => "add_checked",
            Self::AddWrapping => "add_wrapping",
            Self::AddSaturating => "add_saturating",
            Self::SubChecked => "sub_checked",
            Self::SubWrapping => "sub_wrapping",
            Self::SubSaturating => "sub_saturating",
            Self::MulChecked => "mul_checked",
            Self::MulWrapping => "mul_wrapping",
            Self::MulSaturating => "mul_saturating",
        }
    }

    /// Is this an arithmetic operator?
    pub const fn is_arithmetic(self) -> bool {
        matches!(
            self,
            Self::Add
                | Self::Sub
                | Self::Mul
                | Self::Div
                | Self::Mod
                | Self::AddChecked
                | Self::AddWrapping
                | Self::AddSaturating
                | Self::SubChecked
                | Self::SubWrapping
                | Self::SubSaturating
                | Self::MulChecked
                | Self::MulWrapping
                | Self::MulSaturating
        )
    }

    /// Is this a comparison operator?
    pub const fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }

    /// Is this a logical operator (short-circuit)?
    pub const fn is_logical(self) -> bool {
        matches!(self, Self::And | Self::Or)
    }

    /// Is this a bitwise operator?
    pub const fn is_bitwise(self) -> bool {
        matches!(
            self,
            Self::BitAnd | Self::BitOr | Self::BitXor | Self::Shl | Self::Shr | Self::UShr
        )
    }

    /// Is this an overflow-annotated operator?
    pub const fn is_overflow_annotated(self) -> bool {
        matches!(
            self,
            Self::AddChecked
                | Self::AddWrapping
                | Self::AddSaturating
                | Self::SubChecked
                | Self::SubWrapping
                | Self::SubSaturating
                | Self::MulChecked
                | Self::MulWrapping
                | Self::MulSaturating
        )
    }

    /// Get precedence (higher = binds tighter)
    pub const fn precedence(self) -> u8 {
        match self {
            Self::Mul | Self::Div | Self::Mod => 12,
            Self::MulChecked | Self::MulWrapping | Self::MulSaturating => 12,
            Self::Add | Self::Sub => 11,
            Self::AddChecked
            | Self::AddWrapping
            | Self::AddSaturating
            | Self::SubChecked
            | Self::SubWrapping
            | Self::SubSaturating => 11,
            Self::Shl | Self::Shr | Self::UShr => 10,
            Self::BitAnd => 9,
            Self::BitXor => 8,
            Self::BitOr => 7,
            Self::Lt | Self::Le | Self::Gt | Self::Ge | Self::Eq | Self::Ne => 6,
            Self::And => 5,
            Self::Or => 4,
        }
    }

    /// Is this operator left-associative?
    pub const fn is_left_assoc(self) -> bool {
        !self.is_comparison() // Comparisons are non-associative
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unary_roundtrip() {
        for op in [
            UnaryOp::Neg,
            UnaryOp::Not,
            UnaryOp::BitNot,
            UnaryOp::Deref,
            UnaryOp::Ref,
            UnaryOp::RefMut,
        ] {
            let s = op.as_str();
            assert_eq!(UnaryOp::from_str(s), Some(op));
        }
    }

    #[test]
    fn test_binary_roundtrip() {
        for op in [
            BinaryOp::Add,
            BinaryOp::Eq,
            BinaryOp::And,
            BinaryOp::BitAnd,
            BinaryOp::AddChecked,
        ] {
            let s = op.as_str();
            assert_eq!(BinaryOp::from_str(s), Some(op));
        }
    }

    #[test]
    fn test_operator_categories() {
        assert!(BinaryOp::Add.is_arithmetic());
        assert!(BinaryOp::Eq.is_comparison());
        assert!(BinaryOp::And.is_logical());
        assert!(BinaryOp::BitAnd.is_bitwise());
        assert!(BinaryOp::AddChecked.is_overflow_annotated());
    }

    #[test]
    fn test_precedence() {
        assert!(BinaryOp::Mul.precedence() > BinaryOp::Add.precedence());
        assert!(BinaryOp::Add.precedence() > BinaryOp::Eq.precedence());
        assert!(BinaryOp::Eq.precedence() > BinaryOp::And.precedence());
    }
}
