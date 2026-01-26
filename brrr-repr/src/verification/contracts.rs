//! Contract types for formal verification
//!
//! Mirrors F* Contracts.fst for requires/ensures clauses and loop invariants.
//!
//! # Overview
//!
//! This module provides Hoare-style contract annotations:
//! - **Preconditions** (`requires`): Must hold before function execution
//! - **Postconditions** (`ensures`): Must hold after function returns
//! - **Loop invariants**: Must hold at each iteration of a loop
//!
//! # Special Variables
//!
//! - `result`: Refers to the return value in postconditions
//! - `old(x)`: Refers to the value of `x` at function entry (via `OldRef`)
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::verification::{Contract, Formula, trivial_contract, formula_and};
//!
//! // F* equivalent:
//! // val abs: x:i32 -> Pure i32 (requires True) (ensures fun r -> r >= 0)
//!
//! let contract = Contract::new(
//!     Formula::True,
//!     Formula::ge(result_expr, zero_expr),
//! );
//! ```

use lasso::{Key, Spur};
use serde::{Deserialize, Serialize};

use super::formula::{formula_and, Formula};
use crate::expr::{Expr, Range};
use crate::types::BrrrType;

/// Variable identifier (same as expr::VarId)
pub type VarId = Spur;

/// Reference to old (pre-state) value of a variable
///
/// Used in postconditions to refer to the value of a variable
/// at function entry. Wraps a variable expression with `old()` semantics.
///
/// # Example
/// ```ignore
/// // ensures result == old(x) + 1
/// let old_x = OldRef::new(x_expr);
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OldRef {
    /// Source location
    pub range: Range,
    /// The variable/expression to take pre-state value of
    pub expr: Box<Expr>,
}

impl OldRef {
    /// Create a new old-reference
    pub fn new(expr: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            expr: Box::new(expr),
        }
    }

    /// Set the source location
    pub fn at(mut self, range: Range) -> Self {
        self.range = range;
        self
    }
}

/// Simple runtime assertion (state -> bool predicate)
///
/// Less expressive than `Formula` but easier to evaluate at runtime.
/// Used for dynamic checks and simple invariants.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Assertion {
    /// Source location of the assertion
    pub range: Range,
    /// Human-readable message on failure
    pub message: Option<String>,
    /// The condition that must hold
    pub condition: Expr,
}

impl Assertion {
    /// Create a new assertion
    pub fn new(condition: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            message: None,
            condition,
        }
    }

    /// Create an assertion with a message
    pub fn with_message(condition: Expr, message: impl Into<String>) -> Self {
        Self {
            range: Range::SYNTHETIC,
            message: Some(message.into()),
            condition,
        }
    }

    /// Set the source location
    pub fn at(mut self, range: Range) -> Self {
        self.range = range;
        self
    }
}

/// Hoare-style contract for a function
///
/// Maps to F*:
/// ```fstar
/// noeq type contract = {
///   precondition  : formula;   (* requires clause *)
///   postcondition : formula;   (* ensures clause - can use "result" *)
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Contract {
    /// Precondition (requires clause) - must hold on entry
    pub precondition: Formula,
    /// Postcondition (ensures clause) - must hold on exit
    /// Can reference `result` for return value
    pub postcondition: Formula,
}

impl Contract {
    /// Create a new contract
    pub fn new(precondition: Formula, postcondition: Formula) -> Self {
        Self {
            precondition,
            postcondition,
        }
    }

    /// Check if this contract is trivial (pre=True, post=True)
    pub fn is_trivial(&self) -> bool {
        self.precondition.is_true() && self.postcondition.is_true()
    }

    /// Combine two contracts (conjunction of both pre and post)
    pub fn and(self, other: Self) -> Self {
        Self {
            precondition: formula_and(self.precondition, other.precondition),
            postcondition: formula_and(self.postcondition, other.postcondition),
        }
    }
}

impl Default for Contract {
    fn default() -> Self {
        trivial_contract()
    }
}

/// Function with attached contract
///
/// Maps to F*:
/// ```fstar
/// noeq type contracted_function = {
///   fn_name     : string;
///   fn_params   : list (var_id & brrr_type);
///   fn_return   : brrr_type;
///   fn_contract : contract;
///   fn_body     : expr;
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ContractedFunction {
    /// Function name (interned)
    pub name: Spur,
    /// Parameters with types
    pub params: Vec<(VarId, BrrrType)>,
    /// Return type
    pub return_type: BrrrType,
    /// Function contract (requires/ensures)
    pub contract: Contract,
    /// Function body
    pub body: Expr,
}

impl ContractedFunction {
    /// Create a new contracted function
    pub fn new(
        name: Spur,
        params: Vec<(VarId, BrrrType)>,
        return_type: BrrrType,
        contract: Contract,
        body: Expr,
    ) -> Self {
        Self {
            name,
            params,
            return_type,
            contract,
            body,
        }
    }

    /// Create with trivial contract
    pub fn unverified(
        name: Spur,
        params: Vec<(VarId, BrrrType)>,
        return_type: BrrrType,
        body: Expr,
    ) -> Self {
        Self::new(name, params, return_type, trivial_contract(), body)
    }

    /// Check if this function has a non-trivial contract
    pub fn has_contract(&self) -> bool {
        !self.contract.is_trivial()
    }
}

/// While loop with invariant annotation
///
/// Used for verified loop constructs where an invariant must be maintained.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnnotatedWhile {
    /// Source location
    pub range: Range,
    /// Loop invariant (must hold before and after each iteration)
    pub invariant: Formula,
    /// Optional variant for termination (must decrease)
    pub variant: Option<Expr>,
    /// Loop condition
    pub condition: Expr,
    /// Loop body
    pub body: Expr,
}

impl AnnotatedWhile {
    /// Create a new annotated while loop
    pub fn new(invariant: Formula, condition: Expr, body: Expr) -> Self {
        Self {
            range: Range::SYNTHETIC,
            invariant,
            variant: None,
            condition,
            body,
        }
    }

    /// Add a termination variant (expression that decreases each iteration)
    pub fn with_variant(mut self, variant: Expr) -> Self {
        self.variant = Some(variant);
        self
    }

    /// Set the source location
    pub fn at(mut self, range: Range) -> Self {
        self.range = range;
        self
    }
}

// ============================================================================
// Special variable constructors
// ============================================================================

/// Reserved variable name for the return value in postconditions.
///
/// In F*, this corresponds to the implicit `result` binding in `ensures` clauses.
///
/// # Note
/// The actual `Spur` value uses a sentinel that the interner recognizes.
/// For cross-module consistency, use the interned string "___result" directly.
///
/// # Panics
/// Panics if the sentinel index is invalid (should never happen in practice).
pub fn spec_result() -> VarId {
    // Sentinel value - use a high index that won't conflict with typical interned strings
    // The value 0xFFF0 is chosen to be large but valid for most interner configurations
    Spur::try_from_usize(0xFFF0).expect("sentinel index for result variable is invalid")
}

/// Create an old-reference for a variable in postconditions.
///
/// This wraps the given expression to indicate we want its pre-state value.
///
/// # Example
/// ```ignore
/// // ensures result == old(x) + 1
/// let old_x = spec_old(x_expr);
/// ```
///
/// # Implementation
/// Returns an `OldRef` wrapper. Use `OldRef::new()` directly for cleaner code.
pub fn spec_old(expr: Expr) -> OldRef {
    OldRef::new(expr)
}

/// Create a trivial contract (pre=True, post=True)
///
/// Represents an unverified function with no proof obligations.
#[must_use]
pub fn trivial_contract() -> Contract {
    Contract {
        precondition: Formula::True,
        postcondition: Formula::True,
    }
}

/// Well-known variable name for "result" in postconditions
pub const RESULT_VAR_NAME: &str = "___result";

/// Prefix for "old" variable references
pub const OLD_VAR_PREFIX: &str = "___old_";

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Expr_, Literal, WithLoc};
    use crate::verification::formula::CmpOp;

    fn make_int_expr(n: i32) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(n)))
    }

    #[test]
    fn test_trivial_contract() {
        let contract = trivial_contract();
        assert!(contract.is_trivial());
        assert!(contract.precondition.is_true());
        assert!(contract.postcondition.is_true());
    }

    #[test]
    fn test_contract_combination() {
        let phi = Formula::cmp(CmpOp::Gt, make_int_expr(1), make_int_expr(0));
        let psi = Formula::cmp(CmpOp::Lt, make_int_expr(5), make_int_expr(10));

        let c1 = Contract::new(phi.clone(), Formula::True);
        let c2 = Contract::new(Formula::True, psi.clone());

        let combined = c1.and(c2);
        assert!(!combined.is_trivial());

        // Precondition: phi && True = phi
        assert!(matches!(combined.precondition, Formula::Cmp(..)));

        // Postcondition: True && psi = psi
        assert!(matches!(combined.postcondition, Formula::Cmp(..)));
    }

    #[test]
    fn test_assertion() {
        let cond = make_int_expr(1);
        let assertion = Assertion::with_message(cond.clone(), "x must be positive");

        assert_eq!(assertion.message, Some("x must be positive".to_string()));
        assert!(assertion.range.is_synthetic());
    }

    #[test]
    fn test_old_ref() {
        let x = make_int_expr(42);
        let old_x = spec_old(x.clone());

        assert!(old_x.range.is_synthetic());
        assert_eq!(*old_x.expr, x);
    }

    #[test]
    fn test_annotated_while() {
        let invariant = Formula::cmp(CmpOp::Ge, make_int_expr(0), make_int_expr(0));
        let cond = WithLoc::synthetic(Expr_::Lit(Literal::Bool(true)));
        let body = WithLoc::synthetic(Expr_::Hole);
        let variant = make_int_expr(10);

        let annotated = AnnotatedWhile::new(invariant.clone(), cond, body).with_variant(variant);

        assert!(annotated.variant.is_some());
        assert_eq!(annotated.invariant, invariant);
    }

    #[test]
    fn test_contracted_function() {
        let name = Spur::try_from_usize(1).unwrap();
        let body = WithLoc::synthetic(Expr_::Hole);
        let contract = Contract::new(
            Formula::True,
            Formula::cmp(CmpOp::Ge, make_int_expr(0), make_int_expr(0)),
        );

        let func = ContractedFunction::new(name, vec![], BrrrType::UNIT, contract, body);

        assert!(func.has_contract());
    }

    #[test]
    fn test_unverified_function() {
        let name = Spur::try_from_usize(1).unwrap();
        let body = WithLoc::synthetic(Expr_::Hole);

        let func = ContractedFunction::unverified(name, vec![], BrrrType::UNIT, body);

        assert!(!func.has_contract());
        assert!(func.contract.is_trivial());
    }
}
