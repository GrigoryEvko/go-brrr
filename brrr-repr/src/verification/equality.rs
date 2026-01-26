//! Propositional equality types for the verification IR
//!
//! Mirrors F* PropositionalEquality.fst (lines 192-233):
//! ```fstar
//! type eq_type (a: Type) (x y: a) : Type =
//!   | Refl : eq_type a x x
//!
//! let refl (#a: Type) (x: a) : eq_type a x x = Refl
//! let subst (#a: Type) (#x #y: a) (p: eq_type a x y) (prop: a -> Type) (px: prop x) : prop y
//! let sym (#a: Type) (#x #y: a) (p: eq_type a x y) : eq_type a y x
//! let trans (#a: Type) (#x #y #z: a) (p: eq_type a x y) (q: eq_type a y z) : eq_type a x z
//! ```
//!
//! This module provides IR-level representation of equality proofs, not Rust-level equality.
//! Since Rust lacks dependent types, these are symbolic representations used during
//! verification condition generation and SMT encoding.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::verification::equality::{EqWitness, refl, sym, trans, cong};
//!
//! // Create reflexivity proof: x = x
//! let x_eq_x = refl(&int_type, x_expr.clone());
//!
//! // Symmetry: if x = y then y = x
//! let y_eq_x = sym(x_eq_y);
//!
//! // Transitivity: if x = y and y = z then x = z
//! let x_eq_z = trans(x_eq_y, y_eq_z)?;
//!
//! // Congruence: if x = y then f(x) = f(y)
//! let fx_eq_fy = cong(f_expr, x_eq_y);
//! ```

use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use crate::expr::Expr;
use crate::types::{BrrrType, PrimKind, WrapperKind};

/// Proof of propositional equality between two values.
///
/// In a dependently-typed language like F*, `eq_type a x y` is a type that is
/// inhabited only when `x` and `y` are definitionally equal. The only constructor
/// is `Refl : eq_type a x x`.
///
/// In Rust, we cannot express this type-level constraint, so this is a symbolic
/// marker. The actual proof validity is ensured by construction functions
/// (`refl`, `sym`, `trans`, `cong`) and checked during verification.
///
/// The type parameter `T` is a phantom marker that tracks the type of values
/// being compared, enabling some compile-time checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EqProof<T> {
    /// Reflexivity proof: `x = x`
    ///
    /// The only primitive constructor. All other proofs are derived from this
    /// using symmetry, transitivity, and congruence.
    Refl(PhantomData<T>),
}

impl<T> EqProof<T> {
    /// Create a reflexivity proof.
    ///
    /// This is the fundamental proof constructor - reflexivity states that
    /// every value is equal to itself.
    #[inline]
    pub const fn refl() -> Self {
        Self::Refl(PhantomData)
    }

    /// Check if this is a reflexivity proof.
    #[inline]
    pub const fn is_refl(&self) -> bool {
        matches!(self, Self::Refl(_))
    }
}

impl<T> Default for EqProof<T> {
    fn default() -> Self {
        Self::refl()
    }
}

/// Witness of equality between two expressions.
///
/// Contains the complete equality proof information:
/// - The type of the values being compared
/// - The left-hand side expression
/// - The right-hand side expression
/// - The proof that they are equal
///
/// This is the main type used in the verification IR to represent
/// equality facts that can be used in proof obligations.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EqWitness {
    /// Type of the values being compared
    pub ty: BrrrType,

    /// Left-hand side expression
    pub left: Expr,

    /// Right-hand side expression
    pub right: Expr,

    /// Proof of equality (symbolic in Rust, checked during verification)
    pub proof: EqProof<Expr>,
}

impl EqWitness {
    /// Create a new equality witness.
    ///
    /// Note: This does not validate that left and right are actually equal.
    /// Use the construction functions (`refl`, `sym`, `trans`, `cong`) to
    /// create valid witnesses.
    #[inline]
    pub fn new(ty: BrrrType, left: Expr, right: Expr, proof: EqProof<Expr>) -> Self {
        Self {
            ty,
            left,
            right,
            proof,
        }
    }

    /// Check if this is a reflexivity witness (left == right syntactically).
    pub fn is_reflexive(&self) -> bool {
        self.left == self.right
    }

    /// Get the type of the equality.
    #[inline]
    pub fn ty(&self) -> &BrrrType {
        &self.ty
    }

    /// Get the left-hand side expression.
    #[inline]
    pub fn left(&self) -> &Expr {
        &self.left
    }

    /// Get the right-hand side expression.
    #[inline]
    pub fn right(&self) -> &Expr {
        &self.right
    }

    /// Swap left and right sides (used by `sym`).
    fn swap(self) -> Self {
        Self {
            ty: self.ty,
            left: self.right,
            right: self.left,
            proof: self.proof,
        }
    }
}

/// Create a reflexivity witness: `x = x`.
///
/// This is the fundamental equality proof - every expression is equal to itself.
///
/// Maps to F*:
/// ```fstar
/// let refl (#a: Type) (x: a) : eq_type a x x = Refl
/// ```
///
/// # Arguments
///
/// * `ty` - The type of the expression
/// * `expr` - The expression `x`
///
/// # Returns
///
/// An `EqWitness` proving `x = x`
#[inline]
pub fn refl(ty: &BrrrType, expr: Expr) -> EqWitness {
    EqWitness::new(ty.clone(), expr.clone(), expr, EqProof::refl())
}

/// Create a symmetry proof: if `x = y` then `y = x`.
///
/// Given a witness that `x = y`, produce a witness that `y = x`.
///
/// Maps to F*:
/// ```fstar
/// let sym (#a: Type) (#x #y: a) (p: eq_type a x y) : eq_type a y x =
///   match p with | Refl -> Refl
/// ```
///
/// # Arguments
///
/// * `witness` - Proof that `x = y`
///
/// # Returns
///
/// An `EqWitness` proving `y = x`
#[inline]
pub fn sym(witness: EqWitness) -> EqWitness {
    witness.swap()
}

/// Create a transitivity proof: if `x = y` and `y = z` then `x = z`.
///
/// Given witnesses that `x = y` and `y = z`, produce a witness that `x = z`,
/// but only if the middle expressions match (syntactically).
///
/// Maps to F*:
/// ```fstar
/// let trans (#a: Type) (#x #y #z: a) (p: eq_type a x y) (q: eq_type a y z) : eq_type a x z =
///   match p, q with | Refl, Refl -> Refl
/// ```
///
/// # Arguments
///
/// * `w1` - Proof that `x = y`
/// * `w2` - Proof that `y' = z`
///
/// # Returns
///
/// `Some(witness)` proving `x = z` if `y == y'` (syntactically)
/// `None` if the middle expressions don't match
pub fn trans(w1: EqWitness, w2: EqWitness) -> Option<EqWitness> {
    // Check that the middle expressions match
    if w1.right != w2.left {
        return None;
    }

    // Check that types are compatible
    if w1.ty != w2.ty {
        return None;
    }

    Some(EqWitness::new(w1.ty, w1.left, w2.right, EqProof::refl()))
}

/// Create a congruence proof: if `x = y` then `f(x) = f(y)`.
///
/// Given a function expression and a proof that `x = y`, produce a proof
/// that applying the function to both sides preserves equality.
///
/// Maps to the Leibniz property of equality: equal values cannot be
/// distinguished by any function.
///
/// # Arguments
///
/// * `func` - A function expression `f`
/// * `witness` - Proof that `x = y`
///
/// # Returns
///
/// An `EqWitness` proving `f(x) = f(y)`
///
/// # Note
///
/// The result type is computed by applying `func` to the argument type.
/// For simplicity, we currently keep the same type, assuming `f : T -> T`.
/// A full implementation would need type inference.
pub fn cong(func: Expr, witness: EqWitness) -> EqWitness {
    use crate::expr::{Expr_, WithLoc};

    // Build f(x) and f(y)
    let f_left = WithLoc::synthetic(Expr_::Call(
        Box::new(func.clone()),
        vec![witness.left.clone()],
    ));

    let f_right =
        WithLoc::synthetic(Expr_::Call(Box::new(func), vec![witness.right.clone()]));

    // For now, assume the result type is the same as input type.
    // A proper implementation would infer the return type of func.
    EqWitness::new(witness.ty, f_left, f_right, EqProof::refl())
}

/// Result of decidable equality check.
///
/// For types with decidable equality, we can determine at runtime/verification
/// time whether two values are equal, producing either a proof of equality
/// or a proof of inequality.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum DecEqResult {
    /// Values are equal, with witness
    Yes(EqWitness),

    /// Values are not equal (no witness available in propositional equality)
    No,
}

impl DecEqResult {
    /// Check if the result is `Yes`.
    #[inline]
    pub const fn is_yes(&self) -> bool {
        matches!(self, Self::Yes(_))
    }

    /// Check if the result is `No`.
    #[inline]
    pub const fn is_no(&self) -> bool {
        matches!(self, Self::No)
    }

    /// Extract the witness if present.
    #[inline]
    pub fn witness(self) -> Option<EqWitness> {
        match self {
            Self::Yes(w) => Some(w),
            Self::No => None,
        }
    }

    /// Get a reference to the witness if present.
    #[inline]
    pub fn witness_ref(&self) -> Option<&EqWitness> {
        match self {
            Self::Yes(w) => Some(w),
            Self::No => None,
        }
    }
}

/// Check if a type has decidable equality.
///
/// Types with decidable equality can be compared at runtime/verification time
/// to determine if two values are equal. This is important for:
/// - Pattern matching exhaustiveness
/// - SMT encoding (equality can be checked by the solver)
/// - Proof automation
///
/// # Types with decidable equality
///
/// - All primitive types (Unit, Bool, Char, String)
/// - All numeric types (integers, floats)
/// - Option, Result, tuples of decidable types
/// - Arrays and slices of decidable types
/// - Named types (assumed decidable unless proven otherwise)
/// - Structs and enums with all decidable fields
///
/// # Types without decidable equality
///
/// - Function types (cannot compare functions)
/// - Dynamic type (runtime type is unknown)
/// - Unknown type (gradual typing placeholder)
/// - Never type (uninhabited, vacuously true but not useful)
///
/// # Arguments
///
/// * `ty` - The type to check
///
/// # Returns
///
/// `true` if the type has decidable equality, `false` otherwise
pub fn has_decidable_eq(ty: &BrrrType) -> bool {
    match ty {
        // Primitives: most have decidable equality
        BrrrType::Prim(prim) => match prim {
            PrimKind::Unit | PrimKind::Bool | PrimKind::Char | PrimKind::String => true,
            // Dynamic/Unknown types don't have decidable equality
            PrimKind::Dynamic | PrimKind::Unknown => false,
            // Never is uninhabited - vacuously true but not useful
            PrimKind::Never => false,
        },

        // All numeric types have decidable equality
        BrrrType::Numeric(_) => true,

        // Wrapper types: decidable if inner type is decidable
        BrrrType::Wrap(kind, inner) => {
            match kind {
                // Arrays, slices, options: decidable if element is
                WrapperKind::Array
                | WrapperKind::Slice
                | WrapperKind::Option
                | WrapperKind::Box => has_decidable_eq(inner),

                // References: comparing pointers is decidable, but
                // comparing referenced values depends on inner type
                WrapperKind::Ref | WrapperKind::RefMut => has_decidable_eq(inner),

                // Rc/Arc: reference equality is decidable, value equality depends on inner
                WrapperKind::Rc | WrapperKind::Arc => has_decidable_eq(inner),

                // Raw pointers: pointer comparison is decidable
                WrapperKind::Raw => true,
            }
        }

        // Sized arrays: decidable if element type is decidable
        BrrrType::SizedArray(_, inner) => has_decidable_eq(inner),

        // Modal types: decidable if inner is decidable
        BrrrType::Modal(_, inner) => has_decidable_eq(inner),

        // Result type: decidable if both Ok and Err types are decidable
        BrrrType::Result(ok, err) => has_decidable_eq(ok) && has_decidable_eq(err),

        // Tuple: decidable if all elements are decidable
        BrrrType::Tuple(elems) => elems.iter().all(has_decidable_eq),

        // Function types do NOT have decidable equality
        // (cannot compare functions for equality in general)
        BrrrType::Func(_) => false,

        // Type variables: conservatively assume decidable
        // (will be checked when instantiated)
        BrrrType::Var(_) => true,

        // Type application: check the base type
        BrrrType::App(base, _) => has_decidable_eq(base),

        // Named types: assume decidable (user-defined types typically are)
        BrrrType::Named(_) => true,

        // Struct: decidable if all fields are decidable
        BrrrType::Struct(s) => s.fields.iter().all(|f| has_decidable_eq(&f.ty)),

        // Enum: decidable if all variant fields are decidable
        BrrrType::Enum(e) => e
            .variants
            .iter()
            .all(|v| v.fields.iter().all(|f| has_decidable_eq(f))),

        // Interface: interfaces do not have decidable equality
        // (cannot compare interface values for equality in general)
        BrrrType::Interface(_) => false,
    }
}

/// Check if two expressions are syntactically equal.
///
/// This is a conservative check that returns true only if the expressions
/// are identical (same AST structure). For semantic equality, use SMT solving.
///
/// # Arguments
///
/// * `ty` - The type of both expressions
/// * `left` - First expression
/// * `right` - Second expression
///
/// # Returns
///
/// `DecEqResult::Yes(witness)` if expressions are syntactically identical
/// `DecEqResult::No` if they differ (may still be semantically equal)
pub fn syntactic_eq(ty: &BrrrType, left: Expr, right: Expr) -> DecEqResult {
    if left == right {
        DecEqResult::Yes(refl(ty, left))
    } else {
        DecEqResult::No
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Expr_, Literal, WithLoc};
    use crate::types::{IntType, NumericType};

    fn make_int_expr(n: i32) -> Expr {
        WithLoc::synthetic(Expr_::Lit(Literal::i32(n)))
    }

    fn int_type() -> BrrrType {
        BrrrType::Numeric(NumericType::Int(IntType::I32))
    }

    #[test]
    fn test_eq_proof_refl() {
        let proof: EqProof<i32> = EqProof::refl();
        assert!(proof.is_refl());
    }

    #[test]
    fn test_eq_proof_default() {
        let proof: EqProof<String> = EqProof::default();
        assert!(proof.is_refl());
    }

    #[test]
    fn test_refl_creates_valid_witness() {
        let ty = int_type();
        let expr = make_int_expr(42);
        let witness = refl(&ty, expr.clone());

        assert_eq!(witness.ty, ty);
        assert_eq!(witness.left, expr);
        assert_eq!(witness.right, expr);
        assert!(witness.is_reflexive());
    }

    #[test]
    fn test_sym_swaps_sides() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y = make_int_expr(2);

        let x_eq_y = EqWitness::new(ty.clone(), x.clone(), y.clone(), EqProof::refl());
        let y_eq_x = sym(x_eq_y);

        assert_eq!(y_eq_x.left, y);
        assert_eq!(y_eq_x.right, x);
        assert_eq!(y_eq_x.ty, ty);
    }

    #[test]
    fn test_trans_matching_middle() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y = make_int_expr(2);
        let z = make_int_expr(3);

        let x_eq_y = EqWitness::new(ty.clone(), x.clone(), y.clone(), EqProof::refl());
        let y_eq_z = EqWitness::new(ty.clone(), y.clone(), z.clone(), EqProof::refl());

        let result = trans(x_eq_y, y_eq_z);
        assert!(result.is_some());

        let x_eq_z = result.unwrap();
        assert_eq!(x_eq_z.left, x);
        assert_eq!(x_eq_z.right, z);
    }

    #[test]
    fn test_trans_non_matching_middle() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y1 = make_int_expr(2);
        let y2 = make_int_expr(3);
        let z = make_int_expr(4);

        let x_eq_y1 = EqWitness::new(ty.clone(), x.clone(), y1.clone(), EqProof::refl());
        let y2_eq_z = EqWitness::new(ty.clone(), y2.clone(), z.clone(), EqProof::refl());

        let result = trans(x_eq_y1, y2_eq_z);
        assert!(result.is_none());
    }

    #[test]
    fn test_trans_type_mismatch() {
        let int_ty = int_type();
        let bool_ty = BrrrType::BOOL;
        let x = make_int_expr(1);
        let y = make_int_expr(2);

        let x_eq_y_int = EqWitness::new(int_ty, x.clone(), y.clone(), EqProof::refl());
        let y_eq_x_bool = EqWitness::new(bool_ty, y.clone(), x.clone(), EqProof::refl());

        let result = trans(x_eq_y_int, y_eq_x_bool);
        assert!(result.is_none());
    }

    #[test]
    fn test_cong_builds_function_application() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y = make_int_expr(2);

        use lasso::Rodeo;
        let mut rodeo = Rodeo::default();
        let f_name = rodeo.get_or_intern("f");
        let f = WithLoc::synthetic(Expr_::Global(f_name));

        let x_eq_y = EqWitness::new(ty, x.clone(), y.clone(), EqProof::refl());
        let fx_eq_fy = cong(f, x_eq_y);

        // Check that left is Call(f, [x])
        assert!(matches!(fx_eq_fy.left.value, Expr_::Call(_, _)));
        // Check that right is Call(f, [y])
        assert!(matches!(fx_eq_fy.right.value, Expr_::Call(_, _)));
    }

    #[test]
    fn test_dec_eq_result_yes() {
        let ty = int_type();
        let expr = make_int_expr(42);
        let witness = refl(&ty, expr);

        let result = DecEqResult::Yes(witness.clone());
        assert!(result.is_yes());
        assert!(!result.is_no());

        let extracted = result.witness();
        assert!(extracted.is_some());
        assert_eq!(extracted.unwrap(), witness);
    }

    #[test]
    fn test_dec_eq_result_no() {
        let result = DecEqResult::No;
        assert!(result.is_no());
        assert!(!result.is_yes());
        assert!(result.witness().is_none());
    }

    #[test]
    fn test_has_decidable_eq_primitives() {
        assert!(has_decidable_eq(&BrrrType::UNIT));
        assert!(has_decidable_eq(&BrrrType::BOOL));
        assert!(has_decidable_eq(&BrrrType::STRING));
        assert!(has_decidable_eq(&BrrrType::CHAR));

        // These don't have decidable equality
        assert!(!has_decidable_eq(&BrrrType::DYNAMIC));
        assert!(!has_decidable_eq(&BrrrType::UNKNOWN));
        assert!(!has_decidable_eq(&BrrrType::NEVER));
    }

    #[test]
    fn test_has_decidable_eq_numerics() {
        assert!(has_decidable_eq(&BrrrType::Numeric(NumericType::Int(
            IntType::I32
        ))));
        assert!(has_decidable_eq(&BrrrType::Numeric(NumericType::Int(
            IntType::U64
        ))));
        assert!(has_decidable_eq(&BrrrType::Numeric(NumericType::Float(
            crate::types::FloatPrec::F64
        ))));
    }

    #[test]
    fn test_has_decidable_eq_wrappers() {
        let int_ty = int_type();

        // Array, Slice, Option of decidable type are decidable
        assert!(has_decidable_eq(&BrrrType::array(int_ty.clone())));
        assert!(has_decidable_eq(&BrrrType::slice(int_ty.clone())));
        assert!(has_decidable_eq(&BrrrType::option(int_ty.clone())));

        // Wrappers of non-decidable types are not decidable
        assert!(!has_decidable_eq(&BrrrType::option(BrrrType::DYNAMIC)));
    }

    #[test]
    fn test_has_decidable_eq_tuples() {
        let int_ty = int_type();

        // Tuple of decidable types is decidable
        assert!(has_decidable_eq(&BrrrType::Tuple(vec![
            int_ty.clone(),
            BrrrType::BOOL
        ])));

        // Tuple with non-decidable type is not decidable
        assert!(!has_decidable_eq(&BrrrType::Tuple(vec![
            int_ty.clone(),
            BrrrType::DYNAMIC
        ])));

        // Empty tuple is decidable
        assert!(has_decidable_eq(&BrrrType::Tuple(vec![])));
    }

    #[test]
    fn test_has_decidable_eq_functions() {
        use crate::effects::EffectRow;
        use crate::types::FuncType;

        let func_ty = BrrrType::Func(Box::new(FuncType {
            params: vec![],
            return_type: BrrrType::UNIT,
            effects: EffectRow::pure(),
            is_unsafe: false,
        }));

        // Functions do NOT have decidable equality
        assert!(!has_decidable_eq(&func_ty));
    }

    #[test]
    fn test_syntactic_eq_identical() {
        let ty = int_type();
        let expr = make_int_expr(42);

        let result = syntactic_eq(&ty, expr.clone(), expr.clone());
        assert!(result.is_yes());
    }

    #[test]
    fn test_syntactic_eq_different() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y = make_int_expr(2);

        let result = syntactic_eq(&ty, x, y);
        assert!(result.is_no());
    }

    #[test]
    fn test_witness_accessors() {
        let ty = int_type();
        let x = make_int_expr(1);
        let y = make_int_expr(2);

        let witness = EqWitness::new(ty.clone(), x.clone(), y.clone(), EqProof::refl());

        assert_eq!(witness.ty(), &ty);
        assert_eq!(witness.left(), &x);
        assert_eq!(witness.right(), &y);
        assert!(!witness.is_reflexive());
    }
}
