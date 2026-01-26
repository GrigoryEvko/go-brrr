//! Region (lifetime) inference module
//!
//! Implements region inference following F* BorrowChecker.fsti lines 298-312:
//! ```fstar
//! type lifetime_constraint =
//!   | LCOutlives : r1:region -> r2:region -> lifetime_constraint  (* r1: r2 *)
//!   | LCEqual    : r1:region -> r2:region -> lifetime_constraint  (* r1 = r2 *)
//!
//! val solve_lifetime_constraints : lifetime_constraints -> option (list (region & region))
//! ```
//!
//! # Overview
//!
//! This module provides region inference for borrow checking:
//!
//! - **Region variables**: Fresh regions generated during inference
//! - **Region constraints**: Outlives, equality, borrow validity constraints
//! - **Constraint solving**: Graph-based algorithm to find minimal regions
//! - **Error reporting**: Detailed region errors with source locations
//!
//! # Algorithm
//!
//! 1. Traverse expressions, generating fresh regions for borrows
//! 2. Collect constraints based on usage patterns
//! 3. Build outlives graph from constraints
//! 4. Check for cycles (which indicate errors)
//! 5. Compute minimal regions satisfying all constraints
//!
//! # Integration
//!
//! Region inference integrates with borrow checking:
//! - `BorrowState` tracks active loans with regions
//! - `RegionInferenceState` accumulates region constraints
//! - After inference, constraints are solved to validate borrows

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::borrow::{BorrowState, LifetimeConstraint, LifetimeConstraints};
use crate::expr::{Expr, Expr_, Range};
use crate::types::{BrrrType, Region};

// ============================================================================
// Region Variable
// ============================================================================

/// A region inference variable (unresolved region).
///
/// During inference, fresh region variables are created for each borrow.
/// After constraint solving, each variable is mapped to a concrete region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RegionVar(pub u32);

impl RegionVar {
    /// Create a new region variable with the given ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the variable ID
    #[must_use]
    pub const fn id(self) -> u32 {
        self.0
    }

    /// Convert to a Region::Fresh
    #[must_use]
    pub const fn to_region(self) -> Region {
        Region::Fresh(self.0)
    }
}

impl From<RegionVar> for Region {
    fn from(var: RegionVar) -> Self {
        var.to_region()
    }
}

// ============================================================================
// Region Constraint
// ============================================================================

/// Constraint on region lifetimes generated during inference.
///
/// These constraints are more expressive than `LifetimeConstraint`,
/// including borrow validity and well-formedness constraints.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RegionConstraint {
    /// Outlives constraint: `'a: 'b` (r1 outlives r2)
    ///
    /// The first region must live at least as long as the second.
    /// Generated when a reference with region r1 is used where region r2 is expected.
    Outlives(Region, Region, Range),

    /// Equality constraint: `'a = 'b`
    ///
    /// Both regions must be the same lifetime.
    /// Generated when two references must have identical lifetimes.
    Equal(Region, Region, Range),

    /// Borrow validity constraint: borrow in region r1 is valid for region r2
    ///
    /// The borrow must remain valid for the entire extent of r2.
    /// Generated for each borrow expression.
    BorrowValid {
        /// Region of the borrow
        borrow_region: Region,
        /// Region where the borrow is used
        use_region: Region,
        /// Source location for error reporting
        span: Range,
    },

    /// Well-formedness constraint: all regions in type are valid
    ///
    /// Ensures that a type's regions are properly scoped.
    /// Generated for type annotations and function boundaries.
    WellFormed {
        /// The type to check
        ty: BrrrType,
        /// Source location for error reporting
        span: Range,
    },

    /// Scope constraint: region must not escape its scope
    ///
    /// Generated at scope boundaries (let bindings, function returns).
    NotEscaping {
        /// Region that must not escape
        region: Region,
        /// Depth of the defining scope
        scope_depth: u32,
        /// Source location for error reporting
        span: Range,
    },
}

impl RegionConstraint {
    /// Create an outlives constraint
    #[must_use]
    pub fn outlives(r1: Region, r2: Region, span: Range) -> Self {
        Self::Outlives(r1, r2, span)
    }

    /// Create an equality constraint
    #[must_use]
    pub fn equal(r1: Region, r2: Region, span: Range) -> Self {
        Self::Equal(r1, r2, span)
    }

    /// Create a borrow validity constraint
    #[must_use]
    pub fn borrow_valid(borrow_region: Region, use_region: Region, span: Range) -> Self {
        Self::BorrowValid {
            borrow_region,
            use_region,
            span,
        }
    }

    /// Create a well-formedness constraint
    #[must_use]
    pub fn well_formed(ty: BrrrType, span: Range) -> Self {
        Self::WellFormed { ty, span }
    }

    /// Create a not-escaping constraint
    #[must_use]
    pub fn not_escaping(region: Region, scope_depth: u32, span: Range) -> Self {
        Self::NotEscaping {
            region,
            scope_depth,
            span,
        }
    }

    /// Get the source span for error reporting
    #[must_use]
    pub fn span(&self) -> Range {
        match self {
            Self::Outlives(_, _, span)
            | Self::Equal(_, _, span)
            | Self::BorrowValid { span, .. }
            | Self::WellFormed { span, .. }
            | Self::NotEscaping { span, .. } => *span,
        }
    }

    /// Convert to a basic LifetimeConstraint (if applicable)
    ///
    /// Returns `None` for constraints that don't map directly.
    #[must_use]
    pub fn to_lifetime_constraint(&self) -> Option<LifetimeConstraint> {
        match self {
            Self::Outlives(r1, r2, _) => Some(LifetimeConstraint::Outlives(*r1, *r2)),
            Self::Equal(r1, r2, _) => Some(LifetimeConstraint::Equal(*r1, *r2)),
            Self::BorrowValid {
                borrow_region,
                use_region,
                ..
            } => Some(LifetimeConstraint::Outlives(*borrow_region, *use_region)),
            _ => None,
        }
    }

    /// Check if this constraint is trivially satisfied
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        match self {
            Self::Outlives(r1, r2, _) => r1 == r2 || r1.is_static(),
            Self::Equal(r1, r2, _) => r1 == r2,
            Self::BorrowValid {
                borrow_region,
                use_region,
                ..
            } => borrow_region == use_region || borrow_region.is_static(),
            Self::WellFormed { .. } => false, // Requires type inspection
            Self::NotEscaping { region, .. } => region.is_static(),
        }
    }
}

// ============================================================================
// Region Error
// ============================================================================

/// Error types for region inference and checking.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RegionError {
    /// A region escapes its defining scope.
    ///
    /// This happens when a reference with a local region is returned
    /// or stored in a place that outlives the region.
    RegionEscapes {
        /// The escaping region
        region: Region,
        /// The type containing the escaping region
        escaping_type: BrrrType,
        /// Source location where the escape was detected
        span: Range,
    },

    /// A borrow does not live long enough for its use.
    ///
    /// This happens when a reference is used after its borrow expires.
    BorrowOutlivesValue {
        /// The region of the borrow
        borrow_region: Region,
        /// The region of the borrowed value
        value_region: Region,
        /// Source location of the conflicting use
        span: Range,
    },

    /// Two constraints require conflicting region relationships.
    ///
    /// This indicates an impossible situation, like requiring
    /// both `'a: 'b` and `'b: 'a` for different regions.
    ConflictingConstraints {
        /// First conflicting region
        r1: Region,
        /// Second conflicting region
        r2: Region,
        /// Source location where the conflict was detected
        span: Range,
        /// Optional explanation of the conflict
        message: Option<String>,
    },

    /// A region variable could not be resolved.
    ///
    /// This happens when there are insufficient constraints
    /// to determine a region's lifetime.
    UnresolvedRegion {
        /// The unresolved variable
        var: RegionVar,
        /// Source location where the variable was introduced
        span: Range,
    },

    /// A cycle was detected in the outlives graph.
    ///
    /// Cycles like `'a: 'b, 'b: 'c, 'c: 'a` for distinct regions
    /// indicate an error unless all regions in the cycle are equal.
    CycleDetected {
        /// Regions participating in the cycle
        cycle: Vec<Region>,
        /// Source location relevant to the cycle
        span: Range,
    },

    /// A type is not well-formed with respect to regions.
    ///
    /// The type contains regions that are not in scope or
    /// violate variance requirements.
    IllFormedType {
        /// The ill-formed type
        ty: BrrrType,
        /// Explanation of the issue
        reason: String,
        /// Source location of the type
        span: Range,
    },
}

impl RegionError {
    /// Create a region escapes error
    #[must_use]
    pub fn region_escapes(region: Region, escaping_type: BrrrType, span: Range) -> Self {
        Self::RegionEscapes {
            region,
            escaping_type,
            span,
        }
    }

    /// Create a borrow outlives value error
    #[must_use]
    pub fn borrow_outlives_value(borrow_region: Region, value_region: Region, span: Range) -> Self {
        Self::BorrowOutlivesValue {
            borrow_region,
            value_region,
            span,
        }
    }

    /// Create a conflicting constraints error
    #[must_use]
    pub fn conflicting_constraints(r1: Region, r2: Region, span: Range) -> Self {
        Self::ConflictingConstraints {
            r1,
            r2,
            span,
            message: None,
        }
    }

    /// Create an unresolved region error
    #[must_use]
    pub fn unresolved_region(var: RegionVar, span: Range) -> Self {
        Self::UnresolvedRegion { var, span }
    }

    /// Create a cycle detected error
    #[must_use]
    pub fn cycle_detected(cycle: Vec<Region>, span: Range) -> Self {
        Self::CycleDetected { cycle, span }
    }

    /// Create an ill-formed type error
    #[must_use]
    pub fn ill_formed_type(ty: BrrrType, reason: impl Into<String>, span: Range) -> Self {
        Self::IllFormedType {
            ty,
            reason: reason.into(),
            span,
        }
    }

    /// Get the source span for error reporting
    #[must_use]
    pub fn span(&self) -> Range {
        match self {
            Self::RegionEscapes { span, .. }
            | Self::BorrowOutlivesValue { span, .. }
            | Self::ConflictingConstraints { span, .. }
            | Self::UnresolvedRegion { span, .. }
            | Self::CycleDetected { span, .. }
            | Self::IllFormedType { span, .. } => *span,
        }
    }

    /// Get a human-readable error message
    #[must_use]
    pub fn message(&self) -> String {
        match self {
            Self::RegionEscapes { region, .. } => {
                format!("region {} escapes its scope", region.format())
            }
            Self::BorrowOutlivesValue {
                borrow_region,
                value_region,
                ..
            } => {
                format!(
                    "borrow with region {} does not live long enough (borrowed value has region {})",
                    borrow_region.format(),
                    value_region.format()
                )
            }
            Self::ConflictingConstraints {
                r1, r2, message, ..
            } => {
                let base = format!(
                    "conflicting region constraints: {} and {}",
                    r1.format(),
                    r2.format()
                );
                if let Some(msg) = message {
                    format!("{}: {}", base, msg)
                } else {
                    base
                }
            }
            Self::UnresolvedRegion { var, .. } => {
                format!("could not infer region for '_{})", var.0)
            }
            Self::CycleDetected { cycle, .. } => {
                let regions: Vec<_> = cycle.iter().map(|r| r.format()).collect();
                format!("region cycle detected: {}", regions.join(" -> "))
            }
            Self::IllFormedType { reason, .. } => {
                format!("ill-formed type: {}", reason)
            }
        }
    }
}

impl std::fmt::Display for RegionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for RegionError {}

// ============================================================================
// Region Inference State
// ============================================================================

/// State maintained during region inference.
///
/// Tracks fresh region generation, accumulated constraints,
/// the current substitution, and any errors encountered.
#[derive(Debug, Clone, Default)]
pub struct RegionInferenceState {
    /// Counter for generating fresh region variables
    pub next_var: u32,

    /// Accumulated region constraints
    pub constraints: Vec<RegionConstraint>,

    /// Current substitution mapping region variables to concrete regions
    pub substitution: HashMap<RegionVar, Region>,

    /// Accumulated region errors
    pub errors: Vec<RegionError>,

    /// Current scope depth (for tracking region scopes)
    pub scope_depth: u32,

    /// Regions introduced at each scope depth
    scope_regions: Vec<Vec<Region>>,
}

impl RegionInferenceState {
    /// Create a new empty region inference state
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh region variable
    #[must_use]
    pub fn fresh_region(&mut self) -> Region {
        let var = RegionVar(self.next_var);
        self.next_var += 1;
        Region::Fresh(var.0)
    }

    /// Generate a fresh region variable and return the RegionVar
    #[must_use]
    pub fn fresh_region_var(&mut self) -> RegionVar {
        let var = RegionVar(self.next_var);
        self.next_var += 1;
        var
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: RegionConstraint) {
        // Skip trivially satisfied constraints
        if !constraint.is_trivial() {
            self.constraints.push(constraint);
        }
    }

    /// Add an outlives constraint: r1 outlives r2
    pub fn constrain_outlives(&mut self, r1: Region, r2: Region, span: Range) {
        self.add_constraint(RegionConstraint::outlives(r1, r2, span));
    }

    /// Add an equality constraint
    pub fn constrain_equal(&mut self, r1: Region, r2: Region, span: Range) {
        self.add_constraint(RegionConstraint::equal(r1, r2, span));
    }

    /// Add a borrow validity constraint
    pub fn constrain_borrow_valid(&mut self, borrow: Region, use_region: Region, span: Range) {
        self.add_constraint(RegionConstraint::borrow_valid(borrow, use_region, span));
    }

    /// Add a well-formedness constraint for a type
    pub fn constrain_well_formed(&mut self, ty: BrrrType, span: Range) {
        self.add_constraint(RegionConstraint::well_formed(ty, span));
    }

    /// Add a not-escaping constraint
    pub fn constrain_not_escaping(&mut self, region: Region, span: Range) {
        self.add_constraint(RegionConstraint::not_escaping(
            region,
            self.scope_depth,
            span,
        ));
    }

    /// Record a region error
    pub fn add_error(&mut self, error: RegionError) {
        self.errors.push(error);
    }

    /// Check if any errors have been recorded
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Enter a new scope
    pub fn enter_scope(&mut self) {
        self.scope_depth += 1;
        self.scope_regions.push(Vec::new());
    }

    /// Exit the current scope
    ///
    /// Returns the regions that were introduced in this scope.
    pub fn exit_scope(&mut self) -> Vec<Region> {
        if self.scope_depth > 0 {
            self.scope_depth -= 1;
        }
        self.scope_regions.pop().unwrap_or_default()
    }

    /// Introduce a region at the current scope
    pub fn introduce_region(&mut self, region: Region) {
        if let Some(scope) = self.scope_regions.last_mut() {
            scope.push(region);
        }
    }

    /// Get the current scope as a region
    #[must_use]
    pub fn current_scope_region(&self) -> Region {
        Region::Scope(self.scope_depth)
    }

    /// Apply the current substitution to a region
    #[must_use]
    pub fn apply(&self, region: &Region) -> Region {
        match region {
            Region::Fresh(id) => {
                let var = RegionVar(*id);
                if let Some(resolved) = self.substitution.get(&var) {
                    // Recursively apply in case of chained substitutions
                    self.apply(resolved)
                } else {
                    *region
                }
            }
            _ => *region,
        }
    }

    /// Extend the substitution with a new mapping
    pub fn extend_substitution(&mut self, var: RegionVar, region: Region) {
        self.substitution.insert(var, region);
    }

    /// Convert all constraints to basic LifetimeConstraints
    #[must_use]
    pub fn to_lifetime_constraints(&self) -> LifetimeConstraints {
        self.constraints
            .iter()
            .filter_map(|c| c.to_lifetime_constraint())
            .collect()
    }

    /// Clear all constraints (after solving)
    pub fn clear_constraints(&mut self) {
        self.constraints.clear();
    }
}

// ============================================================================
// Region Inference for Expressions
// ============================================================================

/// Infer regions for an expression, generating constraints.
///
/// This traverses the expression tree, creating fresh regions for borrows
/// and adding constraints based on usage patterns.
///
/// # Arguments
/// * `expr` - The expression to analyze
/// * `state` - Region inference state to accumulate constraints
///
/// # Returns
/// `Ok(())` on success, or the first error encountered
pub fn infer_regions(expr: &Expr, state: &mut RegionInferenceState) -> Result<(), RegionError> {
    infer_regions_inner(&expr.value, expr.range, state)
}

fn infer_regions_inner(
    expr: &Expr_,
    span: Range,
    state: &mut RegionInferenceState,
) -> Result<(), RegionError> {
    match expr {
        // Literals and variables don't create region constraints
        Expr_::Lit(_) | Expr_::Var(_) | Expr_::Global(_) | Expr_::Hole | Expr_::Error(_) => Ok(()),

        // Borrow creates a fresh region
        Expr_::Borrow(inner) => {
            // Generate fresh region for the borrow
            let borrow_region = state.fresh_region();
            state.introduce_region(borrow_region);

            // The borrow must be valid for the current scope
            let scope_region = state.current_scope_region();
            state.constrain_borrow_valid(borrow_region, scope_region, span);

            // Recurse into the borrowed expression
            infer_regions(inner, state)
        }

        // Mutable borrow similarly creates a fresh region
        Expr_::BorrowMut(inner) => {
            let borrow_region = state.fresh_region();
            state.introduce_region(borrow_region);

            let scope_region = state.current_scope_region();
            state.constrain_borrow_valid(borrow_region, scope_region, span);

            infer_regions(inner, state)
        }

        // Let binding introduces a new scope
        Expr_::Let { init, body, ty, .. } => {
            // Check the initializer
            infer_regions(init, state)?;

            // If there's a type annotation, check well-formedness
            if let Some(ty) = ty {
                state.constrain_well_formed(ty.clone(), span);
            }

            // Enter scope for the binding
            state.enter_scope();

            // Check the body
            let result = infer_regions(body, state);

            // Exit scope
            let scope_regions = state.exit_scope();

            // Ensure scope regions don't escape
            for region in scope_regions {
                state.constrain_not_escaping(region, span);
            }

            result
        }

        // LetMut is similar to Let
        Expr_::LetMut { init, body, ty, .. } => {
            infer_regions(init, state)?;

            if let Some(ty) = ty {
                state.constrain_well_formed(ty.clone(), span);
            }

            state.enter_scope();
            let result = infer_regions(body, state);
            let scope_regions = state.exit_scope();

            for region in scope_regions {
                state.constrain_not_escaping(region, span);
            }

            result
        }

        // Lambda introduces a new scope for parameters
        Expr_::Lambda { params, body } => {
            state.enter_scope();

            // Check parameter types for well-formedness
            for (_, ty) in params {
                state.constrain_well_formed(ty.clone(), span);
            }

            let result = infer_regions(body, state);
            let scope_regions = state.exit_scope();

            // Lambda parameters' regions must not escape
            for region in scope_regions {
                state.constrain_not_escaping(region, span);
            }

            result
        }

        // Closure is similar to Lambda with captures
        Expr_::Closure {
            params,
            body,
            captures: _,
        } => {
            state.enter_scope();

            for (_, ty) in params {
                state.constrain_well_formed(ty.clone(), span);
            }

            let result = infer_regions(body, state);
            let scope_regions = state.exit_scope();

            for region in scope_regions {
                state.constrain_not_escaping(region, span);
            }

            result
        }

        // Function call: check arguments
        Expr_::Call(func, args) => {
            infer_regions(func, state)?;
            for arg in args {
                infer_regions(arg, state)?;
            }
            Ok(())
        }

        // Method call
        Expr_::MethodCall(receiver, _, args) => {
            infer_regions(receiver, state)?;
            for arg in args {
                infer_regions(arg, state)?;
            }
            Ok(())
        }

        // Unary operations
        Expr_::Unary(_, inner) => infer_regions(inner, state),

        // Binary operations
        Expr_::Binary(_, lhs, rhs) => {
            infer_regions(lhs, state)?;
            infer_regions(rhs, state)
        }

        // Tuple construction
        Expr_::Tuple(elems) => {
            for elem in elems {
                infer_regions(elem, state)?;
            }
            Ok(())
        }

        // Array construction
        Expr_::Array(elems) => {
            for elem in elems {
                infer_regions(elem, state)?;
            }
            Ok(())
        }

        // Struct construction
        Expr_::Struct { fields, .. } => {
            for (_, expr) in fields {
                infer_regions(expr, state)?;
            }
            Ok(())
        }

        // Enum variant construction
        Expr_::Variant { fields, .. } => {
            for field in fields {
                infer_regions(field, state)?;
            }
            Ok(())
        }

        // Field access
        Expr_::Field(base, _) => infer_regions(base, state),

        // Index access
        Expr_::Index(base, index) => {
            infer_regions(base, state)?;
            infer_regions(index, state)
        }

        // Tuple projection
        Expr_::TupleProj(base, _) => infer_regions(base, state),

        // If-else: both branches must have compatible regions
        Expr_::If(cond, then_branch, else_branch) => {
            infer_regions(cond, state)?;
            infer_regions(then_branch, state)?;
            infer_regions(else_branch, state)
        }

        // Match expression
        Expr_::Match(scrutinee, arms) => {
            infer_regions(scrutinee, state)?;
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    infer_regions(guard, state)?;
                }
                infer_regions(&arm.body, state)?;
            }
            Ok(())
        }

        // Loop body
        Expr_::Loop { body, .. } => {
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }

        // While loop
        Expr_::While { cond, body, .. } => {
            infer_regions(cond, state)?;
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }

        // For loop
        Expr_::For { iter, body, .. } => {
            infer_regions(iter, state)?;
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }

        // Break/continue don't affect regions
        Expr_::Break { value, .. } => {
            if let Some(v) = value {
                infer_regions(v, state)?;
            }
            Ok(())
        }
        Expr_::Continue { .. } => Ok(()),

        // Return: ensure returned value doesn't escape function scope
        Expr_::Return(value) => {
            if let Some(v) = value {
                infer_regions(v, state)?;
            }
            Ok(())
        }

        // Assignment
        Expr_::Assign(lhs, rhs) => {
            infer_regions(lhs, state)?;
            infer_regions(rhs, state)
        }

        // Box allocation
        Expr_::Box(inner) => infer_regions(inner, state),

        // Dereference
        Expr_::Deref(inner) => infer_regions(inner, state),

        // Move
        Expr_::Move(inner) => infer_regions(inner, state),

        // Drop
        Expr_::Drop(inner) => infer_regions(inner, state),

        // Throw
        Expr_::Throw(inner) => infer_regions(inner, state),

        // Try-catch
        Expr_::Try {
            body,
            catches,
            finally,
        } => {
            infer_regions(body, state)?;
            for catch in catches {
                infer_regions(&catch.body, state)?;
            }
            if let Some(fin) = finally {
                infer_regions(fin, state)?;
            }
            Ok(())
        }

        // Async operations
        Expr_::Await(inner) => infer_regions(inner, state),
        Expr_::Yield(inner) => infer_regions(inner, state),
        Expr_::Async(inner) => {
            state.enter_scope();
            let result = infer_regions(inner, state);
            state.exit_scope();
            result
        }
        Expr_::Spawn(inner) => {
            state.enter_scope();
            let result = infer_regions(inner, state);
            state.exit_scope();
            result
        }

        // Effect operations
        Expr_::Handle(body, _handler) => {
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }
        Expr_::Perform(_, args) => {
            for arg in args {
                infer_regions(arg, state)?;
            }
            Ok(())
        }
        Expr_::Resume { value, .. } => infer_regions(value, state),

        // Delimited continuations
        Expr_::Reset { body, .. } => {
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }
        Expr_::Shift { body, .. } => {
            state.enter_scope();
            let result = infer_regions(body, state);
            state.exit_scope();
            result
        }

        // Type operations
        Expr_::As(inner, ty) => {
            infer_regions(inner, state)?;
            state.constrain_well_formed(ty.clone(), span);
            Ok(())
        }
        Expr_::Is(inner, ty) => {
            infer_regions(inner, state)?;
            state.constrain_well_formed(ty.clone(), span);
            Ok(())
        }
        Expr_::Sizeof(ty) => {
            state.constrain_well_formed(ty.clone(), span);
            Ok(())
        }
        Expr_::Alignof(ty) => {
            state.constrain_well_formed(ty.clone(), span);
            Ok(())
        }

        // Blocks and sequences
        Expr_::Block(exprs) => {
            state.enter_scope();
            for expr in exprs {
                infer_regions(expr, state)?;
            }
            state.exit_scope();
            Ok(())
        }
        Expr_::Seq(first, second) => {
            infer_regions(first, state)?;
            infer_regions(second, state)
        }
        Expr_::Unsafe(inner) => infer_regions(inner, state),

        // Gradual cast
        Expr_::GradualCast { expr, .. } => infer_regions(expr, state),

        // Control flow labels
        Expr_::Goto { .. } => Ok(()),
        Expr_::Labeled { body, .. } => infer_regions(body, state),
    }
}

// ============================================================================
// Constraint Solving
// ============================================================================

/// Build an outlives graph from constraints.
///
/// Returns a map from each region to the set of regions it must outlive.
fn build_outlives_graph(constraints: &[RegionConstraint]) -> HashMap<Region, HashSet<Region>> {
    let mut graph: HashMap<Region, HashSet<Region>> = HashMap::new();

    for constraint in constraints {
        match constraint {
            RegionConstraint::Outlives(r1, r2, _) => {
                // r1: r2 means r1 outlives r2
                graph.entry(*r1).or_default().insert(*r2);
            }
            RegionConstraint::Equal(r1, r2, _) => {
                // Equality means both directions
                graph.entry(*r1).or_default().insert(*r2);
                graph.entry(*r2).or_default().insert(*r1);
            }
            RegionConstraint::BorrowValid {
                borrow_region,
                use_region,
                ..
            } => {
                // Borrow must outlive use
                graph.entry(*borrow_region).or_default().insert(*use_region);
            }
            _ => {}
        }
    }

    graph
}

/// Check for cycles in the outlives graph.
///
/// Returns `Some(cycle)` if a cycle is found, `None` otherwise.
fn find_cycle(graph: &HashMap<Region, HashSet<Region>>) -> Option<Vec<Region>> {
    let mut visited = HashSet::new();
    let mut rec_stack = HashSet::new();
    let mut path = Vec::new();

    for start in graph.keys() {
        if !visited.contains(start) {
            if let Some(cycle) =
                find_cycle_dfs(*start, graph, &mut visited, &mut rec_stack, &mut path)
            {
                return Some(cycle);
            }
        }
    }

    None
}

fn find_cycle_dfs(
    node: Region,
    graph: &HashMap<Region, HashSet<Region>>,
    visited: &mut HashSet<Region>,
    rec_stack: &mut HashSet<Region>,
    path: &mut Vec<Region>,
) -> Option<Vec<Region>> {
    visited.insert(node);
    rec_stack.insert(node);
    path.push(node);

    if let Some(neighbors) = graph.get(&node) {
        for neighbor in neighbors {
            // Skip self-loops (which are trivially satisfied)
            if *neighbor == node {
                continue;
            }

            if !visited.contains(neighbor) {
                if let Some(cycle) = find_cycle_dfs(*neighbor, graph, visited, rec_stack, path) {
                    return Some(cycle);
                }
            } else if rec_stack.contains(neighbor) {
                // Found a cycle - extract it from the path
                let cycle_start = path.iter().position(|r| r == neighbor).unwrap();
                return Some(path[cycle_start..].to_vec());
            }
        }
    }

    path.pop();
    rec_stack.remove(&node);
    None
}

/// Solve region constraints and compute a substitution.
///
/// This algorithm:
/// 1. Builds an outlives graph from constraints
/// 2. Checks for invalid cycles
/// 3. Computes minimal regions satisfying all constraints
///
/// # Arguments
/// * `constraints` - The constraints to solve
///
/// # Returns
/// `Ok(substitution)` mapping region variables to concrete regions,
/// or an error if constraints are unsatisfiable.
pub fn solve_region_constraints(
    constraints: &[RegionConstraint],
) -> Result<HashMap<RegionVar, Region>, RegionError> {
    // Build the outlives graph
    let graph = build_outlives_graph(constraints);

    // Check for invalid cycles
    if let Some(cycle) = find_cycle(&graph) {
        // A cycle is only valid if all regions in the cycle should be equal
        // For now, we report it as an error with a synthetic span
        return Err(RegionError::cycle_detected(cycle, Range::SYNTHETIC));
    }

    // Compute minimal regions
    // For each fresh region variable, find the minimal region that satisfies
    // all outlives constraints.
    let mut substitution = HashMap::new();

    // Collect all fresh region variables
    let mut fresh_vars: HashSet<RegionVar> = HashSet::new();
    for constraint in constraints {
        match constraint {
            RegionConstraint::Outlives(r1, r2, _) => {
                if let Region::Fresh(id) = r1 {
                    fresh_vars.insert(RegionVar(*id));
                }
                if let Region::Fresh(id) = r2 {
                    fresh_vars.insert(RegionVar(*id));
                }
            }
            RegionConstraint::Equal(r1, r2, _) => {
                if let Region::Fresh(id) = r1 {
                    fresh_vars.insert(RegionVar(*id));
                }
                if let Region::Fresh(id) = r2 {
                    fresh_vars.insert(RegionVar(*id));
                }
            }
            RegionConstraint::BorrowValid {
                borrow_region,
                use_region,
                ..
            } => {
                if let Region::Fresh(id) = borrow_region {
                    fresh_vars.insert(RegionVar(*id));
                }
                if let Region::Fresh(id) = use_region {
                    fresh_vars.insert(RegionVar(*id));
                }
            }
            RegionConstraint::NotEscaping { region, .. } => {
                if let Region::Fresh(id) = region {
                    fresh_vars.insert(RegionVar(*id));
                }
            }
            _ => {}
        }
    }

    // For each fresh variable, compute its minimal region
    for var in fresh_vars {
        let region = var.to_region();

        // Find all regions that this variable must outlive
        let must_outlive: HashSet<Region> = graph.get(&region).cloned().unwrap_or_default();

        // The minimal region is the maximum of all constraints
        // For scope regions, larger depth = more local = lives less long
        // So we want the minimum depth (longest lived)
        let minimal = if must_outlive.is_empty() {
            // No constraints - default to static
            Region::Static
        } else {
            compute_minimal_region(&must_outlive)
        };

        substitution.insert(var, minimal);
    }

    Ok(substitution)
}

/// Compute the minimal region that outlives all given regions.
fn compute_minimal_region(regions: &HashSet<Region>) -> Region {
    let mut min_scope_depth: Option<u32> = None;
    let mut has_static = false;

    for region in regions {
        match region {
            Region::Static => has_static = true,
            Region::Scope(depth) => {
                min_scope_depth = Some(min_scope_depth.map_or(*depth, |d| d.min(*depth)));
            }
            Region::Fresh(_) => {
                // Fresh regions need to be resolved transitively
                // For now, treat as scope 0
                min_scope_depth = Some(min_scope_depth.map_or(0, |d| d.min(0)));
            }
            Region::Named(_) => {
                // Named regions are treated conservatively
                min_scope_depth = Some(min_scope_depth.map_or(0, |d| d.min(0)));
            }
        }
    }

    // If we need to outlive 'static, we must be 'static
    if has_static {
        return Region::Static;
    }

    // Otherwise, use the minimum scope depth found
    min_scope_depth.map_or(Region::Static, Region::Scope)
}

// ============================================================================
// Integration with Borrow Checker
// ============================================================================

/// Check borrow regions against the borrow state.
///
/// This verifies that all borrows in the state have valid regions
/// according to the region inference results.
///
/// # Arguments
/// * `borrow_state` - The current borrow checker state
/// * `region_state` - The region inference state with solved constraints
///
/// # Returns
/// A list of region errors found during checking
pub fn check_borrow_regions(
    borrow_state: &BorrowState,
    region_state: &RegionInferenceState,
) -> Vec<RegionError> {
    let mut errors = Vec::new();

    // Check each active loan
    for loan in &borrow_state.loans {
        // Look up the variable being borrowed
        if let Some(var_entry) = borrow_state.lookup_var(loan.var) {
            // The loan's region must be valid at the current scope
            let loan_scope = Region::Scope(loan.depth);
            let current_scope = Region::Scope(borrow_state.depth);

            // Check if the loan region outlives the current scope
            let resolved_loan = region_state.apply(&loan_scope);
            let resolved_current = region_state.apply(&current_scope);

            if !resolved_loan.outlives(&resolved_current) {
                errors.push(RegionError::borrow_outlives_value(
                    resolved_loan,
                    resolved_current,
                    Range::SYNTHETIC,
                ));
            }

            // Check well-formedness of the borrowed type's regions
            let regions_in_type = extract_regions_from_type(&var_entry.ty);
            for region in regions_in_type {
                let resolved = region_state.apply(&region);
                if !resolved.outlives(&current_scope) {
                    errors.push(RegionError::region_escapes(
                        resolved,
                        var_entry.ty.clone(),
                        Range::SYNTHETIC,
                    ));
                }
            }
        }
    }

    // Add any errors from the region inference itself
    errors.extend(region_state.errors.clone());

    errors
}

/// Extract all regions from a type.
fn extract_regions_from_type(ty: &BrrrType) -> Vec<Region> {
    // For now, we don't have regions embedded in types
    // This would be extended when we add explicit region annotations to types
    let _ = ty;
    Vec::new()
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Create a scope region for a given depth
#[must_use]
pub const fn scope_region(depth: u32) -> Region {
    Region::Scope(depth)
}

/// Create a static region
#[must_use]
pub const fn static_region() -> Region {
    Region::Static
}

/// Check if a region is concrete (not a fresh variable)
#[must_use]
pub fn is_concrete_region(region: &Region) -> bool {
    !matches!(region, Region::Fresh(_))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Literal, WithLoc};

    fn make_expr(e: Expr_) -> Expr {
        WithLoc::synthetic(e)
    }

    #[test]
    fn test_region_var_creation() {
        let mut state = RegionInferenceState::new();

        let r1 = state.fresh_region();
        let r2 = state.fresh_region();

        assert!(matches!(r1, Region::Fresh(0)));
        assert!(matches!(r2, Region::Fresh(1)));
        assert_eq!(state.next_var, 2);
    }

    #[test]
    fn test_region_constraint_creation() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Scope(1);
        let span = Range::SYNTHETIC;

        let outlives = RegionConstraint::outlives(r1, r2, span);
        assert!(matches!(outlives, RegionConstraint::Outlives(_, _, _)));

        let equal = RegionConstraint::equal(r1, r2, span);
        assert!(matches!(equal, RegionConstraint::Equal(_, _, _)));
    }

    #[test]
    fn test_trivial_constraints() {
        let r = Region::Scope(1);
        let span = Range::SYNTHETIC;

        // Same region is trivial
        assert!(RegionConstraint::outlives(r, r, span).is_trivial());
        assert!(RegionConstraint::equal(r, r, span).is_trivial());

        // Static outlives anything is trivial
        assert!(RegionConstraint::outlives(Region::Static, r, span).is_trivial());

        // Non-static outliving static is NOT trivial
        assert!(!RegionConstraint::outlives(r, Region::Static, span).is_trivial());
    }

    #[test]
    fn test_inference_state_scopes() {
        let mut state = RegionInferenceState::new();

        assert_eq!(state.scope_depth, 0);

        state.enter_scope();
        assert_eq!(state.scope_depth, 1);

        let r = state.fresh_region();
        state.introduce_region(r);

        state.enter_scope();
        assert_eq!(state.scope_depth, 2);

        let exited = state.exit_scope();
        assert!(exited.is_empty()); // Inner scope had no regions

        assert_eq!(state.scope_depth, 1);

        let exited = state.exit_scope();
        assert_eq!(exited.len(), 1);
        assert_eq!(exited[0], r);

        assert_eq!(state.scope_depth, 0);
    }

    #[test]
    fn test_constraint_to_lifetime() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Scope(1);
        let span = Range::SYNTHETIC;

        let outlives = RegionConstraint::outlives(r1, r2, span);
        let lc = outlives.to_lifetime_constraint().unwrap();
        assert!(matches!(lc, LifetimeConstraint::Outlives(_, _)));

        let equal = RegionConstraint::equal(r1, r2, span);
        let lc = equal.to_lifetime_constraint().unwrap();
        assert!(matches!(lc, LifetimeConstraint::Equal(_, _)));

        let wf = RegionConstraint::well_formed(BrrrType::BOOL, span);
        assert!(wf.to_lifetime_constraint().is_none());
    }

    #[test]
    fn test_infer_regions_simple() {
        let mut state = RegionInferenceState::new();

        // Simple literal - no constraints
        let expr = make_expr(Expr_::Lit(Literal::Bool(true)));
        let result = infer_regions(&expr, &mut state);

        assert!(result.is_ok());
        assert!(state.constraints.is_empty());
    }

    #[test]
    fn test_infer_regions_borrow() {
        let mut state = RegionInferenceState::new();

        // &x creates a fresh region
        let inner = make_expr(Expr_::Lit(Literal::Unit));
        let borrow = make_expr(Expr_::Borrow(Box::new(inner)));

        let result = infer_regions(&borrow, &mut state);

        assert!(result.is_ok());
        assert_eq!(state.next_var, 1); // One fresh region created
                                       // Should have at least one constraint (borrow validity)
        assert!(!state.constraints.is_empty());
    }

    #[test]
    fn test_infer_regions_let() {
        let mut state = RegionInferenceState::new();

        let init = make_expr(Expr_::Lit(Literal::i32(42)));
        let body = make_expr(Expr_::Lit(Literal::Unit));

        let let_expr = make_expr(Expr_::Let {
            pattern: crate::expr::Pattern::synthetic(crate::expr::Pattern_::Wild),
            ty: None,
            init: Box::new(init),
            body: Box::new(body),
        });

        let result = infer_regions(&let_expr, &mut state);
        assert!(result.is_ok());
    }

    #[test]
    fn test_build_outlives_graph() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Scope(1);
        let r3 = Region::Scope(2);
        let span = Range::SYNTHETIC;

        let constraints = vec![
            RegionConstraint::outlives(r1, r2, span),
            RegionConstraint::outlives(r2, r3, span),
        ];

        let graph = build_outlives_graph(&constraints);

        assert!(graph.get(&r1).unwrap().contains(&r2));
        assert!(graph.get(&r2).unwrap().contains(&r3));
    }

    #[test]
    fn test_find_cycle_no_cycle() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Scope(1);
        let span = Range::SYNTHETIC;

        let constraints = vec![RegionConstraint::outlives(r1, r2, span)];

        let graph = build_outlives_graph(&constraints);
        let cycle = find_cycle(&graph);

        assert!(cycle.is_none());
    }

    #[test]
    fn test_find_cycle_with_cycle() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Fresh(1);
        let r3 = Region::Fresh(2);
        let span = Range::SYNTHETIC;

        let constraints = vec![
            RegionConstraint::outlives(r1, r2, span),
            RegionConstraint::outlives(r2, r3, span),
            RegionConstraint::outlives(r3, r1, span),
        ];

        let graph = build_outlives_graph(&constraints);
        let cycle = find_cycle(&graph);

        assert!(cycle.is_some());
        let cycle = cycle.unwrap();
        assert!(cycle.len() >= 2);
    }

    #[test]
    fn test_solve_simple_constraints() {
        let r1 = Region::Fresh(0);
        let r2 = Region::Scope(1);
        let span = Range::SYNTHETIC;

        let constraints = vec![RegionConstraint::outlives(r1, r2, span)];

        let result = solve_region_constraints(&constraints);
        assert!(result.is_ok());

        let subst = result.unwrap();
        // Fresh(0) should be resolved to something that outlives Scope(1)
        // That would be Scope(0) or Scope(1) (depending on minimal)
        if let Some(resolved) = subst.get(&RegionVar(0)) {
            assert!(resolved.outlives(&r2) || *resolved == r2);
        }
    }

    #[test]
    fn test_region_error_messages() {
        let err = RegionError::region_escapes(Region::Fresh(0), BrrrType::BOOL, Range::SYNTHETIC);
        assert!(err.message().contains("escapes"));

        let err = RegionError::borrow_outlives_value(
            Region::Scope(1),
            Region::Scope(0),
            Range::SYNTHETIC,
        );
        assert!(err.message().contains("live long enough"));

        let err =
            RegionError::cycle_detected(vec![Region::Fresh(0), Region::Fresh(1)], Range::SYNTHETIC);
        assert!(err.message().contains("cycle"));
    }

    #[test]
    fn test_region_substitution_apply() {
        let mut state = RegionInferenceState::new();

        let var = state.fresh_region_var();
        let resolved = Region::Scope(5);

        state.extend_substitution(var, resolved);

        let fresh = Region::Fresh(var.0);
        let applied = state.apply(&fresh);

        assert_eq!(applied, resolved);
    }

    #[test]
    fn test_compute_minimal_region() {
        let mut regions = HashSet::new();
        regions.insert(Region::Scope(2));
        regions.insert(Region::Scope(5));

        let minimal = compute_minimal_region(&regions);
        // Minimal should be Scope(2) - the outermost (longest lived)
        assert_eq!(minimal, Region::Scope(2));
    }

    #[test]
    fn test_compute_minimal_region_with_static() {
        let mut regions = HashSet::new();
        regions.insert(Region::Scope(2));
        regions.insert(Region::Static);

        let minimal = compute_minimal_region(&regions);
        // If we need to outlive 'static, we must be 'static
        assert_eq!(minimal, Region::Static);
    }

    #[test]
    fn test_check_borrow_regions_empty() {
        let borrow_state = BorrowState::new();
        let region_state = RegionInferenceState::new();

        let errors = check_borrow_regions(&borrow_state, &region_state);
        assert!(errors.is_empty());
    }
}
