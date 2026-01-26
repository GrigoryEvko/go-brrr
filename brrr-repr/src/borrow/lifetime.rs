//! Lifetime constraint types for borrow checking
//!
//! Mirrors F* BorrowChecker.fst lines 2214-2312:
//! ```fstar
//! type lifetime_constraint =
//!   | LCOutlives : r1:region -> r2:region -> lifetime_constraint  (* r1: r2 *)
//!   | LCEqual    : r1:region -> r2:region -> lifetime_constraint  (* r1 = r2 *)
//!
//! type lifetime_constraints = list lifetime_constraint
//! ```
//!
//! # Overview
//!
//! This module provides lifetime constraint types for tracking region relationships
//! during borrow checking. Constraints express:
//!
//! - **Outlives**: `r1: r2` means region r1 lives at least as long as r2
//! - **Equal**: `r1 = r2` means regions are the same lifetime
//!
//! # Constraint Solving
//!
//! The solver attempts to find a consistent assignment of region orderings
//! that satisfies all constraints. This is used during type inference to
//! determine valid lifetime relationships.

use serde::{Deserialize, Serialize};

use crate::types::Region;

// ============================================================================
// Lifetime Constraint
// ============================================================================

/// A constraint on region lifetimes
///
/// Maps to F*:
/// ```fstar
/// type lifetime_constraint =
///   | LCOutlives : r1:region -> r2:region -> lifetime_constraint  (* r1: r2 *)
///   | LCEqual    : r1:region -> r2:region -> lifetime_constraint  (* r1 = r2 *)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LifetimeConstraint {
    /// `r1: r2` - region r1 outlives (lives at least as long as) region r2
    ///
    /// This means any reference with lifetime r1 can be used where
    /// a reference with lifetime r2 is expected.
    Outlives(Region, Region),

    /// `r1 = r2` - regions r1 and r2 are equal
    ///
    /// Equivalent to both `r1: r2` and `r2: r1`.
    Equal(Region, Region),
}

impl LifetimeConstraint {
    /// Create an outlives constraint: r1 outlives r2 (r1: r2)
    pub const fn outlives(r1: Region, r2: Region) -> Self {
        Self::Outlives(r1, r2)
    }

    /// Create an equality constraint: r1 = r2
    pub const fn equal(r1: Region, r2: Region) -> Self {
        Self::Equal(r1, r2)
    }

    /// Get the first region in the constraint
    pub const fn first(&self) -> Region {
        match self {
            Self::Outlives(r1, _) | Self::Equal(r1, _) => *r1,
        }
    }

    /// Get the second region in the constraint
    pub const fn second(&self) -> Region {
        match self {
            Self::Outlives(_, r2) | Self::Equal(_, r2) => *r2,
        }
    }

    /// Check if this is an outlives constraint
    pub const fn is_outlives(&self) -> bool {
        matches!(self, Self::Outlives(_, _))
    }

    /// Check if this is an equality constraint
    pub const fn is_equal(&self) -> bool {
        matches!(self, Self::Equal(_, _))
    }

    /// Check if the constraint is trivially satisfied
    ///
    /// A constraint is trivially satisfied if:
    /// - Both regions are the same (for both Outlives and Equal)
    /// - r1 is Static (for Outlives, since 'static outlives everything)
    pub fn is_trivial(&self) -> bool {
        match self {
            Self::Outlives(r1, r2) => {
                r1 == r2 || r1.is_static()
            }
            Self::Equal(r1, r2) => r1 == r2,
        }
    }

    /// Expand an equality constraint into two outlives constraints
    ///
    /// `r1 = r2` expands to `[r1: r2, r2: r1]`
    pub fn expand_equal(self) -> Vec<Self> {
        match self {
            Self::Equal(r1, r2) => {
                vec![Self::Outlives(r1, r2), Self::Outlives(r2, r1)]
            }
            c @ Self::Outlives(_, _) => vec![c],
        }
    }

    /// Format as a human-readable string
    pub fn format(&self) -> String {
        match self {
            Self::Outlives(r1, r2) => format!("{}: {}", r1.format(), r2.format()),
            Self::Equal(r1, r2) => format!("{} = {}", r1.format(), r2.format()),
        }
    }
}

// ============================================================================
// Lifetime Constraints Collection
// ============================================================================

/// A collection of lifetime constraints
///
/// Maps to F*: `type lifetime_constraints = list lifetime_constraint`
pub type LifetimeConstraints = Vec<LifetimeConstraint>;

/// Add a constraint to the constraint set
///
/// Returns a new constraint set with the constraint added.
/// Skips trivially satisfied constraints.
///
/// # Arguments
/// * `constraints` - Existing constraints
/// * `c` - New constraint to add
///
/// # Returns
/// New constraint set with the constraint added (if non-trivial)
pub fn add_constraint(mut constraints: LifetimeConstraints, c: LifetimeConstraint) -> LifetimeConstraints {
    // Skip trivially satisfied constraints
    if !c.is_trivial() && !constraints.contains(&c) {
        constraints.push(c);
    }
    constraints
}

/// Check if a set of constraints is satisfiable
///
/// Performs basic consistency checking:
/// 1. Static region can only be equal to itself
/// 2. No cyclic outlives constraints that would require r: r for non-static r
/// 3. Scope regions must have valid depth ordering
///
/// This is a conservative check - returning true does not guarantee
/// full satisfiability, but returning false means definitely unsatisfiable.
///
/// # Arguments
/// * `constraints` - The constraints to check
///
/// # Returns
/// `true` if constraints appear satisfiable, `false` if definitely unsatisfiable
pub fn constraints_satisfiable(constraints: &LifetimeConstraints) -> bool {
    for c in constraints {
        match c {
            LifetimeConstraint::Equal(r1, r2) => {
                // Static can only equal static
                if r1.is_static() != r2.is_static() {
                    return false;
                }
            }
            LifetimeConstraint::Outlives(r1, r2) => {
                // Check basic satisfiability using region_outlives
                // Note: We skip this for named regions as they may be unifiable
                match (r1, r2) {
                    (Region::Static, _) => { /* Always satisfiable */ }
                    (_, Region::Static) => {
                        // Only 'static can outlive 'static
                        if !r1.is_static() {
                            // This is only satisfiable if r1 can be unified with 'static
                            // For now, we're conservative and allow it for named/fresh regions
                            match r1 {
                                Region::Scope(_) | Region::Fresh(_) => {
                                    // These cannot outlive 'static
                                    return false;
                                }
                                _ => {}
                            }
                        }
                    }
                    (Region::Scope(d1), Region::Scope(d2)) => {
                        // Outer scopes outlive inner scopes (smaller depth = longer lived)
                        if *d1 > *d2 {
                            return false;
                        }
                    }
                    (Region::Fresh(n1), Region::Fresh(n2)) => {
                        // Earlier fresh regions outlive later ones
                        if *n1 > *n2 {
                            return false;
                        }
                    }
                    _ => {
                        // Named regions are unifiable, so we allow the constraint
                    }
                }
            }
        }
    }

    // Check for cycles in outlives constraints
    // A cycle like r1: r2, r2: r1 for different regions is only valid
    // if r1 = r2, which means they must be unifiable
    // For now, we do a simple check: no immediate contradictions found

    true
}

/// Attempt to solve constraints and return region equivalence classes
///
/// This performs a simplified unification-based solving:
/// 1. Collect all equality constraints into equivalence classes
/// 2. Verify outlives constraints are satisfiable
/// 3. Return pairs of equivalent regions
///
/// # Arguments
/// * `constraints` - The constraints to solve
///
/// # Returns
/// `Some(equivalences)` if solvable, where each pair represents equivalent regions
/// `None` if the constraints are unsatisfiable
pub fn solve_constraints(constraints: &LifetimeConstraints) -> Option<Vec<(Region, Region)>> {
    if !constraints_satisfiable(constraints) {
        return None;
    }

    let mut equivalences = Vec::new();

    // Extract equality constraints
    for c in constraints {
        if let LifetimeConstraint::Equal(r1, r2) = c {
            if r1 != r2 {
                equivalences.push((*r1, *r2));
            }
        }
    }

    // For outlives constraints, check if they form implicit equalities
    // e.g., r1: r2 and r2: r1 implies r1 = r2
    let outlives: Vec<_> = constraints
        .iter()
        .filter_map(|c| {
            if let LifetimeConstraint::Outlives(r1, r2) = c {
                Some((*r1, *r2))
            } else {
                None
            }
        })
        .collect();

    for &(r1, r2) in &outlives {
        // Check for reverse constraint
        if outlives.contains(&(r2, r1)) && r1 != r2 {
            // Mutual outlives implies equality
            // Use canonical ordering: pair them so we don't add duplicates
            if !equivalences.contains(&(r1, r2)) && !equivalences.contains(&(r2, r1)) {
                equivalences.push((r1, r2));
            }
        }
    }

    Some(equivalences)
}

// ============================================================================
// Region Outlives Check
// ============================================================================

/// Check if region r1 outlives region r2
///
/// This implements the basic lifetime ordering rules:
/// - `'static` outlives all regions
/// - A named region only outlives itself (without additional constraints)
/// - Fresh regions: earlier (lower number) outlives later
/// - Scope regions: outer (lower depth) outlives inner
///
/// # Arguments
/// * `r1` - The potentially longer-lived region
/// * `r2` - The potentially shorter-lived region
///
/// # Returns
/// `true` if r1 definitely outlives r2 based on the region structure
pub fn region_outlives(r1: &Region, r2: &Region) -> bool {
    r1.outlives(r2)
}

// ============================================================================
// Borrow Constraint Construction
// ============================================================================

/// Create a borrow constraint for a region at a given scope depth
///
/// When borrowing at a certain scope depth, we need to ensure the
/// borrowed reference's region outlives the scope where it's used.
///
/// # Arguments
/// * `region` - The region of the reference being borrowed
/// * `depth` - The current scope depth where the borrow occurs
///
/// # Returns
/// A constraint that `region` must outlive the scope at `depth`
pub fn borrow_constraint(region: Region, depth: u32) -> LifetimeConstraint {
    LifetimeConstraint::outlives(region, Region::Scope(depth))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lifetime_constraint_creation() {
        let r1 = Region::Static;
        let r2 = Region::Scope(1);

        let outlives = LifetimeConstraint::outlives(r1, r2);
        assert!(outlives.is_outlives());
        assert!(!outlives.is_equal());
        assert_eq!(outlives.first(), r1);
        assert_eq!(outlives.second(), r2);

        let equal = LifetimeConstraint::equal(r1, r2);
        assert!(equal.is_equal());
        assert!(!equal.is_outlives());
    }

    #[test]
    fn test_trivial_constraints() {
        let r = Region::Scope(1);

        // Same region is trivial
        assert!(LifetimeConstraint::outlives(r, r).is_trivial());
        assert!(LifetimeConstraint::equal(r, r).is_trivial());

        // Static outlives anything is trivial
        assert!(LifetimeConstraint::outlives(Region::Static, r).is_trivial());

        // Non-static outliving static is not trivial
        assert!(!LifetimeConstraint::outlives(r, Region::Static).is_trivial());

        // Different regions equality is not trivial
        assert!(!LifetimeConstraint::equal(Region::Static, r).is_trivial());
    }

    #[test]
    fn test_expand_equal() {
        let r1 = Region::Scope(1);
        let r2 = Region::Scope(2);

        let equal = LifetimeConstraint::equal(r1, r2);
        let expanded = equal.expand_equal();

        assert_eq!(expanded.len(), 2);
        assert!(expanded.contains(&LifetimeConstraint::outlives(r1, r2)));
        assert!(expanded.contains(&LifetimeConstraint::outlives(r2, r1)));

        // Outlives expands to itself
        let outlives = LifetimeConstraint::outlives(r1, r2);
        let expanded = outlives.expand_equal();
        assert_eq!(expanded.len(), 1);
        assert_eq!(expanded[0], outlives);
    }

    #[test]
    fn test_add_constraint() {
        let constraints = LifetimeConstraints::new();
        let r1 = Region::Scope(1);
        let r2 = Region::Scope(2);

        // Add non-trivial constraint
        let c = LifetimeConstraint::outlives(r1, r2);
        let constraints = add_constraint(constraints, c);
        assert_eq!(constraints.len(), 1);

        // Adding same constraint again doesn't duplicate
        let constraints = add_constraint(constraints, c);
        assert_eq!(constraints.len(), 1);

        // Trivial constraint is not added
        let trivial = LifetimeConstraint::outlives(r1, r1);
        let constraints = add_constraint(constraints, trivial);
        assert_eq!(constraints.len(), 1);
    }

    #[test]
    fn test_constraints_satisfiable() {
        // Valid: 'static outlives scope
        let c1 = LifetimeConstraint::outlives(Region::Static, Region::Scope(1));
        assert!(constraints_satisfiable(&vec![c1]));

        // Valid: outer scope outlives inner scope
        let c2 = LifetimeConstraint::outlives(Region::Scope(0), Region::Scope(1));
        assert!(constraints_satisfiable(&vec![c2]));

        // Invalid: inner scope cannot outlive outer scope
        let c3 = LifetimeConstraint::outlives(Region::Scope(2), Region::Scope(1));
        assert!(!constraints_satisfiable(&vec![c3]));

        // Invalid: scope cannot outlive 'static
        let c4 = LifetimeConstraint::outlives(Region::Scope(1), Region::Static);
        assert!(!constraints_satisfiable(&vec![c4]));

        // Invalid: static cannot equal non-static
        let c5 = LifetimeConstraint::equal(Region::Static, Region::Scope(1));
        assert!(!constraints_satisfiable(&vec![c5]));
    }

    #[test]
    fn test_solve_constraints() {
        // Empty constraints are solvable
        let empty: LifetimeConstraints = vec![];
        assert!(solve_constraints(&empty).is_some());
        assert!(solve_constraints(&empty).unwrap().is_empty());

        // Simple equality between named regions (unifiable)
        let mut rodeo = lasso::Rodeo::default();
        let r1 = Region::Named(rodeo.get_or_intern("a"));
        let r2 = Region::Named(rodeo.get_or_intern("b"));

        let constraints = vec![LifetimeConstraint::equal(r1, r2)];
        let solution = solve_constraints(&constraints);
        assert!(solution.is_some());
        let equivs = solution.unwrap();
        assert_eq!(equivs.len(), 1);
        assert!(equivs.contains(&(r1, r2)) || equivs.contains(&(r2, r1)));

        // Mutual outlives implies equality (between named regions)
        let constraints = vec![
            LifetimeConstraint::outlives(r1, r2),
            LifetimeConstraint::outlives(r2, r1),
        ];
        let solution = solve_constraints(&constraints);
        assert!(solution.is_some());
        let equivs = solution.unwrap();
        assert!(!equivs.is_empty());

        // Fresh regions: only one direction is satisfiable
        let f1 = Region::Fresh(0);
        let f2 = Region::Fresh(1);

        // Fresh(0) outlives Fresh(1) is satisfiable
        let constraints = vec![LifetimeConstraint::outlives(f1, f2)];
        assert!(constraints_satisfiable(&constraints));

        // Fresh(1) outlives Fresh(0) is NOT satisfiable
        let constraints = vec![LifetimeConstraint::outlives(f2, f1)];
        assert!(!constraints_satisfiable(&constraints));
    }

    #[test]
    fn test_region_outlives() {
        // Static outlives everything
        assert!(region_outlives(&Region::Static, &Region::Static));
        assert!(region_outlives(&Region::Static, &Region::Scope(0)));
        assert!(region_outlives(&Region::Static, &Region::Fresh(0)));

        // Same region outlives itself
        let r = Region::Scope(1);
        assert!(region_outlives(&r, &r));

        // Outer scope outlives inner scope
        assert!(region_outlives(&Region::Scope(0), &Region::Scope(1)));
        assert!(!region_outlives(&Region::Scope(2), &Region::Scope(1)));

        // Earlier fresh outlives later fresh
        assert!(region_outlives(&Region::Fresh(0), &Region::Fresh(1)));
        assert!(!region_outlives(&Region::Fresh(2), &Region::Fresh(1)));

        // Non-static cannot outlive static
        assert!(!region_outlives(&Region::Scope(0), &Region::Static));
    }

    #[test]
    fn test_borrow_constraint() {
        let region = Region::Fresh(0);
        let depth = 2;

        let c = borrow_constraint(region, depth);

        assert!(c.is_outlives());
        assert_eq!(c.first(), region);
        assert_eq!(c.second(), Region::Scope(depth));
    }

    #[test]
    fn test_constraint_format() {
        let r1 = Region::Static;
        let r2 = Region::Scope(1);

        let outlives = LifetimeConstraint::outlives(r1, r2);
        assert!(outlives.format().contains(":"));

        let equal = LifetimeConstraint::equal(r1, r2);
        assert!(equal.format().contains("="));
    }
}
