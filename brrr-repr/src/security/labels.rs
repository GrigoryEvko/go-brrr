//! Security labels and DLM primitives for information flow control
//!
//! Mirrors F* SecurityTypes.fsti: confidentiality, integrity, sec_label
//!
//! Implements a two-point lattice for both confidentiality and integrity:
//! - Confidentiality: Public <= Secret (can flow to more restricted)
//! - Integrity: Untrusted <= Trusted (inverted for flow - trusted can't go to untrusted)
//!
//! The DLM (Decentralized Label Model) provides fine-grained access control
//! with owner/reader policies that compose via join.

use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

use super::taint::TaintSet;

/// Principal - security actor (user, role, process)
/// Uses string interning for efficient comparison and storage
pub type Principal = Spur;

// ============================================================================
// Confidentiality Lattice
// ============================================================================

/// Confidentiality level - two-point lattice
/// Maps to F*: type confidentiality = CPublic | CSecret
///
/// Lattice structure: Public <= Secret
/// - Public: no restrictions on reading
/// - Secret: restricted access
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[repr(u8)]
pub enum Confidentiality {
    /// Anyone can read - bottom of lattice
    #[default]
    Public = 0,
    /// Restricted access - top of lattice
    Secret = 1,
}

impl Confidentiality {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "public" | "Public" | "pub" => Some(Self::Public),
            "secret" | "Secret" | "sec" => Some(Self::Secret),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Public => "public",
            Self::Secret => "secret",
        }
    }

    /// Lattice join (least upper bound)
    /// Public join X = X, Secret join X = Secret
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Secret, _) | (_, Self::Secret) => Self::Secret,
            (Self::Public, Self::Public) => Self::Public,
        }
    }

    /// Lattice meet (greatest lower bound)
    /// Secret meet X = X, Public meet X = Public
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Public, _) | (_, Self::Public) => Self::Public,
            (Self::Secret, Self::Secret) => Self::Secret,
        }
    }

    /// Lattice ordering: Public <= Secret
    /// Returns true if self can flow to other (self is at most as secret as other)
    pub const fn leq(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Public, _) | (Self::Secret, Self::Secret)
        )
    }

    /// Check if this is public
    pub const fn is_public(self) -> bool {
        matches!(self, Self::Public)
    }

    /// Check if this is secret
    pub const fn is_secret(self) -> bool {
        matches!(self, Self::Secret)
    }
}

// ============================================================================
// Integrity Lattice
// ============================================================================

/// Integrity level - two-point lattice
/// Maps to F*: type integrity = IUntrusted | ITrusted
///
/// Lattice structure: Untrusted <= Trusted
/// - Untrusted: from external/tainted source
/// - Trusted: from verified/sanitized source
///
/// NOTE: For information flow, integrity flows OPPOSITE to confidentiality:
/// trusted data should not flow to untrusted sinks without validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[repr(u8)]
pub enum Integrity {
    /// From untrusted source (tainted) - bottom of lattice
    #[default]
    Untrusted = 0,
    /// From trusted source (sanitized) - top of lattice
    Trusted = 1,
}

impl Integrity {
    /// Parse from text format
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "untrusted" | "Untrusted" | "tainted" => Some(Self::Untrusted),
            "trusted" | "Trusted" | "sanitized" => Some(Self::Trusted),
            _ => None,
        }
    }

    /// Format to text
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Untrusted => "untrusted",
            Self::Trusted => "trusted",
        }
    }

    /// Lattice join (least upper bound) - untrusted absorbs
    /// Untrusted join X = Untrusted, Trusted join Trusted = Trusted
    ///
    /// Note: For integrity, mixing with untrusted data taints the result
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Trusted, Self::Trusted) => Self::Trusted,
            _ => Self::Untrusted,
        }
    }

    /// Lattice meet (greatest lower bound)
    /// Trusted meet X = X, Untrusted meet Untrusted = Untrusted
    pub const fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Untrusted, Self::Untrusted) => Self::Untrusted,
            _ => Self::Trusted,
        }
    }

    /// Lattice ordering: Untrusted <= Trusted
    /// Returns true if self is at most as trusted as other
    pub const fn leq(self, other: Self) -> bool {
        matches!(
            (self, other),
            (Self::Untrusted, _) | (Self::Trusted, Self::Trusted)
        )
    }

    /// Check if this is untrusted
    pub const fn is_untrusted(self) -> bool {
        matches!(self, Self::Untrusted)
    }

    /// Check if this is trusted
    pub const fn is_trusted(self) -> bool {
        matches!(self, Self::Trusted)
    }
}

// ============================================================================
// DLM (Decentralized Label Model)
// ============================================================================

/// DLM Policy - owner with reader set
///
/// A policy specifies who owns the data and who can read it.
/// Empty readers set means "public" (anyone can read if owner permits).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    /// Who owns the data
    pub owner: Principal,
    /// Who can read (if owner permits). Empty = public.
    pub readers: HashSet<Principal>,
}

impl Policy {
    /// Create a policy with explicit readers
    pub fn new(owner: Principal, readers: impl IntoIterator<Item = Principal>) -> Self {
        Self {
            owner,
            readers: readers.into_iter().collect(),
        }
    }

    /// Create a policy that allows everyone to read (empty readers = public)
    pub fn public(owner: Principal) -> Self {
        Self {
            owner,
            readers: HashSet::new(),
        }
    }

    /// Create a policy that only the owner can read
    pub fn private(owner: Principal) -> Self {
        let mut readers = HashSet::new();
        readers.insert(owner);
        Self { owner, readers }
    }

    /// Check if a principal can read under this policy
    pub fn can_read(&self, principal: &Principal) -> bool {
        // Empty readers = public (anyone can read)
        // Otherwise, must be owner or in readers set
        self.readers.is_empty() || self.readers.contains(principal) || *principal == self.owner
    }

    /// Check if this is a public policy (no reader restrictions)
    pub fn is_public(&self) -> bool {
        self.readers.is_empty()
    }
}

/// DLM Label - join of multiple policies
///
/// A label is a set of policies that must all be satisfied.
/// The join of two labels is the union of their policies.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct DlmLabel {
    /// Set of policies that must all be satisfied
    pub policies: Vec<Policy>,
}

impl DlmLabel {
    /// Empty label (most permissive - no policies to satisfy)
    pub const BOTTOM: Self = Self {
        policies: Vec::new(),
    };

    /// Create from a list of policies
    pub fn new(policies: Vec<Policy>) -> Self {
        Self { policies }
    }

    /// Create a single-policy label
    pub fn single(policy: Policy) -> Self {
        Self {
            policies: vec![policy],
        }
    }

    /// Join two labels (union of policies)
    /// The result is more restrictive - all policies must be satisfied.
    pub fn join(&self, other: &Self) -> Self {
        let mut policies = self.policies.clone();
        policies.extend(other.policies.iter().cloned());
        Self { policies }
    }

    /// Check if this label flows to other (this is less or equally restrictive)
    ///
    /// Flows-to means: all our policies are satisfied by other's policies.
    /// This is conservative - if in doubt, it returns false.
    pub fn flows_to(&self, other: &Self) -> bool {
        // Empty label flows to anything
        if self.policies.is_empty() {
            return true;
        }

        // Each of our policies must be "covered" by some policy in other
        self.policies.iter().all(|p1| {
            other.policies.iter().any(|p2| {
                // Same owner and our readers are subset of their readers
                p1.owner == p2.owner && p1.readers.is_subset(&p2.readers)
            })
        })
    }

    /// Check if a principal can read under all policies in this label
    pub fn can_read(&self, principal: &Principal) -> bool {
        self.policies.iter().all(|p| p.can_read(principal))
    }

    /// Check if this is the bottom label (no policies)
    pub fn is_bottom(&self) -> bool {
        self.policies.is_empty()
    }
}

// ============================================================================
// Complete Security Label
// ============================================================================

/// Complete security label combining confidentiality, integrity, and DLM
/// Maps to F*: noeq type sec_label = { confidentiality; integrity; taints }
///
/// Information flow rules:
/// - Confidentiality: self.conf <= other.conf (can flow to higher secrecy)
/// - Integrity: other.integ <= self.integ (trusted can't flow to untrusted)
/// - DLM: self.dlm flows_to other.dlm
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct SecurityLabel {
    /// Confidentiality component
    pub confidentiality: Confidentiality,
    /// Integrity component
    pub integrity: Integrity,
    /// DLM label for fine-grained access control (optional)
    pub dlm: Option<DlmLabel>,
    /// Taint set for fine-grained vulnerability tracking
    ///
    /// While `integrity` tracks binary trusted/untrusted status,
    /// `taints` tracks which specific vulnerability categories
    /// (SQLi, XSS, etc.) the data may enable.
    pub taints: TaintSet,
}

impl SecurityLabel {
    /// Public trusted - bottom of the lattice (most permissive)
    /// Data with this label can flow anywhere.
    #[must_use]
    pub fn public_trusted() -> Self {
        Self {
            confidentiality: Confidentiality::Public,
            integrity: Integrity::Trusted,
            dlm: None,
            taints: TaintSet::empty(),
        }
    }

    /// Secret untrusted - top of the lattice (most restrictive)
    /// Data with this label cannot flow to most places.
    #[must_use]
    pub fn secret_untrusted() -> Self {
        Self {
            confidentiality: Confidentiality::Secret,
            integrity: Integrity::Untrusted,
            dlm: None,
            taints: TaintSet::empty(),
        }
    }

    /// Public untrusted - typical for user input (tainted)
    #[must_use]
    pub fn public_untrusted() -> Self {
        Self {
            confidentiality: Confidentiality::Public,
            integrity: Integrity::Untrusted,
            dlm: None,
            taints: TaintSet::empty(),
        }
    }

    /// Secret trusted - typical for internal secrets
    #[must_use]
    pub fn secret_trusted() -> Self {
        Self {
            confidentiality: Confidentiality::Secret,
            integrity: Integrity::Trusted,
            dlm: None,
            taints: TaintSet::empty(),
        }
    }

    /// Create a new label without DLM or taints
    #[must_use]
    pub fn new(conf: Confidentiality, integ: Integrity) -> Self {
        Self {
            confidentiality: conf,
            integrity: integ,
            dlm: None,
            taints: TaintSet::empty(),
        }
    }

    /// Create a label with DLM
    pub fn with_dlm(conf: Confidentiality, integ: Integrity, dlm: DlmLabel) -> Self {
        Self {
            confidentiality: conf,
            integrity: integ,
            dlm: Some(dlm),
            taints: TaintSet::empty(),
        }
    }

    /// Create a label with taints
    pub fn with_taints(conf: Confidentiality, integ: Integrity, taints: TaintSet) -> Self {
        Self {
            confidentiality: conf,
            integrity: integ,
            dlm: None,
            taints,
        }
    }

    /// Create a full label with all components
    pub fn full(
        conf: Confidentiality,
        integ: Integrity,
        dlm: Option<DlmLabel>,
        taints: TaintSet,
    ) -> Self {
        Self {
            confidentiality: conf,
            integrity: integ,
            dlm,
            taints,
        }
    }

    /// Join two labels (least upper bound)
    /// Results in a label that is at least as restrictive as both inputs.
    pub fn join(&self, other: &Self) -> Self {
        Self {
            confidentiality: self.confidentiality.join(other.confidentiality),
            integrity: self.integrity.join(other.integrity),
            dlm: match (&self.dlm, &other.dlm) {
                (Some(d1), Some(d2)) => Some(d1.join(d2)),
                (Some(d), None) | (None, Some(d)) => Some(d.clone()),
                (None, None) => None,
            },
            taints: self.taints.union(&other.taints),
        }
    }

    /// Meet two labels (greatest lower bound)
    /// Results in a label that is at most as restrictive as both inputs.
    pub fn meet(&self, other: &Self) -> Self {
        Self {
            confidentiality: self.confidentiality.meet(other.confidentiality),
            integrity: self.integrity.meet(other.integrity),
            // For meet, DLM is intersection (both must allow) - complex, so None for now
            dlm: None,
            taints: self.taints.intersection(&other.taints),
        }
    }

    /// Check if information can flow from self to other
    ///
    /// Flow rules (standard lattice model):
    /// - Confidentiality: self <= other (low to high OK, secret cannot leak to public)
    /// - Integrity: self <= other (low to high OK, untrusted data can be sanitized)
    /// - DLM: self flows_to other (policies satisfied)
    ///
    /// Note: This models information flow in the lattice. Practical systems may
    /// require explicit sanitization at upgrade points for integrity.
    pub fn flows_to(&self, other: &Self) -> bool {
        // Confidentiality: public can flow to secret, but not vice versa
        let conf_ok = self.confidentiality.leq(other.confidentiality);

        // Integrity: trusted cannot flow to untrusted (Biba "no write down")
        // High integrity (Trusted) cannot flow to low integrity (Untrusted)
        // This means self.integrity <= other.integrity
        let integ_ok = self.integrity.leq(other.integrity);

        // DLM: if present, must also satisfy flows_to
        let dlm_ok = match (&self.dlm, &other.dlm) {
            (Some(d1), Some(d2)) => d1.flows_to(d2),
            (Some(_), None) => false, // Has restrictions, target has none
            (None, _) => true,        // No DLM restrictions
        };

        conf_ok && integ_ok && dlm_ok
    }

    /// Check if this is the bottom label (public trusted, no DLM, no taints)
    pub fn is_bottom(&self) -> bool {
        self.confidentiality.is_public()
            && self.integrity.is_trusted()
            && self.dlm.as_ref().is_none_or(DlmLabel::is_bottom)
            && self.taints.is_empty()
    }

    /// Check if this is the top label (secret untrusted)
    pub fn is_top(&self) -> bool {
        self.confidentiality.is_secret() && self.integrity.is_untrusted()
    }

    /// Check if this label has any taints
    pub fn has_taints(&self) -> bool {
        !self.taints.is_empty()
    }

    /// Get a reference to the taints
    pub fn taints(&self) -> &TaintSet {
        &self.taints
    }

    /// Format to text
    pub fn as_str(&self) -> String {
        format!(
            "{}:{}",
            self.confidentiality.as_str(),
            self.integrity.as_str()
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_confidentiality_lattice() {
        // Ordering
        assert!(Confidentiality::Public.leq(Confidentiality::Public));
        assert!(Confidentiality::Public.leq(Confidentiality::Secret));
        assert!(!Confidentiality::Secret.leq(Confidentiality::Public));
        assert!(Confidentiality::Secret.leq(Confidentiality::Secret));

        // Join
        assert_eq!(
            Confidentiality::Public.join(Confidentiality::Public),
            Confidentiality::Public
        );
        assert_eq!(
            Confidentiality::Public.join(Confidentiality::Secret),
            Confidentiality::Secret
        );
        assert_eq!(
            Confidentiality::Secret.join(Confidentiality::Public),
            Confidentiality::Secret
        );
        assert_eq!(
            Confidentiality::Secret.join(Confidentiality::Secret),
            Confidentiality::Secret
        );

        // Meet
        assert_eq!(
            Confidentiality::Public.meet(Confidentiality::Public),
            Confidentiality::Public
        );
        assert_eq!(
            Confidentiality::Public.meet(Confidentiality::Secret),
            Confidentiality::Public
        );
        assert_eq!(
            Confidentiality::Secret.meet(Confidentiality::Secret),
            Confidentiality::Secret
        );
    }

    #[test]
    fn test_integrity_lattice() {
        // Ordering
        assert!(Integrity::Untrusted.leq(Integrity::Untrusted));
        assert!(Integrity::Untrusted.leq(Integrity::Trusted));
        assert!(!Integrity::Trusted.leq(Integrity::Untrusted));
        assert!(Integrity::Trusted.leq(Integrity::Trusted));

        // Join (untrusted absorbs - mixing taints)
        assert_eq!(
            Integrity::Trusted.join(Integrity::Trusted),
            Integrity::Trusted
        );
        assert_eq!(
            Integrity::Trusted.join(Integrity::Untrusted),
            Integrity::Untrusted
        );
        assert_eq!(
            Integrity::Untrusted.join(Integrity::Trusted),
            Integrity::Untrusted
        );
        assert_eq!(
            Integrity::Untrusted.join(Integrity::Untrusted),
            Integrity::Untrusted
        );

        // Meet
        assert_eq!(
            Integrity::Trusted.meet(Integrity::Trusted),
            Integrity::Trusted
        );
        assert_eq!(
            Integrity::Trusted.meet(Integrity::Untrusted),
            Integrity::Trusted
        );
        assert_eq!(
            Integrity::Untrusted.meet(Integrity::Untrusted),
            Integrity::Untrusted
        );
    }

    #[test]
    fn test_security_label_flow() {
        let public_trusted = SecurityLabel::public_trusted();
        let public_untrusted = SecurityLabel::public_untrusted();
        let secret_trusted = SecurityLabel::secret_trusted();
        let secret_untrusted = SecurityLabel::secret_untrusted();

        // Public trusted can flow to same or higher confidentiality AND same or lower integrity
        // Since Trusted > Untrusted, trusted cannot flow to untrusted
        assert!(public_trusted.flows_to(&public_trusted));
        assert!(public_trusted.flows_to(&secret_trusted));
        // Cannot flow to untrusted (would lose integrity)
        assert!(!public_trusted.flows_to(&public_untrusted));
        assert!(!public_trusted.flows_to(&secret_untrusted));

        // Secret cannot flow to public (confidentiality violation)
        assert!(!secret_trusted.flows_to(&public_trusted));
        assert!(!secret_trusted.flows_to(&public_untrusted));
        assert!(!secret_trusted.flows_to(&secret_untrusted));

        // Untrusted can flow to trusted (can be sanitized)
        assert!(public_untrusted.flows_to(&public_trusted));
        assert!(secret_untrusted.flows_to(&secret_trusted));

        // Secret untrusted is top - nothing flows from it except itself
        assert!(secret_untrusted.flows_to(&secret_untrusted));
        assert!(!secret_untrusted.flows_to(&public_trusted));
    }

    #[test]
    fn test_security_label_join() {
        let public_trusted = SecurityLabel::public_trusted();
        let secret_untrusted = SecurityLabel::secret_untrusted();

        // Join produces the least upper bound
        let joined = public_trusted.join(&secret_untrusted);
        assert_eq!(joined.confidentiality, Confidentiality::Secret);
        assert_eq!(joined.integrity, Integrity::Untrusted);

        // Join with self produces equivalent label
        let pt_joined = public_trusted.join(&SecurityLabel::public_trusted());
        assert_eq!(pt_joined.confidentiality, Confidentiality::Public);
        assert_eq!(pt_joined.integrity, Integrity::Trusted);
    }

    #[test]
    fn test_confidentiality_parsing() {
        assert_eq!(
            Confidentiality::from_str("public"),
            Some(Confidentiality::Public)
        );
        assert_eq!(
            Confidentiality::from_str("secret"),
            Some(Confidentiality::Secret)
        );
        assert_eq!(Confidentiality::from_str("invalid"), None);
    }

    #[test]
    fn test_integrity_parsing() {
        assert_eq!(
            Integrity::from_str("untrusted"),
            Some(Integrity::Untrusted)
        );
        assert_eq!(Integrity::from_str("trusted"), Some(Integrity::Trusted));
        assert_eq!(Integrity::from_str("tainted"), Some(Integrity::Untrusted));
        assert_eq!(Integrity::from_str("invalid"), None);
    }

    #[test]
    fn test_lattice_laws() {
        let confs = [Confidentiality::Public, Confidentiality::Secret];
        let integs = [Integrity::Untrusted, Integrity::Trusted];

        // Verify lattice laws for confidentiality
        for &a in &confs {
            for &b in &confs {
                // Join is commutative
                assert_eq!(a.join(b), b.join(a));
                // Meet is commutative
                assert_eq!(a.meet(b), b.meet(a));
                // Absorption: a join (a meet b) = a
                assert_eq!(a.join(a.meet(b)), a);
                // Absorption: a meet (a join b) = a
                assert_eq!(a.meet(a.join(b)), a);

                for &c in &confs {
                    // Join associativity
                    assert_eq!(a.join(b).join(c), a.join(b.join(c)));
                    // Meet associativity
                    assert_eq!(a.meet(b).meet(c), a.meet(b.meet(c)));
                }
            }
        }

        // Verify lattice laws for integrity
        for &a in &integs {
            for &b in &integs {
                assert_eq!(a.join(b), b.join(a));
                assert_eq!(a.meet(b), b.meet(a));
                assert_eq!(a.join(a.meet(b)), a);
                assert_eq!(a.meet(a.join(b)), a);
            }
        }
    }

    #[test]
    fn test_bottom_top() {
        assert!(SecurityLabel::public_trusted().is_bottom());
        assert!(!SecurityLabel::public_trusted().is_top());
        assert!(SecurityLabel::secret_untrusted().is_top());
        assert!(!SecurityLabel::secret_untrusted().is_bottom());
    }

    #[test]
    fn test_dlm_label_empty() {
        let empty = DlmLabel::BOTTOM;
        assert!(empty.is_bottom());

        // Empty flows to anything
        let non_empty = DlmLabel::new(vec![]);
        assert!(empty.flows_to(&non_empty));
    }
}
