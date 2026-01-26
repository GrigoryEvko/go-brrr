//! Cross-language boundary issue detection
//!
//! Mirrors F* synthesis_part9.tex boundary_issue type (lines 569-586).
//!
//! # Language Boundary Problems
//!
//! When code crosses language boundaries (FFI, RPC, serialization),
//! several classes of issues can occur:
//!
//! - **Null crossing**: Null pointers from C entering Rust
//! - **Ownership unclear**: Who is responsible for deallocation?
//! - **Type mismatch**: Different memory representations
//! - **Tainted crossing**: Untrusted data crossing security boundaries
//! - **Lifetime mismatch**: Dangling references across boundaries
//! - **Thread safety**: Data races in concurrent FFI
//! - **Serialization unsafe**: Types that cannot safely serialize
//!
//! # FFI Safety Checking
//!
//! The `check_ffi_safe` function analyzes types for FFI compatibility,
//! reporting all potential issues that could occur at language boundaries.

use serde::{Deserialize, Serialize};
use std::fmt;

use crate::types::BrrrType;

// ============================================================================
// NodeId
// ============================================================================

/// Node identifier in the program graph.
///
/// Used to locate issues within the code structure.
/// Wraps a u32 for efficient storage and comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct NodeId(pub u32);

impl NodeId {
    /// Create a new node ID.
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value.
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Invalid/unknown node location.
    pub const UNKNOWN: Self = Self(u32::MAX);
}

impl From<u32> for NodeId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Self::UNKNOWN {
            write!(f, "<unknown>")
        } else {
            write!(f, "node#{}", self.0)
        }
    }
}

// ============================================================================
// NodeIdCounter
// ============================================================================

/// Counter for generating fresh node IDs.
///
/// Provides monotonically increasing unique identifiers for CPG nodes.
/// Thread-safe via atomic operations.
#[derive(Debug)]
pub struct NodeIdCounter {
    next: std::sync::atomic::AtomicU32,
}

impl NodeIdCounter {
    /// Create a new counter starting at 0.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next: std::sync::atomic::AtomicU32::new(0),
        }
    }

    /// Create a counter starting at a specific value.
    #[must_use]
    pub const fn starting_at(start: u32) -> Self {
        Self {
            next: std::sync::atomic::AtomicU32::new(start),
        }
    }

    /// Generate the next fresh node ID.
    ///
    /// This is thread-safe and guarantees unique IDs across threads.
    pub fn fresh(&self) -> NodeId {
        let id = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        NodeId(id)
    }

    /// Get the current counter value without incrementing.
    #[must_use]
    pub fn current(&self) -> u32 {
        self.next.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Reset the counter to a specific value.
    ///
    /// Use with caution - may cause duplicate IDs if previously generated
    /// IDs are still in use.
    pub fn reset(&self, value: u32) {
        self.next.store(value, std::sync::atomic::Ordering::Relaxed);
    }
}

impl Default for NodeIdCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for NodeIdCounter {
    /// Clone creates a new counter starting at the current value.
    ///
    /// Note: The cloned counter will generate the same IDs as the original
    /// if used from this point forward. Use `starting_at(original.current())`
    /// if you need independent counters.
    fn clone(&self) -> Self {
        Self::starting_at(self.current())
    }
}

// ============================================================================
// TaintSource
// ============================================================================

/// Source of tainted data at language boundaries.
///
/// Represents where untrusted data originates before crossing
/// a language boundary. Different from `TaintKind` which represents
/// the vulnerability category.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaintSource {
    /// User-provided input (CLI args, stdin, form data)
    UserInput,
    /// Network data (HTTP requests, socket reads)
    Network,
    /// File system data
    FileSystem,
    /// Environment variables
    Environment,
    /// Database query results
    Database,
    /// Inter-process communication
    Ipc,
    /// Deserialized data from untrusted source
    Deserialization,
    /// Custom taint source with description
    Custom(String),
}

impl TaintSource {
    /// Returns a human-readable name for the taint source.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::UserInput => "user input",
            Self::Network => "network",
            Self::FileSystem => "file system",
            Self::Environment => "environment variable",
            Self::Database => "database",
            Self::Ipc => "IPC",
            Self::Deserialization => "deserialization",
            Self::Custom(s) => s.as_str(),
        }
    }

    /// Get discriminant for binary encoding.
    #[must_use]
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::UserInput => 0,
            Self::Network => 1,
            Self::FileSystem => 2,
            Self::Environment => 3,
            Self::Database => 4,
            Self::Ipc => 5,
            Self::Deserialization => 6,
            Self::Custom(_) => 7,
        }
    }
}

impl Default for TaintSource {
    fn default() -> Self {
        Self::UserInput
    }
}

impl fmt::Display for TaintSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ============================================================================
// BoundaryIssueSeverity
// ============================================================================

/// Severity level for boundary issues.
///
/// Ordered from most severe (Critical) to least severe (Low).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum BoundaryIssueSeverity {
    /// Critical: Immediate memory safety or security violation
    /// Examples: null dereference, use-after-free, remote code execution
    Critical = 3,
    /// High: Likely to cause crashes or security vulnerabilities
    /// Examples: ownership confusion, tainted data crossing
    High = 2,
    /// Medium: Potential issues under certain conditions
    /// Examples: type representation mismatches, lifetime concerns
    Medium = 1,
    /// Low: Code smell or potential future problem
    /// Examples: suboptimal patterns, missing annotations
    Low = 0,
}

impl BoundaryIssueSeverity {
    /// All severity levels from highest to lowest.
    pub const ALL: &'static [Self] = &[Self::Critical, Self::High, Self::Medium, Self::Low];

    /// Returns a human-readable name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Critical => "Critical",
            Self::High => "High",
            Self::Medium => "Medium",
            Self::Low => "Low",
        }
    }

    /// Returns a short symbol for display.
    #[must_use]
    pub const fn symbol(self) -> &'static str {
        match self {
            Self::Critical => "[CRIT]",
            Self::High => "[HIGH]",
            Self::Medium => "[MED]",
            Self::Low => "[LOW]",
        }
    }

    /// Check if this is a blocking severity (Critical or High).
    #[must_use]
    pub const fn is_blocking(self) -> bool {
        matches!(self, Self::Critical | Self::High)
    }
}

impl Default for BoundaryIssueSeverity {
    fn default() -> Self {
        Self::Medium
    }
}

impl fmt::Display for BoundaryIssueSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ============================================================================
// BoundaryIssue
// ============================================================================

/// Cross-language boundary issue.
///
/// Mirrors F* synthesis_part9.tex:
/// ```fstar
/// type boundary_issue =
///   | IssueNullCrossing : loc:node_id -> boundary_issue
///   | IssueOwnershipUnclear : loc:node_id -> boundary_issue
///   | IssueTypeMismatch : expected:string -> actual:string -> loc:node_id -> boundary_issue
///   | IssueTaintedCrossing : source:taint_source -> loc:node_id -> boundary_issue
///   | IssueLifetimeMismatch : loc:node_id -> boundary_issue
///   | IssueThreadSafety : loc:node_id -> boundary_issue
///   | IssueSerializationUnsafe : type_:string -> loc:node_id -> boundary_issue
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum BoundaryIssue {
    /// Null pointer crossing from C/C++ into Rust.
    ///
    /// Rust's Option<&T> is not null, but C pointers can be.
    /// This is a critical issue that can cause undefined behavior.
    NullCrossing {
        /// Location in the program graph
        loc: NodeId,
    },

    /// Ownership of memory is unclear at boundary.
    ///
    /// Who is responsible for freeing the memory?
    /// Common with raw pointers passed between languages.
    OwnershipUnclear {
        /// Location in the program graph
        loc: NodeId,
    },

    /// Type representation mismatch between languages.
    ///
    /// Examples:
    /// - C's int vs Rust's i32 on different platforms
    /// - Different struct layouts due to padding
    /// - Enum representation differences
    TypeMismatch {
        /// Expected type representation
        expected: String,
        /// Actual type representation
        actual: String,
        /// Location in the program graph
        loc: NodeId,
    },

    /// Tainted (untrusted) data crossing security boundary.
    ///
    /// Data from untrusted sources crossing into trusted code
    /// without proper validation or sanitization.
    TaintedCrossing {
        /// Source of the tainted data
        source: TaintSource,
        /// Location in the program graph
        loc: NodeId,
    },

    /// Lifetime mismatch causing potential dangling references.
    ///
    /// When a reference outlives the data it points to,
    /// or when lifetime guarantees differ between languages.
    LifetimeMismatch {
        /// Location in the program graph
        loc: NodeId,
    },

    /// Thread safety issue at boundary.
    ///
    /// Data races possible when concurrent access patterns
    /// differ between languages (e.g., Rust's Send/Sync vs C's threading).
    ThreadSafety {
        /// Location in the program graph
        loc: NodeId,
    },

    /// Type cannot be safely serialized across boundary.
    ///
    /// Types containing pointers, file handles, or other
    /// non-serializable data cannot cross process/machine boundaries.
    SerializationUnsafe {
        /// The type that is unsafe to serialize
        type_name: String,
        /// Location in the program graph
        loc: NodeId,
    },

    /// Shared reference crosses FFI boundary unsafely.
    ///
    /// When a shared reference (`&T`) is passed to foreign code,
    /// the aliasing and lifetime guarantees may be violated.
    /// Foreign code might hold the reference longer than its lifetime
    /// or mutate through it unexpectedly.
    SharedRefUnsafe {
        /// The Rust type being referenced
        rust_type: String,
        /// The foreign type it's being passed as
        foreign_type: String,
        /// Location in the program graph
        loc: NodeId,
    },
}

impl BoundaryIssue {
    /// Create a null crossing issue.
    #[must_use]
    pub const fn null_crossing(loc: NodeId) -> Self {
        Self::NullCrossing { loc }
    }

    /// Create an ownership unclear issue.
    #[must_use]
    pub const fn ownership_unclear(loc: NodeId) -> Self {
        Self::OwnershipUnclear { loc }
    }

    /// Create a type mismatch issue.
    #[must_use]
    pub fn type_mismatch(expected: impl Into<String>, actual: impl Into<String>, loc: NodeId) -> Self {
        Self::TypeMismatch {
            expected: expected.into(),
            actual: actual.into(),
            loc,
        }
    }

    /// Create a tainted crossing issue.
    #[must_use]
    pub const fn tainted_crossing(source: TaintSource, loc: NodeId) -> Self {
        Self::TaintedCrossing { source, loc }
    }

    /// Create a lifetime mismatch issue.
    #[must_use]
    pub const fn lifetime_mismatch(loc: NodeId) -> Self {
        Self::LifetimeMismatch { loc }
    }

    /// Create a thread safety issue.
    #[must_use]
    pub const fn thread_safety(loc: NodeId) -> Self {
        Self::ThreadSafety { loc }
    }

    /// Create a serialization unsafe issue.
    #[must_use]
    pub fn serialization_unsafe(type_name: impl Into<String>, loc: NodeId) -> Self {
        Self::SerializationUnsafe {
            type_name: type_name.into(),
            loc,
        }
    }

    /// Create a shared reference unsafe issue.
    #[must_use]
    pub fn shared_ref_unsafe(
        rust_type: impl Into<String>,
        foreign_type: impl Into<String>,
        loc: NodeId,
    ) -> Self {
        Self::SharedRefUnsafe {
            rust_type: rust_type.into(),
            foreign_type: foreign_type.into(),
            loc,
        }
    }

    /// Get discriminant for binary encoding.
    #[must_use]
    pub const fn discriminant(&self) -> u8 {
        match self {
            Self::NullCrossing { .. } => 0,
            Self::OwnershipUnclear { .. } => 1,
            Self::TypeMismatch { .. } => 2,
            Self::TaintedCrossing { .. } => 3,
            Self::LifetimeMismatch { .. } => 4,
            Self::ThreadSafety { .. } => 5,
            Self::SerializationUnsafe { .. } => 6,
            Self::SharedRefUnsafe { .. } => 7,
        }
    }
}

/// Get the severity of a boundary issue.
///
/// Maps each issue type to its severity level based on
/// potential impact on memory safety and security.
#[must_use]
pub fn severity(issue: &BoundaryIssue) -> BoundaryIssueSeverity {
    match issue {
        // Critical: Immediate memory safety violations
        BoundaryIssue::NullCrossing { .. } => BoundaryIssueSeverity::Critical,

        // High: Likely memory or security issues
        BoundaryIssue::OwnershipUnclear { .. } => BoundaryIssueSeverity::High,
        BoundaryIssue::TaintedCrossing { .. } => BoundaryIssueSeverity::High,
        BoundaryIssue::LifetimeMismatch { .. } => BoundaryIssueSeverity::High,
        BoundaryIssue::SharedRefUnsafe { .. } => BoundaryIssueSeverity::High,

        // Medium: Potential issues under certain conditions
        BoundaryIssue::TypeMismatch { .. } => BoundaryIssueSeverity::Medium,
        BoundaryIssue::ThreadSafety { .. } => BoundaryIssueSeverity::Medium,
        BoundaryIssue::SerializationUnsafe { .. } => BoundaryIssueSeverity::Medium,
    }
}

/// Get the location of a boundary issue.
#[must_use]
pub const fn issue_location(issue: &BoundaryIssue) -> NodeId {
    match issue {
        BoundaryIssue::NullCrossing { loc }
        | BoundaryIssue::OwnershipUnclear { loc }
        | BoundaryIssue::TypeMismatch { loc, .. }
        | BoundaryIssue::TaintedCrossing { loc, .. }
        | BoundaryIssue::LifetimeMismatch { loc }
        | BoundaryIssue::ThreadSafety { loc }
        | BoundaryIssue::SerializationUnsafe { loc, .. }
        | BoundaryIssue::SharedRefUnsafe { loc, .. } => *loc,
    }
}

/// Generate a human-readable description of a boundary issue.
#[must_use]
pub fn describe_issue(issue: &BoundaryIssue) -> String {
    match issue {
        BoundaryIssue::NullCrossing { loc } => {
            format!(
                "Null pointer may cross FFI boundary at {loc}. \
                 C/C++ null pointers are undefined behavior in Rust. \
                 Use Option<NonNull<T>> or explicit null checks."
            )
        }
        BoundaryIssue::OwnershipUnclear { loc } => {
            format!(
                "Memory ownership unclear at FFI boundary at {loc}. \
                 It is ambiguous which language is responsible for deallocation. \
                 Document ownership transfer or use explicit lifetime annotations."
            )
        }
        BoundaryIssue::TypeMismatch { expected, actual, loc } => {
            format!(
                "Type representation mismatch at {loc}: expected '{expected}', got '{actual}'. \
                 Different languages may use different memory layouts for this type."
            )
        }
        BoundaryIssue::TaintedCrossing { source, loc } => {
            format!(
                "Tainted data from {source} crosses security boundary at {loc}. \
                 Validate and sanitize data before crossing trust boundaries."
            )
        }
        BoundaryIssue::LifetimeMismatch { loc } => {
            format!(
                "Lifetime mismatch at FFI boundary at {loc}. \
                 Reference may outlive the data it points to, causing dangling pointers. \
                 Ensure proper lifetime management across language boundaries."
            )
        }
        BoundaryIssue::ThreadSafety { loc } => {
            format!(
                "Thread safety concern at FFI boundary at {loc}. \
                 Concurrent access patterns may differ between languages. \
                 Verify Send/Sync requirements and use appropriate synchronization."
            )
        }
        BoundaryIssue::SerializationUnsafe { type_name, loc } => {
            format!(
                "Type '{type_name}' at {loc} cannot be safely serialized. \
                 Contains pointers, handles, or other non-portable data. \
                 Use a proper serialization format for cross-boundary communication."
            )
        }
        BoundaryIssue::SharedRefUnsafe { rust_type, foreign_type, loc } => {
            format!(
                "Shared reference '&{rust_type}' passed as '{foreign_type}' at {loc} is unsafe. \
                 Foreign code may hold the reference beyond its lifetime or mutate through it. \
                 Consider using raw pointers with explicit lifetime documentation."
            )
        }
    }
}

impl fmt::Display for BoundaryIssue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sev = severity(self);
        write!(f, "{} {}", sev.symbol(), describe_issue(self))
    }
}

// ============================================================================
// FfiSafeType
// ============================================================================

/// Result of FFI safety check for a type.
///
/// Either the type is safe for FFI, or it has one or more issues
/// that need to be addressed before it can safely cross boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FfiSafeType {
    /// Type is safe for FFI boundary crossing
    Safe,
    /// Type has issues that prevent safe FFI usage
    Unsafe(Vec<BoundaryIssue>),
}

impl FfiSafeType {
    /// Check if the type is safe for FFI.
    #[must_use]
    pub const fn is_safe(&self) -> bool {
        matches!(self, Self::Safe)
    }

    /// Check if the type has issues.
    #[must_use]
    pub const fn is_unsafe(&self) -> bool {
        matches!(self, Self::Unsafe(_))
    }

    /// Get issues if unsafe, None if safe.
    #[must_use]
    pub fn issues(&self) -> Option<&[BoundaryIssue]> {
        match self {
            Self::Safe => None,
            Self::Unsafe(issues) => Some(issues),
        }
    }

    /// Get the highest severity among issues, None if safe.
    #[must_use]
    pub fn max_severity(&self) -> Option<BoundaryIssueSeverity> {
        match self {
            Self::Safe => None,
            Self::Unsafe(issues) => issues.iter().map(severity).max(),
        }
    }

    /// Check if any issue is blocking (Critical or High).
    #[must_use]
    pub fn has_blocking_issues(&self) -> bool {
        self.max_severity()
            .map(|s| s.is_blocking())
            .unwrap_or(false)
    }

    /// Combine with another FFI safety result.
    /// If either is unsafe, the result is unsafe with combined issues.
    #[must_use]
    pub fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Safe, Self::Safe) => Self::Safe,
            (Self::Safe, Self::Unsafe(issues)) | (Self::Unsafe(issues), Self::Safe) => {
                Self::Unsafe(issues)
            }
            (Self::Unsafe(mut issues1), Self::Unsafe(issues2)) => {
                issues1.extend(issues2);
                Self::Unsafe(issues1)
            }
        }
    }
}

impl Default for FfiSafeType {
    fn default() -> Self {
        Self::Safe
    }
}

// ============================================================================
// FFI Safety Checking
// ============================================================================

/// Check if a BrrrType is safe for FFI boundary crossing.
///
/// Analyzes the type structure and reports all potential issues
/// that could occur when passing this type across language boundaries.
///
/// # FFI-Safe Types
///
/// - Primitive numeric types (i8-i64, u8-u64, f32, f64)
/// - `()` (unit/void)
/// - Raw pointers with explicit null handling
/// - `#[repr(C)]` structs with FFI-safe fields
/// - Enums with explicit discriminant
///
/// # FFI-Unsafe Types
///
/// - References (`&T`, `&mut T`) - lifetime cannot be tracked
/// - Trait objects (`dyn Trait`) - vtable layout varies
/// - Closures - captures cannot be represented
/// - Box, Rc, Arc - Rust-specific allocation
/// - String, Vec - Rust-specific layout
/// - Option<T> where T is not a pointer
///
/// # Arguments
///
/// * `ty` - The type to check for FFI safety
///
/// # Returns
///
/// `FfiSafeType::Safe` if the type can safely cross boundaries,
/// or `FfiSafeType::Unsafe` with a list of issues otherwise.
#[must_use]
pub fn check_ffi_safe(ty: &BrrrType) -> FfiSafeType {
    check_ffi_safe_impl(ty, NodeId::UNKNOWN, &mut Vec::new())
}

/// Check FFI safety with a specific location for error reporting.
#[must_use]
pub fn check_ffi_safe_at(ty: &BrrrType, loc: NodeId) -> FfiSafeType {
    check_ffi_safe_impl(ty, loc, &mut Vec::new())
}

/// Internal implementation with visited tracking to handle cycles.
fn check_ffi_safe_impl(ty: &BrrrType, loc: NodeId, issues: &mut Vec<BoundaryIssue>) -> FfiSafeType {
    use crate::types::{PrimKind, WrapperKind, NumericType, IntType, FloatPrec};

    match ty {
        // Primitive types
        BrrrType::Prim(kind) => match kind {
            // Safe: void, bool, char
            PrimKind::Unit | PrimKind::Bool | PrimKind::Char => FfiSafeType::Safe,
            // Never type is fine (function doesn't return)
            PrimKind::Never => FfiSafeType::Safe,
            // String is NOT FFI-safe (Rust-specific layout)
            PrimKind::String => {
                issues.push(BoundaryIssue::serialization_unsafe("String", loc));
                FfiSafeType::Unsafe(issues.clone())
            }
            // Dynamic/Unknown are unsafe
            PrimKind::Dynamic | PrimKind::Unknown => {
                issues.push(BoundaryIssue::type_mismatch("concrete FFI type", "dynamic type", loc));
                FfiSafeType::Unsafe(issues.clone())
            }
        },

        // Numeric types - generally safe
        BrrrType::Numeric(num_ty) => match num_ty {
            // Fixed-width integers are FFI-safe
            NumericType::Int(IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 |
                            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64) => {
                FfiSafeType::Safe
            }
            // 128-bit integers may not be supported on all platforms
            NumericType::Int(IntType::I128 | IntType::U128) => {
                issues.push(BoundaryIssue::type_mismatch(
                    "platform-supported integer",
                    "128-bit integer",
                    loc,
                ));
                FfiSafeType::Unsafe(issues.clone())
            }
            // isize/usize are platform-dependent
            NumericType::Int(IntType::ISize | IntType::USize) => {
                // Safe but worth noting platform dependency
                FfiSafeType::Safe
            }
            // Big integers are not FFI-safe (arbitrary precision)
            NumericType::Int(IntType::IBig) => {
                issues.push(BoundaryIssue::type_mismatch(
                    "fixed-width integer",
                    "arbitrary-precision integer (BigInt)",
                    loc,
                ));
                FfiSafeType::Unsafe(issues.clone())
            }
            // Floats are generally FFI-safe
            NumericType::Float(FloatPrec::F32 | FloatPrec::F64) => FfiSafeType::Safe,
            // f16 may not be supported
            NumericType::Float(FloatPrec::F16) => {
                issues.push(BoundaryIssue::type_mismatch(
                    "platform-supported float",
                    "f16 (half precision)",
                    loc,
                ));
                FfiSafeType::Unsafe(issues.clone())
            }
        },

        // Wrapper types
        BrrrType::Wrap(kind, inner) => match kind {
            // Raw pointers are FFI-safe (but may be null!)
            WrapperKind::Raw => {
                issues.push(BoundaryIssue::null_crossing(loc));
                issues.push(BoundaryIssue::ownership_unclear(loc));
                // Still check inner type
                let inner_result = check_ffi_safe_impl(inner, loc, issues);
                if issues.is_empty() {
                    inner_result
                } else {
                    FfiSafeType::Unsafe(issues.clone())
                }
            }
            // References are NOT FFI-safe (lifetimes cannot be tracked)
            WrapperKind::Ref | WrapperKind::RefMut => {
                issues.push(BoundaryIssue::lifetime_mismatch(loc));
                FfiSafeType::Unsafe(issues.clone())
            }
            // Box, Rc, Arc are Rust-specific
            WrapperKind::Box | WrapperKind::Rc | WrapperKind::Arc => {
                issues.push(BoundaryIssue::ownership_unclear(loc));
                issues.push(BoundaryIssue::serialization_unsafe(
                    format!("{kind:?}<...>"),
                    loc,
                ));
                FfiSafeType::Unsafe(issues.clone())
            }
            // Option<ptr> is FFI-safe (niche optimization), but Option<T> is not
            WrapperKind::Option => {
                // Check if inner is a pointer type (niche-optimized)
                if matches!(inner.as_ref(), BrrrType::Wrap(WrapperKind::Raw, _)) {
                    check_ffi_safe_impl(inner, loc, issues)
                } else {
                    issues.push(BoundaryIssue::type_mismatch(
                        "FFI-compatible option",
                        "Option<T> (non-pointer)",
                        loc,
                    ));
                    FfiSafeType::Unsafe(issues.clone())
                }
            }
            // Array (fixed-size) is FFI-safe if element is
            WrapperKind::Array => check_ffi_safe_impl(inner, loc, issues),
            // Slice is NOT FFI-safe (fat pointer)
            WrapperKind::Slice => {
                issues.push(BoundaryIssue::type_mismatch(
                    "thin pointer",
                    "slice (fat pointer with length)",
                    loc,
                ));
                FfiSafeType::Unsafe(issues.clone())
            }
        },

        // Sized arrays are FFI-safe if element type is FFI-safe
        BrrrType::SizedArray(_, inner) => check_ffi_safe_impl(inner, loc, issues),

        // Modal types are not directly FFI-safe
        BrrrType::Modal(_, _) => {
            issues.push(BoundaryIssue::type_mismatch(
                "plain type",
                "modal type",
                loc,
            ));
            FfiSafeType::Unsafe(issues.clone())
        }

        // Result types are not FFI-safe
        BrrrType::Result(_, _) => {
            issues.push(BoundaryIssue::type_mismatch(
                "plain type or error code",
                "Result<T, E>",
                loc,
            ));
            FfiSafeType::Unsafe(issues.clone())
        }

        // Tuples are FFI-safe if all elements are (and repr(C))
        BrrrType::Tuple(elems) => {
            for elem in elems {
                let _ = check_ffi_safe_impl(elem, loc, issues);
            }
            if issues.is_empty() {
                FfiSafeType::Safe
            } else {
                FfiSafeType::Unsafe(issues.clone())
            }
        }

        // Function types: only extern "C" functions are FFI-safe
        BrrrType::Func(func) => {
            // Check all parameter types
            for param in &func.params {
                let _ = check_ffi_safe_impl(&param.ty, loc, issues);
            }
            // Check return type
            let _ = check_ffi_safe_impl(&func.return_type, loc, issues);

            if issues.is_empty() {
                FfiSafeType::Safe
            } else {
                FfiSafeType::Unsafe(issues.clone())
            }
        }

        // Type variables cannot be checked statically
        BrrrType::Var(_) => {
            issues.push(BoundaryIssue::type_mismatch(
                "concrete type",
                "type variable",
                loc,
            ));
            FfiSafeType::Unsafe(issues.clone())
        }

        // Type application: depends on the instantiation
        BrrrType::App(_, _) => {
            issues.push(BoundaryIssue::type_mismatch(
                "monomorphic type",
                "type application",
                loc,
            ));
            FfiSafeType::Unsafe(issues.clone())
        }

        // Named types: need to resolve to check
        BrrrType::Named(_) => {
            // Cannot check without type resolution context
            // Conservative: assume safe (caller should resolve first)
            FfiSafeType::Safe
        }

        // Struct types: check all fields
        BrrrType::Struct(s) => {
            for field in &s.fields {
                let _ = check_ffi_safe_impl(&field.ty, loc, issues);
            }
            if issues.is_empty() {
                FfiSafeType::Safe
            } else {
                FfiSafeType::Unsafe(issues.clone())
            }
        }

        // Enum types: need explicit repr for FFI
        BrrrType::Enum(e) => {
            // Check all variant fields
            for variant in &e.variants {
                for field_ty in &variant.fields {
                    let _ = check_ffi_safe_impl(field_ty, loc, issues);
                }
            }
            // Note: We should also check for #[repr(C)] or #[repr(int)]
            // but that information isn't in the type itself
            if issues.is_empty() {
                FfiSafeType::Safe
            } else {
                FfiSafeType::Unsafe(issues.clone())
            }
        }

        // Interface types are not FFI-safe (vtable-based dispatch)
        BrrrType::Interface(_) => {
            issues.push(BoundaryIssue::type_mismatch(
                "concrete type",
                "interface/trait object",
                loc,
            ));
            FfiSafeType::Unsafe(issues.clone())
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{IntType, NumericType, PrimKind, WrapperKind};

    #[test]
    fn test_node_id() {
        let id = NodeId::new(42);
        assert_eq!(id.raw(), 42);
        assert_eq!(format!("{}", id), "node#42");

        let unknown = NodeId::UNKNOWN;
        assert_eq!(format!("{}", unknown), "<unknown>");
    }

    #[test]
    fn test_taint_source() {
        assert_eq!(TaintSource::UserInput.name(), "user input");
        assert_eq!(TaintSource::Network.discriminant(), 1);
        assert_eq!(format!("{}", TaintSource::Database), "database");
    }

    #[test]
    fn test_severity_ordering() {
        assert!(BoundaryIssueSeverity::Critical > BoundaryIssueSeverity::High);
        assert!(BoundaryIssueSeverity::High > BoundaryIssueSeverity::Medium);
        assert!(BoundaryIssueSeverity::Medium > BoundaryIssueSeverity::Low);
    }

    #[test]
    fn test_severity_is_blocking() {
        assert!(BoundaryIssueSeverity::Critical.is_blocking());
        assert!(BoundaryIssueSeverity::High.is_blocking());
        assert!(!BoundaryIssueSeverity::Medium.is_blocking());
        assert!(!BoundaryIssueSeverity::Low.is_blocking());
    }

    #[test]
    fn test_boundary_issue_constructors() {
        let loc = NodeId::new(10);

        let null = BoundaryIssue::null_crossing(loc);
        assert!(matches!(null, BoundaryIssue::NullCrossing { .. }));
        assert_eq!(issue_location(&null), loc);
        assert_eq!(severity(&null), BoundaryIssueSeverity::Critical);

        let ownership = BoundaryIssue::ownership_unclear(loc);
        assert_eq!(severity(&ownership), BoundaryIssueSeverity::High);

        let mismatch = BoundaryIssue::type_mismatch("i32", "int", loc);
        assert_eq!(severity(&mismatch), BoundaryIssueSeverity::Medium);

        let tainted = BoundaryIssue::tainted_crossing(TaintSource::Network, loc);
        assert_eq!(severity(&tainted), BoundaryIssueSeverity::High);
    }

    #[test]
    fn test_describe_issue() {
        let issue = BoundaryIssue::null_crossing(NodeId::new(5));
        let desc = describe_issue(&issue);
        assert!(desc.contains("Null pointer"));
        assert!(desc.contains("node#5"));
    }

    #[test]
    fn test_ffi_safe_type() {
        let safe = FfiSafeType::Safe;
        assert!(safe.is_safe());
        assert!(!safe.is_unsafe());
        assert!(safe.issues().is_none());

        let issues = vec![BoundaryIssue::null_crossing(NodeId::new(1))];
        let unsafe_type = FfiSafeType::Unsafe(issues);
        assert!(!unsafe_type.is_safe());
        assert!(unsafe_type.is_unsafe());
        assert_eq!(unsafe_type.issues().unwrap().len(), 1);
        assert!(unsafe_type.has_blocking_issues());
    }

    #[test]
    fn test_ffi_safe_combine() {
        let safe1 = FfiSafeType::Safe;
        let safe2 = FfiSafeType::Safe;
        assert!(safe1.combine(safe2).is_safe());

        let safe = FfiSafeType::Safe;
        let unsafe_t = FfiSafeType::Unsafe(vec![BoundaryIssue::null_crossing(NodeId::new(1))]);
        let combined = safe.combine(unsafe_t);
        assert!(combined.is_unsafe());
        assert_eq!(combined.issues().unwrap().len(), 1);
    }

    #[test]
    fn test_check_ffi_safe_primitives() {
        // Unit is safe
        assert!(check_ffi_safe(&BrrrType::UNIT).is_safe());

        // Bool is safe
        assert!(check_ffi_safe(&BrrrType::BOOL).is_safe());

        // String is NOT safe
        assert!(check_ffi_safe(&BrrrType::STRING).is_unsafe());
    }

    #[test]
    fn test_check_ffi_safe_numerics() {
        // i32 is safe
        let i32_ty = BrrrType::Numeric(NumericType::Int(IntType::I32));
        assert!(check_ffi_safe(&i32_ty).is_safe());

        // u64 is safe
        let u64_ty = BrrrType::Numeric(NumericType::Int(IntType::U64));
        assert!(check_ffi_safe(&u64_ty).is_safe());

        // i128 is NOT safe on all platforms
        let i128_ty = BrrrType::Numeric(NumericType::Int(IntType::I128));
        assert!(check_ffi_safe(&i128_ty).is_unsafe());
    }

    #[test]
    fn test_check_ffi_safe_references() {
        // References are NOT safe
        let ref_ty = BrrrType::Wrap(WrapperKind::Ref, Box::new(BrrrType::BOOL));
        let result = check_ffi_safe(&ref_ty);
        assert!(result.is_unsafe());

        // Check it's a lifetime issue
        let issues = result.issues().unwrap();
        assert!(matches!(issues[0], BoundaryIssue::LifetimeMismatch { .. }));
    }

    #[test]
    fn test_check_ffi_safe_raw_pointers() {
        // Raw pointers are "safe" but generate warnings
        let raw_ty = BrrrType::Wrap(
            WrapperKind::Raw,
            Box::new(BrrrType::Numeric(NumericType::Int(IntType::I32))),
        );
        let result = check_ffi_safe(&raw_ty);

        // Should have null crossing and ownership warnings
        assert!(result.is_unsafe());
        let issues = result.issues().unwrap();
        assert!(issues.iter().any(|i| matches!(i, BoundaryIssue::NullCrossing { .. })));
        assert!(issues.iter().any(|i| matches!(i, BoundaryIssue::OwnershipUnclear { .. })));
    }

    #[test]
    fn test_check_ffi_safe_box() {
        // Box is NOT safe
        let box_ty = BrrrType::Wrap(WrapperKind::Box, Box::new(BrrrType::BOOL));
        assert!(check_ffi_safe(&box_ty).is_unsafe());
    }

    #[test]
    fn test_check_ffi_safe_slice() {
        // Slices are NOT safe (fat pointers)
        let slice_ty = BrrrType::Wrap(WrapperKind::Slice, Box::new(BrrrType::BOOL));
        let result = check_ffi_safe(&slice_ty);
        assert!(result.is_unsafe());

        let issues = result.issues().unwrap();
        assert!(issues.iter().any(|i| matches!(i, BoundaryIssue::TypeMismatch { .. })));
    }

    #[test]
    fn test_check_ffi_safe_tuple() {
        // Safe tuple
        let safe_tuple = BrrrType::Tuple(vec![
            BrrrType::Numeric(NumericType::Int(IntType::I32)),
            BrrrType::BOOL,
        ]);
        assert!(check_ffi_safe(&safe_tuple).is_safe());

        // Unsafe tuple (contains String)
        let unsafe_tuple = BrrrType::Tuple(vec![
            BrrrType::Numeric(NumericType::Int(IntType::I32)),
            BrrrType::STRING,
        ]);
        assert!(check_ffi_safe(&unsafe_tuple).is_unsafe());
    }

    #[test]
    fn test_node_id_counter() {
        let counter = NodeIdCounter::new();
        assert_eq!(counter.current(), 0);

        let id1 = counter.fresh();
        assert_eq!(id1.raw(), 0);
        assert_eq!(counter.current(), 1);

        let id2 = counter.fresh();
        assert_eq!(id2.raw(), 1);
        assert_eq!(counter.current(), 2);

        // IDs should be different
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_node_id_counter_starting_at() {
        let counter = NodeIdCounter::starting_at(100);
        assert_eq!(counter.current(), 100);

        let id = counter.fresh();
        assert_eq!(id.raw(), 100);
        assert_eq!(counter.current(), 101);
    }

    #[test]
    fn test_node_id_counter_reset() {
        let counter = NodeIdCounter::new();
        let _ = counter.fresh();
        let _ = counter.fresh();
        assert_eq!(counter.current(), 2);

        counter.reset(0);
        assert_eq!(counter.current(), 0);

        let id = counter.fresh();
        assert_eq!(id.raw(), 0);
    }

    #[test]
    fn test_node_id_counter_clone() {
        let counter = NodeIdCounter::new();
        let _ = counter.fresh();
        let _ = counter.fresh();

        let cloned = counter.clone();
        assert_eq!(cloned.current(), counter.current());
    }

    #[test]
    fn test_shared_ref_unsafe_issue() {
        let loc = NodeId::new(42);
        let issue = BoundaryIssue::shared_ref_unsafe("String", "const char*", loc);

        assert!(matches!(issue, BoundaryIssue::SharedRefUnsafe { .. }));
        assert_eq!(issue_location(&issue), loc);
        assert_eq!(severity(&issue), BoundaryIssueSeverity::High);
        assert_eq!(issue.discriminant(), 7);

        let desc = describe_issue(&issue);
        assert!(desc.contains("&String"));
        assert!(desc.contains("const char*"));
        assert!(desc.contains("node#42"));
    }
}
