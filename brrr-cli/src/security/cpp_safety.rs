//! C++26 Safety Axiom Analyzer.
//!
//! Enforces 7 safety axioms plus performance and anti-pattern rules (38 rules total).
//!
//! **Safety Axioms** (from the Crucible model):
//! - **MemSafe** (Critical): No use-after-free, double-free, buffer overflow
//! - **TypeSafe** (High): Type system prevents category errors
//! - **NullSafe** (Medium): No null pointer dereference
//! - **RaceFree** (High): No data races
//! - **LeakFree** (Low): No resource leaks
//! - **DetDrop** (Low): Deterministic destruction order
//! - **InitSafe** (Medium): Every value initialized before first read
//!
//! **Supplementary categories**:
//! - **Performance**: Performance anti-patterns (false sharing, unnecessary allocations)
//! - **AntiPattern**: C++ anti-patterns (RTTI abuse, exception misuse)
//!
//! Detection uses tree-sitter AST analysis combined with text pattern matching
//! for robust cross-grammar-version support.

use std::collections::HashMap;
use std::path::Path;

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use streaming_iterator::StreamingIterator;
use tree_sitter::{Node, Query, QueryCursor, Tree};

use crate::callgraph::scanner::{ProjectScanner, ScanConfig};
use crate::error::{BrrrError, Result};
use crate::lang::LanguageRegistry;
use crate::security::common::{Confidence, Severity, SourceLocation};

// =============================================================================
// Type Definitions
// =============================================================================

/// The 7 Crucible safety axioms plus supplementary analysis categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SafetyAxiom {
    /// Memory safety: no UAF, double-free, buffer overflow. Risk: Critical.
    MemSafe,
    /// Type safety: no type confusion or category errors. Risk: High.
    TypeSafe,
    /// Null safety: no null pointer dereference. Risk: Medium.
    NullSafe,
    /// Race freedom: no data races on shared mutable state. Risk: High.
    RaceFree,
    /// Leak freedom: no resource leaks. Risk: Low.
    LeakFree,
    /// Deterministic drop: predictable destruction order. Risk: Low.
    DetDrop,
    /// Init safety: every value initialized before first read. Risk: Medium.
    InitSafe,
    /// Performance anti-patterns (not a safety axiom).
    Performance,
    /// C++ anti-patterns (not a safety axiom).
    AntiPattern,
}

impl std::fmt::Display for SafetyAxiom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemSafe => write!(f, "MemSafe"),
            Self::TypeSafe => write!(f, "TypeSafe"),
            Self::NullSafe => write!(f, "NullSafe"),
            Self::RaceFree => write!(f, "RaceFree"),
            Self::LeakFree => write!(f, "LeakFree"),
            Self::DetDrop => write!(f, "DetDrop"),
            Self::InitSafe => write!(f, "InitSafe"),
            Self::Performance => write!(f, "Performance"),
            Self::AntiPattern => write!(f, "AntiPattern"),
        }
    }
}

impl std::str::FromStr for SafetyAxiom {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "memsafe" | "mem" | "memory" => Ok(Self::MemSafe),
            "typesafe" | "type" => Ok(Self::TypeSafe),
            "nullsafe" | "null" => Ok(Self::NullSafe),
            "racefree" | "race" => Ok(Self::RaceFree),
            "leakfree" | "leak" => Ok(Self::LeakFree),
            "detdrop" | "det" | "drop" => Ok(Self::DetDrop),
            "initsafe" | "init" => Ok(Self::InitSafe),
            "performance" | "perf" => Ok(Self::Performance),
            "antipattern" | "anti" => Ok(Self::AntiPattern),
            _ => Err(format!("Unknown axiom: {s}. Valid: init, type, null, mem, race, leak, det, perf, anti")),
        }
    }
}

/// Analysis profile controlling which categories are active.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CppSafetyProfile {
    /// Only the 7 Crucible safety axioms (no Performance/AntiPattern).
    Crucible,
    /// All categories including Performance and AntiPattern.
    Standard,
}

impl Default for CppSafetyProfile {
    fn default() -> Self {
        Self::Standard
    }
}

impl std::str::FromStr for CppSafetyProfile {
    type Err = String;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "crucible" => Ok(Self::Crucible),
            "standard" | "std" => Ok(Self::Standard),
            _ => Err(format!("Unknown profile: {s}. Valid: crucible, standard")),
        }
    }
}

/// Configuration for the C++ safety analyzer.
#[derive(Debug, Clone)]
pub struct CppSafetyConfig {
    /// Filter to a single axiom (None = all applicable).
    pub axiom_filter: Option<SafetyAxiom>,
    /// Analysis profile.
    pub profile: CppSafetyProfile,
    /// Minimum severity to report.
    pub min_severity: Severity,
}

impl Default for CppSafetyConfig {
    fn default() -> Self {
        Self {
            axiom_filter: None,
            profile: CppSafetyProfile::Standard,
            min_severity: Severity::Low,
        }
    }
}

/// A single C++ safety finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CppSafetyFinding {
    /// Source location.
    pub location: SourceLocation,
    /// Rule identifier (e.g., "INIT-001", "MEM-003").
    pub rule_id: String,
    /// Which axiom this finding violates.
    pub axiom: SafetyAxiom,
    /// Severity level.
    pub severity: Severity,
    /// Confidence level.
    pub confidence: Confidence,
    /// Short title.
    pub title: String,
    /// Detailed description.
    pub description: String,
    /// Remediation advice.
    pub remediation: String,
    /// Code snippet around the finding.
    pub code_snippet: String,
    /// CWE identifier, if applicable.
    pub cwe_id: Option<u32>,
    /// Additional metadata.
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub metadata: HashMap<String, String>,
}

/// Scan report containing all findings and summary.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CppSafetyReport {
    /// All findings.
    pub findings: Vec<CppSafetyFinding>,
    /// Number of files scanned.
    pub files_scanned: usize,
    /// Finding count per axiom.
    pub axiom_summary: HashMap<String, usize>,
}

// =============================================================================
// Static Rule Definitions
// =============================================================================

/// A static rule definition used for metadata lookup.
struct RuleDef {
    id: &'static str,
    axiom: SafetyAxiom,
    severity: Severity,
    confidence: Confidence,
    title: &'static str,
    description: &'static str,
    remediation: &'static str,
    cwe: Option<u32>,
}

/// Complete rule catalog.
const RULES: &[RuleDef] = &[
    // ── InitSafe ────────────────────────────────────────────────────────────
    RuleDef {
        id: "INIT-001",
        axiom: SafetyAxiom::InitSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Struct field without NSDMI (non-static data member initializer)",
        description: "Field has no default value (= expr or {}). Uninitialized fields cause UB on read.",
        remediation: "Add a default value: `int x = 0;` or `int x{};`",
        cwe: Some(457),
    },
    RuleDef {
        id: "INIT-002",
        axiom: SafetyAxiom::InitSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Padding/reserved array without zero-init",
        description: "Array field like `uint8_t pad[N]` without `= {}` leaks stack/heap contents.",
        remediation: "Zero-init the array: `uint8_t pad[N]{};` or `= {0}`",
        cwe: Some(457),
    },
    RuleDef {
        id: "INIT-003",
        axiom: SafetyAxiom::InitSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Field not in constructor member initializer list",
        description: "Field without NSDMI is also missing from the constructor's member initializer list.",
        remediation: "Add the field to the constructor initializer list or add NSDMI",
        cwe: Some(457),
    },
    RuleDef {
        id: "INIT-004",
        axiom: SafetyAxiom::InitSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Uninitialized local variable",
        description: "Local variable declared without initialization may contain garbage values.",
        remediation: "Initialize at declaration: `int x = 0;` or `auto x = Type{};`",
        cwe: Some(457),
    },

    // ── TypeSafe ────────────────────────────────────────────────────────────
    RuleDef {
        id: "TYPE-001",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::Medium,
        confidence: Confidence::High,
        title: "Plain enum instead of enum class",
        description: "Unscoped enum leaks names into enclosing scope and allows implicit int conversion.",
        remediation: "Use `enum class` for type-safe scoped enumerations",
        cwe: Some(704),
    },
    RuleDef {
        id: "TYPE-002",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "3+ parameters of same integer type (missing strong types)",
        description: "Multiple parameters of the same integer type are easily transposed at call sites.",
        remediation: "Use strong typedefs (enum class, tagged struct) to distinguish parameters",
        cwe: Some(628),
    },
    RuleDef {
        id: "TYPE-003",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::Medium,
        confidence: Confidence::High,
        title: "Single-argument constructor without explicit",
        description: "Allows implicit conversions that can hide bugs at call sites.",
        remediation: "Mark the constructor `explicit`",
        cwe: Some(704),
    },
    RuleDef {
        id: "TYPE-004",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "reinterpret_cast usage",
        description: "reinterpret_cast bypasses the type system entirely and can cause UB.",
        remediation: "Use `std::bit_cast` (C++20) for type punning or redesign to avoid cast",
        cwe: Some(704),
    },
    RuleDef {
        id: "TYPE-005",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "static_cast from enum to integer",
        description: "Manual enum-to-integer conversion loses type information.",
        remediation: "Use `std::to_underlying()` (C++23) for explicit intent",
        cwe: Some(704),
    },
    RuleDef {
        id: "TYPE-006",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "C-style cast in C++ code",
        description: "C-style casts are unchecked and can perform dangerous conversions silently.",
        remediation: "Use static_cast, const_cast, or reinterpret_cast (with justification)",
        cwe: Some(704),
    },

    // ── NullSafe ────────────────────────────────────────────────────────────
    RuleDef {
        id: "NULL-001",
        axiom: SafetyAxiom::NullSafe,
        severity: Severity::Medium,
        confidence: Confidence::Low,
        title: "Missing [[nodiscard]] on pointer/ref-returning const method",
        description: "Ignoring a returned pointer/reference likely means a missed null check.",
        remediation: "Add `[[nodiscard]]` to const methods returning pointers or references",
        cwe: Some(252),
    },
    RuleDef {
        id: "NULL-002",
        axiom: SafetyAxiom::NullSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "Allocation without null check",
        description: "malloc/calloc/realloc result used without null check. Null deref = crash.",
        remediation: "Check for NULL: `if (!ptr) { /* handle error */ }`",
        cwe: Some(476),
    },
    RuleDef {
        id: "NULL-003",
        axiom: SafetyAxiom::NullSafe,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Adjacent pointer + count fields without span accessor",
        description: "Raw pointer + size pair is a common source of buffer overflows.",
        remediation: "Provide a `std::span` accessor method or use `gsl::span`",
        cwe: Some(119),
    },
    RuleDef {
        id: "NULL-004",
        axiom: SafetyAxiom::NullSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "Pointer dereference without prior null check",
        description: "Dereferencing a pointer without null validation causes UB on null.",
        remediation: "Add a null check or use references/gsl::not_null",
        cwe: Some(476),
    },

    // ── MemSafe ─────────────────────────────────────────────────────────────
    RuleDef {
        id: "MEM-001",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Raw new expression",
        description: "Raw `new` bypasses RAII and creates manual memory management obligations.",
        remediation: "Use arena allocation, std::make_unique, or std::make_shared",
        cwe: Some(401),
    },
    RuleDef {
        id: "MEM-002",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Raw delete expression",
        description: "Raw `delete` indicates manual memory management, prone to double-free and UAF.",
        remediation: "Use smart pointers (unique_ptr/shared_ptr) or arena allocators",
        cwe: Some(415),
    },
    RuleDef {
        id: "MEM-003",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Low,
        confidence: Confidence::High,
        title: "= delete without reason string (C++26)",
        description: "C++26 allows `= delete(\"reason\")` for better diagnostics.",
        remediation: "Add a reason: `void f() = delete(\"use g() instead\");`",
        cwe: None,
    },
    RuleDef {
        id: "MEM-004",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Missing static_assert(sizeof) on aligned struct",
        description: "Struct with `alignas` but no sizeof assertion may have unexpected padding.",
        remediation: "Add `static_assert(sizeof(MyStruct) == EXPECTED_SIZE);`",
        cwe: Some(131),
    },
    RuleDef {
        id: "MEM-005",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "std::string field in data struct",
        description: "std::string allocates on the heap; in data-oriented structs prefer arena strings.",
        remediation: "Use a string_view with arena-backed storage or fixed-size char array",
        cwe: None,
    },
    RuleDef {
        id: "MEM-006",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "std::shared_ptr usage",
        description: "shared_ptr has atomic reference counting overhead and complicates ownership.",
        remediation: "Prefer unique_ptr, raw pointers with clear ownership, or arena allocation",
        cwe: None,
    },
    RuleDef {
        id: "MEM-007",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Virtual method in performance-critical aligned struct",
        description: "Virtual dispatch adds a vtable pointer, breaking cache-line alignment.",
        remediation: "Use CRTP or function pointers for polymorphism in data-oriented structs",
        cwe: None,
    },
    RuleDef {
        id: "MEM-008",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "Raw multiplication before allocation",
        description: "Unchecked `count * size` can overflow, causing undersized allocation.",
        remediation: "Use `std::mul_sat()` (C++26) or check: `if (count > SIZE_MAX / size) { ... }`",
        cwe: Some(190),
    },

    // ── RaceFree ────────────────────────────────────────────────────────────
    RuleDef {
        id: "RACE-001",
        axiom: SafetyAxiom::RaceFree,
        severity: Severity::High,
        confidence: Confidence::Low,
        title: "Mutable field without synchronization",
        description: "A `mutable` field can be modified in const methods, creating hidden shared mutation.",
        remediation: "Protect with std::mutex or use std::atomic for the mutable field",
        cwe: Some(362),
    },
    RuleDef {
        id: "RACE-002",
        axiom: SafetyAxiom::RaceFree,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "std::thread::detach() usage",
        description: "Detached threads are unjoined; accessing shared state after detach is a data race.",
        remediation: "Use std::jthread (C++20) or ensure proper synchronization before detach",
        cwe: Some(362),
    },
    RuleDef {
        id: "RACE-003",
        axiom: SafetyAxiom::RaceFree,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Shared data without lock_guard/unique_lock",
        description: "std::mutex member present but methods access data without holding the lock.",
        remediation: "Use std::lock_guard or std::unique_lock in every method accessing shared data",
        cwe: Some(362),
    },

    // ── LeakFree ────────────────────────────────────────────────────────────
    RuleDef {
        id: "LEAK-001",
        axiom: SafetyAxiom::LeakFree,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "fopen/open without RAII wrapper",
        description: "C-style file handles must be manually closed; exception paths can leak.",
        remediation: "Use std::fstream, std::ifstream, or a custom RAII wrapper",
        cwe: Some(775),
    },
    RuleDef {
        id: "LEAK-002",
        axiom: SafetyAxiom::LeakFree,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Missing virtual destructor in polymorphic base class",
        description: "Deleting via base pointer without virtual destructor causes resource leak and UB.",
        remediation: "Add `virtual ~ClassName() = default;` to the base class",
        cwe: Some(prevent_leak_cwe()),
    },
    RuleDef {
        id: "LEAK-003",
        axiom: SafetyAxiom::LeakFree,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Socket/handle without RAII wrapper",
        description: "Raw file descriptors or socket handles can leak on exception or early return.",
        remediation: "Wrap handles in RAII types that close on destruction",
        cwe: Some(775),
    },

    // ── DetDrop ─────────────────────────────────────────────────────────────
    RuleDef {
        id: "DETD-001",
        axiom: SafetyAxiom::DetDrop,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Global/static variable with non-trivial destructor",
        description: "Static initialization/destruction order is unspecified across translation units.",
        remediation: "Use a function-local static (Meyers singleton) or avoid global state",
        cwe: Some(696),
    },
    RuleDef {
        id: "DETD-002",
        axiom: SafetyAxiom::DetDrop,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "std::unordered_map with non-trivial destructor values",
        description: "Destruction order of unordered_map entries is unspecified.",
        remediation: "If destruction order matters, use std::map or a vector of pairs",
        cwe: Some(696),
    },

    // ── Performance ─────────────────────────────────────────────────────────
    RuleDef {
        id: "PERF-001",
        axiom: SafetyAxiom::Performance,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "std::unordered_map in hot-path struct",
        description: "unordered_map has poor cache locality; consider flat_hash_map or sorted vector.",
        remediation: "Use absl::flat_hash_map, robin_map, or a sorted std::vector for small sets",
        cwe: None,
    },
    RuleDef {
        id: "PERF-002",
        axiom: SafetyAxiom::Performance,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "std::atomic without alignas(64) (false sharing risk)",
        description: "Atomics on the same cache line cause false sharing, destroying scalability.",
        remediation: "Add `alignas(64)` or use `std::hardware_destructive_interference_size`",
        cwe: None,
    },
    RuleDef {
        id: "PERF-003",
        axiom: SafetyAxiom::Performance,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Missing [[likely]]/[[unlikely]] on error branch",
        description: "Error-handling branches are rarely taken; hint helps branch predictor.",
        remediation: "Add `[[unlikely]]` on error paths and `[[likely]]` on hot paths",
        cwe: None,
    },
    RuleDef {
        id: "PERF-004",
        axiom: SafetyAxiom::Performance,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Pure function without constexpr",
        description: "Functions with no side effects can potentially be evaluated at compile time.",
        remediation: "Consider marking as `constexpr` or `consteval` if possible",
        cwe: None,
    },
    RuleDef {
        id: "PERF-005",
        axiom: SafetyAxiom::Performance,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "std::function field (type-erased callable)",
        description: "std::function has heap allocation and virtual dispatch overhead.",
        remediation: "Use templates, function_ref, or inplace_function for hot paths",
        cwe: None,
    },

    // ── AntiPattern ─────────────────────────────────────────────────────────
    RuleDef {
        id: "ANTI-001",
        axiom: SafetyAxiom::AntiPattern,
        severity: Severity::Medium,
        confidence: Confidence::High,
        title: "RTTI usage (dynamic_cast / typeid)",
        description: "RTTI has runtime overhead and often indicates a design flaw.",
        remediation: "Use the visitor pattern, std::variant, or CRTP instead",
        cwe: None,
    },
    RuleDef {
        id: "ANTI-002",
        axiom: SafetyAxiom::AntiPattern,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "std::variant in data struct",
        description: "variant has space overhead (max of all alternatives) and complex visitation.",
        remediation: "Consider a kind enum + union, or tagged struct hierarchy",
        cwe: None,
    },
    RuleDef {
        id: "ANTI-003",
        axiom: SafetyAxiom::AntiPattern,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Exception throw in code",
        description: "Exceptions have unpredictable performance cost and complicate reasoning.",
        remediation: "Use std::expected (C++23), error codes, or Result types",
        cwe: None,
    },

    // ── Lifetime Safety (§1.5.1 D3390) ────────────────────────────────────
    RuleDef {
        id: "LIFE-001",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "string_view bound to temporary std::string",
        description: "string_view does not own its data; binding to a temporary string creates a dangling view after the statement ends.",
        remediation: "Store the string in a named variable first, or use std::string directly",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-002",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "span bound to temporary container",
        description: "span does not own its data; binding to a temporary container creates a dangling span.",
        remediation: "Store the container in a named variable first, or pass by reference",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-003",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Low,
        title: "Non-owning view stored as class member",
        description: "string_view/span stored as struct/class member may outlive the referenced data.",
        remediation: "Use std::string/std::vector for owned storage, or document the lifetime contract explicitly",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-004",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Returning non-owning view to local data",
        description: "Returning string_view or span to function-local data creates a dangling reference.",
        remediation: "Return std::string or std::vector instead of the non-owning view",
        cwe: Some(416),
    },

    // ── Iterator Invalidation (§2.2.2 D3390) ──────────────────────────────
    RuleDef {
        id: "LIFE-005",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Container mutation during range-for loop",
        description: "Calling push_back/erase/insert/clear on a container while iterating over it with range-for invalidates iterators, causing UB.",
        remediation: "Collect modifications and apply after the loop, or use erase-remove idiom",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-006",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Container mutation while holding iterator",
        description: "Modifying a container while iterating with begin()/end() invalidates the iterator.",
        remediation: "Use the return value of erase() to advance, or collect changes for post-loop application",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-007",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Low,
        title: "Container mutation while reference/pointer to element exists",
        description: "Mutating a container (push_back, insert, erase) while holding a reference or pointer to an element may invalidate that reference.",
        remediation: "Re-obtain references after container mutation, or use stable containers like std::list",
        cwe: Some(416),
    },

    // ── Initializer List Dangling (§2.2.3 D3390) ──────────────────────────
    RuleDef {
        id: "LIFE-008",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Local variable of type std::initializer_list",
        description: "The backing array of initializer_list is destroyed at the end of the full expression; storing it in a local variable creates a dangling reference.",
        remediation: "Use std::vector, std::array, or a C array instead",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-009",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Function parameter of type std::initializer_list stored or returned",
        description: "The backing array only lives for the duration of the function call; storing it outlives the data.",
        remediation: "Accept a span<const T> or const vector<T>& instead",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-010",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "std::initializer_list as class data member",
        description: "Storing initializer_list as a member is almost always wrong; the backing array doesn't persist beyond the initializing expression.",
        remediation: "Use std::vector<T> or std::array<T, N> as the member type",
        cwe: Some(416),
    },

    // ── Return Reference/Pointer to Local (§2.2 D3390) ────────────────────
    RuleDef {
        id: "LIFE-011",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Critical,
        confidence: Confidence::High,
        title: "Returning reference or pointer to local variable",
        description: "Function returns reference or pointer to a local variable; the variable is destroyed when the function returns, creating a dangling reference.",
        remediation: "Return by value, use an output parameter, or allocate on the heap",
        cwe: Some(562),
    },
    RuleDef {
        id: "LIFE-013",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "Lambda capturing by reference escapes function scope",
        description: "A lambda with [&] capture that is returned, stored in std::function, or passed to async/thread creates dangling references when the enclosing scope exits.",
        remediation: "Capture by value [=] or explicitly capture needed variables by value",
        cwe: Some(416),
    },
    RuleDef {
        id: "LIFE-014",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::High,
        confidence: Confidence::Medium,
        title: "std::ref/std::cref wrapping local variable",
        description: "std::reference_wrapper wrapping a local variable that escapes scope creates a dangling reference.",
        remediation: "Pass by value or ensure the referenced variable outlives the wrapper",
        cwe: Some(416),
    },
    // ── §2.1 Unsafe Context (UCTX-xxx) ──────────────────────────────────────
    RuleDef {
        id: "UCTX-001",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Pointer arithmetic (unsafe context)",
        description: "Pointer arithmetic (ptr+n, ptr++, ptr[n]) can advance past allocation bounds, causing buffer overflow UB. D3390 §2.1 prohibits this in safe context.",
        remediation: "Use std::span, std::array, or iterator-based access instead of raw pointer arithmetic",
        cwe: Some(119),
    },
    RuleDef {
        id: "UCTX-002",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Low,
        confidence: Confidence::Low,
        title: "Pointer difference (unsafe context)",
        description: "Taking the difference of pointers into different allocations is undefined behavior. D3390 §2.1 prohibits this in safe context.",
        remediation: "Use iterator::distance or container::size instead of pointer subtraction",
        cwe: Some(469),
    },
    RuleDef {
        id: "UCTX-004",
        axiom: SafetyAxiom::TypeSafe,
        severity: Severity::High,
        confidence: Confidence::High,
        title: "Union type definition (unsafe type punning)",
        description: "Union field access without discriminant check is type confusion UB. D3390 §2.1 treats union access as unsafe. Prefer std::variant with visit.",
        remediation: "Replace union with std::variant and use std::visit for safe access",
        cwe: Some(188),
    },
    RuleDef {
        id: "UCTX-005",
        axiom: SafetyAxiom::RaceFree,
        severity: Severity::Medium,
        confidence: Confidence::Medium,
        title: "Mutable static variable (data race hazard)",
        description: "Non-const static variables are data race hazards in multi-threaded programs. D3390 §2.1 prohibits naming mutable statics in safe context.",
        remediation: "Use thread_local, const, constexpr, or protect with a mutex",
        cwe: Some(362),
    },
    RuleDef {
        id: "UCTX-006",
        axiom: SafetyAxiom::MemSafe,
        severity: Severity::Low,
        confidence: Confidence::High,
        title: "Inline assembly (unsafe context)",
        description: "Inline assembly bypasses all compiler safety checks. D3390 §2.1 treats asm blocks as inherently unsafe context.",
        remediation: "Use compiler intrinsics or constexpr functions as safe alternatives where possible",
        cwe: Some(676),
    },
];

/// CWE for resource leak via missing virtual destructor (improper resource shutdown).
const fn prevent_leak_cwe() -> u32 {
    404
}

/// Look up a rule definition by ID.
fn lookup_rule(id: &str) -> Option<&'static RuleDef> {
    RULES.iter().find(|r| r.id == id)
}

// =============================================================================
// Tree-sitter Queries
// =============================================================================

/// Find `new` expressions.
const NEW_EXPR_QUERY: &str = "(new_expression) @expr";

/// Find `delete` expressions.
const DELETE_EXPR_QUERY: &str = "(delete_expression) @expr";

/// Find `throw` statements.
const THROW_QUERY: &str = "(throw_statement) @expr";

/// Find enum specifiers.
const ENUM_QUERY: &str = "(enum_specifier) @enum_spec";

/// Find call expressions with identifier function names.
const CALL_QUERY: &str = r#"
(call_expression
  function: (identifier) @func
  arguments: (argument_list) @args) @call
"#;

/// Find declarations without initializers (uninitialized locals).
const UNINIT_VAR_QUERY: &str = r#"
(declaration
  type: (_) @type
  declarator: (identifier) @var
  !value) @decl
"#;

// =============================================================================
// Scanner Entry Points
// =============================================================================

/// Scan a directory or file for C++ safety axiom violations.
pub fn scan_cpp_safety(path: &Path, config: &CppSafetyConfig) -> Result<CppSafetyReport> {
    if path.is_file() {
        let findings = scan_file_cpp_safety(path, config)?;
        let report = build_report(findings, 1);
        return Ok(report);
    }

    let scanner = ProjectScanner::new(path.to_string_lossy().as_ref())?;

    let mut cfg = ScanConfig::default();
    cfg.extensions = vec![
        ".cpp".into(), ".cc".into(), ".cxx".into(),
        ".hpp".into(), ".hh".into(), ".hxx".into(),
        ".h".into(),
        ".cu".into(), ".cuh".into(),
        ".c".into(),
    ];

    let result = scanner.scan_with_config(&cfg)?;
    let files_scanned = result.files.len();

    let all_findings: Vec<Vec<CppSafetyFinding>> = result
        .files
        .par_iter()
        .filter_map(|file| scan_file_cpp_safety(file, config).ok())
        .collect();

    let findings: Vec<CppSafetyFinding> = all_findings.into_iter().flatten().collect();
    Ok(build_report(findings, files_scanned))
}

/// Scan a single file for C++ safety axiom violations.
pub fn scan_file_cpp_safety(
    path: &Path,
    config: &CppSafetyConfig,
) -> Result<Vec<CppSafetyFinding>> {
    let registry = LanguageRegistry::global();

    let lang = registry.detect_language(path);
    let lang = match lang {
        Some(l) if l.name() == "c" || l.name() == "cpp" => l,
        _ => return Ok(Vec::new()),
    };

    let source = std::fs::read(path).map_err(|e| BrrrError::io_with_path(e, path))?;
    let source_str = std::str::from_utf8(&source).unwrap_or("");

    let mut parser = lang.parser()?;
    let tree = parser.parse(&source, None).ok_or_else(|| BrrrError::Parse {
        file: path.display().to_string(),
        message: "Failed to parse file".to_string(),
    })?;

    let file_path = path.to_string_lossy().to_string();
    let is_cpp = lang.name() == "cpp"
        || path.extension().map_or(false, |ext| {
            matches!(ext.to_str(), Some("cpp" | "cc" | "cxx" | "hpp" | "hh" | "hxx" | "cu" | "cuh"))
        });

    let mut findings = Vec::new();

    // Run all checkers
    check_init_safe(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;
    check_type_safe(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    check_null_safe(&tree, &source, &file_path, source_str, lang.name(), &mut findings)?;
    check_mem_safe(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    check_race_free(source_str, &file_path, is_cpp, &mut findings);
    check_leak_free(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    check_det_drop(source_str, &file_path, &mut findings);
    check_performance(source_str, &file_path, &mut findings);
    check_anti_patterns(&tree, &source, &file_path, source_str, lang.name(), is_cpp, &mut findings)?;
    check_lifetime_safety(source_str, &file_path, is_cpp, &mut findings);
    check_iterator_invalidation(source_str, &file_path, is_cpp, &mut findings);
    check_initializer_list_dangling(source_str, &file_path, is_cpp, &mut findings);
    check_return_ref_to_local(source_str, &file_path, is_cpp, &mut findings);
    check_lambda_ref_escape(source_str, &file_path, is_cpp, &mut findings);
    check_unsafe_context(source_str, &file_path, is_cpp, &mut findings);

    // Apply filters
    let filtered = findings
        .into_iter()
        .filter(|f| {
            if let Some(ref ax) = config.axiom_filter {
                if f.axiom != *ax {
                    return false;
                }
            }
            if f.severity < config.min_severity {
                return false;
            }
            if config.profile == CppSafetyProfile::Crucible {
                if matches!(f.axiom, SafetyAxiom::Performance | SafetyAxiom::AntiPattern) {
                    return false;
                }
            }
            true
        })
        .collect();

    Ok(filtered)
}

/// Build a report from collected findings.
fn build_report(findings: Vec<CppSafetyFinding>, files_scanned: usize) -> CppSafetyReport {
    let mut axiom_summary: HashMap<String, usize> = HashMap::new();
    for f in &findings {
        *axiom_summary.entry(f.axiom.to_string()).or_insert(0) += 1;
    }
    CppSafetyReport {
        findings,
        files_scanned,
        axiom_summary,
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Get text content of a tree-sitter node.
fn node_text<'a>(node: Node, source: &'a [u8]) -> &'a str {
    std::str::from_utf8(&source[node.start_byte()..node.end_byte()]).unwrap_or("")
}

/// Build a SourceLocation from a tree-sitter node.
fn location_from_node(node: Node, file_path: &str) -> SourceLocation {
    SourceLocation::new(
        file_path,
        node.start_position().row + 1,
        node.start_position().column + 1,
        node.end_position().row + 1,
        node.end_position().column + 1,
    )
}

/// Extract a code snippet around a line (1-indexed).
fn snippet_at_line(source_str: &str, line: usize, context: usize) -> String {
    let lines: Vec<&str> = source_str.lines().collect();
    if lines.is_empty() || line == 0 {
        return String::new();
    }
    let idx = line.saturating_sub(1);
    let start = idx.saturating_sub(context);
    let end = (idx + context + 1).min(lines.len());
    lines[start..end].join("\n")
}

/// A text search match with position.
struct TextMatch {
    line: usize,
    column: usize,
    snippet: String,
}

/// Search source text for all non-comment occurrences of `pattern`.
fn find_pattern(source: &str, pattern: &str) -> Vec<TextMatch> {
    let mut results = Vec::new();
    for (line_idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        // Skip pure comment lines
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }
        let mut search_start = 0;
        while let Some(pos) = line[search_start..].find(pattern) {
            let abs_pos = search_start + pos;
            // Skip if preceded by a line comment on this line
            let before = &line[..abs_pos];
            if before.contains("//") {
                break;
            }
            results.push(TextMatch {
                line: line_idx + 1,
                column: abs_pos + 1,
                snippet: trimmed.to_string(),
            });
            search_start = abs_pos + pattern.len();
        }
    }
    results
}

/// Collect all AST nodes matching any of the given kinds.
fn collect_nodes<'a>(node: Node<'a>, kinds: &[&str]) -> Vec<Node<'a>> {
    let mut results = Vec::new();
    collect_nodes_inner(node, kinds, &mut results);
    results
}

fn collect_nodes_inner<'a>(node: Node<'a>, kinds: &[&str], out: &mut Vec<Node<'a>>) {
    if kinds.contains(&node.kind()) {
        out.push(node);
    }
    for i in 0..node.child_count() {
        if let Some(child) = node.child(i as u32) {
            collect_nodes_inner(child, kinds, out);
        }
    }
}

/// Create a finding from a rule ID and location.
fn make_finding(
    rule_id: &str,
    location: SourceLocation,
    code_snippet: String,
) -> CppSafetyFinding {
    let rule = lookup_rule(rule_id).expect("Unknown rule ID");
    CppSafetyFinding {
        location,
        rule_id: rule_id.to_string(),
        axiom: rule.axiom,
        severity: rule.severity,
        confidence: rule.confidence,
        title: rule.title.to_string(),
        description: rule.description.to_string(),
        remediation: rule.remediation.to_string(),
        code_snippet,
        cwe_id: rule.cwe,
        metadata: HashMap::new(),
    }
}

/// Create a finding from a rule ID and a TextMatch.
fn make_finding_from_text(rule_id: &str, file_path: &str, m: &TextMatch) -> CppSafetyFinding {
    let loc = SourceLocation::new(file_path, m.line, m.column, m.line, m.column + 1);
    make_finding(rule_id, loc, m.snippet.clone())
}

// =============================================================================
// InitSafe Checker
// =============================================================================

fn check_init_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // INIT-001 / INIT-002: Struct/class fields without NSDMI
    check_field_nsdmi(tree, source, file_path, source_str, findings);

    // INIT-004: Uninitialized local variables
    check_uninit_locals(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// INIT-001 / INIT-002: Walk struct/class field declarations, flag those without default values.
fn check_field_nsdmi(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let field_list_nodes = collect_nodes(tree.root_node(), &["field_declaration_list"]);

    for field_list in field_list_nodes {
        for i in 0..field_list.named_child_count() {
            let Some(child) = field_list.named_child(i as u32) else { continue };
            if child.kind() != "field_declaration" {
                continue;
            }

            let field_text = node_text(child, source);

            // Skip access specifiers, friend declarations, using declarations, type aliases
            if field_text.starts_with("public")
                || field_text.starts_with("private")
                || field_text.starts_with("protected")
                || field_text.starts_with("friend")
                || field_text.starts_with("using")
                || field_text.starts_with("typedef")
            {
                continue;
            }

            // Skip static fields, constexpr, and function declarations (methods)
            if field_text.contains("static ")
                || field_text.contains("constexpr ")
                || field_text.contains('(')
            {
                continue;
            }

            // Check if field has a default value (NSDMI)
            let has_default = child.child_by_field_name("default_value").is_some();
            // Also check text for `= ...` or `{...}` initializers
            let has_text_init = field_text.contains(" = ")
                || field_text.contains("= ")
                || (field_text.contains('{') && !field_text.starts_with('{'));

            if !has_default && !has_text_init {
                let loc = location_from_node(child, file_path);

                // INIT-002: Check if it's a padding/reserved array
                let is_padding_array = (field_text.contains("pad")
                    || field_text.contains("reserved")
                    || field_text.contains("unused"))
                    && field_text.contains('[');

                let rule_id = if is_padding_array { "INIT-002" } else { "INIT-001" };
                let snippet = snippet_at_line(source_str, loc.line, 0);
                let mut finding = make_finding(rule_id, loc, snippet);
                finding.metadata.insert("field".to_string(), field_text.trim().to_string());
                findings.push(finding);
            }
        }
    }
}

/// INIT-004: Uninitialized local variables via tree-sitter query.
fn check_uninit_locals(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, UNINIT_VAR_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let var_idx = query.capture_index_for_name("var").unwrap_or(0);
    let decl_idx = query.capture_index_for_name("decl").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let var_node = m.captures.iter().find(|c| c.index == var_idx);
        let decl_node = m.captures.iter().find(|c| c.index == decl_idx);

        if let (Some(var_cap), Some(decl_cap)) = (var_node, decl_node) {
            // Only flag variables inside function bodies
            let in_function = is_inside_function(decl_cap.node);
            if !in_function {
                continue;
            }

            let var_name = node_text(var_cap.node, source);
            // Skip loop variables, catch parameters, etc.
            if var_name.starts_with('_') || var_name == "i" || var_name == "j" || var_name == "k" {
                continue;
            }

            let loc = location_from_node(decl_cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding("INIT-004", loc, snippet);
            finding.metadata.insert("variable".to_string(), var_name.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

/// Check if a node is inside a function body (compound_statement under function_definition).
fn is_inside_function(mut node: Node) -> bool {
    while let Some(parent) = node.parent() {
        if parent.kind() == "function_definition" || parent.kind() == "lambda_expression" {
            return true;
        }
        node = parent;
    }
    false
}

// =============================================================================
// TypeSafe Checker
// =============================================================================

fn check_type_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // TYPE-001: Plain enum (not enum class)
    if is_cpp {
        check_plain_enum(tree, source, file_path, source_str, lang_name, findings)?;
    }

    // TYPE-003: Single-arg constructor without explicit (C++ only)
    if is_cpp {
        check_missing_explicit(source_str, file_path, findings);
    }

    // TYPE-004: reinterpret_cast
    if is_cpp {
        for m in find_pattern(source_str, "reinterpret_cast<") {
            findings.push(make_finding_from_text("TYPE-004", file_path, &m));
        }
    }

    // TYPE-005: static_cast from enum
    if is_cpp {
        check_static_cast_enum(source_str, file_path, findings);
    }

    // TYPE-006: C-style cast in C++ code
    if is_cpp {
        check_c_style_cast(source_str, file_path, findings);
    }

    Ok(())
}

/// TYPE-001: Detect plain `enum` (not `enum class` / `enum struct`) using tree-sitter.
fn check_plain_enum(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, ENUM_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let enum_idx = query.capture_index_for_name("enum_spec").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let enum_node = m.captures.iter().find(|c| c.index == enum_idx);
        if let Some(enum_cap) = enum_node {
            let text = node_text(enum_cap.node, source);
            // Check if it has `class` or `struct` keyword after `enum`
            let is_scoped = text.starts_with("enum class") || text.starts_with("enum struct");
            if !is_scoped {
                // Skip forward declarations without body
                if !text.contains('{') {
                    continue;
                }
                let loc = location_from_node(enum_cap.node, file_path);
                let snippet = snippet_at_line(source_str, loc.line, 0);
                findings.push(make_finding("TYPE-001", loc, snippet));
            }
        }
    }

    Ok(())
}

/// TYPE-003: Find single-argument constructors without `explicit`.
fn check_missing_explicit(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // Heuristic: look for constructor-like declarations with a single parameter
    // Pattern: ClassName(Type param) — without `explicit` keyword before it
    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        // Skip comments
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }
        // Skip lines with `explicit`
        if trimmed.contains("explicit") {
            continue;
        }
        // Skip destructors, operators, and templates
        if trimmed.contains('~') || trimmed.contains("operator") || trimmed.starts_with("template") {
            continue;
        }
        // Skip lines that are clearly not constructors
        if trimmed.starts_with("return")
            || trimmed.starts_with("if")
            || trimmed.starts_with("for")
            || trimmed.starts_with("while")
            || trimmed.starts_with("switch")
            || trimmed.starts_with('#')
        {
            continue;
        }

        // Look for pattern: Identifier(Type param) with exactly one parameter
        // and no return type (constructors have no return type)
        // This is a heuristic — we look for:
        // - Line contains exactly one '(' and one ')'
        // - The part before '(' is a single identifier (class name)
        // - The part inside parens has exactly one parameter (no comma)
        // - Line ends with '{' or ':'  or ';' (definition or declaration)
        if let Some(paren_start) = trimmed.find('(') {
            if let Some(paren_end) = trimmed.rfind(')') {
                if paren_start < paren_end {
                    let before_paren = trimmed[..paren_start].trim();
                    let inside_parens = trimmed[paren_start + 1..paren_end].trim();

                    // Must look like a constructor: single capitalized identifier before paren
                    if before_paren.is_empty()
                        || before_paren.contains(' ')
                        || before_paren.contains('<')
                        || before_paren.contains('>')
                        || !before_paren.chars().next().map_or(false, |c| c.is_uppercase())
                    {
                        continue;
                    }

                    // Must have exactly one parameter (no commas, not empty, not void)
                    if inside_parens.is_empty()
                        || inside_parens == "void"
                        || inside_parens.contains(',')
                    {
                        continue;
                    }

                    // Must end with constructor-like suffix
                    let after_paren = trimmed[paren_end + 1..].trim();
                    if !(after_paren.starts_with('{')
                        || after_paren.starts_with(':')
                        || after_paren.starts_with(';')
                        || after_paren.is_empty())
                    {
                        continue;
                    }

                    let loc = SourceLocation::new(
                        file_path,
                        line_idx + 1,
                        1,
                        line_idx + 1,
                        trimmed.len(),
                    );
                    let finding = make_finding("TYPE-003", loc, trimmed.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// TYPE-005: static_cast from enum values.
fn check_static_cast_enum(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "static_cast<int>") {
        // Check if the cast argument looks like an enum value
        let after = &source_str.lines().nth(m.line - 1).unwrap_or("")[m.column..];
        if after.contains("::") {
            findings.push(make_finding_from_text("TYPE-005", file_path, &m));
        }
    }
    // Also check for other integer casts of enum values
    for m in find_pattern(source_str, "static_cast<unsigned") {
        let after = &source_str.lines().nth(m.line - 1).unwrap_or("")[m.column..];
        if after.contains("::") {
            findings.push(make_finding_from_text("TYPE-005", file_path, &m));
        }
    }
}

/// TYPE-006: C-style casts in C++ code.
fn check_c_style_cast(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // Heuristic: look for (Type) expr patterns
    // This is tricky because (int) can also be a function call or macro.
    // We look for casts of specific types that are commonly cast.
    let cast_types = [
        "(int)", "(unsigned)", "(char)", "(long)", "(double)", "(float)",
        "(void*)", "(void *)", "(char*)", "(char *)",
        "(uint8_t)", "(uint16_t)", "(uint32_t)", "(uint64_t)",
        "(int8_t)", "(int16_t)", "(int32_t)", "(int64_t)",
        "(size_t)", "(uintptr_t)", "(intptr_t)",
    ];

    for cast_type in &cast_types {
        for m in find_pattern(source_str, cast_type) {
            // Skip if this is a function declaration/definition parameter
            let line = source_str.lines().nth(m.line - 1).unwrap_or("");
            // Skip if preceded by comma or open paren (likely parameter list)
            let before = &line[..m.column.saturating_sub(1)];
            if before.trim_end().ends_with(',') || before.trim_end().ends_with('(') {
                continue;
            }
            // Skip sizeof expressions
            if before.contains("sizeof") {
                continue;
            }
            findings.push(make_finding_from_text("TYPE-006", file_path, &m));
        }
    }
}

// =============================================================================
// NullSafe Checker
// =============================================================================

fn check_null_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // NULL-002: Allocation without null check (reuse logic from memory_safety)
    check_alloc_null(tree, source, file_path, source_str, lang_name, findings)?;

    // NULL-003: Adjacent pointer + count fields
    check_ptr_count_pair(tree, source, file_path, source_str, findings);

    Ok(())
}

/// NULL-002: malloc/calloc/realloc without null check.
fn check_alloc_null(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, CALL_QUERY) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let alloc_fns = ["malloc", "calloc", "realloc", "strdup", "strndup"];

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(call_cap)) = (func_node, call_node) {
            let func_name = node_text(func_cap.node, source);
            if !alloc_fns.contains(&func_name) {
                continue;
            }

            // Check if result is assigned and tested for NULL
            let parent = call_cap.node.parent();
            let assigned_var = parent.and_then(|p| {
                if p.kind() == "init_declarator" {
                    p.child_by_field_name("declarator").map(|d| node_text(d, source).to_string())
                } else if p.kind() == "assignment_expression" {
                    p.child_by_field_name("left").map(|l| node_text(l, source).to_string())
                } else {
                    None
                }
            });

            if let Some(var_name) = assigned_var {
                let clean_var = var_name.trim_start_matches('*').trim();
                let check_region = &source_str[call_cap.node.end_byte()..];
                let check_window = &check_region[..check_region.len().min(500)];

                let has_null_check = check_window.contains(&format!("{clean_var} == NULL"))
                    || check_window.contains(&format!("{clean_var} != NULL"))
                    || check_window.contains(&format!("!{clean_var}"))
                    || check_window.contains(&format!("{clean_var} == nullptr"))
                    || check_window.contains(&format!("{clean_var} != nullptr"))
                    || check_window.contains(&format!("if ({clean_var})"))
                    || check_window.contains(&format!("if({clean_var})"));

                if !has_null_check {
                    let loc = location_from_node(call_cap.node, file_path);
                    let snippet = snippet_at_line(source_str, loc.line, 1);
                    let mut finding = make_finding("NULL-002", loc, snippet);
                    finding.metadata.insert("function".to_string(), func_name.to_string());
                    finding.metadata.insert("variable".to_string(), clean_var.to_string());
                    findings.push(finding);
                }
            }
        }
    }

    Ok(())
}

/// NULL-003: Adjacent pointer + count/size fields in structs.
fn check_ptr_count_pair(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let field_list_nodes = collect_nodes(tree.root_node(), &["field_declaration_list"]);

    for field_list in field_list_nodes {
        let mut prev_was_pointer = false;
        let mut pointer_line = 0usize;

        for i in 0..field_list.named_child_count() {
            let Some(child) = field_list.named_child(i as u32) else { continue };
            if child.kind() != "field_declaration" {
                prev_was_pointer = false;
                continue;
            }

            let text = node_text(child, source);
            let is_pointer = text.contains('*');
            let is_count = text.contains("size")
                || text.contains("count")
                || text.contains("length")
                || text.contains("len")
                || text.contains("num_")
                || text.contains("n_");

            if prev_was_pointer && is_count && !is_pointer {
                let loc = SourceLocation::new(
                    file_path,
                    pointer_line,
                    1,
                    child.end_position().row + 1,
                    child.end_position().column + 1,
                );
                let snippet = snippet_at_line(source_str, pointer_line, 1);
                findings.push(make_finding("NULL-003", loc, snippet));
            }

            prev_was_pointer = is_pointer && !is_count;
            if is_pointer {
                pointer_line = child.start_position().row + 1;
            }
        }
    }
}

// =============================================================================
// MemSafe Checker
// =============================================================================

fn check_mem_safe(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    if is_cpp {
        // MEM-001: Raw new
        check_new_delete(tree, source, file_path, source_str, lang_name, "MEM-001", NEW_EXPR_QUERY, findings)?;

        // MEM-002: Raw delete
        check_new_delete(tree, source, file_path, source_str, lang_name, "MEM-002", DELETE_EXPR_QUERY, findings)?;

        // MEM-003: = delete without reason
        check_delete_reason(source_str, file_path, findings);

        // MEM-005: std::string field
        check_std_type_field(source_str, file_path, "std::string", "MEM-005", findings);

        // MEM-006: std::shared_ptr
        for m in find_pattern(source_str, "std::shared_ptr") {
            findings.push(make_finding_from_text("MEM-006", file_path, &m));
        }
        for m in find_pattern(source_str, "shared_ptr<") {
            // Skip if it's make_shared or already reported
            if !m.snippet.contains("std::shared_ptr") && !m.snippet.contains("make_shared") {
                findings.push(make_finding_from_text("MEM-006", file_path, &m));
            }
        }
    }

    // MEM-004: Missing static_assert on aligned struct
    if is_cpp {
        check_missing_sizeof_assert(source_str, file_path, findings);
    }

    // MEM-008: Raw multiplication before allocation
    check_alloc_multiply(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// MEM-001 / MEM-002: Detect new/delete expressions via tree-sitter query.
fn check_new_delete(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    rule_id: &str,
    query_str: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, query_str) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let expr_idx = query.capture_index_for_name("expr").unwrap_or(0);
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        if let Some(cap) = m.captures.iter().find(|c| c.index == expr_idx) {
            let text = node_text(cap.node, source);
            // Skip placement new (has parenthesized address before type)
            if rule_id == "MEM-001" && text.contains("placement") {
                continue;
            }
            let loc = location_from_node(cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding(rule_id, loc, snippet);
            finding.metadata.insert("expression".to_string(), text.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

/// MEM-003: `= delete` without C++26 reason string.
fn check_delete_reason(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "= delete;") {
        // Already has `= delete;` without a reason string
        // C++26 allows `= delete("reason");`
        if !m.snippet.contains("= delete(") {
            findings.push(make_finding_from_text("MEM-003", file_path, &m));
        }
    }
}

/// MEM-004: struct with alignas but no static_assert(sizeof).
fn check_missing_sizeof_assert(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // Find structs/classes with alignas
    let mut in_aligned_struct = false;
    let mut aligned_struct_line = 0usize;
    let mut brace_depth = 0i32;
    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if trimmed.contains("alignas(") && (trimmed.contains("struct") || trimmed.contains("class")) {
            in_aligned_struct = true;
            aligned_struct_line = line_idx + 1;
            brace_depth = 0;
        }

        if in_aligned_struct {
            brace_depth += line.matches('{').count() as i32;
            brace_depth -= line.matches('}').count() as i32;

            if brace_depth <= 0 && line.contains('}') {
                // End of struct — check if a static_assert(sizeof) follows within 5 lines
                let remaining_lines: Vec<&str> = source_str.lines()
                    .skip(line_idx + 1)
                    .take(5)
                    .collect();
                let nearby = remaining_lines.join("\n");
                if !nearby.contains("static_assert(sizeof") && !nearby.contains("static_assert (sizeof") {
                    let loc = SourceLocation::new(
                        file_path,
                        aligned_struct_line,
                        1,
                        line_idx + 1,
                        1,
                    );
                    let snippet = snippet_at_line(source_str, aligned_struct_line, 0);
                    findings.push(make_finding("MEM-004", loc, snippet));
                }
                in_aligned_struct = false;
            }
        }
    }
}

/// Check for std:: type usage in struct fields (for MEM-005, PERF-001, etc.).
fn check_std_type_field(
    source_str: &str,
    file_path: &str,
    type_name: &str,
    rule_id: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // We want to find field declarations containing the type,
    // not local variables or function parameters.
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            // Check for the type in this field
            if trimmed.contains(type_name) && !trimmed.starts_with("//") && !trimmed.starts_with("/*") {
                // Skip method declarations (contain parentheses for params)
                if trimmed.contains('(') && !trimmed.contains("std::function") {
                    continue;
                }
                let col = trimmed.find(type_name).unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path,
                    line_idx + 1,
                    col + 1,
                    line_idx + 1,
                    col + type_name.len() + 1,
                );
                findings.push(make_finding(rule_id, loc, trimmed.to_string()));
            }
        }
    }
}

/// MEM-008: Raw multiplication in allocation size arguments.
fn check_alloc_multiply(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let alloc_arith_query = r#"
(call_expression
  function: (identifier) @func
  (#any-of? @func "malloc" "calloc" "realloc" "aligned_alloc")
  arguments: (argument_list
    (binary_expression
      operator: [("+") ("*")]
      ) @arith)) @call
"#;

    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, alloc_arith_query) {
        Ok(q) => q,
        Err(_) => return Ok(()),
    };

    let func_idx = query.capture_index_for_name("func").unwrap_or(0);
    let arith_idx = query.capture_index_for_name("arith").unwrap_or(0);
    let call_idx = query.capture_index_for_name("call").unwrap_or(0);

    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        let func_node = m.captures.iter().find(|c| c.index == func_idx);
        let arith_node = m.captures.iter().find(|c| c.index == arith_idx);
        let call_node = m.captures.iter().find(|c| c.index == call_idx);

        if let (Some(func_cap), Some(arith_cap), Some(call_cap)) = (func_node, arith_node, call_node) {
            let func_name = node_text(func_cap.node, source);
            let arith_text = node_text(arith_cap.node, source);

            let loc = location_from_node(call_cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            let mut finding = make_finding("MEM-008", loc, snippet);
            finding.metadata.insert("function".to_string(), func_name.to_string());
            finding.metadata.insert("expression".to_string(), arith_text.to_string());
            findings.push(finding);
        }
    }

    Ok(())
}

// =============================================================================
// RaceFree Checker
// =============================================================================

fn check_race_free(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    // RACE-001: mutable fields without atomic/mutex
    check_mutable_fields(source_str, file_path, findings);

    // RACE-002: .detach() on threads
    for m in find_pattern(source_str, ".detach()") {
        findings.push(make_finding_from_text("RACE-002", file_path, &m));
    }

    // RACE-003: std::mutex without lock_guard usage nearby
    check_mutex_without_lock(source_str, file_path, findings);
}

/// RACE-001: `mutable` fields that aren't std::mutex or std::atomic.
fn check_mutable_fields(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            if trimmed.starts_with("mutable ") || trimmed.contains(" mutable ") {
                // Skip if it's std::mutex, std::atomic, or a lock type
                if trimmed.contains("mutex")
                    || trimmed.contains("atomic")
                    || trimmed.contains("lock")
                    || trimmed.contains("condition_variable")
                {
                    continue;
                }
                let loc = SourceLocation::new(file_path, line_idx + 1, 1, line_idx + 1, trimmed.len());
                findings.push(make_finding("RACE-001", loc, trimmed.to_string()));
            }
        }
    }
}

/// RACE-003: Class has std::mutex member but methods don't use lock_guard/unique_lock.
fn check_mutex_without_lock(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let has_mutex = source_str.contains("std::mutex") || source_str.contains("std::shared_mutex");
    if !has_mutex {
        return;
    }

    let has_lock = source_str.contains("lock_guard")
        || source_str.contains("unique_lock")
        || source_str.contains("shared_lock")
        || source_str.contains("scoped_lock");

    if !has_lock {
        // File has mutex but no lock guard usage — flag
        for m in find_pattern(source_str, "std::mutex") {
            findings.push(make_finding_from_text("RACE-003", file_path, &m));
        }
        for m in find_pattern(source_str, "std::shared_mutex") {
            findings.push(make_finding_from_text("RACE-003", file_path, &m));
        }
    }
}

// =============================================================================
// LeakFree Checker
// =============================================================================

fn check_leak_free(
    _tree: &Tree,
    _source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    // LEAK-001: fopen without RAII wrapper
    check_fopen_leak(source_str, file_path, findings);

    // LEAK-002: Missing virtual destructor in class with virtual methods
    if is_cpp {
        check_missing_virtual_dtor(source_str, file_path, findings);
    }

    // LEAK-003: Socket/handle patterns without RAII
    check_handle_leak(source_str, file_path, findings);

    Ok(())
}

/// LEAK-001: fopen/open calls in C++ code (should use RAII fstream).
fn check_fopen_leak(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    for m in find_pattern(source_str, "fopen(") {
        findings.push(make_finding_from_text("LEAK-001", file_path, &m));
    }
    for m in find_pattern(source_str, "fopen_s(") {
        findings.push(make_finding_from_text("LEAK-001", file_path, &m));
    }
}

/// LEAK-002: Class with virtual methods but non-virtual destructor.
fn check_missing_virtual_dtor(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // Heuristic: Find class/struct definitions with `virtual` methods,
    // then check if the destructor is also virtual.
    let mut in_class = false;
    let mut class_start_line = 0usize;
    let mut class_name = String::new();
    let mut brace_depth = 0i32;
    let mut has_virtual_method = false;
    let mut has_virtual_dtor = false;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        // Detect class/struct start
        if !in_class {
            let is_class_def = (trimmed.starts_with("class ") || trimmed.starts_with("struct "))
                && (trimmed.contains('{') || !trimmed.contains(';'));

            if is_class_def {
                in_class = true;
                class_start_line = line_idx + 1;
                brace_depth = 0;
                has_virtual_method = false;
                has_virtual_dtor = false;

                // Extract class name
                let parts: Vec<&str> = trimmed.split_whitespace().collect();
                class_name = parts.get(1).unwrap_or(&"").trim_end_matches(':').to_string();
                class_name = class_name.trim_end_matches('{').trim().to_string();
            }
        }

        if in_class {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            // Check for virtual methods
            if trimmed.contains("virtual ") && !trimmed.contains('~') {
                has_virtual_method = true;
            }

            // Check for virtual destructor
            if trimmed.contains("virtual") && trimmed.contains('~') {
                has_virtual_dtor = true;
            }

            // End of class
            if brace_depth <= 0 && trimmed.contains('}') {
                if has_virtual_method && !has_virtual_dtor && !class_name.is_empty() {
                    let loc = SourceLocation::new(
                        file_path,
                        class_start_line,
                        1,
                        line_idx + 1,
                        1,
                    );
                    let snippet = snippet_at_line(source_str, class_start_line, 0);
                    let mut finding = make_finding("LEAK-002", loc, snippet);
                    finding.metadata.insert("class".to_string(), class_name.clone());
                    findings.push(finding);
                }
                in_class = false;
            }
        }
    }
}

/// LEAK-003: socket/handle patterns without RAII.
fn check_handle_leak(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let handle_funcs = ["socket(", "accept(", "open(", "creat(", "dup(", "pipe("];
    for func in &handle_funcs {
        for m in find_pattern(source_str, func) {
            // Skip if it's a method call (obj.open) or in a comment
            if m.snippet.contains('.') && m.snippet.find('.').unwrap_or(usize::MAX) < m.snippet.find(func).unwrap_or(0) {
                continue;
            }
            // Skip if wrapped in an RAII constructor
            if m.snippet.contains("unique_fd")
                || m.snippet.contains("ScopedFd")
                || m.snippet.contains("FileDescriptor")
            {
                continue;
            }
            // Only flag the raw OS call pattern
            if *func == "open(" || *func == "socket(" || *func == "accept(" {
                findings.push(make_finding_from_text("LEAK-003", file_path, &m));
            }
        }
    }
}

// =============================================================================
// DetDrop Checker
// =============================================================================

fn check_det_drop(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // DETD-001: Global/static variables with non-trivial types
    check_global_statics(source_str, file_path, findings);
}

/// DETD-001: Static/global objects with non-trivial destructors.
fn check_global_statics(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let nontrivial_types = [
        "std::string", "std::vector", "std::map", "std::unordered_map",
        "std::set", "std::unordered_set", "std::list", "std::deque",
        "std::shared_ptr", "std::unique_ptr",
    ];

    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // Track brace depth to detect file scope
        brace_depth += trimmed.matches('{').count() as i32;
        brace_depth -= trimmed.matches('}').count() as i32;

        // Only flag at file scope (brace_depth == 0) or namespace scope
        if brace_depth > 1 {
            continue;
        }

        // Look for static/global declarations with non-trivial types
        let is_static = trimmed.starts_with("static ") || trimmed.starts_with("thread_local ");
        let is_global = brace_depth == 0 && !trimmed.starts_with("static ")
            && !trimmed.starts_with('#')
            && !trimmed.starts_with("//")
            && !trimmed.starts_with("namespace")
            && !trimmed.starts_with("class")
            && !trimmed.starts_with("struct")
            && !trimmed.starts_with("enum")
            && !trimmed.starts_with("typedef")
            && !trimmed.starts_with("using")
            && !trimmed.starts_with("template")
            && !trimmed.starts_with("extern")
            && !trimmed.starts_with("inline")
            && !trimmed.starts_with("constexpr")
            && !trimmed.starts_with("void")
            && !trimmed.starts_with("int ")
            && !trimmed.starts_with("auto ")
            && !trimmed.starts_with('{')
            && !trimmed.starts_with('}')
            && !trimmed.is_empty();

        if is_static || is_global {
            for nt in &nontrivial_types {
                if trimmed.contains(nt) {
                    let loc = SourceLocation::new(file_path, line_idx + 1, 1, line_idx + 1, trimmed.len());
                    let mut finding = make_finding("DETD-001", loc, trimmed.to_string());
                    finding.metadata.insert("type".to_string(), (*nt).to_string());
                    findings.push(finding);
                    break;
                }
            }
        }
    }
}

// =============================================================================
// Performance Checker
// =============================================================================

fn check_performance(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    // PERF-001: std::unordered_map fields
    check_std_type_field(source_str, file_path, "std::unordered_map", "PERF-001", findings);

    // PERF-002: std::atomic without alignas(64)
    check_atomic_alignment(source_str, file_path, findings);

    // PERF-005: std::function fields
    check_std_type_field(source_str, file_path, "std::function", "PERF-005", findings);
}

/// PERF-002: std::atomic field without alignas for false sharing prevention.
fn check_atomic_alignment(source_str: &str, file_path: &str, findings: &mut Vec<CppSafetyFinding>) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;
    let mut struct_has_alignas = false;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && trimmed.contains('{')
        {
            in_struct = true;
            brace_depth = 0;
            struct_has_alignas = trimmed.contains("alignas(");
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 {
                in_struct = false;
                continue;
            }

            // Check for atomic fields without their own alignas
            if trimmed.contains("std::atomic") || trimmed.contains("atomic<") {
                if !trimmed.contains("alignas(") && !struct_has_alignas {
                    let loc = SourceLocation::new(
                        file_path,
                        line_idx + 1,
                        1,
                        line_idx + 1,
                        trimmed.len(),
                    );
                    findings.push(make_finding("PERF-002", loc, trimmed.to_string()));
                }
            }
        }
    }
}

// =============================================================================
// AntiPattern Checker
// =============================================================================

fn check_anti_patterns(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    lang_name: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    if !is_cpp {
        return Ok(());
    }

    // ANTI-001: RTTI usage (dynamic_cast, typeid)
    for m in find_pattern(source_str, "dynamic_cast<") {
        findings.push(make_finding_from_text("ANTI-001", file_path, &m));
    }
    for m in find_pattern(source_str, "typeid(") {
        findings.push(make_finding_from_text("ANTI-001", file_path, &m));
    }

    // ANTI-002: std::variant fields
    check_std_type_field(source_str, file_path, "std::variant", "ANTI-002", findings);

    // ANTI-003: throw statements
    check_throw_statements(tree, source, file_path, source_str, lang_name, findings)?;

    Ok(())
}

/// ANTI-003: Detect throw statements via tree-sitter.
fn check_throw_statements(
    tree: &Tree,
    source: &[u8],
    file_path: &str,
    source_str: &str,
    _lang_name: &str,
    findings: &mut Vec<CppSafetyFinding>,
) -> Result<()> {
    let ts_lang = tree.language();
    let query = match Query::new(&ts_lang, THROW_QUERY) {
        Ok(q) => q,
        Err(_) => {
            // Fallback to text search if grammar doesn't have throw_statement
            for m in find_pattern(source_str, "throw ") {
                // Skip `throw;` (rethrow) and comments
                if m.snippet.trim() == "throw;" {
                    continue;
                }
                findings.push(make_finding_from_text("ANTI-003", file_path, &m));
            }
            return Ok(());
        }
    };

    let expr_idx = query.capture_index_for_name("expr").unwrap_or(0);
    let mut cursor = QueryCursor::new();
    let mut matches = cursor.matches(&query, tree.root_node(), source);

    while let Some(m) = matches.next() {
        if let Some(cap) = m.captures.iter().find(|c| c.index == expr_idx) {
            let loc = location_from_node(cap.node, file_path);
            let snippet = snippet_at_line(source_str, loc.line, 0);
            findings.push(make_finding("ANTI-003", loc, snippet));
        }
    }

    Ok(())
}

// =============================================================================
// Lifetime Safety Checker (§1.5.1 D3390)
// =============================================================================

/// Non-owning view types that create dangling references when bound to temporaries.
const VIEW_TYPES: &[&str] = &[
    "string_view", "std::string_view",
    "span", "std::span", "gsl::span",
    "QStringView",
];

fn check_lifetime_safety(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    check_view_from_temporary(source_str, file_path, findings);
    check_view_as_member(source_str, file_path, findings);
    check_return_view_to_local(source_str, file_path, findings);
}

/// LIFE-001 / LIFE-002: string_view or span initialized from a temporary.
///
/// Detects patterns like:
///   string_view sv = std::string("hello");
///   string_view sv = func_returning_string();
///   span<int> s = std::vector<int>{1,2,3};
///   string_view sv = a + b;  (string concatenation yields temporary)
fn check_view_from_temporary(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    // Temporary-producing patterns on the RHS of a view initialization
    let string_temp_patterns = [
        "std::string(", "std::string{",
        "std::to_string(", "to_string(",
        ".str()", ".string()",
        "substr(", ".c_str()",
    ];

    let container_temp_patterns = [
        "std::vector<", "std::vector{",
        "std::array<", "std::array{",
        "std::initializer_list",
    ];

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // Check for string_view bound to string temporary
        let has_sv = trimmed.contains("string_view")
            && (trimmed.contains('=') || trimmed.contains("string_view("));

        if has_sv {
            // Split at '=' to check RHS
            let rhs = if let Some(eq_pos) = trimmed.find('=') {
                &trimmed[eq_pos + 1..]
            } else {
                trimmed
            };

            for pat in &string_temp_patterns {
                if rhs.contains(pat) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-001", loc, trimmed.to_string()));
                    break;
                }
            }

            // Also catch string concatenation (a + b where result is temp string)
            // Pattern: string_view sv = expr + expr; (contains '+' and string-ish types)
            if rhs.contains(" + ") && (rhs.contains("\"") || rhs.contains("str")) {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-001", loc, trimmed.to_string()));
            }
        }

        // Check for span bound to container temporary
        let has_span = (trimmed.contains("span<") || trimmed.contains("span "))
            && (trimmed.contains('=') || trimmed.contains("span(") || trimmed.contains("span{"));

        if has_span {
            let rhs = if let Some(eq_pos) = trimmed.find('=') {
                &trimmed[eq_pos + 1..]
            } else {
                trimmed
            };

            for pat in &container_temp_patterns {
                if rhs.contains(pat) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-002", loc, trimmed.to_string()));
                    break;
                }
            }

            // Brace-enclosed initializer list: span<int> s = {1, 2, 3};
            if rhs.trim_start().starts_with('{') {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-002", loc, trimmed.to_string()));
            }
        }
    }
}

/// LIFE-003: string_view or span stored as struct/class member field.
fn check_view_as_member(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let mut in_struct = false;
    let mut brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();

        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && (trimmed.contains('{') || !trimmed.contains(';'))
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 && trimmed.contains('}') {
                in_struct = false;
                continue;
            }

            // Only look at brace_depth == 1 (direct members, not nested structs)
            if brace_depth != 1 {
                continue;
            }

            if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
                continue;
            }

            // Skip methods (contain parens for params), skip access specifiers
            if trimmed.contains('(') || trimmed.starts_with("public")
                || trimmed.starts_with("private") || trimmed.starts_with("protected")
                || trimmed.starts_with("friend") || trimmed.starts_with("using")
                || trimmed.starts_with("static ") || trimmed.starts_with("constexpr ")
            {
                continue;
            }

            // Check for view types in field declarations
            for vt in VIEW_TYPES {
                if trimmed.contains(vt) {
                    let col = trimmed.find(vt).unwrap_or(0);
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, col + 1, line_idx + 1, col + vt.len() + 1,
                    );
                    findings.push(make_finding("LIFE-003", loc, trimmed.to_string()));
                    break;
                }
            }
        }
    }
}

/// LIFE-004: Function returning string_view/span constructed from local data.
///
/// Detects patterns like:
///   std::string_view get_name() { std::string s = ...; return s; }
///   std::string_view get_name() { ... return std::string_view(local); }
fn check_return_view_to_local(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();
    let mut func_returns_view = false;
    let mut func_brace_depth = 0i32;
    let mut in_func_body = false;
    let mut local_vars: Vec<String> = Vec::new();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Detect function declarations that return a view type
        // Pattern: "string_view funcname(" or "auto funcname(...) -> string_view"
        if !in_func_body {
            let returns_view = VIEW_TYPES.iter().any(|vt| {
                // Return type at start: string_view foo(
                (trimmed.contains(vt) && trimmed.contains('(')
                    && trimmed.find(vt).unwrap_or(usize::MAX) < trimmed.find('(').unwrap_or(0))
                // Trailing return type: -> string_view
                || (trimmed.contains("->") && trimmed.contains(vt)
                    && trimmed.find("->").unwrap_or(0) < trimmed.find(vt).unwrap_or(usize::MAX))
            });

            if returns_view && (trimmed.contains('{') || trimmed.ends_with('{')) {
                func_returns_view = true;
                in_func_body = true;
                func_brace_depth = 0;
                local_vars.clear();
            }
        }

        if in_func_body {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // Track local variable declarations inside the function
            if trimmed.contains('=') && !trimmed.starts_with("return")
                && !trimmed.starts_with("if") && !trimmed.starts_with("for")
            {
                // Extract potential variable name before '='
                if let Some(eq_pos) = trimmed.find('=') {
                    let before_eq = trimmed[..eq_pos].trim();
                    // Last token before '=' is the variable name
                    if let Some(var) = before_eq.split_whitespace().last() {
                        let clean = var.trim_start_matches('*').trim_start_matches('&');
                        if !clean.is_empty() && clean.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            local_vars.push(clean.to_string());
                        }
                    }
                }
            }

            // Look for return statements that construct views from locals
            if func_returns_view && trimmed.starts_with("return ") {
                let return_expr = &trimmed["return ".len()..].trim_end_matches(';').trim();

                // Check if return expr is a known local variable name
                let is_local_var = local_vars.iter().any(|v| v == return_expr);

                // Also flag explicit view construction from a local
                let constructs_view = VIEW_TYPES.iter().any(|vt| return_expr.contains(vt));

                if is_local_var || constructs_view {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-004", loc, trimmed.to_string()));
                }
            }

            if func_brace_depth <= 0 {
                in_func_body = false;
                func_returns_view = false;
            }
        }
    }
}

// =============================================================================
// Iterator Invalidation Checker (§2.2.2 D3390)
// =============================================================================

/// Methods that invalidate iterators/references on sequence containers.
const INVALIDATING_METHODS: &[&str] = &[
    "push_back", "emplace_back", "push_front", "emplace_front",
    "insert", "emplace", "erase", "clear", "resize", "reserve",
    "assign", "pop_back", "pop_front",
];

fn check_iterator_invalidation(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    check_range_for_invalidation(source_str, file_path, findings);
    check_iterator_loop_invalidation(source_str, file_path, findings);
}

/// LIFE-005: Range-for loop body mutates the iterated container.
///
/// Detects: `for (auto& x : vec) { vec.push_back(...); }`
fn check_range_for_invalidation(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Match range-for: for (...keyword... : container_name)
        if !trimmed.starts_with("for ") && !trimmed.starts_with("for(") {
            continue;
        }

        // Extract the container name after ':'
        let Some(colon_pos) = trimmed.find(':') else { continue };
        let after_colon = &trimmed[colon_pos + 1..];
        // Trim to closing paren
        let Some(paren_pos) = after_colon.find(')') else { continue };
        let container = after_colon[..paren_pos].trim();

        // Container must be a simple identifier (not a function call or complex expression)
        if container.is_empty()
            || container.contains('(')
            || container.contains('<')
            || container.contains('"')
            || !container.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            continue;
        }

        // Scan the loop body for mutations on this container
        let mut brace_depth = 0i32;
        let mut started = false;

        for body_line_idx in line_idx..lines.len() {
            let body_trimmed = lines[body_line_idx].trim();
            brace_depth += body_trimmed.matches('{').count() as i32;
            brace_depth -= body_trimmed.matches('}').count() as i32;

            if body_trimmed.contains('{') {
                started = true;
            }

            if started && brace_depth <= 0 {
                break;
            }

            if !started {
                continue;
            }

            // Look for container.invalidating_method(
            for method in INVALIDATING_METHODS {
                let pattern = format!("{container}.{method}(");
                if body_trimmed.contains(&pattern) {
                    let loc = SourceLocation::new(
                        file_path,
                        body_line_idx + 1,
                        1,
                        body_line_idx + 1,
                        body_trimmed.len(),
                    );
                    let mut finding = make_finding("LIFE-005", loc, body_trimmed.to_string());
                    finding.metadata.insert("container".to_string(), container.to_string());
                    finding.metadata.insert("method".to_string(), method.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// LIFE-006: Iterator loop body mutates the container the iterator came from.
///
/// Detects: `for (auto it = vec.begin(); it != vec.end(); ++it) { vec.push_back(...); }`
fn check_iterator_loop_invalidation(
    source_str: &str,
    file_path: &str,
    findings: &mut Vec<CppSafetyFinding>,
) {
    let lines: Vec<&str> = source_str.lines().collect();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if !trimmed.starts_with("for ") && !trimmed.starts_with("for(") {
            continue;
        }

        // Look for .begin() or .cbegin() in the for-init
        let container = extract_iterator_container(trimmed);
        let Some(container) = container else { continue };

        // Scan loop body
        let mut brace_depth = 0i32;
        let mut started = false;

        for body_line_idx in line_idx..lines.len() {
            let body_trimmed = lines[body_line_idx].trim();
            brace_depth += body_trimmed.matches('{').count() as i32;
            brace_depth -= body_trimmed.matches('}').count() as i32;

            if body_trimmed.contains('{') {
                started = true;
            }

            if started && brace_depth <= 0 {
                break;
            }

            if !started || body_line_idx == line_idx {
                continue;
            }

            for method in INVALIDATING_METHODS {
                let pattern = format!("{container}.{method}(");
                if body_trimmed.contains(&pattern) {
                    let loc = SourceLocation::new(
                        file_path,
                        body_line_idx + 1,
                        1,
                        body_line_idx + 1,
                        body_trimmed.len(),
                    );
                    let mut finding = make_finding("LIFE-006", loc, body_trimmed.to_string());
                    finding.metadata.insert("container".to_string(), container.to_string());
                    finding.metadata.insert("method".to_string(), method.to_string());
                    findings.push(finding);
                }
            }
        }
    }
}

/// Extract container name from iterator-based for loop init.
/// Looks for patterns like `container.begin()`, `container.cbegin()`, `std::begin(container)`.
fn extract_iterator_container(for_line: &str) -> Option<String> {
    // Pattern: something.begin() or something.cbegin()
    for begin_fn in &[".begin()", ".cbegin()", ".rbegin()"] {
        if let Some(pos) = for_line.find(begin_fn) {
            // Walk backwards from '.' to find the container name
            let before_dot = &for_line[..pos];
            // Last token is the container
            let container = before_dot.split(|c: char| !c.is_alphanumeric() && c != '_')
                .filter(|s| !s.is_empty())
                .last()?;
            if container.chars().all(|c| c.is_alphanumeric() || c == '_') {
                return Some(container.to_string());
            }
        }
    }
    None
}

// =============================================================================
// Initializer List Dangling Checker (§2.2.3 D3390)
// =============================================================================

fn check_initializer_list_dangling(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    let mut in_struct = false;
    let mut brace_depth = 0i32;
    let mut in_function = false;
    let mut func_brace_depth = 0i32;

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // Track struct scope for LIFE-010
        if (trimmed.starts_with("struct ") || trimmed.starts_with("class "))
            && (trimmed.contains('{') || !trimmed.contains(';'))
        {
            in_struct = true;
            brace_depth = 0;
        }

        if in_struct {
            brace_depth += trimmed.matches('{').count() as i32;
            brace_depth -= trimmed.matches('}').count() as i32;

            if brace_depth <= 0 && trimmed.contains('}') {
                in_struct = false;
            }

            // LIFE-010: initializer_list as class member
            if brace_depth == 1 && trimmed.contains("initializer_list")
                && !trimmed.contains('(')  // not a method
                && !trimmed.starts_with("friend")
                && !trimmed.starts_with("using")
            {
                let col = trimmed.find("initializer_list").unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-010", loc, trimmed.to_string()));
            }
        }

        // Track function scope for LIFE-008
        if !in_function && trimmed.contains('(') && trimmed.contains('{')
            && !trimmed.starts_with("struct") && !trimmed.starts_with("class")
            && !trimmed.starts_with("enum") && !trimmed.starts_with("namespace")
        {
            in_function = true;
            func_brace_depth = 0;
        }

        if in_function {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // LIFE-008: Local variable of type initializer_list
            if trimmed.contains("initializer_list") && trimmed.contains('=') {
                let col = trimmed.find("initializer_list").unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-008", loc, trimmed.to_string()));
            }

            if func_brace_depth <= 0 {
                in_function = false;
            }
        }
    }
}

// =============================================================================
// Return Reference/Pointer to Local Checker (§2.2 D3390)
// =============================================================================

/// LIFE-011: Function returning reference or pointer to a local variable.
fn check_return_ref_to_local(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    let lines: Vec<&str> = source_str.lines().collect();
    let mut func_returns_ref = false;
    let mut func_returns_ptr = false;
    let mut in_func_body = false;
    let mut func_brace_depth = 0i32;
    let mut local_vars: Vec<String> = Vec::new();

    for (line_idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Detect function returning reference or pointer
        if !in_func_body {
            // Skip lambda expressions — they have [capture] before (params)
            let is_lambda = trimmed.contains("[&]") || trimmed.contains("[=]")
                || trimmed.contains("[this]") || trimmed.contains("[&,")
                || trimmed.contains(", &]") || trimmed.contains("[=,");

            if !is_lambda {
                // Check for reference return: T& func( or const T& func(
                let returns_ref = (trimmed.contains("& ") || trimmed.contains("&\t"))
                    && trimmed.contains('(')
                    && !trimmed.starts_with("//")
                    && !trimmed.contains("operator")
                    // Ensure & is in return type, not parameter
                    && trimmed.find('&').unwrap_or(usize::MAX)
                        < trimmed.find('(').unwrap_or(0);

                // Check for pointer return: T* func(
                let returns_ptr = trimmed.contains("* ")
                    && trimmed.contains('(')
                    && !trimmed.starts_with("//")
                    && !trimmed.contains("operator")
                    && trimmed.find('*').unwrap_or(usize::MAX)
                        < trimmed.find('(').unwrap_or(0);

                if (returns_ref || returns_ptr)
                    && (trimmed.contains('{') || trimmed.ends_with('{'))
                {
                    func_returns_ref = returns_ref;
                    func_returns_ptr = returns_ptr;
                    in_func_body = true;
                    func_brace_depth = 0;
                    local_vars.clear();
                }
            }
        }

        if in_func_body {
            func_brace_depth += trimmed.matches('{').count() as i32;
            func_brace_depth -= trimmed.matches('}').count() as i32;

            // Track local variable declarations
            if trimmed.contains('=') && !trimmed.starts_with("return")
                && !trimmed.starts_with("if") && !trimmed.starts_with("for")
            {
                if let Some(eq_pos) = trimmed.find('=') {
                    let before_eq = trimmed[..eq_pos].trim();
                    if let Some(var) = before_eq.split_whitespace().last() {
                        let clean = var.trim_start_matches('*').trim_start_matches('&');
                        if !clean.is_empty() && clean.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            local_vars.push(clean.to_string());
                        }
                    }
                }
            }

            // Check return statements
            if trimmed.starts_with("return ") && (func_returns_ref || func_returns_ptr) {
                let return_expr = trimmed["return ".len()..].trim_end_matches(';').trim();

                // For reference returns: `return local_var;`
                // For pointer returns: `return &local_var;`
                let returned_var = if return_expr.starts_with('&') {
                    return_expr[1..].trim()
                } else {
                    return_expr
                };

                if local_vars.iter().any(|v| v == returned_var) {
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-011", loc, trimmed.to_string()));
                }
            }

            if func_brace_depth <= 0 {
                in_func_body = false;
                func_returns_ref = false;
                func_returns_ptr = false;
            }
        }
    }
}

/// LIFE-013: Lambda with [&] capture escaping scope.
/// LIFE-014: std::ref/std::cref usage (potential dangling wrapper).
fn check_lambda_ref_escape(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // LIFE-013: Lambda with [&] that's returned, stored in std::function, or passed to thread/async
        if trimmed.contains("[&]") || trimmed.contains("[&,") || trimmed.contains(", &]") {
            let lambda_pos = trimmed.find("[&]")
                .or_else(|| trimmed.find("[&,"))
                .or_else(|| trimmed.find(", &]"))
                .unwrap_or(0);

            // Explicit escape mechanisms (always flag regardless of return)
            let has_escape_mechanism = trimmed.contains("std::function")
                || trimmed.contains("std::thread")
                || trimmed.contains("std::async")
                || trimmed.contains("std::jthread")
                || trimmed.contains("detach");

            // `return [&]` — lambda itself being returned directly
            let lambda_returned_directly = trimmed.starts_with("return ")
                && trimmed[7..].trim().starts_with("[&");

            // `return` before `[&]` WITHOUT escape mechanism = inline use
            // e.g., `return data.match([&](...) { ... });` — not escaping
            let return_before_lambda = trimmed.starts_with("return ")
                && lambda_pos > 7;
            let is_inline_use = return_before_lambda && !has_escape_mechanism;

            if !is_inline_use && (has_escape_mechanism || lambda_returned_directly) {
                let col = lambda_pos;
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("LIFE-013", loc, trimmed.to_string()));
            }
        }

        // LIFE-014: std::ref / std::cref
        for ref_fn in &["std::ref(", "std::cref("] {
            if trimmed.contains(ref_fn) {
                // Flag if it's being passed to thread, async, or stored
                let is_risky = trimmed.contains("thread")
                    || trimmed.contains("async")
                    || trimmed.contains("bind")
                    || trimmed.contains("function");

                if is_risky {
                    let col = trimmed.find(ref_fn).unwrap_or(0);
                    let loc = SourceLocation::new(
                        file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                    );
                    findings.push(make_finding("LIFE-014", loc, trimmed.to_string()));
                }
            }
        }
    }
}

/// §2.1 Unsafe Context: operations that D3390 prohibits in safe context.
/// UCTX-001: Pointer arithmetic (ptr+n, ptr++, *(ptr+n)).
/// UCTX-002: Pointer difference.
/// UCTX-004: Union type definitions.
/// UCTX-005: Non-const static/global mutable variables.
/// UCTX-006: Inline assembly.
fn check_unsafe_context(
    source_str: &str,
    file_path: &str,
    is_cpp: bool,
    findings: &mut Vec<CppSafetyFinding>,
) {
    if !is_cpp {
        return;
    }

    for (line_idx, line) in source_str.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") || trimmed.starts_with("/*") || trimmed.starts_with('*') {
            continue;
        }

        // UCTX-001: Pointer arithmetic — dereference of arithmetic result *(ptr + n)
        // Also detect ptr++ / ++ptr / ptr-- / --ptr on pointer-like variables
        if trimmed.contains("*(") && (trimmed.contains(" + ") || trimmed.contains(" - ")) {
            // Pattern: *(identifier + expr) or *(identifier - expr)
            if let Some(star_paren) = trimmed.find("*(") {
                let inside = &trimmed[star_paren + 2..];
                if let Some(close) = inside.find(')') {
                    let expr = &inside[..close];
                    if expr.contains('+') || expr.contains('-') {
                        let loc = SourceLocation::new(
                            file_path, line_idx + 1, star_paren + 1,
                            line_idx + 1, trimmed.len(),
                        );
                        findings.push(make_finding("UCTX-001", loc, trimmed.to_string()));
                    }
                }
            }
        }

        // UCTX-004: Union type definition
        // Match `union Name {` but not `std::variant` or inside comments
        if (trimmed.starts_with("union ") || trimmed.contains(" union "))
            && trimmed.contains('{')
            && !trimmed.contains("std::")
            && !trimmed.contains("typedef")
        {
            let col = trimmed.find("union").unwrap_or(0);
            let loc = SourceLocation::new(
                file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
            );
            findings.push(make_finding("UCTX-004", loc, trimmed.to_string()));
        }

        // UCTX-005: Non-const static mutable variable
        // Match `static Type name` but not `static const`, `static constexpr`,
        // `static_assert`, function declarations, or class member declarations
        if trimmed.starts_with("static ") && !trimmed.starts_with("static_") {
            let after_static = trimmed["static ".len()..].trim();
            let is_const = after_static.starts_with("const ")
                || after_static.starts_with("constexpr ")
                || after_static.starts_with("constinit ");
            let is_function = trimmed.contains('(');
            let is_class_keyword = after_static.starts_with("void ")
                || after_static.starts_with("auto ")
                || after_static.starts_with("inline ");
            // Must have `=` or `;` to be a variable declaration, not a function
            let is_var_decl = trimmed.contains('=') || (trimmed.ends_with(';') && !is_function);

            if !is_const && is_var_decl && !is_class_keyword {
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("UCTX-005", loc, trimmed.to_string()));
            }
        }

        // UCTX-006: Inline assembly
        for asm_kw in &["asm(", "asm (", "__asm(", "__asm (", "__asm__(", "__asm__ (", "asm volatile(", "asm volatile ("] {
            if trimmed.contains(asm_kw) {
                let col = trimmed.find(asm_kw).unwrap_or(0);
                let loc = SourceLocation::new(
                    file_path, line_idx + 1, col + 1, line_idx + 1, trimmed.len(),
                );
                findings.push(make_finding("UCTX-006", loc, trimmed.to_string()));
                break; // one finding per line
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn scan_cpp(code: &str) -> Vec<CppSafetyFinding> {
        let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
        file.write_all(code.as_bytes()).unwrap();
        file.flush().unwrap();
        let config = CppSafetyConfig::default();
        scan_file_cpp_safety(file.path(), &config).unwrap()
    }

    fn scan_c(code: &str) -> Vec<CppSafetyFinding> {
        let mut file = NamedTempFile::with_suffix(".c").unwrap();
        file.write_all(code.as_bytes()).unwrap();
        file.flush().unwrap();
        let config = CppSafetyConfig::default();
        scan_file_cpp_safety(file.path(), &config).unwrap()
    }

    fn findings_with_rule<'a>(findings: &'a [CppSafetyFinding], rule_id: &str) -> Vec<&'a CppSafetyFinding> {
        findings.iter().filter(|f| f.rule_id == rule_id).collect()
    }

    // ── InitSafe tests ──────────────────────────────────────────────────────

    #[test]
    fn test_init001_field_without_nsdmi() {
        let findings = scan_cpp(r#"
struct Widget {
    int x;
    float y;
    bool active;
};
"#);
        let init_findings = findings_with_rule(&findings, "INIT-001");
        assert!(!init_findings.is_empty(), "Should flag fields without NSDMI");
    }

    #[test]
    fn test_init001_field_with_nsdmi_clean() {
        let findings = scan_cpp(r#"
struct Widget {
    int x = 0;
    float y = 1.0f;
    bool active = false;
};
"#);
        let init_findings = findings_with_rule(&findings, "INIT-001");
        assert!(init_findings.is_empty(), "Should NOT flag fields with NSDMI");
    }

    #[test]
    fn test_init002_padding_array() {
        let findings = scan_cpp(r#"
struct Packet {
    int type;
    uint8_t padding[3];
};
"#);
        let pad_findings = findings_with_rule(&findings, "INIT-002");
        // padding without {} should be flagged
        assert!(!pad_findings.is_empty(), "Should flag padding array without zero-init");
    }

    #[test]
    fn test_init004_uninit_local() {
        let findings = scan_cpp(r#"
void foo() {
    int result;
    float value;
    result = compute();
}
"#);
        let uninit_findings = findings_with_rule(&findings, "INIT-004");
        assert!(!uninit_findings.is_empty(), "Should flag uninitialized locals");
    }

    // ── TypeSafe tests ──────────────────────────────────────────────────────

    #[test]
    fn test_type001_plain_enum() {
        let findings = scan_cpp(r#"
enum Color {
    Red,
    Green,
    Blue
};
"#);
        let type_findings = findings_with_rule(&findings, "TYPE-001");
        assert!(!type_findings.is_empty(), "Should flag plain enum");
    }

    #[test]
    fn test_type001_enum_class_clean() {
        let findings = scan_cpp(r#"
enum class Color {
    Red,
    Green,
    Blue
};
"#);
        let type_findings = findings_with_rule(&findings, "TYPE-001");
        assert!(type_findings.is_empty(), "Should NOT flag enum class");
    }

    #[test]
    fn test_type004_reinterpret_cast() {
        let findings = scan_cpp(r#"
void foo(void* ptr) {
    auto x = reinterpret_cast<int*>(ptr);
}
"#);
        let cast_findings = findings_with_rule(&findings, "TYPE-004");
        assert!(!cast_findings.is_empty(), "Should flag reinterpret_cast");
    }

    #[test]
    fn test_type004_no_reinterpret_cast_clean() {
        let findings = scan_cpp(r#"
void foo(void* ptr) {
    auto x = static_cast<int*>(ptr);
}
"#);
        let cast_findings = findings_with_rule(&findings, "TYPE-004");
        assert!(cast_findings.is_empty(), "Should NOT flag static_cast");
    }

    // ── NullSafe tests ──────────────────────────────────────────────────────

    #[test]
    fn test_null002_malloc_no_check() {
        let findings = scan_c(r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    buf[0] = 'a';
}
"#);
        let null_findings = findings_with_rule(&findings, "NULL-002");
        assert!(!null_findings.is_empty(), "Should flag malloc without null check");
    }

    #[test]
    fn test_null002_malloc_with_check_clean() {
        let findings = scan_c(r#"
#include <stdlib.h>
void foo() {
    char *buf = malloc(1024);
    if (buf == NULL) return;
    buf[0] = 'a';
}
"#);
        let null_findings = findings_with_rule(&findings, "NULL-002");
        assert!(null_findings.is_empty(), "Should NOT flag malloc with null check");
    }

    // ── MemSafe tests ───────────────────────────────────────────────────────

    #[test]
    fn test_mem001_raw_new() {
        let findings = scan_cpp(r#"
void foo() {
    auto p = new int(42);
}
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-001");
        assert!(!mem_findings.is_empty(), "Should flag raw new");
    }

    #[test]
    fn test_mem001_make_unique_clean() {
        let findings = scan_cpp(r#"
#include <memory>
void foo() {
    auto p = std::make_unique<int>(42);
}
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-001");
        assert!(mem_findings.is_empty(), "Should NOT flag make_unique");
    }

    #[test]
    fn test_mem002_raw_delete() {
        let findings = scan_cpp(r#"
void foo(int* p) {
    delete p;
}
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-002");
        assert!(!mem_findings.is_empty(), "Should flag raw delete");
    }

    #[test]
    fn test_mem003_delete_without_reason() {
        let findings = scan_cpp(r#"
struct NonCopyable {
    NonCopyable(const NonCopyable&) = delete;
    NonCopyable& operator=(const NonCopyable&) = delete;
};
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-003");
        assert!(!mem_findings.is_empty(), "Should flag = delete without reason");
    }

    #[test]
    fn test_mem006_shared_ptr() {
        let findings = scan_cpp(r#"
#include <memory>
void foo() {
    std::shared_ptr<int> p = std::make_shared<int>(42);
}
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-006");
        assert!(!mem_findings.is_empty(), "Should flag std::shared_ptr usage");
    }

    #[test]
    fn test_mem008_alloc_multiply() {
        let findings = scan_c(r#"
#include <stdlib.h>
void foo(size_t count) {
    int *arr = malloc(count * sizeof(int));
}
"#);
        let mem_findings = findings_with_rule(&findings, "MEM-008");
        assert!(!mem_findings.is_empty(), "Should flag unchecked multiplication in malloc");
    }

    // ── RaceFree tests ──────────────────────────────────────────────────────

    #[test]
    fn test_race001_mutable_field() {
        let findings = scan_cpp(r#"
class Cache {
    mutable int hits_;
    std::string data_;
};
"#);
        let race_findings = findings_with_rule(&findings, "RACE-001");
        assert!(!race_findings.is_empty(), "Should flag mutable non-sync field");
    }

    #[test]
    fn test_race001_mutable_mutex_clean() {
        let findings = scan_cpp(r#"
class Cache {
    mutable std::mutex mutex_;
    int data_;
};
"#);
        let race_findings = findings_with_rule(&findings, "RACE-001");
        assert!(race_findings.is_empty(), "Should NOT flag mutable mutex");
    }

    #[test]
    fn test_race002_thread_detach() {
        let findings = scan_cpp(r#"
#include <thread>
void foo() {
    std::thread t([]{ /* work */ });
    t.detach();
}
"#);
        let race_findings = findings_with_rule(&findings, "RACE-002");
        assert!(!race_findings.is_empty(), "Should flag thread detach");
    }

    // ── LeakFree tests ──────────────────────────────────────────────────────

    #[test]
    fn test_leak001_fopen() {
        let findings = scan_cpp(r#"
#include <cstdio>
void foo() {
    FILE* fp = fopen("data.txt", "r");
    fclose(fp);
}
"#);
        let leak_findings = findings_with_rule(&findings, "LEAK-001");
        assert!(!leak_findings.is_empty(), "Should flag fopen in C++ code");
    }

    #[test]
    fn test_leak002_missing_virtual_dtor() {
        let findings = scan_cpp(r#"
class Base {
public:
    virtual void work() = 0;
    ~Base() {}
};
"#);
        let leak_findings = findings_with_rule(&findings, "LEAK-002");
        assert!(!leak_findings.is_empty(), "Should flag missing virtual destructor");
    }

    #[test]
    fn test_leak002_virtual_dtor_clean() {
        let findings = scan_cpp(r#"
class Base {
public:
    virtual void work() = 0;
    virtual ~Base() = default;
};
"#);
        let leak_findings = findings_with_rule(&findings, "LEAK-002");
        assert!(leak_findings.is_empty(), "Should NOT flag virtual destructor");
    }

    // ── DetDrop tests ───────────────────────────────────────────────────────

    #[test]
    fn test_detd001_global_string() {
        let findings = scan_cpp(r#"
static std::string global_name = "hello";
void foo() {}
"#);
        let detd_findings = findings_with_rule(&findings, "DETD-001");
        assert!(!detd_findings.is_empty(), "Should flag static std::string");
    }

    #[test]
    fn test_detd001_constexpr_clean() {
        let findings = scan_cpp(r#"
static constexpr int GLOBAL_CONST = 42;
void foo() {}
"#);
        let detd_findings = findings_with_rule(&findings, "DETD-001");
        assert!(detd_findings.is_empty(), "Should NOT flag constexpr int");
    }

    // ── Performance tests ───────────────────────────────────────────────────

    #[test]
    fn test_perf002_atomic_no_alignas() {
        let findings = scan_cpp(r#"
struct Counter {
    std::atomic<int> value;
    int padding;
};
"#);
        let perf_findings = findings_with_rule(&findings, "PERF-002");
        assert!(!perf_findings.is_empty(), "Should flag atomic without alignas");
    }

    #[test]
    fn test_perf002_atomic_with_alignas_clean() {
        let findings = scan_cpp(r#"
struct alignas(64) Counter {
    std::atomic<int> value;
    int padding;
};
"#);
        let perf_findings = findings_with_rule(&findings, "PERF-002");
        assert!(perf_findings.is_empty(), "Should NOT flag atomic with struct alignas");
    }

    // ── AntiPattern tests ───────────────────────────────────────────────────

    #[test]
    fn test_anti001_dynamic_cast() {
        let findings = scan_cpp(r#"
class Base { virtual ~Base() = default; };
class Derived : public Base {};
void foo(Base* b) {
    auto d = dynamic_cast<Derived*>(b);
}
"#);
        let anti_findings = findings_with_rule(&findings, "ANTI-001");
        assert!(!anti_findings.is_empty(), "Should flag dynamic_cast");
    }

    #[test]
    fn test_anti003_throw() {
        let findings = scan_cpp(r#"
void foo(int x) {
    if (x < 0) throw std::runtime_error("negative");
}
"#);
        let anti_findings = findings_with_rule(&findings, "ANTI-003");
        assert!(!anti_findings.is_empty(), "Should flag throw statement");
    }

    // ── Profile/filter tests ────────────────────────────────────────────────

    #[test]
    fn test_crucible_profile_excludes_perf() {
        let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
        file.write_all(b"
struct Counter {
    std::atomic<int> value;
    int data;
};
void foo() {
    auto p = new int(42);
}
").unwrap();
        file.flush().unwrap();

        let config = CppSafetyConfig {
            profile: CppSafetyProfile::Crucible,
            ..Default::default()
        };
        let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

        // MEM-001 (MemSafe axiom) should be included
        assert!(findings.iter().any(|f| f.rule_id == "MEM-001"));
        // PERF-002 (Performance) should be excluded
        assert!(!findings.iter().any(|f| f.rule_id == "PERF-002"));
    }

    #[test]
    fn test_axiom_filter() {
        let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
        file.write_all(b"
enum Color { Red, Green, Blue };
void foo() {
    auto p = new int(42);
}
").unwrap();
        file.flush().unwrap();

        let config = CppSafetyConfig {
            axiom_filter: Some(SafetyAxiom::TypeSafe),
            ..Default::default()
        };
        let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

        // Only TypeSafe findings should appear
        for f in &findings {
            assert_eq!(f.axiom, SafetyAxiom::TypeSafe, "All findings should be TypeSafe");
        }
    }

    #[test]
    fn test_severity_filter() {
        let mut file = NamedTempFile::with_suffix(".cpp").unwrap();
        file.write_all(b"
void foo() {
    auto p = new int(42);
    auto x = reinterpret_cast<char*>(p);
}
").unwrap();
        file.flush().unwrap();

        let config = CppSafetyConfig {
            min_severity: Severity::High,
            ..Default::default()
        };
        let findings = scan_file_cpp_safety(file.path(), &config).unwrap();

        for f in &findings {
            assert!(f.severity >= Severity::High, "Only High+ findings should appear");
        }
    }

    #[test]
    fn test_c_file_skips_cpp_rules() {
        let findings = scan_c(r#"
enum color { RED, GREEN, BLUE };
void foo() {}
"#);
        // TYPE-001 (plain enum) should NOT fire for C files
        let type_findings = findings_with_rule(&findings, "TYPE-001");
        assert!(type_findings.is_empty(), "Plain enum in C should NOT be flagged");
    }

    #[test]
    fn test_report_axiom_summary() {
        let findings = scan_cpp(r#"
void foo() {
    auto p = new int(42);
    delete p;
}
"#);
        let report = build_report(findings, 1);
        assert!(report.axiom_summary.contains_key("MemSafe"));
    }

    // ── Helper tests ────────────────────────────────────────────────────────

    #[test]
    fn test_find_pattern_skips_comments() {
        let source = r#"
// reinterpret_cast<int*>(x)
auto y = reinterpret_cast<float*>(z);
"#;
        let matches = find_pattern(source, "reinterpret_cast<");
        assert_eq!(matches.len(), 1, "Should skip commented-out cast");
        assert_eq!(matches[0].line, 3);
    }

    #[test]
    fn test_find_pattern_multiple_matches() {
        let source = "int a; int b; int c;";
        let matches = find_pattern(source, "int ");
        assert_eq!(matches.len(), 3);
    }

    #[test]
    fn test_safety_axiom_display() {
        assert_eq!(SafetyAxiom::MemSafe.to_string(), "MemSafe");
        assert_eq!(SafetyAxiom::RaceFree.to_string(), "RaceFree");
        assert_eq!(SafetyAxiom::DetDrop.to_string(), "DetDrop");
    }

    #[test]
    fn test_safety_axiom_parse() {
        assert_eq!("mem".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::MemSafe);
        assert_eq!("race".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::RaceFree);
        assert_eq!("det".parse::<SafetyAxiom>().unwrap(), SafetyAxiom::DetDrop);
        assert!("invalid".parse::<SafetyAxiom>().is_err());
    }

    #[test]
    fn test_profile_parse() {
        assert_eq!("crucible".parse::<CppSafetyProfile>().unwrap(), CppSafetyProfile::Crucible);
        assert_eq!("standard".parse::<CppSafetyProfile>().unwrap(), CppSafetyProfile::Standard);
    }

    #[test]
    fn test_lookup_rule() {
        let rule = lookup_rule("MEM-001").unwrap();
        assert_eq!(rule.axiom, SafetyAxiom::MemSafe);
        assert_eq!(rule.severity, Severity::High);
    }

    #[test]
    fn test_all_rules_have_unique_ids() {
        let mut ids: Vec<&str> = RULES.iter().map(|r| r.id).collect();
        let original_len = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), original_len, "Duplicate rule IDs found");
    }

    // ── Lifetime Safety tests (LIFE-001 to LIFE-004) ─────────────────────

    #[test]
    fn test_life001_string_view_from_temp_string() {
        let findings = scan_cpp(r#"
void foo() {
    std::string_view sv = std::string("hello");
}
"#);
        let life = findings_with_rule(&findings, "LIFE-001");
        assert!(!life.is_empty(), "Should flag string_view from temporary std::string");
    }

    #[test]
    fn test_life001_string_view_from_substr() {
        let findings = scan_cpp(r#"
void foo(std::string s) {
    std::string_view sv = s.substr(0, 5);
}
"#);
        let life = findings_with_rule(&findings, "LIFE-001");
        assert!(!life.is_empty(), "Should flag string_view from substr (returns temp)");
    }

    #[test]
    fn test_life001_string_view_from_named_ok() {
        let findings = scan_cpp(r#"
void foo() {
    std::string s = "hello";
    std::string_view sv = s;
}
"#);
        let life = findings_with_rule(&findings, "LIFE-001");
        assert!(life.is_empty(), "Should NOT flag string_view from named variable");
    }

    #[test]
    fn test_life002_span_from_temp_vector() {
        let findings = scan_cpp(r#"
void foo() {
    std::span<int> s = std::vector<int>{1, 2, 3};
}
"#);
        let life = findings_with_rule(&findings, "LIFE-002");
        assert!(!life.is_empty(), "Should flag span from temporary vector");
    }

    #[test]
    fn test_life003_view_as_class_member() {
        let findings = scan_cpp(r#"
struct Config {
    std::string_view name;
    int value;
};
"#);
        let life = findings_with_rule(&findings, "LIFE-003");
        assert!(!life.is_empty(), "Should flag string_view as class member");
    }

    #[test]
    fn test_life003_string_member_ok() {
        let findings = scan_cpp(r#"
struct Config {
    std::string name;
    int value;
};
"#);
        let life = findings_with_rule(&findings, "LIFE-003");
        assert!(life.is_empty(), "Should NOT flag std::string as member");
    }

    #[test]
    fn test_life004_return_view_to_local() {
        let findings = scan_cpp(r#"
std::string_view get_name() {
    std::string s = "hello";
    return s;
}
"#);
        let life = findings_with_rule(&findings, "LIFE-004");
        assert!(!life.is_empty(), "Should flag returning string_view to local");
    }

    #[test]
    fn test_life004_return_string_ok() {
        let findings = scan_cpp(r#"
std::string get_name() {
    std::string s = "hello";
    return s;
}
"#);
        let life = findings_with_rule(&findings, "LIFE-004");
        assert!(life.is_empty(), "Should NOT flag returning std::string (owning)");
    }

    // ── Iterator Invalidation tests (LIFE-005 to LIFE-007) ───────────────

    #[test]
    fn test_life005_range_for_push_back() {
        let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        if (x > 0) vec.push_back(x * 2);
    }
}
"#);
        let life = findings_with_rule(&findings, "LIFE-005");
        assert!(!life.is_empty(), "Should flag push_back during range-for");
    }

    #[test]
    fn test_life005_range_for_erase() {
        let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        vec.erase(vec.begin());
    }
}
"#);
        let life = findings_with_rule(&findings, "LIFE-005");
        assert!(!life.is_empty(), "Should flag erase during range-for");
    }

    #[test]
    fn test_life005_range_for_read_ok() {
        let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto& x : vec) {
        int y = vec.size();
    }
}
"#);
        let life = findings_with_rule(&findings, "LIFE-005");
        assert!(life.is_empty(), "Should NOT flag read-only access during range-for");
    }

    #[test]
    fn test_life006_iterator_loop_push_back() {
        let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto it = vec.begin(); it != vec.end(); ++it) {
        vec.push_back(*it);
    }
}
"#);
        let life = findings_with_rule(&findings, "LIFE-006");
        assert!(!life.is_empty(), "Should flag push_back during iterator loop");
    }

    #[test]
    fn test_life006_iterator_loop_no_mutation_ok() {
        let findings = scan_cpp(r#"
void foo(std::vector<int>& vec) {
    for (auto it = vec.begin(); it != vec.end(); ++it) {
        std::cout << *it;
    }
}
"#);
        let life = findings_with_rule(&findings, "LIFE-006");
        assert!(life.is_empty(), "Should NOT flag read-only iterator loop");
    }

    // ── Initializer List Dangling tests (LIFE-008 to LIFE-010) ───────────

    #[test]
    fn test_life008_local_initializer_list() {
        let findings = scan_cpp(r#"
void foo() {
    std::initializer_list<int> il = {1, 2, 3};
    use(il);
}
"#);
        let life = findings_with_rule(&findings, "LIFE-008");
        assert!(!life.is_empty(), "Should flag local initializer_list variable");
    }

    #[test]
    fn test_life010_member_initializer_list() {
        let findings = scan_cpp(r#"
struct Widget {
    std::initializer_list<int> values;
    int count;
};
"#);
        let life = findings_with_rule(&findings, "LIFE-010");
        assert!(!life.is_empty(), "Should flag initializer_list as class member");
    }

    #[test]
    fn test_life010_vector_member_ok() {
        let findings = scan_cpp(r#"
struct Widget {
    std::vector<int> values;
    int count;
};
"#);
        let life = findings_with_rule(&findings, "LIFE-010");
        assert!(life.is_empty(), "Should NOT flag std::vector member");
    }

    // ── Return Ref/Ptr to Local tests (LIFE-011 to LIFE-014) ────────────

    #[test]
    fn test_life011_return_ref_to_local() {
        let findings = scan_cpp(r#"
const std::string& get_name() {
    std::string name = "hello";
    return name;
}
"#);
        let life = findings_with_rule(&findings, "LIFE-011");
        assert!(!life.is_empty(), "Should flag returning reference to local");
    }

    #[test]
    fn test_life011_return_ptr_to_local() {
        let findings = scan_cpp(r#"
int* get_value() {
    int val = 42;
    return &val;
}
"#);
        let life = findings_with_rule(&findings, "LIFE-011");
        assert!(!life.is_empty(), "Should flag returning pointer to local");
    }

    #[test]
    fn test_life011_return_member_ok() {
        let findings = scan_cpp(r#"
class Foo {
    std::string name_;
    const std::string& get_name() {
        return name_;
    }
};
"#);
        let life = findings_with_rule(&findings, "LIFE-011");
        assert!(life.is_empty(), "Should NOT flag returning reference to member");
    }

    #[test]
    fn test_life013_lambda_ref_escape() {
        let findings = scan_cpp(r#"
std::function<void()> make_func() {
    int x = 42;
    return std::function<void()>([&] { use(x); });
}
"#);
        let life = findings_with_rule(&findings, "LIFE-013");
        assert!(!life.is_empty(), "Should flag lambda [&] escaping via std::function return");
    }

    #[test]
    fn test_life013_lambda_value_capture_ok() {
        let findings = scan_cpp(r#"
std::function<void()> make_func() {
    int x = 42;
    return std::function<void()>([=] { use(x); });
}
"#);
        let life = findings_with_rule(&findings, "LIFE-013");
        assert!(life.is_empty(), "Should NOT flag lambda [=] (value capture)");
    }

    // ── Unsafe Context tests (UCTX-001 to UCTX-006) ────────────────────────

    #[test]
    fn test_uctx001_pointer_arithmetic() {
        let findings = scan_cpp(r#"
void process(int* data, int n) {
    int val = *(data + 3);
    int val2 = *(data - 1);
}
"#);
        let uctx = findings_with_rule(&findings, "UCTX-001");
        assert!(uctx.len() >= 2, "Should flag *(ptr + n) and *(ptr - n)");
    }

    #[test]
    fn test_uctx001_no_false_positive_on_normal_math() {
        let findings = scan_cpp(r#"
int compute(int a, int b) {
    return a + b;
}
"#);
        let uctx = findings_with_rule(&findings, "UCTX-001");
        assert!(uctx.is_empty(), "Should NOT flag regular integer arithmetic");
    }

    #[test]
    fn test_uctx004_union_definition() {
        let findings = scan_cpp(r#"
union Value {
    int i;
    float f;
    char* s;
};
"#);
        let uctx = findings_with_rule(&findings, "UCTX-004");
        assert!(!uctx.is_empty(), "Should flag union definition");
    }

    #[test]
    fn test_uctx005_mutable_static() {
        let findings = scan_cpp(r#"
static int counter = 0;
static const int MAX = 100;
static constexpr int SIZE = 64;
"#);
        let uctx = findings_with_rule(&findings, "UCTX-005");
        assert_eq!(uctx.len(), 1, "Should flag only the mutable static, not const/constexpr");
    }

    #[test]
    fn test_uctx006_inline_assembly() {
        let findings = scan_cpp(r#"
void barrier() {
    asm volatile("mfence" ::: "memory");
}
void other() {
    __asm__("nop");
}
"#);
        let uctx = findings_with_rule(&findings, "UCTX-006");
        assert!(uctx.len() >= 2, "Should flag both asm volatile and __asm__");
    }

    #[test]
    fn test_uctx006_no_false_positive() {
        let findings = scan_cpp(r#"
// This is an asm comment
void assemble_data() {
    int x = 42;
}
"#);
        let uctx = findings_with_rule(&findings, "UCTX-006");
        assert!(uctx.is_empty(), "Should NOT flag function with 'asm' in name or comment");
    }
}
