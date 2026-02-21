//! Type definitions for the C++ safety analyzer.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::security::common::{Confidence, Severity, SourceLocation};

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
