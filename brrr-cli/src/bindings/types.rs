//! Core types for cross-language binding detection.

use std::collections::HashMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::callgraph::types::FunctionRef;

/// Identifies which binding technology was detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BindingSystem {
    Pybind11,
    Ctypes,
    RustFfi,
    CGo,
    Jni,
    NapiRs,
    CudaDispatch,
    TorchLibrary,
}

impl BindingSystem {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Pybind11 => "pybind11",
            Self::Ctypes => "ctypes",
            Self::RustFfi => "rust_ffi",
            Self::CGo => "cgo",
            Self::Jni => "jni",
            Self::NapiRs => "napi_rs",
            Self::CudaDispatch => "cuda_dispatch",
            Self::TorchLibrary => "torch_library",
        }
    }

    /// Languages involved: (host_language, target_language).
    pub fn language_pair(&self) -> (&'static str, &'static str) {
        match self {
            Self::Pybind11 => ("cpp", "python"),
            Self::Ctypes => ("python", "c"),
            Self::RustFfi => ("rust", "c"),
            Self::CGo => ("go", "c"),
            Self::Jni => ("java", "c"),
            Self::NapiRs => ("rust", "typescript"),
            Self::CudaDispatch => ("cpp", "cpp"),
            Self::TorchLibrary => ("cpp", "cpp"),
        }
    }

    /// All known binding systems.
    pub const ALL: &'static [BindingSystem] = &[
        Self::Pybind11,
        Self::Ctypes,
        Self::RustFfi,
        Self::CGo,
        Self::Jni,
        Self::NapiRs,
        Self::CudaDispatch,
        Self::TorchLibrary,
    ];
}

impl fmt::Display for BindingSystem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Direction of the binding relationship.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BindingDirection {
    /// Host language exposes a function to target (e.g., C++ → Python via pybind11).
    Export,
    /// Host language calls into target (e.g., Python → C via ctypes).
    Import,
    /// Registration/dispatch pattern (e.g., REGISTER_DISPATCH linking stub → kernel).
    Dispatch,
}

impl fmt::Display for BindingDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Export => f.write_str("export"),
            Self::Import => f.write_str("import"),
            Self::Dispatch => f.write_str("dispatch"),
        }
    }
}

/// A single detected binding declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BindingDeclaration {
    /// The binding technology used.
    pub system: BindingSystem,
    /// Direction of the binding.
    pub direction: BindingDirection,
    /// The exposed name visible in the target language.
    pub exposed_name: String,
    /// The host-side function that implements the binding (may be partial — name only, no file).
    pub host_function: Option<FunctionRef>,
    /// The target-side function reference (populated by cross-file resolver).
    pub target_function: Option<FunctionRef>,
    /// File where the binding declaration was found.
    pub declaration_file: String,
    /// Line number of the binding declaration.
    pub declaration_line: usize,
    /// Module/namespace (pybind11 module name, TORCH_LIBRARY namespace).
    pub module_name: Option<String>,
    /// Class name for method bindings (py::class_ name, JNI class).
    pub class_name: Option<String>,
    /// Raw matched text for debugging.
    pub raw_pattern: Option<String>,
    /// Confidence score (0.0–1.0). 1.0 for macro patterns, lower for heuristic.
    pub confidence: f64,
}

/// Result of scanning a project for bindings.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BindingReport {
    /// All detected binding declarations.
    pub declarations: Vec<BindingDeclaration>,
    /// Per-system counts.
    pub by_system: HashMap<String, usize>,
    /// Total files scanned.
    pub files_scanned: usize,
    /// Files that contained at least one binding.
    pub files_with_bindings: usize,
    /// Bindings where host/target could not be resolved.
    pub unresolved_count: usize,
}

impl BindingReport {
    /// Build report from a list of declarations and scan stats.
    pub fn from_declarations(
        declarations: Vec<BindingDeclaration>,
        files_scanned: usize,
        files_with_bindings: usize,
    ) -> Self {
        let mut by_system: HashMap<String, usize> = HashMap::new();
        let mut unresolved_count = 0;

        for decl in &declarations {
            *by_system.entry(decl.system.as_str().to_string()).or_default() += 1;
            if decl.host_function.is_none() && decl.target_function.is_none() {
                unresolved_count += 1;
            }
        }

        Self {
            declarations,
            by_system,
            files_scanned,
            files_with_bindings,
            unresolved_count,
        }
    }
}

/// Per-file raw detection output (before cross-file resolution).
#[derive(Debug)]
pub(crate) struct FileBindings {
    #[allow(dead_code)]
    pub file_path: String,
    #[allow(dead_code)]
    pub language: String,
    pub declarations: Vec<BindingDeclaration>,
}
