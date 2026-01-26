//! Analysis pipeline orchestration
//!
//! Provides compilation pipeline connecting all analysis passes.
//! Following F* compilation pipeline patterns for modular, configurable analysis.
//!
//! # Pipeline Stages
//!
//! The pipeline executes analysis passes in order with dependency tracking:
//!
//! 1. **Parse** (input is `Module`) - parsing is assumed complete
//! 2. **Name resolution** - resolve identifiers to definitions (TODO: separate pass)
//! 3. **Type inference** - Hindley-Milner type inference with bidirectional typing
//! 4. **Effect inference** - row-polymorphic effect tracking
//! 5. **Mode checking** - linearity/mode verification
//! 6. **Borrow checking** - ownership and lifetime verification
//! 7. **Session type checking** - binary/multiparty session protocol verification (opt-in)
//! 8. **Coeffect checking** - capability and resource tracking (opt-in)
//! 9. **Gradual cast insertion** - insert runtime checks for gradual types (opt-in)
//! 10. **Contract verification** - verify pre/postconditions (opt-in)
//!
//! # Example Usage
//!
//! ```ignore
//! use brrr_repr::pipeline::{compile, CompilationConfig, CompilationResult};
//! use brrr_repr::decl::Module;
//!
//! let module = Module::new("main");
//! let config = CompilationConfig::default();
//! let result = compile(&module, &config);
//!
//! if result.has_errors() {
//!     for err in &result.errors {
//!         eprintln!("Error: {:?}", err);
//!     }
//! } else {
//!     println!("Compilation successful!");
//! }
//! ```
//!
//! # Error Recovery
//!
//! The pipeline supports error recovery through `compile_with_recovery`:
//!
//! ```ignore
//! use brrr_repr::pipeline::{compile_with_recovery, CompilationConfig};
//!
//! let result = compile_with_recovery(&module, &config);
//! // Collects all errors without stopping at first failure
//! println!("Found {} errors, {} warnings", result.errors.len(), result.warnings.len());
//! ```

use std::collections::HashMap;

use lasso::Key;
use serde::{Deserialize, Serialize};

use crate::api::BrrrModule;
use crate::borrow::{BorrowState, ExtendedBorrowState, OwnershipError};
use crate::decl::Module;
use crate::effects::EffectRow;
use crate::expr::Range;
use crate::inference::{
    CoeffectError, CoeffectInferenceState, EffectError, EffectInferenceState, InferenceState,
    ModeCheckState, ModeError, RegionError, RegionInferenceState, SessionCheckState, SessionError,
    TypeCtx, TypeError,
    // Resolution types
    ResolutionState,
};
use crate::types::{BrrrType, TypeVar};
use crate::verification::Formula;

// ============================================================================
// Compilation Configuration
// ============================================================================

/// Configuration for the compilation pipeline.
///
/// Controls which analysis passes are enabled and their behavior.
/// Disabled passes are skipped entirely, reducing compilation time
/// for incremental or partial analysis scenarios.
///
/// # Defaults
///
/// By default, core analysis passes are enabled:
/// - Type checking: enabled
/// - Effect checking: enabled
/// - Borrow checking: enabled
/// - Mode checking: enabled
///
/// Advanced passes are opt-in:
/// - Session checking: disabled
/// - Contract verification: disabled
/// - Gradual casts: disabled
/// - Coeffect checking: disabled
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompilationConfig {
    /// Enable type inference and checking pass.
    ///
    /// When enabled, performs Hindley-Milner type inference with
    /// bidirectional typing support. Required for most other passes.
    pub type_check: bool,

    /// Enable effect inference and checking pass.
    ///
    /// When enabled, tracks computational effects (IO, exceptions, etc.)
    /// using row-polymorphic effect types.
    pub effect_check: bool,

    /// Enable borrow checking pass.
    ///
    /// When enabled, verifies ownership, borrowing, and lifetime rules.
    /// Catches use-after-move, double-free, and borrow conflicts.
    pub borrow_check: bool,

    /// Enable mode (linearity) checking pass.
    ///
    /// When enabled, verifies that linear/affine/relevant variables
    /// are used according to their mode constraints.
    pub mode_check: bool,

    /// Enable session type checking pass.
    ///
    /// When enabled, verifies that communication channels follow
    /// their declared session protocols. Opt-in because it requires
    /// explicit session type annotations.
    pub session_check: bool,

    /// Enable contract verification pass.
    ///
    /// When enabled, attempts to verify that functions satisfy their
    /// pre/postcondition contracts. Opt-in because it may require
    /// external SMT solver interaction.
    pub verify_contracts: bool,

    /// Enable gradual type cast insertion.
    ///
    /// When enabled, inserts runtime casts at gradual type boundaries.
    /// Opt-in for performance-critical code.
    pub gradual_casts: bool,

    /// Enable coeffect checking pass.
    ///
    /// When enabled, tracks resource usage, capabilities, and context
    /// requirements using coeffect types. Opt-in for specialized
    /// resource tracking scenarios.
    pub coeffect_check: bool,

    /// Maximum recursion depth for type inference.
    ///
    /// Limits infinite loops from cyclic type definitions.
    /// Default: 100.
    pub max_inference_depth: u32,

    /// Stop compilation on first error.
    ///
    /// When true, stops at the first error encountered.
    /// When false, continues to collect all errors.
    pub fail_fast: bool,

    /// Enable verbose diagnostic output.
    ///
    /// When true, includes additional context in error messages.
    pub verbose_diagnostics: bool,
}

impl Default for CompilationConfig {
    fn default() -> Self {
        Self {
            // Core passes: enabled by default
            type_check: true,
            effect_check: true,
            borrow_check: true,
            mode_check: true,
            // Advanced passes: opt-in
            session_check: false,
            verify_contracts: false,
            gradual_casts: false,
            coeffect_check: false,
            // Limits
            max_inference_depth: 100,
            fail_fast: false,
            verbose_diagnostics: false,
        }
    }
}

impl CompilationConfig {
    /// Create a minimal configuration with only type checking.
    ///
    /// Useful for quick syntax validation without full analysis.
    #[must_use]
    pub fn minimal() -> Self {
        Self {
            type_check: true,
            effect_check: false,
            borrow_check: false,
            mode_check: false,
            session_check: false,
            verify_contracts: false,
            gradual_casts: false,
            coeffect_check: false,
            max_inference_depth: 100,
            fail_fast: true,
            verbose_diagnostics: false,
        }
    }

    /// Create a full configuration with all passes enabled.
    ///
    /// Useful for thorough verification in CI/release builds.
    #[must_use]
    pub fn full() -> Self {
        Self {
            type_check: true,
            effect_check: true,
            borrow_check: true,
            mode_check: true,
            session_check: true,
            verify_contracts: true,
            gradual_casts: true,
            coeffect_check: true,
            max_inference_depth: 100,
            fail_fast: false,
            verbose_diagnostics: true,
        }
    }

    /// Enable fail-fast mode.
    #[must_use]
    pub fn with_fail_fast(mut self) -> Self {
        self.fail_fast = true;
        self
    }

    /// Enable verbose diagnostics.
    #[must_use]
    pub fn with_verbose(mut self) -> Self {
        self.verbose_diagnostics = true;
        self
    }

    /// Enable session type checking.
    #[must_use]
    pub fn with_session_check(mut self) -> Self {
        self.session_check = true;
        self
    }

    /// Enable contract verification.
    #[must_use]
    pub fn with_contracts(mut self) -> Self {
        self.verify_contracts = true;
        self
    }

    /// Check if any verification passes are enabled.
    #[must_use]
    pub fn has_verification(&self) -> bool {
        self.verify_contracts || self.session_check
    }
}

// ============================================================================
// Compilation Errors and Warnings
// ============================================================================

/// Unified compilation error type.
///
/// Wraps errors from all analysis passes into a single enum
/// for consistent error handling and reporting.
#[derive(Debug, Clone)]
pub enum CompilationError {
    /// Type inference or checking error
    Type(TypeError),

    /// Effect inference or checking error
    Effect(EffectError),

    /// Ownership or borrowing error
    Borrow(OwnershipError),

    /// Mode (linearity) checking error
    Mode(ModeError),

    /// Session type checking error
    Session(SessionError),

    /// Coeffect checking error
    Coeffect(CoeffectError),

    /// Region/lifetime inference error
    Region(RegionError),

    /// Contract verification error
    Verification(VerificationError),

    /// Name resolution error
    Resolution(ResolutionError),
}

impl CompilationError {
    /// Get the source range where this error occurred.
    #[must_use]
    pub fn span(&self) -> Option<Range> {
        match self {
            Self::Type(e) => Some(e.span),
            Self::Effect(e) => Some(e.span),
            Self::Mode(e) => Some(e.span()),
            Self::Session(e) => Some(e.span()),
            Self::Coeffect(e) => Some(e.span()),
            Self::Region(e) => Some(e.span()),
            Self::Verification(e) => e.span,
            Self::Resolution(e) => Some(e.span),
            Self::Borrow(_) => None, // OwnershipError doesn't track span
        }
    }

    /// Get a short error code for this error.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            Self::Type(_) => "TYPE",
            Self::Effect(_) => "EFFECT",
            Self::Borrow(e) => e.code(),
            Self::Mode(_) => "MODE",
            Self::Session(_) => "SESSION",
            Self::Coeffect(_) => "COEFFECT",
            Self::Region(_) => "REGION",
            Self::Verification(_) => "VERIFY",
            Self::Resolution(_) => "RESOLVE",
        }
    }

    /// Get the error category.
    #[must_use]
    pub fn category(&self) -> ErrorCategory {
        match self {
            Self::Type(_) => ErrorCategory::TypeSystem,
            Self::Effect(_) => ErrorCategory::EffectSystem,
            Self::Borrow(_) => ErrorCategory::Ownership,
            Self::Mode(_) => ErrorCategory::Linearity,
            Self::Session(_) => ErrorCategory::Protocol,
            Self::Coeffect(_) => ErrorCategory::Resource,
            Self::Region(_) => ErrorCategory::Lifetime,
            Self::Verification(_) => ErrorCategory::Contract,
            Self::Resolution(_) => ErrorCategory::Name,
        }
    }
}

impl std::fmt::Display for CompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Type(e) => write!(f, "[{}] {}", self.code(), e),
            Self::Effect(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Borrow(e) => write!(f, "[{}] {}", self.code(), e),
            Self::Mode(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Session(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Coeffect(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Region(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Verification(e) => write!(f, "[{}] {:?}", self.code(), e),
            Self::Resolution(e) => write!(f, "[{}] {:?}", self.code(), e),
        }
    }
}

impl std::error::Error for CompilationError {}

/// Error category for grouping related errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorCategory {
    /// Type system errors (type mismatch, unbound type, etc.)
    TypeSystem,
    /// Effect system errors (effect mismatch, unhandled effect, etc.)
    EffectSystem,
    /// Ownership errors (use-after-move, borrow conflicts, etc.)
    Ownership,
    /// Linearity errors (unused linear variable, duplicate use, etc.)
    Linearity,
    /// Protocol errors (session type violations)
    Protocol,
    /// Resource errors (capability violations)
    Resource,
    /// Lifetime errors (dangling reference, region escape, etc.)
    Lifetime,
    /// Contract verification errors (precondition failure, etc.)
    Contract,
    /// Name resolution errors (unbound variable, shadowing, etc.)
    Name,
}

/// Contract verification error.
#[derive(Debug, Clone)]
pub struct VerificationError {
    /// Kind of verification failure
    pub kind: VerificationErrorKind,
    /// Source location if available
    pub span: Option<Range>,
    /// Additional context message
    pub message: Option<String>,
}

/// Kind of verification error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationErrorKind {
    /// Precondition may not hold
    PreconditionFailure,
    /// Postcondition may not hold
    PostconditionFailure,
    /// Loop invariant may not hold
    InvariantFailure,
    /// Assertion may not hold
    AssertionFailure,
    /// Variant may not decrease
    VariantFailure,
    /// Verification timeout
    Timeout,
    /// Verification is undecidable
    Undecidable,
}

impl VerificationError {
    /// Create a precondition failure error.
    #[must_use]
    pub fn precondition(span: Range, message: impl Into<String>) -> Self {
        Self {
            kind: VerificationErrorKind::PreconditionFailure,
            span: Some(span),
            message: Some(message.into()),
        }
    }

    /// Create a postcondition failure error.
    #[must_use]
    pub fn postcondition(span: Range, message: impl Into<String>) -> Self {
        Self {
            kind: VerificationErrorKind::PostconditionFailure,
            span: Some(span),
            message: Some(message.into()),
        }
    }

    /// Create a timeout error.
    #[must_use]
    pub fn timeout() -> Self {
        Self {
            kind: VerificationErrorKind::Timeout,
            span: None,
            message: Some("verification timed out".into()),
        }
    }
}

/// Name resolution error.
#[derive(Debug, Clone)]
pub struct ResolutionError {
    /// Kind of resolution failure
    pub kind: ResolutionErrorKind,
    /// The name that couldn't be resolved
    pub name: String,
    /// Source location
    pub span: Range,
}

/// Kind of resolution error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionErrorKind {
    /// Variable not found in scope
    UnboundVariable,
    /// Type not found in scope
    UnboundType,
    /// Module not found
    UnboundModule,
    /// Ambiguous name (multiple definitions)
    AmbiguousName,
    /// Private item accessed from outside module
    PrivateAccess,
}

/// Compilation warning.
///
/// Non-fatal issues that don't prevent compilation but may indicate problems.
#[derive(Debug, Clone)]
pub struct CompilationWarning {
    /// Warning kind
    pub kind: WarningKind,
    /// Source location
    pub span: Range,
    /// Warning message
    pub message: String,
}

/// Kind of compilation warning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WarningKind {
    /// Unused variable
    UnusedVariable,
    /// Unused import
    UnusedImport,
    /// Unreachable code
    UnreachableCode,
    /// Deprecated feature usage
    Deprecated,
    /// Potential performance issue
    Performance,
    /// Gradual type cast inserted
    GradualCast,
    /// Dead code detected
    DeadCode,
}

impl CompilationWarning {
    /// Create an unused variable warning.
    #[must_use]
    pub fn unused_variable(name: &str, span: Range) -> Self {
        Self {
            kind: WarningKind::UnusedVariable,
            span,
            message: format!("unused variable: `{}`", name),
        }
    }

    /// Create an unreachable code warning.
    #[must_use]
    pub fn unreachable(span: Range, reason: &str) -> Self {
        Self {
            kind: WarningKind::UnreachableCode,
            span,
            message: format!("unreachable code: {}", reason),
        }
    }

    /// Create a gradual cast warning.
    #[must_use]
    pub fn gradual_cast(span: Range, from_ty: &str, to_ty: &str) -> Self {
        Self {
            kind: WarningKind::GradualCast,
            span,
            message: format!("runtime cast inserted: {} -> {}", from_ty, to_ty),
        }
    }
}

// ============================================================================
// Analysis Info Types
// ============================================================================

/// Type information collected during type inference.
#[derive(Debug, Clone, Default)]
pub struct TypeInfo {
    /// Inferred types for expressions (by expression ID)
    pub expr_types: HashMap<u32, BrrrType>,
    /// Type variable substitutions
    pub substitution: HashMap<TypeVar, BrrrType>,
    /// Type schemes for let-bound variables
    pub schemes: HashMap<TypeVar, crate::types::TypeScheme>,
}

impl TypeInfo {
    /// Create empty type info.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up the type of an expression.
    #[must_use]
    pub fn expr_type(&self, expr_id: u32) -> Option<&BrrrType> {
        self.expr_types.get(&expr_id)
    }

    /// Apply substitution to resolve all type variables.
    pub fn resolve(&mut self) {
        let subst = self.substitution.clone();
        for ty in self.expr_types.values_mut() {
            *ty = crate::inference::apply_substitution(ty, &subst);
        }
    }
}

/// Effect information collected during effect inference.
#[derive(Debug, Clone, Default)]
pub struct EffectInfo {
    /// Inferred effect rows for expressions
    pub expr_effects: HashMap<u32, EffectRow>,
    /// Effect handlers in scope
    pub handlers: Vec<HandlerInfo>,
}

/// Information about an effect handler.
#[derive(Debug, Clone)]
pub struct HandlerInfo {
    /// Effect being handled
    pub effect: String,
    /// Handler location
    pub span: Range,
    /// Whether handler is complete (handles all operations)
    pub is_complete: bool,
}

impl EffectInfo {
    /// Create empty effect info.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

/// Borrow information collected during borrow checking.
#[derive(Debug, Clone, Default)]
pub struct BorrowInfo {
    /// Final borrow state after checking
    pub final_state: Option<BorrowState>,
    /// Loan information for debugging
    pub loan_origins: HashMap<u32, LoanOrigin>,
    /// Region constraints (for lifetime inference)
    pub region_constraints: Vec<RegionConstraint>,
}

/// Origin of a loan (for error reporting).
#[derive(Debug, Clone)]
pub struct LoanOrigin {
    /// Variable being borrowed
    pub var: TypeVar,
    /// Location of the borrow
    pub span: Range,
    /// Kind of borrow (shared/exclusive)
    pub kind: crate::borrow::BorrowKind,
}

/// Region outlives constraint.
#[derive(Debug, Clone)]
pub struct RegionConstraint {
    /// Region that must outlive
    pub longer: crate::types::Region,
    /// Region that is outlived
    pub shorter: crate::types::Region,
    /// Source of constraint
    pub span: Range,
}

impl BorrowInfo {
    /// Create empty borrow info.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

// ============================================================================
// Compilation Result
// ============================================================================

/// Result of the compilation pipeline.
///
/// Contains the compiled module along with all analysis information
/// and any errors/warnings encountered during compilation.
#[derive(Debug, Clone)]
pub struct CompilationResult {
    /// The compiled module (may be incomplete if errors occurred)
    pub module: BrrrModule,

    /// Type information from type inference pass
    pub type_info: Option<TypeInfo>,

    /// Effect information from effect inference pass
    pub effect_info: Option<EffectInfo>,

    /// Borrow information from borrow checking pass
    pub borrow_info: Option<BorrowInfo>,

    /// Collected verification conditions (if contract verification enabled)
    pub verification_conditions: Vec<VerificationCondition>,

    /// Compilation errors (fatal issues)
    pub errors: Vec<CompilationError>,

    /// Compilation warnings (non-fatal issues)
    pub warnings: Vec<CompilationWarning>,

    /// Analysis pass that failed (if any)
    pub failed_pass: Option<PassId>,
}

impl CompilationResult {
    /// Create an empty compilation result.
    #[must_use]
    pub fn new(module_name: &str) -> Self {
        Self {
            module: BrrrModule::new(module_name),
            type_info: None,
            effect_info: None,
            borrow_info: None,
            verification_conditions: Vec::new(),
            errors: Vec::new(),
            warnings: Vec::new(),
            failed_pass: None,
        }
    }

    /// Check if compilation succeeded without errors.
    #[must_use]
    pub fn is_success(&self) -> bool {
        self.errors.is_empty()
    }

    /// Check if any errors were recorded.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Get the number of warnings.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Add an error to the result.
    pub fn add_error(&mut self, error: CompilationError) {
        self.errors.push(error);
    }

    /// Add a warning to the result.
    pub fn add_warning(&mut self, warning: CompilationWarning) {
        self.warnings.push(warning);
    }

    /// Add type errors from inference state.
    pub fn add_type_errors(&mut self, state: &InferenceState) {
        for err in &state.errors {
            self.errors.push(CompilationError::Type(err.clone()));
        }
    }

    /// Mark a pass as failed.
    pub fn mark_failed(&mut self, pass: PassId) {
        if self.failed_pass.is_none() {
            self.failed_pass = Some(pass);
        }
    }

    /// Get errors grouped by category.
    #[must_use]
    pub fn errors_by_category(&self) -> HashMap<ErrorCategory, Vec<&CompilationError>> {
        let mut grouped: HashMap<ErrorCategory, Vec<&CompilationError>> = HashMap::new();
        for err in &self.errors {
            grouped.entry(err.category()).or_default().push(err);
        }
        grouped
    }

    /// Format errors for display.
    #[must_use]
    pub fn format_errors(&self) -> String {
        let mut output = String::new();
        for (i, err) in self.errors.iter().enumerate() {
            output.push_str(&format!("error[{}]: {}\n", i + 1, err));
            if let Some(span) = err.span() {
                output.push_str(&format!("  --> {:?}\n", span));
            }
        }
        output
    }
}

impl Default for CompilationResult {
    fn default() -> Self {
        Self::new("unnamed")
    }
}

/// Verification condition for contract checking.
#[derive(Debug, Clone)]
pub struct VerificationCondition {
    /// The formula to prove
    pub formula: Formula,
    /// Source location
    pub span: Range,
    /// Description for error reporting
    pub description: String,
    /// Whether this VC was proven
    pub proven: Option<bool>,
}

/// Identifier for a compilation pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PassId {
    /// Name resolution pass
    Resolution,
    /// Type inference pass
    TypeInference,
    /// Effect inference pass
    EffectInference,
    /// Mode checking pass
    ModeCheck,
    /// Borrow checking pass
    BorrowCheck,
    /// Session type checking pass
    SessionCheck,
    /// Coeffect checking pass
    CoeffectCheck,
    /// Gradual cast insertion pass
    GradualCast,
    /// Contract verification pass
    ContractVerification,
}

impl PassId {
    /// Get the human-readable name of this pass.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Resolution => "name resolution",
            Self::TypeInference => "type inference",
            Self::EffectInference => "effect inference",
            Self::ModeCheck => "mode checking",
            Self::BorrowCheck => "borrow checking",
            Self::SessionCheck => "session type checking",
            Self::CoeffectCheck => "coeffect checking",
            Self::GradualCast => "gradual cast insertion",
            Self::ContractVerification => "contract verification",
        }
    }
}

// ============================================================================
// Analysis Context
// ============================================================================

/// Shared analysis context threaded through all passes.
///
/// Contains state that needs to be shared between analysis passes,
/// including type context, effect state, borrow state, and interning.
#[derive(Debug, Clone, Default)]
pub struct AnalysisContext {
    /// Type inference context
    pub type_ctx: TypeCtx,

    /// Type inference state
    pub type_state: InferenceState,

    /// Effect inference state
    pub effect_state: EffectInferenceState,

    /// Borrow checking state
    pub borrow_state: BorrowState,

    /// Extended borrow state (with regions)
    pub extended_borrow_state: ExtendedBorrowState,

    /// Mode checking state
    pub mode_state: ModeCheckState,

    /// Session type checking state
    pub session_state: SessionCheckState,

    /// Coeffect inference state
    pub coeffect_state: CoeffectInferenceState,

    /// Region inference state
    pub region_state: RegionInferenceState,

    /// Type variable counter for fresh variables
    type_var_counter: u32,

    /// Current compilation pass
    current_pass: Option<PassId>,
}

impl AnalysisContext {
    /// Create a new empty analysis context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh type variable.
    pub fn fresh_type_var(&mut self) -> TypeVar {
        let id = self.type_var_counter;
        self.type_var_counter += 1;
        // Create a synthetic Spur - in real usage, this would use the interner
        lasso::Spur::try_from_usize(id as usize).unwrap_or_else(|| {
            // Fallback for overflow - should never happen in practice
            lasso::Spur::try_from_usize(0).unwrap()
        })
    }

    /// Get the current pass being executed.
    #[must_use]
    pub fn current_pass(&self) -> Option<PassId> {
        self.current_pass
    }

    /// Set the current pass.
    pub fn set_current_pass(&mut self, pass: PassId) {
        self.current_pass = Some(pass);
    }

    /// Check if any errors have been recorded.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.type_state.has_errors()
    }

    /// Reset state for a fresh analysis.
    pub fn reset(&mut self) {
        self.type_ctx = TypeCtx::new();
        self.type_state = InferenceState::new();
        self.effect_state = EffectInferenceState::new();
        self.borrow_state = BorrowState::new();
        self.extended_borrow_state = ExtendedBorrowState::new();
        self.mode_state = ModeCheckState::new();
        self.session_state = SessionCheckState::new();
        self.coeffect_state = CoeffectInferenceState::new();
        self.region_state = RegionInferenceState::new();
        self.type_var_counter = 0;
        self.current_pass = None;
    }
}

// ============================================================================
// Main Compilation Functions
// ============================================================================

/// Main compilation function.
///
/// Executes the configured analysis passes in order on the given module.
/// Returns a `CompilationResult` containing analysis information and errors.
///
/// # Arguments
///
/// * `source` - The source module to compile
/// * `config` - Configuration controlling which passes to run
///
/// # Returns
///
/// A `CompilationResult` with the compiled module and any errors/warnings.
///
/// # Example
///
/// ```ignore
/// use brrr_repr::pipeline::{compile, CompilationConfig};
/// use brrr_repr::decl::Module;
///
/// let module = Module::new("example");
/// let config = CompilationConfig::default();
/// let result = compile(&module, &config);
///
/// if result.is_success() {
///     println!("Compilation successful!");
/// }
/// ```
#[must_use]
pub fn compile(source: &Module, config: &CompilationConfig) -> CompilationResult {
    let mut result = CompilationResult::new(&source.name);
    let mut ctx = AnalysisContext::new();

    // Pipeline order based on dependencies:
    // 1. Name resolution
    // 2. Type inference
    // 3. Effect inference
    // 4. Mode checking
    // 5. Borrow checking
    // 6. Session checking (opt-in)
    // 7. Coeffect checking (opt-in)
    // 8. Gradual cast insertion (opt-in)
    // 9. Contract verification (opt-in)

    // Pass 1: Name resolution (always runs first)
    {
        ctx.set_current_pass(PassId::Resolution);
        run_resolution(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::Resolution);
            return result;
        }
    }

    // Pass 2: Type inference
    if config.type_check {
        ctx.set_current_pass(PassId::TypeInference);
        run_type_inference(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::TypeInference);
            return result;
        }
    }

    // Pass 2: Effect inference
    if config.effect_check {
        ctx.set_current_pass(PassId::EffectInference);
        run_effect_inference(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::EffectInference);
            return result;
        }
    }

    // Pass 3: Mode checking
    if config.mode_check {
        ctx.set_current_pass(PassId::ModeCheck);
        run_mode_check(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::ModeCheck);
            return result;
        }
    }

    // Pass 4: Borrow checking
    if config.borrow_check {
        ctx.set_current_pass(PassId::BorrowCheck);
        run_borrow_check(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::BorrowCheck);
            return result;
        }
    }

    // Pass 5: Session type checking (opt-in)
    if config.session_check {
        ctx.set_current_pass(PassId::SessionCheck);
        run_session_check(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::SessionCheck);
            return result;
        }
    }

    // Pass 6: Coeffect checking (opt-in)
    if config.coeffect_check {
        ctx.set_current_pass(PassId::CoeffectCheck);
        run_coeffect_check(source, &mut ctx, &mut result);

        if config.fail_fast && result.has_errors() {
            result.mark_failed(PassId::CoeffectCheck);
            return result;
        }
    }

    // Pass 7: Gradual cast insertion (opt-in)
    if config.gradual_casts {
        ctx.set_current_pass(PassId::GradualCast);
        run_gradual_cast_insertion(source, &mut ctx, &mut result);
    }

    // Pass 8: Contract verification (opt-in)
    if config.verify_contracts {
        ctx.set_current_pass(PassId::ContractVerification);
        run_contract_verification(source, &mut ctx, &mut result);
    }

    // Collect analysis info into result
    result.type_info = Some(collect_type_info(&ctx));
    result.effect_info = Some(collect_effect_info(&ctx));
    result.borrow_info = Some(collect_borrow_info(&ctx));

    result
}

/// Compile with error recovery.
///
/// Like `compile`, but continues on errors to collect all diagnostics.
/// Useful for IDE integration where showing all errors is more helpful
/// than stopping at the first one.
///
/// # Arguments
///
/// * `source` - The source module to compile
/// * `config` - Configuration (fail_fast is ignored)
///
/// # Returns
///
/// A `CompilationResult` with all collected errors and warnings.
#[must_use]
pub fn compile_with_recovery(source: &Module, config: &CompilationConfig) -> CompilationResult {
    let mut recovery_config = config.clone();
    recovery_config.fail_fast = false;
    compile(source, &recovery_config)
}

/// Compile to BrrrModule format.
///
/// Full pipeline to compiled module format. Returns `Ok` only if
/// compilation succeeds without errors.
///
/// # Arguments
///
/// * `source` - The source module to compile
/// * `config` - Configuration controlling which passes to run
///
/// # Returns
///
/// `Ok(BrrrModule)` on success, `Err(Vec<CompilationError>)` on failure.
pub fn compile_to_brrrx(
    source: &Module,
    config: &CompilationConfig,
) -> Result<BrrrModule, Vec<CompilationError>> {
    let result = compile(source, config);

    if result.is_success() {
        Ok(result.module)
    } else {
        Err(result.errors)
    }
}

// ============================================================================
// Individual Pass Implementations
// ============================================================================

/// Run name resolution pass.
///
/// Resolves all name references in the module, ensuring variables, types,
/// and globals are properly bound. Populates the resolution state in the
/// analysis context.
fn run_resolution(
    source: &Module,
    _ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    use lasso::{Rodeo, RodeoReader};

    // Create a rodeo for interning strings during resolution
    let mut rodeo = Rodeo::default();
    let mut state = ResolutionState::new();

    // First pass: collect all names that need to be interned
    // (This is done by resolve_module internally)

    // Run resolution in two phases:
    // Phase 1: Register globals (only needs intern)
    for (idx, decl) in source.declarations.iter().enumerate() {
        match decl {
            crate::decl::Declaration::Function { name, span, .. } => {
                state.register_global(name, crate::inference::GlobalRef::Function(idx));
                let spur = rodeo.get_or_intern(name);
                if let Err(e) = state.bind_var(
                    name,
                    crate::inference::VarBinding::new(spur, *span),
                ) {
                    state.add_error(e);
                }
            }
            crate::decl::Declaration::Type { name, span, .. } => {
                state.register_global(name, crate::inference::GlobalRef::Type(idx));
                let spur = rodeo.get_or_intern(name);
                state.register_global_type(
                    name,
                    crate::inference::TypeBinding::new(spur, *span),
                );
            }
            crate::decl::Declaration::Constant { name, span, .. } => {
                state.register_global(name, crate::inference::GlobalRef::Const(idx));
                let spur = rodeo.get_or_intern(name);
                if let Err(e) = state.bind_var(
                    name,
                    crate::inference::VarBinding::new(spur, *span),
                ) {
                    state.add_error(e);
                }
            }
            crate::decl::Declaration::Trait { name, span, .. } => {
                state.register_global(name, crate::inference::GlobalRef::Trait(idx));
                let spur = rodeo.get_or_intern(name);
                state.register_global_type(
                    name,
                    crate::inference::TypeBinding::new(spur, *span),
                );
            }
            crate::decl::Declaration::Variable { name, span, .. } => {
                // Variables are like constants for resolution purposes
                state.register_global(name, crate::inference::GlobalRef::Const(idx));
                let spur = rodeo.get_or_intern(name);
                if let Err(e) = state.bind_var(
                    name,
                    crate::inference::VarBinding::new(spur, *span),
                ) {
                    state.add_error(e);
                }
            }
            crate::decl::Declaration::Impl { .. } => {}
            crate::decl::Declaration::Use(_) => {}
        }
    }

    // Register submodules
    for (idx, submod) in source.submodules.iter().enumerate() {
        state.register_global(&submod.name, crate::inference::GlobalRef::Module(idx));
    }

    // Now convert rodeo to a reader for immutable access
    let reader: RodeoReader = rodeo.into_reader();

    // Phase 2 would resolve expression bodies, but we currently don't have
    // function bodies in Module::declarations. This would be done when we have
    // a more complete declaration structure with expression bodies.

    // For now, just record any collected errors
    let resolve_result = if state.has_errors() {
        Err(state.errors.clone())
    } else {
        Ok(())
    };
    let _ = reader; // Silence unused variable warning

    // Convert resolution errors to compilation errors
    if let Err(errors) = resolve_result {
        for err in errors {
            result.add_error(CompilationError::Resolution(
                crate::pipeline::ResolutionError {
                    kind: match err.kind {
                        crate::inference::ResolutionErrorKind::UnboundVariable => {
                            ResolutionErrorKind::UnboundVariable
                        }
                        crate::inference::ResolutionErrorKind::UnboundType => {
                            ResolutionErrorKind::UnboundType
                        }
                        crate::inference::ResolutionErrorKind::UnboundModule => {
                            ResolutionErrorKind::UnboundModule
                        }
                        crate::inference::ResolutionErrorKind::UnboundEffect => {
                            ResolutionErrorKind::UnboundVariable // Map to variable for now
                        }
                        crate::inference::ResolutionErrorKind::DuplicateBinding { .. } => {
                            ResolutionErrorKind::AmbiguousName
                        }
                        crate::inference::ResolutionErrorKind::ImportNotFound => {
                            ResolutionErrorKind::UnboundModule
                        }
                        crate::inference::ResolutionErrorKind::PrivateAccess => {
                            ResolutionErrorKind::PrivateAccess
                        }
                        crate::inference::ResolutionErrorKind::AmbiguousName { .. } => {
                            ResolutionErrorKind::AmbiguousName
                        }
                    },
                    name: err.name,
                    span: err.span,
                },
            ));
        }
    }

    // Also add any errors collected in the state
    for err in state.errors {
        result.add_error(CompilationError::Resolution(
            crate::pipeline::ResolutionError {
                kind: match err.kind {
                    crate::inference::ResolutionErrorKind::UnboundVariable => {
                        ResolutionErrorKind::UnboundVariable
                    }
                    crate::inference::ResolutionErrorKind::UnboundType => {
                        ResolutionErrorKind::UnboundType
                    }
                    crate::inference::ResolutionErrorKind::UnboundModule => {
                        ResolutionErrorKind::UnboundModule
                    }
                    crate::inference::ResolutionErrorKind::UnboundEffect => {
                        ResolutionErrorKind::UnboundVariable
                    }
                    crate::inference::ResolutionErrorKind::DuplicateBinding { .. } => {
                        ResolutionErrorKind::AmbiguousName
                    }
                    crate::inference::ResolutionErrorKind::ImportNotFound => {
                        ResolutionErrorKind::UnboundModule
                    }
                    crate::inference::ResolutionErrorKind::PrivateAccess => {
                        ResolutionErrorKind::PrivateAccess
                    }
                    crate::inference::ResolutionErrorKind::AmbiguousName { .. } => {
                        ResolutionErrorKind::AmbiguousName
                    }
                },
                name: err.name,
                span: err.span,
            },
        ));
    }
}

/// Run type inference pass.
fn run_type_inference(
    _source: &Module,
    ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    // Type inference implementation
    // In full implementation, this would:
    // 1. Walk all declarations in the module
    // 2. Generate type constraints for each expression
    // 3. Solve constraints via unification
    // 4. Record inferred types

    // For now, just collect any errors from the state
    result.add_type_errors(&ctx.type_state);
}

/// Run effect inference pass.
fn run_effect_inference(
    _source: &Module,
    ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    // Effect inference implementation
    // In full implementation, this would:
    // 1. Walk all expressions
    // 2. Infer effect rows for each expression
    // 3. Propagate effects through function calls
    // 4. Check effect handlers cover all effects

    // Collect any effect errors
    for err in &ctx.effect_state.errors {
        result.add_error(CompilationError::Effect(err.clone()));
    }
}

/// Run mode (linearity) checking pass.
fn run_mode_check(
    _source: &Module,
    ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    // Mode checking implementation
    // In full implementation, this would:
    // 1. Track usage counts for each variable
    // 2. Verify linear variables are used exactly once
    // 3. Verify affine variables are used at most once
    // 4. Verify relevant variables are used at least once

    // Collect any mode errors
    for err in &ctx.mode_state.errors {
        result.add_error(CompilationError::Mode(err.clone()));
    }
}

/// Run borrow checking pass.
fn run_borrow_check(
    _source: &Module,
    _ctx: &mut AnalysisContext,
    _result: &mut CompilationResult,
) {
    // Borrow checking implementation
    // In full implementation, this would:
    // 1. Track ownership state of each variable
    // 2. Track active loans (borrows)
    // 3. Detect use-after-move errors
    // 4. Detect borrow conflicts
    // 5. Verify borrows don't outlive borrowed values

    // Note: BorrowState errors would be collected during checking
}

/// Run session type checking pass.
fn run_session_check(
    _source: &Module,
    ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    // Session type checking implementation
    // In full implementation, this would:
    // 1. Track channel usage in expressions
    // 2. Verify send/receive operations match session types
    // 3. Verify session duality for connected endpoints
    // 4. Verify sessions are properly closed

    // Collect any session errors
    for err in &ctx.session_state.errors {
        result.add_error(CompilationError::Session(err.clone()));
    }
}

/// Run coeffect checking pass.
fn run_coeffect_check(
    _source: &Module,
    ctx: &mut AnalysisContext,
    result: &mut CompilationResult,
) {
    // Coeffect checking implementation
    // In full implementation, this would:
    // 1. Track capability requirements
    // 2. Verify capability availability at use sites
    // 3. Track resource usage patterns

    // Collect any coeffect errors
    for err in &ctx.coeffect_state.errors {
        result.add_error(CompilationError::Coeffect(err.clone()));
    }
}

/// Run gradual cast insertion pass.
fn run_gradual_cast_insertion(
    _source: &Module,
    _ctx: &mut AnalysisContext,
    _result: &mut CompilationResult,
) {
    // Gradual cast insertion implementation
    // In full implementation, this would:
    // 1. Find boundaries between static and dynamic types
    // 2. Insert runtime casts at those boundaries
    // 3. Generate warnings for each cast inserted
}

/// Run contract verification pass.
fn run_contract_verification(
    _source: &Module,
    _ctx: &mut AnalysisContext,
    _result: &mut CompilationResult,
) {
    // Contract verification implementation
    // In full implementation, this would:
    // 1. Generate verification conditions from contracts
    // 2. Attempt to prove VCs using SMT solver
    // 3. Report unprovable VCs as errors
}

// ============================================================================
// Info Collection Helpers
// ============================================================================

/// Collect type info from analysis context.
fn collect_type_info(ctx: &AnalysisContext) -> TypeInfo {
    TypeInfo {
        expr_types: HashMap::new(), // Would be populated during type inference
        substitution: ctx.type_state.substitution.clone(),
        schemes: HashMap::new(),
    }
}

/// Collect effect info from analysis context.
fn collect_effect_info(_ctx: &AnalysisContext) -> EffectInfo {
    EffectInfo::new()
}

/// Collect borrow info from analysis context.
fn collect_borrow_info(ctx: &AnalysisContext) -> BorrowInfo {
    BorrowInfo {
        final_state: Some(ctx.borrow_state.clone()),
        loan_origins: HashMap::new(),
        region_constraints: Vec::new(),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = CompilationConfig::default();

        // Core passes should be enabled
        assert!(config.type_check);
        assert!(config.effect_check);
        assert!(config.borrow_check);
        assert!(config.mode_check);

        // Advanced passes should be disabled
        assert!(!config.session_check);
        assert!(!config.verify_contracts);
        assert!(!config.gradual_casts);
        assert!(!config.coeffect_check);
    }

    #[test]
    fn test_minimal_config() {
        let config = CompilationConfig::minimal();

        assert!(config.type_check);
        assert!(!config.effect_check);
        assert!(!config.borrow_check);
        assert!(!config.mode_check);
        assert!(config.fail_fast);
    }

    #[test]
    fn test_full_config() {
        let config = CompilationConfig::full();

        assert!(config.type_check);
        assert!(config.effect_check);
        assert!(config.borrow_check);
        assert!(config.mode_check);
        assert!(config.session_check);
        assert!(config.verify_contracts);
        assert!(config.gradual_casts);
        assert!(config.coeffect_check);
        assert!(config.verbose_diagnostics);
    }

    #[test]
    fn test_config_builders() {
        let config = CompilationConfig::default()
            .with_fail_fast()
            .with_verbose()
            .with_session_check()
            .with_contracts();

        assert!(config.fail_fast);
        assert!(config.verbose_diagnostics);
        assert!(config.session_check);
        assert!(config.verify_contracts);
    }

    #[test]
    fn test_compilation_result_new() {
        let result = CompilationResult::new("test");

        assert!(result.is_success());
        assert!(!result.has_errors());
        assert_eq!(result.error_count(), 0);
        assert_eq!(result.warning_count(), 0);
        assert!(result.failed_pass.is_none());
    }

    #[test]
    fn test_compilation_result_with_errors() {
        let mut result = CompilationResult::new("test");

        let err = TypeError::new(
            crate::inference::TypeErrorKind::CannotInfer,
            Range::SYNTHETIC,
        );
        result.add_error(CompilationError::Type(err));

        assert!(!result.is_success());
        assert!(result.has_errors());
        assert_eq!(result.error_count(), 1);
    }

    #[test]
    fn test_error_categories() {
        let err = CompilationError::Type(TypeError::new(
            crate::inference::TypeErrorKind::Mismatch,
            Range::SYNTHETIC,
        ));
        assert_eq!(err.category(), ErrorCategory::TypeSystem);

        let err = CompilationError::Borrow(OwnershipError::DoubleMove {
            var: lasso::Spur::try_from_usize(0).unwrap(),
        });
        assert_eq!(err.category(), ErrorCategory::Ownership);
    }

    #[test]
    fn test_pass_id_names() {
        assert_eq!(PassId::TypeInference.name(), "type inference");
        assert_eq!(PassId::BorrowCheck.name(), "borrow checking");
        assert_eq!(PassId::SessionCheck.name(), "session type checking");
    }

    #[test]
    fn test_analysis_context_fresh_var() {
        let mut ctx = AnalysisContext::new();

        let v1 = ctx.fresh_type_var();
        let v2 = ctx.fresh_type_var();

        assert_ne!(v1, v2);
    }

    #[test]
    fn test_compile_empty_module() {
        let module = Module::new("empty");
        let config = CompilationConfig::default();
        let result = compile(&module, &config);

        // Empty module should compile without errors
        assert!(result.is_success());
    }

    #[test]
    fn test_compile_with_recovery() {
        let module = Module::new("test");
        let config = CompilationConfig::default().with_fail_fast();

        // Even with fail_fast in config, recovery ignores it
        let result = compile_with_recovery(&module, &config);
        assert!(result.is_success());
    }

    #[test]
    fn test_compile_to_brrrx_success() {
        let module = Module::new("test");
        let config = CompilationConfig::minimal();
        let result = compile_to_brrrx(&module, &config);

        assert!(result.is_ok());
    }

    #[test]
    fn test_type_info() {
        let mut info = TypeInfo::new();
        assert!(info.expr_type(0).is_none());

        info.expr_types.insert(0, BrrrType::BOOL);
        assert!(info.expr_type(0).is_some());
    }

    #[test]
    fn test_warning_creation() {
        let warning = CompilationWarning::unused_variable("x", Range::SYNTHETIC);
        assert_eq!(warning.kind, WarningKind::UnusedVariable);
        assert!(warning.message.contains("x"));

        let warning = CompilationWarning::unreachable(Range::SYNTHETIC, "after return");
        assert_eq!(warning.kind, WarningKind::UnreachableCode);

        let warning = CompilationWarning::gradual_cast(Range::SYNTHETIC, "Int", "?");
        assert_eq!(warning.kind, WarningKind::GradualCast);
    }

    #[test]
    fn test_verification_error() {
        let err = VerificationError::precondition(Range::SYNTHETIC, "x > 0");
        assert_eq!(err.kind, VerificationErrorKind::PreconditionFailure);
        assert!(err.message.is_some());

        let err = VerificationError::timeout();
        assert_eq!(err.kind, VerificationErrorKind::Timeout);
    }

    #[test]
    fn test_errors_by_category() {
        let mut result = CompilationResult::new("test");

        // Add errors of different categories
        let type_err = TypeError::new(
            crate::inference::TypeErrorKind::Mismatch,
            Range::SYNTHETIC,
        );
        result.add_error(CompilationError::Type(type_err));

        let borrow_err = OwnershipError::DoubleMove {
            var: lasso::Spur::try_from_usize(0).unwrap(),
        };
        result.add_error(CompilationError::Borrow(borrow_err));

        let grouped = result.errors_by_category();
        assert_eq!(grouped.len(), 2);
        assert!(grouped.contains_key(&ErrorCategory::TypeSystem));
        assert!(grouped.contains_key(&ErrorCategory::Ownership));
    }
}
