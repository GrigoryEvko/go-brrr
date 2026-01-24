//! Complexity metrics for code analysis.
//!
//! Provides four types of complexity measurement:
//!
//! # Cyclomatic Complexity
//!
//! Cyclomatic complexity (M) measures the number of linearly independent paths
//! through a function. It is calculated using two methods:
//!
//! 1. **Decision Point Method**: M = decision_points + 1
//!    - Counts if, elif, while, for, except, match cases, etc.
//!
//! 2. **Graph Formula**: M = E - N + 2P
//!    - E = edges, N = nodes, P = connected components (usually 1)
//!
//! # Cognitive Complexity (SonarSource methodology)
//!
//! Cognitive complexity measures how difficult code is to understand (not test).
//! It penalizes deeply nested structures more heavily than flat code.
//!
//! - Increments for: if, else if, switch/match, for, while, catch, goto
//! - Nesting penalty: each level of nesting adds to the increment
//! - Logical sequences: `a && b && c` counts as 1, not 2
//! - No increment for: else (counted with if), simple ternary
//!
//! # Halstead Complexity
//!
//! Halstead metrics measure software complexity based on operator/operand counts:
//!
//! - **n1, n2**: Distinct operators and operands
//! - **N1, N2**: Total operators and operands
//! - **Volume (V)**: N * log2(n) - program size in bits
//! - **Difficulty (D)**: (n1/2) * (N2/n2) - error-proneness
//! - **Effort (E)**: D * V - mental effort required
//! - **Time (T)**: E / 18 - development time estimate (seconds)
//! - **Bugs (B)**: V / 3000 - estimated bug count
//!
//! # Maintainability Index
//!
//! Composite metric combining Halstead Volume, Cyclomatic Complexity, and Lines of Code
//! into a single score (0-100) indicating how maintainable the code is.
//!
//! # Risk Levels
//!
//! ## Cyclomatic Complexity
//! - **Low (1-10)**: Simple, well-structured function
//! - **Medium (11-20)**: Moderate complexity, consider splitting
//! - **High (21-50)**: Complex, hard to test and maintain
//! - **Critical (50+)**: Refactor immediately
//!
//! ## Cognitive Complexity (stricter thresholds)
//! - **Low (0-5)**: Simple, easy to understand
//! - **Medium (6-10)**: Moderate complexity, consider simplifying
//! - **High (11-15)**: Complex, hard to understand
//! - **Critical (15+)**: Refactor immediately
//!
//! # Language-Specific Decision Points
//!
//! Each language has specific constructs that count as decision points:
//!
//! - **Python**: if, elif, while, for, except, and, or, comprehension conditions
//! - **TypeScript/JavaScript**: if, else if, for, while, catch, &&, ||, ?:, ?.
//! - **Rust**: if, if let, while, while let, for, match arms, ?
//! - **Go**: if, for, switch cases, select cases

mod cognitive;
pub mod common;
mod cyclomatic;
mod halstead;
mod maintainability;

pub use cyclomatic::{
    analyze_complexity, analyze_file_complexity, ComplexityAnalysis, ComplexityStats,
    CyclomaticComplexity, FunctionComplexity, RiskLevel,
};

pub use cognitive::{
    analyze_cognitive_complexity, analyze_file_cognitive_complexity, CognitiveAnalysis,
    CognitiveAnalysisError, CognitiveComplexity, CognitiveRiskLevel, CognitiveStats,
    ComplexityContribution, ConstructType, FunctionCognitiveComplexity,
};

pub use halstead::{
    analyze_file_halstead, analyze_halstead, FunctionHalstead, HalsteadAnalysis, HalsteadError,
    HalsteadMetrics, HalsteadQuality, HalsteadStats, QualityLevel,
};

pub use maintainability::{
    analyze_file_maintainability, analyze_maintainability, FunctionMaintainability, LinesOfCode,
    MaintainabilityAnalysis, MaintainabilityError, MaintainabilityIndex, MaintainabilityRiskLevel,
    MaintainabilityStats,
};

pub use common::{
    build_histogram, calculate_risk_distribution, find_function_body, find_function_node,
    is_function_node, is_function_signature_part, AnalysisError, BaseComplexityStats, BaseF64Stats,
    HistogramBucket,
};
