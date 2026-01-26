//! Integration tests for Phase 2 features.
//!
//! This module contains comprehensive integration tests for:
//! - Security analysis (vulnerability detection)
//! - Code metrics (complexity, maintainability)
//! - Data flow analysis (constant propagation, live variables)
//! - Quality analysis (clones, code smells)
//! - Coverage mapping

pub mod security_tests;
pub mod metrics_tests;
pub mod dataflow_tests;
pub mod quality_tests;
pub mod coverage_tests;
pub mod analysis_tests;
pub mod cli_tests;
