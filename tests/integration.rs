//! Integration test entry point.
//!
//! This file serves as the entry point for all integration tests.
//! Individual test modules are in tests/integration/.
//!
//! Run all integration tests:
//!   cargo test --test integration
//!
//! Run specific test module:
//!   cargo test --test integration security
//!
//! Run with verbose output:
//!   cargo test --test integration -- --nocapture

// Include test modules directly using path attribute
#[path = "integration/security_tests.rs"]
mod security_tests;

#[path = "integration/metrics_tests.rs"]
mod metrics_tests;

#[path = "integration/dataflow_tests.rs"]
mod dataflow_tests;

#[path = "integration/quality_tests.rs"]
mod quality_tests;

#[path = "integration/coverage_tests.rs"]
mod coverage_tests;

#[path = "integration/analysis_tests.rs"]
mod analysis_tests;

#[path = "integration/cli_tests.rs"]
mod cli_tests;
