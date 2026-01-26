//! Data Flow Analysis Framework.
//!
//! This module provides classical data flow analyses for program optimization
//! and understanding. It builds on top of the CFG (Control Flow Graph) module.
//!
//! # Analyses
//!
//! - **Constant Propagation** (forward): Track which variables have known constant
//!   values at each program point. Enables constant folding and dead branch elimination.
//!
//! - **Live Variables** (backward): For each program point, which variables may
//!   be used before being redefined. Useful for dead store detection.
//!
//! - **Reaching Definitions** (forward): For each program point, which definitions
//!   may reach that point. Useful for def-use chain construction.
//!
//! - **Very Busy Expressions** (backward): An expression is very busy at a point
//!   if it will definitely be computed on ALL paths from that point. Useful for
//!   code hoisting optimization.
//!
//! - **Available Expressions** (forward, must-analysis): An expression is available
//!   at a point if it has been computed on ALL paths to that point and no variable
//!   in the expression has been redefined. Enables Common Subexpression Elimination
//!   (CSE) and loop-invariant code motion.
//!
//! # Applications
//!
//! - Constant folding (e.g., `x = 2 + 3` becomes `x = 5`)
//! - Dead branch elimination (e.g., `if (true)` always takes one branch)
//! - Dead store detection (definition never used)
//! - Unused parameter detection
//! - Register allocation hints
//! - Memory optimization
//! - Code hoisting (move common expressions before conditionals)
//! - Partial redundancy elimination (PRE)
//!
//! # Example: Constant Propagation
//!
//! ```ignore
//! use brrr::dataflow::{analyze_constants, ConstantPropagationResult};
//!
//! let result = analyze_constants_in_file("src/main.py", "compute")?;
//!
//! // Check for constant folding opportunities
//! for folded in &result.folded_expressions {
//!     println!("Can fold {} to {} at line {}",
//!              folded.original, folded.folded_value, folded.location.line);
//! }
//!
//! // Check for dead branches
//! for dead in &result.dead_branches {
//!     println!("Dead branch at line {}: {} is always {}",
//!              dead.location.line, dead.condition, dead.always_value);
//! }
//! ```
//!
//! # Example: Live Variables
//!
//! ```ignore
//! use brrr::dataflow::{analyze_live_variables, LiveVariablesResult};
//! use brrr::cfg::CfgBuilder;
//! use brrr::dfg::DfgBuilder;
//!
//! let cfg = CfgBuilder::extract_from_file("src/main.py", "process")?;
//! let dfg = DfgBuilder::extract_from_file("src/main.py", "process")?;
//!
//! let result = analyze_live_variables(&cfg, &dfg);
//!
//! // Check for dead stores
//! for dead in &result.dead_stores {
//!     println!("Dead store: {} at line {} - {:?}",
//!         dead.variable, dead.location.line, dead.reason);
//! }
//!
//! // Check variable lifetimes
//! for (var, lifetime) in &result.lifetimes {
//!     println!("{}: def at {:?}, last use at {:?}",
//!         var, lifetime.first_def, lifetime.last_use);
//! }
//! ```

pub mod available_expressions;
pub mod common;
pub mod constant_propagation;
pub mod live_variables;
pub mod reaching_definitions;
pub mod very_busy_expressions;

// Re-export common utilities
pub use common::is_valid_identifier;

// Re-export constant propagation types and functions

// Re-export live variables types and functions

// Re-export reaching definitions types and functions

// Re-export very busy expressions types and functions

// Re-export available expressions types and functions
