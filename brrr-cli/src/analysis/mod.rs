//! Code analysis module for advanced program understanding.
//!
//! This module provides high-level analysis capabilities that build on
//! the AST, CFG, and DFG layers to extract semantic information.
//!
//! # Modules
//!
//! - [`invariants`]: Contract inference (preconditions, postconditions, loop invariants)
//! - [`resource_flow`]: Resource lifecycle tracking (acquire/release)
//! - [`state_machine`]: Implicit finite state machine extraction

pub mod invariants;
pub mod resource_flow;
pub mod state_machine;

// Re-exports for invariants
pub use invariants::{
    analyze_invariants, analyze_invariants_function, analyze_invariants_source,
    format_function_json as format_invariant_function_json, format_json as format_invariant_json,
    format_text as format_invariant_text, Evidence, EvidenceKind, FileInvariantAnalysis,
    FunctionInvariantAnalysis, Invariant, InvariantAnalyzer, InvariantError, InvariantMetrics,
    InvariantSummary, InvariantType, Location as InvariantLocation, LoopBounds, LoopInvariantInfo,
    MonotonicDirection, MonotonicVariable, OutputFormat as InvariantOutputFormat,
    SuggestedAssertion, SuggestionCategory,
};

// Re-exports for resource_flow

// Re-exports for state_machine
pub use state_machine::{
    extract_state_machines, extract_state_machines_from_source, ExtractorConfig, OutputFormat,
    State, StateId, StateMachine, StateMachineError, StateMachineExtractor, Transition,
    ValidationIssue, ValidationResult,
};
