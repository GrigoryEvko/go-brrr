//! Security type system for information flow control
//!
//! Implements decentralized label model (DLM), taint tracking, and security annotations.
//!
//! # Overview
//!
//! This module provides security primitives for information flow analysis:
//!
//! - **Labels**: Confidentiality/integrity lattice for information flow
//! - **Taint**: Vulnerability categories (SQLi, XSS, CMDi, etc.)
//! - **Annotations**: Source/sink/sanitizer function annotations
//!
//! # Lattice Structure
//!
//! ```text
//!        Secret:Untrusted (top - most restrictive)
//!             /        \
//!   Secret:Trusted   Public:Untrusted
//!             \        /
//!        Public:Trusted (bottom - most permissive)
//! ```
//!
//! # Information Flow Rules
//!
//! - **Confidentiality**: Information can flow from low to high
//!   (public -> secret is OK, secret -> public is a leak)
//! - **Integrity**: Information can flow from high to low
//!   (untrusted -> trusted needs sanitization, trusted -> untrusted is taint)
//!
//! # DLM (Decentralized Label Model)
//!
//! For fine-grained access control, labels can include DLM policies
//! specifying owners and readers. This enables per-principal access control
//! beyond the simple two-point lattice.
//!
//! # Taint Analysis
//!
//! The taint module provides `TaintKind` for categorizing vulnerability types,
//! while the annotations module provides `SourceAnnotation`, `SinkAnnotation`,
//! and `SanitizerAnnotation` for marking functions with security roles.
//!
//! # Example
//!
//! ```ignore
//! use brrr_repr::security::{TaintKind, SourceAnnotation, SinkAnnotation};
//!
//! // User input is a source of SQLi, XSS, etc.
//! let source = SourceAnnotation::user_input(intern("request.get_param"));
//!
//! // SQL query execution is a sink for SQLi
//! let sink = SinkAnnotation::sql_query(intern("db.execute"), 0);
//!
//! // Check if taint flows without sanitization
//! if source.introduces(TaintKind::SQLi) && sink.rejects_taint(TaintKind::SQLi) {
//!     // Vulnerability detected!
//! }
//! ```

pub mod annotations;
pub mod labels;
pub mod taint;

pub use annotations::{
    endorse_label, sanitize_label, SanitizerAnnotation, SecFuncType, SecParam, SecType,
    SecurityRole, SinkAnnotation, SourceAnnotation,
};
pub use labels::{Confidentiality, DlmLabel, Integrity, Policy, Principal, SecurityLabel};
pub use taint::{
    check_flow_vulnerability, io_sink_requirements, io_source_taints, remove_taints, CustomTaint,
    Taint, TaintKind, TaintSet, TaintStatus, Tainted,
};
