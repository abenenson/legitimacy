//! Runtime-kernel axiom documentation and diagnostic implementations.
//!
//! The crate root re-exports the concrete certificate, observability,
//! impact-bounding, and composition APIs from their implementation modules.
//! This module owns the diagnostic axiom implementations directly, avoiding a
//! parallel re-export hierarchy that could drift from the implementation
//! layout.

pub mod diagnostics;
pub mod kernel;

pub use diagnostics::{binary, consistency, graph, monotonicity, solidarity, strategyproofness};
