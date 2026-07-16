//! Canonical kernel-axiom checks shared by extraction and protocol surfaces.
//!
//! This module is the single canonical write-path for runtime kernel-axiom
//! diagnostics. Both `crate::extract::audit` (which audits extracted graphs)
//! and `crate::protocol::transitions` (which gates protocol state changes)
//! consume the same `check_graph_*` entry points exported here, so a single
//! decision-procedure update propagates uniformly to both surfaces and no
//! parallel implementation can drift.
//!
//! `KernelAxiom` enumerates the axiom family (the four kernel-safety axioms
//! plus `NonVacuous`, the liveness counterpart). `AxiomVerdict` is the typed
//! `Pass | Fail | Skipped` contract. Legacy `Verdict` extraction is fallible:
//! callers must route `Skipped` explicitly instead of rendering it as a pass.

pub mod certifiable;
pub mod compositional;
pub mod corrigible;
pub mod nonvacuity;
pub mod observable;

use crate::{Counterexample, Verdict};
use serde::{Deserialize, Serialize};

/// The axiom family covered by this module. Names are functional, not
/// theory-internal; the canonical graph-side audit string is exposed via
/// [`KernelAxiom::graph_axiom_name`] for parity with the existing
/// `"graph consistency"` / `"graph nonvacuity"` family.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum KernelAxiom {
    /// Graph-side projection of `Certifiable`: audited graph decisions admit a
    /// replayable, bounded certificate trace.
    Certifiable,
    /// Graph-side projection of `GovernanceObservable`: the graph's final
    /// per-claimant decision is invariant across legal traversal orders.
    Observable,
    /// Graph-side projection of `Corrigible`: emergency supervisory overrides
    /// preserve an evaluable governance surface.
    Corrigible,
    /// Graph-side projection of `CompositionalSafety`: denied decisions remain
    /// denied after appending further governance stages.
    CompositionalSafety,
    /// Liveness counterpart: at least one synthetic claim reaches a terminal
    /// `Permit` disposition, and no claim is permanently stuck in `Escalate`.
    NonVacuous,
}

impl KernelAxiom {
    /// Stable wire string used in extracted graph audit reports.
    pub fn graph_axiom_name(self) -> &'static str {
        match self {
            Self::Certifiable => "graph certifiability",
            Self::Observable => "graph observable determinacy",
            Self::Corrigible => "graph corrigibility",
            Self::CompositionalSafety => "graph compositional safety",
            Self::NonVacuous => "graph nonvacuity",
        }
    }
}

/// Typed `Pass | Fail | Skipped` outcome of a kernel-axiom check. Failures
/// carry a concrete counterexample so downstream sacrifice paths and protocol
/// transitions never branch on an opaque string. Skips are explicit in this
/// kernel-internal type. Public extraction audit surfaces preserve skip reasons
/// outside the legacy [`Verdict`] shape instead of rendering them as passes.
/// The witness is boxed so the enum variants stay compactly sized.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AxiomVerdict {
    Pass {
        axiom: KernelAxiom,
        perturbations_tested: usize,
    },
    Fail {
        axiom: KernelAxiom,
        reason: String,
        witness: Box<Counterexample>,
    },
    Skipped {
        axiom: KernelAxiom,
        reason: String,
    },
}

/// Error returned when a kernel verdict cannot be rendered into the legacy
/// `Verdict` shape without losing its skip reason.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SkippedAxiomVerdict {
    pub axiom: KernelAxiom,
    pub reason: String,
}

impl AxiomVerdict {
    pub fn pass(axiom: KernelAxiom, perturbations_tested: usize) -> Self {
        Self::Pass {
            axiom,
            perturbations_tested,
        }
    }

    pub fn fail(axiom: KernelAxiom, reason: impl Into<String>, witness: Counterexample) -> Self {
        Self::Fail {
            axiom,
            reason: reason.into(),
            witness: Box::new(witness),
        }
    }

    pub fn skipped(axiom: KernelAxiom, reason: impl Into<String>) -> Self {
        Self::Skipped {
            axiom,
            reason: reason.into(),
        }
    }
}

impl TryFrom<AxiomVerdict> for Verdict {
    type Error = SkippedAxiomVerdict;

    fn try_from(value: AxiomVerdict) -> Result<Self, Self::Error> {
        match value {
            AxiomVerdict::Pass {
                axiom,
                perturbations_tested,
            } => Ok(Verdict::Admissible {
                axiom: axiom.graph_axiom_name().to_string(),
                perturbations_tested,
            }),
            AxiomVerdict::Fail { axiom, witness, .. } => Ok(Verdict::Rejected {
                axiom: axiom.graph_axiom_name().to_string(),
                counterexample: *witness,
            }),
            AxiomVerdict::Skipped { axiom, reason } => Err(SkippedAxiomVerdict { axiom, reason }),
        }
    }
}

pub use certifiable::check_graph_certifiability;
pub use compositional::check_graph_compositional_safety;
pub use corrigible::check_graph_corrigibility;
pub use nonvacuity::check_graph_nonvacuity;
pub use observable::check_graph_observable_determinacy;
