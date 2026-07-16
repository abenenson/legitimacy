//! Per-step schedule-witness schema for the kernel-extraction contract.
//!
//! This module mirrors the Lean `ScheduleStepCertificate` /
//! `ScheduleStepWitnessChain` types from
//! `lean/Legitimacy/Safety/KernelSafety/ReachabilityStack.lean`. A schedule
//! witness is a JSON document carrying one entry per scheduled step; each
//! entry discriminates between an invariant-preserving kernel transition, a
//! monitored sacrifice certificate, or a malformed shape recorded as a
//! diagnostic.
//!
//! Decoding produces a [`ScheduleKernelExtractionWitness`], the Rust analog of
//! the Lean `ScheduleKernelExtraction` contract. Per-step locality of the
//! failure mode is preserved: malformed shapes do not poison neighboring
//! steps, they appear as their own discriminator value at the step where they
//! occur.

use serde::{Deserialize, Serialize};

use crate::LegitimacyError;

/// Per-step verdict: each scheduled step is one of three discriminator values.
///
/// Mirrors the Lean `ScheduleStepCertificate` two-flavor inductive plus an
/// explicit `malformed` shape that keeps the witness round-tripable for steps
/// the caller could not classify.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum ScheduleStepWitness {
    /// An invariant-preserving kernel transition. The `kernel_step_label`
    /// names the kernel-step constructor (e.g. `refl`,
    /// `graph-preserving-spectral-mutation`), and `current_kernel_id` is the
    /// caller's identifier for the source kernel datum at this step.
    KernelTransitionClaim {
        kernel_step_label: String,
        current_kernel_id: String,
        next_kernel_id: String,
    },
    /// A monitored sacrifice certificate. The `sacrificed_axiom` names the
    /// governance property or kernel axiom the certificate sacrifices; the
    /// `compiled_artifact_id` and `monitoring_plan_id` link the certificate
    /// back to the live compiled governance and monitoring plan.
    SacrificeCertClaim {
        sacrificed_axiom: String,
        current_kernel_id: String,
        next_kernel_id: String,
        compiled_artifact_id: String,
        monitoring_plan_id: String,
    },
    /// A step the caller could not classify. Its presence in a witness chain
    /// localizes the failure to one step rather than invalidating the whole
    /// extraction.
    Malformed { reason: String },
}

impl ScheduleStepWitness {
    /// Whether this step admits the local extraction contract — i.e. either a
    /// kernel-transition claim or a sacrifice-certificate claim. A malformed
    /// step does not.
    pub fn admits_extraction_locally(&self) -> bool {
        matches!(
            self,
            ScheduleStepWitness::KernelTransitionClaim { .. }
                | ScheduleStepWitness::SacrificeCertClaim { .. }
        )
    }
}

/// A schedule-witness chain: one entry per scheduled step, in execution
/// order. Mirrors the Lean `ScheduleStepWitnessChain` shape minus the
/// definitional bijection to `ScheduleKernelExtraction`, which is supplied at
/// the Lean side.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ScheduleWitnessChain {
    /// Caller-provided identifier for the schedule datum that anchors this
    /// chain.
    pub schedule_datum_id: String,
    /// Initial kernel datum identifier.
    pub initial_kernel_id: String,
    /// Per-step witnesses, in scheduled order.
    pub steps: Vec<ScheduleStepWitness>,
}

/// Successful extraction of a schedule-witness chain into a Rust analog of the
/// Lean `ScheduleKernelExtraction` contract. A chain extracts iff every step
/// is locally well-formed; the per-step locality of the failure is preserved
/// by [`ScheduleExtractionError`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleKernelExtractionWitness {
    pub schedule_datum_id: String,
    pub initial_kernel_id: String,
    pub final_kernel_id: String,
    pub steps: Vec<ScheduleStepWitness>,
}

/// Per-step failure of the extraction contract, naming the zero-based step
/// index at which the local witness fails to admit either branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleExtractionError {
    pub step_index: usize,
    pub reason: String,
}

impl std::fmt::Display for ScheduleExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "schedule-witness step {}: {}",
            self.step_index, self.reason
        )
    }
}

impl std::error::Error for ScheduleExtractionError {}

/// Decode a schedule witness from JSON.
pub fn parse_schedule_witness(json: &str) -> Result<ScheduleWitnessChain, LegitimacyError> {
    serde_json::from_str(json).map_err(|source| LegitimacyError::Json {
        context: "schedule witness".to_string(),
        source,
    })
}

/// Extract the schedule-extraction contract from a witness chain.
///
/// Returns `Err(ScheduleExtractionError)` at the first malformed step; the
/// step index is preserved so the caller can localize the failure. A chain of
/// kernel-transition and sacrifice-certificate claims always extracts; the
/// chain's `next_kernel_id` of step `i` must match the `current_kernel_id` of
/// step `i+1` (or the witness's `initial_kernel_id`, for the first step) to
/// preserve datum continuity.
pub fn extract_schedule_witness(
    chain: &ScheduleWitnessChain,
) -> Result<ScheduleKernelExtractionWitness, ScheduleExtractionError> {
    let mut current_id = chain.initial_kernel_id.clone();
    for (index, step) in chain.steps.iter().enumerate() {
        match step {
            ScheduleStepWitness::KernelTransitionClaim {
                current_kernel_id,
                next_kernel_id,
                ..
            }
            | ScheduleStepWitness::SacrificeCertClaim {
                current_kernel_id,
                next_kernel_id,
                ..
            } => {
                if current_kernel_id != &current_id {
                    return Err(ScheduleExtractionError {
                        step_index: index,
                        reason: format!(
                            "datum continuity broken: expected current_kernel_id '{}', got '{}'",
                            current_id, current_kernel_id
                        ),
                    });
                }
                current_id = next_kernel_id.clone();
            }
            ScheduleStepWitness::Malformed { reason } => {
                return Err(ScheduleExtractionError {
                    step_index: index,
                    reason: reason.clone(),
                });
            }
        }
    }
    Ok(ScheduleKernelExtractionWitness {
        schedule_datum_id: chain.schedule_datum_id.clone(),
        initial_kernel_id: chain.initial_kernel_id.clone(),
        final_kernel_id: current_id,
        steps: chain.steps.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn invariant_step(current: &str, next: &str) -> ScheduleStepWitness {
        ScheduleStepWitness::KernelTransitionClaim {
            kernel_step_label: "refl".to_string(),
            current_kernel_id: current.to_string(),
            next_kernel_id: next.to_string(),
        }
    }

    fn sacrifice_step(current: &str, next: &str) -> ScheduleStepWitness {
        ScheduleStepWitness::SacrificeCertClaim {
            sacrificed_axiom: "governance.Consistency".to_string(),
            current_kernel_id: current.to_string(),
            next_kernel_id: next.to_string(),
            compiled_artifact_id: "compiled-v1".to_string(),
            monitoring_plan_id: "monitoring-v1".to_string(),
        }
    }

    #[test]
    fn parses_kernel_transition_claim_discriminator() {
        let json = r#"{
            "schedule_datum_id": "D",
            "initial_kernel_id": "D",
            "steps": [
                {
                    "kind": "kernel-transition-claim",
                    "kernel_step_label": "refl",
                    "current_kernel_id": "D",
                    "next_kernel_id": "D"
                }
            ]
        }"#;
        let chain = parse_schedule_witness(json).expect("parses");
        assert_eq!(chain.steps.len(), 1);
        assert!(chain.steps[0].admits_extraction_locally());
    }

    #[test]
    fn parses_sacrifice_cert_claim_discriminator() {
        let json = r#"{
            "schedule_datum_id": "D",
            "initial_kernel_id": "D",
            "steps": [
                {
                    "kind": "sacrifice-cert-claim",
                    "sacrificed_axiom": "governance.Consistency",
                    "current_kernel_id": "D",
                    "next_kernel_id": "D",
                    "compiled_artifact_id": "compiled-v1",
                    "monitoring_plan_id": "monitoring-v1"
                }
            ]
        }"#;
        let chain = parse_schedule_witness(json).expect("parses");
        assert!(chain.steps[0].admits_extraction_locally());
    }

    #[test]
    fn parses_malformed_discriminator() {
        let json = r#"{
            "schedule_datum_id": "D",
            "initial_kernel_id": "D",
            "steps": [{"kind": "malformed", "reason": "no extractable verdict"}]
        }"#;
        let chain = parse_schedule_witness(json).expect("parses");
        assert!(!chain.steps[0].admits_extraction_locally());
    }

    #[test]
    fn extracts_mixed_invariant_and_sacrifice_chain() {
        let chain = ScheduleWitnessChain {
            schedule_datum_id: "D".into(),
            initial_kernel_id: "D".into(),
            steps: vec![
                invariant_step("D", "D"),
                sacrifice_step("D", "D"),
                invariant_step("D", "D"),
            ],
        };
        let extracted = extract_schedule_witness(&chain).expect("extracts");
        assert_eq!(extracted.final_kernel_id, "D");
        assert_eq!(extracted.steps.len(), 3);
    }

    #[test]
    fn extraction_localizes_malformed_step_to_step_index() {
        let chain = ScheduleWitnessChain {
            schedule_datum_id: "D".into(),
            initial_kernel_id: "D".into(),
            steps: vec![
                invariant_step("D", "D"),
                ScheduleStepWitness::Malformed {
                    reason: "no extractable verdict".into(),
                },
                invariant_step("D", "D"),
            ],
        };
        let err = extract_schedule_witness(&chain).expect_err("localizes failure");
        assert_eq!(err.step_index, 1);
    }

    #[test]
    fn extraction_rejects_datum_continuity_break() {
        let chain = ScheduleWitnessChain {
            schedule_datum_id: "D".into(),
            initial_kernel_id: "D".into(),
            steps: vec![invariant_step("D", "D'"), invariant_step("D", "D")],
        };
        let err = extract_schedule_witness(&chain).expect_err("datum break");
        assert_eq!(err.step_index, 1);
        assert!(err.reason.contains("datum continuity"));
    }
}
