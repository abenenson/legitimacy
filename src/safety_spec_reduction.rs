//! Rust parity surface for `Legitimacy.SafetySpecReduction`.
//!
//! Lean carries proof terms for extractor contracts, kernel reachability, and
//! live-surface sacrifice declarations. The Rust side records the bounded
//! source package and executable audit conclusions that can be serialized,
//! replayed, and compared against fixtures.

use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct ExtractorInput {
    pub source_id: String,
    pub byte_size: u64,
    pub size_bound: u64,
    pub coverage_complete: bool,
    pub parser_errors: u64,
}

impl ExtractorInput {
    pub fn well_formed(&self) -> bool {
        self.byte_size <= self.size_bound && self.coverage_complete && self.parser_errors == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleLayerKernelArtifact {
    extract: String,
    src: ExtractorInput,
    reached_data: String,
    trajectory: String,
    compiled: String,
    report: String,
    monitoring: String,
    runtime_kernel: RuntimeKernelWitness,
    semantic_bridge: SemanticBridgeWitness,
    semantic_kernel: SemanticKernelWitness,
    reachable_state_safe: ReachableStateSafetyWitness,
    forced_sacrifices_declared: ForcedSacrificesDeclaredWitness,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct RuleLayerKernelArtifactParts {
    pub extract: String,
    pub src: ExtractorInput,
    pub reached_data: String,
    pub trajectory: String,
    pub compiled: String,
    pub report: String,
    pub monitoring: String,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct RuleLayerKernelArtifactClaims {
    pub runtime_kernel: bool,
    pub semantic_bridge: bool,
    pub semantic_kernel: bool,
    pub reachable_state_safe: bool,
    pub forced_sacrifices_declared: bool,
}

/// Validator interface for the declared parts of a rule-layer kernel artifact.
///
/// Implementations define the validation strength. The built-in
/// `StructuralKernelArtifactValidator` below is intentionally fixture-shape
/// parity only; it is not a semantic validator for arbitrary safety specs.
pub trait RuleLayerKernelArtifactValidator {
    fn runtime_kernel(&self, parts: &RuleLayerKernelArtifactParts) -> bool;
    fn semantic_bridge(&self, parts: &RuleLayerKernelArtifactParts) -> bool;
    fn semantic_kernel(&self, parts: &RuleLayerKernelArtifactParts) -> bool;
    fn reachable_state_safe(&self, parts: &RuleLayerKernelArtifactParts) -> bool;
    fn forced_sacrifices_declared(&self, parts: &RuleLayerKernelArtifactParts) -> bool;
}

/// Shape validator for the canonical safety-spec reduction fixtures.
///
/// This checks that the Rust artifact has the expected nonempty structural
/// fields and sentinel failure marker used by the Lean/Rust parity examples. It
/// does not semantically validate arbitrary safety specifications, source
/// programs, or runtime behavior.
#[derive(Debug, Clone, Copy, Default)]
pub struct StructuralKernelArtifactValidator;

impl RuleLayerKernelArtifactValidator for StructuralKernelArtifactValidator {
    fn runtime_kernel(&self, parts: &RuleLayerKernelArtifactParts) -> bool {
        !parts.extract.is_empty()
            && !parts.reached_data.is_empty()
            && !parts.trajectory.is_empty()
            && !parts.compiled.is_empty()
    }

    fn semantic_bridge(&self, parts: &RuleLayerKernelArtifactParts) -> bool {
        self.runtime_kernel(parts)
            && !parts.extract.contains("semanticFailureExtractor")
            && !parts.report.is_empty()
            && !parts.monitoring.is_empty()
    }

    fn semantic_kernel(&self, parts: &RuleLayerKernelArtifactParts) -> bool {
        self.runtime_kernel(parts) && self.semantic_bridge(parts)
    }

    fn reachable_state_safe(&self, parts: &RuleLayerKernelArtifactParts) -> bool {
        self.runtime_kernel(parts) && parts.trajectory.contains(&parts.reached_data)
    }

    fn forced_sacrifices_declared(&self, parts: &RuleLayerKernelArtifactParts) -> bool {
        !parts.compiled.is_empty() && !parts.report.is_empty() && !parts.monitoring.is_empty()
    }
}

macro_rules! proof_mirror_witness {
    ($name:ident, $method:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub struct $name {
            holds: bool,
        }

        impl $name {
            pub fn verify(
                parts: &RuleLayerKernelArtifactParts,
                claimed: bool,
                validator: &impl RuleLayerKernelArtifactValidator,
            ) -> Option<Self> {
                if validator.$method(parts) == claimed {
                    Some(Self { holds: claimed })
                } else {
                    None
                }
            }

            pub fn holds(&self) -> bool {
                self.holds
            }
        }
    };
}

proof_mirror_witness!(RuntimeKernelWitness, runtime_kernel);
proof_mirror_witness!(SemanticBridgeWitness, semantic_bridge);
proof_mirror_witness!(SemanticKernelWitness, semantic_kernel);
proof_mirror_witness!(ReachableStateSafetyWitness, reachable_state_safe);
proof_mirror_witness!(ForcedSacrificesDeclaredWitness, forced_sacrifices_declared);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuleLayerKernelArtifactVerificationError {
    RuntimeKernel,
    SemanticBridge,
    SemanticKernel,
    ReachableStateSafe,
    ForcedSacrificesDeclared,
}

impl fmt::Display for RuleLayerKernelArtifactVerificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RuntimeKernel => formatter.write_str("runtime-kernel claim failed validation"),
            Self::SemanticBridge => formatter.write_str("semantic-bridge claim failed validation"),
            Self::SemanticKernel => formatter.write_str("semantic-kernel claim failed validation"),
            Self::ReachableStateSafe => {
                formatter.write_str("reachable-state-safety claim failed validation")
            }
            Self::ForcedSacrificesDeclared => {
                formatter.write_str("forced-sacrifice declaration claim failed validation")
            }
        }
    }
}

impl std::error::Error for RuleLayerKernelArtifactVerificationError {}

impl RuleLayerKernelArtifact {
    pub fn verify(
        parts: RuleLayerKernelArtifactParts,
        claims: RuleLayerKernelArtifactClaims,
        validator: &impl RuleLayerKernelArtifactValidator,
    ) -> Result<Self, RuleLayerKernelArtifactVerificationError> {
        let runtime_kernel = RuntimeKernelWitness::verify(&parts, claims.runtime_kernel, validator)
            .ok_or(RuleLayerKernelArtifactVerificationError::RuntimeKernel)?;
        let semantic_bridge =
            SemanticBridgeWitness::verify(&parts, claims.semantic_bridge, validator)
                .ok_or(RuleLayerKernelArtifactVerificationError::SemanticBridge)?;
        let semantic_kernel =
            SemanticKernelWitness::verify(&parts, claims.semantic_kernel, validator)
                .ok_or(RuleLayerKernelArtifactVerificationError::SemanticKernel)?;
        let reachable_state_safe =
            ReachableStateSafetyWitness::verify(&parts, claims.reachable_state_safe, validator)
                .ok_or(RuleLayerKernelArtifactVerificationError::ReachableStateSafe)?;
        let forced_sacrifices_declared = ForcedSacrificesDeclaredWitness::verify(
            &parts,
            claims.forced_sacrifices_declared,
            validator,
        )
        .ok_or(RuleLayerKernelArtifactVerificationError::ForcedSacrificesDeclared)?;

        Ok(Self {
            extract: parts.extract,
            src: parts.src,
            reached_data: parts.reached_data,
            trajectory: parts.trajectory,
            compiled: parts.compiled,
            report: parts.report,
            monitoring: parts.monitoring,
            runtime_kernel,
            semantic_bridge,
            semantic_kernel,
            reachable_state_safe,
            forced_sacrifices_declared,
        })
    }

    pub fn parts(&self) -> RuleLayerKernelArtifactParts {
        RuleLayerKernelArtifactParts {
            extract: self.extract.clone(),
            src: self.src.clone(),
            reached_data: self.reached_data.clone(),
            trajectory: self.trajectory.clone(),
            compiled: self.compiled.clone(),
            report: self.report.clone(),
            monitoring: self.monitoring.clone(),
        }
    }

    pub fn src(&self) -> &ExtractorInput {
        &self.src
    }

    pub fn runtime_kernel(&self) -> bool {
        self.runtime_kernel.holds()
    }

    pub fn semantic_bridge(&self) -> bool {
        self.semantic_bridge.holds()
    }

    pub fn semantic_kernel(&self) -> bool {
        self.semantic_kernel.holds()
    }

    pub fn reachable_state_safe(&self) -> bool {
        self.reachable_state_safe.holds()
    }

    pub fn forced_sacrifices_declared(&self) -> bool {
        self.forced_sacrifices_declared.holds()
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RuleLayerKernelArtifactSerde {
    extract: String,
    src: ExtractorInput,
    reached_data: String,
    trajectory: String,
    compiled: String,
    report: String,
    monitoring: String,
    runtime_kernel: bool,
    semantic_bridge: bool,
    semantic_kernel: bool,
    reachable_state_safe: bool,
    forced_sacrifices_declared: bool,
}

impl From<&RuleLayerKernelArtifact> for RuleLayerKernelArtifactSerde {
    fn from(artifact: &RuleLayerKernelArtifact) -> Self {
        Self {
            extract: artifact.extract.clone(),
            src: artifact.src.clone(),
            reached_data: artifact.reached_data.clone(),
            trajectory: artifact.trajectory.clone(),
            compiled: artifact.compiled.clone(),
            report: artifact.report.clone(),
            monitoring: artifact.monitoring.clone(),
            runtime_kernel: artifact.runtime_kernel(),
            semantic_bridge: artifact.semantic_bridge(),
            semantic_kernel: artifact.semantic_kernel(),
            reachable_state_safe: artifact.reachable_state_safe(),
            forced_sacrifices_declared: artifact.forced_sacrifices_declared(),
        }
    }
}

impl Serialize for RuleLayerKernelArtifact {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        RuleLayerKernelArtifactSerde::from(self).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for RuleLayerKernelArtifact {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw = RuleLayerKernelArtifactSerde::deserialize(deserializer)?;
        Self::verify(
            RuleLayerKernelArtifactParts {
                extract: raw.extract,
                src: raw.src,
                reached_data: raw.reached_data,
                trajectory: raw.trajectory,
                compiled: raw.compiled,
                report: raw.report,
                monitoring: raw.monitoring,
            },
            RuleLayerKernelArtifactClaims {
                runtime_kernel: raw.runtime_kernel,
                semantic_bridge: raw.semantic_bridge,
                semantic_kernel: raw.semantic_kernel,
                reachable_state_safe: raw.reachable_state_safe,
                forced_sacrifices_declared: raw.forced_sacrifices_declared,
            },
            &StructuralKernelArtifactValidator,
        )
        .map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct RuleLayerKernelAuditObligations {
    pub well_formed: bool,
    pub bounded_extractor_contract: bool,
    pub complete_peer_relative_surface: bool,
    pub live_compiled: bool,
}

impl RuleLayerKernelAuditObligations {
    pub fn satisfied_for(&self, artifact: &RuleLayerKernelArtifact) -> bool {
        self.well_formed
            && artifact.src().well_formed()
            && self.bounded_extractor_contract
            && self.complete_peer_relative_surface
            && self.live_compiled
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct KernelAuditConjunction {
    pub semantic: bool,
    pub forced: bool,
    pub reachable: bool,
    pub bounded_extractor_contract: bool,
}

impl KernelAuditConjunction {
    pub fn from_artifact_and_obligations(
        artifact: &RuleLayerKernelArtifact,
        obligations: &RuleLayerKernelAuditObligations,
    ) -> Option<Self> {
        if !obligations.satisfied_for(artifact) {
            return None;
        }

        Some(Self {
            semantic: artifact.semantic_kernel(),
            forced: artifact.forced_sacrifices_declared(),
            reachable: artifact.reachable_state_safe(),
            bounded_extractor_contract: obligations.bounded_extractor_contract,
        })
    }

    pub fn all_clauses_hold(&self) -> bool {
        self.semantic && self.forced && self.reachable && self.bounded_extractor_contract
    }
}

pub fn no_silent_rule_layer_degradation(artifact: &RuleLayerKernelArtifact) -> bool {
    !artifact.src().well_formed()
        || (artifact.semantic_kernel()
            && artifact.reachable_state_safe()
            && artifact.forced_sacrifices_declared())
}

pub fn autogen_extractor_input() -> ExtractorInput {
    ExtractorInput {
        source_id: "audits/fixtures/sources/leaderboard/autogen".to_string(),
        byte_size: 23_978,
        size_bound: 23_978,
        coverage_complete: true,
        parser_errors: 0,
    }
}

pub fn malformed_safety_spec_reduction_input() -> ExtractorInput {
    ExtractorInput {
        source_id: "audits/safety-spec-reduction/malformed".to_string(),
        byte_size: 2,
        size_bound: 1,
        coverage_complete: false,
        parser_errors: 1,
    }
}

pub fn safety_spec_reduction_example_artifact() -> RuleLayerKernelArtifact {
    RuleLayerKernelArtifact::verify(
        RuleLayerKernelArtifactParts {
            extract: "exampleGovernanceKernelExtractor".to_string(),
            src: autogen_extractor_input(),
            reached_data: "exampleGovernanceKernelData".to_string(),
            trajectory: "KernelGovernedTrajectory.refl exampleGovernanceKernelData".to_string(),
            compiled: "reductionExampleCompiledGovernance".to_string(),
            report: "reductionExampleRiskReport".to_string(),
            monitoring: "reductionExampleMonitoring".to_string(),
        },
        RuleLayerKernelArtifactClaims {
            runtime_kernel: true,
            semantic_bridge: true,
            semantic_kernel: true,
            reachable_state_safe: true,
            forced_sacrifices_declared: true,
        },
        &StructuralKernelArtifactValidator,
    )
    .expect("worked safety-spec artifact claims should validate")
}

pub fn semantic_bridge_failure_artifact() -> RuleLayerKernelArtifact {
    RuleLayerKernelArtifact::verify(
        RuleLayerKernelArtifactParts {
            extract: "semanticFailureExtractor".to_string(),
            src: autogen_extractor_input(),
            reached_data: "semanticFailureCounterexampleData".to_string(),
            trajectory: "KernelGovernedTrajectory.refl semanticFailureCounterexampleData"
                .to_string(),
            compiled: "kernelizationCompiledGovernance".to_string(),
            report: "kernelizationRiskReport".to_string(),
            monitoring: "kernelizationMonitoring".to_string(),
        },
        RuleLayerKernelArtifactClaims {
            runtime_kernel: true,
            semantic_bridge: false,
            semantic_kernel: false,
            reachable_state_safe: true,
            forced_sacrifices_declared: true,
        },
        &StructuralKernelArtifactValidator,
    )
    .expect("semantic bridge failure artifact claims should validate")
}

pub fn malformed_safety_spec_reduction_artifact() -> RuleLayerKernelArtifact {
    let mut parts = safety_spec_reduction_example_artifact().parts();
    parts.src = malformed_safety_spec_reduction_input();
    RuleLayerKernelArtifact::verify(
        parts,
        RuleLayerKernelArtifactClaims {
            runtime_kernel: true,
            semantic_bridge: true,
            semantic_kernel: true,
            reachable_state_safe: true,
            forced_sacrifices_declared: true,
        },
        &StructuralKernelArtifactValidator,
    )
    .expect("halt-branch malformed artifact kernel claims should validate structurally")
}

pub fn safety_spec_reduces_to_kernel_audit(
    artifact: &RuleLayerKernelArtifact,
    obligations: &RuleLayerKernelAuditObligations,
) -> Option<KernelAuditConjunction> {
    KernelAuditConjunction::from_artifact_and_obligations(artifact, obligations)
}

pub fn safety_spec_reduction_example_obligations() -> RuleLayerKernelAuditObligations {
    RuleLayerKernelAuditObligations {
        well_formed: true,
        bounded_extractor_contract: true,
        complete_peer_relative_surface: true,
        live_compiled: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_formed_matches_lean_boundary_predicate() {
        assert!(autogen_extractor_input().well_formed());
        assert!(!malformed_safety_spec_reduction_input().well_formed());
    }

    #[test]
    fn no_silent_degradation_accepts_kernel_audit_and_halt_branch() {
        let clean = safety_spec_reduction_example_artifact();
        assert!(no_silent_rule_layer_degradation(&clean));

        let malformed = malformed_safety_spec_reduction_artifact();
        assert!(no_silent_rule_layer_degradation(&malformed));
        assert!(!malformed.src().well_formed());
    }

    #[test]
    fn audit_conjunction_requires_obligations() {
        let artifact = safety_spec_reduction_example_artifact();
        let obligations = safety_spec_reduction_example_obligations();
        let conjunction =
            KernelAuditConjunction::from_artifact_and_obligations(&artifact, &obligations)
                .expect("worked example obligations should produce a conjunction");
        assert!(conjunction.all_clauses_hold());

        let malformed = malformed_safety_spec_reduction_artifact();
        assert!(
            KernelAuditConjunction::from_artifact_and_obligations(&malformed, &obligations)
                .is_none()
        );
    }

    #[test]
    fn serde_uses_lean_field_names() {
        let encoded = serde_json::to_string(&autogen_extractor_input())
            .expect("extractor input should serialize");
        assert!(encoded.contains("\"sourceId\""));
        assert!(encoded.contains("\"byteSize\""));

        let decoded: ExtractorInput =
            serde_json::from_str(&encoded).expect("extractor input should deserialize");
        assert_eq!(decoded, autogen_extractor_input());
    }

    #[test]
    fn artifact_refuses_unverified_true_claims() {
        let parts = RuleLayerKernelArtifactParts {
            extract: String::new(),
            src: autogen_extractor_input(),
            reached_data: "exampleGovernanceKernelData".to_string(),
            trajectory: "KernelGovernedTrajectory.refl exampleGovernanceKernelData".to_string(),
            compiled: "reductionExampleCompiledGovernance".to_string(),
            report: "reductionExampleRiskReport".to_string(),
            monitoring: "reductionExampleMonitoring".to_string(),
        };
        let result = RuleLayerKernelArtifact::verify(
            parts,
            RuleLayerKernelArtifactClaims {
                runtime_kernel: true,
                semantic_bridge: true,
                semantic_kernel: true,
                reachable_state_safe: true,
                forced_sacrifices_declared: true,
            },
            &StructuralKernelArtifactValidator,
        );

        assert!(matches!(
            result,
            Err(RuleLayerKernelArtifactVerificationError::RuntimeKernel)
        ));
    }
}
