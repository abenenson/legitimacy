//! Rust parity surface for `Legitimacy.Kernelization`.
//!
//! Lean indexes observations and witnesses by proof-carrying artifacts. Rust
//! keeps the same structural authority data and checks certificate minimality
//! by finite list computations.

use crate::safety_spec_reduction::{
    ExtractorInput, RuleLayerKernelArtifact, semantic_bridge_failure_artifact,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fmt;

pub type AuthorityNodeId = String;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "camelCase")]
pub struct AuthorityEdge {
    pub from_node: AuthorityNodeId,
    pub to_node: AuthorityNodeId,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AuthorityGraph {
    pub nodes: Vec<AuthorityNodeId>,
    pub edges: Vec<AuthorityEdge>,
    pub overrides: Vec<AuthorityEdge>,
}

impl AuthorityGraph {
    pub fn well_formed(&self) -> bool {
        let nodes: BTreeSet<&AuthorityNodeId> = self.nodes.iter().collect();
        let endpoints_declared = self
            .edges
            .iter()
            .chain(self.overrides.iter())
            .all(|edge| nodes.contains(&edge.from_node) && nodes.contains(&edge.to_node));
        let nodes_unique = nodes.len() == self.nodes.len();
        nodes_unique && endpoints_declared
    }

    pub fn has_edge(&self, edge: &AuthorityEdge) -> bool {
        self.edges.contains(edge)
    }

    pub fn has_override(&self, edge: &AuthorityEdge) -> bool {
        self.overrides.contains(edge)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct GovernanceKernelizationObservation {
    pub artifact: RuleLayerKernelArtifact,
    pub reported: AuthorityGraph,
    pub effective: AuthorityGraph,
    pub source_edges: Vec<AuthorityEdge>,
    pub reported_semantic_bridge_clean: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct UnmodeledEdgeWitness {
    pub edge: AuthorityEdge,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct BypassPathWitness {
    pub source: AuthorityNodeId,
    pub middle: Vec<AuthorityNodeId>,
    pub target: AuthorityNodeId,
}

impl BypassPathWitness {
    pub fn route(&self) -> Vec<AuthorityNodeId> {
        let mut route = Vec::with_capacity(self.middle.len() + 2);
        route.push(self.source.clone());
        route.extend(self.middle.iter().cloned());
        route.push(self.target.clone());
        route
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct HiddenOverrideWitness {
    pub override_edge: AuthorityEdge,
    pub dominated_pair: AuthorityEdge,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct SourceEvidenceGapWitness {
    pub edge: AuthorityEdge,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "edge", rename_all = "camelCase")]
pub enum SourceEdgeDerivation {
    Source(AuthorityEdge),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub enum SemanticFailureLocus {
    RuntimeKernel,
    SemanticBridge,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct SemanticBridgeFailureWitness {
    pub failure_locus: SemanticFailureLocus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", content = "witness", rename_all = "camelCase")]
pub enum HiddenAuthorityCertificate {
    UnmodeledEdge(UnmodeledEdgeWitness),
    BypassPath(BypassPathWitness),
    HiddenOverride(HiddenOverrideWitness),
    SourceEvidenceGap(SourceEvidenceGapWitness),
    SemanticBridgeFailure(SemanticBridgeFailureWitness),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct KernelizationCleanWitness {
    pub input: ExtractorInput,
    pub reported_equiv: bool,
    pub source_complete: bool,
    pub semantic_kernel: bool,
}

impl KernelizationCleanWitness {
    pub fn holds_for(&self, observation: &GovernanceKernelizationObservation) -> bool {
        &self.input == observation.artifact.src()
            && self.reported_equiv
                == authority_extensionally_equivalent(&observation.reported, &observation.effective)
            && self.source_complete == source_evidence_complete(observation)
            && self.semantic_kernel == observation.artifact.semantic_kernel()
            && self.reported_equiv
            && self.source_complete
            && self.semantic_kernel
    }
}

pub enum KernelizationExtractorResult {
    Clean(KernelizationCleanWitness),
    HiddenAuthority(HiddenAuthorityCertificate),
}

pub type KernelizationExtractFn =
    dyn Fn(&ExtractorInput) -> KernelizationExtractorResult + Send + Sync;

pub struct KernelizationExtractorContract {
    pub extract: Box<KernelizationExtractFn>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelizationHonestyError {
    UnsoundCleanWitness,
    NonminimalCertificate,
}

impl fmt::Display for KernelizationHonestyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsoundCleanWitness => formatter.write_str("unsound kernelization clean witness"),
            Self::NonminimalCertificate => formatter.write_str("nonminimal hidden-authority cert"),
        }
    }
}

impl std::error::Error for KernelizationHonestyError {}

pub fn authority_edge_difference(
    effective: &AuthorityGraph,
    reported: &AuthorityGraph,
) -> Vec<AuthorityEdge> {
    effective
        .edges
        .iter()
        .filter(|edge| !reported.has_edge(edge))
        .cloned()
        .collect()
}

pub fn authority_override_difference(
    effective: &AuthorityGraph,
    reported: &AuthorityGraph,
) -> Vec<AuthorityEdge> {
    effective
        .overrides
        .iter()
        .filter(|edge| !reported.has_override(edge))
        .cloned()
        .collect()
}

pub fn path_authority_edges(path: &[AuthorityNodeId]) -> Vec<AuthorityEdge> {
    path.windows(2)
        .map(|pair| AuthorityEdge {
            from_node: pair[0].clone(),
            to_node: pair[1].clone(),
        })
        .collect()
}

pub fn authority_path_permitted(graph: &AuthorityGraph, path: &[AuthorityNodeId]) -> bool {
    path_authority_edges(path)
        .iter()
        .all(|edge| graph.has_edge(edge))
}

pub fn route_target(path: &[AuthorityNodeId]) -> Option<AuthorityNodeId> {
    path.last().cloned()
}

pub fn route_direct_edge(path: &[AuthorityNodeId]) -> Option<AuthorityEdge> {
    if path.len() < 2 {
        return None;
    }

    Some(AuthorityEdge {
        from_node: path[0].clone(),
        to_node: path[path.len() - 1].clone(),
    })
}

pub fn is_edge_permitted_route(graph: &AuthorityGraph, route: &[AuthorityNodeId]) -> bool {
    route.len() >= 2 && authority_path_permitted(graph, route)
}

pub fn is_edge_permitted_bypass(graph: &AuthorityGraph, route: &[AuthorityNodeId]) -> bool {
    is_edge_permitted_route(graph, route)
        && route_direct_edge(route)
            .map(|edge| !graph.has_edge(&edge))
            .unwrap_or(false)
}

pub fn route_sublists(route: &[AuthorityNodeId]) -> Vec<Vec<AuthorityNodeId>> {
    let mut sublists = vec![Vec::new()];
    for node in route {
        let with_node: Vec<Vec<AuthorityNodeId>> = sublists
            .iter()
            .map(|shorter| {
                let mut next = shorter.clone();
                next.push(node.clone());
                next
            })
            .collect();
        sublists.extend(with_node);
    }
    sublists
}

pub fn proper_route_sublist(shorter: &[AuthorityNodeId], route: &[AuthorityNodeId]) -> bool {
    shorter != route && route_sublists(route).iter().any(|entry| entry == shorter)
}

pub fn authority_extensionally_equivalent(
    reported: &AuthorityGraph,
    effective: &AuthorityGraph,
) -> bool {
    authority_edge_difference(effective, reported).is_empty()
        && authority_edge_difference(reported, effective).is_empty()
        && authority_override_difference(effective, reported).is_empty()
        && authority_override_difference(reported, effective).is_empty()
}

pub fn source_derives_edge(source_edges: &[AuthorityEdge], edge: &AuthorityEdge) -> bool {
    source_edges.contains(edge)
}

pub fn source_evidence_derivable(source_edges: &[AuthorityEdge], edge: &AuthorityEdge) -> bool {
    matches!(
        source_derives_edge(source_edges, edge).then(|| SourceEdgeDerivation::Source(edge.clone())),
        Some(SourceEdgeDerivation::Source(_))
    )
}

pub fn source_evidence_complete(observation: &GovernanceKernelizationObservation) -> bool {
    observation
        .effective
        .edges
        .iter()
        .chain(observation.effective.overrides.iter())
        .all(|edge| source_derives_edge(&observation.source_edges, edge))
}

pub fn kernelization_clean(observation: &GovernanceKernelizationObservation) -> bool {
    authority_extensionally_equivalent(&observation.reported, &observation.effective)
        && source_evidence_complete(observation)
        && observation.artifact.semantic_kernel()
}

pub fn bypass_path_minimal(graph: &AuthorityGraph, witness: &BypassPathWitness) -> bool {
    let route = witness.route();
    is_edge_permitted_route(graph, &route)
        && is_edge_permitted_bypass(graph, &route)
        && route_sublists(&route)
            .iter()
            .all(|shorter| shorter == &route || !is_edge_permitted_bypass(graph, shorter))
}

fn route_nodup(route: &[AuthorityNodeId]) -> bool {
    let unique: BTreeSet<&AuthorityNodeId> = route.iter().collect();
    unique.len() == route.len()
}

pub fn hidden_override_dominates_pair(
    observation: &GovernanceKernelizationObservation,
    witness: &HiddenOverrideWitness,
) -> bool {
    witness.override_edge.from_node == witness.dominated_pair.from_node
        && witness.override_edge.to_node == witness.dominated_pair.to_node
        && observation.reported.has_edge(&witness.dominated_pair)
}

pub fn semantic_failure_locus_fails(
    artifact: &RuleLayerKernelArtifact,
    locus: SemanticFailureLocus,
) -> bool {
    match locus {
        SemanticFailureLocus::RuntimeKernel => !artifact.runtime_kernel(),
        SemanticFailureLocus::SemanticBridge => !artifact.semantic_bridge(),
    }
}

pub fn semantic_failure_locus_minimal(
    artifact: &RuleLayerKernelArtifact,
    locus: SemanticFailureLocus,
) -> bool {
    let fails = semantic_failure_locus_fails(artifact, locus);
    let no_earlier_failure = match locus {
        SemanticFailureLocus::RuntimeKernel => true,
        SemanticFailureLocus::SemanticBridge => {
            !semantic_failure_locus_fails(artifact, SemanticFailureLocus::RuntimeKernel)
        }
    };
    fails && no_earlier_failure
}

pub fn minimal_hidden_authority(
    observation: &GovernanceKernelizationObservation,
    cert: &HiddenAuthorityCertificate,
) -> bool {
    match cert {
        HiddenAuthorityCertificate::UnmodeledEdge(witness) => {
            authority_edge_difference(&observation.effective, &observation.reported)
                .contains(&witness.edge)
        }
        HiddenAuthorityCertificate::BypassPath(witness) => {
            let route = witness.route();
            !witness.middle.is_empty()
                && route_nodup(&route)
                && is_edge_permitted_route(&observation.effective, &route)
                && bypass_path_minimal(&observation.reported, witness)
        }
        HiddenAuthorityCertificate::HiddenOverride(witness) => {
            authority_override_difference(&observation.effective, &observation.reported)
                .contains(&witness.override_edge)
                && hidden_override_dominates_pair(observation, witness)
        }
        HiddenAuthorityCertificate::SourceEvidenceGap(witness) => {
            (observation.effective.has_edge(&witness.edge)
                || observation.effective.has_override(&witness.edge))
                && !source_evidence_derivable(&observation.source_edges, &witness.edge)
        }
        HiddenAuthorityCertificate::SemanticBridgeFailure(witness) => {
            observation.reported_semantic_bridge_clean
                && observation.artifact.src().well_formed()
                && semantic_failure_locus_minimal(&observation.artifact, witness.failure_locus)
        }
    }
}

pub fn kernelization_honesty(
    observation: &GovernanceKernelizationObservation,
    contract: &KernelizationExtractorContract,
) -> Result<KernelizationExtractorResult, KernelizationHonestyError> {
    match (contract.extract)(observation.artifact.src()) {
        KernelizationExtractorResult::Clean(witness) => {
            if witness.holds_for(observation) {
                Ok(KernelizationExtractorResult::Clean(witness))
            } else {
                Err(KernelizationHonestyError::UnsoundCleanWitness)
            }
        }
        KernelizationExtractorResult::HiddenAuthority(cert) => {
            if minimal_hidden_authority(observation, &cert) {
                Ok(KernelizationExtractorResult::HiddenAuthority(cert))
            } else {
                Err(KernelizationHonestyError::NonminimalCertificate)
            }
        }
    }
}

pub fn edge(from_node: &str, to_node: &str) -> AuthorityEdge {
    AuthorityEdge {
        from_node: from_node.to_string(),
        to_node: to_node.to_string(),
    }
}

pub fn clean_authority_graph() -> AuthorityGraph {
    AuthorityGraph {
        nodes: vec!["principal".to_string(), "reviewer".to_string()],
        edges: vec![edge("principal", "reviewer")],
        overrides: Vec::new(),
    }
}

pub fn clean_kernelization_observation() -> GovernanceKernelizationObservation {
    GovernanceKernelizationObservation {
        artifact: crate::safety_spec_reduction::safety_spec_reduction_example_artifact(),
        reported: clean_authority_graph(),
        effective: clean_authority_graph(),
        source_edges: vec![edge("principal", "reviewer")],
        reported_semantic_bridge_clean: true,
    }
}

pub fn unmodeled_edge_observation() -> GovernanceKernelizationObservation {
    GovernanceKernelizationObservation {
        artifact: crate::safety_spec_reduction::safety_spec_reduction_example_artifact(),
        reported: AuthorityGraph {
            nodes: vec!["principal".to_string(), "reviewer".to_string()],
            edges: Vec::new(),
            overrides: Vec::new(),
        },
        effective: clean_authority_graph(),
        source_edges: vec![edge("principal", "reviewer")],
        reported_semantic_bridge_clean: true,
    }
}

pub fn bypass_path_observation() -> GovernanceKernelizationObservation {
    let graph = AuthorityGraph {
        nodes: vec![
            "user".to_string(),
            "router".to_string(),
            "admin".to_string(),
        ],
        edges: vec![edge("user", "router"), edge("router", "admin")],
        overrides: Vec::new(),
    };
    GovernanceKernelizationObservation {
        artifact: crate::safety_spec_reduction::safety_spec_reduction_example_artifact(),
        reported: graph.clone(),
        effective: graph,
        source_edges: vec![edge("user", "router"), edge("router", "admin")],
        reported_semantic_bridge_clean: true,
    }
}

pub fn hidden_override_observation() -> GovernanceKernelizationObservation {
    GovernanceKernelizationObservation {
        artifact: crate::safety_spec_reduction::safety_spec_reduction_example_artifact(),
        reported: AuthorityGraph {
            nodes: vec!["policy".to_string(), "deployment".to_string()],
            edges: vec![edge("policy", "deployment")],
            overrides: Vec::new(),
        },
        effective: AuthorityGraph {
            nodes: vec!["policy".to_string(), "deployment".to_string()],
            edges: vec![edge("policy", "deployment")],
            overrides: vec![edge("policy", "deployment")],
        },
        source_edges: Vec::new(),
        reported_semantic_bridge_clean: true,
    }
}

pub fn source_gap_observation() -> GovernanceKernelizationObservation {
    GovernanceKernelizationObservation {
        artifact: crate::safety_spec_reduction::safety_spec_reduction_example_artifact(),
        reported: clean_authority_graph(),
        effective: clean_authority_graph(),
        source_edges: Vec::new(),
        reported_semantic_bridge_clean: true,
    }
}

pub fn semantic_bridge_failure_observation() -> GovernanceKernelizationObservation {
    GovernanceKernelizationObservation {
        artifact: semantic_bridge_failure_artifact(),
        reported: clean_authority_graph(),
        effective: clean_authority_graph(),
        source_edges: vec![edge("principal", "reviewer")],
        reported_semantic_bridge_clean: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_observation_satisfies_kernelization_clean() {
        let observation = clean_kernelization_observation();
        assert!(observation.reported.well_formed());
        assert!(observation.effective.well_formed());
        assert!(kernelization_clean(&observation));
    }

    #[test]
    fn each_certificate_constructor_has_executable_minimality() {
        let unmodeled = HiddenAuthorityCertificate::UnmodeledEdge(UnmodeledEdgeWitness {
            edge: edge("principal", "reviewer"),
        });
        assert!(minimal_hidden_authority(
            &unmodeled_edge_observation(),
            &unmodeled
        ));

        let bypass = HiddenAuthorityCertificate::BypassPath(BypassPathWitness {
            source: "user".to_string(),
            middle: vec!["router".to_string()],
            target: "admin".to_string(),
        });
        assert!(minimal_hidden_authority(
            &bypass_path_observation(),
            &bypass
        ));

        let hidden_override = HiddenAuthorityCertificate::HiddenOverride(HiddenOverrideWitness {
            override_edge: edge("policy", "deployment"),
            dominated_pair: edge("policy", "deployment"),
        });
        assert!(minimal_hidden_authority(
            &hidden_override_observation(),
            &hidden_override
        ));

        let source_gap = HiddenAuthorityCertificate::SourceEvidenceGap(SourceEvidenceGapWitness {
            edge: edge("principal", "reviewer"),
        });
        assert!(minimal_hidden_authority(
            &source_gap_observation(),
            &source_gap
        ));

        let semantic_failure =
            HiddenAuthorityCertificate::SemanticBridgeFailure(SemanticBridgeFailureWitness {
                failure_locus: SemanticFailureLocus::SemanticBridge,
            });
        assert!(minimal_hidden_authority(
            &semantic_bridge_failure_observation(),
            &semantic_failure
        ));
    }

    #[test]
    fn bypass_minimality_rejects_nonminimal_route() {
        let graph = AuthorityGraph {
            nodes: vec![
                "user".to_string(),
                "router".to_string(),
                "delegate".to_string(),
                "admin".to_string(),
            ],
            edges: vec![
                edge("user", "router"),
                edge("router", "delegate"),
                edge("delegate", "admin"),
                edge("router", "admin"),
            ],
            overrides: Vec::new(),
        };
        let witness = BypassPathWitness {
            source: "user".to_string(),
            middle: vec!["router".to_string(), "delegate".to_string()],
            target: "admin".to_string(),
        };

        assert!(is_edge_permitted_bypass(&graph, &witness.route()));
        assert!(!bypass_path_minimal(&graph, &witness));
    }

    #[test]
    fn kernelization_honesty_checks_contract_output() {
        let observation = clean_kernelization_observation();
        let contract = KernelizationExtractorContract {
            extract: Box::new(|input| {
                KernelizationExtractorResult::Clean(KernelizationCleanWitness {
                    input: input.clone(),
                    reported_equiv: true,
                    source_complete: true,
                    semantic_kernel: true,
                })
            }),
        };

        assert!(matches!(
            kernelization_honesty(&observation, &contract),
            Ok(KernelizationExtractorResult::Clean(_))
        ));
    }

    #[test]
    fn source_evidence_complete_includes_effective_overrides() {
        let mut observation = clean_kernelization_observation();
        let override_edge = edge("reviewer", "principal");
        observation.effective.overrides.push(override_edge.clone());
        assert!(!source_evidence_complete(&observation));

        observation.source_edges.push(override_edge);
        assert!(source_evidence_complete(&observation));
    }

    #[test]
    fn source_evidence_gap_can_witness_missing_override_evidence() {
        let mut observation = clean_kernelization_observation();
        let override_edge = edge("reviewer", "principal");
        observation.effective.overrides.push(override_edge.clone());

        let source_gap = HiddenAuthorityCertificate::SourceEvidenceGap(SourceEvidenceGapWitness {
            edge: override_edge,
        });
        assert!(minimal_hidden_authority(&observation, &source_gap));
    }
}
