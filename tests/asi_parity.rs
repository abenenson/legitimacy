use legitimacy::{
    AuthorityGraph, BypassPathWitness, ExtractorInput, GovernanceKernelizationObservation,
    HiddenAuthorityCertificate, HiddenOverrideWitness, KernelizationCleanWitness,
    RuleLayerKernelArtifact, SemanticBridgeFailureWitness, SemanticFailureLocus,
    SourceEvidenceGapWitness, UnmodeledEdgeWitness, autogen_extractor_input,
    bypass_path_observation, clean_authority_graph, clean_kernelization_observation, edge,
    hidden_override_observation, kernelization_clean, malformed_safety_spec_reduction_artifact,
    minimal_hidden_authority, no_silent_rule_layer_degradation,
    safety_spec_reduction_example_artifact, semantic_bridge_failure_observation,
    source_gap_observation, unmodeled_edge_observation,
};
use serde::Serialize;
use serde::de::DeserializeOwned;

fn assert_json_round_trip<T>(name: &str, fixture: &str, expected: &T)
where
    T: Serialize + DeserializeOwned + PartialEq + std::fmt::Debug,
{
    let decoded: T = serde_json::from_str(fixture).expect("fixture should deserialize");
    assert_eq!(&decoded, expected, "{name} fixture decoded incorrectly");

    let encoded = serde_json::to_value(&decoded).expect("fixture should serialize");
    let fixture_value: serde_json::Value =
        serde_json::from_str(fixture).expect("fixture should parse as JSON");
    assert_eq!(encoded, fixture_value, "{name} JSON value drifted");
}

#[test]
fn safety_spec_reduction_fixtures_round_trip() {
    let input_fixture = r#"{
        "sourceId": "audits/fixtures/sources/leaderboard/autogen",
        "byteSize": 23978,
        "sizeBound": 23978,
        "coverageComplete": true,
        "parserErrors": 0
    }"#;
    assert_json_round_trip::<ExtractorInput>(
        "autogenExtractorInput",
        input_fixture,
        &autogen_extractor_input(),
    );

    let artifact_fixture =
        include_str!("../audits/fixtures/asi-parity/safety-spec-reduction-example-artifact.json");
    assert_json_round_trip::<RuleLayerKernelArtifact>(
        "safetySpecReductionExampleArtifact",
        artifact_fixture,
        &safety_spec_reduction_example_artifact(),
    );

    assert!(no_silent_rule_layer_degradation(
        &safety_spec_reduction_example_artifact()
    ));
    assert!(no_silent_rule_layer_degradation(
        &malformed_safety_spec_reduction_artifact()
    ));
}

#[test]
fn authority_graph_fixtures_round_trip() {
    let clean_graph_fixture = r#"{
        "nodes": ["principal", "reviewer"],
        "edges": [{ "fromNode": "principal", "toNode": "reviewer" }],
        "overrides": []
    }"#;
    assert_json_round_trip::<AuthorityGraph>(
        "cleanAuthorityGraph",
        clean_graph_fixture,
        &clean_authority_graph(),
    );

    let bypass_observation = bypass_path_observation();
    assert!(bypass_observation.reported.well_formed());
    assert_json_round_trip::<AuthorityGraph>(
        "bypassGraph",
        r#"{
            "nodes": ["user", "router", "admin"],
            "edges": [
                { "fromNode": "user", "toNode": "router" },
                { "fromNode": "router", "toNode": "admin" }
            ],
            "overrides": []
        }"#,
        &bypass_observation.reported,
    );
}

#[test]
fn hidden_authority_certificate_fixtures_round_trip() {
    let cases = [
        (
            "unmodeledEdgeCertificate",
            r#"{
                "kind": "unmodeledEdge",
                "witness": { "edge": { "fromNode": "principal", "toNode": "reviewer" } }
            }"#,
            HiddenAuthorityCertificate::UnmodeledEdge(UnmodeledEdgeWitness {
                edge: edge("principal", "reviewer"),
            }),
            unmodeled_edge_observation(),
        ),
        (
            "bypassPathCertificate",
            r#"{
                "kind": "bypassPath",
                "witness": {
                    "source": "user",
                    "middle": ["router"],
                    "target": "admin"
                }
            }"#,
            HiddenAuthorityCertificate::BypassPath(BypassPathWitness {
                source: "user".to_string(),
                middle: vec!["router".to_string()],
                target: "admin".to_string(),
            }),
            bypass_path_observation(),
        ),
        (
            "hiddenOverrideCertificate",
            r#"{
                "kind": "hiddenOverride",
                "witness": {
                    "overrideEdge": { "fromNode": "policy", "toNode": "deployment" },
                    "dominatedPair": { "fromNode": "policy", "toNode": "deployment" }
                }
            }"#,
            HiddenAuthorityCertificate::HiddenOverride(HiddenOverrideWitness {
                override_edge: edge("policy", "deployment"),
                dominated_pair: edge("policy", "deployment"),
            }),
            hidden_override_observation(),
        ),
        (
            "sourceEvidenceGapCertificate",
            r#"{
                "kind": "sourceEvidenceGap",
                "witness": { "edge": { "fromNode": "principal", "toNode": "reviewer" } }
            }"#,
            HiddenAuthorityCertificate::SourceEvidenceGap(SourceEvidenceGapWitness {
                edge: edge("principal", "reviewer"),
            }),
            source_gap_observation(),
        ),
        (
            "semanticBridgeFailureCertificate",
            r#"{
                "kind": "semanticBridgeFailure",
                "witness": { "failureLocus": "semanticBridge" }
            }"#,
            HiddenAuthorityCertificate::SemanticBridgeFailure(SemanticBridgeFailureWitness {
                failure_locus: SemanticFailureLocus::SemanticBridge,
            }),
            semantic_bridge_failure_observation(),
        ),
    ];

    for (name, fixture, expected, observation) in cases {
        assert_json_round_trip::<HiddenAuthorityCertificate>(name, fixture, &expected);
        assert!(
            minimal_hidden_authority(&observation, &expected),
            "{name} should be minimal"
        );
    }
}

#[test]
fn kernelization_observation_and_clean_witness_round_trip() {
    let clean = clean_kernelization_observation();
    assert!(kernelization_clean(&clean));

    let observation_fixture = r#"{
        "artifact": {
            "extract": "exampleGovernanceKernelExtractor",
            "src": {
                "sourceId": "audits/fixtures/sources/leaderboard/autogen",
                "byteSize": 23978,
                "sizeBound": 23978,
                "coverageComplete": true,
                "parserErrors": 0
            },
            "reachedData": "exampleGovernanceKernelData",
            "trajectory": "KernelGovernedTrajectory.refl exampleGovernanceKernelData",
            "compiled": "reductionExampleCompiledGovernance",
            "report": "reductionExampleRiskReport",
            "monitoring": "reductionExampleMonitoring",
            "runtimeKernel": true,
            "semanticBridge": true,
            "semanticKernel": true,
            "reachableStateSafe": true,
            "forcedSacrificesDeclared": true
        },
        "reported": {
            "nodes": ["principal", "reviewer"],
            "edges": [{ "fromNode": "principal", "toNode": "reviewer" }],
            "overrides": []
        },
        "effective": {
            "nodes": ["principal", "reviewer"],
            "edges": [{ "fromNode": "principal", "toNode": "reviewer" }],
            "overrides": []
        },
        "sourceEdges": [{ "fromNode": "principal", "toNode": "reviewer" }],
        "reportedSemanticBridgeClean": true
    }"#;
    assert_json_round_trip::<GovernanceKernelizationObservation>(
        "cleanKernelizationObservation",
        observation_fixture,
        &clean,
    );

    let witness = KernelizationCleanWitness {
        input: autogen_extractor_input(),
        reported_equiv: true,
        source_complete: true,
        semantic_kernel: true,
    };
    assert!(witness.holds_for(&clean));
    assert_json_round_trip::<KernelizationCleanWitness>(
        "cleanKernelizationCleanWitness",
        r#"{
            "input": {
                "sourceId": "audits/fixtures/sources/leaderboard/autogen",
                "byteSize": 23978,
                "sizeBound": 23978,
                "coverageComplete": true,
                "parserErrors": 0
            },
            "reportedEquiv": true,
            "sourceComplete": true,
            "semanticKernel": true
        }"#,
        &witness,
    );
}
