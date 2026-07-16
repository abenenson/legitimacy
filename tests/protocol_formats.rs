use std::collections::BTreeMap;

use legitimacy::{
    Decision, Gate, GateLogic, GovernanceFactorExposure, GovernanceNode, GovernanceProperty,
    GraphBuilder, MonitoringSpec, NodeId,
    protocol::DeclaredSacrifice,
    protocol::formats::{
        GovernanceDeclaration, GovernanceDriftAlert, GovernanceRiskReport, PromotionCertificate,
    },
};

fn sample_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("entry").unwrap(),
                name: "entry".to_string(),
                gates: vec![Gate::ExactMatch {
                    value: "Read".to_string(),
                    decision: Decision::Permit,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

#[test]
fn governance_formats_round_trip_through_json() {
    let declaration = GovernanceDeclaration {
        protocol_version: "0.1.0".to_string(),
        timestamp: "2026-04-15T00:00:00Z".to_string(),
        graph_name: "protocol-fixture".to_string(),
        graph_version: "9.9".to_string(),
        graph: sample_graph(),
        sacrifices: vec![DeclaredSacrifice {
            property: GovernanceProperty::Monotonicity,
            justification: "declared tradeoff".to_string(),
            monitoring_specs: vec![MonitoringSpec {
                metric: "monotonicity.claim_strength_delta".to_string(),
                threshold: 0.3,
                frequency_seconds: 60,
                alert_channel: "governance-risk".to_string(),
            }],
        }],
        spectral_gap: 2.0,
        cv_bound: 0.5,
    };
    let certificate = PromotionCertificate {
        rule_name: "spectral-governance".to_string(),
        claimant_id: "alice".to_string(),
        decision: Decision::Permit,
        outcome_verified: true,
        evidence: BTreeMap::from([("node".to_string(), "entry".to_string())]),
        compiled_rule_hash: "abc123".to_string(),
        prev_cert_hash: None,
        timestamp: "2026-04-15T00:01:00Z".to_string(),
    };
    let drift = GovernanceDriftAlert {
        alert_type: "bound_breach".to_string(),
        property: GovernanceProperty::Monotonicity,
        declared_bound: 0.3,
        actual_magnitude: 0.7,
        evidence: BTreeMap::from([("witness".to_string(), "synthetic".to_string())]),
        recommended_action: "recompile".to_string(),
    };
    let risk = GovernanceRiskReport {
        factor_exposure: GovernanceFactorExposure {
            consistency: 0.0,
            solidarity: 0.0,
            monotonicity: 1.0,
            strategyproofness: 0.0,
            nonvacuity: 0.0,
        },
        spectral_gap: 2.0,
        cv_bound: 0.5,
        localizability_bound: 1.0,
    };

    let json = serde_json::to_string_pretty(&(declaration, certificate, drift, risk)).unwrap();
    let round_trip: (
        GovernanceDeclaration,
        PromotionCertificate,
        GovernanceDriftAlert,
        GovernanceRiskReport,
    ) = serde_json::from_str(&json).unwrap();

    assert_eq!(round_trip.0.sacrifices.len(), 1);
    assert_eq!(round_trip.0.graph_name, "protocol-fixture");
    assert_eq!(round_trip.0.graph_version, "9.9");
    assert_eq!(round_trip.1.decision, Decision::Permit);
    assert_eq!(round_trip.2.alert_type, "bound_breach");
    assert_eq!(round_trip.3.factor_exposure.monotonicity, 1.0);
    assert_eq!(round_trip.3.factor_exposure.nonvacuity, 0.0);
}
