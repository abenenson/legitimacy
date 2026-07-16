use legitimacy::{
    Decision, Gate, GateLogic, GovernanceNode, GraphBuilder, MonitoringSpec, NodeId,
    protocol::{DeclaredSacrifice, ProtocolError, declare},
};

fn admissible_graph() -> legitimacy::GovernanceGraph {
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
fn declare_rejects_phantom_sacrifices_with_clear_error() {
    let error = declare(
        admissible_graph(),
        vec![DeclaredSacrifice {
            property: legitimacy::GovernanceProperty::Monotonicity,
            justification: "placeholder".to_string(),
            monitoring_specs: vec![MonitoringSpec {
                metric: "monotonicity.claim_strength_delta".to_string(),
                threshold: 0.3,
                frequency_seconds: 60,
                alert_channel: "governance-risk".to_string(),
            }],
        }],
    )
    .unwrap_err();

    match error {
        ProtocolError::PhantomSacrifice { property } => assert_eq!(property, "monotonicity"),
        other => panic!("expected phantom sacrifice error, got {other}"),
    }
    assert!(error.to_string().contains("phantom sacrifice rejected"));
}
