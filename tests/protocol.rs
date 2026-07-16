use std::collections::BTreeMap;

use legitimacy::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceClaim, GovernanceNode, GovernanceProperty,
    GraphBuilder, MonitoringSpec, NodeId, SupervisoryAction,
    protocol::{
        DeclaredSacrifice, GovernanceDriftAlert, MonitorConfig, ProtocolError, ProtocolState,
        activate, check_decision, compile, declare, measure, propose_revision, recompile,
        report_drift, supervise,
    },
    traverse,
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

fn representative_claims() -> Vec<GovernanceClaim> {
    vec![
        GovernanceClaim {
            claimant_id: "alice".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("Read".to_string()),
            content: None,
            metrics: BTreeMap::new(),
        },
        GovernanceClaim {
            claimant_id: "bob".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("Write".to_string()),
            content: None,
            metrics: BTreeMap::new(),
        },
    ]
}

fn complete_peer_relative_surface_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("peer").unwrap(),
                name: "peer-relative-surface".to_string(),
                gates: vec![
                    Gate::PeerRelative {
                        field: "strength".to_string(),
                        percentile: 0.75,
                        decision: Decision::Permit,
                    },
                    Gate::PeerRelative {
                        field: "strength".to_string(),
                        percentile: 0.75,
                        decision: Decision::Permit,
                    },
                ],
                default: Decision::Deny,
                combination: GateLogic::AnyMustPass,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn over_limit_observable_graph() -> legitimacy::GovernanceGraph {
    let mut builder = GraphBuilder::new().unwrap();
    for index in 0..11 {
        builder = builder
            .add_node(GovernanceNode::Binary {
                id: NodeId::new(format!("independent-{index}")).unwrap(),
                name: format!("independent-{index}"),
                gates: Vec::new(),
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            })
            .unwrap();
    }
    builder.build().unwrap()
}

#[test]
fn protocol_state_machine_advances_through_all_states() {
    let declared = declare(admissible_graph(), Vec::new()).unwrap();
    let compiled = compile(declared).unwrap();
    let measured = measure(compiled, representative_claims()).unwrap();
    let live = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 7,
        },
    )
    .unwrap();
    let (live, certificate) = check_decision(
        live,
        GovernanceClaim {
            claimant_id: "carol".to_string(),
            strength: 1.0,
            priority_class: None,
            path: None,
            action: Some("Read".to_string()),
            content: None,
            metrics: BTreeMap::new(),
        },
    )
    .unwrap();
    assert_eq!(certificate.decision, Decision::Permit);

    let drifted = report_drift(
        live,
        GovernanceDriftAlert {
            alert_type: "manual".to_string(),
            property: legitimacy::GovernanceProperty::Consistency,
            declared_bound: 0.0,
            actual_magnitude: 0.2,
            evidence: BTreeMap::from([("source".to_string(), "test".to_string())]),
            recommended_action: "recompile".to_string(),
        },
    )
    .unwrap();
    let recompiling = propose_revision(drifted, admissible_graph(), Vec::new()).unwrap();
    let recompiled = recompile(recompiling).unwrap();

    assert!(matches!(recompiled, ProtocolState::Compiled { .. }));
}

#[test]
fn protocol_compile_accepts_admissible_graph_without_sacrifices() {
    let declared = declare(admissible_graph(), Vec::new()).unwrap();
    let compiled = compile(declared).unwrap();
    assert!(matches!(compiled, ProtocolState::Compiled { .. }));
}

#[test]
fn protocol_declare_rejects_skipped_kernel_checks() {
    let error = declare(over_limit_observable_graph(), Vec::new()).unwrap_err();

    let ProtocolError::SkippedKernelCheck { axiom, reason } = &error else {
        panic!("expected skipped kernel check error, got {error}");
    };

    assert_eq!(axiom, "graph observable determinacy");
    assert!(
        reason.contains("above exhaustive observable-determinacy limit"),
        "{reason}"
    );
}

#[test]
fn protocol_compile_rejects_peer_relative_surface_without_forced_sacrifices() {
    let declared = declare(complete_peer_relative_surface_graph(), Vec::new()).unwrap();
    let error = compile(declared).unwrap_err();

    let ProtocolError::UnsacrificedViolations { properties } = &error else {
        panic!("expected undeclared sacrifice error, got {error}");
    };

    assert!(
        properties.contains(&GovernanceProperty::Consistency),
        "missing consistency declaration should block activation: {properties:?}"
    );
    assert!(
        properties.contains(&GovernanceProperty::Monotonicity),
        "missing monotonicity declaration should block activation: {properties:?}"
    );

    let message = error.to_string();
    assert!(message.contains("undeclared violations"), "{message}");
    assert!(message.contains("Consistency"), "{message}");
    assert!(message.contains("Monotonicity"), "{message}");
}

#[test]
fn live_protocol_accepts_all_supervisory_actions() {
    let live = activate(
        measure(
            compile(declare(admissible_graph(), Vec::new()).unwrap()).unwrap(),
            representative_claims(),
        )
        .unwrap(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 13,
        },
    )
    .unwrap();

    for action in [
        SupervisoryAction::Pause,
        SupervisoryAction::Deny,
        SupervisoryAction::Sandbox,
        SupervisoryAction::Degrade,
        SupervisoryAction::Rollback,
        SupervisoryAction::Reroute,
        SupervisoryAction::Stop,
    ] {
        let supervised = supervise(live.clone(), action, Some("operator request".to_string()))
            .expect("live state should accept supervisory action");
        let ProtocolState::Supervised { intervention, .. } = supervised else {
            panic!("supervisory action should produce supervised state");
        };

        assert_eq!(intervention.action, action);
        assert_eq!(intervention.postcondition, action.postcondition());
        assert_eq!(intervention.reason.as_deref(), Some("operator request"));
    }
}

#[test]
fn protocol_nonvacuity_sacrifice_uses_liveness_fraction() {
    let declared = declare(
        mixed_nonvacuity_graph(),
        vec![DeclaredSacrifice {
            property: GovernanceProperty::NonVacuous,
            justification: "documented supervisory fallback".to_string(),
            monitoring_specs: vec![MonitoringSpec {
                metric: "non_vacuous.liveness".to_string(),
                threshold: 0.0,
                frequency_seconds: 60,
                alert_channel: "governance-risk".to_string(),
            }],
        }],
    )
    .unwrap();
    let compiled = compile(declared).unwrap();

    let ProtocolState::Compiled {
        compiled_graph,
        sacrifice_certs,
        ..
    } = compiled
    else {
        panic!("graph with declared nonvacuity sacrifice should compile");
    };

    assert!(compiled_graph.axiom_verdicts.iter().any(|verdict| {
        matches!(verdict, legitimacy::Verdict::Rejected { axiom, .. } if axiom == "graph nonvacuity")
    }));
    assert_eq!(sacrifice_certs.len(), 1);
    assert!((sacrifice_certs[0].impact_bound - (1.0 / 3.0)).abs() < 1e-9);
    assert_eq!(sacrifice_certs[0].source_axiom, "graph nonvacuity");
    assert_eq!(
        sacrifice_certs[0].monitoring_specs[0].threshold,
        sacrifice_certs[0].impact_bound
    );
}

#[test]
fn live_monitoring_covers_non_sacrificed_properties() {
    let declared = declare(
        mixed_nonvacuity_graph(),
        vec![DeclaredSacrifice {
            property: GovernanceProperty::NonVacuous,
            justification: "documented supervisory fallback".to_string(),
            monitoring_specs: Vec::new(),
        }],
    )
    .unwrap();
    let live = activate(
        measure(compile(declared).unwrap(), representative_claims()).unwrap(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 14,
        },
    )
    .unwrap();

    let ProtocolState::Live {
        mut monitor_session,
        ledger,
        declaration,
    } = live
    else {
        panic!("expected live state");
    };
    assert_eq!(
        monitor_session.monitored_properties,
        vec![
            GovernanceProperty::Consistency,
            GovernanceProperty::Solidarity,
            GovernanceProperty::Monotonicity,
            GovernanceProperty::Strategyproofness,
            GovernanceProperty::Certifiability,
            GovernanceProperty::ObservableDeterminacy,
            GovernanceProperty::Corrigibility,
            GovernanceProperty::CompositionalSafety,
        ]
    );

    monitor_session
        .monitored_properties
        .retain(|property| *property != GovernanceProperty::Consistency);
    let malformed = ProtocolState::Live {
        monitor_session,
        ledger,
        declaration,
    };
    let error = malformed.validate().unwrap_err().to_string();
    assert!(error.contains("monitoring coverage"), "{error}");
    assert!(error.contains("consistency"), "{error}");
}

#[test]
fn supervisory_actions_apply_concrete_graph_mutations() {
    let live = activate(
        measure(
            compile(declare(supervisable_graph(), Vec::new()).unwrap()).unwrap(),
            representative_claims(),
        )
        .unwrap(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 17,
        },
    )
    .unwrap();

    let paused = supervise(
        live.clone(),
        SupervisoryAction::Pause,
        Some("pause".to_string()),
    )
    .unwrap();
    let paused_graph = supervised_graph(&paused);
    let paused_result = traverse(paused_graph, &representative_claims()).unwrap();
    assert!(
        paused_result
            .final_decisions
            .values()
            .all(|decision| matches!(decision, Decision::Escalate))
    );

    let denied = supervise(
        live.clone(),
        SupervisoryAction::Deny,
        Some("deny".to_string()),
    )
    .unwrap();
    let denied_result = traverse(supervised_graph(&denied), &representative_claims()).unwrap();
    assert!(
        denied_result
            .final_decisions
            .values()
            .all(|decision| matches!(decision, Decision::Deny))
    );

    let sandboxed = supervise(
        live.clone(),
        SupervisoryAction::Sandbox,
        Some("{\"sandbox_nodes\":[\"review\"]}".to_string()),
    )
    .unwrap();
    let sandboxed_graph = supervised_graph(&sandboxed);
    assert_eq!(sandboxed_graph.nodes.len(), 1);
    assert!(
        sandboxed_graph
            .nodes
            .contains_key(&NodeId::new("review").unwrap())
    );

    let degraded = supervise(
        live.clone(),
        SupervisoryAction::Degrade,
        Some("{\"degradation_factor\":2.0}".to_string()),
    )
    .unwrap();
    assert_eq!(
        threshold_value(supervised_graph(&degraded), "review"),
        Some(1.6)
    );

    let rolled_back = supervise(
        degraded,
        SupervisoryAction::Rollback,
        Some("rollback".to_string()),
    )
    .unwrap();
    assert_eq!(
        threshold_value(supervised_graph(&rolled_back), "review"),
        Some(0.8)
    );

    let rerouted = supervise(
        live,
        SupervisoryAction::Reroute,
        Some("{\"reroute_to\":[\"review\"]}".to_string()),
    )
    .unwrap();
    let rerouted_graph = supervised_graph(&rerouted);
    assert!(
        !rerouted_graph
            .nodes
            .contains_key(&NodeId::new("entry").unwrap())
    );
    assert!(
        rerouted_graph
            .nodes
            .keys()
            .any(|node_id| node_id.to_string().starts_with("__supervision_reroute__"))
    );
}

#[test]
fn supervision_leaves_compiled_artifact_immutable() {
    let original_graph = supervisable_graph();
    let live = activate(
        measure(
            compile(declare(original_graph.clone(), Vec::new()).unwrap()).unwrap(),
            representative_claims(),
        )
        .unwrap(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 18,
        },
    )
    .unwrap();
    let ProtocolState::Live {
        monitor_session: original_session,
        ..
    } = live.clone()
    else {
        panic!("expected live state");
    };

    let supervised = supervise(
        live,
        SupervisoryAction::Pause,
        Some("operator request".to_string()),
    )
    .unwrap();
    let ProtocolState::Supervised {
        monitor_session: supervised_session,
        ..
    } = supervised
    else {
        panic!("expected supervised state");
    };

    assert_eq!(supervised_session.compiled_graph.graph, original_graph);
    assert_eq!(
        supervised_session.compiled_graph.compiled_rule_hash,
        original_session.compiled_graph.compiled_rule_hash
    );
    assert_eq!(
        supervised_session.compiled_graph.axiom_verdicts,
        original_session.compiled_graph.axiom_verdicts
    );
}

#[test]
fn supervision_hash_depends_on_governance_graph_not_representative_claims() {
    let measured = measure(
        compile(declare(supervisable_graph(), Vec::new()).unwrap()).unwrap(),
        representative_claims(),
    )
    .unwrap();
    let live_a = activate(
        measured.clone(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 19,
        },
    )
    .unwrap();
    let live_b = activate(
        measured,
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 23,
        },
    )
    .unwrap();
    let (live_b, _) = check_decision(
        live_b,
        GovernanceClaim {
            claimant_id: "carol".to_string(),
            strength: 2.0,
            priority_class: None,
            path: None,
            action: Some("Read".to_string()),
            content: None,
            metrics: BTreeMap::new(),
        },
    )
    .unwrap();

    let supervised_a = supervise(
        live_a,
        SupervisoryAction::Pause,
        Some("operator request".to_string()),
    )
    .unwrap();
    let supervised_b = supervise(
        live_b,
        SupervisoryAction::Pause,
        Some("operator request".to_string()),
    )
    .unwrap();

    let ProtocolState::Supervised {
        intervention: intervention_a,
        monitor_session: session_a,
        ..
    } = supervised_a
    else {
        panic!("expected supervised state");
    };
    let ProtocolState::Supervised {
        intervention: intervention_b,
        monitor_session: session_b,
        ..
    } = supervised_b
    else {
        panic!("expected supervised state");
    };

    assert_eq!(
        intervention_a.overlay_graph, intervention_b.overlay_graph,
        "identical supervisory actions should yield identical governed overlay graphs"
    );
    assert_eq!(
        session_a.compiled_graph.compiled_rule_hash, session_b.compiled_graph.compiled_rule_hash,
        "compiled hash should remain canonical for the immutable compiled graph"
    );
    assert_eq!(
        session_a.compiled_graph.graph,
        supervisable_graph(),
        "supervision should not mutate the compiled graph while retaining old verdicts"
    );
    assert_ne!(
        intervention_a.overlay_graph, session_a.compiled_graph.graph,
        "the concrete intervention belongs in the supervision overlay"
    );
}

#[test]
fn protocol_recompile_allows_sacrifice_growth_for_revised_graph() {
    let declared = declare(admissible_graph(), Vec::new()).unwrap();
    let ProtocolState::Declared { declaration, .. } = declared else {
        panic!("expected declared state");
    };
    let recompiling = ProtocolState::Recompiling {
        proposed_graph: mixed_nonvacuity_graph(),
        sacrifices: vec![DeclaredSacrifice {
            property: GovernanceProperty::NonVacuous,
            justification: "revision introduces a bounded nonvacuity fallback".to_string(),
            monitoring_specs: Vec::new(),
        }],
        declaration,
    };

    let recompiled = recompile(recompiling).unwrap();
    let ProtocolState::Compiled {
        sacrifice_certs, ..
    } = recompiled
    else {
        panic!("expected compiled state");
    };
    assert_eq!(sacrifice_certs.len(), 1);
    assert_eq!(sacrifice_certs[0].property, GovernanceProperty::NonVacuous);
}

#[test]
fn propose_revision_carries_revised_sacrifices_instead_of_old_certificates() {
    let original = DeclaredSacrifice {
        property: GovernanceProperty::NonVacuous,
        justification: "original bounded fallback".to_string(),
        monitoring_specs: Vec::new(),
    };
    let live = activate(
        measure(
            compile(declare(mixed_nonvacuity_graph(), vec![original]).unwrap()).unwrap(),
            representative_claims(),
        )
        .unwrap(),
        MonitorConfig {
            min_interval_seconds: 5,
            max_interval_seconds: 9,
            seed: 29,
        },
    )
    .unwrap();
    let drifted = report_drift(
        live,
        GovernanceDriftAlert {
            alert_type: "manual".to_string(),
            property: GovernanceProperty::NonVacuous,
            declared_bound: 0.0,
            actual_magnitude: 0.5,
            evidence: BTreeMap::from([("source".to_string(), "test".to_string())]),
            recommended_action: "recompile".to_string(),
        },
    )
    .unwrap();
    let revised = vec![DeclaredSacrifice {
        property: GovernanceProperty::NonVacuous,
        justification: "revised fallback budget for the next compile".to_string(),
        monitoring_specs: vec![MonitoringSpec {
            metric: "non_vacuous.liveness".to_string(),
            threshold: 0.5,
            frequency_seconds: 30,
            alert_channel: "governance-risk.non_vacuous".to_string(),
        }],
    }];

    let recompiling = propose_revision(drifted, mixed_nonvacuity_graph(), revised.clone()).unwrap();

    let ProtocolState::Recompiling { sacrifices, .. } = recompiling else {
        panic!("expected recompiling state");
    };
    assert_eq!(sacrifices, revised);
}

fn supervisable_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("entry").unwrap(),
                name: "entry".to_string(),
                gates: vec![Gate::ExactMatch {
                    value: "Read".to_string(),
                    decision: Decision::Escalate,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Threshold {
                id: NodeId::new("review").unwrap(),
                name: "review".to_string(),
                threshold: 0.8,
                field: "strength".to_string(),
            })
        })
        .and_then(|builder| {
            builder.add_edge(
                NodeId::new("entry").unwrap(),
                NodeId::new("review").unwrap(),
                EdgeTransform::PassThrough,
            )
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}

fn supervised_graph(state: &ProtocolState) -> &legitimacy::GovernanceGraph {
    let ProtocolState::Supervised { intervention, .. } = state else {
        panic!("expected supervised state");
    };
    &intervention.overlay_graph
}

fn threshold_value(graph: &legitimacy::GovernanceGraph, node_id: &str) -> Option<f64> {
    match graph.nodes.get(&NodeId::new(node_id).unwrap()) {
        Some(GovernanceNode::Threshold { threshold, .. }) => Some(*threshold),
        _ => None,
    }
}

fn mixed_nonvacuity_graph() -> legitimacy::GovernanceGraph {
    GraphBuilder::new()
        .and_then(|builder| {
            builder.add_node(GovernanceNode::Binary {
                id: NodeId::new("entry").unwrap(),
                name: "entry".to_string(),
                gates: vec![
                    Gate::ExactMatch {
                        value: "safe_action".to_string(),
                        decision: Decision::Permit,
                    },
                    Gate::ExactMatch {
                        value: "needs_review".to_string(),
                        decision: Decision::Escalate,
                    },
                ],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            })
        })
        .and_then(GraphBuilder::build)
        .unwrap()
}
