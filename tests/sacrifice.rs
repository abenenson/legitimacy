use legitimacy::{
    Claim, CompiledGovernance, Decision, EdgeTransform, Estate, Gate, GateLogic, GovernanceClaim,
    GovernanceNode, GovernanceProperty, GraphBuilder, NodeId, RevisedSacrificeRecompile,
    StrategyproofnessVerdict, Verdict, compile_graph_with_sacrifices, compile_with_sacrifices,
    compile_with_sacrifices_and_monitor,
    ledger::{Ledger, LedgerQuery},
    recompile_with_revised_sacrifice,
    rules::{essay_composite_rule, proportional_rule},
};
use std::collections::BTreeMap;
use std::time::{SystemTime, UNIX_EPOCH};

fn essay_claim(
    id: &str,
    strength: f64,
    diversity: f64,
    peer_relative: f64,
    scarcity_bonus: f64,
    specialization_floor: f64,
    specialization_penalty: f64,
) -> Claim {
    Claim::new(id, strength)
        .unwrap()
        .with_metric("diversity", diversity)
        .with_metric("peer_relative", peer_relative)
        .with_metric("scarcity_bonus", scarcity_bonus)
        .with_metric("specialization_floor", specialization_floor)
        .with_metric("specialization_penalty", specialization_penalty)
}

fn unique_suffix() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos()
}

fn essay_claims() -> Vec<Claim> {
    vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 0.55, 2.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ]
}

fn graph_claim(id: &str, action: &str) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: id.to_string(),
        strength: 1.0,
        priority_class: None,
        path: None,
        action: Some(action.to_string()),
        content: None,
        metrics: BTreeMap::new(),
    }
}

#[test]
fn essay_rule_declares_axiom_and_strategyproofness_sacrifices_with_structured_monitoring() {
    let claims = vec![
        essay_claim("alpha", 0.35, 0.20, 0.25, 1.0, 1.0, 0.0),
        essay_claim("bravo", 0.65, 0.65, 0.70, -0.5, 0.55, 2.0),
        essay_claim("charlie", 0.45, 0.30, 0.47, -1.0, 1.0, 0.0),
        essay_claim("delta", 0.10, 0.00, 0.10, 0.0, 1.0, 0.0),
    ];
    let estate = Estate::new(100.0, "compute").unwrap();

    let certificate = compile_with_sacrifices(&essay_composite_rule(), &claims, &estate).unwrap();

    assert!(matches!(
        certificate.compiled,
        CompiledGovernance::Rule(ref compiled) if compiled.name == "essay-composite-median"
    ));
    assert_eq!(certificate.sacrifices.len(), 4);
    assert_eq!(
        certificate
            .sacrifices
            .iter()
            .map(|sacrifice| sacrifice.sacrificed_property)
            .collect::<Vec<_>>(),
        vec![
            GovernanceProperty::Consistency,
            GovernanceProperty::Solidarity,
            GovernanceProperty::Monotonicity,
            GovernanceProperty::Strategyproofness,
        ]
    );
    assert!(certificate.sacrifices.iter().all(|sacrifice| {
        !sacrifice.justification.is_empty()
            && !sacrifice.monitoring_plan.is_empty()
            && (sacrifice.impact_bound
                - sacrifice
                    .monitoring_plan
                    .iter()
                    .map(|spec| spec.threshold)
                    .fold(0.0_f64, f64::max))
            .abs()
                < 1e-9
            && sacrifice.monitoring_plan.iter().all(|spec| {
                spec.metric
                    .starts_with(sacrifice.sacrificed_property.as_str())
                    && spec.threshold >= 0.0
                    && spec.frequency_seconds > 0
                    && spec.alert_channel.contains("governance-risk")
            })
            && sacrifice
                .provenance
                .source_axiom
                .contains(sacrifice.sacrificed_property.as_str())
    }));
}

#[test]
fn manipulable_monotonicity_violation_declares_both_sacrifices() {
    let claims = essay_claims();
    let estate = Estate::new(100.0, "compute").unwrap();

    let certificate = compile_with_sacrifices(&essay_composite_rule(), &claims, &estate).unwrap();
    let CompiledGovernance::Rule(compiled) = &certificate.compiled else {
        panic!("expected compiled rule");
    };
    assert!(compiled.axiom_verdicts.iter().any(|verdict| matches!(
        verdict,
        Verdict::Rejected { axiom, .. } if axiom.contains("monotonicity")
    )));
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Manipulable { .. }
    ));

    let properties = certificate
        .sacrifices
        .iter()
        .map(|sacrifice| sacrifice.sacrificed_property)
        .collect::<Vec<_>>();
    assert!(properties.contains(&GovernanceProperty::Monotonicity));
    assert!(properties.contains(&GovernanceProperty::Strategyproofness));
}

#[test]
fn proportional_rule_declares_strategyproofness_var_bound_from_misreport_delta() {
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let estate = Estate::new(12.0, "units").unwrap();

    let certificate = compile_with_sacrifices(&proportional_rule(), &claims, &estate).unwrap();

    assert!(matches!(
        certificate.compiled,
        CompiledGovernance::Rule(ref compiled) if compiled.name == "proportional"
    ));
    assert_eq!(certificate.sacrifices.len(), 1);
    assert_eq!(
        certificate.sacrifices[0].sacrificed_property,
        GovernanceProperty::Strategyproofness
    );
    assert_eq!(certificate.sacrifices[0].monitoring_plan.len(), 1);
    assert_eq!(
        certificate.sacrifices[0].monitoring_plan[0].metric,
        "strategyproofness.claim_strength_delta"
    );
    assert_eq!(
        certificate.sacrifices[0].impact_bound,
        certificate.sacrifices[0].monitoring_plan[0].threshold
    );
    assert!(certificate.sacrifices[0].impact_bound > 0.0);
    assert_eq!(
        certificate.sacrifices[0].provenance.source_axiom,
        "strategyproofness"
    );
}

#[test]
fn compile_with_sacrifices_and_monitor_writes_sacrifices_to_hash_chain_ledger() {
    let suffix = unique_suffix();
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let estate = Estate::new(12.0, "units").unwrap();
    let mut rule = proportional_rule();
    rule.name = format!("sacrifice-ledger-{suffix}");
    rule.version = format!("var-{suffix}");

    let certificate = compile_with_sacrifices_and_monitor(&rule, &claims, &estate).unwrap();
    let ledger = Ledger::open_default().unwrap();
    let report = ledger
        .audit(&LedgerQuery {
            rule_name: Some(rule.name.clone()),
            rule_version: Some(rule.version.clone()),
            claimant_id: None,
            limit: 10,
        })
        .unwrap();
    let chain = ledger.verify_chain().unwrap();

    assert_eq!(certificate.sacrifices.len(), 1);
    assert!(report.sacrifices.iter().any(|record| {
        record.subject_name == rule.name
            && record.subject_version == rule.version
            && record.sacrificed_property == GovernanceProperty::Strategyproofness
            && (record.impact_bound - certificate.sacrifices[0].impact_bound).abs() < 1e-9
            && record.monitoring_plan == certificate.sacrifices[0].monitoring_plan
            && record.provenance == certificate.sacrifices[0].provenance
    }));
    assert!(chain.valid);
    assert!(
        chain
            .tables
            .iter()
            .any(|table| table.table == "declared_sacrifices" && table.valid)
    );
}

#[test]
fn revised_sacrifice_recompile_returns_typed_output() {
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let estate = Estate::new(12.0, "units").unwrap();
    let mut revised_sacrifices = compile_with_sacrifices(&proportional_rule(), &claims, &estate)
        .unwrap()
        .sacrifices;
    revised_sacrifices[0].justification =
        "revised strategyproofness declaration supersedes prior ledger".to_string();
    revised_sacrifices[0].impact_bound = 0.25;
    revised_sacrifices[0].monitoring_plan[0].threshold = 0.25;
    let output = recompile_with_revised_sacrifice(RevisedSacrificeRecompile {
        target: &proportional_rule(),
        claims: &claims,
        estate: &estate,
        revised_sacrifices: revised_sacrifices.clone(),
    })
    .unwrap();

    assert!(matches!(
        output.certificate.compiled,
        CompiledGovernance::Rule(_)
    ));
    assert_eq!(output.certificate.sacrifices, revised_sacrifices);
}

#[test]
fn sacrifice_payloads_round_trip_through_json() {
    let claims = vec![
        Claim::new("alice", 1.0).unwrap(),
        Claim::new("bob", 2.0).unwrap(),
        Claim::new("carol", 3.0).unwrap(),
    ];
    let estate = Estate::new(12.0, "units").unwrap();

    let certificate = compile_with_sacrifices(&proportional_rule(), &claims, &estate).unwrap();
    let json = serde_json::to_value(&certificate).unwrap();

    assert_eq!(json["compiled"]["compiled_kind"], "rule");
    assert_eq!(json["sacrifices"].as_array().unwrap().len(), 1);
    assert_eq!(
        json["sacrifices"].as_array().unwrap()[0]["sacrificed_property"],
        "strategyproofness"
    );
    assert!(json["sacrifices"].as_array().unwrap()[0]["justification"].is_string());
    assert!(json["sacrifices"].as_array().unwrap()[0]["monitoring_plan"].is_array());
    assert_eq!(
        json["sacrifices"].as_array().unwrap()[0]["provenance"]["source_axiom"],
        "strategyproofness"
    );
}

#[test]
fn graph_sacrifice_certificate_carries_canonical_surface() {
    let graph = GraphBuilder::new()
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
        .unwrap();
    let claims = vec![graph_claim("alice", "Read"), graph_claim("bob", "Write")];
    let estate = Estate::new(2.0, "decisions").unwrap();

    let certificate = compile_graph_with_sacrifices(&graph, &claims, &estate).unwrap();
    let CompiledGovernance::Graph(compiled) = certificate.compiled else {
        panic!("expected graph certificate");
    };

    let axiom_names = compiled
        .axiom_verdicts
        .iter()
        .map(|verdict| match verdict {
            Verdict::Admissible { axiom, .. } | Verdict::Rejected { axiom, .. } => axiom.as_str(),
        })
        .collect::<Vec<_>>();

    assert_eq!(
        axiom_names,
        vec![
            "graph consistency",
            "graph solidarity",
            "graph monotonicity",
            "graph certifiability",
            "graph observable determinacy",
            "graph corrigibility",
            "graph compositional safety",
            "graph nonvacuity",
        ]
    );
    assert!(matches!(
        compiled.strategyproofness,
        StrategyproofnessVerdict::Strategyproof
    ));
}

#[test]
fn graph_sacrifice_certificate_rejects_skipped_kernel_evidence() {
    let mut builder = GraphBuilder::new().unwrap();
    for index in 0..11 {
        let id = NodeId::new(format!("node-{index}")).unwrap();
        builder = builder
            .add_node(GovernanceNode::Binary {
                id,
                name: format!("node-{index}"),
                gates: Vec::new(),
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            })
            .unwrap();
    }
    for index in 0..10 {
        builder = builder
            .add_edge(
                NodeId::new(format!("node-{index}")).unwrap(),
                NodeId::new(format!("node-{}", index + 1)).unwrap(),
                EdgeTransform::PassThrough,
            )
            .unwrap();
    }
    let graph = builder.build().unwrap();
    let claims = vec![graph_claim("alice", "Read"), graph_claim("bob", "Write")];
    let estate = Estate::new(2.0, "decisions").unwrap();

    let error = compile_graph_with_sacrifices(&graph, &claims, &estate).unwrap_err();
    let message = error.to_string();

    assert!(message.contains("skipped graph observable determinacy"));
    assert!(message.contains("above exhaustive observable-determinacy limit"));
}
