use super::*;

#[test]
fn lean_rust_rich_graph_status_parity() {
    let cases = rich_graph_parity_cases();
    let rust = rust_statuses_for_cases(&cases);
    let lean = lean_statuses_for_cases(&cases);

    for case in &cases {
        for check in CHECKS {
            assert_eq!(
                rust.get(&(case.name.clone(), check.to_string())),
                lean.get(&(case.name.clone(), check.to_string())),
                "Rust/Lean rich-graph parity drift for {} {check}",
                case.name
            );
        }
    }

    for check in CHECKS {
        assert!(
            cases.iter().any(|case| {
                rust.get(&(case.name.clone(), check.to_string()))
                    .is_some_and(|status| status == "passed")
            }),
            "rich parity corpus has no passing case for {check}"
        );
        assert!(
            cases.iter().any(|case| {
                rust.get(&(case.name.clone(), check.to_string()))
                    .is_some_and(|status| status != "passed")
            }),
            "rich parity corpus has no non-passing case for {check}"
        );
    }
}

struct GraphParityCase {
    name: String,
    graph: GovernanceGraph,
    claims: Vec<legitimacy::GovernanceClaim>,
}

fn rich_graph_parity_cases() -> Vec<GraphParityCase> {
    vec![
        graph_parity_case(
            "rich_all_pass_chain",
            rich_all_pass_chain(),
            vec![claim("alice", 0.7), claim("bob", 0.8), claim("carol", 0.9)],
        ),
        graph_parity_case(
            "rich_consistency_peer_relative_reject",
            rich_peer_relative_chain(),
            vec![claim("alice", 0.6), claim("bob", 0.55), claim("carol", 0.9)],
        ),
        graph_parity_case(
            "rich_solidarity_split_threshold_reject",
            rich_split_threshold_chain(),
            vec![
                claim_in_class("alice", 0.45, "shared"),
                claim_in_class("bob", 0.75, "shared"),
                claim_in_class("carol", 0.6, "shared"),
            ],
        ),
        graph_parity_case(
            "rich_strategyproof_threshold_reject",
            rich_threshold_chain("strategy-threshold", Decision::Permit, Decision::Deny, 0.5),
            vec![claim("alice", 0.6), claim("bob", 0.3), claim("carol", 0.7)],
        ),
        graph_parity_case(
            "rich_monotonicity_deny_threshold_reject",
            rich_threshold_chain("deny-threshold", Decision::Deny, Decision::Permit, 0.5),
            vec![claim("alice", 0.4), claim("bob", 0.6), claim("carol", 0.7)],
        ),
        graph_parity_case(
            "rich_nonvacuous_all_deny_reject",
            rich_all_deny_chain(),
            vec![claim("alice", 0.7), claim("bob", 0.8), claim("carol", 0.9)],
        ),
        graph_parity_case(
            "rich_observable_over_node_limit_nonpass",
            rich_many_independent_nodes(11),
            vec![claim("alice", 0.7), claim("bob", 0.8), claim("carol", 0.9)],
        ),
        graph_parity_case(
            "rich_diamond_claim_modification_nonpass",
            rich_claim_modification_diamond(),
            vec![claim("alice", 0.7), claim("bob", 0.8), claim("carol", 0.9)],
        ),
        graph_parity_case(
            "rich_cyclic_triangle_nonpass",
            rich_cyclic_triangle(),
            vec![claim("alice", 0.7), claim("bob", 0.8), claim("carol", 0.9)],
        ),
    ]
}

fn graph_parity_case(
    name: &str,
    graph: GovernanceGraph,
    claims: Vec<legitimacy::GovernanceClaim>,
) -> GraphParityCase {
    GraphParityCase {
        name: name.to_string(),
        graph,
        claims,
    }
}

fn rust_statuses_for_cases(cases: &[GraphParityCase]) -> BTreeMap<(String, String), String> {
    cases
        .iter()
        .flat_map(|case| rust_statuses_for_claim_case(&case.name, &case.graph, &case.claims))
        .collect()
}

fn lean_statuses_for_cases(cases: &[GraphParityCase]) -> BTreeMap<(String, String), String> {
    let script_path = unique_path("rich-graph-parity", "lean");
    std::fs::write(&script_path, lean_rich_graph_script(cases)).unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", script_path.to_str().unwrap()])
        .output()
        .expect("failed to run Lean rich-graph parity check");

    let _ = std::fs::remove_file(&script_path);

    assert!(
        output.status.success(),
        "Lean rich-graph parity runner failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter(|line| line.contains('|'))
        .map(|line| {
            let mut parts = line.split('|');
            let case = parts.next().expect("missing Lean parity case");
            let check = parts.next().expect("missing Lean parity check");
            let status = parts.next().expect("missing Lean parity status");
            assert!(
                parts.next().is_none(),
                "unexpected Lean parity output line: {line}"
            );
            ((case.to_string(), check.to_string()), status.to_string())
        })
        .collect()
}

fn lean_rich_graph_script(cases: &[GraphParityCase]) -> String {
    let mut script = lean_parity_prelude();
    script.push_str("#eval do\n");
    for case in cases {
        script.push_str("  printParityCase ");
        script.push_str(&lean_string(&case.name));
        script.push(' ');
        script.push_str(&lean_subject(&case.graph));
        script.push(' ');
        script.push_str(&lean_claims(&case.claims));
        script.push('\n');
    }
    script
}

fn lean_parity_prelude() -> String {
    r#"
import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks
import Legitimacy.Extract.CertifiabilityParity
import Legitimacy.Extract.CompositionalSafetyParity
import Legitimacy.Extract.CorrigibilityParity
import Legitimacy.Extract.DiagnosticParity
import Legitimacy.Extract.NonVacuityParity
import Legitimacy.Extract.ObservableDeterminacyParity

open Legitimacy

def parityCheckName : AuditCheck → String
  | .consistency => "consistency"
  | .solidarity => "solidarity"
  | .monotonicity => "monotonicity"
  | .strategyproofness => "strategyproofness"
  | .certifiability => "certifiability"
  | .observableDeterminacy => "observable_determinacy"
  | .corrigibility => "corrigibility"
  | .compositionalSafety => "compositional_safety"
  | .nonvacuous => "non_vacuous"

def parityStatusName : Except AuditError AuditCheckStatus → String
  | .ok .passed => "passed"
  | .ok .failed => "failed"
  | .ok .skipped => "skipped"
  | .error _ => "error"

def parityCheckStatusOnClaims
    (subject : AuditSubject)
    (claims : List AuditGovernanceClaim)
    (check : AuditCheck) :
    Except AuditError AuditCheckStatus := do
  match check with
  | .observableDeterminacy =>
      pure (rustCheckObservableDeterminacy subject.graph claims)
  | .nonvacuous =>
      pure (rustCheckGraphNonVacuity subject.graph claims)
  | .consistency =>
      rustCheckGraphConsistency subject.graph claims
  | .solidarity =>
      rustCheckGraphSolidarity subject.graph claims
  | .monotonicity =>
      rustCheckGraphMonotonicity subject.graph claims
  | .strategyproofness =>
      rustCheckGraphStrategyproofness subject.graph claims
  | .certifiability =>
      pure (rustCheckGraphCertifiability subject.graph claims)
  | .corrigibility =>
      pure (rustCheckGraphCorrigibility subject.graph claims)
  | .compositionalSafety =>
      pure (rustCheckGraphCompositionalSafety subject.graph claims)

def printParityCase
    (name : String) (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : IO Unit :=
  auditCheckOrder.forM fun check =>
    IO.println (name ++ "|" ++ parityCheckName check ++ "|" ++
      parityStatusName (parityCheckStatusOnClaims subject claims check))

"#
    .to_string()
}

fn rich_all_pass_chain() -> GovernanceGraph {
    let entry = NodeId::new("rich-pass-entry").unwrap();
    let audit = NodeId::new("rich-pass-audit").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                entry.clone(),
                GovernanceNode::Binary {
                    id: entry.clone(),
                    name: "rich pass entry".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                audit.clone(),
                GovernanceNode::Binary {
                    id: audit.clone(),
                    name: "rich pass audit".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(entry, audit, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn rich_peer_relative_chain() -> GovernanceGraph {
    let entry = NodeId::new("rich-peer-entry").unwrap();
    let peer = NodeId::new("rich-peer-gate").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                entry.clone(),
                GovernanceNode::Binary {
                    id: entry.clone(),
                    name: "rich peer entry".to_string(),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                peer.clone(),
                GovernanceNode::Binary {
                    id: peer.clone(),
                    name: "rich peer gate".to_string(),
                    gates: vec![Gate::PeerRelative {
                        field: "strength".to_string(),
                        percentile: 0.5,
                        decision: Decision::Permit,
                    }],
                    default: Decision::Deny,
                    combination: GateLogic::AnyMustPass,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(entry, peer, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn rich_threshold_chain(
    id: &str,
    threshold_decision: Decision,
    default: Decision,
    min: f64,
) -> GovernanceGraph {
    let entry = NodeId::new(format!("{id}-entry")).unwrap();
    let threshold = NodeId::new(format!("{id}-gate")).unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                entry.clone(),
                GovernanceNode::Binary {
                    id: entry.clone(),
                    name: format!("{id} entry"),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                threshold.clone(),
                GovernanceNode::Binary {
                    id: threshold.clone(),
                    name: format!("{id} gate"),
                    gates: vec![Gate::ThresholdGate {
                        field: "strength".to_string(),
                        min,
                        decision: threshold_decision,
                    }],
                    default,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(entry, threshold, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn rich_split_threshold_chain() -> GovernanceGraph {
    let entry = NodeId::new("rich-split-entry").unwrap();
    let split = NodeId::new("rich-split-gate").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                entry.clone(),
                GovernanceNode::Binary {
                    id: entry.clone(),
                    name: "rich split entry".to_string(),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                split.clone(),
                GovernanceNode::Binary {
                    id: split.clone(),
                    name: "rich split gate".to_string(),
                    gates: vec![
                        Gate::ThresholdGate {
                            field: "strength".to_string(),
                            min: 0.8,
                            decision: Decision::Deny,
                        },
                        Gate::ThresholdGate {
                            field: "strength".to_string(),
                            min: 0.5,
                            decision: Decision::Permit,
                        },
                    ],
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(entry, split, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn rich_all_deny_chain() -> GovernanceGraph {
    let entry = NodeId::new("rich-deny-entry").unwrap();
    let sink = NodeId::new("rich-deny-sink").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                entry.clone(),
                GovernanceNode::Binary {
                    id: entry.clone(),
                    name: "rich deny entry".to_string(),
                    gates: Vec::new(),
                    default: Decision::Deny,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                sink.clone(),
                GovernanceNode::Binary {
                    id: sink.clone(),
                    name: "rich deny sink".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(entry, sink, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn rich_many_independent_nodes(count: usize) -> GovernanceGraph {
    let mut nodes = BTreeMap::new();
    for index in 0..count {
        let id = NodeId::new(format!("rich-wide-{index}")).unwrap();
        nodes.insert(
            id.clone(),
            GovernanceNode::Binary {
                id,
                name: format!("rich wide {index}"),
                gates: Vec::new(),
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            },
        );
    }
    GovernanceGraph {
        nodes,
        edges: Vec::new(),
    }
}

fn rich_claim_modification_diamond() -> GovernanceGraph {
    let left = NodeId::new("rich-diamond-left").unwrap();
    let right = NodeId::new("rich-diamond-right").unwrap();
    let sink = NodeId::new("rich-diamond-sink").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                left.clone(),
                GovernanceNode::Binary {
                    id: left.clone(),
                    name: "rich diamond left".to_string(),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                right.clone(),
                GovernanceNode::Binary {
                    id: right.clone(),
                    name: "rich diamond right".to_string(),
                    gates: Vec::new(),
                    default: Decision::Escalate,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                sink.clone(),
                GovernanceNode::Binary {
                    id: sink.clone(),
                    name: "rich diamond sink".to_string(),
                    gates: vec![Gate::ThresholdGate {
                        field: "strength".to_string(),
                        min: 0.75,
                        decision: Decision::Permit,
                    }],
                    default: Decision::Deny,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(left, sink.clone(), EdgeTransform::PassThrough)
                .unwrap(),
            legitimacy::GovernanceEdge::new(
                right,
                sink,
                EdgeTransform::ClaimModification { delta: 0.1 },
            )
            .unwrap(),
        ],
    }
}

fn rich_cyclic_triangle() -> GovernanceGraph {
    let a = NodeId::new("rich-cycle-a").unwrap();
    let b = NodeId::new("rich-cycle-b").unwrap();
    let c = NodeId::new("rich-cycle-c").unwrap();
    let nodes = [a.clone(), b.clone(), c.clone()]
        .into_iter()
        .map(|id| {
            (
                id.clone(),
                GovernanceNode::Binary {
                    id,
                    name: "rich cyclic node".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            )
        })
        .collect();
    GovernanceGraph {
        nodes,
        edges: vec![
            legitimacy::GovernanceEdge::new(a.clone(), b.clone(), EdgeTransform::PassThrough)
                .unwrap(),
            legitimacy::GovernanceEdge::new(b, c.clone(), EdgeTransform::PassThrough).unwrap(),
            legitimacy::GovernanceEdge::new(c, a, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn claim_in_class(
    claimant_id: &str,
    strength: f64,
    priority_class: &str,
) -> legitimacy::GovernanceClaim {
    legitimacy::GovernanceClaim {
        priority_class: Some(priority_class.to_string()),
        ..claim(claimant_id, strength)
    }
}
