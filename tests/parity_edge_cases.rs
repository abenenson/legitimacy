use legitimacy::{
    BoundaryCausalSafetyAssessment, ClaimCorpusProvenance, Decision, EdgeTransform, Gate,
    GateLogic, GovernanceGraph, GovernanceNode, NodeId, Verdict, audit_governance_graph,
    axioms::{
        graph::{
            consistency::check_graph_consistency,
            monotonicity::monotonicity_check_via_polarity_schema,
            solidarity::check_graph_solidarity, strategyproofness::check_graph_strategyproofness,
        },
        kernel::{
            AxiomVerdict, check_graph_certifiability, check_graph_compositional_safety,
            check_graph_corrigibility, check_graph_nonvacuity, check_graph_observable_determinacy,
        },
    },
    extract::synthetic_claims,
    graph::detect_cycles,
};
#[path = "parity_edge_cases/rich_graph_cases.rs"]
mod rich_graph_cases;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

const CHECKS: [&str; 9] = [
    "consistency",
    "solidarity",
    "monotonicity",
    "strategyproofness",
    "certifiability",
    "observable_determinacy",
    "corrigibility",
    "compositional_safety",
    "non_vacuous",
];

#[test]
fn lean_rust_edge_graph_status_parity() {
    let lean = lean_edge_case_statuses();
    let rust = rust_edge_case_statuses();

    for case in ["singleton", "cyclic"] {
        for check in CHECKS {
            assert_eq!(
                lean.get(&(case.to_string(), check.to_string())),
                rust.get(&(case.to_string(), check.to_string())),
                "Rust/Lean edge parity drift for {case} {check}"
            );
        }
    }

    for check in CHECKS {
        assert_eq!(
            lean.get(&("empty".to_string(), check.to_string())),
            rust.get(&("empty".to_string(), check.to_string())),
            "Rust/Lean edge parity drift for empty {check}"
        );
    }

    let empty_report = audit_governance_graph(
        &empty_graph(),
        synthetic_claims(&empty_graph()),
        ClaimCorpusProvenance::SyntheticStructuralProbe,
        BoundaryCausalSafetyAssessment::default(),
    );
    assert!(
        empty_report.is_err(),
        "Rust full extraction audit should reject empty graphs before a report is available"
    );
}

#[test]
fn strategyproofness_additive_rust_checker_matches_lean_audit_core() {
    let cases = strategyproofness_parity_cases();
    let rust = rust_additive_strategyproofness_statuses(&cases);
    let lean = lean_additive_strategyproofness_statuses(&cases);

    for case in &cases {
        assert_eq!(
            rust.get(&case.name),
            lean.get(&case.name),
            "Rust additive strategyproofness checker drifted from Lean audit core for {}",
            case.name
        );
    }
}

struct StrategyproofnessParityCase {
    name: String,
    graph: GovernanceGraph,
    claims: Vec<legitimacy::GovernanceClaim>,
}

fn strategyproofness_parity_cases() -> Vec<StrategyproofnessParityCase> {
    let mut cases = vec![
        strategyproofness_case("empty", empty_graph(), Vec::new()),
        strategyproofness_case(
            "singleton",
            singleton_graph(),
            synthetic_claims(&singleton_graph()),
        ),
        strategyproofness_case("cyclic", cyclic_graph(), synthetic_claims(&cyclic_graph())),
        strategyproofness_case(
            "threshold_manipulable",
            threshold_graph("threshold", 0.5),
            vec![claim("alice", 0.6), claim("bob", 0.3)],
        ),
        strategyproofness_case(
            "threshold_already_permitted",
            threshold_graph("threshold-pass", 0.5),
            vec![claim("alice", 0.6), claim("bob", 0.7)],
        ),
        strategyproofness_case(
            "peer_relative",
            peer_relative_graph("peer"),
            vec![claim("alice", 0.4), claim("bob", 0.55), claim("carol", 0.9)],
        ),
    ];

    for index in 0..16 {
        let graph = deterministic_strategyproofness_graph(index);
        let claims = deterministic_strategyproofness_claims(index);
        cases.push(strategyproofness_case(
            &format!("randomized_{index}"),
            graph,
            claims,
        ));
    }

    cases
}

fn strategyproofness_case(
    name: &str,
    graph: GovernanceGraph,
    claims: Vec<legitimacy::GovernanceClaim>,
) -> StrategyproofnessParityCase {
    StrategyproofnessParityCase {
        name: name.to_string(),
        graph,
        claims,
    }
}

fn rust_additive_strategyproofness_statuses(
    cases: &[StrategyproofnessParityCase],
) -> BTreeMap<String, String> {
    cases
        .iter()
        .map(|case| {
            (
                case.name.clone(),
                verdict_status(check_graph_strategyproofness(&case.graph, &case.claims)),
            )
        })
        .collect()
}

fn lean_additive_strategyproofness_statuses(
    cases: &[StrategyproofnessParityCase],
) -> BTreeMap<String, String> {
    let script_path = unique_path("strategyproofness-additive-parity", "lean");
    std::fs::write(&script_path, lean_strategyproofness_script(cases)).unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", script_path.to_str().unwrap()])
        .output()
        .expect("failed to run Lean strategyproofness parity check");

    let _ = std::fs::remove_file(&script_path);

    assert!(
        output.status.success(),
        "Lean strategyproofness parity runner failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| {
            let mut parts = line.split('|');
            let case = parts.next().expect("missing strategyproofness case");
            let status = parts.next().expect("missing strategyproofness status");
            assert!(
                parts.next().is_none(),
                "unexpected Lean strategyproofness output line: {line}"
            );
            (case.to_string(), status.to_string())
        })
        .collect()
}

fn lean_strategyproofness_script(cases: &[StrategyproofnessParityCase]) -> String {
    let mut script = r#"
import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks
import Legitimacy.Extract.CertifiabilityParity
import Legitimacy.Extract.CompositionalSafetyParity
import Legitimacy.Extract.CorrigibilityParity
import Legitimacy.Extract.NonVacuityParity
import Legitimacy.Extract.ObservableDeterminacyParity

open Legitimacy

def strategyproofnessStatusName : Except AuditError Bool -> String
  | .ok true => "passed"
  | .ok false => "failed"
  | .error _ => "error"

def printStrategyproofnessCase
    (name : String) (subject : AuditSubject)
    (claims : List AuditGovernanceClaim) : IO Unit :=
  IO.println (name ++ "|" ++
    strategyproofnessStatusName
      (auditCheckStrategyproofnessCore subject claims))

"#
    .to_string();

    script.push_str("#eval do\n");
    for case in cases {
        script.push_str("  printStrategyproofnessCase ");
        script.push_str(&lean_string(&case.name));
        script.push(' ');
        script.push_str(&lean_subject(&case.graph));
        script.push(' ');
        script.push_str(&lean_claims(&case.claims));
        script.push('\n');
    }
    script
}

fn rust_edge_case_statuses() -> BTreeMap<(String, String), String> {
    [
        ("empty", empty_graph()),
        ("singleton", singleton_graph()),
        ("cyclic", cyclic_graph()),
    ]
    .into_iter()
    .flat_map(|(case, graph)| rust_statuses_for_case(case, &graph))
    .collect()
}

fn rust_statuses_for_case(case: &str, graph: &GovernanceGraph) -> Vec<((String, String), String)> {
    let claims = synthetic_claims(graph);
    rust_statuses_for_claim_case(case, graph, &claims)
}

fn rust_statuses_for_claim_case(
    case: &str,
    graph: &GovernanceGraph,
    claims: &[legitimacy::GovernanceClaim],
) -> Vec<((String, String), String)> {
    let cycles = detect_cycles(graph).unwrap();
    if !cycles.is_empty() {
        return CHECKS
            .into_iter()
            .map(|check| {
                let status = if check == "non_vacuous" {
                    kernel_status(check_graph_nonvacuity(graph, &claims, &cycles))
                } else {
                    "skipped".to_string()
                };
                ((case.to_string(), check.to_string()), status)
            })
            .collect();
    }

    let fields = graph_fields(&claims);
    let shocks = graph_shocks(&fields);
    let deltas = graph_deltas(&fields);
    vec![
        (
            "consistency".to_string(),
            verdict_status(check_graph_consistency(graph, &claims)),
        ),
        (
            "solidarity".to_string(),
            verdict_status(check_graph_solidarity(graph, &claims, &shocks)),
        ),
        (
            "monotonicity".to_string(),
            verdict_status(monotonicity_check_via_polarity_schema(
                graph,
                &claims,
                &deltas,
                &Default::default(),
            )),
        ),
        (
            "strategyproofness".to_string(),
            verdict_status(check_graph_strategyproofness(graph, &claims)),
        ),
        (
            "certifiability".to_string(),
            kernel_status(check_graph_certifiability(graph, &claims)),
        ),
        (
            "observable_determinacy".to_string(),
            kernel_status(check_graph_observable_determinacy(graph, &claims)),
        ),
        (
            "corrigibility".to_string(),
            kernel_status(check_graph_corrigibility(graph, &claims)),
        ),
        (
            "compositional_safety".to_string(),
            kernel_status(check_graph_compositional_safety(graph, &claims)),
        ),
        (
            "non_vacuous".to_string(),
            kernel_status(check_graph_nonvacuity(graph, &claims, &cycles)),
        ),
    ]
    .into_iter()
    .map(|(check, status)| ((case.to_string(), check), status))
    .collect()
}

fn verdict_status(result: Result<Verdict, legitimacy::LegitimacyError>) -> String {
    match result {
        Ok(Verdict::Admissible { .. }) => "passed",
        Ok(Verdict::Rejected { .. }) => "failed",
        Err(_) => "error",
    }
    .to_string()
}

fn kernel_status(result: Result<AxiomVerdict, legitimacy::LegitimacyError>) -> String {
    match result {
        Ok(AxiomVerdict::Pass { .. }) => "passed",
        Ok(AxiomVerdict::Fail { .. }) => "failed",
        Ok(AxiomVerdict::Skipped { .. }) => "skipped",
        Err(_) => "error",
    }
    .to_string()
}

fn graph_fields(claims: &[legitimacy::GovernanceClaim]) -> Vec<String> {
    let mut fields = vec!["strength".to_string()];
    for claim in claims {
        fields.extend(claim.metrics.keys().cloned());
    }
    fields.sort();
    fields.dedup();
    fields
}

fn graph_shocks(fields: &[String]) -> Vec<legitimacy::axioms::binary::BinaryShock> {
    fields
        .iter()
        .map(|field| legitimacy::axioms::binary::BinaryShock {
            field: field.clone(),
            delta: if field == "strength" { 0.1 } else { 1.0 },
        })
        .collect()
}

fn graph_deltas(fields: &[String]) -> Vec<legitimacy::axioms::binary::BinaryDelta> {
    fields
        .iter()
        .map(|field| legitimacy::axioms::binary::BinaryDelta {
            field: field.clone(),
            delta: if field == "strength" { 0.1 } else { 1.0 },
        })
        .collect()
}

fn lean_edge_case_statuses() -> BTreeMap<(String, String), String> {
    let script_path = unique_path("edge-case-parity", "lean");
    std::fs::write(
        &script_path,
        r#"
import Legitimacy.Results.GovernanceAdmissibilityAudit.Checks
import Legitimacy.Extract.CertifiabilityParity
import Legitimacy.Extract.CompositionalSafetyParity
import Legitimacy.Extract.CorrigibilityParity
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

def emptySubject : AuditSubject where
  graph := { nodes := [], edges := [] }
  evalNode := auditEvaluateNode

def singletonSubject : AuditSubject where
  graph :=
    { nodes := [ .binary "entry" "entry" [] .permit .firstMatch ]
      edges := [] }
  evalNode := auditEvaluateNode

def cyclicSubject : AuditSubject where
  graph :=
    { nodes :=
        [ .binary "cycle-a" "cycle a" [] .permit .firstMatch
        , .binary "cycle-b" "cycle b" [] .permit .firstMatch
        ]
      edges :=
        [ { fromNode := "cycle-a", toNode := "cycle-b",
            transform := .passThrough }
        , { fromNode := "cycle-b", toNode := "cycle-a",
            transform := .passThrough }
        ] }
  evalNode := auditEvaluateNode

def printParityCase (name : String) (subject : AuditSubject) : IO Unit :=
  auditCheckOrder.forM fun check =>
    IO.println (name ++ "|" ++ parityCheckName check ++ "|" ++
      parityStatusName (auditCheckStatus subject check))

#eval do
  printParityCase "empty" emptySubject
  printParityCase "singleton" singletonSubject
  printParityCase "cyclic" cyclicSubject
"#,
    )
    .unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", script_path.to_str().unwrap()])
        .output()
        .expect("failed to run Lean edge-case parity check");

    let _ = std::fs::remove_file(&script_path);

    assert!(
        output.status.success(),
        "Lean edge-case parity runner failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
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

fn lean_subject(graph: &GovernanceGraph) -> String {
    format!(
        "{{ graph := {}, evalNode := auditEvaluateNode }}",
        lean_graph(graph)
    )
}

fn lean_graph(graph: &GovernanceGraph) -> String {
    format!(
        "{{ nodes := {}, edges := {} }}",
        lean_nodes(graph),
        lean_edges(graph)
    )
}

fn lean_nodes(graph: &GovernanceGraph) -> String {
    let nodes = graph
        .nodes
        .values()
        .map(lean_node)
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{nodes}]")
}

fn lean_node(node: &GovernanceNode) -> String {
    match node {
        GovernanceNode::Binary {
            id,
            name,
            gates,
            default,
            combination,
        } => format!(
            "AuditGovernanceNode.binary {} {} {} {} {}",
            lean_string(&id.to_string()),
            lean_string(name),
            lean_gates(gates),
            lean_decision(default),
            lean_gate_logic(combination)
        ),
        GovernanceNode::Proportional {
            id,
            name,
            rule,
            priority_classes,
        } => format!(
            "AuditGovernanceNode.proportional {} {} {} {}",
            lean_string(&id.to_string()),
            lean_string(name),
            lean_string(&format!("{rule:?}")),
            lean_string_list(priority_classes)
        ),
        GovernanceNode::Threshold {
            id,
            name,
            threshold,
            field,
        } => format!(
            "AuditGovernanceNode.threshold {} {} {} {}",
            lean_string(&id.to_string()),
            lean_string(name),
            lean_rat(*threshold),
            lean_string(field)
        ),
    }
}

fn lean_gates(gates: &[Gate]) -> String {
    let gates = gates.iter().map(lean_gate).collect::<Vec<_>>().join(", ");
    format!("[{gates}]")
}

fn lean_gate(gate: &Gate) -> String {
    match gate {
        Gate::PrefixMatch { pattern, decision } => {
            format!(
                "AuditGate.prefixMatch {} {}",
                lean_string(pattern),
                lean_decision(decision)
            )
        }
        Gate::ExactMatch { value, decision } => {
            format!(
                "AuditGate.exactMatch {} {}",
                lean_string(value),
                lean_decision(decision)
            )
        }
        Gate::ContentMatch { regex, decision } => {
            format!(
                "AuditGate.contentMatch {} {}",
                lean_string(regex),
                lean_decision(decision)
            )
        }
        Gate::ThresholdGate {
            field,
            min,
            decision,
        } => format!(
            "AuditGate.thresholdGate {} {} {}",
            lean_string(field),
            lean_rat(*min),
            lean_decision(decision)
        ),
        Gate::PeerRelative {
            field,
            percentile,
            decision,
        } => format!(
            "AuditGate.peerRelative {} {} {}",
            lean_string(field),
            lean_rat(*percentile),
            lean_decision(decision)
        ),
    }
}

fn lean_decision(decision: &Decision) -> &'static str {
    match decision {
        Decision::Permit => "AuditDecision.permit",
        Decision::Deny => "AuditDecision.deny",
        Decision::Escalate => "AuditDecision.escalate",
    }
}

fn lean_gate_logic(logic: &GateLogic) -> &'static str {
    match logic {
        GateLogic::AllMustPass => "AuditGateLogic.allMustPass",
        GateLogic::AnyMustPass => "AuditGateLogic.anyMustPass",
        GateLogic::FirstMatch => "AuditGateLogic.firstMatch",
    }
}

fn lean_edges(graph: &GovernanceGraph) -> String {
    let edges = graph
        .edges
        .iter()
        .map(lean_edge)
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{edges}]")
}

fn lean_edge(edge: &legitimacy::GovernanceEdge) -> String {
    format!(
        "{{ fromNode := {}, toNode := {}, transform := {} }}",
        lean_string(&edge.from.to_string()),
        lean_string(&edge.to.to_string()),
        lean_edge_transform(&edge.transform)
    )
}

fn lean_edge_transform(transform: &EdgeTransform) -> String {
    match transform {
        EdgeTransform::PassThrough => "AuditEdgeTransform.passThrough".to_string(),
        EdgeTransform::ClaimModification { delta } => {
            format!("AuditEdgeTransform.claimModification {}", lean_rat(*delta))
        }
    }
}

fn lean_claims(claims: &[legitimacy::GovernanceClaim]) -> String {
    let claims = claims.iter().map(lean_claim).collect::<Vec<_>>().join(", ");
    format!("[{claims}]")
}

fn lean_claim(claim: &legitimacy::GovernanceClaim) -> String {
    format!(
        "{{ claimantId := {}, strength := {}, priorityClass := {}, path := {}, action := {}, content := {}, metrics := {} }}",
        lean_string(&claim.claimant_id),
        lean_rat(claim.strength),
        lean_option_string(&claim.priority_class),
        lean_option_string(&claim.path),
        lean_option_string(&claim.action),
        lean_option_string(&claim.content),
        lean_metrics(&claim.metrics)
    )
}

fn lean_metrics(metrics: &BTreeMap<String, f64>) -> String {
    let metrics = metrics
        .iter()
        .map(|(field, value)| format!("({}, {})", lean_string(field), lean_rat(*value)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{metrics}]")
}

fn lean_option_string(value: &Option<String>) -> String {
    match value {
        Some(value) => format!("some {}", lean_string(value)),
        None => "none".to_string(),
    }
}

fn lean_string_list(values: &[String]) -> String {
    let values = values
        .iter()
        .map(|value| lean_string(value))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{values}]")
}

fn lean_string(value: &str) -> String {
    format!("{value:?}")
}

fn lean_rat(value: f64) -> String {
    assert!(
        value.is_finite(),
        "Lean parity fixture only supports finite rationals, got {value}"
    );
    let scaled = (value * 1000.0).round() as i64;
    assert!(
        ((scaled as f64 / 1000.0) - value).abs() < 1e-9,
        "Lean parity fixture value is not representable at denominator 1000: {value}"
    );
    format!("(({scaled} : Rat) / 1000)")
}

fn empty_graph() -> GovernanceGraph {
    GovernanceGraph {
        nodes: BTreeMap::new(),
        edges: Vec::new(),
    }
}

fn singleton_graph() -> GovernanceGraph {
    let node_id = NodeId::new("entry").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([(
            node_id.clone(),
            GovernanceNode::Binary {
                id: node_id,
                name: "entry".to_string(),
                gates: Vec::new(),
                default: Decision::Permit,
                combination: GateLogic::FirstMatch,
            },
        )]),
        edges: Vec::new(),
    }
}

fn cyclic_graph() -> GovernanceGraph {
    let node_a = NodeId::new("cycle-a").unwrap();
    let node_b = NodeId::new("cycle-b").unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([
            (
                node_a.clone(),
                GovernanceNode::Binary {
                    id: node_a.clone(),
                    name: "cycle a".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            ),
            (
                node_b.clone(),
                GovernanceNode::Binary {
                    id: node_b.clone(),
                    name: "cycle b".to_string(),
                    gates: Vec::new(),
                    default: Decision::Permit,
                    combination: GateLogic::FirstMatch,
                },
            ),
        ]),
        edges: vec![
            legitimacy::GovernanceEdge::new(
                node_a.clone(),
                node_b.clone(),
                EdgeTransform::PassThrough,
            )
            .unwrap(),
            legitimacy::GovernanceEdge::new(node_b, node_a, EdgeTransform::PassThrough).unwrap(),
        ],
    }
}

fn threshold_graph(id: &str, min: f64) -> GovernanceGraph {
    let node_id = NodeId::new(id).unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([(
            node_id.clone(),
            GovernanceNode::Binary {
                id: node_id,
                name: id.to_string(),
                gates: vec![Gate::ThresholdGate {
                    field: "strength".to_string(),
                    min,
                    decision: Decision::Permit,
                }],
                default: Decision::Deny,
                combination: GateLogic::FirstMatch,
            },
        )]),
        edges: Vec::new(),
    }
}

fn peer_relative_graph(id: &str) -> GovernanceGraph {
    let node_id = NodeId::new(id).unwrap();
    GovernanceGraph {
        nodes: BTreeMap::from([(
            node_id.clone(),
            GovernanceNode::Binary {
                id: node_id,
                name: id.to_string(),
                gates: vec![Gate::PeerRelative {
                    field: "strength".to_string(),
                    percentile: 0.5,
                    decision: Decision::Permit,
                }],
                default: Decision::Deny,
                combination: GateLogic::AnyMustPass,
            },
        )]),
        edges: Vec::new(),
    }
}

fn deterministic_strategyproofness_graph(index: usize) -> GovernanceGraph {
    let node_count = 1 + (index % 3);
    let mut nodes = BTreeMap::new();
    for node_index in 0..node_count {
        let id = NodeId::new(format!("r{index}-{node_index}")).unwrap();
        let gate = match (index + node_index) % 3 {
            0 => Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 0.5,
                decision: Decision::Permit,
            },
            1 => Gate::ThresholdGate {
                field: "strength".to_string(),
                min: 0.8,
                decision: Decision::Escalate,
            },
            _ => Gate::PeerRelative {
                field: "strength".to_string(),
                percentile: 0.5,
                decision: Decision::Permit,
            },
        };
        let default = if (index + node_index) % 4 == 0 {
            Decision::Permit
        } else {
            Decision::Deny
        };
        let combination = match (index + node_index) % 3 {
            0 => GateLogic::FirstMatch,
            1 => GateLogic::AnyMustPass,
            _ => GateLogic::AllMustPass,
        };
        nodes.insert(
            id.clone(),
            GovernanceNode::Binary {
                id,
                name: format!("randomized {index} {node_index}"),
                gates: vec![gate],
                default,
                combination,
            },
        );
    }

    let mut edges = Vec::new();
    for node_index in 0..node_count.saturating_sub(1) {
        edges.push(
            legitimacy::GovernanceEdge::new(
                NodeId::new(format!("r{index}-{node_index}")).unwrap(),
                NodeId::new(format!("r{index}-{}", node_index + 1)).unwrap(),
                if (index + node_index) % 2 == 0 {
                    EdgeTransform::PassThrough
                } else {
                    EdgeTransform::ClaimModification { delta: 0.1 }
                },
            )
            .unwrap(),
        );
    }

    GovernanceGraph { nodes, edges }
}

fn deterministic_strategyproofness_claims(index: usize) -> Vec<legitimacy::GovernanceClaim> {
    let strengths = [0.3, 0.45, 0.6, 0.75, 0.9];
    (0..4)
        .map(|claim_index| {
            let strength = strengths[(index + claim_index) % strengths.len()];
            claim(&format!("claimant-{index}-{claim_index}"), strength)
        })
        .collect()
}

fn claim(claimant_id: &str, strength: f64) -> legitimacy::GovernanceClaim {
    legitimacy::GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength,
        priority_class: None,
        path: None,
        action: None,
        content: None,
        metrics: BTreeMap::new(),
    }
}

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}
