#![allow(deprecated)]

use legitimacy::{
    Decision, Gate, GateLogic, GovernanceClaim, GovernanceGraph, GovernanceNode, LegitimacyError,
    NodeId, Verdict,
    axioms::{
        binary::BinaryDelta,
        graph::monotonicity::{
            AUDIT_METRIC_POLARITY_SCHEMA, AuditMetricPolarity, AuditMetricPolaritySchema,
            check_graph_monotonicity_positive_delta, monotonicity_check_via_polarity_schema,
        },
    },
};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

#[test]
#[allow(deprecated)]
fn lower_better_schema_rejects_positive_delta_disagreement_fixture() {
    let graph = lower_better_gate_graph("latency");
    let claims = vec![claim_with_metric("baseline", "latency", 0.0)];
    let deltas = [BinaryDelta {
        field: "latency".to_string(),
        delta: 1.0,
    }];

    let legacy = check_graph_monotonicity_positive_delta(&graph, &claims, &deltas).unwrap();
    let canonical = monotonicity_check_via_polarity_schema(
        &graph,
        &claims,
        &deltas,
        &AuditMetricPolaritySchema::default(),
    )
    .unwrap();

    assert!(matches!(legacy, Verdict::Admissible { .. }));
    assert!(matches!(canonical, Verdict::Rejected { .. }));
}

#[test]
fn rust_polarity_fixture_matches_lean_audit_verdict() {
    assert_lean_polarity_fixture_fails();

    let graph = lower_better_gate_graph("paradox_risk");
    let claims = vec![claim_with_metric("baseline", "paradox_risk", 0.0)];
    let deltas = [BinaryDelta {
        field: "paradox_risk".to_string(),
        delta: 1.0,
    }];

    let canonical = monotonicity_check_via_polarity_schema(
        &graph,
        &claims,
        &deltas,
        &AuditMetricPolaritySchema::default(),
    )
    .unwrap();

    assert!(matches!(canonical, Verdict::Rejected { .. }));
}

#[test]
fn rust_polarity_schema_matches_lean_schema() {
    let rust_entries = rust_polarity_schema_entries();
    assert_eq!(
        rust_entries.len(),
        AUDIT_METRIC_POLARITY_SCHEMA.len(),
        "Rust polarity schema contains duplicate keys"
    );

    let lean_lines = lean_polarity_schema_lines();
    let lean_entries = parse_polarity_schema_lines(&lean_lines);
    assert_eq!(
        lean_entries.len(),
        lean_lines.len(),
        "Lean polarity schema contains duplicate keys"
    );

    if let Err(message) = compare_polarity_schema_entries(&rust_entries, &lean_entries) {
        panic!("{message}");
    }
}

#[test]
fn polarity_schema_parity_rejects_existing_key_value_drift() {
    let rust_entries = rust_polarity_schema_entries();
    let mut drifted_entries = rust_entries.clone();
    let lower_previous =
        drifted_entries.insert("paradox_risk".to_string(), "higherBetter".to_string());
    let higher_previous =
        drifted_entries.insert("strength".to_string(), "diagnosticPresence".to_string());
    let diagnostic_previous =
        drifted_entries.insert("approval_required".to_string(), "lowerBetter".to_string());

    assert_eq!(lower_previous.as_deref(), Some("lowerBetter"));
    assert_eq!(higher_previous.as_deref(), Some("higherBetter"));
    assert_eq!(diagnostic_previous.as_deref(), Some("diagnosticPresence"));
    let mismatch = compare_polarity_schema_entries(&rust_entries, &drifted_entries)
        .expect_err("same-key polarity drift should fail schema parity");
    assert!(mismatch.contains("paradox_risk"));
    assert!(mismatch.contains("strength"));
    assert!(mismatch.contains("approval_required"));
}

#[test]
fn diagnostic_presence_delta_is_schema_known_but_not_claimant_improvement() {
    let graph = diagnostic_presence_gate_graph("approval_required");
    let claims = vec![claim_with_metric("baseline", "approval_required", 0.0)];
    let deltas = [BinaryDelta {
        field: "approval_required".to_string(),
        delta: 1.0,
    }];

    let canonical = monotonicity_check_via_polarity_schema(
        &graph,
        &claims,
        &deltas,
        &AuditMetricPolaritySchema::default(),
    )
    .unwrap();

    assert!(matches!(
        canonical,
        Verdict::Admissible {
            perturbations_tested: 0,
            ..
        }
    ));
}

fn rust_polarity_schema_entries() -> BTreeMap<String, String> {
    AUDIT_METRIC_POLARITY_SCHEMA
        .iter()
        .map(|(field, polarity)| ((*field).to_string(), polarity_label(*polarity).to_string()))
        .collect()
}

fn polarity_label(polarity: AuditMetricPolarity) -> &'static str {
    match polarity {
        AuditMetricPolarity::HigherBetter => "higherBetter",
        AuditMetricPolarity::LowerBetter => "lowerBetter",
        AuditMetricPolarity::DiagnosticPresence => "diagnosticPresence",
    }
}

fn compare_polarity_schema_entries(
    expected: &BTreeMap<String, String>,
    actual: &BTreeMap<String, String>,
) -> Result<(), String> {
    if expected == actual {
        return Ok(());
    }

    let differing_fields = expected
        .iter()
        .filter_map(|(field, expected_polarity)| {
            actual.get(field).and_then(|actual_polarity| {
                (actual_polarity != expected_polarity).then(|| {
                    format!("{field}: expected {expected_polarity}, got {actual_polarity}")
                })
            })
        })
        .collect::<Vec<_>>();

    let missing_fields = expected
        .keys()
        .filter(|field| !actual.contains_key(*field))
        .cloned()
        .collect::<Vec<_>>();
    let extra_fields = actual
        .keys()
        .filter(|field| !expected.contains_key(*field))
        .cloned()
        .collect::<Vec<_>>();

    Err(format!(
        "polarity schema mismatch; differing={differing_fields:?}; missing={missing_fields:?}; extra={extra_fields:?}"
    ))
}

#[test]
fn unknown_polarity_field_is_rejected_as_invalid_gate() {
    let field = "schema_absent_metric";
    let graph = lower_better_gate_graph(field);
    let claims = vec![claim_with_metric("baseline", field, 0.0)];
    let deltas = [BinaryDelta {
        field: field.to_string(),
        delta: 1.0,
    }];

    let result = monotonicity_check_via_polarity_schema(
        &graph,
        &claims,
        &deltas,
        &AuditMetricPolaritySchema::default(),
    );

    let Err(LegitimacyError::InvalidGate { gate, message }) = result else {
        panic!("unknown polarity field should be rejected, got {result:?}");
    };
    assert_eq!(gate, field);
    assert!(message.contains("no schema polarity annotation"));
}

fn lower_better_gate_graph(field: &str) -> GovernanceGraph {
    let node_id = NodeId::new("polarity-risk-gate").unwrap();
    let node = GovernanceNode::Binary {
        id: node_id.clone(),
        name: "Backwards lower-better gate".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: field.to_string(),
            min: 0.0,
            decision: Decision::Permit,
        }],
        default: Decision::Deny,
        combination: GateLogic::FirstMatch,
    };

    GovernanceGraph {
        nodes: BTreeMap::from([(node_id, node)]),
        edges: Vec::new(),
    }
}

fn diagnostic_presence_gate_graph(field: &str) -> GovernanceGraph {
    let node_id = NodeId::new("diagnostic-presence-gate").unwrap();
    let node = GovernanceNode::Binary {
        id: node_id.clone(),
        name: "Diagnostic presence gate".to_string(),
        gates: vec![Gate::ThresholdGate {
            field: field.to_string(),
            min: 1.0,
            decision: Decision::Deny,
        }],
        default: Decision::Permit,
        combination: GateLogic::FirstMatch,
    };

    GovernanceGraph {
        nodes: BTreeMap::from([(node_id, node)]),
        edges: Vec::new(),
    }
}

fn claim_with_metric(claimant_id: &str, field: &str, value: f64) -> GovernanceClaim {
    GovernanceClaim {
        claimant_id: claimant_id.to_string(),
        strength: 1.0,
        priority_class: Some("polarity".to_string()),
        path: None,
        action: None,
        content: None,
        metrics: BTreeMap::from([(field.to_string(), value)]),
    }
}

fn parse_polarity_schema_lines(lines: &[String]) -> BTreeMap<String, String> {
    lines
        .iter()
        .map(|line| {
            let (field, polarity) = line
                .rsplit_once(':')
                .unwrap_or_else(|| panic!("invalid Lean polarity schema line: {line}"));
            (field.to_string(), polarity.to_string())
        })
        .collect()
}

fn lean_polarity_schema_lines() -> Vec<String> {
    let script_path = unique_path("polarity-schema-entries", "lean");
    std::fs::write(
        &script_path,
        r#"
import Legitimacy.Results.GovernanceAdmissibilityAudit.Evaluation

open Legitimacy

def polarityName : AuditMetricPolarity → String
  | .lowerBetter => "lowerBetter"
  | .higherBetter => "higherBetter"
  | .diagnosticPresence => "diagnosticPresence"

#eval IO.println (String.intercalate "\n"
  (auditMetricPolaritySchema.map
    (fun entry => entry.fst ++ ":" ++ polarityName entry.snd)))
"#,
    )
    .unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", script_path.to_str().unwrap()])
        .output()
        .expect("failed to run Lean polarity schema key extraction");

    let _ = std::fs::remove_file(&script_path);

    assert!(
        output.status.success(),
        "Lean polarity schema extraction failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(str::to_string)
        .collect()
}

fn assert_lean_polarity_fixture_fails() {
    let script_path = unique_path("polarity-schema-parity", "lean");
    std::fs::write(
        &script_path,
        r#"
import Legitimacy.Results.GovernanceAdmissibilityAudit.Fixtures

open Legitimacy

example :
    auditCheckStatus polarityAwareTightnessSubject AuditCheck.monotonicity =
      .ok .failed := by
  native_decide
"#,
    )
    .unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", script_path.to_str().unwrap()])
        .output()
        .expect("failed to run Lean polarity parity check");

    let _ = std::fs::remove_file(&script_path);

    assert!(
        output.status.success(),
        "Lean polarity fixture did not prove the expected failed verdict\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}
