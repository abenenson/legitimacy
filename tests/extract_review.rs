use legitimacy::{
    ClaimCorpusProvenance, ExtractionEvidenceTier, ExtractionOptions, ExtractionReviewOverlay,
    audit_extracted_graph_with_review, extract_governance_artifacts_with_review,
};
use std::{
    fs,
    path::Path,
    time::{SystemTime, UNIX_EPOCH},
};

#[test]
fn review_overlay_marks_reviewed_nodes_and_edges() {
    let source_dir = unique_source_dir("extract-review-overlay");
    fs::create_dir_all(source_dir.join("a")).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "read" {
        return review_guard(action);
    } else if action == "write" {
        return Decision::Permit;
    } else {
        return Decision::Deny;
    }
}
"#,
    )
    .unwrap();
    fs::write(
        source_dir.join("a/review.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn review_guard(action: &str) -> Decision {
    if action == "delete" {
        return Decision::Deny;
    } else if action == "read" {
        return Decision::Permit;
    } else {
        return Decision::Deny;
    }
}
"#,
    )
    .unwrap();

    let overlay: ExtractionReviewOverlay = serde_json::from_str(
        &fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/sample_governance_review_overlay.json"),
        )
        .unwrap(),
    )
    .unwrap();

    let artifacts = extract_governance_artifacts_with_review(
        &source_dir,
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
        Some(&overlay),
    )
    .unwrap();

    assert!(
        artifacts
            .recognized_nodes
            .iter()
            .any(|node| node.node_id == "policy.rs::approval_gate"
                && node.tier == ExtractionEvidenceTier::Reviewed)
    );
    assert!(
        artifacts
            .recognized_edges
            .iter()
            .any(|edge| edge.from == "policy.rs::approval_gate"
                && edge.to == "a/review.rs::review_guard"
                && edge.tier == ExtractionEvidenceTier::Reviewed)
    );
    assert!(
        artifacts
            .resolution_issues
            .iter()
            .all(|issue| !(issue.caller == "policy.rs::approval_gate"
                && issue.target_symbol == "review_guard"))
    );
}

#[test]
fn reviewed_runtime_corpus_provenance_round_trips_through_audit() {
    let source_dir = unique_source_dir("extract-runtime-provenance");
    fs::create_dir_all(&source_dir).unwrap();
    fs::write(
        source_dir.join("policy.rs"),
        r#"
enum Decision {
    Permit,
    Deny,
}

pub fn approval_gate(action: &str) -> Decision {
    if action == "write" {
        return Decision::Permit;
    }
    Decision::Deny
}
"#,
    )
    .unwrap();

    let claims = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/sample_governance_runtime_claims.jsonl"),
    )
    .unwrap()
    .lines()
    .map(|line| serde_json::from_str(line).unwrap())
    .collect();

    let report = audit_extracted_graph_with_review(
        &source_dir,
        claims,
        ExtractionOptions {
            allow_partial: false,
            ..ExtractionOptions::default()
        },
        ClaimCorpusProvenance::ObservedRuntime,
        None,
    )
    .unwrap();

    assert_eq!(
        report.audit.corpus_provenance,
        ClaimCorpusProvenance::ObservedRuntime
    );
}

fn unique_source_dir(label: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}"))
}
